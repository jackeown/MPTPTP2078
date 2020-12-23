%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:29:08 EST 2020

% Result     : Theorem 8.85s
% Output     : CNFRefutation 8.91s
% Verified   : 
% Statistics : Number of formulae       :  276 (27971 expanded)
%              Number of leaves         :   37 (9272 expanded)
%              Depth                    :   43
%              Number of atoms          :  814 (100099 expanded)
%              Number of equality atoms :   94 (10747 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > m1_subset_1 > m1_pre_topc > v7_struct_0 > v2_struct_0 > v1_xboole_0 > v1_pre_topc > l1_struct_0 > l1_pre_topc > k6_domain_1 > k2_tarski > k1_tex_2 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k1_tarski > #skF_1 > #skF_2 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(u1_pre_topc,type,(
    u1_pre_topc: $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(g1_pre_topc,type,(
    g1_pre_topc: ( $i * $i ) > $i )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(v7_struct_0,type,(
    v7_struct_0: $i > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(k6_domain_1,type,(
    k6_domain_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(v1_pre_topc,type,(
    v1_pre_topc: $i > $o )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k1_tex_2,type,(
    k1_tex_2: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(m1_pre_topc,type,(
    m1_pre_topc: ( $i * $i ) > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_175,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( ( ~ v2_struct_0(B)
              & v7_struct_0(B)
              & m1_pre_topc(B,A) )
           => ? [C] :
                ( m1_subset_1(C,u1_struct_0(A))
                & g1_pre_topc(u1_struct_0(B),u1_pre_topc(B)) = g1_pre_topc(u1_struct_0(k1_tex_2(A,C)),u1_pre_topc(k1_tex_2(A,C))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_tex_2)).

tff(f_44,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_37,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_103,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => m1_pre_topc(A,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tsep_1)).

tff(f_99,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ( v1_pre_topc(g1_pre_topc(u1_struct_0(B),u1_pre_topc(B)))
            & m1_pre_topc(g1_pre_topc(u1_struct_0(B),u1_pre_topc(B)),A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_tmap_1)).

tff(f_83,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( l1_pre_topc(B)
         => ( m1_pre_topc(A,B)
          <=> m1_pre_topc(A,g1_pre_topc(u1_struct_0(B),u1_pre_topc(B))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_pre_topc)).

tff(f_110,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => r1_tarski(u1_struct_0(B),u1_struct_0(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_borsuk_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_122,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ( v7_struct_0(A)
      <=> ? [B] :
            ( m1_subset_1(B,u1_struct_0(A))
            & u1_struct_0(A) = k6_domain_1(u1_struct_0(A),B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tex_1)).

tff(f_142,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( ( ~ v2_struct_0(C)
                & v1_pre_topc(C)
                & m1_pre_topc(C,A) )
             => ( C = k1_tex_2(A,B)
              <=> u1_struct_0(C) = k6_domain_1(u1_struct_0(A),B) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tex_2)).

tff(f_74,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & m1_pre_topc(B,A) )
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(B))
             => m1_subset_1(C,u1_struct_0(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_pre_topc)).

tff(f_156,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,u1_struct_0(A)) )
     => ( ~ v2_struct_0(k1_tex_2(A,B))
        & v1_pre_topc(k1_tex_2(A,B))
        & m1_pre_topc(k1_tex_2(A,B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_tex_2)).

tff(f_50,axiom,(
    ! [A] :
      ( ( v2_struct_0(A)
        & l1_struct_0(A) )
     => v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_struct_0)).

tff(f_58,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

tff(f_90,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(c_56,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_175])).

tff(c_58,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_175])).

tff(c_52,plain,(
    m1_pre_topc('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_175])).

tff(c_75,plain,(
    ! [B_52,A_53] :
      ( l1_pre_topc(B_52)
      | ~ m1_pre_topc(B_52,A_53)
      | ~ l1_pre_topc(A_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_81,plain,
    ( l1_pre_topc('#skF_3')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_52,c_75])).

tff(c_85,plain,(
    l1_pre_topc('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_81])).

tff(c_10,plain,(
    ! [A_4] :
      ( l1_struct_0(A_4)
      | ~ l1_pre_topc(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_54,plain,(
    v7_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_175])).

tff(c_30,plain,(
    ! [A_25] :
      ( m1_pre_topc(A_25,A_25)
      | ~ l1_pre_topc(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_124,plain,(
    ! [B_68,A_69] :
      ( m1_pre_topc(g1_pre_topc(u1_struct_0(B_68),u1_pre_topc(B_68)),A_69)
      | ~ m1_pre_topc(B_68,A_69)
      | ~ l1_pre_topc(A_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_12,plain,(
    ! [B_7,A_5] :
      ( l1_pre_topc(B_7)
      | ~ m1_pre_topc(B_7,A_5)
      | ~ l1_pre_topc(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_132,plain,(
    ! [B_70,A_71] :
      ( l1_pre_topc(g1_pre_topc(u1_struct_0(B_70),u1_pre_topc(B_70)))
      | ~ m1_pre_topc(B_70,A_71)
      | ~ l1_pre_topc(A_71) ) ),
    inference(resolution,[status(thm)],[c_124,c_12])).

tff(c_138,plain,
    ( l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_52,c_132])).

tff(c_143,plain,(
    l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_138])).

tff(c_22,plain,(
    ! [A_17,B_19] :
      ( m1_pre_topc(A_17,g1_pre_topc(u1_struct_0(B_19),u1_pre_topc(B_19)))
      | ~ m1_pre_topc(A_17,B_19)
      | ~ l1_pre_topc(B_19)
      | ~ l1_pre_topc(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_163,plain,(
    ! [A_78,B_79] :
      ( m1_pre_topc(A_78,B_79)
      | ~ m1_pre_topc(A_78,g1_pre_topc(u1_struct_0(B_79),u1_pre_topc(B_79)))
      | ~ l1_pre_topc(B_79)
      | ~ l1_pre_topc(A_78) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_244,plain,(
    ! [B_92] :
      ( m1_pre_topc(g1_pre_topc(u1_struct_0(B_92),u1_pre_topc(B_92)),B_92)
      | ~ l1_pre_topc(B_92)
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(B_92),u1_pre_topc(B_92))) ) ),
    inference(resolution,[status(thm)],[c_30,c_163])).

tff(c_32,plain,(
    ! [B_28,A_26] :
      ( r1_tarski(u1_struct_0(B_28),u1_struct_0(A_26))
      | ~ m1_pre_topc(B_28,A_26)
      | ~ l1_pre_topc(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_99,plain,(
    ! [B_58,A_59] :
      ( r1_tarski(u1_struct_0(B_58),u1_struct_0(A_59))
      | ~ m1_pre_topc(B_58,A_59)
      | ~ l1_pre_topc(A_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_213,plain,(
    ! [B_88,A_89] :
      ( u1_struct_0(B_88) = u1_struct_0(A_89)
      | ~ r1_tarski(u1_struct_0(A_89),u1_struct_0(B_88))
      | ~ m1_pre_topc(B_88,A_89)
      | ~ l1_pre_topc(A_89) ) ),
    inference(resolution,[status(thm)],[c_99,c_2])).

tff(c_221,plain,(
    ! [B_28,A_26] :
      ( u1_struct_0(B_28) = u1_struct_0(A_26)
      | ~ m1_pre_topc(A_26,B_28)
      | ~ l1_pre_topc(B_28)
      | ~ m1_pre_topc(B_28,A_26)
      | ~ l1_pre_topc(A_26) ) ),
    inference(resolution,[status(thm)],[c_32,c_213])).

tff(c_433,plain,(
    ! [B_124] :
      ( u1_struct_0(g1_pre_topc(u1_struct_0(B_124),u1_pre_topc(B_124))) = u1_struct_0(B_124)
      | ~ m1_pre_topc(B_124,g1_pre_topc(u1_struct_0(B_124),u1_pre_topc(B_124)))
      | ~ l1_pre_topc(B_124)
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(B_124),u1_pre_topc(B_124))) ) ),
    inference(resolution,[status(thm)],[c_244,c_221])).

tff(c_444,plain,(
    ! [B_125] :
      ( u1_struct_0(g1_pre_topc(u1_struct_0(B_125),u1_pre_topc(B_125))) = u1_struct_0(B_125)
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(B_125),u1_pre_topc(B_125)))
      | ~ m1_pre_topc(B_125,B_125)
      | ~ l1_pre_topc(B_125) ) ),
    inference(resolution,[status(thm)],[c_22,c_433])).

tff(c_459,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))) = u1_struct_0('#skF_3')
    | ~ m1_pre_topc('#skF_3','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_143,c_444])).

tff(c_468,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))) = u1_struct_0('#skF_3')
    | ~ m1_pre_topc('#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_85,c_459])).

tff(c_469,plain,(
    ~ m1_pre_topc('#skF_3','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_468])).

tff(c_498,plain,(
    ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_30,c_469])).

tff(c_502,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_85,c_498])).

tff(c_504,plain,(
    m1_pre_topc('#skF_3','#skF_3') ),
    inference(splitRight,[status(thm)],[c_468])).

tff(c_36,plain,(
    ! [A_29] :
      ( k6_domain_1(u1_struct_0(A_29),'#skF_1'(A_29)) = u1_struct_0(A_29)
      | ~ v7_struct_0(A_29)
      | ~ l1_struct_0(A_29)
      | v2_struct_0(A_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_306,plain,(
    ! [A_101,B_102,C_103] :
      ( k1_tex_2(A_101,B_102) = C_103
      | u1_struct_0(C_103) != k6_domain_1(u1_struct_0(A_101),B_102)
      | ~ m1_pre_topc(C_103,A_101)
      | ~ v1_pre_topc(C_103)
      | v2_struct_0(C_103)
      | ~ m1_subset_1(B_102,u1_struct_0(A_101))
      | ~ l1_pre_topc(A_101)
      | v2_struct_0(A_101) ) ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_686,plain,(
    ! [A_128,C_129] :
      ( k1_tex_2(A_128,'#skF_1'(A_128)) = C_129
      | u1_struct_0(C_129) != u1_struct_0(A_128)
      | ~ m1_pre_topc(C_129,A_128)
      | ~ v1_pre_topc(C_129)
      | v2_struct_0(C_129)
      | ~ m1_subset_1('#skF_1'(A_128),u1_struct_0(A_128))
      | ~ l1_pre_topc(A_128)
      | v2_struct_0(A_128)
      | ~ v7_struct_0(A_128)
      | ~ l1_struct_0(A_128)
      | v2_struct_0(A_128) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_306])).

tff(c_688,plain,
    ( k1_tex_2('#skF_3','#skF_1'('#skF_3')) = '#skF_3'
    | ~ v1_pre_topc('#skF_3')
    | ~ m1_subset_1('#skF_1'('#skF_3'),u1_struct_0('#skF_3'))
    | ~ l1_pre_topc('#skF_3')
    | ~ v7_struct_0('#skF_3')
    | ~ l1_struct_0('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_504,c_686])).

tff(c_705,plain,
    ( k1_tex_2('#skF_3','#skF_1'('#skF_3')) = '#skF_3'
    | ~ v1_pre_topc('#skF_3')
    | ~ m1_subset_1('#skF_1'('#skF_3'),u1_struct_0('#skF_3'))
    | ~ l1_struct_0('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_85,c_688])).

tff(c_706,plain,
    ( k1_tex_2('#skF_3','#skF_1'('#skF_3')) = '#skF_3'
    | ~ v1_pre_topc('#skF_3')
    | ~ m1_subset_1('#skF_1'('#skF_3'),u1_struct_0('#skF_3'))
    | ~ l1_struct_0('#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_705])).

tff(c_799,plain,(
    ~ l1_struct_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_706])).

tff(c_802,plain,(
    ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_10,c_799])).

tff(c_806,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_85,c_802])).

tff(c_808,plain,(
    l1_struct_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_706])).

tff(c_38,plain,(
    ! [A_29] :
      ( m1_subset_1('#skF_1'(A_29),u1_struct_0(A_29))
      | ~ v7_struct_0(A_29)
      | ~ l1_struct_0(A_29)
      | v2_struct_0(A_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_263,plain,(
    ! [C_93,A_94,B_95] :
      ( m1_subset_1(C_93,u1_struct_0(A_94))
      | ~ m1_subset_1(C_93,u1_struct_0(B_95))
      | ~ m1_pre_topc(B_95,A_94)
      | v2_struct_0(B_95)
      | ~ l1_pre_topc(A_94)
      | v2_struct_0(A_94) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_282,plain,(
    ! [A_97,A_98] :
      ( m1_subset_1('#skF_1'(A_97),u1_struct_0(A_98))
      | ~ m1_pre_topc(A_97,A_98)
      | ~ l1_pre_topc(A_98)
      | v2_struct_0(A_98)
      | ~ v7_struct_0(A_97)
      | ~ l1_struct_0(A_97)
      | v2_struct_0(A_97) ) ),
    inference(resolution,[status(thm)],[c_38,c_263])).

tff(c_18,plain,(
    ! [C_16,A_10,B_14] :
      ( m1_subset_1(C_16,u1_struct_0(A_10))
      | ~ m1_subset_1(C_16,u1_struct_0(B_14))
      | ~ m1_pre_topc(B_14,A_10)
      | v2_struct_0(B_14)
      | ~ l1_pre_topc(A_10)
      | v2_struct_0(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_1734,plain,(
    ! [A_161,A_162,A_163] :
      ( m1_subset_1('#skF_1'(A_161),u1_struct_0(A_162))
      | ~ m1_pre_topc(A_163,A_162)
      | ~ l1_pre_topc(A_162)
      | v2_struct_0(A_162)
      | ~ m1_pre_topc(A_161,A_163)
      | ~ l1_pre_topc(A_163)
      | v2_struct_0(A_163)
      | ~ v7_struct_0(A_161)
      | ~ l1_struct_0(A_161)
      | v2_struct_0(A_161) ) ),
    inference(resolution,[status(thm)],[c_282,c_18])).

tff(c_1744,plain,(
    ! [A_161] :
      ( m1_subset_1('#skF_1'(A_161),u1_struct_0('#skF_3'))
      | ~ m1_pre_topc(A_161,'#skF_3')
      | ~ l1_pre_topc('#skF_3')
      | v2_struct_0('#skF_3')
      | ~ v7_struct_0(A_161)
      | ~ l1_struct_0(A_161)
      | v2_struct_0(A_161) ) ),
    inference(resolution,[status(thm)],[c_504,c_1734])).

tff(c_1775,plain,(
    ! [A_161] :
      ( m1_subset_1('#skF_1'(A_161),u1_struct_0('#skF_3'))
      | ~ m1_pre_topc(A_161,'#skF_3')
      | v2_struct_0('#skF_3')
      | ~ v7_struct_0(A_161)
      | ~ l1_struct_0(A_161)
      | v2_struct_0(A_161) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_85,c_1744])).

tff(c_1840,plain,(
    ! [A_167] :
      ( m1_subset_1('#skF_1'(A_167),u1_struct_0('#skF_3'))
      | ~ m1_pre_topc(A_167,'#skF_3')
      | ~ v7_struct_0(A_167)
      | ~ l1_struct_0(A_167)
      | v2_struct_0(A_167) ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_1775])).

tff(c_46,plain,(
    ! [A_40,B_41] :
      ( v1_pre_topc(k1_tex_2(A_40,B_41))
      | ~ m1_subset_1(B_41,u1_struct_0(A_40))
      | ~ l1_pre_topc(A_40)
      | v2_struct_0(A_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_1850,plain,(
    ! [A_167] :
      ( v1_pre_topc(k1_tex_2('#skF_3','#skF_1'(A_167)))
      | ~ l1_pre_topc('#skF_3')
      | v2_struct_0('#skF_3')
      | ~ m1_pre_topc(A_167,'#skF_3')
      | ~ v7_struct_0(A_167)
      | ~ l1_struct_0(A_167)
      | v2_struct_0(A_167) ) ),
    inference(resolution,[status(thm)],[c_1840,c_46])).

tff(c_1870,plain,(
    ! [A_167] :
      ( v1_pre_topc(k1_tex_2('#skF_3','#skF_1'(A_167)))
      | v2_struct_0('#skF_3')
      | ~ m1_pre_topc(A_167,'#skF_3')
      | ~ v7_struct_0(A_167)
      | ~ l1_struct_0(A_167)
      | v2_struct_0(A_167) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_85,c_1850])).

tff(c_1871,plain,(
    ! [A_167] :
      ( v1_pre_topc(k1_tex_2('#skF_3','#skF_1'(A_167)))
      | ~ m1_pre_topc(A_167,'#skF_3')
      | ~ v7_struct_0(A_167)
      | ~ l1_struct_0(A_167)
      | v2_struct_0(A_167) ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_1870])).

tff(c_1776,plain,(
    ! [A_161] :
      ( m1_subset_1('#skF_1'(A_161),u1_struct_0('#skF_3'))
      | ~ m1_pre_topc(A_161,'#skF_3')
      | ~ v7_struct_0(A_161)
      | ~ l1_struct_0(A_161)
      | v2_struct_0(A_161) ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_1775])).

tff(c_159,plain,(
    ! [A_76,B_77] :
      ( m1_pre_topc(k1_tex_2(A_76,B_77),A_76)
      | ~ m1_subset_1(B_77,u1_struct_0(A_76))
      | ~ l1_pre_topc(A_76)
      | v2_struct_0(A_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_162,plain,(
    ! [A_29] :
      ( m1_pre_topc(k1_tex_2(A_29,'#skF_1'(A_29)),A_29)
      | ~ l1_pre_topc(A_29)
      | ~ v7_struct_0(A_29)
      | ~ l1_struct_0(A_29)
      | v2_struct_0(A_29) ) ),
    inference(resolution,[status(thm)],[c_38,c_159])).

tff(c_333,plain,(
    ! [A_108,B_109] :
      ( k6_domain_1(u1_struct_0(A_108),B_109) = u1_struct_0(k1_tex_2(A_108,B_109))
      | ~ m1_pre_topc(k1_tex_2(A_108,B_109),A_108)
      | ~ v1_pre_topc(k1_tex_2(A_108,B_109))
      | v2_struct_0(k1_tex_2(A_108,B_109))
      | ~ m1_subset_1(B_109,u1_struct_0(A_108))
      | ~ l1_pre_topc(A_108)
      | v2_struct_0(A_108) ) ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_2017,plain,(
    ! [A_173] :
      ( k6_domain_1(u1_struct_0(A_173),'#skF_1'(A_173)) = u1_struct_0(k1_tex_2(A_173,'#skF_1'(A_173)))
      | ~ v1_pre_topc(k1_tex_2(A_173,'#skF_1'(A_173)))
      | v2_struct_0(k1_tex_2(A_173,'#skF_1'(A_173)))
      | ~ m1_subset_1('#skF_1'(A_173),u1_struct_0(A_173))
      | ~ l1_pre_topc(A_173)
      | ~ v7_struct_0(A_173)
      | ~ l1_struct_0(A_173)
      | v2_struct_0(A_173) ) ),
    inference(resolution,[status(thm)],[c_162,c_333])).

tff(c_2021,plain,
    ( k6_domain_1(u1_struct_0('#skF_3'),'#skF_1'('#skF_3')) = u1_struct_0(k1_tex_2('#skF_3','#skF_1'('#skF_3')))
    | ~ v1_pre_topc(k1_tex_2('#skF_3','#skF_1'('#skF_3')))
    | v2_struct_0(k1_tex_2('#skF_3','#skF_1'('#skF_3')))
    | ~ l1_pre_topc('#skF_3')
    | ~ m1_pre_topc('#skF_3','#skF_3')
    | ~ v7_struct_0('#skF_3')
    | ~ l1_struct_0('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_1776,c_2017])).

tff(c_2041,plain,
    ( k6_domain_1(u1_struct_0('#skF_3'),'#skF_1'('#skF_3')) = u1_struct_0(k1_tex_2('#skF_3','#skF_1'('#skF_3')))
    | ~ v1_pre_topc(k1_tex_2('#skF_3','#skF_1'('#skF_3')))
    | v2_struct_0(k1_tex_2('#skF_3','#skF_1'('#skF_3')))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_808,c_54,c_504,c_85,c_2021])).

tff(c_2042,plain,
    ( k6_domain_1(u1_struct_0('#skF_3'),'#skF_1'('#skF_3')) = u1_struct_0(k1_tex_2('#skF_3','#skF_1'('#skF_3')))
    | ~ v1_pre_topc(k1_tex_2('#skF_3','#skF_1'('#skF_3')))
    | v2_struct_0(k1_tex_2('#skF_3','#skF_1'('#skF_3'))) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_2041])).

tff(c_2277,plain,(
    ~ v1_pre_topc(k1_tex_2('#skF_3','#skF_1'('#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_2042])).

tff(c_2280,plain,
    ( ~ m1_pre_topc('#skF_3','#skF_3')
    | ~ v7_struct_0('#skF_3')
    | ~ l1_struct_0('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_1871,c_2277])).

tff(c_2292,plain,(
    v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_808,c_54,c_504,c_2280])).

tff(c_2294,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_2292])).

tff(c_2295,plain,
    ( v2_struct_0(k1_tex_2('#skF_3','#skF_1'('#skF_3')))
    | k6_domain_1(u1_struct_0('#skF_3'),'#skF_1'('#skF_3')) = u1_struct_0(k1_tex_2('#skF_3','#skF_1'('#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_2042])).

tff(c_2303,plain,(
    k6_domain_1(u1_struct_0('#skF_3'),'#skF_1'('#skF_3')) = u1_struct_0(k1_tex_2('#skF_3','#skF_1'('#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_2295])).

tff(c_2321,plain,
    ( u1_struct_0(k1_tex_2('#skF_3','#skF_1'('#skF_3'))) = u1_struct_0('#skF_3')
    | ~ v7_struct_0('#skF_3')
    | ~ l1_struct_0('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_2303,c_36])).

tff(c_2352,plain,
    ( u1_struct_0(k1_tex_2('#skF_3','#skF_1'('#skF_3'))) = u1_struct_0('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_808,c_54,c_2321])).

tff(c_2353,plain,(
    u1_struct_0(k1_tex_2('#skF_3','#skF_1'('#skF_3'))) = u1_struct_0('#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_2352])).

tff(c_191,plain,(
    ! [A_84] :
      ( m1_pre_topc(k1_tex_2(A_84,'#skF_1'(A_84)),A_84)
      | ~ l1_pre_topc(A_84)
      | ~ v7_struct_0(A_84)
      | ~ l1_struct_0(A_84)
      | v2_struct_0(A_84) ) ),
    inference(resolution,[status(thm)],[c_38,c_159])).

tff(c_131,plain,(
    ! [B_68,A_69] :
      ( l1_pre_topc(g1_pre_topc(u1_struct_0(B_68),u1_pre_topc(B_68)))
      | ~ m1_pre_topc(B_68,A_69)
      | ~ l1_pre_topc(A_69) ) ),
    inference(resolution,[status(thm)],[c_124,c_12])).

tff(c_204,plain,(
    ! [A_84] :
      ( l1_pre_topc(g1_pre_topc(u1_struct_0(k1_tex_2(A_84,'#skF_1'(A_84))),u1_pre_topc(k1_tex_2(A_84,'#skF_1'(A_84)))))
      | ~ l1_pre_topc(A_84)
      | ~ v7_struct_0(A_84)
      | ~ l1_struct_0(A_84)
      | v2_struct_0(A_84) ) ),
    inference(resolution,[status(thm)],[c_191,c_131])).

tff(c_2442,plain,
    ( l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc(k1_tex_2('#skF_3','#skF_1'('#skF_3')))))
    | ~ l1_pre_topc('#skF_3')
    | ~ v7_struct_0('#skF_3')
    | ~ l1_struct_0('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_2353,c_204])).

tff(c_2561,plain,
    ( l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc(k1_tex_2('#skF_3','#skF_1'('#skF_3')))))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_808,c_54,c_85,c_2442])).

tff(c_2562,plain,(
    l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc(k1_tex_2('#skF_3','#skF_1'('#skF_3'))))) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_2561])).

tff(c_503,plain,(
    u1_struct_0(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))) = u1_struct_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_468])).

tff(c_14,plain,(
    ! [A_8] :
      ( v1_xboole_0(u1_struct_0(A_8))
      | ~ l1_struct_0(A_8)
      | ~ v2_struct_0(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_630,plain,
    ( v1_xboole_0(u1_struct_0('#skF_3'))
    | ~ l1_struct_0(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')))
    | ~ v2_struct_0(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_503,c_14])).

tff(c_1018,plain,(
    ~ v2_struct_0(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_630])).

tff(c_16,plain,(
    ! [A_9] :
      ( ~ v1_xboole_0(u1_struct_0(A_9))
      | ~ l1_struct_0(A_9)
      | v2_struct_0(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_627,plain,
    ( ~ v1_xboole_0(u1_struct_0('#skF_3'))
    | ~ l1_struct_0(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')))
    | v2_struct_0(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_503,c_16])).

tff(c_1019,plain,
    ( ~ v1_xboole_0(u1_struct_0('#skF_3'))
    | ~ l1_struct_0(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))) ),
    inference(negUnitSimplification,[status(thm)],[c_1018,c_627])).

tff(c_1020,plain,(
    ~ l1_struct_0(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_1019])).

tff(c_1023,plain,(
    ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))) ),
    inference(resolution,[status(thm)],[c_10,c_1020])).

tff(c_1027,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_143,c_1023])).

tff(c_1028,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_1019])).

tff(c_104,plain,(
    ! [B_62,A_63] :
      ( v1_pre_topc(g1_pre_topc(u1_struct_0(B_62),u1_pre_topc(B_62)))
      | ~ m1_pre_topc(B_62,A_63)
      | ~ l1_pre_topc(A_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_108,plain,
    ( v1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_52,c_104])).

tff(c_112,plain,(
    v1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_108])).

tff(c_173,plain,(
    ! [B_79] :
      ( m1_pre_topc(g1_pre_topc(u1_struct_0(B_79),u1_pre_topc(B_79)),B_79)
      | ~ l1_pre_topc(B_79)
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(B_79),u1_pre_topc(B_79))) ) ),
    inference(resolution,[status(thm)],[c_30,c_163])).

tff(c_1842,plain,(
    ! [A_167,A_10] :
      ( m1_subset_1('#skF_1'(A_167),u1_struct_0(A_10))
      | ~ m1_pre_topc('#skF_3',A_10)
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc(A_10)
      | v2_struct_0(A_10)
      | ~ m1_pre_topc(A_167,'#skF_3')
      | ~ v7_struct_0(A_167)
      | ~ l1_struct_0(A_167)
      | v2_struct_0(A_167) ) ),
    inference(resolution,[status(thm)],[c_1840,c_18])).

tff(c_1859,plain,(
    ! [A_167,A_10] :
      ( m1_subset_1('#skF_1'(A_167),u1_struct_0(A_10))
      | ~ m1_pre_topc('#skF_3',A_10)
      | ~ l1_pre_topc(A_10)
      | v2_struct_0(A_10)
      | ~ m1_pre_topc(A_167,'#skF_3')
      | ~ v7_struct_0(A_167)
      | ~ l1_struct_0(A_167)
      | v2_struct_0(A_167) ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_1842])).

tff(c_2367,plain,(
    k6_domain_1(u1_struct_0('#skF_3'),'#skF_1'('#skF_3')) = u1_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2353,c_2303])).

tff(c_40,plain,(
    ! [A_33,B_37,C_39] :
      ( k1_tex_2(A_33,B_37) = C_39
      | u1_struct_0(C_39) != k6_domain_1(u1_struct_0(A_33),B_37)
      | ~ m1_pre_topc(C_39,A_33)
      | ~ v1_pre_topc(C_39)
      | v2_struct_0(C_39)
      | ~ m1_subset_1(B_37,u1_struct_0(A_33))
      | ~ l1_pre_topc(A_33)
      | v2_struct_0(A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_2617,plain,(
    ! [C_39] :
      ( k1_tex_2('#skF_3','#skF_1'('#skF_3')) = C_39
      | u1_struct_0(C_39) != u1_struct_0('#skF_3')
      | ~ m1_pre_topc(C_39,'#skF_3')
      | ~ v1_pre_topc(C_39)
      | v2_struct_0(C_39)
      | ~ m1_subset_1('#skF_1'('#skF_3'),u1_struct_0('#skF_3'))
      | ~ l1_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2367,c_40])).

tff(c_2649,plain,(
    ! [C_39] :
      ( k1_tex_2('#skF_3','#skF_1'('#skF_3')) = C_39
      | u1_struct_0(C_39) != u1_struct_0('#skF_3')
      | ~ m1_pre_topc(C_39,'#skF_3')
      | ~ v1_pre_topc(C_39)
      | v2_struct_0(C_39)
      | ~ m1_subset_1('#skF_1'('#skF_3'),u1_struct_0('#skF_3'))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_85,c_2617])).

tff(c_2650,plain,(
    ! [C_39] :
      ( k1_tex_2('#skF_3','#skF_1'('#skF_3')) = C_39
      | u1_struct_0(C_39) != u1_struct_0('#skF_3')
      | ~ m1_pre_topc(C_39,'#skF_3')
      | ~ v1_pre_topc(C_39)
      | v2_struct_0(C_39)
      | ~ m1_subset_1('#skF_1'('#skF_3'),u1_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_2649])).

tff(c_3544,plain,(
    ~ m1_subset_1('#skF_1'('#skF_3'),u1_struct_0('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_2650])).

tff(c_3547,plain,
    ( ~ l1_pre_topc('#skF_3')
    | ~ m1_pre_topc('#skF_3','#skF_3')
    | ~ v7_struct_0('#skF_3')
    | ~ l1_struct_0('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_1859,c_3544])).

tff(c_3562,plain,(
    v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_808,c_54,c_504,c_85,c_3547])).

tff(c_3564,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_3562])).

tff(c_3967,plain,(
    ! [C_213] :
      ( k1_tex_2('#skF_3','#skF_1'('#skF_3')) = C_213
      | u1_struct_0(C_213) != u1_struct_0('#skF_3')
      | ~ m1_pre_topc(C_213,'#skF_3')
      | ~ v1_pre_topc(C_213)
      | v2_struct_0(C_213) ) ),
    inference(splitRight,[status(thm)],[c_2650])).

tff(c_3993,plain,
    ( g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')) = k1_tex_2('#skF_3','#skF_1'('#skF_3'))
    | u1_struct_0(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))) != u1_struct_0('#skF_3')
    | ~ v1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')))
    | v2_struct_0(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')))
    | ~ l1_pre_topc('#skF_3')
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))) ),
    inference(resolution,[status(thm)],[c_173,c_3967])).

tff(c_4034,plain,
    ( g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')) = k1_tex_2('#skF_3','#skF_1'('#skF_3'))
    | v2_struct_0(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_143,c_85,c_112,c_503,c_3993])).

tff(c_4035,plain,(
    g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')) = k1_tex_2('#skF_3','#skF_1'('#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_1018,c_4034])).

tff(c_4138,plain,(
    ! [A_17] :
      ( m1_pre_topc(A_17,k1_tex_2('#skF_3','#skF_1'('#skF_3')))
      | ~ m1_pre_topc(A_17,'#skF_3')
      | ~ l1_pre_topc('#skF_3')
      | ~ l1_pre_topc(A_17) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4035,c_22])).

tff(c_4199,plain,(
    ! [A_17] :
      ( m1_pre_topc(A_17,k1_tex_2('#skF_3','#skF_1'('#skF_3')))
      | ~ m1_pre_topc(A_17,'#skF_3')
      | ~ l1_pre_topc(A_17) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_85,c_4138])).

tff(c_26,plain,(
    ! [B_24,A_22] :
      ( m1_pre_topc(g1_pre_topc(u1_struct_0(B_24),u1_pre_topc(B_24)),A_22)
      | ~ m1_pre_topc(B_24,A_22)
      | ~ l1_pre_topc(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_342,plain,(
    ! [B_111,A_112] :
      ( l1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(B_111),u1_pre_topc(B_111))),u1_pre_topc(g1_pre_topc(u1_struct_0(B_111),u1_pre_topc(B_111)))))
      | ~ m1_pre_topc(B_111,A_112)
      | ~ l1_pre_topc(A_112) ) ),
    inference(resolution,[status(thm)],[c_26,c_132])).

tff(c_354,plain,
    ( l1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))),u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')))))
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_52,c_342])).

tff(c_362,plain,(
    l1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))),u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_354])).

tff(c_537,plain,(
    l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_503,c_362])).

tff(c_20,plain,(
    ! [A_17,B_19] :
      ( m1_pre_topc(A_17,B_19)
      | ~ m1_pre_topc(A_17,g1_pre_topc(u1_struct_0(B_19),u1_pre_topc(B_19)))
      | ~ l1_pre_topc(B_19)
      | ~ l1_pre_topc(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_595,plain,(
    ! [A_17] :
      ( m1_pre_topc(A_17,g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')))
      | ~ m1_pre_topc(A_17,g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')))))
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')))
      | ~ l1_pre_topc(A_17) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_503,c_20])).

tff(c_1519,plain,(
    ! [A_157] :
      ( m1_pre_topc(A_157,g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')))
      | ~ m1_pre_topc(A_157,g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')))))
      | ~ l1_pre_topc(A_157) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_143,c_595])).

tff(c_1546,plain,
    ( m1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')))),g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))))) ),
    inference(resolution,[status(thm)],[c_30,c_1519])).

tff(c_1565,plain,(
    m1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')))),g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_537,c_1546])).

tff(c_1584,plain,
    ( m1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')))),'#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))))) ),
    inference(resolution,[status(thm)],[c_1565,c_20])).

tff(c_1613,plain,(
    m1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')))),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_537,c_85,c_1584])).

tff(c_4049,plain,(
    m1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc(k1_tex_2('#skF_3','#skF_1'('#skF_3')))),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4035,c_1613])).

tff(c_592,plain,(
    ! [A_17] :
      ( m1_pre_topc(A_17,g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')))))
      | ~ m1_pre_topc(A_17,g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')))
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')))
      | ~ l1_pre_topc(A_17) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_503,c_22])).

tff(c_665,plain,(
    ! [A_17] :
      ( m1_pre_topc(A_17,g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')))))
      | ~ m1_pre_topc(A_17,g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')))
      | ~ l1_pre_topc(A_17) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_143,c_592])).

tff(c_5712,plain,(
    ! [A_230] :
      ( m1_pre_topc(A_230,g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc(k1_tex_2('#skF_3','#skF_1'('#skF_3')))))
      | ~ m1_pre_topc(A_230,k1_tex_2('#skF_3','#skF_1'('#skF_3')))
      | ~ l1_pre_topc(A_230) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4035,c_4035,c_665])).

tff(c_624,plain,(
    ! [B_28] :
      ( r1_tarski(u1_struct_0(B_28),u1_struct_0('#skF_3'))
      | ~ m1_pre_topc(B_28,g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')))
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_503,c_32])).

tff(c_718,plain,(
    ! [B_130] :
      ( r1_tarski(u1_struct_0(B_130),u1_struct_0('#skF_3'))
      | ~ m1_pre_topc(B_130,g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_143,c_624])).

tff(c_734,plain,(
    ! [A_17] :
      ( r1_tarski(u1_struct_0(A_17),u1_struct_0('#skF_3'))
      | ~ m1_pre_topc(A_17,'#skF_3')
      | ~ l1_pre_topc('#skF_3')
      | ~ l1_pre_topc(A_17) ) ),
    inference(resolution,[status(thm)],[c_22,c_718])).

tff(c_761,plain,(
    ! [A_131] :
      ( r1_tarski(u1_struct_0(A_131),u1_struct_0('#skF_3'))
      | ~ m1_pre_topc(A_131,'#skF_3')
      | ~ l1_pre_topc(A_131) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_85,c_734])).

tff(c_102,plain,(
    ! [B_58,A_59] :
      ( u1_struct_0(B_58) = u1_struct_0(A_59)
      | ~ r1_tarski(u1_struct_0(A_59),u1_struct_0(B_58))
      | ~ m1_pre_topc(B_58,A_59)
      | ~ l1_pre_topc(A_59) ) ),
    inference(resolution,[status(thm)],[c_99,c_2])).

tff(c_770,plain,(
    ! [A_131] :
      ( u1_struct_0(A_131) = u1_struct_0('#skF_3')
      | ~ m1_pre_topc('#skF_3',A_131)
      | ~ m1_pre_topc(A_131,'#skF_3')
      | ~ l1_pre_topc(A_131) ) ),
    inference(resolution,[status(thm)],[c_761,c_102])).

tff(c_5730,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc(k1_tex_2('#skF_3','#skF_1'('#skF_3'))))) = u1_struct_0('#skF_3')
    | ~ m1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc(k1_tex_2('#skF_3','#skF_1'('#skF_3')))),'#skF_3')
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc(k1_tex_2('#skF_3','#skF_1'('#skF_3')))))
    | ~ m1_pre_topc('#skF_3',k1_tex_2('#skF_3','#skF_1'('#skF_3')))
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_5712,c_770])).

tff(c_5769,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc(k1_tex_2('#skF_3','#skF_1'('#skF_3'))))) = u1_struct_0('#skF_3')
    | ~ m1_pre_topc('#skF_3',k1_tex_2('#skF_3','#skF_1'('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_85,c_2562,c_4049,c_5730])).

tff(c_5797,plain,(
    ~ m1_pre_topc('#skF_3',k1_tex_2('#skF_3','#skF_1'('#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_5769])).

tff(c_5908,plain,
    ( ~ m1_pre_topc('#skF_3','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_4199,c_5797])).

tff(c_5915,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_85,c_504,c_5908])).

tff(c_5916,plain,(
    u1_struct_0(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc(k1_tex_2('#skF_3','#skF_1'('#skF_3'))))) = u1_struct_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_5769])).

tff(c_6195,plain,
    ( v1_xboole_0(u1_struct_0('#skF_3'))
    | ~ l1_struct_0(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc(k1_tex_2('#skF_3','#skF_1'('#skF_3')))))
    | ~ v2_struct_0(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc(k1_tex_2('#skF_3','#skF_1'('#skF_3'))))) ),
    inference(superposition,[status(thm),theory(equality)],[c_5916,c_14])).

tff(c_6320,plain,
    ( ~ l1_struct_0(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc(k1_tex_2('#skF_3','#skF_1'('#skF_3')))))
    | ~ v2_struct_0(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc(k1_tex_2('#skF_3','#skF_1'('#skF_3'))))) ),
    inference(negUnitSimplification,[status(thm)],[c_1028,c_6195])).

tff(c_7194,plain,(
    ~ v2_struct_0(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc(k1_tex_2('#skF_3','#skF_1'('#skF_3'))))) ),
    inference(splitLeft,[status(thm)],[c_6320])).

tff(c_2524,plain,
    ( v1_xboole_0(u1_struct_0('#skF_3'))
    | ~ l1_struct_0(k1_tex_2('#skF_3','#skF_1'('#skF_3')))
    | ~ v2_struct_0(k1_tex_2('#skF_3','#skF_1'('#skF_3'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_2353,c_14])).

tff(c_2581,plain,
    ( ~ l1_struct_0(k1_tex_2('#skF_3','#skF_1'('#skF_3')))
    | ~ v2_struct_0(k1_tex_2('#skF_3','#skF_1'('#skF_3'))) ),
    inference(negUnitSimplification,[status(thm)],[c_1028,c_2524])).

tff(c_2747,plain,(
    ~ v2_struct_0(k1_tex_2('#skF_3','#skF_1'('#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_2581])).

tff(c_2296,plain,(
    v1_pre_topc(k1_tex_2('#skF_3','#skF_1'('#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_2042])).

tff(c_4147,plain,(
    ! [A_22] :
      ( m1_pre_topc(k1_tex_2('#skF_3','#skF_1'('#skF_3')),A_22)
      | ~ m1_pre_topc('#skF_3',A_22)
      | ~ l1_pre_topc(A_22) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4035,c_26])).

tff(c_60,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_175])).

tff(c_3566,plain,(
    m1_subset_1('#skF_1'('#skF_3'),u1_struct_0('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_2650])).

tff(c_3571,plain,(
    ! [A_10] :
      ( m1_subset_1('#skF_1'('#skF_3'),u1_struct_0(A_10))
      | ~ m1_pre_topc('#skF_3',A_10)
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc(A_10)
      | v2_struct_0(A_10) ) ),
    inference(resolution,[status(thm)],[c_3566,c_18])).

tff(c_3686,plain,(
    ! [A_205] :
      ( m1_subset_1('#skF_1'('#skF_3'),u1_struct_0(A_205))
      | ~ m1_pre_topc('#skF_3',A_205)
      | ~ l1_pre_topc(A_205)
      | v2_struct_0(A_205) ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_3571])).

tff(c_7203,plain,(
    ! [A_243,A_244] :
      ( m1_subset_1('#skF_1'('#skF_3'),u1_struct_0(A_243))
      | ~ m1_pre_topc(A_244,A_243)
      | ~ l1_pre_topc(A_243)
      | v2_struct_0(A_243)
      | ~ m1_pre_topc('#skF_3',A_244)
      | ~ l1_pre_topc(A_244)
      | v2_struct_0(A_244) ) ),
    inference(resolution,[status(thm)],[c_3686,c_18])).

tff(c_7251,plain,
    ( m1_subset_1('#skF_1'('#skF_3'),u1_struct_0('#skF_2'))
    | ~ l1_pre_topc('#skF_2')
    | v2_struct_0('#skF_2')
    | ~ m1_pre_topc('#skF_3','#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_52,c_7203])).

tff(c_7319,plain,
    ( m1_subset_1('#skF_1'('#skF_3'),u1_struct_0('#skF_2'))
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_85,c_504,c_58,c_7251])).

tff(c_7320,plain,(
    m1_subset_1('#skF_1'('#skF_3'),u1_struct_0('#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_60,c_7319])).

tff(c_1036,plain,(
    ! [A_138] :
      ( k1_tex_2(A_138,'#skF_1'(A_138)) = A_138
      | ~ v1_pre_topc(A_138)
      | ~ m1_subset_1('#skF_1'(A_138),u1_struct_0(A_138))
      | ~ v7_struct_0(A_138)
      | ~ l1_struct_0(A_138)
      | v2_struct_0(A_138)
      | ~ l1_pre_topc(A_138) ) ),
    inference(resolution,[status(thm)],[c_30,c_686])).

tff(c_1055,plain,(
    ! [A_139] :
      ( k1_tex_2(A_139,'#skF_1'(A_139)) = A_139
      | ~ v1_pre_topc(A_139)
      | ~ l1_pre_topc(A_139)
      | ~ v7_struct_0(A_139)
      | ~ l1_struct_0(A_139)
      | v2_struct_0(A_139) ) ),
    inference(resolution,[status(thm)],[c_38,c_1036])).

tff(c_50,plain,(
    ! [C_46] :
      ( g1_pre_topc(u1_struct_0(k1_tex_2('#skF_2',C_46)),u1_pre_topc(k1_tex_2('#skF_2',C_46))) != g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))
      | ~ m1_subset_1(C_46,u1_struct_0('#skF_2')) ) ),
    inference(cnfTransformation,[status(thm)],[f_175])).

tff(c_1100,plain,
    ( g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc(k1_tex_2('#skF_2','#skF_1'('#skF_2')))) != g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))
    | ~ m1_subset_1('#skF_1'('#skF_2'),u1_struct_0('#skF_2'))
    | ~ v1_pre_topc('#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v7_struct_0('#skF_2')
    | ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_1055,c_50])).

tff(c_1110,plain,
    ( g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc(k1_tex_2('#skF_2','#skF_1'('#skF_2')))) != g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))
    | ~ m1_subset_1('#skF_1'('#skF_2'),u1_struct_0('#skF_2'))
    | ~ v1_pre_topc('#skF_2')
    | ~ v7_struct_0('#skF_2')
    | ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_1100])).

tff(c_1111,plain,
    ( g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc(k1_tex_2('#skF_2','#skF_1'('#skF_2')))) != g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))
    | ~ m1_subset_1('#skF_1'('#skF_2'),u1_struct_0('#skF_2'))
    | ~ v1_pre_topc('#skF_2')
    | ~ v7_struct_0('#skF_2')
    | ~ l1_struct_0('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_1110])).

tff(c_1161,plain,(
    ~ l1_struct_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_1111])).

tff(c_1164,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_10,c_1161])).

tff(c_1168,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_1164])).

tff(c_1170,plain,(
    l1_struct_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_1111])).

tff(c_1758,plain,(
    ! [A_161] :
      ( m1_subset_1('#skF_1'(A_161),u1_struct_0('#skF_2'))
      | ~ l1_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ m1_pre_topc(A_161,'#skF_3')
      | ~ l1_pre_topc('#skF_3')
      | v2_struct_0('#skF_3')
      | ~ v7_struct_0(A_161)
      | ~ l1_struct_0(A_161)
      | v2_struct_0(A_161) ) ),
    inference(resolution,[status(thm)],[c_52,c_1734])).

tff(c_1785,plain,(
    ! [A_161] :
      ( m1_subset_1('#skF_1'(A_161),u1_struct_0('#skF_2'))
      | v2_struct_0('#skF_2')
      | ~ m1_pre_topc(A_161,'#skF_3')
      | v2_struct_0('#skF_3')
      | ~ v7_struct_0(A_161)
      | ~ l1_struct_0(A_161)
      | v2_struct_0(A_161) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_85,c_58,c_1758])).

tff(c_1787,plain,(
    ! [A_164] :
      ( m1_subset_1('#skF_1'(A_164),u1_struct_0('#skF_2'))
      | ~ m1_pre_topc(A_164,'#skF_3')
      | ~ v7_struct_0(A_164)
      | ~ l1_struct_0(A_164)
      | v2_struct_0(A_164) ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_60,c_1785])).

tff(c_24,plain,(
    ! [A_20,B_21] :
      ( k6_domain_1(A_20,B_21) = k1_tarski(B_21)
      | ~ m1_subset_1(B_21,A_20)
      | v1_xboole_0(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_1823,plain,(
    ! [A_164] :
      ( k6_domain_1(u1_struct_0('#skF_2'),'#skF_1'(A_164)) = k1_tarski('#skF_1'(A_164))
      | v1_xboole_0(u1_struct_0('#skF_2'))
      | ~ m1_pre_topc(A_164,'#skF_3')
      | ~ v7_struct_0(A_164)
      | ~ l1_struct_0(A_164)
      | v2_struct_0(A_164) ) ),
    inference(resolution,[status(thm)],[c_1787,c_24])).

tff(c_2167,plain,(
    v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_1823])).

tff(c_2170,plain,
    ( ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_2167,c_16])).

tff(c_2173,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1170,c_2170])).

tff(c_2175,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_2173])).

tff(c_2177,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_1823])).

tff(c_1856,plain,(
    ! [A_167] :
      ( k6_domain_1(u1_struct_0('#skF_3'),'#skF_1'(A_167)) = k1_tarski('#skF_1'(A_167))
      | v1_xboole_0(u1_struct_0('#skF_3'))
      | ~ m1_pre_topc(A_167,'#skF_3')
      | ~ v7_struct_0(A_167)
      | ~ l1_struct_0(A_167)
      | v2_struct_0(A_167) ) ),
    inference(resolution,[status(thm)],[c_1840,c_24])).

tff(c_2083,plain,(
    ! [A_176] :
      ( k6_domain_1(u1_struct_0('#skF_3'),'#skF_1'(A_176)) = k1_tarski('#skF_1'(A_176))
      | ~ m1_pre_topc(A_176,'#skF_3')
      | ~ v7_struct_0(A_176)
      | ~ l1_struct_0(A_176)
      | v2_struct_0(A_176) ) ),
    inference(negUnitSimplification,[status(thm)],[c_1028,c_1856])).

tff(c_2102,plain,
    ( k1_tarski('#skF_1'('#skF_3')) = u1_struct_0('#skF_3')
    | ~ v7_struct_0('#skF_3')
    | ~ l1_struct_0('#skF_3')
    | v2_struct_0('#skF_3')
    | ~ m1_pre_topc('#skF_3','#skF_3')
    | ~ v7_struct_0('#skF_3')
    | ~ l1_struct_0('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_2083,c_36])).

tff(c_2134,plain,
    ( k1_tarski('#skF_1'('#skF_3')) = u1_struct_0('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_808,c_54,c_504,c_808,c_54,c_2102])).

tff(c_2135,plain,(
    k1_tarski('#skF_1'('#skF_3')) = u1_struct_0('#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_2134])).

tff(c_7336,plain,
    ( k6_domain_1(u1_struct_0('#skF_2'),'#skF_1'('#skF_3')) = k1_tarski('#skF_1'('#skF_3'))
    | v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_7320,c_24])).

tff(c_7357,plain,
    ( k6_domain_1(u1_struct_0('#skF_2'),'#skF_1'('#skF_3')) = u1_struct_0('#skF_3')
    | v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2135,c_7336])).

tff(c_7358,plain,(
    k6_domain_1(u1_struct_0('#skF_2'),'#skF_1'('#skF_3')) = u1_struct_0('#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_2177,c_7357])).

tff(c_7488,plain,(
    ! [C_39] :
      ( k1_tex_2('#skF_2','#skF_1'('#skF_3')) = C_39
      | u1_struct_0(C_39) != u1_struct_0('#skF_3')
      | ~ m1_pre_topc(C_39,'#skF_2')
      | ~ v1_pre_topc(C_39)
      | v2_struct_0(C_39)
      | ~ m1_subset_1('#skF_1'('#skF_3'),u1_struct_0('#skF_2'))
      | ~ l1_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_7358,c_40])).

tff(c_7520,plain,(
    ! [C_39] :
      ( k1_tex_2('#skF_2','#skF_1'('#skF_3')) = C_39
      | u1_struct_0(C_39) != u1_struct_0('#skF_3')
      | ~ m1_pre_topc(C_39,'#skF_2')
      | ~ v1_pre_topc(C_39)
      | v2_struct_0(C_39)
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_7320,c_7488])).

tff(c_8657,plain,(
    ! [C_258] :
      ( k1_tex_2('#skF_2','#skF_1'('#skF_3')) = C_258
      | u1_struct_0(C_258) != u1_struct_0('#skF_3')
      | ~ m1_pre_topc(C_258,'#skF_2')
      | ~ v1_pre_topc(C_258)
      | v2_struct_0(C_258) ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_7520])).

tff(c_8674,plain,
    ( k1_tex_2('#skF_2','#skF_1'('#skF_3')) = k1_tex_2('#skF_3','#skF_1'('#skF_3'))
    | u1_struct_0(k1_tex_2('#skF_3','#skF_1'('#skF_3'))) != u1_struct_0('#skF_3')
    | ~ v1_pre_topc(k1_tex_2('#skF_3','#skF_1'('#skF_3')))
    | v2_struct_0(k1_tex_2('#skF_3','#skF_1'('#skF_3')))
    | ~ m1_pre_topc('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_4147,c_8657])).

tff(c_8724,plain,
    ( k1_tex_2('#skF_2','#skF_1'('#skF_3')) = k1_tex_2('#skF_3','#skF_1'('#skF_3'))
    | v2_struct_0(k1_tex_2('#skF_3','#skF_1'('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_52,c_2296,c_2353,c_8674])).

tff(c_8725,plain,(
    k1_tex_2('#skF_2','#skF_1'('#skF_3')) = k1_tex_2('#skF_3','#skF_1'('#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_2747,c_8724])).

tff(c_48,plain,(
    ! [A_40,B_41] :
      ( ~ v2_struct_0(k1_tex_2(A_40,B_41))
      | ~ m1_subset_1(B_41,u1_struct_0(A_40))
      | ~ l1_pre_topc(A_40)
      | v2_struct_0(A_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_7333,plain,
    ( ~ v2_struct_0(k1_tex_2('#skF_2','#skF_1'('#skF_3')))
    | ~ l1_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_7320,c_48])).

tff(c_7354,plain,
    ( ~ v2_struct_0(k1_tex_2('#skF_2','#skF_1'('#skF_3')))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_7333])).

tff(c_7355,plain,(
    ~ v2_struct_0(k1_tex_2('#skF_2','#skF_1'('#skF_3'))) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_7354])).

tff(c_7330,plain,
    ( v1_pre_topc(k1_tex_2('#skF_2','#skF_1'('#skF_3')))
    | ~ l1_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_7320,c_46])).

tff(c_7350,plain,
    ( v1_pre_topc(k1_tex_2('#skF_2','#skF_1'('#skF_3')))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_7330])).

tff(c_7351,plain,(
    v1_pre_topc(k1_tex_2('#skF_2','#skF_1'('#skF_3'))) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_7350])).

tff(c_44,plain,(
    ! [A_40,B_41] :
      ( m1_pre_topc(k1_tex_2(A_40,B_41),A_40)
      | ~ m1_subset_1(B_41,u1_struct_0(A_40))
      | ~ l1_pre_topc(A_40)
      | v2_struct_0(A_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_7327,plain,
    ( m1_pre_topc(k1_tex_2('#skF_2','#skF_1'('#skF_3')),'#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_7320,c_44])).

tff(c_7346,plain,
    ( m1_pre_topc(k1_tex_2('#skF_2','#skF_1'('#skF_3')),'#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_7327])).

tff(c_7347,plain,(
    m1_pre_topc(k1_tex_2('#skF_2','#skF_1'('#skF_3')),'#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_7346])).

tff(c_42,plain,(
    ! [A_33,B_37] :
      ( k6_domain_1(u1_struct_0(A_33),B_37) = u1_struct_0(k1_tex_2(A_33,B_37))
      | ~ m1_pre_topc(k1_tex_2(A_33,B_37),A_33)
      | ~ v1_pre_topc(k1_tex_2(A_33,B_37))
      | v2_struct_0(k1_tex_2(A_33,B_37))
      | ~ m1_subset_1(B_37,u1_struct_0(A_33))
      | ~ l1_pre_topc(A_33)
      | v2_struct_0(A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_7419,plain,
    ( k6_domain_1(u1_struct_0('#skF_2'),'#skF_1'('#skF_3')) = u1_struct_0(k1_tex_2('#skF_2','#skF_1'('#skF_3')))
    | ~ v1_pre_topc(k1_tex_2('#skF_2','#skF_1'('#skF_3')))
    | v2_struct_0(k1_tex_2('#skF_2','#skF_1'('#skF_3')))
    | ~ m1_subset_1('#skF_1'('#skF_3'),u1_struct_0('#skF_2'))
    | ~ l1_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_7347,c_42])).

tff(c_7451,plain,
    ( k6_domain_1(u1_struct_0('#skF_2'),'#skF_1'('#skF_3')) = u1_struct_0(k1_tex_2('#skF_2','#skF_1'('#skF_3')))
    | v2_struct_0(k1_tex_2('#skF_2','#skF_1'('#skF_3')))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_7320,c_7351,c_7419])).

tff(c_7452,plain,(
    k6_domain_1(u1_struct_0('#skF_2'),'#skF_1'('#skF_3')) = u1_struct_0(k1_tex_2('#skF_2','#skF_1'('#skF_3'))) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_7355,c_7451])).

tff(c_7534,plain,(
    u1_struct_0(k1_tex_2('#skF_2','#skF_1'('#skF_3'))) = u1_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_7358,c_7452])).

tff(c_4069,plain,(
    ! [C_46] :
      ( g1_pre_topc(u1_struct_0(k1_tex_2('#skF_2',C_46)),u1_pre_topc(k1_tex_2('#skF_2',C_46))) != k1_tex_2('#skF_3','#skF_1'('#skF_3'))
      | ~ m1_subset_1(C_46,u1_struct_0('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4035,c_50])).

tff(c_7561,plain,
    ( g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc(k1_tex_2('#skF_2','#skF_1'('#skF_3')))) != k1_tex_2('#skF_3','#skF_1'('#skF_3'))
    | ~ m1_subset_1('#skF_1'('#skF_3'),u1_struct_0('#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_7534,c_4069])).

tff(c_7765,plain,(
    g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc(k1_tex_2('#skF_2','#skF_1'('#skF_3')))) != k1_tex_2('#skF_3','#skF_1'('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7320,c_7561])).

tff(c_8761,plain,(
    g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc(k1_tex_2('#skF_3','#skF_1'('#skF_3')))) != k1_tex_2('#skF_3','#skF_1'('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8725,c_7765])).

tff(c_8769,plain,(
    m1_pre_topc(k1_tex_2('#skF_3','#skF_1'('#skF_3')),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8725,c_7347])).

tff(c_28,plain,(
    ! [B_24,A_22] :
      ( v1_pre_topc(g1_pre_topc(u1_struct_0(B_24),u1_pre_topc(B_24)))
      | ~ m1_pre_topc(B_24,A_22)
      | ~ l1_pre_topc(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_205,plain,(
    ! [A_84] :
      ( v1_pre_topc(g1_pre_topc(u1_struct_0(k1_tex_2(A_84,'#skF_1'(A_84))),u1_pre_topc(k1_tex_2(A_84,'#skF_1'(A_84)))))
      | ~ l1_pre_topc(A_84)
      | ~ v7_struct_0(A_84)
      | ~ l1_struct_0(A_84)
      | v2_struct_0(A_84) ) ),
    inference(resolution,[status(thm)],[c_191,c_28])).

tff(c_2445,plain,
    ( v1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc(k1_tex_2('#skF_3','#skF_1'('#skF_3')))))
    | ~ l1_pre_topc('#skF_3')
    | ~ v7_struct_0('#skF_3')
    | ~ l1_struct_0('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_2353,c_205])).

tff(c_2564,plain,
    ( v1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc(k1_tex_2('#skF_3','#skF_1'('#skF_3')))))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_808,c_54,c_85,c_2445])).

tff(c_2565,plain,(
    v1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc(k1_tex_2('#skF_3','#skF_1'('#skF_3'))))) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_2564])).

tff(c_2503,plain,(
    ! [A_22] :
      ( m1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc(k1_tex_2('#skF_3','#skF_1'('#skF_3')))),A_22)
      | ~ m1_pre_topc(k1_tex_2('#skF_3','#skF_1'('#skF_3')),A_22)
      | ~ l1_pre_topc(A_22) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2353,c_26])).

tff(c_7521,plain,(
    ! [C_39] :
      ( k1_tex_2('#skF_2','#skF_1'('#skF_3')) = C_39
      | u1_struct_0(C_39) != u1_struct_0('#skF_3')
      | ~ m1_pre_topc(C_39,'#skF_2')
      | ~ v1_pre_topc(C_39)
      | v2_struct_0(C_39) ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_7520])).

tff(c_9450,plain,(
    ! [C_268] :
      ( k1_tex_2('#skF_3','#skF_1'('#skF_3')) = C_268
      | u1_struct_0(C_268) != u1_struct_0('#skF_3')
      | ~ m1_pre_topc(C_268,'#skF_2')
      | ~ v1_pre_topc(C_268)
      | v2_struct_0(C_268) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8725,c_7521])).

tff(c_9473,plain,
    ( g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc(k1_tex_2('#skF_3','#skF_1'('#skF_3')))) = k1_tex_2('#skF_3','#skF_1'('#skF_3'))
    | u1_struct_0(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc(k1_tex_2('#skF_3','#skF_1'('#skF_3'))))) != u1_struct_0('#skF_3')
    | ~ v1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc(k1_tex_2('#skF_3','#skF_1'('#skF_3')))))
    | v2_struct_0(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc(k1_tex_2('#skF_3','#skF_1'('#skF_3')))))
    | ~ m1_pre_topc(k1_tex_2('#skF_3','#skF_1'('#skF_3')),'#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_2503,c_9450])).

tff(c_9525,plain,
    ( g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc(k1_tex_2('#skF_3','#skF_1'('#skF_3')))) = k1_tex_2('#skF_3','#skF_1'('#skF_3'))
    | v2_struct_0(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc(k1_tex_2('#skF_3','#skF_1'('#skF_3'))))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_8769,c_2565,c_5916,c_9473])).

tff(c_9527,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_7194,c_8761,c_9525])).

tff(c_9528,plain,(
    ~ l1_struct_0(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc(k1_tex_2('#skF_3','#skF_1'('#skF_3'))))) ),
    inference(splitRight,[status(thm)],[c_6320])).

tff(c_9535,plain,(
    ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc(k1_tex_2('#skF_3','#skF_1'('#skF_3'))))) ),
    inference(resolution,[status(thm)],[c_10,c_9528])).

tff(c_9542,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2562,c_9535])).

tff(c_9544,plain,(
    v2_struct_0(k1_tex_2('#skF_3','#skF_1'('#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_2581])).

tff(c_1853,plain,(
    ! [A_167] :
      ( ~ v2_struct_0(k1_tex_2('#skF_3','#skF_1'(A_167)))
      | ~ l1_pre_topc('#skF_3')
      | v2_struct_0('#skF_3')
      | ~ m1_pre_topc(A_167,'#skF_3')
      | ~ v7_struct_0(A_167)
      | ~ l1_struct_0(A_167)
      | v2_struct_0(A_167) ) ),
    inference(resolution,[status(thm)],[c_1840,c_48])).

tff(c_1874,plain,(
    ! [A_167] :
      ( ~ v2_struct_0(k1_tex_2('#skF_3','#skF_1'(A_167)))
      | v2_struct_0('#skF_3')
      | ~ m1_pre_topc(A_167,'#skF_3')
      | ~ v7_struct_0(A_167)
      | ~ l1_struct_0(A_167)
      | v2_struct_0(A_167) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_85,c_1853])).

tff(c_1875,plain,(
    ! [A_167] :
      ( ~ v2_struct_0(k1_tex_2('#skF_3','#skF_1'(A_167)))
      | ~ m1_pre_topc(A_167,'#skF_3')
      | ~ v7_struct_0(A_167)
      | ~ l1_struct_0(A_167)
      | v2_struct_0(A_167) ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_1874])).

tff(c_9569,plain,
    ( ~ m1_pre_topc('#skF_3','#skF_3')
    | ~ v7_struct_0('#skF_3')
    | ~ l1_struct_0('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_9544,c_1875])).

tff(c_9581,plain,(
    v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_808,c_54,c_504,c_9569])).

tff(c_9583,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_9581])).

tff(c_9584,plain,(
    v2_struct_0(k1_tex_2('#skF_3','#skF_1'('#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_2295])).

tff(c_9588,plain,
    ( ~ m1_pre_topc('#skF_3','#skF_3')
    | ~ v7_struct_0('#skF_3')
    | ~ l1_struct_0('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_9584,c_1875])).

tff(c_9600,plain,(
    v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_808,c_54,c_504,c_9588])).

tff(c_9602,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_9600])).

tff(c_9603,plain,
    ( ~ l1_struct_0(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')))
    | v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_630])).

tff(c_9605,plain,(
    ~ l1_struct_0(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_9603])).

tff(c_9608,plain,(
    ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))) ),
    inference(resolution,[status(thm)],[c_10,c_9605])).

tff(c_9612,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_143,c_9608])).

tff(c_9613,plain,(
    v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_9603])).

tff(c_9635,plain,
    ( ~ l1_struct_0('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_9613,c_16])).

tff(c_9638,plain,(
    v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_808,c_9635])).

tff(c_9640,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_9638])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n003.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 13:30:42 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.85/3.05  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.91/3.09  
% 8.91/3.09  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.91/3.10  %$ r1_tarski > m1_subset_1 > m1_pre_topc > v7_struct_0 > v2_struct_0 > v1_xboole_0 > v1_pre_topc > l1_struct_0 > l1_pre_topc > k6_domain_1 > k2_tarski > k1_tex_2 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k1_tarski > #skF_1 > #skF_2 > #skF_3
% 8.91/3.10  
% 8.91/3.10  %Foreground sorts:
% 8.91/3.10  
% 8.91/3.10  
% 8.91/3.10  %Background operators:
% 8.91/3.10  
% 8.91/3.10  
% 8.91/3.10  %Foreground operators:
% 8.91/3.10  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 8.91/3.10  tff(u1_pre_topc, type, u1_pre_topc: $i > $i).
% 8.91/3.10  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.91/3.10  tff(g1_pre_topc, type, g1_pre_topc: ($i * $i) > $i).
% 8.91/3.10  tff(k1_tarski, type, k1_tarski: $i > $i).
% 8.91/3.10  tff('#skF_1', type, '#skF_1': $i > $i).
% 8.91/3.10  tff(v7_struct_0, type, v7_struct_0: $i > $o).
% 8.91/3.10  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 8.91/3.10  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 8.91/3.10  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 8.91/3.10  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 8.91/3.10  tff('#skF_2', type, '#skF_2': $i).
% 8.91/3.10  tff('#skF_3', type, '#skF_3': $i).
% 8.91/3.10  tff(v1_pre_topc, type, v1_pre_topc: $i > $o).
% 8.91/3.10  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 8.91/3.10  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.91/3.10  tff(k1_tex_2, type, k1_tex_2: ($i * $i) > $i).
% 8.91/3.10  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.91/3.10  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 8.91/3.10  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 8.91/3.10  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 8.91/3.10  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 8.91/3.10  
% 8.91/3.13  tff(f_175, negated_conjecture, ~(![A]: ((~v2_struct_0(A) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v7_struct_0(B)) & m1_pre_topc(B, A)) => (?[C]: (m1_subset_1(C, u1_struct_0(A)) & (g1_pre_topc(u1_struct_0(B), u1_pre_topc(B)) = g1_pre_topc(u1_struct_0(k1_tex_2(A, C)), u1_pre_topc(k1_tex_2(A, C)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t23_tex_2)).
% 8.91/3.13  tff(f_44, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 8.91/3.13  tff(f_37, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 8.91/3.13  tff(f_103, axiom, (![A]: (l1_pre_topc(A) => m1_pre_topc(A, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_tsep_1)).
% 8.91/3.13  tff(f_99, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => (v1_pre_topc(g1_pre_topc(u1_struct_0(B), u1_pre_topc(B))) & m1_pre_topc(g1_pre_topc(u1_struct_0(B), u1_pre_topc(B)), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_tmap_1)).
% 8.91/3.13  tff(f_83, axiom, (![A]: (l1_pre_topc(A) => (![B]: (l1_pre_topc(B) => (m1_pre_topc(A, B) <=> m1_pre_topc(A, g1_pre_topc(u1_struct_0(B), u1_pre_topc(B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_pre_topc)).
% 8.91/3.13  tff(f_110, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => r1_tarski(u1_struct_0(B), u1_struct_0(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t35_borsuk_1)).
% 8.91/3.13  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 8.91/3.13  tff(f_122, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => (v7_struct_0(A) <=> (?[B]: (m1_subset_1(B, u1_struct_0(A)) & (u1_struct_0(A) = k6_domain_1(u1_struct_0(A), B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tex_1)).
% 8.91/3.13  tff(f_142, axiom, (![A]: ((~v2_struct_0(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (((~v2_struct_0(C) & v1_pre_topc(C)) & m1_pre_topc(C, A)) => ((C = k1_tex_2(A, B)) <=> (u1_struct_0(C) = k6_domain_1(u1_struct_0(A), B))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_tex_2)).
% 8.91/3.13  tff(f_74, axiom, (![A]: ((~v2_struct_0(A) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => (![C]: (m1_subset_1(C, u1_struct_0(B)) => m1_subset_1(C, u1_struct_0(A)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_pre_topc)).
% 8.91/3.13  tff(f_156, axiom, (![A, B]: (((~v2_struct_0(A) & l1_pre_topc(A)) & m1_subset_1(B, u1_struct_0(A))) => ((~v2_struct_0(k1_tex_2(A, B)) & v1_pre_topc(k1_tex_2(A, B))) & m1_pre_topc(k1_tex_2(A, B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_tex_2)).
% 8.91/3.13  tff(f_50, axiom, (![A]: ((v2_struct_0(A) & l1_struct_0(A)) => v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_struct_0)).
% 8.91/3.13  tff(f_58, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_struct_0)).
% 8.91/3.13  tff(f_90, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 8.91/3.13  tff(c_56, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_175])).
% 8.91/3.13  tff(c_58, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_175])).
% 8.91/3.13  tff(c_52, plain, (m1_pre_topc('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_175])).
% 8.91/3.13  tff(c_75, plain, (![B_52, A_53]: (l1_pre_topc(B_52) | ~m1_pre_topc(B_52, A_53) | ~l1_pre_topc(A_53))), inference(cnfTransformation, [status(thm)], [f_44])).
% 8.91/3.13  tff(c_81, plain, (l1_pre_topc('#skF_3') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_52, c_75])).
% 8.91/3.13  tff(c_85, plain, (l1_pre_topc('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_81])).
% 8.91/3.13  tff(c_10, plain, (![A_4]: (l1_struct_0(A_4) | ~l1_pre_topc(A_4))), inference(cnfTransformation, [status(thm)], [f_37])).
% 8.91/3.13  tff(c_54, plain, (v7_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_175])).
% 8.91/3.13  tff(c_30, plain, (![A_25]: (m1_pre_topc(A_25, A_25) | ~l1_pre_topc(A_25))), inference(cnfTransformation, [status(thm)], [f_103])).
% 8.91/3.13  tff(c_124, plain, (![B_68, A_69]: (m1_pre_topc(g1_pre_topc(u1_struct_0(B_68), u1_pre_topc(B_68)), A_69) | ~m1_pre_topc(B_68, A_69) | ~l1_pre_topc(A_69))), inference(cnfTransformation, [status(thm)], [f_99])).
% 8.91/3.13  tff(c_12, plain, (![B_7, A_5]: (l1_pre_topc(B_7) | ~m1_pre_topc(B_7, A_5) | ~l1_pre_topc(A_5))), inference(cnfTransformation, [status(thm)], [f_44])).
% 8.91/3.13  tff(c_132, plain, (![B_70, A_71]: (l1_pre_topc(g1_pre_topc(u1_struct_0(B_70), u1_pre_topc(B_70))) | ~m1_pre_topc(B_70, A_71) | ~l1_pre_topc(A_71))), inference(resolution, [status(thm)], [c_124, c_12])).
% 8.91/3.13  tff(c_138, plain, (l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))) | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_52, c_132])).
% 8.91/3.13  tff(c_143, plain, (l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_138])).
% 8.91/3.13  tff(c_22, plain, (![A_17, B_19]: (m1_pre_topc(A_17, g1_pre_topc(u1_struct_0(B_19), u1_pre_topc(B_19))) | ~m1_pre_topc(A_17, B_19) | ~l1_pre_topc(B_19) | ~l1_pre_topc(A_17))), inference(cnfTransformation, [status(thm)], [f_83])).
% 8.91/3.13  tff(c_163, plain, (![A_78, B_79]: (m1_pre_topc(A_78, B_79) | ~m1_pre_topc(A_78, g1_pre_topc(u1_struct_0(B_79), u1_pre_topc(B_79))) | ~l1_pre_topc(B_79) | ~l1_pre_topc(A_78))), inference(cnfTransformation, [status(thm)], [f_83])).
% 8.91/3.13  tff(c_244, plain, (![B_92]: (m1_pre_topc(g1_pre_topc(u1_struct_0(B_92), u1_pre_topc(B_92)), B_92) | ~l1_pre_topc(B_92) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(B_92), u1_pre_topc(B_92))))), inference(resolution, [status(thm)], [c_30, c_163])).
% 8.91/3.13  tff(c_32, plain, (![B_28, A_26]: (r1_tarski(u1_struct_0(B_28), u1_struct_0(A_26)) | ~m1_pre_topc(B_28, A_26) | ~l1_pre_topc(A_26))), inference(cnfTransformation, [status(thm)], [f_110])).
% 8.91/3.13  tff(c_99, plain, (![B_58, A_59]: (r1_tarski(u1_struct_0(B_58), u1_struct_0(A_59)) | ~m1_pre_topc(B_58, A_59) | ~l1_pre_topc(A_59))), inference(cnfTransformation, [status(thm)], [f_110])).
% 8.91/3.13  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 8.91/3.13  tff(c_213, plain, (![B_88, A_89]: (u1_struct_0(B_88)=u1_struct_0(A_89) | ~r1_tarski(u1_struct_0(A_89), u1_struct_0(B_88)) | ~m1_pre_topc(B_88, A_89) | ~l1_pre_topc(A_89))), inference(resolution, [status(thm)], [c_99, c_2])).
% 8.91/3.13  tff(c_221, plain, (![B_28, A_26]: (u1_struct_0(B_28)=u1_struct_0(A_26) | ~m1_pre_topc(A_26, B_28) | ~l1_pre_topc(B_28) | ~m1_pre_topc(B_28, A_26) | ~l1_pre_topc(A_26))), inference(resolution, [status(thm)], [c_32, c_213])).
% 8.91/3.13  tff(c_433, plain, (![B_124]: (u1_struct_0(g1_pre_topc(u1_struct_0(B_124), u1_pre_topc(B_124)))=u1_struct_0(B_124) | ~m1_pre_topc(B_124, g1_pre_topc(u1_struct_0(B_124), u1_pre_topc(B_124))) | ~l1_pre_topc(B_124) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(B_124), u1_pre_topc(B_124))))), inference(resolution, [status(thm)], [c_244, c_221])).
% 8.91/3.13  tff(c_444, plain, (![B_125]: (u1_struct_0(g1_pre_topc(u1_struct_0(B_125), u1_pre_topc(B_125)))=u1_struct_0(B_125) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(B_125), u1_pre_topc(B_125))) | ~m1_pre_topc(B_125, B_125) | ~l1_pre_topc(B_125))), inference(resolution, [status(thm)], [c_22, c_433])).
% 8.91/3.13  tff(c_459, plain, (u1_struct_0(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3')))=u1_struct_0('#skF_3') | ~m1_pre_topc('#skF_3', '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_143, c_444])).
% 8.91/3.13  tff(c_468, plain, (u1_struct_0(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3')))=u1_struct_0('#skF_3') | ~m1_pre_topc('#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_85, c_459])).
% 8.91/3.13  tff(c_469, plain, (~m1_pre_topc('#skF_3', '#skF_3')), inference(splitLeft, [status(thm)], [c_468])).
% 8.91/3.13  tff(c_498, plain, (~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_30, c_469])).
% 8.91/3.13  tff(c_502, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_85, c_498])).
% 8.91/3.13  tff(c_504, plain, (m1_pre_topc('#skF_3', '#skF_3')), inference(splitRight, [status(thm)], [c_468])).
% 8.91/3.13  tff(c_36, plain, (![A_29]: (k6_domain_1(u1_struct_0(A_29), '#skF_1'(A_29))=u1_struct_0(A_29) | ~v7_struct_0(A_29) | ~l1_struct_0(A_29) | v2_struct_0(A_29))), inference(cnfTransformation, [status(thm)], [f_122])).
% 8.91/3.13  tff(c_306, plain, (![A_101, B_102, C_103]: (k1_tex_2(A_101, B_102)=C_103 | u1_struct_0(C_103)!=k6_domain_1(u1_struct_0(A_101), B_102) | ~m1_pre_topc(C_103, A_101) | ~v1_pre_topc(C_103) | v2_struct_0(C_103) | ~m1_subset_1(B_102, u1_struct_0(A_101)) | ~l1_pre_topc(A_101) | v2_struct_0(A_101))), inference(cnfTransformation, [status(thm)], [f_142])).
% 8.91/3.13  tff(c_686, plain, (![A_128, C_129]: (k1_tex_2(A_128, '#skF_1'(A_128))=C_129 | u1_struct_0(C_129)!=u1_struct_0(A_128) | ~m1_pre_topc(C_129, A_128) | ~v1_pre_topc(C_129) | v2_struct_0(C_129) | ~m1_subset_1('#skF_1'(A_128), u1_struct_0(A_128)) | ~l1_pre_topc(A_128) | v2_struct_0(A_128) | ~v7_struct_0(A_128) | ~l1_struct_0(A_128) | v2_struct_0(A_128))), inference(superposition, [status(thm), theory('equality')], [c_36, c_306])).
% 8.91/3.13  tff(c_688, plain, (k1_tex_2('#skF_3', '#skF_1'('#skF_3'))='#skF_3' | ~v1_pre_topc('#skF_3') | ~m1_subset_1('#skF_1'('#skF_3'), u1_struct_0('#skF_3')) | ~l1_pre_topc('#skF_3') | ~v7_struct_0('#skF_3') | ~l1_struct_0('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_504, c_686])).
% 8.91/3.13  tff(c_705, plain, (k1_tex_2('#skF_3', '#skF_1'('#skF_3'))='#skF_3' | ~v1_pre_topc('#skF_3') | ~m1_subset_1('#skF_1'('#skF_3'), u1_struct_0('#skF_3')) | ~l1_struct_0('#skF_3') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_85, c_688])).
% 8.91/3.13  tff(c_706, plain, (k1_tex_2('#skF_3', '#skF_1'('#skF_3'))='#skF_3' | ~v1_pre_topc('#skF_3') | ~m1_subset_1('#skF_1'('#skF_3'), u1_struct_0('#skF_3')) | ~l1_struct_0('#skF_3')), inference(negUnitSimplification, [status(thm)], [c_56, c_705])).
% 8.91/3.13  tff(c_799, plain, (~l1_struct_0('#skF_3')), inference(splitLeft, [status(thm)], [c_706])).
% 8.91/3.13  tff(c_802, plain, (~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_10, c_799])).
% 8.91/3.13  tff(c_806, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_85, c_802])).
% 8.91/3.13  tff(c_808, plain, (l1_struct_0('#skF_3')), inference(splitRight, [status(thm)], [c_706])).
% 8.91/3.13  tff(c_38, plain, (![A_29]: (m1_subset_1('#skF_1'(A_29), u1_struct_0(A_29)) | ~v7_struct_0(A_29) | ~l1_struct_0(A_29) | v2_struct_0(A_29))), inference(cnfTransformation, [status(thm)], [f_122])).
% 8.91/3.13  tff(c_263, plain, (![C_93, A_94, B_95]: (m1_subset_1(C_93, u1_struct_0(A_94)) | ~m1_subset_1(C_93, u1_struct_0(B_95)) | ~m1_pre_topc(B_95, A_94) | v2_struct_0(B_95) | ~l1_pre_topc(A_94) | v2_struct_0(A_94))), inference(cnfTransformation, [status(thm)], [f_74])).
% 8.91/3.13  tff(c_282, plain, (![A_97, A_98]: (m1_subset_1('#skF_1'(A_97), u1_struct_0(A_98)) | ~m1_pre_topc(A_97, A_98) | ~l1_pre_topc(A_98) | v2_struct_0(A_98) | ~v7_struct_0(A_97) | ~l1_struct_0(A_97) | v2_struct_0(A_97))), inference(resolution, [status(thm)], [c_38, c_263])).
% 8.91/3.13  tff(c_18, plain, (![C_16, A_10, B_14]: (m1_subset_1(C_16, u1_struct_0(A_10)) | ~m1_subset_1(C_16, u1_struct_0(B_14)) | ~m1_pre_topc(B_14, A_10) | v2_struct_0(B_14) | ~l1_pre_topc(A_10) | v2_struct_0(A_10))), inference(cnfTransformation, [status(thm)], [f_74])).
% 8.91/3.13  tff(c_1734, plain, (![A_161, A_162, A_163]: (m1_subset_1('#skF_1'(A_161), u1_struct_0(A_162)) | ~m1_pre_topc(A_163, A_162) | ~l1_pre_topc(A_162) | v2_struct_0(A_162) | ~m1_pre_topc(A_161, A_163) | ~l1_pre_topc(A_163) | v2_struct_0(A_163) | ~v7_struct_0(A_161) | ~l1_struct_0(A_161) | v2_struct_0(A_161))), inference(resolution, [status(thm)], [c_282, c_18])).
% 8.91/3.13  tff(c_1744, plain, (![A_161]: (m1_subset_1('#skF_1'(A_161), u1_struct_0('#skF_3')) | ~m1_pre_topc(A_161, '#skF_3') | ~l1_pre_topc('#skF_3') | v2_struct_0('#skF_3') | ~v7_struct_0(A_161) | ~l1_struct_0(A_161) | v2_struct_0(A_161))), inference(resolution, [status(thm)], [c_504, c_1734])).
% 8.91/3.13  tff(c_1775, plain, (![A_161]: (m1_subset_1('#skF_1'(A_161), u1_struct_0('#skF_3')) | ~m1_pre_topc(A_161, '#skF_3') | v2_struct_0('#skF_3') | ~v7_struct_0(A_161) | ~l1_struct_0(A_161) | v2_struct_0(A_161))), inference(demodulation, [status(thm), theory('equality')], [c_85, c_1744])).
% 8.91/3.13  tff(c_1840, plain, (![A_167]: (m1_subset_1('#skF_1'(A_167), u1_struct_0('#skF_3')) | ~m1_pre_topc(A_167, '#skF_3') | ~v7_struct_0(A_167) | ~l1_struct_0(A_167) | v2_struct_0(A_167))), inference(negUnitSimplification, [status(thm)], [c_56, c_1775])).
% 8.91/3.13  tff(c_46, plain, (![A_40, B_41]: (v1_pre_topc(k1_tex_2(A_40, B_41)) | ~m1_subset_1(B_41, u1_struct_0(A_40)) | ~l1_pre_topc(A_40) | v2_struct_0(A_40))), inference(cnfTransformation, [status(thm)], [f_156])).
% 8.91/3.13  tff(c_1850, plain, (![A_167]: (v1_pre_topc(k1_tex_2('#skF_3', '#skF_1'(A_167))) | ~l1_pre_topc('#skF_3') | v2_struct_0('#skF_3') | ~m1_pre_topc(A_167, '#skF_3') | ~v7_struct_0(A_167) | ~l1_struct_0(A_167) | v2_struct_0(A_167))), inference(resolution, [status(thm)], [c_1840, c_46])).
% 8.91/3.13  tff(c_1870, plain, (![A_167]: (v1_pre_topc(k1_tex_2('#skF_3', '#skF_1'(A_167))) | v2_struct_0('#skF_3') | ~m1_pre_topc(A_167, '#skF_3') | ~v7_struct_0(A_167) | ~l1_struct_0(A_167) | v2_struct_0(A_167))), inference(demodulation, [status(thm), theory('equality')], [c_85, c_1850])).
% 8.91/3.13  tff(c_1871, plain, (![A_167]: (v1_pre_topc(k1_tex_2('#skF_3', '#skF_1'(A_167))) | ~m1_pre_topc(A_167, '#skF_3') | ~v7_struct_0(A_167) | ~l1_struct_0(A_167) | v2_struct_0(A_167))), inference(negUnitSimplification, [status(thm)], [c_56, c_1870])).
% 8.91/3.13  tff(c_1776, plain, (![A_161]: (m1_subset_1('#skF_1'(A_161), u1_struct_0('#skF_3')) | ~m1_pre_topc(A_161, '#skF_3') | ~v7_struct_0(A_161) | ~l1_struct_0(A_161) | v2_struct_0(A_161))), inference(negUnitSimplification, [status(thm)], [c_56, c_1775])).
% 8.91/3.13  tff(c_159, plain, (![A_76, B_77]: (m1_pre_topc(k1_tex_2(A_76, B_77), A_76) | ~m1_subset_1(B_77, u1_struct_0(A_76)) | ~l1_pre_topc(A_76) | v2_struct_0(A_76))), inference(cnfTransformation, [status(thm)], [f_156])).
% 8.91/3.13  tff(c_162, plain, (![A_29]: (m1_pre_topc(k1_tex_2(A_29, '#skF_1'(A_29)), A_29) | ~l1_pre_topc(A_29) | ~v7_struct_0(A_29) | ~l1_struct_0(A_29) | v2_struct_0(A_29))), inference(resolution, [status(thm)], [c_38, c_159])).
% 8.91/3.13  tff(c_333, plain, (![A_108, B_109]: (k6_domain_1(u1_struct_0(A_108), B_109)=u1_struct_0(k1_tex_2(A_108, B_109)) | ~m1_pre_topc(k1_tex_2(A_108, B_109), A_108) | ~v1_pre_topc(k1_tex_2(A_108, B_109)) | v2_struct_0(k1_tex_2(A_108, B_109)) | ~m1_subset_1(B_109, u1_struct_0(A_108)) | ~l1_pre_topc(A_108) | v2_struct_0(A_108))), inference(cnfTransformation, [status(thm)], [f_142])).
% 8.91/3.13  tff(c_2017, plain, (![A_173]: (k6_domain_1(u1_struct_0(A_173), '#skF_1'(A_173))=u1_struct_0(k1_tex_2(A_173, '#skF_1'(A_173))) | ~v1_pre_topc(k1_tex_2(A_173, '#skF_1'(A_173))) | v2_struct_0(k1_tex_2(A_173, '#skF_1'(A_173))) | ~m1_subset_1('#skF_1'(A_173), u1_struct_0(A_173)) | ~l1_pre_topc(A_173) | ~v7_struct_0(A_173) | ~l1_struct_0(A_173) | v2_struct_0(A_173))), inference(resolution, [status(thm)], [c_162, c_333])).
% 8.91/3.13  tff(c_2021, plain, (k6_domain_1(u1_struct_0('#skF_3'), '#skF_1'('#skF_3'))=u1_struct_0(k1_tex_2('#skF_3', '#skF_1'('#skF_3'))) | ~v1_pre_topc(k1_tex_2('#skF_3', '#skF_1'('#skF_3'))) | v2_struct_0(k1_tex_2('#skF_3', '#skF_1'('#skF_3'))) | ~l1_pre_topc('#skF_3') | ~m1_pre_topc('#skF_3', '#skF_3') | ~v7_struct_0('#skF_3') | ~l1_struct_0('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_1776, c_2017])).
% 8.91/3.13  tff(c_2041, plain, (k6_domain_1(u1_struct_0('#skF_3'), '#skF_1'('#skF_3'))=u1_struct_0(k1_tex_2('#skF_3', '#skF_1'('#skF_3'))) | ~v1_pre_topc(k1_tex_2('#skF_3', '#skF_1'('#skF_3'))) | v2_struct_0(k1_tex_2('#skF_3', '#skF_1'('#skF_3'))) | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_808, c_54, c_504, c_85, c_2021])).
% 8.91/3.13  tff(c_2042, plain, (k6_domain_1(u1_struct_0('#skF_3'), '#skF_1'('#skF_3'))=u1_struct_0(k1_tex_2('#skF_3', '#skF_1'('#skF_3'))) | ~v1_pre_topc(k1_tex_2('#skF_3', '#skF_1'('#skF_3'))) | v2_struct_0(k1_tex_2('#skF_3', '#skF_1'('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_56, c_2041])).
% 8.91/3.13  tff(c_2277, plain, (~v1_pre_topc(k1_tex_2('#skF_3', '#skF_1'('#skF_3')))), inference(splitLeft, [status(thm)], [c_2042])).
% 8.91/3.13  tff(c_2280, plain, (~m1_pre_topc('#skF_3', '#skF_3') | ~v7_struct_0('#skF_3') | ~l1_struct_0('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_1871, c_2277])).
% 8.91/3.13  tff(c_2292, plain, (v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_808, c_54, c_504, c_2280])).
% 8.91/3.13  tff(c_2294, plain, $false, inference(negUnitSimplification, [status(thm)], [c_56, c_2292])).
% 8.91/3.13  tff(c_2295, plain, (v2_struct_0(k1_tex_2('#skF_3', '#skF_1'('#skF_3'))) | k6_domain_1(u1_struct_0('#skF_3'), '#skF_1'('#skF_3'))=u1_struct_0(k1_tex_2('#skF_3', '#skF_1'('#skF_3')))), inference(splitRight, [status(thm)], [c_2042])).
% 8.91/3.13  tff(c_2303, plain, (k6_domain_1(u1_struct_0('#skF_3'), '#skF_1'('#skF_3'))=u1_struct_0(k1_tex_2('#skF_3', '#skF_1'('#skF_3')))), inference(splitLeft, [status(thm)], [c_2295])).
% 8.91/3.13  tff(c_2321, plain, (u1_struct_0(k1_tex_2('#skF_3', '#skF_1'('#skF_3')))=u1_struct_0('#skF_3') | ~v7_struct_0('#skF_3') | ~l1_struct_0('#skF_3') | v2_struct_0('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_2303, c_36])).
% 8.91/3.13  tff(c_2352, plain, (u1_struct_0(k1_tex_2('#skF_3', '#skF_1'('#skF_3')))=u1_struct_0('#skF_3') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_808, c_54, c_2321])).
% 8.91/3.13  tff(c_2353, plain, (u1_struct_0(k1_tex_2('#skF_3', '#skF_1'('#skF_3')))=u1_struct_0('#skF_3')), inference(negUnitSimplification, [status(thm)], [c_56, c_2352])).
% 8.91/3.13  tff(c_191, plain, (![A_84]: (m1_pre_topc(k1_tex_2(A_84, '#skF_1'(A_84)), A_84) | ~l1_pre_topc(A_84) | ~v7_struct_0(A_84) | ~l1_struct_0(A_84) | v2_struct_0(A_84))), inference(resolution, [status(thm)], [c_38, c_159])).
% 8.91/3.13  tff(c_131, plain, (![B_68, A_69]: (l1_pre_topc(g1_pre_topc(u1_struct_0(B_68), u1_pre_topc(B_68))) | ~m1_pre_topc(B_68, A_69) | ~l1_pre_topc(A_69))), inference(resolution, [status(thm)], [c_124, c_12])).
% 8.91/3.13  tff(c_204, plain, (![A_84]: (l1_pre_topc(g1_pre_topc(u1_struct_0(k1_tex_2(A_84, '#skF_1'(A_84))), u1_pre_topc(k1_tex_2(A_84, '#skF_1'(A_84))))) | ~l1_pre_topc(A_84) | ~v7_struct_0(A_84) | ~l1_struct_0(A_84) | v2_struct_0(A_84))), inference(resolution, [status(thm)], [c_191, c_131])).
% 8.91/3.13  tff(c_2442, plain, (l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc(k1_tex_2('#skF_3', '#skF_1'('#skF_3'))))) | ~l1_pre_topc('#skF_3') | ~v7_struct_0('#skF_3') | ~l1_struct_0('#skF_3') | v2_struct_0('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_2353, c_204])).
% 8.91/3.13  tff(c_2561, plain, (l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc(k1_tex_2('#skF_3', '#skF_1'('#skF_3'))))) | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_808, c_54, c_85, c_2442])).
% 8.91/3.13  tff(c_2562, plain, (l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc(k1_tex_2('#skF_3', '#skF_1'('#skF_3')))))), inference(negUnitSimplification, [status(thm)], [c_56, c_2561])).
% 8.91/3.13  tff(c_503, plain, (u1_struct_0(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3')))=u1_struct_0('#skF_3')), inference(splitRight, [status(thm)], [c_468])).
% 8.91/3.13  tff(c_14, plain, (![A_8]: (v1_xboole_0(u1_struct_0(A_8)) | ~l1_struct_0(A_8) | ~v2_struct_0(A_8))), inference(cnfTransformation, [status(thm)], [f_50])).
% 8.91/3.13  tff(c_630, plain, (v1_xboole_0(u1_struct_0('#skF_3')) | ~l1_struct_0(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))) | ~v2_struct_0(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_503, c_14])).
% 8.91/3.13  tff(c_1018, plain, (~v2_struct_0(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3')))), inference(splitLeft, [status(thm)], [c_630])).
% 8.91/3.13  tff(c_16, plain, (![A_9]: (~v1_xboole_0(u1_struct_0(A_9)) | ~l1_struct_0(A_9) | v2_struct_0(A_9))), inference(cnfTransformation, [status(thm)], [f_58])).
% 8.91/3.13  tff(c_627, plain, (~v1_xboole_0(u1_struct_0('#skF_3')) | ~l1_struct_0(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))) | v2_struct_0(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_503, c_16])).
% 8.91/3.13  tff(c_1019, plain, (~v1_xboole_0(u1_struct_0('#skF_3')) | ~l1_struct_0(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_1018, c_627])).
% 8.91/3.13  tff(c_1020, plain, (~l1_struct_0(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3')))), inference(splitLeft, [status(thm)], [c_1019])).
% 8.91/3.13  tff(c_1023, plain, (~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3')))), inference(resolution, [status(thm)], [c_10, c_1020])).
% 8.91/3.13  tff(c_1027, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_143, c_1023])).
% 8.91/3.13  tff(c_1028, plain, (~v1_xboole_0(u1_struct_0('#skF_3'))), inference(splitRight, [status(thm)], [c_1019])).
% 8.91/3.13  tff(c_104, plain, (![B_62, A_63]: (v1_pre_topc(g1_pre_topc(u1_struct_0(B_62), u1_pre_topc(B_62))) | ~m1_pre_topc(B_62, A_63) | ~l1_pre_topc(A_63))), inference(cnfTransformation, [status(thm)], [f_99])).
% 8.91/3.13  tff(c_108, plain, (v1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))) | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_52, c_104])).
% 8.91/3.13  tff(c_112, plain, (v1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_108])).
% 8.91/3.13  tff(c_173, plain, (![B_79]: (m1_pre_topc(g1_pre_topc(u1_struct_0(B_79), u1_pre_topc(B_79)), B_79) | ~l1_pre_topc(B_79) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(B_79), u1_pre_topc(B_79))))), inference(resolution, [status(thm)], [c_30, c_163])).
% 8.91/3.13  tff(c_1842, plain, (![A_167, A_10]: (m1_subset_1('#skF_1'(A_167), u1_struct_0(A_10)) | ~m1_pre_topc('#skF_3', A_10) | v2_struct_0('#skF_3') | ~l1_pre_topc(A_10) | v2_struct_0(A_10) | ~m1_pre_topc(A_167, '#skF_3') | ~v7_struct_0(A_167) | ~l1_struct_0(A_167) | v2_struct_0(A_167))), inference(resolution, [status(thm)], [c_1840, c_18])).
% 8.91/3.13  tff(c_1859, plain, (![A_167, A_10]: (m1_subset_1('#skF_1'(A_167), u1_struct_0(A_10)) | ~m1_pre_topc('#skF_3', A_10) | ~l1_pre_topc(A_10) | v2_struct_0(A_10) | ~m1_pre_topc(A_167, '#skF_3') | ~v7_struct_0(A_167) | ~l1_struct_0(A_167) | v2_struct_0(A_167))), inference(negUnitSimplification, [status(thm)], [c_56, c_1842])).
% 8.91/3.13  tff(c_2367, plain, (k6_domain_1(u1_struct_0('#skF_3'), '#skF_1'('#skF_3'))=u1_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2353, c_2303])).
% 8.91/3.13  tff(c_40, plain, (![A_33, B_37, C_39]: (k1_tex_2(A_33, B_37)=C_39 | u1_struct_0(C_39)!=k6_domain_1(u1_struct_0(A_33), B_37) | ~m1_pre_topc(C_39, A_33) | ~v1_pre_topc(C_39) | v2_struct_0(C_39) | ~m1_subset_1(B_37, u1_struct_0(A_33)) | ~l1_pre_topc(A_33) | v2_struct_0(A_33))), inference(cnfTransformation, [status(thm)], [f_142])).
% 8.91/3.13  tff(c_2617, plain, (![C_39]: (k1_tex_2('#skF_3', '#skF_1'('#skF_3'))=C_39 | u1_struct_0(C_39)!=u1_struct_0('#skF_3') | ~m1_pre_topc(C_39, '#skF_3') | ~v1_pre_topc(C_39) | v2_struct_0(C_39) | ~m1_subset_1('#skF_1'('#skF_3'), u1_struct_0('#skF_3')) | ~l1_pre_topc('#skF_3') | v2_struct_0('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_2367, c_40])).
% 8.91/3.13  tff(c_2649, plain, (![C_39]: (k1_tex_2('#skF_3', '#skF_1'('#skF_3'))=C_39 | u1_struct_0(C_39)!=u1_struct_0('#skF_3') | ~m1_pre_topc(C_39, '#skF_3') | ~v1_pre_topc(C_39) | v2_struct_0(C_39) | ~m1_subset_1('#skF_1'('#skF_3'), u1_struct_0('#skF_3')) | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_85, c_2617])).
% 8.91/3.13  tff(c_2650, plain, (![C_39]: (k1_tex_2('#skF_3', '#skF_1'('#skF_3'))=C_39 | u1_struct_0(C_39)!=u1_struct_0('#skF_3') | ~m1_pre_topc(C_39, '#skF_3') | ~v1_pre_topc(C_39) | v2_struct_0(C_39) | ~m1_subset_1('#skF_1'('#skF_3'), u1_struct_0('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_56, c_2649])).
% 8.91/3.13  tff(c_3544, plain, (~m1_subset_1('#skF_1'('#skF_3'), u1_struct_0('#skF_3'))), inference(splitLeft, [status(thm)], [c_2650])).
% 8.91/3.13  tff(c_3547, plain, (~l1_pre_topc('#skF_3') | ~m1_pre_topc('#skF_3', '#skF_3') | ~v7_struct_0('#skF_3') | ~l1_struct_0('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_1859, c_3544])).
% 8.91/3.13  tff(c_3562, plain, (v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_808, c_54, c_504, c_85, c_3547])).
% 8.91/3.13  tff(c_3564, plain, $false, inference(negUnitSimplification, [status(thm)], [c_56, c_3562])).
% 8.91/3.13  tff(c_3967, plain, (![C_213]: (k1_tex_2('#skF_3', '#skF_1'('#skF_3'))=C_213 | u1_struct_0(C_213)!=u1_struct_0('#skF_3') | ~m1_pre_topc(C_213, '#skF_3') | ~v1_pre_topc(C_213) | v2_struct_0(C_213))), inference(splitRight, [status(thm)], [c_2650])).
% 8.91/3.13  tff(c_3993, plain, (g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))=k1_tex_2('#skF_3', '#skF_1'('#skF_3')) | u1_struct_0(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3')))!=u1_struct_0('#skF_3') | ~v1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))) | v2_struct_0(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))) | ~l1_pre_topc('#skF_3') | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3')))), inference(resolution, [status(thm)], [c_173, c_3967])).
% 8.91/3.13  tff(c_4034, plain, (g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))=k1_tex_2('#skF_3', '#skF_1'('#skF_3')) | v2_struct_0(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_143, c_85, c_112, c_503, c_3993])).
% 8.91/3.13  tff(c_4035, plain, (g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))=k1_tex_2('#skF_3', '#skF_1'('#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_1018, c_4034])).
% 8.91/3.13  tff(c_4138, plain, (![A_17]: (m1_pre_topc(A_17, k1_tex_2('#skF_3', '#skF_1'('#skF_3'))) | ~m1_pre_topc(A_17, '#skF_3') | ~l1_pre_topc('#skF_3') | ~l1_pre_topc(A_17))), inference(superposition, [status(thm), theory('equality')], [c_4035, c_22])).
% 8.91/3.13  tff(c_4199, plain, (![A_17]: (m1_pre_topc(A_17, k1_tex_2('#skF_3', '#skF_1'('#skF_3'))) | ~m1_pre_topc(A_17, '#skF_3') | ~l1_pre_topc(A_17))), inference(demodulation, [status(thm), theory('equality')], [c_85, c_4138])).
% 8.91/3.13  tff(c_26, plain, (![B_24, A_22]: (m1_pre_topc(g1_pre_topc(u1_struct_0(B_24), u1_pre_topc(B_24)), A_22) | ~m1_pre_topc(B_24, A_22) | ~l1_pre_topc(A_22))), inference(cnfTransformation, [status(thm)], [f_99])).
% 8.91/3.13  tff(c_342, plain, (![B_111, A_112]: (l1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(B_111), u1_pre_topc(B_111))), u1_pre_topc(g1_pre_topc(u1_struct_0(B_111), u1_pre_topc(B_111))))) | ~m1_pre_topc(B_111, A_112) | ~l1_pre_topc(A_112))), inference(resolution, [status(thm)], [c_26, c_132])).
% 8.91/3.13  tff(c_354, plain, (l1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))), u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))))) | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_52, c_342])).
% 8.91/3.13  tff(c_362, plain, (l1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))), u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3')))))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_354])).
% 8.91/3.13  tff(c_537, plain, (l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3')))))), inference(demodulation, [status(thm), theory('equality')], [c_503, c_362])).
% 8.91/3.13  tff(c_20, plain, (![A_17, B_19]: (m1_pre_topc(A_17, B_19) | ~m1_pre_topc(A_17, g1_pre_topc(u1_struct_0(B_19), u1_pre_topc(B_19))) | ~l1_pre_topc(B_19) | ~l1_pre_topc(A_17))), inference(cnfTransformation, [status(thm)], [f_83])).
% 8.91/3.13  tff(c_595, plain, (![A_17]: (m1_pre_topc(A_17, g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))) | ~m1_pre_topc(A_17, g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))) | ~l1_pre_topc(A_17))), inference(superposition, [status(thm), theory('equality')], [c_503, c_20])).
% 8.91/3.13  tff(c_1519, plain, (![A_157]: (m1_pre_topc(A_157, g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))) | ~m1_pre_topc(A_157, g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))))) | ~l1_pre_topc(A_157))), inference(demodulation, [status(thm), theory('equality')], [c_143, c_595])).
% 8.91/3.13  tff(c_1546, plain, (m1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3')))), g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3')))))), inference(resolution, [status(thm)], [c_30, c_1519])).
% 8.91/3.13  tff(c_1565, plain, (m1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3')))), g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_537, c_1546])).
% 8.91/3.13  tff(c_1584, plain, (m1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3')))), '#skF_3') | ~l1_pre_topc('#skF_3') | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3')))))), inference(resolution, [status(thm)], [c_1565, c_20])).
% 8.91/3.13  tff(c_1613, plain, (m1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3')))), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_537, c_85, c_1584])).
% 8.91/3.13  tff(c_4049, plain, (m1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc(k1_tex_2('#skF_3', '#skF_1'('#skF_3')))), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_4035, c_1613])).
% 8.91/3.13  tff(c_592, plain, (![A_17]: (m1_pre_topc(A_17, g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))))) | ~m1_pre_topc(A_17, g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))) | ~l1_pre_topc(A_17))), inference(superposition, [status(thm), theory('equality')], [c_503, c_22])).
% 8.91/3.13  tff(c_665, plain, (![A_17]: (m1_pre_topc(A_17, g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))))) | ~m1_pre_topc(A_17, g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))) | ~l1_pre_topc(A_17))), inference(demodulation, [status(thm), theory('equality')], [c_143, c_592])).
% 8.91/3.13  tff(c_5712, plain, (![A_230]: (m1_pre_topc(A_230, g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc(k1_tex_2('#skF_3', '#skF_1'('#skF_3'))))) | ~m1_pre_topc(A_230, k1_tex_2('#skF_3', '#skF_1'('#skF_3'))) | ~l1_pre_topc(A_230))), inference(demodulation, [status(thm), theory('equality')], [c_4035, c_4035, c_665])).
% 8.91/3.13  tff(c_624, plain, (![B_28]: (r1_tarski(u1_struct_0(B_28), u1_struct_0('#skF_3')) | ~m1_pre_topc(B_28, g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))))), inference(superposition, [status(thm), theory('equality')], [c_503, c_32])).
% 8.91/3.13  tff(c_718, plain, (![B_130]: (r1_tarski(u1_struct_0(B_130), u1_struct_0('#skF_3')) | ~m1_pre_topc(B_130, g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_143, c_624])).
% 8.91/3.13  tff(c_734, plain, (![A_17]: (r1_tarski(u1_struct_0(A_17), u1_struct_0('#skF_3')) | ~m1_pre_topc(A_17, '#skF_3') | ~l1_pre_topc('#skF_3') | ~l1_pre_topc(A_17))), inference(resolution, [status(thm)], [c_22, c_718])).
% 8.91/3.13  tff(c_761, plain, (![A_131]: (r1_tarski(u1_struct_0(A_131), u1_struct_0('#skF_3')) | ~m1_pre_topc(A_131, '#skF_3') | ~l1_pre_topc(A_131))), inference(demodulation, [status(thm), theory('equality')], [c_85, c_734])).
% 8.91/3.13  tff(c_102, plain, (![B_58, A_59]: (u1_struct_0(B_58)=u1_struct_0(A_59) | ~r1_tarski(u1_struct_0(A_59), u1_struct_0(B_58)) | ~m1_pre_topc(B_58, A_59) | ~l1_pre_topc(A_59))), inference(resolution, [status(thm)], [c_99, c_2])).
% 8.91/3.13  tff(c_770, plain, (![A_131]: (u1_struct_0(A_131)=u1_struct_0('#skF_3') | ~m1_pre_topc('#skF_3', A_131) | ~m1_pre_topc(A_131, '#skF_3') | ~l1_pre_topc(A_131))), inference(resolution, [status(thm)], [c_761, c_102])).
% 8.91/3.13  tff(c_5730, plain, (u1_struct_0(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc(k1_tex_2('#skF_3', '#skF_1'('#skF_3')))))=u1_struct_0('#skF_3') | ~m1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc(k1_tex_2('#skF_3', '#skF_1'('#skF_3')))), '#skF_3') | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc(k1_tex_2('#skF_3', '#skF_1'('#skF_3'))))) | ~m1_pre_topc('#skF_3', k1_tex_2('#skF_3', '#skF_1'('#skF_3'))) | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_5712, c_770])).
% 8.91/3.13  tff(c_5769, plain, (u1_struct_0(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc(k1_tex_2('#skF_3', '#skF_1'('#skF_3')))))=u1_struct_0('#skF_3') | ~m1_pre_topc('#skF_3', k1_tex_2('#skF_3', '#skF_1'('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_85, c_2562, c_4049, c_5730])).
% 8.91/3.13  tff(c_5797, plain, (~m1_pre_topc('#skF_3', k1_tex_2('#skF_3', '#skF_1'('#skF_3')))), inference(splitLeft, [status(thm)], [c_5769])).
% 8.91/3.13  tff(c_5908, plain, (~m1_pre_topc('#skF_3', '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_4199, c_5797])).
% 8.91/3.13  tff(c_5915, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_85, c_504, c_5908])).
% 8.91/3.13  tff(c_5916, plain, (u1_struct_0(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc(k1_tex_2('#skF_3', '#skF_1'('#skF_3')))))=u1_struct_0('#skF_3')), inference(splitRight, [status(thm)], [c_5769])).
% 8.91/3.13  tff(c_6195, plain, (v1_xboole_0(u1_struct_0('#skF_3')) | ~l1_struct_0(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc(k1_tex_2('#skF_3', '#skF_1'('#skF_3'))))) | ~v2_struct_0(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc(k1_tex_2('#skF_3', '#skF_1'('#skF_3')))))), inference(superposition, [status(thm), theory('equality')], [c_5916, c_14])).
% 8.91/3.13  tff(c_6320, plain, (~l1_struct_0(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc(k1_tex_2('#skF_3', '#skF_1'('#skF_3'))))) | ~v2_struct_0(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc(k1_tex_2('#skF_3', '#skF_1'('#skF_3')))))), inference(negUnitSimplification, [status(thm)], [c_1028, c_6195])).
% 8.91/3.13  tff(c_7194, plain, (~v2_struct_0(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc(k1_tex_2('#skF_3', '#skF_1'('#skF_3')))))), inference(splitLeft, [status(thm)], [c_6320])).
% 8.91/3.13  tff(c_2524, plain, (v1_xboole_0(u1_struct_0('#skF_3')) | ~l1_struct_0(k1_tex_2('#skF_3', '#skF_1'('#skF_3'))) | ~v2_struct_0(k1_tex_2('#skF_3', '#skF_1'('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_2353, c_14])).
% 8.91/3.13  tff(c_2581, plain, (~l1_struct_0(k1_tex_2('#skF_3', '#skF_1'('#skF_3'))) | ~v2_struct_0(k1_tex_2('#skF_3', '#skF_1'('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_1028, c_2524])).
% 8.91/3.13  tff(c_2747, plain, (~v2_struct_0(k1_tex_2('#skF_3', '#skF_1'('#skF_3')))), inference(splitLeft, [status(thm)], [c_2581])).
% 8.91/3.13  tff(c_2296, plain, (v1_pre_topc(k1_tex_2('#skF_3', '#skF_1'('#skF_3')))), inference(splitRight, [status(thm)], [c_2042])).
% 8.91/3.13  tff(c_4147, plain, (![A_22]: (m1_pre_topc(k1_tex_2('#skF_3', '#skF_1'('#skF_3')), A_22) | ~m1_pre_topc('#skF_3', A_22) | ~l1_pre_topc(A_22))), inference(superposition, [status(thm), theory('equality')], [c_4035, c_26])).
% 8.91/3.13  tff(c_60, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_175])).
% 8.91/3.13  tff(c_3566, plain, (m1_subset_1('#skF_1'('#skF_3'), u1_struct_0('#skF_3'))), inference(splitRight, [status(thm)], [c_2650])).
% 8.91/3.13  tff(c_3571, plain, (![A_10]: (m1_subset_1('#skF_1'('#skF_3'), u1_struct_0(A_10)) | ~m1_pre_topc('#skF_3', A_10) | v2_struct_0('#skF_3') | ~l1_pre_topc(A_10) | v2_struct_0(A_10))), inference(resolution, [status(thm)], [c_3566, c_18])).
% 8.91/3.13  tff(c_3686, plain, (![A_205]: (m1_subset_1('#skF_1'('#skF_3'), u1_struct_0(A_205)) | ~m1_pre_topc('#skF_3', A_205) | ~l1_pre_topc(A_205) | v2_struct_0(A_205))), inference(negUnitSimplification, [status(thm)], [c_56, c_3571])).
% 8.91/3.13  tff(c_7203, plain, (![A_243, A_244]: (m1_subset_1('#skF_1'('#skF_3'), u1_struct_0(A_243)) | ~m1_pre_topc(A_244, A_243) | ~l1_pre_topc(A_243) | v2_struct_0(A_243) | ~m1_pre_topc('#skF_3', A_244) | ~l1_pre_topc(A_244) | v2_struct_0(A_244))), inference(resolution, [status(thm)], [c_3686, c_18])).
% 8.91/3.13  tff(c_7251, plain, (m1_subset_1('#skF_1'('#skF_3'), u1_struct_0('#skF_2')) | ~l1_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~m1_pre_topc('#skF_3', '#skF_3') | ~l1_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_52, c_7203])).
% 8.91/3.13  tff(c_7319, plain, (m1_subset_1('#skF_1'('#skF_3'), u1_struct_0('#skF_2')) | v2_struct_0('#skF_2') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_85, c_504, c_58, c_7251])).
% 8.91/3.13  tff(c_7320, plain, (m1_subset_1('#skF_1'('#skF_3'), u1_struct_0('#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_56, c_60, c_7319])).
% 8.91/3.13  tff(c_1036, plain, (![A_138]: (k1_tex_2(A_138, '#skF_1'(A_138))=A_138 | ~v1_pre_topc(A_138) | ~m1_subset_1('#skF_1'(A_138), u1_struct_0(A_138)) | ~v7_struct_0(A_138) | ~l1_struct_0(A_138) | v2_struct_0(A_138) | ~l1_pre_topc(A_138))), inference(resolution, [status(thm)], [c_30, c_686])).
% 8.91/3.13  tff(c_1055, plain, (![A_139]: (k1_tex_2(A_139, '#skF_1'(A_139))=A_139 | ~v1_pre_topc(A_139) | ~l1_pre_topc(A_139) | ~v7_struct_0(A_139) | ~l1_struct_0(A_139) | v2_struct_0(A_139))), inference(resolution, [status(thm)], [c_38, c_1036])).
% 8.91/3.13  tff(c_50, plain, (![C_46]: (g1_pre_topc(u1_struct_0(k1_tex_2('#skF_2', C_46)), u1_pre_topc(k1_tex_2('#skF_2', C_46)))!=g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3')) | ~m1_subset_1(C_46, u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_175])).
% 8.91/3.13  tff(c_1100, plain, (g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc(k1_tex_2('#skF_2', '#skF_1'('#skF_2'))))!=g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3')) | ~m1_subset_1('#skF_1'('#skF_2'), u1_struct_0('#skF_2')) | ~v1_pre_topc('#skF_2') | ~l1_pre_topc('#skF_2') | ~v7_struct_0('#skF_2') | ~l1_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_1055, c_50])).
% 8.91/3.13  tff(c_1110, plain, (g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc(k1_tex_2('#skF_2', '#skF_1'('#skF_2'))))!=g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3')) | ~m1_subset_1('#skF_1'('#skF_2'), u1_struct_0('#skF_2')) | ~v1_pre_topc('#skF_2') | ~v7_struct_0('#skF_2') | ~l1_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_1100])).
% 8.91/3.13  tff(c_1111, plain, (g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc(k1_tex_2('#skF_2', '#skF_1'('#skF_2'))))!=g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3')) | ~m1_subset_1('#skF_1'('#skF_2'), u1_struct_0('#skF_2')) | ~v1_pre_topc('#skF_2') | ~v7_struct_0('#skF_2') | ~l1_struct_0('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_60, c_1110])).
% 8.91/3.13  tff(c_1161, plain, (~l1_struct_0('#skF_2')), inference(splitLeft, [status(thm)], [c_1111])).
% 8.91/3.13  tff(c_1164, plain, (~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_10, c_1161])).
% 8.91/3.13  tff(c_1168, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_58, c_1164])).
% 8.91/3.13  tff(c_1170, plain, (l1_struct_0('#skF_2')), inference(splitRight, [status(thm)], [c_1111])).
% 8.91/3.13  tff(c_1758, plain, (![A_161]: (m1_subset_1('#skF_1'(A_161), u1_struct_0('#skF_2')) | ~l1_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~m1_pre_topc(A_161, '#skF_3') | ~l1_pre_topc('#skF_3') | v2_struct_0('#skF_3') | ~v7_struct_0(A_161) | ~l1_struct_0(A_161) | v2_struct_0(A_161))), inference(resolution, [status(thm)], [c_52, c_1734])).
% 8.91/3.13  tff(c_1785, plain, (![A_161]: (m1_subset_1('#skF_1'(A_161), u1_struct_0('#skF_2')) | v2_struct_0('#skF_2') | ~m1_pre_topc(A_161, '#skF_3') | v2_struct_0('#skF_3') | ~v7_struct_0(A_161) | ~l1_struct_0(A_161) | v2_struct_0(A_161))), inference(demodulation, [status(thm), theory('equality')], [c_85, c_58, c_1758])).
% 8.91/3.13  tff(c_1787, plain, (![A_164]: (m1_subset_1('#skF_1'(A_164), u1_struct_0('#skF_2')) | ~m1_pre_topc(A_164, '#skF_3') | ~v7_struct_0(A_164) | ~l1_struct_0(A_164) | v2_struct_0(A_164))), inference(negUnitSimplification, [status(thm)], [c_56, c_60, c_1785])).
% 8.91/3.13  tff(c_24, plain, (![A_20, B_21]: (k6_domain_1(A_20, B_21)=k1_tarski(B_21) | ~m1_subset_1(B_21, A_20) | v1_xboole_0(A_20))), inference(cnfTransformation, [status(thm)], [f_90])).
% 8.91/3.13  tff(c_1823, plain, (![A_164]: (k6_domain_1(u1_struct_0('#skF_2'), '#skF_1'(A_164))=k1_tarski('#skF_1'(A_164)) | v1_xboole_0(u1_struct_0('#skF_2')) | ~m1_pre_topc(A_164, '#skF_3') | ~v7_struct_0(A_164) | ~l1_struct_0(A_164) | v2_struct_0(A_164))), inference(resolution, [status(thm)], [c_1787, c_24])).
% 8.91/3.13  tff(c_2167, plain, (v1_xboole_0(u1_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_1823])).
% 8.91/3.13  tff(c_2170, plain, (~l1_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_2167, c_16])).
% 8.91/3.13  tff(c_2173, plain, (v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1170, c_2170])).
% 8.91/3.13  tff(c_2175, plain, $false, inference(negUnitSimplification, [status(thm)], [c_60, c_2173])).
% 8.91/3.13  tff(c_2177, plain, (~v1_xboole_0(u1_struct_0('#skF_2'))), inference(splitRight, [status(thm)], [c_1823])).
% 8.91/3.13  tff(c_1856, plain, (![A_167]: (k6_domain_1(u1_struct_0('#skF_3'), '#skF_1'(A_167))=k1_tarski('#skF_1'(A_167)) | v1_xboole_0(u1_struct_0('#skF_3')) | ~m1_pre_topc(A_167, '#skF_3') | ~v7_struct_0(A_167) | ~l1_struct_0(A_167) | v2_struct_0(A_167))), inference(resolution, [status(thm)], [c_1840, c_24])).
% 8.91/3.13  tff(c_2083, plain, (![A_176]: (k6_domain_1(u1_struct_0('#skF_3'), '#skF_1'(A_176))=k1_tarski('#skF_1'(A_176)) | ~m1_pre_topc(A_176, '#skF_3') | ~v7_struct_0(A_176) | ~l1_struct_0(A_176) | v2_struct_0(A_176))), inference(negUnitSimplification, [status(thm)], [c_1028, c_1856])).
% 8.91/3.13  tff(c_2102, plain, (k1_tarski('#skF_1'('#skF_3'))=u1_struct_0('#skF_3') | ~v7_struct_0('#skF_3') | ~l1_struct_0('#skF_3') | v2_struct_0('#skF_3') | ~m1_pre_topc('#skF_3', '#skF_3') | ~v7_struct_0('#skF_3') | ~l1_struct_0('#skF_3') | v2_struct_0('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_2083, c_36])).
% 8.91/3.13  tff(c_2134, plain, (k1_tarski('#skF_1'('#skF_3'))=u1_struct_0('#skF_3') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_808, c_54, c_504, c_808, c_54, c_2102])).
% 8.91/3.13  tff(c_2135, plain, (k1_tarski('#skF_1'('#skF_3'))=u1_struct_0('#skF_3')), inference(negUnitSimplification, [status(thm)], [c_56, c_2134])).
% 8.91/3.13  tff(c_7336, plain, (k6_domain_1(u1_struct_0('#skF_2'), '#skF_1'('#skF_3'))=k1_tarski('#skF_1'('#skF_3')) | v1_xboole_0(u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_7320, c_24])).
% 8.91/3.13  tff(c_7357, plain, (k6_domain_1(u1_struct_0('#skF_2'), '#skF_1'('#skF_3'))=u1_struct_0('#skF_3') | v1_xboole_0(u1_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_2135, c_7336])).
% 8.91/3.13  tff(c_7358, plain, (k6_domain_1(u1_struct_0('#skF_2'), '#skF_1'('#skF_3'))=u1_struct_0('#skF_3')), inference(negUnitSimplification, [status(thm)], [c_2177, c_7357])).
% 8.91/3.13  tff(c_7488, plain, (![C_39]: (k1_tex_2('#skF_2', '#skF_1'('#skF_3'))=C_39 | u1_struct_0(C_39)!=u1_struct_0('#skF_3') | ~m1_pre_topc(C_39, '#skF_2') | ~v1_pre_topc(C_39) | v2_struct_0(C_39) | ~m1_subset_1('#skF_1'('#skF_3'), u1_struct_0('#skF_2')) | ~l1_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_7358, c_40])).
% 8.91/3.13  tff(c_7520, plain, (![C_39]: (k1_tex_2('#skF_2', '#skF_1'('#skF_3'))=C_39 | u1_struct_0(C_39)!=u1_struct_0('#skF_3') | ~m1_pre_topc(C_39, '#skF_2') | ~v1_pre_topc(C_39) | v2_struct_0(C_39) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_7320, c_7488])).
% 8.91/3.13  tff(c_8657, plain, (![C_258]: (k1_tex_2('#skF_2', '#skF_1'('#skF_3'))=C_258 | u1_struct_0(C_258)!=u1_struct_0('#skF_3') | ~m1_pre_topc(C_258, '#skF_2') | ~v1_pre_topc(C_258) | v2_struct_0(C_258))), inference(negUnitSimplification, [status(thm)], [c_60, c_7520])).
% 8.91/3.13  tff(c_8674, plain, (k1_tex_2('#skF_2', '#skF_1'('#skF_3'))=k1_tex_2('#skF_3', '#skF_1'('#skF_3')) | u1_struct_0(k1_tex_2('#skF_3', '#skF_1'('#skF_3')))!=u1_struct_0('#skF_3') | ~v1_pre_topc(k1_tex_2('#skF_3', '#skF_1'('#skF_3'))) | v2_struct_0(k1_tex_2('#skF_3', '#skF_1'('#skF_3'))) | ~m1_pre_topc('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_4147, c_8657])).
% 8.91/3.13  tff(c_8724, plain, (k1_tex_2('#skF_2', '#skF_1'('#skF_3'))=k1_tex_2('#skF_3', '#skF_1'('#skF_3')) | v2_struct_0(k1_tex_2('#skF_3', '#skF_1'('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_52, c_2296, c_2353, c_8674])).
% 8.91/3.13  tff(c_8725, plain, (k1_tex_2('#skF_2', '#skF_1'('#skF_3'))=k1_tex_2('#skF_3', '#skF_1'('#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_2747, c_8724])).
% 8.91/3.13  tff(c_48, plain, (![A_40, B_41]: (~v2_struct_0(k1_tex_2(A_40, B_41)) | ~m1_subset_1(B_41, u1_struct_0(A_40)) | ~l1_pre_topc(A_40) | v2_struct_0(A_40))), inference(cnfTransformation, [status(thm)], [f_156])).
% 8.91/3.13  tff(c_7333, plain, (~v2_struct_0(k1_tex_2('#skF_2', '#skF_1'('#skF_3'))) | ~l1_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_7320, c_48])).
% 8.91/3.13  tff(c_7354, plain, (~v2_struct_0(k1_tex_2('#skF_2', '#skF_1'('#skF_3'))) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_7333])).
% 8.91/3.13  tff(c_7355, plain, (~v2_struct_0(k1_tex_2('#skF_2', '#skF_1'('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_60, c_7354])).
% 8.91/3.13  tff(c_7330, plain, (v1_pre_topc(k1_tex_2('#skF_2', '#skF_1'('#skF_3'))) | ~l1_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_7320, c_46])).
% 8.91/3.13  tff(c_7350, plain, (v1_pre_topc(k1_tex_2('#skF_2', '#skF_1'('#skF_3'))) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_7330])).
% 8.91/3.13  tff(c_7351, plain, (v1_pre_topc(k1_tex_2('#skF_2', '#skF_1'('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_60, c_7350])).
% 8.91/3.13  tff(c_44, plain, (![A_40, B_41]: (m1_pre_topc(k1_tex_2(A_40, B_41), A_40) | ~m1_subset_1(B_41, u1_struct_0(A_40)) | ~l1_pre_topc(A_40) | v2_struct_0(A_40))), inference(cnfTransformation, [status(thm)], [f_156])).
% 8.91/3.13  tff(c_7327, plain, (m1_pre_topc(k1_tex_2('#skF_2', '#skF_1'('#skF_3')), '#skF_2') | ~l1_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_7320, c_44])).
% 8.91/3.13  tff(c_7346, plain, (m1_pre_topc(k1_tex_2('#skF_2', '#skF_1'('#skF_3')), '#skF_2') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_7327])).
% 8.91/3.13  tff(c_7347, plain, (m1_pre_topc(k1_tex_2('#skF_2', '#skF_1'('#skF_3')), '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_60, c_7346])).
% 8.91/3.13  tff(c_42, plain, (![A_33, B_37]: (k6_domain_1(u1_struct_0(A_33), B_37)=u1_struct_0(k1_tex_2(A_33, B_37)) | ~m1_pre_topc(k1_tex_2(A_33, B_37), A_33) | ~v1_pre_topc(k1_tex_2(A_33, B_37)) | v2_struct_0(k1_tex_2(A_33, B_37)) | ~m1_subset_1(B_37, u1_struct_0(A_33)) | ~l1_pre_topc(A_33) | v2_struct_0(A_33))), inference(cnfTransformation, [status(thm)], [f_142])).
% 8.91/3.13  tff(c_7419, plain, (k6_domain_1(u1_struct_0('#skF_2'), '#skF_1'('#skF_3'))=u1_struct_0(k1_tex_2('#skF_2', '#skF_1'('#skF_3'))) | ~v1_pre_topc(k1_tex_2('#skF_2', '#skF_1'('#skF_3'))) | v2_struct_0(k1_tex_2('#skF_2', '#skF_1'('#skF_3'))) | ~m1_subset_1('#skF_1'('#skF_3'), u1_struct_0('#skF_2')) | ~l1_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_7347, c_42])).
% 8.91/3.13  tff(c_7451, plain, (k6_domain_1(u1_struct_0('#skF_2'), '#skF_1'('#skF_3'))=u1_struct_0(k1_tex_2('#skF_2', '#skF_1'('#skF_3'))) | v2_struct_0(k1_tex_2('#skF_2', '#skF_1'('#skF_3'))) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_7320, c_7351, c_7419])).
% 8.91/3.13  tff(c_7452, plain, (k6_domain_1(u1_struct_0('#skF_2'), '#skF_1'('#skF_3'))=u1_struct_0(k1_tex_2('#skF_2', '#skF_1'('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_60, c_7355, c_7451])).
% 8.91/3.13  tff(c_7534, plain, (u1_struct_0(k1_tex_2('#skF_2', '#skF_1'('#skF_3')))=u1_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_7358, c_7452])).
% 8.91/3.13  tff(c_4069, plain, (![C_46]: (g1_pre_topc(u1_struct_0(k1_tex_2('#skF_2', C_46)), u1_pre_topc(k1_tex_2('#skF_2', C_46)))!=k1_tex_2('#skF_3', '#skF_1'('#skF_3')) | ~m1_subset_1(C_46, u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_4035, c_50])).
% 8.91/3.13  tff(c_7561, plain, (g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc(k1_tex_2('#skF_2', '#skF_1'('#skF_3'))))!=k1_tex_2('#skF_3', '#skF_1'('#skF_3')) | ~m1_subset_1('#skF_1'('#skF_3'), u1_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_7534, c_4069])).
% 8.91/3.13  tff(c_7765, plain, (g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc(k1_tex_2('#skF_2', '#skF_1'('#skF_3'))))!=k1_tex_2('#skF_3', '#skF_1'('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_7320, c_7561])).
% 8.91/3.13  tff(c_8761, plain, (g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc(k1_tex_2('#skF_3', '#skF_1'('#skF_3'))))!=k1_tex_2('#skF_3', '#skF_1'('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_8725, c_7765])).
% 8.91/3.13  tff(c_8769, plain, (m1_pre_topc(k1_tex_2('#skF_3', '#skF_1'('#skF_3')), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_8725, c_7347])).
% 8.91/3.13  tff(c_28, plain, (![B_24, A_22]: (v1_pre_topc(g1_pre_topc(u1_struct_0(B_24), u1_pre_topc(B_24))) | ~m1_pre_topc(B_24, A_22) | ~l1_pre_topc(A_22))), inference(cnfTransformation, [status(thm)], [f_99])).
% 8.91/3.13  tff(c_205, plain, (![A_84]: (v1_pre_topc(g1_pre_topc(u1_struct_0(k1_tex_2(A_84, '#skF_1'(A_84))), u1_pre_topc(k1_tex_2(A_84, '#skF_1'(A_84))))) | ~l1_pre_topc(A_84) | ~v7_struct_0(A_84) | ~l1_struct_0(A_84) | v2_struct_0(A_84))), inference(resolution, [status(thm)], [c_191, c_28])).
% 8.91/3.13  tff(c_2445, plain, (v1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc(k1_tex_2('#skF_3', '#skF_1'('#skF_3'))))) | ~l1_pre_topc('#skF_3') | ~v7_struct_0('#skF_3') | ~l1_struct_0('#skF_3') | v2_struct_0('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_2353, c_205])).
% 8.91/3.13  tff(c_2564, plain, (v1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc(k1_tex_2('#skF_3', '#skF_1'('#skF_3'))))) | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_808, c_54, c_85, c_2445])).
% 8.91/3.13  tff(c_2565, plain, (v1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc(k1_tex_2('#skF_3', '#skF_1'('#skF_3')))))), inference(negUnitSimplification, [status(thm)], [c_56, c_2564])).
% 8.91/3.13  tff(c_2503, plain, (![A_22]: (m1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc(k1_tex_2('#skF_3', '#skF_1'('#skF_3')))), A_22) | ~m1_pre_topc(k1_tex_2('#skF_3', '#skF_1'('#skF_3')), A_22) | ~l1_pre_topc(A_22))), inference(superposition, [status(thm), theory('equality')], [c_2353, c_26])).
% 8.91/3.13  tff(c_7521, plain, (![C_39]: (k1_tex_2('#skF_2', '#skF_1'('#skF_3'))=C_39 | u1_struct_0(C_39)!=u1_struct_0('#skF_3') | ~m1_pre_topc(C_39, '#skF_2') | ~v1_pre_topc(C_39) | v2_struct_0(C_39))), inference(negUnitSimplification, [status(thm)], [c_60, c_7520])).
% 8.91/3.13  tff(c_9450, plain, (![C_268]: (k1_tex_2('#skF_3', '#skF_1'('#skF_3'))=C_268 | u1_struct_0(C_268)!=u1_struct_0('#skF_3') | ~m1_pre_topc(C_268, '#skF_2') | ~v1_pre_topc(C_268) | v2_struct_0(C_268))), inference(demodulation, [status(thm), theory('equality')], [c_8725, c_7521])).
% 8.91/3.13  tff(c_9473, plain, (g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc(k1_tex_2('#skF_3', '#skF_1'('#skF_3'))))=k1_tex_2('#skF_3', '#skF_1'('#skF_3')) | u1_struct_0(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc(k1_tex_2('#skF_3', '#skF_1'('#skF_3')))))!=u1_struct_0('#skF_3') | ~v1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc(k1_tex_2('#skF_3', '#skF_1'('#skF_3'))))) | v2_struct_0(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc(k1_tex_2('#skF_3', '#skF_1'('#skF_3'))))) | ~m1_pre_topc(k1_tex_2('#skF_3', '#skF_1'('#skF_3')), '#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_2503, c_9450])).
% 8.91/3.13  tff(c_9525, plain, (g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc(k1_tex_2('#skF_3', '#skF_1'('#skF_3'))))=k1_tex_2('#skF_3', '#skF_1'('#skF_3')) | v2_struct_0(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc(k1_tex_2('#skF_3', '#skF_1'('#skF_3')))))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_8769, c_2565, c_5916, c_9473])).
% 8.91/3.13  tff(c_9527, plain, $false, inference(negUnitSimplification, [status(thm)], [c_7194, c_8761, c_9525])).
% 8.91/3.13  tff(c_9528, plain, (~l1_struct_0(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc(k1_tex_2('#skF_3', '#skF_1'('#skF_3')))))), inference(splitRight, [status(thm)], [c_6320])).
% 8.91/3.13  tff(c_9535, plain, (~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc(k1_tex_2('#skF_3', '#skF_1'('#skF_3')))))), inference(resolution, [status(thm)], [c_10, c_9528])).
% 8.91/3.13  tff(c_9542, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2562, c_9535])).
% 8.91/3.13  tff(c_9544, plain, (v2_struct_0(k1_tex_2('#skF_3', '#skF_1'('#skF_3')))), inference(splitRight, [status(thm)], [c_2581])).
% 8.91/3.13  tff(c_1853, plain, (![A_167]: (~v2_struct_0(k1_tex_2('#skF_3', '#skF_1'(A_167))) | ~l1_pre_topc('#skF_3') | v2_struct_0('#skF_3') | ~m1_pre_topc(A_167, '#skF_3') | ~v7_struct_0(A_167) | ~l1_struct_0(A_167) | v2_struct_0(A_167))), inference(resolution, [status(thm)], [c_1840, c_48])).
% 8.91/3.13  tff(c_1874, plain, (![A_167]: (~v2_struct_0(k1_tex_2('#skF_3', '#skF_1'(A_167))) | v2_struct_0('#skF_3') | ~m1_pre_topc(A_167, '#skF_3') | ~v7_struct_0(A_167) | ~l1_struct_0(A_167) | v2_struct_0(A_167))), inference(demodulation, [status(thm), theory('equality')], [c_85, c_1853])).
% 8.91/3.13  tff(c_1875, plain, (![A_167]: (~v2_struct_0(k1_tex_2('#skF_3', '#skF_1'(A_167))) | ~m1_pre_topc(A_167, '#skF_3') | ~v7_struct_0(A_167) | ~l1_struct_0(A_167) | v2_struct_0(A_167))), inference(negUnitSimplification, [status(thm)], [c_56, c_1874])).
% 8.91/3.13  tff(c_9569, plain, (~m1_pre_topc('#skF_3', '#skF_3') | ~v7_struct_0('#skF_3') | ~l1_struct_0('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_9544, c_1875])).
% 8.91/3.13  tff(c_9581, plain, (v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_808, c_54, c_504, c_9569])).
% 8.91/3.13  tff(c_9583, plain, $false, inference(negUnitSimplification, [status(thm)], [c_56, c_9581])).
% 8.91/3.13  tff(c_9584, plain, (v2_struct_0(k1_tex_2('#skF_3', '#skF_1'('#skF_3')))), inference(splitRight, [status(thm)], [c_2295])).
% 8.91/3.13  tff(c_9588, plain, (~m1_pre_topc('#skF_3', '#skF_3') | ~v7_struct_0('#skF_3') | ~l1_struct_0('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_9584, c_1875])).
% 8.91/3.13  tff(c_9600, plain, (v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_808, c_54, c_504, c_9588])).
% 8.91/3.13  tff(c_9602, plain, $false, inference(negUnitSimplification, [status(thm)], [c_56, c_9600])).
% 8.91/3.13  tff(c_9603, plain, (~l1_struct_0(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))) | v1_xboole_0(u1_struct_0('#skF_3'))), inference(splitRight, [status(thm)], [c_630])).
% 8.91/3.13  tff(c_9605, plain, (~l1_struct_0(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3')))), inference(splitLeft, [status(thm)], [c_9603])).
% 8.91/3.13  tff(c_9608, plain, (~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3')))), inference(resolution, [status(thm)], [c_10, c_9605])).
% 8.91/3.13  tff(c_9612, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_143, c_9608])).
% 8.91/3.13  tff(c_9613, plain, (v1_xboole_0(u1_struct_0('#skF_3'))), inference(splitRight, [status(thm)], [c_9603])).
% 8.91/3.13  tff(c_9635, plain, (~l1_struct_0('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_9613, c_16])).
% 8.91/3.13  tff(c_9638, plain, (v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_808, c_9635])).
% 8.91/3.13  tff(c_9640, plain, $false, inference(negUnitSimplification, [status(thm)], [c_56, c_9638])).
% 8.91/3.13  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.91/3.13  
% 8.91/3.13  Inference rules
% 8.91/3.13  ----------------------
% 8.91/3.13  #Ref     : 2
% 8.91/3.13  #Sup     : 1835
% 8.91/3.13  #Fact    : 0
% 8.91/3.13  #Define  : 0
% 8.91/3.13  #Split   : 19
% 8.91/3.13  #Chain   : 0
% 8.91/3.13  #Close   : 0
% 8.91/3.13  
% 8.91/3.13  Ordering : KBO
% 8.91/3.13  
% 8.91/3.13  Simplification rules
% 8.91/3.13  ----------------------
% 8.91/3.13  #Subsume      : 299
% 8.91/3.13  #Demod        : 4659
% 8.91/3.13  #Tautology    : 416
% 8.91/3.13  #SimpNegUnit  : 517
% 8.91/3.13  #BackRed      : 42
% 8.91/3.13  
% 8.91/3.13  #Partial instantiations: 0
% 8.91/3.13  #Strategies tried      : 1
% 8.91/3.13  
% 8.91/3.13  Timing (in seconds)
% 8.91/3.13  ----------------------
% 8.91/3.14  Preprocessing        : 0.35
% 8.91/3.14  Parsing              : 0.19
% 8.91/3.14  CNF conversion       : 0.02
% 8.91/3.14  Main loop            : 1.97
% 8.91/3.14  Inferencing          : 0.53
% 8.91/3.14  Reduction            : 0.80
% 8.91/3.14  Demodulation         : 0.60
% 8.91/3.14  BG Simplification    : 0.07
% 8.91/3.14  Subsumption          : 0.46
% 8.91/3.14  Abstraction          : 0.13
% 8.91/3.14  MUC search           : 0.00
% 8.91/3.14  Cooper               : 0.00
% 8.91/3.14  Total                : 2.41
% 8.91/3.14  Index Insertion      : 0.00
% 8.91/3.14  Index Deletion       : 0.00
% 8.91/3.14  Index Matching       : 0.00
% 8.91/3.14  BG Taut test         : 0.00
%------------------------------------------------------------------------------
