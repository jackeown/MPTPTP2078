%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:24:44 EST 2020

% Result     : Theorem 14.23s
% Output     : CNFRefutation 14.23s
% Verified   : 
% Statistics : Number of formulae       :   95 ( 301 expanded)
%              Number of leaves         :   37 ( 122 expanded)
%              Depth                    :   17
%              Number of atoms          :  413 (1750 expanded)
%              Number of equality atoms :   17 (  99 expanded)
%              Maximal formula depth    :   22 (   7 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r4_lattice3 > r3_lattices > r3_lattice3 > r1_lattices > r2_hidden > m1_subset_1 > v9_lattices > v8_lattices > v7_lattices > v6_lattices > v5_lattices > v4_lattices > v4_lattice3 > v2_struct_0 > v10_lattices > l3_lattices > k16_lattice3 > k15_lattice3 > a_2_2_lattice3 > #nlpp > u1_struct_0 > #skF_1 > #skF_4 > #skF_5 > #skF_6 > #skF_2 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(l3_lattices,type,(
    l3_lattices: $i > $o )).

tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

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

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff(r1_lattices,type,(
    r1_lattices: ( $i * $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v4_lattices,type,(
    v4_lattices: $i > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(v6_lattices,type,(
    v6_lattices: $i > $o )).

tff(v9_lattices,type,(
    v9_lattices: $i > $o )).

tff(r4_lattice3,type,(
    r4_lattice3: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(v4_lattice3,type,(
    v4_lattice3: $i > $o )).

tff(v5_lattices,type,(
    v5_lattices: $i > $o )).

tff(v10_lattices,type,(
    v10_lattices: $i > $o )).

tff(a_2_2_lattice3,type,(
    a_2_2_lattice3: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

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

tff(f_174,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v10_lattices(A)
          & v4_lattice3(A)
          & l3_lattices(A) )
       => ! [B] : k15_lattice3(A,B) = k16_lattice3(A,a_2_2_lattice3(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_lattice3)).

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

tff(f_119,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & l3_lattices(A) )
     => m1_subset_1(k15_lattice3(A,B),u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k15_lattice3)).

tff(f_112,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l3_lattices(A) )
     => ( ( ~ v2_struct_0(A)
          & v10_lattices(A)
          & v4_lattice3(A)
          & l3_lattices(A) )
       => ! [B,C] :
            ( m1_subset_1(C,u1_struct_0(A))
           => ( C = k15_lattice3(A,B)
            <=> ( r4_lattice3(A,C,B)
                & ! [D] :
                    ( m1_subset_1(D,u1_struct_0(A))
                   => ( r4_lattice3(A,D,B)
                     => r1_lattices(A,C,D) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d21_lattice3)).

tff(f_84,axiom,(
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

tff(f_137,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(B)
        & v10_lattices(B)
        & v4_lattice3(B)
        & l3_lattices(B) )
     => ( r2_hidden(A,a_2_2_lattice3(B,C))
      <=> ? [D] :
            ( m1_subset_1(D,u1_struct_0(B))
            & A = D
            & r4_lattice3(B,D,C) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fraenkel_a_2_2_lattice3)).

tff(f_161,axiom,(
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

tff(f_66,axiom,(
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

tff(c_66,plain,(
    ~ v2_struct_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_174])).

tff(c_60,plain,(
    l3_lattices('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_174])).

tff(c_64,plain,(
    v10_lattices('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_174])).

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

tff(c_62,plain,(
    v4_lattice3('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_174])).

tff(c_38,plain,(
    ! [A_39,B_40] :
      ( m1_subset_1(k15_lattice3(A_39,B_40),u1_struct_0(A_39))
      | ~ l3_lattices(A_39)
      | v2_struct_0(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_83,plain,(
    ! [A_90,B_91] :
      ( r4_lattice3(A_90,k15_lattice3(A_90,B_91),B_91)
      | ~ m1_subset_1(k15_lattice3(A_90,B_91),u1_struct_0(A_90))
      | ~ v4_lattice3(A_90)
      | ~ v10_lattices(A_90)
      | ~ l3_lattices(A_90)
      | v2_struct_0(A_90) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_86,plain,(
    ! [A_39,B_40] :
      ( r4_lattice3(A_39,k15_lattice3(A_39,B_40),B_40)
      | ~ v4_lattice3(A_39)
      | ~ v10_lattices(A_39)
      | ~ l3_lattices(A_39)
      | v2_struct_0(A_39) ) ),
    inference(resolution,[status(thm)],[c_38,c_83])).

tff(c_24,plain,(
    ! [A_5,B_17,C_23] :
      ( r2_hidden('#skF_1'(A_5,B_17,C_23),C_23)
      | r3_lattice3(A_5,B_17,C_23)
      | ~ m1_subset_1(B_17,u1_struct_0(A_5))
      | ~ l3_lattices(A_5)
      | v2_struct_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_75,plain,(
    ! [A_81,B_82,C_83] :
      ( '#skF_3'(A_81,B_82,C_83) = A_81
      | ~ r2_hidden(A_81,a_2_2_lattice3(B_82,C_83))
      | ~ l3_lattices(B_82)
      | ~ v4_lattice3(B_82)
      | ~ v10_lattices(B_82)
      | v2_struct_0(B_82) ) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_238,plain,(
    ! [A_168,B_169,B_170,C_171] :
      ( '#skF_3'('#skF_1'(A_168,B_169,a_2_2_lattice3(B_170,C_171)),B_170,C_171) = '#skF_1'(A_168,B_169,a_2_2_lattice3(B_170,C_171))
      | ~ l3_lattices(B_170)
      | ~ v4_lattice3(B_170)
      | ~ v10_lattices(B_170)
      | v2_struct_0(B_170)
      | r3_lattice3(A_168,B_169,a_2_2_lattice3(B_170,C_171))
      | ~ m1_subset_1(B_169,u1_struct_0(A_168))
      | ~ l3_lattices(A_168)
      | v2_struct_0(A_168) ) ),
    inference(resolution,[status(thm)],[c_24,c_75])).

tff(c_46,plain,(
    ! [A_41,B_42,C_43] :
      ( m1_subset_1('#skF_3'(A_41,B_42,C_43),u1_struct_0(B_42))
      | ~ r2_hidden(A_41,a_2_2_lattice3(B_42,C_43))
      | ~ l3_lattices(B_42)
      | ~ v4_lattice3(B_42)
      | ~ v10_lattices(B_42)
      | v2_struct_0(B_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_612,plain,(
    ! [A_248,B_249,B_250,C_251] :
      ( m1_subset_1('#skF_1'(A_248,B_249,a_2_2_lattice3(B_250,C_251)),u1_struct_0(B_250))
      | ~ r2_hidden('#skF_1'(A_248,B_249,a_2_2_lattice3(B_250,C_251)),a_2_2_lattice3(B_250,C_251))
      | ~ l3_lattices(B_250)
      | ~ v4_lattice3(B_250)
      | ~ v10_lattices(B_250)
      | v2_struct_0(B_250)
      | ~ l3_lattices(B_250)
      | ~ v4_lattice3(B_250)
      | ~ v10_lattices(B_250)
      | v2_struct_0(B_250)
      | r3_lattice3(A_248,B_249,a_2_2_lattice3(B_250,C_251))
      | ~ m1_subset_1(B_249,u1_struct_0(A_248))
      | ~ l3_lattices(A_248)
      | v2_struct_0(A_248) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_238,c_46])).

tff(c_622,plain,(
    ! [A_5,B_17,B_250,C_251] :
      ( m1_subset_1('#skF_1'(A_5,B_17,a_2_2_lattice3(B_250,C_251)),u1_struct_0(B_250))
      | ~ l3_lattices(B_250)
      | ~ v4_lattice3(B_250)
      | ~ v10_lattices(B_250)
      | v2_struct_0(B_250)
      | r3_lattice3(A_5,B_17,a_2_2_lattice3(B_250,C_251))
      | ~ m1_subset_1(B_17,u1_struct_0(A_5))
      | ~ l3_lattices(A_5)
      | v2_struct_0(A_5) ) ),
    inference(resolution,[status(thm)],[c_24,c_612])).

tff(c_42,plain,(
    ! [B_42,A_41,C_43] :
      ( r4_lattice3(B_42,'#skF_3'(A_41,B_42,C_43),C_43)
      | ~ r2_hidden(A_41,a_2_2_lattice3(B_42,C_43))
      | ~ l3_lattices(B_42)
      | ~ v4_lattice3(B_42)
      | ~ v10_lattices(B_42)
      | v2_struct_0(B_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_694,plain,(
    ! [B_274,A_275,B_276,C_277] :
      ( r4_lattice3(B_274,'#skF_1'(A_275,B_276,a_2_2_lattice3(B_274,C_277)),C_277)
      | ~ r2_hidden('#skF_1'(A_275,B_276,a_2_2_lattice3(B_274,C_277)),a_2_2_lattice3(B_274,C_277))
      | ~ l3_lattices(B_274)
      | ~ v4_lattice3(B_274)
      | ~ v10_lattices(B_274)
      | v2_struct_0(B_274)
      | ~ l3_lattices(B_274)
      | ~ v4_lattice3(B_274)
      | ~ v10_lattices(B_274)
      | v2_struct_0(B_274)
      | r3_lattice3(A_275,B_276,a_2_2_lattice3(B_274,C_277))
      | ~ m1_subset_1(B_276,u1_struct_0(A_275))
      | ~ l3_lattices(A_275)
      | v2_struct_0(A_275) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_238,c_42])).

tff(c_705,plain,(
    ! [B_278,A_279,B_280,C_281] :
      ( r4_lattice3(B_278,'#skF_1'(A_279,B_280,a_2_2_lattice3(B_278,C_281)),C_281)
      | ~ l3_lattices(B_278)
      | ~ v4_lattice3(B_278)
      | ~ v10_lattices(B_278)
      | v2_struct_0(B_278)
      | r3_lattice3(A_279,B_280,a_2_2_lattice3(B_278,C_281))
      | ~ m1_subset_1(B_280,u1_struct_0(A_279))
      | ~ l3_lattices(A_279)
      | v2_struct_0(A_279) ) ),
    inference(resolution,[status(thm)],[c_24,c_694])).

tff(c_164,plain,(
    ! [A_143,B_144,D_145] :
      ( r1_lattices(A_143,k15_lattice3(A_143,B_144),D_145)
      | ~ r4_lattice3(A_143,D_145,B_144)
      | ~ m1_subset_1(D_145,u1_struct_0(A_143))
      | ~ m1_subset_1(k15_lattice3(A_143,B_144),u1_struct_0(A_143))
      | ~ v4_lattice3(A_143)
      | ~ v10_lattices(A_143)
      | ~ l3_lattices(A_143)
      | v2_struct_0(A_143) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_168,plain,(
    ! [A_146,B_147,D_148] :
      ( r1_lattices(A_146,k15_lattice3(A_146,B_147),D_148)
      | ~ r4_lattice3(A_146,D_148,B_147)
      | ~ m1_subset_1(D_148,u1_struct_0(A_146))
      | ~ v4_lattice3(A_146)
      | ~ v10_lattices(A_146)
      | ~ l3_lattices(A_146)
      | v2_struct_0(A_146) ) ),
    inference(resolution,[status(thm)],[c_38,c_164])).

tff(c_22,plain,(
    ! [A_5,B_17,C_23] :
      ( ~ r1_lattices(A_5,B_17,'#skF_1'(A_5,B_17,C_23))
      | r3_lattice3(A_5,B_17,C_23)
      | ~ m1_subset_1(B_17,u1_struct_0(A_5))
      | ~ l3_lattices(A_5)
      | v2_struct_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_178,plain,(
    ! [A_146,B_147,C_23] :
      ( r3_lattice3(A_146,k15_lattice3(A_146,B_147),C_23)
      | ~ m1_subset_1(k15_lattice3(A_146,B_147),u1_struct_0(A_146))
      | ~ r4_lattice3(A_146,'#skF_1'(A_146,k15_lattice3(A_146,B_147),C_23),B_147)
      | ~ m1_subset_1('#skF_1'(A_146,k15_lattice3(A_146,B_147),C_23),u1_struct_0(A_146))
      | ~ v4_lattice3(A_146)
      | ~ v10_lattices(A_146)
      | ~ l3_lattices(A_146)
      | v2_struct_0(A_146) ) ),
    inference(resolution,[status(thm)],[c_168,c_22])).

tff(c_713,plain,(
    ! [A_282,C_283] :
      ( ~ m1_subset_1('#skF_1'(A_282,k15_lattice3(A_282,C_283),a_2_2_lattice3(A_282,C_283)),u1_struct_0(A_282))
      | ~ v4_lattice3(A_282)
      | ~ v10_lattices(A_282)
      | r3_lattice3(A_282,k15_lattice3(A_282,C_283),a_2_2_lattice3(A_282,C_283))
      | ~ m1_subset_1(k15_lattice3(A_282,C_283),u1_struct_0(A_282))
      | ~ l3_lattices(A_282)
      | v2_struct_0(A_282) ) ),
    inference(resolution,[status(thm)],[c_705,c_178])).

tff(c_722,plain,(
    ! [B_250,C_251] :
      ( ~ v4_lattice3(B_250)
      | ~ v10_lattices(B_250)
      | r3_lattice3(B_250,k15_lattice3(B_250,C_251),a_2_2_lattice3(B_250,C_251))
      | ~ m1_subset_1(k15_lattice3(B_250,C_251),u1_struct_0(B_250))
      | ~ l3_lattices(B_250)
      | v2_struct_0(B_250) ) ),
    inference(resolution,[status(thm)],[c_622,c_713])).

tff(c_56,plain,(
    ! [A_47,B_59,C_65] :
      ( m1_subset_1('#skF_4'(A_47,B_59,C_65),u1_struct_0(A_47))
      | k16_lattice3(A_47,C_65) = B_59
      | ~ r3_lattice3(A_47,B_59,C_65)
      | ~ m1_subset_1(B_59,u1_struct_0(A_47))
      | ~ l3_lattices(A_47)
      | ~ v4_lattice3(A_47)
      | ~ v10_lattices(A_47)
      | v2_struct_0(A_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_54,plain,(
    ! [A_47,B_59,C_65] :
      ( r3_lattice3(A_47,'#skF_4'(A_47,B_59,C_65),C_65)
      | k16_lattice3(A_47,C_65) = B_59
      | ~ r3_lattice3(A_47,B_59,C_65)
      | ~ m1_subset_1(B_59,u1_struct_0(A_47))
      | ~ l3_lattices(A_47)
      | ~ v4_lattice3(A_47)
      | ~ v10_lattices(A_47)
      | v2_struct_0(A_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_40,plain,(
    ! [D_46,B_42,C_43] :
      ( r2_hidden(D_46,a_2_2_lattice3(B_42,C_43))
      | ~ r4_lattice3(B_42,D_46,C_43)
      | ~ m1_subset_1(D_46,u1_struct_0(B_42))
      | ~ l3_lattices(B_42)
      | ~ v4_lattice3(B_42)
      | ~ v10_lattices(B_42)
      | v2_struct_0(B_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_103,plain,(
    ! [A_108,B_109,D_110,C_111] :
      ( r1_lattices(A_108,B_109,D_110)
      | ~ r2_hidden(D_110,C_111)
      | ~ m1_subset_1(D_110,u1_struct_0(A_108))
      | ~ r3_lattice3(A_108,B_109,C_111)
      | ~ m1_subset_1(B_109,u1_struct_0(A_108))
      | ~ l3_lattices(A_108)
      | v2_struct_0(A_108) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_271,plain,(
    ! [B_180,C_176,D_177,A_178,B_179] :
      ( r1_lattices(A_178,B_179,D_177)
      | ~ m1_subset_1(D_177,u1_struct_0(A_178))
      | ~ r3_lattice3(A_178,B_179,a_2_2_lattice3(B_180,C_176))
      | ~ m1_subset_1(B_179,u1_struct_0(A_178))
      | ~ l3_lattices(A_178)
      | v2_struct_0(A_178)
      | ~ r4_lattice3(B_180,D_177,C_176)
      | ~ m1_subset_1(D_177,u1_struct_0(B_180))
      | ~ l3_lattices(B_180)
      | ~ v4_lattice3(B_180)
      | ~ v10_lattices(B_180)
      | v2_struct_0(B_180) ) ),
    inference(resolution,[status(thm)],[c_40,c_103])).

tff(c_384,plain,(
    ! [B_208,B_209,A_206,C_210,B_207] :
      ( r1_lattices(A_206,B_207,k15_lattice3(A_206,B_208))
      | ~ r3_lattice3(A_206,B_207,a_2_2_lattice3(B_209,C_210))
      | ~ m1_subset_1(B_207,u1_struct_0(A_206))
      | ~ r4_lattice3(B_209,k15_lattice3(A_206,B_208),C_210)
      | ~ m1_subset_1(k15_lattice3(A_206,B_208),u1_struct_0(B_209))
      | ~ l3_lattices(B_209)
      | ~ v4_lattice3(B_209)
      | ~ v10_lattices(B_209)
      | v2_struct_0(B_209)
      | ~ l3_lattices(A_206)
      | v2_struct_0(A_206) ) ),
    inference(resolution,[status(thm)],[c_38,c_271])).

tff(c_2666,plain,(
    ! [B_590,B_588,B_591,A_587,C_589] :
      ( r1_lattices(A_587,'#skF_4'(A_587,B_588,a_2_2_lattice3(B_591,C_589)),k15_lattice3(A_587,B_590))
      | ~ m1_subset_1('#skF_4'(A_587,B_588,a_2_2_lattice3(B_591,C_589)),u1_struct_0(A_587))
      | ~ r4_lattice3(B_591,k15_lattice3(A_587,B_590),C_589)
      | ~ m1_subset_1(k15_lattice3(A_587,B_590),u1_struct_0(B_591))
      | ~ l3_lattices(B_591)
      | ~ v4_lattice3(B_591)
      | ~ v10_lattices(B_591)
      | v2_struct_0(B_591)
      | k16_lattice3(A_587,a_2_2_lattice3(B_591,C_589)) = B_588
      | ~ r3_lattice3(A_587,B_588,a_2_2_lattice3(B_591,C_589))
      | ~ m1_subset_1(B_588,u1_struct_0(A_587))
      | ~ l3_lattices(A_587)
      | ~ v4_lattice3(A_587)
      | ~ v10_lattices(A_587)
      | v2_struct_0(A_587) ) ),
    inference(resolution,[status(thm)],[c_54,c_384])).

tff(c_130,plain,(
    ! [A_119,B_120,C_121] :
      ( r3_lattices(A_119,B_120,C_121)
      | ~ r1_lattices(A_119,B_120,C_121)
      | ~ m1_subset_1(C_121,u1_struct_0(A_119))
      | ~ m1_subset_1(B_120,u1_struct_0(A_119))
      | ~ l3_lattices(A_119)
      | ~ v9_lattices(A_119)
      | ~ v8_lattices(A_119)
      | ~ v6_lattices(A_119)
      | v2_struct_0(A_119) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_139,plain,(
    ! [A_39,B_120,B_40] :
      ( r3_lattices(A_39,B_120,k15_lattice3(A_39,B_40))
      | ~ r1_lattices(A_39,B_120,k15_lattice3(A_39,B_40))
      | ~ m1_subset_1(B_120,u1_struct_0(A_39))
      | ~ v9_lattices(A_39)
      | ~ v8_lattices(A_39)
      | ~ v6_lattices(A_39)
      | ~ l3_lattices(A_39)
      | v2_struct_0(A_39) ) ),
    inference(resolution,[status(thm)],[c_38,c_130])).

tff(c_144,plain,(
    ! [A_125,B_126,C_127] :
      ( ~ r3_lattices(A_125,'#skF_4'(A_125,B_126,C_127),B_126)
      | k16_lattice3(A_125,C_127) = B_126
      | ~ r3_lattice3(A_125,B_126,C_127)
      | ~ m1_subset_1(B_126,u1_struct_0(A_125))
      | ~ l3_lattices(A_125)
      | ~ v4_lattice3(A_125)
      | ~ v10_lattices(A_125)
      | v2_struct_0(A_125) ) ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_149,plain,(
    ! [A_39,C_127,B_40] :
      ( k16_lattice3(A_39,C_127) = k15_lattice3(A_39,B_40)
      | ~ r3_lattice3(A_39,k15_lattice3(A_39,B_40),C_127)
      | ~ m1_subset_1(k15_lattice3(A_39,B_40),u1_struct_0(A_39))
      | ~ v4_lattice3(A_39)
      | ~ v10_lattices(A_39)
      | ~ r1_lattices(A_39,'#skF_4'(A_39,k15_lattice3(A_39,B_40),C_127),k15_lattice3(A_39,B_40))
      | ~ m1_subset_1('#skF_4'(A_39,k15_lattice3(A_39,B_40),C_127),u1_struct_0(A_39))
      | ~ v9_lattices(A_39)
      | ~ v8_lattices(A_39)
      | ~ v6_lattices(A_39)
      | ~ l3_lattices(A_39)
      | v2_struct_0(A_39) ) ),
    inference(resolution,[status(thm)],[c_139,c_144])).

tff(c_6264,plain,(
    ! [A_891,B_892,B_893,C_894] :
      ( ~ v9_lattices(A_891)
      | ~ v8_lattices(A_891)
      | ~ v6_lattices(A_891)
      | ~ m1_subset_1('#skF_4'(A_891,k15_lattice3(A_891,B_892),a_2_2_lattice3(B_893,C_894)),u1_struct_0(A_891))
      | ~ r4_lattice3(B_893,k15_lattice3(A_891,B_892),C_894)
      | ~ m1_subset_1(k15_lattice3(A_891,B_892),u1_struct_0(B_893))
      | ~ l3_lattices(B_893)
      | ~ v4_lattice3(B_893)
      | ~ v10_lattices(B_893)
      | v2_struct_0(B_893)
      | k16_lattice3(A_891,a_2_2_lattice3(B_893,C_894)) = k15_lattice3(A_891,B_892)
      | ~ r3_lattice3(A_891,k15_lattice3(A_891,B_892),a_2_2_lattice3(B_893,C_894))
      | ~ m1_subset_1(k15_lattice3(A_891,B_892),u1_struct_0(A_891))
      | ~ l3_lattices(A_891)
      | ~ v4_lattice3(A_891)
      | ~ v10_lattices(A_891)
      | v2_struct_0(A_891) ) ),
    inference(resolution,[status(thm)],[c_2666,c_149])).

tff(c_9478,plain,(
    ! [A_985,B_986,B_987,C_988] :
      ( ~ v9_lattices(A_985)
      | ~ v8_lattices(A_985)
      | ~ v6_lattices(A_985)
      | ~ r4_lattice3(B_986,k15_lattice3(A_985,B_987),C_988)
      | ~ m1_subset_1(k15_lattice3(A_985,B_987),u1_struct_0(B_986))
      | ~ l3_lattices(B_986)
      | ~ v4_lattice3(B_986)
      | ~ v10_lattices(B_986)
      | v2_struct_0(B_986)
      | k16_lattice3(A_985,a_2_2_lattice3(B_986,C_988)) = k15_lattice3(A_985,B_987)
      | ~ r3_lattice3(A_985,k15_lattice3(A_985,B_987),a_2_2_lattice3(B_986,C_988))
      | ~ m1_subset_1(k15_lattice3(A_985,B_987),u1_struct_0(A_985))
      | ~ l3_lattices(A_985)
      | ~ v4_lattice3(A_985)
      | ~ v10_lattices(A_985)
      | v2_struct_0(A_985) ) ),
    inference(resolution,[status(thm)],[c_56,c_6264])).

tff(c_9486,plain,(
    ! [B_989,C_990] :
      ( ~ v9_lattices(B_989)
      | ~ v8_lattices(B_989)
      | ~ v6_lattices(B_989)
      | ~ r4_lattice3(B_989,k15_lattice3(B_989,C_990),C_990)
      | k16_lattice3(B_989,a_2_2_lattice3(B_989,C_990)) = k15_lattice3(B_989,C_990)
      | ~ v4_lattice3(B_989)
      | ~ v10_lattices(B_989)
      | ~ m1_subset_1(k15_lattice3(B_989,C_990),u1_struct_0(B_989))
      | ~ l3_lattices(B_989)
      | v2_struct_0(B_989) ) ),
    inference(resolution,[status(thm)],[c_722,c_9478])).

tff(c_9492,plain,(
    ! [A_991,B_992] :
      ( ~ v9_lattices(A_991)
      | ~ v8_lattices(A_991)
      | ~ v6_lattices(A_991)
      | k16_lattice3(A_991,a_2_2_lattice3(A_991,B_992)) = k15_lattice3(A_991,B_992)
      | ~ m1_subset_1(k15_lattice3(A_991,B_992),u1_struct_0(A_991))
      | ~ v4_lattice3(A_991)
      | ~ v10_lattices(A_991)
      | ~ l3_lattices(A_991)
      | v2_struct_0(A_991) ) ),
    inference(resolution,[status(thm)],[c_86,c_9486])).

tff(c_9500,plain,(
    ! [A_993,B_994] :
      ( ~ v9_lattices(A_993)
      | ~ v8_lattices(A_993)
      | ~ v6_lattices(A_993)
      | k16_lattice3(A_993,a_2_2_lattice3(A_993,B_994)) = k15_lattice3(A_993,B_994)
      | ~ v4_lattice3(A_993)
      | ~ v10_lattices(A_993)
      | ~ l3_lattices(A_993)
      | v2_struct_0(A_993) ) ),
    inference(resolution,[status(thm)],[c_38,c_9492])).

tff(c_58,plain,(
    k16_lattice3('#skF_5',a_2_2_lattice3('#skF_5','#skF_6')) != k15_lattice3('#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_174])).

tff(c_9510,plain,
    ( ~ v9_lattices('#skF_5')
    | ~ v8_lattices('#skF_5')
    | ~ v6_lattices('#skF_5')
    | ~ v4_lattice3('#skF_5')
    | ~ v10_lattices('#skF_5')
    | ~ l3_lattices('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_9500,c_58])).

tff(c_9517,plain,
    ( ~ v9_lattices('#skF_5')
    | ~ v8_lattices('#skF_5')
    | ~ v6_lattices('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_64,c_62,c_9510])).

tff(c_9518,plain,
    ( ~ v9_lattices('#skF_5')
    | ~ v8_lattices('#skF_5')
    | ~ v6_lattices('#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_9517])).

tff(c_9520,plain,(
    ~ v6_lattices('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_9518])).

tff(c_9523,plain,
    ( ~ v10_lattices('#skF_5')
    | v2_struct_0('#skF_5')
    | ~ l3_lattices('#skF_5') ),
    inference(resolution,[status(thm)],[c_8,c_9520])).

tff(c_9526,plain,(
    v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_64,c_9523])).

tff(c_9528,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_9526])).

tff(c_9529,plain,
    ( ~ v8_lattices('#skF_5')
    | ~ v9_lattices('#skF_5') ),
    inference(splitRight,[status(thm)],[c_9518])).

tff(c_9531,plain,(
    ~ v9_lattices('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_9529])).

tff(c_9534,plain,
    ( ~ v10_lattices('#skF_5')
    | v2_struct_0('#skF_5')
    | ~ l3_lattices('#skF_5') ),
    inference(resolution,[status(thm)],[c_2,c_9531])).

tff(c_9537,plain,(
    v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_64,c_9534])).

tff(c_9539,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_9537])).

tff(c_9540,plain,(
    ~ v8_lattices('#skF_5') ),
    inference(splitRight,[status(thm)],[c_9529])).

tff(c_9565,plain,
    ( ~ v10_lattices('#skF_5')
    | v2_struct_0('#skF_5')
    | ~ l3_lattices('#skF_5') ),
    inference(resolution,[status(thm)],[c_4,c_9540])).

tff(c_9568,plain,(
    v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_64,c_9565])).

tff(c_9570,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_9568])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.11/0.33  % Computer   : n008.cluster.edu
% 0.11/0.33  % Model      : x86_64 x86_64
% 0.11/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.33  % Memory     : 8042.1875MB
% 0.11/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.33  % CPULimit   : 60
% 0.11/0.33  % DateTime   : Tue Dec  1 16:03:30 EST 2020
% 0.11/0.33  % CPUTime    : 
% 0.11/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 14.23/6.37  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 14.23/6.38  
% 14.23/6.38  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 14.23/6.38  %$ r4_lattice3 > r3_lattices > r3_lattice3 > r1_lattices > r2_hidden > m1_subset_1 > v9_lattices > v8_lattices > v7_lattices > v6_lattices > v5_lattices > v4_lattices > v4_lattice3 > v2_struct_0 > v10_lattices > l3_lattices > k16_lattice3 > k15_lattice3 > a_2_2_lattice3 > #nlpp > u1_struct_0 > #skF_1 > #skF_4 > #skF_5 > #skF_6 > #skF_2 > #skF_3
% 14.23/6.38  
% 14.23/6.38  %Foreground sorts:
% 14.23/6.38  
% 14.23/6.38  
% 14.23/6.38  %Background operators:
% 14.23/6.38  
% 14.23/6.38  
% 14.23/6.38  %Foreground operators:
% 14.23/6.38  tff(l3_lattices, type, l3_lattices: $i > $o).
% 14.23/6.38  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 14.23/6.38  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 14.23/6.38  tff(r3_lattices, type, r3_lattices: ($i * $i * $i) > $o).
% 14.23/6.38  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 14.23/6.38  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 14.23/6.38  tff(k16_lattice3, type, k16_lattice3: ($i * $i) > $i).
% 14.23/6.38  tff(k15_lattice3, type, k15_lattice3: ($i * $i) > $i).
% 14.23/6.38  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 14.23/6.38  tff(r1_lattices, type, r1_lattices: ($i * $i * $i) > $o).
% 14.23/6.38  tff('#skF_5', type, '#skF_5': $i).
% 14.23/6.38  tff(v4_lattices, type, v4_lattices: $i > $o).
% 14.23/6.38  tff('#skF_6', type, '#skF_6': $i).
% 14.23/6.38  tff(v6_lattices, type, v6_lattices: $i > $o).
% 14.23/6.38  tff(v9_lattices, type, v9_lattices: $i > $o).
% 14.23/6.38  tff(r4_lattice3, type, r4_lattice3: ($i * $i * $i) > $o).
% 14.23/6.38  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 14.23/6.38  tff(v4_lattice3, type, v4_lattice3: $i > $o).
% 14.23/6.38  tff(v5_lattices, type, v5_lattices: $i > $o).
% 14.23/6.38  tff(v10_lattices, type, v10_lattices: $i > $o).
% 14.23/6.38  tff(a_2_2_lattice3, type, a_2_2_lattice3: ($i * $i) > $i).
% 14.23/6.38  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 14.23/6.38  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 14.23/6.38  tff(v8_lattices, type, v8_lattices: $i > $o).
% 14.23/6.38  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 14.23/6.38  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 14.23/6.38  tff(r3_lattice3, type, r3_lattice3: ($i * $i * $i) > $o).
% 14.23/6.38  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 14.23/6.38  tff(v7_lattices, type, v7_lattices: $i > $o).
% 14.23/6.38  
% 14.23/6.40  tff(f_174, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v10_lattices(A)) & v4_lattice3(A)) & l3_lattices(A)) => (![B]: (k15_lattice3(A, B) = k16_lattice3(A, a_2_2_lattice3(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t37_lattice3)).
% 14.23/6.40  tff(f_47, axiom, (![A]: (l3_lattices(A) => ((~v2_struct_0(A) & v10_lattices(A)) => ((((((~v2_struct_0(A) & v4_lattices(A)) & v5_lattices(A)) & v6_lattices(A)) & v7_lattices(A)) & v8_lattices(A)) & v9_lattices(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_lattices)).
% 14.23/6.40  tff(f_119, axiom, (![A, B]: ((~v2_struct_0(A) & l3_lattices(A)) => m1_subset_1(k15_lattice3(A, B), u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k15_lattice3)).
% 14.23/6.40  tff(f_112, axiom, (![A]: ((~v2_struct_0(A) & l3_lattices(A)) => ((((~v2_struct_0(A) & v10_lattices(A)) & v4_lattice3(A)) & l3_lattices(A)) => (![B, C]: (m1_subset_1(C, u1_struct_0(A)) => ((C = k15_lattice3(A, B)) <=> (r4_lattice3(A, C, B) & (![D]: (m1_subset_1(D, u1_struct_0(A)) => (r4_lattice3(A, D, B) => r1_lattices(A, C, D))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d21_lattice3)).
% 14.23/6.40  tff(f_84, axiom, (![A]: ((~v2_struct_0(A) & l3_lattices(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (r3_lattice3(A, B, C) <=> (![D]: (m1_subset_1(D, u1_struct_0(A)) => (r2_hidden(D, C) => r1_lattices(A, B, D)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d16_lattice3)).
% 14.23/6.40  tff(f_137, axiom, (![A, B, C]: ((((~v2_struct_0(B) & v10_lattices(B)) & v4_lattice3(B)) & l3_lattices(B)) => (r2_hidden(A, a_2_2_lattice3(B, C)) <=> (?[D]: ((m1_subset_1(D, u1_struct_0(B)) & (A = D)) & r4_lattice3(B, D, C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fraenkel_a_2_2_lattice3)).
% 14.23/6.40  tff(f_161, axiom, (![A]: ((((~v2_struct_0(A) & v10_lattices(A)) & v4_lattice3(A)) & l3_lattices(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: ((B = k16_lattice3(A, C)) <=> (r3_lattice3(A, B, C) & (![D]: (m1_subset_1(D, u1_struct_0(A)) => (r3_lattice3(A, D, C) => r3_lattices(A, D, B))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t34_lattice3)).
% 14.23/6.40  tff(f_66, axiom, (![A, B, C]: (((((((~v2_struct_0(A) & v6_lattices(A)) & v8_lattices(A)) & v9_lattices(A)) & l3_lattices(A)) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => (r3_lattices(A, B, C) <=> r1_lattices(A, B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r3_lattices)).
% 14.23/6.40  tff(c_66, plain, (~v2_struct_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_174])).
% 14.23/6.40  tff(c_60, plain, (l3_lattices('#skF_5')), inference(cnfTransformation, [status(thm)], [f_174])).
% 14.23/6.40  tff(c_64, plain, (v10_lattices('#skF_5')), inference(cnfTransformation, [status(thm)], [f_174])).
% 14.23/6.40  tff(c_4, plain, (![A_1]: (v8_lattices(A_1) | ~v10_lattices(A_1) | v2_struct_0(A_1) | ~l3_lattices(A_1))), inference(cnfTransformation, [status(thm)], [f_47])).
% 14.23/6.40  tff(c_2, plain, (![A_1]: (v9_lattices(A_1) | ~v10_lattices(A_1) | v2_struct_0(A_1) | ~l3_lattices(A_1))), inference(cnfTransformation, [status(thm)], [f_47])).
% 14.23/6.40  tff(c_8, plain, (![A_1]: (v6_lattices(A_1) | ~v10_lattices(A_1) | v2_struct_0(A_1) | ~l3_lattices(A_1))), inference(cnfTransformation, [status(thm)], [f_47])).
% 14.23/6.40  tff(c_62, plain, (v4_lattice3('#skF_5')), inference(cnfTransformation, [status(thm)], [f_174])).
% 14.23/6.40  tff(c_38, plain, (![A_39, B_40]: (m1_subset_1(k15_lattice3(A_39, B_40), u1_struct_0(A_39)) | ~l3_lattices(A_39) | v2_struct_0(A_39))), inference(cnfTransformation, [status(thm)], [f_119])).
% 14.23/6.40  tff(c_83, plain, (![A_90, B_91]: (r4_lattice3(A_90, k15_lattice3(A_90, B_91), B_91) | ~m1_subset_1(k15_lattice3(A_90, B_91), u1_struct_0(A_90)) | ~v4_lattice3(A_90) | ~v10_lattices(A_90) | ~l3_lattices(A_90) | v2_struct_0(A_90))), inference(cnfTransformation, [status(thm)], [f_112])).
% 14.23/6.40  tff(c_86, plain, (![A_39, B_40]: (r4_lattice3(A_39, k15_lattice3(A_39, B_40), B_40) | ~v4_lattice3(A_39) | ~v10_lattices(A_39) | ~l3_lattices(A_39) | v2_struct_0(A_39))), inference(resolution, [status(thm)], [c_38, c_83])).
% 14.23/6.40  tff(c_24, plain, (![A_5, B_17, C_23]: (r2_hidden('#skF_1'(A_5, B_17, C_23), C_23) | r3_lattice3(A_5, B_17, C_23) | ~m1_subset_1(B_17, u1_struct_0(A_5)) | ~l3_lattices(A_5) | v2_struct_0(A_5))), inference(cnfTransformation, [status(thm)], [f_84])).
% 14.23/6.40  tff(c_75, plain, (![A_81, B_82, C_83]: ('#skF_3'(A_81, B_82, C_83)=A_81 | ~r2_hidden(A_81, a_2_2_lattice3(B_82, C_83)) | ~l3_lattices(B_82) | ~v4_lattice3(B_82) | ~v10_lattices(B_82) | v2_struct_0(B_82))), inference(cnfTransformation, [status(thm)], [f_137])).
% 14.23/6.40  tff(c_238, plain, (![A_168, B_169, B_170, C_171]: ('#skF_3'('#skF_1'(A_168, B_169, a_2_2_lattice3(B_170, C_171)), B_170, C_171)='#skF_1'(A_168, B_169, a_2_2_lattice3(B_170, C_171)) | ~l3_lattices(B_170) | ~v4_lattice3(B_170) | ~v10_lattices(B_170) | v2_struct_0(B_170) | r3_lattice3(A_168, B_169, a_2_2_lattice3(B_170, C_171)) | ~m1_subset_1(B_169, u1_struct_0(A_168)) | ~l3_lattices(A_168) | v2_struct_0(A_168))), inference(resolution, [status(thm)], [c_24, c_75])).
% 14.23/6.40  tff(c_46, plain, (![A_41, B_42, C_43]: (m1_subset_1('#skF_3'(A_41, B_42, C_43), u1_struct_0(B_42)) | ~r2_hidden(A_41, a_2_2_lattice3(B_42, C_43)) | ~l3_lattices(B_42) | ~v4_lattice3(B_42) | ~v10_lattices(B_42) | v2_struct_0(B_42))), inference(cnfTransformation, [status(thm)], [f_137])).
% 14.23/6.40  tff(c_612, plain, (![A_248, B_249, B_250, C_251]: (m1_subset_1('#skF_1'(A_248, B_249, a_2_2_lattice3(B_250, C_251)), u1_struct_0(B_250)) | ~r2_hidden('#skF_1'(A_248, B_249, a_2_2_lattice3(B_250, C_251)), a_2_2_lattice3(B_250, C_251)) | ~l3_lattices(B_250) | ~v4_lattice3(B_250) | ~v10_lattices(B_250) | v2_struct_0(B_250) | ~l3_lattices(B_250) | ~v4_lattice3(B_250) | ~v10_lattices(B_250) | v2_struct_0(B_250) | r3_lattice3(A_248, B_249, a_2_2_lattice3(B_250, C_251)) | ~m1_subset_1(B_249, u1_struct_0(A_248)) | ~l3_lattices(A_248) | v2_struct_0(A_248))), inference(superposition, [status(thm), theory('equality')], [c_238, c_46])).
% 14.23/6.40  tff(c_622, plain, (![A_5, B_17, B_250, C_251]: (m1_subset_1('#skF_1'(A_5, B_17, a_2_2_lattice3(B_250, C_251)), u1_struct_0(B_250)) | ~l3_lattices(B_250) | ~v4_lattice3(B_250) | ~v10_lattices(B_250) | v2_struct_0(B_250) | r3_lattice3(A_5, B_17, a_2_2_lattice3(B_250, C_251)) | ~m1_subset_1(B_17, u1_struct_0(A_5)) | ~l3_lattices(A_5) | v2_struct_0(A_5))), inference(resolution, [status(thm)], [c_24, c_612])).
% 14.23/6.40  tff(c_42, plain, (![B_42, A_41, C_43]: (r4_lattice3(B_42, '#skF_3'(A_41, B_42, C_43), C_43) | ~r2_hidden(A_41, a_2_2_lattice3(B_42, C_43)) | ~l3_lattices(B_42) | ~v4_lattice3(B_42) | ~v10_lattices(B_42) | v2_struct_0(B_42))), inference(cnfTransformation, [status(thm)], [f_137])).
% 14.23/6.40  tff(c_694, plain, (![B_274, A_275, B_276, C_277]: (r4_lattice3(B_274, '#skF_1'(A_275, B_276, a_2_2_lattice3(B_274, C_277)), C_277) | ~r2_hidden('#skF_1'(A_275, B_276, a_2_2_lattice3(B_274, C_277)), a_2_2_lattice3(B_274, C_277)) | ~l3_lattices(B_274) | ~v4_lattice3(B_274) | ~v10_lattices(B_274) | v2_struct_0(B_274) | ~l3_lattices(B_274) | ~v4_lattice3(B_274) | ~v10_lattices(B_274) | v2_struct_0(B_274) | r3_lattice3(A_275, B_276, a_2_2_lattice3(B_274, C_277)) | ~m1_subset_1(B_276, u1_struct_0(A_275)) | ~l3_lattices(A_275) | v2_struct_0(A_275))), inference(superposition, [status(thm), theory('equality')], [c_238, c_42])).
% 14.23/6.40  tff(c_705, plain, (![B_278, A_279, B_280, C_281]: (r4_lattice3(B_278, '#skF_1'(A_279, B_280, a_2_2_lattice3(B_278, C_281)), C_281) | ~l3_lattices(B_278) | ~v4_lattice3(B_278) | ~v10_lattices(B_278) | v2_struct_0(B_278) | r3_lattice3(A_279, B_280, a_2_2_lattice3(B_278, C_281)) | ~m1_subset_1(B_280, u1_struct_0(A_279)) | ~l3_lattices(A_279) | v2_struct_0(A_279))), inference(resolution, [status(thm)], [c_24, c_694])).
% 14.23/6.40  tff(c_164, plain, (![A_143, B_144, D_145]: (r1_lattices(A_143, k15_lattice3(A_143, B_144), D_145) | ~r4_lattice3(A_143, D_145, B_144) | ~m1_subset_1(D_145, u1_struct_0(A_143)) | ~m1_subset_1(k15_lattice3(A_143, B_144), u1_struct_0(A_143)) | ~v4_lattice3(A_143) | ~v10_lattices(A_143) | ~l3_lattices(A_143) | v2_struct_0(A_143))), inference(cnfTransformation, [status(thm)], [f_112])).
% 14.23/6.40  tff(c_168, plain, (![A_146, B_147, D_148]: (r1_lattices(A_146, k15_lattice3(A_146, B_147), D_148) | ~r4_lattice3(A_146, D_148, B_147) | ~m1_subset_1(D_148, u1_struct_0(A_146)) | ~v4_lattice3(A_146) | ~v10_lattices(A_146) | ~l3_lattices(A_146) | v2_struct_0(A_146))), inference(resolution, [status(thm)], [c_38, c_164])).
% 14.23/6.40  tff(c_22, plain, (![A_5, B_17, C_23]: (~r1_lattices(A_5, B_17, '#skF_1'(A_5, B_17, C_23)) | r3_lattice3(A_5, B_17, C_23) | ~m1_subset_1(B_17, u1_struct_0(A_5)) | ~l3_lattices(A_5) | v2_struct_0(A_5))), inference(cnfTransformation, [status(thm)], [f_84])).
% 14.23/6.40  tff(c_178, plain, (![A_146, B_147, C_23]: (r3_lattice3(A_146, k15_lattice3(A_146, B_147), C_23) | ~m1_subset_1(k15_lattice3(A_146, B_147), u1_struct_0(A_146)) | ~r4_lattice3(A_146, '#skF_1'(A_146, k15_lattice3(A_146, B_147), C_23), B_147) | ~m1_subset_1('#skF_1'(A_146, k15_lattice3(A_146, B_147), C_23), u1_struct_0(A_146)) | ~v4_lattice3(A_146) | ~v10_lattices(A_146) | ~l3_lattices(A_146) | v2_struct_0(A_146))), inference(resolution, [status(thm)], [c_168, c_22])).
% 14.23/6.40  tff(c_713, plain, (![A_282, C_283]: (~m1_subset_1('#skF_1'(A_282, k15_lattice3(A_282, C_283), a_2_2_lattice3(A_282, C_283)), u1_struct_0(A_282)) | ~v4_lattice3(A_282) | ~v10_lattices(A_282) | r3_lattice3(A_282, k15_lattice3(A_282, C_283), a_2_2_lattice3(A_282, C_283)) | ~m1_subset_1(k15_lattice3(A_282, C_283), u1_struct_0(A_282)) | ~l3_lattices(A_282) | v2_struct_0(A_282))), inference(resolution, [status(thm)], [c_705, c_178])).
% 14.23/6.40  tff(c_722, plain, (![B_250, C_251]: (~v4_lattice3(B_250) | ~v10_lattices(B_250) | r3_lattice3(B_250, k15_lattice3(B_250, C_251), a_2_2_lattice3(B_250, C_251)) | ~m1_subset_1(k15_lattice3(B_250, C_251), u1_struct_0(B_250)) | ~l3_lattices(B_250) | v2_struct_0(B_250))), inference(resolution, [status(thm)], [c_622, c_713])).
% 14.23/6.40  tff(c_56, plain, (![A_47, B_59, C_65]: (m1_subset_1('#skF_4'(A_47, B_59, C_65), u1_struct_0(A_47)) | k16_lattice3(A_47, C_65)=B_59 | ~r3_lattice3(A_47, B_59, C_65) | ~m1_subset_1(B_59, u1_struct_0(A_47)) | ~l3_lattices(A_47) | ~v4_lattice3(A_47) | ~v10_lattices(A_47) | v2_struct_0(A_47))), inference(cnfTransformation, [status(thm)], [f_161])).
% 14.23/6.40  tff(c_54, plain, (![A_47, B_59, C_65]: (r3_lattice3(A_47, '#skF_4'(A_47, B_59, C_65), C_65) | k16_lattice3(A_47, C_65)=B_59 | ~r3_lattice3(A_47, B_59, C_65) | ~m1_subset_1(B_59, u1_struct_0(A_47)) | ~l3_lattices(A_47) | ~v4_lattice3(A_47) | ~v10_lattices(A_47) | v2_struct_0(A_47))), inference(cnfTransformation, [status(thm)], [f_161])).
% 14.23/6.40  tff(c_40, plain, (![D_46, B_42, C_43]: (r2_hidden(D_46, a_2_2_lattice3(B_42, C_43)) | ~r4_lattice3(B_42, D_46, C_43) | ~m1_subset_1(D_46, u1_struct_0(B_42)) | ~l3_lattices(B_42) | ~v4_lattice3(B_42) | ~v10_lattices(B_42) | v2_struct_0(B_42))), inference(cnfTransformation, [status(thm)], [f_137])).
% 14.23/6.40  tff(c_103, plain, (![A_108, B_109, D_110, C_111]: (r1_lattices(A_108, B_109, D_110) | ~r2_hidden(D_110, C_111) | ~m1_subset_1(D_110, u1_struct_0(A_108)) | ~r3_lattice3(A_108, B_109, C_111) | ~m1_subset_1(B_109, u1_struct_0(A_108)) | ~l3_lattices(A_108) | v2_struct_0(A_108))), inference(cnfTransformation, [status(thm)], [f_84])).
% 14.23/6.40  tff(c_271, plain, (![B_180, C_176, D_177, A_178, B_179]: (r1_lattices(A_178, B_179, D_177) | ~m1_subset_1(D_177, u1_struct_0(A_178)) | ~r3_lattice3(A_178, B_179, a_2_2_lattice3(B_180, C_176)) | ~m1_subset_1(B_179, u1_struct_0(A_178)) | ~l3_lattices(A_178) | v2_struct_0(A_178) | ~r4_lattice3(B_180, D_177, C_176) | ~m1_subset_1(D_177, u1_struct_0(B_180)) | ~l3_lattices(B_180) | ~v4_lattice3(B_180) | ~v10_lattices(B_180) | v2_struct_0(B_180))), inference(resolution, [status(thm)], [c_40, c_103])).
% 14.23/6.40  tff(c_384, plain, (![B_208, B_209, A_206, C_210, B_207]: (r1_lattices(A_206, B_207, k15_lattice3(A_206, B_208)) | ~r3_lattice3(A_206, B_207, a_2_2_lattice3(B_209, C_210)) | ~m1_subset_1(B_207, u1_struct_0(A_206)) | ~r4_lattice3(B_209, k15_lattice3(A_206, B_208), C_210) | ~m1_subset_1(k15_lattice3(A_206, B_208), u1_struct_0(B_209)) | ~l3_lattices(B_209) | ~v4_lattice3(B_209) | ~v10_lattices(B_209) | v2_struct_0(B_209) | ~l3_lattices(A_206) | v2_struct_0(A_206))), inference(resolution, [status(thm)], [c_38, c_271])).
% 14.23/6.40  tff(c_2666, plain, (![B_590, B_588, B_591, A_587, C_589]: (r1_lattices(A_587, '#skF_4'(A_587, B_588, a_2_2_lattice3(B_591, C_589)), k15_lattice3(A_587, B_590)) | ~m1_subset_1('#skF_4'(A_587, B_588, a_2_2_lattice3(B_591, C_589)), u1_struct_0(A_587)) | ~r4_lattice3(B_591, k15_lattice3(A_587, B_590), C_589) | ~m1_subset_1(k15_lattice3(A_587, B_590), u1_struct_0(B_591)) | ~l3_lattices(B_591) | ~v4_lattice3(B_591) | ~v10_lattices(B_591) | v2_struct_0(B_591) | k16_lattice3(A_587, a_2_2_lattice3(B_591, C_589))=B_588 | ~r3_lattice3(A_587, B_588, a_2_2_lattice3(B_591, C_589)) | ~m1_subset_1(B_588, u1_struct_0(A_587)) | ~l3_lattices(A_587) | ~v4_lattice3(A_587) | ~v10_lattices(A_587) | v2_struct_0(A_587))), inference(resolution, [status(thm)], [c_54, c_384])).
% 14.23/6.40  tff(c_130, plain, (![A_119, B_120, C_121]: (r3_lattices(A_119, B_120, C_121) | ~r1_lattices(A_119, B_120, C_121) | ~m1_subset_1(C_121, u1_struct_0(A_119)) | ~m1_subset_1(B_120, u1_struct_0(A_119)) | ~l3_lattices(A_119) | ~v9_lattices(A_119) | ~v8_lattices(A_119) | ~v6_lattices(A_119) | v2_struct_0(A_119))), inference(cnfTransformation, [status(thm)], [f_66])).
% 14.23/6.40  tff(c_139, plain, (![A_39, B_120, B_40]: (r3_lattices(A_39, B_120, k15_lattice3(A_39, B_40)) | ~r1_lattices(A_39, B_120, k15_lattice3(A_39, B_40)) | ~m1_subset_1(B_120, u1_struct_0(A_39)) | ~v9_lattices(A_39) | ~v8_lattices(A_39) | ~v6_lattices(A_39) | ~l3_lattices(A_39) | v2_struct_0(A_39))), inference(resolution, [status(thm)], [c_38, c_130])).
% 14.23/6.40  tff(c_144, plain, (![A_125, B_126, C_127]: (~r3_lattices(A_125, '#skF_4'(A_125, B_126, C_127), B_126) | k16_lattice3(A_125, C_127)=B_126 | ~r3_lattice3(A_125, B_126, C_127) | ~m1_subset_1(B_126, u1_struct_0(A_125)) | ~l3_lattices(A_125) | ~v4_lattice3(A_125) | ~v10_lattices(A_125) | v2_struct_0(A_125))), inference(cnfTransformation, [status(thm)], [f_161])).
% 14.23/6.40  tff(c_149, plain, (![A_39, C_127, B_40]: (k16_lattice3(A_39, C_127)=k15_lattice3(A_39, B_40) | ~r3_lattice3(A_39, k15_lattice3(A_39, B_40), C_127) | ~m1_subset_1(k15_lattice3(A_39, B_40), u1_struct_0(A_39)) | ~v4_lattice3(A_39) | ~v10_lattices(A_39) | ~r1_lattices(A_39, '#skF_4'(A_39, k15_lattice3(A_39, B_40), C_127), k15_lattice3(A_39, B_40)) | ~m1_subset_1('#skF_4'(A_39, k15_lattice3(A_39, B_40), C_127), u1_struct_0(A_39)) | ~v9_lattices(A_39) | ~v8_lattices(A_39) | ~v6_lattices(A_39) | ~l3_lattices(A_39) | v2_struct_0(A_39))), inference(resolution, [status(thm)], [c_139, c_144])).
% 14.23/6.40  tff(c_6264, plain, (![A_891, B_892, B_893, C_894]: (~v9_lattices(A_891) | ~v8_lattices(A_891) | ~v6_lattices(A_891) | ~m1_subset_1('#skF_4'(A_891, k15_lattice3(A_891, B_892), a_2_2_lattice3(B_893, C_894)), u1_struct_0(A_891)) | ~r4_lattice3(B_893, k15_lattice3(A_891, B_892), C_894) | ~m1_subset_1(k15_lattice3(A_891, B_892), u1_struct_0(B_893)) | ~l3_lattices(B_893) | ~v4_lattice3(B_893) | ~v10_lattices(B_893) | v2_struct_0(B_893) | k16_lattice3(A_891, a_2_2_lattice3(B_893, C_894))=k15_lattice3(A_891, B_892) | ~r3_lattice3(A_891, k15_lattice3(A_891, B_892), a_2_2_lattice3(B_893, C_894)) | ~m1_subset_1(k15_lattice3(A_891, B_892), u1_struct_0(A_891)) | ~l3_lattices(A_891) | ~v4_lattice3(A_891) | ~v10_lattices(A_891) | v2_struct_0(A_891))), inference(resolution, [status(thm)], [c_2666, c_149])).
% 14.23/6.40  tff(c_9478, plain, (![A_985, B_986, B_987, C_988]: (~v9_lattices(A_985) | ~v8_lattices(A_985) | ~v6_lattices(A_985) | ~r4_lattice3(B_986, k15_lattice3(A_985, B_987), C_988) | ~m1_subset_1(k15_lattice3(A_985, B_987), u1_struct_0(B_986)) | ~l3_lattices(B_986) | ~v4_lattice3(B_986) | ~v10_lattices(B_986) | v2_struct_0(B_986) | k16_lattice3(A_985, a_2_2_lattice3(B_986, C_988))=k15_lattice3(A_985, B_987) | ~r3_lattice3(A_985, k15_lattice3(A_985, B_987), a_2_2_lattice3(B_986, C_988)) | ~m1_subset_1(k15_lattice3(A_985, B_987), u1_struct_0(A_985)) | ~l3_lattices(A_985) | ~v4_lattice3(A_985) | ~v10_lattices(A_985) | v2_struct_0(A_985))), inference(resolution, [status(thm)], [c_56, c_6264])).
% 14.23/6.40  tff(c_9486, plain, (![B_989, C_990]: (~v9_lattices(B_989) | ~v8_lattices(B_989) | ~v6_lattices(B_989) | ~r4_lattice3(B_989, k15_lattice3(B_989, C_990), C_990) | k16_lattice3(B_989, a_2_2_lattice3(B_989, C_990))=k15_lattice3(B_989, C_990) | ~v4_lattice3(B_989) | ~v10_lattices(B_989) | ~m1_subset_1(k15_lattice3(B_989, C_990), u1_struct_0(B_989)) | ~l3_lattices(B_989) | v2_struct_0(B_989))), inference(resolution, [status(thm)], [c_722, c_9478])).
% 14.23/6.40  tff(c_9492, plain, (![A_991, B_992]: (~v9_lattices(A_991) | ~v8_lattices(A_991) | ~v6_lattices(A_991) | k16_lattice3(A_991, a_2_2_lattice3(A_991, B_992))=k15_lattice3(A_991, B_992) | ~m1_subset_1(k15_lattice3(A_991, B_992), u1_struct_0(A_991)) | ~v4_lattice3(A_991) | ~v10_lattices(A_991) | ~l3_lattices(A_991) | v2_struct_0(A_991))), inference(resolution, [status(thm)], [c_86, c_9486])).
% 14.23/6.40  tff(c_9500, plain, (![A_993, B_994]: (~v9_lattices(A_993) | ~v8_lattices(A_993) | ~v6_lattices(A_993) | k16_lattice3(A_993, a_2_2_lattice3(A_993, B_994))=k15_lattice3(A_993, B_994) | ~v4_lattice3(A_993) | ~v10_lattices(A_993) | ~l3_lattices(A_993) | v2_struct_0(A_993))), inference(resolution, [status(thm)], [c_38, c_9492])).
% 14.23/6.40  tff(c_58, plain, (k16_lattice3('#skF_5', a_2_2_lattice3('#skF_5', '#skF_6'))!=k15_lattice3('#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_174])).
% 14.23/6.40  tff(c_9510, plain, (~v9_lattices('#skF_5') | ~v8_lattices('#skF_5') | ~v6_lattices('#skF_5') | ~v4_lattice3('#skF_5') | ~v10_lattices('#skF_5') | ~l3_lattices('#skF_5') | v2_struct_0('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_9500, c_58])).
% 14.23/6.40  tff(c_9517, plain, (~v9_lattices('#skF_5') | ~v8_lattices('#skF_5') | ~v6_lattices('#skF_5') | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_64, c_62, c_9510])).
% 14.23/6.40  tff(c_9518, plain, (~v9_lattices('#skF_5') | ~v8_lattices('#skF_5') | ~v6_lattices('#skF_5')), inference(negUnitSimplification, [status(thm)], [c_66, c_9517])).
% 14.23/6.40  tff(c_9520, plain, (~v6_lattices('#skF_5')), inference(splitLeft, [status(thm)], [c_9518])).
% 14.23/6.40  tff(c_9523, plain, (~v10_lattices('#skF_5') | v2_struct_0('#skF_5') | ~l3_lattices('#skF_5')), inference(resolution, [status(thm)], [c_8, c_9520])).
% 14.23/6.40  tff(c_9526, plain, (v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_64, c_9523])).
% 14.23/6.40  tff(c_9528, plain, $false, inference(negUnitSimplification, [status(thm)], [c_66, c_9526])).
% 14.23/6.40  tff(c_9529, plain, (~v8_lattices('#skF_5') | ~v9_lattices('#skF_5')), inference(splitRight, [status(thm)], [c_9518])).
% 14.23/6.40  tff(c_9531, plain, (~v9_lattices('#skF_5')), inference(splitLeft, [status(thm)], [c_9529])).
% 14.23/6.40  tff(c_9534, plain, (~v10_lattices('#skF_5') | v2_struct_0('#skF_5') | ~l3_lattices('#skF_5')), inference(resolution, [status(thm)], [c_2, c_9531])).
% 14.23/6.40  tff(c_9537, plain, (v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_64, c_9534])).
% 14.23/6.40  tff(c_9539, plain, $false, inference(negUnitSimplification, [status(thm)], [c_66, c_9537])).
% 14.23/6.40  tff(c_9540, plain, (~v8_lattices('#skF_5')), inference(splitRight, [status(thm)], [c_9529])).
% 14.23/6.40  tff(c_9565, plain, (~v10_lattices('#skF_5') | v2_struct_0('#skF_5') | ~l3_lattices('#skF_5')), inference(resolution, [status(thm)], [c_4, c_9540])).
% 14.23/6.40  tff(c_9568, plain, (v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_64, c_9565])).
% 14.23/6.40  tff(c_9570, plain, $false, inference(negUnitSimplification, [status(thm)], [c_66, c_9568])).
% 14.23/6.40  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 14.23/6.40  
% 14.23/6.40  Inference rules
% 14.23/6.40  ----------------------
% 14.23/6.40  #Ref     : 0
% 14.23/6.40  #Sup     : 2752
% 14.23/6.40  #Fact    : 0
% 14.23/6.40  #Define  : 0
% 14.23/6.40  #Split   : 2
% 14.23/6.40  #Chain   : 0
% 14.23/6.40  #Close   : 0
% 14.23/6.40  
% 14.23/6.40  Ordering : KBO
% 14.23/6.40  
% 14.23/6.40  Simplification rules
% 14.23/6.40  ----------------------
% 14.23/6.40  #Subsume      : 576
% 14.23/6.40  #Demod        : 9
% 14.23/6.40  #Tautology    : 668
% 14.23/6.40  #SimpNegUnit  : 4
% 14.23/6.40  #BackRed      : 0
% 14.23/6.40  
% 14.23/6.40  #Partial instantiations: 0
% 14.23/6.40  #Strategies tried      : 1
% 14.23/6.40  
% 14.23/6.40  Timing (in seconds)
% 14.23/6.40  ----------------------
% 14.23/6.40  Preprocessing        : 0.34
% 14.23/6.40  Parsing              : 0.18
% 14.23/6.40  CNF conversion       : 0.03
% 14.23/6.40  Main loop            : 5.32
% 14.23/6.40  Inferencing          : 1.21
% 14.23/6.40  Reduction            : 0.60
% 14.23/6.40  Demodulation         : 0.39
% 14.23/6.40  BG Simplification    : 0.16
% 14.23/6.40  Subsumption          : 3.18
% 14.23/6.40  Abstraction          : 0.18
% 14.23/6.40  MUC search           : 0.00
% 14.23/6.40  Cooper               : 0.00
% 14.23/6.40  Total                : 5.69
% 14.23/6.40  Index Insertion      : 0.00
% 14.23/6.40  Index Deletion       : 0.00
% 14.23/6.40  Index Matching       : 0.00
% 14.23/6.40  BG Taut test         : 0.00
%------------------------------------------------------------------------------
