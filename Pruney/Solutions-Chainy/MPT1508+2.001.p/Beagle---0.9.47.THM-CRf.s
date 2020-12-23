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
% DateTime   : Thu Dec  3 10:24:47 EST 2020

% Result     : Theorem 3.42s
% Output     : CNFRefutation 3.57s
% Verified   : 
% Statistics : Number of formulae       :  124 ( 379 expanded)
%              Number of leaves         :   39 ( 147 expanded)
%              Depth                    :   19
%              Number of atoms          :  400 (1654 expanded)
%              Number of equality atoms :   40 ( 135 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r3_lattices > r3_lattice3 > r1_lattices > r2_hidden > m1_subset_1 > v9_lattices > v8_lattices > v7_lattices > v6_lattices > v5_lattices > v4_lattices > v4_lattice3 > v2_struct_0 > v10_lattices > l3_lattices > l2_lattices > l1_lattices > k3_lattices > k1_lattices > k16_lattice3 > k15_lattice3 > #nlpp > u1_struct_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4

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

tff(k1_lattices,type,(
    k1_lattices: ( $i * $i * $i ) > $i )).

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

tff(f_183,negated_conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_lattice3)).

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

tff(f_113,axiom,(
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

tff(f_81,axiom,(
    ! [A] :
      ( l3_lattices(A)
     => ( l1_lattices(A)
        & l2_lattices(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l3_lattices)).

tff(f_120,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & l3_lattices(A) )
     => m1_subset_1(k16_lattice3(A,B),u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k16_lattice3)).

tff(f_144,axiom,(
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

tff(f_75,axiom,(
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

tff(f_94,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(A)
        & v4_lattices(A)
        & l2_lattices(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,u1_struct_0(A)) )
     => k3_lattices(A,B,C) = k1_lattices(A,B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k3_lattices)).

tff(f_60,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(A)
        & v4_lattices(A)
        & l2_lattices(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,u1_struct_0(A)) )
     => k3_lattices(A,B,C) = k3_lattices(A,C,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_lattices)).

tff(f_163,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_lattice3)).

tff(c_48,plain,(
    k16_lattice3('#skF_2','#skF_4') != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_183])).

tff(c_52,plain,(
    r2_hidden('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_183])).

tff(c_50,plain,(
    r3_lattice3('#skF_2','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_183])).

tff(c_62,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_183])).

tff(c_56,plain,(
    l3_lattices('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_183])).

tff(c_60,plain,(
    v10_lattices('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_183])).

tff(c_58,plain,(
    v4_lattice3('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_183])).

tff(c_8,plain,(
    ! [A_1] :
      ( v6_lattices(A_1)
      | ~ v10_lattices(A_1)
      | v2_struct_0(A_1)
      | ~ l3_lattices(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_54,plain,(
    m1_subset_1('#skF_3',u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_183])).

tff(c_200,plain,(
    ! [A_92,B_93,C_94] :
      ( r3_lattices(A_92,B_93,C_94)
      | ~ r1_lattices(A_92,B_93,C_94)
      | ~ m1_subset_1(C_94,u1_struct_0(A_92))
      | ~ m1_subset_1(B_93,u1_struct_0(A_92))
      | ~ l3_lattices(A_92)
      | ~ v9_lattices(A_92)
      | ~ v8_lattices(A_92)
      | ~ v6_lattices(A_92)
      | v2_struct_0(A_92) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_204,plain,(
    ! [B_93] :
      ( r3_lattices('#skF_2',B_93,'#skF_3')
      | ~ r1_lattices('#skF_2',B_93,'#skF_3')
      | ~ m1_subset_1(B_93,u1_struct_0('#skF_2'))
      | ~ l3_lattices('#skF_2')
      | ~ v9_lattices('#skF_2')
      | ~ v8_lattices('#skF_2')
      | ~ v6_lattices('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_54,c_200])).

tff(c_208,plain,(
    ! [B_93] :
      ( r3_lattices('#skF_2',B_93,'#skF_3')
      | ~ r1_lattices('#skF_2',B_93,'#skF_3')
      | ~ m1_subset_1(B_93,u1_struct_0('#skF_2'))
      | ~ v9_lattices('#skF_2')
      | ~ v8_lattices('#skF_2')
      | ~ v6_lattices('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_204])).

tff(c_209,plain,(
    ! [B_93] :
      ( r3_lattices('#skF_2',B_93,'#skF_3')
      | ~ r1_lattices('#skF_2',B_93,'#skF_3')
      | ~ m1_subset_1(B_93,u1_struct_0('#skF_2'))
      | ~ v9_lattices('#skF_2')
      | ~ v8_lattices('#skF_2')
      | ~ v6_lattices('#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_208])).

tff(c_210,plain,(
    ~ v6_lattices('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_209])).

tff(c_213,plain,
    ( ~ v10_lattices('#skF_2')
    | v2_struct_0('#skF_2')
    | ~ l3_lattices('#skF_2') ),
    inference(resolution,[status(thm)],[c_8,c_210])).

tff(c_216,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_60,c_213])).

tff(c_218,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_216])).

tff(c_220,plain,(
    v6_lattices('#skF_2') ),
    inference(splitRight,[status(thm)],[c_209])).

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

tff(c_219,plain,(
    ! [B_93] :
      ( ~ v8_lattices('#skF_2')
      | ~ v9_lattices('#skF_2')
      | r3_lattices('#skF_2',B_93,'#skF_3')
      | ~ r1_lattices('#skF_2',B_93,'#skF_3')
      | ~ m1_subset_1(B_93,u1_struct_0('#skF_2')) ) ),
    inference(splitRight,[status(thm)],[c_209])).

tff(c_221,plain,(
    ~ v9_lattices('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_219])).

tff(c_224,plain,
    ( ~ v10_lattices('#skF_2')
    | v2_struct_0('#skF_2')
    | ~ l3_lattices('#skF_2') ),
    inference(resolution,[status(thm)],[c_2,c_221])).

tff(c_227,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_60,c_224])).

tff(c_229,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_227])).

tff(c_230,plain,(
    ! [B_93] :
      ( ~ v8_lattices('#skF_2')
      | r3_lattices('#skF_2',B_93,'#skF_3')
      | ~ r1_lattices('#skF_2',B_93,'#skF_3')
      | ~ m1_subset_1(B_93,u1_struct_0('#skF_2')) ) ),
    inference(splitRight,[status(thm)],[c_219])).

tff(c_239,plain,(
    ~ v8_lattices('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_230])).

tff(c_242,plain,
    ( ~ v10_lattices('#skF_2')
    | v2_struct_0('#skF_2')
    | ~ l3_lattices('#skF_2') ),
    inference(resolution,[status(thm)],[c_4,c_239])).

tff(c_245,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_60,c_242])).

tff(c_247,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_245])).

tff(c_249,plain,(
    v8_lattices('#skF_2') ),
    inference(splitRight,[status(thm)],[c_230])).

tff(c_231,plain,(
    v9_lattices('#skF_2') ),
    inference(splitRight,[status(thm)],[c_219])).

tff(c_63,plain,(
    ! [A_54] :
      ( l2_lattices(A_54)
      | ~ l3_lattices(A_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_67,plain,(
    l2_lattices('#skF_2') ),
    inference(resolution,[status(thm)],[c_56,c_63])).

tff(c_32,plain,(
    ! [A_19,B_20] :
      ( m1_subset_1(k16_lattice3(A_19,B_20),u1_struct_0(A_19))
      | ~ l3_lattices(A_19)
      | v2_struct_0(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_544,plain,(
    ! [A_143,D_144,C_145] :
      ( r3_lattices(A_143,D_144,k16_lattice3(A_143,C_145))
      | ~ r3_lattice3(A_143,D_144,C_145)
      | ~ m1_subset_1(D_144,u1_struct_0(A_143))
      | ~ m1_subset_1(k16_lattice3(A_143,C_145),u1_struct_0(A_143))
      | ~ l3_lattices(A_143)
      | ~ v4_lattice3(A_143)
      | ~ v10_lattices(A_143)
      | v2_struct_0(A_143) ) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_548,plain,(
    ! [A_146,D_147,B_148] :
      ( r3_lattices(A_146,D_147,k16_lattice3(A_146,B_148))
      | ~ r3_lattice3(A_146,D_147,B_148)
      | ~ m1_subset_1(D_147,u1_struct_0(A_146))
      | ~ v4_lattice3(A_146)
      | ~ v10_lattices(A_146)
      | ~ l3_lattices(A_146)
      | v2_struct_0(A_146) ) ),
    inference(resolution,[status(thm)],[c_32,c_544])).

tff(c_30,plain,(
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
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_650,plain,(
    ! [A_172,D_173,B_174] :
      ( r1_lattices(A_172,D_173,k16_lattice3(A_172,B_174))
      | ~ m1_subset_1(k16_lattice3(A_172,B_174),u1_struct_0(A_172))
      | ~ v9_lattices(A_172)
      | ~ v8_lattices(A_172)
      | ~ v6_lattices(A_172)
      | ~ r3_lattice3(A_172,D_173,B_174)
      | ~ m1_subset_1(D_173,u1_struct_0(A_172))
      | ~ v4_lattice3(A_172)
      | ~ v10_lattices(A_172)
      | ~ l3_lattices(A_172)
      | v2_struct_0(A_172) ) ),
    inference(resolution,[status(thm)],[c_548,c_30])).

tff(c_654,plain,(
    ! [A_175,D_176,B_177] :
      ( r1_lattices(A_175,D_176,k16_lattice3(A_175,B_177))
      | ~ v9_lattices(A_175)
      | ~ v8_lattices(A_175)
      | ~ v6_lattices(A_175)
      | ~ r3_lattice3(A_175,D_176,B_177)
      | ~ m1_subset_1(D_176,u1_struct_0(A_175))
      | ~ v4_lattice3(A_175)
      | ~ v10_lattices(A_175)
      | ~ l3_lattices(A_175)
      | v2_struct_0(A_175) ) ),
    inference(resolution,[status(thm)],[c_32,c_650])).

tff(c_20,plain,(
    ! [A_5,B_9,C_11] :
      ( k1_lattices(A_5,B_9,C_11) = C_11
      | ~ r1_lattices(A_5,B_9,C_11)
      | ~ m1_subset_1(C_11,u1_struct_0(A_5))
      | ~ m1_subset_1(B_9,u1_struct_0(A_5))
      | ~ l2_lattices(A_5)
      | v2_struct_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_706,plain,(
    ! [A_192,D_193,B_194] :
      ( k1_lattices(A_192,D_193,k16_lattice3(A_192,B_194)) = k16_lattice3(A_192,B_194)
      | ~ m1_subset_1(k16_lattice3(A_192,B_194),u1_struct_0(A_192))
      | ~ l2_lattices(A_192)
      | ~ v9_lattices(A_192)
      | ~ v8_lattices(A_192)
      | ~ v6_lattices(A_192)
      | ~ r3_lattice3(A_192,D_193,B_194)
      | ~ m1_subset_1(D_193,u1_struct_0(A_192))
      | ~ v4_lattice3(A_192)
      | ~ v10_lattices(A_192)
      | ~ l3_lattices(A_192)
      | v2_struct_0(A_192) ) ),
    inference(resolution,[status(thm)],[c_654,c_20])).

tff(c_710,plain,(
    ! [A_195,D_196,B_197] :
      ( k1_lattices(A_195,D_196,k16_lattice3(A_195,B_197)) = k16_lattice3(A_195,B_197)
      | ~ l2_lattices(A_195)
      | ~ v9_lattices(A_195)
      | ~ v8_lattices(A_195)
      | ~ v6_lattices(A_195)
      | ~ r3_lattice3(A_195,D_196,B_197)
      | ~ m1_subset_1(D_196,u1_struct_0(A_195))
      | ~ v4_lattice3(A_195)
      | ~ v10_lattices(A_195)
      | ~ l3_lattices(A_195)
      | v2_struct_0(A_195) ) ),
    inference(resolution,[status(thm)],[c_32,c_706])).

tff(c_716,plain,(
    ! [B_197] :
      ( k1_lattices('#skF_2','#skF_3',k16_lattice3('#skF_2',B_197)) = k16_lattice3('#skF_2',B_197)
      | ~ l2_lattices('#skF_2')
      | ~ v9_lattices('#skF_2')
      | ~ v8_lattices('#skF_2')
      | ~ v6_lattices('#skF_2')
      | ~ r3_lattice3('#skF_2','#skF_3',B_197)
      | ~ v4_lattice3('#skF_2')
      | ~ v10_lattices('#skF_2')
      | ~ l3_lattices('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_54,c_710])).

tff(c_721,plain,(
    ! [B_197] :
      ( k1_lattices('#skF_2','#skF_3',k16_lattice3('#skF_2',B_197)) = k16_lattice3('#skF_2',B_197)
      | ~ r3_lattice3('#skF_2','#skF_3',B_197)
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_60,c_58,c_220,c_249,c_231,c_67,c_716])).

tff(c_723,plain,(
    ! [B_198] :
      ( k1_lattices('#skF_2','#skF_3',k16_lattice3('#skF_2',B_198)) = k16_lattice3('#skF_2',B_198)
      | ~ r3_lattice3('#skF_2','#skF_3',B_198) ) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_721])).

tff(c_12,plain,(
    ! [A_1] :
      ( v4_lattices(A_1)
      | ~ v10_lattices(A_1)
      | v2_struct_0(A_1)
      | ~ l3_lattices(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_119,plain,(
    ! [A_82,B_83,C_84] :
      ( k3_lattices(A_82,B_83,C_84) = k1_lattices(A_82,B_83,C_84)
      | ~ m1_subset_1(C_84,u1_struct_0(A_82))
      | ~ m1_subset_1(B_83,u1_struct_0(A_82))
      | ~ l2_lattices(A_82)
      | ~ v4_lattices(A_82)
      | v2_struct_0(A_82) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_123,plain,(
    ! [B_83] :
      ( k3_lattices('#skF_2',B_83,'#skF_3') = k1_lattices('#skF_2',B_83,'#skF_3')
      | ~ m1_subset_1(B_83,u1_struct_0('#skF_2'))
      | ~ l2_lattices('#skF_2')
      | ~ v4_lattices('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_54,c_119])).

tff(c_127,plain,(
    ! [B_83] :
      ( k3_lattices('#skF_2',B_83,'#skF_3') = k1_lattices('#skF_2',B_83,'#skF_3')
      | ~ m1_subset_1(B_83,u1_struct_0('#skF_2'))
      | ~ v4_lattices('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_67,c_123])).

tff(c_128,plain,(
    ! [B_83] :
      ( k3_lattices('#skF_2',B_83,'#skF_3') = k1_lattices('#skF_2',B_83,'#skF_3')
      | ~ m1_subset_1(B_83,u1_struct_0('#skF_2'))
      | ~ v4_lattices('#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_127])).

tff(c_129,plain,(
    ~ v4_lattices('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_128])).

tff(c_132,plain,
    ( ~ v10_lattices('#skF_2')
    | v2_struct_0('#skF_2')
    | ~ l3_lattices('#skF_2') ),
    inference(resolution,[status(thm)],[c_12,c_129])).

tff(c_135,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_60,c_132])).

tff(c_137,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_135])).

tff(c_139,plain,(
    v4_lattices('#skF_2') ),
    inference(splitRight,[status(thm)],[c_128])).

tff(c_140,plain,(
    ! [B_85] :
      ( k3_lattices('#skF_2',B_85,'#skF_3') = k1_lattices('#skF_2',B_85,'#skF_3')
      | ~ m1_subset_1(B_85,u1_struct_0('#skF_2')) ) ),
    inference(splitRight,[status(thm)],[c_128])).

tff(c_144,plain,(
    ! [B_20] :
      ( k3_lattices('#skF_2',k16_lattice3('#skF_2',B_20),'#skF_3') = k1_lattices('#skF_2',k16_lattice3('#skF_2',B_20),'#skF_3')
      | ~ l3_lattices('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_32,c_140])).

tff(c_150,plain,(
    ! [B_20] :
      ( k3_lattices('#skF_2',k16_lattice3('#skF_2',B_20),'#skF_3') = k1_lattices('#skF_2',k16_lattice3('#skF_2',B_20),'#skF_3')
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_144])).

tff(c_151,plain,(
    ! [B_20] : k3_lattices('#skF_2',k16_lattice3('#skF_2',B_20),'#skF_3') = k1_lattices('#skF_2',k16_lattice3('#skF_2',B_20),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_150])).

tff(c_157,plain,(
    ! [A_86,C_87,B_88] :
      ( k3_lattices(A_86,C_87,B_88) = k3_lattices(A_86,B_88,C_87)
      | ~ m1_subset_1(C_87,u1_struct_0(A_86))
      | ~ m1_subset_1(B_88,u1_struct_0(A_86))
      | ~ l2_lattices(A_86)
      | ~ v4_lattices(A_86)
      | v2_struct_0(A_86) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_161,plain,(
    ! [B_88] :
      ( k3_lattices('#skF_2',B_88,'#skF_3') = k3_lattices('#skF_2','#skF_3',B_88)
      | ~ m1_subset_1(B_88,u1_struct_0('#skF_2'))
      | ~ l2_lattices('#skF_2')
      | ~ v4_lattices('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_54,c_157])).

tff(c_165,plain,(
    ! [B_88] :
      ( k3_lattices('#skF_2',B_88,'#skF_3') = k3_lattices('#skF_2','#skF_3',B_88)
      | ~ m1_subset_1(B_88,u1_struct_0('#skF_2'))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_139,c_67,c_161])).

tff(c_167,plain,(
    ! [B_89] :
      ( k3_lattices('#skF_2',B_89,'#skF_3') = k3_lattices('#skF_2','#skF_3',B_89)
      | ~ m1_subset_1(B_89,u1_struct_0('#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_165])).

tff(c_171,plain,(
    ! [B_20] :
      ( k3_lattices('#skF_2',k16_lattice3('#skF_2',B_20),'#skF_3') = k3_lattices('#skF_2','#skF_3',k16_lattice3('#skF_2',B_20))
      | ~ l3_lattices('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_32,c_167])).

tff(c_177,plain,(
    ! [B_20] :
      ( k3_lattices('#skF_2',k16_lattice3('#skF_2',B_20),'#skF_3') = k3_lattices('#skF_2','#skF_3',k16_lattice3('#skF_2',B_20))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_171])).

tff(c_178,plain,(
    ! [B_20] : k3_lattices('#skF_2',k16_lattice3('#skF_2',B_20),'#skF_3') = k3_lattices('#skF_2','#skF_3',k16_lattice3('#skF_2',B_20)) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_177])).

tff(c_190,plain,(
    ! [B_20] : k3_lattices('#skF_2','#skF_3',k16_lattice3('#skF_2',B_20)) = k1_lattices('#skF_2',k16_lattice3('#skF_2',B_20),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_151,c_178])).

tff(c_329,plain,(
    ! [A_106,B_107,B_108] :
      ( k3_lattices(A_106,B_107,k16_lattice3(A_106,B_108)) = k1_lattices(A_106,B_107,k16_lattice3(A_106,B_108))
      | ~ m1_subset_1(B_107,u1_struct_0(A_106))
      | ~ l2_lattices(A_106)
      | ~ v4_lattices(A_106)
      | ~ l3_lattices(A_106)
      | v2_struct_0(A_106) ) ),
    inference(resolution,[status(thm)],[c_32,c_119])).

tff(c_335,plain,(
    ! [B_108] :
      ( k3_lattices('#skF_2','#skF_3',k16_lattice3('#skF_2',B_108)) = k1_lattices('#skF_2','#skF_3',k16_lattice3('#skF_2',B_108))
      | ~ l2_lattices('#skF_2')
      | ~ v4_lattices('#skF_2')
      | ~ l3_lattices('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_54,c_329])).

tff(c_340,plain,(
    ! [B_108] :
      ( k1_lattices('#skF_2',k16_lattice3('#skF_2',B_108),'#skF_3') = k1_lattices('#skF_2','#skF_3',k16_lattice3('#skF_2',B_108))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_139,c_67,c_190,c_335])).

tff(c_341,plain,(
    ! [B_108] : k1_lattices('#skF_2',k16_lattice3('#skF_2',B_108),'#skF_3') = k1_lattices('#skF_2','#skF_3',k16_lattice3('#skF_2',B_108)) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_340])).

tff(c_44,plain,(
    ! [A_43,C_49,B_47] :
      ( r3_lattices(A_43,k16_lattice3(A_43,C_49),B_47)
      | ~ r2_hidden(B_47,C_49)
      | ~ m1_subset_1(B_47,u1_struct_0(A_43))
      | ~ l3_lattices(A_43)
      | ~ v4_lattice3(A_43)
      | ~ v10_lattices(A_43)
      | v2_struct_0(A_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_232,plain,(
    ! [A_95,B_96,C_97] :
      ( r1_lattices(A_95,B_96,C_97)
      | ~ r3_lattices(A_95,B_96,C_97)
      | ~ m1_subset_1(C_97,u1_struct_0(A_95))
      | ~ m1_subset_1(B_96,u1_struct_0(A_95))
      | ~ l3_lattices(A_95)
      | ~ v9_lattices(A_95)
      | ~ v8_lattices(A_95)
      | ~ v6_lattices(A_95)
      | v2_struct_0(A_95) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_626,plain,(
    ! [A_160,C_161,B_162] :
      ( r1_lattices(A_160,k16_lattice3(A_160,C_161),B_162)
      | ~ m1_subset_1(k16_lattice3(A_160,C_161),u1_struct_0(A_160))
      | ~ v9_lattices(A_160)
      | ~ v8_lattices(A_160)
      | ~ v6_lattices(A_160)
      | ~ r2_hidden(B_162,C_161)
      | ~ m1_subset_1(B_162,u1_struct_0(A_160))
      | ~ l3_lattices(A_160)
      | ~ v4_lattice3(A_160)
      | ~ v10_lattices(A_160)
      | v2_struct_0(A_160) ) ),
    inference(resolution,[status(thm)],[c_44,c_232])).

tff(c_630,plain,(
    ! [A_163,B_164,B_165] :
      ( r1_lattices(A_163,k16_lattice3(A_163,B_164),B_165)
      | ~ v9_lattices(A_163)
      | ~ v8_lattices(A_163)
      | ~ v6_lattices(A_163)
      | ~ r2_hidden(B_165,B_164)
      | ~ m1_subset_1(B_165,u1_struct_0(A_163))
      | ~ v4_lattice3(A_163)
      | ~ v10_lattices(A_163)
      | ~ l3_lattices(A_163)
      | v2_struct_0(A_163) ) ),
    inference(resolution,[status(thm)],[c_32,c_626])).

tff(c_658,plain,(
    ! [A_178,B_179,B_180] :
      ( k1_lattices(A_178,k16_lattice3(A_178,B_179),B_180) = B_180
      | ~ m1_subset_1(k16_lattice3(A_178,B_179),u1_struct_0(A_178))
      | ~ l2_lattices(A_178)
      | ~ v9_lattices(A_178)
      | ~ v8_lattices(A_178)
      | ~ v6_lattices(A_178)
      | ~ r2_hidden(B_180,B_179)
      | ~ m1_subset_1(B_180,u1_struct_0(A_178))
      | ~ v4_lattice3(A_178)
      | ~ v10_lattices(A_178)
      | ~ l3_lattices(A_178)
      | v2_struct_0(A_178) ) ),
    inference(resolution,[status(thm)],[c_630,c_20])).

tff(c_662,plain,(
    ! [A_181,B_182,B_183] :
      ( k1_lattices(A_181,k16_lattice3(A_181,B_182),B_183) = B_183
      | ~ l2_lattices(A_181)
      | ~ v9_lattices(A_181)
      | ~ v8_lattices(A_181)
      | ~ v6_lattices(A_181)
      | ~ r2_hidden(B_183,B_182)
      | ~ m1_subset_1(B_183,u1_struct_0(A_181))
      | ~ v4_lattice3(A_181)
      | ~ v10_lattices(A_181)
      | ~ l3_lattices(A_181)
      | v2_struct_0(A_181) ) ),
    inference(resolution,[status(thm)],[c_32,c_658])).

tff(c_668,plain,(
    ! [B_182] :
      ( k1_lattices('#skF_2',k16_lattice3('#skF_2',B_182),'#skF_3') = '#skF_3'
      | ~ l2_lattices('#skF_2')
      | ~ v9_lattices('#skF_2')
      | ~ v8_lattices('#skF_2')
      | ~ v6_lattices('#skF_2')
      | ~ r2_hidden('#skF_3',B_182)
      | ~ v4_lattice3('#skF_2')
      | ~ v10_lattices('#skF_2')
      | ~ l3_lattices('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_54,c_662])).

tff(c_673,plain,(
    ! [B_182] :
      ( k1_lattices('#skF_2','#skF_3',k16_lattice3('#skF_2',B_182)) = '#skF_3'
      | ~ r2_hidden('#skF_3',B_182)
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_60,c_58,c_220,c_249,c_231,c_67,c_341,c_668])).

tff(c_674,plain,(
    ! [B_182] :
      ( k1_lattices('#skF_2','#skF_3',k16_lattice3('#skF_2',B_182)) = '#skF_3'
      | ~ r2_hidden('#skF_3',B_182) ) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_673])).

tff(c_738,plain,(
    ! [B_199] :
      ( k16_lattice3('#skF_2',B_199) = '#skF_3'
      | ~ r2_hidden('#skF_3',B_199)
      | ~ r3_lattice3('#skF_2','#skF_3',B_199) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_723,c_674])).

tff(c_741,plain,
    ( k16_lattice3('#skF_2','#skF_4') = '#skF_3'
    | ~ r2_hidden('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_50,c_738])).

tff(c_744,plain,(
    k16_lattice3('#skF_2','#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_741])).

tff(c_746,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_744])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n023.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 11:58:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.42/1.53  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.42/1.54  
% 3.42/1.54  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.42/1.54  %$ r3_lattices > r3_lattice3 > r1_lattices > r2_hidden > m1_subset_1 > v9_lattices > v8_lattices > v7_lattices > v6_lattices > v5_lattices > v4_lattices > v4_lattice3 > v2_struct_0 > v10_lattices > l3_lattices > l2_lattices > l1_lattices > k3_lattices > k1_lattices > k16_lattice3 > k15_lattice3 > #nlpp > u1_struct_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4
% 3.42/1.54  
% 3.42/1.54  %Foreground sorts:
% 3.42/1.54  
% 3.42/1.54  
% 3.42/1.54  %Background operators:
% 3.42/1.54  
% 3.42/1.54  
% 3.42/1.54  %Foreground operators:
% 3.42/1.54  tff(l3_lattices, type, l3_lattices: $i > $o).
% 3.42/1.54  tff(k3_lattices, type, k3_lattices: ($i * $i * $i) > $i).
% 3.42/1.54  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.42/1.54  tff(l2_lattices, type, l2_lattices: $i > $o).
% 3.42/1.54  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 3.42/1.54  tff(r3_lattices, type, r3_lattices: ($i * $i * $i) > $o).
% 3.42/1.54  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.42/1.54  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.42/1.54  tff(k16_lattice3, type, k16_lattice3: ($i * $i) > $i).
% 3.42/1.54  tff(k1_lattices, type, k1_lattices: ($i * $i * $i) > $i).
% 3.42/1.54  tff(k15_lattice3, type, k15_lattice3: ($i * $i) > $i).
% 3.42/1.54  tff(l1_lattices, type, l1_lattices: $i > $o).
% 3.42/1.54  tff(r1_lattices, type, r1_lattices: ($i * $i * $i) > $o).
% 3.42/1.54  tff(v4_lattices, type, v4_lattices: $i > $o).
% 3.42/1.54  tff(v6_lattices, type, v6_lattices: $i > $o).
% 3.42/1.54  tff('#skF_2', type, '#skF_2': $i).
% 3.42/1.54  tff(v9_lattices, type, v9_lattices: $i > $o).
% 3.42/1.54  tff('#skF_3', type, '#skF_3': $i).
% 3.42/1.54  tff(v4_lattice3, type, v4_lattice3: $i > $o).
% 3.42/1.54  tff(v5_lattices, type, v5_lattices: $i > $o).
% 3.42/1.54  tff(v10_lattices, type, v10_lattices: $i > $o).
% 3.42/1.54  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.42/1.54  tff('#skF_4', type, '#skF_4': $i).
% 3.42/1.54  tff(v8_lattices, type, v8_lattices: $i > $o).
% 3.42/1.54  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.42/1.54  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.42/1.54  tff(r3_lattice3, type, r3_lattice3: ($i * $i * $i) > $o).
% 3.42/1.54  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.42/1.54  tff(v7_lattices, type, v7_lattices: $i > $o).
% 3.42/1.54  
% 3.57/1.56  tff(f_183, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v10_lattices(A)) & v4_lattice3(A)) & l3_lattices(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: ((r2_hidden(B, C) & r3_lattice3(A, B, C)) => (k16_lattice3(A, C) = B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t42_lattice3)).
% 3.57/1.56  tff(f_47, axiom, (![A]: (l3_lattices(A) => ((~v2_struct_0(A) & v10_lattices(A)) => ((((((~v2_struct_0(A) & v4_lattices(A)) & v5_lattices(A)) & v6_lattices(A)) & v7_lattices(A)) & v8_lattices(A)) & v9_lattices(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_lattices)).
% 3.57/1.56  tff(f_113, axiom, (![A, B, C]: (((((((~v2_struct_0(A) & v6_lattices(A)) & v8_lattices(A)) & v9_lattices(A)) & l3_lattices(A)) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => (r3_lattices(A, B, C) <=> r1_lattices(A, B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r3_lattices)).
% 3.57/1.56  tff(f_81, axiom, (![A]: (l3_lattices(A) => (l1_lattices(A) & l2_lattices(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l3_lattices)).
% 3.57/1.56  tff(f_120, axiom, (![A, B]: ((~v2_struct_0(A) & l3_lattices(A)) => m1_subset_1(k16_lattice3(A, B), u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k16_lattice3)).
% 3.57/1.56  tff(f_144, axiom, (![A]: ((((~v2_struct_0(A) & v10_lattices(A)) & v4_lattice3(A)) & l3_lattices(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: ((B = k16_lattice3(A, C)) <=> (r3_lattice3(A, B, C) & (![D]: (m1_subset_1(D, u1_struct_0(A)) => (r3_lattice3(A, D, C) => r3_lattices(A, D, B))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t34_lattice3)).
% 3.57/1.56  tff(f_75, axiom, (![A]: ((~v2_struct_0(A) & l2_lattices(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r1_lattices(A, B, C) <=> (k1_lattices(A, B, C) = C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_lattices)).
% 3.57/1.56  tff(f_94, axiom, (![A, B, C]: (((((~v2_struct_0(A) & v4_lattices(A)) & l2_lattices(A)) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => (k3_lattices(A, B, C) = k1_lattices(A, B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k3_lattices)).
% 3.57/1.56  tff(f_60, axiom, (![A, B, C]: (((((~v2_struct_0(A) & v4_lattices(A)) & l2_lattices(A)) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => (k3_lattices(A, B, C) = k3_lattices(A, C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_lattices)).
% 3.57/1.56  tff(f_163, axiom, (![A]: ((((~v2_struct_0(A) & v10_lattices(A)) & v4_lattice3(A)) & l3_lattices(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (r2_hidden(B, C) => (r3_lattices(A, B, k15_lattice3(A, C)) & r3_lattices(A, k16_lattice3(A, C), B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_lattice3)).
% 3.57/1.56  tff(c_48, plain, (k16_lattice3('#skF_2', '#skF_4')!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_183])).
% 3.57/1.56  tff(c_52, plain, (r2_hidden('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_183])).
% 3.57/1.56  tff(c_50, plain, (r3_lattice3('#skF_2', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_183])).
% 3.57/1.56  tff(c_62, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_183])).
% 3.57/1.56  tff(c_56, plain, (l3_lattices('#skF_2')), inference(cnfTransformation, [status(thm)], [f_183])).
% 3.57/1.56  tff(c_60, plain, (v10_lattices('#skF_2')), inference(cnfTransformation, [status(thm)], [f_183])).
% 3.57/1.56  tff(c_58, plain, (v4_lattice3('#skF_2')), inference(cnfTransformation, [status(thm)], [f_183])).
% 3.57/1.56  tff(c_8, plain, (![A_1]: (v6_lattices(A_1) | ~v10_lattices(A_1) | v2_struct_0(A_1) | ~l3_lattices(A_1))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.57/1.56  tff(c_54, plain, (m1_subset_1('#skF_3', u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_183])).
% 3.57/1.56  tff(c_200, plain, (![A_92, B_93, C_94]: (r3_lattices(A_92, B_93, C_94) | ~r1_lattices(A_92, B_93, C_94) | ~m1_subset_1(C_94, u1_struct_0(A_92)) | ~m1_subset_1(B_93, u1_struct_0(A_92)) | ~l3_lattices(A_92) | ~v9_lattices(A_92) | ~v8_lattices(A_92) | ~v6_lattices(A_92) | v2_struct_0(A_92))), inference(cnfTransformation, [status(thm)], [f_113])).
% 3.57/1.56  tff(c_204, plain, (![B_93]: (r3_lattices('#skF_2', B_93, '#skF_3') | ~r1_lattices('#skF_2', B_93, '#skF_3') | ~m1_subset_1(B_93, u1_struct_0('#skF_2')) | ~l3_lattices('#skF_2') | ~v9_lattices('#skF_2') | ~v8_lattices('#skF_2') | ~v6_lattices('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_54, c_200])).
% 3.57/1.56  tff(c_208, plain, (![B_93]: (r3_lattices('#skF_2', B_93, '#skF_3') | ~r1_lattices('#skF_2', B_93, '#skF_3') | ~m1_subset_1(B_93, u1_struct_0('#skF_2')) | ~v9_lattices('#skF_2') | ~v8_lattices('#skF_2') | ~v6_lattices('#skF_2') | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_204])).
% 3.57/1.56  tff(c_209, plain, (![B_93]: (r3_lattices('#skF_2', B_93, '#skF_3') | ~r1_lattices('#skF_2', B_93, '#skF_3') | ~m1_subset_1(B_93, u1_struct_0('#skF_2')) | ~v9_lattices('#skF_2') | ~v8_lattices('#skF_2') | ~v6_lattices('#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_62, c_208])).
% 3.57/1.56  tff(c_210, plain, (~v6_lattices('#skF_2')), inference(splitLeft, [status(thm)], [c_209])).
% 3.57/1.56  tff(c_213, plain, (~v10_lattices('#skF_2') | v2_struct_0('#skF_2') | ~l3_lattices('#skF_2')), inference(resolution, [status(thm)], [c_8, c_210])).
% 3.57/1.56  tff(c_216, plain, (v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_60, c_213])).
% 3.57/1.56  tff(c_218, plain, $false, inference(negUnitSimplification, [status(thm)], [c_62, c_216])).
% 3.57/1.56  tff(c_220, plain, (v6_lattices('#skF_2')), inference(splitRight, [status(thm)], [c_209])).
% 3.57/1.56  tff(c_4, plain, (![A_1]: (v8_lattices(A_1) | ~v10_lattices(A_1) | v2_struct_0(A_1) | ~l3_lattices(A_1))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.57/1.56  tff(c_2, plain, (![A_1]: (v9_lattices(A_1) | ~v10_lattices(A_1) | v2_struct_0(A_1) | ~l3_lattices(A_1))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.57/1.56  tff(c_219, plain, (![B_93]: (~v8_lattices('#skF_2') | ~v9_lattices('#skF_2') | r3_lattices('#skF_2', B_93, '#skF_3') | ~r1_lattices('#skF_2', B_93, '#skF_3') | ~m1_subset_1(B_93, u1_struct_0('#skF_2')))), inference(splitRight, [status(thm)], [c_209])).
% 3.57/1.56  tff(c_221, plain, (~v9_lattices('#skF_2')), inference(splitLeft, [status(thm)], [c_219])).
% 3.57/1.56  tff(c_224, plain, (~v10_lattices('#skF_2') | v2_struct_0('#skF_2') | ~l3_lattices('#skF_2')), inference(resolution, [status(thm)], [c_2, c_221])).
% 3.57/1.56  tff(c_227, plain, (v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_60, c_224])).
% 3.57/1.56  tff(c_229, plain, $false, inference(negUnitSimplification, [status(thm)], [c_62, c_227])).
% 3.57/1.56  tff(c_230, plain, (![B_93]: (~v8_lattices('#skF_2') | r3_lattices('#skF_2', B_93, '#skF_3') | ~r1_lattices('#skF_2', B_93, '#skF_3') | ~m1_subset_1(B_93, u1_struct_0('#skF_2')))), inference(splitRight, [status(thm)], [c_219])).
% 3.57/1.56  tff(c_239, plain, (~v8_lattices('#skF_2')), inference(splitLeft, [status(thm)], [c_230])).
% 3.57/1.56  tff(c_242, plain, (~v10_lattices('#skF_2') | v2_struct_0('#skF_2') | ~l3_lattices('#skF_2')), inference(resolution, [status(thm)], [c_4, c_239])).
% 3.57/1.56  tff(c_245, plain, (v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_60, c_242])).
% 3.57/1.56  tff(c_247, plain, $false, inference(negUnitSimplification, [status(thm)], [c_62, c_245])).
% 3.57/1.56  tff(c_249, plain, (v8_lattices('#skF_2')), inference(splitRight, [status(thm)], [c_230])).
% 3.57/1.56  tff(c_231, plain, (v9_lattices('#skF_2')), inference(splitRight, [status(thm)], [c_219])).
% 3.57/1.56  tff(c_63, plain, (![A_54]: (l2_lattices(A_54) | ~l3_lattices(A_54))), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.57/1.56  tff(c_67, plain, (l2_lattices('#skF_2')), inference(resolution, [status(thm)], [c_56, c_63])).
% 3.57/1.56  tff(c_32, plain, (![A_19, B_20]: (m1_subset_1(k16_lattice3(A_19, B_20), u1_struct_0(A_19)) | ~l3_lattices(A_19) | v2_struct_0(A_19))), inference(cnfTransformation, [status(thm)], [f_120])).
% 3.57/1.56  tff(c_544, plain, (![A_143, D_144, C_145]: (r3_lattices(A_143, D_144, k16_lattice3(A_143, C_145)) | ~r3_lattice3(A_143, D_144, C_145) | ~m1_subset_1(D_144, u1_struct_0(A_143)) | ~m1_subset_1(k16_lattice3(A_143, C_145), u1_struct_0(A_143)) | ~l3_lattices(A_143) | ~v4_lattice3(A_143) | ~v10_lattices(A_143) | v2_struct_0(A_143))), inference(cnfTransformation, [status(thm)], [f_144])).
% 3.57/1.56  tff(c_548, plain, (![A_146, D_147, B_148]: (r3_lattices(A_146, D_147, k16_lattice3(A_146, B_148)) | ~r3_lattice3(A_146, D_147, B_148) | ~m1_subset_1(D_147, u1_struct_0(A_146)) | ~v4_lattice3(A_146) | ~v10_lattices(A_146) | ~l3_lattices(A_146) | v2_struct_0(A_146))), inference(resolution, [status(thm)], [c_32, c_544])).
% 3.57/1.56  tff(c_30, plain, (![A_16, B_17, C_18]: (r1_lattices(A_16, B_17, C_18) | ~r3_lattices(A_16, B_17, C_18) | ~m1_subset_1(C_18, u1_struct_0(A_16)) | ~m1_subset_1(B_17, u1_struct_0(A_16)) | ~l3_lattices(A_16) | ~v9_lattices(A_16) | ~v8_lattices(A_16) | ~v6_lattices(A_16) | v2_struct_0(A_16))), inference(cnfTransformation, [status(thm)], [f_113])).
% 3.57/1.56  tff(c_650, plain, (![A_172, D_173, B_174]: (r1_lattices(A_172, D_173, k16_lattice3(A_172, B_174)) | ~m1_subset_1(k16_lattice3(A_172, B_174), u1_struct_0(A_172)) | ~v9_lattices(A_172) | ~v8_lattices(A_172) | ~v6_lattices(A_172) | ~r3_lattice3(A_172, D_173, B_174) | ~m1_subset_1(D_173, u1_struct_0(A_172)) | ~v4_lattice3(A_172) | ~v10_lattices(A_172) | ~l3_lattices(A_172) | v2_struct_0(A_172))), inference(resolution, [status(thm)], [c_548, c_30])).
% 3.57/1.56  tff(c_654, plain, (![A_175, D_176, B_177]: (r1_lattices(A_175, D_176, k16_lattice3(A_175, B_177)) | ~v9_lattices(A_175) | ~v8_lattices(A_175) | ~v6_lattices(A_175) | ~r3_lattice3(A_175, D_176, B_177) | ~m1_subset_1(D_176, u1_struct_0(A_175)) | ~v4_lattice3(A_175) | ~v10_lattices(A_175) | ~l3_lattices(A_175) | v2_struct_0(A_175))), inference(resolution, [status(thm)], [c_32, c_650])).
% 3.57/1.56  tff(c_20, plain, (![A_5, B_9, C_11]: (k1_lattices(A_5, B_9, C_11)=C_11 | ~r1_lattices(A_5, B_9, C_11) | ~m1_subset_1(C_11, u1_struct_0(A_5)) | ~m1_subset_1(B_9, u1_struct_0(A_5)) | ~l2_lattices(A_5) | v2_struct_0(A_5))), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.57/1.56  tff(c_706, plain, (![A_192, D_193, B_194]: (k1_lattices(A_192, D_193, k16_lattice3(A_192, B_194))=k16_lattice3(A_192, B_194) | ~m1_subset_1(k16_lattice3(A_192, B_194), u1_struct_0(A_192)) | ~l2_lattices(A_192) | ~v9_lattices(A_192) | ~v8_lattices(A_192) | ~v6_lattices(A_192) | ~r3_lattice3(A_192, D_193, B_194) | ~m1_subset_1(D_193, u1_struct_0(A_192)) | ~v4_lattice3(A_192) | ~v10_lattices(A_192) | ~l3_lattices(A_192) | v2_struct_0(A_192))), inference(resolution, [status(thm)], [c_654, c_20])).
% 3.57/1.56  tff(c_710, plain, (![A_195, D_196, B_197]: (k1_lattices(A_195, D_196, k16_lattice3(A_195, B_197))=k16_lattice3(A_195, B_197) | ~l2_lattices(A_195) | ~v9_lattices(A_195) | ~v8_lattices(A_195) | ~v6_lattices(A_195) | ~r3_lattice3(A_195, D_196, B_197) | ~m1_subset_1(D_196, u1_struct_0(A_195)) | ~v4_lattice3(A_195) | ~v10_lattices(A_195) | ~l3_lattices(A_195) | v2_struct_0(A_195))), inference(resolution, [status(thm)], [c_32, c_706])).
% 3.57/1.56  tff(c_716, plain, (![B_197]: (k1_lattices('#skF_2', '#skF_3', k16_lattice3('#skF_2', B_197))=k16_lattice3('#skF_2', B_197) | ~l2_lattices('#skF_2') | ~v9_lattices('#skF_2') | ~v8_lattices('#skF_2') | ~v6_lattices('#skF_2') | ~r3_lattice3('#skF_2', '#skF_3', B_197) | ~v4_lattice3('#skF_2') | ~v10_lattices('#skF_2') | ~l3_lattices('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_54, c_710])).
% 3.57/1.56  tff(c_721, plain, (![B_197]: (k1_lattices('#skF_2', '#skF_3', k16_lattice3('#skF_2', B_197))=k16_lattice3('#skF_2', B_197) | ~r3_lattice3('#skF_2', '#skF_3', B_197) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_60, c_58, c_220, c_249, c_231, c_67, c_716])).
% 3.57/1.56  tff(c_723, plain, (![B_198]: (k1_lattices('#skF_2', '#skF_3', k16_lattice3('#skF_2', B_198))=k16_lattice3('#skF_2', B_198) | ~r3_lattice3('#skF_2', '#skF_3', B_198))), inference(negUnitSimplification, [status(thm)], [c_62, c_721])).
% 3.57/1.56  tff(c_12, plain, (![A_1]: (v4_lattices(A_1) | ~v10_lattices(A_1) | v2_struct_0(A_1) | ~l3_lattices(A_1))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.57/1.56  tff(c_119, plain, (![A_82, B_83, C_84]: (k3_lattices(A_82, B_83, C_84)=k1_lattices(A_82, B_83, C_84) | ~m1_subset_1(C_84, u1_struct_0(A_82)) | ~m1_subset_1(B_83, u1_struct_0(A_82)) | ~l2_lattices(A_82) | ~v4_lattices(A_82) | v2_struct_0(A_82))), inference(cnfTransformation, [status(thm)], [f_94])).
% 3.57/1.56  tff(c_123, plain, (![B_83]: (k3_lattices('#skF_2', B_83, '#skF_3')=k1_lattices('#skF_2', B_83, '#skF_3') | ~m1_subset_1(B_83, u1_struct_0('#skF_2')) | ~l2_lattices('#skF_2') | ~v4_lattices('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_54, c_119])).
% 3.57/1.56  tff(c_127, plain, (![B_83]: (k3_lattices('#skF_2', B_83, '#skF_3')=k1_lattices('#skF_2', B_83, '#skF_3') | ~m1_subset_1(B_83, u1_struct_0('#skF_2')) | ~v4_lattices('#skF_2') | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_67, c_123])).
% 3.57/1.56  tff(c_128, plain, (![B_83]: (k3_lattices('#skF_2', B_83, '#skF_3')=k1_lattices('#skF_2', B_83, '#skF_3') | ~m1_subset_1(B_83, u1_struct_0('#skF_2')) | ~v4_lattices('#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_62, c_127])).
% 3.57/1.56  tff(c_129, plain, (~v4_lattices('#skF_2')), inference(splitLeft, [status(thm)], [c_128])).
% 3.57/1.56  tff(c_132, plain, (~v10_lattices('#skF_2') | v2_struct_0('#skF_2') | ~l3_lattices('#skF_2')), inference(resolution, [status(thm)], [c_12, c_129])).
% 3.57/1.56  tff(c_135, plain, (v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_60, c_132])).
% 3.57/1.56  tff(c_137, plain, $false, inference(negUnitSimplification, [status(thm)], [c_62, c_135])).
% 3.57/1.56  tff(c_139, plain, (v4_lattices('#skF_2')), inference(splitRight, [status(thm)], [c_128])).
% 3.57/1.56  tff(c_140, plain, (![B_85]: (k3_lattices('#skF_2', B_85, '#skF_3')=k1_lattices('#skF_2', B_85, '#skF_3') | ~m1_subset_1(B_85, u1_struct_0('#skF_2')))), inference(splitRight, [status(thm)], [c_128])).
% 3.57/1.56  tff(c_144, plain, (![B_20]: (k3_lattices('#skF_2', k16_lattice3('#skF_2', B_20), '#skF_3')=k1_lattices('#skF_2', k16_lattice3('#skF_2', B_20), '#skF_3') | ~l3_lattices('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_32, c_140])).
% 3.57/1.56  tff(c_150, plain, (![B_20]: (k3_lattices('#skF_2', k16_lattice3('#skF_2', B_20), '#skF_3')=k1_lattices('#skF_2', k16_lattice3('#skF_2', B_20), '#skF_3') | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_144])).
% 3.57/1.56  tff(c_151, plain, (![B_20]: (k3_lattices('#skF_2', k16_lattice3('#skF_2', B_20), '#skF_3')=k1_lattices('#skF_2', k16_lattice3('#skF_2', B_20), '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_62, c_150])).
% 3.57/1.56  tff(c_157, plain, (![A_86, C_87, B_88]: (k3_lattices(A_86, C_87, B_88)=k3_lattices(A_86, B_88, C_87) | ~m1_subset_1(C_87, u1_struct_0(A_86)) | ~m1_subset_1(B_88, u1_struct_0(A_86)) | ~l2_lattices(A_86) | ~v4_lattices(A_86) | v2_struct_0(A_86))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.57/1.56  tff(c_161, plain, (![B_88]: (k3_lattices('#skF_2', B_88, '#skF_3')=k3_lattices('#skF_2', '#skF_3', B_88) | ~m1_subset_1(B_88, u1_struct_0('#skF_2')) | ~l2_lattices('#skF_2') | ~v4_lattices('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_54, c_157])).
% 3.57/1.56  tff(c_165, plain, (![B_88]: (k3_lattices('#skF_2', B_88, '#skF_3')=k3_lattices('#skF_2', '#skF_3', B_88) | ~m1_subset_1(B_88, u1_struct_0('#skF_2')) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_139, c_67, c_161])).
% 3.57/1.56  tff(c_167, plain, (![B_89]: (k3_lattices('#skF_2', B_89, '#skF_3')=k3_lattices('#skF_2', '#skF_3', B_89) | ~m1_subset_1(B_89, u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_62, c_165])).
% 3.57/1.56  tff(c_171, plain, (![B_20]: (k3_lattices('#skF_2', k16_lattice3('#skF_2', B_20), '#skF_3')=k3_lattices('#skF_2', '#skF_3', k16_lattice3('#skF_2', B_20)) | ~l3_lattices('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_32, c_167])).
% 3.57/1.56  tff(c_177, plain, (![B_20]: (k3_lattices('#skF_2', k16_lattice3('#skF_2', B_20), '#skF_3')=k3_lattices('#skF_2', '#skF_3', k16_lattice3('#skF_2', B_20)) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_171])).
% 3.57/1.56  tff(c_178, plain, (![B_20]: (k3_lattices('#skF_2', k16_lattice3('#skF_2', B_20), '#skF_3')=k3_lattices('#skF_2', '#skF_3', k16_lattice3('#skF_2', B_20)))), inference(negUnitSimplification, [status(thm)], [c_62, c_177])).
% 3.57/1.56  tff(c_190, plain, (![B_20]: (k3_lattices('#skF_2', '#skF_3', k16_lattice3('#skF_2', B_20))=k1_lattices('#skF_2', k16_lattice3('#skF_2', B_20), '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_151, c_178])).
% 3.57/1.56  tff(c_329, plain, (![A_106, B_107, B_108]: (k3_lattices(A_106, B_107, k16_lattice3(A_106, B_108))=k1_lattices(A_106, B_107, k16_lattice3(A_106, B_108)) | ~m1_subset_1(B_107, u1_struct_0(A_106)) | ~l2_lattices(A_106) | ~v4_lattices(A_106) | ~l3_lattices(A_106) | v2_struct_0(A_106))), inference(resolution, [status(thm)], [c_32, c_119])).
% 3.57/1.56  tff(c_335, plain, (![B_108]: (k3_lattices('#skF_2', '#skF_3', k16_lattice3('#skF_2', B_108))=k1_lattices('#skF_2', '#skF_3', k16_lattice3('#skF_2', B_108)) | ~l2_lattices('#skF_2') | ~v4_lattices('#skF_2') | ~l3_lattices('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_54, c_329])).
% 3.57/1.56  tff(c_340, plain, (![B_108]: (k1_lattices('#skF_2', k16_lattice3('#skF_2', B_108), '#skF_3')=k1_lattices('#skF_2', '#skF_3', k16_lattice3('#skF_2', B_108)) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_139, c_67, c_190, c_335])).
% 3.57/1.56  tff(c_341, plain, (![B_108]: (k1_lattices('#skF_2', k16_lattice3('#skF_2', B_108), '#skF_3')=k1_lattices('#skF_2', '#skF_3', k16_lattice3('#skF_2', B_108)))), inference(negUnitSimplification, [status(thm)], [c_62, c_340])).
% 3.57/1.56  tff(c_44, plain, (![A_43, C_49, B_47]: (r3_lattices(A_43, k16_lattice3(A_43, C_49), B_47) | ~r2_hidden(B_47, C_49) | ~m1_subset_1(B_47, u1_struct_0(A_43)) | ~l3_lattices(A_43) | ~v4_lattice3(A_43) | ~v10_lattices(A_43) | v2_struct_0(A_43))), inference(cnfTransformation, [status(thm)], [f_163])).
% 3.57/1.56  tff(c_232, plain, (![A_95, B_96, C_97]: (r1_lattices(A_95, B_96, C_97) | ~r3_lattices(A_95, B_96, C_97) | ~m1_subset_1(C_97, u1_struct_0(A_95)) | ~m1_subset_1(B_96, u1_struct_0(A_95)) | ~l3_lattices(A_95) | ~v9_lattices(A_95) | ~v8_lattices(A_95) | ~v6_lattices(A_95) | v2_struct_0(A_95))), inference(cnfTransformation, [status(thm)], [f_113])).
% 3.57/1.56  tff(c_626, plain, (![A_160, C_161, B_162]: (r1_lattices(A_160, k16_lattice3(A_160, C_161), B_162) | ~m1_subset_1(k16_lattice3(A_160, C_161), u1_struct_0(A_160)) | ~v9_lattices(A_160) | ~v8_lattices(A_160) | ~v6_lattices(A_160) | ~r2_hidden(B_162, C_161) | ~m1_subset_1(B_162, u1_struct_0(A_160)) | ~l3_lattices(A_160) | ~v4_lattice3(A_160) | ~v10_lattices(A_160) | v2_struct_0(A_160))), inference(resolution, [status(thm)], [c_44, c_232])).
% 3.57/1.56  tff(c_630, plain, (![A_163, B_164, B_165]: (r1_lattices(A_163, k16_lattice3(A_163, B_164), B_165) | ~v9_lattices(A_163) | ~v8_lattices(A_163) | ~v6_lattices(A_163) | ~r2_hidden(B_165, B_164) | ~m1_subset_1(B_165, u1_struct_0(A_163)) | ~v4_lattice3(A_163) | ~v10_lattices(A_163) | ~l3_lattices(A_163) | v2_struct_0(A_163))), inference(resolution, [status(thm)], [c_32, c_626])).
% 3.57/1.56  tff(c_658, plain, (![A_178, B_179, B_180]: (k1_lattices(A_178, k16_lattice3(A_178, B_179), B_180)=B_180 | ~m1_subset_1(k16_lattice3(A_178, B_179), u1_struct_0(A_178)) | ~l2_lattices(A_178) | ~v9_lattices(A_178) | ~v8_lattices(A_178) | ~v6_lattices(A_178) | ~r2_hidden(B_180, B_179) | ~m1_subset_1(B_180, u1_struct_0(A_178)) | ~v4_lattice3(A_178) | ~v10_lattices(A_178) | ~l3_lattices(A_178) | v2_struct_0(A_178))), inference(resolution, [status(thm)], [c_630, c_20])).
% 3.57/1.56  tff(c_662, plain, (![A_181, B_182, B_183]: (k1_lattices(A_181, k16_lattice3(A_181, B_182), B_183)=B_183 | ~l2_lattices(A_181) | ~v9_lattices(A_181) | ~v8_lattices(A_181) | ~v6_lattices(A_181) | ~r2_hidden(B_183, B_182) | ~m1_subset_1(B_183, u1_struct_0(A_181)) | ~v4_lattice3(A_181) | ~v10_lattices(A_181) | ~l3_lattices(A_181) | v2_struct_0(A_181))), inference(resolution, [status(thm)], [c_32, c_658])).
% 3.57/1.56  tff(c_668, plain, (![B_182]: (k1_lattices('#skF_2', k16_lattice3('#skF_2', B_182), '#skF_3')='#skF_3' | ~l2_lattices('#skF_2') | ~v9_lattices('#skF_2') | ~v8_lattices('#skF_2') | ~v6_lattices('#skF_2') | ~r2_hidden('#skF_3', B_182) | ~v4_lattice3('#skF_2') | ~v10_lattices('#skF_2') | ~l3_lattices('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_54, c_662])).
% 3.57/1.56  tff(c_673, plain, (![B_182]: (k1_lattices('#skF_2', '#skF_3', k16_lattice3('#skF_2', B_182))='#skF_3' | ~r2_hidden('#skF_3', B_182) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_60, c_58, c_220, c_249, c_231, c_67, c_341, c_668])).
% 3.57/1.56  tff(c_674, plain, (![B_182]: (k1_lattices('#skF_2', '#skF_3', k16_lattice3('#skF_2', B_182))='#skF_3' | ~r2_hidden('#skF_3', B_182))), inference(negUnitSimplification, [status(thm)], [c_62, c_673])).
% 3.57/1.56  tff(c_738, plain, (![B_199]: (k16_lattice3('#skF_2', B_199)='#skF_3' | ~r2_hidden('#skF_3', B_199) | ~r3_lattice3('#skF_2', '#skF_3', B_199))), inference(superposition, [status(thm), theory('equality')], [c_723, c_674])).
% 3.57/1.56  tff(c_741, plain, (k16_lattice3('#skF_2', '#skF_4')='#skF_3' | ~r2_hidden('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_50, c_738])).
% 3.57/1.56  tff(c_744, plain, (k16_lattice3('#skF_2', '#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_52, c_741])).
% 3.57/1.56  tff(c_746, plain, $false, inference(negUnitSimplification, [status(thm)], [c_48, c_744])).
% 3.57/1.56  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.57/1.56  
% 3.57/1.56  Inference rules
% 3.57/1.56  ----------------------
% 3.57/1.56  #Ref     : 0
% 3.57/1.56  #Sup     : 137
% 3.57/1.56  #Fact    : 0
% 3.57/1.56  #Define  : 0
% 3.57/1.56  #Split   : 6
% 3.57/1.56  #Chain   : 0
% 3.57/1.56  #Close   : 0
% 3.57/1.56  
% 3.57/1.56  Ordering : KBO
% 3.57/1.56  
% 3.57/1.56  Simplification rules
% 3.57/1.56  ----------------------
% 3.57/1.56  #Subsume      : 15
% 3.57/1.56  #Demod        : 95
% 3.57/1.56  #Tautology    : 54
% 3.57/1.56  #SimpNegUnit  : 32
% 3.57/1.56  #BackRed      : 3
% 3.57/1.56  
% 3.57/1.56  #Partial instantiations: 0
% 3.57/1.56  #Strategies tried      : 1
% 3.57/1.56  
% 3.57/1.56  Timing (in seconds)
% 3.57/1.56  ----------------------
% 3.57/1.57  Preprocessing        : 0.35
% 3.57/1.57  Parsing              : 0.18
% 3.57/1.57  CNF conversion       : 0.02
% 3.57/1.57  Main loop            : 0.43
% 3.57/1.57  Inferencing          : 0.17
% 3.57/1.57  Reduction            : 0.11
% 3.57/1.57  Demodulation         : 0.08
% 3.57/1.57  BG Simplification    : 0.03
% 3.57/1.57  Subsumption          : 0.08
% 3.57/1.57  Abstraction          : 0.03
% 3.57/1.57  MUC search           : 0.00
% 3.57/1.57  Cooper               : 0.00
% 3.57/1.57  Total                : 0.81
% 3.57/1.57  Index Insertion      : 0.00
% 3.57/1.57  Index Deletion       : 0.00
% 3.57/1.57  Index Matching       : 0.00
% 3.57/1.57  BG Taut test         : 0.00
%------------------------------------------------------------------------------
