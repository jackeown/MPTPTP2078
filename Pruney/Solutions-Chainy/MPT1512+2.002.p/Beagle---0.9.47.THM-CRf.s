%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:24:50 EST 2020

% Result     : Theorem 4.15s
% Output     : CNFRefutation 4.63s
% Verified   : 
% Statistics : Number of formulae       :  196 (1734 expanded)
%              Number of leaves         :   41 ( 598 expanded)
%              Depth                    :   30
%              Number of atoms          :  619 (7516 expanded)
%              Number of equality atoms :    1 (   6 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r4_lattice3 > r3_lattices > r3_lattice3 > r1_lattices > r2_hidden > r1_tarski > m1_subset_1 > v9_lattices > v8_lattices > v7_lattices > v6_lattices > v5_lattices > v4_lattices > v4_lattice3 > v2_struct_0 > v10_lattices > l3_lattices > k16_lattice3 > k15_lattice3 > #nlpp > u1_struct_0 > #skF_4 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(l3_lattices,type,(
    l3_lattices: $i > $o )).

tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

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

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_lattices,type,(
    r1_lattices: ( $i * $i * $i ) > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(r3_lattice3,type,(
    r3_lattice3: ( $i * $i * $i ) > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(v7_lattices,type,(
    v7_lattices: $i > $o )).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_204,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v10_lattices(A)
          & v4_lattice3(A)
          & l3_lattices(A) )
       => ! [B,C] :
            ( r1_tarski(B,C)
           => ( r3_lattices(A,k15_lattice3(A,B),k15_lattice3(A,C))
              & r3_lattices(A,k16_lattice3(A,C),k16_lattice3(A,B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_lattice3)).

tff(f_151,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & l3_lattices(A) )
     => m1_subset_1(k16_lattice3(A,B),u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k16_lattice3)).

tff(f_187,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v10_lattices(A)
        & v4_lattice3(A)
        & l3_lattices(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( r3_lattice3(A,B,C)
             => r3_lattices(A,B,k16_lattice3(A,C)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_lattice3)).

tff(f_144,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & l3_lattices(A) )
     => m1_subset_1(k15_lattice3(A,B),u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k15_lattice3)).

tff(f_170,axiom,(
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

tff(f_137,axiom,(
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

tff(f_73,axiom,(
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

tff(f_109,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l3_lattices(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( r4_lattice3(A,B,C)
            <=> ! [D] :
                  ( m1_subset_1(D,u1_struct_0(A))
                 => ( r2_hidden(D,C)
                   => r1_lattices(A,D,B) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d17_lattice3)).

tff(f_91,axiom,(
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

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_717,plain,(
    ! [A_302,B_303] :
      ( ~ r2_hidden('#skF_1'(A_302,B_303),B_303)
      | r1_tarski(A_302,B_303) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_722,plain,(
    ! [A_1] : r1_tarski(A_1,A_1) ),
    inference(resolution,[status(thm)],[c_6,c_717])).

tff(c_72,plain,(
    ~ v2_struct_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_204])).

tff(c_66,plain,(
    l3_lattices('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_204])).

tff(c_54,plain,(
    ! [A_68,B_69] :
      ( m1_subset_1(k16_lattice3(A_68,B_69),u1_struct_0(A_68))
      | ~ l3_lattices(A_68)
      | v2_struct_0(A_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_70,plain,(
    v10_lattices('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_204])).

tff(c_68,plain,(
    v4_lattice3('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_204])).

tff(c_839,plain,(
    ! [A_366,B_367,C_368] :
      ( r3_lattices(A_366,B_367,k16_lattice3(A_366,C_368))
      | ~ r3_lattice3(A_366,B_367,C_368)
      | ~ m1_subset_1(B_367,u1_struct_0(A_366))
      | ~ l3_lattices(A_366)
      | ~ v4_lattice3(A_366)
      | ~ v10_lattices(A_366)
      | v2_struct_0(A_366) ) ),
    inference(cnfTransformation,[status(thm)],[f_187])).

tff(c_81,plain,(
    ! [A_94,B_95] :
      ( ~ r2_hidden('#skF_1'(A_94,B_95),B_95)
      | r1_tarski(A_94,B_95) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_86,plain,(
    ! [A_1] : r1_tarski(A_1,A_1) ),
    inference(resolution,[status(thm)],[c_6,c_81])).

tff(c_52,plain,(
    ! [A_66,B_67] :
      ( m1_subset_1(k15_lattice3(A_66,B_67),u1_struct_0(A_66))
      | ~ l3_lattices(A_66)
      | v2_struct_0(A_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_179,plain,(
    ! [A_148,B_149,C_150] :
      ( r3_lattices(A_148,B_149,k15_lattice3(A_148,C_150))
      | ~ r2_hidden(B_149,C_150)
      | ~ m1_subset_1(B_149,u1_struct_0(A_148))
      | ~ l3_lattices(A_148)
      | ~ v4_lattice3(A_148)
      | ~ v10_lattices(A_148)
      | v2_struct_0(A_148) ) ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_62,plain,
    ( ~ r3_lattices('#skF_5',k16_lattice3('#skF_5','#skF_7'),k16_lattice3('#skF_5','#skF_6'))
    | ~ r3_lattices('#skF_5',k15_lattice3('#skF_5','#skF_6'),k15_lattice3('#skF_5','#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_204])).

tff(c_77,plain,(
    ~ r3_lattices('#skF_5',k15_lattice3('#skF_5','#skF_6'),k15_lattice3('#skF_5','#skF_7')) ),
    inference(splitLeft,[status(thm)],[c_62])).

tff(c_182,plain,
    ( ~ r2_hidden(k15_lattice3('#skF_5','#skF_6'),'#skF_7')
    | ~ m1_subset_1(k15_lattice3('#skF_5','#skF_6'),u1_struct_0('#skF_5'))
    | ~ l3_lattices('#skF_5')
    | ~ v4_lattice3('#skF_5')
    | ~ v10_lattices('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_179,c_77])).

tff(c_185,plain,
    ( ~ r2_hidden(k15_lattice3('#skF_5','#skF_6'),'#skF_7')
    | ~ m1_subset_1(k15_lattice3('#skF_5','#skF_6'),u1_struct_0('#skF_5'))
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_66,c_182])).

tff(c_186,plain,
    ( ~ r2_hidden(k15_lattice3('#skF_5','#skF_6'),'#skF_7')
    | ~ m1_subset_1(k15_lattice3('#skF_5','#skF_6'),u1_struct_0('#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_185])).

tff(c_187,plain,(
    ~ m1_subset_1(k15_lattice3('#skF_5','#skF_6'),u1_struct_0('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_186])).

tff(c_190,plain,
    ( ~ l3_lattices('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_52,c_187])).

tff(c_193,plain,(
    v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_190])).

tff(c_195,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_193])).

tff(c_197,plain,(
    m1_subset_1(k15_lattice3('#skF_5','#skF_6'),u1_struct_0('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_186])).

tff(c_456,plain,(
    ! [A_256,B_257,D_258] :
      ( r1_lattices(A_256,k15_lattice3(A_256,B_257),D_258)
      | ~ r4_lattice3(A_256,D_258,B_257)
      | ~ m1_subset_1(D_258,u1_struct_0(A_256))
      | ~ m1_subset_1(k15_lattice3(A_256,B_257),u1_struct_0(A_256))
      | ~ v4_lattice3(A_256)
      | ~ v10_lattices(A_256)
      | ~ l3_lattices(A_256)
      | v2_struct_0(A_256) ) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_458,plain,(
    ! [D_258] :
      ( r1_lattices('#skF_5',k15_lattice3('#skF_5','#skF_6'),D_258)
      | ~ r4_lattice3('#skF_5',D_258,'#skF_6')
      | ~ m1_subset_1(D_258,u1_struct_0('#skF_5'))
      | ~ v4_lattice3('#skF_5')
      | ~ v10_lattices('#skF_5')
      | ~ l3_lattices('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_197,c_456])).

tff(c_463,plain,(
    ! [D_258] :
      ( r1_lattices('#skF_5',k15_lattice3('#skF_5','#skF_6'),D_258)
      | ~ r4_lattice3('#skF_5',D_258,'#skF_6')
      | ~ m1_subset_1(D_258,u1_struct_0('#skF_5'))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_70,c_68,c_458])).

tff(c_466,plain,(
    ! [D_259] :
      ( r1_lattices('#skF_5',k15_lattice3('#skF_5','#skF_6'),D_259)
      | ~ r4_lattice3('#skF_5',D_259,'#skF_6')
      | ~ m1_subset_1(D_259,u1_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_463])).

tff(c_14,plain,(
    ! [A_6] :
      ( v6_lattices(A_6)
      | ~ v10_lattices(A_6)
      | v2_struct_0(A_6)
      | ~ l3_lattices(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_348,plain,(
    ! [A_208,B_209,C_210] :
      ( r3_lattices(A_208,B_209,C_210)
      | ~ r1_lattices(A_208,B_209,C_210)
      | ~ m1_subset_1(C_210,u1_struct_0(A_208))
      | ~ m1_subset_1(B_209,u1_struct_0(A_208))
      | ~ l3_lattices(A_208)
      | ~ v9_lattices(A_208)
      | ~ v8_lattices(A_208)
      | ~ v6_lattices(A_208)
      | v2_struct_0(A_208) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_350,plain,(
    ! [B_209] :
      ( r3_lattices('#skF_5',B_209,k15_lattice3('#skF_5','#skF_6'))
      | ~ r1_lattices('#skF_5',B_209,k15_lattice3('#skF_5','#skF_6'))
      | ~ m1_subset_1(B_209,u1_struct_0('#skF_5'))
      | ~ l3_lattices('#skF_5')
      | ~ v9_lattices('#skF_5')
      | ~ v8_lattices('#skF_5')
      | ~ v6_lattices('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_197,c_348])).

tff(c_361,plain,(
    ! [B_209] :
      ( r3_lattices('#skF_5',B_209,k15_lattice3('#skF_5','#skF_6'))
      | ~ r1_lattices('#skF_5',B_209,k15_lattice3('#skF_5','#skF_6'))
      | ~ m1_subset_1(B_209,u1_struct_0('#skF_5'))
      | ~ v9_lattices('#skF_5')
      | ~ v8_lattices('#skF_5')
      | ~ v6_lattices('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_350])).

tff(c_362,plain,(
    ! [B_209] :
      ( r3_lattices('#skF_5',B_209,k15_lattice3('#skF_5','#skF_6'))
      | ~ r1_lattices('#skF_5',B_209,k15_lattice3('#skF_5','#skF_6'))
      | ~ m1_subset_1(B_209,u1_struct_0('#skF_5'))
      | ~ v9_lattices('#skF_5')
      | ~ v8_lattices('#skF_5')
      | ~ v6_lattices('#skF_5') ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_361])).

tff(c_367,plain,(
    ~ v6_lattices('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_362])).

tff(c_370,plain,
    ( ~ v10_lattices('#skF_5')
    | v2_struct_0('#skF_5')
    | ~ l3_lattices('#skF_5') ),
    inference(resolution,[status(thm)],[c_14,c_367])).

tff(c_373,plain,(
    v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_70,c_370])).

tff(c_375,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_373])).

tff(c_377,plain,(
    v6_lattices('#skF_5') ),
    inference(splitRight,[status(thm)],[c_362])).

tff(c_10,plain,(
    ! [A_6] :
      ( v8_lattices(A_6)
      | ~ v10_lattices(A_6)
      | v2_struct_0(A_6)
      | ~ l3_lattices(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_8,plain,(
    ! [A_6] :
      ( v9_lattices(A_6)
      | ~ v10_lattices(A_6)
      | v2_struct_0(A_6)
      | ~ l3_lattices(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_376,plain,(
    ! [B_209] :
      ( ~ v8_lattices('#skF_5')
      | ~ v9_lattices('#skF_5')
      | r3_lattices('#skF_5',B_209,k15_lattice3('#skF_5','#skF_6'))
      | ~ r1_lattices('#skF_5',B_209,k15_lattice3('#skF_5','#skF_6'))
      | ~ m1_subset_1(B_209,u1_struct_0('#skF_5')) ) ),
    inference(splitRight,[status(thm)],[c_362])).

tff(c_378,plain,(
    ~ v9_lattices('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_376])).

tff(c_381,plain,
    ( ~ v10_lattices('#skF_5')
    | v2_struct_0('#skF_5')
    | ~ l3_lattices('#skF_5') ),
    inference(resolution,[status(thm)],[c_8,c_378])).

tff(c_384,plain,(
    v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_70,c_381])).

tff(c_386,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_384])).

tff(c_387,plain,(
    ! [B_209] :
      ( ~ v8_lattices('#skF_5')
      | r3_lattices('#skF_5',B_209,k15_lattice3('#skF_5','#skF_6'))
      | ~ r1_lattices('#skF_5',B_209,k15_lattice3('#skF_5','#skF_6'))
      | ~ m1_subset_1(B_209,u1_struct_0('#skF_5')) ) ),
    inference(splitRight,[status(thm)],[c_376])).

tff(c_389,plain,(
    ~ v8_lattices('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_387])).

tff(c_396,plain,
    ( ~ v10_lattices('#skF_5')
    | v2_struct_0('#skF_5')
    | ~ l3_lattices('#skF_5') ),
    inference(resolution,[status(thm)],[c_10,c_389])).

tff(c_399,plain,(
    v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_70,c_396])).

tff(c_401,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_399])).

tff(c_403,plain,(
    v8_lattices('#skF_5') ),
    inference(splitRight,[status(thm)],[c_387])).

tff(c_388,plain,(
    v9_lattices('#skF_5') ),
    inference(splitRight,[status(thm)],[c_376])).

tff(c_412,plain,(
    ! [A_219,B_220,B_221] :
      ( r3_lattices(A_219,B_220,k15_lattice3(A_219,B_221))
      | ~ r1_lattices(A_219,B_220,k15_lattice3(A_219,B_221))
      | ~ m1_subset_1(B_220,u1_struct_0(A_219))
      | ~ v9_lattices(A_219)
      | ~ v8_lattices(A_219)
      | ~ v6_lattices(A_219)
      | ~ l3_lattices(A_219)
      | v2_struct_0(A_219) ) ),
    inference(resolution,[status(thm)],[c_52,c_348])).

tff(c_417,plain,
    ( ~ r1_lattices('#skF_5',k15_lattice3('#skF_5','#skF_6'),k15_lattice3('#skF_5','#skF_7'))
    | ~ m1_subset_1(k15_lattice3('#skF_5','#skF_6'),u1_struct_0('#skF_5'))
    | ~ v9_lattices('#skF_5')
    | ~ v8_lattices('#skF_5')
    | ~ v6_lattices('#skF_5')
    | ~ l3_lattices('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_412,c_77])).

tff(c_421,plain,
    ( ~ r1_lattices('#skF_5',k15_lattice3('#skF_5','#skF_6'),k15_lattice3('#skF_5','#skF_7'))
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_377,c_403,c_388,c_197,c_417])).

tff(c_422,plain,(
    ~ r1_lattices('#skF_5',k15_lattice3('#skF_5','#skF_6'),k15_lattice3('#skF_5','#skF_7')) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_421])).

tff(c_482,plain,
    ( ~ r4_lattice3('#skF_5',k15_lattice3('#skF_5','#skF_7'),'#skF_6')
    | ~ m1_subset_1(k15_lattice3('#skF_5','#skF_7'),u1_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_466,c_422])).

tff(c_487,plain,(
    ~ m1_subset_1(k15_lattice3('#skF_5','#skF_7'),u1_struct_0('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_482])).

tff(c_490,plain,
    ( ~ l3_lattices('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_52,c_487])).

tff(c_493,plain,(
    v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_490])).

tff(c_495,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_493])).

tff(c_497,plain,(
    m1_subset_1(k15_lattice3('#skF_5','#skF_7'),u1_struct_0('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_482])).

tff(c_64,plain,(
    r1_tarski('#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_204])).

tff(c_94,plain,(
    ! [A_104,B_105,C_106] :
      ( r2_hidden('#skF_3'(A_104,B_105,C_106),C_106)
      | r4_lattice3(A_104,B_105,C_106)
      | ~ m1_subset_1(B_105,u1_struct_0(A_104))
      | ~ l3_lattices(A_104)
      | v2_struct_0(A_104) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_203,plain,(
    ! [A_158,B_159,C_160,B_161] :
      ( r2_hidden('#skF_3'(A_158,B_159,C_160),B_161)
      | ~ r1_tarski(C_160,B_161)
      | r4_lattice3(A_158,B_159,C_160)
      | ~ m1_subset_1(B_159,u1_struct_0(A_158))
      | ~ l3_lattices(A_158)
      | v2_struct_0(A_158) ) ),
    inference(resolution,[status(thm)],[c_94,c_2])).

tff(c_278,plain,(
    ! [B_183,C_185,A_182,B_184,B_181] :
      ( r2_hidden('#skF_3'(A_182,B_183,C_185),B_184)
      | ~ r1_tarski(B_181,B_184)
      | ~ r1_tarski(C_185,B_181)
      | r4_lattice3(A_182,B_183,C_185)
      | ~ m1_subset_1(B_183,u1_struct_0(A_182))
      | ~ l3_lattices(A_182)
      | v2_struct_0(A_182) ) ),
    inference(resolution,[status(thm)],[c_203,c_2])).

tff(c_288,plain,(
    ! [A_186,B_187,C_188] :
      ( r2_hidden('#skF_3'(A_186,B_187,C_188),'#skF_7')
      | ~ r1_tarski(C_188,'#skF_6')
      | r4_lattice3(A_186,B_187,C_188)
      | ~ m1_subset_1(B_187,u1_struct_0(A_186))
      | ~ l3_lattices(A_186)
      | v2_struct_0(A_186) ) ),
    inference(resolution,[status(thm)],[c_64,c_278])).

tff(c_297,plain,(
    ! [A_186,B_187,C_188,B_2] :
      ( r2_hidden('#skF_3'(A_186,B_187,C_188),B_2)
      | ~ r1_tarski('#skF_7',B_2)
      | ~ r1_tarski(C_188,'#skF_6')
      | r4_lattice3(A_186,B_187,C_188)
      | ~ m1_subset_1(B_187,u1_struct_0(A_186))
      | ~ l3_lattices(A_186)
      | v2_struct_0(A_186) ) ),
    inference(resolution,[status(thm)],[c_288,c_2])).

tff(c_40,plain,(
    ! [A_32,B_44,C_50] :
      ( m1_subset_1('#skF_3'(A_32,B_44,C_50),u1_struct_0(A_32))
      | r4_lattice3(A_32,B_44,C_50)
      | ~ m1_subset_1(B_44,u1_struct_0(A_32))
      | ~ l3_lattices(A_32)
      | v2_struct_0(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_58,plain,(
    ! [A_70,B_74,C_76] :
      ( r3_lattices(A_70,B_74,k15_lattice3(A_70,C_76))
      | ~ r2_hidden(B_74,C_76)
      | ~ m1_subset_1(B_74,u1_struct_0(A_70))
      | ~ l3_lattices(A_70)
      | ~ v4_lattice3(A_70)
      | ~ v10_lattices(A_70)
      | v2_struct_0(A_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_328,plain,(
    ! [A_201,B_202,C_203] :
      ( r1_lattices(A_201,B_202,C_203)
      | ~ r3_lattices(A_201,B_202,C_203)
      | ~ m1_subset_1(C_203,u1_struct_0(A_201))
      | ~ m1_subset_1(B_202,u1_struct_0(A_201))
      | ~ l3_lattices(A_201)
      | ~ v9_lattices(A_201)
      | ~ v8_lattices(A_201)
      | ~ v6_lattices(A_201)
      | v2_struct_0(A_201) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_583,plain,(
    ! [A_284,B_285,C_286] :
      ( r1_lattices(A_284,B_285,k15_lattice3(A_284,C_286))
      | ~ m1_subset_1(k15_lattice3(A_284,C_286),u1_struct_0(A_284))
      | ~ v9_lattices(A_284)
      | ~ v8_lattices(A_284)
      | ~ v6_lattices(A_284)
      | ~ r2_hidden(B_285,C_286)
      | ~ m1_subset_1(B_285,u1_struct_0(A_284))
      | ~ l3_lattices(A_284)
      | ~ v4_lattice3(A_284)
      | ~ v10_lattices(A_284)
      | v2_struct_0(A_284) ) ),
    inference(resolution,[status(thm)],[c_58,c_328])).

tff(c_585,plain,(
    ! [B_285] :
      ( r1_lattices('#skF_5',B_285,k15_lattice3('#skF_5','#skF_7'))
      | ~ v9_lattices('#skF_5')
      | ~ v8_lattices('#skF_5')
      | ~ v6_lattices('#skF_5')
      | ~ r2_hidden(B_285,'#skF_7')
      | ~ m1_subset_1(B_285,u1_struct_0('#skF_5'))
      | ~ l3_lattices('#skF_5')
      | ~ v4_lattice3('#skF_5')
      | ~ v10_lattices('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_497,c_583])).

tff(c_592,plain,(
    ! [B_285] :
      ( r1_lattices('#skF_5',B_285,k15_lattice3('#skF_5','#skF_7'))
      | ~ r2_hidden(B_285,'#skF_7')
      | ~ m1_subset_1(B_285,u1_struct_0('#skF_5'))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_66,c_377,c_403,c_388,c_585])).

tff(c_608,plain,(
    ! [B_288] :
      ( r1_lattices('#skF_5',B_288,k15_lattice3('#skF_5','#skF_7'))
      | ~ r2_hidden(B_288,'#skF_7')
      | ~ m1_subset_1(B_288,u1_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_592])).

tff(c_36,plain,(
    ! [A_32,B_44,C_50] :
      ( ~ r1_lattices(A_32,'#skF_3'(A_32,B_44,C_50),B_44)
      | r4_lattice3(A_32,B_44,C_50)
      | ~ m1_subset_1(B_44,u1_struct_0(A_32))
      | ~ l3_lattices(A_32)
      | v2_struct_0(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_615,plain,(
    ! [C_50] :
      ( r4_lattice3('#skF_5',k15_lattice3('#skF_5','#skF_7'),C_50)
      | ~ m1_subset_1(k15_lattice3('#skF_5','#skF_7'),u1_struct_0('#skF_5'))
      | ~ l3_lattices('#skF_5')
      | v2_struct_0('#skF_5')
      | ~ r2_hidden('#skF_3'('#skF_5',k15_lattice3('#skF_5','#skF_7'),C_50),'#skF_7')
      | ~ m1_subset_1('#skF_3'('#skF_5',k15_lattice3('#skF_5','#skF_7'),C_50),u1_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_608,c_36])).

tff(c_621,plain,(
    ! [C_50] :
      ( r4_lattice3('#skF_5',k15_lattice3('#skF_5','#skF_7'),C_50)
      | v2_struct_0('#skF_5')
      | ~ r2_hidden('#skF_3'('#skF_5',k15_lattice3('#skF_5','#skF_7'),C_50),'#skF_7')
      | ~ m1_subset_1('#skF_3'('#skF_5',k15_lattice3('#skF_5','#skF_7'),C_50),u1_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_497,c_615])).

tff(c_662,plain,(
    ! [C_295] :
      ( r4_lattice3('#skF_5',k15_lattice3('#skF_5','#skF_7'),C_295)
      | ~ r2_hidden('#skF_3'('#skF_5',k15_lattice3('#skF_5','#skF_7'),C_295),'#skF_7')
      | ~ m1_subset_1('#skF_3'('#skF_5',k15_lattice3('#skF_5','#skF_7'),C_295),u1_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_621])).

tff(c_666,plain,(
    ! [C_50] :
      ( ~ r2_hidden('#skF_3'('#skF_5',k15_lattice3('#skF_5','#skF_7'),C_50),'#skF_7')
      | r4_lattice3('#skF_5',k15_lattice3('#skF_5','#skF_7'),C_50)
      | ~ m1_subset_1(k15_lattice3('#skF_5','#skF_7'),u1_struct_0('#skF_5'))
      | ~ l3_lattices('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_40,c_662])).

tff(c_669,plain,(
    ! [C_50] :
      ( ~ r2_hidden('#skF_3'('#skF_5',k15_lattice3('#skF_5','#skF_7'),C_50),'#skF_7')
      | r4_lattice3('#skF_5',k15_lattice3('#skF_5','#skF_7'),C_50)
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_497,c_666])).

tff(c_671,plain,(
    ! [C_296] :
      ( ~ r2_hidden('#skF_3'('#skF_5',k15_lattice3('#skF_5','#skF_7'),C_296),'#skF_7')
      | r4_lattice3('#skF_5',k15_lattice3('#skF_5','#skF_7'),C_296) ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_669])).

tff(c_675,plain,(
    ! [C_188] :
      ( ~ r1_tarski('#skF_7','#skF_7')
      | ~ r1_tarski(C_188,'#skF_6')
      | r4_lattice3('#skF_5',k15_lattice3('#skF_5','#skF_7'),C_188)
      | ~ m1_subset_1(k15_lattice3('#skF_5','#skF_7'),u1_struct_0('#skF_5'))
      | ~ l3_lattices('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_297,c_671])).

tff(c_690,plain,(
    ! [C_188] :
      ( ~ r1_tarski(C_188,'#skF_6')
      | r4_lattice3('#skF_5',k15_lattice3('#skF_5','#skF_7'),C_188)
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_497,c_86,c_675])).

tff(c_704,plain,(
    ! [C_297] :
      ( ~ r1_tarski(C_297,'#skF_6')
      | r4_lattice3('#skF_5',k15_lattice3('#skF_5','#skF_7'),C_297) ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_690])).

tff(c_496,plain,(
    ~ r4_lattice3('#skF_5',k15_lattice3('#skF_5','#skF_7'),'#skF_6') ),
    inference(splitRight,[status(thm)],[c_482])).

tff(c_707,plain,(
    ~ r1_tarski('#skF_6','#skF_6') ),
    inference(resolution,[status(thm)],[c_704,c_496])).

tff(c_711,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_707])).

tff(c_712,plain,(
    ~ r3_lattices('#skF_5',k16_lattice3('#skF_5','#skF_7'),k16_lattice3('#skF_5','#skF_6')) ),
    inference(splitRight,[status(thm)],[c_62])).

tff(c_842,plain,
    ( ~ r3_lattice3('#skF_5',k16_lattice3('#skF_5','#skF_7'),'#skF_6')
    | ~ m1_subset_1(k16_lattice3('#skF_5','#skF_7'),u1_struct_0('#skF_5'))
    | ~ l3_lattices('#skF_5')
    | ~ v4_lattice3('#skF_5')
    | ~ v10_lattices('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_839,c_712])).

tff(c_845,plain,
    ( ~ r3_lattice3('#skF_5',k16_lattice3('#skF_5','#skF_7'),'#skF_6')
    | ~ m1_subset_1(k16_lattice3('#skF_5','#skF_7'),u1_struct_0('#skF_5'))
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_66,c_842])).

tff(c_846,plain,
    ( ~ r3_lattice3('#skF_5',k16_lattice3('#skF_5','#skF_7'),'#skF_6')
    | ~ m1_subset_1(k16_lattice3('#skF_5','#skF_7'),u1_struct_0('#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_845])).

tff(c_847,plain,(
    ~ m1_subset_1(k16_lattice3('#skF_5','#skF_7'),u1_struct_0('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_846])).

tff(c_850,plain,
    ( ~ l3_lattices('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_54,c_847])).

tff(c_853,plain,(
    v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_850])).

tff(c_855,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_853])).

tff(c_857,plain,(
    m1_subset_1(k16_lattice3('#skF_5','#skF_7'),u1_struct_0('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_846])).

tff(c_768,plain,(
    ! [A_325,B_326,C_327] :
      ( r2_hidden('#skF_2'(A_325,B_326,C_327),C_327)
      | r3_lattice3(A_325,B_326,C_327)
      | ~ m1_subset_1(B_326,u1_struct_0(A_325))
      | ~ l3_lattices(A_325)
      | v2_struct_0(A_325) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_858,plain,(
    ! [A_369,B_370,C_371,B_372] :
      ( r2_hidden('#skF_2'(A_369,B_370,C_371),B_372)
      | ~ r1_tarski(C_371,B_372)
      | r3_lattice3(A_369,B_370,C_371)
      | ~ m1_subset_1(B_370,u1_struct_0(A_369))
      | ~ l3_lattices(A_369)
      | v2_struct_0(A_369) ) ),
    inference(resolution,[status(thm)],[c_768,c_2])).

tff(c_1092,plain,(
    ! [B_408,C_410,B_407,A_406,B_409] :
      ( r2_hidden('#skF_2'(A_406,B_407,C_410),B_409)
      | ~ r1_tarski(B_408,B_409)
      | ~ r1_tarski(C_410,B_408)
      | r3_lattice3(A_406,B_407,C_410)
      | ~ m1_subset_1(B_407,u1_struct_0(A_406))
      | ~ l3_lattices(A_406)
      | v2_struct_0(A_406) ) ),
    inference(resolution,[status(thm)],[c_858,c_2])).

tff(c_1102,plain,(
    ! [A_411,B_412,C_413] :
      ( r2_hidden('#skF_2'(A_411,B_412,C_413),'#skF_7')
      | ~ r1_tarski(C_413,'#skF_6')
      | r3_lattice3(A_411,B_412,C_413)
      | ~ m1_subset_1(B_412,u1_struct_0(A_411))
      | ~ l3_lattices(A_411)
      | v2_struct_0(A_411) ) ),
    inference(resolution,[status(thm)],[c_64,c_1092])).

tff(c_1111,plain,(
    ! [A_411,B_412,C_413,B_2] :
      ( r2_hidden('#skF_2'(A_411,B_412,C_413),B_2)
      | ~ r1_tarski('#skF_7',B_2)
      | ~ r1_tarski(C_413,'#skF_6')
      | r3_lattice3(A_411,B_412,C_413)
      | ~ m1_subset_1(B_412,u1_struct_0(A_411))
      | ~ l3_lattices(A_411)
      | v2_struct_0(A_411) ) ),
    inference(resolution,[status(thm)],[c_1102,c_2])).

tff(c_32,plain,(
    ! [A_10,B_22,C_28] :
      ( m1_subset_1('#skF_2'(A_10,B_22,C_28),u1_struct_0(A_10))
      | r3_lattice3(A_10,B_22,C_28)
      | ~ m1_subset_1(B_22,u1_struct_0(A_10))
      | ~ l3_lattices(A_10)
      | v2_struct_0(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_932,plain,(
    ! [A_389,B_390,C_391] :
      ( r3_lattices(A_389,B_390,C_391)
      | ~ r1_lattices(A_389,B_390,C_391)
      | ~ m1_subset_1(C_391,u1_struct_0(A_389))
      | ~ m1_subset_1(B_390,u1_struct_0(A_389))
      | ~ l3_lattices(A_389)
      | ~ v9_lattices(A_389)
      | ~ v8_lattices(A_389)
      | ~ v6_lattices(A_389)
      | v2_struct_0(A_389) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_934,plain,(
    ! [B_390] :
      ( r3_lattices('#skF_5',B_390,k16_lattice3('#skF_5','#skF_7'))
      | ~ r1_lattices('#skF_5',B_390,k16_lattice3('#skF_5','#skF_7'))
      | ~ m1_subset_1(B_390,u1_struct_0('#skF_5'))
      | ~ l3_lattices('#skF_5')
      | ~ v9_lattices('#skF_5')
      | ~ v8_lattices('#skF_5')
      | ~ v6_lattices('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_857,c_932])).

tff(c_947,plain,(
    ! [B_390] :
      ( r3_lattices('#skF_5',B_390,k16_lattice3('#skF_5','#skF_7'))
      | ~ r1_lattices('#skF_5',B_390,k16_lattice3('#skF_5','#skF_7'))
      | ~ m1_subset_1(B_390,u1_struct_0('#skF_5'))
      | ~ v9_lattices('#skF_5')
      | ~ v8_lattices('#skF_5')
      | ~ v6_lattices('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_934])).

tff(c_948,plain,(
    ! [B_390] :
      ( r3_lattices('#skF_5',B_390,k16_lattice3('#skF_5','#skF_7'))
      | ~ r1_lattices('#skF_5',B_390,k16_lattice3('#skF_5','#skF_7'))
      | ~ m1_subset_1(B_390,u1_struct_0('#skF_5'))
      | ~ v9_lattices('#skF_5')
      | ~ v8_lattices('#skF_5')
      | ~ v6_lattices('#skF_5') ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_947])).

tff(c_957,plain,(
    ~ v6_lattices('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_948])).

tff(c_960,plain,
    ( ~ v10_lattices('#skF_5')
    | v2_struct_0('#skF_5')
    | ~ l3_lattices('#skF_5') ),
    inference(resolution,[status(thm)],[c_14,c_957])).

tff(c_963,plain,(
    v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_70,c_960])).

tff(c_965,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_963])).

tff(c_967,plain,(
    v6_lattices('#skF_5') ),
    inference(splitRight,[status(thm)],[c_948])).

tff(c_816,plain,(
    ! [A_359,C_360,B_361] :
      ( r3_lattices(A_359,k16_lattice3(A_359,C_360),B_361)
      | ~ r2_hidden(B_361,C_360)
      | ~ m1_subset_1(B_361,u1_struct_0(A_359))
      | ~ l3_lattices(A_359)
      | ~ v4_lattice3(A_359)
      | ~ v10_lattices(A_359)
      | v2_struct_0(A_359) ) ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_819,plain,
    ( ~ r2_hidden(k16_lattice3('#skF_5','#skF_6'),'#skF_7')
    | ~ m1_subset_1(k16_lattice3('#skF_5','#skF_6'),u1_struct_0('#skF_5'))
    | ~ l3_lattices('#skF_5')
    | ~ v4_lattice3('#skF_5')
    | ~ v10_lattices('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_816,c_712])).

tff(c_822,plain,
    ( ~ r2_hidden(k16_lattice3('#skF_5','#skF_6'),'#skF_7')
    | ~ m1_subset_1(k16_lattice3('#skF_5','#skF_6'),u1_struct_0('#skF_5'))
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_66,c_819])).

tff(c_823,plain,
    ( ~ r2_hidden(k16_lattice3('#skF_5','#skF_6'),'#skF_7')
    | ~ m1_subset_1(k16_lattice3('#skF_5','#skF_6'),u1_struct_0('#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_822])).

tff(c_824,plain,(
    ~ m1_subset_1(k16_lattice3('#skF_5','#skF_6'),u1_struct_0('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_823])).

tff(c_827,plain,
    ( ~ l3_lattices('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_54,c_824])).

tff(c_830,plain,(
    v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_827])).

tff(c_832,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_830])).

tff(c_834,plain,(
    m1_subset_1(k16_lattice3('#skF_5','#skF_6'),u1_struct_0('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_823])).

tff(c_936,plain,(
    ! [B_390] :
      ( r3_lattices('#skF_5',B_390,k16_lattice3('#skF_5','#skF_6'))
      | ~ r1_lattices('#skF_5',B_390,k16_lattice3('#skF_5','#skF_6'))
      | ~ m1_subset_1(B_390,u1_struct_0('#skF_5'))
      | ~ l3_lattices('#skF_5')
      | ~ v9_lattices('#skF_5')
      | ~ v8_lattices('#skF_5')
      | ~ v6_lattices('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_834,c_932])).

tff(c_951,plain,(
    ! [B_390] :
      ( r3_lattices('#skF_5',B_390,k16_lattice3('#skF_5','#skF_6'))
      | ~ r1_lattices('#skF_5',B_390,k16_lattice3('#skF_5','#skF_6'))
      | ~ m1_subset_1(B_390,u1_struct_0('#skF_5'))
      | ~ v9_lattices('#skF_5')
      | ~ v8_lattices('#skF_5')
      | ~ v6_lattices('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_936])).

tff(c_952,plain,(
    ! [B_390] :
      ( r3_lattices('#skF_5',B_390,k16_lattice3('#skF_5','#skF_6'))
      | ~ r1_lattices('#skF_5',B_390,k16_lattice3('#skF_5','#skF_6'))
      | ~ m1_subset_1(B_390,u1_struct_0('#skF_5'))
      | ~ v9_lattices('#skF_5')
      | ~ v8_lattices('#skF_5')
      | ~ v6_lattices('#skF_5') ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_951])).

tff(c_969,plain,(
    ! [B_390] :
      ( r3_lattices('#skF_5',B_390,k16_lattice3('#skF_5','#skF_6'))
      | ~ r1_lattices('#skF_5',B_390,k16_lattice3('#skF_5','#skF_6'))
      | ~ m1_subset_1(B_390,u1_struct_0('#skF_5'))
      | ~ v9_lattices('#skF_5')
      | ~ v8_lattices('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_967,c_952])).

tff(c_970,plain,(
    ~ v8_lattices('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_969])).

tff(c_973,plain,
    ( ~ v10_lattices('#skF_5')
    | v2_struct_0('#skF_5')
    | ~ l3_lattices('#skF_5') ),
    inference(resolution,[status(thm)],[c_10,c_970])).

tff(c_976,plain,(
    v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_70,c_973])).

tff(c_978,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_976])).

tff(c_980,plain,(
    v8_lattices('#skF_5') ),
    inference(splitRight,[status(thm)],[c_969])).

tff(c_979,plain,(
    ! [B_390] :
      ( ~ v9_lattices('#skF_5')
      | r3_lattices('#skF_5',B_390,k16_lattice3('#skF_5','#skF_6'))
      | ~ r1_lattices('#skF_5',B_390,k16_lattice3('#skF_5','#skF_6'))
      | ~ m1_subset_1(B_390,u1_struct_0('#skF_5')) ) ),
    inference(splitRight,[status(thm)],[c_969])).

tff(c_981,plain,(
    ~ v9_lattices('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_979])).

tff(c_984,plain,
    ( ~ v10_lattices('#skF_5')
    | v2_struct_0('#skF_5')
    | ~ l3_lattices('#skF_5') ),
    inference(resolution,[status(thm)],[c_8,c_981])).

tff(c_987,plain,(
    v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_70,c_984])).

tff(c_989,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_987])).

tff(c_991,plain,(
    v9_lattices('#skF_5') ),
    inference(splitRight,[status(thm)],[c_979])).

tff(c_56,plain,(
    ! [A_70,C_76,B_74] :
      ( r3_lattices(A_70,k16_lattice3(A_70,C_76),B_74)
      | ~ r2_hidden(B_74,C_76)
      | ~ m1_subset_1(B_74,u1_struct_0(A_70))
      | ~ l3_lattices(A_70)
      | ~ v4_lattice3(A_70)
      | ~ v10_lattices(A_70)
      | v2_struct_0(A_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_992,plain,(
    ! [A_392,B_393,C_394] :
      ( r1_lattices(A_392,B_393,C_394)
      | ~ r3_lattices(A_392,B_393,C_394)
      | ~ m1_subset_1(C_394,u1_struct_0(A_392))
      | ~ m1_subset_1(B_393,u1_struct_0(A_392))
      | ~ l3_lattices(A_392)
      | ~ v9_lattices(A_392)
      | ~ v8_lattices(A_392)
      | ~ v6_lattices(A_392)
      | v2_struct_0(A_392) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_1274,plain,(
    ! [A_483,C_484,B_485] :
      ( r1_lattices(A_483,k16_lattice3(A_483,C_484),B_485)
      | ~ m1_subset_1(k16_lattice3(A_483,C_484),u1_struct_0(A_483))
      | ~ v9_lattices(A_483)
      | ~ v8_lattices(A_483)
      | ~ v6_lattices(A_483)
      | ~ r2_hidden(B_485,C_484)
      | ~ m1_subset_1(B_485,u1_struct_0(A_483))
      | ~ l3_lattices(A_483)
      | ~ v4_lattice3(A_483)
      | ~ v10_lattices(A_483)
      | v2_struct_0(A_483) ) ),
    inference(resolution,[status(thm)],[c_56,c_992])).

tff(c_1276,plain,(
    ! [B_485] :
      ( r1_lattices('#skF_5',k16_lattice3('#skF_5','#skF_7'),B_485)
      | ~ v9_lattices('#skF_5')
      | ~ v8_lattices('#skF_5')
      | ~ v6_lattices('#skF_5')
      | ~ r2_hidden(B_485,'#skF_7')
      | ~ m1_subset_1(B_485,u1_struct_0('#skF_5'))
      | ~ l3_lattices('#skF_5')
      | ~ v4_lattice3('#skF_5')
      | ~ v10_lattices('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_857,c_1274])).

tff(c_1283,plain,(
    ! [B_485] :
      ( r1_lattices('#skF_5',k16_lattice3('#skF_5','#skF_7'),B_485)
      | ~ r2_hidden(B_485,'#skF_7')
      | ~ m1_subset_1(B_485,u1_struct_0('#skF_5'))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_66,c_967,c_980,c_991,c_1276])).

tff(c_1290,plain,(
    ! [B_486] :
      ( r1_lattices('#skF_5',k16_lattice3('#skF_5','#skF_7'),B_486)
      | ~ r2_hidden(B_486,'#skF_7')
      | ~ m1_subset_1(B_486,u1_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_1283])).

tff(c_28,plain,(
    ! [A_10,B_22,C_28] :
      ( ~ r1_lattices(A_10,B_22,'#skF_2'(A_10,B_22,C_28))
      | r3_lattice3(A_10,B_22,C_28)
      | ~ m1_subset_1(B_22,u1_struct_0(A_10))
      | ~ l3_lattices(A_10)
      | v2_struct_0(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_1301,plain,(
    ! [C_28] :
      ( r3_lattice3('#skF_5',k16_lattice3('#skF_5','#skF_7'),C_28)
      | ~ m1_subset_1(k16_lattice3('#skF_5','#skF_7'),u1_struct_0('#skF_5'))
      | ~ l3_lattices('#skF_5')
      | v2_struct_0('#skF_5')
      | ~ r2_hidden('#skF_2'('#skF_5',k16_lattice3('#skF_5','#skF_7'),C_28),'#skF_7')
      | ~ m1_subset_1('#skF_2'('#skF_5',k16_lattice3('#skF_5','#skF_7'),C_28),u1_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_1290,c_28])).

tff(c_1311,plain,(
    ! [C_28] :
      ( r3_lattice3('#skF_5',k16_lattice3('#skF_5','#skF_7'),C_28)
      | v2_struct_0('#skF_5')
      | ~ r2_hidden('#skF_2'('#skF_5',k16_lattice3('#skF_5','#skF_7'),C_28),'#skF_7')
      | ~ m1_subset_1('#skF_2'('#skF_5',k16_lattice3('#skF_5','#skF_7'),C_28),u1_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_857,c_1301])).

tff(c_1340,plain,(
    ! [C_489] :
      ( r3_lattice3('#skF_5',k16_lattice3('#skF_5','#skF_7'),C_489)
      | ~ r2_hidden('#skF_2'('#skF_5',k16_lattice3('#skF_5','#skF_7'),C_489),'#skF_7')
      | ~ m1_subset_1('#skF_2'('#skF_5',k16_lattice3('#skF_5','#skF_7'),C_489),u1_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_1311])).

tff(c_1344,plain,(
    ! [C_28] :
      ( ~ r2_hidden('#skF_2'('#skF_5',k16_lattice3('#skF_5','#skF_7'),C_28),'#skF_7')
      | r3_lattice3('#skF_5',k16_lattice3('#skF_5','#skF_7'),C_28)
      | ~ m1_subset_1(k16_lattice3('#skF_5','#skF_7'),u1_struct_0('#skF_5'))
      | ~ l3_lattices('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_32,c_1340])).

tff(c_1347,plain,(
    ! [C_28] :
      ( ~ r2_hidden('#skF_2'('#skF_5',k16_lattice3('#skF_5','#skF_7'),C_28),'#skF_7')
      | r3_lattice3('#skF_5',k16_lattice3('#skF_5','#skF_7'),C_28)
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_857,c_1344])).

tff(c_1349,plain,(
    ! [C_490] :
      ( ~ r2_hidden('#skF_2'('#skF_5',k16_lattice3('#skF_5','#skF_7'),C_490),'#skF_7')
      | r3_lattice3('#skF_5',k16_lattice3('#skF_5','#skF_7'),C_490) ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_1347])).

tff(c_1353,plain,(
    ! [C_413] :
      ( ~ r1_tarski('#skF_7','#skF_7')
      | ~ r1_tarski(C_413,'#skF_6')
      | r3_lattice3('#skF_5',k16_lattice3('#skF_5','#skF_7'),C_413)
      | ~ m1_subset_1(k16_lattice3('#skF_5','#skF_7'),u1_struct_0('#skF_5'))
      | ~ l3_lattices('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_1111,c_1349])).

tff(c_1368,plain,(
    ! [C_413] :
      ( ~ r1_tarski(C_413,'#skF_6')
      | r3_lattice3('#skF_5',k16_lattice3('#skF_5','#skF_7'),C_413)
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_857,c_722,c_1353])).

tff(c_1382,plain,(
    ! [C_491] :
      ( ~ r1_tarski(C_491,'#skF_6')
      | r3_lattice3('#skF_5',k16_lattice3('#skF_5','#skF_7'),C_491) ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_1368])).

tff(c_856,plain,(
    ~ r3_lattice3('#skF_5',k16_lattice3('#skF_5','#skF_7'),'#skF_6') ),
    inference(splitRight,[status(thm)],[c_846])).

tff(c_1385,plain,(
    ~ r1_tarski('#skF_6','#skF_6') ),
    inference(resolution,[status(thm)],[c_1382,c_856])).

tff(c_1389,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_722,c_1385])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 16:48:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.15/1.74  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.15/1.76  
% 4.15/1.76  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.15/1.76  %$ r4_lattice3 > r3_lattices > r3_lattice3 > r1_lattices > r2_hidden > r1_tarski > m1_subset_1 > v9_lattices > v8_lattices > v7_lattices > v6_lattices > v5_lattices > v4_lattices > v4_lattice3 > v2_struct_0 > v10_lattices > l3_lattices > k16_lattice3 > k15_lattice3 > #nlpp > u1_struct_0 > #skF_4 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1
% 4.15/1.76  
% 4.15/1.76  %Foreground sorts:
% 4.15/1.76  
% 4.15/1.76  
% 4.15/1.76  %Background operators:
% 4.15/1.76  
% 4.15/1.76  
% 4.15/1.76  %Foreground operators:
% 4.15/1.76  tff(l3_lattices, type, l3_lattices: $i > $o).
% 4.15/1.76  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 4.15/1.76  tff(r3_lattices, type, r3_lattices: ($i * $i * $i) > $o).
% 4.15/1.76  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.15/1.76  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.15/1.76  tff(k16_lattice3, type, k16_lattice3: ($i * $i) > $i).
% 4.15/1.76  tff(k15_lattice3, type, k15_lattice3: ($i * $i) > $i).
% 4.15/1.76  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 4.15/1.76  tff('#skF_7', type, '#skF_7': $i).
% 4.15/1.76  tff(r1_lattices, type, r1_lattices: ($i * $i * $i) > $o).
% 4.15/1.76  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.15/1.76  tff('#skF_5', type, '#skF_5': $i).
% 4.15/1.76  tff(v4_lattices, type, v4_lattices: $i > $o).
% 4.15/1.76  tff('#skF_6', type, '#skF_6': $i).
% 4.15/1.76  tff(v6_lattices, type, v6_lattices: $i > $o).
% 4.15/1.76  tff(v9_lattices, type, v9_lattices: $i > $o).
% 4.15/1.76  tff(r4_lattice3, type, r4_lattice3: ($i * $i * $i) > $o).
% 4.15/1.76  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 4.15/1.76  tff(v4_lattice3, type, v4_lattice3: $i > $o).
% 4.15/1.76  tff(v5_lattices, type, v5_lattices: $i > $o).
% 4.15/1.76  tff(v10_lattices, type, v10_lattices: $i > $o).
% 4.15/1.76  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.15/1.76  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 4.15/1.76  tff(v8_lattices, type, v8_lattices: $i > $o).
% 4.15/1.76  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.15/1.76  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 4.15/1.76  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 4.15/1.76  tff(r3_lattice3, type, r3_lattice3: ($i * $i * $i) > $o).
% 4.15/1.76  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.15/1.76  tff(v7_lattices, type, v7_lattices: $i > $o).
% 4.15/1.76  
% 4.63/1.79  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 4.63/1.79  tff(f_204, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v10_lattices(A)) & v4_lattice3(A)) & l3_lattices(A)) => (![B, C]: (r1_tarski(B, C) => (r3_lattices(A, k15_lattice3(A, B), k15_lattice3(A, C)) & r3_lattices(A, k16_lattice3(A, C), k16_lattice3(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_lattice3)).
% 4.63/1.79  tff(f_151, axiom, (![A, B]: ((~v2_struct_0(A) & l3_lattices(A)) => m1_subset_1(k16_lattice3(A, B), u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k16_lattice3)).
% 4.63/1.79  tff(f_187, axiom, (![A]: ((((~v2_struct_0(A) & v10_lattices(A)) & v4_lattice3(A)) & l3_lattices(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (r3_lattice3(A, B, C) => r3_lattices(A, B, k16_lattice3(A, C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t40_lattice3)).
% 4.63/1.79  tff(f_144, axiom, (![A, B]: ((~v2_struct_0(A) & l3_lattices(A)) => m1_subset_1(k15_lattice3(A, B), u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k15_lattice3)).
% 4.63/1.79  tff(f_170, axiom, (![A]: ((((~v2_struct_0(A) & v10_lattices(A)) & v4_lattice3(A)) & l3_lattices(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (r2_hidden(B, C) => (r3_lattices(A, B, k15_lattice3(A, C)) & r3_lattices(A, k16_lattice3(A, C), B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_lattice3)).
% 4.63/1.79  tff(f_137, axiom, (![A]: ((~v2_struct_0(A) & l3_lattices(A)) => ((((~v2_struct_0(A) & v10_lattices(A)) & v4_lattice3(A)) & l3_lattices(A)) => (![B, C]: (m1_subset_1(C, u1_struct_0(A)) => ((C = k15_lattice3(A, B)) <=> (r4_lattice3(A, C, B) & (![D]: (m1_subset_1(D, u1_struct_0(A)) => (r4_lattice3(A, D, B) => r1_lattices(A, C, D))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d21_lattice3)).
% 4.63/1.79  tff(f_54, axiom, (![A]: (l3_lattices(A) => ((~v2_struct_0(A) & v10_lattices(A)) => ((((((~v2_struct_0(A) & v4_lattices(A)) & v5_lattices(A)) & v6_lattices(A)) & v7_lattices(A)) & v8_lattices(A)) & v9_lattices(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_lattices)).
% 4.63/1.79  tff(f_73, axiom, (![A, B, C]: (((((((~v2_struct_0(A) & v6_lattices(A)) & v8_lattices(A)) & v9_lattices(A)) & l3_lattices(A)) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => (r3_lattices(A, B, C) <=> r1_lattices(A, B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r3_lattices)).
% 4.63/1.79  tff(f_109, axiom, (![A]: ((~v2_struct_0(A) & l3_lattices(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (r4_lattice3(A, B, C) <=> (![D]: (m1_subset_1(D, u1_struct_0(A)) => (r2_hidden(D, C) => r1_lattices(A, D, B)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d17_lattice3)).
% 4.63/1.79  tff(f_91, axiom, (![A]: ((~v2_struct_0(A) & l3_lattices(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (r3_lattice3(A, B, C) <=> (![D]: (m1_subset_1(D, u1_struct_0(A)) => (r2_hidden(D, C) => r1_lattices(A, B, D)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d16_lattice3)).
% 4.63/1.79  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.63/1.79  tff(c_717, plain, (![A_302, B_303]: (~r2_hidden('#skF_1'(A_302, B_303), B_303) | r1_tarski(A_302, B_303))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.63/1.79  tff(c_722, plain, (![A_1]: (r1_tarski(A_1, A_1))), inference(resolution, [status(thm)], [c_6, c_717])).
% 4.63/1.79  tff(c_72, plain, (~v2_struct_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_204])).
% 4.63/1.79  tff(c_66, plain, (l3_lattices('#skF_5')), inference(cnfTransformation, [status(thm)], [f_204])).
% 4.63/1.79  tff(c_54, plain, (![A_68, B_69]: (m1_subset_1(k16_lattice3(A_68, B_69), u1_struct_0(A_68)) | ~l3_lattices(A_68) | v2_struct_0(A_68))), inference(cnfTransformation, [status(thm)], [f_151])).
% 4.63/1.79  tff(c_70, plain, (v10_lattices('#skF_5')), inference(cnfTransformation, [status(thm)], [f_204])).
% 4.63/1.79  tff(c_68, plain, (v4_lattice3('#skF_5')), inference(cnfTransformation, [status(thm)], [f_204])).
% 4.63/1.79  tff(c_839, plain, (![A_366, B_367, C_368]: (r3_lattices(A_366, B_367, k16_lattice3(A_366, C_368)) | ~r3_lattice3(A_366, B_367, C_368) | ~m1_subset_1(B_367, u1_struct_0(A_366)) | ~l3_lattices(A_366) | ~v4_lattice3(A_366) | ~v10_lattices(A_366) | v2_struct_0(A_366))), inference(cnfTransformation, [status(thm)], [f_187])).
% 4.63/1.79  tff(c_81, plain, (![A_94, B_95]: (~r2_hidden('#skF_1'(A_94, B_95), B_95) | r1_tarski(A_94, B_95))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.63/1.79  tff(c_86, plain, (![A_1]: (r1_tarski(A_1, A_1))), inference(resolution, [status(thm)], [c_6, c_81])).
% 4.63/1.79  tff(c_52, plain, (![A_66, B_67]: (m1_subset_1(k15_lattice3(A_66, B_67), u1_struct_0(A_66)) | ~l3_lattices(A_66) | v2_struct_0(A_66))), inference(cnfTransformation, [status(thm)], [f_144])).
% 4.63/1.79  tff(c_179, plain, (![A_148, B_149, C_150]: (r3_lattices(A_148, B_149, k15_lattice3(A_148, C_150)) | ~r2_hidden(B_149, C_150) | ~m1_subset_1(B_149, u1_struct_0(A_148)) | ~l3_lattices(A_148) | ~v4_lattice3(A_148) | ~v10_lattices(A_148) | v2_struct_0(A_148))), inference(cnfTransformation, [status(thm)], [f_170])).
% 4.63/1.79  tff(c_62, plain, (~r3_lattices('#skF_5', k16_lattice3('#skF_5', '#skF_7'), k16_lattice3('#skF_5', '#skF_6')) | ~r3_lattices('#skF_5', k15_lattice3('#skF_5', '#skF_6'), k15_lattice3('#skF_5', '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_204])).
% 4.63/1.79  tff(c_77, plain, (~r3_lattices('#skF_5', k15_lattice3('#skF_5', '#skF_6'), k15_lattice3('#skF_5', '#skF_7'))), inference(splitLeft, [status(thm)], [c_62])).
% 4.63/1.79  tff(c_182, plain, (~r2_hidden(k15_lattice3('#skF_5', '#skF_6'), '#skF_7') | ~m1_subset_1(k15_lattice3('#skF_5', '#skF_6'), u1_struct_0('#skF_5')) | ~l3_lattices('#skF_5') | ~v4_lattice3('#skF_5') | ~v10_lattices('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_179, c_77])).
% 4.63/1.79  tff(c_185, plain, (~r2_hidden(k15_lattice3('#skF_5', '#skF_6'), '#skF_7') | ~m1_subset_1(k15_lattice3('#skF_5', '#skF_6'), u1_struct_0('#skF_5')) | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_66, c_182])).
% 4.63/1.79  tff(c_186, plain, (~r2_hidden(k15_lattice3('#skF_5', '#skF_6'), '#skF_7') | ~m1_subset_1(k15_lattice3('#skF_5', '#skF_6'), u1_struct_0('#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_72, c_185])).
% 4.63/1.79  tff(c_187, plain, (~m1_subset_1(k15_lattice3('#skF_5', '#skF_6'), u1_struct_0('#skF_5'))), inference(splitLeft, [status(thm)], [c_186])).
% 4.63/1.79  tff(c_190, plain, (~l3_lattices('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_52, c_187])).
% 4.63/1.79  tff(c_193, plain, (v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_190])).
% 4.63/1.79  tff(c_195, plain, $false, inference(negUnitSimplification, [status(thm)], [c_72, c_193])).
% 4.63/1.79  tff(c_197, plain, (m1_subset_1(k15_lattice3('#skF_5', '#skF_6'), u1_struct_0('#skF_5'))), inference(splitRight, [status(thm)], [c_186])).
% 4.63/1.79  tff(c_456, plain, (![A_256, B_257, D_258]: (r1_lattices(A_256, k15_lattice3(A_256, B_257), D_258) | ~r4_lattice3(A_256, D_258, B_257) | ~m1_subset_1(D_258, u1_struct_0(A_256)) | ~m1_subset_1(k15_lattice3(A_256, B_257), u1_struct_0(A_256)) | ~v4_lattice3(A_256) | ~v10_lattices(A_256) | ~l3_lattices(A_256) | v2_struct_0(A_256))), inference(cnfTransformation, [status(thm)], [f_137])).
% 4.63/1.79  tff(c_458, plain, (![D_258]: (r1_lattices('#skF_5', k15_lattice3('#skF_5', '#skF_6'), D_258) | ~r4_lattice3('#skF_5', D_258, '#skF_6') | ~m1_subset_1(D_258, u1_struct_0('#skF_5')) | ~v4_lattice3('#skF_5') | ~v10_lattices('#skF_5') | ~l3_lattices('#skF_5') | v2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_197, c_456])).
% 4.63/1.79  tff(c_463, plain, (![D_258]: (r1_lattices('#skF_5', k15_lattice3('#skF_5', '#skF_6'), D_258) | ~r4_lattice3('#skF_5', D_258, '#skF_6') | ~m1_subset_1(D_258, u1_struct_0('#skF_5')) | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_70, c_68, c_458])).
% 4.63/1.79  tff(c_466, plain, (![D_259]: (r1_lattices('#skF_5', k15_lattice3('#skF_5', '#skF_6'), D_259) | ~r4_lattice3('#skF_5', D_259, '#skF_6') | ~m1_subset_1(D_259, u1_struct_0('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_72, c_463])).
% 4.63/1.79  tff(c_14, plain, (![A_6]: (v6_lattices(A_6) | ~v10_lattices(A_6) | v2_struct_0(A_6) | ~l3_lattices(A_6))), inference(cnfTransformation, [status(thm)], [f_54])).
% 4.63/1.79  tff(c_348, plain, (![A_208, B_209, C_210]: (r3_lattices(A_208, B_209, C_210) | ~r1_lattices(A_208, B_209, C_210) | ~m1_subset_1(C_210, u1_struct_0(A_208)) | ~m1_subset_1(B_209, u1_struct_0(A_208)) | ~l3_lattices(A_208) | ~v9_lattices(A_208) | ~v8_lattices(A_208) | ~v6_lattices(A_208) | v2_struct_0(A_208))), inference(cnfTransformation, [status(thm)], [f_73])).
% 4.63/1.79  tff(c_350, plain, (![B_209]: (r3_lattices('#skF_5', B_209, k15_lattice3('#skF_5', '#skF_6')) | ~r1_lattices('#skF_5', B_209, k15_lattice3('#skF_5', '#skF_6')) | ~m1_subset_1(B_209, u1_struct_0('#skF_5')) | ~l3_lattices('#skF_5') | ~v9_lattices('#skF_5') | ~v8_lattices('#skF_5') | ~v6_lattices('#skF_5') | v2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_197, c_348])).
% 4.63/1.79  tff(c_361, plain, (![B_209]: (r3_lattices('#skF_5', B_209, k15_lattice3('#skF_5', '#skF_6')) | ~r1_lattices('#skF_5', B_209, k15_lattice3('#skF_5', '#skF_6')) | ~m1_subset_1(B_209, u1_struct_0('#skF_5')) | ~v9_lattices('#skF_5') | ~v8_lattices('#skF_5') | ~v6_lattices('#skF_5') | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_350])).
% 4.63/1.79  tff(c_362, plain, (![B_209]: (r3_lattices('#skF_5', B_209, k15_lattice3('#skF_5', '#skF_6')) | ~r1_lattices('#skF_5', B_209, k15_lattice3('#skF_5', '#skF_6')) | ~m1_subset_1(B_209, u1_struct_0('#skF_5')) | ~v9_lattices('#skF_5') | ~v8_lattices('#skF_5') | ~v6_lattices('#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_72, c_361])).
% 4.63/1.79  tff(c_367, plain, (~v6_lattices('#skF_5')), inference(splitLeft, [status(thm)], [c_362])).
% 4.63/1.79  tff(c_370, plain, (~v10_lattices('#skF_5') | v2_struct_0('#skF_5') | ~l3_lattices('#skF_5')), inference(resolution, [status(thm)], [c_14, c_367])).
% 4.63/1.79  tff(c_373, plain, (v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_70, c_370])).
% 4.63/1.79  tff(c_375, plain, $false, inference(negUnitSimplification, [status(thm)], [c_72, c_373])).
% 4.63/1.79  tff(c_377, plain, (v6_lattices('#skF_5')), inference(splitRight, [status(thm)], [c_362])).
% 4.63/1.79  tff(c_10, plain, (![A_6]: (v8_lattices(A_6) | ~v10_lattices(A_6) | v2_struct_0(A_6) | ~l3_lattices(A_6))), inference(cnfTransformation, [status(thm)], [f_54])).
% 4.63/1.79  tff(c_8, plain, (![A_6]: (v9_lattices(A_6) | ~v10_lattices(A_6) | v2_struct_0(A_6) | ~l3_lattices(A_6))), inference(cnfTransformation, [status(thm)], [f_54])).
% 4.63/1.79  tff(c_376, plain, (![B_209]: (~v8_lattices('#skF_5') | ~v9_lattices('#skF_5') | r3_lattices('#skF_5', B_209, k15_lattice3('#skF_5', '#skF_6')) | ~r1_lattices('#skF_5', B_209, k15_lattice3('#skF_5', '#skF_6')) | ~m1_subset_1(B_209, u1_struct_0('#skF_5')))), inference(splitRight, [status(thm)], [c_362])).
% 4.63/1.79  tff(c_378, plain, (~v9_lattices('#skF_5')), inference(splitLeft, [status(thm)], [c_376])).
% 4.63/1.79  tff(c_381, plain, (~v10_lattices('#skF_5') | v2_struct_0('#skF_5') | ~l3_lattices('#skF_5')), inference(resolution, [status(thm)], [c_8, c_378])).
% 4.63/1.79  tff(c_384, plain, (v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_70, c_381])).
% 4.63/1.79  tff(c_386, plain, $false, inference(negUnitSimplification, [status(thm)], [c_72, c_384])).
% 4.63/1.79  tff(c_387, plain, (![B_209]: (~v8_lattices('#skF_5') | r3_lattices('#skF_5', B_209, k15_lattice3('#skF_5', '#skF_6')) | ~r1_lattices('#skF_5', B_209, k15_lattice3('#skF_5', '#skF_6')) | ~m1_subset_1(B_209, u1_struct_0('#skF_5')))), inference(splitRight, [status(thm)], [c_376])).
% 4.63/1.79  tff(c_389, plain, (~v8_lattices('#skF_5')), inference(splitLeft, [status(thm)], [c_387])).
% 4.63/1.79  tff(c_396, plain, (~v10_lattices('#skF_5') | v2_struct_0('#skF_5') | ~l3_lattices('#skF_5')), inference(resolution, [status(thm)], [c_10, c_389])).
% 4.63/1.79  tff(c_399, plain, (v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_70, c_396])).
% 4.63/1.79  tff(c_401, plain, $false, inference(negUnitSimplification, [status(thm)], [c_72, c_399])).
% 4.63/1.79  tff(c_403, plain, (v8_lattices('#skF_5')), inference(splitRight, [status(thm)], [c_387])).
% 4.63/1.79  tff(c_388, plain, (v9_lattices('#skF_5')), inference(splitRight, [status(thm)], [c_376])).
% 4.63/1.79  tff(c_412, plain, (![A_219, B_220, B_221]: (r3_lattices(A_219, B_220, k15_lattice3(A_219, B_221)) | ~r1_lattices(A_219, B_220, k15_lattice3(A_219, B_221)) | ~m1_subset_1(B_220, u1_struct_0(A_219)) | ~v9_lattices(A_219) | ~v8_lattices(A_219) | ~v6_lattices(A_219) | ~l3_lattices(A_219) | v2_struct_0(A_219))), inference(resolution, [status(thm)], [c_52, c_348])).
% 4.63/1.79  tff(c_417, plain, (~r1_lattices('#skF_5', k15_lattice3('#skF_5', '#skF_6'), k15_lattice3('#skF_5', '#skF_7')) | ~m1_subset_1(k15_lattice3('#skF_5', '#skF_6'), u1_struct_0('#skF_5')) | ~v9_lattices('#skF_5') | ~v8_lattices('#skF_5') | ~v6_lattices('#skF_5') | ~l3_lattices('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_412, c_77])).
% 4.63/1.79  tff(c_421, plain, (~r1_lattices('#skF_5', k15_lattice3('#skF_5', '#skF_6'), k15_lattice3('#skF_5', '#skF_7')) | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_377, c_403, c_388, c_197, c_417])).
% 4.63/1.79  tff(c_422, plain, (~r1_lattices('#skF_5', k15_lattice3('#skF_5', '#skF_6'), k15_lattice3('#skF_5', '#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_72, c_421])).
% 4.63/1.79  tff(c_482, plain, (~r4_lattice3('#skF_5', k15_lattice3('#skF_5', '#skF_7'), '#skF_6') | ~m1_subset_1(k15_lattice3('#skF_5', '#skF_7'), u1_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_466, c_422])).
% 4.63/1.79  tff(c_487, plain, (~m1_subset_1(k15_lattice3('#skF_5', '#skF_7'), u1_struct_0('#skF_5'))), inference(splitLeft, [status(thm)], [c_482])).
% 4.63/1.79  tff(c_490, plain, (~l3_lattices('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_52, c_487])).
% 4.63/1.79  tff(c_493, plain, (v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_490])).
% 4.63/1.79  tff(c_495, plain, $false, inference(negUnitSimplification, [status(thm)], [c_72, c_493])).
% 4.63/1.79  tff(c_497, plain, (m1_subset_1(k15_lattice3('#skF_5', '#skF_7'), u1_struct_0('#skF_5'))), inference(splitRight, [status(thm)], [c_482])).
% 4.63/1.79  tff(c_64, plain, (r1_tarski('#skF_6', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_204])).
% 4.63/1.79  tff(c_94, plain, (![A_104, B_105, C_106]: (r2_hidden('#skF_3'(A_104, B_105, C_106), C_106) | r4_lattice3(A_104, B_105, C_106) | ~m1_subset_1(B_105, u1_struct_0(A_104)) | ~l3_lattices(A_104) | v2_struct_0(A_104))), inference(cnfTransformation, [status(thm)], [f_109])).
% 4.63/1.79  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.63/1.79  tff(c_203, plain, (![A_158, B_159, C_160, B_161]: (r2_hidden('#skF_3'(A_158, B_159, C_160), B_161) | ~r1_tarski(C_160, B_161) | r4_lattice3(A_158, B_159, C_160) | ~m1_subset_1(B_159, u1_struct_0(A_158)) | ~l3_lattices(A_158) | v2_struct_0(A_158))), inference(resolution, [status(thm)], [c_94, c_2])).
% 4.63/1.79  tff(c_278, plain, (![B_183, C_185, A_182, B_184, B_181]: (r2_hidden('#skF_3'(A_182, B_183, C_185), B_184) | ~r1_tarski(B_181, B_184) | ~r1_tarski(C_185, B_181) | r4_lattice3(A_182, B_183, C_185) | ~m1_subset_1(B_183, u1_struct_0(A_182)) | ~l3_lattices(A_182) | v2_struct_0(A_182))), inference(resolution, [status(thm)], [c_203, c_2])).
% 4.63/1.79  tff(c_288, plain, (![A_186, B_187, C_188]: (r2_hidden('#skF_3'(A_186, B_187, C_188), '#skF_7') | ~r1_tarski(C_188, '#skF_6') | r4_lattice3(A_186, B_187, C_188) | ~m1_subset_1(B_187, u1_struct_0(A_186)) | ~l3_lattices(A_186) | v2_struct_0(A_186))), inference(resolution, [status(thm)], [c_64, c_278])).
% 4.63/1.79  tff(c_297, plain, (![A_186, B_187, C_188, B_2]: (r2_hidden('#skF_3'(A_186, B_187, C_188), B_2) | ~r1_tarski('#skF_7', B_2) | ~r1_tarski(C_188, '#skF_6') | r4_lattice3(A_186, B_187, C_188) | ~m1_subset_1(B_187, u1_struct_0(A_186)) | ~l3_lattices(A_186) | v2_struct_0(A_186))), inference(resolution, [status(thm)], [c_288, c_2])).
% 4.63/1.79  tff(c_40, plain, (![A_32, B_44, C_50]: (m1_subset_1('#skF_3'(A_32, B_44, C_50), u1_struct_0(A_32)) | r4_lattice3(A_32, B_44, C_50) | ~m1_subset_1(B_44, u1_struct_0(A_32)) | ~l3_lattices(A_32) | v2_struct_0(A_32))), inference(cnfTransformation, [status(thm)], [f_109])).
% 4.63/1.79  tff(c_58, plain, (![A_70, B_74, C_76]: (r3_lattices(A_70, B_74, k15_lattice3(A_70, C_76)) | ~r2_hidden(B_74, C_76) | ~m1_subset_1(B_74, u1_struct_0(A_70)) | ~l3_lattices(A_70) | ~v4_lattice3(A_70) | ~v10_lattices(A_70) | v2_struct_0(A_70))), inference(cnfTransformation, [status(thm)], [f_170])).
% 4.63/1.79  tff(c_328, plain, (![A_201, B_202, C_203]: (r1_lattices(A_201, B_202, C_203) | ~r3_lattices(A_201, B_202, C_203) | ~m1_subset_1(C_203, u1_struct_0(A_201)) | ~m1_subset_1(B_202, u1_struct_0(A_201)) | ~l3_lattices(A_201) | ~v9_lattices(A_201) | ~v8_lattices(A_201) | ~v6_lattices(A_201) | v2_struct_0(A_201))), inference(cnfTransformation, [status(thm)], [f_73])).
% 4.63/1.79  tff(c_583, plain, (![A_284, B_285, C_286]: (r1_lattices(A_284, B_285, k15_lattice3(A_284, C_286)) | ~m1_subset_1(k15_lattice3(A_284, C_286), u1_struct_0(A_284)) | ~v9_lattices(A_284) | ~v8_lattices(A_284) | ~v6_lattices(A_284) | ~r2_hidden(B_285, C_286) | ~m1_subset_1(B_285, u1_struct_0(A_284)) | ~l3_lattices(A_284) | ~v4_lattice3(A_284) | ~v10_lattices(A_284) | v2_struct_0(A_284))), inference(resolution, [status(thm)], [c_58, c_328])).
% 4.63/1.79  tff(c_585, plain, (![B_285]: (r1_lattices('#skF_5', B_285, k15_lattice3('#skF_5', '#skF_7')) | ~v9_lattices('#skF_5') | ~v8_lattices('#skF_5') | ~v6_lattices('#skF_5') | ~r2_hidden(B_285, '#skF_7') | ~m1_subset_1(B_285, u1_struct_0('#skF_5')) | ~l3_lattices('#skF_5') | ~v4_lattice3('#skF_5') | ~v10_lattices('#skF_5') | v2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_497, c_583])).
% 4.63/1.79  tff(c_592, plain, (![B_285]: (r1_lattices('#skF_5', B_285, k15_lattice3('#skF_5', '#skF_7')) | ~r2_hidden(B_285, '#skF_7') | ~m1_subset_1(B_285, u1_struct_0('#skF_5')) | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_66, c_377, c_403, c_388, c_585])).
% 4.63/1.79  tff(c_608, plain, (![B_288]: (r1_lattices('#skF_5', B_288, k15_lattice3('#skF_5', '#skF_7')) | ~r2_hidden(B_288, '#skF_7') | ~m1_subset_1(B_288, u1_struct_0('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_72, c_592])).
% 4.63/1.79  tff(c_36, plain, (![A_32, B_44, C_50]: (~r1_lattices(A_32, '#skF_3'(A_32, B_44, C_50), B_44) | r4_lattice3(A_32, B_44, C_50) | ~m1_subset_1(B_44, u1_struct_0(A_32)) | ~l3_lattices(A_32) | v2_struct_0(A_32))), inference(cnfTransformation, [status(thm)], [f_109])).
% 4.63/1.79  tff(c_615, plain, (![C_50]: (r4_lattice3('#skF_5', k15_lattice3('#skF_5', '#skF_7'), C_50) | ~m1_subset_1(k15_lattice3('#skF_5', '#skF_7'), u1_struct_0('#skF_5')) | ~l3_lattices('#skF_5') | v2_struct_0('#skF_5') | ~r2_hidden('#skF_3'('#skF_5', k15_lattice3('#skF_5', '#skF_7'), C_50), '#skF_7') | ~m1_subset_1('#skF_3'('#skF_5', k15_lattice3('#skF_5', '#skF_7'), C_50), u1_struct_0('#skF_5')))), inference(resolution, [status(thm)], [c_608, c_36])).
% 4.63/1.79  tff(c_621, plain, (![C_50]: (r4_lattice3('#skF_5', k15_lattice3('#skF_5', '#skF_7'), C_50) | v2_struct_0('#skF_5') | ~r2_hidden('#skF_3'('#skF_5', k15_lattice3('#skF_5', '#skF_7'), C_50), '#skF_7') | ~m1_subset_1('#skF_3'('#skF_5', k15_lattice3('#skF_5', '#skF_7'), C_50), u1_struct_0('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_497, c_615])).
% 4.63/1.79  tff(c_662, plain, (![C_295]: (r4_lattice3('#skF_5', k15_lattice3('#skF_5', '#skF_7'), C_295) | ~r2_hidden('#skF_3'('#skF_5', k15_lattice3('#skF_5', '#skF_7'), C_295), '#skF_7') | ~m1_subset_1('#skF_3'('#skF_5', k15_lattice3('#skF_5', '#skF_7'), C_295), u1_struct_0('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_72, c_621])).
% 4.63/1.79  tff(c_666, plain, (![C_50]: (~r2_hidden('#skF_3'('#skF_5', k15_lattice3('#skF_5', '#skF_7'), C_50), '#skF_7') | r4_lattice3('#skF_5', k15_lattice3('#skF_5', '#skF_7'), C_50) | ~m1_subset_1(k15_lattice3('#skF_5', '#skF_7'), u1_struct_0('#skF_5')) | ~l3_lattices('#skF_5') | v2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_40, c_662])).
% 4.63/1.79  tff(c_669, plain, (![C_50]: (~r2_hidden('#skF_3'('#skF_5', k15_lattice3('#skF_5', '#skF_7'), C_50), '#skF_7') | r4_lattice3('#skF_5', k15_lattice3('#skF_5', '#skF_7'), C_50) | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_497, c_666])).
% 4.63/1.79  tff(c_671, plain, (![C_296]: (~r2_hidden('#skF_3'('#skF_5', k15_lattice3('#skF_5', '#skF_7'), C_296), '#skF_7') | r4_lattice3('#skF_5', k15_lattice3('#skF_5', '#skF_7'), C_296))), inference(negUnitSimplification, [status(thm)], [c_72, c_669])).
% 4.63/1.79  tff(c_675, plain, (![C_188]: (~r1_tarski('#skF_7', '#skF_7') | ~r1_tarski(C_188, '#skF_6') | r4_lattice3('#skF_5', k15_lattice3('#skF_5', '#skF_7'), C_188) | ~m1_subset_1(k15_lattice3('#skF_5', '#skF_7'), u1_struct_0('#skF_5')) | ~l3_lattices('#skF_5') | v2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_297, c_671])).
% 4.63/1.79  tff(c_690, plain, (![C_188]: (~r1_tarski(C_188, '#skF_6') | r4_lattice3('#skF_5', k15_lattice3('#skF_5', '#skF_7'), C_188) | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_497, c_86, c_675])).
% 4.63/1.79  tff(c_704, plain, (![C_297]: (~r1_tarski(C_297, '#skF_6') | r4_lattice3('#skF_5', k15_lattice3('#skF_5', '#skF_7'), C_297))), inference(negUnitSimplification, [status(thm)], [c_72, c_690])).
% 4.63/1.79  tff(c_496, plain, (~r4_lattice3('#skF_5', k15_lattice3('#skF_5', '#skF_7'), '#skF_6')), inference(splitRight, [status(thm)], [c_482])).
% 4.63/1.79  tff(c_707, plain, (~r1_tarski('#skF_6', '#skF_6')), inference(resolution, [status(thm)], [c_704, c_496])).
% 4.63/1.79  tff(c_711, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_86, c_707])).
% 4.63/1.79  tff(c_712, plain, (~r3_lattices('#skF_5', k16_lattice3('#skF_5', '#skF_7'), k16_lattice3('#skF_5', '#skF_6'))), inference(splitRight, [status(thm)], [c_62])).
% 4.63/1.79  tff(c_842, plain, (~r3_lattice3('#skF_5', k16_lattice3('#skF_5', '#skF_7'), '#skF_6') | ~m1_subset_1(k16_lattice3('#skF_5', '#skF_7'), u1_struct_0('#skF_5')) | ~l3_lattices('#skF_5') | ~v4_lattice3('#skF_5') | ~v10_lattices('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_839, c_712])).
% 4.63/1.79  tff(c_845, plain, (~r3_lattice3('#skF_5', k16_lattice3('#skF_5', '#skF_7'), '#skF_6') | ~m1_subset_1(k16_lattice3('#skF_5', '#skF_7'), u1_struct_0('#skF_5')) | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_66, c_842])).
% 4.63/1.79  tff(c_846, plain, (~r3_lattice3('#skF_5', k16_lattice3('#skF_5', '#skF_7'), '#skF_6') | ~m1_subset_1(k16_lattice3('#skF_5', '#skF_7'), u1_struct_0('#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_72, c_845])).
% 4.63/1.79  tff(c_847, plain, (~m1_subset_1(k16_lattice3('#skF_5', '#skF_7'), u1_struct_0('#skF_5'))), inference(splitLeft, [status(thm)], [c_846])).
% 4.63/1.79  tff(c_850, plain, (~l3_lattices('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_54, c_847])).
% 4.63/1.79  tff(c_853, plain, (v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_850])).
% 4.63/1.79  tff(c_855, plain, $false, inference(negUnitSimplification, [status(thm)], [c_72, c_853])).
% 4.63/1.79  tff(c_857, plain, (m1_subset_1(k16_lattice3('#skF_5', '#skF_7'), u1_struct_0('#skF_5'))), inference(splitRight, [status(thm)], [c_846])).
% 4.63/1.79  tff(c_768, plain, (![A_325, B_326, C_327]: (r2_hidden('#skF_2'(A_325, B_326, C_327), C_327) | r3_lattice3(A_325, B_326, C_327) | ~m1_subset_1(B_326, u1_struct_0(A_325)) | ~l3_lattices(A_325) | v2_struct_0(A_325))), inference(cnfTransformation, [status(thm)], [f_91])).
% 4.63/1.79  tff(c_858, plain, (![A_369, B_370, C_371, B_372]: (r2_hidden('#skF_2'(A_369, B_370, C_371), B_372) | ~r1_tarski(C_371, B_372) | r3_lattice3(A_369, B_370, C_371) | ~m1_subset_1(B_370, u1_struct_0(A_369)) | ~l3_lattices(A_369) | v2_struct_0(A_369))), inference(resolution, [status(thm)], [c_768, c_2])).
% 4.63/1.79  tff(c_1092, plain, (![B_408, C_410, B_407, A_406, B_409]: (r2_hidden('#skF_2'(A_406, B_407, C_410), B_409) | ~r1_tarski(B_408, B_409) | ~r1_tarski(C_410, B_408) | r3_lattice3(A_406, B_407, C_410) | ~m1_subset_1(B_407, u1_struct_0(A_406)) | ~l3_lattices(A_406) | v2_struct_0(A_406))), inference(resolution, [status(thm)], [c_858, c_2])).
% 4.63/1.79  tff(c_1102, plain, (![A_411, B_412, C_413]: (r2_hidden('#skF_2'(A_411, B_412, C_413), '#skF_7') | ~r1_tarski(C_413, '#skF_6') | r3_lattice3(A_411, B_412, C_413) | ~m1_subset_1(B_412, u1_struct_0(A_411)) | ~l3_lattices(A_411) | v2_struct_0(A_411))), inference(resolution, [status(thm)], [c_64, c_1092])).
% 4.63/1.79  tff(c_1111, plain, (![A_411, B_412, C_413, B_2]: (r2_hidden('#skF_2'(A_411, B_412, C_413), B_2) | ~r1_tarski('#skF_7', B_2) | ~r1_tarski(C_413, '#skF_6') | r3_lattice3(A_411, B_412, C_413) | ~m1_subset_1(B_412, u1_struct_0(A_411)) | ~l3_lattices(A_411) | v2_struct_0(A_411))), inference(resolution, [status(thm)], [c_1102, c_2])).
% 4.63/1.79  tff(c_32, plain, (![A_10, B_22, C_28]: (m1_subset_1('#skF_2'(A_10, B_22, C_28), u1_struct_0(A_10)) | r3_lattice3(A_10, B_22, C_28) | ~m1_subset_1(B_22, u1_struct_0(A_10)) | ~l3_lattices(A_10) | v2_struct_0(A_10))), inference(cnfTransformation, [status(thm)], [f_91])).
% 4.63/1.79  tff(c_932, plain, (![A_389, B_390, C_391]: (r3_lattices(A_389, B_390, C_391) | ~r1_lattices(A_389, B_390, C_391) | ~m1_subset_1(C_391, u1_struct_0(A_389)) | ~m1_subset_1(B_390, u1_struct_0(A_389)) | ~l3_lattices(A_389) | ~v9_lattices(A_389) | ~v8_lattices(A_389) | ~v6_lattices(A_389) | v2_struct_0(A_389))), inference(cnfTransformation, [status(thm)], [f_73])).
% 4.63/1.79  tff(c_934, plain, (![B_390]: (r3_lattices('#skF_5', B_390, k16_lattice3('#skF_5', '#skF_7')) | ~r1_lattices('#skF_5', B_390, k16_lattice3('#skF_5', '#skF_7')) | ~m1_subset_1(B_390, u1_struct_0('#skF_5')) | ~l3_lattices('#skF_5') | ~v9_lattices('#skF_5') | ~v8_lattices('#skF_5') | ~v6_lattices('#skF_5') | v2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_857, c_932])).
% 4.63/1.79  tff(c_947, plain, (![B_390]: (r3_lattices('#skF_5', B_390, k16_lattice3('#skF_5', '#skF_7')) | ~r1_lattices('#skF_5', B_390, k16_lattice3('#skF_5', '#skF_7')) | ~m1_subset_1(B_390, u1_struct_0('#skF_5')) | ~v9_lattices('#skF_5') | ~v8_lattices('#skF_5') | ~v6_lattices('#skF_5') | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_934])).
% 4.63/1.79  tff(c_948, plain, (![B_390]: (r3_lattices('#skF_5', B_390, k16_lattice3('#skF_5', '#skF_7')) | ~r1_lattices('#skF_5', B_390, k16_lattice3('#skF_5', '#skF_7')) | ~m1_subset_1(B_390, u1_struct_0('#skF_5')) | ~v9_lattices('#skF_5') | ~v8_lattices('#skF_5') | ~v6_lattices('#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_72, c_947])).
% 4.63/1.79  tff(c_957, plain, (~v6_lattices('#skF_5')), inference(splitLeft, [status(thm)], [c_948])).
% 4.63/1.79  tff(c_960, plain, (~v10_lattices('#skF_5') | v2_struct_0('#skF_5') | ~l3_lattices('#skF_5')), inference(resolution, [status(thm)], [c_14, c_957])).
% 4.63/1.79  tff(c_963, plain, (v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_70, c_960])).
% 4.63/1.79  tff(c_965, plain, $false, inference(negUnitSimplification, [status(thm)], [c_72, c_963])).
% 4.63/1.79  tff(c_967, plain, (v6_lattices('#skF_5')), inference(splitRight, [status(thm)], [c_948])).
% 4.63/1.79  tff(c_816, plain, (![A_359, C_360, B_361]: (r3_lattices(A_359, k16_lattice3(A_359, C_360), B_361) | ~r2_hidden(B_361, C_360) | ~m1_subset_1(B_361, u1_struct_0(A_359)) | ~l3_lattices(A_359) | ~v4_lattice3(A_359) | ~v10_lattices(A_359) | v2_struct_0(A_359))), inference(cnfTransformation, [status(thm)], [f_170])).
% 4.63/1.79  tff(c_819, plain, (~r2_hidden(k16_lattice3('#skF_5', '#skF_6'), '#skF_7') | ~m1_subset_1(k16_lattice3('#skF_5', '#skF_6'), u1_struct_0('#skF_5')) | ~l3_lattices('#skF_5') | ~v4_lattice3('#skF_5') | ~v10_lattices('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_816, c_712])).
% 4.63/1.79  tff(c_822, plain, (~r2_hidden(k16_lattice3('#skF_5', '#skF_6'), '#skF_7') | ~m1_subset_1(k16_lattice3('#skF_5', '#skF_6'), u1_struct_0('#skF_5')) | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_66, c_819])).
% 4.63/1.79  tff(c_823, plain, (~r2_hidden(k16_lattice3('#skF_5', '#skF_6'), '#skF_7') | ~m1_subset_1(k16_lattice3('#skF_5', '#skF_6'), u1_struct_0('#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_72, c_822])).
% 4.63/1.79  tff(c_824, plain, (~m1_subset_1(k16_lattice3('#skF_5', '#skF_6'), u1_struct_0('#skF_5'))), inference(splitLeft, [status(thm)], [c_823])).
% 4.63/1.79  tff(c_827, plain, (~l3_lattices('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_54, c_824])).
% 4.63/1.79  tff(c_830, plain, (v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_827])).
% 4.63/1.79  tff(c_832, plain, $false, inference(negUnitSimplification, [status(thm)], [c_72, c_830])).
% 4.63/1.79  tff(c_834, plain, (m1_subset_1(k16_lattice3('#skF_5', '#skF_6'), u1_struct_0('#skF_5'))), inference(splitRight, [status(thm)], [c_823])).
% 4.63/1.79  tff(c_936, plain, (![B_390]: (r3_lattices('#skF_5', B_390, k16_lattice3('#skF_5', '#skF_6')) | ~r1_lattices('#skF_5', B_390, k16_lattice3('#skF_5', '#skF_6')) | ~m1_subset_1(B_390, u1_struct_0('#skF_5')) | ~l3_lattices('#skF_5') | ~v9_lattices('#skF_5') | ~v8_lattices('#skF_5') | ~v6_lattices('#skF_5') | v2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_834, c_932])).
% 4.63/1.79  tff(c_951, plain, (![B_390]: (r3_lattices('#skF_5', B_390, k16_lattice3('#skF_5', '#skF_6')) | ~r1_lattices('#skF_5', B_390, k16_lattice3('#skF_5', '#skF_6')) | ~m1_subset_1(B_390, u1_struct_0('#skF_5')) | ~v9_lattices('#skF_5') | ~v8_lattices('#skF_5') | ~v6_lattices('#skF_5') | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_936])).
% 4.63/1.79  tff(c_952, plain, (![B_390]: (r3_lattices('#skF_5', B_390, k16_lattice3('#skF_5', '#skF_6')) | ~r1_lattices('#skF_5', B_390, k16_lattice3('#skF_5', '#skF_6')) | ~m1_subset_1(B_390, u1_struct_0('#skF_5')) | ~v9_lattices('#skF_5') | ~v8_lattices('#skF_5') | ~v6_lattices('#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_72, c_951])).
% 4.63/1.79  tff(c_969, plain, (![B_390]: (r3_lattices('#skF_5', B_390, k16_lattice3('#skF_5', '#skF_6')) | ~r1_lattices('#skF_5', B_390, k16_lattice3('#skF_5', '#skF_6')) | ~m1_subset_1(B_390, u1_struct_0('#skF_5')) | ~v9_lattices('#skF_5') | ~v8_lattices('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_967, c_952])).
% 4.63/1.79  tff(c_970, plain, (~v8_lattices('#skF_5')), inference(splitLeft, [status(thm)], [c_969])).
% 4.63/1.79  tff(c_973, plain, (~v10_lattices('#skF_5') | v2_struct_0('#skF_5') | ~l3_lattices('#skF_5')), inference(resolution, [status(thm)], [c_10, c_970])).
% 4.63/1.79  tff(c_976, plain, (v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_70, c_973])).
% 4.63/1.79  tff(c_978, plain, $false, inference(negUnitSimplification, [status(thm)], [c_72, c_976])).
% 4.63/1.79  tff(c_980, plain, (v8_lattices('#skF_5')), inference(splitRight, [status(thm)], [c_969])).
% 4.63/1.79  tff(c_979, plain, (![B_390]: (~v9_lattices('#skF_5') | r3_lattices('#skF_5', B_390, k16_lattice3('#skF_5', '#skF_6')) | ~r1_lattices('#skF_5', B_390, k16_lattice3('#skF_5', '#skF_6')) | ~m1_subset_1(B_390, u1_struct_0('#skF_5')))), inference(splitRight, [status(thm)], [c_969])).
% 4.63/1.79  tff(c_981, plain, (~v9_lattices('#skF_5')), inference(splitLeft, [status(thm)], [c_979])).
% 4.63/1.79  tff(c_984, plain, (~v10_lattices('#skF_5') | v2_struct_0('#skF_5') | ~l3_lattices('#skF_5')), inference(resolution, [status(thm)], [c_8, c_981])).
% 4.63/1.79  tff(c_987, plain, (v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_70, c_984])).
% 4.63/1.79  tff(c_989, plain, $false, inference(negUnitSimplification, [status(thm)], [c_72, c_987])).
% 4.63/1.79  tff(c_991, plain, (v9_lattices('#skF_5')), inference(splitRight, [status(thm)], [c_979])).
% 4.63/1.79  tff(c_56, plain, (![A_70, C_76, B_74]: (r3_lattices(A_70, k16_lattice3(A_70, C_76), B_74) | ~r2_hidden(B_74, C_76) | ~m1_subset_1(B_74, u1_struct_0(A_70)) | ~l3_lattices(A_70) | ~v4_lattice3(A_70) | ~v10_lattices(A_70) | v2_struct_0(A_70))), inference(cnfTransformation, [status(thm)], [f_170])).
% 4.63/1.79  tff(c_992, plain, (![A_392, B_393, C_394]: (r1_lattices(A_392, B_393, C_394) | ~r3_lattices(A_392, B_393, C_394) | ~m1_subset_1(C_394, u1_struct_0(A_392)) | ~m1_subset_1(B_393, u1_struct_0(A_392)) | ~l3_lattices(A_392) | ~v9_lattices(A_392) | ~v8_lattices(A_392) | ~v6_lattices(A_392) | v2_struct_0(A_392))), inference(cnfTransformation, [status(thm)], [f_73])).
% 4.63/1.79  tff(c_1274, plain, (![A_483, C_484, B_485]: (r1_lattices(A_483, k16_lattice3(A_483, C_484), B_485) | ~m1_subset_1(k16_lattice3(A_483, C_484), u1_struct_0(A_483)) | ~v9_lattices(A_483) | ~v8_lattices(A_483) | ~v6_lattices(A_483) | ~r2_hidden(B_485, C_484) | ~m1_subset_1(B_485, u1_struct_0(A_483)) | ~l3_lattices(A_483) | ~v4_lattice3(A_483) | ~v10_lattices(A_483) | v2_struct_0(A_483))), inference(resolution, [status(thm)], [c_56, c_992])).
% 4.63/1.79  tff(c_1276, plain, (![B_485]: (r1_lattices('#skF_5', k16_lattice3('#skF_5', '#skF_7'), B_485) | ~v9_lattices('#skF_5') | ~v8_lattices('#skF_5') | ~v6_lattices('#skF_5') | ~r2_hidden(B_485, '#skF_7') | ~m1_subset_1(B_485, u1_struct_0('#skF_5')) | ~l3_lattices('#skF_5') | ~v4_lattice3('#skF_5') | ~v10_lattices('#skF_5') | v2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_857, c_1274])).
% 4.63/1.79  tff(c_1283, plain, (![B_485]: (r1_lattices('#skF_5', k16_lattice3('#skF_5', '#skF_7'), B_485) | ~r2_hidden(B_485, '#skF_7') | ~m1_subset_1(B_485, u1_struct_0('#skF_5')) | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_66, c_967, c_980, c_991, c_1276])).
% 4.63/1.79  tff(c_1290, plain, (![B_486]: (r1_lattices('#skF_5', k16_lattice3('#skF_5', '#skF_7'), B_486) | ~r2_hidden(B_486, '#skF_7') | ~m1_subset_1(B_486, u1_struct_0('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_72, c_1283])).
% 4.63/1.79  tff(c_28, plain, (![A_10, B_22, C_28]: (~r1_lattices(A_10, B_22, '#skF_2'(A_10, B_22, C_28)) | r3_lattice3(A_10, B_22, C_28) | ~m1_subset_1(B_22, u1_struct_0(A_10)) | ~l3_lattices(A_10) | v2_struct_0(A_10))), inference(cnfTransformation, [status(thm)], [f_91])).
% 4.63/1.79  tff(c_1301, plain, (![C_28]: (r3_lattice3('#skF_5', k16_lattice3('#skF_5', '#skF_7'), C_28) | ~m1_subset_1(k16_lattice3('#skF_5', '#skF_7'), u1_struct_0('#skF_5')) | ~l3_lattices('#skF_5') | v2_struct_0('#skF_5') | ~r2_hidden('#skF_2'('#skF_5', k16_lattice3('#skF_5', '#skF_7'), C_28), '#skF_7') | ~m1_subset_1('#skF_2'('#skF_5', k16_lattice3('#skF_5', '#skF_7'), C_28), u1_struct_0('#skF_5')))), inference(resolution, [status(thm)], [c_1290, c_28])).
% 4.63/1.79  tff(c_1311, plain, (![C_28]: (r3_lattice3('#skF_5', k16_lattice3('#skF_5', '#skF_7'), C_28) | v2_struct_0('#skF_5') | ~r2_hidden('#skF_2'('#skF_5', k16_lattice3('#skF_5', '#skF_7'), C_28), '#skF_7') | ~m1_subset_1('#skF_2'('#skF_5', k16_lattice3('#skF_5', '#skF_7'), C_28), u1_struct_0('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_857, c_1301])).
% 4.63/1.79  tff(c_1340, plain, (![C_489]: (r3_lattice3('#skF_5', k16_lattice3('#skF_5', '#skF_7'), C_489) | ~r2_hidden('#skF_2'('#skF_5', k16_lattice3('#skF_5', '#skF_7'), C_489), '#skF_7') | ~m1_subset_1('#skF_2'('#skF_5', k16_lattice3('#skF_5', '#skF_7'), C_489), u1_struct_0('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_72, c_1311])).
% 4.63/1.79  tff(c_1344, plain, (![C_28]: (~r2_hidden('#skF_2'('#skF_5', k16_lattice3('#skF_5', '#skF_7'), C_28), '#skF_7') | r3_lattice3('#skF_5', k16_lattice3('#skF_5', '#skF_7'), C_28) | ~m1_subset_1(k16_lattice3('#skF_5', '#skF_7'), u1_struct_0('#skF_5')) | ~l3_lattices('#skF_5') | v2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_32, c_1340])).
% 4.63/1.79  tff(c_1347, plain, (![C_28]: (~r2_hidden('#skF_2'('#skF_5', k16_lattice3('#skF_5', '#skF_7'), C_28), '#skF_7') | r3_lattice3('#skF_5', k16_lattice3('#skF_5', '#skF_7'), C_28) | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_857, c_1344])).
% 4.63/1.79  tff(c_1349, plain, (![C_490]: (~r2_hidden('#skF_2'('#skF_5', k16_lattice3('#skF_5', '#skF_7'), C_490), '#skF_7') | r3_lattice3('#skF_5', k16_lattice3('#skF_5', '#skF_7'), C_490))), inference(negUnitSimplification, [status(thm)], [c_72, c_1347])).
% 4.63/1.79  tff(c_1353, plain, (![C_413]: (~r1_tarski('#skF_7', '#skF_7') | ~r1_tarski(C_413, '#skF_6') | r3_lattice3('#skF_5', k16_lattice3('#skF_5', '#skF_7'), C_413) | ~m1_subset_1(k16_lattice3('#skF_5', '#skF_7'), u1_struct_0('#skF_5')) | ~l3_lattices('#skF_5') | v2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_1111, c_1349])).
% 4.63/1.79  tff(c_1368, plain, (![C_413]: (~r1_tarski(C_413, '#skF_6') | r3_lattice3('#skF_5', k16_lattice3('#skF_5', '#skF_7'), C_413) | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_857, c_722, c_1353])).
% 4.63/1.79  tff(c_1382, plain, (![C_491]: (~r1_tarski(C_491, '#skF_6') | r3_lattice3('#skF_5', k16_lattice3('#skF_5', '#skF_7'), C_491))), inference(negUnitSimplification, [status(thm)], [c_72, c_1368])).
% 4.63/1.79  tff(c_856, plain, (~r3_lattice3('#skF_5', k16_lattice3('#skF_5', '#skF_7'), '#skF_6')), inference(splitRight, [status(thm)], [c_846])).
% 4.63/1.79  tff(c_1385, plain, (~r1_tarski('#skF_6', '#skF_6')), inference(resolution, [status(thm)], [c_1382, c_856])).
% 4.63/1.79  tff(c_1389, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_722, c_1385])).
% 4.63/1.79  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.63/1.79  
% 4.63/1.79  Inference rules
% 4.63/1.79  ----------------------
% 4.63/1.79  #Ref     : 0
% 4.63/1.80  #Sup     : 251
% 4.63/1.80  #Fact    : 0
% 4.63/1.80  #Define  : 0
% 4.63/1.80  #Split   : 15
% 4.63/1.80  #Chain   : 0
% 4.63/1.80  #Close   : 0
% 4.63/1.80  
% 4.63/1.80  Ordering : KBO
% 4.63/1.80  
% 4.63/1.80  Simplification rules
% 4.63/1.80  ----------------------
% 4.63/1.80  #Subsume      : 63
% 4.63/1.80  #Demod        : 218
% 4.63/1.80  #Tautology    : 15
% 4.63/1.80  #SimpNegUnit  : 71
% 4.63/1.80  #BackRed      : 0
% 4.63/1.80  
% 4.63/1.80  #Partial instantiations: 0
% 4.63/1.80  #Strategies tried      : 1
% 4.63/1.80  
% 4.63/1.80  Timing (in seconds)
% 4.63/1.80  ----------------------
% 4.63/1.80  Preprocessing        : 0.33
% 4.63/1.80  Parsing              : 0.18
% 4.63/1.80  CNF conversion       : 0.03
% 4.63/1.80  Main loop            : 0.65
% 4.63/1.80  Inferencing          : 0.27
% 4.63/1.80  Reduction            : 0.17
% 4.63/1.80  Demodulation         : 0.11
% 4.63/1.80  BG Simplification    : 0.03
% 4.63/1.80  Subsumption          : 0.14
% 4.63/1.80  Abstraction          : 0.02
% 4.63/1.80  MUC search           : 0.00
% 4.63/1.80  Cooper               : 0.00
% 4.63/1.80  Total                : 1.05
% 4.63/1.80  Index Insertion      : 0.00
% 4.63/1.80  Index Deletion       : 0.00
% 4.63/1.80  Index Matching       : 0.00
% 4.63/1.80  BG Taut test         : 0.00
%------------------------------------------------------------------------------
