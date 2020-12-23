%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:24:50 EST 2020

% Result     : Theorem 9.57s
% Output     : CNFRefutation 9.77s
% Verified   : 
% Statistics : Number of formulae       :  179 (5868 expanded)
%              Number of leaves         :   39 (1939 expanded)
%              Depth                    :   37
%              Number of atoms          :  561 (35363 expanded)
%              Number of equality atoms :   26 ( 222 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r4_lattice3 > r3_lattices > r1_lattices > r2_hidden > m1_subset_1 > v9_lattices > v8_lattices > v7_lattices > v6_lattices > v5_lattices > v4_lattices > v4_lattice3 > v2_struct_0 > v10_lattices > l3_lattices > k16_lattice3 > k15_lattice3 > a_2_6_lattice3 > a_2_5_lattice3 > #nlpp > u1_struct_0 > #skF_1 > #skF_8 > #skF_4 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3

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

tff('#skF_8',type,(
    '#skF_8': $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

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

tff(a_2_5_lattice3,type,(
    a_2_5_lattice3: ( $i * $i ) > $i )).

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

tff(a_2_6_lattice3,type,(
    a_2_6_lattice3: ( $i * $i ) > $i )).

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

tff(f_156,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v10_lattices(A)
        & v4_lattice3(A)
        & l3_lattices(A) )
     => ! [B] :
          ( k15_lattice3(A,B) = k15_lattice3(A,a_2_5_lattice3(A,B))
          & k16_lattice3(A,B) = k16_lattice3(A,a_2_6_lattice3(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_lattice3)).

tff(f_119,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & l3_lattices(A) )
     => m1_subset_1(k15_lattice3(A,B),u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k15_lattice3)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d21_lattice3)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r3_lattices)).

tff(f_84,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d17_lattice3)).

tff(f_142,axiom,(
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

tff(c_56,plain,(
    ~ r3_lattices('#skF_5',k15_lattice3('#skF_5','#skF_6'),k15_lattice3('#skF_5','#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_183])).

tff(c_64,plain,(
    ~ v2_struct_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_183])).

tff(c_62,plain,(
    v10_lattices('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_183])).

tff(c_60,plain,(
    v4_lattice3('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_183])).

tff(c_58,plain,(
    l3_lattices('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_183])).

tff(c_52,plain,(
    ! [A_54,B_56] :
      ( k15_lattice3(A_54,a_2_5_lattice3(A_54,B_56)) = k15_lattice3(A_54,B_56)
      | ~ l3_lattices(A_54)
      | ~ v4_lattice3(A_54)
      | ~ v10_lattices(A_54)
      | v2_struct_0(A_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_38,plain,(
    ! [A_39,B_40] :
      ( m1_subset_1(k15_lattice3(A_39,B_40),u1_struct_0(A_39))
      | ~ l3_lattices(A_39)
      | v2_struct_0(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_118,plain,(
    ! [A_103,B_104] :
      ( r4_lattice3(A_103,k15_lattice3(A_103,B_104),B_104)
      | ~ m1_subset_1(k15_lattice3(A_103,B_104),u1_struct_0(A_103))
      | ~ v4_lattice3(A_103)
      | ~ v10_lattices(A_103)
      | ~ l3_lattices(A_103)
      | v2_struct_0(A_103) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_124,plain,(
    ! [A_105,B_106] :
      ( r4_lattice3(A_105,k15_lattice3(A_105,B_106),B_106)
      | ~ v4_lattice3(A_105)
      | ~ v10_lattices(A_105)
      | ~ l3_lattices(A_105)
      | v2_struct_0(A_105) ) ),
    inference(resolution,[status(thm)],[c_38,c_118])).

tff(c_127,plain,(
    ! [A_54,B_56] :
      ( r4_lattice3(A_54,k15_lattice3(A_54,B_56),a_2_5_lattice3(A_54,B_56))
      | ~ v4_lattice3(A_54)
      | ~ v10_lattices(A_54)
      | ~ l3_lattices(A_54)
      | v2_struct_0(A_54)
      | ~ l3_lattices(A_54)
      | ~ v4_lattice3(A_54)
      | ~ v10_lattices(A_54)
      | v2_struct_0(A_54) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_52,c_124])).

tff(c_8,plain,(
    ! [A_1] :
      ( v6_lattices(A_1)
      | ~ v10_lattices(A_1)
      | v2_struct_0(A_1)
      | ~ l3_lattices(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_68,plain,(
    ! [D_68] :
      ( r3_lattices('#skF_5',D_68,'#skF_8'(D_68))
      | ~ r2_hidden(D_68,'#skF_6')
      | ~ m1_subset_1(D_68,u1_struct_0('#skF_5')) ) ),
    inference(cnfTransformation,[status(thm)],[f_183])).

tff(c_152,plain,(
    ! [A_124,B_125,C_126] :
      ( r1_lattices(A_124,B_125,C_126)
      | ~ r3_lattices(A_124,B_125,C_126)
      | ~ m1_subset_1(C_126,u1_struct_0(A_124))
      | ~ m1_subset_1(B_125,u1_struct_0(A_124))
      | ~ l3_lattices(A_124)
      | ~ v9_lattices(A_124)
      | ~ v8_lattices(A_124)
      | ~ v6_lattices(A_124)
      | v2_struct_0(A_124) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_156,plain,(
    ! [D_68] :
      ( r1_lattices('#skF_5',D_68,'#skF_8'(D_68))
      | ~ m1_subset_1('#skF_8'(D_68),u1_struct_0('#skF_5'))
      | ~ l3_lattices('#skF_5')
      | ~ v9_lattices('#skF_5')
      | ~ v8_lattices('#skF_5')
      | ~ v6_lattices('#skF_5')
      | v2_struct_0('#skF_5')
      | ~ r2_hidden(D_68,'#skF_6')
      | ~ m1_subset_1(D_68,u1_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_68,c_152])).

tff(c_160,plain,(
    ! [D_68] :
      ( r1_lattices('#skF_5',D_68,'#skF_8'(D_68))
      | ~ m1_subset_1('#skF_8'(D_68),u1_struct_0('#skF_5'))
      | ~ v9_lattices('#skF_5')
      | ~ v8_lattices('#skF_5')
      | ~ v6_lattices('#skF_5')
      | v2_struct_0('#skF_5')
      | ~ r2_hidden(D_68,'#skF_6')
      | ~ m1_subset_1(D_68,u1_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_156])).

tff(c_161,plain,(
    ! [D_68] :
      ( r1_lattices('#skF_5',D_68,'#skF_8'(D_68))
      | ~ m1_subset_1('#skF_8'(D_68),u1_struct_0('#skF_5'))
      | ~ v9_lattices('#skF_5')
      | ~ v8_lattices('#skF_5')
      | ~ v6_lattices('#skF_5')
      | ~ r2_hidden(D_68,'#skF_6')
      | ~ m1_subset_1(D_68,u1_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_160])).

tff(c_162,plain,(
    ~ v6_lattices('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_161])).

tff(c_165,plain,
    ( ~ v10_lattices('#skF_5')
    | v2_struct_0('#skF_5')
    | ~ l3_lattices('#skF_5') ),
    inference(resolution,[status(thm)],[c_8,c_162])).

tff(c_168,plain,(
    v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_62,c_165])).

tff(c_170,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_168])).

tff(c_172,plain,(
    v6_lattices('#skF_5') ),
    inference(splitRight,[status(thm)],[c_161])).

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

tff(c_171,plain,(
    ! [D_68] :
      ( ~ v8_lattices('#skF_5')
      | ~ v9_lattices('#skF_5')
      | r1_lattices('#skF_5',D_68,'#skF_8'(D_68))
      | ~ m1_subset_1('#skF_8'(D_68),u1_struct_0('#skF_5'))
      | ~ r2_hidden(D_68,'#skF_6')
      | ~ m1_subset_1(D_68,u1_struct_0('#skF_5')) ) ),
    inference(splitRight,[status(thm)],[c_161])).

tff(c_192,plain,(
    ~ v9_lattices('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_171])).

tff(c_195,plain,
    ( ~ v10_lattices('#skF_5')
    | v2_struct_0('#skF_5')
    | ~ l3_lattices('#skF_5') ),
    inference(resolution,[status(thm)],[c_2,c_192])).

tff(c_198,plain,(
    v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_62,c_195])).

tff(c_200,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_198])).

tff(c_202,plain,(
    v9_lattices('#skF_5') ),
    inference(splitRight,[status(thm)],[c_171])).

tff(c_70,plain,(
    ! [D_68] :
      ( m1_subset_1('#skF_8'(D_68),u1_struct_0('#skF_5'))
      | ~ r2_hidden(D_68,'#skF_6')
      | ~ m1_subset_1(D_68,u1_struct_0('#skF_5')) ) ),
    inference(cnfTransformation,[status(thm)],[f_183])).

tff(c_173,plain,(
    ! [A_127,B_128,C_129] :
      ( r3_lattices(A_127,B_128,C_129)
      | ~ r1_lattices(A_127,B_128,C_129)
      | ~ m1_subset_1(C_129,u1_struct_0(A_127))
      | ~ m1_subset_1(B_128,u1_struct_0(A_127))
      | ~ l3_lattices(A_127)
      | ~ v9_lattices(A_127)
      | ~ v8_lattices(A_127)
      | ~ v6_lattices(A_127)
      | v2_struct_0(A_127) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_181,plain,(
    ! [B_128,D_68] :
      ( r3_lattices('#skF_5',B_128,'#skF_8'(D_68))
      | ~ r1_lattices('#skF_5',B_128,'#skF_8'(D_68))
      | ~ m1_subset_1(B_128,u1_struct_0('#skF_5'))
      | ~ l3_lattices('#skF_5')
      | ~ v9_lattices('#skF_5')
      | ~ v8_lattices('#skF_5')
      | ~ v6_lattices('#skF_5')
      | v2_struct_0('#skF_5')
      | ~ r2_hidden(D_68,'#skF_6')
      | ~ m1_subset_1(D_68,u1_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_70,c_173])).

tff(c_189,plain,(
    ! [B_128,D_68] :
      ( r3_lattices('#skF_5',B_128,'#skF_8'(D_68))
      | ~ r1_lattices('#skF_5',B_128,'#skF_8'(D_68))
      | ~ m1_subset_1(B_128,u1_struct_0('#skF_5'))
      | ~ v9_lattices('#skF_5')
      | ~ v8_lattices('#skF_5')
      | v2_struct_0('#skF_5')
      | ~ r2_hidden(D_68,'#skF_6')
      | ~ m1_subset_1(D_68,u1_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_172,c_58,c_181])).

tff(c_190,plain,(
    ! [B_128,D_68] :
      ( r3_lattices('#skF_5',B_128,'#skF_8'(D_68))
      | ~ r1_lattices('#skF_5',B_128,'#skF_8'(D_68))
      | ~ m1_subset_1(B_128,u1_struct_0('#skF_5'))
      | ~ v9_lattices('#skF_5')
      | ~ v8_lattices('#skF_5')
      | ~ r2_hidden(D_68,'#skF_6')
      | ~ m1_subset_1(D_68,u1_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_189])).

tff(c_204,plain,(
    ! [B_128,D_68] :
      ( r3_lattices('#skF_5',B_128,'#skF_8'(D_68))
      | ~ r1_lattices('#skF_5',B_128,'#skF_8'(D_68))
      | ~ m1_subset_1(B_128,u1_struct_0('#skF_5'))
      | ~ v8_lattices('#skF_5')
      | ~ r2_hidden(D_68,'#skF_6')
      | ~ m1_subset_1(D_68,u1_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_202,c_190])).

tff(c_205,plain,(
    ~ v8_lattices('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_204])).

tff(c_208,plain,
    ( ~ v10_lattices('#skF_5')
    | v2_struct_0('#skF_5')
    | ~ l3_lattices('#skF_5') ),
    inference(resolution,[status(thm)],[c_4,c_205])).

tff(c_211,plain,(
    v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_62,c_208])).

tff(c_213,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_211])).

tff(c_215,plain,(
    v8_lattices('#skF_5') ),
    inference(splitRight,[status(thm)],[c_204])).

tff(c_239,plain,(
    ! [A_137,B_138,B_139] :
      ( r3_lattices(A_137,B_138,k15_lattice3(A_137,B_139))
      | ~ r1_lattices(A_137,B_138,k15_lattice3(A_137,B_139))
      | ~ m1_subset_1(B_138,u1_struct_0(A_137))
      | ~ v9_lattices(A_137)
      | ~ v8_lattices(A_137)
      | ~ v6_lattices(A_137)
      | ~ l3_lattices(A_137)
      | v2_struct_0(A_137) ) ),
    inference(resolution,[status(thm)],[c_38,c_173])).

tff(c_244,plain,
    ( ~ r1_lattices('#skF_5',k15_lattice3('#skF_5','#skF_6'),k15_lattice3('#skF_5','#skF_7'))
    | ~ m1_subset_1(k15_lattice3('#skF_5','#skF_6'),u1_struct_0('#skF_5'))
    | ~ v9_lattices('#skF_5')
    | ~ v8_lattices('#skF_5')
    | ~ v6_lattices('#skF_5')
    | ~ l3_lattices('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_239,c_56])).

tff(c_251,plain,
    ( ~ r1_lattices('#skF_5',k15_lattice3('#skF_5','#skF_6'),k15_lattice3('#skF_5','#skF_7'))
    | ~ m1_subset_1(k15_lattice3('#skF_5','#skF_6'),u1_struct_0('#skF_5'))
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_172,c_215,c_202,c_244])).

tff(c_252,plain,
    ( ~ r1_lattices('#skF_5',k15_lattice3('#skF_5','#skF_6'),k15_lattice3('#skF_5','#skF_7'))
    | ~ m1_subset_1(k15_lattice3('#skF_5','#skF_6'),u1_struct_0('#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_251])).

tff(c_253,plain,(
    ~ m1_subset_1(k15_lattice3('#skF_5','#skF_6'),u1_struct_0('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_252])).

tff(c_256,plain,
    ( ~ l3_lattices('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_38,c_253])).

tff(c_259,plain,(
    v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_256])).

tff(c_261,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_259])).

tff(c_263,plain,(
    m1_subset_1(k15_lattice3('#skF_5','#skF_6'),u1_struct_0('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_252])).

tff(c_291,plain,(
    ! [A_149,B_150,D_151] :
      ( r1_lattices(A_149,k15_lattice3(A_149,B_150),D_151)
      | ~ r4_lattice3(A_149,D_151,B_150)
      | ~ m1_subset_1(D_151,u1_struct_0(A_149))
      | ~ m1_subset_1(k15_lattice3(A_149,B_150),u1_struct_0(A_149))
      | ~ v4_lattice3(A_149)
      | ~ v10_lattices(A_149)
      | ~ l3_lattices(A_149)
      | v2_struct_0(A_149) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_293,plain,(
    ! [D_151] :
      ( r1_lattices('#skF_5',k15_lattice3('#skF_5','#skF_6'),D_151)
      | ~ r4_lattice3('#skF_5',D_151,'#skF_6')
      | ~ m1_subset_1(D_151,u1_struct_0('#skF_5'))
      | ~ v4_lattice3('#skF_5')
      | ~ v10_lattices('#skF_5')
      | ~ l3_lattices('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_263,c_291])).

tff(c_300,plain,(
    ! [D_151] :
      ( r1_lattices('#skF_5',k15_lattice3('#skF_5','#skF_6'),D_151)
      | ~ r4_lattice3('#skF_5',D_151,'#skF_6')
      | ~ m1_subset_1(D_151,u1_struct_0('#skF_5'))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_62,c_60,c_293])).

tff(c_303,plain,(
    ! [D_152] :
      ( r1_lattices('#skF_5',k15_lattice3('#skF_5','#skF_6'),D_152)
      | ~ r4_lattice3('#skF_5',D_152,'#skF_6')
      | ~ m1_subset_1(D_152,u1_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_300])).

tff(c_262,plain,(
    ~ r1_lattices('#skF_5',k15_lattice3('#skF_5','#skF_6'),k15_lattice3('#skF_5','#skF_7')) ),
    inference(splitRight,[status(thm)],[c_252])).

tff(c_311,plain,
    ( ~ r4_lattice3('#skF_5',k15_lattice3('#skF_5','#skF_7'),'#skF_6')
    | ~ m1_subset_1(k15_lattice3('#skF_5','#skF_7'),u1_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_303,c_262])).

tff(c_316,plain,(
    ~ m1_subset_1(k15_lattice3('#skF_5','#skF_7'),u1_struct_0('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_311])).

tff(c_319,plain,
    ( ~ l3_lattices('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_38,c_316])).

tff(c_322,plain,(
    v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_319])).

tff(c_324,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_322])).

tff(c_325,plain,(
    ~ r4_lattice3('#skF_5',k15_lattice3('#skF_5','#skF_7'),'#skF_6') ),
    inference(splitRight,[status(thm)],[c_311])).

tff(c_326,plain,(
    m1_subset_1(k15_lattice3('#skF_5','#skF_7'),u1_struct_0('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_311])).

tff(c_24,plain,(
    ! [A_5,B_17,C_23] :
      ( r2_hidden('#skF_1'(A_5,B_17,C_23),C_23)
      | r4_lattice3(A_5,B_17,C_23)
      | ~ m1_subset_1(B_17,u1_struct_0(A_5))
      | ~ l3_lattices(A_5)
      | v2_struct_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_26,plain,(
    ! [A_5,B_17,C_23] :
      ( m1_subset_1('#skF_1'(A_5,B_17,C_23),u1_struct_0(A_5))
      | r4_lattice3(A_5,B_17,C_23)
      | ~ m1_subset_1(B_17,u1_struct_0(A_5))
      | ~ l3_lattices(A_5)
      | v2_struct_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_66,plain,(
    ! [D_68] :
      ( r2_hidden('#skF_8'(D_68),'#skF_7')
      | ~ r2_hidden(D_68,'#skF_6')
      | ~ m1_subset_1(D_68,u1_struct_0('#skF_5')) ) ),
    inference(cnfTransformation,[status(thm)],[f_183])).

tff(c_380,plain,(
    ! [D_157,B_158,C_159,E_160] :
      ( r2_hidden(D_157,a_2_5_lattice3(B_158,C_159))
      | ~ r2_hidden(E_160,C_159)
      | ~ r3_lattices(B_158,D_157,E_160)
      | ~ m1_subset_1(E_160,u1_struct_0(B_158))
      | ~ m1_subset_1(D_157,u1_struct_0(B_158))
      | ~ l3_lattices(B_158)
      | ~ v4_lattice3(B_158)
      | ~ v10_lattices(B_158)
      | v2_struct_0(B_158) ) ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_462,plain,(
    ! [D_175,B_176,D_177] :
      ( r2_hidden(D_175,a_2_5_lattice3(B_176,'#skF_7'))
      | ~ r3_lattices(B_176,D_175,'#skF_8'(D_177))
      | ~ m1_subset_1('#skF_8'(D_177),u1_struct_0(B_176))
      | ~ m1_subset_1(D_175,u1_struct_0(B_176))
      | ~ l3_lattices(B_176)
      | ~ v4_lattice3(B_176)
      | ~ v10_lattices(B_176)
      | v2_struct_0(B_176)
      | ~ r2_hidden(D_177,'#skF_6')
      | ~ m1_subset_1(D_177,u1_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_66,c_380])).

tff(c_466,plain,(
    ! [D_68] :
      ( r2_hidden(D_68,a_2_5_lattice3('#skF_5','#skF_7'))
      | ~ m1_subset_1('#skF_8'(D_68),u1_struct_0('#skF_5'))
      | ~ l3_lattices('#skF_5')
      | ~ v4_lattice3('#skF_5')
      | ~ v10_lattices('#skF_5')
      | v2_struct_0('#skF_5')
      | ~ r2_hidden(D_68,'#skF_6')
      | ~ m1_subset_1(D_68,u1_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_68,c_462])).

tff(c_473,plain,(
    ! [D_68] :
      ( r2_hidden(D_68,a_2_5_lattice3('#skF_5','#skF_7'))
      | ~ m1_subset_1('#skF_8'(D_68),u1_struct_0('#skF_5'))
      | v2_struct_0('#skF_5')
      | ~ r2_hidden(D_68,'#skF_6')
      | ~ m1_subset_1(D_68,u1_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_58,c_466])).

tff(c_475,plain,(
    ! [D_178] :
      ( r2_hidden(D_178,a_2_5_lattice3('#skF_5','#skF_7'))
      | ~ m1_subset_1('#skF_8'(D_178),u1_struct_0('#skF_5'))
      | ~ r2_hidden(D_178,'#skF_6')
      | ~ m1_subset_1(D_178,u1_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_473])).

tff(c_479,plain,(
    ! [D_68] :
      ( r2_hidden(D_68,a_2_5_lattice3('#skF_5','#skF_7'))
      | ~ r2_hidden(D_68,'#skF_6')
      | ~ m1_subset_1(D_68,u1_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_70,c_475])).

tff(c_480,plain,(
    ! [D_179] :
      ( r2_hidden(D_179,a_2_5_lattice3('#skF_5','#skF_7'))
      | ~ r2_hidden(D_179,'#skF_6')
      | ~ m1_subset_1(D_179,u1_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_70,c_475])).

tff(c_48,plain,(
    ! [A_41,B_42,C_43] :
      ( '#skF_3'(A_41,B_42,C_43) = A_41
      | ~ r2_hidden(A_41,a_2_5_lattice3(B_42,C_43))
      | ~ l3_lattices(B_42)
      | ~ v4_lattice3(B_42)
      | ~ v10_lattices(B_42)
      | v2_struct_0(B_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_487,plain,(
    ! [D_179] :
      ( '#skF_3'(D_179,'#skF_5','#skF_7') = D_179
      | ~ l3_lattices('#skF_5')
      | ~ v4_lattice3('#skF_5')
      | ~ v10_lattices('#skF_5')
      | v2_struct_0('#skF_5')
      | ~ r2_hidden(D_179,'#skF_6')
      | ~ m1_subset_1(D_179,u1_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_480,c_48])).

tff(c_492,plain,(
    ! [D_179] :
      ( '#skF_3'(D_179,'#skF_5','#skF_7') = D_179
      | v2_struct_0('#skF_5')
      | ~ r2_hidden(D_179,'#skF_6')
      | ~ m1_subset_1(D_179,u1_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_58,c_487])).

tff(c_494,plain,(
    ! [D_180] :
      ( '#skF_3'(D_180,'#skF_5','#skF_7') = D_180
      | ~ r2_hidden(D_180,'#skF_6')
      | ~ m1_subset_1(D_180,u1_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_492])).

tff(c_516,plain,(
    ! [B_17,C_23] :
      ( '#skF_3'('#skF_1'('#skF_5',B_17,C_23),'#skF_5','#skF_7') = '#skF_1'('#skF_5',B_17,C_23)
      | ~ r2_hidden('#skF_1'('#skF_5',B_17,C_23),'#skF_6')
      | r4_lattice3('#skF_5',B_17,C_23)
      | ~ m1_subset_1(B_17,u1_struct_0('#skF_5'))
      | ~ l3_lattices('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_26,c_494])).

tff(c_540,plain,(
    ! [B_17,C_23] :
      ( '#skF_3'('#skF_1'('#skF_5',B_17,C_23),'#skF_5','#skF_7') = '#skF_1'('#skF_5',B_17,C_23)
      | ~ r2_hidden('#skF_1'('#skF_5',B_17,C_23),'#skF_6')
      | r4_lattice3('#skF_5',B_17,C_23)
      | ~ m1_subset_1(B_17,u1_struct_0('#skF_5'))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_516])).

tff(c_1274,plain,(
    ! [B_236,C_237] :
      ( '#skF_3'('#skF_1'('#skF_5',B_236,C_237),'#skF_5','#skF_7') = '#skF_1'('#skF_5',B_236,C_237)
      | ~ r2_hidden('#skF_1'('#skF_5',B_236,C_237),'#skF_6')
      | r4_lattice3('#skF_5',B_236,C_237)
      | ~ m1_subset_1(B_236,u1_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_540])).

tff(c_1278,plain,(
    ! [B_17] :
      ( '#skF_3'('#skF_1'('#skF_5',B_17,'#skF_6'),'#skF_5','#skF_7') = '#skF_1'('#skF_5',B_17,'#skF_6')
      | r4_lattice3('#skF_5',B_17,'#skF_6')
      | ~ m1_subset_1(B_17,u1_struct_0('#skF_5'))
      | ~ l3_lattices('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_24,c_1274])).

tff(c_1281,plain,(
    ! [B_17] :
      ( '#skF_3'('#skF_1'('#skF_5',B_17,'#skF_6'),'#skF_5','#skF_7') = '#skF_1'('#skF_5',B_17,'#skF_6')
      | r4_lattice3('#skF_5',B_17,'#skF_6')
      | ~ m1_subset_1(B_17,u1_struct_0('#skF_5'))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_1278])).

tff(c_1283,plain,(
    ! [B_238] :
      ( '#skF_3'('#skF_1'('#skF_5',B_238,'#skF_6'),'#skF_5','#skF_7') = '#skF_1'('#skF_5',B_238,'#skF_6')
      | r4_lattice3('#skF_5',B_238,'#skF_6')
      | ~ m1_subset_1(B_238,u1_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_1281])).

tff(c_1307,plain,
    ( '#skF_3'('#skF_1'('#skF_5',k15_lattice3('#skF_5','#skF_7'),'#skF_6'),'#skF_5','#skF_7') = '#skF_1'('#skF_5',k15_lattice3('#skF_5','#skF_7'),'#skF_6')
    | r4_lattice3('#skF_5',k15_lattice3('#skF_5','#skF_7'),'#skF_6') ),
    inference(resolution,[status(thm)],[c_326,c_1283])).

tff(c_1343,plain,(
    '#skF_3'('#skF_1'('#skF_5',k15_lattice3('#skF_5','#skF_7'),'#skF_6'),'#skF_5','#skF_7') = '#skF_1'('#skF_5',k15_lattice3('#skF_5','#skF_7'),'#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_325,c_1307])).

tff(c_50,plain,(
    ! [A_41,B_42,C_43] :
      ( m1_subset_1('#skF_3'(A_41,B_42,C_43),u1_struct_0(B_42))
      | ~ r2_hidden(A_41,a_2_5_lattice3(B_42,C_43))
      | ~ l3_lattices(B_42)
      | ~ v4_lattice3(B_42)
      | ~ v10_lattices(B_42)
      | v2_struct_0(B_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_1382,plain,
    ( m1_subset_1('#skF_1'('#skF_5',k15_lattice3('#skF_5','#skF_7'),'#skF_6'),u1_struct_0('#skF_5'))
    | ~ r2_hidden('#skF_1'('#skF_5',k15_lattice3('#skF_5','#skF_7'),'#skF_6'),a_2_5_lattice3('#skF_5','#skF_7'))
    | ~ l3_lattices('#skF_5')
    | ~ v4_lattice3('#skF_5')
    | ~ v10_lattices('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_1343,c_50])).

tff(c_1393,plain,
    ( m1_subset_1('#skF_1'('#skF_5',k15_lattice3('#skF_5','#skF_7'),'#skF_6'),u1_struct_0('#skF_5'))
    | ~ r2_hidden('#skF_1'('#skF_5',k15_lattice3('#skF_5','#skF_7'),'#skF_6'),a_2_5_lattice3('#skF_5','#skF_7'))
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_58,c_1382])).

tff(c_1394,plain,
    ( m1_subset_1('#skF_1'('#skF_5',k15_lattice3('#skF_5','#skF_7'),'#skF_6'),u1_struct_0('#skF_5'))
    | ~ r2_hidden('#skF_1'('#skF_5',k15_lattice3('#skF_5','#skF_7'),'#skF_6'),a_2_5_lattice3('#skF_5','#skF_7')) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_1393])).

tff(c_1396,plain,(
    ~ r2_hidden('#skF_1'('#skF_5',k15_lattice3('#skF_5','#skF_7'),'#skF_6'),a_2_5_lattice3('#skF_5','#skF_7')) ),
    inference(splitLeft,[status(thm)],[c_1394])).

tff(c_1400,plain,
    ( ~ r2_hidden('#skF_1'('#skF_5',k15_lattice3('#skF_5','#skF_7'),'#skF_6'),'#skF_6')
    | ~ m1_subset_1('#skF_1'('#skF_5',k15_lattice3('#skF_5','#skF_7'),'#skF_6'),u1_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_479,c_1396])).

tff(c_1451,plain,(
    ~ m1_subset_1('#skF_1'('#skF_5',k15_lattice3('#skF_5','#skF_7'),'#skF_6'),u1_struct_0('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_1400])).

tff(c_1454,plain,
    ( r4_lattice3('#skF_5',k15_lattice3('#skF_5','#skF_7'),'#skF_6')
    | ~ m1_subset_1(k15_lattice3('#skF_5','#skF_7'),u1_struct_0('#skF_5'))
    | ~ l3_lattices('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_26,c_1451])).

tff(c_1457,plain,
    ( r4_lattice3('#skF_5',k15_lattice3('#skF_5','#skF_7'),'#skF_6')
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_326,c_1454])).

tff(c_1459,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_325,c_1457])).

tff(c_1460,plain,(
    ~ r2_hidden('#skF_1'('#skF_5',k15_lattice3('#skF_5','#skF_7'),'#skF_6'),'#skF_6') ),
    inference(splitRight,[status(thm)],[c_1400])).

tff(c_1464,plain,
    ( r4_lattice3('#skF_5',k15_lattice3('#skF_5','#skF_7'),'#skF_6')
    | ~ m1_subset_1(k15_lattice3('#skF_5','#skF_7'),u1_struct_0('#skF_5'))
    | ~ l3_lattices('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_24,c_1460])).

tff(c_1467,plain,
    ( r4_lattice3('#skF_5',k15_lattice3('#skF_5','#skF_7'),'#skF_6')
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_326,c_1464])).

tff(c_1469,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_325,c_1467])).

tff(c_1470,plain,(
    m1_subset_1('#skF_1'('#skF_5',k15_lattice3('#skF_5','#skF_7'),'#skF_6'),u1_struct_0('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_1394])).

tff(c_1333,plain,(
    ! [B_40] :
      ( '#skF_3'('#skF_1'('#skF_5',k15_lattice3('#skF_5',B_40),'#skF_6'),'#skF_5','#skF_7') = '#skF_1'('#skF_5',k15_lattice3('#skF_5',B_40),'#skF_6')
      | r4_lattice3('#skF_5',k15_lattice3('#skF_5',B_40),'#skF_6')
      | ~ l3_lattices('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_38,c_1283])).

tff(c_1364,plain,(
    ! [B_40] :
      ( '#skF_3'('#skF_1'('#skF_5',k15_lattice3('#skF_5',B_40),'#skF_6'),'#skF_5','#skF_7') = '#skF_1'('#skF_5',k15_lattice3('#skF_5',B_40),'#skF_6')
      | r4_lattice3('#skF_5',k15_lattice3('#skF_5',B_40),'#skF_6')
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_1333])).

tff(c_1532,plain,(
    ! [B_250] :
      ( '#skF_3'('#skF_1'('#skF_5',k15_lattice3('#skF_5',B_250),'#skF_6'),'#skF_5','#skF_7') = '#skF_1'('#skF_5',k15_lattice3('#skF_5',B_250),'#skF_6')
      | r4_lattice3('#skF_5',k15_lattice3('#skF_5',B_250),'#skF_6') ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_1364])).

tff(c_1563,plain,(
    ! [B_56] :
      ( '#skF_1'('#skF_5',k15_lattice3('#skF_5',a_2_5_lattice3('#skF_5',B_56)),'#skF_6') = '#skF_3'('#skF_1'('#skF_5',k15_lattice3('#skF_5',B_56),'#skF_6'),'#skF_5','#skF_7')
      | r4_lattice3('#skF_5',k15_lattice3('#skF_5',a_2_5_lattice3('#skF_5',B_56)),'#skF_6')
      | ~ l3_lattices('#skF_5')
      | ~ v4_lattice3('#skF_5')
      | ~ v10_lattices('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_52,c_1532])).

tff(c_1580,plain,(
    ! [B_56] :
      ( '#skF_1'('#skF_5',k15_lattice3('#skF_5',a_2_5_lattice3('#skF_5',B_56)),'#skF_6') = '#skF_3'('#skF_1'('#skF_5',k15_lattice3('#skF_5',B_56),'#skF_6'),'#skF_5','#skF_7')
      | r4_lattice3('#skF_5',k15_lattice3('#skF_5',a_2_5_lattice3('#skF_5',B_56)),'#skF_6')
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_58,c_1563])).

tff(c_1581,plain,(
    ! [B_56] :
      ( '#skF_1'('#skF_5',k15_lattice3('#skF_5',a_2_5_lattice3('#skF_5',B_56)),'#skF_6') = '#skF_3'('#skF_1'('#skF_5',k15_lattice3('#skF_5',B_56),'#skF_6'),'#skF_5','#skF_7')
      | r4_lattice3('#skF_5',k15_lattice3('#skF_5',a_2_5_lattice3('#skF_5',B_56)),'#skF_6') ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_1580])).

tff(c_301,plain,(
    ! [D_151] :
      ( r1_lattices('#skF_5',k15_lattice3('#skF_5','#skF_6'),D_151)
      | ~ r4_lattice3('#skF_5',D_151,'#skF_6')
      | ~ m1_subset_1(D_151,u1_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_300])).

tff(c_3673,plain,(
    ! [A_367,B_368,B_369] :
      ( r3_lattices(A_367,B_368,k15_lattice3(A_367,B_369))
      | ~ r1_lattices(A_367,B_368,k15_lattice3(A_367,a_2_5_lattice3(A_367,B_369)))
      | ~ m1_subset_1(B_368,u1_struct_0(A_367))
      | ~ v9_lattices(A_367)
      | ~ v8_lattices(A_367)
      | ~ v6_lattices(A_367)
      | ~ l3_lattices(A_367)
      | v2_struct_0(A_367)
      | ~ l3_lattices(A_367)
      | ~ v4_lattice3(A_367)
      | ~ v10_lattices(A_367)
      | v2_struct_0(A_367) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_52,c_239])).

tff(c_3795,plain,(
    ! [B_369] :
      ( r3_lattices('#skF_5',k15_lattice3('#skF_5','#skF_6'),k15_lattice3('#skF_5',B_369))
      | ~ m1_subset_1(k15_lattice3('#skF_5','#skF_6'),u1_struct_0('#skF_5'))
      | ~ v9_lattices('#skF_5')
      | ~ v8_lattices('#skF_5')
      | ~ v6_lattices('#skF_5')
      | ~ l3_lattices('#skF_5')
      | ~ v4_lattice3('#skF_5')
      | ~ v10_lattices('#skF_5')
      | v2_struct_0('#skF_5')
      | ~ r4_lattice3('#skF_5',k15_lattice3('#skF_5',a_2_5_lattice3('#skF_5',B_369)),'#skF_6')
      | ~ m1_subset_1(k15_lattice3('#skF_5',a_2_5_lattice3('#skF_5',B_369)),u1_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_301,c_3673])).

tff(c_3917,plain,(
    ! [B_369] :
      ( r3_lattices('#skF_5',k15_lattice3('#skF_5','#skF_6'),k15_lattice3('#skF_5',B_369))
      | v2_struct_0('#skF_5')
      | ~ r4_lattice3('#skF_5',k15_lattice3('#skF_5',a_2_5_lattice3('#skF_5',B_369)),'#skF_6')
      | ~ m1_subset_1(k15_lattice3('#skF_5',a_2_5_lattice3('#skF_5',B_369)),u1_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_58,c_172,c_215,c_202,c_263,c_3795])).

tff(c_3923,plain,(
    ! [B_370] :
      ( r3_lattices('#skF_5',k15_lattice3('#skF_5','#skF_6'),k15_lattice3('#skF_5',B_370))
      | ~ r4_lattice3('#skF_5',k15_lattice3('#skF_5',a_2_5_lattice3('#skF_5',B_370)),'#skF_6')
      | ~ m1_subset_1(k15_lattice3('#skF_5',a_2_5_lattice3('#skF_5',B_370)),u1_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_3917])).

tff(c_3945,plain,(
    ! [B_370] :
      ( r3_lattices('#skF_5',k15_lattice3('#skF_5','#skF_6'),k15_lattice3('#skF_5',B_370))
      | ~ r4_lattice3('#skF_5',k15_lattice3('#skF_5',a_2_5_lattice3('#skF_5',B_370)),'#skF_6')
      | ~ l3_lattices('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_38,c_3923])).

tff(c_3955,plain,(
    ! [B_370] :
      ( r3_lattices('#skF_5',k15_lattice3('#skF_5','#skF_6'),k15_lattice3('#skF_5',B_370))
      | ~ r4_lattice3('#skF_5',k15_lattice3('#skF_5',a_2_5_lattice3('#skF_5',B_370)),'#skF_6')
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_3945])).

tff(c_3957,plain,(
    ! [B_371] :
      ( r3_lattices('#skF_5',k15_lattice3('#skF_5','#skF_6'),k15_lattice3('#skF_5',B_371))
      | ~ r4_lattice3('#skF_5',k15_lattice3('#skF_5',a_2_5_lattice3('#skF_5',B_371)),'#skF_6') ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_3955])).

tff(c_4089,plain,(
    ! [B_381] :
      ( r3_lattices('#skF_5',k15_lattice3('#skF_5','#skF_6'),k15_lattice3('#skF_5',B_381))
      | '#skF_1'('#skF_5',k15_lattice3('#skF_5',a_2_5_lattice3('#skF_5',B_381)),'#skF_6') = '#skF_3'('#skF_1'('#skF_5',k15_lattice3('#skF_5',B_381),'#skF_6'),'#skF_5','#skF_7') ) ),
    inference(resolution,[status(thm)],[c_1581,c_3957])).

tff(c_4094,plain,(
    '#skF_1'('#skF_5',k15_lattice3('#skF_5',a_2_5_lattice3('#skF_5','#skF_7')),'#skF_6') = '#skF_3'('#skF_1'('#skF_5',k15_lattice3('#skF_5','#skF_7'),'#skF_6'),'#skF_5','#skF_7') ),
    inference(resolution,[status(thm)],[c_4089,c_56])).

tff(c_4107,plain,(
    '#skF_1'('#skF_5',k15_lattice3('#skF_5',a_2_5_lattice3('#skF_5','#skF_7')),'#skF_6') = '#skF_1'('#skF_5',k15_lattice3('#skF_5','#skF_7'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1343,c_4094])).

tff(c_4142,plain,
    ( r2_hidden('#skF_1'('#skF_5',k15_lattice3('#skF_5','#skF_7'),'#skF_6'),'#skF_6')
    | r4_lattice3('#skF_5',k15_lattice3('#skF_5',a_2_5_lattice3('#skF_5','#skF_7')),'#skF_6')
    | ~ m1_subset_1(k15_lattice3('#skF_5',a_2_5_lattice3('#skF_5','#skF_7')),u1_struct_0('#skF_5'))
    | ~ l3_lattices('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_4107,c_24])).

tff(c_4176,plain,
    ( r2_hidden('#skF_1'('#skF_5',k15_lattice3('#skF_5','#skF_7'),'#skF_6'),'#skF_6')
    | r4_lattice3('#skF_5',k15_lattice3('#skF_5',a_2_5_lattice3('#skF_5','#skF_7')),'#skF_6')
    | ~ m1_subset_1(k15_lattice3('#skF_5',a_2_5_lattice3('#skF_5','#skF_7')),u1_struct_0('#skF_5'))
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_4142])).

tff(c_4177,plain,
    ( r2_hidden('#skF_1'('#skF_5',k15_lattice3('#skF_5','#skF_7'),'#skF_6'),'#skF_6')
    | r4_lattice3('#skF_5',k15_lattice3('#skF_5',a_2_5_lattice3('#skF_5','#skF_7')),'#skF_6')
    | ~ m1_subset_1(k15_lattice3('#skF_5',a_2_5_lattice3('#skF_5','#skF_7')),u1_struct_0('#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_4176])).

tff(c_4185,plain,(
    ~ m1_subset_1(k15_lattice3('#skF_5',a_2_5_lattice3('#skF_5','#skF_7')),u1_struct_0('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_4177])).

tff(c_4200,plain,
    ( ~ m1_subset_1(k15_lattice3('#skF_5','#skF_7'),u1_struct_0('#skF_5'))
    | ~ l3_lattices('#skF_5')
    | ~ v4_lattice3('#skF_5')
    | ~ v10_lattices('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_52,c_4185])).

tff(c_4209,plain,(
    v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_58,c_326,c_4200])).

tff(c_4211,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_4209])).

tff(c_4212,plain,
    ( r4_lattice3('#skF_5',k15_lattice3('#skF_5',a_2_5_lattice3('#skF_5','#skF_7')),'#skF_6')
    | r2_hidden('#skF_1'('#skF_5',k15_lattice3('#skF_5','#skF_7'),'#skF_6'),'#skF_6') ),
    inference(splitRight,[status(thm)],[c_4177])).

tff(c_4248,plain,(
    r2_hidden('#skF_1'('#skF_5',k15_lattice3('#skF_5','#skF_7'),'#skF_6'),'#skF_6') ),
    inference(splitLeft,[status(thm)],[c_4212])).

tff(c_20,plain,(
    ! [A_5,D_26,B_17,C_23] :
      ( r1_lattices(A_5,D_26,B_17)
      | ~ r2_hidden(D_26,C_23)
      | ~ m1_subset_1(D_26,u1_struct_0(A_5))
      | ~ r4_lattice3(A_5,B_17,C_23)
      | ~ m1_subset_1(B_17,u1_struct_0(A_5))
      | ~ l3_lattices(A_5)
      | v2_struct_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_10049,plain,(
    ! [A_581,D_582,B_583] :
      ( r1_lattices(A_581,D_582,B_583)
      | ~ m1_subset_1(D_582,u1_struct_0(A_581))
      | ~ r4_lattice3(A_581,B_583,a_2_5_lattice3('#skF_5','#skF_7'))
      | ~ m1_subset_1(B_583,u1_struct_0(A_581))
      | ~ l3_lattices(A_581)
      | v2_struct_0(A_581)
      | ~ r2_hidden(D_582,'#skF_6')
      | ~ m1_subset_1(D_582,u1_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_480,c_20])).

tff(c_10069,plain,(
    ! [B_583] :
      ( r1_lattices('#skF_5','#skF_1'('#skF_5',k15_lattice3('#skF_5','#skF_7'),'#skF_6'),B_583)
      | ~ r4_lattice3('#skF_5',B_583,a_2_5_lattice3('#skF_5','#skF_7'))
      | ~ m1_subset_1(B_583,u1_struct_0('#skF_5'))
      | ~ l3_lattices('#skF_5')
      | v2_struct_0('#skF_5')
      | ~ r2_hidden('#skF_1'('#skF_5',k15_lattice3('#skF_5','#skF_7'),'#skF_6'),'#skF_6')
      | ~ m1_subset_1('#skF_1'('#skF_5',k15_lattice3('#skF_5','#skF_7'),'#skF_6'),u1_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_1470,c_10049])).

tff(c_10135,plain,(
    ! [B_583] :
      ( r1_lattices('#skF_5','#skF_1'('#skF_5',k15_lattice3('#skF_5','#skF_7'),'#skF_6'),B_583)
      | ~ r4_lattice3('#skF_5',B_583,a_2_5_lattice3('#skF_5','#skF_7'))
      | ~ m1_subset_1(B_583,u1_struct_0('#skF_5'))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1470,c_4248,c_58,c_10069])).

tff(c_10182,plain,(
    ! [B_584] :
      ( r1_lattices('#skF_5','#skF_1'('#skF_5',k15_lattice3('#skF_5','#skF_7'),'#skF_6'),B_584)
      | ~ r4_lattice3('#skF_5',B_584,a_2_5_lattice3('#skF_5','#skF_7'))
      | ~ m1_subset_1(B_584,u1_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_10135])).

tff(c_22,plain,(
    ! [A_5,B_17,C_23] :
      ( ~ r1_lattices(A_5,'#skF_1'(A_5,B_17,C_23),B_17)
      | r4_lattice3(A_5,B_17,C_23)
      | ~ m1_subset_1(B_17,u1_struct_0(A_5))
      | ~ l3_lattices(A_5)
      | v2_struct_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_10258,plain,
    ( r4_lattice3('#skF_5',k15_lattice3('#skF_5','#skF_7'),'#skF_6')
    | ~ l3_lattices('#skF_5')
    | v2_struct_0('#skF_5')
    | ~ r4_lattice3('#skF_5',k15_lattice3('#skF_5','#skF_7'),a_2_5_lattice3('#skF_5','#skF_7'))
    | ~ m1_subset_1(k15_lattice3('#skF_5','#skF_7'),u1_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_10182,c_22])).

tff(c_10323,plain,
    ( r4_lattice3('#skF_5',k15_lattice3('#skF_5','#skF_7'),'#skF_6')
    | v2_struct_0('#skF_5')
    | ~ r4_lattice3('#skF_5',k15_lattice3('#skF_5','#skF_7'),a_2_5_lattice3('#skF_5','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_326,c_58,c_10258])).

tff(c_10324,plain,(
    ~ r4_lattice3('#skF_5',k15_lattice3('#skF_5','#skF_7'),a_2_5_lattice3('#skF_5','#skF_7')) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_325,c_10323])).

tff(c_10327,plain,
    ( ~ l3_lattices('#skF_5')
    | ~ v4_lattice3('#skF_5')
    | ~ v10_lattices('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_127,c_10324])).

tff(c_10330,plain,(
    v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_58,c_10327])).

tff(c_10332,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_10330])).

tff(c_10333,plain,(
    r4_lattice3('#skF_5',k15_lattice3('#skF_5',a_2_5_lattice3('#skF_5','#skF_7')),'#skF_6') ),
    inference(splitRight,[status(thm)],[c_4212])).

tff(c_3956,plain,(
    ! [B_370] :
      ( r3_lattices('#skF_5',k15_lattice3('#skF_5','#skF_6'),k15_lattice3('#skF_5',B_370))
      | ~ r4_lattice3('#skF_5',k15_lattice3('#skF_5',a_2_5_lattice3('#skF_5',B_370)),'#skF_6') ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_3955])).

tff(c_10337,plain,(
    r3_lattices('#skF_5',k15_lattice3('#skF_5','#skF_6'),k15_lattice3('#skF_5','#skF_7')) ),
    inference(resolution,[status(thm)],[c_10333,c_3956])).

tff(c_10344,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_10337])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:34:26 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 9.57/3.38  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.77/3.39  
% 9.77/3.39  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.77/3.40  %$ r4_lattice3 > r3_lattices > r1_lattices > r2_hidden > m1_subset_1 > v9_lattices > v8_lattices > v7_lattices > v6_lattices > v5_lattices > v4_lattices > v4_lattice3 > v2_struct_0 > v10_lattices > l3_lattices > k16_lattice3 > k15_lattice3 > a_2_6_lattice3 > a_2_5_lattice3 > #nlpp > u1_struct_0 > #skF_1 > #skF_8 > #skF_4 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3
% 9.77/3.40  
% 9.77/3.40  %Foreground sorts:
% 9.77/3.40  
% 9.77/3.40  
% 9.77/3.40  %Background operators:
% 9.77/3.40  
% 9.77/3.40  
% 9.77/3.40  %Foreground operators:
% 9.77/3.40  tff(l3_lattices, type, l3_lattices: $i > $o).
% 9.77/3.40  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 9.77/3.40  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 9.77/3.40  tff(r3_lattices, type, r3_lattices: ($i * $i * $i) > $o).
% 9.77/3.40  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 9.77/3.40  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 9.77/3.40  tff(k16_lattice3, type, k16_lattice3: ($i * $i) > $i).
% 9.77/3.40  tff(k15_lattice3, type, k15_lattice3: ($i * $i) > $i).
% 9.77/3.40  tff('#skF_8', type, '#skF_8': $i > $i).
% 9.77/3.40  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 9.77/3.40  tff('#skF_7', type, '#skF_7': $i).
% 9.77/3.40  tff(r1_lattices, type, r1_lattices: ($i * $i * $i) > $o).
% 9.77/3.40  tff('#skF_5', type, '#skF_5': $i).
% 9.77/3.40  tff(v4_lattices, type, v4_lattices: $i > $o).
% 9.77/3.40  tff('#skF_6', type, '#skF_6': $i).
% 9.77/3.40  tff(v6_lattices, type, v6_lattices: $i > $o).
% 9.77/3.40  tff(v9_lattices, type, v9_lattices: $i > $o).
% 9.77/3.40  tff(r4_lattice3, type, r4_lattice3: ($i * $i * $i) > $o).
% 9.77/3.40  tff(a_2_5_lattice3, type, a_2_5_lattice3: ($i * $i) > $i).
% 9.77/3.40  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 9.77/3.40  tff(v4_lattice3, type, v4_lattice3: $i > $o).
% 9.77/3.40  tff(v5_lattices, type, v5_lattices: $i > $o).
% 9.77/3.40  tff(v10_lattices, type, v10_lattices: $i > $o).
% 9.77/3.40  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 9.77/3.40  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 9.77/3.40  tff(v8_lattices, type, v8_lattices: $i > $o).
% 9.77/3.40  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 9.77/3.40  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 9.77/3.40  tff(a_2_6_lattice3, type, a_2_6_lattice3: ($i * $i) > $i).
% 9.77/3.40  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 9.77/3.40  tff(v7_lattices, type, v7_lattices: $i > $o).
% 9.77/3.40  
% 9.77/3.42  tff(f_183, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v10_lattices(A)) & v4_lattice3(A)) & l3_lattices(A)) => (![B, C]: ((![D]: (m1_subset_1(D, u1_struct_0(A)) => ~(r2_hidden(D, B) & (![E]: (m1_subset_1(E, u1_struct_0(A)) => ~(r3_lattices(A, D, E) & r2_hidden(E, C))))))) => r3_lattices(A, k15_lattice3(A, B), k15_lattice3(A, C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_lattice3)).
% 9.77/3.42  tff(f_156, axiom, (![A]: ((((~v2_struct_0(A) & v10_lattices(A)) & v4_lattice3(A)) & l3_lattices(A)) => (![B]: ((k15_lattice3(A, B) = k15_lattice3(A, a_2_5_lattice3(A, B))) & (k16_lattice3(A, B) = k16_lattice3(A, a_2_6_lattice3(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_lattice3)).
% 9.77/3.42  tff(f_119, axiom, (![A, B]: ((~v2_struct_0(A) & l3_lattices(A)) => m1_subset_1(k15_lattice3(A, B), u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k15_lattice3)).
% 9.77/3.42  tff(f_112, axiom, (![A]: ((~v2_struct_0(A) & l3_lattices(A)) => ((((~v2_struct_0(A) & v10_lattices(A)) & v4_lattice3(A)) & l3_lattices(A)) => (![B, C]: (m1_subset_1(C, u1_struct_0(A)) => ((C = k15_lattice3(A, B)) <=> (r4_lattice3(A, C, B) & (![D]: (m1_subset_1(D, u1_struct_0(A)) => (r4_lattice3(A, D, B) => r1_lattices(A, C, D))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d21_lattice3)).
% 9.77/3.42  tff(f_47, axiom, (![A]: (l3_lattices(A) => ((~v2_struct_0(A) & v10_lattices(A)) => ((((((~v2_struct_0(A) & v4_lattices(A)) & v5_lattices(A)) & v6_lattices(A)) & v7_lattices(A)) & v8_lattices(A)) & v9_lattices(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_lattices)).
% 9.77/3.42  tff(f_66, axiom, (![A, B, C]: (((((((~v2_struct_0(A) & v6_lattices(A)) & v8_lattices(A)) & v9_lattices(A)) & l3_lattices(A)) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => (r3_lattices(A, B, C) <=> r1_lattices(A, B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r3_lattices)).
% 9.77/3.42  tff(f_84, axiom, (![A]: ((~v2_struct_0(A) & l3_lattices(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (r4_lattice3(A, B, C) <=> (![D]: (m1_subset_1(D, u1_struct_0(A)) => (r2_hidden(D, C) => r1_lattices(A, D, B)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d17_lattice3)).
% 9.77/3.42  tff(f_142, axiom, (![A, B, C]: ((((~v2_struct_0(B) & v10_lattices(B)) & v4_lattice3(B)) & l3_lattices(B)) => (r2_hidden(A, a_2_5_lattice3(B, C)) <=> (?[D]: ((m1_subset_1(D, u1_struct_0(B)) & (A = D)) & (?[E]: ((m1_subset_1(E, u1_struct_0(B)) & r3_lattices(B, D, E)) & r2_hidden(E, C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fraenkel_a_2_5_lattice3)).
% 9.77/3.42  tff(c_56, plain, (~r3_lattices('#skF_5', k15_lattice3('#skF_5', '#skF_6'), k15_lattice3('#skF_5', '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_183])).
% 9.77/3.42  tff(c_64, plain, (~v2_struct_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_183])).
% 9.77/3.42  tff(c_62, plain, (v10_lattices('#skF_5')), inference(cnfTransformation, [status(thm)], [f_183])).
% 9.77/3.42  tff(c_60, plain, (v4_lattice3('#skF_5')), inference(cnfTransformation, [status(thm)], [f_183])).
% 9.77/3.42  tff(c_58, plain, (l3_lattices('#skF_5')), inference(cnfTransformation, [status(thm)], [f_183])).
% 9.77/3.42  tff(c_52, plain, (![A_54, B_56]: (k15_lattice3(A_54, a_2_5_lattice3(A_54, B_56))=k15_lattice3(A_54, B_56) | ~l3_lattices(A_54) | ~v4_lattice3(A_54) | ~v10_lattices(A_54) | v2_struct_0(A_54))), inference(cnfTransformation, [status(thm)], [f_156])).
% 9.77/3.42  tff(c_38, plain, (![A_39, B_40]: (m1_subset_1(k15_lattice3(A_39, B_40), u1_struct_0(A_39)) | ~l3_lattices(A_39) | v2_struct_0(A_39))), inference(cnfTransformation, [status(thm)], [f_119])).
% 9.77/3.42  tff(c_118, plain, (![A_103, B_104]: (r4_lattice3(A_103, k15_lattice3(A_103, B_104), B_104) | ~m1_subset_1(k15_lattice3(A_103, B_104), u1_struct_0(A_103)) | ~v4_lattice3(A_103) | ~v10_lattices(A_103) | ~l3_lattices(A_103) | v2_struct_0(A_103))), inference(cnfTransformation, [status(thm)], [f_112])).
% 9.77/3.42  tff(c_124, plain, (![A_105, B_106]: (r4_lattice3(A_105, k15_lattice3(A_105, B_106), B_106) | ~v4_lattice3(A_105) | ~v10_lattices(A_105) | ~l3_lattices(A_105) | v2_struct_0(A_105))), inference(resolution, [status(thm)], [c_38, c_118])).
% 9.77/3.42  tff(c_127, plain, (![A_54, B_56]: (r4_lattice3(A_54, k15_lattice3(A_54, B_56), a_2_5_lattice3(A_54, B_56)) | ~v4_lattice3(A_54) | ~v10_lattices(A_54) | ~l3_lattices(A_54) | v2_struct_0(A_54) | ~l3_lattices(A_54) | ~v4_lattice3(A_54) | ~v10_lattices(A_54) | v2_struct_0(A_54))), inference(superposition, [status(thm), theory('equality')], [c_52, c_124])).
% 9.77/3.42  tff(c_8, plain, (![A_1]: (v6_lattices(A_1) | ~v10_lattices(A_1) | v2_struct_0(A_1) | ~l3_lattices(A_1))), inference(cnfTransformation, [status(thm)], [f_47])).
% 9.77/3.42  tff(c_68, plain, (![D_68]: (r3_lattices('#skF_5', D_68, '#skF_8'(D_68)) | ~r2_hidden(D_68, '#skF_6') | ~m1_subset_1(D_68, u1_struct_0('#skF_5')))), inference(cnfTransformation, [status(thm)], [f_183])).
% 9.77/3.42  tff(c_152, plain, (![A_124, B_125, C_126]: (r1_lattices(A_124, B_125, C_126) | ~r3_lattices(A_124, B_125, C_126) | ~m1_subset_1(C_126, u1_struct_0(A_124)) | ~m1_subset_1(B_125, u1_struct_0(A_124)) | ~l3_lattices(A_124) | ~v9_lattices(A_124) | ~v8_lattices(A_124) | ~v6_lattices(A_124) | v2_struct_0(A_124))), inference(cnfTransformation, [status(thm)], [f_66])).
% 9.77/3.42  tff(c_156, plain, (![D_68]: (r1_lattices('#skF_5', D_68, '#skF_8'(D_68)) | ~m1_subset_1('#skF_8'(D_68), u1_struct_0('#skF_5')) | ~l3_lattices('#skF_5') | ~v9_lattices('#skF_5') | ~v8_lattices('#skF_5') | ~v6_lattices('#skF_5') | v2_struct_0('#skF_5') | ~r2_hidden(D_68, '#skF_6') | ~m1_subset_1(D_68, u1_struct_0('#skF_5')))), inference(resolution, [status(thm)], [c_68, c_152])).
% 9.77/3.42  tff(c_160, plain, (![D_68]: (r1_lattices('#skF_5', D_68, '#skF_8'(D_68)) | ~m1_subset_1('#skF_8'(D_68), u1_struct_0('#skF_5')) | ~v9_lattices('#skF_5') | ~v8_lattices('#skF_5') | ~v6_lattices('#skF_5') | v2_struct_0('#skF_5') | ~r2_hidden(D_68, '#skF_6') | ~m1_subset_1(D_68, u1_struct_0('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_156])).
% 9.77/3.42  tff(c_161, plain, (![D_68]: (r1_lattices('#skF_5', D_68, '#skF_8'(D_68)) | ~m1_subset_1('#skF_8'(D_68), u1_struct_0('#skF_5')) | ~v9_lattices('#skF_5') | ~v8_lattices('#skF_5') | ~v6_lattices('#skF_5') | ~r2_hidden(D_68, '#skF_6') | ~m1_subset_1(D_68, u1_struct_0('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_64, c_160])).
% 9.77/3.42  tff(c_162, plain, (~v6_lattices('#skF_5')), inference(splitLeft, [status(thm)], [c_161])).
% 9.77/3.42  tff(c_165, plain, (~v10_lattices('#skF_5') | v2_struct_0('#skF_5') | ~l3_lattices('#skF_5')), inference(resolution, [status(thm)], [c_8, c_162])).
% 9.77/3.42  tff(c_168, plain, (v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_62, c_165])).
% 9.77/3.42  tff(c_170, plain, $false, inference(negUnitSimplification, [status(thm)], [c_64, c_168])).
% 9.77/3.42  tff(c_172, plain, (v6_lattices('#skF_5')), inference(splitRight, [status(thm)], [c_161])).
% 9.77/3.42  tff(c_4, plain, (![A_1]: (v8_lattices(A_1) | ~v10_lattices(A_1) | v2_struct_0(A_1) | ~l3_lattices(A_1))), inference(cnfTransformation, [status(thm)], [f_47])).
% 9.77/3.42  tff(c_2, plain, (![A_1]: (v9_lattices(A_1) | ~v10_lattices(A_1) | v2_struct_0(A_1) | ~l3_lattices(A_1))), inference(cnfTransformation, [status(thm)], [f_47])).
% 9.77/3.42  tff(c_171, plain, (![D_68]: (~v8_lattices('#skF_5') | ~v9_lattices('#skF_5') | r1_lattices('#skF_5', D_68, '#skF_8'(D_68)) | ~m1_subset_1('#skF_8'(D_68), u1_struct_0('#skF_5')) | ~r2_hidden(D_68, '#skF_6') | ~m1_subset_1(D_68, u1_struct_0('#skF_5')))), inference(splitRight, [status(thm)], [c_161])).
% 9.77/3.42  tff(c_192, plain, (~v9_lattices('#skF_5')), inference(splitLeft, [status(thm)], [c_171])).
% 9.77/3.42  tff(c_195, plain, (~v10_lattices('#skF_5') | v2_struct_0('#skF_5') | ~l3_lattices('#skF_5')), inference(resolution, [status(thm)], [c_2, c_192])).
% 9.77/3.42  tff(c_198, plain, (v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_62, c_195])).
% 9.77/3.42  tff(c_200, plain, $false, inference(negUnitSimplification, [status(thm)], [c_64, c_198])).
% 9.77/3.42  tff(c_202, plain, (v9_lattices('#skF_5')), inference(splitRight, [status(thm)], [c_171])).
% 9.77/3.42  tff(c_70, plain, (![D_68]: (m1_subset_1('#skF_8'(D_68), u1_struct_0('#skF_5')) | ~r2_hidden(D_68, '#skF_6') | ~m1_subset_1(D_68, u1_struct_0('#skF_5')))), inference(cnfTransformation, [status(thm)], [f_183])).
% 9.77/3.42  tff(c_173, plain, (![A_127, B_128, C_129]: (r3_lattices(A_127, B_128, C_129) | ~r1_lattices(A_127, B_128, C_129) | ~m1_subset_1(C_129, u1_struct_0(A_127)) | ~m1_subset_1(B_128, u1_struct_0(A_127)) | ~l3_lattices(A_127) | ~v9_lattices(A_127) | ~v8_lattices(A_127) | ~v6_lattices(A_127) | v2_struct_0(A_127))), inference(cnfTransformation, [status(thm)], [f_66])).
% 9.77/3.42  tff(c_181, plain, (![B_128, D_68]: (r3_lattices('#skF_5', B_128, '#skF_8'(D_68)) | ~r1_lattices('#skF_5', B_128, '#skF_8'(D_68)) | ~m1_subset_1(B_128, u1_struct_0('#skF_5')) | ~l3_lattices('#skF_5') | ~v9_lattices('#skF_5') | ~v8_lattices('#skF_5') | ~v6_lattices('#skF_5') | v2_struct_0('#skF_5') | ~r2_hidden(D_68, '#skF_6') | ~m1_subset_1(D_68, u1_struct_0('#skF_5')))), inference(resolution, [status(thm)], [c_70, c_173])).
% 9.77/3.42  tff(c_189, plain, (![B_128, D_68]: (r3_lattices('#skF_5', B_128, '#skF_8'(D_68)) | ~r1_lattices('#skF_5', B_128, '#skF_8'(D_68)) | ~m1_subset_1(B_128, u1_struct_0('#skF_5')) | ~v9_lattices('#skF_5') | ~v8_lattices('#skF_5') | v2_struct_0('#skF_5') | ~r2_hidden(D_68, '#skF_6') | ~m1_subset_1(D_68, u1_struct_0('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_172, c_58, c_181])).
% 9.77/3.42  tff(c_190, plain, (![B_128, D_68]: (r3_lattices('#skF_5', B_128, '#skF_8'(D_68)) | ~r1_lattices('#skF_5', B_128, '#skF_8'(D_68)) | ~m1_subset_1(B_128, u1_struct_0('#skF_5')) | ~v9_lattices('#skF_5') | ~v8_lattices('#skF_5') | ~r2_hidden(D_68, '#skF_6') | ~m1_subset_1(D_68, u1_struct_0('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_64, c_189])).
% 9.77/3.42  tff(c_204, plain, (![B_128, D_68]: (r3_lattices('#skF_5', B_128, '#skF_8'(D_68)) | ~r1_lattices('#skF_5', B_128, '#skF_8'(D_68)) | ~m1_subset_1(B_128, u1_struct_0('#skF_5')) | ~v8_lattices('#skF_5') | ~r2_hidden(D_68, '#skF_6') | ~m1_subset_1(D_68, u1_struct_0('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_202, c_190])).
% 9.77/3.42  tff(c_205, plain, (~v8_lattices('#skF_5')), inference(splitLeft, [status(thm)], [c_204])).
% 9.77/3.42  tff(c_208, plain, (~v10_lattices('#skF_5') | v2_struct_0('#skF_5') | ~l3_lattices('#skF_5')), inference(resolution, [status(thm)], [c_4, c_205])).
% 9.77/3.42  tff(c_211, plain, (v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_62, c_208])).
% 9.77/3.42  tff(c_213, plain, $false, inference(negUnitSimplification, [status(thm)], [c_64, c_211])).
% 9.77/3.42  tff(c_215, plain, (v8_lattices('#skF_5')), inference(splitRight, [status(thm)], [c_204])).
% 9.77/3.42  tff(c_239, plain, (![A_137, B_138, B_139]: (r3_lattices(A_137, B_138, k15_lattice3(A_137, B_139)) | ~r1_lattices(A_137, B_138, k15_lattice3(A_137, B_139)) | ~m1_subset_1(B_138, u1_struct_0(A_137)) | ~v9_lattices(A_137) | ~v8_lattices(A_137) | ~v6_lattices(A_137) | ~l3_lattices(A_137) | v2_struct_0(A_137))), inference(resolution, [status(thm)], [c_38, c_173])).
% 9.77/3.42  tff(c_244, plain, (~r1_lattices('#skF_5', k15_lattice3('#skF_5', '#skF_6'), k15_lattice3('#skF_5', '#skF_7')) | ~m1_subset_1(k15_lattice3('#skF_5', '#skF_6'), u1_struct_0('#skF_5')) | ~v9_lattices('#skF_5') | ~v8_lattices('#skF_5') | ~v6_lattices('#skF_5') | ~l3_lattices('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_239, c_56])).
% 9.77/3.42  tff(c_251, plain, (~r1_lattices('#skF_5', k15_lattice3('#skF_5', '#skF_6'), k15_lattice3('#skF_5', '#skF_7')) | ~m1_subset_1(k15_lattice3('#skF_5', '#skF_6'), u1_struct_0('#skF_5')) | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_172, c_215, c_202, c_244])).
% 9.77/3.42  tff(c_252, plain, (~r1_lattices('#skF_5', k15_lattice3('#skF_5', '#skF_6'), k15_lattice3('#skF_5', '#skF_7')) | ~m1_subset_1(k15_lattice3('#skF_5', '#skF_6'), u1_struct_0('#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_64, c_251])).
% 9.77/3.42  tff(c_253, plain, (~m1_subset_1(k15_lattice3('#skF_5', '#skF_6'), u1_struct_0('#skF_5'))), inference(splitLeft, [status(thm)], [c_252])).
% 9.77/3.42  tff(c_256, plain, (~l3_lattices('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_38, c_253])).
% 9.77/3.42  tff(c_259, plain, (v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_256])).
% 9.77/3.42  tff(c_261, plain, $false, inference(negUnitSimplification, [status(thm)], [c_64, c_259])).
% 9.77/3.42  tff(c_263, plain, (m1_subset_1(k15_lattice3('#skF_5', '#skF_6'), u1_struct_0('#skF_5'))), inference(splitRight, [status(thm)], [c_252])).
% 9.77/3.42  tff(c_291, plain, (![A_149, B_150, D_151]: (r1_lattices(A_149, k15_lattice3(A_149, B_150), D_151) | ~r4_lattice3(A_149, D_151, B_150) | ~m1_subset_1(D_151, u1_struct_0(A_149)) | ~m1_subset_1(k15_lattice3(A_149, B_150), u1_struct_0(A_149)) | ~v4_lattice3(A_149) | ~v10_lattices(A_149) | ~l3_lattices(A_149) | v2_struct_0(A_149))), inference(cnfTransformation, [status(thm)], [f_112])).
% 9.77/3.42  tff(c_293, plain, (![D_151]: (r1_lattices('#skF_5', k15_lattice3('#skF_5', '#skF_6'), D_151) | ~r4_lattice3('#skF_5', D_151, '#skF_6') | ~m1_subset_1(D_151, u1_struct_0('#skF_5')) | ~v4_lattice3('#skF_5') | ~v10_lattices('#skF_5') | ~l3_lattices('#skF_5') | v2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_263, c_291])).
% 9.77/3.42  tff(c_300, plain, (![D_151]: (r1_lattices('#skF_5', k15_lattice3('#skF_5', '#skF_6'), D_151) | ~r4_lattice3('#skF_5', D_151, '#skF_6') | ~m1_subset_1(D_151, u1_struct_0('#skF_5')) | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_62, c_60, c_293])).
% 9.77/3.42  tff(c_303, plain, (![D_152]: (r1_lattices('#skF_5', k15_lattice3('#skF_5', '#skF_6'), D_152) | ~r4_lattice3('#skF_5', D_152, '#skF_6') | ~m1_subset_1(D_152, u1_struct_0('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_64, c_300])).
% 9.77/3.42  tff(c_262, plain, (~r1_lattices('#skF_5', k15_lattice3('#skF_5', '#skF_6'), k15_lattice3('#skF_5', '#skF_7'))), inference(splitRight, [status(thm)], [c_252])).
% 9.77/3.42  tff(c_311, plain, (~r4_lattice3('#skF_5', k15_lattice3('#skF_5', '#skF_7'), '#skF_6') | ~m1_subset_1(k15_lattice3('#skF_5', '#skF_7'), u1_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_303, c_262])).
% 9.77/3.42  tff(c_316, plain, (~m1_subset_1(k15_lattice3('#skF_5', '#skF_7'), u1_struct_0('#skF_5'))), inference(splitLeft, [status(thm)], [c_311])).
% 9.77/3.42  tff(c_319, plain, (~l3_lattices('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_38, c_316])).
% 9.77/3.42  tff(c_322, plain, (v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_319])).
% 9.77/3.42  tff(c_324, plain, $false, inference(negUnitSimplification, [status(thm)], [c_64, c_322])).
% 9.77/3.42  tff(c_325, plain, (~r4_lattice3('#skF_5', k15_lattice3('#skF_5', '#skF_7'), '#skF_6')), inference(splitRight, [status(thm)], [c_311])).
% 9.77/3.42  tff(c_326, plain, (m1_subset_1(k15_lattice3('#skF_5', '#skF_7'), u1_struct_0('#skF_5'))), inference(splitRight, [status(thm)], [c_311])).
% 9.77/3.42  tff(c_24, plain, (![A_5, B_17, C_23]: (r2_hidden('#skF_1'(A_5, B_17, C_23), C_23) | r4_lattice3(A_5, B_17, C_23) | ~m1_subset_1(B_17, u1_struct_0(A_5)) | ~l3_lattices(A_5) | v2_struct_0(A_5))), inference(cnfTransformation, [status(thm)], [f_84])).
% 9.77/3.42  tff(c_26, plain, (![A_5, B_17, C_23]: (m1_subset_1('#skF_1'(A_5, B_17, C_23), u1_struct_0(A_5)) | r4_lattice3(A_5, B_17, C_23) | ~m1_subset_1(B_17, u1_struct_0(A_5)) | ~l3_lattices(A_5) | v2_struct_0(A_5))), inference(cnfTransformation, [status(thm)], [f_84])).
% 9.77/3.42  tff(c_66, plain, (![D_68]: (r2_hidden('#skF_8'(D_68), '#skF_7') | ~r2_hidden(D_68, '#skF_6') | ~m1_subset_1(D_68, u1_struct_0('#skF_5')))), inference(cnfTransformation, [status(thm)], [f_183])).
% 9.77/3.42  tff(c_380, plain, (![D_157, B_158, C_159, E_160]: (r2_hidden(D_157, a_2_5_lattice3(B_158, C_159)) | ~r2_hidden(E_160, C_159) | ~r3_lattices(B_158, D_157, E_160) | ~m1_subset_1(E_160, u1_struct_0(B_158)) | ~m1_subset_1(D_157, u1_struct_0(B_158)) | ~l3_lattices(B_158) | ~v4_lattice3(B_158) | ~v10_lattices(B_158) | v2_struct_0(B_158))), inference(cnfTransformation, [status(thm)], [f_142])).
% 9.77/3.42  tff(c_462, plain, (![D_175, B_176, D_177]: (r2_hidden(D_175, a_2_5_lattice3(B_176, '#skF_7')) | ~r3_lattices(B_176, D_175, '#skF_8'(D_177)) | ~m1_subset_1('#skF_8'(D_177), u1_struct_0(B_176)) | ~m1_subset_1(D_175, u1_struct_0(B_176)) | ~l3_lattices(B_176) | ~v4_lattice3(B_176) | ~v10_lattices(B_176) | v2_struct_0(B_176) | ~r2_hidden(D_177, '#skF_6') | ~m1_subset_1(D_177, u1_struct_0('#skF_5')))), inference(resolution, [status(thm)], [c_66, c_380])).
% 9.77/3.42  tff(c_466, plain, (![D_68]: (r2_hidden(D_68, a_2_5_lattice3('#skF_5', '#skF_7')) | ~m1_subset_1('#skF_8'(D_68), u1_struct_0('#skF_5')) | ~l3_lattices('#skF_5') | ~v4_lattice3('#skF_5') | ~v10_lattices('#skF_5') | v2_struct_0('#skF_5') | ~r2_hidden(D_68, '#skF_6') | ~m1_subset_1(D_68, u1_struct_0('#skF_5')))), inference(resolution, [status(thm)], [c_68, c_462])).
% 9.77/3.42  tff(c_473, plain, (![D_68]: (r2_hidden(D_68, a_2_5_lattice3('#skF_5', '#skF_7')) | ~m1_subset_1('#skF_8'(D_68), u1_struct_0('#skF_5')) | v2_struct_0('#skF_5') | ~r2_hidden(D_68, '#skF_6') | ~m1_subset_1(D_68, u1_struct_0('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_58, c_466])).
% 9.77/3.42  tff(c_475, plain, (![D_178]: (r2_hidden(D_178, a_2_5_lattice3('#skF_5', '#skF_7')) | ~m1_subset_1('#skF_8'(D_178), u1_struct_0('#skF_5')) | ~r2_hidden(D_178, '#skF_6') | ~m1_subset_1(D_178, u1_struct_0('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_64, c_473])).
% 9.77/3.42  tff(c_479, plain, (![D_68]: (r2_hidden(D_68, a_2_5_lattice3('#skF_5', '#skF_7')) | ~r2_hidden(D_68, '#skF_6') | ~m1_subset_1(D_68, u1_struct_0('#skF_5')))), inference(resolution, [status(thm)], [c_70, c_475])).
% 9.77/3.42  tff(c_480, plain, (![D_179]: (r2_hidden(D_179, a_2_5_lattice3('#skF_5', '#skF_7')) | ~r2_hidden(D_179, '#skF_6') | ~m1_subset_1(D_179, u1_struct_0('#skF_5')))), inference(resolution, [status(thm)], [c_70, c_475])).
% 9.77/3.42  tff(c_48, plain, (![A_41, B_42, C_43]: ('#skF_3'(A_41, B_42, C_43)=A_41 | ~r2_hidden(A_41, a_2_5_lattice3(B_42, C_43)) | ~l3_lattices(B_42) | ~v4_lattice3(B_42) | ~v10_lattices(B_42) | v2_struct_0(B_42))), inference(cnfTransformation, [status(thm)], [f_142])).
% 9.77/3.42  tff(c_487, plain, (![D_179]: ('#skF_3'(D_179, '#skF_5', '#skF_7')=D_179 | ~l3_lattices('#skF_5') | ~v4_lattice3('#skF_5') | ~v10_lattices('#skF_5') | v2_struct_0('#skF_5') | ~r2_hidden(D_179, '#skF_6') | ~m1_subset_1(D_179, u1_struct_0('#skF_5')))), inference(resolution, [status(thm)], [c_480, c_48])).
% 9.77/3.42  tff(c_492, plain, (![D_179]: ('#skF_3'(D_179, '#skF_5', '#skF_7')=D_179 | v2_struct_0('#skF_5') | ~r2_hidden(D_179, '#skF_6') | ~m1_subset_1(D_179, u1_struct_0('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_58, c_487])).
% 9.77/3.42  tff(c_494, plain, (![D_180]: ('#skF_3'(D_180, '#skF_5', '#skF_7')=D_180 | ~r2_hidden(D_180, '#skF_6') | ~m1_subset_1(D_180, u1_struct_0('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_64, c_492])).
% 9.77/3.42  tff(c_516, plain, (![B_17, C_23]: ('#skF_3'('#skF_1'('#skF_5', B_17, C_23), '#skF_5', '#skF_7')='#skF_1'('#skF_5', B_17, C_23) | ~r2_hidden('#skF_1'('#skF_5', B_17, C_23), '#skF_6') | r4_lattice3('#skF_5', B_17, C_23) | ~m1_subset_1(B_17, u1_struct_0('#skF_5')) | ~l3_lattices('#skF_5') | v2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_26, c_494])).
% 9.77/3.42  tff(c_540, plain, (![B_17, C_23]: ('#skF_3'('#skF_1'('#skF_5', B_17, C_23), '#skF_5', '#skF_7')='#skF_1'('#skF_5', B_17, C_23) | ~r2_hidden('#skF_1'('#skF_5', B_17, C_23), '#skF_6') | r4_lattice3('#skF_5', B_17, C_23) | ~m1_subset_1(B_17, u1_struct_0('#skF_5')) | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_516])).
% 9.77/3.42  tff(c_1274, plain, (![B_236, C_237]: ('#skF_3'('#skF_1'('#skF_5', B_236, C_237), '#skF_5', '#skF_7')='#skF_1'('#skF_5', B_236, C_237) | ~r2_hidden('#skF_1'('#skF_5', B_236, C_237), '#skF_6') | r4_lattice3('#skF_5', B_236, C_237) | ~m1_subset_1(B_236, u1_struct_0('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_64, c_540])).
% 9.77/3.42  tff(c_1278, plain, (![B_17]: ('#skF_3'('#skF_1'('#skF_5', B_17, '#skF_6'), '#skF_5', '#skF_7')='#skF_1'('#skF_5', B_17, '#skF_6') | r4_lattice3('#skF_5', B_17, '#skF_6') | ~m1_subset_1(B_17, u1_struct_0('#skF_5')) | ~l3_lattices('#skF_5') | v2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_24, c_1274])).
% 9.77/3.42  tff(c_1281, plain, (![B_17]: ('#skF_3'('#skF_1'('#skF_5', B_17, '#skF_6'), '#skF_5', '#skF_7')='#skF_1'('#skF_5', B_17, '#skF_6') | r4_lattice3('#skF_5', B_17, '#skF_6') | ~m1_subset_1(B_17, u1_struct_0('#skF_5')) | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_1278])).
% 9.77/3.42  tff(c_1283, plain, (![B_238]: ('#skF_3'('#skF_1'('#skF_5', B_238, '#skF_6'), '#skF_5', '#skF_7')='#skF_1'('#skF_5', B_238, '#skF_6') | r4_lattice3('#skF_5', B_238, '#skF_6') | ~m1_subset_1(B_238, u1_struct_0('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_64, c_1281])).
% 9.77/3.42  tff(c_1307, plain, ('#skF_3'('#skF_1'('#skF_5', k15_lattice3('#skF_5', '#skF_7'), '#skF_6'), '#skF_5', '#skF_7')='#skF_1'('#skF_5', k15_lattice3('#skF_5', '#skF_7'), '#skF_6') | r4_lattice3('#skF_5', k15_lattice3('#skF_5', '#skF_7'), '#skF_6')), inference(resolution, [status(thm)], [c_326, c_1283])).
% 9.77/3.42  tff(c_1343, plain, ('#skF_3'('#skF_1'('#skF_5', k15_lattice3('#skF_5', '#skF_7'), '#skF_6'), '#skF_5', '#skF_7')='#skF_1'('#skF_5', k15_lattice3('#skF_5', '#skF_7'), '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_325, c_1307])).
% 9.77/3.42  tff(c_50, plain, (![A_41, B_42, C_43]: (m1_subset_1('#skF_3'(A_41, B_42, C_43), u1_struct_0(B_42)) | ~r2_hidden(A_41, a_2_5_lattice3(B_42, C_43)) | ~l3_lattices(B_42) | ~v4_lattice3(B_42) | ~v10_lattices(B_42) | v2_struct_0(B_42))), inference(cnfTransformation, [status(thm)], [f_142])).
% 9.77/3.42  tff(c_1382, plain, (m1_subset_1('#skF_1'('#skF_5', k15_lattice3('#skF_5', '#skF_7'), '#skF_6'), u1_struct_0('#skF_5')) | ~r2_hidden('#skF_1'('#skF_5', k15_lattice3('#skF_5', '#skF_7'), '#skF_6'), a_2_5_lattice3('#skF_5', '#skF_7')) | ~l3_lattices('#skF_5') | ~v4_lattice3('#skF_5') | ~v10_lattices('#skF_5') | v2_struct_0('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_1343, c_50])).
% 9.77/3.42  tff(c_1393, plain, (m1_subset_1('#skF_1'('#skF_5', k15_lattice3('#skF_5', '#skF_7'), '#skF_6'), u1_struct_0('#skF_5')) | ~r2_hidden('#skF_1'('#skF_5', k15_lattice3('#skF_5', '#skF_7'), '#skF_6'), a_2_5_lattice3('#skF_5', '#skF_7')) | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_58, c_1382])).
% 9.77/3.42  tff(c_1394, plain, (m1_subset_1('#skF_1'('#skF_5', k15_lattice3('#skF_5', '#skF_7'), '#skF_6'), u1_struct_0('#skF_5')) | ~r2_hidden('#skF_1'('#skF_5', k15_lattice3('#skF_5', '#skF_7'), '#skF_6'), a_2_5_lattice3('#skF_5', '#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_64, c_1393])).
% 9.77/3.42  tff(c_1396, plain, (~r2_hidden('#skF_1'('#skF_5', k15_lattice3('#skF_5', '#skF_7'), '#skF_6'), a_2_5_lattice3('#skF_5', '#skF_7'))), inference(splitLeft, [status(thm)], [c_1394])).
% 9.77/3.42  tff(c_1400, plain, (~r2_hidden('#skF_1'('#skF_5', k15_lattice3('#skF_5', '#skF_7'), '#skF_6'), '#skF_6') | ~m1_subset_1('#skF_1'('#skF_5', k15_lattice3('#skF_5', '#skF_7'), '#skF_6'), u1_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_479, c_1396])).
% 9.77/3.42  tff(c_1451, plain, (~m1_subset_1('#skF_1'('#skF_5', k15_lattice3('#skF_5', '#skF_7'), '#skF_6'), u1_struct_0('#skF_5'))), inference(splitLeft, [status(thm)], [c_1400])).
% 9.77/3.42  tff(c_1454, plain, (r4_lattice3('#skF_5', k15_lattice3('#skF_5', '#skF_7'), '#skF_6') | ~m1_subset_1(k15_lattice3('#skF_5', '#skF_7'), u1_struct_0('#skF_5')) | ~l3_lattices('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_26, c_1451])).
% 9.77/3.42  tff(c_1457, plain, (r4_lattice3('#skF_5', k15_lattice3('#skF_5', '#skF_7'), '#skF_6') | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_326, c_1454])).
% 9.77/3.42  tff(c_1459, plain, $false, inference(negUnitSimplification, [status(thm)], [c_64, c_325, c_1457])).
% 9.77/3.42  tff(c_1460, plain, (~r2_hidden('#skF_1'('#skF_5', k15_lattice3('#skF_5', '#skF_7'), '#skF_6'), '#skF_6')), inference(splitRight, [status(thm)], [c_1400])).
% 9.77/3.42  tff(c_1464, plain, (r4_lattice3('#skF_5', k15_lattice3('#skF_5', '#skF_7'), '#skF_6') | ~m1_subset_1(k15_lattice3('#skF_5', '#skF_7'), u1_struct_0('#skF_5')) | ~l3_lattices('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_24, c_1460])).
% 9.77/3.42  tff(c_1467, plain, (r4_lattice3('#skF_5', k15_lattice3('#skF_5', '#skF_7'), '#skF_6') | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_326, c_1464])).
% 9.77/3.42  tff(c_1469, plain, $false, inference(negUnitSimplification, [status(thm)], [c_64, c_325, c_1467])).
% 9.77/3.42  tff(c_1470, plain, (m1_subset_1('#skF_1'('#skF_5', k15_lattice3('#skF_5', '#skF_7'), '#skF_6'), u1_struct_0('#skF_5'))), inference(splitRight, [status(thm)], [c_1394])).
% 9.77/3.42  tff(c_1333, plain, (![B_40]: ('#skF_3'('#skF_1'('#skF_5', k15_lattice3('#skF_5', B_40), '#skF_6'), '#skF_5', '#skF_7')='#skF_1'('#skF_5', k15_lattice3('#skF_5', B_40), '#skF_6') | r4_lattice3('#skF_5', k15_lattice3('#skF_5', B_40), '#skF_6') | ~l3_lattices('#skF_5') | v2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_38, c_1283])).
% 9.77/3.42  tff(c_1364, plain, (![B_40]: ('#skF_3'('#skF_1'('#skF_5', k15_lattice3('#skF_5', B_40), '#skF_6'), '#skF_5', '#skF_7')='#skF_1'('#skF_5', k15_lattice3('#skF_5', B_40), '#skF_6') | r4_lattice3('#skF_5', k15_lattice3('#skF_5', B_40), '#skF_6') | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_1333])).
% 9.77/3.42  tff(c_1532, plain, (![B_250]: ('#skF_3'('#skF_1'('#skF_5', k15_lattice3('#skF_5', B_250), '#skF_6'), '#skF_5', '#skF_7')='#skF_1'('#skF_5', k15_lattice3('#skF_5', B_250), '#skF_6') | r4_lattice3('#skF_5', k15_lattice3('#skF_5', B_250), '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_64, c_1364])).
% 9.77/3.42  tff(c_1563, plain, (![B_56]: ('#skF_1'('#skF_5', k15_lattice3('#skF_5', a_2_5_lattice3('#skF_5', B_56)), '#skF_6')='#skF_3'('#skF_1'('#skF_5', k15_lattice3('#skF_5', B_56), '#skF_6'), '#skF_5', '#skF_7') | r4_lattice3('#skF_5', k15_lattice3('#skF_5', a_2_5_lattice3('#skF_5', B_56)), '#skF_6') | ~l3_lattices('#skF_5') | ~v4_lattice3('#skF_5') | ~v10_lattices('#skF_5') | v2_struct_0('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_52, c_1532])).
% 9.77/3.42  tff(c_1580, plain, (![B_56]: ('#skF_1'('#skF_5', k15_lattice3('#skF_5', a_2_5_lattice3('#skF_5', B_56)), '#skF_6')='#skF_3'('#skF_1'('#skF_5', k15_lattice3('#skF_5', B_56), '#skF_6'), '#skF_5', '#skF_7') | r4_lattice3('#skF_5', k15_lattice3('#skF_5', a_2_5_lattice3('#skF_5', B_56)), '#skF_6') | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_58, c_1563])).
% 9.77/3.42  tff(c_1581, plain, (![B_56]: ('#skF_1'('#skF_5', k15_lattice3('#skF_5', a_2_5_lattice3('#skF_5', B_56)), '#skF_6')='#skF_3'('#skF_1'('#skF_5', k15_lattice3('#skF_5', B_56), '#skF_6'), '#skF_5', '#skF_7') | r4_lattice3('#skF_5', k15_lattice3('#skF_5', a_2_5_lattice3('#skF_5', B_56)), '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_64, c_1580])).
% 9.77/3.42  tff(c_301, plain, (![D_151]: (r1_lattices('#skF_5', k15_lattice3('#skF_5', '#skF_6'), D_151) | ~r4_lattice3('#skF_5', D_151, '#skF_6') | ~m1_subset_1(D_151, u1_struct_0('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_64, c_300])).
% 9.77/3.42  tff(c_3673, plain, (![A_367, B_368, B_369]: (r3_lattices(A_367, B_368, k15_lattice3(A_367, B_369)) | ~r1_lattices(A_367, B_368, k15_lattice3(A_367, a_2_5_lattice3(A_367, B_369))) | ~m1_subset_1(B_368, u1_struct_0(A_367)) | ~v9_lattices(A_367) | ~v8_lattices(A_367) | ~v6_lattices(A_367) | ~l3_lattices(A_367) | v2_struct_0(A_367) | ~l3_lattices(A_367) | ~v4_lattice3(A_367) | ~v10_lattices(A_367) | v2_struct_0(A_367))), inference(superposition, [status(thm), theory('equality')], [c_52, c_239])).
% 9.77/3.42  tff(c_3795, plain, (![B_369]: (r3_lattices('#skF_5', k15_lattice3('#skF_5', '#skF_6'), k15_lattice3('#skF_5', B_369)) | ~m1_subset_1(k15_lattice3('#skF_5', '#skF_6'), u1_struct_0('#skF_5')) | ~v9_lattices('#skF_5') | ~v8_lattices('#skF_5') | ~v6_lattices('#skF_5') | ~l3_lattices('#skF_5') | ~v4_lattice3('#skF_5') | ~v10_lattices('#skF_5') | v2_struct_0('#skF_5') | ~r4_lattice3('#skF_5', k15_lattice3('#skF_5', a_2_5_lattice3('#skF_5', B_369)), '#skF_6') | ~m1_subset_1(k15_lattice3('#skF_5', a_2_5_lattice3('#skF_5', B_369)), u1_struct_0('#skF_5')))), inference(resolution, [status(thm)], [c_301, c_3673])).
% 9.77/3.42  tff(c_3917, plain, (![B_369]: (r3_lattices('#skF_5', k15_lattice3('#skF_5', '#skF_6'), k15_lattice3('#skF_5', B_369)) | v2_struct_0('#skF_5') | ~r4_lattice3('#skF_5', k15_lattice3('#skF_5', a_2_5_lattice3('#skF_5', B_369)), '#skF_6') | ~m1_subset_1(k15_lattice3('#skF_5', a_2_5_lattice3('#skF_5', B_369)), u1_struct_0('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_58, c_172, c_215, c_202, c_263, c_3795])).
% 9.77/3.42  tff(c_3923, plain, (![B_370]: (r3_lattices('#skF_5', k15_lattice3('#skF_5', '#skF_6'), k15_lattice3('#skF_5', B_370)) | ~r4_lattice3('#skF_5', k15_lattice3('#skF_5', a_2_5_lattice3('#skF_5', B_370)), '#skF_6') | ~m1_subset_1(k15_lattice3('#skF_5', a_2_5_lattice3('#skF_5', B_370)), u1_struct_0('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_64, c_3917])).
% 9.77/3.42  tff(c_3945, plain, (![B_370]: (r3_lattices('#skF_5', k15_lattice3('#skF_5', '#skF_6'), k15_lattice3('#skF_5', B_370)) | ~r4_lattice3('#skF_5', k15_lattice3('#skF_5', a_2_5_lattice3('#skF_5', B_370)), '#skF_6') | ~l3_lattices('#skF_5') | v2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_38, c_3923])).
% 9.77/3.42  tff(c_3955, plain, (![B_370]: (r3_lattices('#skF_5', k15_lattice3('#skF_5', '#skF_6'), k15_lattice3('#skF_5', B_370)) | ~r4_lattice3('#skF_5', k15_lattice3('#skF_5', a_2_5_lattice3('#skF_5', B_370)), '#skF_6') | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_3945])).
% 9.77/3.42  tff(c_3957, plain, (![B_371]: (r3_lattices('#skF_5', k15_lattice3('#skF_5', '#skF_6'), k15_lattice3('#skF_5', B_371)) | ~r4_lattice3('#skF_5', k15_lattice3('#skF_5', a_2_5_lattice3('#skF_5', B_371)), '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_64, c_3955])).
% 9.77/3.42  tff(c_4089, plain, (![B_381]: (r3_lattices('#skF_5', k15_lattice3('#skF_5', '#skF_6'), k15_lattice3('#skF_5', B_381)) | '#skF_1'('#skF_5', k15_lattice3('#skF_5', a_2_5_lattice3('#skF_5', B_381)), '#skF_6')='#skF_3'('#skF_1'('#skF_5', k15_lattice3('#skF_5', B_381), '#skF_6'), '#skF_5', '#skF_7'))), inference(resolution, [status(thm)], [c_1581, c_3957])).
% 9.77/3.42  tff(c_4094, plain, ('#skF_1'('#skF_5', k15_lattice3('#skF_5', a_2_5_lattice3('#skF_5', '#skF_7')), '#skF_6')='#skF_3'('#skF_1'('#skF_5', k15_lattice3('#skF_5', '#skF_7'), '#skF_6'), '#skF_5', '#skF_7')), inference(resolution, [status(thm)], [c_4089, c_56])).
% 9.77/3.42  tff(c_4107, plain, ('#skF_1'('#skF_5', k15_lattice3('#skF_5', a_2_5_lattice3('#skF_5', '#skF_7')), '#skF_6')='#skF_1'('#skF_5', k15_lattice3('#skF_5', '#skF_7'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_1343, c_4094])).
% 9.77/3.42  tff(c_4142, plain, (r2_hidden('#skF_1'('#skF_5', k15_lattice3('#skF_5', '#skF_7'), '#skF_6'), '#skF_6') | r4_lattice3('#skF_5', k15_lattice3('#skF_5', a_2_5_lattice3('#skF_5', '#skF_7')), '#skF_6') | ~m1_subset_1(k15_lattice3('#skF_5', a_2_5_lattice3('#skF_5', '#skF_7')), u1_struct_0('#skF_5')) | ~l3_lattices('#skF_5') | v2_struct_0('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_4107, c_24])).
% 9.77/3.42  tff(c_4176, plain, (r2_hidden('#skF_1'('#skF_5', k15_lattice3('#skF_5', '#skF_7'), '#skF_6'), '#skF_6') | r4_lattice3('#skF_5', k15_lattice3('#skF_5', a_2_5_lattice3('#skF_5', '#skF_7')), '#skF_6') | ~m1_subset_1(k15_lattice3('#skF_5', a_2_5_lattice3('#skF_5', '#skF_7')), u1_struct_0('#skF_5')) | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_4142])).
% 9.77/3.42  tff(c_4177, plain, (r2_hidden('#skF_1'('#skF_5', k15_lattice3('#skF_5', '#skF_7'), '#skF_6'), '#skF_6') | r4_lattice3('#skF_5', k15_lattice3('#skF_5', a_2_5_lattice3('#skF_5', '#skF_7')), '#skF_6') | ~m1_subset_1(k15_lattice3('#skF_5', a_2_5_lattice3('#skF_5', '#skF_7')), u1_struct_0('#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_64, c_4176])).
% 9.77/3.42  tff(c_4185, plain, (~m1_subset_1(k15_lattice3('#skF_5', a_2_5_lattice3('#skF_5', '#skF_7')), u1_struct_0('#skF_5'))), inference(splitLeft, [status(thm)], [c_4177])).
% 9.77/3.42  tff(c_4200, plain, (~m1_subset_1(k15_lattice3('#skF_5', '#skF_7'), u1_struct_0('#skF_5')) | ~l3_lattices('#skF_5') | ~v4_lattice3('#skF_5') | ~v10_lattices('#skF_5') | v2_struct_0('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_52, c_4185])).
% 9.77/3.42  tff(c_4209, plain, (v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_58, c_326, c_4200])).
% 9.77/3.42  tff(c_4211, plain, $false, inference(negUnitSimplification, [status(thm)], [c_64, c_4209])).
% 9.77/3.42  tff(c_4212, plain, (r4_lattice3('#skF_5', k15_lattice3('#skF_5', a_2_5_lattice3('#skF_5', '#skF_7')), '#skF_6') | r2_hidden('#skF_1'('#skF_5', k15_lattice3('#skF_5', '#skF_7'), '#skF_6'), '#skF_6')), inference(splitRight, [status(thm)], [c_4177])).
% 9.77/3.42  tff(c_4248, plain, (r2_hidden('#skF_1'('#skF_5', k15_lattice3('#skF_5', '#skF_7'), '#skF_6'), '#skF_6')), inference(splitLeft, [status(thm)], [c_4212])).
% 9.77/3.42  tff(c_20, plain, (![A_5, D_26, B_17, C_23]: (r1_lattices(A_5, D_26, B_17) | ~r2_hidden(D_26, C_23) | ~m1_subset_1(D_26, u1_struct_0(A_5)) | ~r4_lattice3(A_5, B_17, C_23) | ~m1_subset_1(B_17, u1_struct_0(A_5)) | ~l3_lattices(A_5) | v2_struct_0(A_5))), inference(cnfTransformation, [status(thm)], [f_84])).
% 9.77/3.42  tff(c_10049, plain, (![A_581, D_582, B_583]: (r1_lattices(A_581, D_582, B_583) | ~m1_subset_1(D_582, u1_struct_0(A_581)) | ~r4_lattice3(A_581, B_583, a_2_5_lattice3('#skF_5', '#skF_7')) | ~m1_subset_1(B_583, u1_struct_0(A_581)) | ~l3_lattices(A_581) | v2_struct_0(A_581) | ~r2_hidden(D_582, '#skF_6') | ~m1_subset_1(D_582, u1_struct_0('#skF_5')))), inference(resolution, [status(thm)], [c_480, c_20])).
% 9.77/3.42  tff(c_10069, plain, (![B_583]: (r1_lattices('#skF_5', '#skF_1'('#skF_5', k15_lattice3('#skF_5', '#skF_7'), '#skF_6'), B_583) | ~r4_lattice3('#skF_5', B_583, a_2_5_lattice3('#skF_5', '#skF_7')) | ~m1_subset_1(B_583, u1_struct_0('#skF_5')) | ~l3_lattices('#skF_5') | v2_struct_0('#skF_5') | ~r2_hidden('#skF_1'('#skF_5', k15_lattice3('#skF_5', '#skF_7'), '#skF_6'), '#skF_6') | ~m1_subset_1('#skF_1'('#skF_5', k15_lattice3('#skF_5', '#skF_7'), '#skF_6'), u1_struct_0('#skF_5')))), inference(resolution, [status(thm)], [c_1470, c_10049])).
% 9.77/3.42  tff(c_10135, plain, (![B_583]: (r1_lattices('#skF_5', '#skF_1'('#skF_5', k15_lattice3('#skF_5', '#skF_7'), '#skF_6'), B_583) | ~r4_lattice3('#skF_5', B_583, a_2_5_lattice3('#skF_5', '#skF_7')) | ~m1_subset_1(B_583, u1_struct_0('#skF_5')) | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_1470, c_4248, c_58, c_10069])).
% 9.77/3.42  tff(c_10182, plain, (![B_584]: (r1_lattices('#skF_5', '#skF_1'('#skF_5', k15_lattice3('#skF_5', '#skF_7'), '#skF_6'), B_584) | ~r4_lattice3('#skF_5', B_584, a_2_5_lattice3('#skF_5', '#skF_7')) | ~m1_subset_1(B_584, u1_struct_0('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_64, c_10135])).
% 9.77/3.42  tff(c_22, plain, (![A_5, B_17, C_23]: (~r1_lattices(A_5, '#skF_1'(A_5, B_17, C_23), B_17) | r4_lattice3(A_5, B_17, C_23) | ~m1_subset_1(B_17, u1_struct_0(A_5)) | ~l3_lattices(A_5) | v2_struct_0(A_5))), inference(cnfTransformation, [status(thm)], [f_84])).
% 9.77/3.42  tff(c_10258, plain, (r4_lattice3('#skF_5', k15_lattice3('#skF_5', '#skF_7'), '#skF_6') | ~l3_lattices('#skF_5') | v2_struct_0('#skF_5') | ~r4_lattice3('#skF_5', k15_lattice3('#skF_5', '#skF_7'), a_2_5_lattice3('#skF_5', '#skF_7')) | ~m1_subset_1(k15_lattice3('#skF_5', '#skF_7'), u1_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_10182, c_22])).
% 9.77/3.42  tff(c_10323, plain, (r4_lattice3('#skF_5', k15_lattice3('#skF_5', '#skF_7'), '#skF_6') | v2_struct_0('#skF_5') | ~r4_lattice3('#skF_5', k15_lattice3('#skF_5', '#skF_7'), a_2_5_lattice3('#skF_5', '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_326, c_58, c_10258])).
% 9.77/3.42  tff(c_10324, plain, (~r4_lattice3('#skF_5', k15_lattice3('#skF_5', '#skF_7'), a_2_5_lattice3('#skF_5', '#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_64, c_325, c_10323])).
% 9.77/3.42  tff(c_10327, plain, (~l3_lattices('#skF_5') | ~v4_lattice3('#skF_5') | ~v10_lattices('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_127, c_10324])).
% 9.77/3.42  tff(c_10330, plain, (v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_58, c_10327])).
% 9.77/3.42  tff(c_10332, plain, $false, inference(negUnitSimplification, [status(thm)], [c_64, c_10330])).
% 9.77/3.42  tff(c_10333, plain, (r4_lattice3('#skF_5', k15_lattice3('#skF_5', a_2_5_lattice3('#skF_5', '#skF_7')), '#skF_6')), inference(splitRight, [status(thm)], [c_4212])).
% 9.77/3.42  tff(c_3956, plain, (![B_370]: (r3_lattices('#skF_5', k15_lattice3('#skF_5', '#skF_6'), k15_lattice3('#skF_5', B_370)) | ~r4_lattice3('#skF_5', k15_lattice3('#skF_5', a_2_5_lattice3('#skF_5', B_370)), '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_64, c_3955])).
% 9.77/3.42  tff(c_10337, plain, (r3_lattices('#skF_5', k15_lattice3('#skF_5', '#skF_6'), k15_lattice3('#skF_5', '#skF_7'))), inference(resolution, [status(thm)], [c_10333, c_3956])).
% 9.77/3.42  tff(c_10344, plain, $false, inference(negUnitSimplification, [status(thm)], [c_56, c_10337])).
% 9.77/3.42  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.77/3.42  
% 9.77/3.42  Inference rules
% 9.77/3.42  ----------------------
% 9.77/3.42  #Ref     : 0
% 9.77/3.42  #Sup     : 1863
% 9.77/3.42  #Fact    : 0
% 9.77/3.42  #Define  : 0
% 9.77/3.42  #Split   : 22
% 9.77/3.42  #Chain   : 0
% 9.77/3.42  #Close   : 0
% 9.77/3.42  
% 9.77/3.42  Ordering : KBO
% 9.77/3.42  
% 9.77/3.42  Simplification rules
% 9.77/3.42  ----------------------
% 9.77/3.42  #Subsume      : 541
% 9.77/3.42  #Demod        : 3325
% 9.77/3.42  #Tautology    : 180
% 9.77/3.42  #SimpNegUnit  : 823
% 9.77/3.42  #BackRed      : 0
% 9.77/3.42  
% 9.77/3.42  #Partial instantiations: 0
% 9.77/3.42  #Strategies tried      : 1
% 9.77/3.42  
% 9.77/3.42  Timing (in seconds)
% 9.77/3.42  ----------------------
% 9.77/3.42  Preprocessing        : 0.33
% 9.77/3.43  Parsing              : 0.18
% 9.77/3.43  CNF conversion       : 0.03
% 9.77/3.43  Main loop            : 2.29
% 9.77/3.43  Inferencing          : 0.79
% 9.77/3.43  Reduction            : 0.79
% 9.77/3.43  Demodulation         : 0.55
% 9.77/3.43  BG Simplification    : 0.07
% 9.77/3.43  Subsumption          : 0.51
% 9.77/3.43  Abstraction          : 0.08
% 9.77/3.43  MUC search           : 0.00
% 9.77/3.43  Cooper               : 0.00
% 9.77/3.43  Total                : 2.67
% 9.77/3.43  Index Insertion      : 0.00
% 9.77/3.43  Index Deletion       : 0.00
% 9.77/3.43  Index Matching       : 0.00
% 9.77/3.43  BG Taut test         : 0.00
%------------------------------------------------------------------------------
