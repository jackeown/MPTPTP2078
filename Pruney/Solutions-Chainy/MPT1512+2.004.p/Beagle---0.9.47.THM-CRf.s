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
% DateTime   : Thu Dec  3 10:24:50 EST 2020

% Result     : Theorem 5.51s
% Output     : CNFRefutation 5.51s
% Verified   : 
% Statistics : Number of formulae       :  209 (1079 expanded)
%              Number of leaves         :   43 ( 385 expanded)
%              Depth                    :   26
%              Number of atoms          :  671 (4618 expanded)
%              Number of equality atoms :    3 (  19 expanded)
%              Maximal formula depth    :   17 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r4_lattice3 > r3_lattices > r3_lattice3 > r1_lattices > r2_hidden > r1_tarski > m1_subset_1 > v9_lattices > v8_lattices > v7_lattices > v6_lattices > v5_lattices > v4_lattices > v4_lattice3 > v2_struct_0 > v10_lattices > l3_lattices > k16_lattice3 > k15_lattice3 > a_2_2_lattice3 > #nlpp > u1_struct_0 > #skF_4 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1

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

tff(f_206,negated_conjecture,(
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

tff(f_123,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & l3_lattices(A) )
     => m1_subset_1(k16_lattice3(A,B),u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k16_lattice3)).

tff(f_189,axiom,(
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

tff(f_116,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & l3_lattices(A) )
     => m1_subset_1(k15_lattice3(A,B),u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k15_lattice3)).

tff(f_153,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v10_lattices(A)
        & v4_lattice3(A)
        & l3_lattices(A) )
     => ! [B] : k15_lattice3(A,B) = k16_lattice3(A,a_2_2_lattice3(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_lattice3)).

tff(f_172,axiom,(
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

tff(f_141,axiom,(
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

tff(c_1003,plain,(
    ! [A_367,B_368] :
      ( r2_hidden('#skF_1'(A_367,B_368),A_367)
      | r1_tarski(A_367,B_368) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_1008,plain,(
    ! [A_367] : r1_tarski(A_367,A_367) ),
    inference(resolution,[status(thm)],[c_1003,c_4])).

tff(c_72,plain,(
    ~ v2_struct_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_206])).

tff(c_66,plain,(
    l3_lattices('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_206])).

tff(c_44,plain,(
    ! [A_56,B_57] :
      ( m1_subset_1(k16_lattice3(A_56,B_57),u1_struct_0(A_56))
      | ~ l3_lattices(A_56)
      | v2_struct_0(A_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_70,plain,(
    v10_lattices('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_206])).

tff(c_68,plain,(
    v4_lattice3('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_206])).

tff(c_1193,plain,(
    ! [A_451,B_452,C_453] :
      ( r3_lattices(A_451,B_452,k16_lattice3(A_451,C_453))
      | ~ r3_lattice3(A_451,B_452,C_453)
      | ~ m1_subset_1(B_452,u1_struct_0(A_451))
      | ~ l3_lattices(A_451)
      | ~ v4_lattice3(A_451)
      | ~ v10_lattices(A_451)
      | v2_struct_0(A_451) ) ),
    inference(cnfTransformation,[status(thm)],[f_189])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_81,plain,(
    ! [A_91,B_92] :
      ( ~ r2_hidden('#skF_1'(A_91,B_92),B_92)
      | r1_tarski(A_91,B_92) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_86,plain,(
    ! [A_1] : r1_tarski(A_1,A_1) ),
    inference(resolution,[status(thm)],[c_6,c_81])).

tff(c_42,plain,(
    ! [A_54,B_55] :
      ( m1_subset_1(k15_lattice3(A_54,B_55),u1_struct_0(A_54))
      | ~ l3_lattices(A_54)
      | v2_struct_0(A_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_54,plain,(
    ! [A_64,B_66] :
      ( k16_lattice3(A_64,a_2_2_lattice3(A_64,B_66)) = k15_lattice3(A_64,B_66)
      | ~ l3_lattices(A_64)
      | ~ v4_lattice3(A_64)
      | ~ v10_lattices(A_64)
      | v2_struct_0(A_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_215,plain,(
    ! [A_156,C_157,B_158] :
      ( r3_lattices(A_156,k16_lattice3(A_156,C_157),B_158)
      | ~ r2_hidden(B_158,C_157)
      | ~ m1_subset_1(B_158,u1_struct_0(A_156))
      | ~ l3_lattices(A_156)
      | ~ v4_lattice3(A_156)
      | ~ v10_lattices(A_156)
      | v2_struct_0(A_156) ) ),
    inference(cnfTransformation,[status(thm)],[f_172])).

tff(c_573,plain,(
    ! [A_285,B_286,B_287] :
      ( r3_lattices(A_285,k15_lattice3(A_285,B_286),B_287)
      | ~ r2_hidden(B_287,a_2_2_lattice3(A_285,B_286))
      | ~ m1_subset_1(B_287,u1_struct_0(A_285))
      | ~ l3_lattices(A_285)
      | ~ v4_lattice3(A_285)
      | ~ v10_lattices(A_285)
      | v2_struct_0(A_285)
      | ~ l3_lattices(A_285)
      | ~ v4_lattice3(A_285)
      | ~ v10_lattices(A_285)
      | v2_struct_0(A_285) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_54,c_215])).

tff(c_62,plain,
    ( ~ r3_lattices('#skF_5',k16_lattice3('#skF_5','#skF_7'),k16_lattice3('#skF_5','#skF_6'))
    | ~ r3_lattices('#skF_5',k15_lattice3('#skF_5','#skF_6'),k15_lattice3('#skF_5','#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_206])).

tff(c_77,plain,(
    ~ r3_lattices('#skF_5',k15_lattice3('#skF_5','#skF_6'),k15_lattice3('#skF_5','#skF_7')) ),
    inference(splitLeft,[status(thm)],[c_62])).

tff(c_578,plain,
    ( ~ r2_hidden(k15_lattice3('#skF_5','#skF_7'),a_2_2_lattice3('#skF_5','#skF_6'))
    | ~ m1_subset_1(k15_lattice3('#skF_5','#skF_7'),u1_struct_0('#skF_5'))
    | ~ l3_lattices('#skF_5')
    | ~ v4_lattice3('#skF_5')
    | ~ v10_lattices('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_573,c_77])).

tff(c_582,plain,
    ( ~ r2_hidden(k15_lattice3('#skF_5','#skF_7'),a_2_2_lattice3('#skF_5','#skF_6'))
    | ~ m1_subset_1(k15_lattice3('#skF_5','#skF_7'),u1_struct_0('#skF_5'))
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_66,c_578])).

tff(c_583,plain,
    ( ~ r2_hidden(k15_lattice3('#skF_5','#skF_7'),a_2_2_lattice3('#skF_5','#skF_6'))
    | ~ m1_subset_1(k15_lattice3('#skF_5','#skF_7'),u1_struct_0('#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_582])).

tff(c_584,plain,(
    ~ m1_subset_1(k15_lattice3('#skF_5','#skF_7'),u1_struct_0('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_583])).

tff(c_587,plain,
    ( ~ l3_lattices('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_42,c_584])).

tff(c_590,plain,(
    v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_587])).

tff(c_592,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_590])).

tff(c_594,plain,(
    m1_subset_1(k15_lattice3('#skF_5','#skF_7'),u1_struct_0('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_583])).

tff(c_40,plain,(
    ! [A_32,B_44,C_50] :
      ( m1_subset_1('#skF_3'(A_32,B_44,C_50),u1_struct_0(A_32))
      | r4_lattice3(A_32,B_44,C_50)
      | ~ m1_subset_1(B_44,u1_struct_0(A_32))
      | ~ l3_lattices(A_32)
      | v2_struct_0(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_64,plain,(
    r1_tarski('#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_206])).

tff(c_199,plain,(
    ! [A_131,B_132,C_133] :
      ( r2_hidden('#skF_3'(A_131,B_132,C_133),C_133)
      | r4_lattice3(A_131,B_132,C_133)
      | ~ m1_subset_1(B_132,u1_struct_0(A_131))
      | ~ l3_lattices(A_131)
      | v2_struct_0(A_131) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_281,plain,(
    ! [A_175,B_176,C_177,B_178] :
      ( r2_hidden('#skF_3'(A_175,B_176,C_177),B_178)
      | ~ r1_tarski(C_177,B_178)
      | r4_lattice3(A_175,B_176,C_177)
      | ~ m1_subset_1(B_176,u1_struct_0(A_175))
      | ~ l3_lattices(A_175)
      | v2_struct_0(A_175) ) ),
    inference(resolution,[status(thm)],[c_199,c_2])).

tff(c_342,plain,(
    ! [B_194,A_192,C_191,B_193,B_195] :
      ( r2_hidden('#skF_3'(A_192,B_193,C_191),B_195)
      | ~ r1_tarski(B_194,B_195)
      | ~ r1_tarski(C_191,B_194)
      | r4_lattice3(A_192,B_193,C_191)
      | ~ m1_subset_1(B_193,u1_struct_0(A_192))
      | ~ l3_lattices(A_192)
      | v2_struct_0(A_192) ) ),
    inference(resolution,[status(thm)],[c_281,c_2])).

tff(c_362,plain,(
    ! [A_199,B_200,C_201] :
      ( r2_hidden('#skF_3'(A_199,B_200,C_201),'#skF_7')
      | ~ r1_tarski(C_201,'#skF_6')
      | r4_lattice3(A_199,B_200,C_201)
      | ~ m1_subset_1(B_200,u1_struct_0(A_199))
      | ~ l3_lattices(A_199)
      | v2_struct_0(A_199) ) ),
    inference(resolution,[status(thm)],[c_64,c_342])).

tff(c_34,plain,(
    ! [A_32,D_53,B_44,C_50] :
      ( r1_lattices(A_32,D_53,B_44)
      | ~ r2_hidden(D_53,C_50)
      | ~ m1_subset_1(D_53,u1_struct_0(A_32))
      | ~ r4_lattice3(A_32,B_44,C_50)
      | ~ m1_subset_1(B_44,u1_struct_0(A_32))
      | ~ l3_lattices(A_32)
      | v2_struct_0(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_632,plain,(
    ! [C_296,A_293,B_292,A_294,B_295] :
      ( r1_lattices(A_293,'#skF_3'(A_294,B_292,C_296),B_295)
      | ~ m1_subset_1('#skF_3'(A_294,B_292,C_296),u1_struct_0(A_293))
      | ~ r4_lattice3(A_293,B_295,'#skF_7')
      | ~ m1_subset_1(B_295,u1_struct_0(A_293))
      | ~ l3_lattices(A_293)
      | v2_struct_0(A_293)
      | ~ r1_tarski(C_296,'#skF_6')
      | r4_lattice3(A_294,B_292,C_296)
      | ~ m1_subset_1(B_292,u1_struct_0(A_294))
      | ~ l3_lattices(A_294)
      | v2_struct_0(A_294) ) ),
    inference(resolution,[status(thm)],[c_362,c_34])).

tff(c_636,plain,(
    ! [A_297,B_298,C_299,B_300] :
      ( r1_lattices(A_297,'#skF_3'(A_297,B_298,C_299),B_300)
      | ~ r4_lattice3(A_297,B_300,'#skF_7')
      | ~ m1_subset_1(B_300,u1_struct_0(A_297))
      | ~ r1_tarski(C_299,'#skF_6')
      | r4_lattice3(A_297,B_298,C_299)
      | ~ m1_subset_1(B_298,u1_struct_0(A_297))
      | ~ l3_lattices(A_297)
      | v2_struct_0(A_297) ) ),
    inference(resolution,[status(thm)],[c_40,c_632])).

tff(c_36,plain,(
    ! [A_32,B_44,C_50] :
      ( ~ r1_lattices(A_32,'#skF_3'(A_32,B_44,C_50),B_44)
      | r4_lattice3(A_32,B_44,C_50)
      | ~ m1_subset_1(B_44,u1_struct_0(A_32))
      | ~ l3_lattices(A_32)
      | v2_struct_0(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_647,plain,(
    ! [A_301,B_302,C_303] :
      ( ~ r4_lattice3(A_301,B_302,'#skF_7')
      | ~ r1_tarski(C_303,'#skF_6')
      | r4_lattice3(A_301,B_302,C_303)
      | ~ m1_subset_1(B_302,u1_struct_0(A_301))
      | ~ l3_lattices(A_301)
      | v2_struct_0(A_301) ) ),
    inference(resolution,[status(thm)],[c_636,c_36])).

tff(c_649,plain,(
    ! [C_303] :
      ( ~ r4_lattice3('#skF_5',k15_lattice3('#skF_5','#skF_7'),'#skF_7')
      | ~ r1_tarski(C_303,'#skF_6')
      | r4_lattice3('#skF_5',k15_lattice3('#skF_5','#skF_7'),C_303)
      | ~ l3_lattices('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_594,c_647])).

tff(c_664,plain,(
    ! [C_303] :
      ( ~ r4_lattice3('#skF_5',k15_lattice3('#skF_5','#skF_7'),'#skF_7')
      | ~ r1_tarski(C_303,'#skF_6')
      | r4_lattice3('#skF_5',k15_lattice3('#skF_5','#skF_7'),C_303)
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_649])).

tff(c_665,plain,(
    ! [C_303] :
      ( ~ r4_lattice3('#skF_5',k15_lattice3('#skF_5','#skF_7'),'#skF_7')
      | ~ r1_tarski(C_303,'#skF_6')
      | r4_lattice3('#skF_5',k15_lattice3('#skF_5','#skF_7'),C_303) ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_664])).

tff(c_675,plain,(
    ~ r4_lattice3('#skF_5',k15_lattice3('#skF_5','#skF_7'),'#skF_7') ),
    inference(splitLeft,[status(thm)],[c_665])).

tff(c_38,plain,(
    ! [A_32,B_44,C_50] :
      ( r2_hidden('#skF_3'(A_32,B_44,C_50),C_50)
      | r4_lattice3(A_32,B_44,C_50)
      | ~ m1_subset_1(B_44,u1_struct_0(A_32))
      | ~ l3_lattices(A_32)
      | v2_struct_0(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_14,plain,(
    ! [A_6] :
      ( v6_lattices(A_6)
      | ~ v10_lattices(A_6)
      | v2_struct_0(A_6)
      | ~ l3_lattices(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_232,plain,(
    ! [A_162,B_163,C_164] :
      ( r3_lattices(A_162,B_163,k15_lattice3(A_162,C_164))
      | ~ r2_hidden(B_163,C_164)
      | ~ m1_subset_1(B_163,u1_struct_0(A_162))
      | ~ l3_lattices(A_162)
      | ~ v4_lattice3(A_162)
      | ~ v10_lattices(A_162)
      | v2_struct_0(A_162) ) ),
    inference(cnfTransformation,[status(thm)],[f_172])).

tff(c_235,plain,
    ( ~ r2_hidden(k15_lattice3('#skF_5','#skF_6'),'#skF_7')
    | ~ m1_subset_1(k15_lattice3('#skF_5','#skF_6'),u1_struct_0('#skF_5'))
    | ~ l3_lattices('#skF_5')
    | ~ v4_lattice3('#skF_5')
    | ~ v10_lattices('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_232,c_77])).

tff(c_238,plain,
    ( ~ r2_hidden(k15_lattice3('#skF_5','#skF_6'),'#skF_7')
    | ~ m1_subset_1(k15_lattice3('#skF_5','#skF_6'),u1_struct_0('#skF_5'))
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_66,c_235])).

tff(c_239,plain,
    ( ~ r2_hidden(k15_lattice3('#skF_5','#skF_6'),'#skF_7')
    | ~ m1_subset_1(k15_lattice3('#skF_5','#skF_6'),u1_struct_0('#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_238])).

tff(c_240,plain,(
    ~ m1_subset_1(k15_lattice3('#skF_5','#skF_6'),u1_struct_0('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_239])).

tff(c_243,plain,
    ( ~ l3_lattices('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_42,c_240])).

tff(c_246,plain,(
    v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_243])).

tff(c_248,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_246])).

tff(c_250,plain,(
    m1_subset_1(k15_lattice3('#skF_5','#skF_6'),u1_struct_0('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_239])).

tff(c_451,plain,(
    ! [A_233,B_234,C_235] :
      ( r3_lattices(A_233,B_234,C_235)
      | ~ r1_lattices(A_233,B_234,C_235)
      | ~ m1_subset_1(C_235,u1_struct_0(A_233))
      | ~ m1_subset_1(B_234,u1_struct_0(A_233))
      | ~ l3_lattices(A_233)
      | ~ v9_lattices(A_233)
      | ~ v8_lattices(A_233)
      | ~ v6_lattices(A_233)
      | v2_struct_0(A_233) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_453,plain,(
    ! [B_234] :
      ( r3_lattices('#skF_5',B_234,k15_lattice3('#skF_5','#skF_6'))
      | ~ r1_lattices('#skF_5',B_234,k15_lattice3('#skF_5','#skF_6'))
      | ~ m1_subset_1(B_234,u1_struct_0('#skF_5'))
      | ~ l3_lattices('#skF_5')
      | ~ v9_lattices('#skF_5')
      | ~ v8_lattices('#skF_5')
      | ~ v6_lattices('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_250,c_451])).

tff(c_466,plain,(
    ! [B_234] :
      ( r3_lattices('#skF_5',B_234,k15_lattice3('#skF_5','#skF_6'))
      | ~ r1_lattices('#skF_5',B_234,k15_lattice3('#skF_5','#skF_6'))
      | ~ m1_subset_1(B_234,u1_struct_0('#skF_5'))
      | ~ v9_lattices('#skF_5')
      | ~ v8_lattices('#skF_5')
      | ~ v6_lattices('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_453])).

tff(c_467,plain,(
    ! [B_234] :
      ( r3_lattices('#skF_5',B_234,k15_lattice3('#skF_5','#skF_6'))
      | ~ r1_lattices('#skF_5',B_234,k15_lattice3('#skF_5','#skF_6'))
      | ~ m1_subset_1(B_234,u1_struct_0('#skF_5'))
      | ~ v9_lattices('#skF_5')
      | ~ v8_lattices('#skF_5')
      | ~ v6_lattices('#skF_5') ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_466])).

tff(c_473,plain,(
    ~ v6_lattices('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_467])).

tff(c_476,plain,
    ( ~ v10_lattices('#skF_5')
    | v2_struct_0('#skF_5')
    | ~ l3_lattices('#skF_5') ),
    inference(resolution,[status(thm)],[c_14,c_473])).

tff(c_479,plain,(
    v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_70,c_476])).

tff(c_481,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_479])).

tff(c_483,plain,(
    v6_lattices('#skF_5') ),
    inference(splitRight,[status(thm)],[c_467])).

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

tff(c_482,plain,(
    ! [B_234] :
      ( ~ v8_lattices('#skF_5')
      | ~ v9_lattices('#skF_5')
      | r3_lattices('#skF_5',B_234,k15_lattice3('#skF_5','#skF_6'))
      | ~ r1_lattices('#skF_5',B_234,k15_lattice3('#skF_5','#skF_6'))
      | ~ m1_subset_1(B_234,u1_struct_0('#skF_5')) ) ),
    inference(splitRight,[status(thm)],[c_467])).

tff(c_484,plain,(
    ~ v9_lattices('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_482])).

tff(c_487,plain,
    ( ~ v10_lattices('#skF_5')
    | v2_struct_0('#skF_5')
    | ~ l3_lattices('#skF_5') ),
    inference(resolution,[status(thm)],[c_8,c_484])).

tff(c_490,plain,(
    v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_70,c_487])).

tff(c_492,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_490])).

tff(c_493,plain,(
    ! [B_234] :
      ( ~ v8_lattices('#skF_5')
      | r3_lattices('#skF_5',B_234,k15_lattice3('#skF_5','#skF_6'))
      | ~ r1_lattices('#skF_5',B_234,k15_lattice3('#skF_5','#skF_6'))
      | ~ m1_subset_1(B_234,u1_struct_0('#skF_5')) ) ),
    inference(splitRight,[status(thm)],[c_482])).

tff(c_495,plain,(
    ~ v8_lattices('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_493])).

tff(c_498,plain,
    ( ~ v10_lattices('#skF_5')
    | v2_struct_0('#skF_5')
    | ~ l3_lattices('#skF_5') ),
    inference(resolution,[status(thm)],[c_10,c_495])).

tff(c_501,plain,(
    v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_70,c_498])).

tff(c_503,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_501])).

tff(c_505,plain,(
    v8_lattices('#skF_5') ),
    inference(splitRight,[status(thm)],[c_493])).

tff(c_494,plain,(
    v9_lattices('#skF_5') ),
    inference(splitRight,[status(thm)],[c_482])).

tff(c_58,plain,(
    ! [A_67,B_71,C_73] :
      ( r3_lattices(A_67,B_71,k15_lattice3(A_67,C_73))
      | ~ r2_hidden(B_71,C_73)
      | ~ m1_subset_1(B_71,u1_struct_0(A_67))
      | ~ l3_lattices(A_67)
      | ~ v4_lattice3(A_67)
      | ~ v10_lattices(A_67)
      | v2_struct_0(A_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_172])).

tff(c_352,plain,(
    ! [A_196,B_197,C_198] :
      ( r1_lattices(A_196,B_197,C_198)
      | ~ r3_lattices(A_196,B_197,C_198)
      | ~ m1_subset_1(C_198,u1_struct_0(A_196))
      | ~ m1_subset_1(B_197,u1_struct_0(A_196))
      | ~ l3_lattices(A_196)
      | ~ v9_lattices(A_196)
      | ~ v8_lattices(A_196)
      | ~ v6_lattices(A_196)
      | v2_struct_0(A_196) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_727,plain,(
    ! [A_336,B_337,C_338] :
      ( r1_lattices(A_336,B_337,k15_lattice3(A_336,C_338))
      | ~ m1_subset_1(k15_lattice3(A_336,C_338),u1_struct_0(A_336))
      | ~ v9_lattices(A_336)
      | ~ v8_lattices(A_336)
      | ~ v6_lattices(A_336)
      | ~ r2_hidden(B_337,C_338)
      | ~ m1_subset_1(B_337,u1_struct_0(A_336))
      | ~ l3_lattices(A_336)
      | ~ v4_lattice3(A_336)
      | ~ v10_lattices(A_336)
      | v2_struct_0(A_336) ) ),
    inference(resolution,[status(thm)],[c_58,c_352])).

tff(c_729,plain,(
    ! [B_337] :
      ( r1_lattices('#skF_5',B_337,k15_lattice3('#skF_5','#skF_7'))
      | ~ v9_lattices('#skF_5')
      | ~ v8_lattices('#skF_5')
      | ~ v6_lattices('#skF_5')
      | ~ r2_hidden(B_337,'#skF_7')
      | ~ m1_subset_1(B_337,u1_struct_0('#skF_5'))
      | ~ l3_lattices('#skF_5')
      | ~ v4_lattice3('#skF_5')
      | ~ v10_lattices('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_594,c_727])).

tff(c_736,plain,(
    ! [B_337] :
      ( r1_lattices('#skF_5',B_337,k15_lattice3('#skF_5','#skF_7'))
      | ~ r2_hidden(B_337,'#skF_7')
      | ~ m1_subset_1(B_337,u1_struct_0('#skF_5'))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_66,c_483,c_505,c_494,c_729])).

tff(c_752,plain,(
    ! [B_340] :
      ( r1_lattices('#skF_5',B_340,k15_lattice3('#skF_5','#skF_7'))
      | ~ r2_hidden(B_340,'#skF_7')
      | ~ m1_subset_1(B_340,u1_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_736])).

tff(c_759,plain,(
    ! [C_50] :
      ( r4_lattice3('#skF_5',k15_lattice3('#skF_5','#skF_7'),C_50)
      | ~ m1_subset_1(k15_lattice3('#skF_5','#skF_7'),u1_struct_0('#skF_5'))
      | ~ l3_lattices('#skF_5')
      | v2_struct_0('#skF_5')
      | ~ r2_hidden('#skF_3'('#skF_5',k15_lattice3('#skF_5','#skF_7'),C_50),'#skF_7')
      | ~ m1_subset_1('#skF_3'('#skF_5',k15_lattice3('#skF_5','#skF_7'),C_50),u1_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_752,c_36])).

tff(c_765,plain,(
    ! [C_50] :
      ( r4_lattice3('#skF_5',k15_lattice3('#skF_5','#skF_7'),C_50)
      | v2_struct_0('#skF_5')
      | ~ r2_hidden('#skF_3'('#skF_5',k15_lattice3('#skF_5','#skF_7'),C_50),'#skF_7')
      | ~ m1_subset_1('#skF_3'('#skF_5',k15_lattice3('#skF_5','#skF_7'),C_50),u1_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_594,c_759])).

tff(c_927,plain,(
    ! [C_358] :
      ( r4_lattice3('#skF_5',k15_lattice3('#skF_5','#skF_7'),C_358)
      | ~ r2_hidden('#skF_3'('#skF_5',k15_lattice3('#skF_5','#skF_7'),C_358),'#skF_7')
      | ~ m1_subset_1('#skF_3'('#skF_5',k15_lattice3('#skF_5','#skF_7'),C_358),u1_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_765])).

tff(c_931,plain,(
    ! [C_50] :
      ( ~ r2_hidden('#skF_3'('#skF_5',k15_lattice3('#skF_5','#skF_7'),C_50),'#skF_7')
      | r4_lattice3('#skF_5',k15_lattice3('#skF_5','#skF_7'),C_50)
      | ~ m1_subset_1(k15_lattice3('#skF_5','#skF_7'),u1_struct_0('#skF_5'))
      | ~ l3_lattices('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_40,c_927])).

tff(c_934,plain,(
    ! [C_50] :
      ( ~ r2_hidden('#skF_3'('#skF_5',k15_lattice3('#skF_5','#skF_7'),C_50),'#skF_7')
      | r4_lattice3('#skF_5',k15_lattice3('#skF_5','#skF_7'),C_50)
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_594,c_931])).

tff(c_940,plain,(
    ! [C_363] :
      ( ~ r2_hidden('#skF_3'('#skF_5',k15_lattice3('#skF_5','#skF_7'),C_363),'#skF_7')
      | r4_lattice3('#skF_5',k15_lattice3('#skF_5','#skF_7'),C_363) ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_934])).

tff(c_956,plain,
    ( r4_lattice3('#skF_5',k15_lattice3('#skF_5','#skF_7'),'#skF_7')
    | ~ m1_subset_1(k15_lattice3('#skF_5','#skF_7'),u1_struct_0('#skF_5'))
    | ~ l3_lattices('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_38,c_940])).

tff(c_971,plain,
    ( r4_lattice3('#skF_5',k15_lattice3('#skF_5','#skF_7'),'#skF_7')
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_594,c_956])).

tff(c_973,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_675,c_971])).

tff(c_988,plain,(
    ! [C_364] :
      ( ~ r1_tarski(C_364,'#skF_6')
      | r4_lattice3('#skF_5',k15_lattice3('#skF_5','#skF_7'),C_364) ) ),
    inference(splitRight,[status(thm)],[c_665])).

tff(c_46,plain,(
    ! [D_63,B_59,C_60] :
      ( r2_hidden(D_63,a_2_2_lattice3(B_59,C_60))
      | ~ r4_lattice3(B_59,D_63,C_60)
      | ~ m1_subset_1(D_63,u1_struct_0(B_59))
      | ~ l3_lattices(B_59)
      | ~ v4_lattice3(B_59)
      | ~ v10_lattices(B_59)
      | v2_struct_0(B_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_593,plain,(
    ~ r2_hidden(k15_lattice3('#skF_5','#skF_7'),a_2_2_lattice3('#skF_5','#skF_6')) ),
    inference(splitRight,[status(thm)],[c_583])).

tff(c_603,plain,
    ( ~ r4_lattice3('#skF_5',k15_lattice3('#skF_5','#skF_7'),'#skF_6')
    | ~ m1_subset_1(k15_lattice3('#skF_5','#skF_7'),u1_struct_0('#skF_5'))
    | ~ l3_lattices('#skF_5')
    | ~ v4_lattice3('#skF_5')
    | ~ v10_lattices('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_46,c_593])).

tff(c_606,plain,
    ( ~ r4_lattice3('#skF_5',k15_lattice3('#skF_5','#skF_7'),'#skF_6')
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_66,c_594,c_603])).

tff(c_607,plain,(
    ~ r4_lattice3('#skF_5',k15_lattice3('#skF_5','#skF_7'),'#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_606])).

tff(c_991,plain,(
    ~ r1_tarski('#skF_6','#skF_6') ),
    inference(resolution,[status(thm)],[c_988,c_607])).

tff(c_999,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_991])).

tff(c_1000,plain,(
    ~ r3_lattices('#skF_5',k16_lattice3('#skF_5','#skF_7'),k16_lattice3('#skF_5','#skF_6')) ),
    inference(splitRight,[status(thm)],[c_62])).

tff(c_1196,plain,
    ( ~ r3_lattice3('#skF_5',k16_lattice3('#skF_5','#skF_7'),'#skF_6')
    | ~ m1_subset_1(k16_lattice3('#skF_5','#skF_7'),u1_struct_0('#skF_5'))
    | ~ l3_lattices('#skF_5')
    | ~ v4_lattice3('#skF_5')
    | ~ v10_lattices('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_1193,c_1000])).

tff(c_1202,plain,
    ( ~ r3_lattice3('#skF_5',k16_lattice3('#skF_5','#skF_7'),'#skF_6')
    | ~ m1_subset_1(k16_lattice3('#skF_5','#skF_7'),u1_struct_0('#skF_5'))
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_66,c_1196])).

tff(c_1203,plain,
    ( ~ r3_lattice3('#skF_5',k16_lattice3('#skF_5','#skF_7'),'#skF_6')
    | ~ m1_subset_1(k16_lattice3('#skF_5','#skF_7'),u1_struct_0('#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_1202])).

tff(c_1204,plain,(
    ~ m1_subset_1(k16_lattice3('#skF_5','#skF_7'),u1_struct_0('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_1203])).

tff(c_1207,plain,
    ( ~ l3_lattices('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_44,c_1204])).

tff(c_1210,plain,(
    v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_1207])).

tff(c_1212,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_1210])).

tff(c_1214,plain,(
    m1_subset_1(k16_lattice3('#skF_5','#skF_7'),u1_struct_0('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_1203])).

tff(c_1123,plain,(
    ! [A_409,B_410,C_411] :
      ( r2_hidden('#skF_2'(A_409,B_410,C_411),C_411)
      | r3_lattice3(A_409,B_410,C_411)
      | ~ m1_subset_1(B_410,u1_struct_0(A_409))
      | ~ l3_lattices(A_409)
      | v2_struct_0(A_409) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_1175,plain,(
    ! [A_443,B_444,C_445,B_446] :
      ( r2_hidden('#skF_2'(A_443,B_444,C_445),B_446)
      | ~ r1_tarski(C_445,B_446)
      | r3_lattice3(A_443,B_444,C_445)
      | ~ m1_subset_1(B_444,u1_struct_0(A_443))
      | ~ l3_lattices(A_443)
      | v2_struct_0(A_443) ) ),
    inference(resolution,[status(thm)],[c_1123,c_2])).

tff(c_1304,plain,(
    ! [A_481,B_480,C_479,B_478,B_477] :
      ( r2_hidden('#skF_2'(A_481,B_478,C_479),B_480)
      | ~ r1_tarski(B_477,B_480)
      | ~ r1_tarski(C_479,B_477)
      | r3_lattice3(A_481,B_478,C_479)
      | ~ m1_subset_1(B_478,u1_struct_0(A_481))
      | ~ l3_lattices(A_481)
      | v2_struct_0(A_481) ) ),
    inference(resolution,[status(thm)],[c_1175,c_2])).

tff(c_1314,plain,(
    ! [A_482,B_483,C_484] :
      ( r2_hidden('#skF_2'(A_482,B_483,C_484),'#skF_7')
      | ~ r1_tarski(C_484,'#skF_6')
      | r3_lattice3(A_482,B_483,C_484)
      | ~ m1_subset_1(B_483,u1_struct_0(A_482))
      | ~ l3_lattices(A_482)
      | v2_struct_0(A_482) ) ),
    inference(resolution,[status(thm)],[c_64,c_1304])).

tff(c_1323,plain,(
    ! [A_482,B_483,C_484,B_2] :
      ( r2_hidden('#skF_2'(A_482,B_483,C_484),B_2)
      | ~ r1_tarski('#skF_7',B_2)
      | ~ r1_tarski(C_484,'#skF_6')
      | r3_lattice3(A_482,B_483,C_484)
      | ~ m1_subset_1(B_483,u1_struct_0(A_482))
      | ~ l3_lattices(A_482)
      | v2_struct_0(A_482) ) ),
    inference(resolution,[status(thm)],[c_1314,c_2])).

tff(c_32,plain,(
    ! [A_10,B_22,C_28] :
      ( m1_subset_1('#skF_2'(A_10,B_22,C_28),u1_struct_0(A_10))
      | r3_lattice3(A_10,B_22,C_28)
      | ~ m1_subset_1(B_22,u1_struct_0(A_10))
      | ~ l3_lattices(A_10)
      | v2_struct_0(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_1364,plain,(
    ! [A_497,B_498,C_499] :
      ( r3_lattices(A_497,B_498,C_499)
      | ~ r1_lattices(A_497,B_498,C_499)
      | ~ m1_subset_1(C_499,u1_struct_0(A_497))
      | ~ m1_subset_1(B_498,u1_struct_0(A_497))
      | ~ l3_lattices(A_497)
      | ~ v9_lattices(A_497)
      | ~ v8_lattices(A_497)
      | ~ v6_lattices(A_497)
      | v2_struct_0(A_497) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_1366,plain,(
    ! [B_498] :
      ( r3_lattices('#skF_5',B_498,k16_lattice3('#skF_5','#skF_7'))
      | ~ r1_lattices('#skF_5',B_498,k16_lattice3('#skF_5','#skF_7'))
      | ~ m1_subset_1(B_498,u1_struct_0('#skF_5'))
      | ~ l3_lattices('#skF_5')
      | ~ v9_lattices('#skF_5')
      | ~ v8_lattices('#skF_5')
      | ~ v6_lattices('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_1214,c_1364])).

tff(c_1381,plain,(
    ! [B_498] :
      ( r3_lattices('#skF_5',B_498,k16_lattice3('#skF_5','#skF_7'))
      | ~ r1_lattices('#skF_5',B_498,k16_lattice3('#skF_5','#skF_7'))
      | ~ m1_subset_1(B_498,u1_struct_0('#skF_5'))
      | ~ v9_lattices('#skF_5')
      | ~ v8_lattices('#skF_5')
      | ~ v6_lattices('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_1366])).

tff(c_1382,plain,(
    ! [B_498] :
      ( r3_lattices('#skF_5',B_498,k16_lattice3('#skF_5','#skF_7'))
      | ~ r1_lattices('#skF_5',B_498,k16_lattice3('#skF_5','#skF_7'))
      | ~ m1_subset_1(B_498,u1_struct_0('#skF_5'))
      | ~ v9_lattices('#skF_5')
      | ~ v8_lattices('#skF_5')
      | ~ v6_lattices('#skF_5') ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_1381])).

tff(c_1392,plain,(
    ~ v6_lattices('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_1382])).

tff(c_1395,plain,
    ( ~ v10_lattices('#skF_5')
    | v2_struct_0('#skF_5')
    | ~ l3_lattices('#skF_5') ),
    inference(resolution,[status(thm)],[c_14,c_1392])).

tff(c_1398,plain,(
    v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_70,c_1395])).

tff(c_1400,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_1398])).

tff(c_1402,plain,(
    v6_lattices('#skF_5') ),
    inference(splitRight,[status(thm)],[c_1382])).

tff(c_1139,plain,(
    ! [A_434,C_435,B_436] :
      ( r3_lattices(A_434,k16_lattice3(A_434,C_435),B_436)
      | ~ r2_hidden(B_436,C_435)
      | ~ m1_subset_1(B_436,u1_struct_0(A_434))
      | ~ l3_lattices(A_434)
      | ~ v4_lattice3(A_434)
      | ~ v10_lattices(A_434)
      | v2_struct_0(A_434) ) ),
    inference(cnfTransformation,[status(thm)],[f_172])).

tff(c_1142,plain,
    ( ~ r2_hidden(k16_lattice3('#skF_5','#skF_6'),'#skF_7')
    | ~ m1_subset_1(k16_lattice3('#skF_5','#skF_6'),u1_struct_0('#skF_5'))
    | ~ l3_lattices('#skF_5')
    | ~ v4_lattice3('#skF_5')
    | ~ v10_lattices('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_1139,c_1000])).

tff(c_1148,plain,
    ( ~ r2_hidden(k16_lattice3('#skF_5','#skF_6'),'#skF_7')
    | ~ m1_subset_1(k16_lattice3('#skF_5','#skF_6'),u1_struct_0('#skF_5'))
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_66,c_1142])).

tff(c_1149,plain,
    ( ~ r2_hidden(k16_lattice3('#skF_5','#skF_6'),'#skF_7')
    | ~ m1_subset_1(k16_lattice3('#skF_5','#skF_6'),u1_struct_0('#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_1148])).

tff(c_1150,plain,(
    ~ m1_subset_1(k16_lattice3('#skF_5','#skF_6'),u1_struct_0('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_1149])).

tff(c_1153,plain,
    ( ~ l3_lattices('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_44,c_1150])).

tff(c_1156,plain,(
    v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_1153])).

tff(c_1158,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_1156])).

tff(c_1160,plain,(
    m1_subset_1(k16_lattice3('#skF_5','#skF_6'),u1_struct_0('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_1149])).

tff(c_1368,plain,(
    ! [B_498] :
      ( r3_lattices('#skF_5',B_498,k16_lattice3('#skF_5','#skF_6'))
      | ~ r1_lattices('#skF_5',B_498,k16_lattice3('#skF_5','#skF_6'))
      | ~ m1_subset_1(B_498,u1_struct_0('#skF_5'))
      | ~ l3_lattices('#skF_5')
      | ~ v9_lattices('#skF_5')
      | ~ v8_lattices('#skF_5')
      | ~ v6_lattices('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_1160,c_1364])).

tff(c_1385,plain,(
    ! [B_498] :
      ( r3_lattices('#skF_5',B_498,k16_lattice3('#skF_5','#skF_6'))
      | ~ r1_lattices('#skF_5',B_498,k16_lattice3('#skF_5','#skF_6'))
      | ~ m1_subset_1(B_498,u1_struct_0('#skF_5'))
      | ~ v9_lattices('#skF_5')
      | ~ v8_lattices('#skF_5')
      | ~ v6_lattices('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_1368])).

tff(c_1386,plain,(
    ! [B_498] :
      ( r3_lattices('#skF_5',B_498,k16_lattice3('#skF_5','#skF_6'))
      | ~ r1_lattices('#skF_5',B_498,k16_lattice3('#skF_5','#skF_6'))
      | ~ m1_subset_1(B_498,u1_struct_0('#skF_5'))
      | ~ v9_lattices('#skF_5')
      | ~ v8_lattices('#skF_5')
      | ~ v6_lattices('#skF_5') ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_1385])).

tff(c_1404,plain,(
    ! [B_498] :
      ( r3_lattices('#skF_5',B_498,k16_lattice3('#skF_5','#skF_6'))
      | ~ r1_lattices('#skF_5',B_498,k16_lattice3('#skF_5','#skF_6'))
      | ~ m1_subset_1(B_498,u1_struct_0('#skF_5'))
      | ~ v9_lattices('#skF_5')
      | ~ v8_lattices('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1402,c_1386])).

tff(c_1405,plain,(
    ~ v8_lattices('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_1404])).

tff(c_1408,plain,
    ( ~ v10_lattices('#skF_5')
    | v2_struct_0('#skF_5')
    | ~ l3_lattices('#skF_5') ),
    inference(resolution,[status(thm)],[c_10,c_1405])).

tff(c_1411,plain,(
    v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_70,c_1408])).

tff(c_1413,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_1411])).

tff(c_1415,plain,(
    v8_lattices('#skF_5') ),
    inference(splitRight,[status(thm)],[c_1404])).

tff(c_1414,plain,(
    ! [B_498] :
      ( ~ v9_lattices('#skF_5')
      | r3_lattices('#skF_5',B_498,k16_lattice3('#skF_5','#skF_6'))
      | ~ r1_lattices('#skF_5',B_498,k16_lattice3('#skF_5','#skF_6'))
      | ~ m1_subset_1(B_498,u1_struct_0('#skF_5')) ) ),
    inference(splitRight,[status(thm)],[c_1404])).

tff(c_1416,plain,(
    ~ v9_lattices('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_1414])).

tff(c_1419,plain,
    ( ~ v10_lattices('#skF_5')
    | v2_struct_0('#skF_5')
    | ~ l3_lattices('#skF_5') ),
    inference(resolution,[status(thm)],[c_8,c_1416])).

tff(c_1422,plain,(
    v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_70,c_1419])).

tff(c_1424,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_1422])).

tff(c_1426,plain,(
    v9_lattices('#skF_5') ),
    inference(splitRight,[status(thm)],[c_1414])).

tff(c_56,plain,(
    ! [A_67,C_73,B_71] :
      ( r3_lattices(A_67,k16_lattice3(A_67,C_73),B_71)
      | ~ r2_hidden(B_71,C_73)
      | ~ m1_subset_1(B_71,u1_struct_0(A_67))
      | ~ l3_lattices(A_67)
      | ~ v4_lattice3(A_67)
      | ~ v10_lattices(A_67)
      | v2_struct_0(A_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_172])).

tff(c_1427,plain,(
    ! [A_500,B_501,C_502] :
      ( r1_lattices(A_500,B_501,C_502)
      | ~ r3_lattices(A_500,B_501,C_502)
      | ~ m1_subset_1(C_502,u1_struct_0(A_500))
      | ~ m1_subset_1(B_501,u1_struct_0(A_500))
      | ~ l3_lattices(A_500)
      | ~ v9_lattices(A_500)
      | ~ v8_lattices(A_500)
      | ~ v6_lattices(A_500)
      | v2_struct_0(A_500) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_1788,plain,(
    ! [A_587,C_588,B_589] :
      ( r1_lattices(A_587,k16_lattice3(A_587,C_588),B_589)
      | ~ m1_subset_1(k16_lattice3(A_587,C_588),u1_struct_0(A_587))
      | ~ v9_lattices(A_587)
      | ~ v8_lattices(A_587)
      | ~ v6_lattices(A_587)
      | ~ r2_hidden(B_589,C_588)
      | ~ m1_subset_1(B_589,u1_struct_0(A_587))
      | ~ l3_lattices(A_587)
      | ~ v4_lattice3(A_587)
      | ~ v10_lattices(A_587)
      | v2_struct_0(A_587) ) ),
    inference(resolution,[status(thm)],[c_56,c_1427])).

tff(c_1790,plain,(
    ! [B_589] :
      ( r1_lattices('#skF_5',k16_lattice3('#skF_5','#skF_7'),B_589)
      | ~ v9_lattices('#skF_5')
      | ~ v8_lattices('#skF_5')
      | ~ v6_lattices('#skF_5')
      | ~ r2_hidden(B_589,'#skF_7')
      | ~ m1_subset_1(B_589,u1_struct_0('#skF_5'))
      | ~ l3_lattices('#skF_5')
      | ~ v4_lattice3('#skF_5')
      | ~ v10_lattices('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_1214,c_1788])).

tff(c_1799,plain,(
    ! [B_589] :
      ( r1_lattices('#skF_5',k16_lattice3('#skF_5','#skF_7'),B_589)
      | ~ r2_hidden(B_589,'#skF_7')
      | ~ m1_subset_1(B_589,u1_struct_0('#skF_5'))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_66,c_1402,c_1415,c_1426,c_1790])).

tff(c_1806,plain,(
    ! [B_590] :
      ( r1_lattices('#skF_5',k16_lattice3('#skF_5','#skF_7'),B_590)
      | ~ r2_hidden(B_590,'#skF_7')
      | ~ m1_subset_1(B_590,u1_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_1799])).

tff(c_28,plain,(
    ! [A_10,B_22,C_28] :
      ( ~ r1_lattices(A_10,B_22,'#skF_2'(A_10,B_22,C_28))
      | r3_lattice3(A_10,B_22,C_28)
      | ~ m1_subset_1(B_22,u1_struct_0(A_10))
      | ~ l3_lattices(A_10)
      | v2_struct_0(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_1813,plain,(
    ! [C_28] :
      ( r3_lattice3('#skF_5',k16_lattice3('#skF_5','#skF_7'),C_28)
      | ~ m1_subset_1(k16_lattice3('#skF_5','#skF_7'),u1_struct_0('#skF_5'))
      | ~ l3_lattices('#skF_5')
      | v2_struct_0('#skF_5')
      | ~ r2_hidden('#skF_2'('#skF_5',k16_lattice3('#skF_5','#skF_7'),C_28),'#skF_7')
      | ~ m1_subset_1('#skF_2'('#skF_5',k16_lattice3('#skF_5','#skF_7'),C_28),u1_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_1806,c_28])).

tff(c_1819,plain,(
    ! [C_28] :
      ( r3_lattice3('#skF_5',k16_lattice3('#skF_5','#skF_7'),C_28)
      | v2_struct_0('#skF_5')
      | ~ r2_hidden('#skF_2'('#skF_5',k16_lattice3('#skF_5','#skF_7'),C_28),'#skF_7')
      | ~ m1_subset_1('#skF_2'('#skF_5',k16_lattice3('#skF_5','#skF_7'),C_28),u1_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_1214,c_1813])).

tff(c_1830,plain,(
    ! [C_592] :
      ( r3_lattice3('#skF_5',k16_lattice3('#skF_5','#skF_7'),C_592)
      | ~ r2_hidden('#skF_2'('#skF_5',k16_lattice3('#skF_5','#skF_7'),C_592),'#skF_7')
      | ~ m1_subset_1('#skF_2'('#skF_5',k16_lattice3('#skF_5','#skF_7'),C_592),u1_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_1819])).

tff(c_1834,plain,(
    ! [C_28] :
      ( ~ r2_hidden('#skF_2'('#skF_5',k16_lattice3('#skF_5','#skF_7'),C_28),'#skF_7')
      | r3_lattice3('#skF_5',k16_lattice3('#skF_5','#skF_7'),C_28)
      | ~ m1_subset_1(k16_lattice3('#skF_5','#skF_7'),u1_struct_0('#skF_5'))
      | ~ l3_lattices('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_32,c_1830])).

tff(c_1837,plain,(
    ! [C_28] :
      ( ~ r2_hidden('#skF_2'('#skF_5',k16_lattice3('#skF_5','#skF_7'),C_28),'#skF_7')
      | r3_lattice3('#skF_5',k16_lattice3('#skF_5','#skF_7'),C_28)
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_1214,c_1834])).

tff(c_1839,plain,(
    ! [C_593] :
      ( ~ r2_hidden('#skF_2'('#skF_5',k16_lattice3('#skF_5','#skF_7'),C_593),'#skF_7')
      | r3_lattice3('#skF_5',k16_lattice3('#skF_5','#skF_7'),C_593) ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_1837])).

tff(c_1843,plain,(
    ! [C_484] :
      ( ~ r1_tarski('#skF_7','#skF_7')
      | ~ r1_tarski(C_484,'#skF_6')
      | r3_lattice3('#skF_5',k16_lattice3('#skF_5','#skF_7'),C_484)
      | ~ m1_subset_1(k16_lattice3('#skF_5','#skF_7'),u1_struct_0('#skF_5'))
      | ~ l3_lattices('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_1323,c_1839])).

tff(c_1858,plain,(
    ! [C_484] :
      ( ~ r1_tarski(C_484,'#skF_6')
      | r3_lattice3('#skF_5',k16_lattice3('#skF_5','#skF_7'),C_484)
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_1214,c_1008,c_1843])).

tff(c_1872,plain,(
    ! [C_594] :
      ( ~ r1_tarski(C_594,'#skF_6')
      | r3_lattice3('#skF_5',k16_lattice3('#skF_5','#skF_7'),C_594) ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_1858])).

tff(c_1213,plain,(
    ~ r3_lattice3('#skF_5',k16_lattice3('#skF_5','#skF_7'),'#skF_6') ),
    inference(splitRight,[status(thm)],[c_1203])).

tff(c_1875,plain,(
    ~ r1_tarski('#skF_6','#skF_6') ),
    inference(resolution,[status(thm)],[c_1872,c_1213])).

tff(c_1879,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1008,c_1875])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:08:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.51/2.16  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.51/2.18  
% 5.51/2.18  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.51/2.18  %$ r4_lattice3 > r3_lattices > r3_lattice3 > r1_lattices > r2_hidden > r1_tarski > m1_subset_1 > v9_lattices > v8_lattices > v7_lattices > v6_lattices > v5_lattices > v4_lattices > v4_lattice3 > v2_struct_0 > v10_lattices > l3_lattices > k16_lattice3 > k15_lattice3 > a_2_2_lattice3 > #nlpp > u1_struct_0 > #skF_4 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1
% 5.51/2.18  
% 5.51/2.18  %Foreground sorts:
% 5.51/2.18  
% 5.51/2.18  
% 5.51/2.18  %Background operators:
% 5.51/2.18  
% 5.51/2.18  
% 5.51/2.18  %Foreground operators:
% 5.51/2.18  tff(l3_lattices, type, l3_lattices: $i > $o).
% 5.51/2.18  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 5.51/2.18  tff(r3_lattices, type, r3_lattices: ($i * $i * $i) > $o).
% 5.51/2.18  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.51/2.18  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.51/2.18  tff(k16_lattice3, type, k16_lattice3: ($i * $i) > $i).
% 5.51/2.18  tff(k15_lattice3, type, k15_lattice3: ($i * $i) > $i).
% 5.51/2.18  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 5.51/2.18  tff('#skF_7', type, '#skF_7': $i).
% 5.51/2.18  tff(r1_lattices, type, r1_lattices: ($i * $i * $i) > $o).
% 5.51/2.18  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.51/2.18  tff('#skF_5', type, '#skF_5': $i).
% 5.51/2.18  tff(v4_lattices, type, v4_lattices: $i > $o).
% 5.51/2.18  tff('#skF_6', type, '#skF_6': $i).
% 5.51/2.18  tff(v6_lattices, type, v6_lattices: $i > $o).
% 5.51/2.18  tff(v9_lattices, type, v9_lattices: $i > $o).
% 5.51/2.18  tff(r4_lattice3, type, r4_lattice3: ($i * $i * $i) > $o).
% 5.51/2.18  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 5.51/2.18  tff(v4_lattice3, type, v4_lattice3: $i > $o).
% 5.51/2.18  tff(v5_lattices, type, v5_lattices: $i > $o).
% 5.51/2.18  tff(v10_lattices, type, v10_lattices: $i > $o).
% 5.51/2.18  tff(a_2_2_lattice3, type, a_2_2_lattice3: ($i * $i) > $i).
% 5.51/2.18  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.51/2.18  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 5.51/2.18  tff(v8_lattices, type, v8_lattices: $i > $o).
% 5.51/2.18  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.51/2.18  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 5.51/2.18  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 5.51/2.18  tff(r3_lattice3, type, r3_lattice3: ($i * $i * $i) > $o).
% 5.51/2.18  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.51/2.18  tff(v7_lattices, type, v7_lattices: $i > $o).
% 5.51/2.18  
% 5.51/2.22  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 5.51/2.22  tff(f_206, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v10_lattices(A)) & v4_lattice3(A)) & l3_lattices(A)) => (![B, C]: (r1_tarski(B, C) => (r3_lattices(A, k15_lattice3(A, B), k15_lattice3(A, C)) & r3_lattices(A, k16_lattice3(A, C), k16_lattice3(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_lattice3)).
% 5.51/2.22  tff(f_123, axiom, (![A, B]: ((~v2_struct_0(A) & l3_lattices(A)) => m1_subset_1(k16_lattice3(A, B), u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k16_lattice3)).
% 5.51/2.22  tff(f_189, axiom, (![A]: ((((~v2_struct_0(A) & v10_lattices(A)) & v4_lattice3(A)) & l3_lattices(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (r3_lattice3(A, B, C) => r3_lattices(A, B, k16_lattice3(A, C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t40_lattice3)).
% 5.51/2.22  tff(f_116, axiom, (![A, B]: ((~v2_struct_0(A) & l3_lattices(A)) => m1_subset_1(k15_lattice3(A, B), u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k15_lattice3)).
% 5.51/2.22  tff(f_153, axiom, (![A]: ((((~v2_struct_0(A) & v10_lattices(A)) & v4_lattice3(A)) & l3_lattices(A)) => (![B]: (k15_lattice3(A, B) = k16_lattice3(A, a_2_2_lattice3(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t37_lattice3)).
% 5.51/2.22  tff(f_172, axiom, (![A]: ((((~v2_struct_0(A) & v10_lattices(A)) & v4_lattice3(A)) & l3_lattices(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (r2_hidden(B, C) => (r3_lattices(A, B, k15_lattice3(A, C)) & r3_lattices(A, k16_lattice3(A, C), B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_lattice3)).
% 5.51/2.22  tff(f_109, axiom, (![A]: ((~v2_struct_0(A) & l3_lattices(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (r4_lattice3(A, B, C) <=> (![D]: (m1_subset_1(D, u1_struct_0(A)) => (r2_hidden(D, C) => r1_lattices(A, D, B)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d17_lattice3)).
% 5.51/2.22  tff(f_54, axiom, (![A]: (l3_lattices(A) => ((~v2_struct_0(A) & v10_lattices(A)) => ((((((~v2_struct_0(A) & v4_lattices(A)) & v5_lattices(A)) & v6_lattices(A)) & v7_lattices(A)) & v8_lattices(A)) & v9_lattices(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_lattices)).
% 5.51/2.22  tff(f_73, axiom, (![A, B, C]: (((((((~v2_struct_0(A) & v6_lattices(A)) & v8_lattices(A)) & v9_lattices(A)) & l3_lattices(A)) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => (r3_lattices(A, B, C) <=> r1_lattices(A, B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r3_lattices)).
% 5.51/2.22  tff(f_141, axiom, (![A, B, C]: ((((~v2_struct_0(B) & v10_lattices(B)) & v4_lattice3(B)) & l3_lattices(B)) => (r2_hidden(A, a_2_2_lattice3(B, C)) <=> (?[D]: ((m1_subset_1(D, u1_struct_0(B)) & (A = D)) & r4_lattice3(B, D, C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fraenkel_a_2_2_lattice3)).
% 5.51/2.22  tff(f_91, axiom, (![A]: ((~v2_struct_0(A) & l3_lattices(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (r3_lattice3(A, B, C) <=> (![D]: (m1_subset_1(D, u1_struct_0(A)) => (r2_hidden(D, C) => r1_lattices(A, B, D)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d16_lattice3)).
% 5.51/2.22  tff(c_1003, plain, (![A_367, B_368]: (r2_hidden('#skF_1'(A_367, B_368), A_367) | r1_tarski(A_367, B_368))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.51/2.22  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.51/2.22  tff(c_1008, plain, (![A_367]: (r1_tarski(A_367, A_367))), inference(resolution, [status(thm)], [c_1003, c_4])).
% 5.51/2.22  tff(c_72, plain, (~v2_struct_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_206])).
% 5.51/2.22  tff(c_66, plain, (l3_lattices('#skF_5')), inference(cnfTransformation, [status(thm)], [f_206])).
% 5.51/2.22  tff(c_44, plain, (![A_56, B_57]: (m1_subset_1(k16_lattice3(A_56, B_57), u1_struct_0(A_56)) | ~l3_lattices(A_56) | v2_struct_0(A_56))), inference(cnfTransformation, [status(thm)], [f_123])).
% 5.51/2.22  tff(c_70, plain, (v10_lattices('#skF_5')), inference(cnfTransformation, [status(thm)], [f_206])).
% 5.51/2.22  tff(c_68, plain, (v4_lattice3('#skF_5')), inference(cnfTransformation, [status(thm)], [f_206])).
% 5.51/2.22  tff(c_1193, plain, (![A_451, B_452, C_453]: (r3_lattices(A_451, B_452, k16_lattice3(A_451, C_453)) | ~r3_lattice3(A_451, B_452, C_453) | ~m1_subset_1(B_452, u1_struct_0(A_451)) | ~l3_lattices(A_451) | ~v4_lattice3(A_451) | ~v10_lattices(A_451) | v2_struct_0(A_451))), inference(cnfTransformation, [status(thm)], [f_189])).
% 5.51/2.22  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.51/2.22  tff(c_81, plain, (![A_91, B_92]: (~r2_hidden('#skF_1'(A_91, B_92), B_92) | r1_tarski(A_91, B_92))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.51/2.22  tff(c_86, plain, (![A_1]: (r1_tarski(A_1, A_1))), inference(resolution, [status(thm)], [c_6, c_81])).
% 5.51/2.22  tff(c_42, plain, (![A_54, B_55]: (m1_subset_1(k15_lattice3(A_54, B_55), u1_struct_0(A_54)) | ~l3_lattices(A_54) | v2_struct_0(A_54))), inference(cnfTransformation, [status(thm)], [f_116])).
% 5.51/2.22  tff(c_54, plain, (![A_64, B_66]: (k16_lattice3(A_64, a_2_2_lattice3(A_64, B_66))=k15_lattice3(A_64, B_66) | ~l3_lattices(A_64) | ~v4_lattice3(A_64) | ~v10_lattices(A_64) | v2_struct_0(A_64))), inference(cnfTransformation, [status(thm)], [f_153])).
% 5.51/2.22  tff(c_215, plain, (![A_156, C_157, B_158]: (r3_lattices(A_156, k16_lattice3(A_156, C_157), B_158) | ~r2_hidden(B_158, C_157) | ~m1_subset_1(B_158, u1_struct_0(A_156)) | ~l3_lattices(A_156) | ~v4_lattice3(A_156) | ~v10_lattices(A_156) | v2_struct_0(A_156))), inference(cnfTransformation, [status(thm)], [f_172])).
% 5.51/2.22  tff(c_573, plain, (![A_285, B_286, B_287]: (r3_lattices(A_285, k15_lattice3(A_285, B_286), B_287) | ~r2_hidden(B_287, a_2_2_lattice3(A_285, B_286)) | ~m1_subset_1(B_287, u1_struct_0(A_285)) | ~l3_lattices(A_285) | ~v4_lattice3(A_285) | ~v10_lattices(A_285) | v2_struct_0(A_285) | ~l3_lattices(A_285) | ~v4_lattice3(A_285) | ~v10_lattices(A_285) | v2_struct_0(A_285))), inference(superposition, [status(thm), theory('equality')], [c_54, c_215])).
% 5.51/2.22  tff(c_62, plain, (~r3_lattices('#skF_5', k16_lattice3('#skF_5', '#skF_7'), k16_lattice3('#skF_5', '#skF_6')) | ~r3_lattices('#skF_5', k15_lattice3('#skF_5', '#skF_6'), k15_lattice3('#skF_5', '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_206])).
% 5.51/2.22  tff(c_77, plain, (~r3_lattices('#skF_5', k15_lattice3('#skF_5', '#skF_6'), k15_lattice3('#skF_5', '#skF_7'))), inference(splitLeft, [status(thm)], [c_62])).
% 5.51/2.22  tff(c_578, plain, (~r2_hidden(k15_lattice3('#skF_5', '#skF_7'), a_2_2_lattice3('#skF_5', '#skF_6')) | ~m1_subset_1(k15_lattice3('#skF_5', '#skF_7'), u1_struct_0('#skF_5')) | ~l3_lattices('#skF_5') | ~v4_lattice3('#skF_5') | ~v10_lattices('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_573, c_77])).
% 5.51/2.22  tff(c_582, plain, (~r2_hidden(k15_lattice3('#skF_5', '#skF_7'), a_2_2_lattice3('#skF_5', '#skF_6')) | ~m1_subset_1(k15_lattice3('#skF_5', '#skF_7'), u1_struct_0('#skF_5')) | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_66, c_578])).
% 5.51/2.22  tff(c_583, plain, (~r2_hidden(k15_lattice3('#skF_5', '#skF_7'), a_2_2_lattice3('#skF_5', '#skF_6')) | ~m1_subset_1(k15_lattice3('#skF_5', '#skF_7'), u1_struct_0('#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_72, c_582])).
% 5.51/2.22  tff(c_584, plain, (~m1_subset_1(k15_lattice3('#skF_5', '#skF_7'), u1_struct_0('#skF_5'))), inference(splitLeft, [status(thm)], [c_583])).
% 5.51/2.22  tff(c_587, plain, (~l3_lattices('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_42, c_584])).
% 5.51/2.22  tff(c_590, plain, (v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_587])).
% 5.51/2.22  tff(c_592, plain, $false, inference(negUnitSimplification, [status(thm)], [c_72, c_590])).
% 5.51/2.22  tff(c_594, plain, (m1_subset_1(k15_lattice3('#skF_5', '#skF_7'), u1_struct_0('#skF_5'))), inference(splitRight, [status(thm)], [c_583])).
% 5.51/2.22  tff(c_40, plain, (![A_32, B_44, C_50]: (m1_subset_1('#skF_3'(A_32, B_44, C_50), u1_struct_0(A_32)) | r4_lattice3(A_32, B_44, C_50) | ~m1_subset_1(B_44, u1_struct_0(A_32)) | ~l3_lattices(A_32) | v2_struct_0(A_32))), inference(cnfTransformation, [status(thm)], [f_109])).
% 5.51/2.22  tff(c_64, plain, (r1_tarski('#skF_6', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_206])).
% 5.51/2.22  tff(c_199, plain, (![A_131, B_132, C_133]: (r2_hidden('#skF_3'(A_131, B_132, C_133), C_133) | r4_lattice3(A_131, B_132, C_133) | ~m1_subset_1(B_132, u1_struct_0(A_131)) | ~l3_lattices(A_131) | v2_struct_0(A_131))), inference(cnfTransformation, [status(thm)], [f_109])).
% 5.51/2.22  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.51/2.22  tff(c_281, plain, (![A_175, B_176, C_177, B_178]: (r2_hidden('#skF_3'(A_175, B_176, C_177), B_178) | ~r1_tarski(C_177, B_178) | r4_lattice3(A_175, B_176, C_177) | ~m1_subset_1(B_176, u1_struct_0(A_175)) | ~l3_lattices(A_175) | v2_struct_0(A_175))), inference(resolution, [status(thm)], [c_199, c_2])).
% 5.51/2.22  tff(c_342, plain, (![B_194, A_192, C_191, B_193, B_195]: (r2_hidden('#skF_3'(A_192, B_193, C_191), B_195) | ~r1_tarski(B_194, B_195) | ~r1_tarski(C_191, B_194) | r4_lattice3(A_192, B_193, C_191) | ~m1_subset_1(B_193, u1_struct_0(A_192)) | ~l3_lattices(A_192) | v2_struct_0(A_192))), inference(resolution, [status(thm)], [c_281, c_2])).
% 5.51/2.22  tff(c_362, plain, (![A_199, B_200, C_201]: (r2_hidden('#skF_3'(A_199, B_200, C_201), '#skF_7') | ~r1_tarski(C_201, '#skF_6') | r4_lattice3(A_199, B_200, C_201) | ~m1_subset_1(B_200, u1_struct_0(A_199)) | ~l3_lattices(A_199) | v2_struct_0(A_199))), inference(resolution, [status(thm)], [c_64, c_342])).
% 5.51/2.22  tff(c_34, plain, (![A_32, D_53, B_44, C_50]: (r1_lattices(A_32, D_53, B_44) | ~r2_hidden(D_53, C_50) | ~m1_subset_1(D_53, u1_struct_0(A_32)) | ~r4_lattice3(A_32, B_44, C_50) | ~m1_subset_1(B_44, u1_struct_0(A_32)) | ~l3_lattices(A_32) | v2_struct_0(A_32))), inference(cnfTransformation, [status(thm)], [f_109])).
% 5.51/2.22  tff(c_632, plain, (![C_296, A_293, B_292, A_294, B_295]: (r1_lattices(A_293, '#skF_3'(A_294, B_292, C_296), B_295) | ~m1_subset_1('#skF_3'(A_294, B_292, C_296), u1_struct_0(A_293)) | ~r4_lattice3(A_293, B_295, '#skF_7') | ~m1_subset_1(B_295, u1_struct_0(A_293)) | ~l3_lattices(A_293) | v2_struct_0(A_293) | ~r1_tarski(C_296, '#skF_6') | r4_lattice3(A_294, B_292, C_296) | ~m1_subset_1(B_292, u1_struct_0(A_294)) | ~l3_lattices(A_294) | v2_struct_0(A_294))), inference(resolution, [status(thm)], [c_362, c_34])).
% 5.51/2.22  tff(c_636, plain, (![A_297, B_298, C_299, B_300]: (r1_lattices(A_297, '#skF_3'(A_297, B_298, C_299), B_300) | ~r4_lattice3(A_297, B_300, '#skF_7') | ~m1_subset_1(B_300, u1_struct_0(A_297)) | ~r1_tarski(C_299, '#skF_6') | r4_lattice3(A_297, B_298, C_299) | ~m1_subset_1(B_298, u1_struct_0(A_297)) | ~l3_lattices(A_297) | v2_struct_0(A_297))), inference(resolution, [status(thm)], [c_40, c_632])).
% 5.51/2.22  tff(c_36, plain, (![A_32, B_44, C_50]: (~r1_lattices(A_32, '#skF_3'(A_32, B_44, C_50), B_44) | r4_lattice3(A_32, B_44, C_50) | ~m1_subset_1(B_44, u1_struct_0(A_32)) | ~l3_lattices(A_32) | v2_struct_0(A_32))), inference(cnfTransformation, [status(thm)], [f_109])).
% 5.51/2.22  tff(c_647, plain, (![A_301, B_302, C_303]: (~r4_lattice3(A_301, B_302, '#skF_7') | ~r1_tarski(C_303, '#skF_6') | r4_lattice3(A_301, B_302, C_303) | ~m1_subset_1(B_302, u1_struct_0(A_301)) | ~l3_lattices(A_301) | v2_struct_0(A_301))), inference(resolution, [status(thm)], [c_636, c_36])).
% 5.51/2.22  tff(c_649, plain, (![C_303]: (~r4_lattice3('#skF_5', k15_lattice3('#skF_5', '#skF_7'), '#skF_7') | ~r1_tarski(C_303, '#skF_6') | r4_lattice3('#skF_5', k15_lattice3('#skF_5', '#skF_7'), C_303) | ~l3_lattices('#skF_5') | v2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_594, c_647])).
% 5.51/2.22  tff(c_664, plain, (![C_303]: (~r4_lattice3('#skF_5', k15_lattice3('#skF_5', '#skF_7'), '#skF_7') | ~r1_tarski(C_303, '#skF_6') | r4_lattice3('#skF_5', k15_lattice3('#skF_5', '#skF_7'), C_303) | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_649])).
% 5.51/2.22  tff(c_665, plain, (![C_303]: (~r4_lattice3('#skF_5', k15_lattice3('#skF_5', '#skF_7'), '#skF_7') | ~r1_tarski(C_303, '#skF_6') | r4_lattice3('#skF_5', k15_lattice3('#skF_5', '#skF_7'), C_303))), inference(negUnitSimplification, [status(thm)], [c_72, c_664])).
% 5.51/2.22  tff(c_675, plain, (~r4_lattice3('#skF_5', k15_lattice3('#skF_5', '#skF_7'), '#skF_7')), inference(splitLeft, [status(thm)], [c_665])).
% 5.51/2.22  tff(c_38, plain, (![A_32, B_44, C_50]: (r2_hidden('#skF_3'(A_32, B_44, C_50), C_50) | r4_lattice3(A_32, B_44, C_50) | ~m1_subset_1(B_44, u1_struct_0(A_32)) | ~l3_lattices(A_32) | v2_struct_0(A_32))), inference(cnfTransformation, [status(thm)], [f_109])).
% 5.51/2.22  tff(c_14, plain, (![A_6]: (v6_lattices(A_6) | ~v10_lattices(A_6) | v2_struct_0(A_6) | ~l3_lattices(A_6))), inference(cnfTransformation, [status(thm)], [f_54])).
% 5.51/2.22  tff(c_232, plain, (![A_162, B_163, C_164]: (r3_lattices(A_162, B_163, k15_lattice3(A_162, C_164)) | ~r2_hidden(B_163, C_164) | ~m1_subset_1(B_163, u1_struct_0(A_162)) | ~l3_lattices(A_162) | ~v4_lattice3(A_162) | ~v10_lattices(A_162) | v2_struct_0(A_162))), inference(cnfTransformation, [status(thm)], [f_172])).
% 5.51/2.22  tff(c_235, plain, (~r2_hidden(k15_lattice3('#skF_5', '#skF_6'), '#skF_7') | ~m1_subset_1(k15_lattice3('#skF_5', '#skF_6'), u1_struct_0('#skF_5')) | ~l3_lattices('#skF_5') | ~v4_lattice3('#skF_5') | ~v10_lattices('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_232, c_77])).
% 5.51/2.22  tff(c_238, plain, (~r2_hidden(k15_lattice3('#skF_5', '#skF_6'), '#skF_7') | ~m1_subset_1(k15_lattice3('#skF_5', '#skF_6'), u1_struct_0('#skF_5')) | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_66, c_235])).
% 5.51/2.22  tff(c_239, plain, (~r2_hidden(k15_lattice3('#skF_5', '#skF_6'), '#skF_7') | ~m1_subset_1(k15_lattice3('#skF_5', '#skF_6'), u1_struct_0('#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_72, c_238])).
% 5.51/2.22  tff(c_240, plain, (~m1_subset_1(k15_lattice3('#skF_5', '#skF_6'), u1_struct_0('#skF_5'))), inference(splitLeft, [status(thm)], [c_239])).
% 5.51/2.22  tff(c_243, plain, (~l3_lattices('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_42, c_240])).
% 5.51/2.22  tff(c_246, plain, (v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_243])).
% 5.51/2.22  tff(c_248, plain, $false, inference(negUnitSimplification, [status(thm)], [c_72, c_246])).
% 5.51/2.22  tff(c_250, plain, (m1_subset_1(k15_lattice3('#skF_5', '#skF_6'), u1_struct_0('#skF_5'))), inference(splitRight, [status(thm)], [c_239])).
% 5.51/2.22  tff(c_451, plain, (![A_233, B_234, C_235]: (r3_lattices(A_233, B_234, C_235) | ~r1_lattices(A_233, B_234, C_235) | ~m1_subset_1(C_235, u1_struct_0(A_233)) | ~m1_subset_1(B_234, u1_struct_0(A_233)) | ~l3_lattices(A_233) | ~v9_lattices(A_233) | ~v8_lattices(A_233) | ~v6_lattices(A_233) | v2_struct_0(A_233))), inference(cnfTransformation, [status(thm)], [f_73])).
% 5.51/2.22  tff(c_453, plain, (![B_234]: (r3_lattices('#skF_5', B_234, k15_lattice3('#skF_5', '#skF_6')) | ~r1_lattices('#skF_5', B_234, k15_lattice3('#skF_5', '#skF_6')) | ~m1_subset_1(B_234, u1_struct_0('#skF_5')) | ~l3_lattices('#skF_5') | ~v9_lattices('#skF_5') | ~v8_lattices('#skF_5') | ~v6_lattices('#skF_5') | v2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_250, c_451])).
% 5.51/2.22  tff(c_466, plain, (![B_234]: (r3_lattices('#skF_5', B_234, k15_lattice3('#skF_5', '#skF_6')) | ~r1_lattices('#skF_5', B_234, k15_lattice3('#skF_5', '#skF_6')) | ~m1_subset_1(B_234, u1_struct_0('#skF_5')) | ~v9_lattices('#skF_5') | ~v8_lattices('#skF_5') | ~v6_lattices('#skF_5') | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_453])).
% 5.51/2.22  tff(c_467, plain, (![B_234]: (r3_lattices('#skF_5', B_234, k15_lattice3('#skF_5', '#skF_6')) | ~r1_lattices('#skF_5', B_234, k15_lattice3('#skF_5', '#skF_6')) | ~m1_subset_1(B_234, u1_struct_0('#skF_5')) | ~v9_lattices('#skF_5') | ~v8_lattices('#skF_5') | ~v6_lattices('#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_72, c_466])).
% 5.51/2.22  tff(c_473, plain, (~v6_lattices('#skF_5')), inference(splitLeft, [status(thm)], [c_467])).
% 5.51/2.22  tff(c_476, plain, (~v10_lattices('#skF_5') | v2_struct_0('#skF_5') | ~l3_lattices('#skF_5')), inference(resolution, [status(thm)], [c_14, c_473])).
% 5.51/2.22  tff(c_479, plain, (v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_70, c_476])).
% 5.51/2.22  tff(c_481, plain, $false, inference(negUnitSimplification, [status(thm)], [c_72, c_479])).
% 5.51/2.22  tff(c_483, plain, (v6_lattices('#skF_5')), inference(splitRight, [status(thm)], [c_467])).
% 5.51/2.22  tff(c_10, plain, (![A_6]: (v8_lattices(A_6) | ~v10_lattices(A_6) | v2_struct_0(A_6) | ~l3_lattices(A_6))), inference(cnfTransformation, [status(thm)], [f_54])).
% 5.51/2.22  tff(c_8, plain, (![A_6]: (v9_lattices(A_6) | ~v10_lattices(A_6) | v2_struct_0(A_6) | ~l3_lattices(A_6))), inference(cnfTransformation, [status(thm)], [f_54])).
% 5.51/2.22  tff(c_482, plain, (![B_234]: (~v8_lattices('#skF_5') | ~v9_lattices('#skF_5') | r3_lattices('#skF_5', B_234, k15_lattice3('#skF_5', '#skF_6')) | ~r1_lattices('#skF_5', B_234, k15_lattice3('#skF_5', '#skF_6')) | ~m1_subset_1(B_234, u1_struct_0('#skF_5')))), inference(splitRight, [status(thm)], [c_467])).
% 5.51/2.22  tff(c_484, plain, (~v9_lattices('#skF_5')), inference(splitLeft, [status(thm)], [c_482])).
% 5.51/2.22  tff(c_487, plain, (~v10_lattices('#skF_5') | v2_struct_0('#skF_5') | ~l3_lattices('#skF_5')), inference(resolution, [status(thm)], [c_8, c_484])).
% 5.51/2.22  tff(c_490, plain, (v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_70, c_487])).
% 5.51/2.22  tff(c_492, plain, $false, inference(negUnitSimplification, [status(thm)], [c_72, c_490])).
% 5.51/2.22  tff(c_493, plain, (![B_234]: (~v8_lattices('#skF_5') | r3_lattices('#skF_5', B_234, k15_lattice3('#skF_5', '#skF_6')) | ~r1_lattices('#skF_5', B_234, k15_lattice3('#skF_5', '#skF_6')) | ~m1_subset_1(B_234, u1_struct_0('#skF_5')))), inference(splitRight, [status(thm)], [c_482])).
% 5.51/2.22  tff(c_495, plain, (~v8_lattices('#skF_5')), inference(splitLeft, [status(thm)], [c_493])).
% 5.51/2.22  tff(c_498, plain, (~v10_lattices('#skF_5') | v2_struct_0('#skF_5') | ~l3_lattices('#skF_5')), inference(resolution, [status(thm)], [c_10, c_495])).
% 5.51/2.22  tff(c_501, plain, (v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_70, c_498])).
% 5.51/2.22  tff(c_503, plain, $false, inference(negUnitSimplification, [status(thm)], [c_72, c_501])).
% 5.51/2.22  tff(c_505, plain, (v8_lattices('#skF_5')), inference(splitRight, [status(thm)], [c_493])).
% 5.51/2.22  tff(c_494, plain, (v9_lattices('#skF_5')), inference(splitRight, [status(thm)], [c_482])).
% 5.51/2.22  tff(c_58, plain, (![A_67, B_71, C_73]: (r3_lattices(A_67, B_71, k15_lattice3(A_67, C_73)) | ~r2_hidden(B_71, C_73) | ~m1_subset_1(B_71, u1_struct_0(A_67)) | ~l3_lattices(A_67) | ~v4_lattice3(A_67) | ~v10_lattices(A_67) | v2_struct_0(A_67))), inference(cnfTransformation, [status(thm)], [f_172])).
% 5.51/2.22  tff(c_352, plain, (![A_196, B_197, C_198]: (r1_lattices(A_196, B_197, C_198) | ~r3_lattices(A_196, B_197, C_198) | ~m1_subset_1(C_198, u1_struct_0(A_196)) | ~m1_subset_1(B_197, u1_struct_0(A_196)) | ~l3_lattices(A_196) | ~v9_lattices(A_196) | ~v8_lattices(A_196) | ~v6_lattices(A_196) | v2_struct_0(A_196))), inference(cnfTransformation, [status(thm)], [f_73])).
% 5.51/2.22  tff(c_727, plain, (![A_336, B_337, C_338]: (r1_lattices(A_336, B_337, k15_lattice3(A_336, C_338)) | ~m1_subset_1(k15_lattice3(A_336, C_338), u1_struct_0(A_336)) | ~v9_lattices(A_336) | ~v8_lattices(A_336) | ~v6_lattices(A_336) | ~r2_hidden(B_337, C_338) | ~m1_subset_1(B_337, u1_struct_0(A_336)) | ~l3_lattices(A_336) | ~v4_lattice3(A_336) | ~v10_lattices(A_336) | v2_struct_0(A_336))), inference(resolution, [status(thm)], [c_58, c_352])).
% 5.51/2.22  tff(c_729, plain, (![B_337]: (r1_lattices('#skF_5', B_337, k15_lattice3('#skF_5', '#skF_7')) | ~v9_lattices('#skF_5') | ~v8_lattices('#skF_5') | ~v6_lattices('#skF_5') | ~r2_hidden(B_337, '#skF_7') | ~m1_subset_1(B_337, u1_struct_0('#skF_5')) | ~l3_lattices('#skF_5') | ~v4_lattice3('#skF_5') | ~v10_lattices('#skF_5') | v2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_594, c_727])).
% 5.51/2.22  tff(c_736, plain, (![B_337]: (r1_lattices('#skF_5', B_337, k15_lattice3('#skF_5', '#skF_7')) | ~r2_hidden(B_337, '#skF_7') | ~m1_subset_1(B_337, u1_struct_0('#skF_5')) | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_66, c_483, c_505, c_494, c_729])).
% 5.51/2.22  tff(c_752, plain, (![B_340]: (r1_lattices('#skF_5', B_340, k15_lattice3('#skF_5', '#skF_7')) | ~r2_hidden(B_340, '#skF_7') | ~m1_subset_1(B_340, u1_struct_0('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_72, c_736])).
% 5.51/2.22  tff(c_759, plain, (![C_50]: (r4_lattice3('#skF_5', k15_lattice3('#skF_5', '#skF_7'), C_50) | ~m1_subset_1(k15_lattice3('#skF_5', '#skF_7'), u1_struct_0('#skF_5')) | ~l3_lattices('#skF_5') | v2_struct_0('#skF_5') | ~r2_hidden('#skF_3'('#skF_5', k15_lattice3('#skF_5', '#skF_7'), C_50), '#skF_7') | ~m1_subset_1('#skF_3'('#skF_5', k15_lattice3('#skF_5', '#skF_7'), C_50), u1_struct_0('#skF_5')))), inference(resolution, [status(thm)], [c_752, c_36])).
% 5.51/2.22  tff(c_765, plain, (![C_50]: (r4_lattice3('#skF_5', k15_lattice3('#skF_5', '#skF_7'), C_50) | v2_struct_0('#skF_5') | ~r2_hidden('#skF_3'('#skF_5', k15_lattice3('#skF_5', '#skF_7'), C_50), '#skF_7') | ~m1_subset_1('#skF_3'('#skF_5', k15_lattice3('#skF_5', '#skF_7'), C_50), u1_struct_0('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_594, c_759])).
% 5.51/2.22  tff(c_927, plain, (![C_358]: (r4_lattice3('#skF_5', k15_lattice3('#skF_5', '#skF_7'), C_358) | ~r2_hidden('#skF_3'('#skF_5', k15_lattice3('#skF_5', '#skF_7'), C_358), '#skF_7') | ~m1_subset_1('#skF_3'('#skF_5', k15_lattice3('#skF_5', '#skF_7'), C_358), u1_struct_0('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_72, c_765])).
% 5.51/2.22  tff(c_931, plain, (![C_50]: (~r2_hidden('#skF_3'('#skF_5', k15_lattice3('#skF_5', '#skF_7'), C_50), '#skF_7') | r4_lattice3('#skF_5', k15_lattice3('#skF_5', '#skF_7'), C_50) | ~m1_subset_1(k15_lattice3('#skF_5', '#skF_7'), u1_struct_0('#skF_5')) | ~l3_lattices('#skF_5') | v2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_40, c_927])).
% 5.51/2.22  tff(c_934, plain, (![C_50]: (~r2_hidden('#skF_3'('#skF_5', k15_lattice3('#skF_5', '#skF_7'), C_50), '#skF_7') | r4_lattice3('#skF_5', k15_lattice3('#skF_5', '#skF_7'), C_50) | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_594, c_931])).
% 5.51/2.22  tff(c_940, plain, (![C_363]: (~r2_hidden('#skF_3'('#skF_5', k15_lattice3('#skF_5', '#skF_7'), C_363), '#skF_7') | r4_lattice3('#skF_5', k15_lattice3('#skF_5', '#skF_7'), C_363))), inference(negUnitSimplification, [status(thm)], [c_72, c_934])).
% 5.51/2.22  tff(c_956, plain, (r4_lattice3('#skF_5', k15_lattice3('#skF_5', '#skF_7'), '#skF_7') | ~m1_subset_1(k15_lattice3('#skF_5', '#skF_7'), u1_struct_0('#skF_5')) | ~l3_lattices('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_38, c_940])).
% 5.51/2.22  tff(c_971, plain, (r4_lattice3('#skF_5', k15_lattice3('#skF_5', '#skF_7'), '#skF_7') | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_594, c_956])).
% 5.51/2.22  tff(c_973, plain, $false, inference(negUnitSimplification, [status(thm)], [c_72, c_675, c_971])).
% 5.51/2.22  tff(c_988, plain, (![C_364]: (~r1_tarski(C_364, '#skF_6') | r4_lattice3('#skF_5', k15_lattice3('#skF_5', '#skF_7'), C_364))), inference(splitRight, [status(thm)], [c_665])).
% 5.51/2.22  tff(c_46, plain, (![D_63, B_59, C_60]: (r2_hidden(D_63, a_2_2_lattice3(B_59, C_60)) | ~r4_lattice3(B_59, D_63, C_60) | ~m1_subset_1(D_63, u1_struct_0(B_59)) | ~l3_lattices(B_59) | ~v4_lattice3(B_59) | ~v10_lattices(B_59) | v2_struct_0(B_59))), inference(cnfTransformation, [status(thm)], [f_141])).
% 5.51/2.22  tff(c_593, plain, (~r2_hidden(k15_lattice3('#skF_5', '#skF_7'), a_2_2_lattice3('#skF_5', '#skF_6'))), inference(splitRight, [status(thm)], [c_583])).
% 5.51/2.22  tff(c_603, plain, (~r4_lattice3('#skF_5', k15_lattice3('#skF_5', '#skF_7'), '#skF_6') | ~m1_subset_1(k15_lattice3('#skF_5', '#skF_7'), u1_struct_0('#skF_5')) | ~l3_lattices('#skF_5') | ~v4_lattice3('#skF_5') | ~v10_lattices('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_46, c_593])).
% 5.51/2.22  tff(c_606, plain, (~r4_lattice3('#skF_5', k15_lattice3('#skF_5', '#skF_7'), '#skF_6') | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_66, c_594, c_603])).
% 5.51/2.22  tff(c_607, plain, (~r4_lattice3('#skF_5', k15_lattice3('#skF_5', '#skF_7'), '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_72, c_606])).
% 5.51/2.22  tff(c_991, plain, (~r1_tarski('#skF_6', '#skF_6')), inference(resolution, [status(thm)], [c_988, c_607])).
% 5.51/2.22  tff(c_999, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_86, c_991])).
% 5.51/2.22  tff(c_1000, plain, (~r3_lattices('#skF_5', k16_lattice3('#skF_5', '#skF_7'), k16_lattice3('#skF_5', '#skF_6'))), inference(splitRight, [status(thm)], [c_62])).
% 5.51/2.22  tff(c_1196, plain, (~r3_lattice3('#skF_5', k16_lattice3('#skF_5', '#skF_7'), '#skF_6') | ~m1_subset_1(k16_lattice3('#skF_5', '#skF_7'), u1_struct_0('#skF_5')) | ~l3_lattices('#skF_5') | ~v4_lattice3('#skF_5') | ~v10_lattices('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_1193, c_1000])).
% 5.51/2.22  tff(c_1202, plain, (~r3_lattice3('#skF_5', k16_lattice3('#skF_5', '#skF_7'), '#skF_6') | ~m1_subset_1(k16_lattice3('#skF_5', '#skF_7'), u1_struct_0('#skF_5')) | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_66, c_1196])).
% 5.51/2.22  tff(c_1203, plain, (~r3_lattice3('#skF_5', k16_lattice3('#skF_5', '#skF_7'), '#skF_6') | ~m1_subset_1(k16_lattice3('#skF_5', '#skF_7'), u1_struct_0('#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_72, c_1202])).
% 5.51/2.22  tff(c_1204, plain, (~m1_subset_1(k16_lattice3('#skF_5', '#skF_7'), u1_struct_0('#skF_5'))), inference(splitLeft, [status(thm)], [c_1203])).
% 5.51/2.22  tff(c_1207, plain, (~l3_lattices('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_44, c_1204])).
% 5.51/2.22  tff(c_1210, plain, (v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_1207])).
% 5.51/2.22  tff(c_1212, plain, $false, inference(negUnitSimplification, [status(thm)], [c_72, c_1210])).
% 5.51/2.22  tff(c_1214, plain, (m1_subset_1(k16_lattice3('#skF_5', '#skF_7'), u1_struct_0('#skF_5'))), inference(splitRight, [status(thm)], [c_1203])).
% 5.51/2.22  tff(c_1123, plain, (![A_409, B_410, C_411]: (r2_hidden('#skF_2'(A_409, B_410, C_411), C_411) | r3_lattice3(A_409, B_410, C_411) | ~m1_subset_1(B_410, u1_struct_0(A_409)) | ~l3_lattices(A_409) | v2_struct_0(A_409))), inference(cnfTransformation, [status(thm)], [f_91])).
% 5.51/2.22  tff(c_1175, plain, (![A_443, B_444, C_445, B_446]: (r2_hidden('#skF_2'(A_443, B_444, C_445), B_446) | ~r1_tarski(C_445, B_446) | r3_lattice3(A_443, B_444, C_445) | ~m1_subset_1(B_444, u1_struct_0(A_443)) | ~l3_lattices(A_443) | v2_struct_0(A_443))), inference(resolution, [status(thm)], [c_1123, c_2])).
% 5.51/2.22  tff(c_1304, plain, (![A_481, B_480, C_479, B_478, B_477]: (r2_hidden('#skF_2'(A_481, B_478, C_479), B_480) | ~r1_tarski(B_477, B_480) | ~r1_tarski(C_479, B_477) | r3_lattice3(A_481, B_478, C_479) | ~m1_subset_1(B_478, u1_struct_0(A_481)) | ~l3_lattices(A_481) | v2_struct_0(A_481))), inference(resolution, [status(thm)], [c_1175, c_2])).
% 5.51/2.22  tff(c_1314, plain, (![A_482, B_483, C_484]: (r2_hidden('#skF_2'(A_482, B_483, C_484), '#skF_7') | ~r1_tarski(C_484, '#skF_6') | r3_lattice3(A_482, B_483, C_484) | ~m1_subset_1(B_483, u1_struct_0(A_482)) | ~l3_lattices(A_482) | v2_struct_0(A_482))), inference(resolution, [status(thm)], [c_64, c_1304])).
% 5.51/2.22  tff(c_1323, plain, (![A_482, B_483, C_484, B_2]: (r2_hidden('#skF_2'(A_482, B_483, C_484), B_2) | ~r1_tarski('#skF_7', B_2) | ~r1_tarski(C_484, '#skF_6') | r3_lattice3(A_482, B_483, C_484) | ~m1_subset_1(B_483, u1_struct_0(A_482)) | ~l3_lattices(A_482) | v2_struct_0(A_482))), inference(resolution, [status(thm)], [c_1314, c_2])).
% 5.51/2.22  tff(c_32, plain, (![A_10, B_22, C_28]: (m1_subset_1('#skF_2'(A_10, B_22, C_28), u1_struct_0(A_10)) | r3_lattice3(A_10, B_22, C_28) | ~m1_subset_1(B_22, u1_struct_0(A_10)) | ~l3_lattices(A_10) | v2_struct_0(A_10))), inference(cnfTransformation, [status(thm)], [f_91])).
% 5.51/2.22  tff(c_1364, plain, (![A_497, B_498, C_499]: (r3_lattices(A_497, B_498, C_499) | ~r1_lattices(A_497, B_498, C_499) | ~m1_subset_1(C_499, u1_struct_0(A_497)) | ~m1_subset_1(B_498, u1_struct_0(A_497)) | ~l3_lattices(A_497) | ~v9_lattices(A_497) | ~v8_lattices(A_497) | ~v6_lattices(A_497) | v2_struct_0(A_497))), inference(cnfTransformation, [status(thm)], [f_73])).
% 5.51/2.22  tff(c_1366, plain, (![B_498]: (r3_lattices('#skF_5', B_498, k16_lattice3('#skF_5', '#skF_7')) | ~r1_lattices('#skF_5', B_498, k16_lattice3('#skF_5', '#skF_7')) | ~m1_subset_1(B_498, u1_struct_0('#skF_5')) | ~l3_lattices('#skF_5') | ~v9_lattices('#skF_5') | ~v8_lattices('#skF_5') | ~v6_lattices('#skF_5') | v2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_1214, c_1364])).
% 5.51/2.22  tff(c_1381, plain, (![B_498]: (r3_lattices('#skF_5', B_498, k16_lattice3('#skF_5', '#skF_7')) | ~r1_lattices('#skF_5', B_498, k16_lattice3('#skF_5', '#skF_7')) | ~m1_subset_1(B_498, u1_struct_0('#skF_5')) | ~v9_lattices('#skF_5') | ~v8_lattices('#skF_5') | ~v6_lattices('#skF_5') | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_1366])).
% 5.51/2.22  tff(c_1382, plain, (![B_498]: (r3_lattices('#skF_5', B_498, k16_lattice3('#skF_5', '#skF_7')) | ~r1_lattices('#skF_5', B_498, k16_lattice3('#skF_5', '#skF_7')) | ~m1_subset_1(B_498, u1_struct_0('#skF_5')) | ~v9_lattices('#skF_5') | ~v8_lattices('#skF_5') | ~v6_lattices('#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_72, c_1381])).
% 5.51/2.22  tff(c_1392, plain, (~v6_lattices('#skF_5')), inference(splitLeft, [status(thm)], [c_1382])).
% 5.51/2.22  tff(c_1395, plain, (~v10_lattices('#skF_5') | v2_struct_0('#skF_5') | ~l3_lattices('#skF_5')), inference(resolution, [status(thm)], [c_14, c_1392])).
% 5.51/2.22  tff(c_1398, plain, (v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_70, c_1395])).
% 5.51/2.22  tff(c_1400, plain, $false, inference(negUnitSimplification, [status(thm)], [c_72, c_1398])).
% 5.51/2.22  tff(c_1402, plain, (v6_lattices('#skF_5')), inference(splitRight, [status(thm)], [c_1382])).
% 5.51/2.22  tff(c_1139, plain, (![A_434, C_435, B_436]: (r3_lattices(A_434, k16_lattice3(A_434, C_435), B_436) | ~r2_hidden(B_436, C_435) | ~m1_subset_1(B_436, u1_struct_0(A_434)) | ~l3_lattices(A_434) | ~v4_lattice3(A_434) | ~v10_lattices(A_434) | v2_struct_0(A_434))), inference(cnfTransformation, [status(thm)], [f_172])).
% 5.51/2.22  tff(c_1142, plain, (~r2_hidden(k16_lattice3('#skF_5', '#skF_6'), '#skF_7') | ~m1_subset_1(k16_lattice3('#skF_5', '#skF_6'), u1_struct_0('#skF_5')) | ~l3_lattices('#skF_5') | ~v4_lattice3('#skF_5') | ~v10_lattices('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_1139, c_1000])).
% 5.51/2.22  tff(c_1148, plain, (~r2_hidden(k16_lattice3('#skF_5', '#skF_6'), '#skF_7') | ~m1_subset_1(k16_lattice3('#skF_5', '#skF_6'), u1_struct_0('#skF_5')) | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_66, c_1142])).
% 5.51/2.22  tff(c_1149, plain, (~r2_hidden(k16_lattice3('#skF_5', '#skF_6'), '#skF_7') | ~m1_subset_1(k16_lattice3('#skF_5', '#skF_6'), u1_struct_0('#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_72, c_1148])).
% 5.51/2.22  tff(c_1150, plain, (~m1_subset_1(k16_lattice3('#skF_5', '#skF_6'), u1_struct_0('#skF_5'))), inference(splitLeft, [status(thm)], [c_1149])).
% 5.51/2.22  tff(c_1153, plain, (~l3_lattices('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_44, c_1150])).
% 5.51/2.22  tff(c_1156, plain, (v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_1153])).
% 5.51/2.22  tff(c_1158, plain, $false, inference(negUnitSimplification, [status(thm)], [c_72, c_1156])).
% 5.51/2.22  tff(c_1160, plain, (m1_subset_1(k16_lattice3('#skF_5', '#skF_6'), u1_struct_0('#skF_5'))), inference(splitRight, [status(thm)], [c_1149])).
% 5.51/2.22  tff(c_1368, plain, (![B_498]: (r3_lattices('#skF_5', B_498, k16_lattice3('#skF_5', '#skF_6')) | ~r1_lattices('#skF_5', B_498, k16_lattice3('#skF_5', '#skF_6')) | ~m1_subset_1(B_498, u1_struct_0('#skF_5')) | ~l3_lattices('#skF_5') | ~v9_lattices('#skF_5') | ~v8_lattices('#skF_5') | ~v6_lattices('#skF_5') | v2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_1160, c_1364])).
% 5.51/2.22  tff(c_1385, plain, (![B_498]: (r3_lattices('#skF_5', B_498, k16_lattice3('#skF_5', '#skF_6')) | ~r1_lattices('#skF_5', B_498, k16_lattice3('#skF_5', '#skF_6')) | ~m1_subset_1(B_498, u1_struct_0('#skF_5')) | ~v9_lattices('#skF_5') | ~v8_lattices('#skF_5') | ~v6_lattices('#skF_5') | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_1368])).
% 5.51/2.22  tff(c_1386, plain, (![B_498]: (r3_lattices('#skF_5', B_498, k16_lattice3('#skF_5', '#skF_6')) | ~r1_lattices('#skF_5', B_498, k16_lattice3('#skF_5', '#skF_6')) | ~m1_subset_1(B_498, u1_struct_0('#skF_5')) | ~v9_lattices('#skF_5') | ~v8_lattices('#skF_5') | ~v6_lattices('#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_72, c_1385])).
% 5.51/2.22  tff(c_1404, plain, (![B_498]: (r3_lattices('#skF_5', B_498, k16_lattice3('#skF_5', '#skF_6')) | ~r1_lattices('#skF_5', B_498, k16_lattice3('#skF_5', '#skF_6')) | ~m1_subset_1(B_498, u1_struct_0('#skF_5')) | ~v9_lattices('#skF_5') | ~v8_lattices('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_1402, c_1386])).
% 5.51/2.22  tff(c_1405, plain, (~v8_lattices('#skF_5')), inference(splitLeft, [status(thm)], [c_1404])).
% 5.51/2.22  tff(c_1408, plain, (~v10_lattices('#skF_5') | v2_struct_0('#skF_5') | ~l3_lattices('#skF_5')), inference(resolution, [status(thm)], [c_10, c_1405])).
% 5.51/2.22  tff(c_1411, plain, (v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_70, c_1408])).
% 5.51/2.22  tff(c_1413, plain, $false, inference(negUnitSimplification, [status(thm)], [c_72, c_1411])).
% 5.51/2.22  tff(c_1415, plain, (v8_lattices('#skF_5')), inference(splitRight, [status(thm)], [c_1404])).
% 5.51/2.22  tff(c_1414, plain, (![B_498]: (~v9_lattices('#skF_5') | r3_lattices('#skF_5', B_498, k16_lattice3('#skF_5', '#skF_6')) | ~r1_lattices('#skF_5', B_498, k16_lattice3('#skF_5', '#skF_6')) | ~m1_subset_1(B_498, u1_struct_0('#skF_5')))), inference(splitRight, [status(thm)], [c_1404])).
% 5.51/2.22  tff(c_1416, plain, (~v9_lattices('#skF_5')), inference(splitLeft, [status(thm)], [c_1414])).
% 5.51/2.22  tff(c_1419, plain, (~v10_lattices('#skF_5') | v2_struct_0('#skF_5') | ~l3_lattices('#skF_5')), inference(resolution, [status(thm)], [c_8, c_1416])).
% 5.51/2.22  tff(c_1422, plain, (v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_70, c_1419])).
% 5.51/2.22  tff(c_1424, plain, $false, inference(negUnitSimplification, [status(thm)], [c_72, c_1422])).
% 5.51/2.22  tff(c_1426, plain, (v9_lattices('#skF_5')), inference(splitRight, [status(thm)], [c_1414])).
% 5.51/2.22  tff(c_56, plain, (![A_67, C_73, B_71]: (r3_lattices(A_67, k16_lattice3(A_67, C_73), B_71) | ~r2_hidden(B_71, C_73) | ~m1_subset_1(B_71, u1_struct_0(A_67)) | ~l3_lattices(A_67) | ~v4_lattice3(A_67) | ~v10_lattices(A_67) | v2_struct_0(A_67))), inference(cnfTransformation, [status(thm)], [f_172])).
% 5.51/2.22  tff(c_1427, plain, (![A_500, B_501, C_502]: (r1_lattices(A_500, B_501, C_502) | ~r3_lattices(A_500, B_501, C_502) | ~m1_subset_1(C_502, u1_struct_0(A_500)) | ~m1_subset_1(B_501, u1_struct_0(A_500)) | ~l3_lattices(A_500) | ~v9_lattices(A_500) | ~v8_lattices(A_500) | ~v6_lattices(A_500) | v2_struct_0(A_500))), inference(cnfTransformation, [status(thm)], [f_73])).
% 5.51/2.22  tff(c_1788, plain, (![A_587, C_588, B_589]: (r1_lattices(A_587, k16_lattice3(A_587, C_588), B_589) | ~m1_subset_1(k16_lattice3(A_587, C_588), u1_struct_0(A_587)) | ~v9_lattices(A_587) | ~v8_lattices(A_587) | ~v6_lattices(A_587) | ~r2_hidden(B_589, C_588) | ~m1_subset_1(B_589, u1_struct_0(A_587)) | ~l3_lattices(A_587) | ~v4_lattice3(A_587) | ~v10_lattices(A_587) | v2_struct_0(A_587))), inference(resolution, [status(thm)], [c_56, c_1427])).
% 5.51/2.22  tff(c_1790, plain, (![B_589]: (r1_lattices('#skF_5', k16_lattice3('#skF_5', '#skF_7'), B_589) | ~v9_lattices('#skF_5') | ~v8_lattices('#skF_5') | ~v6_lattices('#skF_5') | ~r2_hidden(B_589, '#skF_7') | ~m1_subset_1(B_589, u1_struct_0('#skF_5')) | ~l3_lattices('#skF_5') | ~v4_lattice3('#skF_5') | ~v10_lattices('#skF_5') | v2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_1214, c_1788])).
% 5.51/2.22  tff(c_1799, plain, (![B_589]: (r1_lattices('#skF_5', k16_lattice3('#skF_5', '#skF_7'), B_589) | ~r2_hidden(B_589, '#skF_7') | ~m1_subset_1(B_589, u1_struct_0('#skF_5')) | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_66, c_1402, c_1415, c_1426, c_1790])).
% 5.51/2.22  tff(c_1806, plain, (![B_590]: (r1_lattices('#skF_5', k16_lattice3('#skF_5', '#skF_7'), B_590) | ~r2_hidden(B_590, '#skF_7') | ~m1_subset_1(B_590, u1_struct_0('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_72, c_1799])).
% 5.51/2.22  tff(c_28, plain, (![A_10, B_22, C_28]: (~r1_lattices(A_10, B_22, '#skF_2'(A_10, B_22, C_28)) | r3_lattice3(A_10, B_22, C_28) | ~m1_subset_1(B_22, u1_struct_0(A_10)) | ~l3_lattices(A_10) | v2_struct_0(A_10))), inference(cnfTransformation, [status(thm)], [f_91])).
% 5.51/2.22  tff(c_1813, plain, (![C_28]: (r3_lattice3('#skF_5', k16_lattice3('#skF_5', '#skF_7'), C_28) | ~m1_subset_1(k16_lattice3('#skF_5', '#skF_7'), u1_struct_0('#skF_5')) | ~l3_lattices('#skF_5') | v2_struct_0('#skF_5') | ~r2_hidden('#skF_2'('#skF_5', k16_lattice3('#skF_5', '#skF_7'), C_28), '#skF_7') | ~m1_subset_1('#skF_2'('#skF_5', k16_lattice3('#skF_5', '#skF_7'), C_28), u1_struct_0('#skF_5')))), inference(resolution, [status(thm)], [c_1806, c_28])).
% 5.51/2.22  tff(c_1819, plain, (![C_28]: (r3_lattice3('#skF_5', k16_lattice3('#skF_5', '#skF_7'), C_28) | v2_struct_0('#skF_5') | ~r2_hidden('#skF_2'('#skF_5', k16_lattice3('#skF_5', '#skF_7'), C_28), '#skF_7') | ~m1_subset_1('#skF_2'('#skF_5', k16_lattice3('#skF_5', '#skF_7'), C_28), u1_struct_0('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_1214, c_1813])).
% 5.51/2.22  tff(c_1830, plain, (![C_592]: (r3_lattice3('#skF_5', k16_lattice3('#skF_5', '#skF_7'), C_592) | ~r2_hidden('#skF_2'('#skF_5', k16_lattice3('#skF_5', '#skF_7'), C_592), '#skF_7') | ~m1_subset_1('#skF_2'('#skF_5', k16_lattice3('#skF_5', '#skF_7'), C_592), u1_struct_0('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_72, c_1819])).
% 5.51/2.22  tff(c_1834, plain, (![C_28]: (~r2_hidden('#skF_2'('#skF_5', k16_lattice3('#skF_5', '#skF_7'), C_28), '#skF_7') | r3_lattice3('#skF_5', k16_lattice3('#skF_5', '#skF_7'), C_28) | ~m1_subset_1(k16_lattice3('#skF_5', '#skF_7'), u1_struct_0('#skF_5')) | ~l3_lattices('#skF_5') | v2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_32, c_1830])).
% 5.51/2.22  tff(c_1837, plain, (![C_28]: (~r2_hidden('#skF_2'('#skF_5', k16_lattice3('#skF_5', '#skF_7'), C_28), '#skF_7') | r3_lattice3('#skF_5', k16_lattice3('#skF_5', '#skF_7'), C_28) | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_1214, c_1834])).
% 5.51/2.22  tff(c_1839, plain, (![C_593]: (~r2_hidden('#skF_2'('#skF_5', k16_lattice3('#skF_5', '#skF_7'), C_593), '#skF_7') | r3_lattice3('#skF_5', k16_lattice3('#skF_5', '#skF_7'), C_593))), inference(negUnitSimplification, [status(thm)], [c_72, c_1837])).
% 5.51/2.22  tff(c_1843, plain, (![C_484]: (~r1_tarski('#skF_7', '#skF_7') | ~r1_tarski(C_484, '#skF_6') | r3_lattice3('#skF_5', k16_lattice3('#skF_5', '#skF_7'), C_484) | ~m1_subset_1(k16_lattice3('#skF_5', '#skF_7'), u1_struct_0('#skF_5')) | ~l3_lattices('#skF_5') | v2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_1323, c_1839])).
% 5.51/2.22  tff(c_1858, plain, (![C_484]: (~r1_tarski(C_484, '#skF_6') | r3_lattice3('#skF_5', k16_lattice3('#skF_5', '#skF_7'), C_484) | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_1214, c_1008, c_1843])).
% 5.51/2.22  tff(c_1872, plain, (![C_594]: (~r1_tarski(C_594, '#skF_6') | r3_lattice3('#skF_5', k16_lattice3('#skF_5', '#skF_7'), C_594))), inference(negUnitSimplification, [status(thm)], [c_72, c_1858])).
% 5.51/2.22  tff(c_1213, plain, (~r3_lattice3('#skF_5', k16_lattice3('#skF_5', '#skF_7'), '#skF_6')), inference(splitRight, [status(thm)], [c_1203])).
% 5.51/2.22  tff(c_1875, plain, (~r1_tarski('#skF_6', '#skF_6')), inference(resolution, [status(thm)], [c_1872, c_1213])).
% 5.51/2.22  tff(c_1879, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1008, c_1875])).
% 5.51/2.22  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.51/2.22  
% 5.51/2.22  Inference rules
% 5.51/2.22  ----------------------
% 5.51/2.22  #Ref     : 0
% 5.51/2.22  #Sup     : 376
% 5.51/2.22  #Fact    : 0
% 5.51/2.22  #Define  : 0
% 5.51/2.22  #Split   : 19
% 5.51/2.22  #Chain   : 0
% 5.51/2.22  #Close   : 0
% 5.51/2.22  
% 5.51/2.22  Ordering : KBO
% 5.51/2.22  
% 5.51/2.22  Simplification rules
% 5.51/2.22  ----------------------
% 5.51/2.22  #Subsume      : 65
% 5.51/2.22  #Demod        : 256
% 5.51/2.22  #Tautology    : 41
% 5.51/2.22  #SimpNegUnit  : 84
% 5.51/2.22  #BackRed      : 0
% 5.51/2.22  
% 5.51/2.22  #Partial instantiations: 0
% 5.51/2.22  #Strategies tried      : 1
% 5.51/2.22  
% 5.51/2.22  Timing (in seconds)
% 5.51/2.22  ----------------------
% 5.51/2.22  Preprocessing        : 0.52
% 5.51/2.22  Parsing              : 0.29
% 5.51/2.22  CNF conversion       : 0.04
% 5.51/2.22  Main loop            : 0.79
% 5.51/2.22  Inferencing          : 0.32
% 5.51/2.22  Reduction            : 0.21
% 5.51/2.22  Demodulation         : 0.14
% 5.51/2.22  BG Simplification    : 0.04
% 5.51/2.22  Subsumption          : 0.16
% 5.51/2.22  Abstraction          : 0.03
% 5.51/2.22  MUC search           : 0.00
% 5.51/2.22  Cooper               : 0.00
% 5.51/2.22  Total                : 1.38
% 5.51/2.22  Index Insertion      : 0.00
% 5.51/2.22  Index Deletion       : 0.00
% 5.51/2.22  Index Matching       : 0.00
% 5.51/2.22  BG Taut test         : 0.00
%------------------------------------------------------------------------------
