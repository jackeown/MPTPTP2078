%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:24:49 EST 2020

% Result     : Theorem 5.65s
% Output     : CNFRefutation 5.83s
% Verified   : 
% Statistics : Number of formulae       :  151 ( 525 expanded)
%              Number of leaves         :   42 ( 192 expanded)
%              Depth                    :   18
%              Number of atoms          :  442 (2176 expanded)
%              Number of equality atoms :    2 (   6 expanded)
%              Maximal formula depth    :   17 (   5 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r4_lattice3 > r3_lattices > r3_lattice3 > r1_lattices > r2_hidden > r1_tarski > m1_subset_1 > v9_lattices > v8_lattices > v7_lattices > v6_lattices > v5_lattices > v4_lattices > v4_lattice3 > v2_struct_0 > v10_lattices > l3_lattices > k16_lattice3 > k15_lattice3 > #nlpp > u1_struct_0 > #skF_4 > #skF_7 > #skF_6 > #skF_5 > #skF_2 > #skF_8 > #skF_3 > #skF_1

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

tff(v4_lattices,type,(
    v4_lattices: $i > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(v6_lattices,type,(
    v6_lattices: $i > $o )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

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

tff('#skF_8',type,(
    '#skF_8': $i )).

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

tff(f_209,negated_conjecture,(
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

tff(f_175,axiom,(
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

tff(f_192,axiom,(
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

tff(f_144,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & l3_lattices(A) )
     => m1_subset_1(k15_lattice3(A,B),u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k15_lattice3)).

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

tff(c_798,plain,(
    ! [A_454,B_455] :
      ( ~ r2_hidden('#skF_1'(A_454,B_455),B_455)
      | r1_tarski(A_454,B_455) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_803,plain,(
    ! [A_1] : r1_tarski(A_1,A_1) ),
    inference(resolution,[status(thm)],[c_6,c_798])).

tff(c_78,plain,(
    ~ v2_struct_0('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_209])).

tff(c_72,plain,(
    l3_lattices('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_209])).

tff(c_76,plain,(
    v10_lattices('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_209])).

tff(c_74,plain,(
    v4_lattice3('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_209])).

tff(c_54,plain,(
    ! [A_68,B_69] :
      ( m1_subset_1(k16_lattice3(A_68,B_69),u1_struct_0(A_68))
      | ~ l3_lattices(A_68)
      | v2_struct_0(A_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_882,plain,(
    ! [A_506,C_507] :
      ( r3_lattice3(A_506,k16_lattice3(A_506,C_507),C_507)
      | ~ m1_subset_1(k16_lattice3(A_506,C_507),u1_struct_0(A_506))
      | ~ l3_lattices(A_506)
      | ~ v4_lattice3(A_506)
      | ~ v10_lattices(A_506)
      | v2_struct_0(A_506) ) ),
    inference(cnfTransformation,[status(thm)],[f_175])).

tff(c_885,plain,(
    ! [A_68,B_69] :
      ( r3_lattice3(A_68,k16_lattice3(A_68,B_69),B_69)
      | ~ v4_lattice3(A_68)
      | ~ v10_lattices(A_68)
      | ~ l3_lattices(A_68)
      | v2_struct_0(A_68) ) ),
    inference(resolution,[status(thm)],[c_54,c_882])).

tff(c_887,plain,(
    ! [A_510,B_511,C_512] :
      ( r3_lattices(A_510,B_511,k16_lattice3(A_510,C_512))
      | ~ r3_lattice3(A_510,B_511,C_512)
      | ~ m1_subset_1(B_511,u1_struct_0(A_510))
      | ~ l3_lattices(A_510)
      | ~ v4_lattice3(A_510)
      | ~ v10_lattices(A_510)
      | v2_struct_0(A_510) ) ),
    inference(cnfTransformation,[status(thm)],[f_192])).

tff(c_8,plain,(
    ! [A_6] :
      ( v9_lattices(A_6)
      | ~ v10_lattices(A_6)
      | v2_struct_0(A_6)
      | ~ l3_lattices(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_52,plain,(
    ! [A_66,B_67] :
      ( m1_subset_1(k15_lattice3(A_66,B_67),u1_struct_0(A_66))
      | ~ l3_lattices(A_66)
      | v2_struct_0(A_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_10,plain,(
    ! [A_6] :
      ( v8_lattices(A_6)
      | ~ v10_lattices(A_6)
      | v2_struct_0(A_6)
      | ~ l3_lattices(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_87,plain,(
    ! [A_109,B_110] :
      ( ~ r2_hidden('#skF_1'(A_109,B_110),B_110)
      | r1_tarski(A_109,B_110) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_92,plain,(
    ! [A_1] : r1_tarski(A_1,A_1) ),
    inference(resolution,[status(thm)],[c_6,c_87])).

tff(c_170,plain,(
    ! [A_160,B_161] :
      ( r4_lattice3(A_160,k15_lattice3(A_160,B_161),B_161)
      | ~ m1_subset_1(k15_lattice3(A_160,B_161),u1_struct_0(A_160))
      | ~ v4_lattice3(A_160)
      | ~ v10_lattices(A_160)
      | ~ l3_lattices(A_160)
      | v2_struct_0(A_160) ) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_173,plain,(
    ! [A_66,B_67] :
      ( r4_lattice3(A_66,k15_lattice3(A_66,B_67),B_67)
      | ~ v4_lattice3(A_66)
      | ~ v10_lattices(A_66)
      | ~ l3_lattices(A_66)
      | v2_struct_0(A_66) ) ),
    inference(resolution,[status(thm)],[c_52,c_170])).

tff(c_362,plain,(
    ! [A_249,B_250,D_251] :
      ( r1_lattices(A_249,k15_lattice3(A_249,B_250),D_251)
      | ~ r4_lattice3(A_249,D_251,B_250)
      | ~ m1_subset_1(D_251,u1_struct_0(A_249))
      | ~ m1_subset_1(k15_lattice3(A_249,B_250),u1_struct_0(A_249))
      | ~ v4_lattice3(A_249)
      | ~ v10_lattices(A_249)
      | ~ l3_lattices(A_249)
      | v2_struct_0(A_249) ) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_366,plain,(
    ! [A_252,B_253,D_254] :
      ( r1_lattices(A_252,k15_lattice3(A_252,B_253),D_254)
      | ~ r4_lattice3(A_252,D_254,B_253)
      | ~ m1_subset_1(D_254,u1_struct_0(A_252))
      | ~ v4_lattice3(A_252)
      | ~ v10_lattices(A_252)
      | ~ l3_lattices(A_252)
      | v2_struct_0(A_252) ) ),
    inference(resolution,[status(thm)],[c_52,c_362])).

tff(c_14,plain,(
    ! [A_6] :
      ( v6_lattices(A_6)
      | ~ v10_lattices(A_6)
      | v2_struct_0(A_6)
      | ~ l3_lattices(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_268,plain,(
    ! [A_199,B_200,C_201] :
      ( r3_lattices(A_199,B_200,C_201)
      | ~ r1_lattices(A_199,B_200,C_201)
      | ~ m1_subset_1(C_201,u1_struct_0(A_199))
      | ~ m1_subset_1(B_200,u1_struct_0(A_199))
      | ~ l3_lattices(A_199)
      | ~ v9_lattices(A_199)
      | ~ v8_lattices(A_199)
      | ~ v6_lattices(A_199)
      | v2_struct_0(A_199) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_306,plain,(
    ! [A_217,B_218,B_219] :
      ( r3_lattices(A_217,B_218,k15_lattice3(A_217,B_219))
      | ~ r1_lattices(A_217,B_218,k15_lattice3(A_217,B_219))
      | ~ m1_subset_1(B_218,u1_struct_0(A_217))
      | ~ v9_lattices(A_217)
      | ~ v8_lattices(A_217)
      | ~ v6_lattices(A_217)
      | ~ l3_lattices(A_217)
      | v2_struct_0(A_217) ) ),
    inference(resolution,[status(thm)],[c_52,c_268])).

tff(c_68,plain,
    ( ~ r3_lattices('#skF_6',k16_lattice3('#skF_6','#skF_8'),k16_lattice3('#skF_6','#skF_7'))
    | ~ r3_lattices('#skF_6',k15_lattice3('#skF_6','#skF_7'),k15_lattice3('#skF_6','#skF_8')) ),
    inference(cnfTransformation,[status(thm)],[f_209])).

tff(c_83,plain,(
    ~ r3_lattices('#skF_6',k15_lattice3('#skF_6','#skF_7'),k15_lattice3('#skF_6','#skF_8')) ),
    inference(splitLeft,[status(thm)],[c_68])).

tff(c_311,plain,
    ( ~ r1_lattices('#skF_6',k15_lattice3('#skF_6','#skF_7'),k15_lattice3('#skF_6','#skF_8'))
    | ~ m1_subset_1(k15_lattice3('#skF_6','#skF_7'),u1_struct_0('#skF_6'))
    | ~ v9_lattices('#skF_6')
    | ~ v8_lattices('#skF_6')
    | ~ v6_lattices('#skF_6')
    | ~ l3_lattices('#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_306,c_83])).

tff(c_315,plain,
    ( ~ r1_lattices('#skF_6',k15_lattice3('#skF_6','#skF_7'),k15_lattice3('#skF_6','#skF_8'))
    | ~ m1_subset_1(k15_lattice3('#skF_6','#skF_7'),u1_struct_0('#skF_6'))
    | ~ v9_lattices('#skF_6')
    | ~ v8_lattices('#skF_6')
    | ~ v6_lattices('#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_311])).

tff(c_316,plain,
    ( ~ r1_lattices('#skF_6',k15_lattice3('#skF_6','#skF_7'),k15_lattice3('#skF_6','#skF_8'))
    | ~ m1_subset_1(k15_lattice3('#skF_6','#skF_7'),u1_struct_0('#skF_6'))
    | ~ v9_lattices('#skF_6')
    | ~ v8_lattices('#skF_6')
    | ~ v6_lattices('#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_315])).

tff(c_317,plain,(
    ~ v6_lattices('#skF_6') ),
    inference(splitLeft,[status(thm)],[c_316])).

tff(c_320,plain,
    ( ~ v10_lattices('#skF_6')
    | v2_struct_0('#skF_6')
    | ~ l3_lattices('#skF_6') ),
    inference(resolution,[status(thm)],[c_14,c_317])).

tff(c_323,plain,(
    v2_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_76,c_320])).

tff(c_325,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_323])).

tff(c_326,plain,
    ( ~ v8_lattices('#skF_6')
    | ~ v9_lattices('#skF_6')
    | ~ m1_subset_1(k15_lattice3('#skF_6','#skF_7'),u1_struct_0('#skF_6'))
    | ~ r1_lattices('#skF_6',k15_lattice3('#skF_6','#skF_7'),k15_lattice3('#skF_6','#skF_8')) ),
    inference(splitRight,[status(thm)],[c_316])).

tff(c_328,plain,(
    ~ r1_lattices('#skF_6',k15_lattice3('#skF_6','#skF_7'),k15_lattice3('#skF_6','#skF_8')) ),
    inference(splitLeft,[status(thm)],[c_326])).

tff(c_373,plain,
    ( ~ r4_lattice3('#skF_6',k15_lattice3('#skF_6','#skF_8'),'#skF_7')
    | ~ m1_subset_1(k15_lattice3('#skF_6','#skF_8'),u1_struct_0('#skF_6'))
    | ~ v4_lattice3('#skF_6')
    | ~ v10_lattices('#skF_6')
    | ~ l3_lattices('#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_366,c_328])).

tff(c_381,plain,
    ( ~ r4_lattice3('#skF_6',k15_lattice3('#skF_6','#skF_8'),'#skF_7')
    | ~ m1_subset_1(k15_lattice3('#skF_6','#skF_8'),u1_struct_0('#skF_6'))
    | v2_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_76,c_74,c_373])).

tff(c_382,plain,
    ( ~ r4_lattice3('#skF_6',k15_lattice3('#skF_6','#skF_8'),'#skF_7')
    | ~ m1_subset_1(k15_lattice3('#skF_6','#skF_8'),u1_struct_0('#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_381])).

tff(c_384,plain,(
    ~ m1_subset_1(k15_lattice3('#skF_6','#skF_8'),u1_struct_0('#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_382])).

tff(c_387,plain,
    ( ~ l3_lattices('#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_52,c_384])).

tff(c_390,plain,(
    v2_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_387])).

tff(c_392,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_390])).

tff(c_394,plain,(
    m1_subset_1(k15_lattice3('#skF_6','#skF_8'),u1_struct_0('#skF_6')) ),
    inference(splitRight,[status(thm)],[c_382])).

tff(c_40,plain,(
    ! [A_32,B_44,C_50] :
      ( m1_subset_1('#skF_3'(A_32,B_44,C_50),u1_struct_0(A_32))
      | r4_lattice3(A_32,B_44,C_50)
      | ~ m1_subset_1(B_44,u1_struct_0(A_32))
      | ~ l3_lattices(A_32)
      | v2_struct_0(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_70,plain,(
    r1_tarski('#skF_7','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_209])).

tff(c_100,plain,(
    ! [A_119,B_120,C_121] :
      ( r2_hidden('#skF_3'(A_119,B_120,C_121),C_121)
      | r4_lattice3(A_119,B_120,C_121)
      | ~ m1_subset_1(B_120,u1_struct_0(A_119))
      | ~ l3_lattices(A_119)
      | v2_struct_0(A_119) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_180,plain,(
    ! [A_171,B_172,C_173,B_174] :
      ( r2_hidden('#skF_3'(A_171,B_172,C_173),B_174)
      | ~ r1_tarski(C_173,B_174)
      | r4_lattice3(A_171,B_172,C_173)
      | ~ m1_subset_1(B_172,u1_struct_0(A_171))
      | ~ l3_lattices(A_171)
      | v2_struct_0(A_171) ) ),
    inference(resolution,[status(thm)],[c_100,c_2])).

tff(c_234,plain,(
    ! [B_185,A_186,C_183,B_184,B_187] :
      ( r2_hidden('#skF_3'(A_186,B_187,C_183),B_185)
      | ~ r1_tarski(B_184,B_185)
      | ~ r1_tarski(C_183,B_184)
      | r4_lattice3(A_186,B_187,C_183)
      | ~ m1_subset_1(B_187,u1_struct_0(A_186))
      | ~ l3_lattices(A_186)
      | v2_struct_0(A_186) ) ),
    inference(resolution,[status(thm)],[c_180,c_2])).

tff(c_241,plain,(
    ! [A_188,B_189,C_190] :
      ( r2_hidden('#skF_3'(A_188,B_189,C_190),'#skF_8')
      | ~ r1_tarski(C_190,'#skF_7')
      | r4_lattice3(A_188,B_189,C_190)
      | ~ m1_subset_1(B_189,u1_struct_0(A_188))
      | ~ l3_lattices(A_188)
      | v2_struct_0(A_188) ) ),
    inference(resolution,[status(thm)],[c_70,c_234])).

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

tff(c_673,plain,(
    ! [A_420,B_421,C_424,B_422,A_423] :
      ( r1_lattices(A_420,'#skF_3'(A_423,B_421,C_424),B_422)
      | ~ m1_subset_1('#skF_3'(A_423,B_421,C_424),u1_struct_0(A_420))
      | ~ r4_lattice3(A_420,B_422,'#skF_8')
      | ~ m1_subset_1(B_422,u1_struct_0(A_420))
      | ~ l3_lattices(A_420)
      | v2_struct_0(A_420)
      | ~ r1_tarski(C_424,'#skF_7')
      | r4_lattice3(A_423,B_421,C_424)
      | ~ m1_subset_1(B_421,u1_struct_0(A_423))
      | ~ l3_lattices(A_423)
      | v2_struct_0(A_423) ) ),
    inference(resolution,[status(thm)],[c_241,c_34])).

tff(c_679,plain,(
    ! [A_433,B_434,C_435,B_436] :
      ( r1_lattices(A_433,'#skF_3'(A_433,B_434,C_435),B_436)
      | ~ r4_lattice3(A_433,B_436,'#skF_8')
      | ~ m1_subset_1(B_436,u1_struct_0(A_433))
      | ~ r1_tarski(C_435,'#skF_7')
      | r4_lattice3(A_433,B_434,C_435)
      | ~ m1_subset_1(B_434,u1_struct_0(A_433))
      | ~ l3_lattices(A_433)
      | v2_struct_0(A_433) ) ),
    inference(resolution,[status(thm)],[c_40,c_673])).

tff(c_36,plain,(
    ! [A_32,B_44,C_50] :
      ( ~ r1_lattices(A_32,'#skF_3'(A_32,B_44,C_50),B_44)
      | r4_lattice3(A_32,B_44,C_50)
      | ~ m1_subset_1(B_44,u1_struct_0(A_32))
      | ~ l3_lattices(A_32)
      | v2_struct_0(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_695,plain,(
    ! [A_437,B_438,C_439] :
      ( ~ r4_lattice3(A_437,B_438,'#skF_8')
      | ~ r1_tarski(C_439,'#skF_7')
      | r4_lattice3(A_437,B_438,C_439)
      | ~ m1_subset_1(B_438,u1_struct_0(A_437))
      | ~ l3_lattices(A_437)
      | v2_struct_0(A_437) ) ),
    inference(resolution,[status(thm)],[c_679,c_36])).

tff(c_697,plain,(
    ! [C_439] :
      ( ~ r4_lattice3('#skF_6',k15_lattice3('#skF_6','#skF_8'),'#skF_8')
      | ~ r1_tarski(C_439,'#skF_7')
      | r4_lattice3('#skF_6',k15_lattice3('#skF_6','#skF_8'),C_439)
      | ~ l3_lattices('#skF_6')
      | v2_struct_0('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_394,c_695])).

tff(c_712,plain,(
    ! [C_439] :
      ( ~ r4_lattice3('#skF_6',k15_lattice3('#skF_6','#skF_8'),'#skF_8')
      | ~ r1_tarski(C_439,'#skF_7')
      | r4_lattice3('#skF_6',k15_lattice3('#skF_6','#skF_8'),C_439)
      | v2_struct_0('#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_697])).

tff(c_713,plain,(
    ! [C_439] :
      ( ~ r4_lattice3('#skF_6',k15_lattice3('#skF_6','#skF_8'),'#skF_8')
      | ~ r1_tarski(C_439,'#skF_7')
      | r4_lattice3('#skF_6',k15_lattice3('#skF_6','#skF_8'),C_439) ) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_712])).

tff(c_720,plain,(
    ~ r4_lattice3('#skF_6',k15_lattice3('#skF_6','#skF_8'),'#skF_8') ),
    inference(splitLeft,[status(thm)],[c_713])).

tff(c_729,plain,
    ( ~ v4_lattice3('#skF_6')
    | ~ v10_lattices('#skF_6')
    | ~ l3_lattices('#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_173,c_720])).

tff(c_732,plain,(
    v2_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_76,c_74,c_729])).

tff(c_734,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_732])).

tff(c_743,plain,(
    ! [C_443] :
      ( ~ r1_tarski(C_443,'#skF_7')
      | r4_lattice3('#skF_6',k15_lattice3('#skF_6','#skF_8'),C_443) ) ),
    inference(splitRight,[status(thm)],[c_713])).

tff(c_393,plain,(
    ~ r4_lattice3('#skF_6',k15_lattice3('#skF_6','#skF_8'),'#skF_7') ),
    inference(splitRight,[status(thm)],[c_382])).

tff(c_748,plain,(
    ~ r1_tarski('#skF_7','#skF_7') ),
    inference(resolution,[status(thm)],[c_743,c_393])).

tff(c_756,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_748])).

tff(c_757,plain,
    ( ~ m1_subset_1(k15_lattice3('#skF_6','#skF_7'),u1_struct_0('#skF_6'))
    | ~ v9_lattices('#skF_6')
    | ~ v8_lattices('#skF_6') ),
    inference(splitRight,[status(thm)],[c_326])).

tff(c_760,plain,(
    ~ v8_lattices('#skF_6') ),
    inference(splitLeft,[status(thm)],[c_757])).

tff(c_763,plain,
    ( ~ v10_lattices('#skF_6')
    | v2_struct_0('#skF_6')
    | ~ l3_lattices('#skF_6') ),
    inference(resolution,[status(thm)],[c_10,c_760])).

tff(c_766,plain,(
    v2_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_76,c_763])).

tff(c_768,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_766])).

tff(c_769,plain,
    ( ~ v9_lattices('#skF_6')
    | ~ m1_subset_1(k15_lattice3('#skF_6','#skF_7'),u1_struct_0('#skF_6')) ),
    inference(splitRight,[status(thm)],[c_757])).

tff(c_771,plain,(
    ~ m1_subset_1(k15_lattice3('#skF_6','#skF_7'),u1_struct_0('#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_769])).

tff(c_778,plain,
    ( ~ l3_lattices('#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_52,c_771])).

tff(c_781,plain,(
    v2_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_778])).

tff(c_783,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_781])).

tff(c_784,plain,(
    ~ v9_lattices('#skF_6') ),
    inference(splitRight,[status(thm)],[c_769])).

tff(c_788,plain,
    ( ~ v10_lattices('#skF_6')
    | v2_struct_0('#skF_6')
    | ~ l3_lattices('#skF_6') ),
    inference(resolution,[status(thm)],[c_8,c_784])).

tff(c_791,plain,(
    v2_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_76,c_788])).

tff(c_793,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_791])).

tff(c_794,plain,(
    ~ r3_lattices('#skF_6',k16_lattice3('#skF_6','#skF_8'),k16_lattice3('#skF_6','#skF_7')) ),
    inference(splitRight,[status(thm)],[c_68])).

tff(c_890,plain,
    ( ~ r3_lattice3('#skF_6',k16_lattice3('#skF_6','#skF_8'),'#skF_7')
    | ~ m1_subset_1(k16_lattice3('#skF_6','#skF_8'),u1_struct_0('#skF_6'))
    | ~ l3_lattices('#skF_6')
    | ~ v4_lattice3('#skF_6')
    | ~ v10_lattices('#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_887,c_794])).

tff(c_893,plain,
    ( ~ r3_lattice3('#skF_6',k16_lattice3('#skF_6','#skF_8'),'#skF_7')
    | ~ m1_subset_1(k16_lattice3('#skF_6','#skF_8'),u1_struct_0('#skF_6'))
    | v2_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_72,c_890])).

tff(c_894,plain,
    ( ~ r3_lattice3('#skF_6',k16_lattice3('#skF_6','#skF_8'),'#skF_7')
    | ~ m1_subset_1(k16_lattice3('#skF_6','#skF_8'),u1_struct_0('#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_893])).

tff(c_895,plain,(
    ~ m1_subset_1(k16_lattice3('#skF_6','#skF_8'),u1_struct_0('#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_894])).

tff(c_898,plain,
    ( ~ l3_lattices('#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_54,c_895])).

tff(c_901,plain,(
    v2_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_898])).

tff(c_903,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_901])).

tff(c_905,plain,(
    m1_subset_1(k16_lattice3('#skF_6','#skF_8'),u1_struct_0('#skF_6')) ),
    inference(splitRight,[status(thm)],[c_894])).

tff(c_32,plain,(
    ! [A_10,B_22,C_28] :
      ( m1_subset_1('#skF_2'(A_10,B_22,C_28),u1_struct_0(A_10))
      | r3_lattice3(A_10,B_22,C_28)
      | ~ m1_subset_1(B_22,u1_struct_0(A_10))
      | ~ l3_lattices(A_10)
      | v2_struct_0(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_821,plain,(
    ! [A_468,B_469,C_470] :
      ( r2_hidden('#skF_2'(A_468,B_469,C_470),C_470)
      | r3_lattice3(A_468,B_469,C_470)
      | ~ m1_subset_1(B_469,u1_struct_0(A_468))
      | ~ l3_lattices(A_468)
      | v2_struct_0(A_468) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_906,plain,(
    ! [A_513,B_514,C_515,B_516] :
      ( r2_hidden('#skF_2'(A_513,B_514,C_515),B_516)
      | ~ r1_tarski(C_515,B_516)
      | r3_lattice3(A_513,B_514,C_515)
      | ~ m1_subset_1(B_514,u1_struct_0(A_513))
      | ~ l3_lattices(A_513)
      | v2_struct_0(A_513) ) ),
    inference(resolution,[status(thm)],[c_821,c_2])).

tff(c_991,plain,(
    ! [B_541,A_543,B_544,C_542,B_540] :
      ( r2_hidden('#skF_2'(A_543,B_541,C_542),B_544)
      | ~ r1_tarski(B_540,B_544)
      | ~ r1_tarski(C_542,B_540)
      | r3_lattice3(A_543,B_541,C_542)
      | ~ m1_subset_1(B_541,u1_struct_0(A_543))
      | ~ l3_lattices(A_543)
      | v2_struct_0(A_543) ) ),
    inference(resolution,[status(thm)],[c_906,c_2])).

tff(c_998,plain,(
    ! [A_545,B_546,C_547] :
      ( r2_hidden('#skF_2'(A_545,B_546,C_547),'#skF_8')
      | ~ r1_tarski(C_547,'#skF_7')
      | r3_lattice3(A_545,B_546,C_547)
      | ~ m1_subset_1(B_546,u1_struct_0(A_545))
      | ~ l3_lattices(A_545)
      | v2_struct_0(A_545) ) ),
    inference(resolution,[status(thm)],[c_70,c_991])).

tff(c_26,plain,(
    ! [A_10,B_22,D_31,C_28] :
      ( r1_lattices(A_10,B_22,D_31)
      | ~ r2_hidden(D_31,C_28)
      | ~ m1_subset_1(D_31,u1_struct_0(A_10))
      | ~ r3_lattice3(A_10,B_22,C_28)
      | ~ m1_subset_1(B_22,u1_struct_0(A_10))
      | ~ l3_lattices(A_10)
      | v2_struct_0(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_1587,plain,(
    ! [B_736,A_739,C_737,B_738,A_735] :
      ( r1_lattices(A_739,B_738,'#skF_2'(A_735,B_736,C_737))
      | ~ m1_subset_1('#skF_2'(A_735,B_736,C_737),u1_struct_0(A_739))
      | ~ r3_lattice3(A_739,B_738,'#skF_8')
      | ~ m1_subset_1(B_738,u1_struct_0(A_739))
      | ~ l3_lattices(A_739)
      | v2_struct_0(A_739)
      | ~ r1_tarski(C_737,'#skF_7')
      | r3_lattice3(A_735,B_736,C_737)
      | ~ m1_subset_1(B_736,u1_struct_0(A_735))
      | ~ l3_lattices(A_735)
      | v2_struct_0(A_735) ) ),
    inference(resolution,[status(thm)],[c_998,c_26])).

tff(c_1591,plain,(
    ! [A_740,B_741,B_742,C_743] :
      ( r1_lattices(A_740,B_741,'#skF_2'(A_740,B_742,C_743))
      | ~ r3_lattice3(A_740,B_741,'#skF_8')
      | ~ m1_subset_1(B_741,u1_struct_0(A_740))
      | ~ r1_tarski(C_743,'#skF_7')
      | r3_lattice3(A_740,B_742,C_743)
      | ~ m1_subset_1(B_742,u1_struct_0(A_740))
      | ~ l3_lattices(A_740)
      | v2_struct_0(A_740) ) ),
    inference(resolution,[status(thm)],[c_32,c_1587])).

tff(c_28,plain,(
    ! [A_10,B_22,C_28] :
      ( ~ r1_lattices(A_10,B_22,'#skF_2'(A_10,B_22,C_28))
      | r3_lattice3(A_10,B_22,C_28)
      | ~ m1_subset_1(B_22,u1_struct_0(A_10))
      | ~ l3_lattices(A_10)
      | v2_struct_0(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_1602,plain,(
    ! [A_744,B_745,C_746] :
      ( ~ r3_lattice3(A_744,B_745,'#skF_8')
      | ~ r1_tarski(C_746,'#skF_7')
      | r3_lattice3(A_744,B_745,C_746)
      | ~ m1_subset_1(B_745,u1_struct_0(A_744))
      | ~ l3_lattices(A_744)
      | v2_struct_0(A_744) ) ),
    inference(resolution,[status(thm)],[c_1591,c_28])).

tff(c_1612,plain,(
    ! [C_746] :
      ( ~ r3_lattice3('#skF_6',k16_lattice3('#skF_6','#skF_8'),'#skF_8')
      | ~ r1_tarski(C_746,'#skF_7')
      | r3_lattice3('#skF_6',k16_lattice3('#skF_6','#skF_8'),C_746)
      | ~ l3_lattices('#skF_6')
      | v2_struct_0('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_905,c_1602])).

tff(c_1633,plain,(
    ! [C_746] :
      ( ~ r3_lattice3('#skF_6',k16_lattice3('#skF_6','#skF_8'),'#skF_8')
      | ~ r1_tarski(C_746,'#skF_7')
      | r3_lattice3('#skF_6',k16_lattice3('#skF_6','#skF_8'),C_746)
      | v2_struct_0('#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_1612])).

tff(c_1634,plain,(
    ! [C_746] :
      ( ~ r3_lattice3('#skF_6',k16_lattice3('#skF_6','#skF_8'),'#skF_8')
      | ~ r1_tarski(C_746,'#skF_7')
      | r3_lattice3('#skF_6',k16_lattice3('#skF_6','#skF_8'),C_746) ) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_1633])).

tff(c_1645,plain,(
    ~ r3_lattice3('#skF_6',k16_lattice3('#skF_6','#skF_8'),'#skF_8') ),
    inference(splitLeft,[status(thm)],[c_1634])).

tff(c_1648,plain,
    ( ~ v4_lattice3('#skF_6')
    | ~ v10_lattices('#skF_6')
    | ~ l3_lattices('#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_885,c_1645])).

tff(c_1651,plain,(
    v2_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_76,c_74,c_1648])).

tff(c_1653,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_1651])).

tff(c_1656,plain,(
    ! [C_752] :
      ( ~ r1_tarski(C_752,'#skF_7')
      | r3_lattice3('#skF_6',k16_lattice3('#skF_6','#skF_8'),C_752) ) ),
    inference(splitRight,[status(thm)],[c_1634])).

tff(c_904,plain,(
    ~ r3_lattice3('#skF_6',k16_lattice3('#skF_6','#skF_8'),'#skF_7') ),
    inference(splitRight,[status(thm)],[c_894])).

tff(c_1659,plain,(
    ~ r1_tarski('#skF_7','#skF_7') ),
    inference(resolution,[status(thm)],[c_1656,c_904])).

tff(c_1663,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_803,c_1659])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:59:56 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.65/2.08  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.71/2.09  
% 5.71/2.09  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.71/2.10  %$ r4_lattice3 > r3_lattices > r3_lattice3 > r1_lattices > r2_hidden > r1_tarski > m1_subset_1 > v9_lattices > v8_lattices > v7_lattices > v6_lattices > v5_lattices > v4_lattices > v4_lattice3 > v2_struct_0 > v10_lattices > l3_lattices > k16_lattice3 > k15_lattice3 > #nlpp > u1_struct_0 > #skF_4 > #skF_7 > #skF_6 > #skF_5 > #skF_2 > #skF_8 > #skF_3 > #skF_1
% 5.71/2.10  
% 5.71/2.10  %Foreground sorts:
% 5.71/2.10  
% 5.71/2.10  
% 5.71/2.10  %Background operators:
% 5.71/2.10  
% 5.71/2.10  
% 5.71/2.10  %Foreground operators:
% 5.71/2.10  tff(l3_lattices, type, l3_lattices: $i > $o).
% 5.71/2.10  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 5.71/2.10  tff(r3_lattices, type, r3_lattices: ($i * $i * $i) > $o).
% 5.71/2.10  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.71/2.10  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.71/2.10  tff(k16_lattice3, type, k16_lattice3: ($i * $i) > $i).
% 5.71/2.10  tff(k15_lattice3, type, k15_lattice3: ($i * $i) > $i).
% 5.71/2.10  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 5.71/2.10  tff('#skF_7', type, '#skF_7': $i).
% 5.71/2.10  tff(r1_lattices, type, r1_lattices: ($i * $i * $i) > $o).
% 5.71/2.10  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.71/2.10  tff(v4_lattices, type, v4_lattices: $i > $o).
% 5.71/2.10  tff('#skF_6', type, '#skF_6': $i).
% 5.71/2.10  tff(v6_lattices, type, v6_lattices: $i > $o).
% 5.71/2.10  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 5.71/2.10  tff(v9_lattices, type, v9_lattices: $i > $o).
% 5.71/2.10  tff(r4_lattice3, type, r4_lattice3: ($i * $i * $i) > $o).
% 5.71/2.10  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 5.71/2.10  tff(v4_lattice3, type, v4_lattice3: $i > $o).
% 5.71/2.10  tff(v5_lattices, type, v5_lattices: $i > $o).
% 5.71/2.10  tff(v10_lattices, type, v10_lattices: $i > $o).
% 5.71/2.10  tff('#skF_8', type, '#skF_8': $i).
% 5.71/2.10  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.71/2.10  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 5.71/2.10  tff(v8_lattices, type, v8_lattices: $i > $o).
% 5.71/2.10  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.71/2.10  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 5.71/2.10  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 5.71/2.10  tff(r3_lattice3, type, r3_lattice3: ($i * $i * $i) > $o).
% 5.71/2.10  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.71/2.10  tff(v7_lattices, type, v7_lattices: $i > $o).
% 5.71/2.10  
% 5.83/2.12  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 5.83/2.12  tff(f_209, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v10_lattices(A)) & v4_lattice3(A)) & l3_lattices(A)) => (![B, C]: (r1_tarski(B, C) => (r3_lattices(A, k15_lattice3(A, B), k15_lattice3(A, C)) & r3_lattices(A, k16_lattice3(A, C), k16_lattice3(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_lattice3)).
% 5.83/2.12  tff(f_151, axiom, (![A, B]: ((~v2_struct_0(A) & l3_lattices(A)) => m1_subset_1(k16_lattice3(A, B), u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k16_lattice3)).
% 5.83/2.12  tff(f_175, axiom, (![A]: ((((~v2_struct_0(A) & v10_lattices(A)) & v4_lattice3(A)) & l3_lattices(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: ((B = k16_lattice3(A, C)) <=> (r3_lattice3(A, B, C) & (![D]: (m1_subset_1(D, u1_struct_0(A)) => (r3_lattice3(A, D, C) => r3_lattices(A, D, B))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t34_lattice3)).
% 5.83/2.12  tff(f_192, axiom, (![A]: ((((~v2_struct_0(A) & v10_lattices(A)) & v4_lattice3(A)) & l3_lattices(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (r3_lattice3(A, B, C) => r3_lattices(A, B, k16_lattice3(A, C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t40_lattice3)).
% 5.83/2.12  tff(f_54, axiom, (![A]: (l3_lattices(A) => ((~v2_struct_0(A) & v10_lattices(A)) => ((((((~v2_struct_0(A) & v4_lattices(A)) & v5_lattices(A)) & v6_lattices(A)) & v7_lattices(A)) & v8_lattices(A)) & v9_lattices(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_lattices)).
% 5.83/2.12  tff(f_144, axiom, (![A, B]: ((~v2_struct_0(A) & l3_lattices(A)) => m1_subset_1(k15_lattice3(A, B), u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k15_lattice3)).
% 5.83/2.12  tff(f_137, axiom, (![A]: ((~v2_struct_0(A) & l3_lattices(A)) => ((((~v2_struct_0(A) & v10_lattices(A)) & v4_lattice3(A)) & l3_lattices(A)) => (![B, C]: (m1_subset_1(C, u1_struct_0(A)) => ((C = k15_lattice3(A, B)) <=> (r4_lattice3(A, C, B) & (![D]: (m1_subset_1(D, u1_struct_0(A)) => (r4_lattice3(A, D, B) => r1_lattices(A, C, D))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d21_lattice3)).
% 5.83/2.12  tff(f_73, axiom, (![A, B, C]: (((((((~v2_struct_0(A) & v6_lattices(A)) & v8_lattices(A)) & v9_lattices(A)) & l3_lattices(A)) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => (r3_lattices(A, B, C) <=> r1_lattices(A, B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r3_lattices)).
% 5.83/2.12  tff(f_109, axiom, (![A]: ((~v2_struct_0(A) & l3_lattices(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (r4_lattice3(A, B, C) <=> (![D]: (m1_subset_1(D, u1_struct_0(A)) => (r2_hidden(D, C) => r1_lattices(A, D, B)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d17_lattice3)).
% 5.83/2.12  tff(f_91, axiom, (![A]: ((~v2_struct_0(A) & l3_lattices(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (r3_lattice3(A, B, C) <=> (![D]: (m1_subset_1(D, u1_struct_0(A)) => (r2_hidden(D, C) => r1_lattices(A, B, D)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d16_lattice3)).
% 5.83/2.12  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.83/2.12  tff(c_798, plain, (![A_454, B_455]: (~r2_hidden('#skF_1'(A_454, B_455), B_455) | r1_tarski(A_454, B_455))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.83/2.12  tff(c_803, plain, (![A_1]: (r1_tarski(A_1, A_1))), inference(resolution, [status(thm)], [c_6, c_798])).
% 5.83/2.12  tff(c_78, plain, (~v2_struct_0('#skF_6')), inference(cnfTransformation, [status(thm)], [f_209])).
% 5.83/2.12  tff(c_72, plain, (l3_lattices('#skF_6')), inference(cnfTransformation, [status(thm)], [f_209])).
% 5.83/2.12  tff(c_76, plain, (v10_lattices('#skF_6')), inference(cnfTransformation, [status(thm)], [f_209])).
% 5.83/2.12  tff(c_74, plain, (v4_lattice3('#skF_6')), inference(cnfTransformation, [status(thm)], [f_209])).
% 5.83/2.12  tff(c_54, plain, (![A_68, B_69]: (m1_subset_1(k16_lattice3(A_68, B_69), u1_struct_0(A_68)) | ~l3_lattices(A_68) | v2_struct_0(A_68))), inference(cnfTransformation, [status(thm)], [f_151])).
% 5.83/2.12  tff(c_882, plain, (![A_506, C_507]: (r3_lattice3(A_506, k16_lattice3(A_506, C_507), C_507) | ~m1_subset_1(k16_lattice3(A_506, C_507), u1_struct_0(A_506)) | ~l3_lattices(A_506) | ~v4_lattice3(A_506) | ~v10_lattices(A_506) | v2_struct_0(A_506))), inference(cnfTransformation, [status(thm)], [f_175])).
% 5.83/2.12  tff(c_885, plain, (![A_68, B_69]: (r3_lattice3(A_68, k16_lattice3(A_68, B_69), B_69) | ~v4_lattice3(A_68) | ~v10_lattices(A_68) | ~l3_lattices(A_68) | v2_struct_0(A_68))), inference(resolution, [status(thm)], [c_54, c_882])).
% 5.83/2.12  tff(c_887, plain, (![A_510, B_511, C_512]: (r3_lattices(A_510, B_511, k16_lattice3(A_510, C_512)) | ~r3_lattice3(A_510, B_511, C_512) | ~m1_subset_1(B_511, u1_struct_0(A_510)) | ~l3_lattices(A_510) | ~v4_lattice3(A_510) | ~v10_lattices(A_510) | v2_struct_0(A_510))), inference(cnfTransformation, [status(thm)], [f_192])).
% 5.83/2.12  tff(c_8, plain, (![A_6]: (v9_lattices(A_6) | ~v10_lattices(A_6) | v2_struct_0(A_6) | ~l3_lattices(A_6))), inference(cnfTransformation, [status(thm)], [f_54])).
% 5.83/2.12  tff(c_52, plain, (![A_66, B_67]: (m1_subset_1(k15_lattice3(A_66, B_67), u1_struct_0(A_66)) | ~l3_lattices(A_66) | v2_struct_0(A_66))), inference(cnfTransformation, [status(thm)], [f_144])).
% 5.83/2.12  tff(c_10, plain, (![A_6]: (v8_lattices(A_6) | ~v10_lattices(A_6) | v2_struct_0(A_6) | ~l3_lattices(A_6))), inference(cnfTransformation, [status(thm)], [f_54])).
% 5.83/2.12  tff(c_87, plain, (![A_109, B_110]: (~r2_hidden('#skF_1'(A_109, B_110), B_110) | r1_tarski(A_109, B_110))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.83/2.12  tff(c_92, plain, (![A_1]: (r1_tarski(A_1, A_1))), inference(resolution, [status(thm)], [c_6, c_87])).
% 5.83/2.12  tff(c_170, plain, (![A_160, B_161]: (r4_lattice3(A_160, k15_lattice3(A_160, B_161), B_161) | ~m1_subset_1(k15_lattice3(A_160, B_161), u1_struct_0(A_160)) | ~v4_lattice3(A_160) | ~v10_lattices(A_160) | ~l3_lattices(A_160) | v2_struct_0(A_160))), inference(cnfTransformation, [status(thm)], [f_137])).
% 5.83/2.12  tff(c_173, plain, (![A_66, B_67]: (r4_lattice3(A_66, k15_lattice3(A_66, B_67), B_67) | ~v4_lattice3(A_66) | ~v10_lattices(A_66) | ~l3_lattices(A_66) | v2_struct_0(A_66))), inference(resolution, [status(thm)], [c_52, c_170])).
% 5.83/2.12  tff(c_362, plain, (![A_249, B_250, D_251]: (r1_lattices(A_249, k15_lattice3(A_249, B_250), D_251) | ~r4_lattice3(A_249, D_251, B_250) | ~m1_subset_1(D_251, u1_struct_0(A_249)) | ~m1_subset_1(k15_lattice3(A_249, B_250), u1_struct_0(A_249)) | ~v4_lattice3(A_249) | ~v10_lattices(A_249) | ~l3_lattices(A_249) | v2_struct_0(A_249))), inference(cnfTransformation, [status(thm)], [f_137])).
% 5.83/2.12  tff(c_366, plain, (![A_252, B_253, D_254]: (r1_lattices(A_252, k15_lattice3(A_252, B_253), D_254) | ~r4_lattice3(A_252, D_254, B_253) | ~m1_subset_1(D_254, u1_struct_0(A_252)) | ~v4_lattice3(A_252) | ~v10_lattices(A_252) | ~l3_lattices(A_252) | v2_struct_0(A_252))), inference(resolution, [status(thm)], [c_52, c_362])).
% 5.83/2.12  tff(c_14, plain, (![A_6]: (v6_lattices(A_6) | ~v10_lattices(A_6) | v2_struct_0(A_6) | ~l3_lattices(A_6))), inference(cnfTransformation, [status(thm)], [f_54])).
% 5.83/2.12  tff(c_268, plain, (![A_199, B_200, C_201]: (r3_lattices(A_199, B_200, C_201) | ~r1_lattices(A_199, B_200, C_201) | ~m1_subset_1(C_201, u1_struct_0(A_199)) | ~m1_subset_1(B_200, u1_struct_0(A_199)) | ~l3_lattices(A_199) | ~v9_lattices(A_199) | ~v8_lattices(A_199) | ~v6_lattices(A_199) | v2_struct_0(A_199))), inference(cnfTransformation, [status(thm)], [f_73])).
% 5.83/2.12  tff(c_306, plain, (![A_217, B_218, B_219]: (r3_lattices(A_217, B_218, k15_lattice3(A_217, B_219)) | ~r1_lattices(A_217, B_218, k15_lattice3(A_217, B_219)) | ~m1_subset_1(B_218, u1_struct_0(A_217)) | ~v9_lattices(A_217) | ~v8_lattices(A_217) | ~v6_lattices(A_217) | ~l3_lattices(A_217) | v2_struct_0(A_217))), inference(resolution, [status(thm)], [c_52, c_268])).
% 5.83/2.12  tff(c_68, plain, (~r3_lattices('#skF_6', k16_lattice3('#skF_6', '#skF_8'), k16_lattice3('#skF_6', '#skF_7')) | ~r3_lattices('#skF_6', k15_lattice3('#skF_6', '#skF_7'), k15_lattice3('#skF_6', '#skF_8'))), inference(cnfTransformation, [status(thm)], [f_209])).
% 5.83/2.12  tff(c_83, plain, (~r3_lattices('#skF_6', k15_lattice3('#skF_6', '#skF_7'), k15_lattice3('#skF_6', '#skF_8'))), inference(splitLeft, [status(thm)], [c_68])).
% 5.83/2.12  tff(c_311, plain, (~r1_lattices('#skF_6', k15_lattice3('#skF_6', '#skF_7'), k15_lattice3('#skF_6', '#skF_8')) | ~m1_subset_1(k15_lattice3('#skF_6', '#skF_7'), u1_struct_0('#skF_6')) | ~v9_lattices('#skF_6') | ~v8_lattices('#skF_6') | ~v6_lattices('#skF_6') | ~l3_lattices('#skF_6') | v2_struct_0('#skF_6')), inference(resolution, [status(thm)], [c_306, c_83])).
% 5.83/2.12  tff(c_315, plain, (~r1_lattices('#skF_6', k15_lattice3('#skF_6', '#skF_7'), k15_lattice3('#skF_6', '#skF_8')) | ~m1_subset_1(k15_lattice3('#skF_6', '#skF_7'), u1_struct_0('#skF_6')) | ~v9_lattices('#skF_6') | ~v8_lattices('#skF_6') | ~v6_lattices('#skF_6') | v2_struct_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_311])).
% 5.83/2.12  tff(c_316, plain, (~r1_lattices('#skF_6', k15_lattice3('#skF_6', '#skF_7'), k15_lattice3('#skF_6', '#skF_8')) | ~m1_subset_1(k15_lattice3('#skF_6', '#skF_7'), u1_struct_0('#skF_6')) | ~v9_lattices('#skF_6') | ~v8_lattices('#skF_6') | ~v6_lattices('#skF_6')), inference(negUnitSimplification, [status(thm)], [c_78, c_315])).
% 5.83/2.12  tff(c_317, plain, (~v6_lattices('#skF_6')), inference(splitLeft, [status(thm)], [c_316])).
% 5.83/2.12  tff(c_320, plain, (~v10_lattices('#skF_6') | v2_struct_0('#skF_6') | ~l3_lattices('#skF_6')), inference(resolution, [status(thm)], [c_14, c_317])).
% 5.83/2.12  tff(c_323, plain, (v2_struct_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_76, c_320])).
% 5.83/2.12  tff(c_325, plain, $false, inference(negUnitSimplification, [status(thm)], [c_78, c_323])).
% 5.83/2.12  tff(c_326, plain, (~v8_lattices('#skF_6') | ~v9_lattices('#skF_6') | ~m1_subset_1(k15_lattice3('#skF_6', '#skF_7'), u1_struct_0('#skF_6')) | ~r1_lattices('#skF_6', k15_lattice3('#skF_6', '#skF_7'), k15_lattice3('#skF_6', '#skF_8'))), inference(splitRight, [status(thm)], [c_316])).
% 5.83/2.12  tff(c_328, plain, (~r1_lattices('#skF_6', k15_lattice3('#skF_6', '#skF_7'), k15_lattice3('#skF_6', '#skF_8'))), inference(splitLeft, [status(thm)], [c_326])).
% 5.83/2.12  tff(c_373, plain, (~r4_lattice3('#skF_6', k15_lattice3('#skF_6', '#skF_8'), '#skF_7') | ~m1_subset_1(k15_lattice3('#skF_6', '#skF_8'), u1_struct_0('#skF_6')) | ~v4_lattice3('#skF_6') | ~v10_lattices('#skF_6') | ~l3_lattices('#skF_6') | v2_struct_0('#skF_6')), inference(resolution, [status(thm)], [c_366, c_328])).
% 5.83/2.12  tff(c_381, plain, (~r4_lattice3('#skF_6', k15_lattice3('#skF_6', '#skF_8'), '#skF_7') | ~m1_subset_1(k15_lattice3('#skF_6', '#skF_8'), u1_struct_0('#skF_6')) | v2_struct_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_76, c_74, c_373])).
% 5.83/2.12  tff(c_382, plain, (~r4_lattice3('#skF_6', k15_lattice3('#skF_6', '#skF_8'), '#skF_7') | ~m1_subset_1(k15_lattice3('#skF_6', '#skF_8'), u1_struct_0('#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_78, c_381])).
% 5.83/2.12  tff(c_384, plain, (~m1_subset_1(k15_lattice3('#skF_6', '#skF_8'), u1_struct_0('#skF_6'))), inference(splitLeft, [status(thm)], [c_382])).
% 5.83/2.12  tff(c_387, plain, (~l3_lattices('#skF_6') | v2_struct_0('#skF_6')), inference(resolution, [status(thm)], [c_52, c_384])).
% 5.83/2.12  tff(c_390, plain, (v2_struct_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_387])).
% 5.83/2.12  tff(c_392, plain, $false, inference(negUnitSimplification, [status(thm)], [c_78, c_390])).
% 5.83/2.12  tff(c_394, plain, (m1_subset_1(k15_lattice3('#skF_6', '#skF_8'), u1_struct_0('#skF_6'))), inference(splitRight, [status(thm)], [c_382])).
% 5.83/2.12  tff(c_40, plain, (![A_32, B_44, C_50]: (m1_subset_1('#skF_3'(A_32, B_44, C_50), u1_struct_0(A_32)) | r4_lattice3(A_32, B_44, C_50) | ~m1_subset_1(B_44, u1_struct_0(A_32)) | ~l3_lattices(A_32) | v2_struct_0(A_32))), inference(cnfTransformation, [status(thm)], [f_109])).
% 5.83/2.12  tff(c_70, plain, (r1_tarski('#skF_7', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_209])).
% 5.83/2.12  tff(c_100, plain, (![A_119, B_120, C_121]: (r2_hidden('#skF_3'(A_119, B_120, C_121), C_121) | r4_lattice3(A_119, B_120, C_121) | ~m1_subset_1(B_120, u1_struct_0(A_119)) | ~l3_lattices(A_119) | v2_struct_0(A_119))), inference(cnfTransformation, [status(thm)], [f_109])).
% 5.83/2.12  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.83/2.12  tff(c_180, plain, (![A_171, B_172, C_173, B_174]: (r2_hidden('#skF_3'(A_171, B_172, C_173), B_174) | ~r1_tarski(C_173, B_174) | r4_lattice3(A_171, B_172, C_173) | ~m1_subset_1(B_172, u1_struct_0(A_171)) | ~l3_lattices(A_171) | v2_struct_0(A_171))), inference(resolution, [status(thm)], [c_100, c_2])).
% 5.83/2.12  tff(c_234, plain, (![B_185, A_186, C_183, B_184, B_187]: (r2_hidden('#skF_3'(A_186, B_187, C_183), B_185) | ~r1_tarski(B_184, B_185) | ~r1_tarski(C_183, B_184) | r4_lattice3(A_186, B_187, C_183) | ~m1_subset_1(B_187, u1_struct_0(A_186)) | ~l3_lattices(A_186) | v2_struct_0(A_186))), inference(resolution, [status(thm)], [c_180, c_2])).
% 5.83/2.12  tff(c_241, plain, (![A_188, B_189, C_190]: (r2_hidden('#skF_3'(A_188, B_189, C_190), '#skF_8') | ~r1_tarski(C_190, '#skF_7') | r4_lattice3(A_188, B_189, C_190) | ~m1_subset_1(B_189, u1_struct_0(A_188)) | ~l3_lattices(A_188) | v2_struct_0(A_188))), inference(resolution, [status(thm)], [c_70, c_234])).
% 5.83/2.12  tff(c_34, plain, (![A_32, D_53, B_44, C_50]: (r1_lattices(A_32, D_53, B_44) | ~r2_hidden(D_53, C_50) | ~m1_subset_1(D_53, u1_struct_0(A_32)) | ~r4_lattice3(A_32, B_44, C_50) | ~m1_subset_1(B_44, u1_struct_0(A_32)) | ~l3_lattices(A_32) | v2_struct_0(A_32))), inference(cnfTransformation, [status(thm)], [f_109])).
% 5.83/2.12  tff(c_673, plain, (![A_420, B_421, C_424, B_422, A_423]: (r1_lattices(A_420, '#skF_3'(A_423, B_421, C_424), B_422) | ~m1_subset_1('#skF_3'(A_423, B_421, C_424), u1_struct_0(A_420)) | ~r4_lattice3(A_420, B_422, '#skF_8') | ~m1_subset_1(B_422, u1_struct_0(A_420)) | ~l3_lattices(A_420) | v2_struct_0(A_420) | ~r1_tarski(C_424, '#skF_7') | r4_lattice3(A_423, B_421, C_424) | ~m1_subset_1(B_421, u1_struct_0(A_423)) | ~l3_lattices(A_423) | v2_struct_0(A_423))), inference(resolution, [status(thm)], [c_241, c_34])).
% 5.83/2.12  tff(c_679, plain, (![A_433, B_434, C_435, B_436]: (r1_lattices(A_433, '#skF_3'(A_433, B_434, C_435), B_436) | ~r4_lattice3(A_433, B_436, '#skF_8') | ~m1_subset_1(B_436, u1_struct_0(A_433)) | ~r1_tarski(C_435, '#skF_7') | r4_lattice3(A_433, B_434, C_435) | ~m1_subset_1(B_434, u1_struct_0(A_433)) | ~l3_lattices(A_433) | v2_struct_0(A_433))), inference(resolution, [status(thm)], [c_40, c_673])).
% 5.83/2.12  tff(c_36, plain, (![A_32, B_44, C_50]: (~r1_lattices(A_32, '#skF_3'(A_32, B_44, C_50), B_44) | r4_lattice3(A_32, B_44, C_50) | ~m1_subset_1(B_44, u1_struct_0(A_32)) | ~l3_lattices(A_32) | v2_struct_0(A_32))), inference(cnfTransformation, [status(thm)], [f_109])).
% 5.83/2.12  tff(c_695, plain, (![A_437, B_438, C_439]: (~r4_lattice3(A_437, B_438, '#skF_8') | ~r1_tarski(C_439, '#skF_7') | r4_lattice3(A_437, B_438, C_439) | ~m1_subset_1(B_438, u1_struct_0(A_437)) | ~l3_lattices(A_437) | v2_struct_0(A_437))), inference(resolution, [status(thm)], [c_679, c_36])).
% 5.83/2.12  tff(c_697, plain, (![C_439]: (~r4_lattice3('#skF_6', k15_lattice3('#skF_6', '#skF_8'), '#skF_8') | ~r1_tarski(C_439, '#skF_7') | r4_lattice3('#skF_6', k15_lattice3('#skF_6', '#skF_8'), C_439) | ~l3_lattices('#skF_6') | v2_struct_0('#skF_6'))), inference(resolution, [status(thm)], [c_394, c_695])).
% 5.83/2.12  tff(c_712, plain, (![C_439]: (~r4_lattice3('#skF_6', k15_lattice3('#skF_6', '#skF_8'), '#skF_8') | ~r1_tarski(C_439, '#skF_7') | r4_lattice3('#skF_6', k15_lattice3('#skF_6', '#skF_8'), C_439) | v2_struct_0('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_697])).
% 5.83/2.12  tff(c_713, plain, (![C_439]: (~r4_lattice3('#skF_6', k15_lattice3('#skF_6', '#skF_8'), '#skF_8') | ~r1_tarski(C_439, '#skF_7') | r4_lattice3('#skF_6', k15_lattice3('#skF_6', '#skF_8'), C_439))), inference(negUnitSimplification, [status(thm)], [c_78, c_712])).
% 5.83/2.12  tff(c_720, plain, (~r4_lattice3('#skF_6', k15_lattice3('#skF_6', '#skF_8'), '#skF_8')), inference(splitLeft, [status(thm)], [c_713])).
% 5.83/2.12  tff(c_729, plain, (~v4_lattice3('#skF_6') | ~v10_lattices('#skF_6') | ~l3_lattices('#skF_6') | v2_struct_0('#skF_6')), inference(resolution, [status(thm)], [c_173, c_720])).
% 5.83/2.12  tff(c_732, plain, (v2_struct_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_76, c_74, c_729])).
% 5.83/2.12  tff(c_734, plain, $false, inference(negUnitSimplification, [status(thm)], [c_78, c_732])).
% 5.83/2.12  tff(c_743, plain, (![C_443]: (~r1_tarski(C_443, '#skF_7') | r4_lattice3('#skF_6', k15_lattice3('#skF_6', '#skF_8'), C_443))), inference(splitRight, [status(thm)], [c_713])).
% 5.83/2.12  tff(c_393, plain, (~r4_lattice3('#skF_6', k15_lattice3('#skF_6', '#skF_8'), '#skF_7')), inference(splitRight, [status(thm)], [c_382])).
% 5.83/2.12  tff(c_748, plain, (~r1_tarski('#skF_7', '#skF_7')), inference(resolution, [status(thm)], [c_743, c_393])).
% 5.83/2.12  tff(c_756, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_92, c_748])).
% 5.83/2.12  tff(c_757, plain, (~m1_subset_1(k15_lattice3('#skF_6', '#skF_7'), u1_struct_0('#skF_6')) | ~v9_lattices('#skF_6') | ~v8_lattices('#skF_6')), inference(splitRight, [status(thm)], [c_326])).
% 5.83/2.12  tff(c_760, plain, (~v8_lattices('#skF_6')), inference(splitLeft, [status(thm)], [c_757])).
% 5.83/2.12  tff(c_763, plain, (~v10_lattices('#skF_6') | v2_struct_0('#skF_6') | ~l3_lattices('#skF_6')), inference(resolution, [status(thm)], [c_10, c_760])).
% 5.83/2.12  tff(c_766, plain, (v2_struct_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_76, c_763])).
% 5.83/2.12  tff(c_768, plain, $false, inference(negUnitSimplification, [status(thm)], [c_78, c_766])).
% 5.83/2.12  tff(c_769, plain, (~v9_lattices('#skF_6') | ~m1_subset_1(k15_lattice3('#skF_6', '#skF_7'), u1_struct_0('#skF_6'))), inference(splitRight, [status(thm)], [c_757])).
% 5.83/2.12  tff(c_771, plain, (~m1_subset_1(k15_lattice3('#skF_6', '#skF_7'), u1_struct_0('#skF_6'))), inference(splitLeft, [status(thm)], [c_769])).
% 5.83/2.12  tff(c_778, plain, (~l3_lattices('#skF_6') | v2_struct_0('#skF_6')), inference(resolution, [status(thm)], [c_52, c_771])).
% 5.83/2.12  tff(c_781, plain, (v2_struct_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_778])).
% 5.83/2.12  tff(c_783, plain, $false, inference(negUnitSimplification, [status(thm)], [c_78, c_781])).
% 5.83/2.12  tff(c_784, plain, (~v9_lattices('#skF_6')), inference(splitRight, [status(thm)], [c_769])).
% 5.83/2.12  tff(c_788, plain, (~v10_lattices('#skF_6') | v2_struct_0('#skF_6') | ~l3_lattices('#skF_6')), inference(resolution, [status(thm)], [c_8, c_784])).
% 5.83/2.12  tff(c_791, plain, (v2_struct_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_76, c_788])).
% 5.83/2.12  tff(c_793, plain, $false, inference(negUnitSimplification, [status(thm)], [c_78, c_791])).
% 5.83/2.12  tff(c_794, plain, (~r3_lattices('#skF_6', k16_lattice3('#skF_6', '#skF_8'), k16_lattice3('#skF_6', '#skF_7'))), inference(splitRight, [status(thm)], [c_68])).
% 5.83/2.12  tff(c_890, plain, (~r3_lattice3('#skF_6', k16_lattice3('#skF_6', '#skF_8'), '#skF_7') | ~m1_subset_1(k16_lattice3('#skF_6', '#skF_8'), u1_struct_0('#skF_6')) | ~l3_lattices('#skF_6') | ~v4_lattice3('#skF_6') | ~v10_lattices('#skF_6') | v2_struct_0('#skF_6')), inference(resolution, [status(thm)], [c_887, c_794])).
% 5.83/2.12  tff(c_893, plain, (~r3_lattice3('#skF_6', k16_lattice3('#skF_6', '#skF_8'), '#skF_7') | ~m1_subset_1(k16_lattice3('#skF_6', '#skF_8'), u1_struct_0('#skF_6')) | v2_struct_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_74, c_72, c_890])).
% 5.83/2.12  tff(c_894, plain, (~r3_lattice3('#skF_6', k16_lattice3('#skF_6', '#skF_8'), '#skF_7') | ~m1_subset_1(k16_lattice3('#skF_6', '#skF_8'), u1_struct_0('#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_78, c_893])).
% 5.83/2.12  tff(c_895, plain, (~m1_subset_1(k16_lattice3('#skF_6', '#skF_8'), u1_struct_0('#skF_6'))), inference(splitLeft, [status(thm)], [c_894])).
% 5.83/2.12  tff(c_898, plain, (~l3_lattices('#skF_6') | v2_struct_0('#skF_6')), inference(resolution, [status(thm)], [c_54, c_895])).
% 5.83/2.12  tff(c_901, plain, (v2_struct_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_898])).
% 5.83/2.12  tff(c_903, plain, $false, inference(negUnitSimplification, [status(thm)], [c_78, c_901])).
% 5.83/2.12  tff(c_905, plain, (m1_subset_1(k16_lattice3('#skF_6', '#skF_8'), u1_struct_0('#skF_6'))), inference(splitRight, [status(thm)], [c_894])).
% 5.83/2.12  tff(c_32, plain, (![A_10, B_22, C_28]: (m1_subset_1('#skF_2'(A_10, B_22, C_28), u1_struct_0(A_10)) | r3_lattice3(A_10, B_22, C_28) | ~m1_subset_1(B_22, u1_struct_0(A_10)) | ~l3_lattices(A_10) | v2_struct_0(A_10))), inference(cnfTransformation, [status(thm)], [f_91])).
% 5.83/2.12  tff(c_821, plain, (![A_468, B_469, C_470]: (r2_hidden('#skF_2'(A_468, B_469, C_470), C_470) | r3_lattice3(A_468, B_469, C_470) | ~m1_subset_1(B_469, u1_struct_0(A_468)) | ~l3_lattices(A_468) | v2_struct_0(A_468))), inference(cnfTransformation, [status(thm)], [f_91])).
% 5.83/2.12  tff(c_906, plain, (![A_513, B_514, C_515, B_516]: (r2_hidden('#skF_2'(A_513, B_514, C_515), B_516) | ~r1_tarski(C_515, B_516) | r3_lattice3(A_513, B_514, C_515) | ~m1_subset_1(B_514, u1_struct_0(A_513)) | ~l3_lattices(A_513) | v2_struct_0(A_513))), inference(resolution, [status(thm)], [c_821, c_2])).
% 5.83/2.12  tff(c_991, plain, (![B_541, A_543, B_544, C_542, B_540]: (r2_hidden('#skF_2'(A_543, B_541, C_542), B_544) | ~r1_tarski(B_540, B_544) | ~r1_tarski(C_542, B_540) | r3_lattice3(A_543, B_541, C_542) | ~m1_subset_1(B_541, u1_struct_0(A_543)) | ~l3_lattices(A_543) | v2_struct_0(A_543))), inference(resolution, [status(thm)], [c_906, c_2])).
% 5.83/2.12  tff(c_998, plain, (![A_545, B_546, C_547]: (r2_hidden('#skF_2'(A_545, B_546, C_547), '#skF_8') | ~r1_tarski(C_547, '#skF_7') | r3_lattice3(A_545, B_546, C_547) | ~m1_subset_1(B_546, u1_struct_0(A_545)) | ~l3_lattices(A_545) | v2_struct_0(A_545))), inference(resolution, [status(thm)], [c_70, c_991])).
% 5.83/2.12  tff(c_26, plain, (![A_10, B_22, D_31, C_28]: (r1_lattices(A_10, B_22, D_31) | ~r2_hidden(D_31, C_28) | ~m1_subset_1(D_31, u1_struct_0(A_10)) | ~r3_lattice3(A_10, B_22, C_28) | ~m1_subset_1(B_22, u1_struct_0(A_10)) | ~l3_lattices(A_10) | v2_struct_0(A_10))), inference(cnfTransformation, [status(thm)], [f_91])).
% 5.83/2.12  tff(c_1587, plain, (![B_736, A_739, C_737, B_738, A_735]: (r1_lattices(A_739, B_738, '#skF_2'(A_735, B_736, C_737)) | ~m1_subset_1('#skF_2'(A_735, B_736, C_737), u1_struct_0(A_739)) | ~r3_lattice3(A_739, B_738, '#skF_8') | ~m1_subset_1(B_738, u1_struct_0(A_739)) | ~l3_lattices(A_739) | v2_struct_0(A_739) | ~r1_tarski(C_737, '#skF_7') | r3_lattice3(A_735, B_736, C_737) | ~m1_subset_1(B_736, u1_struct_0(A_735)) | ~l3_lattices(A_735) | v2_struct_0(A_735))), inference(resolution, [status(thm)], [c_998, c_26])).
% 5.83/2.12  tff(c_1591, plain, (![A_740, B_741, B_742, C_743]: (r1_lattices(A_740, B_741, '#skF_2'(A_740, B_742, C_743)) | ~r3_lattice3(A_740, B_741, '#skF_8') | ~m1_subset_1(B_741, u1_struct_0(A_740)) | ~r1_tarski(C_743, '#skF_7') | r3_lattice3(A_740, B_742, C_743) | ~m1_subset_1(B_742, u1_struct_0(A_740)) | ~l3_lattices(A_740) | v2_struct_0(A_740))), inference(resolution, [status(thm)], [c_32, c_1587])).
% 5.83/2.12  tff(c_28, plain, (![A_10, B_22, C_28]: (~r1_lattices(A_10, B_22, '#skF_2'(A_10, B_22, C_28)) | r3_lattice3(A_10, B_22, C_28) | ~m1_subset_1(B_22, u1_struct_0(A_10)) | ~l3_lattices(A_10) | v2_struct_0(A_10))), inference(cnfTransformation, [status(thm)], [f_91])).
% 5.83/2.12  tff(c_1602, plain, (![A_744, B_745, C_746]: (~r3_lattice3(A_744, B_745, '#skF_8') | ~r1_tarski(C_746, '#skF_7') | r3_lattice3(A_744, B_745, C_746) | ~m1_subset_1(B_745, u1_struct_0(A_744)) | ~l3_lattices(A_744) | v2_struct_0(A_744))), inference(resolution, [status(thm)], [c_1591, c_28])).
% 5.83/2.12  tff(c_1612, plain, (![C_746]: (~r3_lattice3('#skF_6', k16_lattice3('#skF_6', '#skF_8'), '#skF_8') | ~r1_tarski(C_746, '#skF_7') | r3_lattice3('#skF_6', k16_lattice3('#skF_6', '#skF_8'), C_746) | ~l3_lattices('#skF_6') | v2_struct_0('#skF_6'))), inference(resolution, [status(thm)], [c_905, c_1602])).
% 5.83/2.12  tff(c_1633, plain, (![C_746]: (~r3_lattice3('#skF_6', k16_lattice3('#skF_6', '#skF_8'), '#skF_8') | ~r1_tarski(C_746, '#skF_7') | r3_lattice3('#skF_6', k16_lattice3('#skF_6', '#skF_8'), C_746) | v2_struct_0('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_1612])).
% 5.83/2.12  tff(c_1634, plain, (![C_746]: (~r3_lattice3('#skF_6', k16_lattice3('#skF_6', '#skF_8'), '#skF_8') | ~r1_tarski(C_746, '#skF_7') | r3_lattice3('#skF_6', k16_lattice3('#skF_6', '#skF_8'), C_746))), inference(negUnitSimplification, [status(thm)], [c_78, c_1633])).
% 5.83/2.12  tff(c_1645, plain, (~r3_lattice3('#skF_6', k16_lattice3('#skF_6', '#skF_8'), '#skF_8')), inference(splitLeft, [status(thm)], [c_1634])).
% 5.83/2.12  tff(c_1648, plain, (~v4_lattice3('#skF_6') | ~v10_lattices('#skF_6') | ~l3_lattices('#skF_6') | v2_struct_0('#skF_6')), inference(resolution, [status(thm)], [c_885, c_1645])).
% 5.83/2.12  tff(c_1651, plain, (v2_struct_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_76, c_74, c_1648])).
% 5.83/2.12  tff(c_1653, plain, $false, inference(negUnitSimplification, [status(thm)], [c_78, c_1651])).
% 5.83/2.12  tff(c_1656, plain, (![C_752]: (~r1_tarski(C_752, '#skF_7') | r3_lattice3('#skF_6', k16_lattice3('#skF_6', '#skF_8'), C_752))), inference(splitRight, [status(thm)], [c_1634])).
% 5.83/2.12  tff(c_904, plain, (~r3_lattice3('#skF_6', k16_lattice3('#skF_6', '#skF_8'), '#skF_7')), inference(splitRight, [status(thm)], [c_894])).
% 5.83/2.12  tff(c_1659, plain, (~r1_tarski('#skF_7', '#skF_7')), inference(resolution, [status(thm)], [c_1656, c_904])).
% 5.83/2.12  tff(c_1663, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_803, c_1659])).
% 5.83/2.12  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.83/2.12  
% 5.83/2.12  Inference rules
% 5.83/2.12  ----------------------
% 5.83/2.12  #Ref     : 0
% 5.83/2.12  #Sup     : 305
% 5.83/2.12  #Fact    : 0
% 5.83/2.12  #Define  : 0
% 5.83/2.12  #Split   : 22
% 5.83/2.12  #Chain   : 0
% 5.83/2.12  #Close   : 0
% 5.83/2.12  
% 5.83/2.12  Ordering : KBO
% 5.83/2.12  
% 5.83/2.12  Simplification rules
% 5.83/2.12  ----------------------
% 5.83/2.12  #Subsume      : 42
% 5.83/2.12  #Demod        : 180
% 5.83/2.12  #Tautology    : 26
% 5.83/2.12  #SimpNegUnit  : 64
% 5.83/2.12  #BackRed      : 0
% 5.83/2.12  
% 5.83/2.12  #Partial instantiations: 0
% 5.83/2.12  #Strategies tried      : 1
% 5.83/2.12  
% 5.83/2.12  Timing (in seconds)
% 5.83/2.12  ----------------------
% 5.83/2.12  Preprocessing        : 0.41
% 5.83/2.12  Parsing              : 0.22
% 5.83/2.13  CNF conversion       : 0.03
% 5.83/2.13  Main loop            : 0.93
% 5.83/2.13  Inferencing          : 0.40
% 5.83/2.13  Reduction            : 0.22
% 5.83/2.13  Demodulation         : 0.14
% 5.83/2.13  BG Simplification    : 0.04
% 5.83/2.13  Subsumption          : 0.20
% 5.83/2.13  Abstraction          : 0.03
% 5.83/2.13  MUC search           : 0.00
% 5.83/2.13  Cooper               : 0.00
% 5.83/2.13  Total                : 1.39
% 5.83/2.13  Index Insertion      : 0.00
% 5.83/2.13  Index Deletion       : 0.00
% 5.83/2.13  Index Matching       : 0.00
% 5.83/2.13  BG Taut test         : 0.00
%------------------------------------------------------------------------------
