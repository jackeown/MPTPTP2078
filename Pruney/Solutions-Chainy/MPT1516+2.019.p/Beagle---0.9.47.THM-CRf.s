%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:24:53 EST 2020

% Result     : Theorem 8.98s
% Output     : CNFRefutation 8.98s
% Verified   : 
% Statistics : Number of formulae       :  157 ( 792 expanded)
%              Number of leaves         :   47 ( 290 expanded)
%              Depth                    :   25
%              Number of atoms          :  543 (3344 expanded)
%              Number of equality atoms :   61 ( 423 expanded)
%              Maximal formula depth    :   21 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r4_lattice3 > r1_lattices > r2_hidden > r1_tarski > m1_subset_1 > v9_lattices > v8_lattices > v7_lattices > v6_lattices > v5_lattices > v4_lattices > v4_lattice3 > v2_struct_0 > v13_lattices > v10_lattices > l3_lattices > l2_lattices > l1_lattices > k2_lattices > k15_lattice3 > #nlpp > u1_struct_0 > k5_lattices > k1_xboole_0 > #skF_7 > #skF_2 > #skF_4 > #skF_3 > #skF_5 > #skF_8 > #skF_1 > #skF_6

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

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k15_lattice3,type,(
    k15_lattice3: ( $i * $i ) > $i )).

tff(l1_lattices,type,(
    l1_lattices: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_lattices,type,(
    r1_lattices: ( $i * $i * $i ) > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(v4_lattices,type,(
    v4_lattices: $i > $o )).

tff(v6_lattices,type,(
    v6_lattices: $i > $o )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff(v9_lattices,type,(
    v9_lattices: $i > $o )).

tff(r4_lattice3,type,(
    r4_lattice3: ( $i * $i * $i ) > $o )).

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

tff('#skF_6',type,(
    '#skF_6': $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(v7_lattices,type,(
    v7_lattices: $i > $o )).

tff(f_211,negated_conjecture,(
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

tff(f_86,axiom,(
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

tff(f_190,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & l3_lattices(A) )
     => m1_subset_1(k15_lattice3(A,B),u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k15_lattice3)).

tff(f_122,axiom,(
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

tff(f_27,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_140,axiom,(
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

tff(f_32,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

tff(f_168,axiom,(
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

tff(f_105,axiom,(
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

tff(f_183,axiom,(
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

tff(f_80,axiom,(
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

tff(c_78,plain,(
    l3_lattices('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_211])).

tff(c_89,plain,(
    ! [A_83] :
      ( l1_lattices(A_83)
      | ~ l3_lattices(A_83) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_93,plain,(
    l1_lattices('#skF_8') ),
    inference(resolution,[status(thm)],[c_78,c_89])).

tff(c_84,plain,(
    ~ v2_struct_0('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_211])).

tff(c_82,plain,(
    v10_lattices('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_211])).

tff(c_76,plain,
    ( k15_lattice3('#skF_8',k1_xboole_0) != k5_lattices('#skF_8')
    | ~ l3_lattices('#skF_8')
    | ~ v13_lattices('#skF_8')
    | ~ v10_lattices('#skF_8')
    | v2_struct_0('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_211])).

tff(c_86,plain,
    ( k15_lattice3('#skF_8',k1_xboole_0) != k5_lattices('#skF_8')
    | ~ v13_lattices('#skF_8')
    | v2_struct_0('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_78,c_76])).

tff(c_87,plain,
    ( k15_lattice3('#skF_8',k1_xboole_0) != k5_lattices('#skF_8')
    | ~ v13_lattices('#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_84,c_86])).

tff(c_99,plain,(
    ~ v13_lattices('#skF_8') ),
    inference(splitLeft,[status(thm)],[c_87])).

tff(c_80,plain,(
    v4_lattice3('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_211])).

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

tff(c_74,plain,(
    ! [A_80,B_81] :
      ( m1_subset_1(k15_lattice3(A_80,B_81),u1_struct_0(A_80))
      | ~ l3_lattices(A_80)
      | v2_struct_0(A_80) ) ),
    inference(cnfTransformation,[status(thm)],[f_190])).

tff(c_40,plain,(
    ! [A_24,B_33] :
      ( m1_subset_1('#skF_3'(A_24,B_33),u1_struct_0(A_24))
      | v13_lattices(A_24)
      | ~ m1_subset_1(B_33,u1_struct_0(A_24))
      | ~ l1_lattices(A_24)
      | v2_struct_0(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_2,plain,(
    ! [A_1] : r1_tarski(k1_xboole_0,A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_169,plain,(
    ! [A_107,B_108,C_109] :
      ( r2_hidden('#skF_4'(A_107,B_108,C_109),C_109)
      | r4_lattice3(A_107,B_108,C_109)
      | ~ m1_subset_1(B_108,u1_struct_0(A_107))
      | ~ l3_lattices(A_107)
      | v2_struct_0(A_107) ) ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_4,plain,(
    ! [B_3,A_2] :
      ( ~ r1_tarski(B_3,A_2)
      | ~ r2_hidden(A_2,B_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_238,plain,(
    ! [C_120,A_121,B_122] :
      ( ~ r1_tarski(C_120,'#skF_4'(A_121,B_122,C_120))
      | r4_lattice3(A_121,B_122,C_120)
      | ~ m1_subset_1(B_122,u1_struct_0(A_121))
      | ~ l3_lattices(A_121)
      | v2_struct_0(A_121) ) ),
    inference(resolution,[status(thm)],[c_169,c_4])).

tff(c_251,plain,(
    ! [A_126,B_127] :
      ( r4_lattice3(A_126,B_127,k1_xboole_0)
      | ~ m1_subset_1(B_127,u1_struct_0(A_126))
      | ~ l3_lattices(A_126)
      | v2_struct_0(A_126) ) ),
    inference(resolution,[status(thm)],[c_2,c_238])).

tff(c_274,plain,(
    ! [A_24,B_33] :
      ( r4_lattice3(A_24,'#skF_3'(A_24,B_33),k1_xboole_0)
      | ~ l3_lattices(A_24)
      | v13_lattices(A_24)
      | ~ m1_subset_1(B_33,u1_struct_0(A_24))
      | ~ l1_lattices(A_24)
      | v2_struct_0(A_24) ) ),
    inference(resolution,[status(thm)],[c_40,c_251])).

tff(c_858,plain,(
    ! [A_242,B_243,D_244] :
      ( r1_lattices(A_242,k15_lattice3(A_242,B_243),D_244)
      | ~ r4_lattice3(A_242,D_244,B_243)
      | ~ m1_subset_1(D_244,u1_struct_0(A_242))
      | ~ m1_subset_1(k15_lattice3(A_242,B_243),u1_struct_0(A_242))
      | ~ v4_lattice3(A_242)
      | ~ v10_lattices(A_242)
      | ~ l3_lattices(A_242)
      | v2_struct_0(A_242) ) ),
    inference(cnfTransformation,[status(thm)],[f_168])).

tff(c_862,plain,(
    ! [A_245,B_246,D_247] :
      ( r1_lattices(A_245,k15_lattice3(A_245,B_246),D_247)
      | ~ r4_lattice3(A_245,D_247,B_246)
      | ~ m1_subset_1(D_247,u1_struct_0(A_245))
      | ~ v4_lattice3(A_245)
      | ~ v10_lattices(A_245)
      | ~ l3_lattices(A_245)
      | v2_struct_0(A_245) ) ),
    inference(resolution,[status(thm)],[c_74,c_858])).

tff(c_36,plain,(
    ! [A_17,B_21,C_23] :
      ( k2_lattices(A_17,B_21,C_23) = B_21
      | ~ r1_lattices(A_17,B_21,C_23)
      | ~ m1_subset_1(C_23,u1_struct_0(A_17))
      | ~ m1_subset_1(B_21,u1_struct_0(A_17))
      | ~ l3_lattices(A_17)
      | ~ v9_lattices(A_17)
      | ~ v8_lattices(A_17)
      | v2_struct_0(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_1286,plain,(
    ! [A_320,B_321,D_322] :
      ( k2_lattices(A_320,k15_lattice3(A_320,B_321),D_322) = k15_lattice3(A_320,B_321)
      | ~ m1_subset_1(k15_lattice3(A_320,B_321),u1_struct_0(A_320))
      | ~ v9_lattices(A_320)
      | ~ v8_lattices(A_320)
      | ~ r4_lattice3(A_320,D_322,B_321)
      | ~ m1_subset_1(D_322,u1_struct_0(A_320))
      | ~ v4_lattice3(A_320)
      | ~ v10_lattices(A_320)
      | ~ l3_lattices(A_320)
      | v2_struct_0(A_320) ) ),
    inference(resolution,[status(thm)],[c_862,c_36])).

tff(c_1290,plain,(
    ! [A_323,B_324,D_325] :
      ( k2_lattices(A_323,k15_lattice3(A_323,B_324),D_325) = k15_lattice3(A_323,B_324)
      | ~ v9_lattices(A_323)
      | ~ v8_lattices(A_323)
      | ~ r4_lattice3(A_323,D_325,B_324)
      | ~ m1_subset_1(D_325,u1_struct_0(A_323))
      | ~ v4_lattice3(A_323)
      | ~ v10_lattices(A_323)
      | ~ l3_lattices(A_323)
      | v2_struct_0(A_323) ) ),
    inference(resolution,[status(thm)],[c_74,c_1286])).

tff(c_1312,plain,(
    ! [A_24,B_324,B_33] :
      ( k2_lattices(A_24,k15_lattice3(A_24,B_324),'#skF_3'(A_24,B_33)) = k15_lattice3(A_24,B_324)
      | ~ v9_lattices(A_24)
      | ~ v8_lattices(A_24)
      | ~ r4_lattice3(A_24,'#skF_3'(A_24,B_33),B_324)
      | ~ v4_lattice3(A_24)
      | ~ v10_lattices(A_24)
      | ~ l3_lattices(A_24)
      | v13_lattices(A_24)
      | ~ m1_subset_1(B_33,u1_struct_0(A_24))
      | ~ l1_lattices(A_24)
      | v2_struct_0(A_24) ) ),
    inference(resolution,[status(thm)],[c_40,c_1290])).

tff(c_1427,plain,(
    ! [A_349,B_350,B_351] :
      ( k2_lattices(A_349,k15_lattice3(A_349,B_350),'#skF_3'(A_349,B_351)) = k15_lattice3(A_349,B_350)
      | ~ v9_lattices(A_349)
      | ~ v8_lattices(A_349)
      | ~ r4_lattice3(A_349,'#skF_3'(A_349,B_351),B_350)
      | ~ v4_lattice3(A_349)
      | ~ v10_lattices(A_349)
      | ~ l3_lattices(A_349)
      | v13_lattices(A_349)
      | ~ m1_subset_1(B_351,u1_struct_0(A_349))
      | ~ l1_lattices(A_349)
      | v2_struct_0(A_349) ) ),
    inference(resolution,[status(thm)],[c_40,c_1290])).

tff(c_394,plain,(
    ! [A_158,C_159,B_160] :
      ( k2_lattices(A_158,C_159,B_160) = k2_lattices(A_158,B_160,C_159)
      | ~ m1_subset_1(C_159,u1_struct_0(A_158))
      | ~ m1_subset_1(B_160,u1_struct_0(A_158))
      | ~ v6_lattices(A_158)
      | ~ l1_lattices(A_158)
      | v2_struct_0(A_158) ) ),
    inference(cnfTransformation,[status(thm)],[f_183])).

tff(c_910,plain,(
    ! [A_259,B_260,B_261] :
      ( k2_lattices(A_259,B_260,'#skF_3'(A_259,B_261)) = k2_lattices(A_259,'#skF_3'(A_259,B_261),B_260)
      | ~ m1_subset_1(B_260,u1_struct_0(A_259))
      | ~ v6_lattices(A_259)
      | v13_lattices(A_259)
      | ~ m1_subset_1(B_261,u1_struct_0(A_259))
      | ~ l1_lattices(A_259)
      | v2_struct_0(A_259) ) ),
    inference(resolution,[status(thm)],[c_40,c_394])).

tff(c_936,plain,(
    ! [A_80,B_81,B_261] :
      ( k2_lattices(A_80,k15_lattice3(A_80,B_81),'#skF_3'(A_80,B_261)) = k2_lattices(A_80,'#skF_3'(A_80,B_261),k15_lattice3(A_80,B_81))
      | ~ v6_lattices(A_80)
      | v13_lattices(A_80)
      | ~ m1_subset_1(B_261,u1_struct_0(A_80))
      | ~ l1_lattices(A_80)
      | ~ l3_lattices(A_80)
      | v2_struct_0(A_80) ) ),
    inference(resolution,[status(thm)],[c_74,c_910])).

tff(c_2269,plain,(
    ! [A_540,B_541,B_542] :
      ( k2_lattices(A_540,'#skF_3'(A_540,B_541),k15_lattice3(A_540,B_542)) = k15_lattice3(A_540,B_542)
      | ~ v6_lattices(A_540)
      | v13_lattices(A_540)
      | ~ m1_subset_1(B_541,u1_struct_0(A_540))
      | ~ l1_lattices(A_540)
      | ~ l3_lattices(A_540)
      | v2_struct_0(A_540)
      | ~ v9_lattices(A_540)
      | ~ v8_lattices(A_540)
      | ~ r4_lattice3(A_540,'#skF_3'(A_540,B_541),B_542)
      | ~ v4_lattice3(A_540)
      | ~ v10_lattices(A_540)
      | ~ l3_lattices(A_540)
      | v13_lattices(A_540)
      | ~ m1_subset_1(B_541,u1_struct_0(A_540))
      | ~ l1_lattices(A_540)
      | v2_struct_0(A_540) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1427,c_936])).

tff(c_38,plain,(
    ! [A_24,B_33] :
      ( k2_lattices(A_24,'#skF_3'(A_24,B_33),B_33) != B_33
      | k2_lattices(A_24,B_33,'#skF_3'(A_24,B_33)) != B_33
      | v13_lattices(A_24)
      | ~ m1_subset_1(B_33,u1_struct_0(A_24))
      | ~ l1_lattices(A_24)
      | v2_struct_0(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_2288,plain,(
    ! [A_543,B_544] :
      ( k2_lattices(A_543,k15_lattice3(A_543,B_544),'#skF_3'(A_543,k15_lattice3(A_543,B_544))) != k15_lattice3(A_543,B_544)
      | ~ v6_lattices(A_543)
      | ~ v9_lattices(A_543)
      | ~ v8_lattices(A_543)
      | ~ r4_lattice3(A_543,'#skF_3'(A_543,k15_lattice3(A_543,B_544)),B_544)
      | ~ v4_lattice3(A_543)
      | ~ v10_lattices(A_543)
      | ~ l3_lattices(A_543)
      | v13_lattices(A_543)
      | ~ m1_subset_1(k15_lattice3(A_543,B_544),u1_struct_0(A_543))
      | ~ l1_lattices(A_543)
      | v2_struct_0(A_543) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2269,c_38])).

tff(c_2294,plain,(
    ! [A_545,B_546] :
      ( ~ v6_lattices(A_545)
      | ~ v9_lattices(A_545)
      | ~ v8_lattices(A_545)
      | ~ r4_lattice3(A_545,'#skF_3'(A_545,k15_lattice3(A_545,B_546)),B_546)
      | ~ v4_lattice3(A_545)
      | ~ v10_lattices(A_545)
      | ~ l3_lattices(A_545)
      | v13_lattices(A_545)
      | ~ m1_subset_1(k15_lattice3(A_545,B_546),u1_struct_0(A_545))
      | ~ l1_lattices(A_545)
      | v2_struct_0(A_545) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1312,c_2288])).

tff(c_2300,plain,(
    ! [A_547] :
      ( ~ v6_lattices(A_547)
      | ~ v9_lattices(A_547)
      | ~ v8_lattices(A_547)
      | ~ v4_lattice3(A_547)
      | ~ v10_lattices(A_547)
      | ~ l3_lattices(A_547)
      | v13_lattices(A_547)
      | ~ m1_subset_1(k15_lattice3(A_547,k1_xboole_0),u1_struct_0(A_547))
      | ~ l1_lattices(A_547)
      | v2_struct_0(A_547) ) ),
    inference(resolution,[status(thm)],[c_274,c_2294])).

tff(c_2306,plain,(
    ! [A_548] :
      ( ~ v6_lattices(A_548)
      | ~ v9_lattices(A_548)
      | ~ v8_lattices(A_548)
      | ~ v4_lattice3(A_548)
      | ~ v10_lattices(A_548)
      | v13_lattices(A_548)
      | ~ l1_lattices(A_548)
      | ~ l3_lattices(A_548)
      | v2_struct_0(A_548) ) ),
    inference(resolution,[status(thm)],[c_74,c_2300])).

tff(c_2311,plain,(
    ! [A_549] :
      ( ~ v6_lattices(A_549)
      | ~ v8_lattices(A_549)
      | ~ v4_lattice3(A_549)
      | v13_lattices(A_549)
      | ~ l1_lattices(A_549)
      | ~ v10_lattices(A_549)
      | v2_struct_0(A_549)
      | ~ l3_lattices(A_549) ) ),
    inference(resolution,[status(thm)],[c_6,c_2306])).

tff(c_2316,plain,(
    ! [A_550] :
      ( ~ v6_lattices(A_550)
      | ~ v4_lattice3(A_550)
      | v13_lattices(A_550)
      | ~ l1_lattices(A_550)
      | ~ v10_lattices(A_550)
      | v2_struct_0(A_550)
      | ~ l3_lattices(A_550) ) ),
    inference(resolution,[status(thm)],[c_8,c_2311])).

tff(c_2321,plain,(
    ! [A_551] :
      ( ~ v4_lattice3(A_551)
      | v13_lattices(A_551)
      | ~ l1_lattices(A_551)
      | ~ v10_lattices(A_551)
      | v2_struct_0(A_551)
      | ~ l3_lattices(A_551) ) ),
    inference(resolution,[status(thm)],[c_12,c_2316])).

tff(c_2324,plain,
    ( v13_lattices('#skF_8')
    | ~ l1_lattices('#skF_8')
    | ~ v10_lattices('#skF_8')
    | v2_struct_0('#skF_8')
    | ~ l3_lattices('#skF_8') ),
    inference(resolution,[status(thm)],[c_80,c_2321])).

tff(c_2327,plain,
    ( v13_lattices('#skF_8')
    | v2_struct_0('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_82,c_93,c_2324])).

tff(c_2329,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_84,c_99,c_2327])).

tff(c_2331,plain,(
    v13_lattices('#skF_8') ),
    inference(splitRight,[status(thm)],[c_87])).

tff(c_28,plain,(
    ! [A_15] :
      ( m1_subset_1(k5_lattices(A_15),u1_struct_0(A_15))
      | ~ l1_lattices(A_15)
      | v2_struct_0(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_42,plain,(
    ! [A_24] :
      ( m1_subset_1('#skF_2'(A_24),u1_struct_0(A_24))
      | ~ v13_lattices(A_24)
      | ~ l1_lattices(A_24)
      | v2_struct_0(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_2537,plain,(
    ! [A_617,C_618] :
      ( k2_lattices(A_617,C_618,k5_lattices(A_617)) = k5_lattices(A_617)
      | ~ m1_subset_1(C_618,u1_struct_0(A_617))
      | ~ m1_subset_1(k5_lattices(A_617),u1_struct_0(A_617))
      | ~ v13_lattices(A_617)
      | ~ l1_lattices(A_617)
      | v2_struct_0(A_617) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_2562,plain,(
    ! [A_619] :
      ( k2_lattices(A_619,'#skF_2'(A_619),k5_lattices(A_619)) = k5_lattices(A_619)
      | ~ m1_subset_1(k5_lattices(A_619),u1_struct_0(A_619))
      | ~ v13_lattices(A_619)
      | ~ l1_lattices(A_619)
      | v2_struct_0(A_619) ) ),
    inference(resolution,[status(thm)],[c_42,c_2537])).

tff(c_2591,plain,(
    ! [A_622] :
      ( k2_lattices(A_622,'#skF_2'(A_622),k5_lattices(A_622)) = k5_lattices(A_622)
      | ~ v13_lattices(A_622)
      | ~ l1_lattices(A_622)
      | v2_struct_0(A_622) ) ),
    inference(resolution,[status(thm)],[c_28,c_2562])).

tff(c_2345,plain,(
    ! [A_568,C_569] :
      ( k2_lattices(A_568,'#skF_2'(A_568),C_569) = '#skF_2'(A_568)
      | ~ m1_subset_1(C_569,u1_struct_0(A_568))
      | ~ v13_lattices(A_568)
      | ~ l1_lattices(A_568)
      | v2_struct_0(A_568) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_2363,plain,(
    ! [A_15] :
      ( k2_lattices(A_15,'#skF_2'(A_15),k5_lattices(A_15)) = '#skF_2'(A_15)
      | ~ v13_lattices(A_15)
      | ~ l1_lattices(A_15)
      | v2_struct_0(A_15) ) ),
    inference(resolution,[status(thm)],[c_28,c_2345])).

tff(c_2597,plain,(
    ! [A_622] :
      ( k5_lattices(A_622) = '#skF_2'(A_622)
      | ~ v13_lattices(A_622)
      | ~ l1_lattices(A_622)
      | v2_struct_0(A_622)
      | ~ v13_lattices(A_622)
      | ~ l1_lattices(A_622)
      | v2_struct_0(A_622) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2591,c_2363])).

tff(c_2619,plain,(
    ! [A_624] :
      ( k5_lattices(A_624) = '#skF_2'(A_624)
      | ~ v13_lattices(A_624)
      | ~ l1_lattices(A_624)
      | v2_struct_0(A_624) ) ),
    inference(factorization,[status(thm),theory(equality)],[c_2597])).

tff(c_2622,plain,
    ( k5_lattices('#skF_8') = '#skF_2'('#skF_8')
    | ~ v13_lattices('#skF_8')
    | ~ l1_lattices('#skF_8') ),
    inference(resolution,[status(thm)],[c_2619,c_84])).

tff(c_2625,plain,(
    k5_lattices('#skF_8') = '#skF_2'('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_93,c_2331,c_2622])).

tff(c_2330,plain,(
    k15_lattice3('#skF_8',k1_xboole_0) != k5_lattices('#skF_8') ),
    inference(splitRight,[status(thm)],[c_87])).

tff(c_2626,plain,(
    k15_lattice3('#skF_8',k1_xboole_0) != '#skF_2'('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2625,c_2330])).

tff(c_2401,plain,(
    ! [A_574,B_575,C_576] :
      ( r2_hidden('#skF_4'(A_574,B_575,C_576),C_576)
      | r4_lattice3(A_574,B_575,C_576)
      | ~ m1_subset_1(B_575,u1_struct_0(A_574))
      | ~ l3_lattices(A_574)
      | v2_struct_0(A_574) ) ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_2470,plain,(
    ! [C_587,A_588,B_589] :
      ( ~ r1_tarski(C_587,'#skF_4'(A_588,B_589,C_587))
      | r4_lattice3(A_588,B_589,C_587)
      | ~ m1_subset_1(B_589,u1_struct_0(A_588))
      | ~ l3_lattices(A_588)
      | v2_struct_0(A_588) ) ),
    inference(resolution,[status(thm)],[c_2401,c_4])).

tff(c_2477,plain,(
    ! [A_593,B_594] :
      ( r4_lattice3(A_593,B_594,k1_xboole_0)
      | ~ m1_subset_1(B_594,u1_struct_0(A_593))
      | ~ l3_lattices(A_593)
      | v2_struct_0(A_593) ) ),
    inference(resolution,[status(thm)],[c_2,c_2470])).

tff(c_2501,plain,(
    ! [A_15] :
      ( r4_lattice3(A_15,k5_lattices(A_15),k1_xboole_0)
      | ~ l3_lattices(A_15)
      | ~ l1_lattices(A_15)
      | v2_struct_0(A_15) ) ),
    inference(resolution,[status(thm)],[c_28,c_2477])).

tff(c_2633,plain,
    ( r4_lattice3('#skF_8','#skF_2'('#skF_8'),k1_xboole_0)
    | ~ l3_lattices('#skF_8')
    | ~ l1_lattices('#skF_8')
    | v2_struct_0('#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_2625,c_2501])).

tff(c_2649,plain,
    ( r4_lattice3('#skF_8','#skF_2'('#skF_8'),k1_xboole_0)
    | v2_struct_0('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_93,c_78,c_2633])).

tff(c_2650,plain,(
    r4_lattice3('#skF_8','#skF_2'('#skF_8'),k1_xboole_0) ),
    inference(negUnitSimplification,[status(thm)],[c_84,c_2649])).

tff(c_2642,plain,
    ( m1_subset_1('#skF_2'('#skF_8'),u1_struct_0('#skF_8'))
    | ~ l1_lattices('#skF_8')
    | v2_struct_0('#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_2625,c_28])).

tff(c_2658,plain,
    ( m1_subset_1('#skF_2'('#skF_8'),u1_struct_0('#skF_8'))
    | v2_struct_0('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_93,c_2642])).

tff(c_2659,plain,(
    m1_subset_1('#skF_2'('#skF_8'),u1_struct_0('#skF_8')) ),
    inference(negUnitSimplification,[status(thm)],[c_84,c_2658])).

tff(c_3214,plain,(
    ! [A_666,B_667,C_668] :
      ( r1_lattices(A_666,B_667,C_668)
      | k2_lattices(A_666,B_667,C_668) != B_667
      | ~ m1_subset_1(C_668,u1_struct_0(A_666))
      | ~ m1_subset_1(B_667,u1_struct_0(A_666))
      | ~ l3_lattices(A_666)
      | ~ v9_lattices(A_666)
      | ~ v8_lattices(A_666)
      | v2_struct_0(A_666) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_3216,plain,(
    ! [B_667] :
      ( r1_lattices('#skF_8',B_667,'#skF_2'('#skF_8'))
      | k2_lattices('#skF_8',B_667,'#skF_2'('#skF_8')) != B_667
      | ~ m1_subset_1(B_667,u1_struct_0('#skF_8'))
      | ~ l3_lattices('#skF_8')
      | ~ v9_lattices('#skF_8')
      | ~ v8_lattices('#skF_8')
      | v2_struct_0('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_2659,c_3214])).

tff(c_3235,plain,(
    ! [B_667] :
      ( r1_lattices('#skF_8',B_667,'#skF_2'('#skF_8'))
      | k2_lattices('#skF_8',B_667,'#skF_2'('#skF_8')) != B_667
      | ~ m1_subset_1(B_667,u1_struct_0('#skF_8'))
      | ~ v9_lattices('#skF_8')
      | ~ v8_lattices('#skF_8')
      | v2_struct_0('#skF_8') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_3216])).

tff(c_3236,plain,(
    ! [B_667] :
      ( r1_lattices('#skF_8',B_667,'#skF_2'('#skF_8'))
      | k2_lattices('#skF_8',B_667,'#skF_2'('#skF_8')) != B_667
      | ~ m1_subset_1(B_667,u1_struct_0('#skF_8'))
      | ~ v9_lattices('#skF_8')
      | ~ v8_lattices('#skF_8') ) ),
    inference(negUnitSimplification,[status(thm)],[c_84,c_3235])).

tff(c_3245,plain,(
    ~ v8_lattices('#skF_8') ),
    inference(splitLeft,[status(thm)],[c_3236])).

tff(c_3248,plain,
    ( ~ v10_lattices('#skF_8')
    | v2_struct_0('#skF_8')
    | ~ l3_lattices('#skF_8') ),
    inference(resolution,[status(thm)],[c_8,c_3245])).

tff(c_3251,plain,(
    v2_struct_0('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_82,c_3248])).

tff(c_3253,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_84,c_3251])).

tff(c_3255,plain,(
    v8_lattices('#skF_8') ),
    inference(splitRight,[status(thm)],[c_3236])).

tff(c_3254,plain,(
    ! [B_667] :
      ( ~ v9_lattices('#skF_8')
      | r1_lattices('#skF_8',B_667,'#skF_2'('#skF_8'))
      | k2_lattices('#skF_8',B_667,'#skF_2'('#skF_8')) != B_667
      | ~ m1_subset_1(B_667,u1_struct_0('#skF_8')) ) ),
    inference(splitRight,[status(thm)],[c_3236])).

tff(c_3256,plain,(
    ~ v9_lattices('#skF_8') ),
    inference(splitLeft,[status(thm)],[c_3254])).

tff(c_3259,plain,
    ( ~ v10_lattices('#skF_8')
    | v2_struct_0('#skF_8')
    | ~ l3_lattices('#skF_8') ),
    inference(resolution,[status(thm)],[c_6,c_3256])).

tff(c_3262,plain,(
    v2_struct_0('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_82,c_3259])).

tff(c_3264,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_84,c_3262])).

tff(c_3266,plain,(
    v9_lattices('#skF_8') ),
    inference(splitRight,[status(thm)],[c_3254])).

tff(c_2711,plain,(
    ! [A_625,C_626,B_627] :
      ( k2_lattices(A_625,C_626,B_627) = k2_lattices(A_625,B_627,C_626)
      | ~ m1_subset_1(C_626,u1_struct_0(A_625))
      | ~ m1_subset_1(B_627,u1_struct_0(A_625))
      | ~ v6_lattices(A_625)
      | ~ l1_lattices(A_625)
      | v2_struct_0(A_625) ) ),
    inference(cnfTransformation,[status(thm)],[f_183])).

tff(c_2713,plain,(
    ! [B_627] :
      ( k2_lattices('#skF_8',B_627,'#skF_2'('#skF_8')) = k2_lattices('#skF_8','#skF_2'('#skF_8'),B_627)
      | ~ m1_subset_1(B_627,u1_struct_0('#skF_8'))
      | ~ v6_lattices('#skF_8')
      | ~ l1_lattices('#skF_8')
      | v2_struct_0('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_2659,c_2711])).

tff(c_2732,plain,(
    ! [B_627] :
      ( k2_lattices('#skF_8',B_627,'#skF_2'('#skF_8')) = k2_lattices('#skF_8','#skF_2'('#skF_8'),B_627)
      | ~ m1_subset_1(B_627,u1_struct_0('#skF_8'))
      | ~ v6_lattices('#skF_8')
      | v2_struct_0('#skF_8') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_93,c_2713])).

tff(c_2733,plain,(
    ! [B_627] :
      ( k2_lattices('#skF_8',B_627,'#skF_2'('#skF_8')) = k2_lattices('#skF_8','#skF_2'('#skF_8'),B_627)
      | ~ m1_subset_1(B_627,u1_struct_0('#skF_8'))
      | ~ v6_lattices('#skF_8') ) ),
    inference(negUnitSimplification,[status(thm)],[c_84,c_2732])).

tff(c_2747,plain,(
    ~ v6_lattices('#skF_8') ),
    inference(splitLeft,[status(thm)],[c_2733])).

tff(c_2750,plain,
    ( ~ v10_lattices('#skF_8')
    | v2_struct_0('#skF_8')
    | ~ l3_lattices('#skF_8') ),
    inference(resolution,[status(thm)],[c_12,c_2747])).

tff(c_2753,plain,(
    v2_struct_0('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_82,c_2750])).

tff(c_2755,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_84,c_2753])).

tff(c_2762,plain,(
    ! [B_632] :
      ( k2_lattices('#skF_8',B_632,'#skF_2'('#skF_8')) = k2_lattices('#skF_8','#skF_2'('#skF_8'),B_632)
      | ~ m1_subset_1(B_632,u1_struct_0('#skF_8')) ) ),
    inference(splitRight,[status(thm)],[c_2733])).

tff(c_2793,plain,(
    ! [B_81] :
      ( k2_lattices('#skF_8',k15_lattice3('#skF_8',B_81),'#skF_2'('#skF_8')) = k2_lattices('#skF_8','#skF_2'('#skF_8'),k15_lattice3('#skF_8',B_81))
      | ~ l3_lattices('#skF_8')
      | v2_struct_0('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_74,c_2762])).

tff(c_2826,plain,(
    ! [B_81] :
      ( k2_lattices('#skF_8',k15_lattice3('#skF_8',B_81),'#skF_2'('#skF_8')) = k2_lattices('#skF_8','#skF_2'('#skF_8'),k15_lattice3('#skF_8',B_81))
      | v2_struct_0('#skF_8') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_2793])).

tff(c_2832,plain,(
    ! [B_633] : k2_lattices('#skF_8',k15_lattice3('#skF_8',B_633),'#skF_2'('#skF_8')) = k2_lattices('#skF_8','#skF_2'('#skF_8'),k15_lattice3('#skF_8',B_633)) ),
    inference(negUnitSimplification,[status(thm)],[c_84,c_2826])).

tff(c_2364,plain,(
    ! [A_570,C_571] :
      ( k2_lattices(A_570,C_571,'#skF_2'(A_570)) = '#skF_2'(A_570)
      | ~ m1_subset_1(C_571,u1_struct_0(A_570))
      | ~ v13_lattices(A_570)
      | ~ l1_lattices(A_570)
      | v2_struct_0(A_570) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_2381,plain,(
    ! [A_80,B_81] :
      ( k2_lattices(A_80,k15_lattice3(A_80,B_81),'#skF_2'(A_80)) = '#skF_2'(A_80)
      | ~ v13_lattices(A_80)
      | ~ l1_lattices(A_80)
      | ~ l3_lattices(A_80)
      | v2_struct_0(A_80) ) ),
    inference(resolution,[status(thm)],[c_74,c_2364])).

tff(c_2838,plain,(
    ! [B_633] :
      ( k2_lattices('#skF_8','#skF_2'('#skF_8'),k15_lattice3('#skF_8',B_633)) = '#skF_2'('#skF_8')
      | ~ v13_lattices('#skF_8')
      | ~ l1_lattices('#skF_8')
      | ~ l3_lattices('#skF_8')
      | v2_struct_0('#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2832,c_2381])).

tff(c_2848,plain,(
    ! [B_633] :
      ( k2_lattices('#skF_8','#skF_2'('#skF_8'),k15_lattice3('#skF_8',B_633)) = '#skF_2'('#skF_8')
      | v2_struct_0('#skF_8') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_93,c_2331,c_2838])).

tff(c_2849,plain,(
    ! [B_633] : k2_lattices('#skF_8','#skF_2'('#skF_8'),k15_lattice3('#skF_8',B_633)) = '#skF_2'('#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_84,c_2848])).

tff(c_2827,plain,(
    ! [B_81] : k2_lattices('#skF_8',k15_lattice3('#skF_8',B_81),'#skF_2'('#skF_8')) = k2_lattices('#skF_8','#skF_2'('#skF_8'),k15_lattice3('#skF_8',B_81)) ),
    inference(negUnitSimplification,[status(thm)],[c_84,c_2826])).

tff(c_2854,plain,(
    ! [B_81] : k2_lattices('#skF_8',k15_lattice3('#skF_8',B_81),'#skF_2'('#skF_8')) = '#skF_2'('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2849,c_2827])).

tff(c_3821,plain,(
    ! [A_727,B_728,D_729] :
      ( r1_lattices(A_727,k15_lattice3(A_727,B_728),D_729)
      | ~ r4_lattice3(A_727,D_729,B_728)
      | ~ m1_subset_1(D_729,u1_struct_0(A_727))
      | ~ m1_subset_1(k15_lattice3(A_727,B_728),u1_struct_0(A_727))
      | ~ v4_lattice3(A_727)
      | ~ v10_lattices(A_727)
      | ~ l3_lattices(A_727)
      | v2_struct_0(A_727) ) ),
    inference(cnfTransformation,[status(thm)],[f_168])).

tff(c_3825,plain,(
    ! [A_730,B_731,D_732] :
      ( r1_lattices(A_730,k15_lattice3(A_730,B_731),D_732)
      | ~ r4_lattice3(A_730,D_732,B_731)
      | ~ m1_subset_1(D_732,u1_struct_0(A_730))
      | ~ v4_lattice3(A_730)
      | ~ v10_lattices(A_730)
      | ~ l3_lattices(A_730)
      | v2_struct_0(A_730) ) ),
    inference(resolution,[status(thm)],[c_74,c_3821])).

tff(c_4537,plain,(
    ! [A_808,B_809,D_810] :
      ( k2_lattices(A_808,k15_lattice3(A_808,B_809),D_810) = k15_lattice3(A_808,B_809)
      | ~ m1_subset_1(k15_lattice3(A_808,B_809),u1_struct_0(A_808))
      | ~ v9_lattices(A_808)
      | ~ v8_lattices(A_808)
      | ~ r4_lattice3(A_808,D_810,B_809)
      | ~ m1_subset_1(D_810,u1_struct_0(A_808))
      | ~ v4_lattice3(A_808)
      | ~ v10_lattices(A_808)
      | ~ l3_lattices(A_808)
      | v2_struct_0(A_808) ) ),
    inference(resolution,[status(thm)],[c_3825,c_36])).

tff(c_4541,plain,(
    ! [A_811,B_812,D_813] :
      ( k2_lattices(A_811,k15_lattice3(A_811,B_812),D_813) = k15_lattice3(A_811,B_812)
      | ~ v9_lattices(A_811)
      | ~ v8_lattices(A_811)
      | ~ r4_lattice3(A_811,D_813,B_812)
      | ~ m1_subset_1(D_813,u1_struct_0(A_811))
      | ~ v4_lattice3(A_811)
      | ~ v10_lattices(A_811)
      | ~ l3_lattices(A_811)
      | v2_struct_0(A_811) ) ),
    inference(resolution,[status(thm)],[c_74,c_4537])).

tff(c_4545,plain,(
    ! [B_812] :
      ( k2_lattices('#skF_8',k15_lattice3('#skF_8',B_812),'#skF_2'('#skF_8')) = k15_lattice3('#skF_8',B_812)
      | ~ v9_lattices('#skF_8')
      | ~ v8_lattices('#skF_8')
      | ~ r4_lattice3('#skF_8','#skF_2'('#skF_8'),B_812)
      | ~ v4_lattice3('#skF_8')
      | ~ v10_lattices('#skF_8')
      | ~ l3_lattices('#skF_8')
      | v2_struct_0('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_2659,c_4541])).

tff(c_4565,plain,(
    ! [B_812] :
      ( k15_lattice3('#skF_8',B_812) = '#skF_2'('#skF_8')
      | ~ r4_lattice3('#skF_8','#skF_2'('#skF_8'),B_812)
      | v2_struct_0('#skF_8') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_82,c_80,c_3255,c_3266,c_2854,c_4545])).

tff(c_4575,plain,(
    ! [B_814] :
      ( k15_lattice3('#skF_8',B_814) = '#skF_2'('#skF_8')
      | ~ r4_lattice3('#skF_8','#skF_2'('#skF_8'),B_814) ) ),
    inference(negUnitSimplification,[status(thm)],[c_84,c_4565])).

tff(c_4581,plain,(
    k15_lattice3('#skF_8',k1_xboole_0) = '#skF_2'('#skF_8') ),
    inference(resolution,[status(thm)],[c_2650,c_4575])).

tff(c_4590,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2626,c_4581])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:11:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.98/2.92  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.98/2.94  
% 8.98/2.94  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.98/2.94  %$ r4_lattice3 > r1_lattices > r2_hidden > r1_tarski > m1_subset_1 > v9_lattices > v8_lattices > v7_lattices > v6_lattices > v5_lattices > v4_lattices > v4_lattice3 > v2_struct_0 > v13_lattices > v10_lattices > l3_lattices > l2_lattices > l1_lattices > k2_lattices > k15_lattice3 > #nlpp > u1_struct_0 > k5_lattices > k1_xboole_0 > #skF_7 > #skF_2 > #skF_4 > #skF_3 > #skF_5 > #skF_8 > #skF_1 > #skF_6
% 8.98/2.94  
% 8.98/2.94  %Foreground sorts:
% 8.98/2.94  
% 8.98/2.94  
% 8.98/2.94  %Background operators:
% 8.98/2.94  
% 8.98/2.94  
% 8.98/2.94  %Foreground operators:
% 8.98/2.94  tff(l3_lattices, type, l3_lattices: $i > $o).
% 8.98/2.94  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 8.98/2.94  tff('#skF_7', type, '#skF_7': $i > $i).
% 8.98/2.94  tff(k2_lattices, type, k2_lattices: ($i * $i * $i) > $i).
% 8.98/2.94  tff(l2_lattices, type, l2_lattices: $i > $o).
% 8.98/2.94  tff('#skF_2', type, '#skF_2': $i > $i).
% 8.98/2.94  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.98/2.94  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 8.98/2.94  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 8.98/2.94  tff(k15_lattice3, type, k15_lattice3: ($i * $i) > $i).
% 8.98/2.94  tff(l1_lattices, type, l1_lattices: $i > $o).
% 8.98/2.94  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 8.98/2.94  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 8.98/2.94  tff(r1_lattices, type, r1_lattices: ($i * $i * $i) > $o).
% 8.98/2.94  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 8.98/2.94  tff(v4_lattices, type, v4_lattices: $i > $o).
% 8.98/2.94  tff(v6_lattices, type, v6_lattices: $i > $o).
% 8.98/2.94  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 8.98/2.94  tff(v9_lattices, type, v9_lattices: $i > $o).
% 8.98/2.94  tff(r4_lattice3, type, r4_lattice3: ($i * $i * $i) > $o).
% 8.98/2.94  tff(v4_lattice3, type, v4_lattice3: $i > $o).
% 8.98/2.94  tff(v5_lattices, type, v5_lattices: $i > $o).
% 8.98/2.94  tff(v10_lattices, type, v10_lattices: $i > $o).
% 8.98/2.94  tff('#skF_8', type, '#skF_8': $i).
% 8.98/2.94  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.98/2.94  tff(v13_lattices, type, v13_lattices: $i > $o).
% 8.98/2.94  tff(v8_lattices, type, v8_lattices: $i > $o).
% 8.98/2.94  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.98/2.94  tff(k5_lattices, type, k5_lattices: $i > $i).
% 8.98/2.94  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 8.98/2.94  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 8.98/2.94  tff('#skF_6', type, '#skF_6': $i > $i).
% 8.98/2.94  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 8.98/2.94  tff(v7_lattices, type, v7_lattices: $i > $o).
% 8.98/2.94  
% 8.98/2.96  tff(f_211, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v10_lattices(A)) & v4_lattice3(A)) & l3_lattices(A)) => ((((~v2_struct_0(A) & v10_lattices(A)) & v13_lattices(A)) & l3_lattices(A)) & (k5_lattices(A) = k15_lattice3(A, k1_xboole_0))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t50_lattice3)).
% 8.98/2.96  tff(f_86, axiom, (![A]: (l3_lattices(A) => (l1_lattices(A) & l2_lattices(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l3_lattices)).
% 8.98/2.96  tff(f_54, axiom, (![A]: (l3_lattices(A) => ((~v2_struct_0(A) & v10_lattices(A)) => ((((((~v2_struct_0(A) & v4_lattices(A)) & v5_lattices(A)) & v6_lattices(A)) & v7_lattices(A)) & v8_lattices(A)) & v9_lattices(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_lattices)).
% 8.98/2.96  tff(f_190, axiom, (![A, B]: ((~v2_struct_0(A) & l3_lattices(A)) => m1_subset_1(k15_lattice3(A, B), u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k15_lattice3)).
% 8.98/2.96  tff(f_122, axiom, (![A]: ((~v2_struct_0(A) & l1_lattices(A)) => (v13_lattices(A) <=> (?[B]: (m1_subset_1(B, u1_struct_0(A)) & (![C]: (m1_subset_1(C, u1_struct_0(A)) => ((k2_lattices(A, B, C) = B) & (k2_lattices(A, C, B) = B))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d13_lattices)).
% 8.98/2.96  tff(f_27, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 8.98/2.96  tff(f_140, axiom, (![A]: ((~v2_struct_0(A) & l3_lattices(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (r4_lattice3(A, B, C) <=> (![D]: (m1_subset_1(D, u1_struct_0(A)) => (r2_hidden(D, C) => r1_lattices(A, D, B)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d17_lattice3)).
% 8.98/2.96  tff(f_32, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 8.98/2.96  tff(f_168, axiom, (![A]: ((~v2_struct_0(A) & l3_lattices(A)) => ((((~v2_struct_0(A) & v10_lattices(A)) & v4_lattice3(A)) & l3_lattices(A)) => (![B, C]: (m1_subset_1(C, u1_struct_0(A)) => ((C = k15_lattice3(A, B)) <=> (r4_lattice3(A, C, B) & (![D]: (m1_subset_1(D, u1_struct_0(A)) => (r4_lattice3(A, D, B) => r1_lattices(A, C, D))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d21_lattice3)).
% 8.98/2.96  tff(f_105, axiom, (![A]: ((((~v2_struct_0(A) & v8_lattices(A)) & v9_lattices(A)) & l3_lattices(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r1_lattices(A, B, C) <=> (k2_lattices(A, B, C) = B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t21_lattices)).
% 8.98/2.96  tff(f_183, axiom, (![A]: ((~v2_struct_0(A) & l1_lattices(A)) => (v6_lattices(A) <=> (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (k2_lattices(A, B, C) = k2_lattices(A, C, B))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d6_lattices)).
% 8.98/2.96  tff(f_80, axiom, (![A]: ((~v2_struct_0(A) & l1_lattices(A)) => m1_subset_1(k5_lattices(A), u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k5_lattices)).
% 8.98/2.96  tff(f_73, axiom, (![A]: ((~v2_struct_0(A) & l1_lattices(A)) => (v13_lattices(A) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => ((B = k5_lattices(A)) <=> (![C]: (m1_subset_1(C, u1_struct_0(A)) => ((k2_lattices(A, B, C) = B) & (k2_lattices(A, C, B) = B)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d16_lattices)).
% 8.98/2.96  tff(c_78, plain, (l3_lattices('#skF_8')), inference(cnfTransformation, [status(thm)], [f_211])).
% 8.98/2.96  tff(c_89, plain, (![A_83]: (l1_lattices(A_83) | ~l3_lattices(A_83))), inference(cnfTransformation, [status(thm)], [f_86])).
% 8.98/2.96  tff(c_93, plain, (l1_lattices('#skF_8')), inference(resolution, [status(thm)], [c_78, c_89])).
% 8.98/2.96  tff(c_84, plain, (~v2_struct_0('#skF_8')), inference(cnfTransformation, [status(thm)], [f_211])).
% 8.98/2.96  tff(c_82, plain, (v10_lattices('#skF_8')), inference(cnfTransformation, [status(thm)], [f_211])).
% 8.98/2.96  tff(c_76, plain, (k15_lattice3('#skF_8', k1_xboole_0)!=k5_lattices('#skF_8') | ~l3_lattices('#skF_8') | ~v13_lattices('#skF_8') | ~v10_lattices('#skF_8') | v2_struct_0('#skF_8')), inference(cnfTransformation, [status(thm)], [f_211])).
% 8.98/2.96  tff(c_86, plain, (k15_lattice3('#skF_8', k1_xboole_0)!=k5_lattices('#skF_8') | ~v13_lattices('#skF_8') | v2_struct_0('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_82, c_78, c_76])).
% 8.98/2.96  tff(c_87, plain, (k15_lattice3('#skF_8', k1_xboole_0)!=k5_lattices('#skF_8') | ~v13_lattices('#skF_8')), inference(negUnitSimplification, [status(thm)], [c_84, c_86])).
% 8.98/2.96  tff(c_99, plain, (~v13_lattices('#skF_8')), inference(splitLeft, [status(thm)], [c_87])).
% 8.98/2.96  tff(c_80, plain, (v4_lattice3('#skF_8')), inference(cnfTransformation, [status(thm)], [f_211])).
% 8.98/2.96  tff(c_12, plain, (![A_4]: (v6_lattices(A_4) | ~v10_lattices(A_4) | v2_struct_0(A_4) | ~l3_lattices(A_4))), inference(cnfTransformation, [status(thm)], [f_54])).
% 8.98/2.96  tff(c_8, plain, (![A_4]: (v8_lattices(A_4) | ~v10_lattices(A_4) | v2_struct_0(A_4) | ~l3_lattices(A_4))), inference(cnfTransformation, [status(thm)], [f_54])).
% 8.98/2.96  tff(c_6, plain, (![A_4]: (v9_lattices(A_4) | ~v10_lattices(A_4) | v2_struct_0(A_4) | ~l3_lattices(A_4))), inference(cnfTransformation, [status(thm)], [f_54])).
% 8.98/2.96  tff(c_74, plain, (![A_80, B_81]: (m1_subset_1(k15_lattice3(A_80, B_81), u1_struct_0(A_80)) | ~l3_lattices(A_80) | v2_struct_0(A_80))), inference(cnfTransformation, [status(thm)], [f_190])).
% 8.98/2.96  tff(c_40, plain, (![A_24, B_33]: (m1_subset_1('#skF_3'(A_24, B_33), u1_struct_0(A_24)) | v13_lattices(A_24) | ~m1_subset_1(B_33, u1_struct_0(A_24)) | ~l1_lattices(A_24) | v2_struct_0(A_24))), inference(cnfTransformation, [status(thm)], [f_122])).
% 8.98/2.96  tff(c_2, plain, (![A_1]: (r1_tarski(k1_xboole_0, A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 8.98/2.96  tff(c_169, plain, (![A_107, B_108, C_109]: (r2_hidden('#skF_4'(A_107, B_108, C_109), C_109) | r4_lattice3(A_107, B_108, C_109) | ~m1_subset_1(B_108, u1_struct_0(A_107)) | ~l3_lattices(A_107) | v2_struct_0(A_107))), inference(cnfTransformation, [status(thm)], [f_140])).
% 8.98/2.96  tff(c_4, plain, (![B_3, A_2]: (~r1_tarski(B_3, A_2) | ~r2_hidden(A_2, B_3))), inference(cnfTransformation, [status(thm)], [f_32])).
% 8.98/2.96  tff(c_238, plain, (![C_120, A_121, B_122]: (~r1_tarski(C_120, '#skF_4'(A_121, B_122, C_120)) | r4_lattice3(A_121, B_122, C_120) | ~m1_subset_1(B_122, u1_struct_0(A_121)) | ~l3_lattices(A_121) | v2_struct_0(A_121))), inference(resolution, [status(thm)], [c_169, c_4])).
% 8.98/2.96  tff(c_251, plain, (![A_126, B_127]: (r4_lattice3(A_126, B_127, k1_xboole_0) | ~m1_subset_1(B_127, u1_struct_0(A_126)) | ~l3_lattices(A_126) | v2_struct_0(A_126))), inference(resolution, [status(thm)], [c_2, c_238])).
% 8.98/2.96  tff(c_274, plain, (![A_24, B_33]: (r4_lattice3(A_24, '#skF_3'(A_24, B_33), k1_xboole_0) | ~l3_lattices(A_24) | v13_lattices(A_24) | ~m1_subset_1(B_33, u1_struct_0(A_24)) | ~l1_lattices(A_24) | v2_struct_0(A_24))), inference(resolution, [status(thm)], [c_40, c_251])).
% 8.98/2.96  tff(c_858, plain, (![A_242, B_243, D_244]: (r1_lattices(A_242, k15_lattice3(A_242, B_243), D_244) | ~r4_lattice3(A_242, D_244, B_243) | ~m1_subset_1(D_244, u1_struct_0(A_242)) | ~m1_subset_1(k15_lattice3(A_242, B_243), u1_struct_0(A_242)) | ~v4_lattice3(A_242) | ~v10_lattices(A_242) | ~l3_lattices(A_242) | v2_struct_0(A_242))), inference(cnfTransformation, [status(thm)], [f_168])).
% 8.98/2.96  tff(c_862, plain, (![A_245, B_246, D_247]: (r1_lattices(A_245, k15_lattice3(A_245, B_246), D_247) | ~r4_lattice3(A_245, D_247, B_246) | ~m1_subset_1(D_247, u1_struct_0(A_245)) | ~v4_lattice3(A_245) | ~v10_lattices(A_245) | ~l3_lattices(A_245) | v2_struct_0(A_245))), inference(resolution, [status(thm)], [c_74, c_858])).
% 8.98/2.96  tff(c_36, plain, (![A_17, B_21, C_23]: (k2_lattices(A_17, B_21, C_23)=B_21 | ~r1_lattices(A_17, B_21, C_23) | ~m1_subset_1(C_23, u1_struct_0(A_17)) | ~m1_subset_1(B_21, u1_struct_0(A_17)) | ~l3_lattices(A_17) | ~v9_lattices(A_17) | ~v8_lattices(A_17) | v2_struct_0(A_17))), inference(cnfTransformation, [status(thm)], [f_105])).
% 8.98/2.96  tff(c_1286, plain, (![A_320, B_321, D_322]: (k2_lattices(A_320, k15_lattice3(A_320, B_321), D_322)=k15_lattice3(A_320, B_321) | ~m1_subset_1(k15_lattice3(A_320, B_321), u1_struct_0(A_320)) | ~v9_lattices(A_320) | ~v8_lattices(A_320) | ~r4_lattice3(A_320, D_322, B_321) | ~m1_subset_1(D_322, u1_struct_0(A_320)) | ~v4_lattice3(A_320) | ~v10_lattices(A_320) | ~l3_lattices(A_320) | v2_struct_0(A_320))), inference(resolution, [status(thm)], [c_862, c_36])).
% 8.98/2.96  tff(c_1290, plain, (![A_323, B_324, D_325]: (k2_lattices(A_323, k15_lattice3(A_323, B_324), D_325)=k15_lattice3(A_323, B_324) | ~v9_lattices(A_323) | ~v8_lattices(A_323) | ~r4_lattice3(A_323, D_325, B_324) | ~m1_subset_1(D_325, u1_struct_0(A_323)) | ~v4_lattice3(A_323) | ~v10_lattices(A_323) | ~l3_lattices(A_323) | v2_struct_0(A_323))), inference(resolution, [status(thm)], [c_74, c_1286])).
% 8.98/2.96  tff(c_1312, plain, (![A_24, B_324, B_33]: (k2_lattices(A_24, k15_lattice3(A_24, B_324), '#skF_3'(A_24, B_33))=k15_lattice3(A_24, B_324) | ~v9_lattices(A_24) | ~v8_lattices(A_24) | ~r4_lattice3(A_24, '#skF_3'(A_24, B_33), B_324) | ~v4_lattice3(A_24) | ~v10_lattices(A_24) | ~l3_lattices(A_24) | v13_lattices(A_24) | ~m1_subset_1(B_33, u1_struct_0(A_24)) | ~l1_lattices(A_24) | v2_struct_0(A_24))), inference(resolution, [status(thm)], [c_40, c_1290])).
% 8.98/2.96  tff(c_1427, plain, (![A_349, B_350, B_351]: (k2_lattices(A_349, k15_lattice3(A_349, B_350), '#skF_3'(A_349, B_351))=k15_lattice3(A_349, B_350) | ~v9_lattices(A_349) | ~v8_lattices(A_349) | ~r4_lattice3(A_349, '#skF_3'(A_349, B_351), B_350) | ~v4_lattice3(A_349) | ~v10_lattices(A_349) | ~l3_lattices(A_349) | v13_lattices(A_349) | ~m1_subset_1(B_351, u1_struct_0(A_349)) | ~l1_lattices(A_349) | v2_struct_0(A_349))), inference(resolution, [status(thm)], [c_40, c_1290])).
% 8.98/2.96  tff(c_394, plain, (![A_158, C_159, B_160]: (k2_lattices(A_158, C_159, B_160)=k2_lattices(A_158, B_160, C_159) | ~m1_subset_1(C_159, u1_struct_0(A_158)) | ~m1_subset_1(B_160, u1_struct_0(A_158)) | ~v6_lattices(A_158) | ~l1_lattices(A_158) | v2_struct_0(A_158))), inference(cnfTransformation, [status(thm)], [f_183])).
% 8.98/2.96  tff(c_910, plain, (![A_259, B_260, B_261]: (k2_lattices(A_259, B_260, '#skF_3'(A_259, B_261))=k2_lattices(A_259, '#skF_3'(A_259, B_261), B_260) | ~m1_subset_1(B_260, u1_struct_0(A_259)) | ~v6_lattices(A_259) | v13_lattices(A_259) | ~m1_subset_1(B_261, u1_struct_0(A_259)) | ~l1_lattices(A_259) | v2_struct_0(A_259))), inference(resolution, [status(thm)], [c_40, c_394])).
% 8.98/2.96  tff(c_936, plain, (![A_80, B_81, B_261]: (k2_lattices(A_80, k15_lattice3(A_80, B_81), '#skF_3'(A_80, B_261))=k2_lattices(A_80, '#skF_3'(A_80, B_261), k15_lattice3(A_80, B_81)) | ~v6_lattices(A_80) | v13_lattices(A_80) | ~m1_subset_1(B_261, u1_struct_0(A_80)) | ~l1_lattices(A_80) | ~l3_lattices(A_80) | v2_struct_0(A_80))), inference(resolution, [status(thm)], [c_74, c_910])).
% 8.98/2.96  tff(c_2269, plain, (![A_540, B_541, B_542]: (k2_lattices(A_540, '#skF_3'(A_540, B_541), k15_lattice3(A_540, B_542))=k15_lattice3(A_540, B_542) | ~v6_lattices(A_540) | v13_lattices(A_540) | ~m1_subset_1(B_541, u1_struct_0(A_540)) | ~l1_lattices(A_540) | ~l3_lattices(A_540) | v2_struct_0(A_540) | ~v9_lattices(A_540) | ~v8_lattices(A_540) | ~r4_lattice3(A_540, '#skF_3'(A_540, B_541), B_542) | ~v4_lattice3(A_540) | ~v10_lattices(A_540) | ~l3_lattices(A_540) | v13_lattices(A_540) | ~m1_subset_1(B_541, u1_struct_0(A_540)) | ~l1_lattices(A_540) | v2_struct_0(A_540))), inference(superposition, [status(thm), theory('equality')], [c_1427, c_936])).
% 8.98/2.96  tff(c_38, plain, (![A_24, B_33]: (k2_lattices(A_24, '#skF_3'(A_24, B_33), B_33)!=B_33 | k2_lattices(A_24, B_33, '#skF_3'(A_24, B_33))!=B_33 | v13_lattices(A_24) | ~m1_subset_1(B_33, u1_struct_0(A_24)) | ~l1_lattices(A_24) | v2_struct_0(A_24))), inference(cnfTransformation, [status(thm)], [f_122])).
% 8.98/2.96  tff(c_2288, plain, (![A_543, B_544]: (k2_lattices(A_543, k15_lattice3(A_543, B_544), '#skF_3'(A_543, k15_lattice3(A_543, B_544)))!=k15_lattice3(A_543, B_544) | ~v6_lattices(A_543) | ~v9_lattices(A_543) | ~v8_lattices(A_543) | ~r4_lattice3(A_543, '#skF_3'(A_543, k15_lattice3(A_543, B_544)), B_544) | ~v4_lattice3(A_543) | ~v10_lattices(A_543) | ~l3_lattices(A_543) | v13_lattices(A_543) | ~m1_subset_1(k15_lattice3(A_543, B_544), u1_struct_0(A_543)) | ~l1_lattices(A_543) | v2_struct_0(A_543))), inference(superposition, [status(thm), theory('equality')], [c_2269, c_38])).
% 8.98/2.96  tff(c_2294, plain, (![A_545, B_546]: (~v6_lattices(A_545) | ~v9_lattices(A_545) | ~v8_lattices(A_545) | ~r4_lattice3(A_545, '#skF_3'(A_545, k15_lattice3(A_545, B_546)), B_546) | ~v4_lattice3(A_545) | ~v10_lattices(A_545) | ~l3_lattices(A_545) | v13_lattices(A_545) | ~m1_subset_1(k15_lattice3(A_545, B_546), u1_struct_0(A_545)) | ~l1_lattices(A_545) | v2_struct_0(A_545))), inference(superposition, [status(thm), theory('equality')], [c_1312, c_2288])).
% 8.98/2.96  tff(c_2300, plain, (![A_547]: (~v6_lattices(A_547) | ~v9_lattices(A_547) | ~v8_lattices(A_547) | ~v4_lattice3(A_547) | ~v10_lattices(A_547) | ~l3_lattices(A_547) | v13_lattices(A_547) | ~m1_subset_1(k15_lattice3(A_547, k1_xboole_0), u1_struct_0(A_547)) | ~l1_lattices(A_547) | v2_struct_0(A_547))), inference(resolution, [status(thm)], [c_274, c_2294])).
% 8.98/2.96  tff(c_2306, plain, (![A_548]: (~v6_lattices(A_548) | ~v9_lattices(A_548) | ~v8_lattices(A_548) | ~v4_lattice3(A_548) | ~v10_lattices(A_548) | v13_lattices(A_548) | ~l1_lattices(A_548) | ~l3_lattices(A_548) | v2_struct_0(A_548))), inference(resolution, [status(thm)], [c_74, c_2300])).
% 8.98/2.96  tff(c_2311, plain, (![A_549]: (~v6_lattices(A_549) | ~v8_lattices(A_549) | ~v4_lattice3(A_549) | v13_lattices(A_549) | ~l1_lattices(A_549) | ~v10_lattices(A_549) | v2_struct_0(A_549) | ~l3_lattices(A_549))), inference(resolution, [status(thm)], [c_6, c_2306])).
% 8.98/2.96  tff(c_2316, plain, (![A_550]: (~v6_lattices(A_550) | ~v4_lattice3(A_550) | v13_lattices(A_550) | ~l1_lattices(A_550) | ~v10_lattices(A_550) | v2_struct_0(A_550) | ~l3_lattices(A_550))), inference(resolution, [status(thm)], [c_8, c_2311])).
% 8.98/2.96  tff(c_2321, plain, (![A_551]: (~v4_lattice3(A_551) | v13_lattices(A_551) | ~l1_lattices(A_551) | ~v10_lattices(A_551) | v2_struct_0(A_551) | ~l3_lattices(A_551))), inference(resolution, [status(thm)], [c_12, c_2316])).
% 8.98/2.96  tff(c_2324, plain, (v13_lattices('#skF_8') | ~l1_lattices('#skF_8') | ~v10_lattices('#skF_8') | v2_struct_0('#skF_8') | ~l3_lattices('#skF_8')), inference(resolution, [status(thm)], [c_80, c_2321])).
% 8.98/2.96  tff(c_2327, plain, (v13_lattices('#skF_8') | v2_struct_0('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_82, c_93, c_2324])).
% 8.98/2.96  tff(c_2329, plain, $false, inference(negUnitSimplification, [status(thm)], [c_84, c_99, c_2327])).
% 8.98/2.96  tff(c_2331, plain, (v13_lattices('#skF_8')), inference(splitRight, [status(thm)], [c_87])).
% 8.98/2.96  tff(c_28, plain, (![A_15]: (m1_subset_1(k5_lattices(A_15), u1_struct_0(A_15)) | ~l1_lattices(A_15) | v2_struct_0(A_15))), inference(cnfTransformation, [status(thm)], [f_80])).
% 8.98/2.96  tff(c_42, plain, (![A_24]: (m1_subset_1('#skF_2'(A_24), u1_struct_0(A_24)) | ~v13_lattices(A_24) | ~l1_lattices(A_24) | v2_struct_0(A_24))), inference(cnfTransformation, [status(thm)], [f_122])).
% 8.98/2.96  tff(c_2537, plain, (![A_617, C_618]: (k2_lattices(A_617, C_618, k5_lattices(A_617))=k5_lattices(A_617) | ~m1_subset_1(C_618, u1_struct_0(A_617)) | ~m1_subset_1(k5_lattices(A_617), u1_struct_0(A_617)) | ~v13_lattices(A_617) | ~l1_lattices(A_617) | v2_struct_0(A_617))), inference(cnfTransformation, [status(thm)], [f_73])).
% 8.98/2.96  tff(c_2562, plain, (![A_619]: (k2_lattices(A_619, '#skF_2'(A_619), k5_lattices(A_619))=k5_lattices(A_619) | ~m1_subset_1(k5_lattices(A_619), u1_struct_0(A_619)) | ~v13_lattices(A_619) | ~l1_lattices(A_619) | v2_struct_0(A_619))), inference(resolution, [status(thm)], [c_42, c_2537])).
% 8.98/2.96  tff(c_2591, plain, (![A_622]: (k2_lattices(A_622, '#skF_2'(A_622), k5_lattices(A_622))=k5_lattices(A_622) | ~v13_lattices(A_622) | ~l1_lattices(A_622) | v2_struct_0(A_622))), inference(resolution, [status(thm)], [c_28, c_2562])).
% 8.98/2.96  tff(c_2345, plain, (![A_568, C_569]: (k2_lattices(A_568, '#skF_2'(A_568), C_569)='#skF_2'(A_568) | ~m1_subset_1(C_569, u1_struct_0(A_568)) | ~v13_lattices(A_568) | ~l1_lattices(A_568) | v2_struct_0(A_568))), inference(cnfTransformation, [status(thm)], [f_122])).
% 8.98/2.96  tff(c_2363, plain, (![A_15]: (k2_lattices(A_15, '#skF_2'(A_15), k5_lattices(A_15))='#skF_2'(A_15) | ~v13_lattices(A_15) | ~l1_lattices(A_15) | v2_struct_0(A_15))), inference(resolution, [status(thm)], [c_28, c_2345])).
% 8.98/2.96  tff(c_2597, plain, (![A_622]: (k5_lattices(A_622)='#skF_2'(A_622) | ~v13_lattices(A_622) | ~l1_lattices(A_622) | v2_struct_0(A_622) | ~v13_lattices(A_622) | ~l1_lattices(A_622) | v2_struct_0(A_622))), inference(superposition, [status(thm), theory('equality')], [c_2591, c_2363])).
% 8.98/2.96  tff(c_2619, plain, (![A_624]: (k5_lattices(A_624)='#skF_2'(A_624) | ~v13_lattices(A_624) | ~l1_lattices(A_624) | v2_struct_0(A_624))), inference(factorization, [status(thm), theory('equality')], [c_2597])).
% 8.98/2.96  tff(c_2622, plain, (k5_lattices('#skF_8')='#skF_2'('#skF_8') | ~v13_lattices('#skF_8') | ~l1_lattices('#skF_8')), inference(resolution, [status(thm)], [c_2619, c_84])).
% 8.98/2.96  tff(c_2625, plain, (k5_lattices('#skF_8')='#skF_2'('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_93, c_2331, c_2622])).
% 8.98/2.96  tff(c_2330, plain, (k15_lattice3('#skF_8', k1_xboole_0)!=k5_lattices('#skF_8')), inference(splitRight, [status(thm)], [c_87])).
% 8.98/2.96  tff(c_2626, plain, (k15_lattice3('#skF_8', k1_xboole_0)!='#skF_2'('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_2625, c_2330])).
% 8.98/2.96  tff(c_2401, plain, (![A_574, B_575, C_576]: (r2_hidden('#skF_4'(A_574, B_575, C_576), C_576) | r4_lattice3(A_574, B_575, C_576) | ~m1_subset_1(B_575, u1_struct_0(A_574)) | ~l3_lattices(A_574) | v2_struct_0(A_574))), inference(cnfTransformation, [status(thm)], [f_140])).
% 8.98/2.96  tff(c_2470, plain, (![C_587, A_588, B_589]: (~r1_tarski(C_587, '#skF_4'(A_588, B_589, C_587)) | r4_lattice3(A_588, B_589, C_587) | ~m1_subset_1(B_589, u1_struct_0(A_588)) | ~l3_lattices(A_588) | v2_struct_0(A_588))), inference(resolution, [status(thm)], [c_2401, c_4])).
% 8.98/2.96  tff(c_2477, plain, (![A_593, B_594]: (r4_lattice3(A_593, B_594, k1_xboole_0) | ~m1_subset_1(B_594, u1_struct_0(A_593)) | ~l3_lattices(A_593) | v2_struct_0(A_593))), inference(resolution, [status(thm)], [c_2, c_2470])).
% 8.98/2.96  tff(c_2501, plain, (![A_15]: (r4_lattice3(A_15, k5_lattices(A_15), k1_xboole_0) | ~l3_lattices(A_15) | ~l1_lattices(A_15) | v2_struct_0(A_15))), inference(resolution, [status(thm)], [c_28, c_2477])).
% 8.98/2.96  tff(c_2633, plain, (r4_lattice3('#skF_8', '#skF_2'('#skF_8'), k1_xboole_0) | ~l3_lattices('#skF_8') | ~l1_lattices('#skF_8') | v2_struct_0('#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_2625, c_2501])).
% 8.98/2.96  tff(c_2649, plain, (r4_lattice3('#skF_8', '#skF_2'('#skF_8'), k1_xboole_0) | v2_struct_0('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_93, c_78, c_2633])).
% 8.98/2.96  tff(c_2650, plain, (r4_lattice3('#skF_8', '#skF_2'('#skF_8'), k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_84, c_2649])).
% 8.98/2.96  tff(c_2642, plain, (m1_subset_1('#skF_2'('#skF_8'), u1_struct_0('#skF_8')) | ~l1_lattices('#skF_8') | v2_struct_0('#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_2625, c_28])).
% 8.98/2.96  tff(c_2658, plain, (m1_subset_1('#skF_2'('#skF_8'), u1_struct_0('#skF_8')) | v2_struct_0('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_93, c_2642])).
% 8.98/2.96  tff(c_2659, plain, (m1_subset_1('#skF_2'('#skF_8'), u1_struct_0('#skF_8'))), inference(negUnitSimplification, [status(thm)], [c_84, c_2658])).
% 8.98/2.96  tff(c_3214, plain, (![A_666, B_667, C_668]: (r1_lattices(A_666, B_667, C_668) | k2_lattices(A_666, B_667, C_668)!=B_667 | ~m1_subset_1(C_668, u1_struct_0(A_666)) | ~m1_subset_1(B_667, u1_struct_0(A_666)) | ~l3_lattices(A_666) | ~v9_lattices(A_666) | ~v8_lattices(A_666) | v2_struct_0(A_666))), inference(cnfTransformation, [status(thm)], [f_105])).
% 8.98/2.96  tff(c_3216, plain, (![B_667]: (r1_lattices('#skF_8', B_667, '#skF_2'('#skF_8')) | k2_lattices('#skF_8', B_667, '#skF_2'('#skF_8'))!=B_667 | ~m1_subset_1(B_667, u1_struct_0('#skF_8')) | ~l3_lattices('#skF_8') | ~v9_lattices('#skF_8') | ~v8_lattices('#skF_8') | v2_struct_0('#skF_8'))), inference(resolution, [status(thm)], [c_2659, c_3214])).
% 8.98/2.96  tff(c_3235, plain, (![B_667]: (r1_lattices('#skF_8', B_667, '#skF_2'('#skF_8')) | k2_lattices('#skF_8', B_667, '#skF_2'('#skF_8'))!=B_667 | ~m1_subset_1(B_667, u1_struct_0('#skF_8')) | ~v9_lattices('#skF_8') | ~v8_lattices('#skF_8') | v2_struct_0('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_3216])).
% 8.98/2.96  tff(c_3236, plain, (![B_667]: (r1_lattices('#skF_8', B_667, '#skF_2'('#skF_8')) | k2_lattices('#skF_8', B_667, '#skF_2'('#skF_8'))!=B_667 | ~m1_subset_1(B_667, u1_struct_0('#skF_8')) | ~v9_lattices('#skF_8') | ~v8_lattices('#skF_8'))), inference(negUnitSimplification, [status(thm)], [c_84, c_3235])).
% 8.98/2.96  tff(c_3245, plain, (~v8_lattices('#skF_8')), inference(splitLeft, [status(thm)], [c_3236])).
% 8.98/2.96  tff(c_3248, plain, (~v10_lattices('#skF_8') | v2_struct_0('#skF_8') | ~l3_lattices('#skF_8')), inference(resolution, [status(thm)], [c_8, c_3245])).
% 8.98/2.96  tff(c_3251, plain, (v2_struct_0('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_82, c_3248])).
% 8.98/2.96  tff(c_3253, plain, $false, inference(negUnitSimplification, [status(thm)], [c_84, c_3251])).
% 8.98/2.96  tff(c_3255, plain, (v8_lattices('#skF_8')), inference(splitRight, [status(thm)], [c_3236])).
% 8.98/2.96  tff(c_3254, plain, (![B_667]: (~v9_lattices('#skF_8') | r1_lattices('#skF_8', B_667, '#skF_2'('#skF_8')) | k2_lattices('#skF_8', B_667, '#skF_2'('#skF_8'))!=B_667 | ~m1_subset_1(B_667, u1_struct_0('#skF_8')))), inference(splitRight, [status(thm)], [c_3236])).
% 8.98/2.96  tff(c_3256, plain, (~v9_lattices('#skF_8')), inference(splitLeft, [status(thm)], [c_3254])).
% 8.98/2.96  tff(c_3259, plain, (~v10_lattices('#skF_8') | v2_struct_0('#skF_8') | ~l3_lattices('#skF_8')), inference(resolution, [status(thm)], [c_6, c_3256])).
% 8.98/2.96  tff(c_3262, plain, (v2_struct_0('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_82, c_3259])).
% 8.98/2.96  tff(c_3264, plain, $false, inference(negUnitSimplification, [status(thm)], [c_84, c_3262])).
% 8.98/2.96  tff(c_3266, plain, (v9_lattices('#skF_8')), inference(splitRight, [status(thm)], [c_3254])).
% 8.98/2.96  tff(c_2711, plain, (![A_625, C_626, B_627]: (k2_lattices(A_625, C_626, B_627)=k2_lattices(A_625, B_627, C_626) | ~m1_subset_1(C_626, u1_struct_0(A_625)) | ~m1_subset_1(B_627, u1_struct_0(A_625)) | ~v6_lattices(A_625) | ~l1_lattices(A_625) | v2_struct_0(A_625))), inference(cnfTransformation, [status(thm)], [f_183])).
% 8.98/2.96  tff(c_2713, plain, (![B_627]: (k2_lattices('#skF_8', B_627, '#skF_2'('#skF_8'))=k2_lattices('#skF_8', '#skF_2'('#skF_8'), B_627) | ~m1_subset_1(B_627, u1_struct_0('#skF_8')) | ~v6_lattices('#skF_8') | ~l1_lattices('#skF_8') | v2_struct_0('#skF_8'))), inference(resolution, [status(thm)], [c_2659, c_2711])).
% 8.98/2.96  tff(c_2732, plain, (![B_627]: (k2_lattices('#skF_8', B_627, '#skF_2'('#skF_8'))=k2_lattices('#skF_8', '#skF_2'('#skF_8'), B_627) | ~m1_subset_1(B_627, u1_struct_0('#skF_8')) | ~v6_lattices('#skF_8') | v2_struct_0('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_93, c_2713])).
% 8.98/2.96  tff(c_2733, plain, (![B_627]: (k2_lattices('#skF_8', B_627, '#skF_2'('#skF_8'))=k2_lattices('#skF_8', '#skF_2'('#skF_8'), B_627) | ~m1_subset_1(B_627, u1_struct_0('#skF_8')) | ~v6_lattices('#skF_8'))), inference(negUnitSimplification, [status(thm)], [c_84, c_2732])).
% 8.98/2.96  tff(c_2747, plain, (~v6_lattices('#skF_8')), inference(splitLeft, [status(thm)], [c_2733])).
% 8.98/2.96  tff(c_2750, plain, (~v10_lattices('#skF_8') | v2_struct_0('#skF_8') | ~l3_lattices('#skF_8')), inference(resolution, [status(thm)], [c_12, c_2747])).
% 8.98/2.96  tff(c_2753, plain, (v2_struct_0('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_82, c_2750])).
% 8.98/2.96  tff(c_2755, plain, $false, inference(negUnitSimplification, [status(thm)], [c_84, c_2753])).
% 8.98/2.96  tff(c_2762, plain, (![B_632]: (k2_lattices('#skF_8', B_632, '#skF_2'('#skF_8'))=k2_lattices('#skF_8', '#skF_2'('#skF_8'), B_632) | ~m1_subset_1(B_632, u1_struct_0('#skF_8')))), inference(splitRight, [status(thm)], [c_2733])).
% 8.98/2.96  tff(c_2793, plain, (![B_81]: (k2_lattices('#skF_8', k15_lattice3('#skF_8', B_81), '#skF_2'('#skF_8'))=k2_lattices('#skF_8', '#skF_2'('#skF_8'), k15_lattice3('#skF_8', B_81)) | ~l3_lattices('#skF_8') | v2_struct_0('#skF_8'))), inference(resolution, [status(thm)], [c_74, c_2762])).
% 8.98/2.96  tff(c_2826, plain, (![B_81]: (k2_lattices('#skF_8', k15_lattice3('#skF_8', B_81), '#skF_2'('#skF_8'))=k2_lattices('#skF_8', '#skF_2'('#skF_8'), k15_lattice3('#skF_8', B_81)) | v2_struct_0('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_2793])).
% 8.98/2.96  tff(c_2832, plain, (![B_633]: (k2_lattices('#skF_8', k15_lattice3('#skF_8', B_633), '#skF_2'('#skF_8'))=k2_lattices('#skF_8', '#skF_2'('#skF_8'), k15_lattice3('#skF_8', B_633)))), inference(negUnitSimplification, [status(thm)], [c_84, c_2826])).
% 8.98/2.96  tff(c_2364, plain, (![A_570, C_571]: (k2_lattices(A_570, C_571, '#skF_2'(A_570))='#skF_2'(A_570) | ~m1_subset_1(C_571, u1_struct_0(A_570)) | ~v13_lattices(A_570) | ~l1_lattices(A_570) | v2_struct_0(A_570))), inference(cnfTransformation, [status(thm)], [f_122])).
% 8.98/2.96  tff(c_2381, plain, (![A_80, B_81]: (k2_lattices(A_80, k15_lattice3(A_80, B_81), '#skF_2'(A_80))='#skF_2'(A_80) | ~v13_lattices(A_80) | ~l1_lattices(A_80) | ~l3_lattices(A_80) | v2_struct_0(A_80))), inference(resolution, [status(thm)], [c_74, c_2364])).
% 8.98/2.96  tff(c_2838, plain, (![B_633]: (k2_lattices('#skF_8', '#skF_2'('#skF_8'), k15_lattice3('#skF_8', B_633))='#skF_2'('#skF_8') | ~v13_lattices('#skF_8') | ~l1_lattices('#skF_8') | ~l3_lattices('#skF_8') | v2_struct_0('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_2832, c_2381])).
% 8.98/2.96  tff(c_2848, plain, (![B_633]: (k2_lattices('#skF_8', '#skF_2'('#skF_8'), k15_lattice3('#skF_8', B_633))='#skF_2'('#skF_8') | v2_struct_0('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_93, c_2331, c_2838])).
% 8.98/2.96  tff(c_2849, plain, (![B_633]: (k2_lattices('#skF_8', '#skF_2'('#skF_8'), k15_lattice3('#skF_8', B_633))='#skF_2'('#skF_8'))), inference(negUnitSimplification, [status(thm)], [c_84, c_2848])).
% 8.98/2.96  tff(c_2827, plain, (![B_81]: (k2_lattices('#skF_8', k15_lattice3('#skF_8', B_81), '#skF_2'('#skF_8'))=k2_lattices('#skF_8', '#skF_2'('#skF_8'), k15_lattice3('#skF_8', B_81)))), inference(negUnitSimplification, [status(thm)], [c_84, c_2826])).
% 8.98/2.96  tff(c_2854, plain, (![B_81]: (k2_lattices('#skF_8', k15_lattice3('#skF_8', B_81), '#skF_2'('#skF_8'))='#skF_2'('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_2849, c_2827])).
% 8.98/2.96  tff(c_3821, plain, (![A_727, B_728, D_729]: (r1_lattices(A_727, k15_lattice3(A_727, B_728), D_729) | ~r4_lattice3(A_727, D_729, B_728) | ~m1_subset_1(D_729, u1_struct_0(A_727)) | ~m1_subset_1(k15_lattice3(A_727, B_728), u1_struct_0(A_727)) | ~v4_lattice3(A_727) | ~v10_lattices(A_727) | ~l3_lattices(A_727) | v2_struct_0(A_727))), inference(cnfTransformation, [status(thm)], [f_168])).
% 8.98/2.96  tff(c_3825, plain, (![A_730, B_731, D_732]: (r1_lattices(A_730, k15_lattice3(A_730, B_731), D_732) | ~r4_lattice3(A_730, D_732, B_731) | ~m1_subset_1(D_732, u1_struct_0(A_730)) | ~v4_lattice3(A_730) | ~v10_lattices(A_730) | ~l3_lattices(A_730) | v2_struct_0(A_730))), inference(resolution, [status(thm)], [c_74, c_3821])).
% 8.98/2.96  tff(c_4537, plain, (![A_808, B_809, D_810]: (k2_lattices(A_808, k15_lattice3(A_808, B_809), D_810)=k15_lattice3(A_808, B_809) | ~m1_subset_1(k15_lattice3(A_808, B_809), u1_struct_0(A_808)) | ~v9_lattices(A_808) | ~v8_lattices(A_808) | ~r4_lattice3(A_808, D_810, B_809) | ~m1_subset_1(D_810, u1_struct_0(A_808)) | ~v4_lattice3(A_808) | ~v10_lattices(A_808) | ~l3_lattices(A_808) | v2_struct_0(A_808))), inference(resolution, [status(thm)], [c_3825, c_36])).
% 8.98/2.96  tff(c_4541, plain, (![A_811, B_812, D_813]: (k2_lattices(A_811, k15_lattice3(A_811, B_812), D_813)=k15_lattice3(A_811, B_812) | ~v9_lattices(A_811) | ~v8_lattices(A_811) | ~r4_lattice3(A_811, D_813, B_812) | ~m1_subset_1(D_813, u1_struct_0(A_811)) | ~v4_lattice3(A_811) | ~v10_lattices(A_811) | ~l3_lattices(A_811) | v2_struct_0(A_811))), inference(resolution, [status(thm)], [c_74, c_4537])).
% 8.98/2.96  tff(c_4545, plain, (![B_812]: (k2_lattices('#skF_8', k15_lattice3('#skF_8', B_812), '#skF_2'('#skF_8'))=k15_lattice3('#skF_8', B_812) | ~v9_lattices('#skF_8') | ~v8_lattices('#skF_8') | ~r4_lattice3('#skF_8', '#skF_2'('#skF_8'), B_812) | ~v4_lattice3('#skF_8') | ~v10_lattices('#skF_8') | ~l3_lattices('#skF_8') | v2_struct_0('#skF_8'))), inference(resolution, [status(thm)], [c_2659, c_4541])).
% 8.98/2.96  tff(c_4565, plain, (![B_812]: (k15_lattice3('#skF_8', B_812)='#skF_2'('#skF_8') | ~r4_lattice3('#skF_8', '#skF_2'('#skF_8'), B_812) | v2_struct_0('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_82, c_80, c_3255, c_3266, c_2854, c_4545])).
% 8.98/2.96  tff(c_4575, plain, (![B_814]: (k15_lattice3('#skF_8', B_814)='#skF_2'('#skF_8') | ~r4_lattice3('#skF_8', '#skF_2'('#skF_8'), B_814))), inference(negUnitSimplification, [status(thm)], [c_84, c_4565])).
% 8.98/2.96  tff(c_4581, plain, (k15_lattice3('#skF_8', k1_xboole_0)='#skF_2'('#skF_8')), inference(resolution, [status(thm)], [c_2650, c_4575])).
% 8.98/2.96  tff(c_4590, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2626, c_4581])).
% 8.98/2.96  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.98/2.96  
% 8.98/2.96  Inference rules
% 8.98/2.96  ----------------------
% 8.98/2.96  #Ref     : 0
% 8.98/2.96  #Sup     : 1049
% 8.98/2.96  #Fact    : 4
% 8.98/2.96  #Define  : 0
% 8.98/2.96  #Split   : 4
% 8.98/2.96  #Chain   : 0
% 8.98/2.96  #Close   : 0
% 8.98/2.96  
% 8.98/2.96  Ordering : KBO
% 8.98/2.96  
% 8.98/2.96  Simplification rules
% 8.98/2.96  ----------------------
% 8.98/2.96  #Subsume      : 242
% 8.98/2.96  #Demod        : 507
% 8.98/2.96  #Tautology    : 502
% 8.98/2.96  #SimpNegUnit  : 128
% 8.98/2.96  #BackRed      : 2
% 8.98/2.96  
% 8.98/2.96  #Partial instantiations: 0
% 8.98/2.96  #Strategies tried      : 1
% 8.98/2.96  
% 8.98/2.97  Timing (in seconds)
% 8.98/2.97  ----------------------
% 8.98/2.97  Preprocessing        : 0.37
% 8.98/2.97  Parsing              : 0.19
% 8.98/2.97  CNF conversion       : 0.03
% 8.98/2.97  Main loop            : 1.77
% 8.98/2.97  Inferencing          : 0.75
% 8.98/2.97  Reduction            : 0.34
% 8.98/2.97  Demodulation         : 0.22
% 8.98/2.97  BG Simplification    : 0.07
% 8.98/2.97  Subsumption          : 0.51
% 8.98/2.97  Abstraction          : 0.08
% 8.98/2.97  MUC search           : 0.00
% 8.98/2.97  Cooper               : 0.00
% 8.98/2.97  Total                : 2.19
% 8.98/2.97  Index Insertion      : 0.00
% 8.98/2.97  Index Deletion       : 0.00
% 8.98/2.97  Index Matching       : 0.00
% 8.98/2.97  BG Taut test         : 0.00
%------------------------------------------------------------------------------
