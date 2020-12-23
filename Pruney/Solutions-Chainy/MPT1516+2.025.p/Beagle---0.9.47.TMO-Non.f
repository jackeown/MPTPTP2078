%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:24:54 EST 2020

% Result     : Timeout 58.65s
% Output     : None 
% Verified   : 
% Statistics : Number of formulae       :  186 ( 849 expanded)
%              Number of leaves         :   55 ( 313 expanded)
%              Depth                    :   23
%              Number of atoms          :  708 (3582 expanded)
%              Number of equality atoms :   71 ( 446 expanded)
%              Maximal formula depth    :   17 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r3_lattices > r1_lattices > r2_hidden > r1_tarski > m1_subset_1 > v9_lattices > v8_lattices > v7_lattices > v6_lattices > v5_lattices > v4_lattices > v4_lattice3 > v2_struct_0 > v13_lattices > v10_lattices > l3_lattices > l2_lattices > l1_lattices > k2_lattices > k6_domain_1 > k2_zfmisc_1 > k16_lattice3 > k15_lattice3 > a_2_6_lattice3 > #nlpp > u1_struct_0 > k5_lattices > k1_xboole_0 > #skF_5 > #skF_10 > #skF_7 > #skF_9 > #skF_3 > #skF_2 > #skF_8 > #skF_1 > #skF_6 > #skF_4

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

tff('#skF_10',type,(
    '#skF_10': $i )).

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

tff('#skF_7',type,(
    '#skF_7': ( $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff(v13_lattices,type,(
    v13_lattices: $i > $o )).

tff('#skF_3',type,(
    '#skF_3': $i > $i )).

tff(v8_lattices,type,(
    v8_lattices: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k5_lattices,type,(
    k5_lattices: $i > $i )).

tff('#skF_8',type,(
    '#skF_8': ( $i * $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(a_2_6_lattice3,type,(
    a_2_6_lattice3: ( $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(v7_lattices,type,(
    v7_lattices: $i > $o )).

tff(f_262,negated_conjecture,(
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

tff(f_99,axiom,(
    ! [A] :
      ( l3_lattices(A)
     => ( l1_lattices(A)
        & l2_lattices(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l3_lattices)).

tff(f_67,axiom,(
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

tff(f_176,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & l3_lattices(A) )
     => m1_subset_1(k15_lattice3(A,B),u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k15_lattice3)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_154,axiom,(
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

tff(f_215,axiom,(
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

tff(f_42,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_241,axiom,(
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

tff(f_45,axiom,(
    ! [A,B] : ~ r2_hidden(A,k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_zfmisc_1)).

tff(f_118,axiom,(
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

tff(f_137,axiom,(
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

tff(f_169,axiom,(
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

tff(f_93,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_lattices(A) )
     => m1_subset_1(k5_lattices(A),u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_lattices)).

tff(f_86,axiom,(
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

tff(c_104,plain,(
    ~ v2_struct_0('#skF_10') ),
    inference(cnfTransformation,[status(thm)],[f_262])).

tff(c_98,plain,(
    l3_lattices('#skF_10') ),
    inference(cnfTransformation,[status(thm)],[f_262])).

tff(c_120,plain,(
    ! [A_92] :
      ( l1_lattices(A_92)
      | ~ l3_lattices(A_92) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_124,plain,(
    l1_lattices('#skF_10') ),
    inference(resolution,[status(thm)],[c_98,c_120])).

tff(c_102,plain,(
    v10_lattices('#skF_10') ),
    inference(cnfTransformation,[status(thm)],[f_262])).

tff(c_96,plain,
    ( k15_lattice3('#skF_10',k1_xboole_0) != k5_lattices('#skF_10')
    | ~ l3_lattices('#skF_10')
    | ~ v13_lattices('#skF_10')
    | ~ v10_lattices('#skF_10')
    | v2_struct_0('#skF_10') ),
    inference(cnfTransformation,[status(thm)],[f_262])).

tff(c_106,plain,
    ( k15_lattice3('#skF_10',k1_xboole_0) != k5_lattices('#skF_10')
    | ~ v13_lattices('#skF_10')
    | v2_struct_0('#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_98,c_96])).

tff(c_107,plain,
    ( k15_lattice3('#skF_10',k1_xboole_0) != k5_lattices('#skF_10')
    | ~ v13_lattices('#skF_10') ),
    inference(negUnitSimplification,[status(thm)],[c_104,c_106])).

tff(c_125,plain,(
    ~ v13_lattices('#skF_10') ),
    inference(splitLeft,[status(thm)],[c_107])).

tff(c_100,plain,(
    v4_lattice3('#skF_10') ),
    inference(cnfTransformation,[status(thm)],[f_262])).

tff(c_24,plain,(
    ! [A_11] :
      ( v6_lattices(A_11)
      | ~ v10_lattices(A_11)
      | v2_struct_0(A_11)
      | ~ l3_lattices(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_20,plain,(
    ! [A_11] :
      ( v8_lattices(A_11)
      | ~ v10_lattices(A_11)
      | v2_struct_0(A_11)
      | ~ l3_lattices(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_18,plain,(
    ! [A_11] :
      ( v9_lattices(A_11)
      | ~ v10_lattices(A_11)
      | v2_struct_0(A_11)
      | ~ l3_lattices(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_72,plain,(
    ! [A_56,B_57] :
      ( m1_subset_1(k15_lattice3(A_56,B_57),u1_struct_0(A_56))
      | ~ l3_lattices(A_56)
      | v2_struct_0(A_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_176])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_166,plain,(
    ! [A_104,B_105] :
      ( ~ r2_hidden('#skF_1'(A_104,B_105),B_105)
      | r1_tarski(A_104,B_105) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_171,plain,(
    ! [A_1] : r1_tarski(A_1,A_1) ),
    inference(resolution,[status(thm)],[c_6,c_166])).

tff(c_56,plain,(
    ! [A_34,B_43] :
      ( m1_subset_1('#skF_4'(A_34,B_43),u1_struct_0(A_34))
      | v13_lattices(A_34)
      | ~ m1_subset_1(B_43,u1_struct_0(A_34))
      | ~ l1_lattices(A_34)
      | v2_struct_0(A_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_88,plain,(
    ! [A_71,B_73] :
      ( k15_lattice3(A_71,k6_domain_1(u1_struct_0(A_71),B_73)) = B_73
      | ~ m1_subset_1(B_73,u1_struct_0(A_71))
      | ~ l3_lattices(A_71)
      | ~ v4_lattice3(A_71)
      | ~ v10_lattices(A_71)
      | v2_struct_0(A_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_215])).

tff(c_12,plain,(
    ! [A_7] : k2_zfmisc_1(A_7,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_554,plain,(
    ! [A_180,B_181,C_182] :
      ( r2_hidden('#skF_9'(A_180,B_181,C_182),B_181)
      | r3_lattices(A_180,k15_lattice3(A_180,B_181),k15_lattice3(A_180,C_182))
      | ~ l3_lattices(A_180)
      | ~ v4_lattice3(A_180)
      | ~ v10_lattices(A_180)
      | v2_struct_0(A_180) ) ),
    inference(cnfTransformation,[status(thm)],[f_241])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_1430,plain,(
    ! [A_297,B_298,C_299,B_300] :
      ( r2_hidden('#skF_9'(A_297,B_298,C_299),B_300)
      | ~ r1_tarski(B_298,B_300)
      | r3_lattices(A_297,k15_lattice3(A_297,B_298),k15_lattice3(A_297,C_299))
      | ~ l3_lattices(A_297)
      | ~ v4_lattice3(A_297)
      | ~ v10_lattices(A_297)
      | v2_struct_0(A_297) ) ),
    inference(resolution,[status(thm)],[c_554,c_2])).

tff(c_16,plain,(
    ! [A_9,B_10] : ~ r2_hidden(A_9,k2_zfmisc_1(A_9,B_10)) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_1477,plain,(
    ! [B_303,A_304,C_305,B_306] :
      ( ~ r1_tarski(B_303,k2_zfmisc_1('#skF_9'(A_304,B_303,C_305),B_306))
      | r3_lattices(A_304,k15_lattice3(A_304,B_303),k15_lattice3(A_304,C_305))
      | ~ l3_lattices(A_304)
      | ~ v4_lattice3(A_304)
      | ~ v10_lattices(A_304)
      | v2_struct_0(A_304) ) ),
    inference(resolution,[status(thm)],[c_1430,c_16])).

tff(c_1507,plain,(
    ! [B_309,A_310,C_311] :
      ( ~ r1_tarski(B_309,k1_xboole_0)
      | r3_lattices(A_310,k15_lattice3(A_310,B_309),k15_lattice3(A_310,C_311))
      | ~ l3_lattices(A_310)
      | ~ v4_lattice3(A_310)
      | ~ v10_lattices(A_310)
      | v2_struct_0(A_310) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_1477])).

tff(c_2559,plain,(
    ! [B_444,A_445,B_446] :
      ( ~ r1_tarski(B_444,k1_xboole_0)
      | r3_lattices(A_445,k15_lattice3(A_445,B_444),B_446)
      | ~ l3_lattices(A_445)
      | ~ v4_lattice3(A_445)
      | ~ v10_lattices(A_445)
      | v2_struct_0(A_445)
      | ~ m1_subset_1(B_446,u1_struct_0(A_445))
      | ~ l3_lattices(A_445)
      | ~ v4_lattice3(A_445)
      | ~ v10_lattices(A_445)
      | v2_struct_0(A_445) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_88,c_1507])).

tff(c_48,plain,(
    ! [A_24,B_25,C_26] :
      ( r1_lattices(A_24,B_25,C_26)
      | ~ r3_lattices(A_24,B_25,C_26)
      | ~ m1_subset_1(C_26,u1_struct_0(A_24))
      | ~ m1_subset_1(B_25,u1_struct_0(A_24))
      | ~ l3_lattices(A_24)
      | ~ v9_lattices(A_24)
      | ~ v8_lattices(A_24)
      | ~ v6_lattices(A_24)
      | v2_struct_0(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_3127,plain,(
    ! [A_512,B_513,B_514] :
      ( r1_lattices(A_512,k15_lattice3(A_512,B_513),B_514)
      | ~ m1_subset_1(k15_lattice3(A_512,B_513),u1_struct_0(A_512))
      | ~ v9_lattices(A_512)
      | ~ v8_lattices(A_512)
      | ~ v6_lattices(A_512)
      | ~ r1_tarski(B_513,k1_xboole_0)
      | ~ m1_subset_1(B_514,u1_struct_0(A_512))
      | ~ l3_lattices(A_512)
      | ~ v4_lattice3(A_512)
      | ~ v10_lattices(A_512)
      | v2_struct_0(A_512) ) ),
    inference(resolution,[status(thm)],[c_2559,c_48])).

tff(c_3133,plain,(
    ! [A_515,B_516,B_517] :
      ( r1_lattices(A_515,k15_lattice3(A_515,B_516),B_517)
      | ~ v9_lattices(A_515)
      | ~ v8_lattices(A_515)
      | ~ v6_lattices(A_515)
      | ~ r1_tarski(B_516,k1_xboole_0)
      | ~ m1_subset_1(B_517,u1_struct_0(A_515))
      | ~ v4_lattice3(A_515)
      | ~ v10_lattices(A_515)
      | ~ l3_lattices(A_515)
      | v2_struct_0(A_515) ) ),
    inference(resolution,[status(thm)],[c_72,c_3127])).

tff(c_52,plain,(
    ! [A_27,B_31,C_33] :
      ( k2_lattices(A_27,B_31,C_33) = B_31
      | ~ r1_lattices(A_27,B_31,C_33)
      | ~ m1_subset_1(C_33,u1_struct_0(A_27))
      | ~ m1_subset_1(B_31,u1_struct_0(A_27))
      | ~ l3_lattices(A_27)
      | ~ v9_lattices(A_27)
      | ~ v8_lattices(A_27)
      | v2_struct_0(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_5715,plain,(
    ! [A_754,B_755,B_756] :
      ( k2_lattices(A_754,k15_lattice3(A_754,B_755),B_756) = k15_lattice3(A_754,B_755)
      | ~ m1_subset_1(k15_lattice3(A_754,B_755),u1_struct_0(A_754))
      | ~ v9_lattices(A_754)
      | ~ v8_lattices(A_754)
      | ~ v6_lattices(A_754)
      | ~ r1_tarski(B_755,k1_xboole_0)
      | ~ m1_subset_1(B_756,u1_struct_0(A_754))
      | ~ v4_lattice3(A_754)
      | ~ v10_lattices(A_754)
      | ~ l3_lattices(A_754)
      | v2_struct_0(A_754) ) ),
    inference(resolution,[status(thm)],[c_3133,c_52])).

tff(c_5721,plain,(
    ! [A_757,B_758,B_759] :
      ( k2_lattices(A_757,k15_lattice3(A_757,B_758),B_759) = k15_lattice3(A_757,B_758)
      | ~ v9_lattices(A_757)
      | ~ v8_lattices(A_757)
      | ~ v6_lattices(A_757)
      | ~ r1_tarski(B_758,k1_xboole_0)
      | ~ m1_subset_1(B_759,u1_struct_0(A_757))
      | ~ v4_lattice3(A_757)
      | ~ v10_lattices(A_757)
      | ~ l3_lattices(A_757)
      | v2_struct_0(A_757) ) ),
    inference(resolution,[status(thm)],[c_72,c_5715])).

tff(c_5749,plain,(
    ! [A_34,B_758,B_43] :
      ( k2_lattices(A_34,k15_lattice3(A_34,B_758),'#skF_4'(A_34,B_43)) = k15_lattice3(A_34,B_758)
      | ~ v9_lattices(A_34)
      | ~ v8_lattices(A_34)
      | ~ v6_lattices(A_34)
      | ~ r1_tarski(B_758,k1_xboole_0)
      | ~ v4_lattice3(A_34)
      | ~ v10_lattices(A_34)
      | ~ l3_lattices(A_34)
      | v13_lattices(A_34)
      | ~ m1_subset_1(B_43,u1_struct_0(A_34))
      | ~ l1_lattices(A_34)
      | v2_struct_0(A_34) ) ),
    inference(resolution,[status(thm)],[c_56,c_5721])).

tff(c_153,plain,(
    ! [A_101,B_102] :
      ( r2_hidden('#skF_1'(A_101,B_102),A_101)
      | r1_tarski(A_101,B_102) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_141,plain,(
    ! [A_94,B_95] : ~ r2_hidden(A_94,k2_zfmisc_1(A_94,B_95)) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_144,plain,(
    ! [A_7] : ~ r2_hidden(A_7,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_141])).

tff(c_158,plain,(
    ! [B_102] : r1_tarski(k1_xboole_0,B_102) ),
    inference(resolution,[status(thm)],[c_153,c_144])).

tff(c_92,plain,(
    ! [A_74,B_83,C_84] :
      ( r2_hidden('#skF_9'(A_74,B_83,C_84),B_83)
      | r3_lattices(A_74,k15_lattice3(A_74,B_83),k15_lattice3(A_74,C_84))
      | ~ l3_lattices(A_74)
      | ~ v4_lattice3(A_74)
      | ~ v10_lattices(A_74)
      | v2_struct_0(A_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_241])).

tff(c_904,plain,(
    ! [A_230,B_231,C_232] :
      ( r1_lattices(A_230,B_231,C_232)
      | ~ r3_lattices(A_230,B_231,C_232)
      | ~ m1_subset_1(C_232,u1_struct_0(A_230))
      | ~ m1_subset_1(B_231,u1_struct_0(A_230))
      | ~ l3_lattices(A_230)
      | ~ v9_lattices(A_230)
      | ~ v8_lattices(A_230)
      | ~ v6_lattices(A_230)
      | v2_struct_0(A_230) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_6801,plain,(
    ! [A_828,B_829,C_830] :
      ( r1_lattices(A_828,k15_lattice3(A_828,B_829),k15_lattice3(A_828,C_830))
      | ~ m1_subset_1(k15_lattice3(A_828,C_830),u1_struct_0(A_828))
      | ~ m1_subset_1(k15_lattice3(A_828,B_829),u1_struct_0(A_828))
      | ~ v9_lattices(A_828)
      | ~ v8_lattices(A_828)
      | ~ v6_lattices(A_828)
      | r2_hidden('#skF_9'(A_828,B_829,C_830),B_829)
      | ~ l3_lattices(A_828)
      | ~ v4_lattice3(A_828)
      | ~ v10_lattices(A_828)
      | v2_struct_0(A_828) ) ),
    inference(resolution,[status(thm)],[c_92,c_904])).

tff(c_14419,plain,(
    ! [A_1312,B_1313,C_1314] :
      ( k2_lattices(A_1312,k15_lattice3(A_1312,B_1313),k15_lattice3(A_1312,C_1314)) = k15_lattice3(A_1312,B_1313)
      | ~ m1_subset_1(k15_lattice3(A_1312,C_1314),u1_struct_0(A_1312))
      | ~ m1_subset_1(k15_lattice3(A_1312,B_1313),u1_struct_0(A_1312))
      | ~ v9_lattices(A_1312)
      | ~ v8_lattices(A_1312)
      | ~ v6_lattices(A_1312)
      | r2_hidden('#skF_9'(A_1312,B_1313,C_1314),B_1313)
      | ~ l3_lattices(A_1312)
      | ~ v4_lattice3(A_1312)
      | ~ v10_lattices(A_1312)
      | v2_struct_0(A_1312) ) ),
    inference(resolution,[status(thm)],[c_6801,c_52])).

tff(c_14441,plain,(
    ! [A_1315,B_1316,B_1317] :
      ( k2_lattices(A_1315,k15_lattice3(A_1315,B_1316),k15_lattice3(A_1315,B_1317)) = k15_lattice3(A_1315,B_1316)
      | ~ m1_subset_1(k15_lattice3(A_1315,B_1316),u1_struct_0(A_1315))
      | ~ v9_lattices(A_1315)
      | ~ v8_lattices(A_1315)
      | ~ v6_lattices(A_1315)
      | r2_hidden('#skF_9'(A_1315,B_1316,B_1317),B_1316)
      | ~ v4_lattice3(A_1315)
      | ~ v10_lattices(A_1315)
      | ~ l3_lattices(A_1315)
      | v2_struct_0(A_1315) ) ),
    inference(resolution,[status(thm)],[c_72,c_14419])).

tff(c_14464,plain,(
    ! [A_1318,B_1319,B_1320] :
      ( k2_lattices(A_1318,k15_lattice3(A_1318,B_1319),k15_lattice3(A_1318,B_1320)) = k15_lattice3(A_1318,B_1319)
      | ~ v9_lattices(A_1318)
      | ~ v8_lattices(A_1318)
      | ~ v6_lattices(A_1318)
      | r2_hidden('#skF_9'(A_1318,B_1319,B_1320),B_1319)
      | ~ v4_lattice3(A_1318)
      | ~ v10_lattices(A_1318)
      | ~ l3_lattices(A_1318)
      | v2_struct_0(A_1318) ) ),
    inference(resolution,[status(thm)],[c_72,c_14441])).

tff(c_526,plain,(
    ! [A_177,C_178,B_179] :
      ( k2_lattices(A_177,C_178,B_179) = k2_lattices(A_177,B_179,C_178)
      | ~ m1_subset_1(C_178,u1_struct_0(A_177))
      | ~ m1_subset_1(B_179,u1_struct_0(A_177))
      | ~ v6_lattices(A_177)
      | ~ l1_lattices(A_177)
      | v2_struct_0(A_177) ) ),
    inference(cnfTransformation,[status(thm)],[f_169])).

tff(c_1331,plain,(
    ! [A_282,B_283,B_284] :
      ( k2_lattices(A_282,k15_lattice3(A_282,B_283),B_284) = k2_lattices(A_282,B_284,k15_lattice3(A_282,B_283))
      | ~ m1_subset_1(B_284,u1_struct_0(A_282))
      | ~ v6_lattices(A_282)
      | ~ l1_lattices(A_282)
      | ~ l3_lattices(A_282)
      | v2_struct_0(A_282) ) ),
    inference(resolution,[status(thm)],[c_72,c_526])).

tff(c_1357,plain,(
    ! [A_56,B_57,B_283] :
      ( k2_lattices(A_56,k15_lattice3(A_56,B_57),k15_lattice3(A_56,B_283)) = k2_lattices(A_56,k15_lattice3(A_56,B_283),k15_lattice3(A_56,B_57))
      | ~ v6_lattices(A_56)
      | ~ l1_lattices(A_56)
      | ~ l3_lattices(A_56)
      | v2_struct_0(A_56) ) ),
    inference(resolution,[status(thm)],[c_72,c_1331])).

tff(c_17954,plain,(
    ! [A_1435,B_1436,B_1437] :
      ( k2_lattices(A_1435,k15_lattice3(A_1435,B_1436),k15_lattice3(A_1435,B_1437)) = k15_lattice3(A_1435,B_1437)
      | ~ v6_lattices(A_1435)
      | ~ l1_lattices(A_1435)
      | ~ l3_lattices(A_1435)
      | v2_struct_0(A_1435)
      | ~ v9_lattices(A_1435)
      | ~ v8_lattices(A_1435)
      | ~ v6_lattices(A_1435)
      | r2_hidden('#skF_9'(A_1435,B_1437,B_1436),B_1437)
      | ~ v4_lattice3(A_1435)
      | ~ v10_lattices(A_1435)
      | ~ l3_lattices(A_1435)
      | v2_struct_0(A_1435) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14464,c_1357])).

tff(c_18204,plain,(
    ! [A_1438,B_1439,B_1440,B_1441] :
      ( r2_hidden('#skF_9'(A_1438,B_1439,B_1440),B_1441)
      | ~ r1_tarski(B_1439,B_1441)
      | k2_lattices(A_1438,k15_lattice3(A_1438,B_1440),k15_lattice3(A_1438,B_1439)) = k15_lattice3(A_1438,B_1439)
      | ~ l1_lattices(A_1438)
      | ~ v9_lattices(A_1438)
      | ~ v8_lattices(A_1438)
      | ~ v6_lattices(A_1438)
      | ~ v4_lattice3(A_1438)
      | ~ v10_lattices(A_1438)
      | ~ l3_lattices(A_1438)
      | v2_struct_0(A_1438) ) ),
    inference(resolution,[status(thm)],[c_17954,c_2])).

tff(c_18502,plain,(
    ! [B_1445,A_1446,B_1447,B_1448] :
      ( ~ r1_tarski(B_1445,k2_zfmisc_1('#skF_9'(A_1446,B_1445,B_1447),B_1448))
      | k2_lattices(A_1446,k15_lattice3(A_1446,B_1447),k15_lattice3(A_1446,B_1445)) = k15_lattice3(A_1446,B_1445)
      | ~ l1_lattices(A_1446)
      | ~ v9_lattices(A_1446)
      | ~ v8_lattices(A_1446)
      | ~ v6_lattices(A_1446)
      | ~ v4_lattice3(A_1446)
      | ~ v10_lattices(A_1446)
      | ~ l3_lattices(A_1446)
      | v2_struct_0(A_1446) ) ),
    inference(resolution,[status(thm)],[c_18204,c_16])).

tff(c_18553,plain,(
    ! [A_1449,B_1450] :
      ( k2_lattices(A_1449,k15_lattice3(A_1449,B_1450),k15_lattice3(A_1449,k1_xboole_0)) = k15_lattice3(A_1449,k1_xboole_0)
      | ~ l1_lattices(A_1449)
      | ~ v9_lattices(A_1449)
      | ~ v8_lattices(A_1449)
      | ~ v6_lattices(A_1449)
      | ~ v4_lattice3(A_1449)
      | ~ v10_lattices(A_1449)
      | ~ l3_lattices(A_1449)
      | v2_struct_0(A_1449) ) ),
    inference(resolution,[status(thm)],[c_158,c_18502])).

tff(c_18915,plain,(
    ! [A_1454,B_1455] :
      ( k2_lattices(A_1454,B_1455,k15_lattice3(A_1454,k1_xboole_0)) = k15_lattice3(A_1454,k1_xboole_0)
      | ~ l1_lattices(A_1454)
      | ~ v9_lattices(A_1454)
      | ~ v8_lattices(A_1454)
      | ~ v6_lattices(A_1454)
      | ~ v4_lattice3(A_1454)
      | ~ v10_lattices(A_1454)
      | ~ l3_lattices(A_1454)
      | v2_struct_0(A_1454)
      | ~ m1_subset_1(B_1455,u1_struct_0(A_1454))
      | ~ l3_lattices(A_1454)
      | ~ v4_lattice3(A_1454)
      | ~ v10_lattices(A_1454)
      | v2_struct_0(A_1454) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_88,c_18553])).

tff(c_19130,plain,(
    ! [A_1468,B_1469] :
      ( k2_lattices(A_1468,'#skF_4'(A_1468,B_1469),k15_lattice3(A_1468,k1_xboole_0)) = k15_lattice3(A_1468,k1_xboole_0)
      | ~ v9_lattices(A_1468)
      | ~ v8_lattices(A_1468)
      | ~ v6_lattices(A_1468)
      | ~ l3_lattices(A_1468)
      | ~ v4_lattice3(A_1468)
      | ~ v10_lattices(A_1468)
      | v13_lattices(A_1468)
      | ~ m1_subset_1(B_1469,u1_struct_0(A_1468))
      | ~ l1_lattices(A_1468)
      | v2_struct_0(A_1468) ) ),
    inference(resolution,[status(thm)],[c_56,c_18915])).

tff(c_54,plain,(
    ! [A_34,B_43] :
      ( k2_lattices(A_34,'#skF_4'(A_34,B_43),B_43) != B_43
      | k2_lattices(A_34,B_43,'#skF_4'(A_34,B_43)) != B_43
      | v13_lattices(A_34)
      | ~ m1_subset_1(B_43,u1_struct_0(A_34))
      | ~ l1_lattices(A_34)
      | v2_struct_0(A_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_19215,plain,(
    ! [A_1475] :
      ( k2_lattices(A_1475,k15_lattice3(A_1475,k1_xboole_0),'#skF_4'(A_1475,k15_lattice3(A_1475,k1_xboole_0))) != k15_lattice3(A_1475,k1_xboole_0)
      | ~ v9_lattices(A_1475)
      | ~ v8_lattices(A_1475)
      | ~ v6_lattices(A_1475)
      | ~ l3_lattices(A_1475)
      | ~ v4_lattice3(A_1475)
      | ~ v10_lattices(A_1475)
      | v13_lattices(A_1475)
      | ~ m1_subset_1(k15_lattice3(A_1475,k1_xboole_0),u1_struct_0(A_1475))
      | ~ l1_lattices(A_1475)
      | v2_struct_0(A_1475) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_19130,c_54])).

tff(c_19219,plain,(
    ! [A_34] :
      ( ~ v9_lattices(A_34)
      | ~ v8_lattices(A_34)
      | ~ v6_lattices(A_34)
      | ~ r1_tarski(k1_xboole_0,k1_xboole_0)
      | ~ v4_lattice3(A_34)
      | ~ v10_lattices(A_34)
      | ~ l3_lattices(A_34)
      | v13_lattices(A_34)
      | ~ m1_subset_1(k15_lattice3(A_34,k1_xboole_0),u1_struct_0(A_34))
      | ~ l1_lattices(A_34)
      | v2_struct_0(A_34) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5749,c_19215])).

tff(c_19228,plain,(
    ! [A_1476] :
      ( ~ v9_lattices(A_1476)
      | ~ v8_lattices(A_1476)
      | ~ v6_lattices(A_1476)
      | ~ v4_lattice3(A_1476)
      | ~ v10_lattices(A_1476)
      | ~ l3_lattices(A_1476)
      | v13_lattices(A_1476)
      | ~ m1_subset_1(k15_lattice3(A_1476,k1_xboole_0),u1_struct_0(A_1476))
      | ~ l1_lattices(A_1476)
      | v2_struct_0(A_1476) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_171,c_19219])).

tff(c_19234,plain,(
    ! [A_1477] :
      ( ~ v9_lattices(A_1477)
      | ~ v8_lattices(A_1477)
      | ~ v6_lattices(A_1477)
      | ~ v4_lattice3(A_1477)
      | ~ v10_lattices(A_1477)
      | v13_lattices(A_1477)
      | ~ l1_lattices(A_1477)
      | ~ l3_lattices(A_1477)
      | v2_struct_0(A_1477) ) ),
    inference(resolution,[status(thm)],[c_72,c_19228])).

tff(c_19239,plain,(
    ! [A_1478] :
      ( ~ v8_lattices(A_1478)
      | ~ v6_lattices(A_1478)
      | ~ v4_lattice3(A_1478)
      | v13_lattices(A_1478)
      | ~ l1_lattices(A_1478)
      | ~ v10_lattices(A_1478)
      | v2_struct_0(A_1478)
      | ~ l3_lattices(A_1478) ) ),
    inference(resolution,[status(thm)],[c_18,c_19234])).

tff(c_19244,plain,(
    ! [A_1479] :
      ( ~ v6_lattices(A_1479)
      | ~ v4_lattice3(A_1479)
      | v13_lattices(A_1479)
      | ~ l1_lattices(A_1479)
      | ~ v10_lattices(A_1479)
      | v2_struct_0(A_1479)
      | ~ l3_lattices(A_1479) ) ),
    inference(resolution,[status(thm)],[c_20,c_19239])).

tff(c_19249,plain,(
    ! [A_1480] :
      ( ~ v4_lattice3(A_1480)
      | v13_lattices(A_1480)
      | ~ l1_lattices(A_1480)
      | ~ v10_lattices(A_1480)
      | v2_struct_0(A_1480)
      | ~ l3_lattices(A_1480) ) ),
    inference(resolution,[status(thm)],[c_24,c_19244])).

tff(c_19252,plain,
    ( v13_lattices('#skF_10')
    | ~ l1_lattices('#skF_10')
    | ~ v10_lattices('#skF_10')
    | v2_struct_0('#skF_10')
    | ~ l3_lattices('#skF_10') ),
    inference(resolution,[status(thm)],[c_100,c_19249])).

tff(c_19255,plain,
    ( v13_lattices('#skF_10')
    | v2_struct_0('#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_102,c_124,c_19252])).

tff(c_19257,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_104,c_125,c_19255])).

tff(c_19259,plain,(
    v13_lattices('#skF_10') ),
    inference(splitRight,[status(thm)],[c_107])).

tff(c_40,plain,(
    ! [A_22] :
      ( m1_subset_1(k5_lattices(A_22),u1_struct_0(A_22))
      | ~ l1_lattices(A_22)
      | v2_struct_0(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_58,plain,(
    ! [A_34] :
      ( m1_subset_1('#skF_3'(A_34),u1_struct_0(A_34))
      | ~ v13_lattices(A_34)
      | ~ l1_lattices(A_34)
      | v2_struct_0(A_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_19732,plain,(
    ! [A_1571,C_1572] :
      ( k2_lattices(A_1571,k5_lattices(A_1571),C_1572) = k5_lattices(A_1571)
      | ~ m1_subset_1(C_1572,u1_struct_0(A_1571))
      | ~ m1_subset_1(k5_lattices(A_1571),u1_struct_0(A_1571))
      | ~ v13_lattices(A_1571)
      | ~ l1_lattices(A_1571)
      | v2_struct_0(A_1571) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_19788,plain,(
    ! [A_1575] :
      ( k2_lattices(A_1575,k5_lattices(A_1575),'#skF_3'(A_1575)) = k5_lattices(A_1575)
      | ~ m1_subset_1(k5_lattices(A_1575),u1_struct_0(A_1575))
      | ~ v13_lattices(A_1575)
      | ~ l1_lattices(A_1575)
      | v2_struct_0(A_1575) ) ),
    inference(resolution,[status(thm)],[c_58,c_19732])).

tff(c_19792,plain,(
    ! [A_1576] :
      ( k2_lattices(A_1576,k5_lattices(A_1576),'#skF_3'(A_1576)) = k5_lattices(A_1576)
      | ~ v13_lattices(A_1576)
      | ~ l1_lattices(A_1576)
      | v2_struct_0(A_1576) ) ),
    inference(resolution,[status(thm)],[c_40,c_19788])).

tff(c_19421,plain,(
    ! [A_1527,C_1528] :
      ( k2_lattices(A_1527,C_1528,'#skF_3'(A_1527)) = '#skF_3'(A_1527)
      | ~ m1_subset_1(C_1528,u1_struct_0(A_1527))
      | ~ v13_lattices(A_1527)
      | ~ l1_lattices(A_1527)
      | v2_struct_0(A_1527) ) ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_19439,plain,(
    ! [A_22] :
      ( k2_lattices(A_22,k5_lattices(A_22),'#skF_3'(A_22)) = '#skF_3'(A_22)
      | ~ v13_lattices(A_22)
      | ~ l1_lattices(A_22)
      | v2_struct_0(A_22) ) ),
    inference(resolution,[status(thm)],[c_40,c_19421])).

tff(c_19801,plain,(
    ! [A_1576] :
      ( k5_lattices(A_1576) = '#skF_3'(A_1576)
      | ~ v13_lattices(A_1576)
      | ~ l1_lattices(A_1576)
      | v2_struct_0(A_1576)
      | ~ v13_lattices(A_1576)
      | ~ l1_lattices(A_1576)
      | v2_struct_0(A_1576) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_19792,c_19439])).

tff(c_19848,plain,(
    ! [A_1581] :
      ( k5_lattices(A_1581) = '#skF_3'(A_1581)
      | ~ v13_lattices(A_1581)
      | ~ l1_lattices(A_1581)
      | v2_struct_0(A_1581) ) ),
    inference(factorization,[status(thm),theory(equality)],[c_19801])).

tff(c_19851,plain,
    ( k5_lattices('#skF_10') = '#skF_3'('#skF_10')
    | ~ v13_lattices('#skF_10')
    | ~ l1_lattices('#skF_10') ),
    inference(resolution,[status(thm)],[c_19848,c_104])).

tff(c_19854,plain,(
    k5_lattices('#skF_10') = '#skF_3'('#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_124,c_19259,c_19851])).

tff(c_19258,plain,(
    k15_lattice3('#skF_10',k1_xboole_0) != k5_lattices('#skF_10') ),
    inference(splitRight,[status(thm)],[c_107])).

tff(c_19855,plain,(
    k15_lattice3('#skF_10',k1_xboole_0) != '#skF_3'('#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_19854,c_19258])).

tff(c_19871,plain,
    ( m1_subset_1('#skF_3'('#skF_10'),u1_struct_0('#skF_10'))
    | ~ l1_lattices('#skF_10')
    | v2_struct_0('#skF_10') ),
    inference(superposition,[status(thm),theory(equality)],[c_19854,c_40])).

tff(c_19887,plain,
    ( m1_subset_1('#skF_3'('#skF_10'),u1_struct_0('#skF_10'))
    | v2_struct_0('#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_124,c_19871])).

tff(c_19888,plain,(
    m1_subset_1('#skF_3'('#skF_10'),u1_struct_0('#skF_10')) ),
    inference(negUnitSimplification,[status(thm)],[c_104,c_19887])).

tff(c_64,plain,(
    ! [A_45,C_54,B_52] :
      ( k2_lattices(A_45,C_54,B_52) = k2_lattices(A_45,B_52,C_54)
      | ~ m1_subset_1(C_54,u1_struct_0(A_45))
      | ~ m1_subset_1(B_52,u1_struct_0(A_45))
      | ~ v6_lattices(A_45)
      | ~ l1_lattices(A_45)
      | v2_struct_0(A_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_169])).

tff(c_19897,plain,(
    ! [B_52] :
      ( k2_lattices('#skF_10',B_52,'#skF_3'('#skF_10')) = k2_lattices('#skF_10','#skF_3'('#skF_10'),B_52)
      | ~ m1_subset_1(B_52,u1_struct_0('#skF_10'))
      | ~ v6_lattices('#skF_10')
      | ~ l1_lattices('#skF_10')
      | v2_struct_0('#skF_10') ) ),
    inference(resolution,[status(thm)],[c_19888,c_64])).

tff(c_19916,plain,(
    ! [B_52] :
      ( k2_lattices('#skF_10',B_52,'#skF_3'('#skF_10')) = k2_lattices('#skF_10','#skF_3'('#skF_10'),B_52)
      | ~ m1_subset_1(B_52,u1_struct_0('#skF_10'))
      | ~ v6_lattices('#skF_10')
      | v2_struct_0('#skF_10') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_124,c_19897])).

tff(c_19917,plain,(
    ! [B_52] :
      ( k2_lattices('#skF_10',B_52,'#skF_3'('#skF_10')) = k2_lattices('#skF_10','#skF_3'('#skF_10'),B_52)
      | ~ m1_subset_1(B_52,u1_struct_0('#skF_10'))
      | ~ v6_lattices('#skF_10') ) ),
    inference(negUnitSimplification,[status(thm)],[c_104,c_19916])).

tff(c_19957,plain,(
    ~ v6_lattices('#skF_10') ),
    inference(splitLeft,[status(thm)],[c_19917])).

tff(c_19961,plain,
    ( ~ v10_lattices('#skF_10')
    | v2_struct_0('#skF_10')
    | ~ l3_lattices('#skF_10') ),
    inference(resolution,[status(thm)],[c_24,c_19957])).

tff(c_19964,plain,(
    v2_struct_0('#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_102,c_19961])).

tff(c_19966,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_104,c_19964])).

tff(c_19968,plain,(
    v6_lattices('#skF_10') ),
    inference(splitRight,[status(thm)],[c_19917])).

tff(c_20701,plain,(
    ! [A_1637,B_1638,C_1639] :
      ( r1_lattices(A_1637,B_1638,C_1639)
      | k2_lattices(A_1637,B_1638,C_1639) != B_1638
      | ~ m1_subset_1(C_1639,u1_struct_0(A_1637))
      | ~ m1_subset_1(B_1638,u1_struct_0(A_1637))
      | ~ l3_lattices(A_1637)
      | ~ v9_lattices(A_1637)
      | ~ v8_lattices(A_1637)
      | v2_struct_0(A_1637) ) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_20703,plain,(
    ! [B_1638] :
      ( r1_lattices('#skF_10',B_1638,'#skF_3'('#skF_10'))
      | k2_lattices('#skF_10',B_1638,'#skF_3'('#skF_10')) != B_1638
      | ~ m1_subset_1(B_1638,u1_struct_0('#skF_10'))
      | ~ l3_lattices('#skF_10')
      | ~ v9_lattices('#skF_10')
      | ~ v8_lattices('#skF_10')
      | v2_struct_0('#skF_10') ) ),
    inference(resolution,[status(thm)],[c_19888,c_20701])).

tff(c_20724,plain,(
    ! [B_1638] :
      ( r1_lattices('#skF_10',B_1638,'#skF_3'('#skF_10'))
      | k2_lattices('#skF_10',B_1638,'#skF_3'('#skF_10')) != B_1638
      | ~ m1_subset_1(B_1638,u1_struct_0('#skF_10'))
      | ~ v9_lattices('#skF_10')
      | ~ v8_lattices('#skF_10')
      | v2_struct_0('#skF_10') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_20703])).

tff(c_20725,plain,(
    ! [B_1638] :
      ( r1_lattices('#skF_10',B_1638,'#skF_3'('#skF_10'))
      | k2_lattices('#skF_10',B_1638,'#skF_3'('#skF_10')) != B_1638
      | ~ m1_subset_1(B_1638,u1_struct_0('#skF_10'))
      | ~ v9_lattices('#skF_10')
      | ~ v8_lattices('#skF_10') ) ),
    inference(negUnitSimplification,[status(thm)],[c_104,c_20724])).

tff(c_20753,plain,(
    ~ v8_lattices('#skF_10') ),
    inference(splitLeft,[status(thm)],[c_20725])).

tff(c_20756,plain,
    ( ~ v10_lattices('#skF_10')
    | v2_struct_0('#skF_10')
    | ~ l3_lattices('#skF_10') ),
    inference(resolution,[status(thm)],[c_20,c_20753])).

tff(c_20759,plain,(
    v2_struct_0('#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_102,c_20756])).

tff(c_20761,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_104,c_20759])).

tff(c_20763,plain,(
    v8_lattices('#skF_10') ),
    inference(splitRight,[status(thm)],[c_20725])).

tff(c_20762,plain,(
    ! [B_1638] :
      ( ~ v9_lattices('#skF_10')
      | r1_lattices('#skF_10',B_1638,'#skF_3'('#skF_10'))
      | k2_lattices('#skF_10',B_1638,'#skF_3'('#skF_10')) != B_1638
      | ~ m1_subset_1(B_1638,u1_struct_0('#skF_10')) ) ),
    inference(splitRight,[status(thm)],[c_20725])).

tff(c_20764,plain,(
    ~ v9_lattices('#skF_10') ),
    inference(splitLeft,[status(thm)],[c_20762])).

tff(c_20767,plain,
    ( ~ v10_lattices('#skF_10')
    | v2_struct_0('#skF_10')
    | ~ l3_lattices('#skF_10') ),
    inference(resolution,[status(thm)],[c_18,c_20764])).

tff(c_20770,plain,(
    v2_struct_0('#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_102,c_20767])).

tff(c_20772,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_104,c_20770])).

tff(c_20774,plain,(
    v9_lattices('#skF_10') ),
    inference(splitRight,[status(thm)],[c_20762])).

tff(c_19969,plain,(
    ! [B_1588] :
      ( k2_lattices('#skF_10',B_1588,'#skF_3'('#skF_10')) = k2_lattices('#skF_10','#skF_3'('#skF_10'),B_1588)
      | ~ m1_subset_1(B_1588,u1_struct_0('#skF_10')) ) ),
    inference(splitRight,[status(thm)],[c_19917])).

tff(c_20004,plain,(
    ! [B_57] :
      ( k2_lattices('#skF_10',k15_lattice3('#skF_10',B_57),'#skF_3'('#skF_10')) = k2_lattices('#skF_10','#skF_3'('#skF_10'),k15_lattice3('#skF_10',B_57))
      | ~ l3_lattices('#skF_10')
      | v2_struct_0('#skF_10') ) ),
    inference(resolution,[status(thm)],[c_72,c_19969])).

tff(c_20041,plain,(
    ! [B_57] :
      ( k2_lattices('#skF_10',k15_lattice3('#skF_10',B_57),'#skF_3'('#skF_10')) = k2_lattices('#skF_10','#skF_3'('#skF_10'),k15_lattice3('#skF_10',B_57))
      | v2_struct_0('#skF_10') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_20004])).

tff(c_20047,plain,(
    ! [B_1589] : k2_lattices('#skF_10',k15_lattice3('#skF_10',B_1589),'#skF_3'('#skF_10')) = k2_lattices('#skF_10','#skF_3'('#skF_10'),k15_lattice3('#skF_10',B_1589)) ),
    inference(negUnitSimplification,[status(thm)],[c_104,c_20041])).

tff(c_19438,plain,(
    ! [A_56,B_57] :
      ( k2_lattices(A_56,k15_lattice3(A_56,B_57),'#skF_3'(A_56)) = '#skF_3'(A_56)
      | ~ v13_lattices(A_56)
      | ~ l1_lattices(A_56)
      | ~ l3_lattices(A_56)
      | v2_struct_0(A_56) ) ),
    inference(resolution,[status(thm)],[c_72,c_19421])).

tff(c_20053,plain,(
    ! [B_1589] :
      ( k2_lattices('#skF_10','#skF_3'('#skF_10'),k15_lattice3('#skF_10',B_1589)) = '#skF_3'('#skF_10')
      | ~ v13_lattices('#skF_10')
      | ~ l1_lattices('#skF_10')
      | ~ l3_lattices('#skF_10')
      | v2_struct_0('#skF_10') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20047,c_19438])).

tff(c_20067,plain,(
    ! [B_1589] :
      ( k2_lattices('#skF_10','#skF_3'('#skF_10'),k15_lattice3('#skF_10',B_1589)) = '#skF_3'('#skF_10')
      | v2_struct_0('#skF_10') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_124,c_19259,c_20053])).

tff(c_20068,plain,(
    ! [B_1589] : k2_lattices('#skF_10','#skF_3'('#skF_10'),k15_lattice3('#skF_10',B_1589)) = '#skF_3'('#skF_10') ),
    inference(negUnitSimplification,[status(thm)],[c_104,c_20067])).

tff(c_20042,plain,(
    ! [B_57] : k2_lattices('#skF_10',k15_lattice3('#skF_10',B_57),'#skF_3'('#skF_10')) = k2_lattices('#skF_10','#skF_3'('#skF_10'),k15_lattice3('#skF_10',B_57)) ),
    inference(negUnitSimplification,[status(thm)],[c_104,c_20041])).

tff(c_20076,plain,(
    ! [B_57] : k2_lattices('#skF_10',k15_lattice3('#skF_10',B_57),'#skF_3'('#skF_10')) = '#skF_3'('#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20068,c_20042])).

tff(c_19298,plain,(
    ! [A_1492,B_1493] :
      ( r2_hidden('#skF_1'(A_1492,B_1493),A_1492)
      | r1_tarski(A_1492,B_1493) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_19275,plain,(
    ! [A_1482,B_1483] : ~ r2_hidden(A_1482,k2_zfmisc_1(A_1482,B_1483)) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_19278,plain,(
    ! [A_7] : ~ r2_hidden(A_7,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_19275])).

tff(c_19308,plain,(
    ! [B_1493] : r1_tarski(k1_xboole_0,B_1493) ),
    inference(resolution,[status(thm)],[c_19298,c_19278])).

tff(c_19826,plain,(
    ! [A_1578,B_1579,C_1580] :
      ( r2_hidden('#skF_9'(A_1578,B_1579,C_1580),B_1579)
      | r3_lattices(A_1578,k15_lattice3(A_1578,B_1579),k15_lattice3(A_1578,C_1580))
      | ~ l3_lattices(A_1578)
      | ~ v4_lattice3(A_1578)
      | ~ v10_lattices(A_1578)
      | v2_struct_0(A_1578) ) ),
    inference(cnfTransformation,[status(thm)],[f_241])).

tff(c_21389,plain,(
    ! [A_1710,B_1711,C_1712,B_1713] :
      ( r2_hidden('#skF_9'(A_1710,B_1711,C_1712),B_1713)
      | ~ r1_tarski(B_1711,B_1713)
      | r3_lattices(A_1710,k15_lattice3(A_1710,B_1711),k15_lattice3(A_1710,C_1712))
      | ~ l3_lattices(A_1710)
      | ~ v4_lattice3(A_1710)
      | ~ v10_lattices(A_1710)
      | v2_struct_0(A_1710) ) ),
    inference(resolution,[status(thm)],[c_19826,c_2])).

tff(c_21432,plain,(
    ! [B_1714,A_1715,C_1716,B_1717] :
      ( ~ r1_tarski(B_1714,k2_zfmisc_1('#skF_9'(A_1715,B_1714,C_1716),B_1717))
      | r3_lattices(A_1715,k15_lattice3(A_1715,B_1714),k15_lattice3(A_1715,C_1716))
      | ~ l3_lattices(A_1715)
      | ~ v4_lattice3(A_1715)
      | ~ v10_lattices(A_1715)
      | v2_struct_0(A_1715) ) ),
    inference(resolution,[status(thm)],[c_21389,c_16])).

tff(c_21455,plain,(
    ! [A_1718,C_1719] :
      ( r3_lattices(A_1718,k15_lattice3(A_1718,k1_xboole_0),k15_lattice3(A_1718,C_1719))
      | ~ l3_lattices(A_1718)
      | ~ v4_lattice3(A_1718)
      | ~ v10_lattices(A_1718)
      | v2_struct_0(A_1718) ) ),
    inference(resolution,[status(thm)],[c_19308,c_21432])).

tff(c_22427,plain,(
    ! [A_1793,B_1794] :
      ( r3_lattices(A_1793,k15_lattice3(A_1793,k1_xboole_0),B_1794)
      | ~ l3_lattices(A_1793)
      | ~ v4_lattice3(A_1793)
      | ~ v10_lattices(A_1793)
      | v2_struct_0(A_1793)
      | ~ m1_subset_1(B_1794,u1_struct_0(A_1793))
      | ~ l3_lattices(A_1793)
      | ~ v4_lattice3(A_1793)
      | ~ v10_lattices(A_1793)
      | v2_struct_0(A_1793) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_88,c_21455])).

tff(c_23794,plain,(
    ! [A_1908,B_1909] :
      ( r1_lattices(A_1908,k15_lattice3(A_1908,k1_xboole_0),B_1909)
      | ~ m1_subset_1(k15_lattice3(A_1908,k1_xboole_0),u1_struct_0(A_1908))
      | ~ v9_lattices(A_1908)
      | ~ v8_lattices(A_1908)
      | ~ v6_lattices(A_1908)
      | ~ m1_subset_1(B_1909,u1_struct_0(A_1908))
      | ~ l3_lattices(A_1908)
      | ~ v4_lattice3(A_1908)
      | ~ v10_lattices(A_1908)
      | v2_struct_0(A_1908) ) ),
    inference(resolution,[status(thm)],[c_22427,c_48])).

tff(c_23799,plain,(
    ! [A_1910,B_1911] :
      ( r1_lattices(A_1910,k15_lattice3(A_1910,k1_xboole_0),B_1911)
      | ~ v9_lattices(A_1910)
      | ~ v8_lattices(A_1910)
      | ~ v6_lattices(A_1910)
      | ~ m1_subset_1(B_1911,u1_struct_0(A_1910))
      | ~ v4_lattice3(A_1910)
      | ~ v10_lattices(A_1910)
      | ~ l3_lattices(A_1910)
      | v2_struct_0(A_1910) ) ),
    inference(resolution,[status(thm)],[c_72,c_23794])).

tff(c_27641,plain,(
    ! [A_2095,B_2096] :
      ( k2_lattices(A_2095,k15_lattice3(A_2095,k1_xboole_0),B_2096) = k15_lattice3(A_2095,k1_xboole_0)
      | ~ m1_subset_1(k15_lattice3(A_2095,k1_xboole_0),u1_struct_0(A_2095))
      | ~ v9_lattices(A_2095)
      | ~ v8_lattices(A_2095)
      | ~ v6_lattices(A_2095)
      | ~ m1_subset_1(B_2096,u1_struct_0(A_2095))
      | ~ v4_lattice3(A_2095)
      | ~ v10_lattices(A_2095)
      | ~ l3_lattices(A_2095)
      | v2_struct_0(A_2095) ) ),
    inference(resolution,[status(thm)],[c_23799,c_52])).

tff(c_27653,plain,(
    ! [A_2101,B_2102] :
      ( k2_lattices(A_2101,k15_lattice3(A_2101,k1_xboole_0),B_2102) = k15_lattice3(A_2101,k1_xboole_0)
      | ~ v9_lattices(A_2101)
      | ~ v8_lattices(A_2101)
      | ~ v6_lattices(A_2101)
      | ~ m1_subset_1(B_2102,u1_struct_0(A_2101))
      | ~ v4_lattice3(A_2101)
      | ~ v10_lattices(A_2101)
      | ~ l3_lattices(A_2101)
      | v2_struct_0(A_2101) ) ),
    inference(resolution,[status(thm)],[c_72,c_27641])).

tff(c_27657,plain,
    ( k2_lattices('#skF_10',k15_lattice3('#skF_10',k1_xboole_0),'#skF_3'('#skF_10')) = k15_lattice3('#skF_10',k1_xboole_0)
    | ~ v9_lattices('#skF_10')
    | ~ v8_lattices('#skF_10')
    | ~ v6_lattices('#skF_10')
    | ~ v4_lattice3('#skF_10')
    | ~ v10_lattices('#skF_10')
    | ~ l3_lattices('#skF_10')
    | v2_struct_0('#skF_10') ),
    inference(resolution,[status(thm)],[c_19888,c_27653])).

tff(c_27679,plain,
    ( k15_lattice3('#skF_10',k1_xboole_0) = '#skF_3'('#skF_10')
    | v2_struct_0('#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_102,c_100,c_19968,c_20763,c_20774,c_20076,c_27657])).

tff(c_27681,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_104,c_19855,c_27679])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n021.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 10:11:19 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 58.65/47.98  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 58.67/48.00  
% 58.67/48.00  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 58.67/48.00  %$ r3_lattices > r1_lattices > r2_hidden > r1_tarski > m1_subset_1 > v9_lattices > v8_lattices > v7_lattices > v6_lattices > v5_lattices > v4_lattices > v4_lattice3 > v2_struct_0 > v13_lattices > v10_lattices > l3_lattices > l2_lattices > l1_lattices > k2_lattices > k6_domain_1 > k2_zfmisc_1 > k16_lattice3 > k15_lattice3 > a_2_6_lattice3 > #nlpp > u1_struct_0 > k5_lattices > k1_xboole_0 > #skF_5 > #skF_10 > #skF_7 > #skF_9 > #skF_3 > #skF_2 > #skF_8 > #skF_1 > #skF_6 > #skF_4
% 58.67/48.00  
% 58.67/48.00  %Foreground sorts:
% 58.67/48.00  
% 58.67/48.00  
% 58.67/48.00  %Background operators:
% 58.67/48.00  
% 58.67/48.00  
% 58.67/48.00  %Foreground operators:
% 58.67/48.00  tff(l3_lattices, type, l3_lattices: $i > $o).
% 58.67/48.00  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 58.67/48.00  tff(k2_lattices, type, k2_lattices: ($i * $i * $i) > $i).
% 58.67/48.00  tff('#skF_5', type, '#skF_5': $i > $i).
% 58.67/48.00  tff(l2_lattices, type, l2_lattices: $i > $o).
% 58.67/48.00  tff(r3_lattices, type, r3_lattices: ($i * $i * $i) > $o).
% 58.67/48.00  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 58.67/48.00  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 58.67/48.00  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 58.67/48.00  tff(k16_lattice3, type, k16_lattice3: ($i * $i) > $i).
% 58.67/48.00  tff(k15_lattice3, type, k15_lattice3: ($i * $i) > $i).
% 58.67/48.00  tff(l1_lattices, type, l1_lattices: $i > $o).
% 58.67/48.00  tff(r1_lattices, type, r1_lattices: ($i * $i * $i) > $o).
% 58.67/48.00  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 58.67/48.00  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 58.67/48.00  tff('#skF_10', type, '#skF_10': $i).
% 58.67/48.00  tff(v4_lattices, type, v4_lattices: $i > $o).
% 58.67/48.00  tff(v6_lattices, type, v6_lattices: $i > $o).
% 58.67/48.00  tff(v9_lattices, type, v9_lattices: $i > $o).
% 58.67/48.00  tff(v4_lattice3, type, v4_lattice3: $i > $o).
% 58.67/48.00  tff(v5_lattices, type, v5_lattices: $i > $o).
% 58.67/48.00  tff(v10_lattices, type, v10_lattices: $i > $o).
% 58.67/48.00  tff('#skF_7', type, '#skF_7': ($i * $i * $i) > $i).
% 58.67/48.00  tff('#skF_9', type, '#skF_9': ($i * $i * $i) > $i).
% 58.67/48.00  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 58.67/48.00  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 58.67/48.00  tff(v13_lattices, type, v13_lattices: $i > $o).
% 58.67/48.00  tff('#skF_3', type, '#skF_3': $i > $i).
% 58.67/48.00  tff(v8_lattices, type, v8_lattices: $i > $o).
% 58.67/48.00  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 58.67/48.00  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 58.67/48.00  tff(k5_lattices, type, k5_lattices: $i > $i).
% 58.67/48.00  tff('#skF_8', type, '#skF_8': ($i * $i * $i) > $i).
% 58.67/48.00  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 58.67/48.00  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 58.67/48.00  tff(a_2_6_lattice3, type, a_2_6_lattice3: ($i * $i) > $i).
% 58.67/48.00  tff('#skF_6', type, '#skF_6': $i > $i).
% 58.67/48.00  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 58.67/48.00  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 58.67/48.00  tff(v7_lattices, type, v7_lattices: $i > $o).
% 58.67/48.00  
% 58.67/48.03  tff(f_262, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v10_lattices(A)) & v4_lattice3(A)) & l3_lattices(A)) => ((((~v2_struct_0(A) & v10_lattices(A)) & v13_lattices(A)) & l3_lattices(A)) & (k5_lattices(A) = k15_lattice3(A, k1_xboole_0))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t50_lattice3)).
% 58.67/48.03  tff(f_99, axiom, (![A]: (l3_lattices(A) => (l1_lattices(A) & l2_lattices(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l3_lattices)).
% 58.67/48.03  tff(f_67, axiom, (![A]: (l3_lattices(A) => ((~v2_struct_0(A) & v10_lattices(A)) => ((((((~v2_struct_0(A) & v4_lattices(A)) & v5_lattices(A)) & v6_lattices(A)) & v7_lattices(A)) & v8_lattices(A)) & v9_lattices(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_lattices)).
% 58.67/48.03  tff(f_176, axiom, (![A, B]: ((~v2_struct_0(A) & l3_lattices(A)) => m1_subset_1(k15_lattice3(A, B), u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k15_lattice3)).
% 58.67/48.03  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 58.67/48.03  tff(f_154, axiom, (![A]: ((~v2_struct_0(A) & l1_lattices(A)) => (v13_lattices(A) <=> (?[B]: (m1_subset_1(B, u1_struct_0(A)) & (![C]: (m1_subset_1(C, u1_struct_0(A)) => ((k2_lattices(A, B, C) = B) & (k2_lattices(A, C, B) = B))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d13_lattices)).
% 58.67/48.03  tff(f_215, axiom, (![A]: ((((~v2_struct_0(A) & v10_lattices(A)) & v4_lattice3(A)) & l3_lattices(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => ((k15_lattice3(A, k6_domain_1(u1_struct_0(A), B)) = B) & (k16_lattice3(A, k6_domain_1(u1_struct_0(A), B)) = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_lattice3)).
% 58.67/48.03  tff(f_42, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 58.67/48.03  tff(f_241, axiom, (![A]: ((((~v2_struct_0(A) & v10_lattices(A)) & v4_lattice3(A)) & l3_lattices(A)) => (![B, C]: ((![D]: (m1_subset_1(D, u1_struct_0(A)) => ~(r2_hidden(D, B) & (![E]: (m1_subset_1(E, u1_struct_0(A)) => ~(r3_lattices(A, D, E) & r2_hidden(E, C))))))) => r3_lattices(A, k15_lattice3(A, B), k15_lattice3(A, C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_lattice3)).
% 58.67/48.03  tff(f_45, axiom, (![A, B]: ~r2_hidden(A, k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t152_zfmisc_1)).
% 58.67/48.03  tff(f_118, axiom, (![A, B, C]: (((((((~v2_struct_0(A) & v6_lattices(A)) & v8_lattices(A)) & v9_lattices(A)) & l3_lattices(A)) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => (r3_lattices(A, B, C) <=> r1_lattices(A, B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r3_lattices)).
% 58.67/48.03  tff(f_137, axiom, (![A]: ((((~v2_struct_0(A) & v8_lattices(A)) & v9_lattices(A)) & l3_lattices(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r1_lattices(A, B, C) <=> (k2_lattices(A, B, C) = B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t21_lattices)).
% 58.67/48.03  tff(f_169, axiom, (![A]: ((~v2_struct_0(A) & l1_lattices(A)) => (v6_lattices(A) <=> (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (k2_lattices(A, B, C) = k2_lattices(A, C, B))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d6_lattices)).
% 58.67/48.03  tff(f_93, axiom, (![A]: ((~v2_struct_0(A) & l1_lattices(A)) => m1_subset_1(k5_lattices(A), u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k5_lattices)).
% 58.67/48.03  tff(f_86, axiom, (![A]: ((~v2_struct_0(A) & l1_lattices(A)) => (v13_lattices(A) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => ((B = k5_lattices(A)) <=> (![C]: (m1_subset_1(C, u1_struct_0(A)) => ((k2_lattices(A, B, C) = B) & (k2_lattices(A, C, B) = B)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d16_lattices)).
% 58.67/48.03  tff(c_104, plain, (~v2_struct_0('#skF_10')), inference(cnfTransformation, [status(thm)], [f_262])).
% 58.67/48.03  tff(c_98, plain, (l3_lattices('#skF_10')), inference(cnfTransformation, [status(thm)], [f_262])).
% 58.67/48.03  tff(c_120, plain, (![A_92]: (l1_lattices(A_92) | ~l3_lattices(A_92))), inference(cnfTransformation, [status(thm)], [f_99])).
% 58.67/48.03  tff(c_124, plain, (l1_lattices('#skF_10')), inference(resolution, [status(thm)], [c_98, c_120])).
% 58.67/48.03  tff(c_102, plain, (v10_lattices('#skF_10')), inference(cnfTransformation, [status(thm)], [f_262])).
% 58.67/48.03  tff(c_96, plain, (k15_lattice3('#skF_10', k1_xboole_0)!=k5_lattices('#skF_10') | ~l3_lattices('#skF_10') | ~v13_lattices('#skF_10') | ~v10_lattices('#skF_10') | v2_struct_0('#skF_10')), inference(cnfTransformation, [status(thm)], [f_262])).
% 58.67/48.03  tff(c_106, plain, (k15_lattice3('#skF_10', k1_xboole_0)!=k5_lattices('#skF_10') | ~v13_lattices('#skF_10') | v2_struct_0('#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_102, c_98, c_96])).
% 58.67/48.03  tff(c_107, plain, (k15_lattice3('#skF_10', k1_xboole_0)!=k5_lattices('#skF_10') | ~v13_lattices('#skF_10')), inference(negUnitSimplification, [status(thm)], [c_104, c_106])).
% 58.67/48.03  tff(c_125, plain, (~v13_lattices('#skF_10')), inference(splitLeft, [status(thm)], [c_107])).
% 58.67/48.03  tff(c_100, plain, (v4_lattice3('#skF_10')), inference(cnfTransformation, [status(thm)], [f_262])).
% 58.67/48.03  tff(c_24, plain, (![A_11]: (v6_lattices(A_11) | ~v10_lattices(A_11) | v2_struct_0(A_11) | ~l3_lattices(A_11))), inference(cnfTransformation, [status(thm)], [f_67])).
% 58.67/48.03  tff(c_20, plain, (![A_11]: (v8_lattices(A_11) | ~v10_lattices(A_11) | v2_struct_0(A_11) | ~l3_lattices(A_11))), inference(cnfTransformation, [status(thm)], [f_67])).
% 58.67/48.03  tff(c_18, plain, (![A_11]: (v9_lattices(A_11) | ~v10_lattices(A_11) | v2_struct_0(A_11) | ~l3_lattices(A_11))), inference(cnfTransformation, [status(thm)], [f_67])).
% 58.67/48.03  tff(c_72, plain, (![A_56, B_57]: (m1_subset_1(k15_lattice3(A_56, B_57), u1_struct_0(A_56)) | ~l3_lattices(A_56) | v2_struct_0(A_56))), inference(cnfTransformation, [status(thm)], [f_176])).
% 58.67/48.03  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 58.67/48.03  tff(c_166, plain, (![A_104, B_105]: (~r2_hidden('#skF_1'(A_104, B_105), B_105) | r1_tarski(A_104, B_105))), inference(cnfTransformation, [status(thm)], [f_32])).
% 58.67/48.03  tff(c_171, plain, (![A_1]: (r1_tarski(A_1, A_1))), inference(resolution, [status(thm)], [c_6, c_166])).
% 58.67/48.03  tff(c_56, plain, (![A_34, B_43]: (m1_subset_1('#skF_4'(A_34, B_43), u1_struct_0(A_34)) | v13_lattices(A_34) | ~m1_subset_1(B_43, u1_struct_0(A_34)) | ~l1_lattices(A_34) | v2_struct_0(A_34))), inference(cnfTransformation, [status(thm)], [f_154])).
% 58.67/48.03  tff(c_88, plain, (![A_71, B_73]: (k15_lattice3(A_71, k6_domain_1(u1_struct_0(A_71), B_73))=B_73 | ~m1_subset_1(B_73, u1_struct_0(A_71)) | ~l3_lattices(A_71) | ~v4_lattice3(A_71) | ~v10_lattices(A_71) | v2_struct_0(A_71))), inference(cnfTransformation, [status(thm)], [f_215])).
% 58.67/48.03  tff(c_12, plain, (![A_7]: (k2_zfmisc_1(A_7, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_42])).
% 58.67/48.03  tff(c_554, plain, (![A_180, B_181, C_182]: (r2_hidden('#skF_9'(A_180, B_181, C_182), B_181) | r3_lattices(A_180, k15_lattice3(A_180, B_181), k15_lattice3(A_180, C_182)) | ~l3_lattices(A_180) | ~v4_lattice3(A_180) | ~v10_lattices(A_180) | v2_struct_0(A_180))), inference(cnfTransformation, [status(thm)], [f_241])).
% 58.67/48.03  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 58.67/48.03  tff(c_1430, plain, (![A_297, B_298, C_299, B_300]: (r2_hidden('#skF_9'(A_297, B_298, C_299), B_300) | ~r1_tarski(B_298, B_300) | r3_lattices(A_297, k15_lattice3(A_297, B_298), k15_lattice3(A_297, C_299)) | ~l3_lattices(A_297) | ~v4_lattice3(A_297) | ~v10_lattices(A_297) | v2_struct_0(A_297))), inference(resolution, [status(thm)], [c_554, c_2])).
% 58.67/48.03  tff(c_16, plain, (![A_9, B_10]: (~r2_hidden(A_9, k2_zfmisc_1(A_9, B_10)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 58.67/48.03  tff(c_1477, plain, (![B_303, A_304, C_305, B_306]: (~r1_tarski(B_303, k2_zfmisc_1('#skF_9'(A_304, B_303, C_305), B_306)) | r3_lattices(A_304, k15_lattice3(A_304, B_303), k15_lattice3(A_304, C_305)) | ~l3_lattices(A_304) | ~v4_lattice3(A_304) | ~v10_lattices(A_304) | v2_struct_0(A_304))), inference(resolution, [status(thm)], [c_1430, c_16])).
% 58.67/48.03  tff(c_1507, plain, (![B_309, A_310, C_311]: (~r1_tarski(B_309, k1_xboole_0) | r3_lattices(A_310, k15_lattice3(A_310, B_309), k15_lattice3(A_310, C_311)) | ~l3_lattices(A_310) | ~v4_lattice3(A_310) | ~v10_lattices(A_310) | v2_struct_0(A_310))), inference(superposition, [status(thm), theory('equality')], [c_12, c_1477])).
% 58.67/48.03  tff(c_2559, plain, (![B_444, A_445, B_446]: (~r1_tarski(B_444, k1_xboole_0) | r3_lattices(A_445, k15_lattice3(A_445, B_444), B_446) | ~l3_lattices(A_445) | ~v4_lattice3(A_445) | ~v10_lattices(A_445) | v2_struct_0(A_445) | ~m1_subset_1(B_446, u1_struct_0(A_445)) | ~l3_lattices(A_445) | ~v4_lattice3(A_445) | ~v10_lattices(A_445) | v2_struct_0(A_445))), inference(superposition, [status(thm), theory('equality')], [c_88, c_1507])).
% 58.67/48.03  tff(c_48, plain, (![A_24, B_25, C_26]: (r1_lattices(A_24, B_25, C_26) | ~r3_lattices(A_24, B_25, C_26) | ~m1_subset_1(C_26, u1_struct_0(A_24)) | ~m1_subset_1(B_25, u1_struct_0(A_24)) | ~l3_lattices(A_24) | ~v9_lattices(A_24) | ~v8_lattices(A_24) | ~v6_lattices(A_24) | v2_struct_0(A_24))), inference(cnfTransformation, [status(thm)], [f_118])).
% 58.67/48.03  tff(c_3127, plain, (![A_512, B_513, B_514]: (r1_lattices(A_512, k15_lattice3(A_512, B_513), B_514) | ~m1_subset_1(k15_lattice3(A_512, B_513), u1_struct_0(A_512)) | ~v9_lattices(A_512) | ~v8_lattices(A_512) | ~v6_lattices(A_512) | ~r1_tarski(B_513, k1_xboole_0) | ~m1_subset_1(B_514, u1_struct_0(A_512)) | ~l3_lattices(A_512) | ~v4_lattice3(A_512) | ~v10_lattices(A_512) | v2_struct_0(A_512))), inference(resolution, [status(thm)], [c_2559, c_48])).
% 58.67/48.03  tff(c_3133, plain, (![A_515, B_516, B_517]: (r1_lattices(A_515, k15_lattice3(A_515, B_516), B_517) | ~v9_lattices(A_515) | ~v8_lattices(A_515) | ~v6_lattices(A_515) | ~r1_tarski(B_516, k1_xboole_0) | ~m1_subset_1(B_517, u1_struct_0(A_515)) | ~v4_lattice3(A_515) | ~v10_lattices(A_515) | ~l3_lattices(A_515) | v2_struct_0(A_515))), inference(resolution, [status(thm)], [c_72, c_3127])).
% 58.67/48.03  tff(c_52, plain, (![A_27, B_31, C_33]: (k2_lattices(A_27, B_31, C_33)=B_31 | ~r1_lattices(A_27, B_31, C_33) | ~m1_subset_1(C_33, u1_struct_0(A_27)) | ~m1_subset_1(B_31, u1_struct_0(A_27)) | ~l3_lattices(A_27) | ~v9_lattices(A_27) | ~v8_lattices(A_27) | v2_struct_0(A_27))), inference(cnfTransformation, [status(thm)], [f_137])).
% 58.67/48.03  tff(c_5715, plain, (![A_754, B_755, B_756]: (k2_lattices(A_754, k15_lattice3(A_754, B_755), B_756)=k15_lattice3(A_754, B_755) | ~m1_subset_1(k15_lattice3(A_754, B_755), u1_struct_0(A_754)) | ~v9_lattices(A_754) | ~v8_lattices(A_754) | ~v6_lattices(A_754) | ~r1_tarski(B_755, k1_xboole_0) | ~m1_subset_1(B_756, u1_struct_0(A_754)) | ~v4_lattice3(A_754) | ~v10_lattices(A_754) | ~l3_lattices(A_754) | v2_struct_0(A_754))), inference(resolution, [status(thm)], [c_3133, c_52])).
% 58.67/48.03  tff(c_5721, plain, (![A_757, B_758, B_759]: (k2_lattices(A_757, k15_lattice3(A_757, B_758), B_759)=k15_lattice3(A_757, B_758) | ~v9_lattices(A_757) | ~v8_lattices(A_757) | ~v6_lattices(A_757) | ~r1_tarski(B_758, k1_xboole_0) | ~m1_subset_1(B_759, u1_struct_0(A_757)) | ~v4_lattice3(A_757) | ~v10_lattices(A_757) | ~l3_lattices(A_757) | v2_struct_0(A_757))), inference(resolution, [status(thm)], [c_72, c_5715])).
% 58.67/48.03  tff(c_5749, plain, (![A_34, B_758, B_43]: (k2_lattices(A_34, k15_lattice3(A_34, B_758), '#skF_4'(A_34, B_43))=k15_lattice3(A_34, B_758) | ~v9_lattices(A_34) | ~v8_lattices(A_34) | ~v6_lattices(A_34) | ~r1_tarski(B_758, k1_xboole_0) | ~v4_lattice3(A_34) | ~v10_lattices(A_34) | ~l3_lattices(A_34) | v13_lattices(A_34) | ~m1_subset_1(B_43, u1_struct_0(A_34)) | ~l1_lattices(A_34) | v2_struct_0(A_34))), inference(resolution, [status(thm)], [c_56, c_5721])).
% 58.67/48.03  tff(c_153, plain, (![A_101, B_102]: (r2_hidden('#skF_1'(A_101, B_102), A_101) | r1_tarski(A_101, B_102))), inference(cnfTransformation, [status(thm)], [f_32])).
% 58.67/48.03  tff(c_141, plain, (![A_94, B_95]: (~r2_hidden(A_94, k2_zfmisc_1(A_94, B_95)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 58.67/48.03  tff(c_144, plain, (![A_7]: (~r2_hidden(A_7, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_12, c_141])).
% 58.67/48.03  tff(c_158, plain, (![B_102]: (r1_tarski(k1_xboole_0, B_102))), inference(resolution, [status(thm)], [c_153, c_144])).
% 58.67/48.03  tff(c_92, plain, (![A_74, B_83, C_84]: (r2_hidden('#skF_9'(A_74, B_83, C_84), B_83) | r3_lattices(A_74, k15_lattice3(A_74, B_83), k15_lattice3(A_74, C_84)) | ~l3_lattices(A_74) | ~v4_lattice3(A_74) | ~v10_lattices(A_74) | v2_struct_0(A_74))), inference(cnfTransformation, [status(thm)], [f_241])).
% 58.67/48.03  tff(c_904, plain, (![A_230, B_231, C_232]: (r1_lattices(A_230, B_231, C_232) | ~r3_lattices(A_230, B_231, C_232) | ~m1_subset_1(C_232, u1_struct_0(A_230)) | ~m1_subset_1(B_231, u1_struct_0(A_230)) | ~l3_lattices(A_230) | ~v9_lattices(A_230) | ~v8_lattices(A_230) | ~v6_lattices(A_230) | v2_struct_0(A_230))), inference(cnfTransformation, [status(thm)], [f_118])).
% 58.67/48.03  tff(c_6801, plain, (![A_828, B_829, C_830]: (r1_lattices(A_828, k15_lattice3(A_828, B_829), k15_lattice3(A_828, C_830)) | ~m1_subset_1(k15_lattice3(A_828, C_830), u1_struct_0(A_828)) | ~m1_subset_1(k15_lattice3(A_828, B_829), u1_struct_0(A_828)) | ~v9_lattices(A_828) | ~v8_lattices(A_828) | ~v6_lattices(A_828) | r2_hidden('#skF_9'(A_828, B_829, C_830), B_829) | ~l3_lattices(A_828) | ~v4_lattice3(A_828) | ~v10_lattices(A_828) | v2_struct_0(A_828))), inference(resolution, [status(thm)], [c_92, c_904])).
% 58.67/48.03  tff(c_14419, plain, (![A_1312, B_1313, C_1314]: (k2_lattices(A_1312, k15_lattice3(A_1312, B_1313), k15_lattice3(A_1312, C_1314))=k15_lattice3(A_1312, B_1313) | ~m1_subset_1(k15_lattice3(A_1312, C_1314), u1_struct_0(A_1312)) | ~m1_subset_1(k15_lattice3(A_1312, B_1313), u1_struct_0(A_1312)) | ~v9_lattices(A_1312) | ~v8_lattices(A_1312) | ~v6_lattices(A_1312) | r2_hidden('#skF_9'(A_1312, B_1313, C_1314), B_1313) | ~l3_lattices(A_1312) | ~v4_lattice3(A_1312) | ~v10_lattices(A_1312) | v2_struct_0(A_1312))), inference(resolution, [status(thm)], [c_6801, c_52])).
% 58.67/48.03  tff(c_14441, plain, (![A_1315, B_1316, B_1317]: (k2_lattices(A_1315, k15_lattice3(A_1315, B_1316), k15_lattice3(A_1315, B_1317))=k15_lattice3(A_1315, B_1316) | ~m1_subset_1(k15_lattice3(A_1315, B_1316), u1_struct_0(A_1315)) | ~v9_lattices(A_1315) | ~v8_lattices(A_1315) | ~v6_lattices(A_1315) | r2_hidden('#skF_9'(A_1315, B_1316, B_1317), B_1316) | ~v4_lattice3(A_1315) | ~v10_lattices(A_1315) | ~l3_lattices(A_1315) | v2_struct_0(A_1315))), inference(resolution, [status(thm)], [c_72, c_14419])).
% 58.67/48.03  tff(c_14464, plain, (![A_1318, B_1319, B_1320]: (k2_lattices(A_1318, k15_lattice3(A_1318, B_1319), k15_lattice3(A_1318, B_1320))=k15_lattice3(A_1318, B_1319) | ~v9_lattices(A_1318) | ~v8_lattices(A_1318) | ~v6_lattices(A_1318) | r2_hidden('#skF_9'(A_1318, B_1319, B_1320), B_1319) | ~v4_lattice3(A_1318) | ~v10_lattices(A_1318) | ~l3_lattices(A_1318) | v2_struct_0(A_1318))), inference(resolution, [status(thm)], [c_72, c_14441])).
% 58.67/48.03  tff(c_526, plain, (![A_177, C_178, B_179]: (k2_lattices(A_177, C_178, B_179)=k2_lattices(A_177, B_179, C_178) | ~m1_subset_1(C_178, u1_struct_0(A_177)) | ~m1_subset_1(B_179, u1_struct_0(A_177)) | ~v6_lattices(A_177) | ~l1_lattices(A_177) | v2_struct_0(A_177))), inference(cnfTransformation, [status(thm)], [f_169])).
% 58.67/48.03  tff(c_1331, plain, (![A_282, B_283, B_284]: (k2_lattices(A_282, k15_lattice3(A_282, B_283), B_284)=k2_lattices(A_282, B_284, k15_lattice3(A_282, B_283)) | ~m1_subset_1(B_284, u1_struct_0(A_282)) | ~v6_lattices(A_282) | ~l1_lattices(A_282) | ~l3_lattices(A_282) | v2_struct_0(A_282))), inference(resolution, [status(thm)], [c_72, c_526])).
% 58.67/48.03  tff(c_1357, plain, (![A_56, B_57, B_283]: (k2_lattices(A_56, k15_lattice3(A_56, B_57), k15_lattice3(A_56, B_283))=k2_lattices(A_56, k15_lattice3(A_56, B_283), k15_lattice3(A_56, B_57)) | ~v6_lattices(A_56) | ~l1_lattices(A_56) | ~l3_lattices(A_56) | v2_struct_0(A_56))), inference(resolution, [status(thm)], [c_72, c_1331])).
% 58.67/48.03  tff(c_17954, plain, (![A_1435, B_1436, B_1437]: (k2_lattices(A_1435, k15_lattice3(A_1435, B_1436), k15_lattice3(A_1435, B_1437))=k15_lattice3(A_1435, B_1437) | ~v6_lattices(A_1435) | ~l1_lattices(A_1435) | ~l3_lattices(A_1435) | v2_struct_0(A_1435) | ~v9_lattices(A_1435) | ~v8_lattices(A_1435) | ~v6_lattices(A_1435) | r2_hidden('#skF_9'(A_1435, B_1437, B_1436), B_1437) | ~v4_lattice3(A_1435) | ~v10_lattices(A_1435) | ~l3_lattices(A_1435) | v2_struct_0(A_1435))), inference(superposition, [status(thm), theory('equality')], [c_14464, c_1357])).
% 58.67/48.03  tff(c_18204, plain, (![A_1438, B_1439, B_1440, B_1441]: (r2_hidden('#skF_9'(A_1438, B_1439, B_1440), B_1441) | ~r1_tarski(B_1439, B_1441) | k2_lattices(A_1438, k15_lattice3(A_1438, B_1440), k15_lattice3(A_1438, B_1439))=k15_lattice3(A_1438, B_1439) | ~l1_lattices(A_1438) | ~v9_lattices(A_1438) | ~v8_lattices(A_1438) | ~v6_lattices(A_1438) | ~v4_lattice3(A_1438) | ~v10_lattices(A_1438) | ~l3_lattices(A_1438) | v2_struct_0(A_1438))), inference(resolution, [status(thm)], [c_17954, c_2])).
% 58.67/48.03  tff(c_18502, plain, (![B_1445, A_1446, B_1447, B_1448]: (~r1_tarski(B_1445, k2_zfmisc_1('#skF_9'(A_1446, B_1445, B_1447), B_1448)) | k2_lattices(A_1446, k15_lattice3(A_1446, B_1447), k15_lattice3(A_1446, B_1445))=k15_lattice3(A_1446, B_1445) | ~l1_lattices(A_1446) | ~v9_lattices(A_1446) | ~v8_lattices(A_1446) | ~v6_lattices(A_1446) | ~v4_lattice3(A_1446) | ~v10_lattices(A_1446) | ~l3_lattices(A_1446) | v2_struct_0(A_1446))), inference(resolution, [status(thm)], [c_18204, c_16])).
% 58.67/48.03  tff(c_18553, plain, (![A_1449, B_1450]: (k2_lattices(A_1449, k15_lattice3(A_1449, B_1450), k15_lattice3(A_1449, k1_xboole_0))=k15_lattice3(A_1449, k1_xboole_0) | ~l1_lattices(A_1449) | ~v9_lattices(A_1449) | ~v8_lattices(A_1449) | ~v6_lattices(A_1449) | ~v4_lattice3(A_1449) | ~v10_lattices(A_1449) | ~l3_lattices(A_1449) | v2_struct_0(A_1449))), inference(resolution, [status(thm)], [c_158, c_18502])).
% 58.67/48.03  tff(c_18915, plain, (![A_1454, B_1455]: (k2_lattices(A_1454, B_1455, k15_lattice3(A_1454, k1_xboole_0))=k15_lattice3(A_1454, k1_xboole_0) | ~l1_lattices(A_1454) | ~v9_lattices(A_1454) | ~v8_lattices(A_1454) | ~v6_lattices(A_1454) | ~v4_lattice3(A_1454) | ~v10_lattices(A_1454) | ~l3_lattices(A_1454) | v2_struct_0(A_1454) | ~m1_subset_1(B_1455, u1_struct_0(A_1454)) | ~l3_lattices(A_1454) | ~v4_lattice3(A_1454) | ~v10_lattices(A_1454) | v2_struct_0(A_1454))), inference(superposition, [status(thm), theory('equality')], [c_88, c_18553])).
% 58.67/48.03  tff(c_19130, plain, (![A_1468, B_1469]: (k2_lattices(A_1468, '#skF_4'(A_1468, B_1469), k15_lattice3(A_1468, k1_xboole_0))=k15_lattice3(A_1468, k1_xboole_0) | ~v9_lattices(A_1468) | ~v8_lattices(A_1468) | ~v6_lattices(A_1468) | ~l3_lattices(A_1468) | ~v4_lattice3(A_1468) | ~v10_lattices(A_1468) | v13_lattices(A_1468) | ~m1_subset_1(B_1469, u1_struct_0(A_1468)) | ~l1_lattices(A_1468) | v2_struct_0(A_1468))), inference(resolution, [status(thm)], [c_56, c_18915])).
% 58.67/48.03  tff(c_54, plain, (![A_34, B_43]: (k2_lattices(A_34, '#skF_4'(A_34, B_43), B_43)!=B_43 | k2_lattices(A_34, B_43, '#skF_4'(A_34, B_43))!=B_43 | v13_lattices(A_34) | ~m1_subset_1(B_43, u1_struct_0(A_34)) | ~l1_lattices(A_34) | v2_struct_0(A_34))), inference(cnfTransformation, [status(thm)], [f_154])).
% 58.67/48.03  tff(c_19215, plain, (![A_1475]: (k2_lattices(A_1475, k15_lattice3(A_1475, k1_xboole_0), '#skF_4'(A_1475, k15_lattice3(A_1475, k1_xboole_0)))!=k15_lattice3(A_1475, k1_xboole_0) | ~v9_lattices(A_1475) | ~v8_lattices(A_1475) | ~v6_lattices(A_1475) | ~l3_lattices(A_1475) | ~v4_lattice3(A_1475) | ~v10_lattices(A_1475) | v13_lattices(A_1475) | ~m1_subset_1(k15_lattice3(A_1475, k1_xboole_0), u1_struct_0(A_1475)) | ~l1_lattices(A_1475) | v2_struct_0(A_1475))), inference(superposition, [status(thm), theory('equality')], [c_19130, c_54])).
% 58.67/48.03  tff(c_19219, plain, (![A_34]: (~v9_lattices(A_34) | ~v8_lattices(A_34) | ~v6_lattices(A_34) | ~r1_tarski(k1_xboole_0, k1_xboole_0) | ~v4_lattice3(A_34) | ~v10_lattices(A_34) | ~l3_lattices(A_34) | v13_lattices(A_34) | ~m1_subset_1(k15_lattice3(A_34, k1_xboole_0), u1_struct_0(A_34)) | ~l1_lattices(A_34) | v2_struct_0(A_34))), inference(superposition, [status(thm), theory('equality')], [c_5749, c_19215])).
% 58.67/48.03  tff(c_19228, plain, (![A_1476]: (~v9_lattices(A_1476) | ~v8_lattices(A_1476) | ~v6_lattices(A_1476) | ~v4_lattice3(A_1476) | ~v10_lattices(A_1476) | ~l3_lattices(A_1476) | v13_lattices(A_1476) | ~m1_subset_1(k15_lattice3(A_1476, k1_xboole_0), u1_struct_0(A_1476)) | ~l1_lattices(A_1476) | v2_struct_0(A_1476))), inference(demodulation, [status(thm), theory('equality')], [c_171, c_19219])).
% 58.67/48.03  tff(c_19234, plain, (![A_1477]: (~v9_lattices(A_1477) | ~v8_lattices(A_1477) | ~v6_lattices(A_1477) | ~v4_lattice3(A_1477) | ~v10_lattices(A_1477) | v13_lattices(A_1477) | ~l1_lattices(A_1477) | ~l3_lattices(A_1477) | v2_struct_0(A_1477))), inference(resolution, [status(thm)], [c_72, c_19228])).
% 58.67/48.03  tff(c_19239, plain, (![A_1478]: (~v8_lattices(A_1478) | ~v6_lattices(A_1478) | ~v4_lattice3(A_1478) | v13_lattices(A_1478) | ~l1_lattices(A_1478) | ~v10_lattices(A_1478) | v2_struct_0(A_1478) | ~l3_lattices(A_1478))), inference(resolution, [status(thm)], [c_18, c_19234])).
% 58.67/48.03  tff(c_19244, plain, (![A_1479]: (~v6_lattices(A_1479) | ~v4_lattice3(A_1479) | v13_lattices(A_1479) | ~l1_lattices(A_1479) | ~v10_lattices(A_1479) | v2_struct_0(A_1479) | ~l3_lattices(A_1479))), inference(resolution, [status(thm)], [c_20, c_19239])).
% 58.67/48.03  tff(c_19249, plain, (![A_1480]: (~v4_lattice3(A_1480) | v13_lattices(A_1480) | ~l1_lattices(A_1480) | ~v10_lattices(A_1480) | v2_struct_0(A_1480) | ~l3_lattices(A_1480))), inference(resolution, [status(thm)], [c_24, c_19244])).
% 58.67/48.03  tff(c_19252, plain, (v13_lattices('#skF_10') | ~l1_lattices('#skF_10') | ~v10_lattices('#skF_10') | v2_struct_0('#skF_10') | ~l3_lattices('#skF_10')), inference(resolution, [status(thm)], [c_100, c_19249])).
% 58.67/48.03  tff(c_19255, plain, (v13_lattices('#skF_10') | v2_struct_0('#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_98, c_102, c_124, c_19252])).
% 58.67/48.03  tff(c_19257, plain, $false, inference(negUnitSimplification, [status(thm)], [c_104, c_125, c_19255])).
% 58.67/48.03  tff(c_19259, plain, (v13_lattices('#skF_10')), inference(splitRight, [status(thm)], [c_107])).
% 58.67/48.03  tff(c_40, plain, (![A_22]: (m1_subset_1(k5_lattices(A_22), u1_struct_0(A_22)) | ~l1_lattices(A_22) | v2_struct_0(A_22))), inference(cnfTransformation, [status(thm)], [f_93])).
% 58.67/48.03  tff(c_58, plain, (![A_34]: (m1_subset_1('#skF_3'(A_34), u1_struct_0(A_34)) | ~v13_lattices(A_34) | ~l1_lattices(A_34) | v2_struct_0(A_34))), inference(cnfTransformation, [status(thm)], [f_154])).
% 58.67/48.03  tff(c_19732, plain, (![A_1571, C_1572]: (k2_lattices(A_1571, k5_lattices(A_1571), C_1572)=k5_lattices(A_1571) | ~m1_subset_1(C_1572, u1_struct_0(A_1571)) | ~m1_subset_1(k5_lattices(A_1571), u1_struct_0(A_1571)) | ~v13_lattices(A_1571) | ~l1_lattices(A_1571) | v2_struct_0(A_1571))), inference(cnfTransformation, [status(thm)], [f_86])).
% 58.67/48.03  tff(c_19788, plain, (![A_1575]: (k2_lattices(A_1575, k5_lattices(A_1575), '#skF_3'(A_1575))=k5_lattices(A_1575) | ~m1_subset_1(k5_lattices(A_1575), u1_struct_0(A_1575)) | ~v13_lattices(A_1575) | ~l1_lattices(A_1575) | v2_struct_0(A_1575))), inference(resolution, [status(thm)], [c_58, c_19732])).
% 58.67/48.03  tff(c_19792, plain, (![A_1576]: (k2_lattices(A_1576, k5_lattices(A_1576), '#skF_3'(A_1576))=k5_lattices(A_1576) | ~v13_lattices(A_1576) | ~l1_lattices(A_1576) | v2_struct_0(A_1576))), inference(resolution, [status(thm)], [c_40, c_19788])).
% 58.67/48.03  tff(c_19421, plain, (![A_1527, C_1528]: (k2_lattices(A_1527, C_1528, '#skF_3'(A_1527))='#skF_3'(A_1527) | ~m1_subset_1(C_1528, u1_struct_0(A_1527)) | ~v13_lattices(A_1527) | ~l1_lattices(A_1527) | v2_struct_0(A_1527))), inference(cnfTransformation, [status(thm)], [f_154])).
% 58.67/48.03  tff(c_19439, plain, (![A_22]: (k2_lattices(A_22, k5_lattices(A_22), '#skF_3'(A_22))='#skF_3'(A_22) | ~v13_lattices(A_22) | ~l1_lattices(A_22) | v2_struct_0(A_22))), inference(resolution, [status(thm)], [c_40, c_19421])).
% 58.67/48.03  tff(c_19801, plain, (![A_1576]: (k5_lattices(A_1576)='#skF_3'(A_1576) | ~v13_lattices(A_1576) | ~l1_lattices(A_1576) | v2_struct_0(A_1576) | ~v13_lattices(A_1576) | ~l1_lattices(A_1576) | v2_struct_0(A_1576))), inference(superposition, [status(thm), theory('equality')], [c_19792, c_19439])).
% 58.67/48.03  tff(c_19848, plain, (![A_1581]: (k5_lattices(A_1581)='#skF_3'(A_1581) | ~v13_lattices(A_1581) | ~l1_lattices(A_1581) | v2_struct_0(A_1581))), inference(factorization, [status(thm), theory('equality')], [c_19801])).
% 58.67/48.03  tff(c_19851, plain, (k5_lattices('#skF_10')='#skF_3'('#skF_10') | ~v13_lattices('#skF_10') | ~l1_lattices('#skF_10')), inference(resolution, [status(thm)], [c_19848, c_104])).
% 58.67/48.03  tff(c_19854, plain, (k5_lattices('#skF_10')='#skF_3'('#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_124, c_19259, c_19851])).
% 58.67/48.03  tff(c_19258, plain, (k15_lattice3('#skF_10', k1_xboole_0)!=k5_lattices('#skF_10')), inference(splitRight, [status(thm)], [c_107])).
% 58.67/48.03  tff(c_19855, plain, (k15_lattice3('#skF_10', k1_xboole_0)!='#skF_3'('#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_19854, c_19258])).
% 58.67/48.03  tff(c_19871, plain, (m1_subset_1('#skF_3'('#skF_10'), u1_struct_0('#skF_10')) | ~l1_lattices('#skF_10') | v2_struct_0('#skF_10')), inference(superposition, [status(thm), theory('equality')], [c_19854, c_40])).
% 58.67/48.03  tff(c_19887, plain, (m1_subset_1('#skF_3'('#skF_10'), u1_struct_0('#skF_10')) | v2_struct_0('#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_124, c_19871])).
% 58.67/48.03  tff(c_19888, plain, (m1_subset_1('#skF_3'('#skF_10'), u1_struct_0('#skF_10'))), inference(negUnitSimplification, [status(thm)], [c_104, c_19887])).
% 58.67/48.03  tff(c_64, plain, (![A_45, C_54, B_52]: (k2_lattices(A_45, C_54, B_52)=k2_lattices(A_45, B_52, C_54) | ~m1_subset_1(C_54, u1_struct_0(A_45)) | ~m1_subset_1(B_52, u1_struct_0(A_45)) | ~v6_lattices(A_45) | ~l1_lattices(A_45) | v2_struct_0(A_45))), inference(cnfTransformation, [status(thm)], [f_169])).
% 58.67/48.03  tff(c_19897, plain, (![B_52]: (k2_lattices('#skF_10', B_52, '#skF_3'('#skF_10'))=k2_lattices('#skF_10', '#skF_3'('#skF_10'), B_52) | ~m1_subset_1(B_52, u1_struct_0('#skF_10')) | ~v6_lattices('#skF_10') | ~l1_lattices('#skF_10') | v2_struct_0('#skF_10'))), inference(resolution, [status(thm)], [c_19888, c_64])).
% 58.67/48.03  tff(c_19916, plain, (![B_52]: (k2_lattices('#skF_10', B_52, '#skF_3'('#skF_10'))=k2_lattices('#skF_10', '#skF_3'('#skF_10'), B_52) | ~m1_subset_1(B_52, u1_struct_0('#skF_10')) | ~v6_lattices('#skF_10') | v2_struct_0('#skF_10'))), inference(demodulation, [status(thm), theory('equality')], [c_124, c_19897])).
% 58.67/48.03  tff(c_19917, plain, (![B_52]: (k2_lattices('#skF_10', B_52, '#skF_3'('#skF_10'))=k2_lattices('#skF_10', '#skF_3'('#skF_10'), B_52) | ~m1_subset_1(B_52, u1_struct_0('#skF_10')) | ~v6_lattices('#skF_10'))), inference(negUnitSimplification, [status(thm)], [c_104, c_19916])).
% 58.67/48.03  tff(c_19957, plain, (~v6_lattices('#skF_10')), inference(splitLeft, [status(thm)], [c_19917])).
% 58.67/48.03  tff(c_19961, plain, (~v10_lattices('#skF_10') | v2_struct_0('#skF_10') | ~l3_lattices('#skF_10')), inference(resolution, [status(thm)], [c_24, c_19957])).
% 58.67/48.03  tff(c_19964, plain, (v2_struct_0('#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_98, c_102, c_19961])).
% 58.67/48.03  tff(c_19966, plain, $false, inference(negUnitSimplification, [status(thm)], [c_104, c_19964])).
% 58.67/48.03  tff(c_19968, plain, (v6_lattices('#skF_10')), inference(splitRight, [status(thm)], [c_19917])).
% 58.67/48.03  tff(c_20701, plain, (![A_1637, B_1638, C_1639]: (r1_lattices(A_1637, B_1638, C_1639) | k2_lattices(A_1637, B_1638, C_1639)!=B_1638 | ~m1_subset_1(C_1639, u1_struct_0(A_1637)) | ~m1_subset_1(B_1638, u1_struct_0(A_1637)) | ~l3_lattices(A_1637) | ~v9_lattices(A_1637) | ~v8_lattices(A_1637) | v2_struct_0(A_1637))), inference(cnfTransformation, [status(thm)], [f_137])).
% 58.67/48.03  tff(c_20703, plain, (![B_1638]: (r1_lattices('#skF_10', B_1638, '#skF_3'('#skF_10')) | k2_lattices('#skF_10', B_1638, '#skF_3'('#skF_10'))!=B_1638 | ~m1_subset_1(B_1638, u1_struct_0('#skF_10')) | ~l3_lattices('#skF_10') | ~v9_lattices('#skF_10') | ~v8_lattices('#skF_10') | v2_struct_0('#skF_10'))), inference(resolution, [status(thm)], [c_19888, c_20701])).
% 58.67/48.03  tff(c_20724, plain, (![B_1638]: (r1_lattices('#skF_10', B_1638, '#skF_3'('#skF_10')) | k2_lattices('#skF_10', B_1638, '#skF_3'('#skF_10'))!=B_1638 | ~m1_subset_1(B_1638, u1_struct_0('#skF_10')) | ~v9_lattices('#skF_10') | ~v8_lattices('#skF_10') | v2_struct_0('#skF_10'))), inference(demodulation, [status(thm), theory('equality')], [c_98, c_20703])).
% 58.67/48.03  tff(c_20725, plain, (![B_1638]: (r1_lattices('#skF_10', B_1638, '#skF_3'('#skF_10')) | k2_lattices('#skF_10', B_1638, '#skF_3'('#skF_10'))!=B_1638 | ~m1_subset_1(B_1638, u1_struct_0('#skF_10')) | ~v9_lattices('#skF_10') | ~v8_lattices('#skF_10'))), inference(negUnitSimplification, [status(thm)], [c_104, c_20724])).
% 58.67/48.03  tff(c_20753, plain, (~v8_lattices('#skF_10')), inference(splitLeft, [status(thm)], [c_20725])).
% 58.67/48.03  tff(c_20756, plain, (~v10_lattices('#skF_10') | v2_struct_0('#skF_10') | ~l3_lattices('#skF_10')), inference(resolution, [status(thm)], [c_20, c_20753])).
% 58.67/48.03  tff(c_20759, plain, (v2_struct_0('#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_98, c_102, c_20756])).
% 58.67/48.03  tff(c_20761, plain, $false, inference(negUnitSimplification, [status(thm)], [c_104, c_20759])).
% 58.67/48.03  tff(c_20763, plain, (v8_lattices('#skF_10')), inference(splitRight, [status(thm)], [c_20725])).
% 58.67/48.03  tff(c_20762, plain, (![B_1638]: (~v9_lattices('#skF_10') | r1_lattices('#skF_10', B_1638, '#skF_3'('#skF_10')) | k2_lattices('#skF_10', B_1638, '#skF_3'('#skF_10'))!=B_1638 | ~m1_subset_1(B_1638, u1_struct_0('#skF_10')))), inference(splitRight, [status(thm)], [c_20725])).
% 58.67/48.03  tff(c_20764, plain, (~v9_lattices('#skF_10')), inference(splitLeft, [status(thm)], [c_20762])).
% 58.67/48.03  tff(c_20767, plain, (~v10_lattices('#skF_10') | v2_struct_0('#skF_10') | ~l3_lattices('#skF_10')), inference(resolution, [status(thm)], [c_18, c_20764])).
% 58.67/48.03  tff(c_20770, plain, (v2_struct_0('#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_98, c_102, c_20767])).
% 58.67/48.03  tff(c_20772, plain, $false, inference(negUnitSimplification, [status(thm)], [c_104, c_20770])).
% 58.67/48.03  tff(c_20774, plain, (v9_lattices('#skF_10')), inference(splitRight, [status(thm)], [c_20762])).
% 58.67/48.03  tff(c_19969, plain, (![B_1588]: (k2_lattices('#skF_10', B_1588, '#skF_3'('#skF_10'))=k2_lattices('#skF_10', '#skF_3'('#skF_10'), B_1588) | ~m1_subset_1(B_1588, u1_struct_0('#skF_10')))), inference(splitRight, [status(thm)], [c_19917])).
% 58.67/48.03  tff(c_20004, plain, (![B_57]: (k2_lattices('#skF_10', k15_lattice3('#skF_10', B_57), '#skF_3'('#skF_10'))=k2_lattices('#skF_10', '#skF_3'('#skF_10'), k15_lattice3('#skF_10', B_57)) | ~l3_lattices('#skF_10') | v2_struct_0('#skF_10'))), inference(resolution, [status(thm)], [c_72, c_19969])).
% 58.67/48.03  tff(c_20041, plain, (![B_57]: (k2_lattices('#skF_10', k15_lattice3('#skF_10', B_57), '#skF_3'('#skF_10'))=k2_lattices('#skF_10', '#skF_3'('#skF_10'), k15_lattice3('#skF_10', B_57)) | v2_struct_0('#skF_10'))), inference(demodulation, [status(thm), theory('equality')], [c_98, c_20004])).
% 58.67/48.03  tff(c_20047, plain, (![B_1589]: (k2_lattices('#skF_10', k15_lattice3('#skF_10', B_1589), '#skF_3'('#skF_10'))=k2_lattices('#skF_10', '#skF_3'('#skF_10'), k15_lattice3('#skF_10', B_1589)))), inference(negUnitSimplification, [status(thm)], [c_104, c_20041])).
% 58.67/48.03  tff(c_19438, plain, (![A_56, B_57]: (k2_lattices(A_56, k15_lattice3(A_56, B_57), '#skF_3'(A_56))='#skF_3'(A_56) | ~v13_lattices(A_56) | ~l1_lattices(A_56) | ~l3_lattices(A_56) | v2_struct_0(A_56))), inference(resolution, [status(thm)], [c_72, c_19421])).
% 58.67/48.03  tff(c_20053, plain, (![B_1589]: (k2_lattices('#skF_10', '#skF_3'('#skF_10'), k15_lattice3('#skF_10', B_1589))='#skF_3'('#skF_10') | ~v13_lattices('#skF_10') | ~l1_lattices('#skF_10') | ~l3_lattices('#skF_10') | v2_struct_0('#skF_10'))), inference(superposition, [status(thm), theory('equality')], [c_20047, c_19438])).
% 58.67/48.03  tff(c_20067, plain, (![B_1589]: (k2_lattices('#skF_10', '#skF_3'('#skF_10'), k15_lattice3('#skF_10', B_1589))='#skF_3'('#skF_10') | v2_struct_0('#skF_10'))), inference(demodulation, [status(thm), theory('equality')], [c_98, c_124, c_19259, c_20053])).
% 58.67/48.03  tff(c_20068, plain, (![B_1589]: (k2_lattices('#skF_10', '#skF_3'('#skF_10'), k15_lattice3('#skF_10', B_1589))='#skF_3'('#skF_10'))), inference(negUnitSimplification, [status(thm)], [c_104, c_20067])).
% 58.67/48.03  tff(c_20042, plain, (![B_57]: (k2_lattices('#skF_10', k15_lattice3('#skF_10', B_57), '#skF_3'('#skF_10'))=k2_lattices('#skF_10', '#skF_3'('#skF_10'), k15_lattice3('#skF_10', B_57)))), inference(negUnitSimplification, [status(thm)], [c_104, c_20041])).
% 58.67/48.03  tff(c_20076, plain, (![B_57]: (k2_lattices('#skF_10', k15_lattice3('#skF_10', B_57), '#skF_3'('#skF_10'))='#skF_3'('#skF_10'))), inference(demodulation, [status(thm), theory('equality')], [c_20068, c_20042])).
% 58.67/48.03  tff(c_19298, plain, (![A_1492, B_1493]: (r2_hidden('#skF_1'(A_1492, B_1493), A_1492) | r1_tarski(A_1492, B_1493))), inference(cnfTransformation, [status(thm)], [f_32])).
% 58.67/48.03  tff(c_19275, plain, (![A_1482, B_1483]: (~r2_hidden(A_1482, k2_zfmisc_1(A_1482, B_1483)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 58.67/48.03  tff(c_19278, plain, (![A_7]: (~r2_hidden(A_7, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_12, c_19275])).
% 58.67/48.03  tff(c_19308, plain, (![B_1493]: (r1_tarski(k1_xboole_0, B_1493))), inference(resolution, [status(thm)], [c_19298, c_19278])).
% 58.67/48.03  tff(c_19826, plain, (![A_1578, B_1579, C_1580]: (r2_hidden('#skF_9'(A_1578, B_1579, C_1580), B_1579) | r3_lattices(A_1578, k15_lattice3(A_1578, B_1579), k15_lattice3(A_1578, C_1580)) | ~l3_lattices(A_1578) | ~v4_lattice3(A_1578) | ~v10_lattices(A_1578) | v2_struct_0(A_1578))), inference(cnfTransformation, [status(thm)], [f_241])).
% 58.67/48.03  tff(c_21389, plain, (![A_1710, B_1711, C_1712, B_1713]: (r2_hidden('#skF_9'(A_1710, B_1711, C_1712), B_1713) | ~r1_tarski(B_1711, B_1713) | r3_lattices(A_1710, k15_lattice3(A_1710, B_1711), k15_lattice3(A_1710, C_1712)) | ~l3_lattices(A_1710) | ~v4_lattice3(A_1710) | ~v10_lattices(A_1710) | v2_struct_0(A_1710))), inference(resolution, [status(thm)], [c_19826, c_2])).
% 58.67/48.03  tff(c_21432, plain, (![B_1714, A_1715, C_1716, B_1717]: (~r1_tarski(B_1714, k2_zfmisc_1('#skF_9'(A_1715, B_1714, C_1716), B_1717)) | r3_lattices(A_1715, k15_lattice3(A_1715, B_1714), k15_lattice3(A_1715, C_1716)) | ~l3_lattices(A_1715) | ~v4_lattice3(A_1715) | ~v10_lattices(A_1715) | v2_struct_0(A_1715))), inference(resolution, [status(thm)], [c_21389, c_16])).
% 58.67/48.03  tff(c_21455, plain, (![A_1718, C_1719]: (r3_lattices(A_1718, k15_lattice3(A_1718, k1_xboole_0), k15_lattice3(A_1718, C_1719)) | ~l3_lattices(A_1718) | ~v4_lattice3(A_1718) | ~v10_lattices(A_1718) | v2_struct_0(A_1718))), inference(resolution, [status(thm)], [c_19308, c_21432])).
% 58.67/48.03  tff(c_22427, plain, (![A_1793, B_1794]: (r3_lattices(A_1793, k15_lattice3(A_1793, k1_xboole_0), B_1794) | ~l3_lattices(A_1793) | ~v4_lattice3(A_1793) | ~v10_lattices(A_1793) | v2_struct_0(A_1793) | ~m1_subset_1(B_1794, u1_struct_0(A_1793)) | ~l3_lattices(A_1793) | ~v4_lattice3(A_1793) | ~v10_lattices(A_1793) | v2_struct_0(A_1793))), inference(superposition, [status(thm), theory('equality')], [c_88, c_21455])).
% 58.67/48.03  tff(c_23794, plain, (![A_1908, B_1909]: (r1_lattices(A_1908, k15_lattice3(A_1908, k1_xboole_0), B_1909) | ~m1_subset_1(k15_lattice3(A_1908, k1_xboole_0), u1_struct_0(A_1908)) | ~v9_lattices(A_1908) | ~v8_lattices(A_1908) | ~v6_lattices(A_1908) | ~m1_subset_1(B_1909, u1_struct_0(A_1908)) | ~l3_lattices(A_1908) | ~v4_lattice3(A_1908) | ~v10_lattices(A_1908) | v2_struct_0(A_1908))), inference(resolution, [status(thm)], [c_22427, c_48])).
% 58.67/48.03  tff(c_23799, plain, (![A_1910, B_1911]: (r1_lattices(A_1910, k15_lattice3(A_1910, k1_xboole_0), B_1911) | ~v9_lattices(A_1910) | ~v8_lattices(A_1910) | ~v6_lattices(A_1910) | ~m1_subset_1(B_1911, u1_struct_0(A_1910)) | ~v4_lattice3(A_1910) | ~v10_lattices(A_1910) | ~l3_lattices(A_1910) | v2_struct_0(A_1910))), inference(resolution, [status(thm)], [c_72, c_23794])).
% 58.67/48.03  tff(c_27641, plain, (![A_2095, B_2096]: (k2_lattices(A_2095, k15_lattice3(A_2095, k1_xboole_0), B_2096)=k15_lattice3(A_2095, k1_xboole_0) | ~m1_subset_1(k15_lattice3(A_2095, k1_xboole_0), u1_struct_0(A_2095)) | ~v9_lattices(A_2095) | ~v8_lattices(A_2095) | ~v6_lattices(A_2095) | ~m1_subset_1(B_2096, u1_struct_0(A_2095)) | ~v4_lattice3(A_2095) | ~v10_lattices(A_2095) | ~l3_lattices(A_2095) | v2_struct_0(A_2095))), inference(resolution, [status(thm)], [c_23799, c_52])).
% 58.67/48.03  tff(c_27653, plain, (![A_2101, B_2102]: (k2_lattices(A_2101, k15_lattice3(A_2101, k1_xboole_0), B_2102)=k15_lattice3(A_2101, k1_xboole_0) | ~v9_lattices(A_2101) | ~v8_lattices(A_2101) | ~v6_lattices(A_2101) | ~m1_subset_1(B_2102, u1_struct_0(A_2101)) | ~v4_lattice3(A_2101) | ~v10_lattices(A_2101) | ~l3_lattices(A_2101) | v2_struct_0(A_2101))), inference(resolution, [status(thm)], [c_72, c_27641])).
% 58.67/48.03  tff(c_27657, plain, (k2_lattices('#skF_10', k15_lattice3('#skF_10', k1_xboole_0), '#skF_3'('#skF_10'))=k15_lattice3('#skF_10', k1_xboole_0) | ~v9_lattices('#skF_10') | ~v8_lattices('#skF_10') | ~v6_lattices('#skF_10') | ~v4_lattice3('#skF_10') | ~v10_lattices('#skF_10') | ~l3_lattices('#skF_10') | v2_struct_0('#skF_10')), inference(resolution, [status(thm)], [c_19888, c_27653])).
% 58.67/48.03  tff(c_27679, plain, (k15_lattice3('#skF_10', k1_xboole_0)='#skF_3'('#skF_10') | v2_struct_0('#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_98, c_102, c_100, c_19968, c_20763, c_20774, c_20076, c_27657])).
% 58.67/48.03  tff(c_27681, plain, $false, inference(negUnitSimplification, [status(thm)], [c_104, c_19855, c_27679])).
% 58.67/48.03  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 58.67/48.03  
% 58.67/48.03  Inference rules
% 58.67/48.03  ----------------------
% 58.67/48.03  #Ref     : 0
% 58.67/48.03  #Sup     : 7005
% 58.67/48.03  #Fact    : 4
% 58.67/48.03  #Define  : 0
% 58.67/48.03  #Split   : 39
% 58.67/48.03  #Chain   : 0
% 58.67/48.03  #Close   : 0
% 58.67/48.03  
% 58.67/48.03  Ordering : KBO
% 58.67/48.03  
% 58.89/48.03  Simplification rules
% 58.89/48.03  ----------------------
% 58.89/48.03  #Subsume      : 5771
% 58.89/48.03  #Demod        : 2681
% 58.89/48.03  #Tautology    : 1241
% 58.89/48.03  #SimpNegUnit  : 563
% 58.89/48.03  #BackRed      : 2
% 58.89/48.03  
% 58.89/48.03  #Partial instantiations: 0
% 58.89/48.03  #Strategies tried      : 1
% 58.89/48.03  
% 58.89/48.03  Timing (in seconds)
% 58.89/48.03  ----------------------
% 58.89/48.03  Preprocessing        : 0.40
% 58.89/48.03  Parsing              : 0.20
% 58.89/48.03  CNF conversion       : 0.03
% 58.89/48.03  Main loop            : 46.84
% 58.89/48.03  Inferencing          : 2.26
% 58.89/48.03  Reduction            : 1.79
% 58.89/48.03  Demodulation         : 1.29
% 58.89/48.03  BG Simplification    : 0.22
% 58.89/48.03  Subsumption          : 42.19
% 58.89/48.03  Abstraction          : 0.29
% 58.89/48.03  MUC search           : 0.00
% 58.89/48.03  Cooper               : 0.00
% 58.89/48.03  Total                : 47.30
% 58.89/48.03  Index Insertion      : 0.00
% 58.89/48.03  Index Deletion       : 0.00
% 58.89/48.03  Index Matching       : 0.00
% 58.89/48.03  BG Taut test         : 0.00
%------------------------------------------------------------------------------
