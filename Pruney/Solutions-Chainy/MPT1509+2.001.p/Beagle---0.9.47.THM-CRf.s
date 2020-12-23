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
% DateTime   : Thu Dec  3 10:24:49 EST 2020

% Result     : Theorem 11.51s
% Output     : CNFRefutation 11.78s
% Verified   : 
% Statistics : Number of formulae       :  318 (4523 expanded)
%              Number of leaves         :   59 (1491 expanded)
%              Depth                    :   31
%              Number of atoms          : 1034 (19287 expanded)
%              Number of equality atoms :  132 (3683 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r4_lattice3 > r3_lattice3 > r1_lattices > r2_hidden > m1_subset_1 > v9_lattices > v8_lattices > v7_lattices > v6_lattices > v5_lattices > v4_lattices > v4_lattice3 > v2_struct_0 > v1_xboole_0 > v10_lattices > l3_lattices > l2_lattices > l1_struct_0 > l1_lattices > k4_lattices > k2_lattices > k1_lattices > k6_domain_1 > k16_lattice3 > k15_lattice3 > #nlpp > u1_struct_0 > k1_tarski > #skF_9 > #skF_4 > #skF_11 > #skF_6 > #skF_8 > #skF_10 > #skF_5 > #skF_7 > #skF_3 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(l3_lattices,type,(
    l3_lattices: $i > $o )).

tff('#skF_9',type,(
    '#skF_9': $i > $i )).

tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(k2_lattices,type,(
    k2_lattices: ( $i * $i * $i ) > $i )).

tff(l2_lattices,type,(
    l2_lattices: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_11',type,(
    '#skF_11': $i )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i ) > $i )).

tff(k4_lattices,type,(
    k4_lattices: ( $i * $i * $i ) > $i )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k16_lattice3,type,(
    k16_lattice3: ( $i * $i ) > $i )).

tff(k1_lattices,type,(
    k1_lattices: ( $i * $i * $i ) > $i )).

tff(k15_lattice3,type,(
    k15_lattice3: ( $i * $i ) > $i )).

tff(l1_lattices,type,(
    l1_lattices: $i > $o )).

tff('#skF_8',type,(
    '#skF_8': $i > $i )).

tff(r1_lattices,type,(
    r1_lattices: ( $i * $i * $i ) > $o )).

tff(k6_domain_1,type,(
    k6_domain_1: ( $i * $i ) > $i )).

tff('#skF_10',type,(
    '#skF_10': $i )).

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

tff('#skF_7',type,(
    '#skF_7': ( $i * $i * $i ) > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_3',type,(
    '#skF_3': $i > $i )).

tff(v8_lattices,type,(
    v8_lattices: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(r3_lattice3,type,(
    r3_lattice3: ( $i * $i * $i ) > $o )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(v7_lattices,type,(
    v7_lattices: $i > $o )).

tff(f_307,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v10_lattices(A)
          & v4_lattice3(A)
          & l3_lattices(A) )
       => ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => ( k15_lattice3(A,k6_domain_1(u1_struct_0(A),B)) = B
              & k16_lattice3(A,k6_domain_1(u1_struct_0(A),B)) = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_lattice3)).

tff(f_94,axiom,(
    ! [A] :
      ( l3_lattices(A)
     => ( l1_lattices(A)
        & l2_lattices(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l3_lattices)).

tff(f_88,axiom,(
    ! [A] :
      ( l2_lattices(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l2_lattices)).

tff(f_47,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_40,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

tff(f_271,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & l3_lattices(A) )
     => m1_subset_1(k15_lattice3(A,B),u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k15_lattice3)).

tff(f_249,axiom,(
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

tff(f_32,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

tff(f_221,axiom,(
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

tff(f_69,axiom,(
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

tff(f_123,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v6_lattices(A)
        & v8_lattices(A)
        & v9_lattices(A)
        & l3_lattices(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => k1_lattices(A,B,B) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_lattices)).

tff(f_264,axiom,(
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

tff(f_142,axiom,(
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

tff(f_161,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v4_lattices(A)
        & l2_lattices(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ( ( r1_lattices(A,B,C)
                  & r1_lattices(A,C,B) )
               => B = C ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_lattices)).

tff(f_84,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l3_lattices(A) )
     => ( v9_lattices(A)
      <=> ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => ! [C] :
                ( m1_subset_1(C,u1_struct_0(A))
               => k2_lattices(A,B,k1_lattices(A,B,C)) = B ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_lattices)).

tff(f_185,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v7_lattices(A)
        & v8_lattices(A)
        & v9_lattices(A)
        & l3_lattices(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ! [D] :
                  ( m1_subset_1(D,u1_struct_0(A))
                 => ( r1_lattices(A,B,C)
                   => r1_lattices(A,k2_lattices(A,B,D),k2_lattices(A,C,D)) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t27_lattices)).

tff(f_203,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d16_lattice3)).

tff(f_290,axiom,(
    ! [A] :
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_lattice3)).

tff(c_106,plain,(
    ~ v2_struct_0('#skF_10') ),
    inference(cnfTransformation,[status(thm)],[f_307])).

tff(c_100,plain,(
    l3_lattices('#skF_10') ),
    inference(cnfTransformation,[status(thm)],[f_307])).

tff(c_114,plain,(
    ! [A_138] :
      ( l2_lattices(A_138)
      | ~ l3_lattices(A_138) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_118,plain,(
    l2_lattices('#skF_10') ),
    inference(resolution,[status(thm)],[c_100,c_114])).

tff(c_40,plain,(
    ! [A_21] :
      ( l1_struct_0(A_21)
      | ~ l2_lattices(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_122,plain,(
    l1_struct_0('#skF_10') ),
    inference(resolution,[status(thm)],[c_118,c_40])).

tff(c_98,plain,(
    m1_subset_1('#skF_11',u1_struct_0('#skF_10')) ),
    inference(cnfTransformation,[status(thm)],[f_307])).

tff(c_11595,plain,(
    ! [A_778,B_779] :
      ( k6_domain_1(A_778,B_779) = k1_tarski(B_779)
      | ~ m1_subset_1(B_779,A_778)
      | v1_xboole_0(A_778) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_11599,plain,
    ( k6_domain_1(u1_struct_0('#skF_10'),'#skF_11') = k1_tarski('#skF_11')
    | v1_xboole_0(u1_struct_0('#skF_10')) ),
    inference(resolution,[status(thm)],[c_98,c_11595])).

tff(c_11611,plain,(
    v1_xboole_0(u1_struct_0('#skF_10')) ),
    inference(splitLeft,[status(thm)],[c_11599])).

tff(c_14,plain,(
    ! [A_6] :
      ( ~ v1_xboole_0(u1_struct_0(A_6))
      | ~ l1_struct_0(A_6)
      | v2_struct_0(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_11614,plain,
    ( ~ l1_struct_0('#skF_10')
    | v2_struct_0('#skF_10') ),
    inference(resolution,[status(thm)],[c_11611,c_14])).

tff(c_11617,plain,(
    v2_struct_0('#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_122,c_11614])).

tff(c_11619,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_106,c_11617])).

tff(c_11620,plain,(
    k6_domain_1(u1_struct_0('#skF_10'),'#skF_11') = k1_tarski('#skF_11') ),
    inference(splitRight,[status(thm)],[c_11599])).

tff(c_137,plain,(
    ! [A_148,B_149] :
      ( k6_domain_1(A_148,B_149) = k1_tarski(B_149)
      | ~ m1_subset_1(B_149,A_148)
      | v1_xboole_0(A_148) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_141,plain,
    ( k6_domain_1(u1_struct_0('#skF_10'),'#skF_11') = k1_tarski('#skF_11')
    | v1_xboole_0(u1_struct_0('#skF_10')) ),
    inference(resolution,[status(thm)],[c_98,c_137])).

tff(c_142,plain,(
    v1_xboole_0(u1_struct_0('#skF_10')) ),
    inference(splitLeft,[status(thm)],[c_141])).

tff(c_145,plain,
    ( ~ l1_struct_0('#skF_10')
    | v2_struct_0('#skF_10') ),
    inference(resolution,[status(thm)],[c_142,c_14])).

tff(c_148,plain,(
    v2_struct_0('#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_122,c_145])).

tff(c_150,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_106,c_148])).

tff(c_151,plain,(
    k6_domain_1(u1_struct_0('#skF_10'),'#skF_11') = k1_tarski('#skF_11') ),
    inference(splitRight,[status(thm)],[c_141])).

tff(c_96,plain,
    ( k16_lattice3('#skF_10',k6_domain_1(u1_struct_0('#skF_10'),'#skF_11')) != '#skF_11'
    | k15_lattice3('#skF_10',k6_domain_1(u1_struct_0('#skF_10'),'#skF_11')) != '#skF_11' ),
    inference(cnfTransformation,[status(thm)],[f_307])).

tff(c_135,plain,(
    k15_lattice3('#skF_10',k6_domain_1(u1_struct_0('#skF_10'),'#skF_11')) != '#skF_11' ),
    inference(splitLeft,[status(thm)],[c_96])).

tff(c_158,plain,(
    k15_lattice3('#skF_10',k1_tarski('#skF_11')) != '#skF_11' ),
    inference(demodulation,[status(thm),theory(equality)],[c_151,c_135])).

tff(c_104,plain,(
    v10_lattices('#skF_10') ),
    inference(cnfTransformation,[status(thm)],[f_307])).

tff(c_102,plain,(
    v4_lattice3('#skF_10') ),
    inference(cnfTransformation,[status(thm)],[f_307])).

tff(c_92,plain,(
    ! [A_125,B_126] :
      ( m1_subset_1(k15_lattice3(A_125,B_126),u1_struct_0(A_125))
      | ~ l3_lattices(A_125)
      | v2_struct_0(A_125) ) ),
    inference(cnfTransformation,[status(thm)],[f_271])).

tff(c_359,plain,(
    ! [A_202,B_203] :
      ( r4_lattice3(A_202,k15_lattice3(A_202,B_203),B_203)
      | ~ m1_subset_1(k15_lattice3(A_202,B_203),u1_struct_0(A_202))
      | ~ v4_lattice3(A_202)
      | ~ v10_lattices(A_202)
      | ~ l3_lattices(A_202)
      | v2_struct_0(A_202) ) ),
    inference(cnfTransformation,[status(thm)],[f_249])).

tff(c_362,plain,(
    ! [A_125,B_126] :
      ( r4_lattice3(A_125,k15_lattice3(A_125,B_126),B_126)
      | ~ v4_lattice3(A_125)
      | ~ v10_lattices(A_125)
      | ~ l3_lattices(A_125)
      | v2_struct_0(A_125) ) ),
    inference(resolution,[status(thm)],[c_92,c_359])).

tff(c_4,plain,(
    ! [C_5] : r2_hidden(C_5,k1_tarski(C_5)) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_935,plain,(
    ! [A_244,D_245,B_246,C_247] :
      ( r1_lattices(A_244,D_245,B_246)
      | ~ r2_hidden(D_245,C_247)
      | ~ m1_subset_1(D_245,u1_struct_0(A_244))
      | ~ r4_lattice3(A_244,B_246,C_247)
      | ~ m1_subset_1(B_246,u1_struct_0(A_244))
      | ~ l3_lattices(A_244)
      | v2_struct_0(A_244) ) ),
    inference(cnfTransformation,[status(thm)],[f_221])).

tff(c_951,plain,(
    ! [A_248,C_249,B_250] :
      ( r1_lattices(A_248,C_249,B_250)
      | ~ m1_subset_1(C_249,u1_struct_0(A_248))
      | ~ r4_lattice3(A_248,B_250,k1_tarski(C_249))
      | ~ m1_subset_1(B_250,u1_struct_0(A_248))
      | ~ l3_lattices(A_248)
      | v2_struct_0(A_248) ) ),
    inference(resolution,[status(thm)],[c_4,c_935])).

tff(c_8500,plain,(
    ! [A_666,C_667] :
      ( r1_lattices(A_666,C_667,k15_lattice3(A_666,k1_tarski(C_667)))
      | ~ m1_subset_1(C_667,u1_struct_0(A_666))
      | ~ m1_subset_1(k15_lattice3(A_666,k1_tarski(C_667)),u1_struct_0(A_666))
      | ~ v4_lattice3(A_666)
      | ~ v10_lattices(A_666)
      | ~ l3_lattices(A_666)
      | v2_struct_0(A_666) ) ),
    inference(resolution,[status(thm)],[c_362,c_951])).

tff(c_8504,plain,(
    ! [A_125,C_667] :
      ( r1_lattices(A_125,C_667,k15_lattice3(A_125,k1_tarski(C_667)))
      | ~ m1_subset_1(C_667,u1_struct_0(A_125))
      | ~ v4_lattice3(A_125)
      | ~ v10_lattices(A_125)
      | ~ l3_lattices(A_125)
      | v2_struct_0(A_125) ) ),
    inference(resolution,[status(thm)],[c_92,c_8500])).

tff(c_28,plain,(
    ! [A_9] :
      ( v4_lattices(A_9)
      | ~ v10_lattices(A_9)
      | v2_struct_0(A_9)
      | ~ l3_lattices(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_107,plain,(
    ! [A_135] :
      ( l1_lattices(A_135)
      | ~ l3_lattices(A_135) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_111,plain,(
    l1_lattices('#skF_10') ),
    inference(resolution,[status(thm)],[c_100,c_107])).

tff(c_24,plain,(
    ! [A_9] :
      ( v6_lattices(A_9)
      | ~ v10_lattices(A_9)
      | v2_struct_0(A_9)
      | ~ l3_lattices(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_290,plain,(
    ! [A_188,B_189] :
      ( k1_lattices(A_188,B_189,B_189) = B_189
      | ~ m1_subset_1(B_189,u1_struct_0(A_188))
      | ~ l3_lattices(A_188)
      | ~ v9_lattices(A_188)
      | ~ v8_lattices(A_188)
      | ~ v6_lattices(A_188)
      | v2_struct_0(A_188) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_306,plain,
    ( k1_lattices('#skF_10','#skF_11','#skF_11') = '#skF_11'
    | ~ l3_lattices('#skF_10')
    | ~ v9_lattices('#skF_10')
    | ~ v8_lattices('#skF_10')
    | ~ v6_lattices('#skF_10')
    | v2_struct_0('#skF_10') ),
    inference(resolution,[status(thm)],[c_98,c_290])).

tff(c_316,plain,
    ( k1_lattices('#skF_10','#skF_11','#skF_11') = '#skF_11'
    | ~ v9_lattices('#skF_10')
    | ~ v8_lattices('#skF_10')
    | ~ v6_lattices('#skF_10')
    | v2_struct_0('#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_306])).

tff(c_317,plain,
    ( k1_lattices('#skF_10','#skF_11','#skF_11') = '#skF_11'
    | ~ v9_lattices('#skF_10')
    | ~ v8_lattices('#skF_10')
    | ~ v6_lattices('#skF_10') ),
    inference(negUnitSimplification,[status(thm)],[c_106,c_316])).

tff(c_318,plain,(
    ~ v6_lattices('#skF_10') ),
    inference(splitLeft,[status(thm)],[c_317])).

tff(c_321,plain,
    ( ~ v10_lattices('#skF_10')
    | v2_struct_0('#skF_10')
    | ~ l3_lattices('#skF_10') ),
    inference(resolution,[status(thm)],[c_24,c_318])).

tff(c_324,plain,(
    v2_struct_0('#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_104,c_321])).

tff(c_326,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_106,c_324])).

tff(c_328,plain,(
    v6_lattices('#skF_10') ),
    inference(splitRight,[status(thm)],[c_317])).

tff(c_374,plain,(
    ! [A_211,C_212,B_213] :
      ( k2_lattices(A_211,C_212,B_213) = k2_lattices(A_211,B_213,C_212)
      | ~ m1_subset_1(C_212,u1_struct_0(A_211))
      | ~ m1_subset_1(B_213,u1_struct_0(A_211))
      | ~ v6_lattices(A_211)
      | ~ l1_lattices(A_211)
      | v2_struct_0(A_211) ) ),
    inference(cnfTransformation,[status(thm)],[f_264])).

tff(c_390,plain,(
    ! [B_213] :
      ( k2_lattices('#skF_10',B_213,'#skF_11') = k2_lattices('#skF_10','#skF_11',B_213)
      | ~ m1_subset_1(B_213,u1_struct_0('#skF_10'))
      | ~ v6_lattices('#skF_10')
      | ~ l1_lattices('#skF_10')
      | v2_struct_0('#skF_10') ) ),
    inference(resolution,[status(thm)],[c_98,c_374])).

tff(c_400,plain,(
    ! [B_213] :
      ( k2_lattices('#skF_10',B_213,'#skF_11') = k2_lattices('#skF_10','#skF_11',B_213)
      | ~ m1_subset_1(B_213,u1_struct_0('#skF_10'))
      | v2_struct_0('#skF_10') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_111,c_328,c_390])).

tff(c_402,plain,(
    ! [B_214] :
      ( k2_lattices('#skF_10',B_214,'#skF_11') = k2_lattices('#skF_10','#skF_11',B_214)
      | ~ m1_subset_1(B_214,u1_struct_0('#skF_10')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_106,c_400])).

tff(c_430,plain,(
    ! [B_126] :
      ( k2_lattices('#skF_10',k15_lattice3('#skF_10',B_126),'#skF_11') = k2_lattices('#skF_10','#skF_11',k15_lattice3('#skF_10',B_126))
      | ~ l3_lattices('#skF_10')
      | v2_struct_0('#skF_10') ) ),
    inference(resolution,[status(thm)],[c_92,c_402])).

tff(c_460,plain,(
    ! [B_126] :
      ( k2_lattices('#skF_10',k15_lattice3('#skF_10',B_126),'#skF_11') = k2_lattices('#skF_10','#skF_11',k15_lattice3('#skF_10',B_126))
      | v2_struct_0('#skF_10') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_430])).

tff(c_461,plain,(
    ! [B_126] : k2_lattices('#skF_10',k15_lattice3('#skF_10',B_126),'#skF_11') = k2_lattices('#skF_10','#skF_11',k15_lattice3('#skF_10',B_126)) ),
    inference(negUnitSimplification,[status(thm)],[c_106,c_460])).

tff(c_20,plain,(
    ! [A_9] :
      ( v8_lattices(A_9)
      | ~ v10_lattices(A_9)
      | v2_struct_0(A_9)
      | ~ l3_lattices(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_18,plain,(
    ! [A_9] :
      ( v9_lattices(A_9)
      | ~ v10_lattices(A_9)
      | v2_struct_0(A_9)
      | ~ l3_lattices(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_327,plain,
    ( ~ v8_lattices('#skF_10')
    | ~ v9_lattices('#skF_10')
    | k1_lattices('#skF_10','#skF_11','#skF_11') = '#skF_11' ),
    inference(splitRight,[status(thm)],[c_317])).

tff(c_329,plain,(
    ~ v9_lattices('#skF_10') ),
    inference(splitLeft,[status(thm)],[c_327])).

tff(c_333,plain,
    ( ~ v10_lattices('#skF_10')
    | v2_struct_0('#skF_10')
    | ~ l3_lattices('#skF_10') ),
    inference(resolution,[status(thm)],[c_18,c_329])).

tff(c_336,plain,(
    v2_struct_0('#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_104,c_333])).

tff(c_338,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_106,c_336])).

tff(c_339,plain,
    ( ~ v8_lattices('#skF_10')
    | k1_lattices('#skF_10','#skF_11','#skF_11') = '#skF_11' ),
    inference(splitRight,[status(thm)],[c_327])).

tff(c_341,plain,(
    ~ v8_lattices('#skF_10') ),
    inference(splitLeft,[status(thm)],[c_339])).

tff(c_344,plain,
    ( ~ v10_lattices('#skF_10')
    | v2_struct_0('#skF_10')
    | ~ l3_lattices('#skF_10') ),
    inference(resolution,[status(thm)],[c_20,c_341])).

tff(c_347,plain,(
    v2_struct_0('#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_104,c_344])).

tff(c_349,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_106,c_347])).

tff(c_351,plain,(
    v8_lattices('#skF_10') ),
    inference(splitRight,[status(thm)],[c_339])).

tff(c_340,plain,(
    v9_lattices('#skF_10') ),
    inference(splitRight,[status(thm)],[c_327])).

tff(c_6741,plain,(
    ! [A_559,B_560,C_561] :
      ( r1_lattices(A_559,B_560,C_561)
      | k2_lattices(A_559,B_560,C_561) != B_560
      | ~ m1_subset_1(C_561,u1_struct_0(A_559))
      | ~ m1_subset_1(B_560,u1_struct_0(A_559))
      | ~ l3_lattices(A_559)
      | ~ v9_lattices(A_559)
      | ~ v8_lattices(A_559)
      | v2_struct_0(A_559) ) ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_6757,plain,(
    ! [B_560] :
      ( r1_lattices('#skF_10',B_560,'#skF_11')
      | k2_lattices('#skF_10',B_560,'#skF_11') != B_560
      | ~ m1_subset_1(B_560,u1_struct_0('#skF_10'))
      | ~ l3_lattices('#skF_10')
      | ~ v9_lattices('#skF_10')
      | ~ v8_lattices('#skF_10')
      | v2_struct_0('#skF_10') ) ),
    inference(resolution,[status(thm)],[c_98,c_6741])).

tff(c_6767,plain,(
    ! [B_560] :
      ( r1_lattices('#skF_10',B_560,'#skF_11')
      | k2_lattices('#skF_10',B_560,'#skF_11') != B_560
      | ~ m1_subset_1(B_560,u1_struct_0('#skF_10'))
      | v2_struct_0('#skF_10') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_351,c_340,c_100,c_6757])).

tff(c_6769,plain,(
    ! [B_562] :
      ( r1_lattices('#skF_10',B_562,'#skF_11')
      | k2_lattices('#skF_10',B_562,'#skF_11') != B_562
      | ~ m1_subset_1(B_562,u1_struct_0('#skF_10')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_106,c_6767])).

tff(c_6797,plain,(
    ! [B_126] :
      ( r1_lattices('#skF_10',k15_lattice3('#skF_10',B_126),'#skF_11')
      | k2_lattices('#skF_10',k15_lattice3('#skF_10',B_126),'#skF_11') != k15_lattice3('#skF_10',B_126)
      | ~ l3_lattices('#skF_10')
      | v2_struct_0('#skF_10') ) ),
    inference(resolution,[status(thm)],[c_92,c_6769])).

tff(c_6827,plain,(
    ! [B_126] :
      ( r1_lattices('#skF_10',k15_lattice3('#skF_10',B_126),'#skF_11')
      | k2_lattices('#skF_10','#skF_11',k15_lattice3('#skF_10',B_126)) != k15_lattice3('#skF_10',B_126)
      | v2_struct_0('#skF_10') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_461,c_6797])).

tff(c_6832,plain,(
    ! [B_563] :
      ( r1_lattices('#skF_10',k15_lattice3('#skF_10',B_563),'#skF_11')
      | k2_lattices('#skF_10','#skF_11',k15_lattice3('#skF_10',B_563)) != k15_lattice3('#skF_10',B_563) ) ),
    inference(negUnitSimplification,[status(thm)],[c_106,c_6827])).

tff(c_54,plain,(
    ! [C_42,B_40,A_36] :
      ( C_42 = B_40
      | ~ r1_lattices(A_36,C_42,B_40)
      | ~ r1_lattices(A_36,B_40,C_42)
      | ~ m1_subset_1(C_42,u1_struct_0(A_36))
      | ~ m1_subset_1(B_40,u1_struct_0(A_36))
      | ~ l2_lattices(A_36)
      | ~ v4_lattices(A_36)
      | v2_struct_0(A_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_6834,plain,(
    ! [B_563] :
      ( k15_lattice3('#skF_10',B_563) = '#skF_11'
      | ~ r1_lattices('#skF_10','#skF_11',k15_lattice3('#skF_10',B_563))
      | ~ m1_subset_1(k15_lattice3('#skF_10',B_563),u1_struct_0('#skF_10'))
      | ~ m1_subset_1('#skF_11',u1_struct_0('#skF_10'))
      | ~ l2_lattices('#skF_10')
      | ~ v4_lattices('#skF_10')
      | v2_struct_0('#skF_10')
      | k2_lattices('#skF_10','#skF_11',k15_lattice3('#skF_10',B_563)) != k15_lattice3('#skF_10',B_563) ) ),
    inference(resolution,[status(thm)],[c_6832,c_54])).

tff(c_6837,plain,(
    ! [B_563] :
      ( k15_lattice3('#skF_10',B_563) = '#skF_11'
      | ~ r1_lattices('#skF_10','#skF_11',k15_lattice3('#skF_10',B_563))
      | ~ m1_subset_1(k15_lattice3('#skF_10',B_563),u1_struct_0('#skF_10'))
      | ~ v4_lattices('#skF_10')
      | v2_struct_0('#skF_10')
      | k2_lattices('#skF_10','#skF_11',k15_lattice3('#skF_10',B_563)) != k15_lattice3('#skF_10',B_563) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_118,c_98,c_6834])).

tff(c_6838,plain,(
    ! [B_563] :
      ( k15_lattice3('#skF_10',B_563) = '#skF_11'
      | ~ r1_lattices('#skF_10','#skF_11',k15_lattice3('#skF_10',B_563))
      | ~ m1_subset_1(k15_lattice3('#skF_10',B_563),u1_struct_0('#skF_10'))
      | ~ v4_lattices('#skF_10')
      | k2_lattices('#skF_10','#skF_11',k15_lattice3('#skF_10',B_563)) != k15_lattice3('#skF_10',B_563) ) ),
    inference(negUnitSimplification,[status(thm)],[c_106,c_6837])).

tff(c_9319,plain,(
    ~ v4_lattices('#skF_10') ),
    inference(splitLeft,[status(thm)],[c_6838])).

tff(c_9322,plain,
    ( ~ v10_lattices('#skF_10')
    | v2_struct_0('#skF_10')
    | ~ l3_lattices('#skF_10') ),
    inference(resolution,[status(thm)],[c_28,c_9319])).

tff(c_9325,plain,(
    v2_struct_0('#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_104,c_9322])).

tff(c_9327,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_106,c_9325])).

tff(c_9330,plain,(
    ! [B_705] :
      ( k15_lattice3('#skF_10',B_705) = '#skF_11'
      | ~ r1_lattices('#skF_10','#skF_11',k15_lattice3('#skF_10',B_705))
      | ~ m1_subset_1(k15_lattice3('#skF_10',B_705),u1_struct_0('#skF_10'))
      | k2_lattices('#skF_10','#skF_11',k15_lattice3('#skF_10',B_705)) != k15_lattice3('#skF_10',B_705) ) ),
    inference(splitRight,[status(thm)],[c_6838])).

tff(c_9334,plain,(
    ! [B_126] :
      ( k15_lattice3('#skF_10',B_126) = '#skF_11'
      | ~ r1_lattices('#skF_10','#skF_11',k15_lattice3('#skF_10',B_126))
      | k2_lattices('#skF_10','#skF_11',k15_lattice3('#skF_10',B_126)) != k15_lattice3('#skF_10',B_126)
      | ~ l3_lattices('#skF_10')
      | v2_struct_0('#skF_10') ) ),
    inference(resolution,[status(thm)],[c_92,c_9330])).

tff(c_9337,plain,(
    ! [B_126] :
      ( k15_lattice3('#skF_10',B_126) = '#skF_11'
      | ~ r1_lattices('#skF_10','#skF_11',k15_lattice3('#skF_10',B_126))
      | k2_lattices('#skF_10','#skF_11',k15_lattice3('#skF_10',B_126)) != k15_lattice3('#skF_10',B_126)
      | v2_struct_0('#skF_10') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_9334])).

tff(c_9339,plain,(
    ! [B_706] :
      ( k15_lattice3('#skF_10',B_706) = '#skF_11'
      | ~ r1_lattices('#skF_10','#skF_11',k15_lattice3('#skF_10',B_706))
      | k2_lattices('#skF_10','#skF_11',k15_lattice3('#skF_10',B_706)) != k15_lattice3('#skF_10',B_706) ) ),
    inference(negUnitSimplification,[status(thm)],[c_106,c_9337])).

tff(c_9343,plain,
    ( k15_lattice3('#skF_10',k1_tarski('#skF_11')) = '#skF_11'
    | k2_lattices('#skF_10','#skF_11',k15_lattice3('#skF_10',k1_tarski('#skF_11'))) != k15_lattice3('#skF_10',k1_tarski('#skF_11'))
    | ~ m1_subset_1('#skF_11',u1_struct_0('#skF_10'))
    | ~ v4_lattice3('#skF_10')
    | ~ v10_lattices('#skF_10')
    | ~ l3_lattices('#skF_10')
    | v2_struct_0('#skF_10') ),
    inference(resolution,[status(thm)],[c_8504,c_9339])).

tff(c_9350,plain,
    ( k15_lattice3('#skF_10',k1_tarski('#skF_11')) = '#skF_11'
    | k2_lattices('#skF_10','#skF_11',k15_lattice3('#skF_10',k1_tarski('#skF_11'))) != k15_lattice3('#skF_10',k1_tarski('#skF_11'))
    | v2_struct_0('#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_104,c_102,c_98,c_9343])).

tff(c_9351,plain,(
    k2_lattices('#skF_10','#skF_11',k15_lattice3('#skF_10',k1_tarski('#skF_11'))) != k15_lattice3('#skF_10',k1_tarski('#skF_11')) ),
    inference(negUnitSimplification,[status(thm)],[c_106,c_158,c_9350])).

tff(c_8505,plain,(
    ! [A_668,C_669] :
      ( r1_lattices(A_668,C_669,k15_lattice3(A_668,k1_tarski(C_669)))
      | ~ m1_subset_1(C_669,u1_struct_0(A_668))
      | ~ v4_lattice3(A_668)
      | ~ v10_lattices(A_668)
      | ~ l3_lattices(A_668)
      | v2_struct_0(A_668) ) ),
    inference(resolution,[status(thm)],[c_92,c_8500])).

tff(c_52,plain,(
    ! [A_29,B_33,C_35] :
      ( k2_lattices(A_29,B_33,C_35) = B_33
      | ~ r1_lattices(A_29,B_33,C_35)
      | ~ m1_subset_1(C_35,u1_struct_0(A_29))
      | ~ m1_subset_1(B_33,u1_struct_0(A_29))
      | ~ l3_lattices(A_29)
      | ~ v9_lattices(A_29)
      | ~ v8_lattices(A_29)
      | v2_struct_0(A_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_10524,plain,(
    ! [A_757,C_758] :
      ( k2_lattices(A_757,C_758,k15_lattice3(A_757,k1_tarski(C_758))) = C_758
      | ~ m1_subset_1(k15_lattice3(A_757,k1_tarski(C_758)),u1_struct_0(A_757))
      | ~ v9_lattices(A_757)
      | ~ v8_lattices(A_757)
      | ~ m1_subset_1(C_758,u1_struct_0(A_757))
      | ~ v4_lattice3(A_757)
      | ~ v10_lattices(A_757)
      | ~ l3_lattices(A_757)
      | v2_struct_0(A_757) ) ),
    inference(resolution,[status(thm)],[c_8505,c_52])).

tff(c_10533,plain,(
    ! [A_759,C_760] :
      ( k2_lattices(A_759,C_760,k15_lattice3(A_759,k1_tarski(C_760))) = C_760
      | ~ v9_lattices(A_759)
      | ~ v8_lattices(A_759)
      | ~ m1_subset_1(C_760,u1_struct_0(A_759))
      | ~ v4_lattice3(A_759)
      | ~ v10_lattices(A_759)
      | ~ l3_lattices(A_759)
      | v2_struct_0(A_759) ) ),
    inference(resolution,[status(thm)],[c_92,c_10524])).

tff(c_22,plain,(
    ! [A_9] :
      ( v7_lattices(A_9)
      | ~ v10_lattices(A_9)
      | v2_struct_0(A_9)
      | ~ l3_lattices(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_350,plain,(
    k1_lattices('#skF_10','#skF_11','#skF_11') = '#skF_11' ),
    inference(splitRight,[status(thm)],[c_339])).

tff(c_473,plain,(
    ! [A_216,B_217,C_218] :
      ( k2_lattices(A_216,B_217,k1_lattices(A_216,B_217,C_218)) = B_217
      | ~ m1_subset_1(C_218,u1_struct_0(A_216))
      | ~ m1_subset_1(B_217,u1_struct_0(A_216))
      | ~ v9_lattices(A_216)
      | ~ l3_lattices(A_216)
      | v2_struct_0(A_216) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_489,plain,(
    ! [B_217] :
      ( k2_lattices('#skF_10',B_217,k1_lattices('#skF_10',B_217,'#skF_11')) = B_217
      | ~ m1_subset_1(B_217,u1_struct_0('#skF_10'))
      | ~ v9_lattices('#skF_10')
      | ~ l3_lattices('#skF_10')
      | v2_struct_0('#skF_10') ) ),
    inference(resolution,[status(thm)],[c_98,c_473])).

tff(c_499,plain,(
    ! [B_217] :
      ( k2_lattices('#skF_10',B_217,k1_lattices('#skF_10',B_217,'#skF_11')) = B_217
      | ~ m1_subset_1(B_217,u1_struct_0('#skF_10'))
      | v2_struct_0('#skF_10') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_340,c_489])).

tff(c_501,plain,(
    ! [B_219] :
      ( k2_lattices('#skF_10',B_219,k1_lattices('#skF_10',B_219,'#skF_11')) = B_219
      | ~ m1_subset_1(B_219,u1_struct_0('#skF_10')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_106,c_499])).

tff(c_524,plain,(
    k2_lattices('#skF_10','#skF_11',k1_lattices('#skF_10','#skF_11','#skF_11')) = '#skF_11' ),
    inference(resolution,[status(thm)],[c_98,c_501])).

tff(c_554,plain,(
    k2_lattices('#skF_10','#skF_11','#skF_11') = '#skF_11' ),
    inference(demodulation,[status(thm),theory(equality)],[c_350,c_524])).

tff(c_8581,plain,(
    ! [A_673,B_674,D_675,C_676] :
      ( r1_lattices(A_673,k2_lattices(A_673,B_674,D_675),k2_lattices(A_673,C_676,D_675))
      | ~ r1_lattices(A_673,B_674,C_676)
      | ~ m1_subset_1(D_675,u1_struct_0(A_673))
      | ~ m1_subset_1(C_676,u1_struct_0(A_673))
      | ~ m1_subset_1(B_674,u1_struct_0(A_673))
      | ~ l3_lattices(A_673)
      | ~ v9_lattices(A_673)
      | ~ v8_lattices(A_673)
      | ~ v7_lattices(A_673)
      | v2_struct_0(A_673) ) ),
    inference(cnfTransformation,[status(thm)],[f_185])).

tff(c_8708,plain,(
    ! [C_676] :
      ( r1_lattices('#skF_10','#skF_11',k2_lattices('#skF_10',C_676,'#skF_11'))
      | ~ r1_lattices('#skF_10','#skF_11',C_676)
      | ~ m1_subset_1('#skF_11',u1_struct_0('#skF_10'))
      | ~ m1_subset_1(C_676,u1_struct_0('#skF_10'))
      | ~ m1_subset_1('#skF_11',u1_struct_0('#skF_10'))
      | ~ l3_lattices('#skF_10')
      | ~ v9_lattices('#skF_10')
      | ~ v8_lattices('#skF_10')
      | ~ v7_lattices('#skF_10')
      | v2_struct_0('#skF_10') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_554,c_8581])).

tff(c_8793,plain,(
    ! [C_676] :
      ( r1_lattices('#skF_10','#skF_11',k2_lattices('#skF_10',C_676,'#skF_11'))
      | ~ r1_lattices('#skF_10','#skF_11',C_676)
      | ~ m1_subset_1(C_676,u1_struct_0('#skF_10'))
      | ~ v7_lattices('#skF_10')
      | v2_struct_0('#skF_10') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_351,c_340,c_100,c_98,c_98,c_8708])).

tff(c_8794,plain,(
    ! [C_676] :
      ( r1_lattices('#skF_10','#skF_11',k2_lattices('#skF_10',C_676,'#skF_11'))
      | ~ r1_lattices('#skF_10','#skF_11',C_676)
      | ~ m1_subset_1(C_676,u1_struct_0('#skF_10'))
      | ~ v7_lattices('#skF_10') ) ),
    inference(negUnitSimplification,[status(thm)],[c_106,c_8793])).

tff(c_8804,plain,(
    ~ v7_lattices('#skF_10') ),
    inference(splitLeft,[status(thm)],[c_8794])).

tff(c_8807,plain,
    ( ~ v10_lattices('#skF_10')
    | v2_struct_0('#skF_10')
    | ~ l3_lattices('#skF_10') ),
    inference(resolution,[status(thm)],[c_22,c_8804])).

tff(c_8810,plain,(
    v2_struct_0('#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_104,c_8807])).

tff(c_8812,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_106,c_8810])).

tff(c_8814,plain,(
    v7_lattices('#skF_10') ),
    inference(splitRight,[status(thm)],[c_8794])).

tff(c_8714,plain,(
    ! [B_126,C_676] :
      ( r1_lattices('#skF_10',k2_lattices('#skF_10','#skF_11',k15_lattice3('#skF_10',B_126)),k2_lattices('#skF_10',C_676,'#skF_11'))
      | ~ r1_lattices('#skF_10',k15_lattice3('#skF_10',B_126),C_676)
      | ~ m1_subset_1('#skF_11',u1_struct_0('#skF_10'))
      | ~ m1_subset_1(C_676,u1_struct_0('#skF_10'))
      | ~ m1_subset_1(k15_lattice3('#skF_10',B_126),u1_struct_0('#skF_10'))
      | ~ l3_lattices('#skF_10')
      | ~ v9_lattices('#skF_10')
      | ~ v8_lattices('#skF_10')
      | ~ v7_lattices('#skF_10')
      | v2_struct_0('#skF_10') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_461,c_8581])).

tff(c_8799,plain,(
    ! [B_126,C_676] :
      ( r1_lattices('#skF_10',k2_lattices('#skF_10','#skF_11',k15_lattice3('#skF_10',B_126)),k2_lattices('#skF_10',C_676,'#skF_11'))
      | ~ r1_lattices('#skF_10',k15_lattice3('#skF_10',B_126),C_676)
      | ~ m1_subset_1(C_676,u1_struct_0('#skF_10'))
      | ~ m1_subset_1(k15_lattice3('#skF_10',B_126),u1_struct_0('#skF_10'))
      | ~ v7_lattices('#skF_10')
      | v2_struct_0('#skF_10') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_351,c_340,c_100,c_98,c_8714])).

tff(c_8800,plain,(
    ! [B_126,C_676] :
      ( r1_lattices('#skF_10',k2_lattices('#skF_10','#skF_11',k15_lattice3('#skF_10',B_126)),k2_lattices('#skF_10',C_676,'#skF_11'))
      | ~ r1_lattices('#skF_10',k15_lattice3('#skF_10',B_126),C_676)
      | ~ m1_subset_1(C_676,u1_struct_0('#skF_10'))
      | ~ m1_subset_1(k15_lattice3('#skF_10',B_126),u1_struct_0('#skF_10'))
      | ~ v7_lattices('#skF_10') ) ),
    inference(negUnitSimplification,[status(thm)],[c_106,c_8799])).

tff(c_10364,plain,(
    ! [B_126,C_676] :
      ( r1_lattices('#skF_10',k2_lattices('#skF_10','#skF_11',k15_lattice3('#skF_10',B_126)),k2_lattices('#skF_10',C_676,'#skF_11'))
      | ~ r1_lattices('#skF_10',k15_lattice3('#skF_10',B_126),C_676)
      | ~ m1_subset_1(C_676,u1_struct_0('#skF_10'))
      | ~ m1_subset_1(k15_lattice3('#skF_10',B_126),u1_struct_0('#skF_10')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8814,c_8800])).

tff(c_10540,plain,(
    ! [C_676] :
      ( r1_lattices('#skF_10','#skF_11',k2_lattices('#skF_10',C_676,'#skF_11'))
      | ~ r1_lattices('#skF_10',k15_lattice3('#skF_10',k1_tarski('#skF_11')),C_676)
      | ~ m1_subset_1(C_676,u1_struct_0('#skF_10'))
      | ~ m1_subset_1(k15_lattice3('#skF_10',k1_tarski('#skF_11')),u1_struct_0('#skF_10'))
      | ~ v9_lattices('#skF_10')
      | ~ v8_lattices('#skF_10')
      | ~ m1_subset_1('#skF_11',u1_struct_0('#skF_10'))
      | ~ v4_lattice3('#skF_10')
      | ~ v10_lattices('#skF_10')
      | ~ l3_lattices('#skF_10')
      | v2_struct_0('#skF_10') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10533,c_10364])).

tff(c_10577,plain,(
    ! [C_676] :
      ( r1_lattices('#skF_10','#skF_11',k2_lattices('#skF_10',C_676,'#skF_11'))
      | ~ r1_lattices('#skF_10',k15_lattice3('#skF_10',k1_tarski('#skF_11')),C_676)
      | ~ m1_subset_1(C_676,u1_struct_0('#skF_10'))
      | ~ m1_subset_1(k15_lattice3('#skF_10',k1_tarski('#skF_11')),u1_struct_0('#skF_10'))
      | v2_struct_0('#skF_10') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_104,c_102,c_98,c_351,c_340,c_10540])).

tff(c_10578,plain,(
    ! [C_676] :
      ( r1_lattices('#skF_10','#skF_11',k2_lattices('#skF_10',C_676,'#skF_11'))
      | ~ r1_lattices('#skF_10',k15_lattice3('#skF_10',k1_tarski('#skF_11')),C_676)
      | ~ m1_subset_1(C_676,u1_struct_0('#skF_10'))
      | ~ m1_subset_1(k15_lattice3('#skF_10',k1_tarski('#skF_11')),u1_struct_0('#skF_10')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_106,c_10577])).

tff(c_10595,plain,(
    ~ m1_subset_1(k15_lattice3('#skF_10',k1_tarski('#skF_11')),u1_struct_0('#skF_10')) ),
    inference(splitLeft,[status(thm)],[c_10578])).

tff(c_10599,plain,
    ( ~ l3_lattices('#skF_10')
    | v2_struct_0('#skF_10') ),
    inference(resolution,[status(thm)],[c_92,c_10595])).

tff(c_10602,plain,(
    v2_struct_0('#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_10599])).

tff(c_10604,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_106,c_10602])).

tff(c_10606,plain,(
    m1_subset_1(k15_lattice3('#skF_10',k1_tarski('#skF_11')),u1_struct_0('#skF_10')) ),
    inference(splitRight,[status(thm)],[c_10578])).

tff(c_273,plain,(
    ! [A_178,B_179,C_180] :
      ( r2_hidden('#skF_6'(A_178,B_179,C_180),C_180)
      | r4_lattice3(A_178,B_179,C_180)
      | ~ m1_subset_1(B_179,u1_struct_0(A_178))
      | ~ l3_lattices(A_178)
      | v2_struct_0(A_178) ) ),
    inference(cnfTransformation,[status(thm)],[f_221])).

tff(c_2,plain,(
    ! [C_5,A_1] :
      ( C_5 = A_1
      | ~ r2_hidden(C_5,k1_tarski(A_1)) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_278,plain,(
    ! [A_178,B_179,A_1] :
      ( '#skF_6'(A_178,B_179,k1_tarski(A_1)) = A_1
      | r4_lattice3(A_178,B_179,k1_tarski(A_1))
      | ~ m1_subset_1(B_179,u1_struct_0(A_178))
      | ~ l3_lattices(A_178)
      | v2_struct_0(A_178) ) ),
    inference(resolution,[status(thm)],[c_273,c_2])).

tff(c_961,plain,(
    ! [A_251,A_252,B_253] :
      ( r1_lattices(A_251,A_252,B_253)
      | ~ m1_subset_1(A_252,u1_struct_0(A_251))
      | '#skF_6'(A_251,B_253,k1_tarski(A_252)) = A_252
      | ~ m1_subset_1(B_253,u1_struct_0(A_251))
      | ~ l3_lattices(A_251)
      | v2_struct_0(A_251) ) ),
    inference(resolution,[status(thm)],[c_278,c_951])).

tff(c_977,plain,(
    ! [B_253] :
      ( r1_lattices('#skF_10','#skF_11',B_253)
      | '#skF_6'('#skF_10',B_253,k1_tarski('#skF_11')) = '#skF_11'
      | ~ m1_subset_1(B_253,u1_struct_0('#skF_10'))
      | ~ l3_lattices('#skF_10')
      | v2_struct_0('#skF_10') ) ),
    inference(resolution,[status(thm)],[c_98,c_961])).

tff(c_987,plain,(
    ! [B_253] :
      ( r1_lattices('#skF_10','#skF_11',B_253)
      | '#skF_6'('#skF_10',B_253,k1_tarski('#skF_11')) = '#skF_11'
      | ~ m1_subset_1(B_253,u1_struct_0('#skF_10'))
      | v2_struct_0('#skF_10') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_977])).

tff(c_989,plain,(
    ! [B_254] :
      ( r1_lattices('#skF_10','#skF_11',B_254)
      | '#skF_6'('#skF_10',B_254,k1_tarski('#skF_11')) = '#skF_11'
      | ~ m1_subset_1(B_254,u1_struct_0('#skF_10')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_106,c_987])).

tff(c_1049,plain,
    ( r1_lattices('#skF_10','#skF_11','#skF_11')
    | '#skF_6'('#skF_10','#skF_11',k1_tarski('#skF_11')) = '#skF_11' ),
    inference(resolution,[status(thm)],[c_98,c_989])).

tff(c_1050,plain,(
    '#skF_6'('#skF_10','#skF_11',k1_tarski('#skF_11')) = '#skF_11' ),
    inference(splitLeft,[status(thm)],[c_1049])).

tff(c_68,plain,(
    ! [A_80,B_92,C_98] :
      ( ~ r1_lattices(A_80,'#skF_6'(A_80,B_92,C_98),B_92)
      | r4_lattice3(A_80,B_92,C_98)
      | ~ m1_subset_1(B_92,u1_struct_0(A_80))
      | ~ l3_lattices(A_80)
      | v2_struct_0(A_80) ) ),
    inference(cnfTransformation,[status(thm)],[f_221])).

tff(c_1076,plain,
    ( ~ r1_lattices('#skF_10','#skF_11','#skF_11')
    | r4_lattice3('#skF_10','#skF_11',k1_tarski('#skF_11'))
    | ~ m1_subset_1('#skF_11',u1_struct_0('#skF_10'))
    | ~ l3_lattices('#skF_10')
    | v2_struct_0('#skF_10') ),
    inference(superposition,[status(thm),theory(equality)],[c_1050,c_68])).

tff(c_1088,plain,
    ( ~ r1_lattices('#skF_10','#skF_11','#skF_11')
    | r4_lattice3('#skF_10','#skF_11',k1_tarski('#skF_11'))
    | v2_struct_0('#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_98,c_1076])).

tff(c_1089,plain,
    ( ~ r1_lattices('#skF_10','#skF_11','#skF_11')
    | r4_lattice3('#skF_10','#skF_11',k1_tarski('#skF_11')) ),
    inference(negUnitSimplification,[status(thm)],[c_106,c_1088])).

tff(c_1097,plain,(
    ~ r1_lattices('#skF_10','#skF_11','#skF_11') ),
    inference(splitLeft,[status(thm)],[c_1089])).

tff(c_1493,plain,(
    ! [A_288,B_289,C_290] :
      ( r1_lattices(A_288,B_289,C_290)
      | k2_lattices(A_288,B_289,C_290) != B_289
      | ~ m1_subset_1(C_290,u1_struct_0(A_288))
      | ~ m1_subset_1(B_289,u1_struct_0(A_288))
      | ~ l3_lattices(A_288)
      | ~ v9_lattices(A_288)
      | ~ v8_lattices(A_288)
      | v2_struct_0(A_288) ) ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_1509,plain,(
    ! [B_289] :
      ( r1_lattices('#skF_10',B_289,'#skF_11')
      | k2_lattices('#skF_10',B_289,'#skF_11') != B_289
      | ~ m1_subset_1(B_289,u1_struct_0('#skF_10'))
      | ~ l3_lattices('#skF_10')
      | ~ v9_lattices('#skF_10')
      | ~ v8_lattices('#skF_10')
      | v2_struct_0('#skF_10') ) ),
    inference(resolution,[status(thm)],[c_98,c_1493])).

tff(c_1519,plain,(
    ! [B_289] :
      ( r1_lattices('#skF_10',B_289,'#skF_11')
      | k2_lattices('#skF_10',B_289,'#skF_11') != B_289
      | ~ m1_subset_1(B_289,u1_struct_0('#skF_10'))
      | v2_struct_0('#skF_10') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_351,c_340,c_100,c_1509])).

tff(c_1521,plain,(
    ! [B_291] :
      ( r1_lattices('#skF_10',B_291,'#skF_11')
      | k2_lattices('#skF_10',B_291,'#skF_11') != B_291
      | ~ m1_subset_1(B_291,u1_struct_0('#skF_10')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_106,c_1519])).

tff(c_1552,plain,
    ( r1_lattices('#skF_10','#skF_11','#skF_11')
    | k2_lattices('#skF_10','#skF_11','#skF_11') != '#skF_11' ),
    inference(resolution,[status(thm)],[c_98,c_1521])).

tff(c_1583,plain,(
    r1_lattices('#skF_10','#skF_11','#skF_11') ),
    inference(demodulation,[status(thm),theory(equality)],[c_554,c_1552])).

tff(c_1585,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1097,c_1583])).

tff(c_1586,plain,(
    r4_lattice3('#skF_10','#skF_11',k1_tarski('#skF_11')) ),
    inference(splitRight,[status(thm)],[c_1089])).

tff(c_3662,plain,(
    ! [A_418,B_419,D_420] :
      ( r1_lattices(A_418,k15_lattice3(A_418,B_419),D_420)
      | ~ r4_lattice3(A_418,D_420,B_419)
      | ~ m1_subset_1(D_420,u1_struct_0(A_418))
      | ~ m1_subset_1(k15_lattice3(A_418,B_419),u1_struct_0(A_418))
      | ~ v4_lattice3(A_418)
      | ~ v10_lattices(A_418)
      | ~ l3_lattices(A_418)
      | v2_struct_0(A_418) ) ),
    inference(cnfTransformation,[status(thm)],[f_249])).

tff(c_3665,plain,(
    ! [A_125,B_126,D_420] :
      ( r1_lattices(A_125,k15_lattice3(A_125,B_126),D_420)
      | ~ r4_lattice3(A_125,D_420,B_126)
      | ~ m1_subset_1(D_420,u1_struct_0(A_125))
      | ~ v4_lattice3(A_125)
      | ~ v10_lattices(A_125)
      | ~ l3_lattices(A_125)
      | v2_struct_0(A_125) ) ),
    inference(resolution,[status(thm)],[c_92,c_3662])).

tff(c_1975,plain,(
    ! [A_322,B_323,C_324] :
      ( r1_lattices(A_322,B_323,C_324)
      | k2_lattices(A_322,B_323,C_324) != B_323
      | ~ m1_subset_1(C_324,u1_struct_0(A_322))
      | ~ m1_subset_1(B_323,u1_struct_0(A_322))
      | ~ l3_lattices(A_322)
      | ~ v9_lattices(A_322)
      | ~ v8_lattices(A_322)
      | v2_struct_0(A_322) ) ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_1991,plain,(
    ! [B_323] :
      ( r1_lattices('#skF_10',B_323,'#skF_11')
      | k2_lattices('#skF_10',B_323,'#skF_11') != B_323
      | ~ m1_subset_1(B_323,u1_struct_0('#skF_10'))
      | ~ l3_lattices('#skF_10')
      | ~ v9_lattices('#skF_10')
      | ~ v8_lattices('#skF_10')
      | v2_struct_0('#skF_10') ) ),
    inference(resolution,[status(thm)],[c_98,c_1975])).

tff(c_2001,plain,(
    ! [B_323] :
      ( r1_lattices('#skF_10',B_323,'#skF_11')
      | k2_lattices('#skF_10',B_323,'#skF_11') != B_323
      | ~ m1_subset_1(B_323,u1_struct_0('#skF_10'))
      | v2_struct_0('#skF_10') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_351,c_340,c_100,c_1991])).

tff(c_2003,plain,(
    ! [B_325] :
      ( r1_lattices('#skF_10',B_325,'#skF_11')
      | k2_lattices('#skF_10',B_325,'#skF_11') != B_325
      | ~ m1_subset_1(B_325,u1_struct_0('#skF_10')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_106,c_2001])).

tff(c_2031,plain,(
    ! [B_126] :
      ( r1_lattices('#skF_10',k15_lattice3('#skF_10',B_126),'#skF_11')
      | k2_lattices('#skF_10',k15_lattice3('#skF_10',B_126),'#skF_11') != k15_lattice3('#skF_10',B_126)
      | ~ l3_lattices('#skF_10')
      | v2_struct_0('#skF_10') ) ),
    inference(resolution,[status(thm)],[c_92,c_2003])).

tff(c_2061,plain,(
    ! [B_126] :
      ( r1_lattices('#skF_10',k15_lattice3('#skF_10',B_126),'#skF_11')
      | k2_lattices('#skF_10','#skF_11',k15_lattice3('#skF_10',B_126)) != k15_lattice3('#skF_10',B_126)
      | v2_struct_0('#skF_10') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_461,c_2031])).

tff(c_2066,plain,(
    ! [B_326] :
      ( r1_lattices('#skF_10',k15_lattice3('#skF_10',B_326),'#skF_11')
      | k2_lattices('#skF_10','#skF_11',k15_lattice3('#skF_10',B_326)) != k15_lattice3('#skF_10',B_326) ) ),
    inference(negUnitSimplification,[status(thm)],[c_106,c_2061])).

tff(c_2068,plain,(
    ! [B_326] :
      ( k15_lattice3('#skF_10',B_326) = '#skF_11'
      | ~ r1_lattices('#skF_10','#skF_11',k15_lattice3('#skF_10',B_326))
      | ~ m1_subset_1(k15_lattice3('#skF_10',B_326),u1_struct_0('#skF_10'))
      | ~ m1_subset_1('#skF_11',u1_struct_0('#skF_10'))
      | ~ l2_lattices('#skF_10')
      | ~ v4_lattices('#skF_10')
      | v2_struct_0('#skF_10')
      | k2_lattices('#skF_10','#skF_11',k15_lattice3('#skF_10',B_326)) != k15_lattice3('#skF_10',B_326) ) ),
    inference(resolution,[status(thm)],[c_2066,c_54])).

tff(c_2071,plain,(
    ! [B_326] :
      ( k15_lattice3('#skF_10',B_326) = '#skF_11'
      | ~ r1_lattices('#skF_10','#skF_11',k15_lattice3('#skF_10',B_326))
      | ~ m1_subset_1(k15_lattice3('#skF_10',B_326),u1_struct_0('#skF_10'))
      | ~ v4_lattices('#skF_10')
      | v2_struct_0('#skF_10')
      | k2_lattices('#skF_10','#skF_11',k15_lattice3('#skF_10',B_326)) != k15_lattice3('#skF_10',B_326) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_118,c_98,c_2068])).

tff(c_2072,plain,(
    ! [B_326] :
      ( k15_lattice3('#skF_10',B_326) = '#skF_11'
      | ~ r1_lattices('#skF_10','#skF_11',k15_lattice3('#skF_10',B_326))
      | ~ m1_subset_1(k15_lattice3('#skF_10',B_326),u1_struct_0('#skF_10'))
      | ~ v4_lattices('#skF_10')
      | k2_lattices('#skF_10','#skF_11',k15_lattice3('#skF_10',B_326)) != k15_lattice3('#skF_10',B_326) ) ),
    inference(negUnitSimplification,[status(thm)],[c_106,c_2071])).

tff(c_4332,plain,(
    ~ v4_lattices('#skF_10') ),
    inference(splitLeft,[status(thm)],[c_2072])).

tff(c_4335,plain,
    ( ~ v10_lattices('#skF_10')
    | v2_struct_0('#skF_10')
    | ~ l3_lattices('#skF_10') ),
    inference(resolution,[status(thm)],[c_28,c_4332])).

tff(c_4338,plain,(
    v2_struct_0('#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_104,c_4335])).

tff(c_4340,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_106,c_4338])).

tff(c_4342,plain,(
    v4_lattices('#skF_10') ),
    inference(splitRight,[status(thm)],[c_2072])).

tff(c_3821,plain,(
    ! [A_430,C_431] :
      ( r1_lattices(A_430,C_431,k15_lattice3(A_430,k1_tarski(C_431)))
      | ~ m1_subset_1(C_431,u1_struct_0(A_430))
      | ~ m1_subset_1(k15_lattice3(A_430,k1_tarski(C_431)),u1_struct_0(A_430))
      | ~ v4_lattice3(A_430)
      | ~ v10_lattices(A_430)
      | ~ l3_lattices(A_430)
      | v2_struct_0(A_430) ) ),
    inference(resolution,[status(thm)],[c_362,c_951])).

tff(c_3826,plain,(
    ! [A_432,C_433] :
      ( r1_lattices(A_432,C_433,k15_lattice3(A_432,k1_tarski(C_433)))
      | ~ m1_subset_1(C_433,u1_struct_0(A_432))
      | ~ v4_lattice3(A_432)
      | ~ v10_lattices(A_432)
      | ~ l3_lattices(A_432)
      | v2_struct_0(A_432) ) ),
    inference(resolution,[status(thm)],[c_92,c_3821])).

tff(c_5654,plain,(
    ! [A_513,C_514] :
      ( k2_lattices(A_513,C_514,k15_lattice3(A_513,k1_tarski(C_514))) = C_514
      | ~ m1_subset_1(k15_lattice3(A_513,k1_tarski(C_514)),u1_struct_0(A_513))
      | ~ v9_lattices(A_513)
      | ~ v8_lattices(A_513)
      | ~ m1_subset_1(C_514,u1_struct_0(A_513))
      | ~ v4_lattice3(A_513)
      | ~ v10_lattices(A_513)
      | ~ l3_lattices(A_513)
      | v2_struct_0(A_513) ) ),
    inference(resolution,[status(thm)],[c_3826,c_52])).

tff(c_5663,plain,(
    ! [A_515,C_516] :
      ( k2_lattices(A_515,C_516,k15_lattice3(A_515,k1_tarski(C_516))) = C_516
      | ~ v9_lattices(A_515)
      | ~ v8_lattices(A_515)
      | ~ m1_subset_1(C_516,u1_struct_0(A_515))
      | ~ v4_lattice3(A_515)
      | ~ v10_lattices(A_515)
      | ~ l3_lattices(A_515)
      | v2_struct_0(A_515) ) ),
    inference(resolution,[status(thm)],[c_92,c_5654])).

tff(c_3850,plain,(
    ! [A_436,B_437,D_438,C_439] :
      ( r1_lattices(A_436,k2_lattices(A_436,B_437,D_438),k2_lattices(A_436,C_439,D_438))
      | ~ r1_lattices(A_436,B_437,C_439)
      | ~ m1_subset_1(D_438,u1_struct_0(A_436))
      | ~ m1_subset_1(C_439,u1_struct_0(A_436))
      | ~ m1_subset_1(B_437,u1_struct_0(A_436))
      | ~ l3_lattices(A_436)
      | ~ v9_lattices(A_436)
      | ~ v8_lattices(A_436)
      | ~ v7_lattices(A_436)
      | v2_struct_0(A_436) ) ),
    inference(cnfTransformation,[status(thm)],[f_185])).

tff(c_3977,plain,(
    ! [C_439] :
      ( r1_lattices('#skF_10','#skF_11',k2_lattices('#skF_10',C_439,'#skF_11'))
      | ~ r1_lattices('#skF_10','#skF_11',C_439)
      | ~ m1_subset_1('#skF_11',u1_struct_0('#skF_10'))
      | ~ m1_subset_1(C_439,u1_struct_0('#skF_10'))
      | ~ m1_subset_1('#skF_11',u1_struct_0('#skF_10'))
      | ~ l3_lattices('#skF_10')
      | ~ v9_lattices('#skF_10')
      | ~ v8_lattices('#skF_10')
      | ~ v7_lattices('#skF_10')
      | v2_struct_0('#skF_10') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_554,c_3850])).

tff(c_4062,plain,(
    ! [C_439] :
      ( r1_lattices('#skF_10','#skF_11',k2_lattices('#skF_10',C_439,'#skF_11'))
      | ~ r1_lattices('#skF_10','#skF_11',C_439)
      | ~ m1_subset_1(C_439,u1_struct_0('#skF_10'))
      | ~ v7_lattices('#skF_10')
      | v2_struct_0('#skF_10') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_351,c_340,c_100,c_98,c_98,c_3977])).

tff(c_4063,plain,(
    ! [C_439] :
      ( r1_lattices('#skF_10','#skF_11',k2_lattices('#skF_10',C_439,'#skF_11'))
      | ~ r1_lattices('#skF_10','#skF_11',C_439)
      | ~ m1_subset_1(C_439,u1_struct_0('#skF_10'))
      | ~ v7_lattices('#skF_10') ) ),
    inference(negUnitSimplification,[status(thm)],[c_106,c_4062])).

tff(c_4073,plain,(
    ~ v7_lattices('#skF_10') ),
    inference(splitLeft,[status(thm)],[c_4063])).

tff(c_4076,plain,
    ( ~ v10_lattices('#skF_10')
    | v2_struct_0('#skF_10')
    | ~ l3_lattices('#skF_10') ),
    inference(resolution,[status(thm)],[c_22,c_4073])).

tff(c_4079,plain,(
    v2_struct_0('#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_104,c_4076])).

tff(c_4081,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_106,c_4079])).

tff(c_4083,plain,(
    v7_lattices('#skF_10') ),
    inference(splitRight,[status(thm)],[c_4063])).

tff(c_3986,plain,(
    ! [B_437,B_126] :
      ( r1_lattices('#skF_10',k2_lattices('#skF_10',B_437,'#skF_11'),k2_lattices('#skF_10','#skF_11',k15_lattice3('#skF_10',B_126)))
      | ~ r1_lattices('#skF_10',B_437,k15_lattice3('#skF_10',B_126))
      | ~ m1_subset_1('#skF_11',u1_struct_0('#skF_10'))
      | ~ m1_subset_1(k15_lattice3('#skF_10',B_126),u1_struct_0('#skF_10'))
      | ~ m1_subset_1(B_437,u1_struct_0('#skF_10'))
      | ~ l3_lattices('#skF_10')
      | ~ v9_lattices('#skF_10')
      | ~ v8_lattices('#skF_10')
      | ~ v7_lattices('#skF_10')
      | v2_struct_0('#skF_10') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_461,c_3850])).

tff(c_4071,plain,(
    ! [B_437,B_126] :
      ( r1_lattices('#skF_10',k2_lattices('#skF_10',B_437,'#skF_11'),k2_lattices('#skF_10','#skF_11',k15_lattice3('#skF_10',B_126)))
      | ~ r1_lattices('#skF_10',B_437,k15_lattice3('#skF_10',B_126))
      | ~ m1_subset_1(k15_lattice3('#skF_10',B_126),u1_struct_0('#skF_10'))
      | ~ m1_subset_1(B_437,u1_struct_0('#skF_10'))
      | ~ v7_lattices('#skF_10')
      | v2_struct_0('#skF_10') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_351,c_340,c_100,c_98,c_3986])).

tff(c_4072,plain,(
    ! [B_437,B_126] :
      ( r1_lattices('#skF_10',k2_lattices('#skF_10',B_437,'#skF_11'),k2_lattices('#skF_10','#skF_11',k15_lattice3('#skF_10',B_126)))
      | ~ r1_lattices('#skF_10',B_437,k15_lattice3('#skF_10',B_126))
      | ~ m1_subset_1(k15_lattice3('#skF_10',B_126),u1_struct_0('#skF_10'))
      | ~ m1_subset_1(B_437,u1_struct_0('#skF_10'))
      | ~ v7_lattices('#skF_10') ) ),
    inference(negUnitSimplification,[status(thm)],[c_106,c_4071])).

tff(c_5560,plain,(
    ! [B_437,B_126] :
      ( r1_lattices('#skF_10',k2_lattices('#skF_10',B_437,'#skF_11'),k2_lattices('#skF_10','#skF_11',k15_lattice3('#skF_10',B_126)))
      | ~ r1_lattices('#skF_10',B_437,k15_lattice3('#skF_10',B_126))
      | ~ m1_subset_1(k15_lattice3('#skF_10',B_126),u1_struct_0('#skF_10'))
      | ~ m1_subset_1(B_437,u1_struct_0('#skF_10')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4083,c_4072])).

tff(c_5670,plain,(
    ! [B_437] :
      ( r1_lattices('#skF_10',k2_lattices('#skF_10',B_437,'#skF_11'),'#skF_11')
      | ~ r1_lattices('#skF_10',B_437,k15_lattice3('#skF_10',k1_tarski('#skF_11')))
      | ~ m1_subset_1(k15_lattice3('#skF_10',k1_tarski('#skF_11')),u1_struct_0('#skF_10'))
      | ~ m1_subset_1(B_437,u1_struct_0('#skF_10'))
      | ~ v9_lattices('#skF_10')
      | ~ v8_lattices('#skF_10')
      | ~ m1_subset_1('#skF_11',u1_struct_0('#skF_10'))
      | ~ v4_lattice3('#skF_10')
      | ~ v10_lattices('#skF_10')
      | ~ l3_lattices('#skF_10')
      | v2_struct_0('#skF_10') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5663,c_5560])).

tff(c_5707,plain,(
    ! [B_437] :
      ( r1_lattices('#skF_10',k2_lattices('#skF_10',B_437,'#skF_11'),'#skF_11')
      | ~ r1_lattices('#skF_10',B_437,k15_lattice3('#skF_10',k1_tarski('#skF_11')))
      | ~ m1_subset_1(k15_lattice3('#skF_10',k1_tarski('#skF_11')),u1_struct_0('#skF_10'))
      | ~ m1_subset_1(B_437,u1_struct_0('#skF_10'))
      | v2_struct_0('#skF_10') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_104,c_102,c_98,c_351,c_340,c_5670])).

tff(c_5708,plain,(
    ! [B_437] :
      ( r1_lattices('#skF_10',k2_lattices('#skF_10',B_437,'#skF_11'),'#skF_11')
      | ~ r1_lattices('#skF_10',B_437,k15_lattice3('#skF_10',k1_tarski('#skF_11')))
      | ~ m1_subset_1(k15_lattice3('#skF_10',k1_tarski('#skF_11')),u1_struct_0('#skF_10'))
      | ~ m1_subset_1(B_437,u1_struct_0('#skF_10')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_106,c_5707])).

tff(c_5725,plain,(
    ~ m1_subset_1(k15_lattice3('#skF_10',k1_tarski('#skF_11')),u1_struct_0('#skF_10')) ),
    inference(splitLeft,[status(thm)],[c_5708])).

tff(c_5728,plain,
    ( ~ l3_lattices('#skF_10')
    | v2_struct_0('#skF_10') ),
    inference(resolution,[status(thm)],[c_92,c_5725])).

tff(c_5731,plain,(
    v2_struct_0('#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_5728])).

tff(c_5733,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_106,c_5731])).

tff(c_5735,plain,(
    m1_subset_1(k15_lattice3('#skF_10',k1_tarski('#skF_11')),u1_struct_0('#skF_10')) ),
    inference(splitRight,[status(thm)],[c_5708])).

tff(c_3825,plain,(
    ! [A_125,C_431] :
      ( r1_lattices(A_125,C_431,k15_lattice3(A_125,k1_tarski(C_431)))
      | ~ m1_subset_1(C_431,u1_struct_0(A_125))
      | ~ v4_lattice3(A_125)
      | ~ v10_lattices(A_125)
      | ~ l3_lattices(A_125)
      | v2_struct_0(A_125) ) ),
    inference(resolution,[status(thm)],[c_92,c_3821])).

tff(c_84,plain,(
    ! [A_114,C_123,B_121] :
      ( k2_lattices(A_114,C_123,B_121) = k2_lattices(A_114,B_121,C_123)
      | ~ m1_subset_1(C_123,u1_struct_0(A_114))
      | ~ m1_subset_1(B_121,u1_struct_0(A_114))
      | ~ v6_lattices(A_114)
      | ~ l1_lattices(A_114)
      | v2_struct_0(A_114) ) ),
    inference(cnfTransformation,[status(thm)],[f_264])).

tff(c_5793,plain,(
    ! [B_121] :
      ( k2_lattices('#skF_10',k15_lattice3('#skF_10',k1_tarski('#skF_11')),B_121) = k2_lattices('#skF_10',B_121,k15_lattice3('#skF_10',k1_tarski('#skF_11')))
      | ~ m1_subset_1(B_121,u1_struct_0('#skF_10'))
      | ~ v6_lattices('#skF_10')
      | ~ l1_lattices('#skF_10')
      | v2_struct_0('#skF_10') ) ),
    inference(resolution,[status(thm)],[c_5735,c_84])).

tff(c_5865,plain,(
    ! [B_121] :
      ( k2_lattices('#skF_10',k15_lattice3('#skF_10',k1_tarski('#skF_11')),B_121) = k2_lattices('#skF_10',B_121,k15_lattice3('#skF_10',k1_tarski('#skF_11')))
      | ~ m1_subset_1(B_121,u1_struct_0('#skF_10'))
      | v2_struct_0('#skF_10') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_111,c_328,c_5793])).

tff(c_6005,plain,(
    ! [B_523] :
      ( k2_lattices('#skF_10',k15_lattice3('#skF_10',k1_tarski('#skF_11')),B_523) = k2_lattices('#skF_10',B_523,k15_lattice3('#skF_10',k1_tarski('#skF_11')))
      | ~ m1_subset_1(B_523,u1_struct_0('#skF_10')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_106,c_5865])).

tff(c_4082,plain,(
    ! [C_439] :
      ( r1_lattices('#skF_10','#skF_11',k2_lattices('#skF_10',C_439,'#skF_11'))
      | ~ r1_lattices('#skF_10','#skF_11',C_439)
      | ~ m1_subset_1(C_439,u1_struct_0('#skF_10')) ) ),
    inference(splitRight,[status(thm)],[c_4063])).

tff(c_6039,plain,
    ( r1_lattices('#skF_10','#skF_11',k2_lattices('#skF_10','#skF_11',k15_lattice3('#skF_10',k1_tarski('#skF_11'))))
    | ~ r1_lattices('#skF_10','#skF_11',k15_lattice3('#skF_10',k1_tarski('#skF_11')))
    | ~ m1_subset_1(k15_lattice3('#skF_10',k1_tarski('#skF_11')),u1_struct_0('#skF_10'))
    | ~ m1_subset_1('#skF_11',u1_struct_0('#skF_10')) ),
    inference(superposition,[status(thm),theory(equality)],[c_6005,c_4082])).

tff(c_6133,plain,
    ( r1_lattices('#skF_10','#skF_11',k2_lattices('#skF_10','#skF_11',k15_lattice3('#skF_10',k1_tarski('#skF_11'))))
    | ~ r1_lattices('#skF_10','#skF_11',k15_lattice3('#skF_10',k1_tarski('#skF_11'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_5735,c_6039])).

tff(c_6204,plain,(
    ~ r1_lattices('#skF_10','#skF_11',k15_lattice3('#skF_10',k1_tarski('#skF_11'))) ),
    inference(splitLeft,[status(thm)],[c_6133])).

tff(c_6207,plain,
    ( ~ m1_subset_1('#skF_11',u1_struct_0('#skF_10'))
    | ~ v4_lattice3('#skF_10')
    | ~ v10_lattices('#skF_10')
    | ~ l3_lattices('#skF_10')
    | v2_struct_0('#skF_10') ),
    inference(resolution,[status(thm)],[c_3825,c_6204])).

tff(c_6213,plain,(
    v2_struct_0('#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_104,c_102,c_98,c_6207])).

tff(c_6215,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_106,c_6213])).

tff(c_6217,plain,(
    r1_lattices('#skF_10','#skF_11',k15_lattice3('#skF_10',k1_tarski('#skF_11'))) ),
    inference(splitRight,[status(thm)],[c_6133])).

tff(c_6335,plain,
    ( k15_lattice3('#skF_10',k1_tarski('#skF_11')) = '#skF_11'
    | ~ r1_lattices('#skF_10',k15_lattice3('#skF_10',k1_tarski('#skF_11')),'#skF_11')
    | ~ m1_subset_1('#skF_11',u1_struct_0('#skF_10'))
    | ~ m1_subset_1(k15_lattice3('#skF_10',k1_tarski('#skF_11')),u1_struct_0('#skF_10'))
    | ~ l2_lattices('#skF_10')
    | ~ v4_lattices('#skF_10')
    | v2_struct_0('#skF_10') ),
    inference(resolution,[status(thm)],[c_6217,c_54])).

tff(c_6347,plain,
    ( k15_lattice3('#skF_10',k1_tarski('#skF_11')) = '#skF_11'
    | ~ r1_lattices('#skF_10',k15_lattice3('#skF_10',k1_tarski('#skF_11')),'#skF_11')
    | v2_struct_0('#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4342,c_118,c_5735,c_98,c_6335])).

tff(c_6348,plain,(
    ~ r1_lattices('#skF_10',k15_lattice3('#skF_10',k1_tarski('#skF_11')),'#skF_11') ),
    inference(negUnitSimplification,[status(thm)],[c_106,c_158,c_6347])).

tff(c_6351,plain,
    ( ~ r4_lattice3('#skF_10','#skF_11',k1_tarski('#skF_11'))
    | ~ m1_subset_1('#skF_11',u1_struct_0('#skF_10'))
    | ~ v4_lattice3('#skF_10')
    | ~ v10_lattices('#skF_10')
    | ~ l3_lattices('#skF_10')
    | v2_struct_0('#skF_10') ),
    inference(resolution,[status(thm)],[c_3665,c_6348])).

tff(c_6357,plain,(
    v2_struct_0('#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_104,c_102,c_98,c_1586,c_6351])).

tff(c_6359,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_106,c_6357])).

tff(c_6361,plain,(
    '#skF_6'('#skF_10','#skF_11',k1_tarski('#skF_11')) != '#skF_11' ),
    inference(splitRight,[status(thm)],[c_1049])).

tff(c_8254,plain,(
    ! [A_653,B_654,D_655] :
      ( r1_lattices(A_653,k15_lattice3(A_653,B_654),D_655)
      | ~ r4_lattice3(A_653,D_655,B_654)
      | ~ m1_subset_1(D_655,u1_struct_0(A_653))
      | ~ m1_subset_1(k15_lattice3(A_653,B_654),u1_struct_0(A_653))
      | ~ v4_lattice3(A_653)
      | ~ v10_lattices(A_653)
      | ~ l3_lattices(A_653)
      | v2_struct_0(A_653) ) ),
    inference(cnfTransformation,[status(thm)],[f_249])).

tff(c_8257,plain,(
    ! [A_125,B_126,D_655] :
      ( r1_lattices(A_125,k15_lattice3(A_125,B_126),D_655)
      | ~ r4_lattice3(A_125,D_655,B_126)
      | ~ m1_subset_1(D_655,u1_struct_0(A_125))
      | ~ v4_lattice3(A_125)
      | ~ v10_lattices(A_125)
      | ~ l3_lattices(A_125)
      | v2_struct_0(A_125) ) ),
    inference(resolution,[status(thm)],[c_92,c_8254])).

tff(c_10661,plain,(
    ! [B_121] :
      ( k2_lattices('#skF_10',k15_lattice3('#skF_10',k1_tarski('#skF_11')),B_121) = k2_lattices('#skF_10',B_121,k15_lattice3('#skF_10',k1_tarski('#skF_11')))
      | ~ m1_subset_1(B_121,u1_struct_0('#skF_10'))
      | ~ v6_lattices('#skF_10')
      | ~ l1_lattices('#skF_10')
      | v2_struct_0('#skF_10') ) ),
    inference(resolution,[status(thm)],[c_10606,c_84])).

tff(c_10733,plain,(
    ! [B_121] :
      ( k2_lattices('#skF_10',k15_lattice3('#skF_10',k1_tarski('#skF_11')),B_121) = k2_lattices('#skF_10',B_121,k15_lattice3('#skF_10',k1_tarski('#skF_11')))
      | ~ m1_subset_1(B_121,u1_struct_0('#skF_10'))
      | v2_struct_0('#skF_10') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_111,c_328,c_10661])).

tff(c_11291,plain,(
    ! [B_771] :
      ( k2_lattices('#skF_10',k15_lattice3('#skF_10',k1_tarski('#skF_11')),B_771) = k2_lattices('#skF_10',B_771,k15_lattice3('#skF_10',k1_tarski('#skF_11')))
      | ~ m1_subset_1(B_771,u1_struct_0('#skF_10')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_106,c_10733])).

tff(c_8711,plain,(
    ! [B_674] :
      ( r1_lattices('#skF_10',k2_lattices('#skF_10',B_674,'#skF_11'),'#skF_11')
      | ~ r1_lattices('#skF_10',B_674,'#skF_11')
      | ~ m1_subset_1('#skF_11',u1_struct_0('#skF_10'))
      | ~ m1_subset_1('#skF_11',u1_struct_0('#skF_10'))
      | ~ m1_subset_1(B_674,u1_struct_0('#skF_10'))
      | ~ l3_lattices('#skF_10')
      | ~ v9_lattices('#skF_10')
      | ~ v8_lattices('#skF_10')
      | ~ v7_lattices('#skF_10')
      | v2_struct_0('#skF_10') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_554,c_8581])).

tff(c_8796,plain,(
    ! [B_674] :
      ( r1_lattices('#skF_10',k2_lattices('#skF_10',B_674,'#skF_11'),'#skF_11')
      | ~ r1_lattices('#skF_10',B_674,'#skF_11')
      | ~ m1_subset_1(B_674,u1_struct_0('#skF_10'))
      | ~ v7_lattices('#skF_10')
      | v2_struct_0('#skF_10') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_351,c_340,c_100,c_98,c_98,c_8711])).

tff(c_8797,plain,(
    ! [B_674] :
      ( r1_lattices('#skF_10',k2_lattices('#skF_10',B_674,'#skF_11'),'#skF_11')
      | ~ r1_lattices('#skF_10',B_674,'#skF_11')
      | ~ m1_subset_1(B_674,u1_struct_0('#skF_10'))
      | ~ v7_lattices('#skF_10') ) ),
    inference(negUnitSimplification,[status(thm)],[c_106,c_8796])).

tff(c_8816,plain,(
    ! [B_674] :
      ( r1_lattices('#skF_10',k2_lattices('#skF_10',B_674,'#skF_11'),'#skF_11')
      | ~ r1_lattices('#skF_10',B_674,'#skF_11')
      | ~ m1_subset_1(B_674,u1_struct_0('#skF_10')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8814,c_8797])).

tff(c_11339,plain,
    ( r1_lattices('#skF_10',k2_lattices('#skF_10','#skF_11',k15_lattice3('#skF_10',k1_tarski('#skF_11'))),'#skF_11')
    | ~ r1_lattices('#skF_10',k15_lattice3('#skF_10',k1_tarski('#skF_11')),'#skF_11')
    | ~ m1_subset_1(k15_lattice3('#skF_10',k1_tarski('#skF_11')),u1_struct_0('#skF_10'))
    | ~ m1_subset_1('#skF_11',u1_struct_0('#skF_10')) ),
    inference(superposition,[status(thm),theory(equality)],[c_11291,c_8816])).

tff(c_11441,plain,
    ( r1_lattices('#skF_10',k2_lattices('#skF_10','#skF_11',k15_lattice3('#skF_10',k1_tarski('#skF_11'))),'#skF_11')
    | ~ r1_lattices('#skF_10',k15_lattice3('#skF_10',k1_tarski('#skF_11')),'#skF_11') ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_10606,c_11339])).

tff(c_11515,plain,(
    ~ r1_lattices('#skF_10',k15_lattice3('#skF_10',k1_tarski('#skF_11')),'#skF_11') ),
    inference(splitLeft,[status(thm)],[c_11441])).

tff(c_11518,plain,
    ( ~ r4_lattice3('#skF_10','#skF_11',k1_tarski('#skF_11'))
    | ~ m1_subset_1('#skF_11',u1_struct_0('#skF_10'))
    | ~ v4_lattice3('#skF_10')
    | ~ v10_lattices('#skF_10')
    | ~ l3_lattices('#skF_10')
    | v2_struct_0('#skF_10') ),
    inference(resolution,[status(thm)],[c_8257,c_11515])).

tff(c_11524,plain,
    ( ~ r4_lattice3('#skF_10','#skF_11',k1_tarski('#skF_11'))
    | v2_struct_0('#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_104,c_102,c_98,c_11518])).

tff(c_11525,plain,(
    ~ r4_lattice3('#skF_10','#skF_11',k1_tarski('#skF_11')) ),
    inference(negUnitSimplification,[status(thm)],[c_106,c_11524])).

tff(c_11529,plain,
    ( '#skF_6'('#skF_10','#skF_11',k1_tarski('#skF_11')) = '#skF_11'
    | ~ m1_subset_1('#skF_11',u1_struct_0('#skF_10'))
    | ~ l3_lattices('#skF_10')
    | v2_struct_0('#skF_10') ),
    inference(resolution,[status(thm)],[c_278,c_11525])).

tff(c_11532,plain,
    ( '#skF_6'('#skF_10','#skF_11',k1_tarski('#skF_11')) = '#skF_11'
    | v2_struct_0('#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_98,c_11529])).

tff(c_11534,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_106,c_6361,c_11532])).

tff(c_11536,plain,(
    r1_lattices('#skF_10',k15_lattice3('#skF_10',k1_tarski('#skF_11')),'#skF_11') ),
    inference(splitRight,[status(thm)],[c_11441])).

tff(c_11577,plain,
    ( k2_lattices('#skF_10',k15_lattice3('#skF_10',k1_tarski('#skF_11')),'#skF_11') = k15_lattice3('#skF_10',k1_tarski('#skF_11'))
    | ~ m1_subset_1('#skF_11',u1_struct_0('#skF_10'))
    | ~ m1_subset_1(k15_lattice3('#skF_10',k1_tarski('#skF_11')),u1_struct_0('#skF_10'))
    | ~ l3_lattices('#skF_10')
    | ~ v9_lattices('#skF_10')
    | ~ v8_lattices('#skF_10')
    | v2_struct_0('#skF_10') ),
    inference(resolution,[status(thm)],[c_11536,c_52])).

tff(c_11585,plain,
    ( k2_lattices('#skF_10','#skF_11',k15_lattice3('#skF_10',k1_tarski('#skF_11'))) = k15_lattice3('#skF_10',k1_tarski('#skF_11'))
    | v2_struct_0('#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_351,c_340,c_100,c_10606,c_98,c_461,c_11577])).

tff(c_11587,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_106,c_9351,c_11585])).

tff(c_11588,plain,(
    k16_lattice3('#skF_10',k6_domain_1(u1_struct_0('#skF_10'),'#skF_11')) != '#skF_11' ),
    inference(splitRight,[status(thm)],[c_96])).

tff(c_11623,plain,(
    k16_lattice3('#skF_10',k1_tarski('#skF_11')) != '#skF_11' ),
    inference(demodulation,[status(thm),theory(equality)],[c_11620,c_11588])).

tff(c_11589,plain,(
    k15_lattice3('#skF_10',k6_domain_1(u1_struct_0('#skF_10'),'#skF_11')) = '#skF_11' ),
    inference(splitRight,[status(thm)],[c_96])).

tff(c_11622,plain,(
    k15_lattice3('#skF_10',k1_tarski('#skF_11')) = '#skF_11' ),
    inference(demodulation,[status(thm),theory(equality)],[c_11620,c_11589])).

tff(c_11840,plain,(
    ! [A_832,B_833] :
      ( r4_lattice3(A_832,k15_lattice3(A_832,B_833),B_833)
      | ~ m1_subset_1(k15_lattice3(A_832,B_833),u1_struct_0(A_832))
      | ~ v4_lattice3(A_832)
      | ~ v10_lattices(A_832)
      | ~ l3_lattices(A_832)
      | v2_struct_0(A_832) ) ),
    inference(cnfTransformation,[status(thm)],[f_249])).

tff(c_11842,plain,
    ( r4_lattice3('#skF_10',k15_lattice3('#skF_10',k1_tarski('#skF_11')),k1_tarski('#skF_11'))
    | ~ m1_subset_1('#skF_11',u1_struct_0('#skF_10'))
    | ~ v4_lattice3('#skF_10')
    | ~ v10_lattices('#skF_10')
    | ~ l3_lattices('#skF_10')
    | v2_struct_0('#skF_10') ),
    inference(superposition,[status(thm),theory(equality)],[c_11622,c_11840])).

tff(c_11846,plain,
    ( r4_lattice3('#skF_10','#skF_11',k1_tarski('#skF_11'))
    | v2_struct_0('#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_104,c_102,c_98,c_11622,c_11842])).

tff(c_11847,plain,(
    r4_lattice3('#skF_10','#skF_11',k1_tarski('#skF_11')) ),
    inference(negUnitSimplification,[status(thm)],[c_106,c_11846])).

tff(c_12222,plain,(
    ! [A_857,D_858,B_859,C_860] :
      ( r1_lattices(A_857,D_858,B_859)
      | ~ r2_hidden(D_858,C_860)
      | ~ m1_subset_1(D_858,u1_struct_0(A_857))
      | ~ r4_lattice3(A_857,B_859,C_860)
      | ~ m1_subset_1(B_859,u1_struct_0(A_857))
      | ~ l3_lattices(A_857)
      | v2_struct_0(A_857) ) ),
    inference(cnfTransformation,[status(thm)],[f_221])).

tff(c_12238,plain,(
    ! [A_861,C_862,B_863] :
      ( r1_lattices(A_861,C_862,B_863)
      | ~ m1_subset_1(C_862,u1_struct_0(A_861))
      | ~ r4_lattice3(A_861,B_863,k1_tarski(C_862))
      | ~ m1_subset_1(B_863,u1_struct_0(A_861))
      | ~ l3_lattices(A_861)
      | v2_struct_0(A_861) ) ),
    inference(resolution,[status(thm)],[c_4,c_12222])).

tff(c_12245,plain,
    ( r1_lattices('#skF_10','#skF_11','#skF_11')
    | ~ m1_subset_1('#skF_11',u1_struct_0('#skF_10'))
    | ~ l3_lattices('#skF_10')
    | v2_struct_0('#skF_10') ),
    inference(resolution,[status(thm)],[c_11847,c_12238])).

tff(c_12252,plain,
    ( r1_lattices('#skF_10','#skF_11','#skF_11')
    | v2_struct_0('#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_98,c_12245])).

tff(c_12253,plain,(
    r1_lattices('#skF_10','#skF_11','#skF_11') ),
    inference(negUnitSimplification,[status(thm)],[c_106,c_12252])).

tff(c_11729,plain,(
    ! [A_802,B_803,C_804] :
      ( r2_hidden('#skF_5'(A_802,B_803,C_804),C_804)
      | r3_lattice3(A_802,B_803,C_804)
      | ~ m1_subset_1(B_803,u1_struct_0(A_802))
      | ~ l3_lattices(A_802)
      | v2_struct_0(A_802) ) ),
    inference(cnfTransformation,[status(thm)],[f_203])).

tff(c_11734,plain,(
    ! [A_802,B_803,A_1] :
      ( '#skF_5'(A_802,B_803,k1_tarski(A_1)) = A_1
      | r3_lattice3(A_802,B_803,k1_tarski(A_1))
      | ~ m1_subset_1(B_803,u1_struct_0(A_802))
      | ~ l3_lattices(A_802)
      | v2_struct_0(A_802) ) ),
    inference(resolution,[status(thm)],[c_11729,c_2])).

tff(c_12766,plain,(
    ! [A_893,C_894,B_895] :
      ( k16_lattice3(A_893,C_894) = B_895
      | ~ r3_lattice3(A_893,B_895,C_894)
      | ~ r2_hidden(B_895,C_894)
      | ~ m1_subset_1(B_895,u1_struct_0(A_893))
      | ~ l3_lattices(A_893)
      | ~ v4_lattice3(A_893)
      | ~ v10_lattices(A_893)
      | v2_struct_0(A_893) ) ),
    inference(cnfTransformation,[status(thm)],[f_290])).

tff(c_15577,plain,(
    ! [A_1053,A_1054,B_1055] :
      ( k16_lattice3(A_1053,k1_tarski(A_1054)) = B_1055
      | ~ r2_hidden(B_1055,k1_tarski(A_1054))
      | ~ v4_lattice3(A_1053)
      | ~ v10_lattices(A_1053)
      | '#skF_5'(A_1053,B_1055,k1_tarski(A_1054)) = A_1054
      | ~ m1_subset_1(B_1055,u1_struct_0(A_1053))
      | ~ l3_lattices(A_1053)
      | v2_struct_0(A_1053) ) ),
    inference(resolution,[status(thm)],[c_11734,c_12766])).

tff(c_15597,plain,(
    ! [A_1056,C_1057] :
      ( k16_lattice3(A_1056,k1_tarski(C_1057)) = C_1057
      | ~ v4_lattice3(A_1056)
      | ~ v10_lattices(A_1056)
      | '#skF_5'(A_1056,C_1057,k1_tarski(C_1057)) = C_1057
      | ~ m1_subset_1(C_1057,u1_struct_0(A_1056))
      | ~ l3_lattices(A_1056)
      | v2_struct_0(A_1056) ) ),
    inference(resolution,[status(thm)],[c_4,c_15577])).

tff(c_15615,plain,
    ( k16_lattice3('#skF_10',k1_tarski('#skF_11')) = '#skF_11'
    | ~ v4_lattice3('#skF_10')
    | ~ v10_lattices('#skF_10')
    | '#skF_5'('#skF_10','#skF_11',k1_tarski('#skF_11')) = '#skF_11'
    | ~ l3_lattices('#skF_10')
    | v2_struct_0('#skF_10') ),
    inference(resolution,[status(thm)],[c_98,c_15597])).

tff(c_15626,plain,
    ( k16_lattice3('#skF_10',k1_tarski('#skF_11')) = '#skF_11'
    | '#skF_5'('#skF_10','#skF_11',k1_tarski('#skF_11')) = '#skF_11'
    | v2_struct_0('#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_104,c_102,c_15615])).

tff(c_15627,plain,(
    '#skF_5'('#skF_10','#skF_11',k1_tarski('#skF_11')) = '#skF_11' ),
    inference(negUnitSimplification,[status(thm)],[c_106,c_11623,c_15626])).

tff(c_60,plain,(
    ! [A_58,B_70,C_76] :
      ( ~ r1_lattices(A_58,B_70,'#skF_5'(A_58,B_70,C_76))
      | r3_lattice3(A_58,B_70,C_76)
      | ~ m1_subset_1(B_70,u1_struct_0(A_58))
      | ~ l3_lattices(A_58)
      | v2_struct_0(A_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_203])).

tff(c_15706,plain,
    ( ~ r1_lattices('#skF_10','#skF_11','#skF_11')
    | r3_lattice3('#skF_10','#skF_11',k1_tarski('#skF_11'))
    | ~ m1_subset_1('#skF_11',u1_struct_0('#skF_10'))
    | ~ l3_lattices('#skF_10')
    | v2_struct_0('#skF_10') ),
    inference(superposition,[status(thm),theory(equality)],[c_15627,c_60])).

tff(c_15731,plain,
    ( r3_lattice3('#skF_10','#skF_11',k1_tarski('#skF_11'))
    | v2_struct_0('#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_98,c_12253,c_15706])).

tff(c_15732,plain,(
    r3_lattice3('#skF_10','#skF_11',k1_tarski('#skF_11')) ),
    inference(negUnitSimplification,[status(thm)],[c_106,c_15731])).

tff(c_94,plain,(
    ! [A_127,C_133,B_131] :
      ( k16_lattice3(A_127,C_133) = B_131
      | ~ r3_lattice3(A_127,B_131,C_133)
      | ~ r2_hidden(B_131,C_133)
      | ~ m1_subset_1(B_131,u1_struct_0(A_127))
      | ~ l3_lattices(A_127)
      | ~ v4_lattice3(A_127)
      | ~ v10_lattices(A_127)
      | v2_struct_0(A_127) ) ),
    inference(cnfTransformation,[status(thm)],[f_290])).

tff(c_15738,plain,
    ( k16_lattice3('#skF_10',k1_tarski('#skF_11')) = '#skF_11'
    | ~ r2_hidden('#skF_11',k1_tarski('#skF_11'))
    | ~ m1_subset_1('#skF_11',u1_struct_0('#skF_10'))
    | ~ l3_lattices('#skF_10')
    | ~ v4_lattice3('#skF_10')
    | ~ v10_lattices('#skF_10')
    | v2_struct_0('#skF_10') ),
    inference(resolution,[status(thm)],[c_15732,c_94])).

tff(c_15744,plain,
    ( k16_lattice3('#skF_10',k1_tarski('#skF_11')) = '#skF_11'
    | v2_struct_0('#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_102,c_100,c_98,c_4,c_15738])).

tff(c_15746,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_106,c_11623,c_15744])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:18:11 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 11.51/4.06  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.51/4.10  
% 11.51/4.10  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.78/4.10  %$ r4_lattice3 > r3_lattice3 > r1_lattices > r2_hidden > m1_subset_1 > v9_lattices > v8_lattices > v7_lattices > v6_lattices > v5_lattices > v4_lattices > v4_lattice3 > v2_struct_0 > v1_xboole_0 > v10_lattices > l3_lattices > l2_lattices > l1_struct_0 > l1_lattices > k4_lattices > k2_lattices > k1_lattices > k6_domain_1 > k16_lattice3 > k15_lattice3 > #nlpp > u1_struct_0 > k1_tarski > #skF_9 > #skF_4 > #skF_11 > #skF_6 > #skF_8 > #skF_10 > #skF_5 > #skF_7 > #skF_3 > #skF_2 > #skF_1
% 11.78/4.10  
% 11.78/4.10  %Foreground sorts:
% 11.78/4.10  
% 11.78/4.10  
% 11.78/4.10  %Background operators:
% 11.78/4.10  
% 11.78/4.10  
% 11.78/4.10  %Foreground operators:
% 11.78/4.10  tff(l3_lattices, type, l3_lattices: $i > $o).
% 11.78/4.10  tff('#skF_9', type, '#skF_9': $i > $i).
% 11.78/4.10  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 11.78/4.10  tff(k2_lattices, type, k2_lattices: ($i * $i * $i) > $i).
% 11.78/4.10  tff(l2_lattices, type, l2_lattices: $i > $o).
% 11.78/4.10  tff('#skF_4', type, '#skF_4': $i > $i).
% 11.78/4.10  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 11.78/4.10  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 11.78/4.10  tff('#skF_11', type, '#skF_11': $i).
% 11.78/4.10  tff('#skF_6', type, '#skF_6': ($i * $i * $i) > $i).
% 11.78/4.10  tff(k4_lattices, type, k4_lattices: ($i * $i * $i) > $i).
% 11.78/4.10  tff(k1_tarski, type, k1_tarski: $i > $i).
% 11.78/4.10  tff(k16_lattice3, type, k16_lattice3: ($i * $i) > $i).
% 11.78/4.10  tff(k1_lattices, type, k1_lattices: ($i * $i * $i) > $i).
% 11.78/4.10  tff(k15_lattice3, type, k15_lattice3: ($i * $i) > $i).
% 11.78/4.10  tff(l1_lattices, type, l1_lattices: $i > $o).
% 11.78/4.10  tff('#skF_8', type, '#skF_8': $i > $i).
% 11.78/4.10  tff(r1_lattices, type, r1_lattices: ($i * $i * $i) > $o).
% 11.78/4.10  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 11.78/4.10  tff('#skF_10', type, '#skF_10': $i).
% 11.78/4.10  tff(v4_lattices, type, v4_lattices: $i > $o).
% 11.78/4.10  tff(v6_lattices, type, v6_lattices: $i > $o).
% 11.78/4.10  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 11.78/4.10  tff(v9_lattices, type, v9_lattices: $i > $o).
% 11.78/4.10  tff(r4_lattice3, type, r4_lattice3: ($i * $i * $i) > $o).
% 11.78/4.10  tff(v4_lattice3, type, v4_lattice3: $i > $o).
% 11.78/4.10  tff(v5_lattices, type, v5_lattices: $i > $o).
% 11.78/4.10  tff(v10_lattices, type, v10_lattices: $i > $o).
% 11.78/4.10  tff('#skF_7', type, '#skF_7': ($i * $i * $i) > $i).
% 11.78/4.10  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 11.78/4.10  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 11.78/4.10  tff('#skF_3', type, '#skF_3': $i > $i).
% 11.78/4.10  tff(v8_lattices, type, v8_lattices: $i > $o).
% 11.78/4.10  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 11.78/4.10  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 11.78/4.10  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 11.78/4.10  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 11.78/4.10  tff(r3_lattice3, type, r3_lattice3: ($i * $i * $i) > $o).
% 11.78/4.10  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 11.78/4.10  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 11.78/4.10  tff(v7_lattices, type, v7_lattices: $i > $o).
% 11.78/4.10  
% 11.78/4.13  tff(f_307, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v10_lattices(A)) & v4_lattice3(A)) & l3_lattices(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => ((k15_lattice3(A, k6_domain_1(u1_struct_0(A), B)) = B) & (k16_lattice3(A, k6_domain_1(u1_struct_0(A), B)) = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_lattice3)).
% 11.78/4.13  tff(f_94, axiom, (![A]: (l3_lattices(A) => (l1_lattices(A) & l2_lattices(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l3_lattices)).
% 11.78/4.13  tff(f_88, axiom, (![A]: (l2_lattices(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l2_lattices)).
% 11.78/4.13  tff(f_47, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 11.78/4.13  tff(f_40, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_struct_0)).
% 11.78/4.13  tff(f_271, axiom, (![A, B]: ((~v2_struct_0(A) & l3_lattices(A)) => m1_subset_1(k15_lattice3(A, B), u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k15_lattice3)).
% 11.78/4.13  tff(f_249, axiom, (![A]: ((~v2_struct_0(A) & l3_lattices(A)) => ((((~v2_struct_0(A) & v10_lattices(A)) & v4_lattice3(A)) & l3_lattices(A)) => (![B, C]: (m1_subset_1(C, u1_struct_0(A)) => ((C = k15_lattice3(A, B)) <=> (r4_lattice3(A, C, B) & (![D]: (m1_subset_1(D, u1_struct_0(A)) => (r4_lattice3(A, D, B) => r1_lattices(A, C, D))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d21_lattice3)).
% 11.78/4.13  tff(f_32, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 11.78/4.13  tff(f_221, axiom, (![A]: ((~v2_struct_0(A) & l3_lattices(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (r4_lattice3(A, B, C) <=> (![D]: (m1_subset_1(D, u1_struct_0(A)) => (r2_hidden(D, C) => r1_lattices(A, D, B)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d17_lattice3)).
% 11.78/4.13  tff(f_69, axiom, (![A]: (l3_lattices(A) => ((~v2_struct_0(A) & v10_lattices(A)) => ((((((~v2_struct_0(A) & v4_lattices(A)) & v5_lattices(A)) & v6_lattices(A)) & v7_lattices(A)) & v8_lattices(A)) & v9_lattices(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_lattices)).
% 11.78/4.13  tff(f_123, axiom, (![A]: (((((~v2_struct_0(A) & v6_lattices(A)) & v8_lattices(A)) & v9_lattices(A)) & l3_lattices(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (k1_lattices(A, B, B) = B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_lattices)).
% 11.78/4.13  tff(f_264, axiom, (![A]: ((~v2_struct_0(A) & l1_lattices(A)) => (v6_lattices(A) <=> (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (k2_lattices(A, B, C) = k2_lattices(A, C, B))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d6_lattices)).
% 11.78/4.13  tff(f_142, axiom, (![A]: ((((~v2_struct_0(A) & v8_lattices(A)) & v9_lattices(A)) & l3_lattices(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r1_lattices(A, B, C) <=> (k2_lattices(A, B, C) = B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t21_lattices)).
% 11.78/4.13  tff(f_161, axiom, (![A]: (((~v2_struct_0(A) & v4_lattices(A)) & l2_lattices(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => ((r1_lattices(A, B, C) & r1_lattices(A, C, B)) => (B = C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t26_lattices)).
% 11.78/4.13  tff(f_84, axiom, (![A]: ((~v2_struct_0(A) & l3_lattices(A)) => (v9_lattices(A) <=> (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (k2_lattices(A, B, k1_lattices(A, B, C)) = B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d9_lattices)).
% 11.78/4.13  tff(f_185, axiom, (![A]: (((((~v2_struct_0(A) & v7_lattices(A)) & v8_lattices(A)) & v9_lattices(A)) & l3_lattices(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (![D]: (m1_subset_1(D, u1_struct_0(A)) => (r1_lattices(A, B, C) => r1_lattices(A, k2_lattices(A, B, D), k2_lattices(A, C, D))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t27_lattices)).
% 11.78/4.13  tff(f_203, axiom, (![A]: ((~v2_struct_0(A) & l3_lattices(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (r3_lattice3(A, B, C) <=> (![D]: (m1_subset_1(D, u1_struct_0(A)) => (r2_hidden(D, C) => r1_lattices(A, B, D)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d16_lattice3)).
% 11.78/4.13  tff(f_290, axiom, (![A]: ((((~v2_struct_0(A) & v10_lattices(A)) & v4_lattice3(A)) & l3_lattices(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: ((r2_hidden(B, C) & r3_lattice3(A, B, C)) => (k16_lattice3(A, C) = B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t42_lattice3)).
% 11.78/4.13  tff(c_106, plain, (~v2_struct_0('#skF_10')), inference(cnfTransformation, [status(thm)], [f_307])).
% 11.78/4.13  tff(c_100, plain, (l3_lattices('#skF_10')), inference(cnfTransformation, [status(thm)], [f_307])).
% 11.78/4.13  tff(c_114, plain, (![A_138]: (l2_lattices(A_138) | ~l3_lattices(A_138))), inference(cnfTransformation, [status(thm)], [f_94])).
% 11.78/4.13  tff(c_118, plain, (l2_lattices('#skF_10')), inference(resolution, [status(thm)], [c_100, c_114])).
% 11.78/4.13  tff(c_40, plain, (![A_21]: (l1_struct_0(A_21) | ~l2_lattices(A_21))), inference(cnfTransformation, [status(thm)], [f_88])).
% 11.78/4.13  tff(c_122, plain, (l1_struct_0('#skF_10')), inference(resolution, [status(thm)], [c_118, c_40])).
% 11.78/4.13  tff(c_98, plain, (m1_subset_1('#skF_11', u1_struct_0('#skF_10'))), inference(cnfTransformation, [status(thm)], [f_307])).
% 11.78/4.13  tff(c_11595, plain, (![A_778, B_779]: (k6_domain_1(A_778, B_779)=k1_tarski(B_779) | ~m1_subset_1(B_779, A_778) | v1_xboole_0(A_778))), inference(cnfTransformation, [status(thm)], [f_47])).
% 11.78/4.13  tff(c_11599, plain, (k6_domain_1(u1_struct_0('#skF_10'), '#skF_11')=k1_tarski('#skF_11') | v1_xboole_0(u1_struct_0('#skF_10'))), inference(resolution, [status(thm)], [c_98, c_11595])).
% 11.78/4.13  tff(c_11611, plain, (v1_xboole_0(u1_struct_0('#skF_10'))), inference(splitLeft, [status(thm)], [c_11599])).
% 11.78/4.13  tff(c_14, plain, (![A_6]: (~v1_xboole_0(u1_struct_0(A_6)) | ~l1_struct_0(A_6) | v2_struct_0(A_6))), inference(cnfTransformation, [status(thm)], [f_40])).
% 11.78/4.13  tff(c_11614, plain, (~l1_struct_0('#skF_10') | v2_struct_0('#skF_10')), inference(resolution, [status(thm)], [c_11611, c_14])).
% 11.78/4.13  tff(c_11617, plain, (v2_struct_0('#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_122, c_11614])).
% 11.78/4.13  tff(c_11619, plain, $false, inference(negUnitSimplification, [status(thm)], [c_106, c_11617])).
% 11.78/4.13  tff(c_11620, plain, (k6_domain_1(u1_struct_0('#skF_10'), '#skF_11')=k1_tarski('#skF_11')), inference(splitRight, [status(thm)], [c_11599])).
% 11.78/4.13  tff(c_137, plain, (![A_148, B_149]: (k6_domain_1(A_148, B_149)=k1_tarski(B_149) | ~m1_subset_1(B_149, A_148) | v1_xboole_0(A_148))), inference(cnfTransformation, [status(thm)], [f_47])).
% 11.78/4.13  tff(c_141, plain, (k6_domain_1(u1_struct_0('#skF_10'), '#skF_11')=k1_tarski('#skF_11') | v1_xboole_0(u1_struct_0('#skF_10'))), inference(resolution, [status(thm)], [c_98, c_137])).
% 11.78/4.13  tff(c_142, plain, (v1_xboole_0(u1_struct_0('#skF_10'))), inference(splitLeft, [status(thm)], [c_141])).
% 11.78/4.13  tff(c_145, plain, (~l1_struct_0('#skF_10') | v2_struct_0('#skF_10')), inference(resolution, [status(thm)], [c_142, c_14])).
% 11.78/4.13  tff(c_148, plain, (v2_struct_0('#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_122, c_145])).
% 11.78/4.13  tff(c_150, plain, $false, inference(negUnitSimplification, [status(thm)], [c_106, c_148])).
% 11.78/4.13  tff(c_151, plain, (k6_domain_1(u1_struct_0('#skF_10'), '#skF_11')=k1_tarski('#skF_11')), inference(splitRight, [status(thm)], [c_141])).
% 11.78/4.13  tff(c_96, plain, (k16_lattice3('#skF_10', k6_domain_1(u1_struct_0('#skF_10'), '#skF_11'))!='#skF_11' | k15_lattice3('#skF_10', k6_domain_1(u1_struct_0('#skF_10'), '#skF_11'))!='#skF_11'), inference(cnfTransformation, [status(thm)], [f_307])).
% 11.78/4.13  tff(c_135, plain, (k15_lattice3('#skF_10', k6_domain_1(u1_struct_0('#skF_10'), '#skF_11'))!='#skF_11'), inference(splitLeft, [status(thm)], [c_96])).
% 11.78/4.13  tff(c_158, plain, (k15_lattice3('#skF_10', k1_tarski('#skF_11'))!='#skF_11'), inference(demodulation, [status(thm), theory('equality')], [c_151, c_135])).
% 11.78/4.13  tff(c_104, plain, (v10_lattices('#skF_10')), inference(cnfTransformation, [status(thm)], [f_307])).
% 11.78/4.13  tff(c_102, plain, (v4_lattice3('#skF_10')), inference(cnfTransformation, [status(thm)], [f_307])).
% 11.78/4.13  tff(c_92, plain, (![A_125, B_126]: (m1_subset_1(k15_lattice3(A_125, B_126), u1_struct_0(A_125)) | ~l3_lattices(A_125) | v2_struct_0(A_125))), inference(cnfTransformation, [status(thm)], [f_271])).
% 11.78/4.13  tff(c_359, plain, (![A_202, B_203]: (r4_lattice3(A_202, k15_lattice3(A_202, B_203), B_203) | ~m1_subset_1(k15_lattice3(A_202, B_203), u1_struct_0(A_202)) | ~v4_lattice3(A_202) | ~v10_lattices(A_202) | ~l3_lattices(A_202) | v2_struct_0(A_202))), inference(cnfTransformation, [status(thm)], [f_249])).
% 11.78/4.13  tff(c_362, plain, (![A_125, B_126]: (r4_lattice3(A_125, k15_lattice3(A_125, B_126), B_126) | ~v4_lattice3(A_125) | ~v10_lattices(A_125) | ~l3_lattices(A_125) | v2_struct_0(A_125))), inference(resolution, [status(thm)], [c_92, c_359])).
% 11.78/4.13  tff(c_4, plain, (![C_5]: (r2_hidden(C_5, k1_tarski(C_5)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 11.78/4.13  tff(c_935, plain, (![A_244, D_245, B_246, C_247]: (r1_lattices(A_244, D_245, B_246) | ~r2_hidden(D_245, C_247) | ~m1_subset_1(D_245, u1_struct_0(A_244)) | ~r4_lattice3(A_244, B_246, C_247) | ~m1_subset_1(B_246, u1_struct_0(A_244)) | ~l3_lattices(A_244) | v2_struct_0(A_244))), inference(cnfTransformation, [status(thm)], [f_221])).
% 11.78/4.13  tff(c_951, plain, (![A_248, C_249, B_250]: (r1_lattices(A_248, C_249, B_250) | ~m1_subset_1(C_249, u1_struct_0(A_248)) | ~r4_lattice3(A_248, B_250, k1_tarski(C_249)) | ~m1_subset_1(B_250, u1_struct_0(A_248)) | ~l3_lattices(A_248) | v2_struct_0(A_248))), inference(resolution, [status(thm)], [c_4, c_935])).
% 11.78/4.13  tff(c_8500, plain, (![A_666, C_667]: (r1_lattices(A_666, C_667, k15_lattice3(A_666, k1_tarski(C_667))) | ~m1_subset_1(C_667, u1_struct_0(A_666)) | ~m1_subset_1(k15_lattice3(A_666, k1_tarski(C_667)), u1_struct_0(A_666)) | ~v4_lattice3(A_666) | ~v10_lattices(A_666) | ~l3_lattices(A_666) | v2_struct_0(A_666))), inference(resolution, [status(thm)], [c_362, c_951])).
% 11.78/4.13  tff(c_8504, plain, (![A_125, C_667]: (r1_lattices(A_125, C_667, k15_lattice3(A_125, k1_tarski(C_667))) | ~m1_subset_1(C_667, u1_struct_0(A_125)) | ~v4_lattice3(A_125) | ~v10_lattices(A_125) | ~l3_lattices(A_125) | v2_struct_0(A_125))), inference(resolution, [status(thm)], [c_92, c_8500])).
% 11.78/4.13  tff(c_28, plain, (![A_9]: (v4_lattices(A_9) | ~v10_lattices(A_9) | v2_struct_0(A_9) | ~l3_lattices(A_9))), inference(cnfTransformation, [status(thm)], [f_69])).
% 11.78/4.13  tff(c_107, plain, (![A_135]: (l1_lattices(A_135) | ~l3_lattices(A_135))), inference(cnfTransformation, [status(thm)], [f_94])).
% 11.78/4.13  tff(c_111, plain, (l1_lattices('#skF_10')), inference(resolution, [status(thm)], [c_100, c_107])).
% 11.78/4.13  tff(c_24, plain, (![A_9]: (v6_lattices(A_9) | ~v10_lattices(A_9) | v2_struct_0(A_9) | ~l3_lattices(A_9))), inference(cnfTransformation, [status(thm)], [f_69])).
% 11.78/4.13  tff(c_290, plain, (![A_188, B_189]: (k1_lattices(A_188, B_189, B_189)=B_189 | ~m1_subset_1(B_189, u1_struct_0(A_188)) | ~l3_lattices(A_188) | ~v9_lattices(A_188) | ~v8_lattices(A_188) | ~v6_lattices(A_188) | v2_struct_0(A_188))), inference(cnfTransformation, [status(thm)], [f_123])).
% 11.78/4.13  tff(c_306, plain, (k1_lattices('#skF_10', '#skF_11', '#skF_11')='#skF_11' | ~l3_lattices('#skF_10') | ~v9_lattices('#skF_10') | ~v8_lattices('#skF_10') | ~v6_lattices('#skF_10') | v2_struct_0('#skF_10')), inference(resolution, [status(thm)], [c_98, c_290])).
% 11.78/4.13  tff(c_316, plain, (k1_lattices('#skF_10', '#skF_11', '#skF_11')='#skF_11' | ~v9_lattices('#skF_10') | ~v8_lattices('#skF_10') | ~v6_lattices('#skF_10') | v2_struct_0('#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_100, c_306])).
% 11.78/4.13  tff(c_317, plain, (k1_lattices('#skF_10', '#skF_11', '#skF_11')='#skF_11' | ~v9_lattices('#skF_10') | ~v8_lattices('#skF_10') | ~v6_lattices('#skF_10')), inference(negUnitSimplification, [status(thm)], [c_106, c_316])).
% 11.78/4.13  tff(c_318, plain, (~v6_lattices('#skF_10')), inference(splitLeft, [status(thm)], [c_317])).
% 11.78/4.13  tff(c_321, plain, (~v10_lattices('#skF_10') | v2_struct_0('#skF_10') | ~l3_lattices('#skF_10')), inference(resolution, [status(thm)], [c_24, c_318])).
% 11.78/4.13  tff(c_324, plain, (v2_struct_0('#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_100, c_104, c_321])).
% 11.78/4.13  tff(c_326, plain, $false, inference(negUnitSimplification, [status(thm)], [c_106, c_324])).
% 11.78/4.13  tff(c_328, plain, (v6_lattices('#skF_10')), inference(splitRight, [status(thm)], [c_317])).
% 11.78/4.13  tff(c_374, plain, (![A_211, C_212, B_213]: (k2_lattices(A_211, C_212, B_213)=k2_lattices(A_211, B_213, C_212) | ~m1_subset_1(C_212, u1_struct_0(A_211)) | ~m1_subset_1(B_213, u1_struct_0(A_211)) | ~v6_lattices(A_211) | ~l1_lattices(A_211) | v2_struct_0(A_211))), inference(cnfTransformation, [status(thm)], [f_264])).
% 11.78/4.13  tff(c_390, plain, (![B_213]: (k2_lattices('#skF_10', B_213, '#skF_11')=k2_lattices('#skF_10', '#skF_11', B_213) | ~m1_subset_1(B_213, u1_struct_0('#skF_10')) | ~v6_lattices('#skF_10') | ~l1_lattices('#skF_10') | v2_struct_0('#skF_10'))), inference(resolution, [status(thm)], [c_98, c_374])).
% 11.78/4.13  tff(c_400, plain, (![B_213]: (k2_lattices('#skF_10', B_213, '#skF_11')=k2_lattices('#skF_10', '#skF_11', B_213) | ~m1_subset_1(B_213, u1_struct_0('#skF_10')) | v2_struct_0('#skF_10'))), inference(demodulation, [status(thm), theory('equality')], [c_111, c_328, c_390])).
% 11.78/4.13  tff(c_402, plain, (![B_214]: (k2_lattices('#skF_10', B_214, '#skF_11')=k2_lattices('#skF_10', '#skF_11', B_214) | ~m1_subset_1(B_214, u1_struct_0('#skF_10')))), inference(negUnitSimplification, [status(thm)], [c_106, c_400])).
% 11.78/4.13  tff(c_430, plain, (![B_126]: (k2_lattices('#skF_10', k15_lattice3('#skF_10', B_126), '#skF_11')=k2_lattices('#skF_10', '#skF_11', k15_lattice3('#skF_10', B_126)) | ~l3_lattices('#skF_10') | v2_struct_0('#skF_10'))), inference(resolution, [status(thm)], [c_92, c_402])).
% 11.78/4.13  tff(c_460, plain, (![B_126]: (k2_lattices('#skF_10', k15_lattice3('#skF_10', B_126), '#skF_11')=k2_lattices('#skF_10', '#skF_11', k15_lattice3('#skF_10', B_126)) | v2_struct_0('#skF_10'))), inference(demodulation, [status(thm), theory('equality')], [c_100, c_430])).
% 11.78/4.13  tff(c_461, plain, (![B_126]: (k2_lattices('#skF_10', k15_lattice3('#skF_10', B_126), '#skF_11')=k2_lattices('#skF_10', '#skF_11', k15_lattice3('#skF_10', B_126)))), inference(negUnitSimplification, [status(thm)], [c_106, c_460])).
% 11.78/4.13  tff(c_20, plain, (![A_9]: (v8_lattices(A_9) | ~v10_lattices(A_9) | v2_struct_0(A_9) | ~l3_lattices(A_9))), inference(cnfTransformation, [status(thm)], [f_69])).
% 11.78/4.13  tff(c_18, plain, (![A_9]: (v9_lattices(A_9) | ~v10_lattices(A_9) | v2_struct_0(A_9) | ~l3_lattices(A_9))), inference(cnfTransformation, [status(thm)], [f_69])).
% 11.78/4.13  tff(c_327, plain, (~v8_lattices('#skF_10') | ~v9_lattices('#skF_10') | k1_lattices('#skF_10', '#skF_11', '#skF_11')='#skF_11'), inference(splitRight, [status(thm)], [c_317])).
% 11.78/4.13  tff(c_329, plain, (~v9_lattices('#skF_10')), inference(splitLeft, [status(thm)], [c_327])).
% 11.78/4.13  tff(c_333, plain, (~v10_lattices('#skF_10') | v2_struct_0('#skF_10') | ~l3_lattices('#skF_10')), inference(resolution, [status(thm)], [c_18, c_329])).
% 11.78/4.13  tff(c_336, plain, (v2_struct_0('#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_100, c_104, c_333])).
% 11.78/4.13  tff(c_338, plain, $false, inference(negUnitSimplification, [status(thm)], [c_106, c_336])).
% 11.78/4.13  tff(c_339, plain, (~v8_lattices('#skF_10') | k1_lattices('#skF_10', '#skF_11', '#skF_11')='#skF_11'), inference(splitRight, [status(thm)], [c_327])).
% 11.78/4.13  tff(c_341, plain, (~v8_lattices('#skF_10')), inference(splitLeft, [status(thm)], [c_339])).
% 11.78/4.13  tff(c_344, plain, (~v10_lattices('#skF_10') | v2_struct_0('#skF_10') | ~l3_lattices('#skF_10')), inference(resolution, [status(thm)], [c_20, c_341])).
% 11.78/4.13  tff(c_347, plain, (v2_struct_0('#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_100, c_104, c_344])).
% 11.78/4.13  tff(c_349, plain, $false, inference(negUnitSimplification, [status(thm)], [c_106, c_347])).
% 11.78/4.13  tff(c_351, plain, (v8_lattices('#skF_10')), inference(splitRight, [status(thm)], [c_339])).
% 11.78/4.13  tff(c_340, plain, (v9_lattices('#skF_10')), inference(splitRight, [status(thm)], [c_327])).
% 11.78/4.13  tff(c_6741, plain, (![A_559, B_560, C_561]: (r1_lattices(A_559, B_560, C_561) | k2_lattices(A_559, B_560, C_561)!=B_560 | ~m1_subset_1(C_561, u1_struct_0(A_559)) | ~m1_subset_1(B_560, u1_struct_0(A_559)) | ~l3_lattices(A_559) | ~v9_lattices(A_559) | ~v8_lattices(A_559) | v2_struct_0(A_559))), inference(cnfTransformation, [status(thm)], [f_142])).
% 11.78/4.14  tff(c_6757, plain, (![B_560]: (r1_lattices('#skF_10', B_560, '#skF_11') | k2_lattices('#skF_10', B_560, '#skF_11')!=B_560 | ~m1_subset_1(B_560, u1_struct_0('#skF_10')) | ~l3_lattices('#skF_10') | ~v9_lattices('#skF_10') | ~v8_lattices('#skF_10') | v2_struct_0('#skF_10'))), inference(resolution, [status(thm)], [c_98, c_6741])).
% 11.78/4.14  tff(c_6767, plain, (![B_560]: (r1_lattices('#skF_10', B_560, '#skF_11') | k2_lattices('#skF_10', B_560, '#skF_11')!=B_560 | ~m1_subset_1(B_560, u1_struct_0('#skF_10')) | v2_struct_0('#skF_10'))), inference(demodulation, [status(thm), theory('equality')], [c_351, c_340, c_100, c_6757])).
% 11.78/4.14  tff(c_6769, plain, (![B_562]: (r1_lattices('#skF_10', B_562, '#skF_11') | k2_lattices('#skF_10', B_562, '#skF_11')!=B_562 | ~m1_subset_1(B_562, u1_struct_0('#skF_10')))), inference(negUnitSimplification, [status(thm)], [c_106, c_6767])).
% 11.78/4.14  tff(c_6797, plain, (![B_126]: (r1_lattices('#skF_10', k15_lattice3('#skF_10', B_126), '#skF_11') | k2_lattices('#skF_10', k15_lattice3('#skF_10', B_126), '#skF_11')!=k15_lattice3('#skF_10', B_126) | ~l3_lattices('#skF_10') | v2_struct_0('#skF_10'))), inference(resolution, [status(thm)], [c_92, c_6769])).
% 11.78/4.14  tff(c_6827, plain, (![B_126]: (r1_lattices('#skF_10', k15_lattice3('#skF_10', B_126), '#skF_11') | k2_lattices('#skF_10', '#skF_11', k15_lattice3('#skF_10', B_126))!=k15_lattice3('#skF_10', B_126) | v2_struct_0('#skF_10'))), inference(demodulation, [status(thm), theory('equality')], [c_100, c_461, c_6797])).
% 11.78/4.14  tff(c_6832, plain, (![B_563]: (r1_lattices('#skF_10', k15_lattice3('#skF_10', B_563), '#skF_11') | k2_lattices('#skF_10', '#skF_11', k15_lattice3('#skF_10', B_563))!=k15_lattice3('#skF_10', B_563))), inference(negUnitSimplification, [status(thm)], [c_106, c_6827])).
% 11.78/4.14  tff(c_54, plain, (![C_42, B_40, A_36]: (C_42=B_40 | ~r1_lattices(A_36, C_42, B_40) | ~r1_lattices(A_36, B_40, C_42) | ~m1_subset_1(C_42, u1_struct_0(A_36)) | ~m1_subset_1(B_40, u1_struct_0(A_36)) | ~l2_lattices(A_36) | ~v4_lattices(A_36) | v2_struct_0(A_36))), inference(cnfTransformation, [status(thm)], [f_161])).
% 11.78/4.14  tff(c_6834, plain, (![B_563]: (k15_lattice3('#skF_10', B_563)='#skF_11' | ~r1_lattices('#skF_10', '#skF_11', k15_lattice3('#skF_10', B_563)) | ~m1_subset_1(k15_lattice3('#skF_10', B_563), u1_struct_0('#skF_10')) | ~m1_subset_1('#skF_11', u1_struct_0('#skF_10')) | ~l2_lattices('#skF_10') | ~v4_lattices('#skF_10') | v2_struct_0('#skF_10') | k2_lattices('#skF_10', '#skF_11', k15_lattice3('#skF_10', B_563))!=k15_lattice3('#skF_10', B_563))), inference(resolution, [status(thm)], [c_6832, c_54])).
% 11.78/4.14  tff(c_6837, plain, (![B_563]: (k15_lattice3('#skF_10', B_563)='#skF_11' | ~r1_lattices('#skF_10', '#skF_11', k15_lattice3('#skF_10', B_563)) | ~m1_subset_1(k15_lattice3('#skF_10', B_563), u1_struct_0('#skF_10')) | ~v4_lattices('#skF_10') | v2_struct_0('#skF_10') | k2_lattices('#skF_10', '#skF_11', k15_lattice3('#skF_10', B_563))!=k15_lattice3('#skF_10', B_563))), inference(demodulation, [status(thm), theory('equality')], [c_118, c_98, c_6834])).
% 11.78/4.14  tff(c_6838, plain, (![B_563]: (k15_lattice3('#skF_10', B_563)='#skF_11' | ~r1_lattices('#skF_10', '#skF_11', k15_lattice3('#skF_10', B_563)) | ~m1_subset_1(k15_lattice3('#skF_10', B_563), u1_struct_0('#skF_10')) | ~v4_lattices('#skF_10') | k2_lattices('#skF_10', '#skF_11', k15_lattice3('#skF_10', B_563))!=k15_lattice3('#skF_10', B_563))), inference(negUnitSimplification, [status(thm)], [c_106, c_6837])).
% 11.78/4.14  tff(c_9319, plain, (~v4_lattices('#skF_10')), inference(splitLeft, [status(thm)], [c_6838])).
% 11.78/4.14  tff(c_9322, plain, (~v10_lattices('#skF_10') | v2_struct_0('#skF_10') | ~l3_lattices('#skF_10')), inference(resolution, [status(thm)], [c_28, c_9319])).
% 11.78/4.14  tff(c_9325, plain, (v2_struct_0('#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_100, c_104, c_9322])).
% 11.78/4.14  tff(c_9327, plain, $false, inference(negUnitSimplification, [status(thm)], [c_106, c_9325])).
% 11.78/4.14  tff(c_9330, plain, (![B_705]: (k15_lattice3('#skF_10', B_705)='#skF_11' | ~r1_lattices('#skF_10', '#skF_11', k15_lattice3('#skF_10', B_705)) | ~m1_subset_1(k15_lattice3('#skF_10', B_705), u1_struct_0('#skF_10')) | k2_lattices('#skF_10', '#skF_11', k15_lattice3('#skF_10', B_705))!=k15_lattice3('#skF_10', B_705))), inference(splitRight, [status(thm)], [c_6838])).
% 11.78/4.14  tff(c_9334, plain, (![B_126]: (k15_lattice3('#skF_10', B_126)='#skF_11' | ~r1_lattices('#skF_10', '#skF_11', k15_lattice3('#skF_10', B_126)) | k2_lattices('#skF_10', '#skF_11', k15_lattice3('#skF_10', B_126))!=k15_lattice3('#skF_10', B_126) | ~l3_lattices('#skF_10') | v2_struct_0('#skF_10'))), inference(resolution, [status(thm)], [c_92, c_9330])).
% 11.78/4.14  tff(c_9337, plain, (![B_126]: (k15_lattice3('#skF_10', B_126)='#skF_11' | ~r1_lattices('#skF_10', '#skF_11', k15_lattice3('#skF_10', B_126)) | k2_lattices('#skF_10', '#skF_11', k15_lattice3('#skF_10', B_126))!=k15_lattice3('#skF_10', B_126) | v2_struct_0('#skF_10'))), inference(demodulation, [status(thm), theory('equality')], [c_100, c_9334])).
% 11.78/4.14  tff(c_9339, plain, (![B_706]: (k15_lattice3('#skF_10', B_706)='#skF_11' | ~r1_lattices('#skF_10', '#skF_11', k15_lattice3('#skF_10', B_706)) | k2_lattices('#skF_10', '#skF_11', k15_lattice3('#skF_10', B_706))!=k15_lattice3('#skF_10', B_706))), inference(negUnitSimplification, [status(thm)], [c_106, c_9337])).
% 11.78/4.14  tff(c_9343, plain, (k15_lattice3('#skF_10', k1_tarski('#skF_11'))='#skF_11' | k2_lattices('#skF_10', '#skF_11', k15_lattice3('#skF_10', k1_tarski('#skF_11')))!=k15_lattice3('#skF_10', k1_tarski('#skF_11')) | ~m1_subset_1('#skF_11', u1_struct_0('#skF_10')) | ~v4_lattice3('#skF_10') | ~v10_lattices('#skF_10') | ~l3_lattices('#skF_10') | v2_struct_0('#skF_10')), inference(resolution, [status(thm)], [c_8504, c_9339])).
% 11.78/4.14  tff(c_9350, plain, (k15_lattice3('#skF_10', k1_tarski('#skF_11'))='#skF_11' | k2_lattices('#skF_10', '#skF_11', k15_lattice3('#skF_10', k1_tarski('#skF_11')))!=k15_lattice3('#skF_10', k1_tarski('#skF_11')) | v2_struct_0('#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_100, c_104, c_102, c_98, c_9343])).
% 11.78/4.14  tff(c_9351, plain, (k2_lattices('#skF_10', '#skF_11', k15_lattice3('#skF_10', k1_tarski('#skF_11')))!=k15_lattice3('#skF_10', k1_tarski('#skF_11'))), inference(negUnitSimplification, [status(thm)], [c_106, c_158, c_9350])).
% 11.78/4.14  tff(c_8505, plain, (![A_668, C_669]: (r1_lattices(A_668, C_669, k15_lattice3(A_668, k1_tarski(C_669))) | ~m1_subset_1(C_669, u1_struct_0(A_668)) | ~v4_lattice3(A_668) | ~v10_lattices(A_668) | ~l3_lattices(A_668) | v2_struct_0(A_668))), inference(resolution, [status(thm)], [c_92, c_8500])).
% 11.78/4.14  tff(c_52, plain, (![A_29, B_33, C_35]: (k2_lattices(A_29, B_33, C_35)=B_33 | ~r1_lattices(A_29, B_33, C_35) | ~m1_subset_1(C_35, u1_struct_0(A_29)) | ~m1_subset_1(B_33, u1_struct_0(A_29)) | ~l3_lattices(A_29) | ~v9_lattices(A_29) | ~v8_lattices(A_29) | v2_struct_0(A_29))), inference(cnfTransformation, [status(thm)], [f_142])).
% 11.78/4.14  tff(c_10524, plain, (![A_757, C_758]: (k2_lattices(A_757, C_758, k15_lattice3(A_757, k1_tarski(C_758)))=C_758 | ~m1_subset_1(k15_lattice3(A_757, k1_tarski(C_758)), u1_struct_0(A_757)) | ~v9_lattices(A_757) | ~v8_lattices(A_757) | ~m1_subset_1(C_758, u1_struct_0(A_757)) | ~v4_lattice3(A_757) | ~v10_lattices(A_757) | ~l3_lattices(A_757) | v2_struct_0(A_757))), inference(resolution, [status(thm)], [c_8505, c_52])).
% 11.78/4.14  tff(c_10533, plain, (![A_759, C_760]: (k2_lattices(A_759, C_760, k15_lattice3(A_759, k1_tarski(C_760)))=C_760 | ~v9_lattices(A_759) | ~v8_lattices(A_759) | ~m1_subset_1(C_760, u1_struct_0(A_759)) | ~v4_lattice3(A_759) | ~v10_lattices(A_759) | ~l3_lattices(A_759) | v2_struct_0(A_759))), inference(resolution, [status(thm)], [c_92, c_10524])).
% 11.78/4.14  tff(c_22, plain, (![A_9]: (v7_lattices(A_9) | ~v10_lattices(A_9) | v2_struct_0(A_9) | ~l3_lattices(A_9))), inference(cnfTransformation, [status(thm)], [f_69])).
% 11.78/4.14  tff(c_350, plain, (k1_lattices('#skF_10', '#skF_11', '#skF_11')='#skF_11'), inference(splitRight, [status(thm)], [c_339])).
% 11.78/4.14  tff(c_473, plain, (![A_216, B_217, C_218]: (k2_lattices(A_216, B_217, k1_lattices(A_216, B_217, C_218))=B_217 | ~m1_subset_1(C_218, u1_struct_0(A_216)) | ~m1_subset_1(B_217, u1_struct_0(A_216)) | ~v9_lattices(A_216) | ~l3_lattices(A_216) | v2_struct_0(A_216))), inference(cnfTransformation, [status(thm)], [f_84])).
% 11.78/4.14  tff(c_489, plain, (![B_217]: (k2_lattices('#skF_10', B_217, k1_lattices('#skF_10', B_217, '#skF_11'))=B_217 | ~m1_subset_1(B_217, u1_struct_0('#skF_10')) | ~v9_lattices('#skF_10') | ~l3_lattices('#skF_10') | v2_struct_0('#skF_10'))), inference(resolution, [status(thm)], [c_98, c_473])).
% 11.78/4.14  tff(c_499, plain, (![B_217]: (k2_lattices('#skF_10', B_217, k1_lattices('#skF_10', B_217, '#skF_11'))=B_217 | ~m1_subset_1(B_217, u1_struct_0('#skF_10')) | v2_struct_0('#skF_10'))), inference(demodulation, [status(thm), theory('equality')], [c_100, c_340, c_489])).
% 11.78/4.14  tff(c_501, plain, (![B_219]: (k2_lattices('#skF_10', B_219, k1_lattices('#skF_10', B_219, '#skF_11'))=B_219 | ~m1_subset_1(B_219, u1_struct_0('#skF_10')))), inference(negUnitSimplification, [status(thm)], [c_106, c_499])).
% 11.78/4.14  tff(c_524, plain, (k2_lattices('#skF_10', '#skF_11', k1_lattices('#skF_10', '#skF_11', '#skF_11'))='#skF_11'), inference(resolution, [status(thm)], [c_98, c_501])).
% 11.78/4.14  tff(c_554, plain, (k2_lattices('#skF_10', '#skF_11', '#skF_11')='#skF_11'), inference(demodulation, [status(thm), theory('equality')], [c_350, c_524])).
% 11.78/4.14  tff(c_8581, plain, (![A_673, B_674, D_675, C_676]: (r1_lattices(A_673, k2_lattices(A_673, B_674, D_675), k2_lattices(A_673, C_676, D_675)) | ~r1_lattices(A_673, B_674, C_676) | ~m1_subset_1(D_675, u1_struct_0(A_673)) | ~m1_subset_1(C_676, u1_struct_0(A_673)) | ~m1_subset_1(B_674, u1_struct_0(A_673)) | ~l3_lattices(A_673) | ~v9_lattices(A_673) | ~v8_lattices(A_673) | ~v7_lattices(A_673) | v2_struct_0(A_673))), inference(cnfTransformation, [status(thm)], [f_185])).
% 11.78/4.14  tff(c_8708, plain, (![C_676]: (r1_lattices('#skF_10', '#skF_11', k2_lattices('#skF_10', C_676, '#skF_11')) | ~r1_lattices('#skF_10', '#skF_11', C_676) | ~m1_subset_1('#skF_11', u1_struct_0('#skF_10')) | ~m1_subset_1(C_676, u1_struct_0('#skF_10')) | ~m1_subset_1('#skF_11', u1_struct_0('#skF_10')) | ~l3_lattices('#skF_10') | ~v9_lattices('#skF_10') | ~v8_lattices('#skF_10') | ~v7_lattices('#skF_10') | v2_struct_0('#skF_10'))), inference(superposition, [status(thm), theory('equality')], [c_554, c_8581])).
% 11.78/4.14  tff(c_8793, plain, (![C_676]: (r1_lattices('#skF_10', '#skF_11', k2_lattices('#skF_10', C_676, '#skF_11')) | ~r1_lattices('#skF_10', '#skF_11', C_676) | ~m1_subset_1(C_676, u1_struct_0('#skF_10')) | ~v7_lattices('#skF_10') | v2_struct_0('#skF_10'))), inference(demodulation, [status(thm), theory('equality')], [c_351, c_340, c_100, c_98, c_98, c_8708])).
% 11.78/4.14  tff(c_8794, plain, (![C_676]: (r1_lattices('#skF_10', '#skF_11', k2_lattices('#skF_10', C_676, '#skF_11')) | ~r1_lattices('#skF_10', '#skF_11', C_676) | ~m1_subset_1(C_676, u1_struct_0('#skF_10')) | ~v7_lattices('#skF_10'))), inference(negUnitSimplification, [status(thm)], [c_106, c_8793])).
% 11.78/4.14  tff(c_8804, plain, (~v7_lattices('#skF_10')), inference(splitLeft, [status(thm)], [c_8794])).
% 11.78/4.14  tff(c_8807, plain, (~v10_lattices('#skF_10') | v2_struct_0('#skF_10') | ~l3_lattices('#skF_10')), inference(resolution, [status(thm)], [c_22, c_8804])).
% 11.78/4.14  tff(c_8810, plain, (v2_struct_0('#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_100, c_104, c_8807])).
% 11.78/4.14  tff(c_8812, plain, $false, inference(negUnitSimplification, [status(thm)], [c_106, c_8810])).
% 11.78/4.14  tff(c_8814, plain, (v7_lattices('#skF_10')), inference(splitRight, [status(thm)], [c_8794])).
% 11.78/4.14  tff(c_8714, plain, (![B_126, C_676]: (r1_lattices('#skF_10', k2_lattices('#skF_10', '#skF_11', k15_lattice3('#skF_10', B_126)), k2_lattices('#skF_10', C_676, '#skF_11')) | ~r1_lattices('#skF_10', k15_lattice3('#skF_10', B_126), C_676) | ~m1_subset_1('#skF_11', u1_struct_0('#skF_10')) | ~m1_subset_1(C_676, u1_struct_0('#skF_10')) | ~m1_subset_1(k15_lattice3('#skF_10', B_126), u1_struct_0('#skF_10')) | ~l3_lattices('#skF_10') | ~v9_lattices('#skF_10') | ~v8_lattices('#skF_10') | ~v7_lattices('#skF_10') | v2_struct_0('#skF_10'))), inference(superposition, [status(thm), theory('equality')], [c_461, c_8581])).
% 11.78/4.14  tff(c_8799, plain, (![B_126, C_676]: (r1_lattices('#skF_10', k2_lattices('#skF_10', '#skF_11', k15_lattice3('#skF_10', B_126)), k2_lattices('#skF_10', C_676, '#skF_11')) | ~r1_lattices('#skF_10', k15_lattice3('#skF_10', B_126), C_676) | ~m1_subset_1(C_676, u1_struct_0('#skF_10')) | ~m1_subset_1(k15_lattice3('#skF_10', B_126), u1_struct_0('#skF_10')) | ~v7_lattices('#skF_10') | v2_struct_0('#skF_10'))), inference(demodulation, [status(thm), theory('equality')], [c_351, c_340, c_100, c_98, c_8714])).
% 11.78/4.14  tff(c_8800, plain, (![B_126, C_676]: (r1_lattices('#skF_10', k2_lattices('#skF_10', '#skF_11', k15_lattice3('#skF_10', B_126)), k2_lattices('#skF_10', C_676, '#skF_11')) | ~r1_lattices('#skF_10', k15_lattice3('#skF_10', B_126), C_676) | ~m1_subset_1(C_676, u1_struct_0('#skF_10')) | ~m1_subset_1(k15_lattice3('#skF_10', B_126), u1_struct_0('#skF_10')) | ~v7_lattices('#skF_10'))), inference(negUnitSimplification, [status(thm)], [c_106, c_8799])).
% 11.78/4.14  tff(c_10364, plain, (![B_126, C_676]: (r1_lattices('#skF_10', k2_lattices('#skF_10', '#skF_11', k15_lattice3('#skF_10', B_126)), k2_lattices('#skF_10', C_676, '#skF_11')) | ~r1_lattices('#skF_10', k15_lattice3('#skF_10', B_126), C_676) | ~m1_subset_1(C_676, u1_struct_0('#skF_10')) | ~m1_subset_1(k15_lattice3('#skF_10', B_126), u1_struct_0('#skF_10')))), inference(demodulation, [status(thm), theory('equality')], [c_8814, c_8800])).
% 11.78/4.14  tff(c_10540, plain, (![C_676]: (r1_lattices('#skF_10', '#skF_11', k2_lattices('#skF_10', C_676, '#skF_11')) | ~r1_lattices('#skF_10', k15_lattice3('#skF_10', k1_tarski('#skF_11')), C_676) | ~m1_subset_1(C_676, u1_struct_0('#skF_10')) | ~m1_subset_1(k15_lattice3('#skF_10', k1_tarski('#skF_11')), u1_struct_0('#skF_10')) | ~v9_lattices('#skF_10') | ~v8_lattices('#skF_10') | ~m1_subset_1('#skF_11', u1_struct_0('#skF_10')) | ~v4_lattice3('#skF_10') | ~v10_lattices('#skF_10') | ~l3_lattices('#skF_10') | v2_struct_0('#skF_10'))), inference(superposition, [status(thm), theory('equality')], [c_10533, c_10364])).
% 11.78/4.14  tff(c_10577, plain, (![C_676]: (r1_lattices('#skF_10', '#skF_11', k2_lattices('#skF_10', C_676, '#skF_11')) | ~r1_lattices('#skF_10', k15_lattice3('#skF_10', k1_tarski('#skF_11')), C_676) | ~m1_subset_1(C_676, u1_struct_0('#skF_10')) | ~m1_subset_1(k15_lattice3('#skF_10', k1_tarski('#skF_11')), u1_struct_0('#skF_10')) | v2_struct_0('#skF_10'))), inference(demodulation, [status(thm), theory('equality')], [c_100, c_104, c_102, c_98, c_351, c_340, c_10540])).
% 11.78/4.14  tff(c_10578, plain, (![C_676]: (r1_lattices('#skF_10', '#skF_11', k2_lattices('#skF_10', C_676, '#skF_11')) | ~r1_lattices('#skF_10', k15_lattice3('#skF_10', k1_tarski('#skF_11')), C_676) | ~m1_subset_1(C_676, u1_struct_0('#skF_10')) | ~m1_subset_1(k15_lattice3('#skF_10', k1_tarski('#skF_11')), u1_struct_0('#skF_10')))), inference(negUnitSimplification, [status(thm)], [c_106, c_10577])).
% 11.78/4.14  tff(c_10595, plain, (~m1_subset_1(k15_lattice3('#skF_10', k1_tarski('#skF_11')), u1_struct_0('#skF_10'))), inference(splitLeft, [status(thm)], [c_10578])).
% 11.78/4.14  tff(c_10599, plain, (~l3_lattices('#skF_10') | v2_struct_0('#skF_10')), inference(resolution, [status(thm)], [c_92, c_10595])).
% 11.78/4.14  tff(c_10602, plain, (v2_struct_0('#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_100, c_10599])).
% 11.78/4.14  tff(c_10604, plain, $false, inference(negUnitSimplification, [status(thm)], [c_106, c_10602])).
% 11.78/4.14  tff(c_10606, plain, (m1_subset_1(k15_lattice3('#skF_10', k1_tarski('#skF_11')), u1_struct_0('#skF_10'))), inference(splitRight, [status(thm)], [c_10578])).
% 11.78/4.14  tff(c_273, plain, (![A_178, B_179, C_180]: (r2_hidden('#skF_6'(A_178, B_179, C_180), C_180) | r4_lattice3(A_178, B_179, C_180) | ~m1_subset_1(B_179, u1_struct_0(A_178)) | ~l3_lattices(A_178) | v2_struct_0(A_178))), inference(cnfTransformation, [status(thm)], [f_221])).
% 11.78/4.14  tff(c_2, plain, (![C_5, A_1]: (C_5=A_1 | ~r2_hidden(C_5, k1_tarski(A_1)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 11.78/4.14  tff(c_278, plain, (![A_178, B_179, A_1]: ('#skF_6'(A_178, B_179, k1_tarski(A_1))=A_1 | r4_lattice3(A_178, B_179, k1_tarski(A_1)) | ~m1_subset_1(B_179, u1_struct_0(A_178)) | ~l3_lattices(A_178) | v2_struct_0(A_178))), inference(resolution, [status(thm)], [c_273, c_2])).
% 11.78/4.14  tff(c_961, plain, (![A_251, A_252, B_253]: (r1_lattices(A_251, A_252, B_253) | ~m1_subset_1(A_252, u1_struct_0(A_251)) | '#skF_6'(A_251, B_253, k1_tarski(A_252))=A_252 | ~m1_subset_1(B_253, u1_struct_0(A_251)) | ~l3_lattices(A_251) | v2_struct_0(A_251))), inference(resolution, [status(thm)], [c_278, c_951])).
% 11.78/4.14  tff(c_977, plain, (![B_253]: (r1_lattices('#skF_10', '#skF_11', B_253) | '#skF_6'('#skF_10', B_253, k1_tarski('#skF_11'))='#skF_11' | ~m1_subset_1(B_253, u1_struct_0('#skF_10')) | ~l3_lattices('#skF_10') | v2_struct_0('#skF_10'))), inference(resolution, [status(thm)], [c_98, c_961])).
% 11.78/4.14  tff(c_987, plain, (![B_253]: (r1_lattices('#skF_10', '#skF_11', B_253) | '#skF_6'('#skF_10', B_253, k1_tarski('#skF_11'))='#skF_11' | ~m1_subset_1(B_253, u1_struct_0('#skF_10')) | v2_struct_0('#skF_10'))), inference(demodulation, [status(thm), theory('equality')], [c_100, c_977])).
% 11.78/4.14  tff(c_989, plain, (![B_254]: (r1_lattices('#skF_10', '#skF_11', B_254) | '#skF_6'('#skF_10', B_254, k1_tarski('#skF_11'))='#skF_11' | ~m1_subset_1(B_254, u1_struct_0('#skF_10')))), inference(negUnitSimplification, [status(thm)], [c_106, c_987])).
% 11.78/4.14  tff(c_1049, plain, (r1_lattices('#skF_10', '#skF_11', '#skF_11') | '#skF_6'('#skF_10', '#skF_11', k1_tarski('#skF_11'))='#skF_11'), inference(resolution, [status(thm)], [c_98, c_989])).
% 11.78/4.14  tff(c_1050, plain, ('#skF_6'('#skF_10', '#skF_11', k1_tarski('#skF_11'))='#skF_11'), inference(splitLeft, [status(thm)], [c_1049])).
% 11.78/4.14  tff(c_68, plain, (![A_80, B_92, C_98]: (~r1_lattices(A_80, '#skF_6'(A_80, B_92, C_98), B_92) | r4_lattice3(A_80, B_92, C_98) | ~m1_subset_1(B_92, u1_struct_0(A_80)) | ~l3_lattices(A_80) | v2_struct_0(A_80))), inference(cnfTransformation, [status(thm)], [f_221])).
% 11.78/4.14  tff(c_1076, plain, (~r1_lattices('#skF_10', '#skF_11', '#skF_11') | r4_lattice3('#skF_10', '#skF_11', k1_tarski('#skF_11')) | ~m1_subset_1('#skF_11', u1_struct_0('#skF_10')) | ~l3_lattices('#skF_10') | v2_struct_0('#skF_10')), inference(superposition, [status(thm), theory('equality')], [c_1050, c_68])).
% 11.78/4.14  tff(c_1088, plain, (~r1_lattices('#skF_10', '#skF_11', '#skF_11') | r4_lattice3('#skF_10', '#skF_11', k1_tarski('#skF_11')) | v2_struct_0('#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_100, c_98, c_1076])).
% 11.78/4.14  tff(c_1089, plain, (~r1_lattices('#skF_10', '#skF_11', '#skF_11') | r4_lattice3('#skF_10', '#skF_11', k1_tarski('#skF_11'))), inference(negUnitSimplification, [status(thm)], [c_106, c_1088])).
% 11.78/4.14  tff(c_1097, plain, (~r1_lattices('#skF_10', '#skF_11', '#skF_11')), inference(splitLeft, [status(thm)], [c_1089])).
% 11.78/4.14  tff(c_1493, plain, (![A_288, B_289, C_290]: (r1_lattices(A_288, B_289, C_290) | k2_lattices(A_288, B_289, C_290)!=B_289 | ~m1_subset_1(C_290, u1_struct_0(A_288)) | ~m1_subset_1(B_289, u1_struct_0(A_288)) | ~l3_lattices(A_288) | ~v9_lattices(A_288) | ~v8_lattices(A_288) | v2_struct_0(A_288))), inference(cnfTransformation, [status(thm)], [f_142])).
% 11.78/4.14  tff(c_1509, plain, (![B_289]: (r1_lattices('#skF_10', B_289, '#skF_11') | k2_lattices('#skF_10', B_289, '#skF_11')!=B_289 | ~m1_subset_1(B_289, u1_struct_0('#skF_10')) | ~l3_lattices('#skF_10') | ~v9_lattices('#skF_10') | ~v8_lattices('#skF_10') | v2_struct_0('#skF_10'))), inference(resolution, [status(thm)], [c_98, c_1493])).
% 11.78/4.14  tff(c_1519, plain, (![B_289]: (r1_lattices('#skF_10', B_289, '#skF_11') | k2_lattices('#skF_10', B_289, '#skF_11')!=B_289 | ~m1_subset_1(B_289, u1_struct_0('#skF_10')) | v2_struct_0('#skF_10'))), inference(demodulation, [status(thm), theory('equality')], [c_351, c_340, c_100, c_1509])).
% 11.78/4.14  tff(c_1521, plain, (![B_291]: (r1_lattices('#skF_10', B_291, '#skF_11') | k2_lattices('#skF_10', B_291, '#skF_11')!=B_291 | ~m1_subset_1(B_291, u1_struct_0('#skF_10')))), inference(negUnitSimplification, [status(thm)], [c_106, c_1519])).
% 11.78/4.14  tff(c_1552, plain, (r1_lattices('#skF_10', '#skF_11', '#skF_11') | k2_lattices('#skF_10', '#skF_11', '#skF_11')!='#skF_11'), inference(resolution, [status(thm)], [c_98, c_1521])).
% 11.78/4.14  tff(c_1583, plain, (r1_lattices('#skF_10', '#skF_11', '#skF_11')), inference(demodulation, [status(thm), theory('equality')], [c_554, c_1552])).
% 11.78/4.14  tff(c_1585, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1097, c_1583])).
% 11.78/4.14  tff(c_1586, plain, (r4_lattice3('#skF_10', '#skF_11', k1_tarski('#skF_11'))), inference(splitRight, [status(thm)], [c_1089])).
% 11.78/4.14  tff(c_3662, plain, (![A_418, B_419, D_420]: (r1_lattices(A_418, k15_lattice3(A_418, B_419), D_420) | ~r4_lattice3(A_418, D_420, B_419) | ~m1_subset_1(D_420, u1_struct_0(A_418)) | ~m1_subset_1(k15_lattice3(A_418, B_419), u1_struct_0(A_418)) | ~v4_lattice3(A_418) | ~v10_lattices(A_418) | ~l3_lattices(A_418) | v2_struct_0(A_418))), inference(cnfTransformation, [status(thm)], [f_249])).
% 11.78/4.14  tff(c_3665, plain, (![A_125, B_126, D_420]: (r1_lattices(A_125, k15_lattice3(A_125, B_126), D_420) | ~r4_lattice3(A_125, D_420, B_126) | ~m1_subset_1(D_420, u1_struct_0(A_125)) | ~v4_lattice3(A_125) | ~v10_lattices(A_125) | ~l3_lattices(A_125) | v2_struct_0(A_125))), inference(resolution, [status(thm)], [c_92, c_3662])).
% 11.78/4.14  tff(c_1975, plain, (![A_322, B_323, C_324]: (r1_lattices(A_322, B_323, C_324) | k2_lattices(A_322, B_323, C_324)!=B_323 | ~m1_subset_1(C_324, u1_struct_0(A_322)) | ~m1_subset_1(B_323, u1_struct_0(A_322)) | ~l3_lattices(A_322) | ~v9_lattices(A_322) | ~v8_lattices(A_322) | v2_struct_0(A_322))), inference(cnfTransformation, [status(thm)], [f_142])).
% 11.78/4.14  tff(c_1991, plain, (![B_323]: (r1_lattices('#skF_10', B_323, '#skF_11') | k2_lattices('#skF_10', B_323, '#skF_11')!=B_323 | ~m1_subset_1(B_323, u1_struct_0('#skF_10')) | ~l3_lattices('#skF_10') | ~v9_lattices('#skF_10') | ~v8_lattices('#skF_10') | v2_struct_0('#skF_10'))), inference(resolution, [status(thm)], [c_98, c_1975])).
% 11.78/4.14  tff(c_2001, plain, (![B_323]: (r1_lattices('#skF_10', B_323, '#skF_11') | k2_lattices('#skF_10', B_323, '#skF_11')!=B_323 | ~m1_subset_1(B_323, u1_struct_0('#skF_10')) | v2_struct_0('#skF_10'))), inference(demodulation, [status(thm), theory('equality')], [c_351, c_340, c_100, c_1991])).
% 11.78/4.14  tff(c_2003, plain, (![B_325]: (r1_lattices('#skF_10', B_325, '#skF_11') | k2_lattices('#skF_10', B_325, '#skF_11')!=B_325 | ~m1_subset_1(B_325, u1_struct_0('#skF_10')))), inference(negUnitSimplification, [status(thm)], [c_106, c_2001])).
% 11.78/4.14  tff(c_2031, plain, (![B_126]: (r1_lattices('#skF_10', k15_lattice3('#skF_10', B_126), '#skF_11') | k2_lattices('#skF_10', k15_lattice3('#skF_10', B_126), '#skF_11')!=k15_lattice3('#skF_10', B_126) | ~l3_lattices('#skF_10') | v2_struct_0('#skF_10'))), inference(resolution, [status(thm)], [c_92, c_2003])).
% 11.78/4.14  tff(c_2061, plain, (![B_126]: (r1_lattices('#skF_10', k15_lattice3('#skF_10', B_126), '#skF_11') | k2_lattices('#skF_10', '#skF_11', k15_lattice3('#skF_10', B_126))!=k15_lattice3('#skF_10', B_126) | v2_struct_0('#skF_10'))), inference(demodulation, [status(thm), theory('equality')], [c_100, c_461, c_2031])).
% 11.78/4.14  tff(c_2066, plain, (![B_326]: (r1_lattices('#skF_10', k15_lattice3('#skF_10', B_326), '#skF_11') | k2_lattices('#skF_10', '#skF_11', k15_lattice3('#skF_10', B_326))!=k15_lattice3('#skF_10', B_326))), inference(negUnitSimplification, [status(thm)], [c_106, c_2061])).
% 11.78/4.14  tff(c_2068, plain, (![B_326]: (k15_lattice3('#skF_10', B_326)='#skF_11' | ~r1_lattices('#skF_10', '#skF_11', k15_lattice3('#skF_10', B_326)) | ~m1_subset_1(k15_lattice3('#skF_10', B_326), u1_struct_0('#skF_10')) | ~m1_subset_1('#skF_11', u1_struct_0('#skF_10')) | ~l2_lattices('#skF_10') | ~v4_lattices('#skF_10') | v2_struct_0('#skF_10') | k2_lattices('#skF_10', '#skF_11', k15_lattice3('#skF_10', B_326))!=k15_lattice3('#skF_10', B_326))), inference(resolution, [status(thm)], [c_2066, c_54])).
% 11.78/4.14  tff(c_2071, plain, (![B_326]: (k15_lattice3('#skF_10', B_326)='#skF_11' | ~r1_lattices('#skF_10', '#skF_11', k15_lattice3('#skF_10', B_326)) | ~m1_subset_1(k15_lattice3('#skF_10', B_326), u1_struct_0('#skF_10')) | ~v4_lattices('#skF_10') | v2_struct_0('#skF_10') | k2_lattices('#skF_10', '#skF_11', k15_lattice3('#skF_10', B_326))!=k15_lattice3('#skF_10', B_326))), inference(demodulation, [status(thm), theory('equality')], [c_118, c_98, c_2068])).
% 11.78/4.14  tff(c_2072, plain, (![B_326]: (k15_lattice3('#skF_10', B_326)='#skF_11' | ~r1_lattices('#skF_10', '#skF_11', k15_lattice3('#skF_10', B_326)) | ~m1_subset_1(k15_lattice3('#skF_10', B_326), u1_struct_0('#skF_10')) | ~v4_lattices('#skF_10') | k2_lattices('#skF_10', '#skF_11', k15_lattice3('#skF_10', B_326))!=k15_lattice3('#skF_10', B_326))), inference(negUnitSimplification, [status(thm)], [c_106, c_2071])).
% 11.78/4.14  tff(c_4332, plain, (~v4_lattices('#skF_10')), inference(splitLeft, [status(thm)], [c_2072])).
% 11.78/4.14  tff(c_4335, plain, (~v10_lattices('#skF_10') | v2_struct_0('#skF_10') | ~l3_lattices('#skF_10')), inference(resolution, [status(thm)], [c_28, c_4332])).
% 11.78/4.14  tff(c_4338, plain, (v2_struct_0('#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_100, c_104, c_4335])).
% 11.78/4.14  tff(c_4340, plain, $false, inference(negUnitSimplification, [status(thm)], [c_106, c_4338])).
% 11.78/4.14  tff(c_4342, plain, (v4_lattices('#skF_10')), inference(splitRight, [status(thm)], [c_2072])).
% 11.78/4.14  tff(c_3821, plain, (![A_430, C_431]: (r1_lattices(A_430, C_431, k15_lattice3(A_430, k1_tarski(C_431))) | ~m1_subset_1(C_431, u1_struct_0(A_430)) | ~m1_subset_1(k15_lattice3(A_430, k1_tarski(C_431)), u1_struct_0(A_430)) | ~v4_lattice3(A_430) | ~v10_lattices(A_430) | ~l3_lattices(A_430) | v2_struct_0(A_430))), inference(resolution, [status(thm)], [c_362, c_951])).
% 11.78/4.14  tff(c_3826, plain, (![A_432, C_433]: (r1_lattices(A_432, C_433, k15_lattice3(A_432, k1_tarski(C_433))) | ~m1_subset_1(C_433, u1_struct_0(A_432)) | ~v4_lattice3(A_432) | ~v10_lattices(A_432) | ~l3_lattices(A_432) | v2_struct_0(A_432))), inference(resolution, [status(thm)], [c_92, c_3821])).
% 11.78/4.14  tff(c_5654, plain, (![A_513, C_514]: (k2_lattices(A_513, C_514, k15_lattice3(A_513, k1_tarski(C_514)))=C_514 | ~m1_subset_1(k15_lattice3(A_513, k1_tarski(C_514)), u1_struct_0(A_513)) | ~v9_lattices(A_513) | ~v8_lattices(A_513) | ~m1_subset_1(C_514, u1_struct_0(A_513)) | ~v4_lattice3(A_513) | ~v10_lattices(A_513) | ~l3_lattices(A_513) | v2_struct_0(A_513))), inference(resolution, [status(thm)], [c_3826, c_52])).
% 11.78/4.14  tff(c_5663, plain, (![A_515, C_516]: (k2_lattices(A_515, C_516, k15_lattice3(A_515, k1_tarski(C_516)))=C_516 | ~v9_lattices(A_515) | ~v8_lattices(A_515) | ~m1_subset_1(C_516, u1_struct_0(A_515)) | ~v4_lattice3(A_515) | ~v10_lattices(A_515) | ~l3_lattices(A_515) | v2_struct_0(A_515))), inference(resolution, [status(thm)], [c_92, c_5654])).
% 11.78/4.14  tff(c_3850, plain, (![A_436, B_437, D_438, C_439]: (r1_lattices(A_436, k2_lattices(A_436, B_437, D_438), k2_lattices(A_436, C_439, D_438)) | ~r1_lattices(A_436, B_437, C_439) | ~m1_subset_1(D_438, u1_struct_0(A_436)) | ~m1_subset_1(C_439, u1_struct_0(A_436)) | ~m1_subset_1(B_437, u1_struct_0(A_436)) | ~l3_lattices(A_436) | ~v9_lattices(A_436) | ~v8_lattices(A_436) | ~v7_lattices(A_436) | v2_struct_0(A_436))), inference(cnfTransformation, [status(thm)], [f_185])).
% 11.78/4.14  tff(c_3977, plain, (![C_439]: (r1_lattices('#skF_10', '#skF_11', k2_lattices('#skF_10', C_439, '#skF_11')) | ~r1_lattices('#skF_10', '#skF_11', C_439) | ~m1_subset_1('#skF_11', u1_struct_0('#skF_10')) | ~m1_subset_1(C_439, u1_struct_0('#skF_10')) | ~m1_subset_1('#skF_11', u1_struct_0('#skF_10')) | ~l3_lattices('#skF_10') | ~v9_lattices('#skF_10') | ~v8_lattices('#skF_10') | ~v7_lattices('#skF_10') | v2_struct_0('#skF_10'))), inference(superposition, [status(thm), theory('equality')], [c_554, c_3850])).
% 11.78/4.14  tff(c_4062, plain, (![C_439]: (r1_lattices('#skF_10', '#skF_11', k2_lattices('#skF_10', C_439, '#skF_11')) | ~r1_lattices('#skF_10', '#skF_11', C_439) | ~m1_subset_1(C_439, u1_struct_0('#skF_10')) | ~v7_lattices('#skF_10') | v2_struct_0('#skF_10'))), inference(demodulation, [status(thm), theory('equality')], [c_351, c_340, c_100, c_98, c_98, c_3977])).
% 11.78/4.14  tff(c_4063, plain, (![C_439]: (r1_lattices('#skF_10', '#skF_11', k2_lattices('#skF_10', C_439, '#skF_11')) | ~r1_lattices('#skF_10', '#skF_11', C_439) | ~m1_subset_1(C_439, u1_struct_0('#skF_10')) | ~v7_lattices('#skF_10'))), inference(negUnitSimplification, [status(thm)], [c_106, c_4062])).
% 11.78/4.14  tff(c_4073, plain, (~v7_lattices('#skF_10')), inference(splitLeft, [status(thm)], [c_4063])).
% 11.78/4.14  tff(c_4076, plain, (~v10_lattices('#skF_10') | v2_struct_0('#skF_10') | ~l3_lattices('#skF_10')), inference(resolution, [status(thm)], [c_22, c_4073])).
% 11.78/4.14  tff(c_4079, plain, (v2_struct_0('#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_100, c_104, c_4076])).
% 11.78/4.14  tff(c_4081, plain, $false, inference(negUnitSimplification, [status(thm)], [c_106, c_4079])).
% 11.78/4.14  tff(c_4083, plain, (v7_lattices('#skF_10')), inference(splitRight, [status(thm)], [c_4063])).
% 11.78/4.14  tff(c_3986, plain, (![B_437, B_126]: (r1_lattices('#skF_10', k2_lattices('#skF_10', B_437, '#skF_11'), k2_lattices('#skF_10', '#skF_11', k15_lattice3('#skF_10', B_126))) | ~r1_lattices('#skF_10', B_437, k15_lattice3('#skF_10', B_126)) | ~m1_subset_1('#skF_11', u1_struct_0('#skF_10')) | ~m1_subset_1(k15_lattice3('#skF_10', B_126), u1_struct_0('#skF_10')) | ~m1_subset_1(B_437, u1_struct_0('#skF_10')) | ~l3_lattices('#skF_10') | ~v9_lattices('#skF_10') | ~v8_lattices('#skF_10') | ~v7_lattices('#skF_10') | v2_struct_0('#skF_10'))), inference(superposition, [status(thm), theory('equality')], [c_461, c_3850])).
% 11.78/4.14  tff(c_4071, plain, (![B_437, B_126]: (r1_lattices('#skF_10', k2_lattices('#skF_10', B_437, '#skF_11'), k2_lattices('#skF_10', '#skF_11', k15_lattice3('#skF_10', B_126))) | ~r1_lattices('#skF_10', B_437, k15_lattice3('#skF_10', B_126)) | ~m1_subset_1(k15_lattice3('#skF_10', B_126), u1_struct_0('#skF_10')) | ~m1_subset_1(B_437, u1_struct_0('#skF_10')) | ~v7_lattices('#skF_10') | v2_struct_0('#skF_10'))), inference(demodulation, [status(thm), theory('equality')], [c_351, c_340, c_100, c_98, c_3986])).
% 11.78/4.14  tff(c_4072, plain, (![B_437, B_126]: (r1_lattices('#skF_10', k2_lattices('#skF_10', B_437, '#skF_11'), k2_lattices('#skF_10', '#skF_11', k15_lattice3('#skF_10', B_126))) | ~r1_lattices('#skF_10', B_437, k15_lattice3('#skF_10', B_126)) | ~m1_subset_1(k15_lattice3('#skF_10', B_126), u1_struct_0('#skF_10')) | ~m1_subset_1(B_437, u1_struct_0('#skF_10')) | ~v7_lattices('#skF_10'))), inference(negUnitSimplification, [status(thm)], [c_106, c_4071])).
% 11.78/4.14  tff(c_5560, plain, (![B_437, B_126]: (r1_lattices('#skF_10', k2_lattices('#skF_10', B_437, '#skF_11'), k2_lattices('#skF_10', '#skF_11', k15_lattice3('#skF_10', B_126))) | ~r1_lattices('#skF_10', B_437, k15_lattice3('#skF_10', B_126)) | ~m1_subset_1(k15_lattice3('#skF_10', B_126), u1_struct_0('#skF_10')) | ~m1_subset_1(B_437, u1_struct_0('#skF_10')))), inference(demodulation, [status(thm), theory('equality')], [c_4083, c_4072])).
% 11.78/4.14  tff(c_5670, plain, (![B_437]: (r1_lattices('#skF_10', k2_lattices('#skF_10', B_437, '#skF_11'), '#skF_11') | ~r1_lattices('#skF_10', B_437, k15_lattice3('#skF_10', k1_tarski('#skF_11'))) | ~m1_subset_1(k15_lattice3('#skF_10', k1_tarski('#skF_11')), u1_struct_0('#skF_10')) | ~m1_subset_1(B_437, u1_struct_0('#skF_10')) | ~v9_lattices('#skF_10') | ~v8_lattices('#skF_10') | ~m1_subset_1('#skF_11', u1_struct_0('#skF_10')) | ~v4_lattice3('#skF_10') | ~v10_lattices('#skF_10') | ~l3_lattices('#skF_10') | v2_struct_0('#skF_10'))), inference(superposition, [status(thm), theory('equality')], [c_5663, c_5560])).
% 11.78/4.14  tff(c_5707, plain, (![B_437]: (r1_lattices('#skF_10', k2_lattices('#skF_10', B_437, '#skF_11'), '#skF_11') | ~r1_lattices('#skF_10', B_437, k15_lattice3('#skF_10', k1_tarski('#skF_11'))) | ~m1_subset_1(k15_lattice3('#skF_10', k1_tarski('#skF_11')), u1_struct_0('#skF_10')) | ~m1_subset_1(B_437, u1_struct_0('#skF_10')) | v2_struct_0('#skF_10'))), inference(demodulation, [status(thm), theory('equality')], [c_100, c_104, c_102, c_98, c_351, c_340, c_5670])).
% 11.78/4.14  tff(c_5708, plain, (![B_437]: (r1_lattices('#skF_10', k2_lattices('#skF_10', B_437, '#skF_11'), '#skF_11') | ~r1_lattices('#skF_10', B_437, k15_lattice3('#skF_10', k1_tarski('#skF_11'))) | ~m1_subset_1(k15_lattice3('#skF_10', k1_tarski('#skF_11')), u1_struct_0('#skF_10')) | ~m1_subset_1(B_437, u1_struct_0('#skF_10')))), inference(negUnitSimplification, [status(thm)], [c_106, c_5707])).
% 11.78/4.14  tff(c_5725, plain, (~m1_subset_1(k15_lattice3('#skF_10', k1_tarski('#skF_11')), u1_struct_0('#skF_10'))), inference(splitLeft, [status(thm)], [c_5708])).
% 11.78/4.14  tff(c_5728, plain, (~l3_lattices('#skF_10') | v2_struct_0('#skF_10')), inference(resolution, [status(thm)], [c_92, c_5725])).
% 11.78/4.14  tff(c_5731, plain, (v2_struct_0('#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_100, c_5728])).
% 11.78/4.14  tff(c_5733, plain, $false, inference(negUnitSimplification, [status(thm)], [c_106, c_5731])).
% 11.78/4.14  tff(c_5735, plain, (m1_subset_1(k15_lattice3('#skF_10', k1_tarski('#skF_11')), u1_struct_0('#skF_10'))), inference(splitRight, [status(thm)], [c_5708])).
% 11.78/4.14  tff(c_3825, plain, (![A_125, C_431]: (r1_lattices(A_125, C_431, k15_lattice3(A_125, k1_tarski(C_431))) | ~m1_subset_1(C_431, u1_struct_0(A_125)) | ~v4_lattice3(A_125) | ~v10_lattices(A_125) | ~l3_lattices(A_125) | v2_struct_0(A_125))), inference(resolution, [status(thm)], [c_92, c_3821])).
% 11.78/4.14  tff(c_84, plain, (![A_114, C_123, B_121]: (k2_lattices(A_114, C_123, B_121)=k2_lattices(A_114, B_121, C_123) | ~m1_subset_1(C_123, u1_struct_0(A_114)) | ~m1_subset_1(B_121, u1_struct_0(A_114)) | ~v6_lattices(A_114) | ~l1_lattices(A_114) | v2_struct_0(A_114))), inference(cnfTransformation, [status(thm)], [f_264])).
% 11.78/4.14  tff(c_5793, plain, (![B_121]: (k2_lattices('#skF_10', k15_lattice3('#skF_10', k1_tarski('#skF_11')), B_121)=k2_lattices('#skF_10', B_121, k15_lattice3('#skF_10', k1_tarski('#skF_11'))) | ~m1_subset_1(B_121, u1_struct_0('#skF_10')) | ~v6_lattices('#skF_10') | ~l1_lattices('#skF_10') | v2_struct_0('#skF_10'))), inference(resolution, [status(thm)], [c_5735, c_84])).
% 11.78/4.14  tff(c_5865, plain, (![B_121]: (k2_lattices('#skF_10', k15_lattice3('#skF_10', k1_tarski('#skF_11')), B_121)=k2_lattices('#skF_10', B_121, k15_lattice3('#skF_10', k1_tarski('#skF_11'))) | ~m1_subset_1(B_121, u1_struct_0('#skF_10')) | v2_struct_0('#skF_10'))), inference(demodulation, [status(thm), theory('equality')], [c_111, c_328, c_5793])).
% 11.78/4.14  tff(c_6005, plain, (![B_523]: (k2_lattices('#skF_10', k15_lattice3('#skF_10', k1_tarski('#skF_11')), B_523)=k2_lattices('#skF_10', B_523, k15_lattice3('#skF_10', k1_tarski('#skF_11'))) | ~m1_subset_1(B_523, u1_struct_0('#skF_10')))), inference(negUnitSimplification, [status(thm)], [c_106, c_5865])).
% 11.78/4.14  tff(c_4082, plain, (![C_439]: (r1_lattices('#skF_10', '#skF_11', k2_lattices('#skF_10', C_439, '#skF_11')) | ~r1_lattices('#skF_10', '#skF_11', C_439) | ~m1_subset_1(C_439, u1_struct_0('#skF_10')))), inference(splitRight, [status(thm)], [c_4063])).
% 11.78/4.14  tff(c_6039, plain, (r1_lattices('#skF_10', '#skF_11', k2_lattices('#skF_10', '#skF_11', k15_lattice3('#skF_10', k1_tarski('#skF_11')))) | ~r1_lattices('#skF_10', '#skF_11', k15_lattice3('#skF_10', k1_tarski('#skF_11'))) | ~m1_subset_1(k15_lattice3('#skF_10', k1_tarski('#skF_11')), u1_struct_0('#skF_10')) | ~m1_subset_1('#skF_11', u1_struct_0('#skF_10'))), inference(superposition, [status(thm), theory('equality')], [c_6005, c_4082])).
% 11.78/4.14  tff(c_6133, plain, (r1_lattices('#skF_10', '#skF_11', k2_lattices('#skF_10', '#skF_11', k15_lattice3('#skF_10', k1_tarski('#skF_11')))) | ~r1_lattices('#skF_10', '#skF_11', k15_lattice3('#skF_10', k1_tarski('#skF_11')))), inference(demodulation, [status(thm), theory('equality')], [c_98, c_5735, c_6039])).
% 11.78/4.14  tff(c_6204, plain, (~r1_lattices('#skF_10', '#skF_11', k15_lattice3('#skF_10', k1_tarski('#skF_11')))), inference(splitLeft, [status(thm)], [c_6133])).
% 11.78/4.14  tff(c_6207, plain, (~m1_subset_1('#skF_11', u1_struct_0('#skF_10')) | ~v4_lattice3('#skF_10') | ~v10_lattices('#skF_10') | ~l3_lattices('#skF_10') | v2_struct_0('#skF_10')), inference(resolution, [status(thm)], [c_3825, c_6204])).
% 11.78/4.14  tff(c_6213, plain, (v2_struct_0('#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_100, c_104, c_102, c_98, c_6207])).
% 11.78/4.14  tff(c_6215, plain, $false, inference(negUnitSimplification, [status(thm)], [c_106, c_6213])).
% 11.78/4.14  tff(c_6217, plain, (r1_lattices('#skF_10', '#skF_11', k15_lattice3('#skF_10', k1_tarski('#skF_11')))), inference(splitRight, [status(thm)], [c_6133])).
% 11.78/4.14  tff(c_6335, plain, (k15_lattice3('#skF_10', k1_tarski('#skF_11'))='#skF_11' | ~r1_lattices('#skF_10', k15_lattice3('#skF_10', k1_tarski('#skF_11')), '#skF_11') | ~m1_subset_1('#skF_11', u1_struct_0('#skF_10')) | ~m1_subset_1(k15_lattice3('#skF_10', k1_tarski('#skF_11')), u1_struct_0('#skF_10')) | ~l2_lattices('#skF_10') | ~v4_lattices('#skF_10') | v2_struct_0('#skF_10')), inference(resolution, [status(thm)], [c_6217, c_54])).
% 11.78/4.14  tff(c_6347, plain, (k15_lattice3('#skF_10', k1_tarski('#skF_11'))='#skF_11' | ~r1_lattices('#skF_10', k15_lattice3('#skF_10', k1_tarski('#skF_11')), '#skF_11') | v2_struct_0('#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_4342, c_118, c_5735, c_98, c_6335])).
% 11.78/4.14  tff(c_6348, plain, (~r1_lattices('#skF_10', k15_lattice3('#skF_10', k1_tarski('#skF_11')), '#skF_11')), inference(negUnitSimplification, [status(thm)], [c_106, c_158, c_6347])).
% 11.78/4.14  tff(c_6351, plain, (~r4_lattice3('#skF_10', '#skF_11', k1_tarski('#skF_11')) | ~m1_subset_1('#skF_11', u1_struct_0('#skF_10')) | ~v4_lattice3('#skF_10') | ~v10_lattices('#skF_10') | ~l3_lattices('#skF_10') | v2_struct_0('#skF_10')), inference(resolution, [status(thm)], [c_3665, c_6348])).
% 11.78/4.14  tff(c_6357, plain, (v2_struct_0('#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_100, c_104, c_102, c_98, c_1586, c_6351])).
% 11.78/4.14  tff(c_6359, plain, $false, inference(negUnitSimplification, [status(thm)], [c_106, c_6357])).
% 11.78/4.14  tff(c_6361, plain, ('#skF_6'('#skF_10', '#skF_11', k1_tarski('#skF_11'))!='#skF_11'), inference(splitRight, [status(thm)], [c_1049])).
% 11.78/4.14  tff(c_8254, plain, (![A_653, B_654, D_655]: (r1_lattices(A_653, k15_lattice3(A_653, B_654), D_655) | ~r4_lattice3(A_653, D_655, B_654) | ~m1_subset_1(D_655, u1_struct_0(A_653)) | ~m1_subset_1(k15_lattice3(A_653, B_654), u1_struct_0(A_653)) | ~v4_lattice3(A_653) | ~v10_lattices(A_653) | ~l3_lattices(A_653) | v2_struct_0(A_653))), inference(cnfTransformation, [status(thm)], [f_249])).
% 11.78/4.14  tff(c_8257, plain, (![A_125, B_126, D_655]: (r1_lattices(A_125, k15_lattice3(A_125, B_126), D_655) | ~r4_lattice3(A_125, D_655, B_126) | ~m1_subset_1(D_655, u1_struct_0(A_125)) | ~v4_lattice3(A_125) | ~v10_lattices(A_125) | ~l3_lattices(A_125) | v2_struct_0(A_125))), inference(resolution, [status(thm)], [c_92, c_8254])).
% 11.78/4.14  tff(c_10661, plain, (![B_121]: (k2_lattices('#skF_10', k15_lattice3('#skF_10', k1_tarski('#skF_11')), B_121)=k2_lattices('#skF_10', B_121, k15_lattice3('#skF_10', k1_tarski('#skF_11'))) | ~m1_subset_1(B_121, u1_struct_0('#skF_10')) | ~v6_lattices('#skF_10') | ~l1_lattices('#skF_10') | v2_struct_0('#skF_10'))), inference(resolution, [status(thm)], [c_10606, c_84])).
% 11.78/4.14  tff(c_10733, plain, (![B_121]: (k2_lattices('#skF_10', k15_lattice3('#skF_10', k1_tarski('#skF_11')), B_121)=k2_lattices('#skF_10', B_121, k15_lattice3('#skF_10', k1_tarski('#skF_11'))) | ~m1_subset_1(B_121, u1_struct_0('#skF_10')) | v2_struct_0('#skF_10'))), inference(demodulation, [status(thm), theory('equality')], [c_111, c_328, c_10661])).
% 11.78/4.14  tff(c_11291, plain, (![B_771]: (k2_lattices('#skF_10', k15_lattice3('#skF_10', k1_tarski('#skF_11')), B_771)=k2_lattices('#skF_10', B_771, k15_lattice3('#skF_10', k1_tarski('#skF_11'))) | ~m1_subset_1(B_771, u1_struct_0('#skF_10')))), inference(negUnitSimplification, [status(thm)], [c_106, c_10733])).
% 11.78/4.14  tff(c_8711, plain, (![B_674]: (r1_lattices('#skF_10', k2_lattices('#skF_10', B_674, '#skF_11'), '#skF_11') | ~r1_lattices('#skF_10', B_674, '#skF_11') | ~m1_subset_1('#skF_11', u1_struct_0('#skF_10')) | ~m1_subset_1('#skF_11', u1_struct_0('#skF_10')) | ~m1_subset_1(B_674, u1_struct_0('#skF_10')) | ~l3_lattices('#skF_10') | ~v9_lattices('#skF_10') | ~v8_lattices('#skF_10') | ~v7_lattices('#skF_10') | v2_struct_0('#skF_10'))), inference(superposition, [status(thm), theory('equality')], [c_554, c_8581])).
% 11.78/4.14  tff(c_8796, plain, (![B_674]: (r1_lattices('#skF_10', k2_lattices('#skF_10', B_674, '#skF_11'), '#skF_11') | ~r1_lattices('#skF_10', B_674, '#skF_11') | ~m1_subset_1(B_674, u1_struct_0('#skF_10')) | ~v7_lattices('#skF_10') | v2_struct_0('#skF_10'))), inference(demodulation, [status(thm), theory('equality')], [c_351, c_340, c_100, c_98, c_98, c_8711])).
% 11.78/4.14  tff(c_8797, plain, (![B_674]: (r1_lattices('#skF_10', k2_lattices('#skF_10', B_674, '#skF_11'), '#skF_11') | ~r1_lattices('#skF_10', B_674, '#skF_11') | ~m1_subset_1(B_674, u1_struct_0('#skF_10')) | ~v7_lattices('#skF_10'))), inference(negUnitSimplification, [status(thm)], [c_106, c_8796])).
% 11.78/4.14  tff(c_8816, plain, (![B_674]: (r1_lattices('#skF_10', k2_lattices('#skF_10', B_674, '#skF_11'), '#skF_11') | ~r1_lattices('#skF_10', B_674, '#skF_11') | ~m1_subset_1(B_674, u1_struct_0('#skF_10')))), inference(demodulation, [status(thm), theory('equality')], [c_8814, c_8797])).
% 11.78/4.14  tff(c_11339, plain, (r1_lattices('#skF_10', k2_lattices('#skF_10', '#skF_11', k15_lattice3('#skF_10', k1_tarski('#skF_11'))), '#skF_11') | ~r1_lattices('#skF_10', k15_lattice3('#skF_10', k1_tarski('#skF_11')), '#skF_11') | ~m1_subset_1(k15_lattice3('#skF_10', k1_tarski('#skF_11')), u1_struct_0('#skF_10')) | ~m1_subset_1('#skF_11', u1_struct_0('#skF_10'))), inference(superposition, [status(thm), theory('equality')], [c_11291, c_8816])).
% 11.78/4.14  tff(c_11441, plain, (r1_lattices('#skF_10', k2_lattices('#skF_10', '#skF_11', k15_lattice3('#skF_10', k1_tarski('#skF_11'))), '#skF_11') | ~r1_lattices('#skF_10', k15_lattice3('#skF_10', k1_tarski('#skF_11')), '#skF_11')), inference(demodulation, [status(thm), theory('equality')], [c_98, c_10606, c_11339])).
% 11.78/4.14  tff(c_11515, plain, (~r1_lattices('#skF_10', k15_lattice3('#skF_10', k1_tarski('#skF_11')), '#skF_11')), inference(splitLeft, [status(thm)], [c_11441])).
% 11.78/4.14  tff(c_11518, plain, (~r4_lattice3('#skF_10', '#skF_11', k1_tarski('#skF_11')) | ~m1_subset_1('#skF_11', u1_struct_0('#skF_10')) | ~v4_lattice3('#skF_10') | ~v10_lattices('#skF_10') | ~l3_lattices('#skF_10') | v2_struct_0('#skF_10')), inference(resolution, [status(thm)], [c_8257, c_11515])).
% 11.78/4.14  tff(c_11524, plain, (~r4_lattice3('#skF_10', '#skF_11', k1_tarski('#skF_11')) | v2_struct_0('#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_100, c_104, c_102, c_98, c_11518])).
% 11.78/4.14  tff(c_11525, plain, (~r4_lattice3('#skF_10', '#skF_11', k1_tarski('#skF_11'))), inference(negUnitSimplification, [status(thm)], [c_106, c_11524])).
% 11.78/4.14  tff(c_11529, plain, ('#skF_6'('#skF_10', '#skF_11', k1_tarski('#skF_11'))='#skF_11' | ~m1_subset_1('#skF_11', u1_struct_0('#skF_10')) | ~l3_lattices('#skF_10') | v2_struct_0('#skF_10')), inference(resolution, [status(thm)], [c_278, c_11525])).
% 11.78/4.14  tff(c_11532, plain, ('#skF_6'('#skF_10', '#skF_11', k1_tarski('#skF_11'))='#skF_11' | v2_struct_0('#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_100, c_98, c_11529])).
% 11.78/4.14  tff(c_11534, plain, $false, inference(negUnitSimplification, [status(thm)], [c_106, c_6361, c_11532])).
% 11.78/4.14  tff(c_11536, plain, (r1_lattices('#skF_10', k15_lattice3('#skF_10', k1_tarski('#skF_11')), '#skF_11')), inference(splitRight, [status(thm)], [c_11441])).
% 11.78/4.14  tff(c_11577, plain, (k2_lattices('#skF_10', k15_lattice3('#skF_10', k1_tarski('#skF_11')), '#skF_11')=k15_lattice3('#skF_10', k1_tarski('#skF_11')) | ~m1_subset_1('#skF_11', u1_struct_0('#skF_10')) | ~m1_subset_1(k15_lattice3('#skF_10', k1_tarski('#skF_11')), u1_struct_0('#skF_10')) | ~l3_lattices('#skF_10') | ~v9_lattices('#skF_10') | ~v8_lattices('#skF_10') | v2_struct_0('#skF_10')), inference(resolution, [status(thm)], [c_11536, c_52])).
% 11.78/4.14  tff(c_11585, plain, (k2_lattices('#skF_10', '#skF_11', k15_lattice3('#skF_10', k1_tarski('#skF_11')))=k15_lattice3('#skF_10', k1_tarski('#skF_11')) | v2_struct_0('#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_351, c_340, c_100, c_10606, c_98, c_461, c_11577])).
% 11.78/4.14  tff(c_11587, plain, $false, inference(negUnitSimplification, [status(thm)], [c_106, c_9351, c_11585])).
% 11.78/4.14  tff(c_11588, plain, (k16_lattice3('#skF_10', k6_domain_1(u1_struct_0('#skF_10'), '#skF_11'))!='#skF_11'), inference(splitRight, [status(thm)], [c_96])).
% 11.78/4.14  tff(c_11623, plain, (k16_lattice3('#skF_10', k1_tarski('#skF_11'))!='#skF_11'), inference(demodulation, [status(thm), theory('equality')], [c_11620, c_11588])).
% 11.78/4.14  tff(c_11589, plain, (k15_lattice3('#skF_10', k6_domain_1(u1_struct_0('#skF_10'), '#skF_11'))='#skF_11'), inference(splitRight, [status(thm)], [c_96])).
% 11.78/4.14  tff(c_11622, plain, (k15_lattice3('#skF_10', k1_tarski('#skF_11'))='#skF_11'), inference(demodulation, [status(thm), theory('equality')], [c_11620, c_11589])).
% 11.78/4.14  tff(c_11840, plain, (![A_832, B_833]: (r4_lattice3(A_832, k15_lattice3(A_832, B_833), B_833) | ~m1_subset_1(k15_lattice3(A_832, B_833), u1_struct_0(A_832)) | ~v4_lattice3(A_832) | ~v10_lattices(A_832) | ~l3_lattices(A_832) | v2_struct_0(A_832))), inference(cnfTransformation, [status(thm)], [f_249])).
% 11.78/4.14  tff(c_11842, plain, (r4_lattice3('#skF_10', k15_lattice3('#skF_10', k1_tarski('#skF_11')), k1_tarski('#skF_11')) | ~m1_subset_1('#skF_11', u1_struct_0('#skF_10')) | ~v4_lattice3('#skF_10') | ~v10_lattices('#skF_10') | ~l3_lattices('#skF_10') | v2_struct_0('#skF_10')), inference(superposition, [status(thm), theory('equality')], [c_11622, c_11840])).
% 11.78/4.14  tff(c_11846, plain, (r4_lattice3('#skF_10', '#skF_11', k1_tarski('#skF_11')) | v2_struct_0('#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_100, c_104, c_102, c_98, c_11622, c_11842])).
% 11.78/4.14  tff(c_11847, plain, (r4_lattice3('#skF_10', '#skF_11', k1_tarski('#skF_11'))), inference(negUnitSimplification, [status(thm)], [c_106, c_11846])).
% 11.78/4.14  tff(c_12222, plain, (![A_857, D_858, B_859, C_860]: (r1_lattices(A_857, D_858, B_859) | ~r2_hidden(D_858, C_860) | ~m1_subset_1(D_858, u1_struct_0(A_857)) | ~r4_lattice3(A_857, B_859, C_860) | ~m1_subset_1(B_859, u1_struct_0(A_857)) | ~l3_lattices(A_857) | v2_struct_0(A_857))), inference(cnfTransformation, [status(thm)], [f_221])).
% 11.78/4.14  tff(c_12238, plain, (![A_861, C_862, B_863]: (r1_lattices(A_861, C_862, B_863) | ~m1_subset_1(C_862, u1_struct_0(A_861)) | ~r4_lattice3(A_861, B_863, k1_tarski(C_862)) | ~m1_subset_1(B_863, u1_struct_0(A_861)) | ~l3_lattices(A_861) | v2_struct_0(A_861))), inference(resolution, [status(thm)], [c_4, c_12222])).
% 11.78/4.14  tff(c_12245, plain, (r1_lattices('#skF_10', '#skF_11', '#skF_11') | ~m1_subset_1('#skF_11', u1_struct_0('#skF_10')) | ~l3_lattices('#skF_10') | v2_struct_0('#skF_10')), inference(resolution, [status(thm)], [c_11847, c_12238])).
% 11.78/4.14  tff(c_12252, plain, (r1_lattices('#skF_10', '#skF_11', '#skF_11') | v2_struct_0('#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_100, c_98, c_12245])).
% 11.78/4.14  tff(c_12253, plain, (r1_lattices('#skF_10', '#skF_11', '#skF_11')), inference(negUnitSimplification, [status(thm)], [c_106, c_12252])).
% 11.78/4.14  tff(c_11729, plain, (![A_802, B_803, C_804]: (r2_hidden('#skF_5'(A_802, B_803, C_804), C_804) | r3_lattice3(A_802, B_803, C_804) | ~m1_subset_1(B_803, u1_struct_0(A_802)) | ~l3_lattices(A_802) | v2_struct_0(A_802))), inference(cnfTransformation, [status(thm)], [f_203])).
% 11.78/4.14  tff(c_11734, plain, (![A_802, B_803, A_1]: ('#skF_5'(A_802, B_803, k1_tarski(A_1))=A_1 | r3_lattice3(A_802, B_803, k1_tarski(A_1)) | ~m1_subset_1(B_803, u1_struct_0(A_802)) | ~l3_lattices(A_802) | v2_struct_0(A_802))), inference(resolution, [status(thm)], [c_11729, c_2])).
% 11.78/4.14  tff(c_12766, plain, (![A_893, C_894, B_895]: (k16_lattice3(A_893, C_894)=B_895 | ~r3_lattice3(A_893, B_895, C_894) | ~r2_hidden(B_895, C_894) | ~m1_subset_1(B_895, u1_struct_0(A_893)) | ~l3_lattices(A_893) | ~v4_lattice3(A_893) | ~v10_lattices(A_893) | v2_struct_0(A_893))), inference(cnfTransformation, [status(thm)], [f_290])).
% 11.78/4.14  tff(c_15577, plain, (![A_1053, A_1054, B_1055]: (k16_lattice3(A_1053, k1_tarski(A_1054))=B_1055 | ~r2_hidden(B_1055, k1_tarski(A_1054)) | ~v4_lattice3(A_1053) | ~v10_lattices(A_1053) | '#skF_5'(A_1053, B_1055, k1_tarski(A_1054))=A_1054 | ~m1_subset_1(B_1055, u1_struct_0(A_1053)) | ~l3_lattices(A_1053) | v2_struct_0(A_1053))), inference(resolution, [status(thm)], [c_11734, c_12766])).
% 11.78/4.14  tff(c_15597, plain, (![A_1056, C_1057]: (k16_lattice3(A_1056, k1_tarski(C_1057))=C_1057 | ~v4_lattice3(A_1056) | ~v10_lattices(A_1056) | '#skF_5'(A_1056, C_1057, k1_tarski(C_1057))=C_1057 | ~m1_subset_1(C_1057, u1_struct_0(A_1056)) | ~l3_lattices(A_1056) | v2_struct_0(A_1056))), inference(resolution, [status(thm)], [c_4, c_15577])).
% 11.78/4.14  tff(c_15615, plain, (k16_lattice3('#skF_10', k1_tarski('#skF_11'))='#skF_11' | ~v4_lattice3('#skF_10') | ~v10_lattices('#skF_10') | '#skF_5'('#skF_10', '#skF_11', k1_tarski('#skF_11'))='#skF_11' | ~l3_lattices('#skF_10') | v2_struct_0('#skF_10')), inference(resolution, [status(thm)], [c_98, c_15597])).
% 11.78/4.14  tff(c_15626, plain, (k16_lattice3('#skF_10', k1_tarski('#skF_11'))='#skF_11' | '#skF_5'('#skF_10', '#skF_11', k1_tarski('#skF_11'))='#skF_11' | v2_struct_0('#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_100, c_104, c_102, c_15615])).
% 11.78/4.14  tff(c_15627, plain, ('#skF_5'('#skF_10', '#skF_11', k1_tarski('#skF_11'))='#skF_11'), inference(negUnitSimplification, [status(thm)], [c_106, c_11623, c_15626])).
% 11.78/4.14  tff(c_60, plain, (![A_58, B_70, C_76]: (~r1_lattices(A_58, B_70, '#skF_5'(A_58, B_70, C_76)) | r3_lattice3(A_58, B_70, C_76) | ~m1_subset_1(B_70, u1_struct_0(A_58)) | ~l3_lattices(A_58) | v2_struct_0(A_58))), inference(cnfTransformation, [status(thm)], [f_203])).
% 11.78/4.14  tff(c_15706, plain, (~r1_lattices('#skF_10', '#skF_11', '#skF_11') | r3_lattice3('#skF_10', '#skF_11', k1_tarski('#skF_11')) | ~m1_subset_1('#skF_11', u1_struct_0('#skF_10')) | ~l3_lattices('#skF_10') | v2_struct_0('#skF_10')), inference(superposition, [status(thm), theory('equality')], [c_15627, c_60])).
% 11.78/4.14  tff(c_15731, plain, (r3_lattice3('#skF_10', '#skF_11', k1_tarski('#skF_11')) | v2_struct_0('#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_100, c_98, c_12253, c_15706])).
% 11.78/4.14  tff(c_15732, plain, (r3_lattice3('#skF_10', '#skF_11', k1_tarski('#skF_11'))), inference(negUnitSimplification, [status(thm)], [c_106, c_15731])).
% 11.78/4.14  tff(c_94, plain, (![A_127, C_133, B_131]: (k16_lattice3(A_127, C_133)=B_131 | ~r3_lattice3(A_127, B_131, C_133) | ~r2_hidden(B_131, C_133) | ~m1_subset_1(B_131, u1_struct_0(A_127)) | ~l3_lattices(A_127) | ~v4_lattice3(A_127) | ~v10_lattices(A_127) | v2_struct_0(A_127))), inference(cnfTransformation, [status(thm)], [f_290])).
% 11.78/4.14  tff(c_15738, plain, (k16_lattice3('#skF_10', k1_tarski('#skF_11'))='#skF_11' | ~r2_hidden('#skF_11', k1_tarski('#skF_11')) | ~m1_subset_1('#skF_11', u1_struct_0('#skF_10')) | ~l3_lattices('#skF_10') | ~v4_lattice3('#skF_10') | ~v10_lattices('#skF_10') | v2_struct_0('#skF_10')), inference(resolution, [status(thm)], [c_15732, c_94])).
% 11.78/4.14  tff(c_15744, plain, (k16_lattice3('#skF_10', k1_tarski('#skF_11'))='#skF_11' | v2_struct_0('#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_104, c_102, c_100, c_98, c_4, c_15738])).
% 11.78/4.14  tff(c_15746, plain, $false, inference(negUnitSimplification, [status(thm)], [c_106, c_11623, c_15744])).
% 11.78/4.14  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.78/4.14  
% 11.78/4.14  Inference rules
% 11.78/4.14  ----------------------
% 11.78/4.14  #Ref     : 0
% 11.78/4.14  #Sup     : 3135
% 11.78/4.14  #Fact    : 0
% 11.78/4.14  #Define  : 0
% 11.78/4.14  #Split   : 23
% 11.78/4.14  #Chain   : 0
% 11.78/4.14  #Close   : 0
% 11.78/4.14  
% 11.78/4.14  Ordering : KBO
% 11.78/4.14  
% 11.78/4.14  Simplification rules
% 11.78/4.14  ----------------------
% 11.78/4.14  #Subsume      : 203
% 11.78/4.14  #Demod        : 4053
% 11.78/4.14  #Tautology    : 1531
% 11.78/4.14  #SimpNegUnit  : 1238
% 11.78/4.14  #BackRed      : 4
% 11.78/4.14  
% 11.78/4.14  #Partial instantiations: 0
% 11.78/4.14  #Strategies tried      : 1
% 11.78/4.14  
% 11.78/4.14  Timing (in seconds)
% 11.78/4.14  ----------------------
% 11.78/4.14  Preprocessing        : 0.53
% 11.78/4.14  Parsing              : 0.27
% 11.78/4.14  CNF conversion       : 0.04
% 11.78/4.14  Main loop            : 2.74
% 11.78/4.14  Inferencing          : 0.97
% 11.78/4.14  Reduction            : 0.90
% 11.78/4.14  Demodulation         : 0.63
% 11.78/4.14  BG Simplification    : 0.12
% 11.78/4.14  Subsumption          : 0.58
% 11.78/4.14  Abstraction          : 0.16
% 11.78/4.14  MUC search           : 0.00
% 11.78/4.14  Cooper               : 0.00
% 11.78/4.14  Total                : 3.36
% 11.78/4.14  Index Insertion      : 0.00
% 11.78/4.14  Index Deletion       : 0.00
% 11.78/4.14  Index Matching       : 0.00
% 11.78/4.14  BG Taut test         : 0.00
%------------------------------------------------------------------------------
