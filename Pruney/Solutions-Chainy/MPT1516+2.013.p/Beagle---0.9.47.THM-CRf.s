%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:24:52 EST 2020

% Result     : Theorem 10.38s
% Output     : CNFRefutation 10.78s
% Verified   : 
% Statistics : Number of formulae       :  236 (5469 expanded)
%              Number of leaves         :   50 (1910 expanded)
%              Depth                    :   31
%              Number of atoms          :  791 (26246 expanded)
%              Number of equality atoms :  120 (3029 expanded)
%              Maximal formula depth    :   17 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r4_lattice3 > r1_lattices > r2_hidden > m1_subset_1 > v9_lattices > v8_lattices > v7_lattices > v6_lattices > v5_lattices > v4_lattices > v4_lattice3 > v2_struct_0 > v13_lattices > v10_lattices > l3_lattices > l2_lattices > l1_lattices > k2_lattices > k2_zfmisc_1 > k15_lattice3 > #nlpp > u1_struct_0 > k5_lattices > k1_xboole_0 > #skF_9 > #skF_2 > #skF_11 > #skF_4 > #skF_3 > #skF_10 > #skF_8 > #skF_7 > #skF_1 > #skF_5 > #skF_6

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

tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_11',type,(
    '#skF_11': $i )).

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

tff(v4_lattices,type,(
    v4_lattices: $i > $o )).

tff('#skF_10',type,(
    '#skF_10': $i > $i )).

tff(v6_lattices,type,(
    v6_lattices: $i > $o )).

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

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff(v13_lattices,type,(
    v13_lattices: $i > $o )).

tff(v8_lattices,type,(
    v8_lattices: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k5_lattices,type,(
    k5_lattices: $i > $i )).

tff('#skF_8',type,(
    '#skF_8': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(v7_lattices,type,(
    v7_lattices: $i > $o )).

tff(f_226,negated_conjecture,(
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

tff(f_88,axiom,(
    ! [A] :
      ( l3_lattices(A)
     => ( l1_lattices(A)
        & l2_lattices(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l3_lattices)).

tff(f_162,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l3_lattices(A) )
     => ( v4_lattice3(A)
      <=> ! [B] :
          ? [C] :
            ( m1_subset_1(C,u1_struct_0(A))
            & r4_lattice3(A,C,B)
            & ! [D] :
                ( m1_subset_1(D,u1_struct_0(A))
               => ( r4_lattice3(A,D,B)
                 => r1_lattices(A,C,D) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_lattice3)).

tff(f_142,axiom,(
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

tff(f_31,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_34,axiom,(
    ! [A,B] : ~ r2_hidden(A,k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_zfmisc_1)).

tff(f_190,axiom,(
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

tff(f_124,axiom,(
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

tff(f_56,axiom,(
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

tff(f_82,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_lattices(A) )
     => m1_subset_1(k5_lattices(A),u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_lattices)).

tff(f_205,axiom,(
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

tff(f_107,axiom,(
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

tff(f_75,axiom,(
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

tff(c_98,plain,(
    ~ v2_struct_0('#skF_11') ),
    inference(cnfTransformation,[status(thm)],[f_226])).

tff(c_92,plain,(
    l3_lattices('#skF_11') ),
    inference(cnfTransformation,[status(thm)],[f_226])).

tff(c_102,plain,(
    ! [A_107] :
      ( l1_lattices(A_107)
      | ~ l3_lattices(A_107) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_106,plain,(
    l1_lattices('#skF_11') ),
    inference(resolution,[status(thm)],[c_92,c_102])).

tff(c_96,plain,(
    v10_lattices('#skF_11') ),
    inference(cnfTransformation,[status(thm)],[f_226])).

tff(c_90,plain,
    ( k15_lattice3('#skF_11',k1_xboole_0) != k5_lattices('#skF_11')
    | ~ l3_lattices('#skF_11')
    | ~ v13_lattices('#skF_11')
    | ~ v10_lattices('#skF_11')
    | v2_struct_0('#skF_11') ),
    inference(cnfTransformation,[status(thm)],[f_226])).

tff(c_100,plain,
    ( k15_lattice3('#skF_11',k1_xboole_0) != k5_lattices('#skF_11')
    | ~ v13_lattices('#skF_11')
    | v2_struct_0('#skF_11') ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_92,c_90])).

tff(c_101,plain,
    ( k15_lattice3('#skF_11',k1_xboole_0) != k5_lattices('#skF_11')
    | ~ v13_lattices('#skF_11') ),
    inference(negUnitSimplification,[status(thm)],[c_98,c_100])).

tff(c_119,plain,(
    ~ v13_lattices('#skF_11') ),
    inference(splitLeft,[status(thm)],[c_101])).

tff(c_94,plain,(
    v4_lattice3('#skF_11') ),
    inference(cnfTransformation,[status(thm)],[f_226])).

tff(c_70,plain,(
    ! [A_58,B_73] :
      ( m1_subset_1('#skF_5'(A_58,B_73),u1_struct_0(A_58))
      | ~ v4_lattice3(A_58)
      | ~ l3_lattices(A_58)
      | v2_struct_0(A_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_241,plain,(
    ! [A_140,B_141,C_142] :
      ( r2_hidden('#skF_4'(A_140,B_141,C_142),C_142)
      | r4_lattice3(A_140,B_141,C_142)
      | ~ m1_subset_1(B_141,u1_struct_0(A_140))
      | ~ l3_lattices(A_140)
      | v2_struct_0(A_140) ) ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_4,plain,(
    ! [A_1] : k2_zfmisc_1(A_1,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_135,plain,(
    ! [A_111,B_112] : ~ r2_hidden(A_111,k2_zfmisc_1(A_111,B_112)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_141,plain,(
    ! [A_1] : ~ r2_hidden(A_1,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_135])).

tff(c_247,plain,(
    ! [A_143,B_144] :
      ( r4_lattice3(A_143,B_144,k1_xboole_0)
      | ~ m1_subset_1(B_144,u1_struct_0(A_143))
      | ~ l3_lattices(A_143)
      | v2_struct_0(A_143) ) ),
    inference(resolution,[status(thm)],[c_241,c_141])).

tff(c_267,plain,(
    ! [A_58,B_73] :
      ( r4_lattice3(A_58,'#skF_5'(A_58,B_73),k1_xboole_0)
      | ~ v4_lattice3(A_58)
      | ~ l3_lattices(A_58)
      | v2_struct_0(A_58) ) ),
    inference(resolution,[status(thm)],[c_70,c_247])).

tff(c_76,plain,(
    ! [A_84,B_91,C_92] :
      ( m1_subset_1('#skF_8'(A_84,B_91,C_92),u1_struct_0(A_84))
      | k15_lattice3(A_84,B_91) = C_92
      | ~ r4_lattice3(A_84,C_92,B_91)
      | ~ m1_subset_1(C_92,u1_struct_0(A_84))
      | ~ v4_lattice3(A_84)
      | ~ v10_lattices(A_84)
      | ~ l3_lattices(A_84)
      | v2_struct_0(A_84) ) ),
    inference(cnfTransformation,[status(thm)],[f_190])).

tff(c_74,plain,(
    ! [A_84,B_91,C_92] :
      ( r4_lattice3(A_84,'#skF_8'(A_84,B_91,C_92),B_91)
      | k15_lattice3(A_84,B_91) = C_92
      | ~ r4_lattice3(A_84,C_92,B_91)
      | ~ m1_subset_1(C_92,u1_struct_0(A_84))
      | ~ v4_lattice3(A_84)
      | ~ v10_lattices(A_84)
      | ~ l3_lattices(A_84)
      | v2_struct_0(A_84) ) ),
    inference(cnfTransformation,[status(thm)],[f_190])).

tff(c_66,plain,(
    ! [A_58,B_73,D_78] :
      ( r1_lattices(A_58,'#skF_5'(A_58,B_73),D_78)
      | ~ r4_lattice3(A_58,D_78,B_73)
      | ~ m1_subset_1(D_78,u1_struct_0(A_58))
      | ~ v4_lattice3(A_58)
      | ~ l3_lattices(A_58)
      | v2_struct_0(A_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_937,plain,(
    ! [A_265,C_266,B_267] :
      ( ~ r1_lattices(A_265,C_266,'#skF_8'(A_265,B_267,C_266))
      | k15_lattice3(A_265,B_267) = C_266
      | ~ r4_lattice3(A_265,C_266,B_267)
      | ~ m1_subset_1(C_266,u1_struct_0(A_265))
      | ~ v4_lattice3(A_265)
      | ~ v10_lattices(A_265)
      | ~ l3_lattices(A_265)
      | v2_struct_0(A_265) ) ),
    inference(cnfTransformation,[status(thm)],[f_190])).

tff(c_2096,plain,(
    ! [A_479,B_480,B_481] :
      ( k15_lattice3(A_479,B_480) = '#skF_5'(A_479,B_481)
      | ~ r4_lattice3(A_479,'#skF_5'(A_479,B_481),B_480)
      | ~ m1_subset_1('#skF_5'(A_479,B_481),u1_struct_0(A_479))
      | ~ v10_lattices(A_479)
      | ~ r4_lattice3(A_479,'#skF_8'(A_479,B_480,'#skF_5'(A_479,B_481)),B_481)
      | ~ m1_subset_1('#skF_8'(A_479,B_480,'#skF_5'(A_479,B_481)),u1_struct_0(A_479))
      | ~ v4_lattice3(A_479)
      | ~ l3_lattices(A_479)
      | v2_struct_0(A_479) ) ),
    inference(resolution,[status(thm)],[c_66,c_937])).

tff(c_2118,plain,(
    ! [A_484,B_485] :
      ( ~ m1_subset_1('#skF_8'(A_484,B_485,'#skF_5'(A_484,B_485)),u1_struct_0(A_484))
      | k15_lattice3(A_484,B_485) = '#skF_5'(A_484,B_485)
      | ~ r4_lattice3(A_484,'#skF_5'(A_484,B_485),B_485)
      | ~ m1_subset_1('#skF_5'(A_484,B_485),u1_struct_0(A_484))
      | ~ v4_lattice3(A_484)
      | ~ v10_lattices(A_484)
      | ~ l3_lattices(A_484)
      | v2_struct_0(A_484) ) ),
    inference(resolution,[status(thm)],[c_74,c_2096])).

tff(c_2124,plain,(
    ! [A_486,B_487] :
      ( k15_lattice3(A_486,B_487) = '#skF_5'(A_486,B_487)
      | ~ r4_lattice3(A_486,'#skF_5'(A_486,B_487),B_487)
      | ~ m1_subset_1('#skF_5'(A_486,B_487),u1_struct_0(A_486))
      | ~ v4_lattice3(A_486)
      | ~ v10_lattices(A_486)
      | ~ l3_lattices(A_486)
      | v2_struct_0(A_486) ) ),
    inference(resolution,[status(thm)],[c_76,c_2118])).

tff(c_2132,plain,(
    ! [A_488] :
      ( k15_lattice3(A_488,k1_xboole_0) = '#skF_5'(A_488,k1_xboole_0)
      | ~ m1_subset_1('#skF_5'(A_488,k1_xboole_0),u1_struct_0(A_488))
      | ~ v10_lattices(A_488)
      | ~ v4_lattice3(A_488)
      | ~ l3_lattices(A_488)
      | v2_struct_0(A_488) ) ),
    inference(resolution,[status(thm)],[c_267,c_2124])).

tff(c_2138,plain,(
    ! [A_489] :
      ( k15_lattice3(A_489,k1_xboole_0) = '#skF_5'(A_489,k1_xboole_0)
      | ~ v10_lattices(A_489)
      | ~ v4_lattice3(A_489)
      | ~ l3_lattices(A_489)
      | v2_struct_0(A_489) ) ),
    inference(resolution,[status(thm)],[c_70,c_2132])).

tff(c_2141,plain,
    ( k15_lattice3('#skF_11',k1_xboole_0) = '#skF_5'('#skF_11',k1_xboole_0)
    | ~ v10_lattices('#skF_11')
    | ~ l3_lattices('#skF_11')
    | v2_struct_0('#skF_11') ),
    inference(resolution,[status(thm)],[c_94,c_2138])).

tff(c_2144,plain,
    ( k15_lattice3('#skF_11',k1_xboole_0) = '#skF_5'('#skF_11',k1_xboole_0)
    | v2_struct_0('#skF_11') ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_96,c_2141])).

tff(c_2145,plain,(
    k15_lattice3('#skF_11',k1_xboole_0) = '#skF_5'('#skF_11',k1_xboole_0) ),
    inference(negUnitSimplification,[status(thm)],[c_98,c_2144])).

tff(c_80,plain,(
    ! [A_84,B_91] :
      ( r4_lattice3(A_84,k15_lattice3(A_84,B_91),B_91)
      | ~ m1_subset_1(k15_lattice3(A_84,B_91),u1_struct_0(A_84))
      | ~ v4_lattice3(A_84)
      | ~ v10_lattices(A_84)
      | ~ l3_lattices(A_84)
      | v2_struct_0(A_84) ) ),
    inference(cnfTransformation,[status(thm)],[f_190])).

tff(c_2150,plain,
    ( r4_lattice3('#skF_11',k15_lattice3('#skF_11',k1_xboole_0),k1_xboole_0)
    | ~ m1_subset_1('#skF_5'('#skF_11',k1_xboole_0),u1_struct_0('#skF_11'))
    | ~ v4_lattice3('#skF_11')
    | ~ v10_lattices('#skF_11')
    | ~ l3_lattices('#skF_11')
    | v2_struct_0('#skF_11') ),
    inference(superposition,[status(thm),theory(equality)],[c_2145,c_80])).

tff(c_2157,plain,
    ( r4_lattice3('#skF_11','#skF_5'('#skF_11',k1_xboole_0),k1_xboole_0)
    | ~ m1_subset_1('#skF_5'('#skF_11',k1_xboole_0),u1_struct_0('#skF_11'))
    | v2_struct_0('#skF_11') ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_96,c_94,c_2145,c_2150])).

tff(c_2158,plain,
    ( r4_lattice3('#skF_11','#skF_5'('#skF_11',k1_xboole_0),k1_xboole_0)
    | ~ m1_subset_1('#skF_5'('#skF_11',k1_xboole_0),u1_struct_0('#skF_11')) ),
    inference(negUnitSimplification,[status(thm)],[c_98,c_2157])).

tff(c_2160,plain,(
    ~ m1_subset_1('#skF_5'('#skF_11',k1_xboole_0),u1_struct_0('#skF_11')) ),
    inference(splitLeft,[status(thm)],[c_2158])).

tff(c_2163,plain,
    ( ~ v4_lattice3('#skF_11')
    | ~ l3_lattices('#skF_11')
    | v2_struct_0('#skF_11') ),
    inference(resolution,[status(thm)],[c_70,c_2160])).

tff(c_2166,plain,(
    v2_struct_0('#skF_11') ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_94,c_2163])).

tff(c_2168,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_98,c_2166])).

tff(c_2170,plain,(
    m1_subset_1('#skF_5'('#skF_11',k1_xboole_0),u1_struct_0('#skF_11')) ),
    inference(splitRight,[status(thm)],[c_2158])).

tff(c_44,plain,(
    ! [A_25,B_34] :
      ( m1_subset_1('#skF_3'(A_25,B_34),u1_struct_0(A_25))
      | v13_lattices(A_25)
      | ~ m1_subset_1(B_34,u1_struct_0(A_25))
      | ~ l1_lattices(A_25)
      | v2_struct_0(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_266,plain,(
    ! [A_25,B_34] :
      ( r4_lattice3(A_25,'#skF_3'(A_25,B_34),k1_xboole_0)
      | ~ l3_lattices(A_25)
      | v13_lattices(A_25)
      | ~ m1_subset_1(B_34,u1_struct_0(A_25))
      | ~ l1_lattices(A_25)
      | v2_struct_0(A_25) ) ),
    inference(resolution,[status(thm)],[c_44,c_247])).

tff(c_12,plain,(
    ! [A_5] :
      ( v8_lattices(A_5)
      | ~ v10_lattices(A_5)
      | v2_struct_0(A_5)
      | ~ l3_lattices(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_32,plain,(
    ! [A_16] :
      ( m1_subset_1(k5_lattices(A_16),u1_struct_0(A_16))
      | ~ l1_lattices(A_16)
      | v2_struct_0(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_271,plain,(
    ! [A_16] :
      ( r4_lattice3(A_16,k5_lattices(A_16),k1_xboole_0)
      | ~ l3_lattices(A_16)
      | ~ l1_lattices(A_16)
      | v2_struct_0(A_16) ) ),
    inference(resolution,[status(thm)],[c_32,c_247])).

tff(c_16,plain,(
    ! [A_5] :
      ( v6_lattices(A_5)
      | ~ v10_lattices(A_5)
      | v2_struct_0(A_5)
      | ~ l3_lattices(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_435,plain,(
    ! [A_191,C_192,B_193] :
      ( k2_lattices(A_191,C_192,B_193) = k2_lattices(A_191,B_193,C_192)
      | ~ m1_subset_1(C_192,u1_struct_0(A_191))
      | ~ m1_subset_1(B_193,u1_struct_0(A_191))
      | ~ v6_lattices(A_191)
      | ~ l1_lattices(A_191)
      | v2_struct_0(A_191) ) ),
    inference(cnfTransformation,[status(thm)],[f_205])).

tff(c_462,plain,(
    ! [A_16,B_193] :
      ( k2_lattices(A_16,k5_lattices(A_16),B_193) = k2_lattices(A_16,B_193,k5_lattices(A_16))
      | ~ m1_subset_1(B_193,u1_struct_0(A_16))
      | ~ v6_lattices(A_16)
      | ~ l1_lattices(A_16)
      | v2_struct_0(A_16) ) ),
    inference(resolution,[status(thm)],[c_32,c_435])).

tff(c_2225,plain,
    ( k2_lattices('#skF_11',k5_lattices('#skF_11'),'#skF_5'('#skF_11',k1_xboole_0)) = k2_lattices('#skF_11','#skF_5'('#skF_11',k1_xboole_0),k5_lattices('#skF_11'))
    | ~ v6_lattices('#skF_11')
    | ~ l1_lattices('#skF_11')
    | v2_struct_0('#skF_11') ),
    inference(resolution,[status(thm)],[c_2170,c_462])).

tff(c_2277,plain,
    ( k2_lattices('#skF_11',k5_lattices('#skF_11'),'#skF_5'('#skF_11',k1_xboole_0)) = k2_lattices('#skF_11','#skF_5'('#skF_11',k1_xboole_0),k5_lattices('#skF_11'))
    | ~ v6_lattices('#skF_11')
    | v2_struct_0('#skF_11') ),
    inference(demodulation,[status(thm),theory(equality)],[c_106,c_2225])).

tff(c_2278,plain,
    ( k2_lattices('#skF_11',k5_lattices('#skF_11'),'#skF_5'('#skF_11',k1_xboole_0)) = k2_lattices('#skF_11','#skF_5'('#skF_11',k1_xboole_0),k5_lattices('#skF_11'))
    | ~ v6_lattices('#skF_11') ),
    inference(negUnitSimplification,[status(thm)],[c_98,c_2277])).

tff(c_2303,plain,(
    ~ v6_lattices('#skF_11') ),
    inference(splitLeft,[status(thm)],[c_2278])).

tff(c_2307,plain,
    ( ~ v10_lattices('#skF_11')
    | v2_struct_0('#skF_11')
    | ~ l3_lattices('#skF_11') ),
    inference(resolution,[status(thm)],[c_16,c_2303])).

tff(c_2310,plain,(
    v2_struct_0('#skF_11') ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_96,c_2307])).

tff(c_2312,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_98,c_2310])).

tff(c_2314,plain,(
    v6_lattices('#skF_11') ),
    inference(splitRight,[status(thm)],[c_2278])).

tff(c_2313,plain,(
    k2_lattices('#skF_11',k5_lattices('#skF_11'),'#skF_5'('#skF_11',k1_xboole_0)) = k2_lattices('#skF_11','#skF_5'('#skF_11',k1_xboole_0),k5_lattices('#skF_11')) ),
    inference(splitRight,[status(thm)],[c_2278])).

tff(c_763,plain,(
    ! [A_238,B_239,C_240] :
      ( k2_lattices(A_238,B_239,C_240) = B_239
      | ~ r1_lattices(A_238,B_239,C_240)
      | ~ m1_subset_1(C_240,u1_struct_0(A_238))
      | ~ m1_subset_1(B_239,u1_struct_0(A_238))
      | ~ l3_lattices(A_238)
      | ~ v9_lattices(A_238)
      | ~ v8_lattices(A_238)
      | v2_struct_0(A_238) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_1278,plain,(
    ! [A_328,B_329,D_330] :
      ( k2_lattices(A_328,'#skF_5'(A_328,B_329),D_330) = '#skF_5'(A_328,B_329)
      | ~ m1_subset_1('#skF_5'(A_328,B_329),u1_struct_0(A_328))
      | ~ v9_lattices(A_328)
      | ~ v8_lattices(A_328)
      | ~ r4_lattice3(A_328,D_330,B_329)
      | ~ m1_subset_1(D_330,u1_struct_0(A_328))
      | ~ v4_lattice3(A_328)
      | ~ l3_lattices(A_328)
      | v2_struct_0(A_328) ) ),
    inference(resolution,[status(thm)],[c_66,c_763])).

tff(c_1282,plain,(
    ! [A_331,B_332,D_333] :
      ( k2_lattices(A_331,'#skF_5'(A_331,B_332),D_333) = '#skF_5'(A_331,B_332)
      | ~ v9_lattices(A_331)
      | ~ v8_lattices(A_331)
      | ~ r4_lattice3(A_331,D_333,B_332)
      | ~ m1_subset_1(D_333,u1_struct_0(A_331))
      | ~ v4_lattice3(A_331)
      | ~ l3_lattices(A_331)
      | v2_struct_0(A_331) ) ),
    inference(resolution,[status(thm)],[c_70,c_1278])).

tff(c_1334,plain,(
    ! [A_337,B_338] :
      ( k2_lattices(A_337,'#skF_5'(A_337,B_338),k5_lattices(A_337)) = '#skF_5'(A_337,B_338)
      | ~ v9_lattices(A_337)
      | ~ v8_lattices(A_337)
      | ~ r4_lattice3(A_337,k5_lattices(A_337),B_338)
      | ~ v4_lattice3(A_337)
      | ~ l3_lattices(A_337)
      | ~ l1_lattices(A_337)
      | v2_struct_0(A_337) ) ),
    inference(resolution,[status(thm)],[c_32,c_1282])).

tff(c_523,plain,(
    ! [A_200,B_201] :
      ( k2_lattices(A_200,k5_lattices(A_200),B_201) = k2_lattices(A_200,B_201,k5_lattices(A_200))
      | ~ m1_subset_1(B_201,u1_struct_0(A_200))
      | ~ v6_lattices(A_200)
      | ~ l1_lattices(A_200)
      | v2_struct_0(A_200) ) ),
    inference(resolution,[status(thm)],[c_32,c_435])).

tff(c_546,plain,(
    ! [A_58,B_73] :
      ( k2_lattices(A_58,k5_lattices(A_58),'#skF_5'(A_58,B_73)) = k2_lattices(A_58,'#skF_5'(A_58,B_73),k5_lattices(A_58))
      | ~ v6_lattices(A_58)
      | ~ l1_lattices(A_58)
      | ~ v4_lattice3(A_58)
      | ~ l3_lattices(A_58)
      | v2_struct_0(A_58) ) ),
    inference(resolution,[status(thm)],[c_70,c_523])).

tff(c_1340,plain,(
    ! [A_337,B_338] :
      ( k2_lattices(A_337,k5_lattices(A_337),'#skF_5'(A_337,B_338)) = '#skF_5'(A_337,B_338)
      | ~ v6_lattices(A_337)
      | ~ l1_lattices(A_337)
      | ~ v4_lattice3(A_337)
      | ~ l3_lattices(A_337)
      | v2_struct_0(A_337)
      | ~ v9_lattices(A_337)
      | ~ v8_lattices(A_337)
      | ~ r4_lattice3(A_337,k5_lattices(A_337),B_338)
      | ~ v4_lattice3(A_337)
      | ~ l3_lattices(A_337)
      | ~ l1_lattices(A_337)
      | v2_struct_0(A_337) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1334,c_546])).

tff(c_2318,plain,
    ( k2_lattices('#skF_11','#skF_5'('#skF_11',k1_xboole_0),k5_lattices('#skF_11')) = '#skF_5'('#skF_11',k1_xboole_0)
    | ~ v6_lattices('#skF_11')
    | ~ l1_lattices('#skF_11')
    | ~ v4_lattice3('#skF_11')
    | ~ l3_lattices('#skF_11')
    | v2_struct_0('#skF_11')
    | ~ v9_lattices('#skF_11')
    | ~ v8_lattices('#skF_11')
    | ~ r4_lattice3('#skF_11',k5_lattices('#skF_11'),k1_xboole_0)
    | ~ v4_lattice3('#skF_11')
    | ~ l3_lattices('#skF_11')
    | ~ l1_lattices('#skF_11')
    | v2_struct_0('#skF_11') ),
    inference(superposition,[status(thm),theory(equality)],[c_2313,c_1340])).

tff(c_2337,plain,
    ( k2_lattices('#skF_11','#skF_5'('#skF_11',k1_xboole_0),k5_lattices('#skF_11')) = '#skF_5'('#skF_11',k1_xboole_0)
    | ~ v9_lattices('#skF_11')
    | ~ v8_lattices('#skF_11')
    | ~ r4_lattice3('#skF_11',k5_lattices('#skF_11'),k1_xboole_0)
    | v2_struct_0('#skF_11') ),
    inference(demodulation,[status(thm),theory(equality)],[c_106,c_92,c_94,c_92,c_94,c_106,c_2314,c_2318])).

tff(c_2338,plain,
    ( k2_lattices('#skF_11','#skF_5'('#skF_11',k1_xboole_0),k5_lattices('#skF_11')) = '#skF_5'('#skF_11',k1_xboole_0)
    | ~ v9_lattices('#skF_11')
    | ~ v8_lattices('#skF_11')
    | ~ r4_lattice3('#skF_11',k5_lattices('#skF_11'),k1_xboole_0) ),
    inference(negUnitSimplification,[status(thm)],[c_98,c_2337])).

tff(c_2575,plain,(
    ~ r4_lattice3('#skF_11',k5_lattices('#skF_11'),k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_2338])).

tff(c_2578,plain,
    ( ~ l3_lattices('#skF_11')
    | ~ l1_lattices('#skF_11')
    | v2_struct_0('#skF_11') ),
    inference(resolution,[status(thm)],[c_271,c_2575])).

tff(c_2581,plain,(
    v2_struct_0('#skF_11') ),
    inference(demodulation,[status(thm),theory(equality)],[c_106,c_92,c_2578])).

tff(c_2583,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_98,c_2581])).

tff(c_2585,plain,(
    r4_lattice3('#skF_11',k5_lattices('#skF_11'),k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_2338])).

tff(c_2328,plain,
    ( k2_lattices('#skF_11','#skF_5'('#skF_11',k1_xboole_0),k5_lattices('#skF_11')) = '#skF_5'('#skF_11',k1_xboole_0)
    | ~ v6_lattices('#skF_11')
    | ~ l1_lattices('#skF_11')
    | ~ v4_lattice3('#skF_11')
    | ~ l3_lattices('#skF_11')
    | v2_struct_0('#skF_11')
    | ~ v9_lattices('#skF_11')
    | ~ v8_lattices('#skF_11')
    | ~ r4_lattice3('#skF_11',k5_lattices('#skF_11'),k1_xboole_0)
    | ~ v4_lattice3('#skF_11')
    | ~ l3_lattices('#skF_11')
    | ~ l1_lattices('#skF_11')
    | v2_struct_0('#skF_11') ),
    inference(superposition,[status(thm),theory(equality)],[c_1340,c_2313])).

tff(c_2348,plain,
    ( k2_lattices('#skF_11','#skF_5'('#skF_11',k1_xboole_0),k5_lattices('#skF_11')) = '#skF_5'('#skF_11',k1_xboole_0)
    | ~ v9_lattices('#skF_11')
    | ~ v8_lattices('#skF_11')
    | ~ r4_lattice3('#skF_11',k5_lattices('#skF_11'),k1_xboole_0)
    | v2_struct_0('#skF_11') ),
    inference(demodulation,[status(thm),theory(equality)],[c_106,c_92,c_94,c_92,c_94,c_106,c_2314,c_2328])).

tff(c_2349,plain,
    ( k2_lattices('#skF_11','#skF_5'('#skF_11',k1_xboole_0),k5_lattices('#skF_11')) = '#skF_5'('#skF_11',k1_xboole_0)
    | ~ v9_lattices('#skF_11')
    | ~ v8_lattices('#skF_11')
    | ~ r4_lattice3('#skF_11',k5_lattices('#skF_11'),k1_xboole_0) ),
    inference(negUnitSimplification,[status(thm)],[c_98,c_2348])).

tff(c_2600,plain,
    ( k2_lattices('#skF_11','#skF_5'('#skF_11',k1_xboole_0),k5_lattices('#skF_11')) = '#skF_5'('#skF_11',k1_xboole_0)
    | ~ v9_lattices('#skF_11')
    | ~ v8_lattices('#skF_11') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2585,c_2349])).

tff(c_2601,plain,(
    ~ v8_lattices('#skF_11') ),
    inference(splitLeft,[status(thm)],[c_2600])).

tff(c_2604,plain,
    ( ~ v10_lattices('#skF_11')
    | v2_struct_0('#skF_11')
    | ~ l3_lattices('#skF_11') ),
    inference(resolution,[status(thm)],[c_12,c_2601])).

tff(c_2607,plain,(
    v2_struct_0('#skF_11') ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_96,c_2604])).

tff(c_2609,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_98,c_2607])).

tff(c_2611,plain,(
    v8_lattices('#skF_11') ),
    inference(splitRight,[status(thm)],[c_2600])).

tff(c_10,plain,(
    ! [A_5] :
      ( v9_lattices(A_5)
      | ~ v10_lattices(A_5)
      | v2_struct_0(A_5)
      | ~ l3_lattices(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_2610,plain,
    ( ~ v9_lattices('#skF_11')
    | k2_lattices('#skF_11','#skF_5'('#skF_11',k1_xboole_0),k5_lattices('#skF_11')) = '#skF_5'('#skF_11',k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_2600])).

tff(c_2612,plain,(
    ~ v9_lattices('#skF_11') ),
    inference(splitLeft,[status(thm)],[c_2610])).

tff(c_2615,plain,
    ( ~ v10_lattices('#skF_11')
    | v2_struct_0('#skF_11')
    | ~ l3_lattices('#skF_11') ),
    inference(resolution,[status(thm)],[c_10,c_2612])).

tff(c_2618,plain,(
    v2_struct_0('#skF_11') ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_96,c_2615])).

tff(c_2620,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_98,c_2618])).

tff(c_2622,plain,(
    v9_lattices('#skF_11') ),
    inference(splitRight,[status(thm)],[c_2610])).

tff(c_1307,plain,(
    ! [A_25,B_332,B_34] :
      ( k2_lattices(A_25,'#skF_5'(A_25,B_332),'#skF_3'(A_25,B_34)) = '#skF_5'(A_25,B_332)
      | ~ v9_lattices(A_25)
      | ~ v8_lattices(A_25)
      | ~ r4_lattice3(A_25,'#skF_3'(A_25,B_34),B_332)
      | ~ v4_lattice3(A_25)
      | ~ l3_lattices(A_25)
      | v13_lattices(A_25)
      | ~ m1_subset_1(B_34,u1_struct_0(A_25))
      | ~ l1_lattices(A_25)
      | v2_struct_0(A_25) ) ),
    inference(resolution,[status(thm)],[c_44,c_1282])).

tff(c_82,plain,(
    ! [A_96,C_105,B_103] :
      ( k2_lattices(A_96,C_105,B_103) = k2_lattices(A_96,B_103,C_105)
      | ~ m1_subset_1(C_105,u1_struct_0(A_96))
      | ~ m1_subset_1(B_103,u1_struct_0(A_96))
      | ~ v6_lattices(A_96)
      | ~ l1_lattices(A_96)
      | v2_struct_0(A_96) ) ),
    inference(cnfTransformation,[status(thm)],[f_205])).

tff(c_2229,plain,(
    ! [B_103] :
      ( k2_lattices('#skF_11',B_103,'#skF_5'('#skF_11',k1_xboole_0)) = k2_lattices('#skF_11','#skF_5'('#skF_11',k1_xboole_0),B_103)
      | ~ m1_subset_1(B_103,u1_struct_0('#skF_11'))
      | ~ v6_lattices('#skF_11')
      | ~ l1_lattices('#skF_11')
      | v2_struct_0('#skF_11') ) ),
    inference(resolution,[status(thm)],[c_2170,c_82])).

tff(c_2285,plain,(
    ! [B_103] :
      ( k2_lattices('#skF_11',B_103,'#skF_5'('#skF_11',k1_xboole_0)) = k2_lattices('#skF_11','#skF_5'('#skF_11',k1_xboole_0),B_103)
      | ~ m1_subset_1(B_103,u1_struct_0('#skF_11'))
      | ~ v6_lattices('#skF_11')
      | v2_struct_0('#skF_11') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_106,c_2229])).

tff(c_2286,plain,(
    ! [B_103] :
      ( k2_lattices('#skF_11',B_103,'#skF_5'('#skF_11',k1_xboole_0)) = k2_lattices('#skF_11','#skF_5'('#skF_11',k1_xboole_0),B_103)
      | ~ m1_subset_1(B_103,u1_struct_0('#skF_11'))
      | ~ v6_lattices('#skF_11') ) ),
    inference(negUnitSimplification,[status(thm)],[c_98,c_2285])).

tff(c_2490,plain,(
    ! [B_494] :
      ( k2_lattices('#skF_11',B_494,'#skF_5'('#skF_11',k1_xboole_0)) = k2_lattices('#skF_11','#skF_5'('#skF_11',k1_xboole_0),B_494)
      | ~ m1_subset_1(B_494,u1_struct_0('#skF_11')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2314,c_2286])).

tff(c_2513,plain,(
    ! [B_34] :
      ( k2_lattices('#skF_11','#skF_3'('#skF_11',B_34),'#skF_5'('#skF_11',k1_xboole_0)) = k2_lattices('#skF_11','#skF_5'('#skF_11',k1_xboole_0),'#skF_3'('#skF_11',B_34))
      | v13_lattices('#skF_11')
      | ~ m1_subset_1(B_34,u1_struct_0('#skF_11'))
      | ~ l1_lattices('#skF_11')
      | v2_struct_0('#skF_11') ) ),
    inference(resolution,[status(thm)],[c_44,c_2490])).

tff(c_2553,plain,(
    ! [B_34] :
      ( k2_lattices('#skF_11','#skF_3'('#skF_11',B_34),'#skF_5'('#skF_11',k1_xboole_0)) = k2_lattices('#skF_11','#skF_5'('#skF_11',k1_xboole_0),'#skF_3'('#skF_11',B_34))
      | v13_lattices('#skF_11')
      | ~ m1_subset_1(B_34,u1_struct_0('#skF_11'))
      | v2_struct_0('#skF_11') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_106,c_2513])).

tff(c_3204,plain,(
    ! [B_518] :
      ( k2_lattices('#skF_11','#skF_3'('#skF_11',B_518),'#skF_5'('#skF_11',k1_xboole_0)) = k2_lattices('#skF_11','#skF_5'('#skF_11',k1_xboole_0),'#skF_3'('#skF_11',B_518))
      | ~ m1_subset_1(B_518,u1_struct_0('#skF_11')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_98,c_119,c_2553])).

tff(c_42,plain,(
    ! [A_25,B_34] :
      ( k2_lattices(A_25,'#skF_3'(A_25,B_34),B_34) != B_34
      | k2_lattices(A_25,B_34,'#skF_3'(A_25,B_34)) != B_34
      | v13_lattices(A_25)
      | ~ m1_subset_1(B_34,u1_struct_0(A_25))
      | ~ l1_lattices(A_25)
      | v2_struct_0(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_3213,plain,
    ( k2_lattices('#skF_11','#skF_5'('#skF_11',k1_xboole_0),'#skF_3'('#skF_11','#skF_5'('#skF_11',k1_xboole_0))) != '#skF_5'('#skF_11',k1_xboole_0)
    | k2_lattices('#skF_11','#skF_5'('#skF_11',k1_xboole_0),'#skF_3'('#skF_11','#skF_5'('#skF_11',k1_xboole_0))) != '#skF_5'('#skF_11',k1_xboole_0)
    | v13_lattices('#skF_11')
    | ~ m1_subset_1('#skF_5'('#skF_11',k1_xboole_0),u1_struct_0('#skF_11'))
    | ~ l1_lattices('#skF_11')
    | v2_struct_0('#skF_11')
    | ~ m1_subset_1('#skF_5'('#skF_11',k1_xboole_0),u1_struct_0('#skF_11')) ),
    inference(superposition,[status(thm),theory(equality)],[c_3204,c_42])).

tff(c_3227,plain,
    ( k2_lattices('#skF_11','#skF_5'('#skF_11',k1_xboole_0),'#skF_3'('#skF_11','#skF_5'('#skF_11',k1_xboole_0))) != '#skF_5'('#skF_11',k1_xboole_0)
    | v13_lattices('#skF_11')
    | v2_struct_0('#skF_11') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2170,c_106,c_2170,c_3213])).

tff(c_3228,plain,(
    k2_lattices('#skF_11','#skF_5'('#skF_11',k1_xboole_0),'#skF_3'('#skF_11','#skF_5'('#skF_11',k1_xboole_0))) != '#skF_5'('#skF_11',k1_xboole_0) ),
    inference(negUnitSimplification,[status(thm)],[c_98,c_119,c_3227])).

tff(c_3236,plain,
    ( ~ v9_lattices('#skF_11')
    | ~ v8_lattices('#skF_11')
    | ~ r4_lattice3('#skF_11','#skF_3'('#skF_11','#skF_5'('#skF_11',k1_xboole_0)),k1_xboole_0)
    | ~ v4_lattice3('#skF_11')
    | ~ l3_lattices('#skF_11')
    | v13_lattices('#skF_11')
    | ~ m1_subset_1('#skF_5'('#skF_11',k1_xboole_0),u1_struct_0('#skF_11'))
    | ~ l1_lattices('#skF_11')
    | v2_struct_0('#skF_11') ),
    inference(superposition,[status(thm),theory(equality)],[c_1307,c_3228])).

tff(c_3239,plain,
    ( ~ r4_lattice3('#skF_11','#skF_3'('#skF_11','#skF_5'('#skF_11',k1_xboole_0)),k1_xboole_0)
    | v13_lattices('#skF_11')
    | v2_struct_0('#skF_11') ),
    inference(demodulation,[status(thm),theory(equality)],[c_106,c_2170,c_92,c_94,c_2611,c_2622,c_3236])).

tff(c_3240,plain,(
    ~ r4_lattice3('#skF_11','#skF_3'('#skF_11','#skF_5'('#skF_11',k1_xboole_0)),k1_xboole_0) ),
    inference(negUnitSimplification,[status(thm)],[c_98,c_119,c_3239])).

tff(c_3243,plain,
    ( ~ l3_lattices('#skF_11')
    | v13_lattices('#skF_11')
    | ~ m1_subset_1('#skF_5'('#skF_11',k1_xboole_0),u1_struct_0('#skF_11'))
    | ~ l1_lattices('#skF_11')
    | v2_struct_0('#skF_11') ),
    inference(resolution,[status(thm)],[c_266,c_3240])).

tff(c_3246,plain,
    ( v13_lattices('#skF_11')
    | v2_struct_0('#skF_11') ),
    inference(demodulation,[status(thm),theory(equality)],[c_106,c_2170,c_92,c_3243])).

tff(c_3248,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_98,c_119,c_3246])).

tff(c_3250,plain,(
    v13_lattices('#skF_11') ),
    inference(splitRight,[status(thm)],[c_101])).

tff(c_46,plain,(
    ! [A_25] :
      ( m1_subset_1('#skF_2'(A_25),u1_struct_0(A_25))
      | ~ v13_lattices(A_25)
      | ~ l1_lattices(A_25)
      | v2_struct_0(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_3497,plain,(
    ! [A_590,C_591] :
      ( k2_lattices(A_590,k5_lattices(A_590),C_591) = k5_lattices(A_590)
      | ~ m1_subset_1(C_591,u1_struct_0(A_590))
      | ~ m1_subset_1(k5_lattices(A_590),u1_struct_0(A_590))
      | ~ v13_lattices(A_590)
      | ~ l1_lattices(A_590)
      | v2_struct_0(A_590) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_3525,plain,(
    ! [A_592] :
      ( k2_lattices(A_592,k5_lattices(A_592),'#skF_2'(A_592)) = k5_lattices(A_592)
      | ~ m1_subset_1(k5_lattices(A_592),u1_struct_0(A_592))
      | ~ v13_lattices(A_592)
      | ~ l1_lattices(A_592)
      | v2_struct_0(A_592) ) ),
    inference(resolution,[status(thm)],[c_46,c_3497])).

tff(c_3529,plain,(
    ! [A_593] :
      ( k2_lattices(A_593,k5_lattices(A_593),'#skF_2'(A_593)) = k5_lattices(A_593)
      | ~ v13_lattices(A_593)
      | ~ l1_lattices(A_593)
      | v2_struct_0(A_593) ) ),
    inference(resolution,[status(thm)],[c_32,c_3525])).

tff(c_3298,plain,(
    ! [A_541,C_542] :
      ( k2_lattices(A_541,C_542,'#skF_2'(A_541)) = '#skF_2'(A_541)
      | ~ m1_subset_1(C_542,u1_struct_0(A_541))
      | ~ v13_lattices(A_541)
      | ~ l1_lattices(A_541)
      | v2_struct_0(A_541) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_3316,plain,(
    ! [A_16] :
      ( k2_lattices(A_16,k5_lattices(A_16),'#skF_2'(A_16)) = '#skF_2'(A_16)
      | ~ v13_lattices(A_16)
      | ~ l1_lattices(A_16)
      | v2_struct_0(A_16) ) ),
    inference(resolution,[status(thm)],[c_32,c_3298])).

tff(c_3535,plain,(
    ! [A_593] :
      ( k5_lattices(A_593) = '#skF_2'(A_593)
      | ~ v13_lattices(A_593)
      | ~ l1_lattices(A_593)
      | v2_struct_0(A_593)
      | ~ v13_lattices(A_593)
      | ~ l1_lattices(A_593)
      | v2_struct_0(A_593) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3529,c_3316])).

tff(c_3558,plain,(
    ! [A_597] :
      ( k5_lattices(A_597) = '#skF_2'(A_597)
      | ~ v13_lattices(A_597)
      | ~ l1_lattices(A_597)
      | v2_struct_0(A_597) ) ),
    inference(factorization,[status(thm),theory(equality)],[c_3535])).

tff(c_3561,plain,
    ( k5_lattices('#skF_11') = '#skF_2'('#skF_11')
    | ~ v13_lattices('#skF_11')
    | ~ l1_lattices('#skF_11') ),
    inference(resolution,[status(thm)],[c_3558,c_98])).

tff(c_3564,plain,(
    k5_lattices('#skF_11') = '#skF_2'('#skF_11') ),
    inference(demodulation,[status(thm),theory(equality)],[c_106,c_3250,c_3561])).

tff(c_3400,plain,(
    ! [A_553,B_554,C_555] :
      ( r2_hidden('#skF_4'(A_553,B_554,C_555),C_555)
      | r4_lattice3(A_553,B_554,C_555)
      | ~ m1_subset_1(B_554,u1_struct_0(A_553))
      | ~ l3_lattices(A_553)
      | v2_struct_0(A_553) ) ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_3266,plain,(
    ! [A_520,B_521] : ~ r2_hidden(A_520,k2_zfmisc_1(A_520,B_521)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_3272,plain,(
    ! [A_1] : ~ r2_hidden(A_1,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_3266])).

tff(c_3406,plain,(
    ! [A_556,B_557] :
      ( r4_lattice3(A_556,B_557,k1_xboole_0)
      | ~ m1_subset_1(B_557,u1_struct_0(A_556))
      | ~ l3_lattices(A_556)
      | v2_struct_0(A_556) ) ),
    inference(resolution,[status(thm)],[c_3400,c_3272])).

tff(c_3430,plain,(
    ! [A_16] :
      ( r4_lattice3(A_16,k5_lattices(A_16),k1_xboole_0)
      | ~ l3_lattices(A_16)
      | ~ l1_lattices(A_16)
      | v2_struct_0(A_16) ) ),
    inference(resolution,[status(thm)],[c_32,c_3406])).

tff(c_3572,plain,
    ( r4_lattice3('#skF_11','#skF_2'('#skF_11'),k1_xboole_0)
    | ~ l3_lattices('#skF_11')
    | ~ l1_lattices('#skF_11')
    | v2_struct_0('#skF_11') ),
    inference(superposition,[status(thm),theory(equality)],[c_3564,c_3430])).

tff(c_3588,plain,
    ( r4_lattice3('#skF_11','#skF_2'('#skF_11'),k1_xboole_0)
    | v2_struct_0('#skF_11') ),
    inference(demodulation,[status(thm),theory(equality)],[c_106,c_92,c_3572])).

tff(c_3589,plain,(
    r4_lattice3('#skF_11','#skF_2'('#skF_11'),k1_xboole_0) ),
    inference(negUnitSimplification,[status(thm)],[c_98,c_3588])).

tff(c_3581,plain,
    ( m1_subset_1('#skF_2'('#skF_11'),u1_struct_0('#skF_11'))
    | ~ l1_lattices('#skF_11')
    | v2_struct_0('#skF_11') ),
    inference(superposition,[status(thm),theory(equality)],[c_3564,c_32])).

tff(c_3597,plain,
    ( m1_subset_1('#skF_2'('#skF_11'),u1_struct_0('#skF_11'))
    | v2_struct_0('#skF_11') ),
    inference(demodulation,[status(thm),theory(equality)],[c_106,c_3581])).

tff(c_3598,plain,(
    m1_subset_1('#skF_2'('#skF_11'),u1_struct_0('#skF_11')) ),
    inference(negUnitSimplification,[status(thm)],[c_98,c_3597])).

tff(c_4154,plain,(
    ! [A_631,B_632,C_633] :
      ( r1_lattices(A_631,B_632,C_633)
      | k2_lattices(A_631,B_632,C_633) != B_632
      | ~ m1_subset_1(C_633,u1_struct_0(A_631))
      | ~ m1_subset_1(B_632,u1_struct_0(A_631))
      | ~ l3_lattices(A_631)
      | ~ v9_lattices(A_631)
      | ~ v8_lattices(A_631)
      | v2_struct_0(A_631) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_4156,plain,(
    ! [B_632] :
      ( r1_lattices('#skF_11',B_632,'#skF_2'('#skF_11'))
      | k2_lattices('#skF_11',B_632,'#skF_2'('#skF_11')) != B_632
      | ~ m1_subset_1(B_632,u1_struct_0('#skF_11'))
      | ~ l3_lattices('#skF_11')
      | ~ v9_lattices('#skF_11')
      | ~ v8_lattices('#skF_11')
      | v2_struct_0('#skF_11') ) ),
    inference(resolution,[status(thm)],[c_3598,c_4154])).

tff(c_4177,plain,(
    ! [B_632] :
      ( r1_lattices('#skF_11',B_632,'#skF_2'('#skF_11'))
      | k2_lattices('#skF_11',B_632,'#skF_2'('#skF_11')) != B_632
      | ~ m1_subset_1(B_632,u1_struct_0('#skF_11'))
      | ~ v9_lattices('#skF_11')
      | ~ v8_lattices('#skF_11')
      | v2_struct_0('#skF_11') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_4156])).

tff(c_4178,plain,(
    ! [B_632] :
      ( r1_lattices('#skF_11',B_632,'#skF_2'('#skF_11'))
      | k2_lattices('#skF_11',B_632,'#skF_2'('#skF_11')) != B_632
      | ~ m1_subset_1(B_632,u1_struct_0('#skF_11'))
      | ~ v9_lattices('#skF_11')
      | ~ v8_lattices('#skF_11') ) ),
    inference(negUnitSimplification,[status(thm)],[c_98,c_4177])).

tff(c_4188,plain,(
    ~ v8_lattices('#skF_11') ),
    inference(splitLeft,[status(thm)],[c_4178])).

tff(c_4191,plain,
    ( ~ v10_lattices('#skF_11')
    | v2_struct_0('#skF_11')
    | ~ l3_lattices('#skF_11') ),
    inference(resolution,[status(thm)],[c_12,c_4188])).

tff(c_4194,plain,(
    v2_struct_0('#skF_11') ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_96,c_4191])).

tff(c_4196,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_98,c_4194])).

tff(c_4198,plain,(
    v8_lattices('#skF_11') ),
    inference(splitRight,[status(thm)],[c_4178])).

tff(c_4197,plain,(
    ! [B_632] :
      ( ~ v9_lattices('#skF_11')
      | r1_lattices('#skF_11',B_632,'#skF_2'('#skF_11'))
      | k2_lattices('#skF_11',B_632,'#skF_2'('#skF_11')) != B_632
      | ~ m1_subset_1(B_632,u1_struct_0('#skF_11')) ) ),
    inference(splitRight,[status(thm)],[c_4178])).

tff(c_4199,plain,(
    ~ v9_lattices('#skF_11') ),
    inference(splitLeft,[status(thm)],[c_4197])).

tff(c_4202,plain,
    ( ~ v10_lattices('#skF_11')
    | v2_struct_0('#skF_11')
    | ~ l3_lattices('#skF_11') ),
    inference(resolution,[status(thm)],[c_10,c_4199])).

tff(c_4205,plain,(
    v2_struct_0('#skF_11') ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_96,c_4202])).

tff(c_4207,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_98,c_4205])).

tff(c_4209,plain,(
    v9_lattices('#skF_11') ),
    inference(splitRight,[status(thm)],[c_4197])).

tff(c_3625,plain,(
    ! [A_598,C_599,B_600] :
      ( k2_lattices(A_598,C_599,B_600) = k2_lattices(A_598,B_600,C_599)
      | ~ m1_subset_1(C_599,u1_struct_0(A_598))
      | ~ m1_subset_1(B_600,u1_struct_0(A_598))
      | ~ v6_lattices(A_598)
      | ~ l1_lattices(A_598)
      | v2_struct_0(A_598) ) ),
    inference(cnfTransformation,[status(thm)],[f_205])).

tff(c_3627,plain,(
    ! [B_600] :
      ( k2_lattices('#skF_11',B_600,'#skF_2'('#skF_11')) = k2_lattices('#skF_11','#skF_2'('#skF_11'),B_600)
      | ~ m1_subset_1(B_600,u1_struct_0('#skF_11'))
      | ~ v6_lattices('#skF_11')
      | ~ l1_lattices('#skF_11')
      | v2_struct_0('#skF_11') ) ),
    inference(resolution,[status(thm)],[c_3598,c_3625])).

tff(c_3648,plain,(
    ! [B_600] :
      ( k2_lattices('#skF_11',B_600,'#skF_2'('#skF_11')) = k2_lattices('#skF_11','#skF_2'('#skF_11'),B_600)
      | ~ m1_subset_1(B_600,u1_struct_0('#skF_11'))
      | ~ v6_lattices('#skF_11')
      | v2_struct_0('#skF_11') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_106,c_3627])).

tff(c_3649,plain,(
    ! [B_600] :
      ( k2_lattices('#skF_11',B_600,'#skF_2'('#skF_11')) = k2_lattices('#skF_11','#skF_2'('#skF_11'),B_600)
      | ~ m1_subset_1(B_600,u1_struct_0('#skF_11'))
      | ~ v6_lattices('#skF_11') ) ),
    inference(negUnitSimplification,[status(thm)],[c_98,c_3648])).

tff(c_3717,plain,(
    ~ v6_lattices('#skF_11') ),
    inference(splitLeft,[status(thm)],[c_3649])).

tff(c_3720,plain,
    ( ~ v10_lattices('#skF_11')
    | v2_struct_0('#skF_11')
    | ~ l3_lattices('#skF_11') ),
    inference(resolution,[status(thm)],[c_16,c_3717])).

tff(c_3723,plain,(
    v2_struct_0('#skF_11') ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_96,c_3720])).

tff(c_3725,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_98,c_3723])).

tff(c_3728,plain,(
    ! [B_603] :
      ( k2_lattices('#skF_11',B_603,'#skF_2'('#skF_11')) = k2_lattices('#skF_11','#skF_2'('#skF_11'),B_603)
      | ~ m1_subset_1(B_603,u1_struct_0('#skF_11')) ) ),
    inference(splitRight,[status(thm)],[c_3649])).

tff(c_3751,plain,(
    ! [B_73] :
      ( k2_lattices('#skF_11','#skF_5'('#skF_11',B_73),'#skF_2'('#skF_11')) = k2_lattices('#skF_11','#skF_2'('#skF_11'),'#skF_5'('#skF_11',B_73))
      | ~ v4_lattice3('#skF_11')
      | ~ l3_lattices('#skF_11')
      | v2_struct_0('#skF_11') ) ),
    inference(resolution,[status(thm)],[c_70,c_3728])).

tff(c_3788,plain,(
    ! [B_73] :
      ( k2_lattices('#skF_11','#skF_5'('#skF_11',B_73),'#skF_2'('#skF_11')) = k2_lattices('#skF_11','#skF_2'('#skF_11'),'#skF_5'('#skF_11',B_73))
      | v2_struct_0('#skF_11') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_94,c_3751])).

tff(c_3806,plain,(
    ! [B_604] : k2_lattices('#skF_11','#skF_5'('#skF_11',B_604),'#skF_2'('#skF_11')) = k2_lattices('#skF_11','#skF_2'('#skF_11'),'#skF_5'('#skF_11',B_604)) ),
    inference(negUnitSimplification,[status(thm)],[c_98,c_3788])).

tff(c_3326,plain,(
    ! [A_544,C_545] :
      ( k2_lattices(A_544,'#skF_2'(A_544),C_545) = '#skF_2'(A_544)
      | ~ m1_subset_1(C_545,u1_struct_0(A_544))
      | ~ v13_lattices(A_544)
      | ~ l1_lattices(A_544)
      | v2_struct_0(A_544) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_3340,plain,(
    ! [A_58,B_73] :
      ( k2_lattices(A_58,'#skF_2'(A_58),'#skF_5'(A_58,B_73)) = '#skF_2'(A_58)
      | ~ v13_lattices(A_58)
      | ~ l1_lattices(A_58)
      | ~ v4_lattice3(A_58)
      | ~ l3_lattices(A_58)
      | v2_struct_0(A_58) ) ),
    inference(resolution,[status(thm)],[c_70,c_3326])).

tff(c_3818,plain,(
    ! [B_604] :
      ( k2_lattices('#skF_11','#skF_5'('#skF_11',B_604),'#skF_2'('#skF_11')) = '#skF_2'('#skF_11')
      | ~ v13_lattices('#skF_11')
      | ~ l1_lattices('#skF_11')
      | ~ v4_lattice3('#skF_11')
      | ~ l3_lattices('#skF_11')
      | v2_struct_0('#skF_11') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3806,c_3340])).

tff(c_3839,plain,(
    ! [B_604] :
      ( k2_lattices('#skF_11','#skF_5'('#skF_11',B_604),'#skF_2'('#skF_11')) = '#skF_2'('#skF_11')
      | v2_struct_0('#skF_11') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_94,c_106,c_3250,c_3818])).

tff(c_3840,plain,(
    ! [B_604] : k2_lattices('#skF_11','#skF_5'('#skF_11',B_604),'#skF_2'('#skF_11')) = '#skF_2'('#skF_11') ),
    inference(negUnitSimplification,[status(thm)],[c_98,c_3839])).

tff(c_4221,plain,(
    ! [A_639,B_640,C_641] :
      ( k2_lattices(A_639,B_640,C_641) = B_640
      | ~ r1_lattices(A_639,B_640,C_641)
      | ~ m1_subset_1(C_641,u1_struct_0(A_639))
      | ~ m1_subset_1(B_640,u1_struct_0(A_639))
      | ~ l3_lattices(A_639)
      | ~ v9_lattices(A_639)
      | ~ v8_lattices(A_639)
      | v2_struct_0(A_639) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_5291,plain,(
    ! [A_754,B_755,D_756] :
      ( k2_lattices(A_754,'#skF_5'(A_754,B_755),D_756) = '#skF_5'(A_754,B_755)
      | ~ m1_subset_1('#skF_5'(A_754,B_755),u1_struct_0(A_754))
      | ~ v9_lattices(A_754)
      | ~ v8_lattices(A_754)
      | ~ r4_lattice3(A_754,D_756,B_755)
      | ~ m1_subset_1(D_756,u1_struct_0(A_754))
      | ~ v4_lattice3(A_754)
      | ~ l3_lattices(A_754)
      | v2_struct_0(A_754) ) ),
    inference(resolution,[status(thm)],[c_66,c_4221])).

tff(c_5295,plain,(
    ! [A_757,B_758,D_759] :
      ( k2_lattices(A_757,'#skF_5'(A_757,B_758),D_759) = '#skF_5'(A_757,B_758)
      | ~ v9_lattices(A_757)
      | ~ v8_lattices(A_757)
      | ~ r4_lattice3(A_757,D_759,B_758)
      | ~ m1_subset_1(D_759,u1_struct_0(A_757))
      | ~ v4_lattice3(A_757)
      | ~ l3_lattices(A_757)
      | v2_struct_0(A_757) ) ),
    inference(resolution,[status(thm)],[c_70,c_5291])).

tff(c_5299,plain,(
    ! [B_758] :
      ( k2_lattices('#skF_11','#skF_5'('#skF_11',B_758),'#skF_2'('#skF_11')) = '#skF_5'('#skF_11',B_758)
      | ~ v9_lattices('#skF_11')
      | ~ v8_lattices('#skF_11')
      | ~ r4_lattice3('#skF_11','#skF_2'('#skF_11'),B_758)
      | ~ v4_lattice3('#skF_11')
      | ~ l3_lattices('#skF_11')
      | v2_struct_0('#skF_11') ) ),
    inference(resolution,[status(thm)],[c_3598,c_5295])).

tff(c_5321,plain,(
    ! [B_758] :
      ( '#skF_5'('#skF_11',B_758) = '#skF_2'('#skF_11')
      | ~ r4_lattice3('#skF_11','#skF_2'('#skF_11'),B_758)
      | v2_struct_0('#skF_11') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_94,c_4198,c_4209,c_3840,c_5299])).

tff(c_5332,plain,(
    ! [B_760] :
      ( '#skF_5'('#skF_11',B_760) = '#skF_2'('#skF_11')
      | ~ r4_lattice3('#skF_11','#skF_2'('#skF_11'),B_760) ) ),
    inference(negUnitSimplification,[status(thm)],[c_98,c_5321])).

tff(c_5344,plain,(
    '#skF_2'('#skF_11') = '#skF_5'('#skF_11',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_3589,c_5332])).

tff(c_3249,plain,(
    k15_lattice3('#skF_11',k1_xboole_0) != k5_lattices('#skF_11') ),
    inference(splitRight,[status(thm)],[c_101])).

tff(c_3565,plain,(
    k15_lattice3('#skF_11',k1_xboole_0) != '#skF_2'('#skF_11') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3564,c_3249])).

tff(c_5367,plain,(
    k15_lattice3('#skF_11',k1_xboole_0) != '#skF_5'('#skF_11',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5344,c_3565])).

tff(c_5365,plain,(
    r4_lattice3('#skF_11','#skF_5'('#skF_11',k1_xboole_0),k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5344,c_3589])).

tff(c_5366,plain,(
    m1_subset_1('#skF_5'('#skF_11',k1_xboole_0),u1_struct_0('#skF_11')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5344,c_3598])).

tff(c_4687,plain,(
    ! [A_687,B_688,C_689] :
      ( m1_subset_1('#skF_8'(A_687,B_688,C_689),u1_struct_0(A_687))
      | k15_lattice3(A_687,B_688) = C_689
      | ~ r4_lattice3(A_687,C_689,B_688)
      | ~ m1_subset_1(C_689,u1_struct_0(A_687))
      | ~ v4_lattice3(A_687)
      | ~ v10_lattices(A_687)
      | ~ l3_lattices(A_687)
      | v2_struct_0(A_687) ) ),
    inference(cnfTransformation,[status(thm)],[f_190])).

tff(c_50,plain,(
    ! [A_25,C_33] :
      ( k2_lattices(A_25,'#skF_2'(A_25),C_33) = '#skF_2'(A_25)
      | ~ m1_subset_1(C_33,u1_struct_0(A_25))
      | ~ v13_lattices(A_25)
      | ~ l1_lattices(A_25)
      | v2_struct_0(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_5914,plain,(
    ! [A_770,B_771,C_772] :
      ( k2_lattices(A_770,'#skF_2'(A_770),'#skF_8'(A_770,B_771,C_772)) = '#skF_2'(A_770)
      | ~ v13_lattices(A_770)
      | ~ l1_lattices(A_770)
      | k15_lattice3(A_770,B_771) = C_772
      | ~ r4_lattice3(A_770,C_772,B_771)
      | ~ m1_subset_1(C_772,u1_struct_0(A_770))
      | ~ v4_lattice3(A_770)
      | ~ v10_lattices(A_770)
      | ~ l3_lattices(A_770)
      | v2_struct_0(A_770) ) ),
    inference(resolution,[status(thm)],[c_4687,c_50])).

tff(c_5923,plain,(
    ! [B_771,C_772] :
      ( k2_lattices('#skF_11','#skF_5'('#skF_11',k1_xboole_0),'#skF_8'('#skF_11',B_771,C_772)) = '#skF_2'('#skF_11')
      | ~ v13_lattices('#skF_11')
      | ~ l1_lattices('#skF_11')
      | k15_lattice3('#skF_11',B_771) = C_772
      | ~ r4_lattice3('#skF_11',C_772,B_771)
      | ~ m1_subset_1(C_772,u1_struct_0('#skF_11'))
      | ~ v4_lattice3('#skF_11')
      | ~ v10_lattices('#skF_11')
      | ~ l3_lattices('#skF_11')
      | v2_struct_0('#skF_11') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5344,c_5914])).

tff(c_5927,plain,(
    ! [B_771,C_772] :
      ( k2_lattices('#skF_11','#skF_5'('#skF_11',k1_xboole_0),'#skF_8'('#skF_11',B_771,C_772)) = '#skF_5'('#skF_11',k1_xboole_0)
      | k15_lattice3('#skF_11',B_771) = C_772
      | ~ r4_lattice3('#skF_11',C_772,B_771)
      | ~ m1_subset_1(C_772,u1_struct_0('#skF_11'))
      | v2_struct_0('#skF_11') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_96,c_94,c_106,c_3250,c_5344,c_5923])).

tff(c_5928,plain,(
    ! [B_771,C_772] :
      ( k2_lattices('#skF_11','#skF_5'('#skF_11',k1_xboole_0),'#skF_8'('#skF_11',B_771,C_772)) = '#skF_5'('#skF_11',k1_xboole_0)
      | k15_lattice3('#skF_11',B_771) = C_772
      | ~ r4_lattice3('#skF_11',C_772,B_771)
      | ~ m1_subset_1(C_772,u1_struct_0('#skF_11')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_98,c_5927])).

tff(c_38,plain,(
    ! [A_18,B_22,C_24] :
      ( r1_lattices(A_18,B_22,C_24)
      | k2_lattices(A_18,B_22,C_24) != B_22
      | ~ m1_subset_1(C_24,u1_struct_0(A_18))
      | ~ m1_subset_1(B_22,u1_struct_0(A_18))
      | ~ l3_lattices(A_18)
      | ~ v9_lattices(A_18)
      | ~ v8_lattices(A_18)
      | v2_struct_0(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_7234,plain,(
    ! [A_910,B_911,B_912,C_913] :
      ( r1_lattices(A_910,B_911,'#skF_8'(A_910,B_912,C_913))
      | k2_lattices(A_910,B_911,'#skF_8'(A_910,B_912,C_913)) != B_911
      | ~ m1_subset_1(B_911,u1_struct_0(A_910))
      | ~ v9_lattices(A_910)
      | ~ v8_lattices(A_910)
      | k15_lattice3(A_910,B_912) = C_913
      | ~ r4_lattice3(A_910,C_913,B_912)
      | ~ m1_subset_1(C_913,u1_struct_0(A_910))
      | ~ v4_lattice3(A_910)
      | ~ v10_lattices(A_910)
      | ~ l3_lattices(A_910)
      | v2_struct_0(A_910) ) ),
    inference(resolution,[status(thm)],[c_4687,c_38])).

tff(c_72,plain,(
    ! [A_84,C_92,B_91] :
      ( ~ r1_lattices(A_84,C_92,'#skF_8'(A_84,B_91,C_92))
      | k15_lattice3(A_84,B_91) = C_92
      | ~ r4_lattice3(A_84,C_92,B_91)
      | ~ m1_subset_1(C_92,u1_struct_0(A_84))
      | ~ v4_lattice3(A_84)
      | ~ v10_lattices(A_84)
      | ~ l3_lattices(A_84)
      | v2_struct_0(A_84) ) ),
    inference(cnfTransformation,[status(thm)],[f_190])).

tff(c_7248,plain,(
    ! [A_914,C_915,B_916] :
      ( k2_lattices(A_914,C_915,'#skF_8'(A_914,B_916,C_915)) != C_915
      | ~ v9_lattices(A_914)
      | ~ v8_lattices(A_914)
      | k15_lattice3(A_914,B_916) = C_915
      | ~ r4_lattice3(A_914,C_915,B_916)
      | ~ m1_subset_1(C_915,u1_struct_0(A_914))
      | ~ v4_lattice3(A_914)
      | ~ v10_lattices(A_914)
      | ~ l3_lattices(A_914)
      | v2_struct_0(A_914) ) ),
    inference(resolution,[status(thm)],[c_7234,c_72])).

tff(c_7254,plain,(
    ! [B_771] :
      ( ~ v9_lattices('#skF_11')
      | ~ v8_lattices('#skF_11')
      | ~ v4_lattice3('#skF_11')
      | ~ v10_lattices('#skF_11')
      | ~ l3_lattices('#skF_11')
      | v2_struct_0('#skF_11')
      | k15_lattice3('#skF_11',B_771) = '#skF_5'('#skF_11',k1_xboole_0)
      | ~ r4_lattice3('#skF_11','#skF_5'('#skF_11',k1_xboole_0),B_771)
      | ~ m1_subset_1('#skF_5'('#skF_11',k1_xboole_0),u1_struct_0('#skF_11')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5928,c_7248])).

tff(c_7261,plain,(
    ! [B_771] :
      ( v2_struct_0('#skF_11')
      | k15_lattice3('#skF_11',B_771) = '#skF_5'('#skF_11',k1_xboole_0)
      | ~ r4_lattice3('#skF_11','#skF_5'('#skF_11',k1_xboole_0),B_771) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5366,c_92,c_96,c_94,c_4198,c_4209,c_7254])).

tff(c_7264,plain,(
    ! [B_917] :
      ( k15_lattice3('#skF_11',B_917) = '#skF_5'('#skF_11',k1_xboole_0)
      | ~ r4_lattice3('#skF_11','#skF_5'('#skF_11',k1_xboole_0),B_917) ) ),
    inference(negUnitSimplification,[status(thm)],[c_98,c_7261])).

tff(c_7270,plain,(
    k15_lattice3('#skF_11',k1_xboole_0) = '#skF_5'('#skF_11',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_5365,c_7264])).

tff(c_7283,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_5367,c_7270])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n012.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 14:40:22 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 10.38/3.31  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.38/3.33  
% 10.38/3.33  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.38/3.34  %$ r4_lattice3 > r1_lattices > r2_hidden > m1_subset_1 > v9_lattices > v8_lattices > v7_lattices > v6_lattices > v5_lattices > v4_lattices > v4_lattice3 > v2_struct_0 > v13_lattices > v10_lattices > l3_lattices > l2_lattices > l1_lattices > k2_lattices > k2_zfmisc_1 > k15_lattice3 > #nlpp > u1_struct_0 > k5_lattices > k1_xboole_0 > #skF_9 > #skF_2 > #skF_11 > #skF_4 > #skF_3 > #skF_10 > #skF_8 > #skF_7 > #skF_1 > #skF_5 > #skF_6
% 10.38/3.34  
% 10.38/3.34  %Foreground sorts:
% 10.38/3.34  
% 10.38/3.34  
% 10.38/3.34  %Background operators:
% 10.38/3.34  
% 10.38/3.34  
% 10.38/3.34  %Foreground operators:
% 10.38/3.34  tff(l3_lattices, type, l3_lattices: $i > $o).
% 10.38/3.34  tff('#skF_9', type, '#skF_9': $i > $i).
% 10.38/3.34  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 10.38/3.34  tff(k2_lattices, type, k2_lattices: ($i * $i * $i) > $i).
% 10.38/3.34  tff(l2_lattices, type, l2_lattices: $i > $o).
% 10.38/3.34  tff('#skF_2', type, '#skF_2': $i > $i).
% 10.38/3.34  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 10.38/3.34  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 10.38/3.34  tff('#skF_11', type, '#skF_11': $i).
% 10.38/3.34  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 10.38/3.34  tff(k15_lattice3, type, k15_lattice3: ($i * $i) > $i).
% 10.38/3.34  tff(l1_lattices, type, l1_lattices: $i > $o).
% 10.38/3.34  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 10.38/3.34  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 10.38/3.34  tff(r1_lattices, type, r1_lattices: ($i * $i * $i) > $o).
% 10.38/3.34  tff(v4_lattices, type, v4_lattices: $i > $o).
% 10.38/3.34  tff('#skF_10', type, '#skF_10': $i > $i).
% 10.38/3.34  tff(v6_lattices, type, v6_lattices: $i > $o).
% 10.38/3.34  tff(v9_lattices, type, v9_lattices: $i > $o).
% 10.38/3.34  tff(r4_lattice3, type, r4_lattice3: ($i * $i * $i) > $o).
% 10.38/3.34  tff(v4_lattice3, type, v4_lattice3: $i > $o).
% 10.38/3.34  tff(v5_lattices, type, v5_lattices: $i > $o).
% 10.38/3.34  tff(v10_lattices, type, v10_lattices: $i > $o).
% 10.38/3.34  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 10.38/3.34  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 10.38/3.34  tff(v13_lattices, type, v13_lattices: $i > $o).
% 10.38/3.34  tff(v8_lattices, type, v8_lattices: $i > $o).
% 10.38/3.34  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 10.38/3.34  tff(k5_lattices, type, k5_lattices: $i > $i).
% 10.38/3.34  tff('#skF_8', type, '#skF_8': ($i * $i * $i) > $i).
% 10.38/3.34  tff('#skF_7', type, '#skF_7': ($i * $i) > $i).
% 10.38/3.34  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 10.38/3.34  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 10.38/3.34  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 10.38/3.34  tff('#skF_6', type, '#skF_6': $i > $i).
% 10.38/3.34  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 10.38/3.34  tff(v7_lattices, type, v7_lattices: $i > $o).
% 10.38/3.34  
% 10.78/3.37  tff(f_226, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v10_lattices(A)) & v4_lattice3(A)) & l3_lattices(A)) => ((((~v2_struct_0(A) & v10_lattices(A)) & v13_lattices(A)) & l3_lattices(A)) & (k5_lattices(A) = k15_lattice3(A, k1_xboole_0))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t50_lattice3)).
% 10.78/3.37  tff(f_88, axiom, (![A]: (l3_lattices(A) => (l1_lattices(A) & l2_lattices(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l3_lattices)).
% 10.78/3.37  tff(f_162, axiom, (![A]: ((~v2_struct_0(A) & l3_lattices(A)) => (v4_lattice3(A) <=> (![B]: (?[C]: ((m1_subset_1(C, u1_struct_0(A)) & r4_lattice3(A, C, B)) & (![D]: (m1_subset_1(D, u1_struct_0(A)) => (r4_lattice3(A, D, B) => r1_lattices(A, C, D)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d18_lattice3)).
% 10.78/3.37  tff(f_142, axiom, (![A]: ((~v2_struct_0(A) & l3_lattices(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (r4_lattice3(A, B, C) <=> (![D]: (m1_subset_1(D, u1_struct_0(A)) => (r2_hidden(D, C) => r1_lattices(A, D, B)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d17_lattice3)).
% 10.78/3.37  tff(f_31, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 10.78/3.37  tff(f_34, axiom, (![A, B]: ~r2_hidden(A, k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t152_zfmisc_1)).
% 10.78/3.37  tff(f_190, axiom, (![A]: ((~v2_struct_0(A) & l3_lattices(A)) => ((((~v2_struct_0(A) & v10_lattices(A)) & v4_lattice3(A)) & l3_lattices(A)) => (![B, C]: (m1_subset_1(C, u1_struct_0(A)) => ((C = k15_lattice3(A, B)) <=> (r4_lattice3(A, C, B) & (![D]: (m1_subset_1(D, u1_struct_0(A)) => (r4_lattice3(A, D, B) => r1_lattices(A, C, D))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d21_lattice3)).
% 10.78/3.37  tff(f_124, axiom, (![A]: ((~v2_struct_0(A) & l1_lattices(A)) => (v13_lattices(A) <=> (?[B]: (m1_subset_1(B, u1_struct_0(A)) & (![C]: (m1_subset_1(C, u1_struct_0(A)) => ((k2_lattices(A, B, C) = B) & (k2_lattices(A, C, B) = B))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d13_lattices)).
% 10.78/3.37  tff(f_56, axiom, (![A]: (l3_lattices(A) => ((~v2_struct_0(A) & v10_lattices(A)) => ((((((~v2_struct_0(A) & v4_lattices(A)) & v5_lattices(A)) & v6_lattices(A)) & v7_lattices(A)) & v8_lattices(A)) & v9_lattices(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_lattices)).
% 10.78/3.37  tff(f_82, axiom, (![A]: ((~v2_struct_0(A) & l1_lattices(A)) => m1_subset_1(k5_lattices(A), u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k5_lattices)).
% 10.78/3.37  tff(f_205, axiom, (![A]: ((~v2_struct_0(A) & l1_lattices(A)) => (v6_lattices(A) <=> (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (k2_lattices(A, B, C) = k2_lattices(A, C, B))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d6_lattices)).
% 10.78/3.37  tff(f_107, axiom, (![A]: ((((~v2_struct_0(A) & v8_lattices(A)) & v9_lattices(A)) & l3_lattices(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r1_lattices(A, B, C) <=> (k2_lattices(A, B, C) = B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t21_lattices)).
% 10.78/3.37  tff(f_75, axiom, (![A]: ((~v2_struct_0(A) & l1_lattices(A)) => (v13_lattices(A) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => ((B = k5_lattices(A)) <=> (![C]: (m1_subset_1(C, u1_struct_0(A)) => ((k2_lattices(A, B, C) = B) & (k2_lattices(A, C, B) = B)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d16_lattices)).
% 10.78/3.37  tff(c_98, plain, (~v2_struct_0('#skF_11')), inference(cnfTransformation, [status(thm)], [f_226])).
% 10.78/3.37  tff(c_92, plain, (l3_lattices('#skF_11')), inference(cnfTransformation, [status(thm)], [f_226])).
% 10.78/3.37  tff(c_102, plain, (![A_107]: (l1_lattices(A_107) | ~l3_lattices(A_107))), inference(cnfTransformation, [status(thm)], [f_88])).
% 10.78/3.37  tff(c_106, plain, (l1_lattices('#skF_11')), inference(resolution, [status(thm)], [c_92, c_102])).
% 10.78/3.37  tff(c_96, plain, (v10_lattices('#skF_11')), inference(cnfTransformation, [status(thm)], [f_226])).
% 10.78/3.37  tff(c_90, plain, (k15_lattice3('#skF_11', k1_xboole_0)!=k5_lattices('#skF_11') | ~l3_lattices('#skF_11') | ~v13_lattices('#skF_11') | ~v10_lattices('#skF_11') | v2_struct_0('#skF_11')), inference(cnfTransformation, [status(thm)], [f_226])).
% 10.78/3.37  tff(c_100, plain, (k15_lattice3('#skF_11', k1_xboole_0)!=k5_lattices('#skF_11') | ~v13_lattices('#skF_11') | v2_struct_0('#skF_11')), inference(demodulation, [status(thm), theory('equality')], [c_96, c_92, c_90])).
% 10.78/3.37  tff(c_101, plain, (k15_lattice3('#skF_11', k1_xboole_0)!=k5_lattices('#skF_11') | ~v13_lattices('#skF_11')), inference(negUnitSimplification, [status(thm)], [c_98, c_100])).
% 10.78/3.37  tff(c_119, plain, (~v13_lattices('#skF_11')), inference(splitLeft, [status(thm)], [c_101])).
% 10.78/3.37  tff(c_94, plain, (v4_lattice3('#skF_11')), inference(cnfTransformation, [status(thm)], [f_226])).
% 10.78/3.37  tff(c_70, plain, (![A_58, B_73]: (m1_subset_1('#skF_5'(A_58, B_73), u1_struct_0(A_58)) | ~v4_lattice3(A_58) | ~l3_lattices(A_58) | v2_struct_0(A_58))), inference(cnfTransformation, [status(thm)], [f_162])).
% 10.78/3.37  tff(c_241, plain, (![A_140, B_141, C_142]: (r2_hidden('#skF_4'(A_140, B_141, C_142), C_142) | r4_lattice3(A_140, B_141, C_142) | ~m1_subset_1(B_141, u1_struct_0(A_140)) | ~l3_lattices(A_140) | v2_struct_0(A_140))), inference(cnfTransformation, [status(thm)], [f_142])).
% 10.78/3.37  tff(c_4, plain, (![A_1]: (k2_zfmisc_1(A_1, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 10.78/3.37  tff(c_135, plain, (![A_111, B_112]: (~r2_hidden(A_111, k2_zfmisc_1(A_111, B_112)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 10.78/3.37  tff(c_141, plain, (![A_1]: (~r2_hidden(A_1, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_4, c_135])).
% 10.78/3.37  tff(c_247, plain, (![A_143, B_144]: (r4_lattice3(A_143, B_144, k1_xboole_0) | ~m1_subset_1(B_144, u1_struct_0(A_143)) | ~l3_lattices(A_143) | v2_struct_0(A_143))), inference(resolution, [status(thm)], [c_241, c_141])).
% 10.78/3.37  tff(c_267, plain, (![A_58, B_73]: (r4_lattice3(A_58, '#skF_5'(A_58, B_73), k1_xboole_0) | ~v4_lattice3(A_58) | ~l3_lattices(A_58) | v2_struct_0(A_58))), inference(resolution, [status(thm)], [c_70, c_247])).
% 10.78/3.37  tff(c_76, plain, (![A_84, B_91, C_92]: (m1_subset_1('#skF_8'(A_84, B_91, C_92), u1_struct_0(A_84)) | k15_lattice3(A_84, B_91)=C_92 | ~r4_lattice3(A_84, C_92, B_91) | ~m1_subset_1(C_92, u1_struct_0(A_84)) | ~v4_lattice3(A_84) | ~v10_lattices(A_84) | ~l3_lattices(A_84) | v2_struct_0(A_84))), inference(cnfTransformation, [status(thm)], [f_190])).
% 10.78/3.37  tff(c_74, plain, (![A_84, B_91, C_92]: (r4_lattice3(A_84, '#skF_8'(A_84, B_91, C_92), B_91) | k15_lattice3(A_84, B_91)=C_92 | ~r4_lattice3(A_84, C_92, B_91) | ~m1_subset_1(C_92, u1_struct_0(A_84)) | ~v4_lattice3(A_84) | ~v10_lattices(A_84) | ~l3_lattices(A_84) | v2_struct_0(A_84))), inference(cnfTransformation, [status(thm)], [f_190])).
% 10.78/3.37  tff(c_66, plain, (![A_58, B_73, D_78]: (r1_lattices(A_58, '#skF_5'(A_58, B_73), D_78) | ~r4_lattice3(A_58, D_78, B_73) | ~m1_subset_1(D_78, u1_struct_0(A_58)) | ~v4_lattice3(A_58) | ~l3_lattices(A_58) | v2_struct_0(A_58))), inference(cnfTransformation, [status(thm)], [f_162])).
% 10.78/3.37  tff(c_937, plain, (![A_265, C_266, B_267]: (~r1_lattices(A_265, C_266, '#skF_8'(A_265, B_267, C_266)) | k15_lattice3(A_265, B_267)=C_266 | ~r4_lattice3(A_265, C_266, B_267) | ~m1_subset_1(C_266, u1_struct_0(A_265)) | ~v4_lattice3(A_265) | ~v10_lattices(A_265) | ~l3_lattices(A_265) | v2_struct_0(A_265))), inference(cnfTransformation, [status(thm)], [f_190])).
% 10.78/3.37  tff(c_2096, plain, (![A_479, B_480, B_481]: (k15_lattice3(A_479, B_480)='#skF_5'(A_479, B_481) | ~r4_lattice3(A_479, '#skF_5'(A_479, B_481), B_480) | ~m1_subset_1('#skF_5'(A_479, B_481), u1_struct_0(A_479)) | ~v10_lattices(A_479) | ~r4_lattice3(A_479, '#skF_8'(A_479, B_480, '#skF_5'(A_479, B_481)), B_481) | ~m1_subset_1('#skF_8'(A_479, B_480, '#skF_5'(A_479, B_481)), u1_struct_0(A_479)) | ~v4_lattice3(A_479) | ~l3_lattices(A_479) | v2_struct_0(A_479))), inference(resolution, [status(thm)], [c_66, c_937])).
% 10.78/3.37  tff(c_2118, plain, (![A_484, B_485]: (~m1_subset_1('#skF_8'(A_484, B_485, '#skF_5'(A_484, B_485)), u1_struct_0(A_484)) | k15_lattice3(A_484, B_485)='#skF_5'(A_484, B_485) | ~r4_lattice3(A_484, '#skF_5'(A_484, B_485), B_485) | ~m1_subset_1('#skF_5'(A_484, B_485), u1_struct_0(A_484)) | ~v4_lattice3(A_484) | ~v10_lattices(A_484) | ~l3_lattices(A_484) | v2_struct_0(A_484))), inference(resolution, [status(thm)], [c_74, c_2096])).
% 10.78/3.37  tff(c_2124, plain, (![A_486, B_487]: (k15_lattice3(A_486, B_487)='#skF_5'(A_486, B_487) | ~r4_lattice3(A_486, '#skF_5'(A_486, B_487), B_487) | ~m1_subset_1('#skF_5'(A_486, B_487), u1_struct_0(A_486)) | ~v4_lattice3(A_486) | ~v10_lattices(A_486) | ~l3_lattices(A_486) | v2_struct_0(A_486))), inference(resolution, [status(thm)], [c_76, c_2118])).
% 10.78/3.37  tff(c_2132, plain, (![A_488]: (k15_lattice3(A_488, k1_xboole_0)='#skF_5'(A_488, k1_xboole_0) | ~m1_subset_1('#skF_5'(A_488, k1_xboole_0), u1_struct_0(A_488)) | ~v10_lattices(A_488) | ~v4_lattice3(A_488) | ~l3_lattices(A_488) | v2_struct_0(A_488))), inference(resolution, [status(thm)], [c_267, c_2124])).
% 10.78/3.37  tff(c_2138, plain, (![A_489]: (k15_lattice3(A_489, k1_xboole_0)='#skF_5'(A_489, k1_xboole_0) | ~v10_lattices(A_489) | ~v4_lattice3(A_489) | ~l3_lattices(A_489) | v2_struct_0(A_489))), inference(resolution, [status(thm)], [c_70, c_2132])).
% 10.78/3.37  tff(c_2141, plain, (k15_lattice3('#skF_11', k1_xboole_0)='#skF_5'('#skF_11', k1_xboole_0) | ~v10_lattices('#skF_11') | ~l3_lattices('#skF_11') | v2_struct_0('#skF_11')), inference(resolution, [status(thm)], [c_94, c_2138])).
% 10.78/3.37  tff(c_2144, plain, (k15_lattice3('#skF_11', k1_xboole_0)='#skF_5'('#skF_11', k1_xboole_0) | v2_struct_0('#skF_11')), inference(demodulation, [status(thm), theory('equality')], [c_92, c_96, c_2141])).
% 10.78/3.37  tff(c_2145, plain, (k15_lattice3('#skF_11', k1_xboole_0)='#skF_5'('#skF_11', k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_98, c_2144])).
% 10.78/3.37  tff(c_80, plain, (![A_84, B_91]: (r4_lattice3(A_84, k15_lattice3(A_84, B_91), B_91) | ~m1_subset_1(k15_lattice3(A_84, B_91), u1_struct_0(A_84)) | ~v4_lattice3(A_84) | ~v10_lattices(A_84) | ~l3_lattices(A_84) | v2_struct_0(A_84))), inference(cnfTransformation, [status(thm)], [f_190])).
% 10.78/3.37  tff(c_2150, plain, (r4_lattice3('#skF_11', k15_lattice3('#skF_11', k1_xboole_0), k1_xboole_0) | ~m1_subset_1('#skF_5'('#skF_11', k1_xboole_0), u1_struct_0('#skF_11')) | ~v4_lattice3('#skF_11') | ~v10_lattices('#skF_11') | ~l3_lattices('#skF_11') | v2_struct_0('#skF_11')), inference(superposition, [status(thm), theory('equality')], [c_2145, c_80])).
% 10.78/3.37  tff(c_2157, plain, (r4_lattice3('#skF_11', '#skF_5'('#skF_11', k1_xboole_0), k1_xboole_0) | ~m1_subset_1('#skF_5'('#skF_11', k1_xboole_0), u1_struct_0('#skF_11')) | v2_struct_0('#skF_11')), inference(demodulation, [status(thm), theory('equality')], [c_92, c_96, c_94, c_2145, c_2150])).
% 10.78/3.37  tff(c_2158, plain, (r4_lattice3('#skF_11', '#skF_5'('#skF_11', k1_xboole_0), k1_xboole_0) | ~m1_subset_1('#skF_5'('#skF_11', k1_xboole_0), u1_struct_0('#skF_11'))), inference(negUnitSimplification, [status(thm)], [c_98, c_2157])).
% 10.78/3.37  tff(c_2160, plain, (~m1_subset_1('#skF_5'('#skF_11', k1_xboole_0), u1_struct_0('#skF_11'))), inference(splitLeft, [status(thm)], [c_2158])).
% 10.78/3.37  tff(c_2163, plain, (~v4_lattice3('#skF_11') | ~l3_lattices('#skF_11') | v2_struct_0('#skF_11')), inference(resolution, [status(thm)], [c_70, c_2160])).
% 10.78/3.37  tff(c_2166, plain, (v2_struct_0('#skF_11')), inference(demodulation, [status(thm), theory('equality')], [c_92, c_94, c_2163])).
% 10.78/3.37  tff(c_2168, plain, $false, inference(negUnitSimplification, [status(thm)], [c_98, c_2166])).
% 10.78/3.37  tff(c_2170, plain, (m1_subset_1('#skF_5'('#skF_11', k1_xboole_0), u1_struct_0('#skF_11'))), inference(splitRight, [status(thm)], [c_2158])).
% 10.78/3.37  tff(c_44, plain, (![A_25, B_34]: (m1_subset_1('#skF_3'(A_25, B_34), u1_struct_0(A_25)) | v13_lattices(A_25) | ~m1_subset_1(B_34, u1_struct_0(A_25)) | ~l1_lattices(A_25) | v2_struct_0(A_25))), inference(cnfTransformation, [status(thm)], [f_124])).
% 10.78/3.37  tff(c_266, plain, (![A_25, B_34]: (r4_lattice3(A_25, '#skF_3'(A_25, B_34), k1_xboole_0) | ~l3_lattices(A_25) | v13_lattices(A_25) | ~m1_subset_1(B_34, u1_struct_0(A_25)) | ~l1_lattices(A_25) | v2_struct_0(A_25))), inference(resolution, [status(thm)], [c_44, c_247])).
% 10.78/3.37  tff(c_12, plain, (![A_5]: (v8_lattices(A_5) | ~v10_lattices(A_5) | v2_struct_0(A_5) | ~l3_lattices(A_5))), inference(cnfTransformation, [status(thm)], [f_56])).
% 10.78/3.37  tff(c_32, plain, (![A_16]: (m1_subset_1(k5_lattices(A_16), u1_struct_0(A_16)) | ~l1_lattices(A_16) | v2_struct_0(A_16))), inference(cnfTransformation, [status(thm)], [f_82])).
% 10.78/3.37  tff(c_271, plain, (![A_16]: (r4_lattice3(A_16, k5_lattices(A_16), k1_xboole_0) | ~l3_lattices(A_16) | ~l1_lattices(A_16) | v2_struct_0(A_16))), inference(resolution, [status(thm)], [c_32, c_247])).
% 10.78/3.37  tff(c_16, plain, (![A_5]: (v6_lattices(A_5) | ~v10_lattices(A_5) | v2_struct_0(A_5) | ~l3_lattices(A_5))), inference(cnfTransformation, [status(thm)], [f_56])).
% 10.78/3.37  tff(c_435, plain, (![A_191, C_192, B_193]: (k2_lattices(A_191, C_192, B_193)=k2_lattices(A_191, B_193, C_192) | ~m1_subset_1(C_192, u1_struct_0(A_191)) | ~m1_subset_1(B_193, u1_struct_0(A_191)) | ~v6_lattices(A_191) | ~l1_lattices(A_191) | v2_struct_0(A_191))), inference(cnfTransformation, [status(thm)], [f_205])).
% 10.78/3.37  tff(c_462, plain, (![A_16, B_193]: (k2_lattices(A_16, k5_lattices(A_16), B_193)=k2_lattices(A_16, B_193, k5_lattices(A_16)) | ~m1_subset_1(B_193, u1_struct_0(A_16)) | ~v6_lattices(A_16) | ~l1_lattices(A_16) | v2_struct_0(A_16))), inference(resolution, [status(thm)], [c_32, c_435])).
% 10.78/3.37  tff(c_2225, plain, (k2_lattices('#skF_11', k5_lattices('#skF_11'), '#skF_5'('#skF_11', k1_xboole_0))=k2_lattices('#skF_11', '#skF_5'('#skF_11', k1_xboole_0), k5_lattices('#skF_11')) | ~v6_lattices('#skF_11') | ~l1_lattices('#skF_11') | v2_struct_0('#skF_11')), inference(resolution, [status(thm)], [c_2170, c_462])).
% 10.78/3.37  tff(c_2277, plain, (k2_lattices('#skF_11', k5_lattices('#skF_11'), '#skF_5'('#skF_11', k1_xboole_0))=k2_lattices('#skF_11', '#skF_5'('#skF_11', k1_xboole_0), k5_lattices('#skF_11')) | ~v6_lattices('#skF_11') | v2_struct_0('#skF_11')), inference(demodulation, [status(thm), theory('equality')], [c_106, c_2225])).
% 10.78/3.37  tff(c_2278, plain, (k2_lattices('#skF_11', k5_lattices('#skF_11'), '#skF_5'('#skF_11', k1_xboole_0))=k2_lattices('#skF_11', '#skF_5'('#skF_11', k1_xboole_0), k5_lattices('#skF_11')) | ~v6_lattices('#skF_11')), inference(negUnitSimplification, [status(thm)], [c_98, c_2277])).
% 10.78/3.37  tff(c_2303, plain, (~v6_lattices('#skF_11')), inference(splitLeft, [status(thm)], [c_2278])).
% 10.78/3.37  tff(c_2307, plain, (~v10_lattices('#skF_11') | v2_struct_0('#skF_11') | ~l3_lattices('#skF_11')), inference(resolution, [status(thm)], [c_16, c_2303])).
% 10.78/3.37  tff(c_2310, plain, (v2_struct_0('#skF_11')), inference(demodulation, [status(thm), theory('equality')], [c_92, c_96, c_2307])).
% 10.78/3.37  tff(c_2312, plain, $false, inference(negUnitSimplification, [status(thm)], [c_98, c_2310])).
% 10.78/3.37  tff(c_2314, plain, (v6_lattices('#skF_11')), inference(splitRight, [status(thm)], [c_2278])).
% 10.78/3.37  tff(c_2313, plain, (k2_lattices('#skF_11', k5_lattices('#skF_11'), '#skF_5'('#skF_11', k1_xboole_0))=k2_lattices('#skF_11', '#skF_5'('#skF_11', k1_xboole_0), k5_lattices('#skF_11'))), inference(splitRight, [status(thm)], [c_2278])).
% 10.78/3.37  tff(c_763, plain, (![A_238, B_239, C_240]: (k2_lattices(A_238, B_239, C_240)=B_239 | ~r1_lattices(A_238, B_239, C_240) | ~m1_subset_1(C_240, u1_struct_0(A_238)) | ~m1_subset_1(B_239, u1_struct_0(A_238)) | ~l3_lattices(A_238) | ~v9_lattices(A_238) | ~v8_lattices(A_238) | v2_struct_0(A_238))), inference(cnfTransformation, [status(thm)], [f_107])).
% 10.78/3.37  tff(c_1278, plain, (![A_328, B_329, D_330]: (k2_lattices(A_328, '#skF_5'(A_328, B_329), D_330)='#skF_5'(A_328, B_329) | ~m1_subset_1('#skF_5'(A_328, B_329), u1_struct_0(A_328)) | ~v9_lattices(A_328) | ~v8_lattices(A_328) | ~r4_lattice3(A_328, D_330, B_329) | ~m1_subset_1(D_330, u1_struct_0(A_328)) | ~v4_lattice3(A_328) | ~l3_lattices(A_328) | v2_struct_0(A_328))), inference(resolution, [status(thm)], [c_66, c_763])).
% 10.78/3.37  tff(c_1282, plain, (![A_331, B_332, D_333]: (k2_lattices(A_331, '#skF_5'(A_331, B_332), D_333)='#skF_5'(A_331, B_332) | ~v9_lattices(A_331) | ~v8_lattices(A_331) | ~r4_lattice3(A_331, D_333, B_332) | ~m1_subset_1(D_333, u1_struct_0(A_331)) | ~v4_lattice3(A_331) | ~l3_lattices(A_331) | v2_struct_0(A_331))), inference(resolution, [status(thm)], [c_70, c_1278])).
% 10.78/3.37  tff(c_1334, plain, (![A_337, B_338]: (k2_lattices(A_337, '#skF_5'(A_337, B_338), k5_lattices(A_337))='#skF_5'(A_337, B_338) | ~v9_lattices(A_337) | ~v8_lattices(A_337) | ~r4_lattice3(A_337, k5_lattices(A_337), B_338) | ~v4_lattice3(A_337) | ~l3_lattices(A_337) | ~l1_lattices(A_337) | v2_struct_0(A_337))), inference(resolution, [status(thm)], [c_32, c_1282])).
% 10.78/3.37  tff(c_523, plain, (![A_200, B_201]: (k2_lattices(A_200, k5_lattices(A_200), B_201)=k2_lattices(A_200, B_201, k5_lattices(A_200)) | ~m1_subset_1(B_201, u1_struct_0(A_200)) | ~v6_lattices(A_200) | ~l1_lattices(A_200) | v2_struct_0(A_200))), inference(resolution, [status(thm)], [c_32, c_435])).
% 10.78/3.37  tff(c_546, plain, (![A_58, B_73]: (k2_lattices(A_58, k5_lattices(A_58), '#skF_5'(A_58, B_73))=k2_lattices(A_58, '#skF_5'(A_58, B_73), k5_lattices(A_58)) | ~v6_lattices(A_58) | ~l1_lattices(A_58) | ~v4_lattice3(A_58) | ~l3_lattices(A_58) | v2_struct_0(A_58))), inference(resolution, [status(thm)], [c_70, c_523])).
% 10.78/3.37  tff(c_1340, plain, (![A_337, B_338]: (k2_lattices(A_337, k5_lattices(A_337), '#skF_5'(A_337, B_338))='#skF_5'(A_337, B_338) | ~v6_lattices(A_337) | ~l1_lattices(A_337) | ~v4_lattice3(A_337) | ~l3_lattices(A_337) | v2_struct_0(A_337) | ~v9_lattices(A_337) | ~v8_lattices(A_337) | ~r4_lattice3(A_337, k5_lattices(A_337), B_338) | ~v4_lattice3(A_337) | ~l3_lattices(A_337) | ~l1_lattices(A_337) | v2_struct_0(A_337))), inference(superposition, [status(thm), theory('equality')], [c_1334, c_546])).
% 10.78/3.37  tff(c_2318, plain, (k2_lattices('#skF_11', '#skF_5'('#skF_11', k1_xboole_0), k5_lattices('#skF_11'))='#skF_5'('#skF_11', k1_xboole_0) | ~v6_lattices('#skF_11') | ~l1_lattices('#skF_11') | ~v4_lattice3('#skF_11') | ~l3_lattices('#skF_11') | v2_struct_0('#skF_11') | ~v9_lattices('#skF_11') | ~v8_lattices('#skF_11') | ~r4_lattice3('#skF_11', k5_lattices('#skF_11'), k1_xboole_0) | ~v4_lattice3('#skF_11') | ~l3_lattices('#skF_11') | ~l1_lattices('#skF_11') | v2_struct_0('#skF_11')), inference(superposition, [status(thm), theory('equality')], [c_2313, c_1340])).
% 10.78/3.37  tff(c_2337, plain, (k2_lattices('#skF_11', '#skF_5'('#skF_11', k1_xboole_0), k5_lattices('#skF_11'))='#skF_5'('#skF_11', k1_xboole_0) | ~v9_lattices('#skF_11') | ~v8_lattices('#skF_11') | ~r4_lattice3('#skF_11', k5_lattices('#skF_11'), k1_xboole_0) | v2_struct_0('#skF_11')), inference(demodulation, [status(thm), theory('equality')], [c_106, c_92, c_94, c_92, c_94, c_106, c_2314, c_2318])).
% 10.78/3.37  tff(c_2338, plain, (k2_lattices('#skF_11', '#skF_5'('#skF_11', k1_xboole_0), k5_lattices('#skF_11'))='#skF_5'('#skF_11', k1_xboole_0) | ~v9_lattices('#skF_11') | ~v8_lattices('#skF_11') | ~r4_lattice3('#skF_11', k5_lattices('#skF_11'), k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_98, c_2337])).
% 10.78/3.37  tff(c_2575, plain, (~r4_lattice3('#skF_11', k5_lattices('#skF_11'), k1_xboole_0)), inference(splitLeft, [status(thm)], [c_2338])).
% 10.78/3.37  tff(c_2578, plain, (~l3_lattices('#skF_11') | ~l1_lattices('#skF_11') | v2_struct_0('#skF_11')), inference(resolution, [status(thm)], [c_271, c_2575])).
% 10.78/3.37  tff(c_2581, plain, (v2_struct_0('#skF_11')), inference(demodulation, [status(thm), theory('equality')], [c_106, c_92, c_2578])).
% 10.78/3.37  tff(c_2583, plain, $false, inference(negUnitSimplification, [status(thm)], [c_98, c_2581])).
% 10.78/3.37  tff(c_2585, plain, (r4_lattice3('#skF_11', k5_lattices('#skF_11'), k1_xboole_0)), inference(splitRight, [status(thm)], [c_2338])).
% 10.78/3.37  tff(c_2328, plain, (k2_lattices('#skF_11', '#skF_5'('#skF_11', k1_xboole_0), k5_lattices('#skF_11'))='#skF_5'('#skF_11', k1_xboole_0) | ~v6_lattices('#skF_11') | ~l1_lattices('#skF_11') | ~v4_lattice3('#skF_11') | ~l3_lattices('#skF_11') | v2_struct_0('#skF_11') | ~v9_lattices('#skF_11') | ~v8_lattices('#skF_11') | ~r4_lattice3('#skF_11', k5_lattices('#skF_11'), k1_xboole_0) | ~v4_lattice3('#skF_11') | ~l3_lattices('#skF_11') | ~l1_lattices('#skF_11') | v2_struct_0('#skF_11')), inference(superposition, [status(thm), theory('equality')], [c_1340, c_2313])).
% 10.78/3.37  tff(c_2348, plain, (k2_lattices('#skF_11', '#skF_5'('#skF_11', k1_xboole_0), k5_lattices('#skF_11'))='#skF_5'('#skF_11', k1_xboole_0) | ~v9_lattices('#skF_11') | ~v8_lattices('#skF_11') | ~r4_lattice3('#skF_11', k5_lattices('#skF_11'), k1_xboole_0) | v2_struct_0('#skF_11')), inference(demodulation, [status(thm), theory('equality')], [c_106, c_92, c_94, c_92, c_94, c_106, c_2314, c_2328])).
% 10.78/3.37  tff(c_2349, plain, (k2_lattices('#skF_11', '#skF_5'('#skF_11', k1_xboole_0), k5_lattices('#skF_11'))='#skF_5'('#skF_11', k1_xboole_0) | ~v9_lattices('#skF_11') | ~v8_lattices('#skF_11') | ~r4_lattice3('#skF_11', k5_lattices('#skF_11'), k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_98, c_2348])).
% 10.78/3.37  tff(c_2600, plain, (k2_lattices('#skF_11', '#skF_5'('#skF_11', k1_xboole_0), k5_lattices('#skF_11'))='#skF_5'('#skF_11', k1_xboole_0) | ~v9_lattices('#skF_11') | ~v8_lattices('#skF_11')), inference(demodulation, [status(thm), theory('equality')], [c_2585, c_2349])).
% 10.78/3.37  tff(c_2601, plain, (~v8_lattices('#skF_11')), inference(splitLeft, [status(thm)], [c_2600])).
% 10.78/3.37  tff(c_2604, plain, (~v10_lattices('#skF_11') | v2_struct_0('#skF_11') | ~l3_lattices('#skF_11')), inference(resolution, [status(thm)], [c_12, c_2601])).
% 10.78/3.37  tff(c_2607, plain, (v2_struct_0('#skF_11')), inference(demodulation, [status(thm), theory('equality')], [c_92, c_96, c_2604])).
% 10.78/3.37  tff(c_2609, plain, $false, inference(negUnitSimplification, [status(thm)], [c_98, c_2607])).
% 10.78/3.37  tff(c_2611, plain, (v8_lattices('#skF_11')), inference(splitRight, [status(thm)], [c_2600])).
% 10.78/3.37  tff(c_10, plain, (![A_5]: (v9_lattices(A_5) | ~v10_lattices(A_5) | v2_struct_0(A_5) | ~l3_lattices(A_5))), inference(cnfTransformation, [status(thm)], [f_56])).
% 10.78/3.37  tff(c_2610, plain, (~v9_lattices('#skF_11') | k2_lattices('#skF_11', '#skF_5'('#skF_11', k1_xboole_0), k5_lattices('#skF_11'))='#skF_5'('#skF_11', k1_xboole_0)), inference(splitRight, [status(thm)], [c_2600])).
% 10.78/3.37  tff(c_2612, plain, (~v9_lattices('#skF_11')), inference(splitLeft, [status(thm)], [c_2610])).
% 10.78/3.37  tff(c_2615, plain, (~v10_lattices('#skF_11') | v2_struct_0('#skF_11') | ~l3_lattices('#skF_11')), inference(resolution, [status(thm)], [c_10, c_2612])).
% 10.78/3.37  tff(c_2618, plain, (v2_struct_0('#skF_11')), inference(demodulation, [status(thm), theory('equality')], [c_92, c_96, c_2615])).
% 10.78/3.37  tff(c_2620, plain, $false, inference(negUnitSimplification, [status(thm)], [c_98, c_2618])).
% 10.78/3.37  tff(c_2622, plain, (v9_lattices('#skF_11')), inference(splitRight, [status(thm)], [c_2610])).
% 10.78/3.37  tff(c_1307, plain, (![A_25, B_332, B_34]: (k2_lattices(A_25, '#skF_5'(A_25, B_332), '#skF_3'(A_25, B_34))='#skF_5'(A_25, B_332) | ~v9_lattices(A_25) | ~v8_lattices(A_25) | ~r4_lattice3(A_25, '#skF_3'(A_25, B_34), B_332) | ~v4_lattice3(A_25) | ~l3_lattices(A_25) | v13_lattices(A_25) | ~m1_subset_1(B_34, u1_struct_0(A_25)) | ~l1_lattices(A_25) | v2_struct_0(A_25))), inference(resolution, [status(thm)], [c_44, c_1282])).
% 10.78/3.37  tff(c_82, plain, (![A_96, C_105, B_103]: (k2_lattices(A_96, C_105, B_103)=k2_lattices(A_96, B_103, C_105) | ~m1_subset_1(C_105, u1_struct_0(A_96)) | ~m1_subset_1(B_103, u1_struct_0(A_96)) | ~v6_lattices(A_96) | ~l1_lattices(A_96) | v2_struct_0(A_96))), inference(cnfTransformation, [status(thm)], [f_205])).
% 10.78/3.37  tff(c_2229, plain, (![B_103]: (k2_lattices('#skF_11', B_103, '#skF_5'('#skF_11', k1_xboole_0))=k2_lattices('#skF_11', '#skF_5'('#skF_11', k1_xboole_0), B_103) | ~m1_subset_1(B_103, u1_struct_0('#skF_11')) | ~v6_lattices('#skF_11') | ~l1_lattices('#skF_11') | v2_struct_0('#skF_11'))), inference(resolution, [status(thm)], [c_2170, c_82])).
% 10.78/3.37  tff(c_2285, plain, (![B_103]: (k2_lattices('#skF_11', B_103, '#skF_5'('#skF_11', k1_xboole_0))=k2_lattices('#skF_11', '#skF_5'('#skF_11', k1_xboole_0), B_103) | ~m1_subset_1(B_103, u1_struct_0('#skF_11')) | ~v6_lattices('#skF_11') | v2_struct_0('#skF_11'))), inference(demodulation, [status(thm), theory('equality')], [c_106, c_2229])).
% 10.78/3.37  tff(c_2286, plain, (![B_103]: (k2_lattices('#skF_11', B_103, '#skF_5'('#skF_11', k1_xboole_0))=k2_lattices('#skF_11', '#skF_5'('#skF_11', k1_xboole_0), B_103) | ~m1_subset_1(B_103, u1_struct_0('#skF_11')) | ~v6_lattices('#skF_11'))), inference(negUnitSimplification, [status(thm)], [c_98, c_2285])).
% 10.78/3.37  tff(c_2490, plain, (![B_494]: (k2_lattices('#skF_11', B_494, '#skF_5'('#skF_11', k1_xboole_0))=k2_lattices('#skF_11', '#skF_5'('#skF_11', k1_xboole_0), B_494) | ~m1_subset_1(B_494, u1_struct_0('#skF_11')))), inference(demodulation, [status(thm), theory('equality')], [c_2314, c_2286])).
% 10.78/3.37  tff(c_2513, plain, (![B_34]: (k2_lattices('#skF_11', '#skF_3'('#skF_11', B_34), '#skF_5'('#skF_11', k1_xboole_0))=k2_lattices('#skF_11', '#skF_5'('#skF_11', k1_xboole_0), '#skF_3'('#skF_11', B_34)) | v13_lattices('#skF_11') | ~m1_subset_1(B_34, u1_struct_0('#skF_11')) | ~l1_lattices('#skF_11') | v2_struct_0('#skF_11'))), inference(resolution, [status(thm)], [c_44, c_2490])).
% 10.78/3.37  tff(c_2553, plain, (![B_34]: (k2_lattices('#skF_11', '#skF_3'('#skF_11', B_34), '#skF_5'('#skF_11', k1_xboole_0))=k2_lattices('#skF_11', '#skF_5'('#skF_11', k1_xboole_0), '#skF_3'('#skF_11', B_34)) | v13_lattices('#skF_11') | ~m1_subset_1(B_34, u1_struct_0('#skF_11')) | v2_struct_0('#skF_11'))), inference(demodulation, [status(thm), theory('equality')], [c_106, c_2513])).
% 10.78/3.37  tff(c_3204, plain, (![B_518]: (k2_lattices('#skF_11', '#skF_3'('#skF_11', B_518), '#skF_5'('#skF_11', k1_xboole_0))=k2_lattices('#skF_11', '#skF_5'('#skF_11', k1_xboole_0), '#skF_3'('#skF_11', B_518)) | ~m1_subset_1(B_518, u1_struct_0('#skF_11')))), inference(negUnitSimplification, [status(thm)], [c_98, c_119, c_2553])).
% 10.78/3.37  tff(c_42, plain, (![A_25, B_34]: (k2_lattices(A_25, '#skF_3'(A_25, B_34), B_34)!=B_34 | k2_lattices(A_25, B_34, '#skF_3'(A_25, B_34))!=B_34 | v13_lattices(A_25) | ~m1_subset_1(B_34, u1_struct_0(A_25)) | ~l1_lattices(A_25) | v2_struct_0(A_25))), inference(cnfTransformation, [status(thm)], [f_124])).
% 10.78/3.37  tff(c_3213, plain, (k2_lattices('#skF_11', '#skF_5'('#skF_11', k1_xboole_0), '#skF_3'('#skF_11', '#skF_5'('#skF_11', k1_xboole_0)))!='#skF_5'('#skF_11', k1_xboole_0) | k2_lattices('#skF_11', '#skF_5'('#skF_11', k1_xboole_0), '#skF_3'('#skF_11', '#skF_5'('#skF_11', k1_xboole_0)))!='#skF_5'('#skF_11', k1_xboole_0) | v13_lattices('#skF_11') | ~m1_subset_1('#skF_5'('#skF_11', k1_xboole_0), u1_struct_0('#skF_11')) | ~l1_lattices('#skF_11') | v2_struct_0('#skF_11') | ~m1_subset_1('#skF_5'('#skF_11', k1_xboole_0), u1_struct_0('#skF_11'))), inference(superposition, [status(thm), theory('equality')], [c_3204, c_42])).
% 10.78/3.37  tff(c_3227, plain, (k2_lattices('#skF_11', '#skF_5'('#skF_11', k1_xboole_0), '#skF_3'('#skF_11', '#skF_5'('#skF_11', k1_xboole_0)))!='#skF_5'('#skF_11', k1_xboole_0) | v13_lattices('#skF_11') | v2_struct_0('#skF_11')), inference(demodulation, [status(thm), theory('equality')], [c_2170, c_106, c_2170, c_3213])).
% 10.78/3.37  tff(c_3228, plain, (k2_lattices('#skF_11', '#skF_5'('#skF_11', k1_xboole_0), '#skF_3'('#skF_11', '#skF_5'('#skF_11', k1_xboole_0)))!='#skF_5'('#skF_11', k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_98, c_119, c_3227])).
% 10.78/3.37  tff(c_3236, plain, (~v9_lattices('#skF_11') | ~v8_lattices('#skF_11') | ~r4_lattice3('#skF_11', '#skF_3'('#skF_11', '#skF_5'('#skF_11', k1_xboole_0)), k1_xboole_0) | ~v4_lattice3('#skF_11') | ~l3_lattices('#skF_11') | v13_lattices('#skF_11') | ~m1_subset_1('#skF_5'('#skF_11', k1_xboole_0), u1_struct_0('#skF_11')) | ~l1_lattices('#skF_11') | v2_struct_0('#skF_11')), inference(superposition, [status(thm), theory('equality')], [c_1307, c_3228])).
% 10.78/3.37  tff(c_3239, plain, (~r4_lattice3('#skF_11', '#skF_3'('#skF_11', '#skF_5'('#skF_11', k1_xboole_0)), k1_xboole_0) | v13_lattices('#skF_11') | v2_struct_0('#skF_11')), inference(demodulation, [status(thm), theory('equality')], [c_106, c_2170, c_92, c_94, c_2611, c_2622, c_3236])).
% 10.78/3.37  tff(c_3240, plain, (~r4_lattice3('#skF_11', '#skF_3'('#skF_11', '#skF_5'('#skF_11', k1_xboole_0)), k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_98, c_119, c_3239])).
% 10.78/3.37  tff(c_3243, plain, (~l3_lattices('#skF_11') | v13_lattices('#skF_11') | ~m1_subset_1('#skF_5'('#skF_11', k1_xboole_0), u1_struct_0('#skF_11')) | ~l1_lattices('#skF_11') | v2_struct_0('#skF_11')), inference(resolution, [status(thm)], [c_266, c_3240])).
% 10.78/3.37  tff(c_3246, plain, (v13_lattices('#skF_11') | v2_struct_0('#skF_11')), inference(demodulation, [status(thm), theory('equality')], [c_106, c_2170, c_92, c_3243])).
% 10.78/3.37  tff(c_3248, plain, $false, inference(negUnitSimplification, [status(thm)], [c_98, c_119, c_3246])).
% 10.78/3.37  tff(c_3250, plain, (v13_lattices('#skF_11')), inference(splitRight, [status(thm)], [c_101])).
% 10.78/3.37  tff(c_46, plain, (![A_25]: (m1_subset_1('#skF_2'(A_25), u1_struct_0(A_25)) | ~v13_lattices(A_25) | ~l1_lattices(A_25) | v2_struct_0(A_25))), inference(cnfTransformation, [status(thm)], [f_124])).
% 10.78/3.37  tff(c_3497, plain, (![A_590, C_591]: (k2_lattices(A_590, k5_lattices(A_590), C_591)=k5_lattices(A_590) | ~m1_subset_1(C_591, u1_struct_0(A_590)) | ~m1_subset_1(k5_lattices(A_590), u1_struct_0(A_590)) | ~v13_lattices(A_590) | ~l1_lattices(A_590) | v2_struct_0(A_590))), inference(cnfTransformation, [status(thm)], [f_75])).
% 10.78/3.37  tff(c_3525, plain, (![A_592]: (k2_lattices(A_592, k5_lattices(A_592), '#skF_2'(A_592))=k5_lattices(A_592) | ~m1_subset_1(k5_lattices(A_592), u1_struct_0(A_592)) | ~v13_lattices(A_592) | ~l1_lattices(A_592) | v2_struct_0(A_592))), inference(resolution, [status(thm)], [c_46, c_3497])).
% 10.78/3.37  tff(c_3529, plain, (![A_593]: (k2_lattices(A_593, k5_lattices(A_593), '#skF_2'(A_593))=k5_lattices(A_593) | ~v13_lattices(A_593) | ~l1_lattices(A_593) | v2_struct_0(A_593))), inference(resolution, [status(thm)], [c_32, c_3525])).
% 10.78/3.37  tff(c_3298, plain, (![A_541, C_542]: (k2_lattices(A_541, C_542, '#skF_2'(A_541))='#skF_2'(A_541) | ~m1_subset_1(C_542, u1_struct_0(A_541)) | ~v13_lattices(A_541) | ~l1_lattices(A_541) | v2_struct_0(A_541))), inference(cnfTransformation, [status(thm)], [f_124])).
% 10.78/3.37  tff(c_3316, plain, (![A_16]: (k2_lattices(A_16, k5_lattices(A_16), '#skF_2'(A_16))='#skF_2'(A_16) | ~v13_lattices(A_16) | ~l1_lattices(A_16) | v2_struct_0(A_16))), inference(resolution, [status(thm)], [c_32, c_3298])).
% 10.78/3.37  tff(c_3535, plain, (![A_593]: (k5_lattices(A_593)='#skF_2'(A_593) | ~v13_lattices(A_593) | ~l1_lattices(A_593) | v2_struct_0(A_593) | ~v13_lattices(A_593) | ~l1_lattices(A_593) | v2_struct_0(A_593))), inference(superposition, [status(thm), theory('equality')], [c_3529, c_3316])).
% 10.78/3.37  tff(c_3558, plain, (![A_597]: (k5_lattices(A_597)='#skF_2'(A_597) | ~v13_lattices(A_597) | ~l1_lattices(A_597) | v2_struct_0(A_597))), inference(factorization, [status(thm), theory('equality')], [c_3535])).
% 10.78/3.37  tff(c_3561, plain, (k5_lattices('#skF_11')='#skF_2'('#skF_11') | ~v13_lattices('#skF_11') | ~l1_lattices('#skF_11')), inference(resolution, [status(thm)], [c_3558, c_98])).
% 10.78/3.37  tff(c_3564, plain, (k5_lattices('#skF_11')='#skF_2'('#skF_11')), inference(demodulation, [status(thm), theory('equality')], [c_106, c_3250, c_3561])).
% 10.78/3.37  tff(c_3400, plain, (![A_553, B_554, C_555]: (r2_hidden('#skF_4'(A_553, B_554, C_555), C_555) | r4_lattice3(A_553, B_554, C_555) | ~m1_subset_1(B_554, u1_struct_0(A_553)) | ~l3_lattices(A_553) | v2_struct_0(A_553))), inference(cnfTransformation, [status(thm)], [f_142])).
% 10.78/3.37  tff(c_3266, plain, (![A_520, B_521]: (~r2_hidden(A_520, k2_zfmisc_1(A_520, B_521)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 10.78/3.37  tff(c_3272, plain, (![A_1]: (~r2_hidden(A_1, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_4, c_3266])).
% 10.78/3.37  tff(c_3406, plain, (![A_556, B_557]: (r4_lattice3(A_556, B_557, k1_xboole_0) | ~m1_subset_1(B_557, u1_struct_0(A_556)) | ~l3_lattices(A_556) | v2_struct_0(A_556))), inference(resolution, [status(thm)], [c_3400, c_3272])).
% 10.78/3.37  tff(c_3430, plain, (![A_16]: (r4_lattice3(A_16, k5_lattices(A_16), k1_xboole_0) | ~l3_lattices(A_16) | ~l1_lattices(A_16) | v2_struct_0(A_16))), inference(resolution, [status(thm)], [c_32, c_3406])).
% 10.78/3.37  tff(c_3572, plain, (r4_lattice3('#skF_11', '#skF_2'('#skF_11'), k1_xboole_0) | ~l3_lattices('#skF_11') | ~l1_lattices('#skF_11') | v2_struct_0('#skF_11')), inference(superposition, [status(thm), theory('equality')], [c_3564, c_3430])).
% 10.78/3.37  tff(c_3588, plain, (r4_lattice3('#skF_11', '#skF_2'('#skF_11'), k1_xboole_0) | v2_struct_0('#skF_11')), inference(demodulation, [status(thm), theory('equality')], [c_106, c_92, c_3572])).
% 10.78/3.37  tff(c_3589, plain, (r4_lattice3('#skF_11', '#skF_2'('#skF_11'), k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_98, c_3588])).
% 10.78/3.37  tff(c_3581, plain, (m1_subset_1('#skF_2'('#skF_11'), u1_struct_0('#skF_11')) | ~l1_lattices('#skF_11') | v2_struct_0('#skF_11')), inference(superposition, [status(thm), theory('equality')], [c_3564, c_32])).
% 10.78/3.37  tff(c_3597, plain, (m1_subset_1('#skF_2'('#skF_11'), u1_struct_0('#skF_11')) | v2_struct_0('#skF_11')), inference(demodulation, [status(thm), theory('equality')], [c_106, c_3581])).
% 10.78/3.37  tff(c_3598, plain, (m1_subset_1('#skF_2'('#skF_11'), u1_struct_0('#skF_11'))), inference(negUnitSimplification, [status(thm)], [c_98, c_3597])).
% 10.78/3.37  tff(c_4154, plain, (![A_631, B_632, C_633]: (r1_lattices(A_631, B_632, C_633) | k2_lattices(A_631, B_632, C_633)!=B_632 | ~m1_subset_1(C_633, u1_struct_0(A_631)) | ~m1_subset_1(B_632, u1_struct_0(A_631)) | ~l3_lattices(A_631) | ~v9_lattices(A_631) | ~v8_lattices(A_631) | v2_struct_0(A_631))), inference(cnfTransformation, [status(thm)], [f_107])).
% 10.78/3.37  tff(c_4156, plain, (![B_632]: (r1_lattices('#skF_11', B_632, '#skF_2'('#skF_11')) | k2_lattices('#skF_11', B_632, '#skF_2'('#skF_11'))!=B_632 | ~m1_subset_1(B_632, u1_struct_0('#skF_11')) | ~l3_lattices('#skF_11') | ~v9_lattices('#skF_11') | ~v8_lattices('#skF_11') | v2_struct_0('#skF_11'))), inference(resolution, [status(thm)], [c_3598, c_4154])).
% 10.78/3.37  tff(c_4177, plain, (![B_632]: (r1_lattices('#skF_11', B_632, '#skF_2'('#skF_11')) | k2_lattices('#skF_11', B_632, '#skF_2'('#skF_11'))!=B_632 | ~m1_subset_1(B_632, u1_struct_0('#skF_11')) | ~v9_lattices('#skF_11') | ~v8_lattices('#skF_11') | v2_struct_0('#skF_11'))), inference(demodulation, [status(thm), theory('equality')], [c_92, c_4156])).
% 10.78/3.37  tff(c_4178, plain, (![B_632]: (r1_lattices('#skF_11', B_632, '#skF_2'('#skF_11')) | k2_lattices('#skF_11', B_632, '#skF_2'('#skF_11'))!=B_632 | ~m1_subset_1(B_632, u1_struct_0('#skF_11')) | ~v9_lattices('#skF_11') | ~v8_lattices('#skF_11'))), inference(negUnitSimplification, [status(thm)], [c_98, c_4177])).
% 10.78/3.37  tff(c_4188, plain, (~v8_lattices('#skF_11')), inference(splitLeft, [status(thm)], [c_4178])).
% 10.78/3.37  tff(c_4191, plain, (~v10_lattices('#skF_11') | v2_struct_0('#skF_11') | ~l3_lattices('#skF_11')), inference(resolution, [status(thm)], [c_12, c_4188])).
% 10.78/3.37  tff(c_4194, plain, (v2_struct_0('#skF_11')), inference(demodulation, [status(thm), theory('equality')], [c_92, c_96, c_4191])).
% 10.78/3.37  tff(c_4196, plain, $false, inference(negUnitSimplification, [status(thm)], [c_98, c_4194])).
% 10.78/3.37  tff(c_4198, plain, (v8_lattices('#skF_11')), inference(splitRight, [status(thm)], [c_4178])).
% 10.78/3.37  tff(c_4197, plain, (![B_632]: (~v9_lattices('#skF_11') | r1_lattices('#skF_11', B_632, '#skF_2'('#skF_11')) | k2_lattices('#skF_11', B_632, '#skF_2'('#skF_11'))!=B_632 | ~m1_subset_1(B_632, u1_struct_0('#skF_11')))), inference(splitRight, [status(thm)], [c_4178])).
% 10.78/3.37  tff(c_4199, plain, (~v9_lattices('#skF_11')), inference(splitLeft, [status(thm)], [c_4197])).
% 10.78/3.37  tff(c_4202, plain, (~v10_lattices('#skF_11') | v2_struct_0('#skF_11') | ~l3_lattices('#skF_11')), inference(resolution, [status(thm)], [c_10, c_4199])).
% 10.78/3.37  tff(c_4205, plain, (v2_struct_0('#skF_11')), inference(demodulation, [status(thm), theory('equality')], [c_92, c_96, c_4202])).
% 10.78/3.37  tff(c_4207, plain, $false, inference(negUnitSimplification, [status(thm)], [c_98, c_4205])).
% 10.78/3.37  tff(c_4209, plain, (v9_lattices('#skF_11')), inference(splitRight, [status(thm)], [c_4197])).
% 10.78/3.37  tff(c_3625, plain, (![A_598, C_599, B_600]: (k2_lattices(A_598, C_599, B_600)=k2_lattices(A_598, B_600, C_599) | ~m1_subset_1(C_599, u1_struct_0(A_598)) | ~m1_subset_1(B_600, u1_struct_0(A_598)) | ~v6_lattices(A_598) | ~l1_lattices(A_598) | v2_struct_0(A_598))), inference(cnfTransformation, [status(thm)], [f_205])).
% 10.78/3.37  tff(c_3627, plain, (![B_600]: (k2_lattices('#skF_11', B_600, '#skF_2'('#skF_11'))=k2_lattices('#skF_11', '#skF_2'('#skF_11'), B_600) | ~m1_subset_1(B_600, u1_struct_0('#skF_11')) | ~v6_lattices('#skF_11') | ~l1_lattices('#skF_11') | v2_struct_0('#skF_11'))), inference(resolution, [status(thm)], [c_3598, c_3625])).
% 10.78/3.37  tff(c_3648, plain, (![B_600]: (k2_lattices('#skF_11', B_600, '#skF_2'('#skF_11'))=k2_lattices('#skF_11', '#skF_2'('#skF_11'), B_600) | ~m1_subset_1(B_600, u1_struct_0('#skF_11')) | ~v6_lattices('#skF_11') | v2_struct_0('#skF_11'))), inference(demodulation, [status(thm), theory('equality')], [c_106, c_3627])).
% 10.78/3.37  tff(c_3649, plain, (![B_600]: (k2_lattices('#skF_11', B_600, '#skF_2'('#skF_11'))=k2_lattices('#skF_11', '#skF_2'('#skF_11'), B_600) | ~m1_subset_1(B_600, u1_struct_0('#skF_11')) | ~v6_lattices('#skF_11'))), inference(negUnitSimplification, [status(thm)], [c_98, c_3648])).
% 10.78/3.37  tff(c_3717, plain, (~v6_lattices('#skF_11')), inference(splitLeft, [status(thm)], [c_3649])).
% 10.78/3.37  tff(c_3720, plain, (~v10_lattices('#skF_11') | v2_struct_0('#skF_11') | ~l3_lattices('#skF_11')), inference(resolution, [status(thm)], [c_16, c_3717])).
% 10.78/3.37  tff(c_3723, plain, (v2_struct_0('#skF_11')), inference(demodulation, [status(thm), theory('equality')], [c_92, c_96, c_3720])).
% 10.78/3.37  tff(c_3725, plain, $false, inference(negUnitSimplification, [status(thm)], [c_98, c_3723])).
% 10.78/3.37  tff(c_3728, plain, (![B_603]: (k2_lattices('#skF_11', B_603, '#skF_2'('#skF_11'))=k2_lattices('#skF_11', '#skF_2'('#skF_11'), B_603) | ~m1_subset_1(B_603, u1_struct_0('#skF_11')))), inference(splitRight, [status(thm)], [c_3649])).
% 10.78/3.37  tff(c_3751, plain, (![B_73]: (k2_lattices('#skF_11', '#skF_5'('#skF_11', B_73), '#skF_2'('#skF_11'))=k2_lattices('#skF_11', '#skF_2'('#skF_11'), '#skF_5'('#skF_11', B_73)) | ~v4_lattice3('#skF_11') | ~l3_lattices('#skF_11') | v2_struct_0('#skF_11'))), inference(resolution, [status(thm)], [c_70, c_3728])).
% 10.78/3.37  tff(c_3788, plain, (![B_73]: (k2_lattices('#skF_11', '#skF_5'('#skF_11', B_73), '#skF_2'('#skF_11'))=k2_lattices('#skF_11', '#skF_2'('#skF_11'), '#skF_5'('#skF_11', B_73)) | v2_struct_0('#skF_11'))), inference(demodulation, [status(thm), theory('equality')], [c_92, c_94, c_3751])).
% 10.78/3.37  tff(c_3806, plain, (![B_604]: (k2_lattices('#skF_11', '#skF_5'('#skF_11', B_604), '#skF_2'('#skF_11'))=k2_lattices('#skF_11', '#skF_2'('#skF_11'), '#skF_5'('#skF_11', B_604)))), inference(negUnitSimplification, [status(thm)], [c_98, c_3788])).
% 10.78/3.37  tff(c_3326, plain, (![A_544, C_545]: (k2_lattices(A_544, '#skF_2'(A_544), C_545)='#skF_2'(A_544) | ~m1_subset_1(C_545, u1_struct_0(A_544)) | ~v13_lattices(A_544) | ~l1_lattices(A_544) | v2_struct_0(A_544))), inference(cnfTransformation, [status(thm)], [f_124])).
% 10.78/3.37  tff(c_3340, plain, (![A_58, B_73]: (k2_lattices(A_58, '#skF_2'(A_58), '#skF_5'(A_58, B_73))='#skF_2'(A_58) | ~v13_lattices(A_58) | ~l1_lattices(A_58) | ~v4_lattice3(A_58) | ~l3_lattices(A_58) | v2_struct_0(A_58))), inference(resolution, [status(thm)], [c_70, c_3326])).
% 10.78/3.37  tff(c_3818, plain, (![B_604]: (k2_lattices('#skF_11', '#skF_5'('#skF_11', B_604), '#skF_2'('#skF_11'))='#skF_2'('#skF_11') | ~v13_lattices('#skF_11') | ~l1_lattices('#skF_11') | ~v4_lattice3('#skF_11') | ~l3_lattices('#skF_11') | v2_struct_0('#skF_11'))), inference(superposition, [status(thm), theory('equality')], [c_3806, c_3340])).
% 10.78/3.37  tff(c_3839, plain, (![B_604]: (k2_lattices('#skF_11', '#skF_5'('#skF_11', B_604), '#skF_2'('#skF_11'))='#skF_2'('#skF_11') | v2_struct_0('#skF_11'))), inference(demodulation, [status(thm), theory('equality')], [c_92, c_94, c_106, c_3250, c_3818])).
% 10.78/3.37  tff(c_3840, plain, (![B_604]: (k2_lattices('#skF_11', '#skF_5'('#skF_11', B_604), '#skF_2'('#skF_11'))='#skF_2'('#skF_11'))), inference(negUnitSimplification, [status(thm)], [c_98, c_3839])).
% 10.78/3.37  tff(c_4221, plain, (![A_639, B_640, C_641]: (k2_lattices(A_639, B_640, C_641)=B_640 | ~r1_lattices(A_639, B_640, C_641) | ~m1_subset_1(C_641, u1_struct_0(A_639)) | ~m1_subset_1(B_640, u1_struct_0(A_639)) | ~l3_lattices(A_639) | ~v9_lattices(A_639) | ~v8_lattices(A_639) | v2_struct_0(A_639))), inference(cnfTransformation, [status(thm)], [f_107])).
% 10.78/3.37  tff(c_5291, plain, (![A_754, B_755, D_756]: (k2_lattices(A_754, '#skF_5'(A_754, B_755), D_756)='#skF_5'(A_754, B_755) | ~m1_subset_1('#skF_5'(A_754, B_755), u1_struct_0(A_754)) | ~v9_lattices(A_754) | ~v8_lattices(A_754) | ~r4_lattice3(A_754, D_756, B_755) | ~m1_subset_1(D_756, u1_struct_0(A_754)) | ~v4_lattice3(A_754) | ~l3_lattices(A_754) | v2_struct_0(A_754))), inference(resolution, [status(thm)], [c_66, c_4221])).
% 10.78/3.37  tff(c_5295, plain, (![A_757, B_758, D_759]: (k2_lattices(A_757, '#skF_5'(A_757, B_758), D_759)='#skF_5'(A_757, B_758) | ~v9_lattices(A_757) | ~v8_lattices(A_757) | ~r4_lattice3(A_757, D_759, B_758) | ~m1_subset_1(D_759, u1_struct_0(A_757)) | ~v4_lattice3(A_757) | ~l3_lattices(A_757) | v2_struct_0(A_757))), inference(resolution, [status(thm)], [c_70, c_5291])).
% 10.78/3.37  tff(c_5299, plain, (![B_758]: (k2_lattices('#skF_11', '#skF_5'('#skF_11', B_758), '#skF_2'('#skF_11'))='#skF_5'('#skF_11', B_758) | ~v9_lattices('#skF_11') | ~v8_lattices('#skF_11') | ~r4_lattice3('#skF_11', '#skF_2'('#skF_11'), B_758) | ~v4_lattice3('#skF_11') | ~l3_lattices('#skF_11') | v2_struct_0('#skF_11'))), inference(resolution, [status(thm)], [c_3598, c_5295])).
% 10.78/3.37  tff(c_5321, plain, (![B_758]: ('#skF_5'('#skF_11', B_758)='#skF_2'('#skF_11') | ~r4_lattice3('#skF_11', '#skF_2'('#skF_11'), B_758) | v2_struct_0('#skF_11'))), inference(demodulation, [status(thm), theory('equality')], [c_92, c_94, c_4198, c_4209, c_3840, c_5299])).
% 10.78/3.37  tff(c_5332, plain, (![B_760]: ('#skF_5'('#skF_11', B_760)='#skF_2'('#skF_11') | ~r4_lattice3('#skF_11', '#skF_2'('#skF_11'), B_760))), inference(negUnitSimplification, [status(thm)], [c_98, c_5321])).
% 10.78/3.37  tff(c_5344, plain, ('#skF_2'('#skF_11')='#skF_5'('#skF_11', k1_xboole_0)), inference(resolution, [status(thm)], [c_3589, c_5332])).
% 10.78/3.37  tff(c_3249, plain, (k15_lattice3('#skF_11', k1_xboole_0)!=k5_lattices('#skF_11')), inference(splitRight, [status(thm)], [c_101])).
% 10.78/3.37  tff(c_3565, plain, (k15_lattice3('#skF_11', k1_xboole_0)!='#skF_2'('#skF_11')), inference(demodulation, [status(thm), theory('equality')], [c_3564, c_3249])).
% 10.78/3.37  tff(c_5367, plain, (k15_lattice3('#skF_11', k1_xboole_0)!='#skF_5'('#skF_11', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_5344, c_3565])).
% 10.78/3.37  tff(c_5365, plain, (r4_lattice3('#skF_11', '#skF_5'('#skF_11', k1_xboole_0), k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_5344, c_3589])).
% 10.78/3.37  tff(c_5366, plain, (m1_subset_1('#skF_5'('#skF_11', k1_xboole_0), u1_struct_0('#skF_11'))), inference(demodulation, [status(thm), theory('equality')], [c_5344, c_3598])).
% 10.78/3.37  tff(c_4687, plain, (![A_687, B_688, C_689]: (m1_subset_1('#skF_8'(A_687, B_688, C_689), u1_struct_0(A_687)) | k15_lattice3(A_687, B_688)=C_689 | ~r4_lattice3(A_687, C_689, B_688) | ~m1_subset_1(C_689, u1_struct_0(A_687)) | ~v4_lattice3(A_687) | ~v10_lattices(A_687) | ~l3_lattices(A_687) | v2_struct_0(A_687))), inference(cnfTransformation, [status(thm)], [f_190])).
% 10.78/3.37  tff(c_50, plain, (![A_25, C_33]: (k2_lattices(A_25, '#skF_2'(A_25), C_33)='#skF_2'(A_25) | ~m1_subset_1(C_33, u1_struct_0(A_25)) | ~v13_lattices(A_25) | ~l1_lattices(A_25) | v2_struct_0(A_25))), inference(cnfTransformation, [status(thm)], [f_124])).
% 10.78/3.37  tff(c_5914, plain, (![A_770, B_771, C_772]: (k2_lattices(A_770, '#skF_2'(A_770), '#skF_8'(A_770, B_771, C_772))='#skF_2'(A_770) | ~v13_lattices(A_770) | ~l1_lattices(A_770) | k15_lattice3(A_770, B_771)=C_772 | ~r4_lattice3(A_770, C_772, B_771) | ~m1_subset_1(C_772, u1_struct_0(A_770)) | ~v4_lattice3(A_770) | ~v10_lattices(A_770) | ~l3_lattices(A_770) | v2_struct_0(A_770))), inference(resolution, [status(thm)], [c_4687, c_50])).
% 10.78/3.37  tff(c_5923, plain, (![B_771, C_772]: (k2_lattices('#skF_11', '#skF_5'('#skF_11', k1_xboole_0), '#skF_8'('#skF_11', B_771, C_772))='#skF_2'('#skF_11') | ~v13_lattices('#skF_11') | ~l1_lattices('#skF_11') | k15_lattice3('#skF_11', B_771)=C_772 | ~r4_lattice3('#skF_11', C_772, B_771) | ~m1_subset_1(C_772, u1_struct_0('#skF_11')) | ~v4_lattice3('#skF_11') | ~v10_lattices('#skF_11') | ~l3_lattices('#skF_11') | v2_struct_0('#skF_11'))), inference(superposition, [status(thm), theory('equality')], [c_5344, c_5914])).
% 10.78/3.37  tff(c_5927, plain, (![B_771, C_772]: (k2_lattices('#skF_11', '#skF_5'('#skF_11', k1_xboole_0), '#skF_8'('#skF_11', B_771, C_772))='#skF_5'('#skF_11', k1_xboole_0) | k15_lattice3('#skF_11', B_771)=C_772 | ~r4_lattice3('#skF_11', C_772, B_771) | ~m1_subset_1(C_772, u1_struct_0('#skF_11')) | v2_struct_0('#skF_11'))), inference(demodulation, [status(thm), theory('equality')], [c_92, c_96, c_94, c_106, c_3250, c_5344, c_5923])).
% 10.78/3.37  tff(c_5928, plain, (![B_771, C_772]: (k2_lattices('#skF_11', '#skF_5'('#skF_11', k1_xboole_0), '#skF_8'('#skF_11', B_771, C_772))='#skF_5'('#skF_11', k1_xboole_0) | k15_lattice3('#skF_11', B_771)=C_772 | ~r4_lattice3('#skF_11', C_772, B_771) | ~m1_subset_1(C_772, u1_struct_0('#skF_11')))), inference(negUnitSimplification, [status(thm)], [c_98, c_5927])).
% 10.78/3.37  tff(c_38, plain, (![A_18, B_22, C_24]: (r1_lattices(A_18, B_22, C_24) | k2_lattices(A_18, B_22, C_24)!=B_22 | ~m1_subset_1(C_24, u1_struct_0(A_18)) | ~m1_subset_1(B_22, u1_struct_0(A_18)) | ~l3_lattices(A_18) | ~v9_lattices(A_18) | ~v8_lattices(A_18) | v2_struct_0(A_18))), inference(cnfTransformation, [status(thm)], [f_107])).
% 10.78/3.37  tff(c_7234, plain, (![A_910, B_911, B_912, C_913]: (r1_lattices(A_910, B_911, '#skF_8'(A_910, B_912, C_913)) | k2_lattices(A_910, B_911, '#skF_8'(A_910, B_912, C_913))!=B_911 | ~m1_subset_1(B_911, u1_struct_0(A_910)) | ~v9_lattices(A_910) | ~v8_lattices(A_910) | k15_lattice3(A_910, B_912)=C_913 | ~r4_lattice3(A_910, C_913, B_912) | ~m1_subset_1(C_913, u1_struct_0(A_910)) | ~v4_lattice3(A_910) | ~v10_lattices(A_910) | ~l3_lattices(A_910) | v2_struct_0(A_910))), inference(resolution, [status(thm)], [c_4687, c_38])).
% 10.78/3.37  tff(c_72, plain, (![A_84, C_92, B_91]: (~r1_lattices(A_84, C_92, '#skF_8'(A_84, B_91, C_92)) | k15_lattice3(A_84, B_91)=C_92 | ~r4_lattice3(A_84, C_92, B_91) | ~m1_subset_1(C_92, u1_struct_0(A_84)) | ~v4_lattice3(A_84) | ~v10_lattices(A_84) | ~l3_lattices(A_84) | v2_struct_0(A_84))), inference(cnfTransformation, [status(thm)], [f_190])).
% 10.78/3.37  tff(c_7248, plain, (![A_914, C_915, B_916]: (k2_lattices(A_914, C_915, '#skF_8'(A_914, B_916, C_915))!=C_915 | ~v9_lattices(A_914) | ~v8_lattices(A_914) | k15_lattice3(A_914, B_916)=C_915 | ~r4_lattice3(A_914, C_915, B_916) | ~m1_subset_1(C_915, u1_struct_0(A_914)) | ~v4_lattice3(A_914) | ~v10_lattices(A_914) | ~l3_lattices(A_914) | v2_struct_0(A_914))), inference(resolution, [status(thm)], [c_7234, c_72])).
% 10.78/3.37  tff(c_7254, plain, (![B_771]: (~v9_lattices('#skF_11') | ~v8_lattices('#skF_11') | ~v4_lattice3('#skF_11') | ~v10_lattices('#skF_11') | ~l3_lattices('#skF_11') | v2_struct_0('#skF_11') | k15_lattice3('#skF_11', B_771)='#skF_5'('#skF_11', k1_xboole_0) | ~r4_lattice3('#skF_11', '#skF_5'('#skF_11', k1_xboole_0), B_771) | ~m1_subset_1('#skF_5'('#skF_11', k1_xboole_0), u1_struct_0('#skF_11')))), inference(superposition, [status(thm), theory('equality')], [c_5928, c_7248])).
% 10.78/3.37  tff(c_7261, plain, (![B_771]: (v2_struct_0('#skF_11') | k15_lattice3('#skF_11', B_771)='#skF_5'('#skF_11', k1_xboole_0) | ~r4_lattice3('#skF_11', '#skF_5'('#skF_11', k1_xboole_0), B_771))), inference(demodulation, [status(thm), theory('equality')], [c_5366, c_92, c_96, c_94, c_4198, c_4209, c_7254])).
% 10.78/3.37  tff(c_7264, plain, (![B_917]: (k15_lattice3('#skF_11', B_917)='#skF_5'('#skF_11', k1_xboole_0) | ~r4_lattice3('#skF_11', '#skF_5'('#skF_11', k1_xboole_0), B_917))), inference(negUnitSimplification, [status(thm)], [c_98, c_7261])).
% 10.78/3.37  tff(c_7270, plain, (k15_lattice3('#skF_11', k1_xboole_0)='#skF_5'('#skF_11', k1_xboole_0)), inference(resolution, [status(thm)], [c_5365, c_7264])).
% 10.78/3.37  tff(c_7283, plain, $false, inference(negUnitSimplification, [status(thm)], [c_5367, c_7270])).
% 10.78/3.37  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.78/3.37  
% 10.78/3.37  Inference rules
% 10.78/3.37  ----------------------
% 10.78/3.37  #Ref     : 0
% 10.78/3.37  #Sup     : 1533
% 10.78/3.37  #Fact    : 4
% 10.78/3.37  #Define  : 0
% 10.78/3.37  #Split   : 10
% 10.78/3.37  #Chain   : 0
% 10.78/3.37  #Close   : 0
% 10.78/3.37  
% 10.78/3.37  Ordering : KBO
% 10.78/3.37  
% 10.78/3.37  Simplification rules
% 10.78/3.37  ----------------------
% 10.78/3.37  #Subsume      : 365
% 10.78/3.37  #Demod        : 1715
% 10.78/3.37  #Tautology    : 778
% 10.78/3.37  #SimpNegUnit  : 388
% 10.78/3.37  #BackRed      : 23
% 10.78/3.37  
% 10.78/3.37  #Partial instantiations: 0
% 10.78/3.37  #Strategies tried      : 1
% 10.78/3.37  
% 10.78/3.37  Timing (in seconds)
% 10.78/3.37  ----------------------
% 10.78/3.38  Preprocessing        : 0.42
% 10.78/3.38  Parsing              : 0.22
% 10.78/3.38  CNF conversion       : 0.04
% 10.78/3.38  Main loop            : 2.14
% 10.78/3.38  Inferencing          : 0.99
% 10.78/3.38  Reduction            : 0.54
% 10.78/3.38  Demodulation         : 0.36
% 10.78/3.38  BG Simplification    : 0.09
% 10.78/3.38  Subsumption          : 0.39
% 10.78/3.38  Abstraction          : 0.11
% 10.78/3.38  MUC search           : 0.00
% 10.78/3.38  Cooper               : 0.00
% 10.78/3.38  Total                : 2.63
% 10.78/3.38  Index Insertion      : 0.00
% 10.78/3.38  Index Deletion       : 0.00
% 10.78/3.38  Index Matching       : 0.00
% 10.78/3.38  BG Taut test         : 0.00
%------------------------------------------------------------------------------
