%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:23:15 EST 2020

% Result     : Theorem 4.80s
% Output     : CNFRefutation 4.80s
% Verified   : 
% Statistics : Number of formulae       :  195 (5057 expanded)
%              Number of leaves         :   47 (1782 expanded)
%              Depth                    :   20
%              Number of atoms          :  323 (15433 expanded)
%              Number of equality atoms :   90 (5043 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > l1_struct_0 > k2_tops_2 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k3_tarski > k2_struct_0 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff(k2_funct_1,type,(
    k2_funct_1: $i > $i )).

tff(v2_funct_1,type,(
    v2_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tops_2,type,(
    k2_tops_2: ( $i * $i * $i ) > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(v1_partfun1,type,(
    v1_partfun1: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_203,negated_conjecture,(
    ~ ! [A] :
        ( l1_struct_0(A)
       => ! [B] :
            ( ( ~ v2_struct_0(B)
              & l1_struct_0(B) )
           => ! [C] :
                ( ( v1_funct_1(C)
                  & v1_funct_2(C,u1_struct_0(A),u1_struct_0(B))
                  & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(B)))) )
               => ( ( k2_relset_1(u1_struct_0(A),u1_struct_0(B),C) = k2_struct_0(B)
                    & v2_funct_1(C) )
                 => ( k1_relset_1(u1_struct_0(B),u1_struct_0(A),k2_tops_2(u1_struct_0(A),u1_struct_0(B),C)) = k2_struct_0(B)
                    & k2_relset_1(u1_struct_0(B),u1_struct_0(A),k2_tops_2(u1_struct_0(A),u1_struct_0(B),C)) = k2_struct_0(A) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_tops_2)).

tff(f_127,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_73,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_83,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_135,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

tff(f_79,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_123,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => ( v1_partfun1(B,A)
      <=> k1_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_partfun1)).

tff(f_97,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => ( ( v1_funct_1(C)
              & v1_funct_2(C,A,B) )
           => ( v1_funct_1(C)
              & v1_partfun1(C,A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc5_funct_2)).

tff(f_69,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k2_relat_1(A) = k1_relat_1(k2_funct_1(A))
          & k1_relat_1(A) = k2_relat_1(k2_funct_1(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).

tff(f_167,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( ( k2_relset_1(A,B,C) = B
          & v2_funct_1(C) )
       => k2_tops_2(A,B,C) = k2_funct_1(C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tops_2)).

tff(f_179,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( v1_funct_1(k2_tops_2(A,B,C))
        & v1_funct_2(k2_tops_2(A,B,C),B,A)
        & m1_subset_1(k2_tops_2(A,B,C),k1_zfmisc_1(k2_zfmisc_1(B,A))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_tops_2)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_115,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( ( ( B = k1_xboole_0
           => A = k1_xboole_0 )
         => ( v1_funct_2(C,A,B)
          <=> A = k1_relset_1(A,B,C) ) )
        & ( B = k1_xboole_0
         => ( A = k1_xboole_0
            | ( v1_funct_2(C,A,B)
            <=> C = k1_xboole_0 ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).

tff(f_59,axiom,(
    ! [A] :
      ( ( ~ v1_xboole_0(A)
        & v1_relat_1(A) )
     => ~ v1_xboole_0(k1_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc8_relat_1)).

tff(f_51,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_xboole_0(k2_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc11_relat_1)).

tff(c_84,plain,(
    l1_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_203])).

tff(c_100,plain,(
    ! [A_49] :
      ( u1_struct_0(A_49) = k2_struct_0(A_49)
      | ~ l1_struct_0(A_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_107,plain,(
    u1_struct_0('#skF_3') = k2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_84,c_100])).

tff(c_88,plain,(
    l1_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_203])).

tff(c_108,plain,(
    u1_struct_0('#skF_2') = k2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_88,c_100])).

tff(c_78,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3')))) ),
    inference(cnfTransformation,[status(thm)],[f_203])).

tff(c_2369,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_107,c_108,c_78])).

tff(c_2386,plain,(
    ! [C_364,A_365,B_366] :
      ( v1_relat_1(C_364)
      | ~ m1_subset_1(C_364,k1_zfmisc_1(k2_zfmisc_1(A_365,B_366))) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_2395,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_2369,c_2386])).

tff(c_2550,plain,(
    ! [A_411,B_412,C_413] :
      ( k2_relset_1(A_411,B_412,C_413) = k2_relat_1(C_413)
      | ~ m1_subset_1(C_413,k1_zfmisc_1(k2_zfmisc_1(A_411,B_412))) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_2559,plain,(
    k2_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_3'),'#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_2369,c_2550])).

tff(c_76,plain,(
    k2_relset_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),'#skF_4') = k2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_203])).

tff(c_2381,plain,(
    k2_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_3'),'#skF_4') = k2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_107,c_108,c_76])).

tff(c_2560,plain,(
    k2_struct_0('#skF_3') = k2_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2559,c_2381])).

tff(c_86,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_203])).

tff(c_134,plain,(
    ! [A_51] :
      ( ~ v1_xboole_0(u1_struct_0(A_51))
      | ~ l1_struct_0(A_51)
      | v2_struct_0(A_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_140,plain,
    ( ~ v1_xboole_0(k2_struct_0('#skF_3'))
    | ~ l1_struct_0('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_107,c_134])).

tff(c_144,plain,
    ( ~ v1_xboole_0(k2_struct_0('#skF_3'))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_140])).

tff(c_145,plain,(
    ~ v1_xboole_0(k2_struct_0('#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_144])).

tff(c_2571,plain,(
    ~ v1_xboole_0(k2_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2560,c_145])).

tff(c_2420,plain,(
    ! [C_376,A_377,B_378] :
      ( v4_relat_1(C_376,A_377)
      | ~ m1_subset_1(C_376,k1_zfmisc_1(k2_zfmisc_1(A_377,B_378))) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_2429,plain,(
    v4_relat_1('#skF_4',k2_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_2369,c_2420])).

tff(c_2514,plain,(
    ! [B_399,A_400] :
      ( k1_relat_1(B_399) = A_400
      | ~ v1_partfun1(B_399,A_400)
      | ~ v4_relat_1(B_399,A_400)
      | ~ v1_relat_1(B_399) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_2517,plain,
    ( k2_struct_0('#skF_2') = k1_relat_1('#skF_4')
    | ~ v1_partfun1('#skF_4',k2_struct_0('#skF_2'))
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_2429,c_2514])).

tff(c_2520,plain,
    ( k2_struct_0('#skF_2') = k1_relat_1('#skF_4')
    | ~ v1_partfun1('#skF_4',k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2395,c_2517])).

tff(c_2521,plain,(
    ~ v1_partfun1('#skF_4',k2_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_2520])).

tff(c_82,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_203])).

tff(c_80,plain,(
    v1_funct_2('#skF_4',u1_struct_0('#skF_2'),u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_203])).

tff(c_109,plain,(
    v1_funct_2('#skF_4',u1_struct_0('#skF_2'),k2_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_107,c_80])).

tff(c_133,plain,(
    v1_funct_2('#skF_4',k2_struct_0('#skF_2'),k2_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_108,c_109])).

tff(c_2572,plain,(
    v1_funct_2('#skF_4',k2_struct_0('#skF_2'),k2_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2560,c_133])).

tff(c_2570,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_2'),k2_relat_1('#skF_4')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2560,c_2369])).

tff(c_2782,plain,(
    ! [C_452,A_453,B_454] :
      ( v1_partfun1(C_452,A_453)
      | ~ v1_funct_2(C_452,A_453,B_454)
      | ~ v1_funct_1(C_452)
      | ~ m1_subset_1(C_452,k1_zfmisc_1(k2_zfmisc_1(A_453,B_454)))
      | v1_xboole_0(B_454) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_2785,plain,
    ( v1_partfun1('#skF_4',k2_struct_0('#skF_2'))
    | ~ v1_funct_2('#skF_4',k2_struct_0('#skF_2'),k2_relat_1('#skF_4'))
    | ~ v1_funct_1('#skF_4')
    | v1_xboole_0(k2_relat_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_2570,c_2782])).

tff(c_2792,plain,
    ( v1_partfun1('#skF_4',k2_struct_0('#skF_2'))
    | v1_xboole_0(k2_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_2572,c_2785])).

tff(c_2794,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2571,c_2521,c_2792])).

tff(c_2795,plain,(
    k2_struct_0('#skF_2') = k1_relat_1('#skF_4') ),
    inference(splitRight,[status(thm)],[c_2520])).

tff(c_169,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_108,c_107,c_78])).

tff(c_26,plain,(
    ! [C_14,A_12,B_13] :
      ( v1_relat_1(C_14)
      | ~ m1_subset_1(C_14,k1_zfmisc_1(k2_zfmisc_1(A_12,B_13))) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_176,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_169,c_26])).

tff(c_74,plain,(
    v2_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_203])).

tff(c_22,plain,(
    ! [A_11] :
      ( k2_relat_1(k2_funct_1(A_11)) = k1_relat_1(A_11)
      | ~ v2_funct_1(A_11)
      | ~ v1_funct_1(A_11)
      | ~ v1_relat_1(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_1281,plain,(
    ! [A_242,B_243,C_244] :
      ( k2_relset_1(A_242,B_243,C_244) = k2_relat_1(C_244)
      | ~ m1_subset_1(C_244,k1_zfmisc_1(k2_zfmisc_1(A_242,B_243))) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_1289,plain,(
    k2_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_3'),'#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_169,c_1281])).

tff(c_147,plain,(
    k2_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_3'),'#skF_4') = k2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_108,c_107,c_76])).

tff(c_1291,plain,(
    k2_struct_0('#skF_3') = k2_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1289,c_147])).

tff(c_1303,plain,(
    ~ v1_xboole_0(k2_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1291,c_145])).

tff(c_192,plain,(
    ! [C_69,A_70,B_71] :
      ( v4_relat_1(C_69,A_70)
      | ~ m1_subset_1(C_69,k1_zfmisc_1(k2_zfmisc_1(A_70,B_71))) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_200,plain,(
    v4_relat_1('#skF_4',k2_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_169,c_192])).

tff(c_1229,plain,(
    ! [B_231,A_232] :
      ( k1_relat_1(B_231) = A_232
      | ~ v1_partfun1(B_231,A_232)
      | ~ v4_relat_1(B_231,A_232)
      | ~ v1_relat_1(B_231) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_1232,plain,
    ( k2_struct_0('#skF_2') = k1_relat_1('#skF_4')
    | ~ v1_partfun1('#skF_4',k2_struct_0('#skF_2'))
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_200,c_1229])).

tff(c_1235,plain,
    ( k2_struct_0('#skF_2') = k1_relat_1('#skF_4')
    | ~ v1_partfun1('#skF_4',k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_176,c_1232])).

tff(c_1236,plain,(
    ~ v1_partfun1('#skF_4',k2_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_1235])).

tff(c_1304,plain,(
    v1_funct_2('#skF_4',k2_struct_0('#skF_2'),k2_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1291,c_133])).

tff(c_1302,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_2'),k2_relat_1('#skF_4')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1291,c_169])).

tff(c_1431,plain,(
    ! [C_262,A_263,B_264] :
      ( v1_partfun1(C_262,A_263)
      | ~ v1_funct_2(C_262,A_263,B_264)
      | ~ v1_funct_1(C_262)
      | ~ m1_subset_1(C_262,k1_zfmisc_1(k2_zfmisc_1(A_263,B_264)))
      | v1_xboole_0(B_264) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_1434,plain,
    ( v1_partfun1('#skF_4',k2_struct_0('#skF_2'))
    | ~ v1_funct_2('#skF_4',k2_struct_0('#skF_2'),k2_relat_1('#skF_4'))
    | ~ v1_funct_1('#skF_4')
    | v1_xboole_0(k2_relat_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_1302,c_1431])).

tff(c_1441,plain,
    ( v1_partfun1('#skF_4',k2_struct_0('#skF_2'))
    | v1_xboole_0(k2_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_1304,c_1434])).

tff(c_1443,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1303,c_1236,c_1441])).

tff(c_1444,plain,(
    k2_struct_0('#skF_2') = k1_relat_1('#skF_4') ),
    inference(splitRight,[status(thm)],[c_1235])).

tff(c_1451,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'),k2_struct_0('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1444,c_169])).

tff(c_1574,plain,(
    ! [A_273,B_274,C_275] :
      ( k2_relset_1(A_273,B_274,C_275) = k2_relat_1(C_275)
      | ~ m1_subset_1(C_275,k1_zfmisc_1(k2_zfmisc_1(A_273,B_274))) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_1582,plain,(
    k2_relset_1(k1_relat_1('#skF_4'),k2_struct_0('#skF_3'),'#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_1451,c_1574])).

tff(c_1452,plain,(
    k2_relset_1(k1_relat_1('#skF_4'),k2_struct_0('#skF_3'),'#skF_4') = k2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1444,c_147])).

tff(c_1584,plain,(
    k2_struct_0('#skF_3') = k2_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1582,c_1452])).

tff(c_1454,plain,(
    v1_funct_2('#skF_4',k1_relat_1('#skF_4'),k2_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1444,c_133])).

tff(c_1593,plain,(
    v1_funct_2('#skF_4',k1_relat_1('#skF_4'),k2_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1584,c_1454])).

tff(c_1590,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'),k2_relat_1('#skF_4')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1584,c_1451])).

tff(c_1589,plain,(
    k2_relset_1(k1_relat_1('#skF_4'),k2_relat_1('#skF_4'),'#skF_4') = k2_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1584,c_1582])).

tff(c_1999,plain,(
    ! [A_345,B_346,C_347] :
      ( k2_tops_2(A_345,B_346,C_347) = k2_funct_1(C_347)
      | ~ v2_funct_1(C_347)
      | k2_relset_1(A_345,B_346,C_347) != B_346
      | ~ m1_subset_1(C_347,k1_zfmisc_1(k2_zfmisc_1(A_345,B_346)))
      | ~ v1_funct_2(C_347,A_345,B_346)
      | ~ v1_funct_1(C_347) ) ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_2005,plain,
    ( k2_tops_2(k1_relat_1('#skF_4'),k2_relat_1('#skF_4'),'#skF_4') = k2_funct_1('#skF_4')
    | ~ v2_funct_1('#skF_4')
    | k2_relset_1(k1_relat_1('#skF_4'),k2_relat_1('#skF_4'),'#skF_4') != k2_relat_1('#skF_4')
    | ~ v1_funct_2('#skF_4',k1_relat_1('#skF_4'),k2_relat_1('#skF_4'))
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_1590,c_1999])).

tff(c_2013,plain,(
    k2_tops_2(k1_relat_1('#skF_4'),k2_relat_1('#skF_4'),'#skF_4') = k2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_1593,c_1589,c_74,c_2005])).

tff(c_66,plain,(
    ! [A_39,B_40,C_41] :
      ( m1_subset_1(k2_tops_2(A_39,B_40,C_41),k1_zfmisc_1(k2_zfmisc_1(B_40,A_39)))
      | ~ m1_subset_1(C_41,k1_zfmisc_1(k2_zfmisc_1(A_39,B_40)))
      | ~ v1_funct_2(C_41,A_39,B_40)
      | ~ v1_funct_1(C_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_2026,plain,
    ( m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_4'),k1_relat_1('#skF_4'))))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'),k2_relat_1('#skF_4'))))
    | ~ v1_funct_2('#skF_4',k1_relat_1('#skF_4'),k2_relat_1('#skF_4'))
    | ~ v1_funct_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_2013,c_66])).

tff(c_2032,plain,(
    m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_4'),k1_relat_1('#skF_4')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_1593,c_1590,c_2026])).

tff(c_32,plain,(
    ! [A_18,B_19,C_20] :
      ( k2_relset_1(A_18,B_19,C_20) = k2_relat_1(C_20)
      | ~ m1_subset_1(C_20,k1_zfmisc_1(k2_zfmisc_1(A_18,B_19))) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_2101,plain,(
    k2_relset_1(k2_relat_1('#skF_4'),k1_relat_1('#skF_4'),k2_funct_1('#skF_4')) = k2_relat_1(k2_funct_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_2032,c_32])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_324,plain,(
    ! [A_102,B_103,C_104] :
      ( k2_relset_1(A_102,B_103,C_104) = k2_relat_1(C_104)
      | ~ m1_subset_1(C_104,k1_zfmisc_1(k2_zfmisc_1(A_102,B_103))) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_332,plain,(
    k2_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_3'),'#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_169,c_324])).

tff(c_334,plain,(
    k2_struct_0('#skF_3') = k2_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_332,c_147])).

tff(c_345,plain,(
    ~ v1_xboole_0(k2_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_334,c_145])).

tff(c_271,plain,(
    ! [B_90,A_91] :
      ( k1_relat_1(B_90) = A_91
      | ~ v1_partfun1(B_90,A_91)
      | ~ v4_relat_1(B_90,A_91)
      | ~ v1_relat_1(B_90) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_274,plain,
    ( k2_struct_0('#skF_2') = k1_relat_1('#skF_4')
    | ~ v1_partfun1('#skF_4',k2_struct_0('#skF_2'))
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_200,c_271])).

tff(c_277,plain,
    ( k2_struct_0('#skF_2') = k1_relat_1('#skF_4')
    | ~ v1_partfun1('#skF_4',k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_176,c_274])).

tff(c_279,plain,(
    ~ v1_partfun1('#skF_4',k2_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_277])).

tff(c_346,plain,(
    v1_funct_2('#skF_4',k2_struct_0('#skF_2'),k2_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_334,c_133])).

tff(c_344,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_2'),k2_relat_1('#skF_4')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_334,c_169])).

tff(c_500,plain,(
    ! [C_130,A_131,B_132] :
      ( v1_partfun1(C_130,A_131)
      | ~ v1_funct_2(C_130,A_131,B_132)
      | ~ v1_funct_1(C_130)
      | ~ m1_subset_1(C_130,k1_zfmisc_1(k2_zfmisc_1(A_131,B_132)))
      | v1_xboole_0(B_132) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_503,plain,
    ( v1_partfun1('#skF_4',k2_struct_0('#skF_2'))
    | ~ v1_funct_2('#skF_4',k2_struct_0('#skF_2'),k2_relat_1('#skF_4'))
    | ~ v1_funct_1('#skF_4')
    | v1_xboole_0(k2_relat_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_344,c_500])).

tff(c_510,plain,
    ( v1_partfun1('#skF_4',k2_struct_0('#skF_2'))
    | v1_xboole_0(k2_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_346,c_503])).

tff(c_512,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_345,c_279,c_510])).

tff(c_513,plain,(
    k2_struct_0('#skF_2') = k1_relat_1('#skF_4') ),
    inference(splitRight,[status(thm)],[c_277])).

tff(c_519,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'),k2_struct_0('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_513,c_169])).

tff(c_642,plain,(
    ! [A_140,B_141,C_142] :
      ( k2_relset_1(A_140,B_141,C_142) = k2_relat_1(C_142)
      | ~ m1_subset_1(C_142,k1_zfmisc_1(k2_zfmisc_1(A_140,B_141))) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_650,plain,(
    k2_relset_1(k1_relat_1('#skF_4'),k2_struct_0('#skF_3'),'#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_519,c_642])).

tff(c_520,plain,(
    k2_relset_1(k1_relat_1('#skF_4'),k2_struct_0('#skF_3'),'#skF_4') = k2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_513,c_147])).

tff(c_652,plain,(
    k2_struct_0('#skF_3') = k2_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_650,c_520])).

tff(c_522,plain,(
    v1_funct_2('#skF_4',k1_relat_1('#skF_4'),k2_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_513,c_133])).

tff(c_661,plain,(
    v1_funct_2('#skF_4',k1_relat_1('#skF_4'),k2_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_652,c_522])).

tff(c_657,plain,(
    k2_relset_1(k1_relat_1('#skF_4'),k2_relat_1('#skF_4'),'#skF_4') = k2_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_652,c_650])).

tff(c_658,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'),k2_relat_1('#skF_4')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_652,c_519])).

tff(c_1065,plain,(
    ! [A_215,B_216,C_217] :
      ( k2_tops_2(A_215,B_216,C_217) = k2_funct_1(C_217)
      | ~ v2_funct_1(C_217)
      | k2_relset_1(A_215,B_216,C_217) != B_216
      | ~ m1_subset_1(C_217,k1_zfmisc_1(k2_zfmisc_1(A_215,B_216)))
      | ~ v1_funct_2(C_217,A_215,B_216)
      | ~ v1_funct_1(C_217) ) ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_1071,plain,
    ( k2_tops_2(k1_relat_1('#skF_4'),k2_relat_1('#skF_4'),'#skF_4') = k2_funct_1('#skF_4')
    | ~ v2_funct_1('#skF_4')
    | k2_relset_1(k1_relat_1('#skF_4'),k2_relat_1('#skF_4'),'#skF_4') != k2_relat_1('#skF_4')
    | ~ v1_funct_2('#skF_4',k1_relat_1('#skF_4'),k2_relat_1('#skF_4'))
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_658,c_1065])).

tff(c_1079,plain,(
    k2_tops_2(k1_relat_1('#skF_4'),k2_relat_1('#skF_4'),'#skF_4') = k2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_661,c_657,c_74,c_1071])).

tff(c_72,plain,
    ( k2_relset_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),k2_tops_2(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),'#skF_4')) != k2_struct_0('#skF_2')
    | k1_relset_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),k2_tops_2(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),'#skF_4')) != k2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_203])).

tff(c_234,plain,
    ( k2_relset_1(k2_struct_0('#skF_3'),k2_struct_0('#skF_2'),k2_tops_2(k2_struct_0('#skF_2'),k2_struct_0('#skF_3'),'#skF_4')) != k2_struct_0('#skF_2')
    | k1_relset_1(k2_struct_0('#skF_3'),k2_struct_0('#skF_2'),k2_tops_2(k2_struct_0('#skF_2'),k2_struct_0('#skF_3'),'#skF_4')) != k2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_108,c_108,c_107,c_107,c_108,c_108,c_107,c_107,c_72])).

tff(c_235,plain,(
    k1_relset_1(k2_struct_0('#skF_3'),k2_struct_0('#skF_2'),k2_tops_2(k2_struct_0('#skF_2'),k2_struct_0('#skF_3'),'#skF_4')) != k2_struct_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_234])).

tff(c_515,plain,(
    k1_relset_1(k2_struct_0('#skF_3'),k1_relat_1('#skF_4'),k2_tops_2(k1_relat_1('#skF_4'),k2_struct_0('#skF_3'),'#skF_4')) != k2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_513,c_513,c_235])).

tff(c_742,plain,(
    k1_relset_1(k2_relat_1('#skF_4'),k1_relat_1('#skF_4'),k2_tops_2(k1_relat_1('#skF_4'),k2_relat_1('#skF_4'),'#skF_4')) != k2_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_652,c_652,c_652,c_515])).

tff(c_1084,plain,(
    k1_relset_1(k2_relat_1('#skF_4'),k1_relat_1('#skF_4'),k2_funct_1('#skF_4')) != k2_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1079,c_742])).

tff(c_912,plain,(
    ! [A_194,B_195,C_196] :
      ( v1_funct_2(k2_tops_2(A_194,B_195,C_196),B_195,A_194)
      | ~ m1_subset_1(C_196,k1_zfmisc_1(k2_zfmisc_1(A_194,B_195)))
      | ~ v1_funct_2(C_196,A_194,B_195)
      | ~ v1_funct_1(C_196) ) ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_914,plain,
    ( v1_funct_2(k2_tops_2(k1_relat_1('#skF_4'),k2_relat_1('#skF_4'),'#skF_4'),k2_relat_1('#skF_4'),k1_relat_1('#skF_4'))
    | ~ v1_funct_2('#skF_4',k1_relat_1('#skF_4'),k2_relat_1('#skF_4'))
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_658,c_912])).

tff(c_920,plain,(
    v1_funct_2(k2_tops_2(k1_relat_1('#skF_4'),k2_relat_1('#skF_4'),'#skF_4'),k2_relat_1('#skF_4'),k1_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_661,c_914])).

tff(c_1082,plain,(
    v1_funct_2(k2_funct_1('#skF_4'),k2_relat_1('#skF_4'),k1_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1079,c_920])).

tff(c_1088,plain,
    ( m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_4'),k1_relat_1('#skF_4'))))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'),k2_relat_1('#skF_4'))))
    | ~ v1_funct_2('#skF_4',k1_relat_1('#skF_4'),k2_relat_1('#skF_4'))
    | ~ v1_funct_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1079,c_66])).

tff(c_1092,plain,(
    m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_4'),k1_relat_1('#skF_4')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_661,c_658,c_1088])).

tff(c_48,plain,(
    ! [B_26,A_25,C_27] :
      ( k1_xboole_0 = B_26
      | k1_relset_1(A_25,B_26,C_27) = A_25
      | ~ v1_funct_2(C_27,A_25,B_26)
      | ~ m1_subset_1(C_27,k1_zfmisc_1(k2_zfmisc_1(A_25,B_26))) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_1113,plain,
    ( k1_relat_1('#skF_4') = k1_xboole_0
    | k1_relset_1(k2_relat_1('#skF_4'),k1_relat_1('#skF_4'),k2_funct_1('#skF_4')) = k2_relat_1('#skF_4')
    | ~ v1_funct_2(k2_funct_1('#skF_4'),k2_relat_1('#skF_4'),k1_relat_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_1092,c_48])).

tff(c_1152,plain,
    ( k1_relat_1('#skF_4') = k1_xboole_0
    | k1_relset_1(k2_relat_1('#skF_4'),k1_relat_1('#skF_4'),k2_funct_1('#skF_4')) = k2_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1082,c_1113])).

tff(c_1153,plain,(
    k1_relat_1('#skF_4') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_1084,c_1152])).

tff(c_137,plain,
    ( ~ v1_xboole_0(k2_struct_0('#skF_2'))
    | ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_108,c_134])).

tff(c_142,plain,
    ( ~ v1_xboole_0(k2_struct_0('#skF_2'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_137])).

tff(c_146,plain,(
    ~ v1_xboole_0(k2_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_142])).

tff(c_521,plain,(
    ~ v1_xboole_0(k1_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_513,c_146])).

tff(c_1176,plain,(
    ~ v1_xboole_0(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1153,c_521])).

tff(c_1180,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_1176])).

tff(c_1181,plain,(
    k2_relset_1(k2_struct_0('#skF_3'),k2_struct_0('#skF_2'),k2_tops_2(k2_struct_0('#skF_2'),k2_struct_0('#skF_3'),'#skF_4')) != k2_struct_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_234])).

tff(c_1448,plain,(
    k2_relset_1(k2_struct_0('#skF_3'),k1_relat_1('#skF_4'),k2_tops_2(k1_relat_1('#skF_4'),k2_struct_0('#skF_3'),'#skF_4')) != k1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1444,c_1444,c_1444,c_1181])).

tff(c_1692,plain,(
    k2_relset_1(k2_relat_1('#skF_4'),k1_relat_1('#skF_4'),k2_tops_2(k1_relat_1('#skF_4'),k2_relat_1('#skF_4'),'#skF_4')) != k1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1584,c_1584,c_1448])).

tff(c_2018,plain,(
    k2_relset_1(k2_relat_1('#skF_4'),k1_relat_1('#skF_4'),k2_funct_1('#skF_4')) != k1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2013,c_1692])).

tff(c_2353,plain,(
    k2_relat_1(k2_funct_1('#skF_4')) != k1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2101,c_2018])).

tff(c_2360,plain,
    ( ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_2353])).

tff(c_2364,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_176,c_82,c_74,c_2360])).

tff(c_2366,plain,(
    v1_xboole_0(k2_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_142])).

tff(c_2803,plain,(
    v1_xboole_0(k1_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2795,c_2366])).

tff(c_20,plain,(
    ! [A_10] :
      ( ~ v1_xboole_0(k1_relat_1(A_10))
      | ~ v1_relat_1(A_10)
      | v1_xboole_0(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_2812,plain,
    ( ~ v1_relat_1('#skF_4')
    | v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_2803,c_20])).

tff(c_2815,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2395,c_2812])).

tff(c_18,plain,(
    ! [A_9] :
      ( v1_xboole_0(k2_relat_1(A_9))
      | ~ v1_xboole_0(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_2802,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'),k2_struct_0('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2795,c_2369])).

tff(c_2910,plain,(
    ! [A_464,B_465,C_466] :
      ( k2_relset_1(A_464,B_465,C_466) = k2_relat_1(C_466)
      | ~ m1_subset_1(C_466,k1_zfmisc_1(k2_zfmisc_1(A_464,B_465))) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_2918,plain,(
    k2_relset_1(k1_relat_1('#skF_4'),k2_struct_0('#skF_3'),'#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_2802,c_2910])).

tff(c_2800,plain,(
    k2_relset_1(k1_relat_1('#skF_4'),k2_struct_0('#skF_3'),'#skF_4') = k2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2795,c_2381])).

tff(c_2920,plain,(
    k2_struct_0('#skF_3') = k2_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2918,c_2800])).

tff(c_2937,plain,(
    ~ v1_xboole_0(k2_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2920,c_145])).

tff(c_2945,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_18,c_2937])).

tff(c_2949,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2815,c_2945])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:50:50 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.80/1.84  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.80/1.86  
% 4.80/1.86  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.80/1.86  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > l1_struct_0 > k2_tops_2 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k3_tarski > k2_struct_0 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4
% 4.80/1.86  
% 4.80/1.86  %Foreground sorts:
% 4.80/1.86  
% 4.80/1.86  
% 4.80/1.86  %Background operators:
% 4.80/1.86  
% 4.80/1.86  
% 4.80/1.86  %Foreground operators:
% 4.80/1.86  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 4.80/1.86  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 4.80/1.86  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.80/1.86  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 4.80/1.86  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 4.80/1.86  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.80/1.86  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.80/1.86  tff('#skF_1', type, '#skF_1': $i > $i).
% 4.80/1.86  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.80/1.86  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.80/1.86  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 4.80/1.86  tff(k2_tops_2, type, k2_tops_2: ($i * $i * $i) > $i).
% 4.80/1.86  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.80/1.86  tff('#skF_2', type, '#skF_2': $i).
% 4.80/1.86  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 4.80/1.86  tff('#skF_3', type, '#skF_3': $i).
% 4.80/1.86  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 4.80/1.86  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 4.80/1.86  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.80/1.86  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 4.80/1.86  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.80/1.86  tff(k3_tarski, type, k3_tarski: $i > $i).
% 4.80/1.86  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.80/1.86  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.80/1.86  tff('#skF_4', type, '#skF_4': $i).
% 4.80/1.86  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.80/1.86  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 4.80/1.86  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 4.80/1.86  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 4.80/1.86  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.80/1.86  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.80/1.86  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.80/1.86  
% 4.80/1.89  tff(f_203, negated_conjecture, ~(![A]: (l1_struct_0(A) => (![B]: ((~v2_struct_0(B) & l1_struct_0(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (((k2_relset_1(u1_struct_0(A), u1_struct_0(B), C) = k2_struct_0(B)) & v2_funct_1(C)) => ((k1_relset_1(u1_struct_0(B), u1_struct_0(A), k2_tops_2(u1_struct_0(A), u1_struct_0(B), C)) = k2_struct_0(B)) & (k2_relset_1(u1_struct_0(B), u1_struct_0(A), k2_tops_2(u1_struct_0(A), u1_struct_0(B), C)) = k2_struct_0(A)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t62_tops_2)).
% 4.80/1.89  tff(f_127, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_struct_0)).
% 4.80/1.89  tff(f_73, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 4.80/1.89  tff(f_83, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 4.80/1.89  tff(f_135, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_struct_0)).
% 4.80/1.89  tff(f_79, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 4.80/1.89  tff(f_123, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (v1_partfun1(B, A) <=> (k1_relat_1(B) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_partfun1)).
% 4.80/1.89  tff(f_97, axiom, (![A, B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) => (v1_funct_1(C) & v1_partfun1(C, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc5_funct_2)).
% 4.80/1.89  tff(f_69, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k2_relat_1(A) = k1_relat_1(k2_funct_1(A))) & (k1_relat_1(A) = k2_relat_1(k2_funct_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_funct_1)).
% 4.80/1.89  tff(f_167, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((k2_relset_1(A, B, C) = B) & v2_funct_1(C)) => (k2_tops_2(A, B, C) = k2_funct_1(C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_tops_2)).
% 4.80/1.89  tff(f_179, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((v1_funct_1(k2_tops_2(A, B, C)) & v1_funct_2(k2_tops_2(A, B, C), B, A)) & m1_subset_1(k2_tops_2(A, B, C), k1_zfmisc_1(k2_zfmisc_1(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_tops_2)).
% 4.80/1.89  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 4.80/1.89  tff(f_115, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 4.80/1.89  tff(f_59, axiom, (![A]: ((~v1_xboole_0(A) & v1_relat_1(A)) => ~v1_xboole_0(k1_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc8_relat_1)).
% 4.80/1.89  tff(f_51, axiom, (![A]: (v1_xboole_0(A) => v1_xboole_0(k2_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc11_relat_1)).
% 4.80/1.89  tff(c_84, plain, (l1_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_203])).
% 4.80/1.89  tff(c_100, plain, (![A_49]: (u1_struct_0(A_49)=k2_struct_0(A_49) | ~l1_struct_0(A_49))), inference(cnfTransformation, [status(thm)], [f_127])).
% 4.80/1.89  tff(c_107, plain, (u1_struct_0('#skF_3')=k2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_84, c_100])).
% 4.80/1.89  tff(c_88, plain, (l1_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_203])).
% 4.80/1.89  tff(c_108, plain, (u1_struct_0('#skF_2')=k2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_88, c_100])).
% 4.80/1.89  tff(c_78, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'))))), inference(cnfTransformation, [status(thm)], [f_203])).
% 4.80/1.89  tff(c_2369, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_107, c_108, c_78])).
% 4.80/1.89  tff(c_2386, plain, (![C_364, A_365, B_366]: (v1_relat_1(C_364) | ~m1_subset_1(C_364, k1_zfmisc_1(k2_zfmisc_1(A_365, B_366))))), inference(cnfTransformation, [status(thm)], [f_73])).
% 4.80/1.89  tff(c_2395, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_2369, c_2386])).
% 4.80/1.89  tff(c_2550, plain, (![A_411, B_412, C_413]: (k2_relset_1(A_411, B_412, C_413)=k2_relat_1(C_413) | ~m1_subset_1(C_413, k1_zfmisc_1(k2_zfmisc_1(A_411, B_412))))), inference(cnfTransformation, [status(thm)], [f_83])).
% 4.80/1.89  tff(c_2559, plain, (k2_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_3'), '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_2369, c_2550])).
% 4.80/1.89  tff(c_76, plain, (k2_relset_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), '#skF_4')=k2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_203])).
% 4.80/1.89  tff(c_2381, plain, (k2_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_3'), '#skF_4')=k2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_107, c_108, c_76])).
% 4.80/1.89  tff(c_2560, plain, (k2_struct_0('#skF_3')=k2_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2559, c_2381])).
% 4.80/1.89  tff(c_86, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_203])).
% 4.80/1.89  tff(c_134, plain, (![A_51]: (~v1_xboole_0(u1_struct_0(A_51)) | ~l1_struct_0(A_51) | v2_struct_0(A_51))), inference(cnfTransformation, [status(thm)], [f_135])).
% 4.80/1.89  tff(c_140, plain, (~v1_xboole_0(k2_struct_0('#skF_3')) | ~l1_struct_0('#skF_3') | v2_struct_0('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_107, c_134])).
% 4.80/1.89  tff(c_144, plain, (~v1_xboole_0(k2_struct_0('#skF_3')) | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_84, c_140])).
% 4.80/1.89  tff(c_145, plain, (~v1_xboole_0(k2_struct_0('#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_86, c_144])).
% 4.80/1.89  tff(c_2571, plain, (~v1_xboole_0(k2_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_2560, c_145])).
% 4.80/1.89  tff(c_2420, plain, (![C_376, A_377, B_378]: (v4_relat_1(C_376, A_377) | ~m1_subset_1(C_376, k1_zfmisc_1(k2_zfmisc_1(A_377, B_378))))), inference(cnfTransformation, [status(thm)], [f_79])).
% 4.80/1.89  tff(c_2429, plain, (v4_relat_1('#skF_4', k2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_2369, c_2420])).
% 4.80/1.89  tff(c_2514, plain, (![B_399, A_400]: (k1_relat_1(B_399)=A_400 | ~v1_partfun1(B_399, A_400) | ~v4_relat_1(B_399, A_400) | ~v1_relat_1(B_399))), inference(cnfTransformation, [status(thm)], [f_123])).
% 4.80/1.89  tff(c_2517, plain, (k2_struct_0('#skF_2')=k1_relat_1('#skF_4') | ~v1_partfun1('#skF_4', k2_struct_0('#skF_2')) | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_2429, c_2514])).
% 4.80/1.89  tff(c_2520, plain, (k2_struct_0('#skF_2')=k1_relat_1('#skF_4') | ~v1_partfun1('#skF_4', k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_2395, c_2517])).
% 4.80/1.89  tff(c_2521, plain, (~v1_partfun1('#skF_4', k2_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_2520])).
% 4.80/1.89  tff(c_82, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_203])).
% 4.80/1.89  tff(c_80, plain, (v1_funct_2('#skF_4', u1_struct_0('#skF_2'), u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_203])).
% 4.80/1.89  tff(c_109, plain, (v1_funct_2('#skF_4', u1_struct_0('#skF_2'), k2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_107, c_80])).
% 4.80/1.89  tff(c_133, plain, (v1_funct_2('#skF_4', k2_struct_0('#skF_2'), k2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_108, c_109])).
% 4.80/1.89  tff(c_2572, plain, (v1_funct_2('#skF_4', k2_struct_0('#skF_2'), k2_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_2560, c_133])).
% 4.80/1.89  tff(c_2570, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_2'), k2_relat_1('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_2560, c_2369])).
% 4.80/1.89  tff(c_2782, plain, (![C_452, A_453, B_454]: (v1_partfun1(C_452, A_453) | ~v1_funct_2(C_452, A_453, B_454) | ~v1_funct_1(C_452) | ~m1_subset_1(C_452, k1_zfmisc_1(k2_zfmisc_1(A_453, B_454))) | v1_xboole_0(B_454))), inference(cnfTransformation, [status(thm)], [f_97])).
% 4.80/1.89  tff(c_2785, plain, (v1_partfun1('#skF_4', k2_struct_0('#skF_2')) | ~v1_funct_2('#skF_4', k2_struct_0('#skF_2'), k2_relat_1('#skF_4')) | ~v1_funct_1('#skF_4') | v1_xboole_0(k2_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_2570, c_2782])).
% 4.80/1.89  tff(c_2792, plain, (v1_partfun1('#skF_4', k2_struct_0('#skF_2')) | v1_xboole_0(k2_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_2572, c_2785])).
% 4.80/1.89  tff(c_2794, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2571, c_2521, c_2792])).
% 4.80/1.89  tff(c_2795, plain, (k2_struct_0('#skF_2')=k1_relat_1('#skF_4')), inference(splitRight, [status(thm)], [c_2520])).
% 4.80/1.89  tff(c_169, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_108, c_107, c_78])).
% 4.80/1.89  tff(c_26, plain, (![C_14, A_12, B_13]: (v1_relat_1(C_14) | ~m1_subset_1(C_14, k1_zfmisc_1(k2_zfmisc_1(A_12, B_13))))), inference(cnfTransformation, [status(thm)], [f_73])).
% 4.80/1.89  tff(c_176, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_169, c_26])).
% 4.80/1.89  tff(c_74, plain, (v2_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_203])).
% 4.80/1.89  tff(c_22, plain, (![A_11]: (k2_relat_1(k2_funct_1(A_11))=k1_relat_1(A_11) | ~v2_funct_1(A_11) | ~v1_funct_1(A_11) | ~v1_relat_1(A_11))), inference(cnfTransformation, [status(thm)], [f_69])).
% 4.80/1.89  tff(c_1281, plain, (![A_242, B_243, C_244]: (k2_relset_1(A_242, B_243, C_244)=k2_relat_1(C_244) | ~m1_subset_1(C_244, k1_zfmisc_1(k2_zfmisc_1(A_242, B_243))))), inference(cnfTransformation, [status(thm)], [f_83])).
% 4.80/1.89  tff(c_1289, plain, (k2_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_3'), '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_169, c_1281])).
% 4.80/1.89  tff(c_147, plain, (k2_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_3'), '#skF_4')=k2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_108, c_107, c_76])).
% 4.80/1.89  tff(c_1291, plain, (k2_struct_0('#skF_3')=k2_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1289, c_147])).
% 4.80/1.89  tff(c_1303, plain, (~v1_xboole_0(k2_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_1291, c_145])).
% 4.80/1.89  tff(c_192, plain, (![C_69, A_70, B_71]: (v4_relat_1(C_69, A_70) | ~m1_subset_1(C_69, k1_zfmisc_1(k2_zfmisc_1(A_70, B_71))))), inference(cnfTransformation, [status(thm)], [f_79])).
% 4.80/1.89  tff(c_200, plain, (v4_relat_1('#skF_4', k2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_169, c_192])).
% 4.80/1.89  tff(c_1229, plain, (![B_231, A_232]: (k1_relat_1(B_231)=A_232 | ~v1_partfun1(B_231, A_232) | ~v4_relat_1(B_231, A_232) | ~v1_relat_1(B_231))), inference(cnfTransformation, [status(thm)], [f_123])).
% 4.80/1.89  tff(c_1232, plain, (k2_struct_0('#skF_2')=k1_relat_1('#skF_4') | ~v1_partfun1('#skF_4', k2_struct_0('#skF_2')) | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_200, c_1229])).
% 4.80/1.89  tff(c_1235, plain, (k2_struct_0('#skF_2')=k1_relat_1('#skF_4') | ~v1_partfun1('#skF_4', k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_176, c_1232])).
% 4.80/1.89  tff(c_1236, plain, (~v1_partfun1('#skF_4', k2_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_1235])).
% 4.80/1.89  tff(c_1304, plain, (v1_funct_2('#skF_4', k2_struct_0('#skF_2'), k2_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_1291, c_133])).
% 4.80/1.89  tff(c_1302, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_2'), k2_relat_1('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_1291, c_169])).
% 4.80/1.89  tff(c_1431, plain, (![C_262, A_263, B_264]: (v1_partfun1(C_262, A_263) | ~v1_funct_2(C_262, A_263, B_264) | ~v1_funct_1(C_262) | ~m1_subset_1(C_262, k1_zfmisc_1(k2_zfmisc_1(A_263, B_264))) | v1_xboole_0(B_264))), inference(cnfTransformation, [status(thm)], [f_97])).
% 4.80/1.89  tff(c_1434, plain, (v1_partfun1('#skF_4', k2_struct_0('#skF_2')) | ~v1_funct_2('#skF_4', k2_struct_0('#skF_2'), k2_relat_1('#skF_4')) | ~v1_funct_1('#skF_4') | v1_xboole_0(k2_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_1302, c_1431])).
% 4.80/1.89  tff(c_1441, plain, (v1_partfun1('#skF_4', k2_struct_0('#skF_2')) | v1_xboole_0(k2_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_1304, c_1434])).
% 4.80/1.89  tff(c_1443, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1303, c_1236, c_1441])).
% 4.80/1.89  tff(c_1444, plain, (k2_struct_0('#skF_2')=k1_relat_1('#skF_4')), inference(splitRight, [status(thm)], [c_1235])).
% 4.80/1.89  tff(c_1451, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'), k2_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_1444, c_169])).
% 4.80/1.89  tff(c_1574, plain, (![A_273, B_274, C_275]: (k2_relset_1(A_273, B_274, C_275)=k2_relat_1(C_275) | ~m1_subset_1(C_275, k1_zfmisc_1(k2_zfmisc_1(A_273, B_274))))), inference(cnfTransformation, [status(thm)], [f_83])).
% 4.80/1.89  tff(c_1582, plain, (k2_relset_1(k1_relat_1('#skF_4'), k2_struct_0('#skF_3'), '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_1451, c_1574])).
% 4.80/1.89  tff(c_1452, plain, (k2_relset_1(k1_relat_1('#skF_4'), k2_struct_0('#skF_3'), '#skF_4')=k2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1444, c_147])).
% 4.80/1.89  tff(c_1584, plain, (k2_struct_0('#skF_3')=k2_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1582, c_1452])).
% 4.80/1.89  tff(c_1454, plain, (v1_funct_2('#skF_4', k1_relat_1('#skF_4'), k2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_1444, c_133])).
% 4.80/1.89  tff(c_1593, plain, (v1_funct_2('#skF_4', k1_relat_1('#skF_4'), k2_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_1584, c_1454])).
% 4.80/1.89  tff(c_1590, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'), k2_relat_1('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_1584, c_1451])).
% 4.80/1.89  tff(c_1589, plain, (k2_relset_1(k1_relat_1('#skF_4'), k2_relat_1('#skF_4'), '#skF_4')=k2_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1584, c_1582])).
% 4.80/1.89  tff(c_1999, plain, (![A_345, B_346, C_347]: (k2_tops_2(A_345, B_346, C_347)=k2_funct_1(C_347) | ~v2_funct_1(C_347) | k2_relset_1(A_345, B_346, C_347)!=B_346 | ~m1_subset_1(C_347, k1_zfmisc_1(k2_zfmisc_1(A_345, B_346))) | ~v1_funct_2(C_347, A_345, B_346) | ~v1_funct_1(C_347))), inference(cnfTransformation, [status(thm)], [f_167])).
% 4.80/1.89  tff(c_2005, plain, (k2_tops_2(k1_relat_1('#skF_4'), k2_relat_1('#skF_4'), '#skF_4')=k2_funct_1('#skF_4') | ~v2_funct_1('#skF_4') | k2_relset_1(k1_relat_1('#skF_4'), k2_relat_1('#skF_4'), '#skF_4')!=k2_relat_1('#skF_4') | ~v1_funct_2('#skF_4', k1_relat_1('#skF_4'), k2_relat_1('#skF_4')) | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_1590, c_1999])).
% 4.80/1.89  tff(c_2013, plain, (k2_tops_2(k1_relat_1('#skF_4'), k2_relat_1('#skF_4'), '#skF_4')=k2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_82, c_1593, c_1589, c_74, c_2005])).
% 4.80/1.89  tff(c_66, plain, (![A_39, B_40, C_41]: (m1_subset_1(k2_tops_2(A_39, B_40, C_41), k1_zfmisc_1(k2_zfmisc_1(B_40, A_39))) | ~m1_subset_1(C_41, k1_zfmisc_1(k2_zfmisc_1(A_39, B_40))) | ~v1_funct_2(C_41, A_39, B_40) | ~v1_funct_1(C_41))), inference(cnfTransformation, [status(thm)], [f_179])).
% 4.80/1.89  tff(c_2026, plain, (m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_4'), k1_relat_1('#skF_4')))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'), k2_relat_1('#skF_4')))) | ~v1_funct_2('#skF_4', k1_relat_1('#skF_4'), k2_relat_1('#skF_4')) | ~v1_funct_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_2013, c_66])).
% 4.80/1.89  tff(c_2032, plain, (m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_4'), k1_relat_1('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_1593, c_1590, c_2026])).
% 4.80/1.89  tff(c_32, plain, (![A_18, B_19, C_20]: (k2_relset_1(A_18, B_19, C_20)=k2_relat_1(C_20) | ~m1_subset_1(C_20, k1_zfmisc_1(k2_zfmisc_1(A_18, B_19))))), inference(cnfTransformation, [status(thm)], [f_83])).
% 4.80/1.89  tff(c_2101, plain, (k2_relset_1(k2_relat_1('#skF_4'), k1_relat_1('#skF_4'), k2_funct_1('#skF_4'))=k2_relat_1(k2_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_2032, c_32])).
% 4.80/1.89  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 4.80/1.89  tff(c_324, plain, (![A_102, B_103, C_104]: (k2_relset_1(A_102, B_103, C_104)=k2_relat_1(C_104) | ~m1_subset_1(C_104, k1_zfmisc_1(k2_zfmisc_1(A_102, B_103))))), inference(cnfTransformation, [status(thm)], [f_83])).
% 4.80/1.89  tff(c_332, plain, (k2_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_3'), '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_169, c_324])).
% 4.80/1.89  tff(c_334, plain, (k2_struct_0('#skF_3')=k2_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_332, c_147])).
% 4.80/1.89  tff(c_345, plain, (~v1_xboole_0(k2_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_334, c_145])).
% 4.80/1.89  tff(c_271, plain, (![B_90, A_91]: (k1_relat_1(B_90)=A_91 | ~v1_partfun1(B_90, A_91) | ~v4_relat_1(B_90, A_91) | ~v1_relat_1(B_90))), inference(cnfTransformation, [status(thm)], [f_123])).
% 4.80/1.89  tff(c_274, plain, (k2_struct_0('#skF_2')=k1_relat_1('#skF_4') | ~v1_partfun1('#skF_4', k2_struct_0('#skF_2')) | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_200, c_271])).
% 4.80/1.89  tff(c_277, plain, (k2_struct_0('#skF_2')=k1_relat_1('#skF_4') | ~v1_partfun1('#skF_4', k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_176, c_274])).
% 4.80/1.89  tff(c_279, plain, (~v1_partfun1('#skF_4', k2_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_277])).
% 4.80/1.89  tff(c_346, plain, (v1_funct_2('#skF_4', k2_struct_0('#skF_2'), k2_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_334, c_133])).
% 4.80/1.89  tff(c_344, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_2'), k2_relat_1('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_334, c_169])).
% 4.80/1.89  tff(c_500, plain, (![C_130, A_131, B_132]: (v1_partfun1(C_130, A_131) | ~v1_funct_2(C_130, A_131, B_132) | ~v1_funct_1(C_130) | ~m1_subset_1(C_130, k1_zfmisc_1(k2_zfmisc_1(A_131, B_132))) | v1_xboole_0(B_132))), inference(cnfTransformation, [status(thm)], [f_97])).
% 4.80/1.89  tff(c_503, plain, (v1_partfun1('#skF_4', k2_struct_0('#skF_2')) | ~v1_funct_2('#skF_4', k2_struct_0('#skF_2'), k2_relat_1('#skF_4')) | ~v1_funct_1('#skF_4') | v1_xboole_0(k2_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_344, c_500])).
% 4.80/1.89  tff(c_510, plain, (v1_partfun1('#skF_4', k2_struct_0('#skF_2')) | v1_xboole_0(k2_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_346, c_503])).
% 4.80/1.89  tff(c_512, plain, $false, inference(negUnitSimplification, [status(thm)], [c_345, c_279, c_510])).
% 4.80/1.89  tff(c_513, plain, (k2_struct_0('#skF_2')=k1_relat_1('#skF_4')), inference(splitRight, [status(thm)], [c_277])).
% 4.80/1.89  tff(c_519, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'), k2_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_513, c_169])).
% 4.80/1.89  tff(c_642, plain, (![A_140, B_141, C_142]: (k2_relset_1(A_140, B_141, C_142)=k2_relat_1(C_142) | ~m1_subset_1(C_142, k1_zfmisc_1(k2_zfmisc_1(A_140, B_141))))), inference(cnfTransformation, [status(thm)], [f_83])).
% 4.80/1.89  tff(c_650, plain, (k2_relset_1(k1_relat_1('#skF_4'), k2_struct_0('#skF_3'), '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_519, c_642])).
% 4.80/1.89  tff(c_520, plain, (k2_relset_1(k1_relat_1('#skF_4'), k2_struct_0('#skF_3'), '#skF_4')=k2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_513, c_147])).
% 4.80/1.89  tff(c_652, plain, (k2_struct_0('#skF_3')=k2_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_650, c_520])).
% 4.80/1.89  tff(c_522, plain, (v1_funct_2('#skF_4', k1_relat_1('#skF_4'), k2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_513, c_133])).
% 4.80/1.89  tff(c_661, plain, (v1_funct_2('#skF_4', k1_relat_1('#skF_4'), k2_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_652, c_522])).
% 4.80/1.89  tff(c_657, plain, (k2_relset_1(k1_relat_1('#skF_4'), k2_relat_1('#skF_4'), '#skF_4')=k2_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_652, c_650])).
% 4.80/1.89  tff(c_658, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'), k2_relat_1('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_652, c_519])).
% 4.80/1.89  tff(c_1065, plain, (![A_215, B_216, C_217]: (k2_tops_2(A_215, B_216, C_217)=k2_funct_1(C_217) | ~v2_funct_1(C_217) | k2_relset_1(A_215, B_216, C_217)!=B_216 | ~m1_subset_1(C_217, k1_zfmisc_1(k2_zfmisc_1(A_215, B_216))) | ~v1_funct_2(C_217, A_215, B_216) | ~v1_funct_1(C_217))), inference(cnfTransformation, [status(thm)], [f_167])).
% 4.80/1.89  tff(c_1071, plain, (k2_tops_2(k1_relat_1('#skF_4'), k2_relat_1('#skF_4'), '#skF_4')=k2_funct_1('#skF_4') | ~v2_funct_1('#skF_4') | k2_relset_1(k1_relat_1('#skF_4'), k2_relat_1('#skF_4'), '#skF_4')!=k2_relat_1('#skF_4') | ~v1_funct_2('#skF_4', k1_relat_1('#skF_4'), k2_relat_1('#skF_4')) | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_658, c_1065])).
% 4.80/1.89  tff(c_1079, plain, (k2_tops_2(k1_relat_1('#skF_4'), k2_relat_1('#skF_4'), '#skF_4')=k2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_82, c_661, c_657, c_74, c_1071])).
% 4.80/1.89  tff(c_72, plain, (k2_relset_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), k2_tops_2(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), '#skF_4'))!=k2_struct_0('#skF_2') | k1_relset_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), k2_tops_2(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), '#skF_4'))!=k2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_203])).
% 4.80/1.89  tff(c_234, plain, (k2_relset_1(k2_struct_0('#skF_3'), k2_struct_0('#skF_2'), k2_tops_2(k2_struct_0('#skF_2'), k2_struct_0('#skF_3'), '#skF_4'))!=k2_struct_0('#skF_2') | k1_relset_1(k2_struct_0('#skF_3'), k2_struct_0('#skF_2'), k2_tops_2(k2_struct_0('#skF_2'), k2_struct_0('#skF_3'), '#skF_4'))!=k2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_108, c_108, c_107, c_107, c_108, c_108, c_107, c_107, c_72])).
% 4.80/1.89  tff(c_235, plain, (k1_relset_1(k2_struct_0('#skF_3'), k2_struct_0('#skF_2'), k2_tops_2(k2_struct_0('#skF_2'), k2_struct_0('#skF_3'), '#skF_4'))!=k2_struct_0('#skF_3')), inference(splitLeft, [status(thm)], [c_234])).
% 4.80/1.89  tff(c_515, plain, (k1_relset_1(k2_struct_0('#skF_3'), k1_relat_1('#skF_4'), k2_tops_2(k1_relat_1('#skF_4'), k2_struct_0('#skF_3'), '#skF_4'))!=k2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_513, c_513, c_235])).
% 4.80/1.89  tff(c_742, plain, (k1_relset_1(k2_relat_1('#skF_4'), k1_relat_1('#skF_4'), k2_tops_2(k1_relat_1('#skF_4'), k2_relat_1('#skF_4'), '#skF_4'))!=k2_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_652, c_652, c_652, c_515])).
% 4.80/1.89  tff(c_1084, plain, (k1_relset_1(k2_relat_1('#skF_4'), k1_relat_1('#skF_4'), k2_funct_1('#skF_4'))!=k2_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1079, c_742])).
% 4.80/1.89  tff(c_912, plain, (![A_194, B_195, C_196]: (v1_funct_2(k2_tops_2(A_194, B_195, C_196), B_195, A_194) | ~m1_subset_1(C_196, k1_zfmisc_1(k2_zfmisc_1(A_194, B_195))) | ~v1_funct_2(C_196, A_194, B_195) | ~v1_funct_1(C_196))), inference(cnfTransformation, [status(thm)], [f_179])).
% 4.80/1.89  tff(c_914, plain, (v1_funct_2(k2_tops_2(k1_relat_1('#skF_4'), k2_relat_1('#skF_4'), '#skF_4'), k2_relat_1('#skF_4'), k1_relat_1('#skF_4')) | ~v1_funct_2('#skF_4', k1_relat_1('#skF_4'), k2_relat_1('#skF_4')) | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_658, c_912])).
% 4.80/1.89  tff(c_920, plain, (v1_funct_2(k2_tops_2(k1_relat_1('#skF_4'), k2_relat_1('#skF_4'), '#skF_4'), k2_relat_1('#skF_4'), k1_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_661, c_914])).
% 4.80/1.89  tff(c_1082, plain, (v1_funct_2(k2_funct_1('#skF_4'), k2_relat_1('#skF_4'), k1_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_1079, c_920])).
% 4.80/1.89  tff(c_1088, plain, (m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_4'), k1_relat_1('#skF_4')))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'), k2_relat_1('#skF_4')))) | ~v1_funct_2('#skF_4', k1_relat_1('#skF_4'), k2_relat_1('#skF_4')) | ~v1_funct_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1079, c_66])).
% 4.80/1.89  tff(c_1092, plain, (m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_4'), k1_relat_1('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_661, c_658, c_1088])).
% 4.80/1.89  tff(c_48, plain, (![B_26, A_25, C_27]: (k1_xboole_0=B_26 | k1_relset_1(A_25, B_26, C_27)=A_25 | ~v1_funct_2(C_27, A_25, B_26) | ~m1_subset_1(C_27, k1_zfmisc_1(k2_zfmisc_1(A_25, B_26))))), inference(cnfTransformation, [status(thm)], [f_115])).
% 4.80/1.89  tff(c_1113, plain, (k1_relat_1('#skF_4')=k1_xboole_0 | k1_relset_1(k2_relat_1('#skF_4'), k1_relat_1('#skF_4'), k2_funct_1('#skF_4'))=k2_relat_1('#skF_4') | ~v1_funct_2(k2_funct_1('#skF_4'), k2_relat_1('#skF_4'), k1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_1092, c_48])).
% 4.80/1.89  tff(c_1152, plain, (k1_relat_1('#skF_4')=k1_xboole_0 | k1_relset_1(k2_relat_1('#skF_4'), k1_relat_1('#skF_4'), k2_funct_1('#skF_4'))=k2_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1082, c_1113])).
% 4.80/1.89  tff(c_1153, plain, (k1_relat_1('#skF_4')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_1084, c_1152])).
% 4.80/1.89  tff(c_137, plain, (~v1_xboole_0(k2_struct_0('#skF_2')) | ~l1_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_108, c_134])).
% 4.80/1.89  tff(c_142, plain, (~v1_xboole_0(k2_struct_0('#skF_2')) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_88, c_137])).
% 4.80/1.89  tff(c_146, plain, (~v1_xboole_0(k2_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_142])).
% 4.80/1.89  tff(c_521, plain, (~v1_xboole_0(k1_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_513, c_146])).
% 4.80/1.89  tff(c_1176, plain, (~v1_xboole_0(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_1153, c_521])).
% 4.80/1.89  tff(c_1180, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2, c_1176])).
% 4.80/1.89  tff(c_1181, plain, (k2_relset_1(k2_struct_0('#skF_3'), k2_struct_0('#skF_2'), k2_tops_2(k2_struct_0('#skF_2'), k2_struct_0('#skF_3'), '#skF_4'))!=k2_struct_0('#skF_2')), inference(splitRight, [status(thm)], [c_234])).
% 4.80/1.89  tff(c_1448, plain, (k2_relset_1(k2_struct_0('#skF_3'), k1_relat_1('#skF_4'), k2_tops_2(k1_relat_1('#skF_4'), k2_struct_0('#skF_3'), '#skF_4'))!=k1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1444, c_1444, c_1444, c_1181])).
% 4.80/1.89  tff(c_1692, plain, (k2_relset_1(k2_relat_1('#skF_4'), k1_relat_1('#skF_4'), k2_tops_2(k1_relat_1('#skF_4'), k2_relat_1('#skF_4'), '#skF_4'))!=k1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1584, c_1584, c_1448])).
% 4.80/1.89  tff(c_2018, plain, (k2_relset_1(k2_relat_1('#skF_4'), k1_relat_1('#skF_4'), k2_funct_1('#skF_4'))!=k1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2013, c_1692])).
% 4.80/1.89  tff(c_2353, plain, (k2_relat_1(k2_funct_1('#skF_4'))!=k1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2101, c_2018])).
% 4.80/1.89  tff(c_2360, plain, (~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_22, c_2353])).
% 4.80/1.89  tff(c_2364, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_176, c_82, c_74, c_2360])).
% 4.80/1.89  tff(c_2366, plain, (v1_xboole_0(k2_struct_0('#skF_2'))), inference(splitRight, [status(thm)], [c_142])).
% 4.80/1.89  tff(c_2803, plain, (v1_xboole_0(k1_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_2795, c_2366])).
% 4.80/1.89  tff(c_20, plain, (![A_10]: (~v1_xboole_0(k1_relat_1(A_10)) | ~v1_relat_1(A_10) | v1_xboole_0(A_10))), inference(cnfTransformation, [status(thm)], [f_59])).
% 4.80/1.89  tff(c_2812, plain, (~v1_relat_1('#skF_4') | v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_2803, c_20])).
% 4.80/1.89  tff(c_2815, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2395, c_2812])).
% 4.80/1.89  tff(c_18, plain, (![A_9]: (v1_xboole_0(k2_relat_1(A_9)) | ~v1_xboole_0(A_9))), inference(cnfTransformation, [status(thm)], [f_51])).
% 4.80/1.89  tff(c_2802, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'), k2_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_2795, c_2369])).
% 4.80/1.89  tff(c_2910, plain, (![A_464, B_465, C_466]: (k2_relset_1(A_464, B_465, C_466)=k2_relat_1(C_466) | ~m1_subset_1(C_466, k1_zfmisc_1(k2_zfmisc_1(A_464, B_465))))), inference(cnfTransformation, [status(thm)], [f_83])).
% 4.80/1.89  tff(c_2918, plain, (k2_relset_1(k1_relat_1('#skF_4'), k2_struct_0('#skF_3'), '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_2802, c_2910])).
% 4.80/1.89  tff(c_2800, plain, (k2_relset_1(k1_relat_1('#skF_4'), k2_struct_0('#skF_3'), '#skF_4')=k2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2795, c_2381])).
% 4.80/1.89  tff(c_2920, plain, (k2_struct_0('#skF_3')=k2_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2918, c_2800])).
% 4.80/1.89  tff(c_2937, plain, (~v1_xboole_0(k2_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_2920, c_145])).
% 4.80/1.89  tff(c_2945, plain, (~v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_18, c_2937])).
% 4.80/1.89  tff(c_2949, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2815, c_2945])).
% 4.80/1.89  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.80/1.89  
% 4.80/1.89  Inference rules
% 4.80/1.89  ----------------------
% 4.80/1.89  #Ref     : 0
% 4.80/1.89  #Sup     : 572
% 4.80/1.89  #Fact    : 0
% 4.80/1.89  #Define  : 0
% 4.80/1.89  #Split   : 18
% 4.80/1.89  #Chain   : 0
% 4.80/1.89  #Close   : 0
% 4.80/1.89  
% 4.80/1.89  Ordering : KBO
% 4.80/1.89  
% 4.80/1.89  Simplification rules
% 4.80/1.89  ----------------------
% 4.80/1.89  #Subsume      : 44
% 4.80/1.89  #Demod        : 489
% 4.80/1.89  #Tautology    : 255
% 4.80/1.89  #SimpNegUnit  : 43
% 4.80/1.89  #BackRed      : 113
% 4.80/1.89  
% 4.80/1.89  #Partial instantiations: 0
% 4.80/1.89  #Strategies tried      : 1
% 4.80/1.89  
% 4.80/1.89  Timing (in seconds)
% 4.80/1.89  ----------------------
% 4.80/1.89  Preprocessing        : 0.36
% 4.80/1.89  Parsing              : 0.19
% 4.80/1.89  CNF conversion       : 0.02
% 4.80/1.89  Main loop            : 0.74
% 4.80/1.89  Inferencing          : 0.27
% 4.80/1.89  Reduction            : 0.24
% 4.80/1.89  Demodulation         : 0.16
% 4.80/1.89  BG Simplification    : 0.03
% 4.80/1.89  Subsumption          : 0.12
% 4.80/1.89  Abstraction          : 0.03
% 4.80/1.89  MUC search           : 0.00
% 4.80/1.89  Cooper               : 0.00
% 4.80/1.89  Total                : 1.15
% 4.80/1.89  Index Insertion      : 0.00
% 4.80/1.89  Index Deletion       : 0.00
% 4.80/1.89  Index Matching       : 0.00
% 4.80/1.89  BG Taut test         : 0.00
%------------------------------------------------------------------------------
