%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:17:02 EST 2020

% Result     : Theorem 5.65s
% Output     : CNFRefutation 5.88s
% Verified   : 
% Statistics : Number of formulae       :  112 ( 698 expanded)
%              Number of leaves         :   35 ( 230 expanded)
%              Depth                    :   13
%              Number of atoms          :  180 (1957 expanded)
%              Number of equality atoms :   31 ( 709 expanded)
%              Maximal formula depth    :   14 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v1_partfun1 > r2_hidden > r1_partfun1 > m1_subset_1 > v1_xboole_0 > v1_funct_1 > k5_partfun1 > k2_zfmisc_1 > #nlpp > k6_partfun1 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_6 > #skF_7 > #skF_10 > #skF_2 > #skF_9 > #skF_4 > #skF_8 > #skF_5 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(v1_partfun1,type,(
    v1_partfun1: ( $i * $i ) > $o )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i * $i ) > $i )).

tff(k6_partfun1,type,(
    k6_partfun1: $i > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i * $i ) > $i )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i ) > $i )).

tff(k5_partfun1,type,(
    k5_partfun1: ( $i * $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(r1_partfun1,type,(
    r1_partfun1: ( $i * $i ) > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_37,axiom,(
    ? [A] : v1_xboole_0(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc1_xboole_0)).

tff(f_35,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_117,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ! [D] :
            ( ( v1_funct_1(D)
              & v1_funct_2(D,A,B)
              & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
           => ( r1_partfun1(C,D)
             => ( ( B = k1_xboole_0
                  & A != k1_xboole_0 )
                | r2_hidden(D,k5_partfun1(A,B,C)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t155_funct_2)).

tff(f_57,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(B,A)))
         => v1_xboole_0(C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc4_relset_1)).

tff(f_71,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => ( ( v1_funct_1(C)
              & v1_funct_2(C,A,B) )
           => ( v1_funct_1(C)
              & v1_partfun1(C,A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc5_funct_2)).

tff(f_92,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ! [D] :
          ( D = k5_partfun1(A,B,C)
        <=> ! [E] :
              ( r2_hidden(E,D)
            <=> ? [F] :
                  ( v1_funct_1(F)
                  & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(A,B)))
                  & F = E
                  & v1_partfun1(F,A)
                  & r1_partfun1(C,F) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_partfun1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_50,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

tff(f_96,axiom,(
    ! [A] :
      ( v1_partfun1(k6_partfun1(A),A)
      & m1_subset_1(k6_partfun1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_8,plain,(
    v1_xboole_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_103,plain,(
    ! [A_66] :
      ( k1_xboole_0 = A_66
      | ~ v1_xboole_0(A_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_107,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_8,c_103])).

tff(c_66,plain,
    ( k1_xboole_0 = '#skF_7'
    | k1_xboole_0 != '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_86,plain,(
    k1_xboole_0 != '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_66])).

tff(c_110,plain,(
    '#skF_2' != '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_107,c_86])).

tff(c_64,plain,(
    ~ r2_hidden('#skF_10',k5_partfun1('#skF_7','#skF_8','#skF_9')) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_78,plain,(
    v1_funct_1('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_68,plain,(
    r1_partfun1('#skF_9','#skF_10') ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_76,plain,(
    m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1('#skF_7','#skF_8'))) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_74,plain,(
    v1_funct_1('#skF_10') ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_226,plain,(
    ! [C_81,B_82,A_83] :
      ( v1_xboole_0(C_81)
      | ~ m1_subset_1(C_81,k1_zfmisc_1(k2_zfmisc_1(B_82,A_83)))
      | ~ v1_xboole_0(A_83) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_243,plain,
    ( v1_xboole_0('#skF_9')
    | ~ v1_xboole_0('#skF_8') ),
    inference(resolution,[status(thm)],[c_76,c_226])).

tff(c_247,plain,(
    ~ v1_xboole_0('#skF_8') ),
    inference(splitLeft,[status(thm)],[c_243])).

tff(c_72,plain,(
    v1_funct_2('#skF_10','#skF_7','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_70,plain,(
    m1_subset_1('#skF_10',k1_zfmisc_1(k2_zfmisc_1('#skF_7','#skF_8'))) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_316,plain,(
    ! [C_89,A_90,B_91] :
      ( v1_partfun1(C_89,A_90)
      | ~ v1_funct_2(C_89,A_90,B_91)
      | ~ v1_funct_1(C_89)
      | ~ m1_subset_1(C_89,k1_zfmisc_1(k2_zfmisc_1(A_90,B_91)))
      | v1_xboole_0(B_91) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_325,plain,
    ( v1_partfun1('#skF_10','#skF_7')
    | ~ v1_funct_2('#skF_10','#skF_7','#skF_8')
    | ~ v1_funct_1('#skF_10')
    | v1_xboole_0('#skF_8') ),
    inference(resolution,[status(thm)],[c_70,c_316])).

tff(c_340,plain,
    ( v1_partfun1('#skF_10','#skF_7')
    | v1_xboole_0('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_325])).

tff(c_341,plain,(
    v1_partfun1('#skF_10','#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_247,c_340])).

tff(c_2191,plain,(
    ! [F_295,A_296,B_297,C_298] :
      ( r2_hidden(F_295,k5_partfun1(A_296,B_297,C_298))
      | ~ r1_partfun1(C_298,F_295)
      | ~ v1_partfun1(F_295,A_296)
      | ~ m1_subset_1(F_295,k1_zfmisc_1(k2_zfmisc_1(A_296,B_297)))
      | ~ v1_funct_1(F_295)
      | ~ m1_subset_1(C_298,k1_zfmisc_1(k2_zfmisc_1(A_296,B_297)))
      | ~ v1_funct_1(C_298) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_2201,plain,(
    ! [C_298] :
      ( r2_hidden('#skF_10',k5_partfun1('#skF_7','#skF_8',C_298))
      | ~ r1_partfun1(C_298,'#skF_10')
      | ~ v1_partfun1('#skF_10','#skF_7')
      | ~ v1_funct_1('#skF_10')
      | ~ m1_subset_1(C_298,k1_zfmisc_1(k2_zfmisc_1('#skF_7','#skF_8')))
      | ~ v1_funct_1(C_298) ) ),
    inference(resolution,[status(thm)],[c_70,c_2191])).

tff(c_2219,plain,(
    ! [C_299] :
      ( r2_hidden('#skF_10',k5_partfun1('#skF_7','#skF_8',C_299))
      | ~ r1_partfun1(C_299,'#skF_10')
      | ~ m1_subset_1(C_299,k1_zfmisc_1(k2_zfmisc_1('#skF_7','#skF_8')))
      | ~ v1_funct_1(C_299) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_341,c_2201])).

tff(c_2226,plain,
    ( r2_hidden('#skF_10',k5_partfun1('#skF_7','#skF_8','#skF_9'))
    | ~ r1_partfun1('#skF_9','#skF_10')
    | ~ v1_funct_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_76,c_2219])).

tff(c_2233,plain,(
    r2_hidden('#skF_10',k5_partfun1('#skF_7','#skF_8','#skF_9')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_68,c_2226])).

tff(c_2235,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_2233])).

tff(c_2237,plain,(
    v1_xboole_0('#skF_8') ),
    inference(splitRight,[status(thm)],[c_243])).

tff(c_6,plain,(
    ! [A_5] :
      ( k1_xboole_0 = A_5
      | ~ v1_xboole_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_108,plain,(
    ! [A_5] :
      ( A_5 = '#skF_2'
      | ~ v1_xboole_0(A_5) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_107,c_6])).

tff(c_2244,plain,(
    '#skF_2' = '#skF_8' ),
    inference(resolution,[status(thm)],[c_2237,c_108])).

tff(c_2248,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_110,c_2244])).

tff(c_2250,plain,(
    k1_xboole_0 = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_66])).

tff(c_2276,plain,(
    ! [A_301] :
      ( A_301 = '#skF_8'
      | ~ v1_xboole_0(A_301) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2250,c_6])).

tff(c_2280,plain,(
    '#skF_2' = '#skF_8' ),
    inference(resolution,[status(thm)],[c_8,c_2276])).

tff(c_2281,plain,(
    v1_xboole_0('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2280,c_8])).

tff(c_2249,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_66])).

tff(c_2256,plain,(
    '#skF_7' = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2250,c_2249])).

tff(c_14,plain,(
    ! [B_7] : k2_zfmisc_1(k1_xboole_0,B_7) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_2251,plain,(
    ! [B_7] : k2_zfmisc_1('#skF_7',B_7) = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2249,c_2249,c_14])).

tff(c_2267,plain,(
    ! [B_7] : k2_zfmisc_1('#skF_8',B_7) = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2256,c_2256,c_2251])).

tff(c_2315,plain,(
    m1_subset_1('#skF_10',k1_zfmisc_1('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2267,c_2256,c_70])).

tff(c_2338,plain,(
    ! [C_310,B_311,A_312] :
      ( ~ v1_xboole_0(C_310)
      | ~ m1_subset_1(B_311,k1_zfmisc_1(C_310))
      | ~ r2_hidden(A_312,B_311) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_2344,plain,(
    ! [A_312] :
      ( ~ v1_xboole_0('#skF_8')
      | ~ r2_hidden(A_312,'#skF_10') ) ),
    inference(resolution,[status(thm)],[c_2315,c_2338])).

tff(c_2357,plain,(
    ! [A_313] : ~ r2_hidden(A_313,'#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2281,c_2344])).

tff(c_2362,plain,(
    v1_xboole_0('#skF_10') ),
    inference(resolution,[status(thm)],[c_4,c_2357])).

tff(c_2275,plain,(
    ! [A_5] :
      ( A_5 = '#skF_8'
      | ~ v1_xboole_0(A_5) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2250,c_6])).

tff(c_2366,plain,(
    '#skF_10' = '#skF_8' ),
    inference(resolution,[status(thm)],[c_2362,c_2275])).

tff(c_2373,plain,(
    v1_funct_1('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2366,c_74])).

tff(c_2369,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2366,c_2315])).

tff(c_2307,plain,(
    m1_subset_1('#skF_9',k1_zfmisc_1('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2267,c_2256,c_76])).

tff(c_2346,plain,(
    ! [A_312] :
      ( ~ v1_xboole_0('#skF_8')
      | ~ r2_hidden(A_312,'#skF_9') ) ),
    inference(resolution,[status(thm)],[c_2307,c_2338])).

tff(c_2379,plain,(
    ! [A_314] : ~ r2_hidden(A_314,'#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2281,c_2346])).

tff(c_2384,plain,(
    v1_xboole_0('#skF_9') ),
    inference(resolution,[status(thm)],[c_4,c_2379])).

tff(c_2401,plain,(
    '#skF_9' = '#skF_8' ),
    inference(resolution,[status(thm)],[c_2384,c_2275])).

tff(c_2372,plain,(
    r1_partfun1('#skF_9','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2366,c_68])).

tff(c_2412,plain,(
    r1_partfun1('#skF_8','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2401,c_2372])).

tff(c_12,plain,(
    ! [A_6] : k2_zfmisc_1(A_6,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_2291,plain,(
    ! [A_6] : k2_zfmisc_1(A_6,'#skF_8') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2250,c_2250,c_12])).

tff(c_2316,plain,(
    ! [A_307] : m1_subset_1(k6_partfun1(A_307),k1_zfmisc_1(k2_zfmisc_1(A_307,A_307))) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_2320,plain,(
    m1_subset_1(k6_partfun1('#skF_8'),k1_zfmisc_1('#skF_8')) ),
    inference(superposition,[status(thm),theory(equality)],[c_2291,c_2316])).

tff(c_2340,plain,(
    ! [A_312] :
      ( ~ v1_xboole_0('#skF_8')
      | ~ r2_hidden(A_312,k6_partfun1('#skF_8')) ) ),
    inference(resolution,[status(thm)],[c_2320,c_2338])).

tff(c_2420,plain,(
    ! [A_319] : ~ r2_hidden(A_319,k6_partfun1('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2281,c_2340])).

tff(c_2425,plain,(
    v1_xboole_0(k6_partfun1('#skF_8')) ),
    inference(resolution,[status(thm)],[c_4,c_2420])).

tff(c_2429,plain,(
    k6_partfun1('#skF_8') = '#skF_8' ),
    inference(resolution,[status(thm)],[c_2425,c_2275])).

tff(c_60,plain,(
    ! [A_61] : v1_partfun1(k6_partfun1(A_61),A_61) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_62,plain,(
    ! [A_61] : m1_subset_1(k6_partfun1(A_61),k1_zfmisc_1(k2_zfmisc_1(A_61,A_61))) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_3502,plain,(
    ! [F_515,A_516,B_517,C_518] :
      ( r2_hidden(F_515,k5_partfun1(A_516,B_517,C_518))
      | ~ r1_partfun1(C_518,F_515)
      | ~ v1_partfun1(F_515,A_516)
      | ~ m1_subset_1(F_515,k1_zfmisc_1(k2_zfmisc_1(A_516,B_517)))
      | ~ v1_funct_1(F_515)
      | ~ m1_subset_1(C_518,k1_zfmisc_1(k2_zfmisc_1(A_516,B_517)))
      | ~ v1_funct_1(C_518) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_3506,plain,(
    ! [A_61,C_518] :
      ( r2_hidden(k6_partfun1(A_61),k5_partfun1(A_61,A_61,C_518))
      | ~ r1_partfun1(C_518,k6_partfun1(A_61))
      | ~ v1_partfun1(k6_partfun1(A_61),A_61)
      | ~ v1_funct_1(k6_partfun1(A_61))
      | ~ m1_subset_1(C_518,k1_zfmisc_1(k2_zfmisc_1(A_61,A_61)))
      | ~ v1_funct_1(C_518) ) ),
    inference(resolution,[status(thm)],[c_62,c_3502])).

tff(c_3521,plain,(
    ! [A_524,C_525] :
      ( r2_hidden(k6_partfun1(A_524),k5_partfun1(A_524,A_524,C_525))
      | ~ r1_partfun1(C_525,k6_partfun1(A_524))
      | ~ v1_funct_1(k6_partfun1(A_524))
      | ~ m1_subset_1(C_525,k1_zfmisc_1(k2_zfmisc_1(A_524,A_524)))
      | ~ v1_funct_1(C_525) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_3506])).

tff(c_3535,plain,(
    ! [C_525] :
      ( r2_hidden('#skF_8',k5_partfun1('#skF_8','#skF_8',C_525))
      | ~ r1_partfun1(C_525,k6_partfun1('#skF_8'))
      | ~ v1_funct_1(k6_partfun1('#skF_8'))
      | ~ m1_subset_1(C_525,k1_zfmisc_1(k2_zfmisc_1('#skF_8','#skF_8')))
      | ~ v1_funct_1(C_525) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2429,c_3521])).

tff(c_3568,plain,(
    ! [C_527] :
      ( r2_hidden('#skF_8',k5_partfun1('#skF_8','#skF_8',C_527))
      | ~ r1_partfun1(C_527,'#skF_8')
      | ~ m1_subset_1(C_527,k1_zfmisc_1('#skF_8'))
      | ~ v1_funct_1(C_527) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2291,c_2373,c_2429,c_2429,c_3535])).

tff(c_2261,plain,(
    ~ r2_hidden('#skF_10',k5_partfun1('#skF_8','#skF_8','#skF_9')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2256,c_64])).

tff(c_2370,plain,(
    ~ r2_hidden('#skF_8',k5_partfun1('#skF_8','#skF_8','#skF_9')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2366,c_2261])).

tff(c_2464,plain,(
    ~ r2_hidden('#skF_8',k5_partfun1('#skF_8','#skF_8','#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2401,c_2370])).

tff(c_3573,plain,
    ( ~ r1_partfun1('#skF_8','#skF_8')
    | ~ m1_subset_1('#skF_8',k1_zfmisc_1('#skF_8'))
    | ~ v1_funct_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_3568,c_2464])).

tff(c_3582,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2373,c_2369,c_2412,c_3573])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n005.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:01:32 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.65/2.16  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.88/2.17  
% 5.88/2.17  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.88/2.17  %$ v1_funct_2 > v1_partfun1 > r2_hidden > r1_partfun1 > m1_subset_1 > v1_xboole_0 > v1_funct_1 > k5_partfun1 > k2_zfmisc_1 > #nlpp > k6_partfun1 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_6 > #skF_7 > #skF_10 > #skF_2 > #skF_9 > #skF_4 > #skF_8 > #skF_5 > #skF_3
% 5.88/2.17  
% 5.88/2.17  %Foreground sorts:
% 5.88/2.17  
% 5.88/2.17  
% 5.88/2.17  %Background operators:
% 5.88/2.17  
% 5.88/2.17  
% 5.88/2.17  %Foreground operators:
% 5.88/2.17  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 5.88/2.17  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.88/2.17  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.88/2.17  tff('#skF_1', type, '#skF_1': $i > $i).
% 5.88/2.17  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.88/2.17  tff('#skF_6', type, '#skF_6': ($i * $i * $i * $i * $i) > $i).
% 5.88/2.17  tff('#skF_7', type, '#skF_7': $i).
% 5.88/2.17  tff('#skF_10', type, '#skF_10': $i).
% 5.88/2.17  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 5.88/2.17  tff('#skF_2', type, '#skF_2': $i).
% 5.88/2.17  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 5.88/2.17  tff('#skF_9', type, '#skF_9': $i).
% 5.88/2.17  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.88/2.17  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i) > $i).
% 5.88/2.17  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 5.88/2.17  tff('#skF_8', type, '#skF_8': $i).
% 5.88/2.17  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.88/2.17  tff('#skF_5', type, '#skF_5': ($i * $i * $i * $i) > $i).
% 5.88/2.17  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 5.88/2.17  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.88/2.17  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 5.88/2.17  tff(k5_partfun1, type, k5_partfun1: ($i * $i * $i) > $i).
% 5.88/2.17  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 5.88/2.17  tff(r1_partfun1, type, r1_partfun1: ($i * $i) > $o).
% 5.88/2.17  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.88/2.17  
% 5.88/2.19  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 5.88/2.19  tff(f_37, axiom, (?[A]: v1_xboole_0(A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', rc1_xboole_0)).
% 5.88/2.19  tff(f_35, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 5.88/2.19  tff(f_117, negated_conjecture, ~(![A, B, C]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r1_partfun1(C, D) => (((B = k1_xboole_0) & ~(A = k1_xboole_0)) | r2_hidden(D, k5_partfun1(A, B, C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t155_funct_2)).
% 5.88/2.19  tff(f_57, axiom, (![A, B]: (v1_xboole_0(A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => v1_xboole_0(C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc4_relset_1)).
% 5.88/2.19  tff(f_71, axiom, (![A, B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) => (v1_funct_1(C) & v1_partfun1(C, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc5_funct_2)).
% 5.88/2.19  tff(f_92, axiom, (![A, B, C]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: ((D = k5_partfun1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> (?[F]: ((((v1_funct_1(F) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & (F = E)) & v1_partfun1(F, A)) & r1_partfun1(C, F))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_partfun1)).
% 5.88/2.19  tff(f_43, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 5.88/2.19  tff(f_50, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_subset)).
% 5.88/2.19  tff(f_96, axiom, (![A]: (v1_partfun1(k6_partfun1(A), A) & m1_subset_1(k6_partfun1(A), k1_zfmisc_1(k2_zfmisc_1(A, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_partfun1)).
% 5.88/2.19  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.88/2.19  tff(c_8, plain, (v1_xboole_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_37])).
% 5.88/2.19  tff(c_103, plain, (![A_66]: (k1_xboole_0=A_66 | ~v1_xboole_0(A_66))), inference(cnfTransformation, [status(thm)], [f_35])).
% 5.88/2.19  tff(c_107, plain, (k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_8, c_103])).
% 5.88/2.19  tff(c_66, plain, (k1_xboole_0='#skF_7' | k1_xboole_0!='#skF_8'), inference(cnfTransformation, [status(thm)], [f_117])).
% 5.88/2.19  tff(c_86, plain, (k1_xboole_0!='#skF_8'), inference(splitLeft, [status(thm)], [c_66])).
% 5.88/2.19  tff(c_110, plain, ('#skF_2'!='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_107, c_86])).
% 5.88/2.19  tff(c_64, plain, (~r2_hidden('#skF_10', k5_partfun1('#skF_7', '#skF_8', '#skF_9'))), inference(cnfTransformation, [status(thm)], [f_117])).
% 5.88/2.19  tff(c_78, plain, (v1_funct_1('#skF_9')), inference(cnfTransformation, [status(thm)], [f_117])).
% 5.88/2.19  tff(c_68, plain, (r1_partfun1('#skF_9', '#skF_10')), inference(cnfTransformation, [status(thm)], [f_117])).
% 5.88/2.19  tff(c_76, plain, (m1_subset_1('#skF_9', k1_zfmisc_1(k2_zfmisc_1('#skF_7', '#skF_8')))), inference(cnfTransformation, [status(thm)], [f_117])).
% 5.88/2.19  tff(c_74, plain, (v1_funct_1('#skF_10')), inference(cnfTransformation, [status(thm)], [f_117])).
% 5.88/2.19  tff(c_226, plain, (![C_81, B_82, A_83]: (v1_xboole_0(C_81) | ~m1_subset_1(C_81, k1_zfmisc_1(k2_zfmisc_1(B_82, A_83))) | ~v1_xboole_0(A_83))), inference(cnfTransformation, [status(thm)], [f_57])).
% 5.88/2.19  tff(c_243, plain, (v1_xboole_0('#skF_9') | ~v1_xboole_0('#skF_8')), inference(resolution, [status(thm)], [c_76, c_226])).
% 5.88/2.19  tff(c_247, plain, (~v1_xboole_0('#skF_8')), inference(splitLeft, [status(thm)], [c_243])).
% 5.88/2.19  tff(c_72, plain, (v1_funct_2('#skF_10', '#skF_7', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_117])).
% 5.88/2.19  tff(c_70, plain, (m1_subset_1('#skF_10', k1_zfmisc_1(k2_zfmisc_1('#skF_7', '#skF_8')))), inference(cnfTransformation, [status(thm)], [f_117])).
% 5.88/2.19  tff(c_316, plain, (![C_89, A_90, B_91]: (v1_partfun1(C_89, A_90) | ~v1_funct_2(C_89, A_90, B_91) | ~v1_funct_1(C_89) | ~m1_subset_1(C_89, k1_zfmisc_1(k2_zfmisc_1(A_90, B_91))) | v1_xboole_0(B_91))), inference(cnfTransformation, [status(thm)], [f_71])).
% 5.88/2.19  tff(c_325, plain, (v1_partfun1('#skF_10', '#skF_7') | ~v1_funct_2('#skF_10', '#skF_7', '#skF_8') | ~v1_funct_1('#skF_10') | v1_xboole_0('#skF_8')), inference(resolution, [status(thm)], [c_70, c_316])).
% 5.88/2.19  tff(c_340, plain, (v1_partfun1('#skF_10', '#skF_7') | v1_xboole_0('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_325])).
% 5.88/2.19  tff(c_341, plain, (v1_partfun1('#skF_10', '#skF_7')), inference(negUnitSimplification, [status(thm)], [c_247, c_340])).
% 5.88/2.19  tff(c_2191, plain, (![F_295, A_296, B_297, C_298]: (r2_hidden(F_295, k5_partfun1(A_296, B_297, C_298)) | ~r1_partfun1(C_298, F_295) | ~v1_partfun1(F_295, A_296) | ~m1_subset_1(F_295, k1_zfmisc_1(k2_zfmisc_1(A_296, B_297))) | ~v1_funct_1(F_295) | ~m1_subset_1(C_298, k1_zfmisc_1(k2_zfmisc_1(A_296, B_297))) | ~v1_funct_1(C_298))), inference(cnfTransformation, [status(thm)], [f_92])).
% 5.88/2.19  tff(c_2201, plain, (![C_298]: (r2_hidden('#skF_10', k5_partfun1('#skF_7', '#skF_8', C_298)) | ~r1_partfun1(C_298, '#skF_10') | ~v1_partfun1('#skF_10', '#skF_7') | ~v1_funct_1('#skF_10') | ~m1_subset_1(C_298, k1_zfmisc_1(k2_zfmisc_1('#skF_7', '#skF_8'))) | ~v1_funct_1(C_298))), inference(resolution, [status(thm)], [c_70, c_2191])).
% 5.88/2.19  tff(c_2219, plain, (![C_299]: (r2_hidden('#skF_10', k5_partfun1('#skF_7', '#skF_8', C_299)) | ~r1_partfun1(C_299, '#skF_10') | ~m1_subset_1(C_299, k1_zfmisc_1(k2_zfmisc_1('#skF_7', '#skF_8'))) | ~v1_funct_1(C_299))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_341, c_2201])).
% 5.88/2.19  tff(c_2226, plain, (r2_hidden('#skF_10', k5_partfun1('#skF_7', '#skF_8', '#skF_9')) | ~r1_partfun1('#skF_9', '#skF_10') | ~v1_funct_1('#skF_9')), inference(resolution, [status(thm)], [c_76, c_2219])).
% 5.88/2.19  tff(c_2233, plain, (r2_hidden('#skF_10', k5_partfun1('#skF_7', '#skF_8', '#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_68, c_2226])).
% 5.88/2.19  tff(c_2235, plain, $false, inference(negUnitSimplification, [status(thm)], [c_64, c_2233])).
% 5.88/2.19  tff(c_2237, plain, (v1_xboole_0('#skF_8')), inference(splitRight, [status(thm)], [c_243])).
% 5.88/2.19  tff(c_6, plain, (![A_5]: (k1_xboole_0=A_5 | ~v1_xboole_0(A_5))), inference(cnfTransformation, [status(thm)], [f_35])).
% 5.88/2.19  tff(c_108, plain, (![A_5]: (A_5='#skF_2' | ~v1_xboole_0(A_5))), inference(demodulation, [status(thm), theory('equality')], [c_107, c_6])).
% 5.88/2.19  tff(c_2244, plain, ('#skF_2'='#skF_8'), inference(resolution, [status(thm)], [c_2237, c_108])).
% 5.88/2.19  tff(c_2248, plain, $false, inference(negUnitSimplification, [status(thm)], [c_110, c_2244])).
% 5.88/2.19  tff(c_2250, plain, (k1_xboole_0='#skF_8'), inference(splitRight, [status(thm)], [c_66])).
% 5.88/2.19  tff(c_2276, plain, (![A_301]: (A_301='#skF_8' | ~v1_xboole_0(A_301))), inference(demodulation, [status(thm), theory('equality')], [c_2250, c_6])).
% 5.88/2.19  tff(c_2280, plain, ('#skF_2'='#skF_8'), inference(resolution, [status(thm)], [c_8, c_2276])).
% 5.88/2.19  tff(c_2281, plain, (v1_xboole_0('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_2280, c_8])).
% 5.88/2.19  tff(c_2249, plain, (k1_xboole_0='#skF_7'), inference(splitRight, [status(thm)], [c_66])).
% 5.88/2.19  tff(c_2256, plain, ('#skF_7'='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_2250, c_2249])).
% 5.88/2.19  tff(c_14, plain, (![B_7]: (k2_zfmisc_1(k1_xboole_0, B_7)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_43])).
% 5.88/2.19  tff(c_2251, plain, (![B_7]: (k2_zfmisc_1('#skF_7', B_7)='#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_2249, c_2249, c_14])).
% 5.88/2.19  tff(c_2267, plain, (![B_7]: (k2_zfmisc_1('#skF_8', B_7)='#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_2256, c_2256, c_2251])).
% 5.88/2.19  tff(c_2315, plain, (m1_subset_1('#skF_10', k1_zfmisc_1('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_2267, c_2256, c_70])).
% 5.88/2.19  tff(c_2338, plain, (![C_310, B_311, A_312]: (~v1_xboole_0(C_310) | ~m1_subset_1(B_311, k1_zfmisc_1(C_310)) | ~r2_hidden(A_312, B_311))), inference(cnfTransformation, [status(thm)], [f_50])).
% 5.88/2.19  tff(c_2344, plain, (![A_312]: (~v1_xboole_0('#skF_8') | ~r2_hidden(A_312, '#skF_10'))), inference(resolution, [status(thm)], [c_2315, c_2338])).
% 5.88/2.19  tff(c_2357, plain, (![A_313]: (~r2_hidden(A_313, '#skF_10'))), inference(demodulation, [status(thm), theory('equality')], [c_2281, c_2344])).
% 5.88/2.19  tff(c_2362, plain, (v1_xboole_0('#skF_10')), inference(resolution, [status(thm)], [c_4, c_2357])).
% 5.88/2.19  tff(c_2275, plain, (![A_5]: (A_5='#skF_8' | ~v1_xboole_0(A_5))), inference(demodulation, [status(thm), theory('equality')], [c_2250, c_6])).
% 5.88/2.19  tff(c_2366, plain, ('#skF_10'='#skF_8'), inference(resolution, [status(thm)], [c_2362, c_2275])).
% 5.88/2.19  tff(c_2373, plain, (v1_funct_1('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_2366, c_74])).
% 5.88/2.19  tff(c_2369, plain, (m1_subset_1('#skF_8', k1_zfmisc_1('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_2366, c_2315])).
% 5.88/2.19  tff(c_2307, plain, (m1_subset_1('#skF_9', k1_zfmisc_1('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_2267, c_2256, c_76])).
% 5.88/2.19  tff(c_2346, plain, (![A_312]: (~v1_xboole_0('#skF_8') | ~r2_hidden(A_312, '#skF_9'))), inference(resolution, [status(thm)], [c_2307, c_2338])).
% 5.88/2.19  tff(c_2379, plain, (![A_314]: (~r2_hidden(A_314, '#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_2281, c_2346])).
% 5.88/2.19  tff(c_2384, plain, (v1_xboole_0('#skF_9')), inference(resolution, [status(thm)], [c_4, c_2379])).
% 5.88/2.19  tff(c_2401, plain, ('#skF_9'='#skF_8'), inference(resolution, [status(thm)], [c_2384, c_2275])).
% 5.88/2.19  tff(c_2372, plain, (r1_partfun1('#skF_9', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_2366, c_68])).
% 5.88/2.19  tff(c_2412, plain, (r1_partfun1('#skF_8', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_2401, c_2372])).
% 5.88/2.19  tff(c_12, plain, (![A_6]: (k2_zfmisc_1(A_6, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_43])).
% 5.88/2.19  tff(c_2291, plain, (![A_6]: (k2_zfmisc_1(A_6, '#skF_8')='#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_2250, c_2250, c_12])).
% 5.88/2.19  tff(c_2316, plain, (![A_307]: (m1_subset_1(k6_partfun1(A_307), k1_zfmisc_1(k2_zfmisc_1(A_307, A_307))))), inference(cnfTransformation, [status(thm)], [f_96])).
% 5.88/2.19  tff(c_2320, plain, (m1_subset_1(k6_partfun1('#skF_8'), k1_zfmisc_1('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_2291, c_2316])).
% 5.88/2.19  tff(c_2340, plain, (![A_312]: (~v1_xboole_0('#skF_8') | ~r2_hidden(A_312, k6_partfun1('#skF_8')))), inference(resolution, [status(thm)], [c_2320, c_2338])).
% 5.88/2.19  tff(c_2420, plain, (![A_319]: (~r2_hidden(A_319, k6_partfun1('#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_2281, c_2340])).
% 5.88/2.19  tff(c_2425, plain, (v1_xboole_0(k6_partfun1('#skF_8'))), inference(resolution, [status(thm)], [c_4, c_2420])).
% 5.88/2.19  tff(c_2429, plain, (k6_partfun1('#skF_8')='#skF_8'), inference(resolution, [status(thm)], [c_2425, c_2275])).
% 5.88/2.19  tff(c_60, plain, (![A_61]: (v1_partfun1(k6_partfun1(A_61), A_61))), inference(cnfTransformation, [status(thm)], [f_96])).
% 5.88/2.19  tff(c_62, plain, (![A_61]: (m1_subset_1(k6_partfun1(A_61), k1_zfmisc_1(k2_zfmisc_1(A_61, A_61))))), inference(cnfTransformation, [status(thm)], [f_96])).
% 5.88/2.19  tff(c_3502, plain, (![F_515, A_516, B_517, C_518]: (r2_hidden(F_515, k5_partfun1(A_516, B_517, C_518)) | ~r1_partfun1(C_518, F_515) | ~v1_partfun1(F_515, A_516) | ~m1_subset_1(F_515, k1_zfmisc_1(k2_zfmisc_1(A_516, B_517))) | ~v1_funct_1(F_515) | ~m1_subset_1(C_518, k1_zfmisc_1(k2_zfmisc_1(A_516, B_517))) | ~v1_funct_1(C_518))), inference(cnfTransformation, [status(thm)], [f_92])).
% 5.88/2.19  tff(c_3506, plain, (![A_61, C_518]: (r2_hidden(k6_partfun1(A_61), k5_partfun1(A_61, A_61, C_518)) | ~r1_partfun1(C_518, k6_partfun1(A_61)) | ~v1_partfun1(k6_partfun1(A_61), A_61) | ~v1_funct_1(k6_partfun1(A_61)) | ~m1_subset_1(C_518, k1_zfmisc_1(k2_zfmisc_1(A_61, A_61))) | ~v1_funct_1(C_518))), inference(resolution, [status(thm)], [c_62, c_3502])).
% 5.88/2.19  tff(c_3521, plain, (![A_524, C_525]: (r2_hidden(k6_partfun1(A_524), k5_partfun1(A_524, A_524, C_525)) | ~r1_partfun1(C_525, k6_partfun1(A_524)) | ~v1_funct_1(k6_partfun1(A_524)) | ~m1_subset_1(C_525, k1_zfmisc_1(k2_zfmisc_1(A_524, A_524))) | ~v1_funct_1(C_525))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_3506])).
% 5.88/2.19  tff(c_3535, plain, (![C_525]: (r2_hidden('#skF_8', k5_partfun1('#skF_8', '#skF_8', C_525)) | ~r1_partfun1(C_525, k6_partfun1('#skF_8')) | ~v1_funct_1(k6_partfun1('#skF_8')) | ~m1_subset_1(C_525, k1_zfmisc_1(k2_zfmisc_1('#skF_8', '#skF_8'))) | ~v1_funct_1(C_525))), inference(superposition, [status(thm), theory('equality')], [c_2429, c_3521])).
% 5.88/2.19  tff(c_3568, plain, (![C_527]: (r2_hidden('#skF_8', k5_partfun1('#skF_8', '#skF_8', C_527)) | ~r1_partfun1(C_527, '#skF_8') | ~m1_subset_1(C_527, k1_zfmisc_1('#skF_8')) | ~v1_funct_1(C_527))), inference(demodulation, [status(thm), theory('equality')], [c_2291, c_2373, c_2429, c_2429, c_3535])).
% 5.88/2.19  tff(c_2261, plain, (~r2_hidden('#skF_10', k5_partfun1('#skF_8', '#skF_8', '#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_2256, c_64])).
% 5.88/2.19  tff(c_2370, plain, (~r2_hidden('#skF_8', k5_partfun1('#skF_8', '#skF_8', '#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_2366, c_2261])).
% 5.88/2.19  tff(c_2464, plain, (~r2_hidden('#skF_8', k5_partfun1('#skF_8', '#skF_8', '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_2401, c_2370])).
% 5.88/2.19  tff(c_3573, plain, (~r1_partfun1('#skF_8', '#skF_8') | ~m1_subset_1('#skF_8', k1_zfmisc_1('#skF_8')) | ~v1_funct_1('#skF_8')), inference(resolution, [status(thm)], [c_3568, c_2464])).
% 5.88/2.19  tff(c_3582, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2373, c_2369, c_2412, c_3573])).
% 5.88/2.19  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.88/2.19  
% 5.88/2.19  Inference rules
% 5.88/2.19  ----------------------
% 5.88/2.19  #Ref     : 0
% 5.88/2.19  #Sup     : 787
% 5.88/2.19  #Fact    : 0
% 5.88/2.19  #Define  : 0
% 5.88/2.19  #Split   : 9
% 5.88/2.19  #Chain   : 0
% 5.88/2.19  #Close   : 0
% 5.88/2.19  
% 5.88/2.19  Ordering : KBO
% 5.88/2.19  
% 5.88/2.19  Simplification rules
% 5.88/2.19  ----------------------
% 5.88/2.19  #Subsume      : 153
% 5.88/2.19  #Demod        : 892
% 5.88/2.19  #Tautology    : 184
% 5.88/2.19  #SimpNegUnit  : 26
% 5.88/2.19  #BackRed      : 35
% 5.88/2.19  
% 5.88/2.19  #Partial instantiations: 0
% 5.88/2.19  #Strategies tried      : 1
% 5.88/2.19  
% 5.88/2.19  Timing (in seconds)
% 5.88/2.19  ----------------------
% 5.88/2.19  Preprocessing        : 0.36
% 5.88/2.19  Parsing              : 0.18
% 5.88/2.19  CNF conversion       : 0.03
% 5.88/2.19  Main loop            : 1.01
% 5.88/2.19  Inferencing          : 0.37
% 5.88/2.19  Reduction            : 0.34
% 5.88/2.19  Demodulation         : 0.24
% 5.88/2.19  BG Simplification    : 0.05
% 5.88/2.19  Subsumption          : 0.18
% 5.88/2.19  Abstraction          : 0.05
% 5.88/2.19  MUC search           : 0.00
% 5.88/2.19  Cooper               : 0.00
% 5.88/2.19  Total                : 1.41
% 5.88/2.19  Index Insertion      : 0.00
% 5.88/2.19  Index Deletion       : 0.00
% 5.88/2.19  Index Matching       : 0.00
% 5.88/2.19  BG Taut test         : 0.00
%------------------------------------------------------------------------------
