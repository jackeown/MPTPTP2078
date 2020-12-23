%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:16:40 EST 2020

% Result     : Theorem 7.43s
% Output     : CNFRefutation 7.43s
% Verified   : 
% Statistics : Number of formulae       :  141 ( 900 expanded)
%              Number of leaves         :   46 ( 303 expanded)
%              Depth                    :   20
%              Number of atoms          :  241 (2245 expanded)
%              Number of equality atoms :   29 ( 306 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_zfmisc_1 > k1_funct_2 > k1_funct_1 > #nlpp > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_11 > #skF_6 > #skF_9 > #skF_3 > #skF_10 > #skF_5 > #skF_7 > #skF_2 > #skF_8 > #skF_1 > #skF_12 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_11',type,(
    '#skF_11': $i )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': ( $i * $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff(v1_partfun1,type,(
    v1_partfun1: ( $i * $i ) > $o )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i * $i ) > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff(k6_partfun1,type,(
    k6_partfun1: $i > $i )).

tff(k1_funct_2,type,(
    k1_funct_2: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff('#skF_8',type,(
    '#skF_8': ( $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_12',type,(
    '#skF_12': $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_158,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r2_hidden(C,k1_funct_2(A,B))
       => ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t121_funct_2)).

tff(f_135,axiom,(
    ! [A,B,C] :
      ( C = k1_funct_2(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ? [E] :
              ( v1_relat_1(E)
              & v1_funct_1(E)
              & D = E
              & k1_relat_1(E) = A
              & r1_tarski(k2_relat_1(E),B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_funct_2)).

tff(f_38,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_95,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( ( r1_tarski(k1_relat_1(C),A)
          & r1_tarski(k2_relat_1(C),B) )
       => m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_relset_1)).

tff(f_74,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_149,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_funct_1(A)
        & v1_funct_2(A,k1_relat_1(A),k2_relat_1(A))
        & m1_subset_1(A,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A)))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_funct_2)).

tff(f_87,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(B,A)))
         => v1_xboole_0(C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc4_relset_1)).

tff(f_105,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( ( v1_funct_1(C)
          & v1_partfun1(C,A) )
       => ( v1_funct_1(C)
          & v1_funct_2(C,A,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_funct_2)).

tff(f_119,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => ( ( v1_funct_1(C)
              & v1_funct_2(C,A,B) )
           => ( v1_funct_1(C)
              & v1_partfun1(C,A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc5_funct_2)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_139,axiom,(
    ! [A] :
      ( v1_partfun1(k6_partfun1(A),A)
      & m1_subset_1(k6_partfun1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).

tff(f_42,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_49,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

tff(f_70,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( B = k2_relat_1(A)
        <=> ! [C] :
              ( r2_hidden(C,B)
            <=> ? [D] :
                  ( r2_hidden(D,k1_relat_1(A))
                  & C = k1_funct_1(A,D) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_funct_1)).

tff(c_108,plain,(
    r2_hidden('#skF_12',k1_funct_2('#skF_10','#skF_11')) ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_894,plain,(
    ! [A_299,B_300,D_301] :
      ( '#skF_9'(A_299,B_300,k1_funct_2(A_299,B_300),D_301) = D_301
      | ~ r2_hidden(D_301,k1_funct_2(A_299,B_300)) ) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_901,plain,(
    '#skF_9'('#skF_10','#skF_11',k1_funct_2('#skF_10','#skF_11'),'#skF_12') = '#skF_12' ),
    inference(resolution,[status(thm)],[c_108,c_894])).

tff(c_992,plain,(
    ! [A_324,B_325,D_326] :
      ( v1_relat_1('#skF_9'(A_324,B_325,k1_funct_2(A_324,B_325),D_326))
      | ~ r2_hidden(D_326,k1_funct_2(A_324,B_325)) ) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_995,plain,
    ( v1_relat_1('#skF_12')
    | ~ r2_hidden('#skF_12',k1_funct_2('#skF_10','#skF_11')) ),
    inference(superposition,[status(thm),theory(equality)],[c_901,c_992])).

tff(c_997,plain,(
    v1_relat_1('#skF_12') ),
    inference(demodulation,[status(thm),theory(equality)],[c_108,c_995])).

tff(c_12,plain,(
    ! [B_7] : r1_tarski(B_7,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_1002,plain,(
    ! [A_334,B_335,D_336] :
      ( k1_relat_1('#skF_9'(A_334,B_335,k1_funct_2(A_334,B_335),D_336)) = A_334
      | ~ r2_hidden(D_336,k1_funct_2(A_334,B_335)) ) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_1020,plain,
    ( k1_relat_1('#skF_12') = '#skF_10'
    | ~ r2_hidden('#skF_12',k1_funct_2('#skF_10','#skF_11')) ),
    inference(superposition,[status(thm),theory(equality)],[c_901,c_1002])).

tff(c_1024,plain,(
    k1_relat_1('#skF_12') = '#skF_10' ),
    inference(demodulation,[status(thm),theory(equality)],[c_108,c_1020])).

tff(c_1632,plain,(
    ! [A_402,B_403,D_404] :
      ( r1_tarski(k2_relat_1('#skF_9'(A_402,B_403,k1_funct_2(A_402,B_403),D_404)),B_403)
      | ~ r2_hidden(D_404,k1_funct_2(A_402,B_403)) ) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_1672,plain,
    ( r1_tarski(k2_relat_1('#skF_12'),'#skF_11')
    | ~ r2_hidden('#skF_12',k1_funct_2('#skF_10','#skF_11')) ),
    inference(superposition,[status(thm),theory(equality)],[c_901,c_1632])).

tff(c_1685,plain,(
    r1_tarski(k2_relat_1('#skF_12'),'#skF_11') ),
    inference(demodulation,[status(thm),theory(equality)],[c_108,c_1672])).

tff(c_2308,plain,(
    ! [C_421,A_422,B_423] :
      ( m1_subset_1(C_421,k1_zfmisc_1(k2_zfmisc_1(A_422,B_423)))
      | ~ r1_tarski(k2_relat_1(C_421),B_423)
      | ~ r1_tarski(k1_relat_1(C_421),A_422)
      | ~ v1_relat_1(C_421) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_106,plain,
    ( ~ m1_subset_1('#skF_12',k1_zfmisc_1(k2_zfmisc_1('#skF_10','#skF_11')))
    | ~ v1_funct_2('#skF_12','#skF_10','#skF_11')
    | ~ v1_funct_1('#skF_12') ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_135,plain,(
    ~ v1_funct_1('#skF_12') ),
    inference(splitLeft,[status(thm)],[c_106])).

tff(c_491,plain,(
    ! [A_202,B_203,D_204] :
      ( '#skF_9'(A_202,B_203,k1_funct_2(A_202,B_203),D_204) = D_204
      | ~ r2_hidden(D_204,k1_funct_2(A_202,B_203)) ) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_498,plain,(
    '#skF_9'('#skF_10','#skF_11',k1_funct_2('#skF_10','#skF_11'),'#skF_12') = '#skF_12' ),
    inference(resolution,[status(thm)],[c_108,c_491])).

tff(c_523,plain,(
    ! [A_210,B_211,D_212] :
      ( v1_funct_1('#skF_9'(A_210,B_211,k1_funct_2(A_210,B_211),D_212))
      | ~ r2_hidden(D_212,k1_funct_2(A_210,B_211)) ) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_526,plain,
    ( v1_funct_1('#skF_12')
    | ~ r2_hidden('#skF_12',k1_funct_2('#skF_10','#skF_11')) ),
    inference(superposition,[status(thm),theory(equality)],[c_498,c_523])).

tff(c_528,plain,(
    v1_funct_1('#skF_12') ),
    inference(demodulation,[status(thm),theory(equality)],[c_108,c_526])).

tff(c_530,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_135,c_528])).

tff(c_531,plain,
    ( ~ v1_funct_2('#skF_12','#skF_10','#skF_11')
    | ~ m1_subset_1('#skF_12',k1_zfmisc_1(k2_zfmisc_1('#skF_10','#skF_11'))) ),
    inference(splitRight,[status(thm)],[c_106])).

tff(c_545,plain,(
    ~ m1_subset_1('#skF_12',k1_zfmisc_1(k2_zfmisc_1('#skF_10','#skF_11'))) ),
    inference(splitLeft,[status(thm)],[c_531])).

tff(c_2325,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_12'),'#skF_11')
    | ~ r1_tarski(k1_relat_1('#skF_12'),'#skF_10')
    | ~ v1_relat_1('#skF_12') ),
    inference(resolution,[status(thm)],[c_2308,c_545])).

tff(c_2343,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_997,c_12,c_1024,c_1685,c_2325])).

tff(c_2345,plain,(
    m1_subset_1('#skF_12',k1_zfmisc_1(k2_zfmisc_1('#skF_10','#skF_11'))) ),
    inference(splitRight,[status(thm)],[c_531])).

tff(c_42,plain,(
    ! [C_57,A_55,B_56] :
      ( v1_relat_1(C_57)
      | ~ m1_subset_1(C_57,k1_zfmisc_1(k2_zfmisc_1(A_55,B_56))) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_2352,plain,(
    v1_relat_1('#skF_12') ),
    inference(resolution,[status(thm)],[c_2345,c_42])).

tff(c_532,plain,(
    v1_funct_1('#skF_12') ),
    inference(splitRight,[status(thm)],[c_106])).

tff(c_2712,plain,(
    ! [A_505,B_506,D_507] :
      ( '#skF_9'(A_505,B_506,k1_funct_2(A_505,B_506),D_507) = D_507
      | ~ r2_hidden(D_507,k1_funct_2(A_505,B_506)) ) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_2719,plain,(
    '#skF_9'('#skF_10','#skF_11',k1_funct_2('#skF_10','#skF_11'),'#skF_12') = '#skF_12' ),
    inference(resolution,[status(thm)],[c_108,c_2712])).

tff(c_2799,plain,(
    ! [A_523,B_524,D_525] :
      ( k1_relat_1('#skF_9'(A_523,B_524,k1_funct_2(A_523,B_524),D_525)) = A_523
      | ~ r2_hidden(D_525,k1_funct_2(A_523,B_524)) ) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_2817,plain,
    ( k1_relat_1('#skF_12') = '#skF_10'
    | ~ r2_hidden('#skF_12',k1_funct_2('#skF_10','#skF_11')) ),
    inference(superposition,[status(thm),theory(equality)],[c_2719,c_2799])).

tff(c_2821,plain,(
    k1_relat_1('#skF_12') = '#skF_10' ),
    inference(demodulation,[status(thm),theory(equality)],[c_108,c_2817])).

tff(c_100,plain,(
    ! [A_96] :
      ( m1_subset_1(A_96,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_96),k2_relat_1(A_96))))
      | ~ v1_funct_1(A_96)
      | ~ v1_relat_1(A_96) ) ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_2828,plain,
    ( m1_subset_1('#skF_12',k1_zfmisc_1(k2_zfmisc_1('#skF_10',k2_relat_1('#skF_12'))))
    | ~ v1_funct_1('#skF_12')
    | ~ v1_relat_1('#skF_12') ),
    inference(superposition,[status(thm),theory(equality)],[c_2821,c_100])).

tff(c_2837,plain,(
    m1_subset_1('#skF_12',k1_zfmisc_1(k2_zfmisc_1('#skF_10',k2_relat_1('#skF_12')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2352,c_532,c_2828])).

tff(c_48,plain,(
    ! [C_64,B_62,A_61] :
      ( v1_xboole_0(C_64)
      | ~ m1_subset_1(C_64,k1_zfmisc_1(k2_zfmisc_1(B_62,A_61)))
      | ~ v1_xboole_0(A_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_2858,plain,
    ( v1_xboole_0('#skF_12')
    | ~ v1_xboole_0(k2_relat_1('#skF_12')) ),
    inference(resolution,[status(thm)],[c_2837,c_48])).

tff(c_2866,plain,(
    ~ v1_xboole_0(k2_relat_1('#skF_12')) ),
    inference(splitLeft,[status(thm)],[c_2858])).

tff(c_2344,plain,(
    ~ v1_funct_2('#skF_12','#skF_10','#skF_11') ),
    inference(splitRight,[status(thm)],[c_531])).

tff(c_3023,plain,(
    ! [C_551,A_552,B_553] :
      ( v1_funct_2(C_551,A_552,B_553)
      | ~ v1_partfun1(C_551,A_552)
      | ~ v1_funct_1(C_551)
      | ~ m1_subset_1(C_551,k1_zfmisc_1(k2_zfmisc_1(A_552,B_553))) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_3032,plain,
    ( v1_funct_2('#skF_12','#skF_10','#skF_11')
    | ~ v1_partfun1('#skF_12','#skF_10')
    | ~ v1_funct_1('#skF_12') ),
    inference(resolution,[status(thm)],[c_2345,c_3023])).

tff(c_3046,plain,
    ( v1_funct_2('#skF_12','#skF_10','#skF_11')
    | ~ v1_partfun1('#skF_12','#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_532,c_3032])).

tff(c_3047,plain,(
    ~ v1_partfun1('#skF_12','#skF_10') ),
    inference(negUnitSimplification,[status(thm)],[c_2344,c_3046])).

tff(c_102,plain,(
    ! [A_96] :
      ( v1_funct_2(A_96,k1_relat_1(A_96),k2_relat_1(A_96))
      | ~ v1_funct_1(A_96)
      | ~ v1_relat_1(A_96) ) ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_2831,plain,
    ( v1_funct_2('#skF_12','#skF_10',k2_relat_1('#skF_12'))
    | ~ v1_funct_1('#skF_12')
    | ~ v1_relat_1('#skF_12') ),
    inference(superposition,[status(thm),theory(equality)],[c_2821,c_102])).

tff(c_2839,plain,(
    v1_funct_2('#skF_12','#skF_10',k2_relat_1('#skF_12')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2352,c_532,c_2831])).

tff(c_6851,plain,(
    ! [C_823,A_824,B_825] :
      ( v1_partfun1(C_823,A_824)
      | ~ v1_funct_2(C_823,A_824,B_825)
      | ~ v1_funct_1(C_823)
      | ~ m1_subset_1(C_823,k1_zfmisc_1(k2_zfmisc_1(A_824,B_825)))
      | v1_xboole_0(B_825) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_6860,plain,
    ( v1_partfun1('#skF_12','#skF_10')
    | ~ v1_funct_2('#skF_12','#skF_10',k2_relat_1('#skF_12'))
    | ~ v1_funct_1('#skF_12')
    | v1_xboole_0(k2_relat_1('#skF_12')) ),
    inference(resolution,[status(thm)],[c_2837,c_6851])).

tff(c_6877,plain,
    ( v1_partfun1('#skF_12','#skF_10')
    | v1_xboole_0(k2_relat_1('#skF_12')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_532,c_2839,c_6860])).

tff(c_6879,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2866,c_3047,c_6877])).

tff(c_6880,plain,(
    v1_xboole_0('#skF_12') ),
    inference(splitRight,[status(thm)],[c_2858])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_98,plain,(
    ! [A_95] : m1_subset_1(k6_partfun1(A_95),k1_zfmisc_1(k2_zfmisc_1(A_95,A_95))) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_2595,plain,(
    ! [C_481,B_482,A_483] :
      ( v1_xboole_0(C_481)
      | ~ m1_subset_1(C_481,k1_zfmisc_1(k2_zfmisc_1(B_482,A_483)))
      | ~ v1_xboole_0(A_483) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_2610,plain,(
    ! [A_484] :
      ( v1_xboole_0(k6_partfun1(A_484))
      | ~ v1_xboole_0(A_484) ) ),
    inference(resolution,[status(thm)],[c_98,c_2595])).

tff(c_16,plain,(
    ! [A_8,B_9] :
      ( m1_subset_1(A_8,k1_zfmisc_1(B_9))
      | ~ r1_tarski(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_2387,plain,(
    ! [C_433,B_434,A_435] :
      ( ~ v1_xboole_0(C_433)
      | ~ m1_subset_1(B_434,k1_zfmisc_1(C_433))
      | ~ r2_hidden(A_435,B_434) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_2398,plain,(
    ! [B_436,A_437,A_438] :
      ( ~ v1_xboole_0(B_436)
      | ~ r2_hidden(A_437,A_438)
      | ~ r1_tarski(A_438,B_436) ) ),
    inference(resolution,[status(thm)],[c_16,c_2387])).

tff(c_2412,plain,(
    ! [B_442,A_443,B_444] :
      ( ~ v1_xboole_0(B_442)
      | ~ r1_tarski(A_443,B_442)
      | r1_tarski(A_443,B_444) ) ),
    inference(resolution,[status(thm)],[c_6,c_2398])).

tff(c_2421,plain,(
    ! [B_7,B_444] :
      ( ~ v1_xboole_0(B_7)
      | r1_tarski(B_7,B_444) ) ),
    inference(resolution,[status(thm)],[c_12,c_2412])).

tff(c_2422,plain,(
    ! [B_445,B_446] :
      ( ~ v1_xboole_0(B_445)
      | r1_tarski(B_445,B_446) ) ),
    inference(resolution,[status(thm)],[c_12,c_2412])).

tff(c_8,plain,(
    ! [B_7,A_6] :
      ( B_7 = A_6
      | ~ r1_tarski(B_7,A_6)
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_2461,plain,(
    ! [B_451,B_450] :
      ( B_451 = B_450
      | ~ r1_tarski(B_450,B_451)
      | ~ v1_xboole_0(B_451) ) ),
    inference(resolution,[status(thm)],[c_2422,c_8])).

tff(c_2478,plain,(
    ! [B_7,B_444] :
      ( B_7 = B_444
      | ~ v1_xboole_0(B_444)
      | ~ v1_xboole_0(B_7) ) ),
    inference(resolution,[status(thm)],[c_2421,c_2461])).

tff(c_2616,plain,(
    ! [A_484,B_7] :
      ( k6_partfun1(A_484) = B_7
      | ~ v1_xboole_0(B_7)
      | ~ v1_xboole_0(A_484) ) ),
    inference(resolution,[status(thm)],[c_2610,c_2478])).

tff(c_7098,plain,(
    ! [A_833] :
      ( k6_partfun1(A_833) = '#skF_12'
      | ~ v1_xboole_0(A_833) ) ),
    inference(resolution,[status(thm)],[c_6880,c_2616])).

tff(c_7108,plain,(
    k6_partfun1('#skF_12') = '#skF_12' ),
    inference(resolution,[status(thm)],[c_6880,c_7098])).

tff(c_2655,plain,(
    ! [A_498,A_499,B_500] :
      ( v1_xboole_0(A_498)
      | ~ v1_xboole_0(A_499)
      | ~ r1_tarski(A_498,k2_zfmisc_1(B_500,A_499)) ) ),
    inference(resolution,[status(thm)],[c_16,c_2595])).

tff(c_2679,plain,(
    ! [B_501,A_502] :
      ( v1_xboole_0(k2_zfmisc_1(B_501,A_502))
      | ~ v1_xboole_0(A_502) ) ),
    inference(resolution,[status(thm)],[c_12,c_2655])).

tff(c_2396,plain,(
    ! [A_95,A_435] :
      ( ~ v1_xboole_0(k2_zfmisc_1(A_95,A_95))
      | ~ r2_hidden(A_435,k6_partfun1(A_95)) ) ),
    inference(resolution,[status(thm)],[c_98,c_2387])).

tff(c_2704,plain,(
    ! [A_435,A_502] :
      ( ~ r2_hidden(A_435,k6_partfun1(A_502))
      | ~ v1_xboole_0(A_502) ) ),
    inference(resolution,[status(thm)],[c_2679,c_2396])).

tff(c_7126,plain,(
    ! [A_435] :
      ( ~ r2_hidden(A_435,'#skF_12')
      | ~ v1_xboole_0('#skF_12') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_7108,c_2704])).

tff(c_7158,plain,(
    ! [A_435] : ~ r2_hidden(A_435,'#skF_12') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6880,c_7126])).

tff(c_6881,plain,(
    v1_xboole_0(k2_relat_1('#skF_12')) ),
    inference(splitRight,[status(thm)],[c_2858])).

tff(c_6960,plain,(
    ! [B_827] :
      ( B_827 = '#skF_12'
      | ~ v1_xboole_0(B_827) ) ),
    inference(resolution,[status(thm)],[c_6880,c_2478])).

tff(c_6973,plain,(
    k2_relat_1('#skF_12') = '#skF_12' ),
    inference(resolution,[status(thm)],[c_6881,c_6960])).

tff(c_7173,plain,(
    ! [A_835,D_836] :
      ( r2_hidden(k1_funct_1(A_835,D_836),k2_relat_1(A_835))
      | ~ r2_hidden(D_836,k1_relat_1(A_835))
      | ~ v1_funct_1(A_835)
      | ~ v1_relat_1(A_835) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_7180,plain,(
    ! [D_836] :
      ( r2_hidden(k1_funct_1('#skF_12',D_836),'#skF_12')
      | ~ r2_hidden(D_836,k1_relat_1('#skF_12'))
      | ~ v1_funct_1('#skF_12')
      | ~ v1_relat_1('#skF_12') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6973,c_7173])).

tff(c_7184,plain,(
    ! [D_836] :
      ( r2_hidden(k1_funct_1('#skF_12',D_836),'#skF_12')
      | ~ r2_hidden(D_836,'#skF_10') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2352,c_532,c_2821,c_7180])).

tff(c_7186,plain,(
    ! [D_837] : ~ r2_hidden(D_837,'#skF_10') ),
    inference(negUnitSimplification,[status(thm)],[c_7158,c_7184])).

tff(c_7192,plain,(
    ! [B_838] : r1_tarski('#skF_10',B_838) ),
    inference(resolution,[status(thm)],[c_6,c_7186])).

tff(c_2442,plain,(
    ! [B_446,B_445] :
      ( B_446 = B_445
      | ~ r1_tarski(B_446,B_445)
      | ~ v1_xboole_0(B_445) ) ),
    inference(resolution,[status(thm)],[c_2422,c_8])).

tff(c_7260,plain,(
    ! [B_841] :
      ( B_841 = '#skF_10'
      | ~ v1_xboole_0(B_841) ) ),
    inference(resolution,[status(thm)],[c_7192,c_2442])).

tff(c_7270,plain,(
    '#skF_10' = '#skF_12' ),
    inference(resolution,[status(thm)],[c_6880,c_7260])).

tff(c_7290,plain,(
    ~ v1_funct_2('#skF_12','#skF_12','#skF_11') ),
    inference(demodulation,[status(thm),theory(equality)],[c_7270,c_2344])).

tff(c_96,plain,(
    ! [A_95] : v1_partfun1(k6_partfun1(A_95),A_95) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_7146,plain,(
    v1_partfun1('#skF_12','#skF_12') ),
    inference(superposition,[status(thm),theory(equality)],[c_7108,c_96])).

tff(c_7289,plain,(
    m1_subset_1('#skF_12',k1_zfmisc_1(k2_zfmisc_1('#skF_12','#skF_11'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7270,c_2345])).

tff(c_52,plain,(
    ! [C_70,A_68,B_69] :
      ( v1_funct_2(C_70,A_68,B_69)
      | ~ v1_partfun1(C_70,A_68)
      | ~ v1_funct_1(C_70)
      | ~ m1_subset_1(C_70,k1_zfmisc_1(k2_zfmisc_1(A_68,B_69))) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_7754,plain,
    ( v1_funct_2('#skF_12','#skF_12','#skF_11')
    | ~ v1_partfun1('#skF_12','#skF_12')
    | ~ v1_funct_1('#skF_12') ),
    inference(resolution,[status(thm)],[c_7289,c_52])).

tff(c_7774,plain,(
    v1_funct_2('#skF_12','#skF_12','#skF_11') ),
    inference(demodulation,[status(thm),theory(equality)],[c_532,c_7146,c_7754])).

tff(c_7776,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_7290,c_7774])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 19:14:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.43/2.55  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.43/2.56  
% 7.43/2.56  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.43/2.56  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_zfmisc_1 > k1_funct_2 > k1_funct_1 > #nlpp > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_11 > #skF_6 > #skF_9 > #skF_3 > #skF_10 > #skF_5 > #skF_7 > #skF_2 > #skF_8 > #skF_1 > #skF_12 > #skF_4
% 7.43/2.56  
% 7.43/2.56  %Foreground sorts:
% 7.43/2.56  
% 7.43/2.56  
% 7.43/2.56  %Background operators:
% 7.43/2.56  
% 7.43/2.56  
% 7.43/2.56  %Foreground operators:
% 7.43/2.56  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 7.43/2.56  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.43/2.56  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 7.43/2.56  tff('#skF_11', type, '#skF_11': $i).
% 7.43/2.56  tff('#skF_6', type, '#skF_6': ($i * $i * $i) > $i).
% 7.43/2.56  tff('#skF_9', type, '#skF_9': ($i * $i * $i * $i) > $i).
% 7.43/2.56  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 7.43/2.56  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.43/2.56  tff('#skF_10', type, '#skF_10': $i).
% 7.43/2.56  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 7.43/2.56  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 7.43/2.56  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 7.43/2.56  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 7.43/2.56  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 7.43/2.56  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 7.43/2.56  tff('#skF_7', type, '#skF_7': ($i * $i * $i) > $i).
% 7.43/2.56  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 7.43/2.56  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 7.43/2.56  tff(k1_funct_2, type, k1_funct_2: ($i * $i) > $i).
% 7.43/2.56  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.43/2.56  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 7.43/2.56  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 7.43/2.56  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.43/2.56  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 7.43/2.56  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 7.43/2.56  tff('#skF_8', type, '#skF_8': ($i * $i * $i) > $i).
% 7.43/2.56  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 7.43/2.56  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 7.43/2.56  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 7.43/2.56  tff('#skF_12', type, '#skF_12': $i).
% 7.43/2.56  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 7.43/2.56  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 7.43/2.56  
% 7.43/2.58  tff(f_158, negated_conjecture, ~(![A, B, C]: (r2_hidden(C, k1_funct_2(A, B)) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t121_funct_2)).
% 7.43/2.58  tff(f_135, axiom, (![A, B, C]: ((C = k1_funct_2(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (?[E]: ((((v1_relat_1(E) & v1_funct_1(E)) & (D = E)) & (k1_relat_1(E) = A)) & r1_tarski(k2_relat_1(E), B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_funct_2)).
% 7.43/2.58  tff(f_38, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 7.43/2.58  tff(f_95, axiom, (![A, B, C]: (v1_relat_1(C) => ((r1_tarski(k1_relat_1(C), A) & r1_tarski(k2_relat_1(C), B)) => m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_relset_1)).
% 7.43/2.58  tff(f_74, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 7.43/2.58  tff(f_149, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => ((v1_funct_1(A) & v1_funct_2(A, k1_relat_1(A), k2_relat_1(A))) & m1_subset_1(A, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_funct_2)).
% 7.43/2.58  tff(f_87, axiom, (![A, B]: (v1_xboole_0(A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => v1_xboole_0(C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc4_relset_1)).
% 7.43/2.58  tff(f_105, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v1_partfun1(C, A)) => (v1_funct_1(C) & v1_funct_2(C, A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_funct_2)).
% 7.43/2.58  tff(f_119, axiom, (![A, B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) => (v1_funct_1(C) & v1_partfun1(C, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc5_funct_2)).
% 7.43/2.58  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 7.43/2.58  tff(f_139, axiom, (![A]: (v1_partfun1(k6_partfun1(A), A) & m1_subset_1(k6_partfun1(A), k1_zfmisc_1(k2_zfmisc_1(A, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_partfun1)).
% 7.43/2.58  tff(f_42, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 7.43/2.58  tff(f_49, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_subset)).
% 7.43/2.58  tff(f_70, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((B = k2_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: (r2_hidden(D, k1_relat_1(A)) & (C = k1_funct_1(A, D)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_funct_1)).
% 7.43/2.58  tff(c_108, plain, (r2_hidden('#skF_12', k1_funct_2('#skF_10', '#skF_11'))), inference(cnfTransformation, [status(thm)], [f_158])).
% 7.43/2.58  tff(c_894, plain, (![A_299, B_300, D_301]: ('#skF_9'(A_299, B_300, k1_funct_2(A_299, B_300), D_301)=D_301 | ~r2_hidden(D_301, k1_funct_2(A_299, B_300)))), inference(cnfTransformation, [status(thm)], [f_135])).
% 7.43/2.58  tff(c_901, plain, ('#skF_9'('#skF_10', '#skF_11', k1_funct_2('#skF_10', '#skF_11'), '#skF_12')='#skF_12'), inference(resolution, [status(thm)], [c_108, c_894])).
% 7.43/2.58  tff(c_992, plain, (![A_324, B_325, D_326]: (v1_relat_1('#skF_9'(A_324, B_325, k1_funct_2(A_324, B_325), D_326)) | ~r2_hidden(D_326, k1_funct_2(A_324, B_325)))), inference(cnfTransformation, [status(thm)], [f_135])).
% 7.43/2.58  tff(c_995, plain, (v1_relat_1('#skF_12') | ~r2_hidden('#skF_12', k1_funct_2('#skF_10', '#skF_11'))), inference(superposition, [status(thm), theory('equality')], [c_901, c_992])).
% 7.43/2.58  tff(c_997, plain, (v1_relat_1('#skF_12')), inference(demodulation, [status(thm), theory('equality')], [c_108, c_995])).
% 7.43/2.58  tff(c_12, plain, (![B_7]: (r1_tarski(B_7, B_7))), inference(cnfTransformation, [status(thm)], [f_38])).
% 7.43/2.58  tff(c_1002, plain, (![A_334, B_335, D_336]: (k1_relat_1('#skF_9'(A_334, B_335, k1_funct_2(A_334, B_335), D_336))=A_334 | ~r2_hidden(D_336, k1_funct_2(A_334, B_335)))), inference(cnfTransformation, [status(thm)], [f_135])).
% 7.43/2.58  tff(c_1020, plain, (k1_relat_1('#skF_12')='#skF_10' | ~r2_hidden('#skF_12', k1_funct_2('#skF_10', '#skF_11'))), inference(superposition, [status(thm), theory('equality')], [c_901, c_1002])).
% 7.43/2.58  tff(c_1024, plain, (k1_relat_1('#skF_12')='#skF_10'), inference(demodulation, [status(thm), theory('equality')], [c_108, c_1020])).
% 7.43/2.58  tff(c_1632, plain, (![A_402, B_403, D_404]: (r1_tarski(k2_relat_1('#skF_9'(A_402, B_403, k1_funct_2(A_402, B_403), D_404)), B_403) | ~r2_hidden(D_404, k1_funct_2(A_402, B_403)))), inference(cnfTransformation, [status(thm)], [f_135])).
% 7.43/2.58  tff(c_1672, plain, (r1_tarski(k2_relat_1('#skF_12'), '#skF_11') | ~r2_hidden('#skF_12', k1_funct_2('#skF_10', '#skF_11'))), inference(superposition, [status(thm), theory('equality')], [c_901, c_1632])).
% 7.43/2.58  tff(c_1685, plain, (r1_tarski(k2_relat_1('#skF_12'), '#skF_11')), inference(demodulation, [status(thm), theory('equality')], [c_108, c_1672])).
% 7.43/2.58  tff(c_2308, plain, (![C_421, A_422, B_423]: (m1_subset_1(C_421, k1_zfmisc_1(k2_zfmisc_1(A_422, B_423))) | ~r1_tarski(k2_relat_1(C_421), B_423) | ~r1_tarski(k1_relat_1(C_421), A_422) | ~v1_relat_1(C_421))), inference(cnfTransformation, [status(thm)], [f_95])).
% 7.43/2.58  tff(c_106, plain, (~m1_subset_1('#skF_12', k1_zfmisc_1(k2_zfmisc_1('#skF_10', '#skF_11'))) | ~v1_funct_2('#skF_12', '#skF_10', '#skF_11') | ~v1_funct_1('#skF_12')), inference(cnfTransformation, [status(thm)], [f_158])).
% 7.43/2.58  tff(c_135, plain, (~v1_funct_1('#skF_12')), inference(splitLeft, [status(thm)], [c_106])).
% 7.43/2.58  tff(c_491, plain, (![A_202, B_203, D_204]: ('#skF_9'(A_202, B_203, k1_funct_2(A_202, B_203), D_204)=D_204 | ~r2_hidden(D_204, k1_funct_2(A_202, B_203)))), inference(cnfTransformation, [status(thm)], [f_135])).
% 7.43/2.58  tff(c_498, plain, ('#skF_9'('#skF_10', '#skF_11', k1_funct_2('#skF_10', '#skF_11'), '#skF_12')='#skF_12'), inference(resolution, [status(thm)], [c_108, c_491])).
% 7.43/2.58  tff(c_523, plain, (![A_210, B_211, D_212]: (v1_funct_1('#skF_9'(A_210, B_211, k1_funct_2(A_210, B_211), D_212)) | ~r2_hidden(D_212, k1_funct_2(A_210, B_211)))), inference(cnfTransformation, [status(thm)], [f_135])).
% 7.43/2.58  tff(c_526, plain, (v1_funct_1('#skF_12') | ~r2_hidden('#skF_12', k1_funct_2('#skF_10', '#skF_11'))), inference(superposition, [status(thm), theory('equality')], [c_498, c_523])).
% 7.43/2.58  tff(c_528, plain, (v1_funct_1('#skF_12')), inference(demodulation, [status(thm), theory('equality')], [c_108, c_526])).
% 7.43/2.58  tff(c_530, plain, $false, inference(negUnitSimplification, [status(thm)], [c_135, c_528])).
% 7.43/2.58  tff(c_531, plain, (~v1_funct_2('#skF_12', '#skF_10', '#skF_11') | ~m1_subset_1('#skF_12', k1_zfmisc_1(k2_zfmisc_1('#skF_10', '#skF_11')))), inference(splitRight, [status(thm)], [c_106])).
% 7.43/2.58  tff(c_545, plain, (~m1_subset_1('#skF_12', k1_zfmisc_1(k2_zfmisc_1('#skF_10', '#skF_11')))), inference(splitLeft, [status(thm)], [c_531])).
% 7.43/2.58  tff(c_2325, plain, (~r1_tarski(k2_relat_1('#skF_12'), '#skF_11') | ~r1_tarski(k1_relat_1('#skF_12'), '#skF_10') | ~v1_relat_1('#skF_12')), inference(resolution, [status(thm)], [c_2308, c_545])).
% 7.43/2.58  tff(c_2343, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_997, c_12, c_1024, c_1685, c_2325])).
% 7.43/2.58  tff(c_2345, plain, (m1_subset_1('#skF_12', k1_zfmisc_1(k2_zfmisc_1('#skF_10', '#skF_11')))), inference(splitRight, [status(thm)], [c_531])).
% 7.43/2.58  tff(c_42, plain, (![C_57, A_55, B_56]: (v1_relat_1(C_57) | ~m1_subset_1(C_57, k1_zfmisc_1(k2_zfmisc_1(A_55, B_56))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 7.43/2.58  tff(c_2352, plain, (v1_relat_1('#skF_12')), inference(resolution, [status(thm)], [c_2345, c_42])).
% 7.43/2.58  tff(c_532, plain, (v1_funct_1('#skF_12')), inference(splitRight, [status(thm)], [c_106])).
% 7.43/2.58  tff(c_2712, plain, (![A_505, B_506, D_507]: ('#skF_9'(A_505, B_506, k1_funct_2(A_505, B_506), D_507)=D_507 | ~r2_hidden(D_507, k1_funct_2(A_505, B_506)))), inference(cnfTransformation, [status(thm)], [f_135])).
% 7.43/2.58  tff(c_2719, plain, ('#skF_9'('#skF_10', '#skF_11', k1_funct_2('#skF_10', '#skF_11'), '#skF_12')='#skF_12'), inference(resolution, [status(thm)], [c_108, c_2712])).
% 7.43/2.58  tff(c_2799, plain, (![A_523, B_524, D_525]: (k1_relat_1('#skF_9'(A_523, B_524, k1_funct_2(A_523, B_524), D_525))=A_523 | ~r2_hidden(D_525, k1_funct_2(A_523, B_524)))), inference(cnfTransformation, [status(thm)], [f_135])).
% 7.43/2.58  tff(c_2817, plain, (k1_relat_1('#skF_12')='#skF_10' | ~r2_hidden('#skF_12', k1_funct_2('#skF_10', '#skF_11'))), inference(superposition, [status(thm), theory('equality')], [c_2719, c_2799])).
% 7.43/2.58  tff(c_2821, plain, (k1_relat_1('#skF_12')='#skF_10'), inference(demodulation, [status(thm), theory('equality')], [c_108, c_2817])).
% 7.43/2.58  tff(c_100, plain, (![A_96]: (m1_subset_1(A_96, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_96), k2_relat_1(A_96)))) | ~v1_funct_1(A_96) | ~v1_relat_1(A_96))), inference(cnfTransformation, [status(thm)], [f_149])).
% 7.43/2.58  tff(c_2828, plain, (m1_subset_1('#skF_12', k1_zfmisc_1(k2_zfmisc_1('#skF_10', k2_relat_1('#skF_12')))) | ~v1_funct_1('#skF_12') | ~v1_relat_1('#skF_12')), inference(superposition, [status(thm), theory('equality')], [c_2821, c_100])).
% 7.43/2.58  tff(c_2837, plain, (m1_subset_1('#skF_12', k1_zfmisc_1(k2_zfmisc_1('#skF_10', k2_relat_1('#skF_12'))))), inference(demodulation, [status(thm), theory('equality')], [c_2352, c_532, c_2828])).
% 7.43/2.58  tff(c_48, plain, (![C_64, B_62, A_61]: (v1_xboole_0(C_64) | ~m1_subset_1(C_64, k1_zfmisc_1(k2_zfmisc_1(B_62, A_61))) | ~v1_xboole_0(A_61))), inference(cnfTransformation, [status(thm)], [f_87])).
% 7.43/2.58  tff(c_2858, plain, (v1_xboole_0('#skF_12') | ~v1_xboole_0(k2_relat_1('#skF_12'))), inference(resolution, [status(thm)], [c_2837, c_48])).
% 7.43/2.58  tff(c_2866, plain, (~v1_xboole_0(k2_relat_1('#skF_12'))), inference(splitLeft, [status(thm)], [c_2858])).
% 7.43/2.58  tff(c_2344, plain, (~v1_funct_2('#skF_12', '#skF_10', '#skF_11')), inference(splitRight, [status(thm)], [c_531])).
% 7.43/2.58  tff(c_3023, plain, (![C_551, A_552, B_553]: (v1_funct_2(C_551, A_552, B_553) | ~v1_partfun1(C_551, A_552) | ~v1_funct_1(C_551) | ~m1_subset_1(C_551, k1_zfmisc_1(k2_zfmisc_1(A_552, B_553))))), inference(cnfTransformation, [status(thm)], [f_105])).
% 7.43/2.58  tff(c_3032, plain, (v1_funct_2('#skF_12', '#skF_10', '#skF_11') | ~v1_partfun1('#skF_12', '#skF_10') | ~v1_funct_1('#skF_12')), inference(resolution, [status(thm)], [c_2345, c_3023])).
% 7.43/2.58  tff(c_3046, plain, (v1_funct_2('#skF_12', '#skF_10', '#skF_11') | ~v1_partfun1('#skF_12', '#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_532, c_3032])).
% 7.43/2.58  tff(c_3047, plain, (~v1_partfun1('#skF_12', '#skF_10')), inference(negUnitSimplification, [status(thm)], [c_2344, c_3046])).
% 7.43/2.58  tff(c_102, plain, (![A_96]: (v1_funct_2(A_96, k1_relat_1(A_96), k2_relat_1(A_96)) | ~v1_funct_1(A_96) | ~v1_relat_1(A_96))), inference(cnfTransformation, [status(thm)], [f_149])).
% 7.43/2.58  tff(c_2831, plain, (v1_funct_2('#skF_12', '#skF_10', k2_relat_1('#skF_12')) | ~v1_funct_1('#skF_12') | ~v1_relat_1('#skF_12')), inference(superposition, [status(thm), theory('equality')], [c_2821, c_102])).
% 7.43/2.58  tff(c_2839, plain, (v1_funct_2('#skF_12', '#skF_10', k2_relat_1('#skF_12'))), inference(demodulation, [status(thm), theory('equality')], [c_2352, c_532, c_2831])).
% 7.43/2.58  tff(c_6851, plain, (![C_823, A_824, B_825]: (v1_partfun1(C_823, A_824) | ~v1_funct_2(C_823, A_824, B_825) | ~v1_funct_1(C_823) | ~m1_subset_1(C_823, k1_zfmisc_1(k2_zfmisc_1(A_824, B_825))) | v1_xboole_0(B_825))), inference(cnfTransformation, [status(thm)], [f_119])).
% 7.43/2.58  tff(c_6860, plain, (v1_partfun1('#skF_12', '#skF_10') | ~v1_funct_2('#skF_12', '#skF_10', k2_relat_1('#skF_12')) | ~v1_funct_1('#skF_12') | v1_xboole_0(k2_relat_1('#skF_12'))), inference(resolution, [status(thm)], [c_2837, c_6851])).
% 7.43/2.58  tff(c_6877, plain, (v1_partfun1('#skF_12', '#skF_10') | v1_xboole_0(k2_relat_1('#skF_12'))), inference(demodulation, [status(thm), theory('equality')], [c_532, c_2839, c_6860])).
% 7.43/2.58  tff(c_6879, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2866, c_3047, c_6877])).
% 7.43/2.58  tff(c_6880, plain, (v1_xboole_0('#skF_12')), inference(splitRight, [status(thm)], [c_2858])).
% 7.43/2.58  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 7.43/2.58  tff(c_98, plain, (![A_95]: (m1_subset_1(k6_partfun1(A_95), k1_zfmisc_1(k2_zfmisc_1(A_95, A_95))))), inference(cnfTransformation, [status(thm)], [f_139])).
% 7.43/2.58  tff(c_2595, plain, (![C_481, B_482, A_483]: (v1_xboole_0(C_481) | ~m1_subset_1(C_481, k1_zfmisc_1(k2_zfmisc_1(B_482, A_483))) | ~v1_xboole_0(A_483))), inference(cnfTransformation, [status(thm)], [f_87])).
% 7.43/2.58  tff(c_2610, plain, (![A_484]: (v1_xboole_0(k6_partfun1(A_484)) | ~v1_xboole_0(A_484))), inference(resolution, [status(thm)], [c_98, c_2595])).
% 7.43/2.58  tff(c_16, plain, (![A_8, B_9]: (m1_subset_1(A_8, k1_zfmisc_1(B_9)) | ~r1_tarski(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_42])).
% 7.43/2.58  tff(c_2387, plain, (![C_433, B_434, A_435]: (~v1_xboole_0(C_433) | ~m1_subset_1(B_434, k1_zfmisc_1(C_433)) | ~r2_hidden(A_435, B_434))), inference(cnfTransformation, [status(thm)], [f_49])).
% 7.43/2.58  tff(c_2398, plain, (![B_436, A_437, A_438]: (~v1_xboole_0(B_436) | ~r2_hidden(A_437, A_438) | ~r1_tarski(A_438, B_436))), inference(resolution, [status(thm)], [c_16, c_2387])).
% 7.43/2.58  tff(c_2412, plain, (![B_442, A_443, B_444]: (~v1_xboole_0(B_442) | ~r1_tarski(A_443, B_442) | r1_tarski(A_443, B_444))), inference(resolution, [status(thm)], [c_6, c_2398])).
% 7.43/2.58  tff(c_2421, plain, (![B_7, B_444]: (~v1_xboole_0(B_7) | r1_tarski(B_7, B_444))), inference(resolution, [status(thm)], [c_12, c_2412])).
% 7.43/2.58  tff(c_2422, plain, (![B_445, B_446]: (~v1_xboole_0(B_445) | r1_tarski(B_445, B_446))), inference(resolution, [status(thm)], [c_12, c_2412])).
% 7.43/2.58  tff(c_8, plain, (![B_7, A_6]: (B_7=A_6 | ~r1_tarski(B_7, A_6) | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_38])).
% 7.43/2.58  tff(c_2461, plain, (![B_451, B_450]: (B_451=B_450 | ~r1_tarski(B_450, B_451) | ~v1_xboole_0(B_451))), inference(resolution, [status(thm)], [c_2422, c_8])).
% 7.43/2.58  tff(c_2478, plain, (![B_7, B_444]: (B_7=B_444 | ~v1_xboole_0(B_444) | ~v1_xboole_0(B_7))), inference(resolution, [status(thm)], [c_2421, c_2461])).
% 7.43/2.58  tff(c_2616, plain, (![A_484, B_7]: (k6_partfun1(A_484)=B_7 | ~v1_xboole_0(B_7) | ~v1_xboole_0(A_484))), inference(resolution, [status(thm)], [c_2610, c_2478])).
% 7.43/2.58  tff(c_7098, plain, (![A_833]: (k6_partfun1(A_833)='#skF_12' | ~v1_xboole_0(A_833))), inference(resolution, [status(thm)], [c_6880, c_2616])).
% 7.43/2.58  tff(c_7108, plain, (k6_partfun1('#skF_12')='#skF_12'), inference(resolution, [status(thm)], [c_6880, c_7098])).
% 7.43/2.58  tff(c_2655, plain, (![A_498, A_499, B_500]: (v1_xboole_0(A_498) | ~v1_xboole_0(A_499) | ~r1_tarski(A_498, k2_zfmisc_1(B_500, A_499)))), inference(resolution, [status(thm)], [c_16, c_2595])).
% 7.43/2.58  tff(c_2679, plain, (![B_501, A_502]: (v1_xboole_0(k2_zfmisc_1(B_501, A_502)) | ~v1_xboole_0(A_502))), inference(resolution, [status(thm)], [c_12, c_2655])).
% 7.43/2.58  tff(c_2396, plain, (![A_95, A_435]: (~v1_xboole_0(k2_zfmisc_1(A_95, A_95)) | ~r2_hidden(A_435, k6_partfun1(A_95)))), inference(resolution, [status(thm)], [c_98, c_2387])).
% 7.43/2.58  tff(c_2704, plain, (![A_435, A_502]: (~r2_hidden(A_435, k6_partfun1(A_502)) | ~v1_xboole_0(A_502))), inference(resolution, [status(thm)], [c_2679, c_2396])).
% 7.43/2.58  tff(c_7126, plain, (![A_435]: (~r2_hidden(A_435, '#skF_12') | ~v1_xboole_0('#skF_12'))), inference(superposition, [status(thm), theory('equality')], [c_7108, c_2704])).
% 7.43/2.58  tff(c_7158, plain, (![A_435]: (~r2_hidden(A_435, '#skF_12'))), inference(demodulation, [status(thm), theory('equality')], [c_6880, c_7126])).
% 7.43/2.58  tff(c_6881, plain, (v1_xboole_0(k2_relat_1('#skF_12'))), inference(splitRight, [status(thm)], [c_2858])).
% 7.43/2.58  tff(c_6960, plain, (![B_827]: (B_827='#skF_12' | ~v1_xboole_0(B_827))), inference(resolution, [status(thm)], [c_6880, c_2478])).
% 7.43/2.58  tff(c_6973, plain, (k2_relat_1('#skF_12')='#skF_12'), inference(resolution, [status(thm)], [c_6881, c_6960])).
% 7.43/2.58  tff(c_7173, plain, (![A_835, D_836]: (r2_hidden(k1_funct_1(A_835, D_836), k2_relat_1(A_835)) | ~r2_hidden(D_836, k1_relat_1(A_835)) | ~v1_funct_1(A_835) | ~v1_relat_1(A_835))), inference(cnfTransformation, [status(thm)], [f_70])).
% 7.43/2.58  tff(c_7180, plain, (![D_836]: (r2_hidden(k1_funct_1('#skF_12', D_836), '#skF_12') | ~r2_hidden(D_836, k1_relat_1('#skF_12')) | ~v1_funct_1('#skF_12') | ~v1_relat_1('#skF_12'))), inference(superposition, [status(thm), theory('equality')], [c_6973, c_7173])).
% 7.43/2.58  tff(c_7184, plain, (![D_836]: (r2_hidden(k1_funct_1('#skF_12', D_836), '#skF_12') | ~r2_hidden(D_836, '#skF_10'))), inference(demodulation, [status(thm), theory('equality')], [c_2352, c_532, c_2821, c_7180])).
% 7.43/2.58  tff(c_7186, plain, (![D_837]: (~r2_hidden(D_837, '#skF_10'))), inference(negUnitSimplification, [status(thm)], [c_7158, c_7184])).
% 7.43/2.58  tff(c_7192, plain, (![B_838]: (r1_tarski('#skF_10', B_838))), inference(resolution, [status(thm)], [c_6, c_7186])).
% 7.43/2.58  tff(c_2442, plain, (![B_446, B_445]: (B_446=B_445 | ~r1_tarski(B_446, B_445) | ~v1_xboole_0(B_445))), inference(resolution, [status(thm)], [c_2422, c_8])).
% 7.43/2.58  tff(c_7260, plain, (![B_841]: (B_841='#skF_10' | ~v1_xboole_0(B_841))), inference(resolution, [status(thm)], [c_7192, c_2442])).
% 7.43/2.58  tff(c_7270, plain, ('#skF_10'='#skF_12'), inference(resolution, [status(thm)], [c_6880, c_7260])).
% 7.43/2.58  tff(c_7290, plain, (~v1_funct_2('#skF_12', '#skF_12', '#skF_11')), inference(demodulation, [status(thm), theory('equality')], [c_7270, c_2344])).
% 7.43/2.58  tff(c_96, plain, (![A_95]: (v1_partfun1(k6_partfun1(A_95), A_95))), inference(cnfTransformation, [status(thm)], [f_139])).
% 7.43/2.58  tff(c_7146, plain, (v1_partfun1('#skF_12', '#skF_12')), inference(superposition, [status(thm), theory('equality')], [c_7108, c_96])).
% 7.43/2.58  tff(c_7289, plain, (m1_subset_1('#skF_12', k1_zfmisc_1(k2_zfmisc_1('#skF_12', '#skF_11')))), inference(demodulation, [status(thm), theory('equality')], [c_7270, c_2345])).
% 7.43/2.58  tff(c_52, plain, (![C_70, A_68, B_69]: (v1_funct_2(C_70, A_68, B_69) | ~v1_partfun1(C_70, A_68) | ~v1_funct_1(C_70) | ~m1_subset_1(C_70, k1_zfmisc_1(k2_zfmisc_1(A_68, B_69))))), inference(cnfTransformation, [status(thm)], [f_105])).
% 7.43/2.58  tff(c_7754, plain, (v1_funct_2('#skF_12', '#skF_12', '#skF_11') | ~v1_partfun1('#skF_12', '#skF_12') | ~v1_funct_1('#skF_12')), inference(resolution, [status(thm)], [c_7289, c_52])).
% 7.43/2.58  tff(c_7774, plain, (v1_funct_2('#skF_12', '#skF_12', '#skF_11')), inference(demodulation, [status(thm), theory('equality')], [c_532, c_7146, c_7754])).
% 7.43/2.58  tff(c_7776, plain, $false, inference(negUnitSimplification, [status(thm)], [c_7290, c_7774])).
% 7.43/2.58  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.43/2.58  
% 7.43/2.58  Inference rules
% 7.43/2.58  ----------------------
% 7.43/2.58  #Ref     : 0
% 7.43/2.58  #Sup     : 1771
% 7.43/2.58  #Fact    : 0
% 7.43/2.58  #Define  : 0
% 7.43/2.58  #Split   : 21
% 7.43/2.58  #Chain   : 0
% 7.43/2.58  #Close   : 0
% 7.43/2.58  
% 7.43/2.58  Ordering : KBO
% 7.43/2.58  
% 7.43/2.58  Simplification rules
% 7.43/2.58  ----------------------
% 7.43/2.58  #Subsume      : 553
% 7.43/2.58  #Demod        : 788
% 7.43/2.58  #Tautology    : 389
% 7.43/2.58  #SimpNegUnit  : 39
% 7.43/2.58  #BackRed      : 77
% 7.43/2.58  
% 7.43/2.58  #Partial instantiations: 0
% 7.43/2.58  #Strategies tried      : 1
% 7.43/2.58  
% 7.43/2.58  Timing (in seconds)
% 7.43/2.58  ----------------------
% 7.43/2.59  Preprocessing        : 0.39
% 7.43/2.59  Parsing              : 0.19
% 7.43/2.59  CNF conversion       : 0.03
% 7.43/2.59  Main loop            : 1.37
% 7.43/2.59  Inferencing          : 0.46
% 7.43/2.59  Reduction            : 0.43
% 7.43/2.59  Demodulation         : 0.30
% 7.43/2.59  BG Simplification    : 0.06
% 7.43/2.59  Subsumption          : 0.30
% 7.43/2.59  Abstraction          : 0.06
% 7.43/2.59  MUC search           : 0.00
% 7.43/2.59  Cooper               : 0.00
% 7.43/2.59  Total                : 1.80
% 7.43/2.59  Index Insertion      : 0.00
% 7.43/2.59  Index Deletion       : 0.00
% 7.43/2.59  Index Matching       : 0.00
% 7.43/2.59  BG Taut test         : 0.00
%------------------------------------------------------------------------------
