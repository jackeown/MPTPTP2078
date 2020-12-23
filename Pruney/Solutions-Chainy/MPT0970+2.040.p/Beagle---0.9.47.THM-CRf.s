%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:11:24 EST 2020

% Result     : Theorem 4.58s
% Output     : CNFRefutation 4.79s
% Verified   : 
% Statistics : Number of formulae       :  159 (1396 expanded)
%              Number of leaves         :   46 ( 502 expanded)
%              Depth                    :   12
%              Number of atoms          :  292 (4457 expanded)
%              Number of equality atoms :   97 (1986 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k4_tarski > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_6 > #skF_4 > #skF_10 > #skF_2 > #skF_7 > #skF_9 > #skF_8 > #skF_5 > #skF_11 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_11',type,(
    '#skF_11': $i > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_154,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( ! [D] :
              ~ ( r2_hidden(D,B)
                & ! [E] :
                    ~ ( r2_hidden(E,A)
                      & D = k1_funct_1(C,E) ) )
         => k2_relset_1(A,B,C) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_funct_2)).

tff(f_105,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_52,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_44,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_117,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( ! [D] :
            ~ ( r2_hidden(D,B)
              & ! [E] : ~ r2_hidden(k4_tarski(E,D),C) )
      <=> k2_relset_1(A,B,C) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_relset_1)).

tff(f_101,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_135,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).

tff(f_91,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B,C] :
          ( C = k9_relat_1(A,B)
        <=> ! [D] :
              ( r2_hidden(D,C)
            <=> ? [E] :
                  ( r2_hidden(E,k1_relat_1(A))
                  & r2_hidden(E,B)
                  & D = k1_funct_1(A,E) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d12_funct_1)).

tff(f_63,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k9_relat_1(C,B))
      <=> ? [D] :
            ( r2_hidden(D,k1_relat_1(C))
            & r2_hidden(k4_tarski(D,A),C)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t143_relat_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_97,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_66,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(c_90,plain,(
    m1_subset_1('#skF_10',k1_zfmisc_1(k2_zfmisc_1('#skF_8','#skF_9'))) ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_305,plain,(
    ! [A_128,B_129,C_130] :
      ( k2_relset_1(A_128,B_129,C_130) = k2_relat_1(C_130)
      | ~ m1_subset_1(C_130,k1_zfmisc_1(k2_zfmisc_1(A_128,B_129))) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_315,plain,(
    k2_relset_1('#skF_8','#skF_9','#skF_10') = k2_relat_1('#skF_10') ),
    inference(resolution,[status(thm)],[c_90,c_305])).

tff(c_88,plain,(
    k2_relset_1('#skF_8','#skF_9','#skF_10') != '#skF_9' ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_316,plain,(
    k2_relat_1('#skF_10') != '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_315,c_88])).

tff(c_20,plain,(
    ! [A_10,B_11] : v1_relat_1(k2_zfmisc_1(A_10,B_11)) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_193,plain,(
    ! [B_104,A_105] :
      ( v1_relat_1(B_104)
      | ~ m1_subset_1(B_104,k1_zfmisc_1(A_105))
      | ~ v1_relat_1(A_105) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_196,plain,
    ( v1_relat_1('#skF_10')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_8','#skF_9')) ),
    inference(resolution,[status(thm)],[c_90,c_193])).

tff(c_199,plain,(
    v1_relat_1('#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_196])).

tff(c_1737,plain,(
    ! [A_400,B_401,C_402] :
      ( r2_hidden('#skF_6'(A_400,B_401,C_402),B_401)
      | k2_relset_1(A_400,B_401,C_402) = B_401
      | ~ m1_subset_1(C_402,k1_zfmisc_1(k2_zfmisc_1(A_400,B_401))) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_1739,plain,
    ( r2_hidden('#skF_6'('#skF_8','#skF_9','#skF_10'),'#skF_9')
    | k2_relset_1('#skF_8','#skF_9','#skF_10') = '#skF_9' ),
    inference(resolution,[status(thm)],[c_90,c_1737])).

tff(c_1745,plain,
    ( r2_hidden('#skF_6'('#skF_8','#skF_9','#skF_10'),'#skF_9')
    | k2_relat_1('#skF_10') = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_315,c_1739])).

tff(c_1746,plain,(
    r2_hidden('#skF_6'('#skF_8','#skF_9','#skF_10'),'#skF_9') ),
    inference(negUnitSimplification,[status(thm)],[c_316,c_1745])).

tff(c_98,plain,(
    ! [D_89] :
      ( r2_hidden('#skF_11'(D_89),'#skF_8')
      | ~ r2_hidden(D_89,'#skF_9') ) ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_94,plain,(
    v1_funct_1('#skF_10') ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_92,plain,(
    v1_funct_2('#skF_10','#skF_8','#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_1554,plain,(
    ! [A_359,B_360,C_361] :
      ( k1_relset_1(A_359,B_360,C_361) = k1_relat_1(C_361)
      | ~ m1_subset_1(C_361,k1_zfmisc_1(k2_zfmisc_1(A_359,B_360))) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_1564,plain,(
    k1_relset_1('#skF_8','#skF_9','#skF_10') = k1_relat_1('#skF_10') ),
    inference(resolution,[status(thm)],[c_90,c_1554])).

tff(c_1706,plain,(
    ! [B_395,A_396,C_397] :
      ( k1_xboole_0 = B_395
      | k1_relset_1(A_396,B_395,C_397) = A_396
      | ~ v1_funct_2(C_397,A_396,B_395)
      | ~ m1_subset_1(C_397,k1_zfmisc_1(k2_zfmisc_1(A_396,B_395))) ) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_1709,plain,
    ( k1_xboole_0 = '#skF_9'
    | k1_relset_1('#skF_8','#skF_9','#skF_10') = '#skF_8'
    | ~ v1_funct_2('#skF_10','#skF_8','#skF_9') ),
    inference(resolution,[status(thm)],[c_90,c_1706])).

tff(c_1718,plain,
    ( k1_xboole_0 = '#skF_9'
    | k1_relat_1('#skF_10') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_1564,c_1709])).

tff(c_1720,plain,(
    k1_relat_1('#skF_10') = '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_1718])).

tff(c_96,plain,(
    ! [D_89] :
      ( k1_funct_1('#skF_10','#skF_11'(D_89)) = D_89
      | ~ r2_hidden(D_89,'#skF_9') ) ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_1779,plain,(
    ! [A_415,E_416,B_417] :
      ( r2_hidden(k1_funct_1(A_415,E_416),k9_relat_1(A_415,B_417))
      | ~ r2_hidden(E_416,B_417)
      | ~ r2_hidden(E_416,k1_relat_1(A_415))
      | ~ v1_funct_1(A_415)
      | ~ v1_relat_1(A_415) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_1782,plain,(
    ! [D_89,B_417] :
      ( r2_hidden(D_89,k9_relat_1('#skF_10',B_417))
      | ~ r2_hidden('#skF_11'(D_89),B_417)
      | ~ r2_hidden('#skF_11'(D_89),k1_relat_1('#skF_10'))
      | ~ v1_funct_1('#skF_10')
      | ~ v1_relat_1('#skF_10')
      | ~ r2_hidden(D_89,'#skF_9') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_96,c_1779])).

tff(c_1785,plain,(
    ! [D_418,B_419] :
      ( r2_hidden(D_418,k9_relat_1('#skF_10',B_419))
      | ~ r2_hidden('#skF_11'(D_418),B_419)
      | ~ r2_hidden('#skF_11'(D_418),'#skF_8')
      | ~ r2_hidden(D_418,'#skF_9') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_199,c_94,c_1720,c_1782])).

tff(c_1789,plain,(
    ! [D_420] :
      ( r2_hidden(D_420,k9_relat_1('#skF_10','#skF_8'))
      | ~ r2_hidden('#skF_11'(D_420),'#skF_8')
      | ~ r2_hidden(D_420,'#skF_9') ) ),
    inference(resolution,[status(thm)],[c_98,c_1785])).

tff(c_1793,plain,(
    ! [D_89] :
      ( r2_hidden(D_89,k9_relat_1('#skF_10','#skF_8'))
      | ~ r2_hidden(D_89,'#skF_9') ) ),
    inference(resolution,[status(thm)],[c_98,c_1789])).

tff(c_26,plain,(
    ! [A_12,B_13,C_14] :
      ( r2_hidden(k4_tarski('#skF_1'(A_12,B_13,C_14),A_12),C_14)
      | ~ r2_hidden(A_12,k9_relat_1(C_14,B_13))
      | ~ v1_relat_1(C_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_1794,plain,(
    ! [E_421,A_422,B_423,C_424] :
      ( ~ r2_hidden(k4_tarski(E_421,'#skF_6'(A_422,B_423,C_424)),C_424)
      | k2_relset_1(A_422,B_423,C_424) = B_423
      | ~ m1_subset_1(C_424,k1_zfmisc_1(k2_zfmisc_1(A_422,B_423))) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_1940,plain,(
    ! [A_456,B_457,C_458,B_459] :
      ( k2_relset_1(A_456,B_457,C_458) = B_457
      | ~ m1_subset_1(C_458,k1_zfmisc_1(k2_zfmisc_1(A_456,B_457)))
      | ~ r2_hidden('#skF_6'(A_456,B_457,C_458),k9_relat_1(C_458,B_459))
      | ~ v1_relat_1(C_458) ) ),
    inference(resolution,[status(thm)],[c_26,c_1794])).

tff(c_1948,plain,(
    ! [A_456,B_457] :
      ( k2_relset_1(A_456,B_457,'#skF_10') = B_457
      | ~ m1_subset_1('#skF_10',k1_zfmisc_1(k2_zfmisc_1(A_456,B_457)))
      | ~ v1_relat_1('#skF_10')
      | ~ r2_hidden('#skF_6'(A_456,B_457,'#skF_10'),'#skF_9') ) ),
    inference(resolution,[status(thm)],[c_1793,c_1940])).

tff(c_1961,plain,(
    ! [A_460,B_461] :
      ( k2_relset_1(A_460,B_461,'#skF_10') = B_461
      | ~ m1_subset_1('#skF_10',k1_zfmisc_1(k2_zfmisc_1(A_460,B_461)))
      | ~ r2_hidden('#skF_6'(A_460,B_461,'#skF_10'),'#skF_9') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_199,c_1948])).

tff(c_1964,plain,
    ( k2_relset_1('#skF_8','#skF_9','#skF_10') = '#skF_9'
    | ~ r2_hidden('#skF_6'('#skF_8','#skF_9','#skF_10'),'#skF_9') ),
    inference(resolution,[status(thm)],[c_90,c_1961])).

tff(c_1973,plain,(
    k2_relat_1('#skF_10') = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1746,c_315,c_1964])).

tff(c_1975,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_316,c_1973])).

tff(c_1976,plain,(
    k1_xboole_0 = '#skF_9' ),
    inference(splitRight,[status(thm)],[c_1718])).

tff(c_10,plain,(
    ! [A_3] : k2_zfmisc_1(A_3,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_2008,plain,(
    ! [A_3] : k2_zfmisc_1(A_3,'#skF_9') = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1976,c_1976,c_10])).

tff(c_2108,plain,(
    m1_subset_1('#skF_10',k1_zfmisc_1('#skF_9')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2008,c_90])).

tff(c_12,plain,(
    ! [B_4] : k2_zfmisc_1(k1_xboole_0,B_4) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_210,plain,(
    ! [C_106,B_107,A_108] :
      ( v5_relat_1(C_106,B_107)
      | ~ m1_subset_1(C_106,k1_zfmisc_1(k2_zfmisc_1(A_108,B_107))) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_219,plain,(
    ! [C_106,B_4] :
      ( v5_relat_1(C_106,B_4)
      | ~ m1_subset_1(C_106,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_210])).

tff(c_2262,plain,(
    ! [C_490,B_491] :
      ( v5_relat_1(C_490,B_491)
      | ~ m1_subset_1(C_490,k1_zfmisc_1('#skF_9')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1976,c_219])).

tff(c_2267,plain,(
    ! [B_491] : v5_relat_1('#skF_10',B_491) ),
    inference(resolution,[status(thm)],[c_2108,c_2262])).

tff(c_420,plain,(
    ! [A_167,B_168,C_169] :
      ( r2_hidden('#skF_6'(A_167,B_168,C_169),B_168)
      | k2_relset_1(A_167,B_168,C_169) = B_168
      | ~ m1_subset_1(C_169,k1_zfmisc_1(k2_zfmisc_1(A_167,B_168))) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_422,plain,
    ( r2_hidden('#skF_6'('#skF_8','#skF_9','#skF_10'),'#skF_9')
    | k2_relset_1('#skF_8','#skF_9','#skF_10') = '#skF_9' ),
    inference(resolution,[status(thm)],[c_90,c_420])).

tff(c_428,plain,
    ( r2_hidden('#skF_6'('#skF_8','#skF_9','#skF_10'),'#skF_9')
    | k2_relat_1('#skF_10') = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_315,c_422])).

tff(c_429,plain,(
    r2_hidden('#skF_6'('#skF_8','#skF_9','#skF_10'),'#skF_9') ),
    inference(negUnitSimplification,[status(thm)],[c_316,c_428])).

tff(c_325,plain,(
    ! [A_137,B_138,C_139] :
      ( k1_relset_1(A_137,B_138,C_139) = k1_relat_1(C_139)
      | ~ m1_subset_1(C_139,k1_zfmisc_1(k2_zfmisc_1(A_137,B_138))) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_335,plain,(
    k1_relset_1('#skF_8','#skF_9','#skF_10') = k1_relat_1('#skF_10') ),
    inference(resolution,[status(thm)],[c_90,c_325])).

tff(c_389,plain,(
    ! [B_162,A_163,C_164] :
      ( k1_xboole_0 = B_162
      | k1_relset_1(A_163,B_162,C_164) = A_163
      | ~ v1_funct_2(C_164,A_163,B_162)
      | ~ m1_subset_1(C_164,k1_zfmisc_1(k2_zfmisc_1(A_163,B_162))) ) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_392,plain,
    ( k1_xboole_0 = '#skF_9'
    | k1_relset_1('#skF_8','#skF_9','#skF_10') = '#skF_8'
    | ~ v1_funct_2('#skF_10','#skF_8','#skF_9') ),
    inference(resolution,[status(thm)],[c_90,c_389])).

tff(c_401,plain,
    ( k1_xboole_0 = '#skF_9'
    | k1_relat_1('#skF_10') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_335,c_392])).

tff(c_403,plain,(
    k1_relat_1('#skF_10') = '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_401])).

tff(c_479,plain,(
    ! [A_183,E_184,B_185] :
      ( r2_hidden(k1_funct_1(A_183,E_184),k9_relat_1(A_183,B_185))
      | ~ r2_hidden(E_184,B_185)
      | ~ r2_hidden(E_184,k1_relat_1(A_183))
      | ~ v1_funct_1(A_183)
      | ~ v1_relat_1(A_183) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_482,plain,(
    ! [D_89,B_185] :
      ( r2_hidden(D_89,k9_relat_1('#skF_10',B_185))
      | ~ r2_hidden('#skF_11'(D_89),B_185)
      | ~ r2_hidden('#skF_11'(D_89),k1_relat_1('#skF_10'))
      | ~ v1_funct_1('#skF_10')
      | ~ v1_relat_1('#skF_10')
      | ~ r2_hidden(D_89,'#skF_9') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_96,c_479])).

tff(c_485,plain,(
    ! [D_186,B_187] :
      ( r2_hidden(D_186,k9_relat_1('#skF_10',B_187))
      | ~ r2_hidden('#skF_11'(D_186),B_187)
      | ~ r2_hidden('#skF_11'(D_186),'#skF_8')
      | ~ r2_hidden(D_186,'#skF_9') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_199,c_94,c_403,c_482])).

tff(c_500,plain,(
    ! [D_191] :
      ( r2_hidden(D_191,k9_relat_1('#skF_10','#skF_8'))
      | ~ r2_hidden('#skF_11'(D_191),'#skF_8')
      | ~ r2_hidden(D_191,'#skF_9') ) ),
    inference(resolution,[status(thm)],[c_98,c_485])).

tff(c_504,plain,(
    ! [D_89] :
      ( r2_hidden(D_89,k9_relat_1('#skF_10','#skF_8'))
      | ~ r2_hidden(D_89,'#skF_9') ) ),
    inference(resolution,[status(thm)],[c_98,c_500])).

tff(c_575,plain,(
    ! [E_203,A_204,B_205,C_206] :
      ( ~ r2_hidden(k4_tarski(E_203,'#skF_6'(A_204,B_205,C_206)),C_206)
      | k2_relset_1(A_204,B_205,C_206) = B_205
      | ~ m1_subset_1(C_206,k1_zfmisc_1(k2_zfmisc_1(A_204,B_205))) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_634,plain,(
    ! [A_221,B_222,C_223,B_224] :
      ( k2_relset_1(A_221,B_222,C_223) = B_222
      | ~ m1_subset_1(C_223,k1_zfmisc_1(k2_zfmisc_1(A_221,B_222)))
      | ~ r2_hidden('#skF_6'(A_221,B_222,C_223),k9_relat_1(C_223,B_224))
      | ~ v1_relat_1(C_223) ) ),
    inference(resolution,[status(thm)],[c_26,c_575])).

tff(c_642,plain,(
    ! [A_221,B_222] :
      ( k2_relset_1(A_221,B_222,'#skF_10') = B_222
      | ~ m1_subset_1('#skF_10',k1_zfmisc_1(k2_zfmisc_1(A_221,B_222)))
      | ~ v1_relat_1('#skF_10')
      | ~ r2_hidden('#skF_6'(A_221,B_222,'#skF_10'),'#skF_9') ) ),
    inference(resolution,[status(thm)],[c_504,c_634])).

tff(c_655,plain,(
    ! [A_225,B_226] :
      ( k2_relset_1(A_225,B_226,'#skF_10') = B_226
      | ~ m1_subset_1('#skF_10',k1_zfmisc_1(k2_zfmisc_1(A_225,B_226)))
      | ~ r2_hidden('#skF_6'(A_225,B_226,'#skF_10'),'#skF_9') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_199,c_642])).

tff(c_658,plain,
    ( k2_relset_1('#skF_8','#skF_9','#skF_10') = '#skF_9'
    | ~ r2_hidden('#skF_6'('#skF_8','#skF_9','#skF_10'),'#skF_9') ),
    inference(resolution,[status(thm)],[c_90,c_655])).

tff(c_667,plain,(
    k2_relat_1('#skF_10') = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_429,c_315,c_658])).

tff(c_669,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_316,c_667])).

tff(c_670,plain,(
    k1_xboole_0 = '#skF_9' ),
    inference(splitRight,[status(thm)],[c_401])).

tff(c_76,plain,(
    ! [A_83] :
      ( v1_funct_2(k1_xboole_0,A_83,k1_xboole_0)
      | k1_xboole_0 = A_83
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(A_83,k1_xboole_0))) ) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_101,plain,(
    ! [A_83] :
      ( v1_funct_2(k1_xboole_0,A_83,k1_xboole_0)
      | k1_xboole_0 = A_83
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_76])).

tff(c_321,plain,(
    ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(splitLeft,[status(thm)],[c_101])).

tff(c_682,plain,(
    ~ m1_subset_1('#skF_9',k1_zfmisc_1('#skF_9')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_670,c_670,c_321])).

tff(c_671,plain,(
    k1_relat_1('#skF_10') != '#skF_8' ),
    inference(splitRight,[status(thm)],[c_401])).

tff(c_695,plain,(
    ! [A_3] : k2_zfmisc_1(A_3,'#skF_9') = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_670,c_670,c_10])).

tff(c_744,plain,(
    m1_subset_1('#skF_10',k1_zfmisc_1('#skF_9')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_695,c_90])).

tff(c_78,plain,(
    ! [C_85,A_83] :
      ( k1_xboole_0 = C_85
      | ~ v1_funct_2(C_85,A_83,k1_xboole_0)
      | k1_xboole_0 = A_83
      | ~ m1_subset_1(C_85,k1_zfmisc_1(k2_zfmisc_1(A_83,k1_xboole_0))) ) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_102,plain,(
    ! [C_85,A_83] :
      ( k1_xboole_0 = C_85
      | ~ v1_funct_2(C_85,A_83,k1_xboole_0)
      | k1_xboole_0 = A_83
      | ~ m1_subset_1(C_85,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_78])).

tff(c_1057,plain,(
    ! [C_289,A_290] :
      ( C_289 = '#skF_9'
      | ~ v1_funct_2(C_289,A_290,'#skF_9')
      | A_290 = '#skF_9'
      | ~ m1_subset_1(C_289,k1_zfmisc_1('#skF_9')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_670,c_670,c_670,c_670,c_102])).

tff(c_1059,plain,
    ( '#skF_10' = '#skF_9'
    | '#skF_9' = '#skF_8'
    | ~ m1_subset_1('#skF_10',k1_zfmisc_1('#skF_9')) ),
    inference(resolution,[status(thm)],[c_92,c_1057])).

tff(c_1062,plain,
    ( '#skF_10' = '#skF_9'
    | '#skF_9' = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_744,c_1059])).

tff(c_1063,plain,(
    '#skF_9' = '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_1062])).

tff(c_1088,plain,(
    m1_subset_1('#skF_10',k1_zfmisc_1('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1063,c_744])).

tff(c_331,plain,(
    ! [A_3,C_139] :
      ( k1_relset_1(A_3,k1_xboole_0,C_139) = k1_relat_1(C_139)
      | ~ m1_subset_1(C_139,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_325])).

tff(c_954,plain,(
    ! [A_264,C_265] :
      ( k1_relset_1(A_264,'#skF_9',C_265) = k1_relat_1(C_265)
      | ~ m1_subset_1(C_265,k1_zfmisc_1('#skF_9')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_670,c_670,c_331])).

tff(c_957,plain,(
    ! [A_264] : k1_relset_1(A_264,'#skF_9','#skF_10') = k1_relat_1('#skF_10') ),
    inference(resolution,[status(thm)],[c_744,c_954])).

tff(c_1072,plain,(
    ! [A_264] : k1_relset_1(A_264,'#skF_8','#skF_10') = k1_relat_1('#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1063,c_957])).

tff(c_1101,plain,(
    v1_funct_2('#skF_10','#skF_8','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1063,c_92])).

tff(c_84,plain,(
    ! [B_84,C_85] :
      ( k1_relset_1(k1_xboole_0,B_84,C_85) = k1_xboole_0
      | ~ v1_funct_2(C_85,k1_xboole_0,B_84)
      | ~ m1_subset_1(C_85,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_84))) ) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_99,plain,(
    ! [B_84,C_85] :
      ( k1_relset_1(k1_xboole_0,B_84,C_85) = k1_xboole_0
      | ~ v1_funct_2(C_85,k1_xboole_0,B_84)
      | ~ m1_subset_1(C_85,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_84])).

tff(c_674,plain,(
    ! [B_84,C_85] :
      ( k1_relset_1('#skF_9',B_84,C_85) = '#skF_9'
      | ~ v1_funct_2(C_85,'#skF_9',B_84)
      | ~ m1_subset_1(C_85,k1_zfmisc_1('#skF_9')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_670,c_670,c_670,c_670,c_99])).

tff(c_1476,plain,(
    ! [B_352,C_353] :
      ( k1_relset_1('#skF_8',B_352,C_353) = '#skF_8'
      | ~ v1_funct_2(C_353,'#skF_8',B_352)
      | ~ m1_subset_1(C_353,k1_zfmisc_1('#skF_8')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1063,c_1063,c_1063,c_1063,c_674])).

tff(c_1478,plain,
    ( k1_relset_1('#skF_8','#skF_8','#skF_10') = '#skF_8'
    | ~ m1_subset_1('#skF_10',k1_zfmisc_1('#skF_8')) ),
    inference(resolution,[status(thm)],[c_1101,c_1476])).

tff(c_1481,plain,(
    k1_relat_1('#skF_10') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1088,c_1072,c_1478])).

tff(c_1483,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_671,c_1481])).

tff(c_1484,plain,(
    '#skF_10' = '#skF_9' ),
    inference(splitRight,[status(thm)],[c_1062])).

tff(c_1494,plain,(
    m1_subset_1('#skF_9',k1_zfmisc_1('#skF_9')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1484,c_744])).

tff(c_1510,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_682,c_1494])).

tff(c_1512,plain,(
    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(splitRight,[status(thm)],[c_101])).

tff(c_1521,plain,(
    ! [B_4] : v5_relat_1(k1_xboole_0,B_4) ),
    inference(resolution,[status(thm)],[c_1512,c_219])).

tff(c_120,plain,(
    ! [A_93,B_94] : v1_relat_1(k2_zfmisc_1(A_93,B_94)) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_122,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_120])).

tff(c_30,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_253,plain,(
    ! [B_121,A_122] :
      ( r1_tarski(k2_relat_1(B_121),A_122)
      | ~ v5_relat_1(B_121,A_122)
      | ~ v1_relat_1(B_121) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_261,plain,(
    ! [A_122] :
      ( r1_tarski(k1_xboole_0,A_122)
      | ~ v5_relat_1(k1_xboole_0,A_122)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_253])).

tff(c_265,plain,(
    ! [A_122] :
      ( r1_tarski(k1_xboole_0,A_122)
      | ~ v5_relat_1(k1_xboole_0,A_122) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_122,c_261])).

tff(c_1528,plain,(
    ! [A_122] : r1_tarski(k1_xboole_0,A_122) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1521,c_265])).

tff(c_2059,plain,(
    ! [A_467] : r1_tarski('#skF_9',A_467) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1976,c_1528])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_263,plain,(
    ! [B_121,A_122] :
      ( k2_relat_1(B_121) = A_122
      | ~ r1_tarski(A_122,k2_relat_1(B_121))
      | ~ v5_relat_1(B_121,A_122)
      | ~ v1_relat_1(B_121) ) ),
    inference(resolution,[status(thm)],[c_253,c_2])).

tff(c_2330,plain,(
    ! [B_506] :
      ( k2_relat_1(B_506) = '#skF_9'
      | ~ v5_relat_1(B_506,'#skF_9')
      | ~ v1_relat_1(B_506) ) ),
    inference(resolution,[status(thm)],[c_2059,c_263])).

tff(c_2334,plain,
    ( k2_relat_1('#skF_10') = '#skF_9'
    | ~ v1_relat_1('#skF_10') ),
    inference(resolution,[status(thm)],[c_2267,c_2330])).

tff(c_2341,plain,(
    k2_relat_1('#skF_10') = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_199,c_2334])).

tff(c_2343,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_316,c_2341])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n017.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 16:05:46 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.58/1.78  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.65/1.80  
% 4.65/1.80  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.65/1.80  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k4_tarski > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_6 > #skF_4 > #skF_10 > #skF_2 > #skF_7 > #skF_9 > #skF_8 > #skF_5 > #skF_11 > #skF_3
% 4.65/1.80  
% 4.65/1.80  %Foreground sorts:
% 4.65/1.80  
% 4.65/1.80  
% 4.65/1.80  %Background operators:
% 4.65/1.80  
% 4.65/1.80  
% 4.65/1.80  %Foreground operators:
% 4.65/1.80  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 4.65/1.80  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 4.65/1.80  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.65/1.80  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.65/1.80  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.65/1.80  tff('#skF_6', type, '#skF_6': ($i * $i * $i) > $i).
% 4.65/1.80  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 4.65/1.80  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.65/1.80  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 4.65/1.80  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.65/1.80  tff('#skF_10', type, '#skF_10': $i).
% 4.65/1.80  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 4.65/1.80  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.65/1.80  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 4.65/1.80  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 4.65/1.80  tff('#skF_7', type, '#skF_7': ($i * $i * $i * $i) > $i).
% 4.65/1.80  tff('#skF_9', type, '#skF_9': $i).
% 4.65/1.80  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 4.65/1.80  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 4.65/1.80  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.65/1.80  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 4.65/1.80  tff('#skF_8', type, '#skF_8': $i).
% 4.65/1.80  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.65/1.80  tff('#skF_5', type, '#skF_5': ($i * $i * $i * $i) > $i).
% 4.65/1.80  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.65/1.80  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.65/1.80  tff('#skF_11', type, '#skF_11': $i > $i).
% 4.65/1.80  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 4.65/1.80  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.65/1.80  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 4.65/1.80  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.65/1.80  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.65/1.80  
% 4.79/1.82  tff(f_154, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((![D]: ~(r2_hidden(D, B) & (![E]: ~(r2_hidden(E, A) & (D = k1_funct_1(C, E)))))) => (k2_relset_1(A, B, C) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t16_funct_2)).
% 4.79/1.82  tff(f_105, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 4.79/1.82  tff(f_52, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 4.79/1.82  tff(f_44, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 4.79/1.82  tff(f_117, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((![D]: ~(r2_hidden(D, B) & (![E]: ~r2_hidden(k4_tarski(E, D), C)))) <=> (k2_relset_1(A, B, C) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t23_relset_1)).
% 4.79/1.82  tff(f_101, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 4.79/1.82  tff(f_135, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 4.79/1.82  tff(f_91, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B, C]: ((C = k9_relat_1(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (?[E]: ((r2_hidden(E, k1_relat_1(A)) & r2_hidden(E, B)) & (D = k1_funct_1(A, E)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d12_funct_1)).
% 4.79/1.82  tff(f_63, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k9_relat_1(C, B)) <=> (?[D]: ((r2_hidden(D, k1_relat_1(C)) & r2_hidden(k4_tarski(D, A), C)) & r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t143_relat_1)).
% 4.79/1.82  tff(f_37, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 4.79/1.82  tff(f_97, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 4.79/1.82  tff(f_66, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 4.79/1.82  tff(f_50, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 4.79/1.82  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 4.79/1.82  tff(c_90, plain, (m1_subset_1('#skF_10', k1_zfmisc_1(k2_zfmisc_1('#skF_8', '#skF_9')))), inference(cnfTransformation, [status(thm)], [f_154])).
% 4.79/1.82  tff(c_305, plain, (![A_128, B_129, C_130]: (k2_relset_1(A_128, B_129, C_130)=k2_relat_1(C_130) | ~m1_subset_1(C_130, k1_zfmisc_1(k2_zfmisc_1(A_128, B_129))))), inference(cnfTransformation, [status(thm)], [f_105])).
% 4.79/1.82  tff(c_315, plain, (k2_relset_1('#skF_8', '#skF_9', '#skF_10')=k2_relat_1('#skF_10')), inference(resolution, [status(thm)], [c_90, c_305])).
% 4.79/1.82  tff(c_88, plain, (k2_relset_1('#skF_8', '#skF_9', '#skF_10')!='#skF_9'), inference(cnfTransformation, [status(thm)], [f_154])).
% 4.79/1.82  tff(c_316, plain, (k2_relat_1('#skF_10')!='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_315, c_88])).
% 4.79/1.82  tff(c_20, plain, (![A_10, B_11]: (v1_relat_1(k2_zfmisc_1(A_10, B_11)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 4.79/1.82  tff(c_193, plain, (![B_104, A_105]: (v1_relat_1(B_104) | ~m1_subset_1(B_104, k1_zfmisc_1(A_105)) | ~v1_relat_1(A_105))), inference(cnfTransformation, [status(thm)], [f_44])).
% 4.79/1.82  tff(c_196, plain, (v1_relat_1('#skF_10') | ~v1_relat_1(k2_zfmisc_1('#skF_8', '#skF_9'))), inference(resolution, [status(thm)], [c_90, c_193])).
% 4.79/1.82  tff(c_199, plain, (v1_relat_1('#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_20, c_196])).
% 4.79/1.82  tff(c_1737, plain, (![A_400, B_401, C_402]: (r2_hidden('#skF_6'(A_400, B_401, C_402), B_401) | k2_relset_1(A_400, B_401, C_402)=B_401 | ~m1_subset_1(C_402, k1_zfmisc_1(k2_zfmisc_1(A_400, B_401))))), inference(cnfTransformation, [status(thm)], [f_117])).
% 4.79/1.82  tff(c_1739, plain, (r2_hidden('#skF_6'('#skF_8', '#skF_9', '#skF_10'), '#skF_9') | k2_relset_1('#skF_8', '#skF_9', '#skF_10')='#skF_9'), inference(resolution, [status(thm)], [c_90, c_1737])).
% 4.79/1.82  tff(c_1745, plain, (r2_hidden('#skF_6'('#skF_8', '#skF_9', '#skF_10'), '#skF_9') | k2_relat_1('#skF_10')='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_315, c_1739])).
% 4.79/1.82  tff(c_1746, plain, (r2_hidden('#skF_6'('#skF_8', '#skF_9', '#skF_10'), '#skF_9')), inference(negUnitSimplification, [status(thm)], [c_316, c_1745])).
% 4.79/1.82  tff(c_98, plain, (![D_89]: (r2_hidden('#skF_11'(D_89), '#skF_8') | ~r2_hidden(D_89, '#skF_9'))), inference(cnfTransformation, [status(thm)], [f_154])).
% 4.79/1.82  tff(c_94, plain, (v1_funct_1('#skF_10')), inference(cnfTransformation, [status(thm)], [f_154])).
% 4.79/1.82  tff(c_92, plain, (v1_funct_2('#skF_10', '#skF_8', '#skF_9')), inference(cnfTransformation, [status(thm)], [f_154])).
% 4.79/1.82  tff(c_1554, plain, (![A_359, B_360, C_361]: (k1_relset_1(A_359, B_360, C_361)=k1_relat_1(C_361) | ~m1_subset_1(C_361, k1_zfmisc_1(k2_zfmisc_1(A_359, B_360))))), inference(cnfTransformation, [status(thm)], [f_101])).
% 4.79/1.82  tff(c_1564, plain, (k1_relset_1('#skF_8', '#skF_9', '#skF_10')=k1_relat_1('#skF_10')), inference(resolution, [status(thm)], [c_90, c_1554])).
% 4.79/1.82  tff(c_1706, plain, (![B_395, A_396, C_397]: (k1_xboole_0=B_395 | k1_relset_1(A_396, B_395, C_397)=A_396 | ~v1_funct_2(C_397, A_396, B_395) | ~m1_subset_1(C_397, k1_zfmisc_1(k2_zfmisc_1(A_396, B_395))))), inference(cnfTransformation, [status(thm)], [f_135])).
% 4.79/1.82  tff(c_1709, plain, (k1_xboole_0='#skF_9' | k1_relset_1('#skF_8', '#skF_9', '#skF_10')='#skF_8' | ~v1_funct_2('#skF_10', '#skF_8', '#skF_9')), inference(resolution, [status(thm)], [c_90, c_1706])).
% 4.79/1.82  tff(c_1718, plain, (k1_xboole_0='#skF_9' | k1_relat_1('#skF_10')='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_92, c_1564, c_1709])).
% 4.79/1.82  tff(c_1720, plain, (k1_relat_1('#skF_10')='#skF_8'), inference(splitLeft, [status(thm)], [c_1718])).
% 4.79/1.82  tff(c_96, plain, (![D_89]: (k1_funct_1('#skF_10', '#skF_11'(D_89))=D_89 | ~r2_hidden(D_89, '#skF_9'))), inference(cnfTransformation, [status(thm)], [f_154])).
% 4.79/1.82  tff(c_1779, plain, (![A_415, E_416, B_417]: (r2_hidden(k1_funct_1(A_415, E_416), k9_relat_1(A_415, B_417)) | ~r2_hidden(E_416, B_417) | ~r2_hidden(E_416, k1_relat_1(A_415)) | ~v1_funct_1(A_415) | ~v1_relat_1(A_415))), inference(cnfTransformation, [status(thm)], [f_91])).
% 4.79/1.82  tff(c_1782, plain, (![D_89, B_417]: (r2_hidden(D_89, k9_relat_1('#skF_10', B_417)) | ~r2_hidden('#skF_11'(D_89), B_417) | ~r2_hidden('#skF_11'(D_89), k1_relat_1('#skF_10')) | ~v1_funct_1('#skF_10') | ~v1_relat_1('#skF_10') | ~r2_hidden(D_89, '#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_96, c_1779])).
% 4.79/1.82  tff(c_1785, plain, (![D_418, B_419]: (r2_hidden(D_418, k9_relat_1('#skF_10', B_419)) | ~r2_hidden('#skF_11'(D_418), B_419) | ~r2_hidden('#skF_11'(D_418), '#skF_8') | ~r2_hidden(D_418, '#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_199, c_94, c_1720, c_1782])).
% 4.79/1.82  tff(c_1789, plain, (![D_420]: (r2_hidden(D_420, k9_relat_1('#skF_10', '#skF_8')) | ~r2_hidden('#skF_11'(D_420), '#skF_8') | ~r2_hidden(D_420, '#skF_9'))), inference(resolution, [status(thm)], [c_98, c_1785])).
% 4.79/1.82  tff(c_1793, plain, (![D_89]: (r2_hidden(D_89, k9_relat_1('#skF_10', '#skF_8')) | ~r2_hidden(D_89, '#skF_9'))), inference(resolution, [status(thm)], [c_98, c_1789])).
% 4.79/1.82  tff(c_26, plain, (![A_12, B_13, C_14]: (r2_hidden(k4_tarski('#skF_1'(A_12, B_13, C_14), A_12), C_14) | ~r2_hidden(A_12, k9_relat_1(C_14, B_13)) | ~v1_relat_1(C_14))), inference(cnfTransformation, [status(thm)], [f_63])).
% 4.79/1.82  tff(c_1794, plain, (![E_421, A_422, B_423, C_424]: (~r2_hidden(k4_tarski(E_421, '#skF_6'(A_422, B_423, C_424)), C_424) | k2_relset_1(A_422, B_423, C_424)=B_423 | ~m1_subset_1(C_424, k1_zfmisc_1(k2_zfmisc_1(A_422, B_423))))), inference(cnfTransformation, [status(thm)], [f_117])).
% 4.79/1.82  tff(c_1940, plain, (![A_456, B_457, C_458, B_459]: (k2_relset_1(A_456, B_457, C_458)=B_457 | ~m1_subset_1(C_458, k1_zfmisc_1(k2_zfmisc_1(A_456, B_457))) | ~r2_hidden('#skF_6'(A_456, B_457, C_458), k9_relat_1(C_458, B_459)) | ~v1_relat_1(C_458))), inference(resolution, [status(thm)], [c_26, c_1794])).
% 4.79/1.82  tff(c_1948, plain, (![A_456, B_457]: (k2_relset_1(A_456, B_457, '#skF_10')=B_457 | ~m1_subset_1('#skF_10', k1_zfmisc_1(k2_zfmisc_1(A_456, B_457))) | ~v1_relat_1('#skF_10') | ~r2_hidden('#skF_6'(A_456, B_457, '#skF_10'), '#skF_9'))), inference(resolution, [status(thm)], [c_1793, c_1940])).
% 4.79/1.82  tff(c_1961, plain, (![A_460, B_461]: (k2_relset_1(A_460, B_461, '#skF_10')=B_461 | ~m1_subset_1('#skF_10', k1_zfmisc_1(k2_zfmisc_1(A_460, B_461))) | ~r2_hidden('#skF_6'(A_460, B_461, '#skF_10'), '#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_199, c_1948])).
% 4.79/1.82  tff(c_1964, plain, (k2_relset_1('#skF_8', '#skF_9', '#skF_10')='#skF_9' | ~r2_hidden('#skF_6'('#skF_8', '#skF_9', '#skF_10'), '#skF_9')), inference(resolution, [status(thm)], [c_90, c_1961])).
% 4.79/1.82  tff(c_1973, plain, (k2_relat_1('#skF_10')='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_1746, c_315, c_1964])).
% 4.79/1.82  tff(c_1975, plain, $false, inference(negUnitSimplification, [status(thm)], [c_316, c_1973])).
% 4.79/1.82  tff(c_1976, plain, (k1_xboole_0='#skF_9'), inference(splitRight, [status(thm)], [c_1718])).
% 4.79/1.82  tff(c_10, plain, (![A_3]: (k2_zfmisc_1(A_3, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.79/1.82  tff(c_2008, plain, (![A_3]: (k2_zfmisc_1(A_3, '#skF_9')='#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_1976, c_1976, c_10])).
% 4.79/1.82  tff(c_2108, plain, (m1_subset_1('#skF_10', k1_zfmisc_1('#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_2008, c_90])).
% 4.79/1.82  tff(c_12, plain, (![B_4]: (k2_zfmisc_1(k1_xboole_0, B_4)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.79/1.82  tff(c_210, plain, (![C_106, B_107, A_108]: (v5_relat_1(C_106, B_107) | ~m1_subset_1(C_106, k1_zfmisc_1(k2_zfmisc_1(A_108, B_107))))), inference(cnfTransformation, [status(thm)], [f_97])).
% 4.79/1.82  tff(c_219, plain, (![C_106, B_4]: (v5_relat_1(C_106, B_4) | ~m1_subset_1(C_106, k1_zfmisc_1(k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_210])).
% 4.79/1.82  tff(c_2262, plain, (![C_490, B_491]: (v5_relat_1(C_490, B_491) | ~m1_subset_1(C_490, k1_zfmisc_1('#skF_9')))), inference(demodulation, [status(thm), theory('equality')], [c_1976, c_219])).
% 4.79/1.82  tff(c_2267, plain, (![B_491]: (v5_relat_1('#skF_10', B_491))), inference(resolution, [status(thm)], [c_2108, c_2262])).
% 4.79/1.82  tff(c_420, plain, (![A_167, B_168, C_169]: (r2_hidden('#skF_6'(A_167, B_168, C_169), B_168) | k2_relset_1(A_167, B_168, C_169)=B_168 | ~m1_subset_1(C_169, k1_zfmisc_1(k2_zfmisc_1(A_167, B_168))))), inference(cnfTransformation, [status(thm)], [f_117])).
% 4.79/1.82  tff(c_422, plain, (r2_hidden('#skF_6'('#skF_8', '#skF_9', '#skF_10'), '#skF_9') | k2_relset_1('#skF_8', '#skF_9', '#skF_10')='#skF_9'), inference(resolution, [status(thm)], [c_90, c_420])).
% 4.79/1.82  tff(c_428, plain, (r2_hidden('#skF_6'('#skF_8', '#skF_9', '#skF_10'), '#skF_9') | k2_relat_1('#skF_10')='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_315, c_422])).
% 4.79/1.82  tff(c_429, plain, (r2_hidden('#skF_6'('#skF_8', '#skF_9', '#skF_10'), '#skF_9')), inference(negUnitSimplification, [status(thm)], [c_316, c_428])).
% 4.79/1.82  tff(c_325, plain, (![A_137, B_138, C_139]: (k1_relset_1(A_137, B_138, C_139)=k1_relat_1(C_139) | ~m1_subset_1(C_139, k1_zfmisc_1(k2_zfmisc_1(A_137, B_138))))), inference(cnfTransformation, [status(thm)], [f_101])).
% 4.79/1.82  tff(c_335, plain, (k1_relset_1('#skF_8', '#skF_9', '#skF_10')=k1_relat_1('#skF_10')), inference(resolution, [status(thm)], [c_90, c_325])).
% 4.79/1.82  tff(c_389, plain, (![B_162, A_163, C_164]: (k1_xboole_0=B_162 | k1_relset_1(A_163, B_162, C_164)=A_163 | ~v1_funct_2(C_164, A_163, B_162) | ~m1_subset_1(C_164, k1_zfmisc_1(k2_zfmisc_1(A_163, B_162))))), inference(cnfTransformation, [status(thm)], [f_135])).
% 4.79/1.82  tff(c_392, plain, (k1_xboole_0='#skF_9' | k1_relset_1('#skF_8', '#skF_9', '#skF_10')='#skF_8' | ~v1_funct_2('#skF_10', '#skF_8', '#skF_9')), inference(resolution, [status(thm)], [c_90, c_389])).
% 4.79/1.82  tff(c_401, plain, (k1_xboole_0='#skF_9' | k1_relat_1('#skF_10')='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_92, c_335, c_392])).
% 4.79/1.82  tff(c_403, plain, (k1_relat_1('#skF_10')='#skF_8'), inference(splitLeft, [status(thm)], [c_401])).
% 4.79/1.82  tff(c_479, plain, (![A_183, E_184, B_185]: (r2_hidden(k1_funct_1(A_183, E_184), k9_relat_1(A_183, B_185)) | ~r2_hidden(E_184, B_185) | ~r2_hidden(E_184, k1_relat_1(A_183)) | ~v1_funct_1(A_183) | ~v1_relat_1(A_183))), inference(cnfTransformation, [status(thm)], [f_91])).
% 4.79/1.82  tff(c_482, plain, (![D_89, B_185]: (r2_hidden(D_89, k9_relat_1('#skF_10', B_185)) | ~r2_hidden('#skF_11'(D_89), B_185) | ~r2_hidden('#skF_11'(D_89), k1_relat_1('#skF_10')) | ~v1_funct_1('#skF_10') | ~v1_relat_1('#skF_10') | ~r2_hidden(D_89, '#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_96, c_479])).
% 4.79/1.82  tff(c_485, plain, (![D_186, B_187]: (r2_hidden(D_186, k9_relat_1('#skF_10', B_187)) | ~r2_hidden('#skF_11'(D_186), B_187) | ~r2_hidden('#skF_11'(D_186), '#skF_8') | ~r2_hidden(D_186, '#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_199, c_94, c_403, c_482])).
% 4.79/1.82  tff(c_500, plain, (![D_191]: (r2_hidden(D_191, k9_relat_1('#skF_10', '#skF_8')) | ~r2_hidden('#skF_11'(D_191), '#skF_8') | ~r2_hidden(D_191, '#skF_9'))), inference(resolution, [status(thm)], [c_98, c_485])).
% 4.79/1.82  tff(c_504, plain, (![D_89]: (r2_hidden(D_89, k9_relat_1('#skF_10', '#skF_8')) | ~r2_hidden(D_89, '#skF_9'))), inference(resolution, [status(thm)], [c_98, c_500])).
% 4.79/1.82  tff(c_575, plain, (![E_203, A_204, B_205, C_206]: (~r2_hidden(k4_tarski(E_203, '#skF_6'(A_204, B_205, C_206)), C_206) | k2_relset_1(A_204, B_205, C_206)=B_205 | ~m1_subset_1(C_206, k1_zfmisc_1(k2_zfmisc_1(A_204, B_205))))), inference(cnfTransformation, [status(thm)], [f_117])).
% 4.79/1.82  tff(c_634, plain, (![A_221, B_222, C_223, B_224]: (k2_relset_1(A_221, B_222, C_223)=B_222 | ~m1_subset_1(C_223, k1_zfmisc_1(k2_zfmisc_1(A_221, B_222))) | ~r2_hidden('#skF_6'(A_221, B_222, C_223), k9_relat_1(C_223, B_224)) | ~v1_relat_1(C_223))), inference(resolution, [status(thm)], [c_26, c_575])).
% 4.79/1.82  tff(c_642, plain, (![A_221, B_222]: (k2_relset_1(A_221, B_222, '#skF_10')=B_222 | ~m1_subset_1('#skF_10', k1_zfmisc_1(k2_zfmisc_1(A_221, B_222))) | ~v1_relat_1('#skF_10') | ~r2_hidden('#skF_6'(A_221, B_222, '#skF_10'), '#skF_9'))), inference(resolution, [status(thm)], [c_504, c_634])).
% 4.79/1.82  tff(c_655, plain, (![A_225, B_226]: (k2_relset_1(A_225, B_226, '#skF_10')=B_226 | ~m1_subset_1('#skF_10', k1_zfmisc_1(k2_zfmisc_1(A_225, B_226))) | ~r2_hidden('#skF_6'(A_225, B_226, '#skF_10'), '#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_199, c_642])).
% 4.79/1.82  tff(c_658, plain, (k2_relset_1('#skF_8', '#skF_9', '#skF_10')='#skF_9' | ~r2_hidden('#skF_6'('#skF_8', '#skF_9', '#skF_10'), '#skF_9')), inference(resolution, [status(thm)], [c_90, c_655])).
% 4.79/1.82  tff(c_667, plain, (k2_relat_1('#skF_10')='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_429, c_315, c_658])).
% 4.79/1.82  tff(c_669, plain, $false, inference(negUnitSimplification, [status(thm)], [c_316, c_667])).
% 4.79/1.82  tff(c_670, plain, (k1_xboole_0='#skF_9'), inference(splitRight, [status(thm)], [c_401])).
% 4.79/1.82  tff(c_76, plain, (![A_83]: (v1_funct_2(k1_xboole_0, A_83, k1_xboole_0) | k1_xboole_0=A_83 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k2_zfmisc_1(A_83, k1_xboole_0))))), inference(cnfTransformation, [status(thm)], [f_135])).
% 4.79/1.82  tff(c_101, plain, (![A_83]: (v1_funct_2(k1_xboole_0, A_83, k1_xboole_0) | k1_xboole_0=A_83 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_76])).
% 4.79/1.82  tff(c_321, plain, (~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_xboole_0))), inference(splitLeft, [status(thm)], [c_101])).
% 4.79/1.82  tff(c_682, plain, (~m1_subset_1('#skF_9', k1_zfmisc_1('#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_670, c_670, c_321])).
% 4.79/1.82  tff(c_671, plain, (k1_relat_1('#skF_10')!='#skF_8'), inference(splitRight, [status(thm)], [c_401])).
% 4.79/1.82  tff(c_695, plain, (![A_3]: (k2_zfmisc_1(A_3, '#skF_9')='#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_670, c_670, c_10])).
% 4.79/1.82  tff(c_744, plain, (m1_subset_1('#skF_10', k1_zfmisc_1('#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_695, c_90])).
% 4.79/1.82  tff(c_78, plain, (![C_85, A_83]: (k1_xboole_0=C_85 | ~v1_funct_2(C_85, A_83, k1_xboole_0) | k1_xboole_0=A_83 | ~m1_subset_1(C_85, k1_zfmisc_1(k2_zfmisc_1(A_83, k1_xboole_0))))), inference(cnfTransformation, [status(thm)], [f_135])).
% 4.79/1.82  tff(c_102, plain, (![C_85, A_83]: (k1_xboole_0=C_85 | ~v1_funct_2(C_85, A_83, k1_xboole_0) | k1_xboole_0=A_83 | ~m1_subset_1(C_85, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_78])).
% 4.79/1.82  tff(c_1057, plain, (![C_289, A_290]: (C_289='#skF_9' | ~v1_funct_2(C_289, A_290, '#skF_9') | A_290='#skF_9' | ~m1_subset_1(C_289, k1_zfmisc_1('#skF_9')))), inference(demodulation, [status(thm), theory('equality')], [c_670, c_670, c_670, c_670, c_102])).
% 4.79/1.82  tff(c_1059, plain, ('#skF_10'='#skF_9' | '#skF_9'='#skF_8' | ~m1_subset_1('#skF_10', k1_zfmisc_1('#skF_9'))), inference(resolution, [status(thm)], [c_92, c_1057])).
% 4.79/1.82  tff(c_1062, plain, ('#skF_10'='#skF_9' | '#skF_9'='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_744, c_1059])).
% 4.79/1.82  tff(c_1063, plain, ('#skF_9'='#skF_8'), inference(splitLeft, [status(thm)], [c_1062])).
% 4.79/1.82  tff(c_1088, plain, (m1_subset_1('#skF_10', k1_zfmisc_1('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_1063, c_744])).
% 4.79/1.82  tff(c_331, plain, (![A_3, C_139]: (k1_relset_1(A_3, k1_xboole_0, C_139)=k1_relat_1(C_139) | ~m1_subset_1(C_139, k1_zfmisc_1(k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_325])).
% 4.79/1.82  tff(c_954, plain, (![A_264, C_265]: (k1_relset_1(A_264, '#skF_9', C_265)=k1_relat_1(C_265) | ~m1_subset_1(C_265, k1_zfmisc_1('#skF_9')))), inference(demodulation, [status(thm), theory('equality')], [c_670, c_670, c_331])).
% 4.79/1.82  tff(c_957, plain, (![A_264]: (k1_relset_1(A_264, '#skF_9', '#skF_10')=k1_relat_1('#skF_10'))), inference(resolution, [status(thm)], [c_744, c_954])).
% 4.79/1.82  tff(c_1072, plain, (![A_264]: (k1_relset_1(A_264, '#skF_8', '#skF_10')=k1_relat_1('#skF_10'))), inference(demodulation, [status(thm), theory('equality')], [c_1063, c_957])).
% 4.79/1.82  tff(c_1101, plain, (v1_funct_2('#skF_10', '#skF_8', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_1063, c_92])).
% 4.79/1.82  tff(c_84, plain, (![B_84, C_85]: (k1_relset_1(k1_xboole_0, B_84, C_85)=k1_xboole_0 | ~v1_funct_2(C_85, k1_xboole_0, B_84) | ~m1_subset_1(C_85, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_84))))), inference(cnfTransformation, [status(thm)], [f_135])).
% 4.79/1.82  tff(c_99, plain, (![B_84, C_85]: (k1_relset_1(k1_xboole_0, B_84, C_85)=k1_xboole_0 | ~v1_funct_2(C_85, k1_xboole_0, B_84) | ~m1_subset_1(C_85, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_84])).
% 4.79/1.82  tff(c_674, plain, (![B_84, C_85]: (k1_relset_1('#skF_9', B_84, C_85)='#skF_9' | ~v1_funct_2(C_85, '#skF_9', B_84) | ~m1_subset_1(C_85, k1_zfmisc_1('#skF_9')))), inference(demodulation, [status(thm), theory('equality')], [c_670, c_670, c_670, c_670, c_99])).
% 4.79/1.82  tff(c_1476, plain, (![B_352, C_353]: (k1_relset_1('#skF_8', B_352, C_353)='#skF_8' | ~v1_funct_2(C_353, '#skF_8', B_352) | ~m1_subset_1(C_353, k1_zfmisc_1('#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_1063, c_1063, c_1063, c_1063, c_674])).
% 4.79/1.82  tff(c_1478, plain, (k1_relset_1('#skF_8', '#skF_8', '#skF_10')='#skF_8' | ~m1_subset_1('#skF_10', k1_zfmisc_1('#skF_8'))), inference(resolution, [status(thm)], [c_1101, c_1476])).
% 4.79/1.82  tff(c_1481, plain, (k1_relat_1('#skF_10')='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_1088, c_1072, c_1478])).
% 4.79/1.82  tff(c_1483, plain, $false, inference(negUnitSimplification, [status(thm)], [c_671, c_1481])).
% 4.79/1.82  tff(c_1484, plain, ('#skF_10'='#skF_9'), inference(splitRight, [status(thm)], [c_1062])).
% 4.79/1.82  tff(c_1494, plain, (m1_subset_1('#skF_9', k1_zfmisc_1('#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_1484, c_744])).
% 4.79/1.82  tff(c_1510, plain, $false, inference(negUnitSimplification, [status(thm)], [c_682, c_1494])).
% 4.79/1.82  tff(c_1512, plain, (m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_xboole_0))), inference(splitRight, [status(thm)], [c_101])).
% 4.79/1.82  tff(c_1521, plain, (![B_4]: (v5_relat_1(k1_xboole_0, B_4))), inference(resolution, [status(thm)], [c_1512, c_219])).
% 4.79/1.82  tff(c_120, plain, (![A_93, B_94]: (v1_relat_1(k2_zfmisc_1(A_93, B_94)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 4.79/1.82  tff(c_122, plain, (v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_12, c_120])).
% 4.79/1.82  tff(c_30, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_66])).
% 4.79/1.82  tff(c_253, plain, (![B_121, A_122]: (r1_tarski(k2_relat_1(B_121), A_122) | ~v5_relat_1(B_121, A_122) | ~v1_relat_1(B_121))), inference(cnfTransformation, [status(thm)], [f_50])).
% 4.79/1.82  tff(c_261, plain, (![A_122]: (r1_tarski(k1_xboole_0, A_122) | ~v5_relat_1(k1_xboole_0, A_122) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_30, c_253])).
% 4.79/1.82  tff(c_265, plain, (![A_122]: (r1_tarski(k1_xboole_0, A_122) | ~v5_relat_1(k1_xboole_0, A_122))), inference(demodulation, [status(thm), theory('equality')], [c_122, c_261])).
% 4.79/1.82  tff(c_1528, plain, (![A_122]: (r1_tarski(k1_xboole_0, A_122))), inference(demodulation, [status(thm), theory('equality')], [c_1521, c_265])).
% 4.79/1.82  tff(c_2059, plain, (![A_467]: (r1_tarski('#skF_9', A_467))), inference(demodulation, [status(thm), theory('equality')], [c_1976, c_1528])).
% 4.79/1.82  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.79/1.82  tff(c_263, plain, (![B_121, A_122]: (k2_relat_1(B_121)=A_122 | ~r1_tarski(A_122, k2_relat_1(B_121)) | ~v5_relat_1(B_121, A_122) | ~v1_relat_1(B_121))), inference(resolution, [status(thm)], [c_253, c_2])).
% 4.79/1.82  tff(c_2330, plain, (![B_506]: (k2_relat_1(B_506)='#skF_9' | ~v5_relat_1(B_506, '#skF_9') | ~v1_relat_1(B_506))), inference(resolution, [status(thm)], [c_2059, c_263])).
% 4.79/1.82  tff(c_2334, plain, (k2_relat_1('#skF_10')='#skF_9' | ~v1_relat_1('#skF_10')), inference(resolution, [status(thm)], [c_2267, c_2330])).
% 4.79/1.82  tff(c_2341, plain, (k2_relat_1('#skF_10')='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_199, c_2334])).
% 4.79/1.82  tff(c_2343, plain, $false, inference(negUnitSimplification, [status(thm)], [c_316, c_2341])).
% 4.79/1.82  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.79/1.82  
% 4.79/1.82  Inference rules
% 4.79/1.82  ----------------------
% 4.79/1.82  #Ref     : 0
% 4.79/1.82  #Sup     : 479
% 4.79/1.82  #Fact    : 0
% 4.79/1.82  #Define  : 0
% 4.79/1.82  #Split   : 8
% 4.79/1.82  #Chain   : 0
% 4.79/1.82  #Close   : 0
% 4.79/1.82  
% 4.79/1.82  Ordering : KBO
% 4.79/1.82  
% 4.79/1.82  Simplification rules
% 4.79/1.82  ----------------------
% 4.79/1.82  #Subsume      : 65
% 4.79/1.82  #Demod        : 470
% 4.79/1.82  #Tautology    : 227
% 4.79/1.82  #SimpNegUnit  : 9
% 4.79/1.82  #BackRed      : 126
% 4.79/1.82  
% 4.79/1.82  #Partial instantiations: 0
% 4.79/1.82  #Strategies tried      : 1
% 4.79/1.82  
% 4.79/1.82  Timing (in seconds)
% 4.79/1.82  ----------------------
% 4.79/1.83  Preprocessing        : 0.37
% 4.79/1.83  Parsing              : 0.19
% 4.79/1.83  CNF conversion       : 0.03
% 4.79/1.83  Main loop            : 0.66
% 4.79/1.83  Inferencing          : 0.24
% 4.79/1.83  Reduction            : 0.22
% 4.79/1.83  Demodulation         : 0.15
% 4.79/1.83  BG Simplification    : 0.04
% 4.79/1.83  Subsumption          : 0.12
% 4.79/1.83  Abstraction          : 0.03
% 4.79/1.83  MUC search           : 0.00
% 4.79/1.83  Cooper               : 0.00
% 4.79/1.83  Total                : 1.08
% 4.79/1.83  Index Insertion      : 0.00
% 4.79/1.83  Index Deletion       : 0.00
% 4.79/1.83  Index Matching       : 0.00
% 4.79/1.83  BG Taut test         : 0.00
%------------------------------------------------------------------------------
