%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:16:40 EST 2020

% Result     : Theorem 6.08s
% Output     : CNFRefutation 6.08s
% Verified   : 
% Statistics : Number of formulae       :  114 ( 275 expanded)
%              Number of leaves         :   44 ( 110 expanded)
%              Depth                    :   11
%              Number of atoms          :  175 ( 660 expanded)
%              Number of equality atoms :   18 ( 122 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v1_partfun1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k4_tarski > k2_zfmisc_1 > k1_funct_2 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_6 > #skF_13 > #skF_15 > #skF_1 > #skF_12 > #skF_3 > #skF_16 > #skF_14 > #skF_5 > #skF_8 > #skF_11 > #skF_9 > #skF_2 > #skF_7 > #skF_4 > #skF_10

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff('#skF_13',type,(
    '#skF_13': ( $i * $i * $i * $i ) > $i )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_15',type,(
    '#skF_15': $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff('#skF_12',type,(
    '#skF_12': ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_16',type,(
    '#skF_16': $i )).

tff('#skF_14',type,(
    '#skF_14': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff(v1_partfun1,type,(
    v1_partfun1: ( $i * $i ) > $o )).

tff('#skF_8',type,(
    '#skF_8': ( $i * $i ) > $i )).

tff('#skF_11',type,(
    '#skF_11': ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#skF_9',type,(
    '#skF_9': ( $i * $i * $i ) > $i )).

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

tff('#skF_7',type,(
    '#skF_7': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff('#skF_10',type,(
    '#skF_10': ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_127,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r2_hidden(C,k1_funct_2(A,B))
       => ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t121_funct_2)).

tff(f_108,axiom,(
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

tff(f_37,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_61,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( ( r1_tarski(k1_relat_1(C),A)
          & r1_tarski(k2_relat_1(C),B) )
       => m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_relset_1)).

tff(f_78,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => v1_partfun1(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_partfun1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_45,axiom,(
    ! [A,B] :
      ( B = k1_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(C,D),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( B = k2_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(D,C),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_relat_1)).

tff(f_71,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( ( v1_funct_1(C)
          & v1_partfun1(C,A) )
       => ( v1_funct_1(C)
          & v1_funct_2(C,A,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_funct_2)).

tff(f_118,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_funct_1(A)
        & v1_funct_2(A,k1_relat_1(A),k2_relat_1(A))
        & m1_subset_1(A,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A)))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_funct_2)).

tff(f_92,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => ( ( v1_funct_1(C)
              & v1_funct_2(C,A,B) )
           => ( v1_funct_1(C)
              & v1_partfun1(C,A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc5_funct_2)).

tff(c_92,plain,(
    r2_hidden('#skF_16',k1_funct_2('#skF_14','#skF_15')) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_259,plain,(
    ! [A_138,B_139,D_140] :
      ( '#skF_13'(A_138,B_139,k1_funct_2(A_138,B_139),D_140) = D_140
      | ~ r2_hidden(D_140,k1_funct_2(A_138,B_139)) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_270,plain,(
    '#skF_13'('#skF_14','#skF_15',k1_funct_2('#skF_14','#skF_15'),'#skF_16') = '#skF_16' ),
    inference(resolution,[status(thm)],[c_92,c_259])).

tff(c_58,plain,(
    ! [A_59,B_60,D_75] :
      ( v1_relat_1('#skF_13'(A_59,B_60,k1_funct_2(A_59,B_60),D_75))
      | ~ r2_hidden(D_75,k1_funct_2(A_59,B_60)) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_275,plain,
    ( v1_relat_1('#skF_16')
    | ~ r2_hidden('#skF_16',k1_funct_2('#skF_14','#skF_15')) ),
    inference(superposition,[status(thm),theory(equality)],[c_270,c_58])).

tff(c_279,plain,(
    v1_relat_1('#skF_16') ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_275])).

tff(c_10,plain,(
    ! [B_6] : r1_tarski(B_6,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_501,plain,(
    ! [A_179,B_180,D_181] :
      ( k1_relat_1('#skF_13'(A_179,B_180,k1_funct_2(A_179,B_180),D_181)) = A_179
      | ~ r2_hidden(D_181,k1_funct_2(A_179,B_180)) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_552,plain,
    ( k1_relat_1('#skF_16') = '#skF_14'
    | ~ r2_hidden('#skF_16',k1_funct_2('#skF_14','#skF_15')) ),
    inference(superposition,[status(thm),theory(equality)],[c_270,c_501])).

tff(c_556,plain,(
    k1_relat_1('#skF_16') = '#skF_14' ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_552])).

tff(c_1063,plain,(
    ! [A_232,B_233,D_234] :
      ( r1_tarski(k2_relat_1('#skF_13'(A_232,B_233,k1_funct_2(A_232,B_233),D_234)),B_233)
      | ~ r2_hidden(D_234,k1_funct_2(A_232,B_233)) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_1068,plain,
    ( r1_tarski(k2_relat_1('#skF_16'),'#skF_15')
    | ~ r2_hidden('#skF_16',k1_funct_2('#skF_14','#skF_15')) ),
    inference(superposition,[status(thm),theory(equality)],[c_270,c_1063])).

tff(c_1071,plain,(
    r1_tarski(k2_relat_1('#skF_16'),'#skF_15') ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_1068])).

tff(c_1661,plain,(
    ! [C_266,A_267,B_268] :
      ( m1_subset_1(C_266,k1_zfmisc_1(k2_zfmisc_1(A_267,B_268)))
      | ~ r1_tarski(k2_relat_1(C_266),B_268)
      | ~ r1_tarski(k1_relat_1(C_266),A_267)
      | ~ v1_relat_1(C_266) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_90,plain,
    ( ~ m1_subset_1('#skF_16',k1_zfmisc_1(k2_zfmisc_1('#skF_14','#skF_15')))
    | ~ v1_funct_2('#skF_16','#skF_14','#skF_15')
    | ~ v1_funct_1('#skF_16') ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_115,plain,(
    ~ v1_funct_1('#skF_16') ),
    inference(splitLeft,[status(thm)],[c_90])).

tff(c_186,plain,(
    ! [A_118,B_119,D_120] :
      ( '#skF_13'(A_118,B_119,k1_funct_2(A_118,B_119),D_120) = D_120
      | ~ r2_hidden(D_120,k1_funct_2(A_118,B_119)) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_197,plain,(
    '#skF_13'('#skF_14','#skF_15',k1_funct_2('#skF_14','#skF_15'),'#skF_16') = '#skF_16' ),
    inference(resolution,[status(thm)],[c_92,c_186])).

tff(c_56,plain,(
    ! [A_59,B_60,D_75] :
      ( v1_funct_1('#skF_13'(A_59,B_60,k1_funct_2(A_59,B_60),D_75))
      | ~ r2_hidden(D_75,k1_funct_2(A_59,B_60)) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_201,plain,
    ( v1_funct_1('#skF_16')
    | ~ r2_hidden('#skF_16',k1_funct_2('#skF_14','#skF_15')) ),
    inference(superposition,[status(thm),theory(equality)],[c_197,c_56])).

tff(c_208,plain,(
    v1_funct_1('#skF_16') ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_201])).

tff(c_210,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_115,c_208])).

tff(c_211,plain,
    ( ~ v1_funct_2('#skF_16','#skF_14','#skF_15')
    | ~ m1_subset_1('#skF_16',k1_zfmisc_1(k2_zfmisc_1('#skF_14','#skF_15'))) ),
    inference(splitRight,[status(thm)],[c_90])).

tff(c_213,plain,(
    ~ m1_subset_1('#skF_16',k1_zfmisc_1(k2_zfmisc_1('#skF_14','#skF_15'))) ),
    inference(splitLeft,[status(thm)],[c_211])).

tff(c_1670,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_16'),'#skF_15')
    | ~ r1_tarski(k1_relat_1('#skF_16'),'#skF_14')
    | ~ v1_relat_1('#skF_16') ),
    inference(resolution,[status(thm)],[c_1661,c_213])).

tff(c_1676,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_279,c_10,c_556,c_1071,c_1670])).

tff(c_1677,plain,(
    ~ v1_funct_2('#skF_16','#skF_14','#skF_15') ),
    inference(splitRight,[status(thm)],[c_211])).

tff(c_212,plain,(
    v1_funct_1('#skF_16') ),
    inference(splitRight,[status(thm)],[c_90])).

tff(c_1678,plain,(
    m1_subset_1('#skF_16',k1_zfmisc_1(k2_zfmisc_1('#skF_14','#skF_15'))) ),
    inference(splitRight,[status(thm)],[c_211])).

tff(c_1679,plain,(
    ! [C_269,A_270,B_271] :
      ( v1_partfun1(C_269,A_270)
      | ~ m1_subset_1(C_269,k1_zfmisc_1(k2_zfmisc_1(A_270,B_271)))
      | ~ v1_xboole_0(A_270) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_1683,plain,
    ( v1_partfun1('#skF_16','#skF_14')
    | ~ v1_xboole_0('#skF_14') ),
    inference(resolution,[status(thm)],[c_1678,c_1679])).

tff(c_1684,plain,(
    ~ v1_xboole_0('#skF_14') ),
    inference(splitLeft,[status(thm)],[c_1683])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_1755,plain,(
    ! [A_295,B_296,D_297] :
      ( '#skF_13'(A_295,B_296,k1_funct_2(A_295,B_296),D_297) = D_297
      | ~ r2_hidden(D_297,k1_funct_2(A_295,B_296)) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_1766,plain,(
    '#skF_13'('#skF_14','#skF_15',k1_funct_2('#skF_14','#skF_15'),'#skF_16') = '#skF_16' ),
    inference(resolution,[status(thm)],[c_92,c_1755])).

tff(c_1920,plain,(
    ! [A_320,B_321,D_322] :
      ( k1_relat_1('#skF_13'(A_320,B_321,k1_funct_2(A_320,B_321),D_322)) = A_320
      | ~ r2_hidden(D_322,k1_funct_2(A_320,B_321)) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_1959,plain,
    ( k1_relat_1('#skF_16') = '#skF_14'
    | ~ r2_hidden('#skF_16',k1_funct_2('#skF_14','#skF_15')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1766,c_1920])).

tff(c_1963,plain,(
    k1_relat_1('#skF_16') = '#skF_14' ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_1959])).

tff(c_12,plain,(
    ! [C_22,A_7] :
      ( r2_hidden(k4_tarski(C_22,'#skF_5'(A_7,k1_relat_1(A_7),C_22)),A_7)
      | ~ r2_hidden(C_22,k1_relat_1(A_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_1985,plain,(
    ! [C_22] :
      ( r2_hidden(k4_tarski(C_22,'#skF_5'('#skF_16','#skF_14',C_22)),'#skF_16')
      | ~ r2_hidden(C_22,k1_relat_1('#skF_16')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1963,c_12])).

tff(c_2276,plain,(
    ! [C_346] :
      ( r2_hidden(k4_tarski(C_346,'#skF_5'('#skF_16','#skF_14',C_346)),'#skF_16')
      | ~ r2_hidden(C_346,'#skF_14') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1963,c_1985])).

tff(c_26,plain,(
    ! [C_41,A_26,D_44] :
      ( r2_hidden(C_41,k2_relat_1(A_26))
      | ~ r2_hidden(k4_tarski(D_44,C_41),A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_2342,plain,(
    ! [C_355] :
      ( r2_hidden('#skF_5'('#skF_16','#skF_14',C_355),k2_relat_1('#skF_16'))
      | ~ r2_hidden(C_355,'#skF_14') ) ),
    inference(resolution,[status(thm)],[c_2276,c_26])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_2350,plain,(
    ! [C_355] :
      ( ~ v1_xboole_0(k2_relat_1('#skF_16'))
      | ~ r2_hidden(C_355,'#skF_14') ) ),
    inference(resolution,[status(thm)],[c_2342,c_2])).

tff(c_2351,plain,(
    ~ v1_xboole_0(k2_relat_1('#skF_16')) ),
    inference(splitLeft,[status(thm)],[c_2350])).

tff(c_2666,plain,(
    ! [C_392,A_393,B_394] :
      ( v1_funct_2(C_392,A_393,B_394)
      | ~ v1_partfun1(C_392,A_393)
      | ~ v1_funct_1(C_392)
      | ~ m1_subset_1(C_392,k1_zfmisc_1(k2_zfmisc_1(A_393,B_394))) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_2675,plain,
    ( v1_funct_2('#skF_16','#skF_14','#skF_15')
    | ~ v1_partfun1('#skF_16','#skF_14')
    | ~ v1_funct_1('#skF_16') ),
    inference(resolution,[status(thm)],[c_1678,c_2666])).

tff(c_2682,plain,
    ( v1_funct_2('#skF_16','#skF_14','#skF_15')
    | ~ v1_partfun1('#skF_16','#skF_14') ),
    inference(demodulation,[status(thm),theory(equality)],[c_212,c_2675])).

tff(c_2683,plain,(
    ~ v1_partfun1('#skF_16','#skF_14') ),
    inference(negUnitSimplification,[status(thm)],[c_1677,c_2682])).

tff(c_1770,plain,
    ( v1_relat_1('#skF_16')
    | ~ r2_hidden('#skF_16',k1_funct_2('#skF_14','#skF_15')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1766,c_58])).

tff(c_1774,plain,(
    v1_relat_1('#skF_16') ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_1770])).

tff(c_86,plain,(
    ! [A_79] :
      ( v1_funct_2(A_79,k1_relat_1(A_79),k2_relat_1(A_79))
      | ~ v1_funct_1(A_79)
      | ~ v1_relat_1(A_79) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_1994,plain,
    ( v1_funct_2('#skF_16','#skF_14',k2_relat_1('#skF_16'))
    | ~ v1_funct_1('#skF_16')
    | ~ v1_relat_1('#skF_16') ),
    inference(superposition,[status(thm),theory(equality)],[c_1963,c_86])).

tff(c_2004,plain,(
    v1_funct_2('#skF_16','#skF_14',k2_relat_1('#skF_16')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1774,c_212,c_1994])).

tff(c_84,plain,(
    ! [A_79] :
      ( m1_subset_1(A_79,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_79),k2_relat_1(A_79))))
      | ~ v1_funct_1(A_79)
      | ~ v1_relat_1(A_79) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_1991,plain,
    ( m1_subset_1('#skF_16',k1_zfmisc_1(k2_zfmisc_1('#skF_14',k2_relat_1('#skF_16'))))
    | ~ v1_funct_1('#skF_16')
    | ~ v1_relat_1('#skF_16') ),
    inference(superposition,[status(thm),theory(equality)],[c_1963,c_84])).

tff(c_2002,plain,(
    m1_subset_1('#skF_16',k1_zfmisc_1(k2_zfmisc_1('#skF_14',k2_relat_1('#skF_16')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1774,c_212,c_1991])).

tff(c_3819,plain,(
    ! [C_444,A_445,B_446] :
      ( v1_partfun1(C_444,A_445)
      | ~ v1_funct_2(C_444,A_445,B_446)
      | ~ v1_funct_1(C_444)
      | ~ m1_subset_1(C_444,k1_zfmisc_1(k2_zfmisc_1(A_445,B_446)))
      | v1_xboole_0(B_446) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_3825,plain,
    ( v1_partfun1('#skF_16','#skF_14')
    | ~ v1_funct_2('#skF_16','#skF_14',k2_relat_1('#skF_16'))
    | ~ v1_funct_1('#skF_16')
    | v1_xboole_0(k2_relat_1('#skF_16')) ),
    inference(resolution,[status(thm)],[c_2002,c_3819])).

tff(c_3835,plain,
    ( v1_partfun1('#skF_16','#skF_14')
    | v1_xboole_0(k2_relat_1('#skF_16')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_212,c_2004,c_3825])).

tff(c_3837,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2351,c_2683,c_3835])).

tff(c_3840,plain,(
    ! [C_447] : ~ r2_hidden(C_447,'#skF_14') ),
    inference(splitRight,[status(thm)],[c_2350])).

tff(c_3856,plain,(
    v1_xboole_0('#skF_14') ),
    inference(resolution,[status(thm)],[c_4,c_3840])).

tff(c_3863,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1684,c_3856])).

tff(c_3864,plain,(
    v1_partfun1('#skF_16','#skF_14') ),
    inference(splitRight,[status(thm)],[c_1683])).

tff(c_5009,plain,(
    ! [C_572,A_573,B_574] :
      ( v1_funct_2(C_572,A_573,B_574)
      | ~ v1_partfun1(C_572,A_573)
      | ~ v1_funct_1(C_572)
      | ~ m1_subset_1(C_572,k1_zfmisc_1(k2_zfmisc_1(A_573,B_574))) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_5018,plain,
    ( v1_funct_2('#skF_16','#skF_14','#skF_15')
    | ~ v1_partfun1('#skF_16','#skF_14')
    | ~ v1_funct_1('#skF_16') ),
    inference(resolution,[status(thm)],[c_1678,c_5009])).

tff(c_5025,plain,(
    v1_funct_2('#skF_16','#skF_14','#skF_15') ),
    inference(demodulation,[status(thm),theory(equality)],[c_212,c_3864,c_5018])).

tff(c_5027,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1677,c_5025])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:28:42 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.08/2.19  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.08/2.20  
% 6.08/2.20  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.08/2.20  %$ v1_funct_2 > v1_partfun1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k4_tarski > k2_zfmisc_1 > k1_funct_2 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_6 > #skF_13 > #skF_15 > #skF_1 > #skF_12 > #skF_3 > #skF_16 > #skF_14 > #skF_5 > #skF_8 > #skF_11 > #skF_9 > #skF_2 > #skF_7 > #skF_4 > #skF_10
% 6.08/2.20  
% 6.08/2.20  %Foreground sorts:
% 6.08/2.20  
% 6.08/2.20  
% 6.08/2.20  %Background operators:
% 6.08/2.20  
% 6.08/2.20  
% 6.08/2.20  %Foreground operators:
% 6.08/2.20  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 6.08/2.20  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 6.08/2.20  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.08/2.20  tff('#skF_13', type, '#skF_13': ($i * $i * $i * $i) > $i).
% 6.08/2.20  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 6.08/2.20  tff('#skF_15', type, '#skF_15': $i).
% 6.08/2.20  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 6.08/2.20  tff('#skF_1', type, '#skF_1': $i > $i).
% 6.08/2.20  tff('#skF_12', type, '#skF_12': ($i * $i * $i) > $i).
% 6.08/2.20  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 6.08/2.20  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.08/2.20  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 6.08/2.20  tff('#skF_16', type, '#skF_16': $i).
% 6.08/2.20  tff('#skF_14', type, '#skF_14': $i).
% 6.08/2.20  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 6.08/2.20  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 6.08/2.20  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 6.08/2.20  tff('#skF_8', type, '#skF_8': ($i * $i) > $i).
% 6.08/2.20  tff('#skF_11', type, '#skF_11': ($i * $i * $i) > $i).
% 6.08/2.20  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 6.08/2.20  tff('#skF_9', type, '#skF_9': ($i * $i * $i) > $i).
% 6.08/2.20  tff(k1_funct_2, type, k1_funct_2: ($i * $i) > $i).
% 6.08/2.20  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.08/2.20  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 6.08/2.20  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 6.08/2.20  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.08/2.20  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 6.08/2.20  tff('#skF_7', type, '#skF_7': ($i * $i) > $i).
% 6.08/2.20  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 6.08/2.20  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 6.08/2.20  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 6.08/2.20  tff('#skF_10', type, '#skF_10': ($i * $i * $i) > $i).
% 6.08/2.20  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 6.08/2.20  
% 6.08/2.22  tff(f_127, negated_conjecture, ~(![A, B, C]: (r2_hidden(C, k1_funct_2(A, B)) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t121_funct_2)).
% 6.08/2.22  tff(f_108, axiom, (![A, B, C]: ((C = k1_funct_2(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (?[E]: ((((v1_relat_1(E) & v1_funct_1(E)) & (D = E)) & (k1_relat_1(E) = A)) & r1_tarski(k2_relat_1(E), B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_funct_2)).
% 6.08/2.22  tff(f_37, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 6.08/2.22  tff(f_61, axiom, (![A, B, C]: (v1_relat_1(C) => ((r1_tarski(k1_relat_1(C), A) & r1_tarski(k2_relat_1(C), B)) => m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_relset_1)).
% 6.08/2.22  tff(f_78, axiom, (![A, B]: (v1_xboole_0(A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_partfun1(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_partfun1)).
% 6.08/2.22  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 6.08/2.22  tff(f_45, axiom, (![A, B]: ((B = k1_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(C, D), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_relat_1)).
% 6.08/2.22  tff(f_53, axiom, (![A, B]: ((B = k2_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(D, C), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_relat_1)).
% 6.08/2.22  tff(f_71, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v1_partfun1(C, A)) => (v1_funct_1(C) & v1_funct_2(C, A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_funct_2)).
% 6.08/2.22  tff(f_118, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => ((v1_funct_1(A) & v1_funct_2(A, k1_relat_1(A), k2_relat_1(A))) & m1_subset_1(A, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_funct_2)).
% 6.08/2.22  tff(f_92, axiom, (![A, B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) => (v1_funct_1(C) & v1_partfun1(C, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc5_funct_2)).
% 6.08/2.22  tff(c_92, plain, (r2_hidden('#skF_16', k1_funct_2('#skF_14', '#skF_15'))), inference(cnfTransformation, [status(thm)], [f_127])).
% 6.08/2.22  tff(c_259, plain, (![A_138, B_139, D_140]: ('#skF_13'(A_138, B_139, k1_funct_2(A_138, B_139), D_140)=D_140 | ~r2_hidden(D_140, k1_funct_2(A_138, B_139)))), inference(cnfTransformation, [status(thm)], [f_108])).
% 6.08/2.22  tff(c_270, plain, ('#skF_13'('#skF_14', '#skF_15', k1_funct_2('#skF_14', '#skF_15'), '#skF_16')='#skF_16'), inference(resolution, [status(thm)], [c_92, c_259])).
% 6.08/2.22  tff(c_58, plain, (![A_59, B_60, D_75]: (v1_relat_1('#skF_13'(A_59, B_60, k1_funct_2(A_59, B_60), D_75)) | ~r2_hidden(D_75, k1_funct_2(A_59, B_60)))), inference(cnfTransformation, [status(thm)], [f_108])).
% 6.08/2.22  tff(c_275, plain, (v1_relat_1('#skF_16') | ~r2_hidden('#skF_16', k1_funct_2('#skF_14', '#skF_15'))), inference(superposition, [status(thm), theory('equality')], [c_270, c_58])).
% 6.08/2.22  tff(c_279, plain, (v1_relat_1('#skF_16')), inference(demodulation, [status(thm), theory('equality')], [c_92, c_275])).
% 6.08/2.22  tff(c_10, plain, (![B_6]: (r1_tarski(B_6, B_6))), inference(cnfTransformation, [status(thm)], [f_37])).
% 6.08/2.22  tff(c_501, plain, (![A_179, B_180, D_181]: (k1_relat_1('#skF_13'(A_179, B_180, k1_funct_2(A_179, B_180), D_181))=A_179 | ~r2_hidden(D_181, k1_funct_2(A_179, B_180)))), inference(cnfTransformation, [status(thm)], [f_108])).
% 6.08/2.22  tff(c_552, plain, (k1_relat_1('#skF_16')='#skF_14' | ~r2_hidden('#skF_16', k1_funct_2('#skF_14', '#skF_15'))), inference(superposition, [status(thm), theory('equality')], [c_270, c_501])).
% 6.08/2.22  tff(c_556, plain, (k1_relat_1('#skF_16')='#skF_14'), inference(demodulation, [status(thm), theory('equality')], [c_92, c_552])).
% 6.08/2.22  tff(c_1063, plain, (![A_232, B_233, D_234]: (r1_tarski(k2_relat_1('#skF_13'(A_232, B_233, k1_funct_2(A_232, B_233), D_234)), B_233) | ~r2_hidden(D_234, k1_funct_2(A_232, B_233)))), inference(cnfTransformation, [status(thm)], [f_108])).
% 6.08/2.22  tff(c_1068, plain, (r1_tarski(k2_relat_1('#skF_16'), '#skF_15') | ~r2_hidden('#skF_16', k1_funct_2('#skF_14', '#skF_15'))), inference(superposition, [status(thm), theory('equality')], [c_270, c_1063])).
% 6.08/2.22  tff(c_1071, plain, (r1_tarski(k2_relat_1('#skF_16'), '#skF_15')), inference(demodulation, [status(thm), theory('equality')], [c_92, c_1068])).
% 6.08/2.22  tff(c_1661, plain, (![C_266, A_267, B_268]: (m1_subset_1(C_266, k1_zfmisc_1(k2_zfmisc_1(A_267, B_268))) | ~r1_tarski(k2_relat_1(C_266), B_268) | ~r1_tarski(k1_relat_1(C_266), A_267) | ~v1_relat_1(C_266))), inference(cnfTransformation, [status(thm)], [f_61])).
% 6.08/2.22  tff(c_90, plain, (~m1_subset_1('#skF_16', k1_zfmisc_1(k2_zfmisc_1('#skF_14', '#skF_15'))) | ~v1_funct_2('#skF_16', '#skF_14', '#skF_15') | ~v1_funct_1('#skF_16')), inference(cnfTransformation, [status(thm)], [f_127])).
% 6.08/2.22  tff(c_115, plain, (~v1_funct_1('#skF_16')), inference(splitLeft, [status(thm)], [c_90])).
% 6.08/2.22  tff(c_186, plain, (![A_118, B_119, D_120]: ('#skF_13'(A_118, B_119, k1_funct_2(A_118, B_119), D_120)=D_120 | ~r2_hidden(D_120, k1_funct_2(A_118, B_119)))), inference(cnfTransformation, [status(thm)], [f_108])).
% 6.08/2.22  tff(c_197, plain, ('#skF_13'('#skF_14', '#skF_15', k1_funct_2('#skF_14', '#skF_15'), '#skF_16')='#skF_16'), inference(resolution, [status(thm)], [c_92, c_186])).
% 6.08/2.22  tff(c_56, plain, (![A_59, B_60, D_75]: (v1_funct_1('#skF_13'(A_59, B_60, k1_funct_2(A_59, B_60), D_75)) | ~r2_hidden(D_75, k1_funct_2(A_59, B_60)))), inference(cnfTransformation, [status(thm)], [f_108])).
% 6.08/2.22  tff(c_201, plain, (v1_funct_1('#skF_16') | ~r2_hidden('#skF_16', k1_funct_2('#skF_14', '#skF_15'))), inference(superposition, [status(thm), theory('equality')], [c_197, c_56])).
% 6.08/2.22  tff(c_208, plain, (v1_funct_1('#skF_16')), inference(demodulation, [status(thm), theory('equality')], [c_92, c_201])).
% 6.08/2.22  tff(c_210, plain, $false, inference(negUnitSimplification, [status(thm)], [c_115, c_208])).
% 6.08/2.22  tff(c_211, plain, (~v1_funct_2('#skF_16', '#skF_14', '#skF_15') | ~m1_subset_1('#skF_16', k1_zfmisc_1(k2_zfmisc_1('#skF_14', '#skF_15')))), inference(splitRight, [status(thm)], [c_90])).
% 6.08/2.22  tff(c_213, plain, (~m1_subset_1('#skF_16', k1_zfmisc_1(k2_zfmisc_1('#skF_14', '#skF_15')))), inference(splitLeft, [status(thm)], [c_211])).
% 6.08/2.22  tff(c_1670, plain, (~r1_tarski(k2_relat_1('#skF_16'), '#skF_15') | ~r1_tarski(k1_relat_1('#skF_16'), '#skF_14') | ~v1_relat_1('#skF_16')), inference(resolution, [status(thm)], [c_1661, c_213])).
% 6.08/2.22  tff(c_1676, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_279, c_10, c_556, c_1071, c_1670])).
% 6.08/2.22  tff(c_1677, plain, (~v1_funct_2('#skF_16', '#skF_14', '#skF_15')), inference(splitRight, [status(thm)], [c_211])).
% 6.08/2.22  tff(c_212, plain, (v1_funct_1('#skF_16')), inference(splitRight, [status(thm)], [c_90])).
% 6.08/2.22  tff(c_1678, plain, (m1_subset_1('#skF_16', k1_zfmisc_1(k2_zfmisc_1('#skF_14', '#skF_15')))), inference(splitRight, [status(thm)], [c_211])).
% 6.08/2.22  tff(c_1679, plain, (![C_269, A_270, B_271]: (v1_partfun1(C_269, A_270) | ~m1_subset_1(C_269, k1_zfmisc_1(k2_zfmisc_1(A_270, B_271))) | ~v1_xboole_0(A_270))), inference(cnfTransformation, [status(thm)], [f_78])).
% 6.08/2.22  tff(c_1683, plain, (v1_partfun1('#skF_16', '#skF_14') | ~v1_xboole_0('#skF_14')), inference(resolution, [status(thm)], [c_1678, c_1679])).
% 6.08/2.22  tff(c_1684, plain, (~v1_xboole_0('#skF_14')), inference(splitLeft, [status(thm)], [c_1683])).
% 6.08/2.22  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 6.08/2.22  tff(c_1755, plain, (![A_295, B_296, D_297]: ('#skF_13'(A_295, B_296, k1_funct_2(A_295, B_296), D_297)=D_297 | ~r2_hidden(D_297, k1_funct_2(A_295, B_296)))), inference(cnfTransformation, [status(thm)], [f_108])).
% 6.08/2.22  tff(c_1766, plain, ('#skF_13'('#skF_14', '#skF_15', k1_funct_2('#skF_14', '#skF_15'), '#skF_16')='#skF_16'), inference(resolution, [status(thm)], [c_92, c_1755])).
% 6.08/2.22  tff(c_1920, plain, (![A_320, B_321, D_322]: (k1_relat_1('#skF_13'(A_320, B_321, k1_funct_2(A_320, B_321), D_322))=A_320 | ~r2_hidden(D_322, k1_funct_2(A_320, B_321)))), inference(cnfTransformation, [status(thm)], [f_108])).
% 6.08/2.22  tff(c_1959, plain, (k1_relat_1('#skF_16')='#skF_14' | ~r2_hidden('#skF_16', k1_funct_2('#skF_14', '#skF_15'))), inference(superposition, [status(thm), theory('equality')], [c_1766, c_1920])).
% 6.08/2.22  tff(c_1963, plain, (k1_relat_1('#skF_16')='#skF_14'), inference(demodulation, [status(thm), theory('equality')], [c_92, c_1959])).
% 6.08/2.22  tff(c_12, plain, (![C_22, A_7]: (r2_hidden(k4_tarski(C_22, '#skF_5'(A_7, k1_relat_1(A_7), C_22)), A_7) | ~r2_hidden(C_22, k1_relat_1(A_7)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 6.08/2.22  tff(c_1985, plain, (![C_22]: (r2_hidden(k4_tarski(C_22, '#skF_5'('#skF_16', '#skF_14', C_22)), '#skF_16') | ~r2_hidden(C_22, k1_relat_1('#skF_16')))), inference(superposition, [status(thm), theory('equality')], [c_1963, c_12])).
% 6.08/2.22  tff(c_2276, plain, (![C_346]: (r2_hidden(k4_tarski(C_346, '#skF_5'('#skF_16', '#skF_14', C_346)), '#skF_16') | ~r2_hidden(C_346, '#skF_14'))), inference(demodulation, [status(thm), theory('equality')], [c_1963, c_1985])).
% 6.08/2.22  tff(c_26, plain, (![C_41, A_26, D_44]: (r2_hidden(C_41, k2_relat_1(A_26)) | ~r2_hidden(k4_tarski(D_44, C_41), A_26))), inference(cnfTransformation, [status(thm)], [f_53])).
% 6.08/2.22  tff(c_2342, plain, (![C_355]: (r2_hidden('#skF_5'('#skF_16', '#skF_14', C_355), k2_relat_1('#skF_16')) | ~r2_hidden(C_355, '#skF_14'))), inference(resolution, [status(thm)], [c_2276, c_26])).
% 6.08/2.22  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 6.08/2.22  tff(c_2350, plain, (![C_355]: (~v1_xboole_0(k2_relat_1('#skF_16')) | ~r2_hidden(C_355, '#skF_14'))), inference(resolution, [status(thm)], [c_2342, c_2])).
% 6.08/2.22  tff(c_2351, plain, (~v1_xboole_0(k2_relat_1('#skF_16'))), inference(splitLeft, [status(thm)], [c_2350])).
% 6.08/2.22  tff(c_2666, plain, (![C_392, A_393, B_394]: (v1_funct_2(C_392, A_393, B_394) | ~v1_partfun1(C_392, A_393) | ~v1_funct_1(C_392) | ~m1_subset_1(C_392, k1_zfmisc_1(k2_zfmisc_1(A_393, B_394))))), inference(cnfTransformation, [status(thm)], [f_71])).
% 6.08/2.22  tff(c_2675, plain, (v1_funct_2('#skF_16', '#skF_14', '#skF_15') | ~v1_partfun1('#skF_16', '#skF_14') | ~v1_funct_1('#skF_16')), inference(resolution, [status(thm)], [c_1678, c_2666])).
% 6.08/2.22  tff(c_2682, plain, (v1_funct_2('#skF_16', '#skF_14', '#skF_15') | ~v1_partfun1('#skF_16', '#skF_14')), inference(demodulation, [status(thm), theory('equality')], [c_212, c_2675])).
% 6.08/2.22  tff(c_2683, plain, (~v1_partfun1('#skF_16', '#skF_14')), inference(negUnitSimplification, [status(thm)], [c_1677, c_2682])).
% 6.08/2.22  tff(c_1770, plain, (v1_relat_1('#skF_16') | ~r2_hidden('#skF_16', k1_funct_2('#skF_14', '#skF_15'))), inference(superposition, [status(thm), theory('equality')], [c_1766, c_58])).
% 6.08/2.22  tff(c_1774, plain, (v1_relat_1('#skF_16')), inference(demodulation, [status(thm), theory('equality')], [c_92, c_1770])).
% 6.08/2.22  tff(c_86, plain, (![A_79]: (v1_funct_2(A_79, k1_relat_1(A_79), k2_relat_1(A_79)) | ~v1_funct_1(A_79) | ~v1_relat_1(A_79))), inference(cnfTransformation, [status(thm)], [f_118])).
% 6.08/2.22  tff(c_1994, plain, (v1_funct_2('#skF_16', '#skF_14', k2_relat_1('#skF_16')) | ~v1_funct_1('#skF_16') | ~v1_relat_1('#skF_16')), inference(superposition, [status(thm), theory('equality')], [c_1963, c_86])).
% 6.08/2.22  tff(c_2004, plain, (v1_funct_2('#skF_16', '#skF_14', k2_relat_1('#skF_16'))), inference(demodulation, [status(thm), theory('equality')], [c_1774, c_212, c_1994])).
% 6.08/2.22  tff(c_84, plain, (![A_79]: (m1_subset_1(A_79, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_79), k2_relat_1(A_79)))) | ~v1_funct_1(A_79) | ~v1_relat_1(A_79))), inference(cnfTransformation, [status(thm)], [f_118])).
% 6.08/2.22  tff(c_1991, plain, (m1_subset_1('#skF_16', k1_zfmisc_1(k2_zfmisc_1('#skF_14', k2_relat_1('#skF_16')))) | ~v1_funct_1('#skF_16') | ~v1_relat_1('#skF_16')), inference(superposition, [status(thm), theory('equality')], [c_1963, c_84])).
% 6.08/2.22  tff(c_2002, plain, (m1_subset_1('#skF_16', k1_zfmisc_1(k2_zfmisc_1('#skF_14', k2_relat_1('#skF_16'))))), inference(demodulation, [status(thm), theory('equality')], [c_1774, c_212, c_1991])).
% 6.08/2.22  tff(c_3819, plain, (![C_444, A_445, B_446]: (v1_partfun1(C_444, A_445) | ~v1_funct_2(C_444, A_445, B_446) | ~v1_funct_1(C_444) | ~m1_subset_1(C_444, k1_zfmisc_1(k2_zfmisc_1(A_445, B_446))) | v1_xboole_0(B_446))), inference(cnfTransformation, [status(thm)], [f_92])).
% 6.08/2.22  tff(c_3825, plain, (v1_partfun1('#skF_16', '#skF_14') | ~v1_funct_2('#skF_16', '#skF_14', k2_relat_1('#skF_16')) | ~v1_funct_1('#skF_16') | v1_xboole_0(k2_relat_1('#skF_16'))), inference(resolution, [status(thm)], [c_2002, c_3819])).
% 6.08/2.22  tff(c_3835, plain, (v1_partfun1('#skF_16', '#skF_14') | v1_xboole_0(k2_relat_1('#skF_16'))), inference(demodulation, [status(thm), theory('equality')], [c_212, c_2004, c_3825])).
% 6.08/2.22  tff(c_3837, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2351, c_2683, c_3835])).
% 6.08/2.22  tff(c_3840, plain, (![C_447]: (~r2_hidden(C_447, '#skF_14'))), inference(splitRight, [status(thm)], [c_2350])).
% 6.08/2.22  tff(c_3856, plain, (v1_xboole_0('#skF_14')), inference(resolution, [status(thm)], [c_4, c_3840])).
% 6.08/2.22  tff(c_3863, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1684, c_3856])).
% 6.08/2.22  tff(c_3864, plain, (v1_partfun1('#skF_16', '#skF_14')), inference(splitRight, [status(thm)], [c_1683])).
% 6.08/2.22  tff(c_5009, plain, (![C_572, A_573, B_574]: (v1_funct_2(C_572, A_573, B_574) | ~v1_partfun1(C_572, A_573) | ~v1_funct_1(C_572) | ~m1_subset_1(C_572, k1_zfmisc_1(k2_zfmisc_1(A_573, B_574))))), inference(cnfTransformation, [status(thm)], [f_71])).
% 6.08/2.22  tff(c_5018, plain, (v1_funct_2('#skF_16', '#skF_14', '#skF_15') | ~v1_partfun1('#skF_16', '#skF_14') | ~v1_funct_1('#skF_16')), inference(resolution, [status(thm)], [c_1678, c_5009])).
% 6.08/2.22  tff(c_5025, plain, (v1_funct_2('#skF_16', '#skF_14', '#skF_15')), inference(demodulation, [status(thm), theory('equality')], [c_212, c_3864, c_5018])).
% 6.08/2.22  tff(c_5027, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1677, c_5025])).
% 6.08/2.22  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.08/2.22  
% 6.08/2.22  Inference rules
% 6.08/2.22  ----------------------
% 6.08/2.22  #Ref     : 0
% 6.08/2.22  #Sup     : 1045
% 6.08/2.22  #Fact    : 0
% 6.08/2.22  #Define  : 0
% 6.08/2.22  #Split   : 11
% 6.08/2.22  #Chain   : 0
% 6.08/2.22  #Close   : 0
% 6.08/2.22  
% 6.08/2.22  Ordering : KBO
% 6.08/2.22  
% 6.08/2.22  Simplification rules
% 6.08/2.22  ----------------------
% 6.08/2.22  #Subsume      : 148
% 6.08/2.22  #Demod        : 84
% 6.08/2.22  #Tautology    : 63
% 6.08/2.22  #SimpNegUnit  : 6
% 6.08/2.22  #BackRed      : 0
% 6.08/2.22  
% 6.08/2.22  #Partial instantiations: 0
% 6.08/2.22  #Strategies tried      : 1
% 6.08/2.22  
% 6.08/2.22  Timing (in seconds)
% 6.08/2.22  ----------------------
% 6.08/2.22  Preprocessing        : 0.36
% 6.08/2.22  Parsing              : 0.17
% 6.08/2.22  CNF conversion       : 0.03
% 6.08/2.22  Main loop            : 1.09
% 6.08/2.22  Inferencing          : 0.39
% 6.08/2.22  Reduction            : 0.24
% 6.08/2.22  Demodulation         : 0.15
% 6.08/2.22  BG Simplification    : 0.05
% 6.08/2.22  Subsumption          : 0.33
% 6.08/2.22  Abstraction          : 0.06
% 6.08/2.22  MUC search           : 0.00
% 6.08/2.22  Cooper               : 0.00
% 6.08/2.22  Total                : 1.48
% 6.08/2.22  Index Insertion      : 0.00
% 6.08/2.22  Index Deletion       : 0.00
% 6.08/2.22  Index Matching       : 0.00
% 6.08/2.22  BG Taut test         : 0.00
%------------------------------------------------------------------------------
