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
% DateTime   : Thu Dec  3 10:16:41 EST 2020

% Result     : Theorem 8.02s
% Output     : CNFRefutation 8.02s
% Verified   : 
% Statistics : Number of formulae       :  180 (1634 expanded)
%              Number of leaves         :   43 ( 479 expanded)
%              Depth                    :   23
%              Number of atoms          :  314 (3672 expanded)
%              Number of equality atoms :   42 ( 367 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v1_partfun1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_2 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_1 > #skF_4 > #skF_10 > #skF_5 > #skF_6 > #skF_9 > #skF_7 > #skF_8 > #skF_3 > #skF_2

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

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff(v1_partfun1,type,(
    v1_partfun1: ( $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i * $i ) > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff(k1_funct_2,type,(
    k1_funct_2: ( $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_160,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r2_hidden(C,k1_funct_2(A,B))
       => ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t121_funct_2)).

tff(f_124,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_funct_2)).

tff(f_44,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_84,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( ( r1_tarski(k1_relat_1(C),A)
          & r1_tarski(k2_relat_1(C),B) )
       => m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_relset_1)).

tff(f_76,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_72,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k1_relset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_relset_1)).

tff(f_54,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_61,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

tff(f_134,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_funct_1(A)
        & v1_funct_2(A,k1_relat_1(A),k2_relat_1(A))
        & m1_subset_1(A,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A)))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_funct_2)).

tff(f_68,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(B,A)))
         => v1_xboole_0(C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc4_relset_1)).

tff(f_94,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( ( v1_funct_1(C)
          & v1_partfun1(C,A) )
       => ( v1_funct_1(C)
          & v1_funct_2(C,A,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_funct_2)).

tff(f_108,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => ( ( v1_funct_1(C)
              & v1_funct_2(C,A,B) )
           => ( v1_funct_1(C)
              & v1_partfun1(C,A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc5_funct_2)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_151,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( ( k1_relat_1(C) = A
          & ! [D] :
              ( r2_hidden(D,A)
             => r2_hidden(k1_funct_1(C,D),B) ) )
       => ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_funct_2)).

tff(c_98,plain,(
    r2_hidden('#skF_10',k1_funct_2('#skF_8','#skF_9')) ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_799,plain,(
    ! [A_248,B_249,D_250] :
      ( '#skF_6'(A_248,B_249,k1_funct_2(A_248,B_249),D_250) = D_250
      | ~ r2_hidden(D_250,k1_funct_2(A_248,B_249)) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_818,plain,(
    '#skF_6'('#skF_8','#skF_9',k1_funct_2('#skF_8','#skF_9'),'#skF_10') = '#skF_10' ),
    inference(resolution,[status(thm)],[c_98,c_799])).

tff(c_860,plain,(
    ! [A_261,B_262,D_263] :
      ( v1_relat_1('#skF_6'(A_261,B_262,k1_funct_2(A_261,B_262),D_263))
      | ~ r2_hidden(D_263,k1_funct_2(A_261,B_262)) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_863,plain,
    ( v1_relat_1('#skF_10')
    | ~ r2_hidden('#skF_10',k1_funct_2('#skF_8','#skF_9')) ),
    inference(superposition,[status(thm),theory(equality)],[c_818,c_860])).

tff(c_865,plain,(
    v1_relat_1('#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_863])).

tff(c_16,plain,(
    ! [B_11] : r1_tarski(B_11,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_1013,plain,(
    ! [A_280,B_281,D_282] :
      ( k1_relat_1('#skF_6'(A_280,B_281,k1_funct_2(A_280,B_281),D_282)) = A_280
      | ~ r2_hidden(D_282,k1_funct_2(A_280,B_281)) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_1037,plain,
    ( k1_relat_1('#skF_10') = '#skF_8'
    | ~ r2_hidden('#skF_10',k1_funct_2('#skF_8','#skF_9')) ),
    inference(superposition,[status(thm),theory(equality)],[c_818,c_1013])).

tff(c_1041,plain,(
    k1_relat_1('#skF_10') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_1037])).

tff(c_1699,plain,(
    ! [A_331,B_332,D_333] :
      ( r1_tarski(k2_relat_1('#skF_6'(A_331,B_332,k1_funct_2(A_331,B_332),D_333)),B_332)
      | ~ r2_hidden(D_333,k1_funct_2(A_331,B_332)) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_1736,plain,
    ( r1_tarski(k2_relat_1('#skF_10'),'#skF_9')
    | ~ r2_hidden('#skF_10',k1_funct_2('#skF_8','#skF_9')) ),
    inference(superposition,[status(thm),theory(equality)],[c_818,c_1699])).

tff(c_1750,plain,(
    r1_tarski(k2_relat_1('#skF_10'),'#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_1736])).

tff(c_2191,plain,(
    ! [C_366,A_367,B_368] :
      ( m1_subset_1(C_366,k1_zfmisc_1(k2_zfmisc_1(A_367,B_368)))
      | ~ r1_tarski(k2_relat_1(C_366),B_368)
      | ~ r1_tarski(k1_relat_1(C_366),A_367)
      | ~ v1_relat_1(C_366) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_96,plain,
    ( ~ m1_subset_1('#skF_10',k1_zfmisc_1(k2_zfmisc_1('#skF_8','#skF_9')))
    | ~ v1_funct_2('#skF_10','#skF_8','#skF_9')
    | ~ v1_funct_1('#skF_10') ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_129,plain,(
    ~ v1_funct_1('#skF_10') ),
    inference(splitLeft,[status(thm)],[c_96])).

tff(c_440,plain,(
    ! [A_163,B_164,D_165] :
      ( '#skF_6'(A_163,B_164,k1_funct_2(A_163,B_164),D_165) = D_165
      | ~ r2_hidden(D_165,k1_funct_2(A_163,B_164)) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_459,plain,(
    '#skF_6'('#skF_8','#skF_9',k1_funct_2('#skF_8','#skF_9'),'#skF_10') = '#skF_10' ),
    inference(resolution,[status(thm)],[c_98,c_440])).

tff(c_508,plain,(
    ! [A_172,B_173,D_174] :
      ( v1_funct_1('#skF_6'(A_172,B_173,k1_funct_2(A_172,B_173),D_174))
      | ~ r2_hidden(D_174,k1_funct_2(A_172,B_173)) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_511,plain,
    ( v1_funct_1('#skF_10')
    | ~ r2_hidden('#skF_10',k1_funct_2('#skF_8','#skF_9')) ),
    inference(superposition,[status(thm),theory(equality)],[c_459,c_508])).

tff(c_513,plain,(
    v1_funct_1('#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_511])).

tff(c_515,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_129,c_513])).

tff(c_516,plain,
    ( ~ v1_funct_2('#skF_10','#skF_8','#skF_9')
    | ~ m1_subset_1('#skF_10',k1_zfmisc_1(k2_zfmisc_1('#skF_8','#skF_9'))) ),
    inference(splitRight,[status(thm)],[c_96])).

tff(c_529,plain,(
    ~ m1_subset_1('#skF_10',k1_zfmisc_1(k2_zfmisc_1('#skF_8','#skF_9'))) ),
    inference(splitLeft,[status(thm)],[c_516])).

tff(c_2207,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_10'),'#skF_9')
    | ~ r1_tarski(k1_relat_1('#skF_10'),'#skF_8')
    | ~ v1_relat_1('#skF_10') ),
    inference(resolution,[status(thm)],[c_2191,c_529])).

tff(c_2219,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_865,c_16,c_1041,c_1750,c_2207])).

tff(c_2221,plain,(
    m1_subset_1('#skF_10',k1_zfmisc_1(k2_zfmisc_1('#skF_8','#skF_9'))) ),
    inference(splitRight,[status(thm)],[c_516])).

tff(c_2446,plain,(
    ! [A_412,B_413,C_414] :
      ( k1_relset_1(A_412,B_413,C_414) = k1_relat_1(C_414)
      | ~ m1_subset_1(C_414,k1_zfmisc_1(k2_zfmisc_1(A_412,B_413))) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_2454,plain,(
    k1_relset_1('#skF_8','#skF_9','#skF_10') = k1_relat_1('#skF_10') ),
    inference(resolution,[status(thm)],[c_2221,c_2446])).

tff(c_2642,plain,(
    ! [A_444,B_445,C_446] :
      ( m1_subset_1(k1_relset_1(A_444,B_445,C_446),k1_zfmisc_1(A_444))
      | ~ m1_subset_1(C_446,k1_zfmisc_1(k2_zfmisc_1(A_444,B_445))) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_2664,plain,
    ( m1_subset_1(k1_relat_1('#skF_10'),k1_zfmisc_1('#skF_8'))
    | ~ m1_subset_1('#skF_10',k1_zfmisc_1(k2_zfmisc_1('#skF_8','#skF_9'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_2454,c_2642])).

tff(c_2670,plain,(
    m1_subset_1(k1_relat_1('#skF_10'),k1_zfmisc_1('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2221,c_2664])).

tff(c_20,plain,(
    ! [A_15,B_16] :
      ( r1_tarski(A_15,B_16)
      | ~ m1_subset_1(A_15,k1_zfmisc_1(B_16)) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_2677,plain,(
    r1_tarski(k1_relat_1('#skF_10'),'#skF_8') ),
    inference(resolution,[status(thm)],[c_2670,c_20])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_22,plain,(
    ! [A_15,B_16] :
      ( m1_subset_1(A_15,k1_zfmisc_1(B_16))
      | ~ r1_tarski(A_15,B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_2315,plain,(
    ! [C_384,B_385,A_386] :
      ( ~ v1_xboole_0(C_384)
      | ~ m1_subset_1(B_385,k1_zfmisc_1(C_384))
      | ~ r2_hidden(A_386,B_385) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_2322,plain,(
    ! [B_387,A_388,A_389] :
      ( ~ v1_xboole_0(B_387)
      | ~ r2_hidden(A_388,A_389)
      | ~ r1_tarski(A_389,B_387) ) ),
    inference(resolution,[status(thm)],[c_22,c_2315])).

tff(c_2330,plain,(
    ! [B_387,A_1] :
      ( ~ v1_xboole_0(B_387)
      | ~ r1_tarski(A_1,B_387)
      | v1_xboole_0(A_1) ) ),
    inference(resolution,[status(thm)],[c_4,c_2322])).

tff(c_2702,plain,
    ( ~ v1_xboole_0('#skF_8')
    | v1_xboole_0(k1_relat_1('#skF_10')) ),
    inference(resolution,[status(thm)],[c_2677,c_2330])).

tff(c_2707,plain,(
    ~ v1_xboole_0('#skF_8') ),
    inference(splitLeft,[status(thm)],[c_2702])).

tff(c_517,plain,(
    v1_funct_1('#skF_10') ),
    inference(splitRight,[status(thm)],[c_96])).

tff(c_2709,plain,(
    ! [A_447,B_448,D_449] :
      ( '#skF_6'(A_447,B_448,k1_funct_2(A_447,B_448),D_449) = D_449
      | ~ r2_hidden(D_449,k1_funct_2(A_447,B_448)) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_2728,plain,(
    '#skF_6'('#skF_8','#skF_9',k1_funct_2('#skF_8','#skF_9'),'#skF_10') = '#skF_10' ),
    inference(resolution,[status(thm)],[c_98,c_2709])).

tff(c_3501,plain,(
    ! [A_508,B_509,D_510] :
      ( k1_relat_1('#skF_6'(A_508,B_509,k1_funct_2(A_508,B_509),D_510)) = A_508
      | ~ r2_hidden(D_510,k1_funct_2(A_508,B_509)) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_3528,plain,
    ( k1_relat_1('#skF_10') = '#skF_8'
    | ~ r2_hidden('#skF_10',k1_funct_2('#skF_8','#skF_9')) ),
    inference(superposition,[status(thm),theory(equality)],[c_2728,c_3501])).

tff(c_3532,plain,(
    k1_relat_1('#skF_10') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_3528])).

tff(c_12,plain,(
    ! [B_11,A_10] :
      ( B_11 = A_10
      | ~ r1_tarski(B_11,A_10)
      | ~ r1_tarski(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_2706,plain,
    ( k1_relat_1('#skF_10') = '#skF_8'
    | ~ r1_tarski('#skF_8',k1_relat_1('#skF_10')) ),
    inference(resolution,[status(thm)],[c_2677,c_12])).

tff(c_2708,plain,(
    ~ r1_tarski('#skF_8',k1_relat_1('#skF_10')) ),
    inference(splitLeft,[status(thm)],[c_2706])).

tff(c_3538,plain,(
    ~ r1_tarski('#skF_8','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3532,c_2708])).

tff(c_3546,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_3538])).

tff(c_3547,plain,(
    k1_relat_1('#skF_10') = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_2706])).

tff(c_80,plain,(
    ! [A_60] :
      ( v1_funct_2(A_60,k1_relat_1(A_60),k2_relat_1(A_60))
      | ~ v1_funct_1(A_60)
      | ~ v1_relat_1(A_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_3568,plain,
    ( v1_funct_2('#skF_10','#skF_8',k2_relat_1('#skF_10'))
    | ~ v1_funct_1('#skF_10')
    | ~ v1_relat_1('#skF_10') ),
    inference(superposition,[status(thm),theory(equality)],[c_3547,c_80])).

tff(c_3580,plain,
    ( v1_funct_2('#skF_10','#skF_8',k2_relat_1('#skF_10'))
    | ~ v1_relat_1('#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_517,c_3568])).

tff(c_3602,plain,(
    ~ v1_relat_1('#skF_10') ),
    inference(splitLeft,[status(thm)],[c_3580])).

tff(c_3603,plain,(
    ! [A_511,B_512,D_513] :
      ( '#skF_6'(A_511,B_512,k1_funct_2(A_511,B_512),D_513) = D_513
      | ~ r2_hidden(D_513,k1_funct_2(A_511,B_512)) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_3622,plain,(
    '#skF_6'('#skF_8','#skF_9',k1_funct_2('#skF_8','#skF_9'),'#skF_10') = '#skF_10' ),
    inference(resolution,[status(thm)],[c_98,c_3603])).

tff(c_3651,plain,(
    ! [A_515,B_516,D_517] :
      ( v1_relat_1('#skF_6'(A_515,B_516,k1_funct_2(A_515,B_516),D_517))
      | ~ r2_hidden(D_517,k1_funct_2(A_515,B_516)) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_3654,plain,
    ( v1_relat_1('#skF_10')
    | ~ r2_hidden('#skF_10',k1_funct_2('#skF_8','#skF_9')) ),
    inference(superposition,[status(thm),theory(equality)],[c_3622,c_3651])).

tff(c_3656,plain,(
    v1_relat_1('#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_3654])).

tff(c_3658,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3602,c_3656])).

tff(c_3660,plain,(
    v1_relat_1('#skF_10') ),
    inference(splitRight,[status(thm)],[c_3580])).

tff(c_2538,plain,(
    ! [A_435] :
      ( m1_subset_1(A_435,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_435),k2_relat_1(A_435))))
      | ~ v1_funct_1(A_435)
      | ~ v1_relat_1(A_435) ) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_2553,plain,(
    ! [A_435] :
      ( r1_tarski(A_435,k2_zfmisc_1(k1_relat_1(A_435),k2_relat_1(A_435)))
      | ~ v1_funct_1(A_435)
      | ~ v1_relat_1(A_435) ) ),
    inference(resolution,[status(thm)],[c_2538,c_20])).

tff(c_3562,plain,
    ( r1_tarski('#skF_10',k2_zfmisc_1('#skF_8',k2_relat_1('#skF_10')))
    | ~ v1_funct_1('#skF_10')
    | ~ v1_relat_1('#skF_10') ),
    inference(superposition,[status(thm),theory(equality)],[c_3547,c_2553])).

tff(c_3576,plain,
    ( r1_tarski('#skF_10',k2_zfmisc_1('#skF_8',k2_relat_1('#skF_10')))
    | ~ v1_relat_1('#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_517,c_3562])).

tff(c_3684,plain,(
    r1_tarski('#skF_10',k2_zfmisc_1('#skF_8',k2_relat_1('#skF_10'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3660,c_3576])).

tff(c_2365,plain,(
    ! [C_393,B_394,A_395] :
      ( v1_xboole_0(C_393)
      | ~ m1_subset_1(C_393,k1_zfmisc_1(k2_zfmisc_1(B_394,A_395)))
      | ~ v1_xboole_0(A_395) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_2374,plain,(
    ! [A_15,A_395,B_394] :
      ( v1_xboole_0(A_15)
      | ~ v1_xboole_0(A_395)
      | ~ r1_tarski(A_15,k2_zfmisc_1(B_394,A_395)) ) ),
    inference(resolution,[status(thm)],[c_22,c_2365])).

tff(c_3716,plain,
    ( v1_xboole_0('#skF_10')
    | ~ v1_xboole_0(k2_relat_1('#skF_10')) ),
    inference(resolution,[status(thm)],[c_3684,c_2374])).

tff(c_3724,plain,(
    ~ v1_xboole_0(k2_relat_1('#skF_10')) ),
    inference(splitLeft,[status(thm)],[c_3716])).

tff(c_2220,plain,(
    ~ v1_funct_2('#skF_10','#skF_8','#skF_9') ),
    inference(splitRight,[status(thm)],[c_516])).

tff(c_4795,plain,(
    ! [C_607,A_608,B_609] :
      ( v1_funct_2(C_607,A_608,B_609)
      | ~ v1_partfun1(C_607,A_608)
      | ~ v1_funct_1(C_607)
      | ~ m1_subset_1(C_607,k1_zfmisc_1(k2_zfmisc_1(A_608,B_609))) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_4808,plain,
    ( v1_funct_2('#skF_10','#skF_8','#skF_9')
    | ~ v1_partfun1('#skF_10','#skF_8')
    | ~ v1_funct_1('#skF_10') ),
    inference(resolution,[status(thm)],[c_2221,c_4795])).

tff(c_4820,plain,
    ( v1_funct_2('#skF_10','#skF_8','#skF_9')
    | ~ v1_partfun1('#skF_10','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_517,c_4808])).

tff(c_4821,plain,(
    ~ v1_partfun1('#skF_10','#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_2220,c_4820])).

tff(c_3659,plain,(
    v1_funct_2('#skF_10','#skF_8',k2_relat_1('#skF_10')) ),
    inference(splitRight,[status(thm)],[c_3580])).

tff(c_78,plain,(
    ! [A_60] :
      ( m1_subset_1(A_60,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_60),k2_relat_1(A_60))))
      | ~ v1_funct_1(A_60)
      | ~ v1_relat_1(A_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_3565,plain,
    ( m1_subset_1('#skF_10',k1_zfmisc_1(k2_zfmisc_1('#skF_8',k2_relat_1('#skF_10'))))
    | ~ v1_funct_1('#skF_10')
    | ~ v1_relat_1('#skF_10') ),
    inference(superposition,[status(thm),theory(equality)],[c_3547,c_78])).

tff(c_3578,plain,
    ( m1_subset_1('#skF_10',k1_zfmisc_1(k2_zfmisc_1('#skF_8',k2_relat_1('#skF_10'))))
    | ~ v1_relat_1('#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_517,c_3565])).

tff(c_3797,plain,(
    m1_subset_1('#skF_10',k1_zfmisc_1(k2_zfmisc_1('#skF_8',k2_relat_1('#skF_10')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3660,c_3578])).

tff(c_6784,plain,(
    ! [C_724,A_725,B_726] :
      ( v1_partfun1(C_724,A_725)
      | ~ v1_funct_2(C_724,A_725,B_726)
      | ~ v1_funct_1(C_724)
      | ~ m1_subset_1(C_724,k1_zfmisc_1(k2_zfmisc_1(A_725,B_726)))
      | v1_xboole_0(B_726) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_6790,plain,
    ( v1_partfun1('#skF_10','#skF_8')
    | ~ v1_funct_2('#skF_10','#skF_8',k2_relat_1('#skF_10'))
    | ~ v1_funct_1('#skF_10')
    | v1_xboole_0(k2_relat_1('#skF_10')) ),
    inference(resolution,[status(thm)],[c_3797,c_6784])).

tff(c_6808,plain,
    ( v1_partfun1('#skF_10','#skF_8')
    | v1_xboole_0(k2_relat_1('#skF_10')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_517,c_3659,c_6790])).

tff(c_6810,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3724,c_4821,c_6808])).

tff(c_6811,plain,(
    v1_xboole_0('#skF_10') ),
    inference(splitRight,[status(thm)],[c_3716])).

tff(c_2401,plain,(
    ! [A_400,A_401,B_402] :
      ( v1_xboole_0(A_400)
      | ~ v1_xboole_0(A_401)
      | ~ r1_tarski(A_400,k2_zfmisc_1(B_402,A_401)) ) ),
    inference(resolution,[status(thm)],[c_22,c_2365])).

tff(c_2420,plain,(
    ! [B_403,A_404] :
      ( v1_xboole_0(k2_zfmisc_1(B_403,A_404))
      | ~ v1_xboole_0(A_404) ) ),
    inference(resolution,[status(thm)],[c_16,c_2401])).

tff(c_118,plain,(
    ! [A_75,B_76] :
      ( r2_hidden('#skF_2'(A_75,B_76),A_75)
      | r1_tarski(A_75,B_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_128,plain,(
    ! [A_75,B_76] :
      ( ~ v1_xboole_0(A_75)
      | r1_tarski(A_75,B_76) ) ),
    inference(resolution,[status(thm)],[c_118,c_2])).

tff(c_519,plain,(
    ! [B_177,A_178] :
      ( B_177 = A_178
      | ~ r1_tarski(B_177,A_178)
      | ~ r1_tarski(A_178,B_177) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_2234,plain,(
    ! [B_369,A_370] :
      ( B_369 = A_370
      | ~ r1_tarski(B_369,A_370)
      | ~ v1_xboole_0(A_370) ) ),
    inference(resolution,[status(thm)],[c_128,c_519])).

tff(c_2245,plain,(
    ! [B_76,A_75] :
      ( B_76 = A_75
      | ~ v1_xboole_0(B_76)
      | ~ v1_xboole_0(A_75) ) ),
    inference(resolution,[status(thm)],[c_128,c_2234])).

tff(c_2426,plain,(
    ! [B_403,A_404,A_75] :
      ( k2_zfmisc_1(B_403,A_404) = A_75
      | ~ v1_xboole_0(A_75)
      | ~ v1_xboole_0(A_404) ) ),
    inference(resolution,[status(thm)],[c_2420,c_2245])).

tff(c_6989,plain,(
    ! [B_735,A_736] :
      ( k2_zfmisc_1(B_735,A_736) = '#skF_10'
      | ~ v1_xboole_0(A_736) ) ),
    inference(resolution,[status(thm)],[c_6811,c_2426])).

tff(c_6994,plain,(
    ! [B_735] : k2_zfmisc_1(B_735,'#skF_10') = '#skF_10' ),
    inference(resolution,[status(thm)],[c_6811,c_6989])).

tff(c_6812,plain,(
    v1_xboole_0(k2_relat_1('#skF_10')) ),
    inference(splitRight,[status(thm)],[c_3716])).

tff(c_6844,plain,(
    ! [A_727] :
      ( A_727 = '#skF_10'
      | ~ v1_xboole_0(A_727) ) ),
    inference(resolution,[status(thm)],[c_6811,c_2245])).

tff(c_6854,plain,(
    k2_relat_1('#skF_10') = '#skF_10' ),
    inference(resolution,[status(thm)],[c_6812,c_6844])).

tff(c_6878,plain,
    ( m1_subset_1('#skF_10',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_10'),'#skF_10')))
    | ~ v1_funct_1('#skF_10')
    | ~ v1_relat_1('#skF_10') ),
    inference(superposition,[status(thm),theory(equality)],[c_6854,c_78])).

tff(c_6893,plain,(
    m1_subset_1('#skF_10',k1_zfmisc_1(k2_zfmisc_1('#skF_8','#skF_10'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3660,c_517,c_3547,c_6878])).

tff(c_7062,plain,(
    m1_subset_1('#skF_10',k1_zfmisc_1('#skF_10')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6994,c_6893])).

tff(c_2464,plain,(
    ! [A_419,B_420,A_421] :
      ( k1_relset_1(A_419,B_420,A_421) = k1_relat_1(A_421)
      | ~ r1_tarski(A_421,k2_zfmisc_1(A_419,B_420)) ) ),
    inference(resolution,[status(thm)],[c_22,c_2446])).

tff(c_2482,plain,(
    ! [A_419,B_420,A_75] :
      ( k1_relset_1(A_419,B_420,A_75) = k1_relat_1(A_75)
      | ~ v1_xboole_0(A_75) ) ),
    inference(resolution,[status(thm)],[c_128,c_2464])).

tff(c_6814,plain,(
    ! [A_419,B_420] : k1_relset_1(A_419,B_420,'#skF_10') = k1_relat_1('#skF_10') ),
    inference(resolution,[status(thm)],[c_6811,c_2482])).

tff(c_6900,plain,(
    ! [A_728,B_729] : k1_relset_1(A_728,B_729,'#skF_10') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3547,c_6814])).

tff(c_28,plain,(
    ! [A_24,B_25,C_26] :
      ( m1_subset_1(k1_relset_1(A_24,B_25,C_26),k1_zfmisc_1(A_24))
      | ~ m1_subset_1(C_26,k1_zfmisc_1(k2_zfmisc_1(A_24,B_25))) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_7550,plain,(
    ! [A_779,B_780] :
      ( m1_subset_1('#skF_8',k1_zfmisc_1(A_779))
      | ~ m1_subset_1('#skF_10',k1_zfmisc_1(k2_zfmisc_1(A_779,B_780))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6900,c_28])).

tff(c_7556,plain,(
    ! [B_735] :
      ( m1_subset_1('#skF_8',k1_zfmisc_1(B_735))
      | ~ m1_subset_1('#skF_10',k1_zfmisc_1('#skF_10')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6994,c_7550])).

tff(c_7581,plain,(
    ! [B_781] : m1_subset_1('#skF_8',k1_zfmisc_1(B_781)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7062,c_7556])).

tff(c_6998,plain,(
    ! [B_737] : k2_zfmisc_1(B_737,'#skF_10') = '#skF_10' ),
    inference(resolution,[status(thm)],[c_6811,c_6989])).

tff(c_26,plain,(
    ! [C_23,B_21,A_20] :
      ( v1_xboole_0(C_23)
      | ~ m1_subset_1(C_23,k1_zfmisc_1(k2_zfmisc_1(B_21,A_20)))
      | ~ v1_xboole_0(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_7018,plain,(
    ! [C_23] :
      ( v1_xboole_0(C_23)
      | ~ m1_subset_1(C_23,k1_zfmisc_1('#skF_10'))
      | ~ v1_xboole_0('#skF_10') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6998,c_26])).

tff(c_7028,plain,(
    ! [C_23] :
      ( v1_xboole_0(C_23)
      | ~ m1_subset_1(C_23,k1_zfmisc_1('#skF_10')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6811,c_7018])).

tff(c_7585,plain,(
    v1_xboole_0('#skF_8') ),
    inference(resolution,[status(thm)],[c_7581,c_7028])).

tff(c_7602,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2707,c_7585])).

tff(c_7604,plain,(
    v1_xboole_0('#skF_8') ),
    inference(splitRight,[status(thm)],[c_2702])).

tff(c_7603,plain,(
    v1_xboole_0(k1_relat_1('#skF_10')) ),
    inference(splitRight,[status(thm)],[c_2702])).

tff(c_7649,plain,(
    ! [A_785] :
      ( A_785 = '#skF_8'
      | ~ v1_xboole_0(A_785) ) ),
    inference(resolution,[status(thm)],[c_7604,c_2245])).

tff(c_7659,plain,(
    k1_relat_1('#skF_10') = '#skF_8' ),
    inference(resolution,[status(thm)],[c_7603,c_7649])).

tff(c_7669,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7659,c_2670])).

tff(c_24,plain,(
    ! [C_19,B_18,A_17] :
      ( ~ v1_xboole_0(C_19)
      | ~ m1_subset_1(B_18,k1_zfmisc_1(C_19))
      | ~ r2_hidden(A_17,B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_7703,plain,(
    ! [A_17] :
      ( ~ v1_xboole_0('#skF_8')
      | ~ r2_hidden(A_17,'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_7669,c_24])).

tff(c_7709,plain,(
    ! [A_17] : ~ r2_hidden(A_17,'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_7604,c_7703])).

tff(c_7605,plain,(
    ! [A_782,B_783,D_784] :
      ( '#skF_6'(A_782,B_783,k1_funct_2(A_782,B_783),D_784) = D_784
      | ~ r2_hidden(D_784,k1_funct_2(A_782,B_783)) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_7624,plain,(
    '#skF_6'('#skF_8','#skF_9',k1_funct_2('#skF_8','#skF_9'),'#skF_10') = '#skF_10' ),
    inference(resolution,[status(thm)],[c_98,c_7605])).

tff(c_7785,plain,(
    ! [A_788,B_789,D_790] :
      ( v1_relat_1('#skF_6'(A_788,B_789,k1_funct_2(A_788,B_789),D_790))
      | ~ r2_hidden(D_790,k1_funct_2(A_788,B_789)) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_7788,plain,
    ( v1_relat_1('#skF_10')
    | ~ r2_hidden('#skF_10',k1_funct_2('#skF_8','#skF_9')) ),
    inference(superposition,[status(thm),theory(equality)],[c_7624,c_7785])).

tff(c_7790,plain,(
    v1_relat_1('#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_7788])).

tff(c_9031,plain,(
    ! [C_875,B_876] :
      ( r2_hidden('#skF_7'(k1_relat_1(C_875),B_876,C_875),k1_relat_1(C_875))
      | v1_funct_2(C_875,k1_relat_1(C_875),B_876)
      | ~ v1_funct_1(C_875)
      | ~ v1_relat_1(C_875) ) ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_9059,plain,(
    ! [B_876] :
      ( r2_hidden('#skF_7'('#skF_8',B_876,'#skF_10'),k1_relat_1('#skF_10'))
      | v1_funct_2('#skF_10',k1_relat_1('#skF_10'),B_876)
      | ~ v1_funct_1('#skF_10')
      | ~ v1_relat_1('#skF_10') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_7659,c_9031])).

tff(c_9071,plain,(
    ! [B_876] :
      ( r2_hidden('#skF_7'('#skF_8',B_876,'#skF_10'),'#skF_8')
      | v1_funct_2('#skF_10','#skF_8',B_876) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7790,c_517,c_7659,c_7659,c_9059])).

tff(c_9072,plain,(
    ! [B_876] : v1_funct_2('#skF_10','#skF_8',B_876) ),
    inference(negUnitSimplification,[status(thm)],[c_7709,c_9071])).

tff(c_9079,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_9072,c_2220])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:17:41 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.02/2.71  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.02/2.72  
% 8.02/2.72  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.02/2.72  %$ v1_funct_2 > v1_partfun1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_2 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_1 > #skF_4 > #skF_10 > #skF_5 > #skF_6 > #skF_9 > #skF_7 > #skF_8 > #skF_3 > #skF_2
% 8.02/2.72  
% 8.02/2.72  %Foreground sorts:
% 8.02/2.72  
% 8.02/2.72  
% 8.02/2.72  %Background operators:
% 8.02/2.72  
% 8.02/2.72  
% 8.02/2.72  %Foreground operators:
% 8.02/2.72  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 8.02/2.72  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.02/2.72  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 8.02/2.72  tff('#skF_1', type, '#skF_1': $i > $i).
% 8.02/2.72  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 8.02/2.72  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 8.02/2.72  tff('#skF_10', type, '#skF_10': $i).
% 8.02/2.72  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 8.02/2.72  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 8.02/2.72  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 8.02/2.72  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 8.02/2.72  tff('#skF_6', type, '#skF_6': ($i * $i * $i * $i) > $i).
% 8.02/2.72  tff('#skF_9', type, '#skF_9': $i).
% 8.02/2.72  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 8.02/2.72  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 8.02/2.72  tff('#skF_7', type, '#skF_7': ($i * $i * $i) > $i).
% 8.02/2.72  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 8.02/2.72  tff(k1_funct_2, type, k1_funct_2: ($i * $i) > $i).
% 8.02/2.72  tff('#skF_8', type, '#skF_8': $i).
% 8.02/2.72  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.02/2.72  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 8.02/2.72  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 8.02/2.72  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 8.02/2.72  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.02/2.72  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 8.02/2.72  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 8.02/2.72  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 8.02/2.72  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 8.02/2.72  
% 8.02/2.75  tff(f_160, negated_conjecture, ~(![A, B, C]: (r2_hidden(C, k1_funct_2(A, B)) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t121_funct_2)).
% 8.02/2.75  tff(f_124, axiom, (![A, B, C]: ((C = k1_funct_2(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (?[E]: ((((v1_relat_1(E) & v1_funct_1(E)) & (D = E)) & (k1_relat_1(E) = A)) & r1_tarski(k2_relat_1(E), B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_funct_2)).
% 8.02/2.75  tff(f_44, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 8.02/2.75  tff(f_84, axiom, (![A, B, C]: (v1_relat_1(C) => ((r1_tarski(k1_relat_1(C), A) & r1_tarski(k2_relat_1(C), B)) => m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_relset_1)).
% 8.02/2.75  tff(f_76, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 8.02/2.75  tff(f_72, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k1_relset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_relset_1)).
% 8.02/2.75  tff(f_54, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 8.02/2.75  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 8.02/2.75  tff(f_61, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_subset)).
% 8.02/2.75  tff(f_134, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => ((v1_funct_1(A) & v1_funct_2(A, k1_relat_1(A), k2_relat_1(A))) & m1_subset_1(A, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_funct_2)).
% 8.02/2.75  tff(f_68, axiom, (![A, B]: (v1_xboole_0(A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => v1_xboole_0(C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc4_relset_1)).
% 8.02/2.75  tff(f_94, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v1_partfun1(C, A)) => (v1_funct_1(C) & v1_funct_2(C, A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_funct_2)).
% 8.02/2.75  tff(f_108, axiom, (![A, B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) => (v1_funct_1(C) & v1_partfun1(C, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc5_funct_2)).
% 8.02/2.75  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 8.02/2.75  tff(f_151, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (((k1_relat_1(C) = A) & (![D]: (r2_hidden(D, A) => r2_hidden(k1_funct_1(C, D), B)))) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_funct_2)).
% 8.02/2.75  tff(c_98, plain, (r2_hidden('#skF_10', k1_funct_2('#skF_8', '#skF_9'))), inference(cnfTransformation, [status(thm)], [f_160])).
% 8.02/2.75  tff(c_799, plain, (![A_248, B_249, D_250]: ('#skF_6'(A_248, B_249, k1_funct_2(A_248, B_249), D_250)=D_250 | ~r2_hidden(D_250, k1_funct_2(A_248, B_249)))), inference(cnfTransformation, [status(thm)], [f_124])).
% 8.02/2.75  tff(c_818, plain, ('#skF_6'('#skF_8', '#skF_9', k1_funct_2('#skF_8', '#skF_9'), '#skF_10')='#skF_10'), inference(resolution, [status(thm)], [c_98, c_799])).
% 8.02/2.75  tff(c_860, plain, (![A_261, B_262, D_263]: (v1_relat_1('#skF_6'(A_261, B_262, k1_funct_2(A_261, B_262), D_263)) | ~r2_hidden(D_263, k1_funct_2(A_261, B_262)))), inference(cnfTransformation, [status(thm)], [f_124])).
% 8.02/2.75  tff(c_863, plain, (v1_relat_1('#skF_10') | ~r2_hidden('#skF_10', k1_funct_2('#skF_8', '#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_818, c_860])).
% 8.02/2.75  tff(c_865, plain, (v1_relat_1('#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_98, c_863])).
% 8.02/2.75  tff(c_16, plain, (![B_11]: (r1_tarski(B_11, B_11))), inference(cnfTransformation, [status(thm)], [f_44])).
% 8.02/2.75  tff(c_1013, plain, (![A_280, B_281, D_282]: (k1_relat_1('#skF_6'(A_280, B_281, k1_funct_2(A_280, B_281), D_282))=A_280 | ~r2_hidden(D_282, k1_funct_2(A_280, B_281)))), inference(cnfTransformation, [status(thm)], [f_124])).
% 8.02/2.75  tff(c_1037, plain, (k1_relat_1('#skF_10')='#skF_8' | ~r2_hidden('#skF_10', k1_funct_2('#skF_8', '#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_818, c_1013])).
% 8.02/2.75  tff(c_1041, plain, (k1_relat_1('#skF_10')='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_98, c_1037])).
% 8.02/2.75  tff(c_1699, plain, (![A_331, B_332, D_333]: (r1_tarski(k2_relat_1('#skF_6'(A_331, B_332, k1_funct_2(A_331, B_332), D_333)), B_332) | ~r2_hidden(D_333, k1_funct_2(A_331, B_332)))), inference(cnfTransformation, [status(thm)], [f_124])).
% 8.02/2.75  tff(c_1736, plain, (r1_tarski(k2_relat_1('#skF_10'), '#skF_9') | ~r2_hidden('#skF_10', k1_funct_2('#skF_8', '#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_818, c_1699])).
% 8.02/2.75  tff(c_1750, plain, (r1_tarski(k2_relat_1('#skF_10'), '#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_98, c_1736])).
% 8.02/2.75  tff(c_2191, plain, (![C_366, A_367, B_368]: (m1_subset_1(C_366, k1_zfmisc_1(k2_zfmisc_1(A_367, B_368))) | ~r1_tarski(k2_relat_1(C_366), B_368) | ~r1_tarski(k1_relat_1(C_366), A_367) | ~v1_relat_1(C_366))), inference(cnfTransformation, [status(thm)], [f_84])).
% 8.02/2.75  tff(c_96, plain, (~m1_subset_1('#skF_10', k1_zfmisc_1(k2_zfmisc_1('#skF_8', '#skF_9'))) | ~v1_funct_2('#skF_10', '#skF_8', '#skF_9') | ~v1_funct_1('#skF_10')), inference(cnfTransformation, [status(thm)], [f_160])).
% 8.02/2.75  tff(c_129, plain, (~v1_funct_1('#skF_10')), inference(splitLeft, [status(thm)], [c_96])).
% 8.02/2.75  tff(c_440, plain, (![A_163, B_164, D_165]: ('#skF_6'(A_163, B_164, k1_funct_2(A_163, B_164), D_165)=D_165 | ~r2_hidden(D_165, k1_funct_2(A_163, B_164)))), inference(cnfTransformation, [status(thm)], [f_124])).
% 8.02/2.75  tff(c_459, plain, ('#skF_6'('#skF_8', '#skF_9', k1_funct_2('#skF_8', '#skF_9'), '#skF_10')='#skF_10'), inference(resolution, [status(thm)], [c_98, c_440])).
% 8.02/2.75  tff(c_508, plain, (![A_172, B_173, D_174]: (v1_funct_1('#skF_6'(A_172, B_173, k1_funct_2(A_172, B_173), D_174)) | ~r2_hidden(D_174, k1_funct_2(A_172, B_173)))), inference(cnfTransformation, [status(thm)], [f_124])).
% 8.02/2.75  tff(c_511, plain, (v1_funct_1('#skF_10') | ~r2_hidden('#skF_10', k1_funct_2('#skF_8', '#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_459, c_508])).
% 8.02/2.75  tff(c_513, plain, (v1_funct_1('#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_98, c_511])).
% 8.02/2.75  tff(c_515, plain, $false, inference(negUnitSimplification, [status(thm)], [c_129, c_513])).
% 8.02/2.75  tff(c_516, plain, (~v1_funct_2('#skF_10', '#skF_8', '#skF_9') | ~m1_subset_1('#skF_10', k1_zfmisc_1(k2_zfmisc_1('#skF_8', '#skF_9')))), inference(splitRight, [status(thm)], [c_96])).
% 8.02/2.75  tff(c_529, plain, (~m1_subset_1('#skF_10', k1_zfmisc_1(k2_zfmisc_1('#skF_8', '#skF_9')))), inference(splitLeft, [status(thm)], [c_516])).
% 8.02/2.75  tff(c_2207, plain, (~r1_tarski(k2_relat_1('#skF_10'), '#skF_9') | ~r1_tarski(k1_relat_1('#skF_10'), '#skF_8') | ~v1_relat_1('#skF_10')), inference(resolution, [status(thm)], [c_2191, c_529])).
% 8.02/2.75  tff(c_2219, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_865, c_16, c_1041, c_1750, c_2207])).
% 8.02/2.75  tff(c_2221, plain, (m1_subset_1('#skF_10', k1_zfmisc_1(k2_zfmisc_1('#skF_8', '#skF_9')))), inference(splitRight, [status(thm)], [c_516])).
% 8.02/2.75  tff(c_2446, plain, (![A_412, B_413, C_414]: (k1_relset_1(A_412, B_413, C_414)=k1_relat_1(C_414) | ~m1_subset_1(C_414, k1_zfmisc_1(k2_zfmisc_1(A_412, B_413))))), inference(cnfTransformation, [status(thm)], [f_76])).
% 8.02/2.75  tff(c_2454, plain, (k1_relset_1('#skF_8', '#skF_9', '#skF_10')=k1_relat_1('#skF_10')), inference(resolution, [status(thm)], [c_2221, c_2446])).
% 8.02/2.75  tff(c_2642, plain, (![A_444, B_445, C_446]: (m1_subset_1(k1_relset_1(A_444, B_445, C_446), k1_zfmisc_1(A_444)) | ~m1_subset_1(C_446, k1_zfmisc_1(k2_zfmisc_1(A_444, B_445))))), inference(cnfTransformation, [status(thm)], [f_72])).
% 8.02/2.75  tff(c_2664, plain, (m1_subset_1(k1_relat_1('#skF_10'), k1_zfmisc_1('#skF_8')) | ~m1_subset_1('#skF_10', k1_zfmisc_1(k2_zfmisc_1('#skF_8', '#skF_9')))), inference(superposition, [status(thm), theory('equality')], [c_2454, c_2642])).
% 8.02/2.75  tff(c_2670, plain, (m1_subset_1(k1_relat_1('#skF_10'), k1_zfmisc_1('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_2221, c_2664])).
% 8.02/2.75  tff(c_20, plain, (![A_15, B_16]: (r1_tarski(A_15, B_16) | ~m1_subset_1(A_15, k1_zfmisc_1(B_16)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 8.02/2.75  tff(c_2677, plain, (r1_tarski(k1_relat_1('#skF_10'), '#skF_8')), inference(resolution, [status(thm)], [c_2670, c_20])).
% 8.02/2.75  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 8.02/2.75  tff(c_22, plain, (![A_15, B_16]: (m1_subset_1(A_15, k1_zfmisc_1(B_16)) | ~r1_tarski(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_54])).
% 8.02/2.75  tff(c_2315, plain, (![C_384, B_385, A_386]: (~v1_xboole_0(C_384) | ~m1_subset_1(B_385, k1_zfmisc_1(C_384)) | ~r2_hidden(A_386, B_385))), inference(cnfTransformation, [status(thm)], [f_61])).
% 8.02/2.75  tff(c_2322, plain, (![B_387, A_388, A_389]: (~v1_xboole_0(B_387) | ~r2_hidden(A_388, A_389) | ~r1_tarski(A_389, B_387))), inference(resolution, [status(thm)], [c_22, c_2315])).
% 8.02/2.75  tff(c_2330, plain, (![B_387, A_1]: (~v1_xboole_0(B_387) | ~r1_tarski(A_1, B_387) | v1_xboole_0(A_1))), inference(resolution, [status(thm)], [c_4, c_2322])).
% 8.02/2.75  tff(c_2702, plain, (~v1_xboole_0('#skF_8') | v1_xboole_0(k1_relat_1('#skF_10'))), inference(resolution, [status(thm)], [c_2677, c_2330])).
% 8.02/2.75  tff(c_2707, plain, (~v1_xboole_0('#skF_8')), inference(splitLeft, [status(thm)], [c_2702])).
% 8.02/2.75  tff(c_517, plain, (v1_funct_1('#skF_10')), inference(splitRight, [status(thm)], [c_96])).
% 8.02/2.75  tff(c_2709, plain, (![A_447, B_448, D_449]: ('#skF_6'(A_447, B_448, k1_funct_2(A_447, B_448), D_449)=D_449 | ~r2_hidden(D_449, k1_funct_2(A_447, B_448)))), inference(cnfTransformation, [status(thm)], [f_124])).
% 8.02/2.75  tff(c_2728, plain, ('#skF_6'('#skF_8', '#skF_9', k1_funct_2('#skF_8', '#skF_9'), '#skF_10')='#skF_10'), inference(resolution, [status(thm)], [c_98, c_2709])).
% 8.02/2.75  tff(c_3501, plain, (![A_508, B_509, D_510]: (k1_relat_1('#skF_6'(A_508, B_509, k1_funct_2(A_508, B_509), D_510))=A_508 | ~r2_hidden(D_510, k1_funct_2(A_508, B_509)))), inference(cnfTransformation, [status(thm)], [f_124])).
% 8.02/2.75  tff(c_3528, plain, (k1_relat_1('#skF_10')='#skF_8' | ~r2_hidden('#skF_10', k1_funct_2('#skF_8', '#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_2728, c_3501])).
% 8.02/2.75  tff(c_3532, plain, (k1_relat_1('#skF_10')='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_98, c_3528])).
% 8.02/2.75  tff(c_12, plain, (![B_11, A_10]: (B_11=A_10 | ~r1_tarski(B_11, A_10) | ~r1_tarski(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_44])).
% 8.02/2.75  tff(c_2706, plain, (k1_relat_1('#skF_10')='#skF_8' | ~r1_tarski('#skF_8', k1_relat_1('#skF_10'))), inference(resolution, [status(thm)], [c_2677, c_12])).
% 8.02/2.75  tff(c_2708, plain, (~r1_tarski('#skF_8', k1_relat_1('#skF_10'))), inference(splitLeft, [status(thm)], [c_2706])).
% 8.02/2.75  tff(c_3538, plain, (~r1_tarski('#skF_8', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_3532, c_2708])).
% 8.02/2.75  tff(c_3546, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_16, c_3538])).
% 8.02/2.75  tff(c_3547, plain, (k1_relat_1('#skF_10')='#skF_8'), inference(splitRight, [status(thm)], [c_2706])).
% 8.02/2.75  tff(c_80, plain, (![A_60]: (v1_funct_2(A_60, k1_relat_1(A_60), k2_relat_1(A_60)) | ~v1_funct_1(A_60) | ~v1_relat_1(A_60))), inference(cnfTransformation, [status(thm)], [f_134])).
% 8.02/2.75  tff(c_3568, plain, (v1_funct_2('#skF_10', '#skF_8', k2_relat_1('#skF_10')) | ~v1_funct_1('#skF_10') | ~v1_relat_1('#skF_10')), inference(superposition, [status(thm), theory('equality')], [c_3547, c_80])).
% 8.02/2.75  tff(c_3580, plain, (v1_funct_2('#skF_10', '#skF_8', k2_relat_1('#skF_10')) | ~v1_relat_1('#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_517, c_3568])).
% 8.02/2.75  tff(c_3602, plain, (~v1_relat_1('#skF_10')), inference(splitLeft, [status(thm)], [c_3580])).
% 8.02/2.75  tff(c_3603, plain, (![A_511, B_512, D_513]: ('#skF_6'(A_511, B_512, k1_funct_2(A_511, B_512), D_513)=D_513 | ~r2_hidden(D_513, k1_funct_2(A_511, B_512)))), inference(cnfTransformation, [status(thm)], [f_124])).
% 8.02/2.75  tff(c_3622, plain, ('#skF_6'('#skF_8', '#skF_9', k1_funct_2('#skF_8', '#skF_9'), '#skF_10')='#skF_10'), inference(resolution, [status(thm)], [c_98, c_3603])).
% 8.02/2.75  tff(c_3651, plain, (![A_515, B_516, D_517]: (v1_relat_1('#skF_6'(A_515, B_516, k1_funct_2(A_515, B_516), D_517)) | ~r2_hidden(D_517, k1_funct_2(A_515, B_516)))), inference(cnfTransformation, [status(thm)], [f_124])).
% 8.02/2.75  tff(c_3654, plain, (v1_relat_1('#skF_10') | ~r2_hidden('#skF_10', k1_funct_2('#skF_8', '#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_3622, c_3651])).
% 8.02/2.75  tff(c_3656, plain, (v1_relat_1('#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_98, c_3654])).
% 8.02/2.75  tff(c_3658, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3602, c_3656])).
% 8.02/2.75  tff(c_3660, plain, (v1_relat_1('#skF_10')), inference(splitRight, [status(thm)], [c_3580])).
% 8.02/2.75  tff(c_2538, plain, (![A_435]: (m1_subset_1(A_435, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_435), k2_relat_1(A_435)))) | ~v1_funct_1(A_435) | ~v1_relat_1(A_435))), inference(cnfTransformation, [status(thm)], [f_134])).
% 8.02/2.75  tff(c_2553, plain, (![A_435]: (r1_tarski(A_435, k2_zfmisc_1(k1_relat_1(A_435), k2_relat_1(A_435))) | ~v1_funct_1(A_435) | ~v1_relat_1(A_435))), inference(resolution, [status(thm)], [c_2538, c_20])).
% 8.02/2.75  tff(c_3562, plain, (r1_tarski('#skF_10', k2_zfmisc_1('#skF_8', k2_relat_1('#skF_10'))) | ~v1_funct_1('#skF_10') | ~v1_relat_1('#skF_10')), inference(superposition, [status(thm), theory('equality')], [c_3547, c_2553])).
% 8.02/2.75  tff(c_3576, plain, (r1_tarski('#skF_10', k2_zfmisc_1('#skF_8', k2_relat_1('#skF_10'))) | ~v1_relat_1('#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_517, c_3562])).
% 8.02/2.75  tff(c_3684, plain, (r1_tarski('#skF_10', k2_zfmisc_1('#skF_8', k2_relat_1('#skF_10')))), inference(demodulation, [status(thm), theory('equality')], [c_3660, c_3576])).
% 8.02/2.75  tff(c_2365, plain, (![C_393, B_394, A_395]: (v1_xboole_0(C_393) | ~m1_subset_1(C_393, k1_zfmisc_1(k2_zfmisc_1(B_394, A_395))) | ~v1_xboole_0(A_395))), inference(cnfTransformation, [status(thm)], [f_68])).
% 8.02/2.75  tff(c_2374, plain, (![A_15, A_395, B_394]: (v1_xboole_0(A_15) | ~v1_xboole_0(A_395) | ~r1_tarski(A_15, k2_zfmisc_1(B_394, A_395)))), inference(resolution, [status(thm)], [c_22, c_2365])).
% 8.02/2.75  tff(c_3716, plain, (v1_xboole_0('#skF_10') | ~v1_xboole_0(k2_relat_1('#skF_10'))), inference(resolution, [status(thm)], [c_3684, c_2374])).
% 8.02/2.75  tff(c_3724, plain, (~v1_xboole_0(k2_relat_1('#skF_10'))), inference(splitLeft, [status(thm)], [c_3716])).
% 8.02/2.75  tff(c_2220, plain, (~v1_funct_2('#skF_10', '#skF_8', '#skF_9')), inference(splitRight, [status(thm)], [c_516])).
% 8.02/2.75  tff(c_4795, plain, (![C_607, A_608, B_609]: (v1_funct_2(C_607, A_608, B_609) | ~v1_partfun1(C_607, A_608) | ~v1_funct_1(C_607) | ~m1_subset_1(C_607, k1_zfmisc_1(k2_zfmisc_1(A_608, B_609))))), inference(cnfTransformation, [status(thm)], [f_94])).
% 8.02/2.75  tff(c_4808, plain, (v1_funct_2('#skF_10', '#skF_8', '#skF_9') | ~v1_partfun1('#skF_10', '#skF_8') | ~v1_funct_1('#skF_10')), inference(resolution, [status(thm)], [c_2221, c_4795])).
% 8.02/2.75  tff(c_4820, plain, (v1_funct_2('#skF_10', '#skF_8', '#skF_9') | ~v1_partfun1('#skF_10', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_517, c_4808])).
% 8.02/2.75  tff(c_4821, plain, (~v1_partfun1('#skF_10', '#skF_8')), inference(negUnitSimplification, [status(thm)], [c_2220, c_4820])).
% 8.02/2.75  tff(c_3659, plain, (v1_funct_2('#skF_10', '#skF_8', k2_relat_1('#skF_10'))), inference(splitRight, [status(thm)], [c_3580])).
% 8.02/2.75  tff(c_78, plain, (![A_60]: (m1_subset_1(A_60, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_60), k2_relat_1(A_60)))) | ~v1_funct_1(A_60) | ~v1_relat_1(A_60))), inference(cnfTransformation, [status(thm)], [f_134])).
% 8.02/2.75  tff(c_3565, plain, (m1_subset_1('#skF_10', k1_zfmisc_1(k2_zfmisc_1('#skF_8', k2_relat_1('#skF_10')))) | ~v1_funct_1('#skF_10') | ~v1_relat_1('#skF_10')), inference(superposition, [status(thm), theory('equality')], [c_3547, c_78])).
% 8.02/2.75  tff(c_3578, plain, (m1_subset_1('#skF_10', k1_zfmisc_1(k2_zfmisc_1('#skF_8', k2_relat_1('#skF_10')))) | ~v1_relat_1('#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_517, c_3565])).
% 8.02/2.75  tff(c_3797, plain, (m1_subset_1('#skF_10', k1_zfmisc_1(k2_zfmisc_1('#skF_8', k2_relat_1('#skF_10'))))), inference(demodulation, [status(thm), theory('equality')], [c_3660, c_3578])).
% 8.02/2.75  tff(c_6784, plain, (![C_724, A_725, B_726]: (v1_partfun1(C_724, A_725) | ~v1_funct_2(C_724, A_725, B_726) | ~v1_funct_1(C_724) | ~m1_subset_1(C_724, k1_zfmisc_1(k2_zfmisc_1(A_725, B_726))) | v1_xboole_0(B_726))), inference(cnfTransformation, [status(thm)], [f_108])).
% 8.02/2.75  tff(c_6790, plain, (v1_partfun1('#skF_10', '#skF_8') | ~v1_funct_2('#skF_10', '#skF_8', k2_relat_1('#skF_10')) | ~v1_funct_1('#skF_10') | v1_xboole_0(k2_relat_1('#skF_10'))), inference(resolution, [status(thm)], [c_3797, c_6784])).
% 8.02/2.75  tff(c_6808, plain, (v1_partfun1('#skF_10', '#skF_8') | v1_xboole_0(k2_relat_1('#skF_10'))), inference(demodulation, [status(thm), theory('equality')], [c_517, c_3659, c_6790])).
% 8.02/2.75  tff(c_6810, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3724, c_4821, c_6808])).
% 8.02/2.75  tff(c_6811, plain, (v1_xboole_0('#skF_10')), inference(splitRight, [status(thm)], [c_3716])).
% 8.02/2.75  tff(c_2401, plain, (![A_400, A_401, B_402]: (v1_xboole_0(A_400) | ~v1_xboole_0(A_401) | ~r1_tarski(A_400, k2_zfmisc_1(B_402, A_401)))), inference(resolution, [status(thm)], [c_22, c_2365])).
% 8.02/2.75  tff(c_2420, plain, (![B_403, A_404]: (v1_xboole_0(k2_zfmisc_1(B_403, A_404)) | ~v1_xboole_0(A_404))), inference(resolution, [status(thm)], [c_16, c_2401])).
% 8.02/2.75  tff(c_118, plain, (![A_75, B_76]: (r2_hidden('#skF_2'(A_75, B_76), A_75) | r1_tarski(A_75, B_76))), inference(cnfTransformation, [status(thm)], [f_38])).
% 8.02/2.75  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 8.02/2.75  tff(c_128, plain, (![A_75, B_76]: (~v1_xboole_0(A_75) | r1_tarski(A_75, B_76))), inference(resolution, [status(thm)], [c_118, c_2])).
% 8.02/2.75  tff(c_519, plain, (![B_177, A_178]: (B_177=A_178 | ~r1_tarski(B_177, A_178) | ~r1_tarski(A_178, B_177))), inference(cnfTransformation, [status(thm)], [f_44])).
% 8.02/2.75  tff(c_2234, plain, (![B_369, A_370]: (B_369=A_370 | ~r1_tarski(B_369, A_370) | ~v1_xboole_0(A_370))), inference(resolution, [status(thm)], [c_128, c_519])).
% 8.02/2.75  tff(c_2245, plain, (![B_76, A_75]: (B_76=A_75 | ~v1_xboole_0(B_76) | ~v1_xboole_0(A_75))), inference(resolution, [status(thm)], [c_128, c_2234])).
% 8.02/2.75  tff(c_2426, plain, (![B_403, A_404, A_75]: (k2_zfmisc_1(B_403, A_404)=A_75 | ~v1_xboole_0(A_75) | ~v1_xboole_0(A_404))), inference(resolution, [status(thm)], [c_2420, c_2245])).
% 8.02/2.75  tff(c_6989, plain, (![B_735, A_736]: (k2_zfmisc_1(B_735, A_736)='#skF_10' | ~v1_xboole_0(A_736))), inference(resolution, [status(thm)], [c_6811, c_2426])).
% 8.02/2.75  tff(c_6994, plain, (![B_735]: (k2_zfmisc_1(B_735, '#skF_10')='#skF_10')), inference(resolution, [status(thm)], [c_6811, c_6989])).
% 8.02/2.75  tff(c_6812, plain, (v1_xboole_0(k2_relat_1('#skF_10'))), inference(splitRight, [status(thm)], [c_3716])).
% 8.02/2.75  tff(c_6844, plain, (![A_727]: (A_727='#skF_10' | ~v1_xboole_0(A_727))), inference(resolution, [status(thm)], [c_6811, c_2245])).
% 8.02/2.75  tff(c_6854, plain, (k2_relat_1('#skF_10')='#skF_10'), inference(resolution, [status(thm)], [c_6812, c_6844])).
% 8.02/2.75  tff(c_6878, plain, (m1_subset_1('#skF_10', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_10'), '#skF_10'))) | ~v1_funct_1('#skF_10') | ~v1_relat_1('#skF_10')), inference(superposition, [status(thm), theory('equality')], [c_6854, c_78])).
% 8.02/2.75  tff(c_6893, plain, (m1_subset_1('#skF_10', k1_zfmisc_1(k2_zfmisc_1('#skF_8', '#skF_10')))), inference(demodulation, [status(thm), theory('equality')], [c_3660, c_517, c_3547, c_6878])).
% 8.02/2.75  tff(c_7062, plain, (m1_subset_1('#skF_10', k1_zfmisc_1('#skF_10'))), inference(demodulation, [status(thm), theory('equality')], [c_6994, c_6893])).
% 8.02/2.75  tff(c_2464, plain, (![A_419, B_420, A_421]: (k1_relset_1(A_419, B_420, A_421)=k1_relat_1(A_421) | ~r1_tarski(A_421, k2_zfmisc_1(A_419, B_420)))), inference(resolution, [status(thm)], [c_22, c_2446])).
% 8.02/2.75  tff(c_2482, plain, (![A_419, B_420, A_75]: (k1_relset_1(A_419, B_420, A_75)=k1_relat_1(A_75) | ~v1_xboole_0(A_75))), inference(resolution, [status(thm)], [c_128, c_2464])).
% 8.02/2.75  tff(c_6814, plain, (![A_419, B_420]: (k1_relset_1(A_419, B_420, '#skF_10')=k1_relat_1('#skF_10'))), inference(resolution, [status(thm)], [c_6811, c_2482])).
% 8.02/2.75  tff(c_6900, plain, (![A_728, B_729]: (k1_relset_1(A_728, B_729, '#skF_10')='#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_3547, c_6814])).
% 8.02/2.75  tff(c_28, plain, (![A_24, B_25, C_26]: (m1_subset_1(k1_relset_1(A_24, B_25, C_26), k1_zfmisc_1(A_24)) | ~m1_subset_1(C_26, k1_zfmisc_1(k2_zfmisc_1(A_24, B_25))))), inference(cnfTransformation, [status(thm)], [f_72])).
% 8.02/2.75  tff(c_7550, plain, (![A_779, B_780]: (m1_subset_1('#skF_8', k1_zfmisc_1(A_779)) | ~m1_subset_1('#skF_10', k1_zfmisc_1(k2_zfmisc_1(A_779, B_780))))), inference(superposition, [status(thm), theory('equality')], [c_6900, c_28])).
% 8.02/2.75  tff(c_7556, plain, (![B_735]: (m1_subset_1('#skF_8', k1_zfmisc_1(B_735)) | ~m1_subset_1('#skF_10', k1_zfmisc_1('#skF_10')))), inference(superposition, [status(thm), theory('equality')], [c_6994, c_7550])).
% 8.02/2.75  tff(c_7581, plain, (![B_781]: (m1_subset_1('#skF_8', k1_zfmisc_1(B_781)))), inference(demodulation, [status(thm), theory('equality')], [c_7062, c_7556])).
% 8.02/2.75  tff(c_6998, plain, (![B_737]: (k2_zfmisc_1(B_737, '#skF_10')='#skF_10')), inference(resolution, [status(thm)], [c_6811, c_6989])).
% 8.02/2.75  tff(c_26, plain, (![C_23, B_21, A_20]: (v1_xboole_0(C_23) | ~m1_subset_1(C_23, k1_zfmisc_1(k2_zfmisc_1(B_21, A_20))) | ~v1_xboole_0(A_20))), inference(cnfTransformation, [status(thm)], [f_68])).
% 8.02/2.75  tff(c_7018, plain, (![C_23]: (v1_xboole_0(C_23) | ~m1_subset_1(C_23, k1_zfmisc_1('#skF_10')) | ~v1_xboole_0('#skF_10'))), inference(superposition, [status(thm), theory('equality')], [c_6998, c_26])).
% 8.02/2.75  tff(c_7028, plain, (![C_23]: (v1_xboole_0(C_23) | ~m1_subset_1(C_23, k1_zfmisc_1('#skF_10')))), inference(demodulation, [status(thm), theory('equality')], [c_6811, c_7018])).
% 8.02/2.75  tff(c_7585, plain, (v1_xboole_0('#skF_8')), inference(resolution, [status(thm)], [c_7581, c_7028])).
% 8.02/2.75  tff(c_7602, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2707, c_7585])).
% 8.02/2.75  tff(c_7604, plain, (v1_xboole_0('#skF_8')), inference(splitRight, [status(thm)], [c_2702])).
% 8.02/2.75  tff(c_7603, plain, (v1_xboole_0(k1_relat_1('#skF_10'))), inference(splitRight, [status(thm)], [c_2702])).
% 8.02/2.75  tff(c_7649, plain, (![A_785]: (A_785='#skF_8' | ~v1_xboole_0(A_785))), inference(resolution, [status(thm)], [c_7604, c_2245])).
% 8.02/2.75  tff(c_7659, plain, (k1_relat_1('#skF_10')='#skF_8'), inference(resolution, [status(thm)], [c_7603, c_7649])).
% 8.02/2.75  tff(c_7669, plain, (m1_subset_1('#skF_8', k1_zfmisc_1('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_7659, c_2670])).
% 8.02/2.75  tff(c_24, plain, (![C_19, B_18, A_17]: (~v1_xboole_0(C_19) | ~m1_subset_1(B_18, k1_zfmisc_1(C_19)) | ~r2_hidden(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_61])).
% 8.02/2.75  tff(c_7703, plain, (![A_17]: (~v1_xboole_0('#skF_8') | ~r2_hidden(A_17, '#skF_8'))), inference(resolution, [status(thm)], [c_7669, c_24])).
% 8.02/2.75  tff(c_7709, plain, (![A_17]: (~r2_hidden(A_17, '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_7604, c_7703])).
% 8.02/2.75  tff(c_7605, plain, (![A_782, B_783, D_784]: ('#skF_6'(A_782, B_783, k1_funct_2(A_782, B_783), D_784)=D_784 | ~r2_hidden(D_784, k1_funct_2(A_782, B_783)))), inference(cnfTransformation, [status(thm)], [f_124])).
% 8.02/2.75  tff(c_7624, plain, ('#skF_6'('#skF_8', '#skF_9', k1_funct_2('#skF_8', '#skF_9'), '#skF_10')='#skF_10'), inference(resolution, [status(thm)], [c_98, c_7605])).
% 8.02/2.75  tff(c_7785, plain, (![A_788, B_789, D_790]: (v1_relat_1('#skF_6'(A_788, B_789, k1_funct_2(A_788, B_789), D_790)) | ~r2_hidden(D_790, k1_funct_2(A_788, B_789)))), inference(cnfTransformation, [status(thm)], [f_124])).
% 8.02/2.75  tff(c_7788, plain, (v1_relat_1('#skF_10') | ~r2_hidden('#skF_10', k1_funct_2('#skF_8', '#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_7624, c_7785])).
% 8.02/2.75  tff(c_7790, plain, (v1_relat_1('#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_98, c_7788])).
% 8.02/2.75  tff(c_9031, plain, (![C_875, B_876]: (r2_hidden('#skF_7'(k1_relat_1(C_875), B_876, C_875), k1_relat_1(C_875)) | v1_funct_2(C_875, k1_relat_1(C_875), B_876) | ~v1_funct_1(C_875) | ~v1_relat_1(C_875))), inference(cnfTransformation, [status(thm)], [f_151])).
% 8.02/2.75  tff(c_9059, plain, (![B_876]: (r2_hidden('#skF_7'('#skF_8', B_876, '#skF_10'), k1_relat_1('#skF_10')) | v1_funct_2('#skF_10', k1_relat_1('#skF_10'), B_876) | ~v1_funct_1('#skF_10') | ~v1_relat_1('#skF_10'))), inference(superposition, [status(thm), theory('equality')], [c_7659, c_9031])).
% 8.02/2.75  tff(c_9071, plain, (![B_876]: (r2_hidden('#skF_7'('#skF_8', B_876, '#skF_10'), '#skF_8') | v1_funct_2('#skF_10', '#skF_8', B_876))), inference(demodulation, [status(thm), theory('equality')], [c_7790, c_517, c_7659, c_7659, c_9059])).
% 8.02/2.75  tff(c_9072, plain, (![B_876]: (v1_funct_2('#skF_10', '#skF_8', B_876))), inference(negUnitSimplification, [status(thm)], [c_7709, c_9071])).
% 8.02/2.75  tff(c_9079, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_9072, c_2220])).
% 8.02/2.75  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.02/2.75  
% 8.02/2.75  Inference rules
% 8.02/2.75  ----------------------
% 8.02/2.75  #Ref     : 0
% 8.02/2.75  #Sup     : 2228
% 8.02/2.75  #Fact    : 0
% 8.02/2.75  #Define  : 0
% 8.02/2.75  #Split   : 42
% 8.02/2.75  #Chain   : 0
% 8.02/2.75  #Close   : 0
% 8.02/2.75  
% 8.02/2.75  Ordering : KBO
% 8.02/2.75  
% 8.02/2.75  Simplification rules
% 8.02/2.75  ----------------------
% 8.02/2.75  #Subsume      : 751
% 8.02/2.75  #Demod        : 580
% 8.02/2.75  #Tautology    : 418
% 8.02/2.75  #SimpNegUnit  : 25
% 8.02/2.75  #BackRed      : 24
% 8.02/2.75  
% 8.02/2.75  #Partial instantiations: 0
% 8.02/2.75  #Strategies tried      : 1
% 8.02/2.75  
% 8.02/2.75  Timing (in seconds)
% 8.02/2.75  ----------------------
% 8.02/2.75  Preprocessing        : 0.41
% 8.02/2.75  Parsing              : 0.19
% 8.02/2.75  CNF conversion       : 0.03
% 8.02/2.75  Main loop            : 1.57
% 8.02/2.75  Inferencing          : 0.52
% 8.02/2.75  Reduction            : 0.44
% 8.02/2.75  Demodulation         : 0.30
% 8.02/2.75  BG Simplification    : 0.07
% 8.02/2.75  Subsumption          : 0.40
% 8.02/2.75  Abstraction          : 0.08
% 8.02/2.75  MUC search           : 0.00
% 8.02/2.75  Cooper               : 0.00
% 8.02/2.75  Total                : 2.02
% 8.02/2.75  Index Insertion      : 0.00
% 8.02/2.75  Index Deletion       : 0.00
% 8.02/2.75  Index Matching       : 0.00
% 8.02/2.75  BG Taut test         : 0.00
%------------------------------------------------------------------------------
