%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:16:39 EST 2020

% Result     : Theorem 8.78s
% Output     : CNFRefutation 8.78s
% Verified   : 
% Statistics : Number of formulae       :  162 (1329 expanded)
%              Number of leaves         :   39 ( 390 expanded)
%              Depth                    :   23
%              Number of atoms          :  283 (3036 expanded)
%              Number of equality atoms :   36 ( 310 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v1_partfun1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_2 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_4 > #skF_7 > #skF_6 > #skF_2 > #skF_8 > #skF_5 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(v1_partfun1,type,(
    v1_partfun1: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_2,type,(
    k1_funct_2: ( $i * $i ) > $i )).

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

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_144,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r2_hidden(C,k1_funct_2(A,B))
       => ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t121_funct_2)).

tff(f_125,axiom,(
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

tff(f_78,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( ( r1_tarski(k1_relat_1(C),A)
          & r1_tarski(k2_relat_1(C),B) )
       => m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_relset_1)).

tff(f_95,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => v1_partfun1(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_partfun1)).

tff(f_70,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_66,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k1_relset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_relset_1)).

tff(f_48,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_135,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_funct_1(A)
        & v1_funct_2(A,k1_relat_1(A),k2_relat_1(A))
        & m1_subset_1(A,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A)))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_funct_2)).

tff(f_62,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(B,A)))
         => v1_xboole_0(C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc4_relset_1)).

tff(f_88,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( ( v1_funct_1(C)
          & v1_partfun1(C,A) )
       => ( v1_funct_1(C)
          & v1_funct_2(C,A,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_funct_2)).

tff(f_109,axiom,(
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

tff(f_55,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

tff(c_84,plain,(
    r2_hidden('#skF_8',k1_funct_2('#skF_6','#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_959,plain,(
    ! [A_261,B_262,D_263] :
      ( '#skF_5'(A_261,B_262,k1_funct_2(A_261,B_262),D_263) = D_263
      | ~ r2_hidden(D_263,k1_funct_2(A_261,B_262)) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_970,plain,(
    '#skF_5'('#skF_6','#skF_7',k1_funct_2('#skF_6','#skF_7'),'#skF_8') = '#skF_8' ),
    inference(resolution,[status(thm)],[c_84,c_959])).

tff(c_980,plain,(
    ! [A_264,B_265,D_266] :
      ( v1_relat_1('#skF_5'(A_264,B_265,k1_funct_2(A_264,B_265),D_266))
      | ~ r2_hidden(D_266,k1_funct_2(A_264,B_265)) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_983,plain,
    ( v1_relat_1('#skF_8')
    | ~ r2_hidden('#skF_8',k1_funct_2('#skF_6','#skF_7')) ),
    inference(superposition,[status(thm),theory(equality)],[c_970,c_980])).

tff(c_985,plain,(
    v1_relat_1('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_983])).

tff(c_12,plain,(
    ! [B_7] : r1_tarski(B_7,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_1074,plain,(
    ! [A_276,B_277,D_278] :
      ( k1_relat_1('#skF_5'(A_276,B_277,k1_funct_2(A_276,B_277),D_278)) = A_276
      | ~ r2_hidden(D_278,k1_funct_2(A_276,B_277)) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_1098,plain,
    ( k1_relat_1('#skF_8') = '#skF_6'
    | ~ r2_hidden('#skF_8',k1_funct_2('#skF_6','#skF_7')) ),
    inference(superposition,[status(thm),theory(equality)],[c_970,c_1074])).

tff(c_1102,plain,(
    k1_relat_1('#skF_8') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_1098])).

tff(c_1455,plain,(
    ! [A_303,B_304,D_305] :
      ( r1_tarski(k2_relat_1('#skF_5'(A_303,B_304,k1_funct_2(A_303,B_304),D_305)),B_304)
      | ~ r2_hidden(D_305,k1_funct_2(A_303,B_304)) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_1470,plain,
    ( r1_tarski(k2_relat_1('#skF_8'),'#skF_7')
    | ~ r2_hidden('#skF_8',k1_funct_2('#skF_6','#skF_7')) ),
    inference(superposition,[status(thm),theory(equality)],[c_970,c_1455])).

tff(c_1476,plain,(
    r1_tarski(k2_relat_1('#skF_8'),'#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_1470])).

tff(c_1885,plain,(
    ! [C_347,A_348,B_349] :
      ( m1_subset_1(C_347,k1_zfmisc_1(k2_zfmisc_1(A_348,B_349)))
      | ~ r1_tarski(k2_relat_1(C_347),B_349)
      | ~ r1_tarski(k1_relat_1(C_347),A_348)
      | ~ v1_relat_1(C_347) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_82,plain,
    ( ~ m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_7')))
    | ~ v1_funct_2('#skF_8','#skF_6','#skF_7')
    | ~ v1_funct_1('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_119,plain,(
    ~ v1_funct_1('#skF_8') ),
    inference(splitLeft,[status(thm)],[c_82])).

tff(c_650,plain,(
    ! [A_173,B_174,D_175] :
      ( '#skF_5'(A_173,B_174,k1_funct_2(A_173,B_174),D_175) = D_175
      | ~ r2_hidden(D_175,k1_funct_2(A_173,B_174)) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_661,plain,(
    '#skF_5'('#skF_6','#skF_7',k1_funct_2('#skF_6','#skF_7'),'#skF_8') = '#skF_8' ),
    inference(resolution,[status(thm)],[c_84,c_650])).

tff(c_679,plain,(
    ! [A_180,B_181,D_182] :
      ( v1_funct_1('#skF_5'(A_180,B_181,k1_funct_2(A_180,B_181),D_182))
      | ~ r2_hidden(D_182,k1_funct_2(A_180,B_181)) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_682,plain,
    ( v1_funct_1('#skF_8')
    | ~ r2_hidden('#skF_8',k1_funct_2('#skF_6','#skF_7')) ),
    inference(superposition,[status(thm),theory(equality)],[c_661,c_679])).

tff(c_684,plain,(
    v1_funct_1('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_682])).

tff(c_686,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_119,c_684])).

tff(c_687,plain,
    ( ~ v1_funct_2('#skF_8','#skF_6','#skF_7')
    | ~ m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_7'))) ),
    inference(splitRight,[status(thm)],[c_82])).

tff(c_695,plain,(
    ~ m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_7'))) ),
    inference(splitLeft,[status(thm)],[c_687])).

tff(c_1896,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_8'),'#skF_7')
    | ~ r1_tarski(k1_relat_1('#skF_8'),'#skF_6')
    | ~ v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_1885,c_695])).

tff(c_1906,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_985,c_12,c_1102,c_1476,c_1896])).

tff(c_1907,plain,(
    ~ v1_funct_2('#skF_8','#skF_6','#skF_7') ),
    inference(splitRight,[status(thm)],[c_687])).

tff(c_688,plain,(
    v1_funct_1('#skF_8') ),
    inference(splitRight,[status(thm)],[c_82])).

tff(c_1908,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_7'))) ),
    inference(splitRight,[status(thm)],[c_687])).

tff(c_2078,plain,(
    ! [C_385,A_386,B_387] :
      ( v1_partfun1(C_385,A_386)
      | ~ m1_subset_1(C_385,k1_zfmisc_1(k2_zfmisc_1(A_386,B_387)))
      | ~ v1_xboole_0(A_386) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_2086,plain,
    ( v1_partfun1('#skF_8','#skF_6')
    | ~ v1_xboole_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_1908,c_2078])).

tff(c_2088,plain,(
    ~ v1_xboole_0('#skF_6') ),
    inference(splitLeft,[status(thm)],[c_2086])).

tff(c_2674,plain,(
    ! [A_449,B_450,D_451] :
      ( '#skF_5'(A_449,B_450,k1_funct_2(A_449,B_450),D_451) = D_451
      | ~ r2_hidden(D_451,k1_funct_2(A_449,B_450)) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_2685,plain,(
    '#skF_5'('#skF_6','#skF_7',k1_funct_2('#skF_6','#skF_7'),'#skF_8') = '#skF_8' ),
    inference(resolution,[status(thm)],[c_84,c_2674])).

tff(c_2786,plain,(
    ! [A_466,B_467,D_468] :
      ( k1_relat_1('#skF_5'(A_466,B_467,k1_funct_2(A_466,B_467),D_468)) = A_466
      | ~ r2_hidden(D_468,k1_funct_2(A_466,B_467)) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_2807,plain,
    ( k1_relat_1('#skF_8') = '#skF_6'
    | ~ r2_hidden('#skF_8',k1_funct_2('#skF_6','#skF_7')) ),
    inference(superposition,[status(thm),theory(equality)],[c_2685,c_2786])).

tff(c_2811,plain,(
    k1_relat_1('#skF_8') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_2807])).

tff(c_2089,plain,(
    ! [A_388,B_389,C_390] :
      ( k1_relset_1(A_388,B_389,C_390) = k1_relat_1(C_390)
      | ~ m1_subset_1(C_390,k1_zfmisc_1(k2_zfmisc_1(A_388,B_389))) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_2097,plain,(
    k1_relset_1('#skF_6','#skF_7','#skF_8') = k1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_1908,c_2089])).

tff(c_2289,plain,(
    ! [A_420,B_421,C_422] :
      ( m1_subset_1(k1_relset_1(A_420,B_421,C_422),k1_zfmisc_1(A_420))
      | ~ m1_subset_1(C_422,k1_zfmisc_1(k2_zfmisc_1(A_420,B_421))) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_2315,plain,
    ( m1_subset_1(k1_relat_1('#skF_8'),k1_zfmisc_1('#skF_6'))
    | ~ m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_7'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_2097,c_2289])).

tff(c_2322,plain,(
    m1_subset_1(k1_relat_1('#skF_8'),k1_zfmisc_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1908,c_2315])).

tff(c_16,plain,(
    ! [A_11,B_12] :
      ( r1_tarski(A_11,B_12)
      | ~ m1_subset_1(A_11,k1_zfmisc_1(B_12)) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_2329,plain,(
    r1_tarski(k1_relat_1('#skF_8'),'#skF_6') ),
    inference(resolution,[status(thm)],[c_2322,c_16])).

tff(c_8,plain,(
    ! [B_7,A_6] :
      ( B_7 = A_6
      | ~ r1_tarski(B_7,A_6)
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_2348,plain,
    ( k1_relat_1('#skF_8') = '#skF_6'
    | ~ r1_tarski('#skF_6',k1_relat_1('#skF_8')) ),
    inference(resolution,[status(thm)],[c_2329,c_8])).

tff(c_2361,plain,(
    ~ r1_tarski('#skF_6',k1_relat_1('#skF_8')) ),
    inference(splitLeft,[status(thm)],[c_2348])).

tff(c_2815,plain,(
    ~ r1_tarski('#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2811,c_2361])).

tff(c_2824,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_2815])).

tff(c_2825,plain,(
    k1_relat_1('#skF_8') = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_2348])).

tff(c_78,plain,(
    ! [A_60] :
      ( v1_funct_2(A_60,k1_relat_1(A_60),k2_relat_1(A_60))
      | ~ v1_funct_1(A_60)
      | ~ v1_relat_1(A_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_2847,plain,
    ( v1_funct_2('#skF_8','#skF_6',k2_relat_1('#skF_8'))
    | ~ v1_funct_1('#skF_8')
    | ~ v1_relat_1('#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_2825,c_78])).

tff(c_2859,plain,
    ( v1_funct_2('#skF_8','#skF_6',k2_relat_1('#skF_8'))
    | ~ v1_relat_1('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_688,c_2847])).

tff(c_2880,plain,(
    ~ v1_relat_1('#skF_8') ),
    inference(splitLeft,[status(thm)],[c_2859])).

tff(c_2881,plain,(
    ! [A_469,B_470,D_471] :
      ( '#skF_5'(A_469,B_470,k1_funct_2(A_469,B_470),D_471) = D_471
      | ~ r2_hidden(D_471,k1_funct_2(A_469,B_470)) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_2892,plain,(
    '#skF_5'('#skF_6','#skF_7',k1_funct_2('#skF_6','#skF_7'),'#skF_8') = '#skF_8' ),
    inference(resolution,[status(thm)],[c_84,c_2881])).

tff(c_3210,plain,(
    ! [A_501,B_502,D_503] :
      ( v1_relat_1('#skF_5'(A_501,B_502,k1_funct_2(A_501,B_502),D_503))
      | ~ r2_hidden(D_503,k1_funct_2(A_501,B_502)) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_3213,plain,
    ( v1_relat_1('#skF_8')
    | ~ r2_hidden('#skF_8',k1_funct_2('#skF_6','#skF_7')) ),
    inference(superposition,[status(thm),theory(equality)],[c_2892,c_3210])).

tff(c_3215,plain,(
    v1_relat_1('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_3213])).

tff(c_3217,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2880,c_3215])).

tff(c_3219,plain,(
    v1_relat_1('#skF_8') ),
    inference(splitRight,[status(thm)],[c_2859])).

tff(c_2188,plain,(
    ! [A_409] :
      ( m1_subset_1(A_409,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_409),k2_relat_1(A_409))))
      | ~ v1_funct_1(A_409)
      | ~ v1_relat_1(A_409) ) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_2207,plain,(
    ! [A_409] :
      ( r1_tarski(A_409,k2_zfmisc_1(k1_relat_1(A_409),k2_relat_1(A_409)))
      | ~ v1_funct_1(A_409)
      | ~ v1_relat_1(A_409) ) ),
    inference(resolution,[status(thm)],[c_2188,c_16])).

tff(c_2841,plain,
    ( r1_tarski('#skF_8',k2_zfmisc_1('#skF_6',k2_relat_1('#skF_8')))
    | ~ v1_funct_1('#skF_8')
    | ~ v1_relat_1('#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_2825,c_2207])).

tff(c_2855,plain,
    ( r1_tarski('#skF_8',k2_zfmisc_1('#skF_6',k2_relat_1('#skF_8')))
    | ~ v1_relat_1('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_688,c_2841])).

tff(c_3221,plain,(
    r1_tarski('#skF_8',k2_zfmisc_1('#skF_6',k2_relat_1('#skF_8'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3219,c_2855])).

tff(c_18,plain,(
    ! [A_11,B_12] :
      ( m1_subset_1(A_11,k1_zfmisc_1(B_12))
      | ~ r1_tarski(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_2017,plain,(
    ! [C_367,B_368,A_369] :
      ( v1_xboole_0(C_367)
      | ~ m1_subset_1(C_367,k1_zfmisc_1(k2_zfmisc_1(B_368,A_369)))
      | ~ v1_xboole_0(A_369) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_2026,plain,(
    ! [A_11,A_369,B_368] :
      ( v1_xboole_0(A_11)
      | ~ v1_xboole_0(A_369)
      | ~ r1_tarski(A_11,k2_zfmisc_1(B_368,A_369)) ) ),
    inference(resolution,[status(thm)],[c_18,c_2017])).

tff(c_3250,plain,
    ( v1_xboole_0('#skF_8')
    | ~ v1_xboole_0(k2_relat_1('#skF_8')) ),
    inference(resolution,[status(thm)],[c_3221,c_2026])).

tff(c_3256,plain,(
    ~ v1_xboole_0(k2_relat_1('#skF_8')) ),
    inference(splitLeft,[status(thm)],[c_3250])).

tff(c_5939,plain,(
    ! [C_737,A_738,B_739] :
      ( v1_funct_2(C_737,A_738,B_739)
      | ~ v1_partfun1(C_737,A_738)
      | ~ v1_funct_1(C_737)
      | ~ m1_subset_1(C_737,k1_zfmisc_1(k2_zfmisc_1(A_738,B_739))) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_5952,plain,
    ( v1_funct_2('#skF_8','#skF_6','#skF_7')
    | ~ v1_partfun1('#skF_8','#skF_6')
    | ~ v1_funct_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_1908,c_5939])).

tff(c_5964,plain,
    ( v1_funct_2('#skF_8','#skF_6','#skF_7')
    | ~ v1_partfun1('#skF_8','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_688,c_5952])).

tff(c_5965,plain,(
    ~ v1_partfun1('#skF_8','#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_1907,c_5964])).

tff(c_3218,plain,(
    v1_funct_2('#skF_8','#skF_6',k2_relat_1('#skF_8')) ),
    inference(splitRight,[status(thm)],[c_2859])).

tff(c_76,plain,(
    ! [A_60] :
      ( m1_subset_1(A_60,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_60),k2_relat_1(A_60))))
      | ~ v1_funct_1(A_60)
      | ~ v1_relat_1(A_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_2844,plain,
    ( m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_6',k2_relat_1('#skF_8'))))
    | ~ v1_funct_1('#skF_8')
    | ~ v1_relat_1('#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_2825,c_76])).

tff(c_2857,plain,
    ( m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_6',k2_relat_1('#skF_8'))))
    | ~ v1_relat_1('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_688,c_2844])).

tff(c_3289,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_6',k2_relat_1('#skF_8')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3219,c_2857])).

tff(c_10734,plain,(
    ! [C_951,A_952,B_953] :
      ( v1_partfun1(C_951,A_952)
      | ~ v1_funct_2(C_951,A_952,B_953)
      | ~ v1_funct_1(C_951)
      | ~ m1_subset_1(C_951,k1_zfmisc_1(k2_zfmisc_1(A_952,B_953)))
      | v1_xboole_0(B_953) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_10743,plain,
    ( v1_partfun1('#skF_8','#skF_6')
    | ~ v1_funct_2('#skF_8','#skF_6',k2_relat_1('#skF_8'))
    | ~ v1_funct_1('#skF_8')
    | v1_xboole_0(k2_relat_1('#skF_8')) ),
    inference(resolution,[status(thm)],[c_3289,c_10734])).

tff(c_10761,plain,
    ( v1_partfun1('#skF_8','#skF_6')
    | v1_xboole_0(k2_relat_1('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_688,c_3218,c_10743])).

tff(c_10763,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3256,c_5965,c_10761])).

tff(c_10764,plain,(
    v1_xboole_0('#skF_8') ),
    inference(splitRight,[status(thm)],[c_3250])).

tff(c_2029,plain,(
    ! [A_371,A_372,B_373] :
      ( v1_xboole_0(A_371)
      | ~ v1_xboole_0(A_372)
      | ~ r1_tarski(A_371,k2_zfmisc_1(B_373,A_372)) ) ),
    inference(resolution,[status(thm)],[c_18,c_2017])).

tff(c_2048,plain,(
    ! [B_374,A_375] :
      ( v1_xboole_0(k2_zfmisc_1(B_374,A_375))
      | ~ v1_xboole_0(A_375) ) ),
    inference(resolution,[status(thm)],[c_12,c_2029])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_108,plain,(
    ! [C_72,B_73,A_74] :
      ( ~ v1_xboole_0(C_72)
      | ~ m1_subset_1(B_73,k1_zfmisc_1(C_72))
      | ~ r2_hidden(A_74,B_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_112,plain,(
    ! [B_75,A_76,A_77] :
      ( ~ v1_xboole_0(B_75)
      | ~ r2_hidden(A_76,A_77)
      | ~ r1_tarski(A_77,B_75) ) ),
    inference(resolution,[status(thm)],[c_18,c_108])).

tff(c_1920,plain,(
    ! [B_350,A_351,B_352] :
      ( ~ v1_xboole_0(B_350)
      | ~ r1_tarski(A_351,B_350)
      | r1_tarski(A_351,B_352) ) ),
    inference(resolution,[status(thm)],[c_6,c_112])).

tff(c_1926,plain,(
    ! [B_7,B_352] :
      ( ~ v1_xboole_0(B_7)
      | r1_tarski(B_7,B_352) ) ),
    inference(resolution,[status(thm)],[c_12,c_1920])).

tff(c_1927,plain,(
    ! [B_353,B_354] :
      ( ~ v1_xboole_0(B_353)
      | r1_tarski(B_353,B_354) ) ),
    inference(resolution,[status(thm)],[c_12,c_1920])).

tff(c_1939,plain,(
    ! [B_356,B_355] :
      ( B_356 = B_355
      | ~ r1_tarski(B_355,B_356)
      | ~ v1_xboole_0(B_356) ) ),
    inference(resolution,[status(thm)],[c_1927,c_8])).

tff(c_1949,plain,(
    ! [B_7,B_352] :
      ( B_7 = B_352
      | ~ v1_xboole_0(B_352)
      | ~ v1_xboole_0(B_7) ) ),
    inference(resolution,[status(thm)],[c_1926,c_1939])).

tff(c_2054,plain,(
    ! [B_374,A_375,B_7] :
      ( k2_zfmisc_1(B_374,A_375) = B_7
      | ~ v1_xboole_0(B_7)
      | ~ v1_xboole_0(A_375) ) ),
    inference(resolution,[status(thm)],[c_2048,c_1949])).

tff(c_10924,plain,(
    ! [B_961,A_962] :
      ( k2_zfmisc_1(B_961,A_962) = '#skF_8'
      | ~ v1_xboole_0(A_962) ) ),
    inference(resolution,[status(thm)],[c_10764,c_2054])).

tff(c_10929,plain,(
    ! [B_961] : k2_zfmisc_1(B_961,'#skF_8') = '#skF_8' ),
    inference(resolution,[status(thm)],[c_10764,c_10924])).

tff(c_10765,plain,(
    v1_xboole_0(k2_relat_1('#skF_8')) ),
    inference(splitRight,[status(thm)],[c_3250])).

tff(c_10797,plain,(
    ! [B_954] :
      ( B_954 = '#skF_8'
      | ~ v1_xboole_0(B_954) ) ),
    inference(resolution,[status(thm)],[c_10764,c_1949])).

tff(c_10807,plain,(
    k2_relat_1('#skF_8') = '#skF_8' ),
    inference(resolution,[status(thm)],[c_10765,c_10797])).

tff(c_10840,plain,
    ( m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_8'),'#skF_8')))
    | ~ v1_funct_1('#skF_8')
    | ~ v1_relat_1('#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_10807,c_76])).

tff(c_10855,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_8'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3219,c_688,c_2825,c_10840])).

tff(c_10999,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10929,c_10855])).

tff(c_2152,plain,(
    ! [A_402,B_403,A_404] :
      ( k1_relset_1(A_402,B_403,A_404) = k1_relat_1(A_404)
      | ~ r1_tarski(A_404,k2_zfmisc_1(A_402,B_403)) ) ),
    inference(resolution,[status(thm)],[c_18,c_2089])).

tff(c_2168,plain,(
    ! [A_402,B_403,B_7] :
      ( k1_relset_1(A_402,B_403,B_7) = k1_relat_1(B_7)
      | ~ v1_xboole_0(B_7) ) ),
    inference(resolution,[status(thm)],[c_1926,c_2152])).

tff(c_10767,plain,(
    ! [A_402,B_403] : k1_relset_1(A_402,B_403,'#skF_8') = k1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_10764,c_2168])).

tff(c_10862,plain,(
    ! [A_956,B_957] : k1_relset_1(A_956,B_957,'#skF_8') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2825,c_10767])).

tff(c_24,plain,(
    ! [A_20,B_21,C_22] :
      ( m1_subset_1(k1_relset_1(A_20,B_21,C_22),k1_zfmisc_1(A_20))
      | ~ m1_subset_1(C_22,k1_zfmisc_1(k2_zfmisc_1(A_20,B_21))) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_11536,plain,(
    ! [A_1010,B_1011] :
      ( m1_subset_1('#skF_6',k1_zfmisc_1(A_1010))
      | ~ m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1(A_1010,B_1011))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10862,c_24])).

tff(c_11542,plain,(
    ! [B_961] :
      ( m1_subset_1('#skF_6',k1_zfmisc_1(B_961))
      | ~ m1_subset_1('#skF_8',k1_zfmisc_1('#skF_8')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10929,c_11536])).

tff(c_11567,plain,(
    ! [B_1012] : m1_subset_1('#skF_6',k1_zfmisc_1(B_1012)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10999,c_11542])).

tff(c_10933,plain,(
    ! [B_963] : k2_zfmisc_1(B_963,'#skF_8') = '#skF_8' ),
    inference(resolution,[status(thm)],[c_10764,c_10924])).

tff(c_22,plain,(
    ! [C_19,B_17,A_16] :
      ( v1_xboole_0(C_19)
      | ~ m1_subset_1(C_19,k1_zfmisc_1(k2_zfmisc_1(B_17,A_16)))
      | ~ v1_xboole_0(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_10962,plain,(
    ! [C_19] :
      ( v1_xboole_0(C_19)
      | ~ m1_subset_1(C_19,k1_zfmisc_1('#skF_8'))
      | ~ v1_xboole_0('#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10933,c_22])).

tff(c_10972,plain,(
    ! [C_19] :
      ( v1_xboole_0(C_19)
      | ~ m1_subset_1(C_19,k1_zfmisc_1('#skF_8')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10764,c_10962])).

tff(c_11574,plain,(
    v1_xboole_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_11567,c_10972])).

tff(c_11596,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2088,c_11574])).

tff(c_11597,plain,(
    v1_partfun1('#skF_8','#skF_6') ),
    inference(splitRight,[status(thm)],[c_2086])).

tff(c_13167,plain,(
    ! [C_1135,A_1136,B_1137] :
      ( v1_funct_2(C_1135,A_1136,B_1137)
      | ~ v1_partfun1(C_1135,A_1136)
      | ~ v1_funct_1(C_1135)
      | ~ m1_subset_1(C_1135,k1_zfmisc_1(k2_zfmisc_1(A_1136,B_1137))) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_13190,plain,
    ( v1_funct_2('#skF_8','#skF_6','#skF_7')
    | ~ v1_partfun1('#skF_8','#skF_6')
    | ~ v1_funct_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_1908,c_13167])).

tff(c_13203,plain,(
    v1_funct_2('#skF_8','#skF_6','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_688,c_11597,c_13190])).

tff(c_13205,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1907,c_13203])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.09  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.00/0.10  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.10/0.29  % Computer   : n020.cluster.edu
% 0.10/0.29  % Model      : x86_64 x86_64
% 0.10/0.29  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.10/0.29  % Memory     : 8042.1875MB
% 0.10/0.29  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.10/0.29  % CPULimit   : 60
% 0.10/0.29  % DateTime   : Tue Dec  1 13:44:52 EST 2020
% 0.10/0.30  % CPUTime    : 
% 0.10/0.30  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.78/2.92  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.78/2.93  
% 8.78/2.93  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.78/2.94  %$ v1_funct_2 > v1_partfun1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_2 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_4 > #skF_7 > #skF_6 > #skF_2 > #skF_8 > #skF_5 > #skF_3 > #skF_1
% 8.78/2.94  
% 8.78/2.94  %Foreground sorts:
% 8.78/2.94  
% 8.78/2.94  
% 8.78/2.94  %Background operators:
% 8.78/2.94  
% 8.78/2.94  
% 8.78/2.94  %Foreground operators:
% 8.78/2.94  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 8.78/2.94  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.78/2.94  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 8.78/2.94  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 8.78/2.94  tff('#skF_7', type, '#skF_7': $i).
% 8.78/2.94  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 8.78/2.94  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 8.78/2.94  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 8.78/2.94  tff('#skF_6', type, '#skF_6': $i).
% 8.78/2.94  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 8.78/2.94  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 8.78/2.94  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 8.78/2.94  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 8.78/2.94  tff(k1_funct_2, type, k1_funct_2: ($i * $i) > $i).
% 8.78/2.94  tff('#skF_8', type, '#skF_8': $i).
% 8.78/2.94  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.78/2.94  tff('#skF_5', type, '#skF_5': ($i * $i * $i * $i) > $i).
% 8.78/2.94  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 8.78/2.94  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 8.78/2.94  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 8.78/2.94  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.78/2.94  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 8.78/2.94  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 8.78/2.94  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 8.78/2.94  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 8.78/2.94  
% 8.78/2.96  tff(f_144, negated_conjecture, ~(![A, B, C]: (r2_hidden(C, k1_funct_2(A, B)) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t121_funct_2)).
% 8.78/2.96  tff(f_125, axiom, (![A, B, C]: ((C = k1_funct_2(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (?[E]: ((((v1_relat_1(E) & v1_funct_1(E)) & (D = E)) & (k1_relat_1(E) = A)) & r1_tarski(k2_relat_1(E), B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_funct_2)).
% 8.78/2.96  tff(f_38, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 8.78/2.96  tff(f_78, axiom, (![A, B, C]: (v1_relat_1(C) => ((r1_tarski(k1_relat_1(C), A) & r1_tarski(k2_relat_1(C), B)) => m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_relset_1)).
% 8.78/2.96  tff(f_95, axiom, (![A, B]: (v1_xboole_0(A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_partfun1(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_partfun1)).
% 8.78/2.96  tff(f_70, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 8.78/2.96  tff(f_66, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k1_relset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_relset_1)).
% 8.78/2.96  tff(f_48, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 8.78/2.96  tff(f_135, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => ((v1_funct_1(A) & v1_funct_2(A, k1_relat_1(A), k2_relat_1(A))) & m1_subset_1(A, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_funct_2)).
% 8.78/2.96  tff(f_62, axiom, (![A, B]: (v1_xboole_0(A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => v1_xboole_0(C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc4_relset_1)).
% 8.78/2.96  tff(f_88, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v1_partfun1(C, A)) => (v1_funct_1(C) & v1_funct_2(C, A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_funct_2)).
% 8.78/2.96  tff(f_109, axiom, (![A, B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) => (v1_funct_1(C) & v1_partfun1(C, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc5_funct_2)).
% 8.78/2.96  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 8.78/2.96  tff(f_55, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_subset)).
% 8.78/2.96  tff(c_84, plain, (r2_hidden('#skF_8', k1_funct_2('#skF_6', '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_144])).
% 8.78/2.96  tff(c_959, plain, (![A_261, B_262, D_263]: ('#skF_5'(A_261, B_262, k1_funct_2(A_261, B_262), D_263)=D_263 | ~r2_hidden(D_263, k1_funct_2(A_261, B_262)))), inference(cnfTransformation, [status(thm)], [f_125])).
% 8.78/2.96  tff(c_970, plain, ('#skF_5'('#skF_6', '#skF_7', k1_funct_2('#skF_6', '#skF_7'), '#skF_8')='#skF_8'), inference(resolution, [status(thm)], [c_84, c_959])).
% 8.78/2.96  tff(c_980, plain, (![A_264, B_265, D_266]: (v1_relat_1('#skF_5'(A_264, B_265, k1_funct_2(A_264, B_265), D_266)) | ~r2_hidden(D_266, k1_funct_2(A_264, B_265)))), inference(cnfTransformation, [status(thm)], [f_125])).
% 8.78/2.96  tff(c_983, plain, (v1_relat_1('#skF_8') | ~r2_hidden('#skF_8', k1_funct_2('#skF_6', '#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_970, c_980])).
% 8.78/2.96  tff(c_985, plain, (v1_relat_1('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_84, c_983])).
% 8.78/2.96  tff(c_12, plain, (![B_7]: (r1_tarski(B_7, B_7))), inference(cnfTransformation, [status(thm)], [f_38])).
% 8.78/2.96  tff(c_1074, plain, (![A_276, B_277, D_278]: (k1_relat_1('#skF_5'(A_276, B_277, k1_funct_2(A_276, B_277), D_278))=A_276 | ~r2_hidden(D_278, k1_funct_2(A_276, B_277)))), inference(cnfTransformation, [status(thm)], [f_125])).
% 8.78/2.96  tff(c_1098, plain, (k1_relat_1('#skF_8')='#skF_6' | ~r2_hidden('#skF_8', k1_funct_2('#skF_6', '#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_970, c_1074])).
% 8.78/2.96  tff(c_1102, plain, (k1_relat_1('#skF_8')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_84, c_1098])).
% 8.78/2.96  tff(c_1455, plain, (![A_303, B_304, D_305]: (r1_tarski(k2_relat_1('#skF_5'(A_303, B_304, k1_funct_2(A_303, B_304), D_305)), B_304) | ~r2_hidden(D_305, k1_funct_2(A_303, B_304)))), inference(cnfTransformation, [status(thm)], [f_125])).
% 8.78/2.96  tff(c_1470, plain, (r1_tarski(k2_relat_1('#skF_8'), '#skF_7') | ~r2_hidden('#skF_8', k1_funct_2('#skF_6', '#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_970, c_1455])).
% 8.78/2.96  tff(c_1476, plain, (r1_tarski(k2_relat_1('#skF_8'), '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_84, c_1470])).
% 8.78/2.96  tff(c_1885, plain, (![C_347, A_348, B_349]: (m1_subset_1(C_347, k1_zfmisc_1(k2_zfmisc_1(A_348, B_349))) | ~r1_tarski(k2_relat_1(C_347), B_349) | ~r1_tarski(k1_relat_1(C_347), A_348) | ~v1_relat_1(C_347))), inference(cnfTransformation, [status(thm)], [f_78])).
% 8.78/2.96  tff(c_82, plain, (~m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_6', '#skF_7'))) | ~v1_funct_2('#skF_8', '#skF_6', '#skF_7') | ~v1_funct_1('#skF_8')), inference(cnfTransformation, [status(thm)], [f_144])).
% 8.78/2.96  tff(c_119, plain, (~v1_funct_1('#skF_8')), inference(splitLeft, [status(thm)], [c_82])).
% 8.78/2.96  tff(c_650, plain, (![A_173, B_174, D_175]: ('#skF_5'(A_173, B_174, k1_funct_2(A_173, B_174), D_175)=D_175 | ~r2_hidden(D_175, k1_funct_2(A_173, B_174)))), inference(cnfTransformation, [status(thm)], [f_125])).
% 8.78/2.96  tff(c_661, plain, ('#skF_5'('#skF_6', '#skF_7', k1_funct_2('#skF_6', '#skF_7'), '#skF_8')='#skF_8'), inference(resolution, [status(thm)], [c_84, c_650])).
% 8.78/2.96  tff(c_679, plain, (![A_180, B_181, D_182]: (v1_funct_1('#skF_5'(A_180, B_181, k1_funct_2(A_180, B_181), D_182)) | ~r2_hidden(D_182, k1_funct_2(A_180, B_181)))), inference(cnfTransformation, [status(thm)], [f_125])).
% 8.78/2.96  tff(c_682, plain, (v1_funct_1('#skF_8') | ~r2_hidden('#skF_8', k1_funct_2('#skF_6', '#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_661, c_679])).
% 8.78/2.96  tff(c_684, plain, (v1_funct_1('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_84, c_682])).
% 8.78/2.96  tff(c_686, plain, $false, inference(negUnitSimplification, [status(thm)], [c_119, c_684])).
% 8.78/2.96  tff(c_687, plain, (~v1_funct_2('#skF_8', '#skF_6', '#skF_7') | ~m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_6', '#skF_7')))), inference(splitRight, [status(thm)], [c_82])).
% 8.78/2.96  tff(c_695, plain, (~m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_6', '#skF_7')))), inference(splitLeft, [status(thm)], [c_687])).
% 8.78/2.96  tff(c_1896, plain, (~r1_tarski(k2_relat_1('#skF_8'), '#skF_7') | ~r1_tarski(k1_relat_1('#skF_8'), '#skF_6') | ~v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_1885, c_695])).
% 8.78/2.96  tff(c_1906, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_985, c_12, c_1102, c_1476, c_1896])).
% 8.78/2.96  tff(c_1907, plain, (~v1_funct_2('#skF_8', '#skF_6', '#skF_7')), inference(splitRight, [status(thm)], [c_687])).
% 8.78/2.96  tff(c_688, plain, (v1_funct_1('#skF_8')), inference(splitRight, [status(thm)], [c_82])).
% 8.78/2.96  tff(c_1908, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_6', '#skF_7')))), inference(splitRight, [status(thm)], [c_687])).
% 8.78/2.96  tff(c_2078, plain, (![C_385, A_386, B_387]: (v1_partfun1(C_385, A_386) | ~m1_subset_1(C_385, k1_zfmisc_1(k2_zfmisc_1(A_386, B_387))) | ~v1_xboole_0(A_386))), inference(cnfTransformation, [status(thm)], [f_95])).
% 8.78/2.96  tff(c_2086, plain, (v1_partfun1('#skF_8', '#skF_6') | ~v1_xboole_0('#skF_6')), inference(resolution, [status(thm)], [c_1908, c_2078])).
% 8.78/2.96  tff(c_2088, plain, (~v1_xboole_0('#skF_6')), inference(splitLeft, [status(thm)], [c_2086])).
% 8.78/2.96  tff(c_2674, plain, (![A_449, B_450, D_451]: ('#skF_5'(A_449, B_450, k1_funct_2(A_449, B_450), D_451)=D_451 | ~r2_hidden(D_451, k1_funct_2(A_449, B_450)))), inference(cnfTransformation, [status(thm)], [f_125])).
% 8.78/2.96  tff(c_2685, plain, ('#skF_5'('#skF_6', '#skF_7', k1_funct_2('#skF_6', '#skF_7'), '#skF_8')='#skF_8'), inference(resolution, [status(thm)], [c_84, c_2674])).
% 8.78/2.96  tff(c_2786, plain, (![A_466, B_467, D_468]: (k1_relat_1('#skF_5'(A_466, B_467, k1_funct_2(A_466, B_467), D_468))=A_466 | ~r2_hidden(D_468, k1_funct_2(A_466, B_467)))), inference(cnfTransformation, [status(thm)], [f_125])).
% 8.78/2.96  tff(c_2807, plain, (k1_relat_1('#skF_8')='#skF_6' | ~r2_hidden('#skF_8', k1_funct_2('#skF_6', '#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_2685, c_2786])).
% 8.78/2.96  tff(c_2811, plain, (k1_relat_1('#skF_8')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_84, c_2807])).
% 8.78/2.96  tff(c_2089, plain, (![A_388, B_389, C_390]: (k1_relset_1(A_388, B_389, C_390)=k1_relat_1(C_390) | ~m1_subset_1(C_390, k1_zfmisc_1(k2_zfmisc_1(A_388, B_389))))), inference(cnfTransformation, [status(thm)], [f_70])).
% 8.78/2.96  tff(c_2097, plain, (k1_relset_1('#skF_6', '#skF_7', '#skF_8')=k1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_1908, c_2089])).
% 8.78/2.96  tff(c_2289, plain, (![A_420, B_421, C_422]: (m1_subset_1(k1_relset_1(A_420, B_421, C_422), k1_zfmisc_1(A_420)) | ~m1_subset_1(C_422, k1_zfmisc_1(k2_zfmisc_1(A_420, B_421))))), inference(cnfTransformation, [status(thm)], [f_66])).
% 8.78/2.96  tff(c_2315, plain, (m1_subset_1(k1_relat_1('#skF_8'), k1_zfmisc_1('#skF_6')) | ~m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_6', '#skF_7')))), inference(superposition, [status(thm), theory('equality')], [c_2097, c_2289])).
% 8.78/2.96  tff(c_2322, plain, (m1_subset_1(k1_relat_1('#skF_8'), k1_zfmisc_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_1908, c_2315])).
% 8.78/2.96  tff(c_16, plain, (![A_11, B_12]: (r1_tarski(A_11, B_12) | ~m1_subset_1(A_11, k1_zfmisc_1(B_12)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 8.78/2.96  tff(c_2329, plain, (r1_tarski(k1_relat_1('#skF_8'), '#skF_6')), inference(resolution, [status(thm)], [c_2322, c_16])).
% 8.78/2.96  tff(c_8, plain, (![B_7, A_6]: (B_7=A_6 | ~r1_tarski(B_7, A_6) | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_38])).
% 8.78/2.96  tff(c_2348, plain, (k1_relat_1('#skF_8')='#skF_6' | ~r1_tarski('#skF_6', k1_relat_1('#skF_8'))), inference(resolution, [status(thm)], [c_2329, c_8])).
% 8.78/2.96  tff(c_2361, plain, (~r1_tarski('#skF_6', k1_relat_1('#skF_8'))), inference(splitLeft, [status(thm)], [c_2348])).
% 8.78/2.96  tff(c_2815, plain, (~r1_tarski('#skF_6', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_2811, c_2361])).
% 8.78/2.96  tff(c_2824, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12, c_2815])).
% 8.78/2.96  tff(c_2825, plain, (k1_relat_1('#skF_8')='#skF_6'), inference(splitRight, [status(thm)], [c_2348])).
% 8.78/2.96  tff(c_78, plain, (![A_60]: (v1_funct_2(A_60, k1_relat_1(A_60), k2_relat_1(A_60)) | ~v1_funct_1(A_60) | ~v1_relat_1(A_60))), inference(cnfTransformation, [status(thm)], [f_135])).
% 8.78/2.96  tff(c_2847, plain, (v1_funct_2('#skF_8', '#skF_6', k2_relat_1('#skF_8')) | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_2825, c_78])).
% 8.78/2.96  tff(c_2859, plain, (v1_funct_2('#skF_8', '#skF_6', k2_relat_1('#skF_8')) | ~v1_relat_1('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_688, c_2847])).
% 8.78/2.96  tff(c_2880, plain, (~v1_relat_1('#skF_8')), inference(splitLeft, [status(thm)], [c_2859])).
% 8.78/2.96  tff(c_2881, plain, (![A_469, B_470, D_471]: ('#skF_5'(A_469, B_470, k1_funct_2(A_469, B_470), D_471)=D_471 | ~r2_hidden(D_471, k1_funct_2(A_469, B_470)))), inference(cnfTransformation, [status(thm)], [f_125])).
% 8.78/2.96  tff(c_2892, plain, ('#skF_5'('#skF_6', '#skF_7', k1_funct_2('#skF_6', '#skF_7'), '#skF_8')='#skF_8'), inference(resolution, [status(thm)], [c_84, c_2881])).
% 8.78/2.96  tff(c_3210, plain, (![A_501, B_502, D_503]: (v1_relat_1('#skF_5'(A_501, B_502, k1_funct_2(A_501, B_502), D_503)) | ~r2_hidden(D_503, k1_funct_2(A_501, B_502)))), inference(cnfTransformation, [status(thm)], [f_125])).
% 8.78/2.96  tff(c_3213, plain, (v1_relat_1('#skF_8') | ~r2_hidden('#skF_8', k1_funct_2('#skF_6', '#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_2892, c_3210])).
% 8.78/2.96  tff(c_3215, plain, (v1_relat_1('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_84, c_3213])).
% 8.78/2.96  tff(c_3217, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2880, c_3215])).
% 8.78/2.96  tff(c_3219, plain, (v1_relat_1('#skF_8')), inference(splitRight, [status(thm)], [c_2859])).
% 8.78/2.96  tff(c_2188, plain, (![A_409]: (m1_subset_1(A_409, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_409), k2_relat_1(A_409)))) | ~v1_funct_1(A_409) | ~v1_relat_1(A_409))), inference(cnfTransformation, [status(thm)], [f_135])).
% 8.78/2.96  tff(c_2207, plain, (![A_409]: (r1_tarski(A_409, k2_zfmisc_1(k1_relat_1(A_409), k2_relat_1(A_409))) | ~v1_funct_1(A_409) | ~v1_relat_1(A_409))), inference(resolution, [status(thm)], [c_2188, c_16])).
% 8.78/2.96  tff(c_2841, plain, (r1_tarski('#skF_8', k2_zfmisc_1('#skF_6', k2_relat_1('#skF_8'))) | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_2825, c_2207])).
% 8.78/2.96  tff(c_2855, plain, (r1_tarski('#skF_8', k2_zfmisc_1('#skF_6', k2_relat_1('#skF_8'))) | ~v1_relat_1('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_688, c_2841])).
% 8.78/2.96  tff(c_3221, plain, (r1_tarski('#skF_8', k2_zfmisc_1('#skF_6', k2_relat_1('#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_3219, c_2855])).
% 8.78/2.96  tff(c_18, plain, (![A_11, B_12]: (m1_subset_1(A_11, k1_zfmisc_1(B_12)) | ~r1_tarski(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_48])).
% 8.78/2.96  tff(c_2017, plain, (![C_367, B_368, A_369]: (v1_xboole_0(C_367) | ~m1_subset_1(C_367, k1_zfmisc_1(k2_zfmisc_1(B_368, A_369))) | ~v1_xboole_0(A_369))), inference(cnfTransformation, [status(thm)], [f_62])).
% 8.78/2.96  tff(c_2026, plain, (![A_11, A_369, B_368]: (v1_xboole_0(A_11) | ~v1_xboole_0(A_369) | ~r1_tarski(A_11, k2_zfmisc_1(B_368, A_369)))), inference(resolution, [status(thm)], [c_18, c_2017])).
% 8.78/2.96  tff(c_3250, plain, (v1_xboole_0('#skF_8') | ~v1_xboole_0(k2_relat_1('#skF_8'))), inference(resolution, [status(thm)], [c_3221, c_2026])).
% 8.78/2.96  tff(c_3256, plain, (~v1_xboole_0(k2_relat_1('#skF_8'))), inference(splitLeft, [status(thm)], [c_3250])).
% 8.78/2.96  tff(c_5939, plain, (![C_737, A_738, B_739]: (v1_funct_2(C_737, A_738, B_739) | ~v1_partfun1(C_737, A_738) | ~v1_funct_1(C_737) | ~m1_subset_1(C_737, k1_zfmisc_1(k2_zfmisc_1(A_738, B_739))))), inference(cnfTransformation, [status(thm)], [f_88])).
% 8.78/2.96  tff(c_5952, plain, (v1_funct_2('#skF_8', '#skF_6', '#skF_7') | ~v1_partfun1('#skF_8', '#skF_6') | ~v1_funct_1('#skF_8')), inference(resolution, [status(thm)], [c_1908, c_5939])).
% 8.78/2.96  tff(c_5964, plain, (v1_funct_2('#skF_8', '#skF_6', '#skF_7') | ~v1_partfun1('#skF_8', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_688, c_5952])).
% 8.78/2.96  tff(c_5965, plain, (~v1_partfun1('#skF_8', '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_1907, c_5964])).
% 8.78/2.96  tff(c_3218, plain, (v1_funct_2('#skF_8', '#skF_6', k2_relat_1('#skF_8'))), inference(splitRight, [status(thm)], [c_2859])).
% 8.78/2.96  tff(c_76, plain, (![A_60]: (m1_subset_1(A_60, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_60), k2_relat_1(A_60)))) | ~v1_funct_1(A_60) | ~v1_relat_1(A_60))), inference(cnfTransformation, [status(thm)], [f_135])).
% 8.78/2.96  tff(c_2844, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_6', k2_relat_1('#skF_8')))) | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_2825, c_76])).
% 8.78/2.96  tff(c_2857, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_6', k2_relat_1('#skF_8')))) | ~v1_relat_1('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_688, c_2844])).
% 8.78/2.96  tff(c_3289, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_6', k2_relat_1('#skF_8'))))), inference(demodulation, [status(thm), theory('equality')], [c_3219, c_2857])).
% 8.78/2.96  tff(c_10734, plain, (![C_951, A_952, B_953]: (v1_partfun1(C_951, A_952) | ~v1_funct_2(C_951, A_952, B_953) | ~v1_funct_1(C_951) | ~m1_subset_1(C_951, k1_zfmisc_1(k2_zfmisc_1(A_952, B_953))) | v1_xboole_0(B_953))), inference(cnfTransformation, [status(thm)], [f_109])).
% 8.78/2.96  tff(c_10743, plain, (v1_partfun1('#skF_8', '#skF_6') | ~v1_funct_2('#skF_8', '#skF_6', k2_relat_1('#skF_8')) | ~v1_funct_1('#skF_8') | v1_xboole_0(k2_relat_1('#skF_8'))), inference(resolution, [status(thm)], [c_3289, c_10734])).
% 8.78/2.96  tff(c_10761, plain, (v1_partfun1('#skF_8', '#skF_6') | v1_xboole_0(k2_relat_1('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_688, c_3218, c_10743])).
% 8.78/2.96  tff(c_10763, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3256, c_5965, c_10761])).
% 8.78/2.96  tff(c_10764, plain, (v1_xboole_0('#skF_8')), inference(splitRight, [status(thm)], [c_3250])).
% 8.78/2.96  tff(c_2029, plain, (![A_371, A_372, B_373]: (v1_xboole_0(A_371) | ~v1_xboole_0(A_372) | ~r1_tarski(A_371, k2_zfmisc_1(B_373, A_372)))), inference(resolution, [status(thm)], [c_18, c_2017])).
% 8.78/2.96  tff(c_2048, plain, (![B_374, A_375]: (v1_xboole_0(k2_zfmisc_1(B_374, A_375)) | ~v1_xboole_0(A_375))), inference(resolution, [status(thm)], [c_12, c_2029])).
% 8.78/2.96  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 8.78/2.96  tff(c_108, plain, (![C_72, B_73, A_74]: (~v1_xboole_0(C_72) | ~m1_subset_1(B_73, k1_zfmisc_1(C_72)) | ~r2_hidden(A_74, B_73))), inference(cnfTransformation, [status(thm)], [f_55])).
% 8.78/2.96  tff(c_112, plain, (![B_75, A_76, A_77]: (~v1_xboole_0(B_75) | ~r2_hidden(A_76, A_77) | ~r1_tarski(A_77, B_75))), inference(resolution, [status(thm)], [c_18, c_108])).
% 8.78/2.96  tff(c_1920, plain, (![B_350, A_351, B_352]: (~v1_xboole_0(B_350) | ~r1_tarski(A_351, B_350) | r1_tarski(A_351, B_352))), inference(resolution, [status(thm)], [c_6, c_112])).
% 8.78/2.96  tff(c_1926, plain, (![B_7, B_352]: (~v1_xboole_0(B_7) | r1_tarski(B_7, B_352))), inference(resolution, [status(thm)], [c_12, c_1920])).
% 8.78/2.96  tff(c_1927, plain, (![B_353, B_354]: (~v1_xboole_0(B_353) | r1_tarski(B_353, B_354))), inference(resolution, [status(thm)], [c_12, c_1920])).
% 8.78/2.96  tff(c_1939, plain, (![B_356, B_355]: (B_356=B_355 | ~r1_tarski(B_355, B_356) | ~v1_xboole_0(B_356))), inference(resolution, [status(thm)], [c_1927, c_8])).
% 8.78/2.96  tff(c_1949, plain, (![B_7, B_352]: (B_7=B_352 | ~v1_xboole_0(B_352) | ~v1_xboole_0(B_7))), inference(resolution, [status(thm)], [c_1926, c_1939])).
% 8.78/2.96  tff(c_2054, plain, (![B_374, A_375, B_7]: (k2_zfmisc_1(B_374, A_375)=B_7 | ~v1_xboole_0(B_7) | ~v1_xboole_0(A_375))), inference(resolution, [status(thm)], [c_2048, c_1949])).
% 8.78/2.96  tff(c_10924, plain, (![B_961, A_962]: (k2_zfmisc_1(B_961, A_962)='#skF_8' | ~v1_xboole_0(A_962))), inference(resolution, [status(thm)], [c_10764, c_2054])).
% 8.78/2.96  tff(c_10929, plain, (![B_961]: (k2_zfmisc_1(B_961, '#skF_8')='#skF_8')), inference(resolution, [status(thm)], [c_10764, c_10924])).
% 8.78/2.96  tff(c_10765, plain, (v1_xboole_0(k2_relat_1('#skF_8'))), inference(splitRight, [status(thm)], [c_3250])).
% 8.78/2.96  tff(c_10797, plain, (![B_954]: (B_954='#skF_8' | ~v1_xboole_0(B_954))), inference(resolution, [status(thm)], [c_10764, c_1949])).
% 8.78/2.96  tff(c_10807, plain, (k2_relat_1('#skF_8')='#skF_8'), inference(resolution, [status(thm)], [c_10765, c_10797])).
% 8.78/2.96  tff(c_10840, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_8'), '#skF_8'))) | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_10807, c_76])).
% 8.78/2.96  tff(c_10855, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_6', '#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_3219, c_688, c_2825, c_10840])).
% 8.78/2.96  tff(c_10999, plain, (m1_subset_1('#skF_8', k1_zfmisc_1('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_10929, c_10855])).
% 8.78/2.96  tff(c_2152, plain, (![A_402, B_403, A_404]: (k1_relset_1(A_402, B_403, A_404)=k1_relat_1(A_404) | ~r1_tarski(A_404, k2_zfmisc_1(A_402, B_403)))), inference(resolution, [status(thm)], [c_18, c_2089])).
% 8.78/2.96  tff(c_2168, plain, (![A_402, B_403, B_7]: (k1_relset_1(A_402, B_403, B_7)=k1_relat_1(B_7) | ~v1_xboole_0(B_7))), inference(resolution, [status(thm)], [c_1926, c_2152])).
% 8.78/2.96  tff(c_10767, plain, (![A_402, B_403]: (k1_relset_1(A_402, B_403, '#skF_8')=k1_relat_1('#skF_8'))), inference(resolution, [status(thm)], [c_10764, c_2168])).
% 8.78/2.96  tff(c_10862, plain, (![A_956, B_957]: (k1_relset_1(A_956, B_957, '#skF_8')='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_2825, c_10767])).
% 8.78/2.96  tff(c_24, plain, (![A_20, B_21, C_22]: (m1_subset_1(k1_relset_1(A_20, B_21, C_22), k1_zfmisc_1(A_20)) | ~m1_subset_1(C_22, k1_zfmisc_1(k2_zfmisc_1(A_20, B_21))))), inference(cnfTransformation, [status(thm)], [f_66])).
% 8.78/2.96  tff(c_11536, plain, (![A_1010, B_1011]: (m1_subset_1('#skF_6', k1_zfmisc_1(A_1010)) | ~m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1(A_1010, B_1011))))), inference(superposition, [status(thm), theory('equality')], [c_10862, c_24])).
% 8.78/2.96  tff(c_11542, plain, (![B_961]: (m1_subset_1('#skF_6', k1_zfmisc_1(B_961)) | ~m1_subset_1('#skF_8', k1_zfmisc_1('#skF_8')))), inference(superposition, [status(thm), theory('equality')], [c_10929, c_11536])).
% 8.78/2.96  tff(c_11567, plain, (![B_1012]: (m1_subset_1('#skF_6', k1_zfmisc_1(B_1012)))), inference(demodulation, [status(thm), theory('equality')], [c_10999, c_11542])).
% 8.78/2.96  tff(c_10933, plain, (![B_963]: (k2_zfmisc_1(B_963, '#skF_8')='#skF_8')), inference(resolution, [status(thm)], [c_10764, c_10924])).
% 8.78/2.96  tff(c_22, plain, (![C_19, B_17, A_16]: (v1_xboole_0(C_19) | ~m1_subset_1(C_19, k1_zfmisc_1(k2_zfmisc_1(B_17, A_16))) | ~v1_xboole_0(A_16))), inference(cnfTransformation, [status(thm)], [f_62])).
% 8.78/2.96  tff(c_10962, plain, (![C_19]: (v1_xboole_0(C_19) | ~m1_subset_1(C_19, k1_zfmisc_1('#skF_8')) | ~v1_xboole_0('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_10933, c_22])).
% 8.78/2.96  tff(c_10972, plain, (![C_19]: (v1_xboole_0(C_19) | ~m1_subset_1(C_19, k1_zfmisc_1('#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_10764, c_10962])).
% 8.78/2.96  tff(c_11574, plain, (v1_xboole_0('#skF_6')), inference(resolution, [status(thm)], [c_11567, c_10972])).
% 8.78/2.96  tff(c_11596, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2088, c_11574])).
% 8.78/2.96  tff(c_11597, plain, (v1_partfun1('#skF_8', '#skF_6')), inference(splitRight, [status(thm)], [c_2086])).
% 8.78/2.96  tff(c_13167, plain, (![C_1135, A_1136, B_1137]: (v1_funct_2(C_1135, A_1136, B_1137) | ~v1_partfun1(C_1135, A_1136) | ~v1_funct_1(C_1135) | ~m1_subset_1(C_1135, k1_zfmisc_1(k2_zfmisc_1(A_1136, B_1137))))), inference(cnfTransformation, [status(thm)], [f_88])).
% 8.78/2.96  tff(c_13190, plain, (v1_funct_2('#skF_8', '#skF_6', '#skF_7') | ~v1_partfun1('#skF_8', '#skF_6') | ~v1_funct_1('#skF_8')), inference(resolution, [status(thm)], [c_1908, c_13167])).
% 8.78/2.96  tff(c_13203, plain, (v1_funct_2('#skF_8', '#skF_6', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_688, c_11597, c_13190])).
% 8.78/2.96  tff(c_13205, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1907, c_13203])).
% 8.78/2.96  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.78/2.96  
% 8.78/2.96  Inference rules
% 8.78/2.96  ----------------------
% 8.78/2.96  #Ref     : 0
% 8.78/2.96  #Sup     : 3289
% 8.78/2.96  #Fact    : 0
% 8.78/2.96  #Define  : 0
% 8.78/2.96  #Split   : 50
% 8.78/2.96  #Chain   : 0
% 8.78/2.96  #Close   : 0
% 8.78/2.96  
% 8.78/2.96  Ordering : KBO
% 8.78/2.96  
% 8.78/2.96  Simplification rules
% 8.78/2.96  ----------------------
% 8.78/2.96  #Subsume      : 1328
% 8.78/2.96  #Demod        : 815
% 8.78/2.96  #Tautology    : 518
% 8.78/2.96  #SimpNegUnit  : 58
% 8.78/2.96  #BackRed      : 24
% 8.78/2.96  
% 8.78/2.96  #Partial instantiations: 0
% 8.78/2.96  #Strategies tried      : 1
% 8.78/2.96  
% 8.78/2.96  Timing (in seconds)
% 8.78/2.96  ----------------------
% 8.78/2.96  Preprocessing        : 0.37
% 8.78/2.96  Parsing              : 0.19
% 8.78/2.96  CNF conversion       : 0.03
% 8.78/2.96  Main loop            : 1.91
% 8.78/2.96  Inferencing          : 0.64
% 8.78/2.96  Reduction            : 0.55
% 8.78/2.96  Demodulation         : 0.37
% 8.78/2.96  BG Simplification    : 0.08
% 8.78/2.96  Subsumption          : 0.50
% 8.78/2.96  Abstraction          : 0.10
% 8.78/2.96  MUC search           : 0.00
% 8.78/2.96  Cooper               : 0.00
% 8.78/2.96  Total                : 2.33
% 8.78/2.96  Index Insertion      : 0.00
% 8.78/2.96  Index Deletion       : 0.00
% 8.78/2.96  Index Matching       : 0.00
% 8.78/2.96  BG Taut test         : 0.00
%------------------------------------------------------------------------------
