%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:11:36 EST 2020

% Result     : Theorem 11.37s
% Output     : CNFRefutation 11.57s
% Verified   : 
% Statistics : Number of formulae       :  176 (2059 expanded)
%              Number of leaves         :   41 ( 696 expanded)
%              Depth                    :   15
%              Number of atoms          :  293 (5301 expanded)
%              Number of equality atoms :   96 ( 775 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_1 > #skF_7 > #skF_3 > #skF_10 > #skF_9 > #skF_8 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_5',type,(
    '#skF_5': $i > $i )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_relset_1,type,(
    r2_relset_1: ( $i * $i * $i * $i ) > $o )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_145,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ! [D] :
            ( ( v1_funct_1(D)
              & v1_funct_2(D,A,B)
              & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
           => ( ! [E] :
                  ( r2_hidden(E,A)
                 => k1_funct_1(C,E) = k1_funct_1(D,E) )
             => r2_relset_1(A,B,C,D) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_funct_2)).

tff(f_106,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => r2_relset_1(A,B,C,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',reflexivity_r2_relset_1)).

tff(f_90,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_100,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_124,axiom,(
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

tff(f_86,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( ( v1_relat_1(B)
            & v1_funct_1(B) )
         => ( ( k1_relat_1(A) = k1_relat_1(B)
              & ! [C] :
                  ( r2_hidden(C,k1_relat_1(A))
                 => k1_funct_1(A,C) = k1_funct_1(B,C) ) )
           => A = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_funct_1)).

tff(f_39,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_52,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_62,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

tff(f_46,axiom,(
    ! [A,B] :
      ( ! [C] :
          ( r2_hidden(C,A)
        <=> r2_hidden(C,B) )
     => A = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tarski)).

tff(f_55,axiom,(
    ! [A] :
    ? [B] : m1_subset_1(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',existence_m1_subset_1)).

tff(c_72,plain,(
    m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1('#skF_7','#skF_8'))) ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_66,plain,(
    m1_subset_1('#skF_10',k1_zfmisc_1(k2_zfmisc_1('#skF_7','#skF_8'))) ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_5857,plain,(
    ! [A_533,B_534,C_535,D_536] :
      ( r2_relset_1(A_533,B_534,C_535,C_535)
      | ~ m1_subset_1(D_536,k1_zfmisc_1(k2_zfmisc_1(A_533,B_534)))
      | ~ m1_subset_1(C_535,k1_zfmisc_1(k2_zfmisc_1(A_533,B_534))) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_5881,plain,(
    ! [C_537] :
      ( r2_relset_1('#skF_7','#skF_8',C_537,C_537)
      | ~ m1_subset_1(C_537,k1_zfmisc_1(k2_zfmisc_1('#skF_7','#skF_8'))) ) ),
    inference(resolution,[status(thm)],[c_66,c_5857])).

tff(c_5898,plain,(
    r2_relset_1('#skF_7','#skF_8','#skF_9','#skF_9') ),
    inference(resolution,[status(thm)],[c_72,c_5881])).

tff(c_121,plain,(
    ! [C_58,A_59,B_60] :
      ( v1_relat_1(C_58)
      | ~ m1_subset_1(C_58,k1_zfmisc_1(k2_zfmisc_1(A_59,B_60))) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_136,plain,(
    v1_relat_1('#skF_10') ),
    inference(resolution,[status(thm)],[c_66,c_121])).

tff(c_70,plain,(
    v1_funct_1('#skF_10') ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_68,plain,(
    v1_funct_2('#skF_10','#skF_7','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_4531,plain,(
    ! [A_447,B_448,C_449] :
      ( k1_relset_1(A_447,B_448,C_449) = k1_relat_1(C_449)
      | ~ m1_subset_1(C_449,k1_zfmisc_1(k2_zfmisc_1(A_447,B_448))) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_4548,plain,(
    k1_relset_1('#skF_7','#skF_8','#skF_10') = k1_relat_1('#skF_10') ),
    inference(resolution,[status(thm)],[c_66,c_4531])).

tff(c_5967,plain,(
    ! [B_546,A_547,C_548] :
      ( k1_xboole_0 = B_546
      | k1_relset_1(A_547,B_546,C_548) = A_547
      | ~ v1_funct_2(C_548,A_547,B_546)
      | ~ m1_subset_1(C_548,k1_zfmisc_1(k2_zfmisc_1(A_547,B_546))) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_5978,plain,
    ( k1_xboole_0 = '#skF_8'
    | k1_relset_1('#skF_7','#skF_8','#skF_10') = '#skF_7'
    | ~ v1_funct_2('#skF_10','#skF_7','#skF_8') ),
    inference(resolution,[status(thm)],[c_66,c_5967])).

tff(c_5996,plain,
    ( k1_xboole_0 = '#skF_8'
    | k1_relat_1('#skF_10') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_4548,c_5978])).

tff(c_6002,plain,(
    k1_relat_1('#skF_10') = '#skF_7' ),
    inference(splitLeft,[status(thm)],[c_5996])).

tff(c_137,plain,(
    v1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_72,c_121])).

tff(c_76,plain,(
    v1_funct_1('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_74,plain,(
    v1_funct_2('#skF_9','#skF_7','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_4549,plain,(
    k1_relset_1('#skF_7','#skF_8','#skF_9') = k1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_72,c_4531])).

tff(c_5981,plain,
    ( k1_xboole_0 = '#skF_8'
    | k1_relset_1('#skF_7','#skF_8','#skF_9') = '#skF_7'
    | ~ v1_funct_2('#skF_9','#skF_7','#skF_8') ),
    inference(resolution,[status(thm)],[c_72,c_5967])).

tff(c_5999,plain,
    ( k1_xboole_0 = '#skF_8'
    | k1_relat_1('#skF_9') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_4549,c_5981])).

tff(c_6027,plain,(
    k1_relat_1('#skF_9') = '#skF_7' ),
    inference(splitLeft,[status(thm)],[c_5999])).

tff(c_6278,plain,(
    ! [A_562,B_563] :
      ( r2_hidden('#skF_6'(A_562,B_563),k1_relat_1(A_562))
      | B_563 = A_562
      | k1_relat_1(B_563) != k1_relat_1(A_562)
      | ~ v1_funct_1(B_563)
      | ~ v1_relat_1(B_563)
      | ~ v1_funct_1(A_562)
      | ~ v1_relat_1(A_562) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_6288,plain,(
    ! [B_563] :
      ( r2_hidden('#skF_6'('#skF_9',B_563),'#skF_7')
      | B_563 = '#skF_9'
      | k1_relat_1(B_563) != k1_relat_1('#skF_9')
      | ~ v1_funct_1(B_563)
      | ~ v1_relat_1(B_563)
      | ~ v1_funct_1('#skF_9')
      | ~ v1_relat_1('#skF_9') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6027,c_6278])).

tff(c_14708,plain,(
    ! [B_943] :
      ( r2_hidden('#skF_6'('#skF_9',B_943),'#skF_7')
      | B_943 = '#skF_9'
      | k1_relat_1(B_943) != '#skF_7'
      | ~ v1_funct_1(B_943)
      | ~ v1_relat_1(B_943) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_137,c_76,c_6027,c_6288])).

tff(c_64,plain,(
    ! [E_49] :
      ( k1_funct_1('#skF_10',E_49) = k1_funct_1('#skF_9',E_49)
      | ~ r2_hidden(E_49,'#skF_7') ) ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_14821,plain,(
    ! [B_948] :
      ( k1_funct_1('#skF_10','#skF_6'('#skF_9',B_948)) = k1_funct_1('#skF_9','#skF_6'('#skF_9',B_948))
      | B_948 = '#skF_9'
      | k1_relat_1(B_948) != '#skF_7'
      | ~ v1_funct_1(B_948)
      | ~ v1_relat_1(B_948) ) ),
    inference(resolution,[status(thm)],[c_14708,c_64])).

tff(c_36,plain,(
    ! [B_27,A_23] :
      ( k1_funct_1(B_27,'#skF_6'(A_23,B_27)) != k1_funct_1(A_23,'#skF_6'(A_23,B_27))
      | B_27 = A_23
      | k1_relat_1(B_27) != k1_relat_1(A_23)
      | ~ v1_funct_1(B_27)
      | ~ v1_relat_1(B_27)
      | ~ v1_funct_1(A_23)
      | ~ v1_relat_1(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_14828,plain,
    ( k1_relat_1('#skF_10') != k1_relat_1('#skF_9')
    | ~ v1_funct_1('#skF_9')
    | ~ v1_relat_1('#skF_9')
    | '#skF_10' = '#skF_9'
    | k1_relat_1('#skF_10') != '#skF_7'
    | ~ v1_funct_1('#skF_10')
    | ~ v1_relat_1('#skF_10') ),
    inference(superposition,[status(thm),theory(equality)],[c_14821,c_36])).

tff(c_14835,plain,(
    '#skF_10' = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_136,c_70,c_6002,c_137,c_76,c_6002,c_6027,c_14828])).

tff(c_62,plain,(
    ~ r2_relset_1('#skF_7','#skF_8','#skF_9','#skF_10') ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_14887,plain,(
    ~ r2_relset_1('#skF_7','#skF_8','#skF_9','#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14835,c_62])).

tff(c_14900,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_5898,c_14887])).

tff(c_14901,plain,(
    k1_xboole_0 = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_5999])).

tff(c_12,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_14944,plain,(
    v1_xboole_0('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14901,c_12])).

tff(c_24,plain,(
    ! [A_13] : k2_zfmisc_1(A_13,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_14943,plain,(
    ! [A_13] : k2_zfmisc_1(A_13,'#skF_8') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_14901,c_14901,c_24])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_4345,plain,(
    ! [C_426,A_427,B_428] :
      ( r2_hidden(C_426,A_427)
      | ~ r2_hidden(C_426,B_428)
      | ~ m1_subset_1(B_428,k1_zfmisc_1(A_427)) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_4355,plain,(
    ! [A_429,A_430] :
      ( r2_hidden('#skF_1'(A_429),A_430)
      | ~ m1_subset_1(A_429,k1_zfmisc_1(A_430))
      | v1_xboole_0(A_429) ) ),
    inference(resolution,[status(thm)],[c_4,c_4345])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_4371,plain,(
    ! [A_431,A_432] :
      ( ~ v1_xboole_0(A_431)
      | ~ m1_subset_1(A_432,k1_zfmisc_1(A_431))
      | v1_xboole_0(A_432) ) ),
    inference(resolution,[status(thm)],[c_4355,c_2])).

tff(c_4388,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1('#skF_7','#skF_8'))
    | v1_xboole_0('#skF_10') ),
    inference(resolution,[status(thm)],[c_66,c_4371])).

tff(c_4391,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_7','#skF_8')) ),
    inference(splitLeft,[status(thm)],[c_4388])).

tff(c_15077,plain,(
    ~ v1_xboole_0('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14943,c_4391])).

tff(c_15082,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_14944,c_15077])).

tff(c_15083,plain,(
    k1_xboole_0 = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_5996])).

tff(c_15126,plain,(
    v1_xboole_0('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_15083,c_12])).

tff(c_15125,plain,(
    ! [A_13] : k2_zfmisc_1(A_13,'#skF_8') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_15083,c_15083,c_24])).

tff(c_15210,plain,(
    ~ v1_xboole_0('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_15125,c_4391])).

tff(c_15215,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_15126,c_15210])).

tff(c_15217,plain,(
    v1_xboole_0(k2_zfmisc_1('#skF_7','#skF_8')) ),
    inference(splitRight,[status(thm)],[c_4388])).

tff(c_4389,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1('#skF_7','#skF_8'))
    | v1_xboole_0('#skF_9') ),
    inference(resolution,[status(thm)],[c_72,c_4371])).

tff(c_15247,plain,(
    v1_xboole_0('#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_15217,c_4389])).

tff(c_15218,plain,(
    ! [A_962,B_963] :
      ( r2_hidden('#skF_3'(A_962,B_963),B_963)
      | r2_hidden('#skF_4'(A_962,B_963),A_962)
      | B_963 = A_962 ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_15272,plain,(
    ! [B_966,A_967] :
      ( ~ v1_xboole_0(B_966)
      | r2_hidden('#skF_4'(A_967,B_966),A_967)
      | B_966 = A_967 ) ),
    inference(resolution,[status(thm)],[c_15218,c_2])).

tff(c_15288,plain,(
    ! [A_968,B_969] :
      ( ~ v1_xboole_0(A_968)
      | ~ v1_xboole_0(B_969)
      | B_969 = A_968 ) ),
    inference(resolution,[status(thm)],[c_15272,c_2])).

tff(c_15304,plain,(
    ! [B_970] :
      ( ~ v1_xboole_0(B_970)
      | k1_xboole_0 = B_970 ) ),
    inference(resolution,[status(thm)],[c_12,c_15288])).

tff(c_15321,plain,(
    k1_xboole_0 = '#skF_9' ),
    inference(resolution,[status(thm)],[c_15247,c_15304])).

tff(c_15322,plain,(
    k2_zfmisc_1('#skF_7','#skF_8') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_15217,c_15304])).

tff(c_15390,plain,(
    k2_zfmisc_1('#skF_7','#skF_8') = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_15321,c_15322])).

tff(c_22,plain,(
    ! [B_14,A_13] :
      ( k1_xboole_0 = B_14
      | k1_xboole_0 = A_13
      | k2_zfmisc_1(A_13,B_14) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_15698,plain,(
    ! [B_1001,A_1002] :
      ( B_1001 = '#skF_9'
      | A_1002 = '#skF_9'
      | k2_zfmisc_1(A_1002,B_1001) != '#skF_9' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_15321,c_15321,c_15321,c_22])).

tff(c_15712,plain,
    ( '#skF_9' = '#skF_8'
    | '#skF_7' = '#skF_9' ),
    inference(superposition,[status(thm),theory(equality)],[c_15390,c_15698])).

tff(c_15713,plain,(
    '#skF_7' = '#skF_9' ),
    inference(splitLeft,[status(thm)],[c_15712])).

tff(c_145,plain,(
    ! [E_65] :
      ( k1_funct_1('#skF_10',E_65) = k1_funct_1('#skF_9',E_65)
      | ~ r2_hidden(E_65,'#skF_7') ) ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_155,plain,
    ( k1_funct_1('#skF_10','#skF_1'('#skF_7')) = k1_funct_1('#skF_9','#skF_1'('#skF_7'))
    | v1_xboole_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_4,c_145])).

tff(c_244,plain,(
    v1_xboole_0('#skF_7') ),
    inference(splitLeft,[status(thm)],[c_155])).

tff(c_1817,plain,(
    ! [A_228,B_229] :
      ( r2_hidden('#skF_3'(A_228,B_229),B_229)
      | r2_hidden('#skF_4'(A_228,B_229),A_228)
      | B_229 = A_228 ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_1861,plain,(
    ! [B_230,A_231] :
      ( ~ v1_xboole_0(B_230)
      | r2_hidden('#skF_4'(A_231,B_230),A_231)
      | B_230 = A_231 ) ),
    inference(resolution,[status(thm)],[c_1817,c_2])).

tff(c_1877,plain,(
    ! [A_232,B_233] :
      ( ~ v1_xboole_0(A_232)
      | ~ v1_xboole_0(B_233)
      | B_233 = A_232 ) ),
    inference(resolution,[status(thm)],[c_1861,c_2])).

tff(c_1908,plain,(
    ! [B_235] :
      ( ~ v1_xboole_0(B_235)
      | k1_xboole_0 = B_235 ) ),
    inference(resolution,[status(thm)],[c_12,c_1877])).

tff(c_1935,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(resolution,[status(thm)],[c_244,c_1908])).

tff(c_26,plain,(
    ! [B_14] : k2_zfmisc_1(k1_xboole_0,B_14) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_1953,plain,(
    ! [B_14] : k2_zfmisc_1('#skF_7',B_14) = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1935,c_1935,c_26])).

tff(c_270,plain,(
    ! [C_95,A_96,B_97] :
      ( r2_hidden(C_95,A_96)
      | ~ r2_hidden(C_95,B_97)
      | ~ m1_subset_1(B_97,k1_zfmisc_1(A_96)) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_1679,plain,(
    ! [A_216,A_217] :
      ( r2_hidden('#skF_1'(A_216),A_217)
      | ~ m1_subset_1(A_216,k1_zfmisc_1(A_217))
      | v1_xboole_0(A_216) ) ),
    inference(resolution,[status(thm)],[c_4,c_270])).

tff(c_1695,plain,(
    ! [A_218,A_219] :
      ( ~ v1_xboole_0(A_218)
      | ~ m1_subset_1(A_219,k1_zfmisc_1(A_218))
      | v1_xboole_0(A_219) ) ),
    inference(resolution,[status(thm)],[c_1679,c_2])).

tff(c_1712,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1('#skF_7','#skF_8'))
    | v1_xboole_0('#skF_10') ),
    inference(resolution,[status(thm)],[c_66,c_1695])).

tff(c_1715,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_7','#skF_8')) ),
    inference(splitLeft,[status(thm)],[c_1712])).

tff(c_2149,plain,(
    ~ v1_xboole_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1953,c_1715])).

tff(c_2154,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_244,c_2149])).

tff(c_2156,plain,(
    v1_xboole_0(k2_zfmisc_1('#skF_7','#skF_8')) ),
    inference(splitRight,[status(thm)],[c_1712])).

tff(c_1713,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1('#skF_7','#skF_8'))
    | v1_xboole_0('#skF_9') ),
    inference(resolution,[status(thm)],[c_72,c_1695])).

tff(c_2157,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_7','#skF_8')) ),
    inference(splitLeft,[status(thm)],[c_1713])).

tff(c_2159,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2156,c_2157])).

tff(c_2160,plain,(
    v1_xboole_0('#skF_9') ),
    inference(splitRight,[status(thm)],[c_1713])).

tff(c_2597,plain,(
    ! [A_283,B_284] :
      ( r2_hidden('#skF_3'(A_283,B_284),B_284)
      | r2_hidden('#skF_4'(A_283,B_284),A_283)
      | B_284 = A_283 ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_2654,plain,(
    ! [B_286,A_287] :
      ( ~ v1_xboole_0(B_286)
      | r2_hidden('#skF_4'(A_287,B_286),A_287)
      | B_286 = A_287 ) ),
    inference(resolution,[status(thm)],[c_2597,c_2])).

tff(c_2678,plain,(
    ! [A_288,B_289] :
      ( ~ v1_xboole_0(A_288)
      | ~ v1_xboole_0(B_289)
      | B_289 = A_288 ) ),
    inference(resolution,[status(thm)],[c_2654,c_2])).

tff(c_2721,plain,(
    ! [B_291] :
      ( ~ v1_xboole_0(B_291)
      | k1_xboole_0 = B_291 ) ),
    inference(resolution,[status(thm)],[c_12,c_2678])).

tff(c_2762,plain,(
    k1_xboole_0 = '#skF_9' ),
    inference(resolution,[status(thm)],[c_2160,c_2721])).

tff(c_28,plain,(
    ! [A_15] : m1_subset_1('#skF_5'(A_15),A_15) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_1714,plain,(
    ! [A_218] :
      ( ~ v1_xboole_0(A_218)
      | v1_xboole_0('#skF_5'(k1_zfmisc_1(A_218))) ) ),
    inference(resolution,[status(thm)],[c_28,c_1695])).

tff(c_2760,plain,(
    ! [A_218] :
      ( '#skF_5'(k1_zfmisc_1(A_218)) = k1_xboole_0
      | ~ v1_xboole_0(A_218) ) ),
    inference(resolution,[status(thm)],[c_1714,c_2721])).

tff(c_3090,plain,(
    ! [A_309] :
      ( '#skF_5'(k1_zfmisc_1(A_309)) = '#skF_9'
      | ~ v1_xboole_0(A_309) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2762,c_2760])).

tff(c_3126,plain,(
    ! [A_309] :
      ( m1_subset_1('#skF_9',k1_zfmisc_1(A_309))
      | ~ v1_xboole_0(A_309) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3090,c_28])).

tff(c_2785,plain,(
    ! [B_14] : k2_zfmisc_1('#skF_9',B_14) = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2762,c_2762,c_26])).

tff(c_3146,plain,(
    ! [A_310,B_311,C_312,D_313] :
      ( r2_relset_1(A_310,B_311,C_312,C_312)
      | ~ m1_subset_1(D_313,k1_zfmisc_1(k2_zfmisc_1(A_310,B_311)))
      | ~ m1_subset_1(C_312,k1_zfmisc_1(k2_zfmisc_1(A_310,B_311))) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_3602,plain,(
    ! [A_346,B_347,C_348] :
      ( r2_relset_1(A_346,B_347,C_348,C_348)
      | ~ m1_subset_1(C_348,k1_zfmisc_1(k2_zfmisc_1(A_346,B_347))) ) ),
    inference(resolution,[status(thm)],[c_28,c_3146])).

tff(c_3635,plain,(
    ! [B_352,C_353] :
      ( r2_relset_1('#skF_9',B_352,C_353,C_353)
      | ~ m1_subset_1(C_353,k1_zfmisc_1('#skF_9')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2785,c_3602])).

tff(c_3638,plain,(
    ! [B_352] :
      ( r2_relset_1('#skF_9',B_352,'#skF_9','#skF_9')
      | ~ v1_xboole_0('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_3126,c_3635])).

tff(c_3646,plain,(
    ! [B_352] : r2_relset_1('#skF_9',B_352,'#skF_9','#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2160,c_3638])).

tff(c_2764,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(resolution,[status(thm)],[c_244,c_2721])).

tff(c_2830,plain,(
    '#skF_7' = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2762,c_2764])).

tff(c_2155,plain,(
    v1_xboole_0('#skF_10') ),
    inference(splitRight,[status(thm)],[c_1712])).

tff(c_2763,plain,(
    k1_xboole_0 = '#skF_10' ),
    inference(resolution,[status(thm)],[c_2155,c_2721])).

tff(c_2797,plain,(
    '#skF_10' = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2762,c_2763])).

tff(c_2813,plain,(
    ~ r2_relset_1('#skF_7','#skF_8','#skF_9','#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2797,c_62])).

tff(c_2995,plain,(
    ~ r2_relset_1('#skF_9','#skF_8','#skF_9','#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2830,c_2813])).

tff(c_3652,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3646,c_2995])).

tff(c_3654,plain,(
    ~ v1_xboole_0('#skF_7') ),
    inference(splitRight,[status(thm)],[c_155])).

tff(c_15718,plain,(
    ~ v1_xboole_0('#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_15713,c_3654])).

tff(c_15723,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_15247,c_15718])).

tff(c_15724,plain,(
    '#skF_9' = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_15712])).

tff(c_15749,plain,(
    v1_xboole_0('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_15724,c_15247])).

tff(c_15340,plain,(
    ! [A_13] : k2_zfmisc_1(A_13,'#skF_9') = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_15321,c_15321,c_24])).

tff(c_15741,plain,(
    ! [A_13] : k2_zfmisc_1(A_13,'#skF_8') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_15724,c_15724,c_15340])).

tff(c_4390,plain,(
    ! [A_431] :
      ( ~ v1_xboole_0(A_431)
      | v1_xboole_0('#skF_5'(k1_zfmisc_1(A_431))) ) ),
    inference(resolution,[status(thm)],[c_28,c_4371])).

tff(c_15320,plain,(
    ! [A_431] :
      ( '#skF_5'(k1_zfmisc_1(A_431)) = k1_xboole_0
      | ~ v1_xboole_0(A_431) ) ),
    inference(resolution,[status(thm)],[c_4390,c_15304])).

tff(c_15558,plain,(
    ! [A_989] :
      ( '#skF_5'(k1_zfmisc_1(A_989)) = '#skF_9'
      | ~ v1_xboole_0(A_989) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_15321,c_15320])).

tff(c_15585,plain,(
    ! [A_989] :
      ( m1_subset_1('#skF_9',k1_zfmisc_1(A_989))
      | ~ v1_xboole_0(A_989) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_15558,c_28])).

tff(c_15730,plain,(
    ! [A_989] :
      ( m1_subset_1('#skF_8',k1_zfmisc_1(A_989))
      | ~ v1_xboole_0(A_989) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_15724,c_15585])).

tff(c_15879,plain,(
    ! [A_1015,B_1016,C_1017,D_1018] :
      ( r2_relset_1(A_1015,B_1016,C_1017,C_1017)
      | ~ m1_subset_1(D_1018,k1_zfmisc_1(k2_zfmisc_1(A_1015,B_1016)))
      | ~ m1_subset_1(C_1017,k1_zfmisc_1(k2_zfmisc_1(A_1015,B_1016))) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_16560,plain,(
    ! [A_1063,B_1064,C_1065] :
      ( r2_relset_1(A_1063,B_1064,C_1065,C_1065)
      | ~ m1_subset_1(C_1065,k1_zfmisc_1(k2_zfmisc_1(A_1063,B_1064))) ) ),
    inference(resolution,[status(thm)],[c_28,c_15879])).

tff(c_16573,plain,(
    ! [A_1066,B_1067] :
      ( r2_relset_1(A_1066,B_1067,'#skF_8','#skF_8')
      | ~ v1_xboole_0(k2_zfmisc_1(A_1066,B_1067)) ) ),
    inference(resolution,[status(thm)],[c_15730,c_16560])).

tff(c_16576,plain,(
    ! [A_13] :
      ( r2_relset_1(A_13,'#skF_8','#skF_8','#skF_8')
      | ~ v1_xboole_0('#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_15741,c_16573])).

tff(c_16581,plain,(
    ! [A_13] : r2_relset_1(A_13,'#skF_8','#skF_8','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_15749,c_16576])).

tff(c_15216,plain,(
    v1_xboole_0('#skF_10') ),
    inference(splitRight,[status(thm)],[c_4388])).

tff(c_15323,plain,(
    k1_xboole_0 = '#skF_10' ),
    inference(resolution,[status(thm)],[c_15216,c_15304])).

tff(c_15362,plain,(
    '#skF_10' = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_15321,c_15323])).

tff(c_15372,plain,(
    ~ r2_relset_1('#skF_7','#skF_8','#skF_9','#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_15362,c_62])).

tff(c_15744,plain,(
    ~ r2_relset_1('#skF_7','#skF_8','#skF_8','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_15724,c_15724,c_15372])).

tff(c_16586,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_16581,c_15744])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:19:55 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 11.37/3.98  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.37/3.99  
% 11.37/3.99  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.37/4.00  %$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_1 > #skF_7 > #skF_3 > #skF_10 > #skF_9 > #skF_8 > #skF_2 > #skF_4
% 11.37/4.00  
% 11.37/4.00  %Foreground sorts:
% 11.37/4.00  
% 11.37/4.00  
% 11.37/4.00  %Background operators:
% 11.37/4.00  
% 11.37/4.00  
% 11.37/4.00  %Foreground operators:
% 11.37/4.00  tff('#skF_5', type, '#skF_5': $i > $i).
% 11.37/4.00  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 11.37/4.00  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 11.37/4.00  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 11.37/4.00  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 11.37/4.00  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 11.37/4.00  tff('#skF_1', type, '#skF_1': $i > $i).
% 11.37/4.00  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 11.37/4.00  tff('#skF_7', type, '#skF_7': $i).
% 11.37/4.00  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 11.37/4.00  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 11.37/4.00  tff('#skF_10', type, '#skF_10': $i).
% 11.37/4.00  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 11.37/4.00  tff('#skF_9', type, '#skF_9': $i).
% 11.37/4.00  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 11.37/4.00  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 11.37/4.00  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 11.37/4.00  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 11.37/4.00  tff('#skF_8', type, '#skF_8': $i).
% 11.37/4.00  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 11.37/4.00  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 11.37/4.00  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 11.37/4.00  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 11.37/4.00  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 11.37/4.00  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 11.37/4.00  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 11.37/4.00  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 11.37/4.00  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 11.37/4.00  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 11.37/4.00  
% 11.57/4.02  tff(f_145, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((![E]: (r2_hidden(E, A) => (k1_funct_1(C, E) = k1_funct_1(D, E)))) => r2_relset_1(A, B, C, D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t18_funct_2)).
% 11.57/4.02  tff(f_106, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => r2_relset_1(A, B, C, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', reflexivity_r2_relset_1)).
% 11.57/4.02  tff(f_90, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 11.57/4.02  tff(f_100, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 11.57/4.02  tff(f_124, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 11.57/4.02  tff(f_86, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (((k1_relat_1(A) = k1_relat_1(B)) & (![C]: (r2_hidden(C, k1_relat_1(A)) => (k1_funct_1(A, C) = k1_funct_1(B, C))))) => (A = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t9_funct_1)).
% 11.57/4.02  tff(f_39, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 11.57/4.02  tff(f_52, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 11.57/4.02  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 11.57/4.02  tff(f_62, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_subset_1)).
% 11.57/4.02  tff(f_46, axiom, (![A, B]: ((![C]: (r2_hidden(C, A) <=> r2_hidden(C, B))) => (A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_tarski)).
% 11.57/4.02  tff(f_55, axiom, (![A]: (?[B]: m1_subset_1(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', existence_m1_subset_1)).
% 11.57/4.02  tff(c_72, plain, (m1_subset_1('#skF_9', k1_zfmisc_1(k2_zfmisc_1('#skF_7', '#skF_8')))), inference(cnfTransformation, [status(thm)], [f_145])).
% 11.57/4.02  tff(c_66, plain, (m1_subset_1('#skF_10', k1_zfmisc_1(k2_zfmisc_1('#skF_7', '#skF_8')))), inference(cnfTransformation, [status(thm)], [f_145])).
% 11.57/4.02  tff(c_5857, plain, (![A_533, B_534, C_535, D_536]: (r2_relset_1(A_533, B_534, C_535, C_535) | ~m1_subset_1(D_536, k1_zfmisc_1(k2_zfmisc_1(A_533, B_534))) | ~m1_subset_1(C_535, k1_zfmisc_1(k2_zfmisc_1(A_533, B_534))))), inference(cnfTransformation, [status(thm)], [f_106])).
% 11.57/4.02  tff(c_5881, plain, (![C_537]: (r2_relset_1('#skF_7', '#skF_8', C_537, C_537) | ~m1_subset_1(C_537, k1_zfmisc_1(k2_zfmisc_1('#skF_7', '#skF_8'))))), inference(resolution, [status(thm)], [c_66, c_5857])).
% 11.57/4.02  tff(c_5898, plain, (r2_relset_1('#skF_7', '#skF_8', '#skF_9', '#skF_9')), inference(resolution, [status(thm)], [c_72, c_5881])).
% 11.57/4.02  tff(c_121, plain, (![C_58, A_59, B_60]: (v1_relat_1(C_58) | ~m1_subset_1(C_58, k1_zfmisc_1(k2_zfmisc_1(A_59, B_60))))), inference(cnfTransformation, [status(thm)], [f_90])).
% 11.57/4.02  tff(c_136, plain, (v1_relat_1('#skF_10')), inference(resolution, [status(thm)], [c_66, c_121])).
% 11.57/4.02  tff(c_70, plain, (v1_funct_1('#skF_10')), inference(cnfTransformation, [status(thm)], [f_145])).
% 11.57/4.02  tff(c_68, plain, (v1_funct_2('#skF_10', '#skF_7', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_145])).
% 11.57/4.02  tff(c_4531, plain, (![A_447, B_448, C_449]: (k1_relset_1(A_447, B_448, C_449)=k1_relat_1(C_449) | ~m1_subset_1(C_449, k1_zfmisc_1(k2_zfmisc_1(A_447, B_448))))), inference(cnfTransformation, [status(thm)], [f_100])).
% 11.57/4.02  tff(c_4548, plain, (k1_relset_1('#skF_7', '#skF_8', '#skF_10')=k1_relat_1('#skF_10')), inference(resolution, [status(thm)], [c_66, c_4531])).
% 11.57/4.02  tff(c_5967, plain, (![B_546, A_547, C_548]: (k1_xboole_0=B_546 | k1_relset_1(A_547, B_546, C_548)=A_547 | ~v1_funct_2(C_548, A_547, B_546) | ~m1_subset_1(C_548, k1_zfmisc_1(k2_zfmisc_1(A_547, B_546))))), inference(cnfTransformation, [status(thm)], [f_124])).
% 11.57/4.02  tff(c_5978, plain, (k1_xboole_0='#skF_8' | k1_relset_1('#skF_7', '#skF_8', '#skF_10')='#skF_7' | ~v1_funct_2('#skF_10', '#skF_7', '#skF_8')), inference(resolution, [status(thm)], [c_66, c_5967])).
% 11.57/4.02  tff(c_5996, plain, (k1_xboole_0='#skF_8' | k1_relat_1('#skF_10')='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_68, c_4548, c_5978])).
% 11.57/4.02  tff(c_6002, plain, (k1_relat_1('#skF_10')='#skF_7'), inference(splitLeft, [status(thm)], [c_5996])).
% 11.57/4.02  tff(c_137, plain, (v1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_72, c_121])).
% 11.57/4.02  tff(c_76, plain, (v1_funct_1('#skF_9')), inference(cnfTransformation, [status(thm)], [f_145])).
% 11.57/4.02  tff(c_74, plain, (v1_funct_2('#skF_9', '#skF_7', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_145])).
% 11.57/4.02  tff(c_4549, plain, (k1_relset_1('#skF_7', '#skF_8', '#skF_9')=k1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_72, c_4531])).
% 11.57/4.02  tff(c_5981, plain, (k1_xboole_0='#skF_8' | k1_relset_1('#skF_7', '#skF_8', '#skF_9')='#skF_7' | ~v1_funct_2('#skF_9', '#skF_7', '#skF_8')), inference(resolution, [status(thm)], [c_72, c_5967])).
% 11.57/4.02  tff(c_5999, plain, (k1_xboole_0='#skF_8' | k1_relat_1('#skF_9')='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_74, c_4549, c_5981])).
% 11.57/4.02  tff(c_6027, plain, (k1_relat_1('#skF_9')='#skF_7'), inference(splitLeft, [status(thm)], [c_5999])).
% 11.57/4.02  tff(c_6278, plain, (![A_562, B_563]: (r2_hidden('#skF_6'(A_562, B_563), k1_relat_1(A_562)) | B_563=A_562 | k1_relat_1(B_563)!=k1_relat_1(A_562) | ~v1_funct_1(B_563) | ~v1_relat_1(B_563) | ~v1_funct_1(A_562) | ~v1_relat_1(A_562))), inference(cnfTransformation, [status(thm)], [f_86])).
% 11.57/4.02  tff(c_6288, plain, (![B_563]: (r2_hidden('#skF_6'('#skF_9', B_563), '#skF_7') | B_563='#skF_9' | k1_relat_1(B_563)!=k1_relat_1('#skF_9') | ~v1_funct_1(B_563) | ~v1_relat_1(B_563) | ~v1_funct_1('#skF_9') | ~v1_relat_1('#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_6027, c_6278])).
% 11.57/4.02  tff(c_14708, plain, (![B_943]: (r2_hidden('#skF_6'('#skF_9', B_943), '#skF_7') | B_943='#skF_9' | k1_relat_1(B_943)!='#skF_7' | ~v1_funct_1(B_943) | ~v1_relat_1(B_943))), inference(demodulation, [status(thm), theory('equality')], [c_137, c_76, c_6027, c_6288])).
% 11.57/4.02  tff(c_64, plain, (![E_49]: (k1_funct_1('#skF_10', E_49)=k1_funct_1('#skF_9', E_49) | ~r2_hidden(E_49, '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_145])).
% 11.57/4.02  tff(c_14821, plain, (![B_948]: (k1_funct_1('#skF_10', '#skF_6'('#skF_9', B_948))=k1_funct_1('#skF_9', '#skF_6'('#skF_9', B_948)) | B_948='#skF_9' | k1_relat_1(B_948)!='#skF_7' | ~v1_funct_1(B_948) | ~v1_relat_1(B_948))), inference(resolution, [status(thm)], [c_14708, c_64])).
% 11.57/4.02  tff(c_36, plain, (![B_27, A_23]: (k1_funct_1(B_27, '#skF_6'(A_23, B_27))!=k1_funct_1(A_23, '#skF_6'(A_23, B_27)) | B_27=A_23 | k1_relat_1(B_27)!=k1_relat_1(A_23) | ~v1_funct_1(B_27) | ~v1_relat_1(B_27) | ~v1_funct_1(A_23) | ~v1_relat_1(A_23))), inference(cnfTransformation, [status(thm)], [f_86])).
% 11.57/4.02  tff(c_14828, plain, (k1_relat_1('#skF_10')!=k1_relat_1('#skF_9') | ~v1_funct_1('#skF_9') | ~v1_relat_1('#skF_9') | '#skF_10'='#skF_9' | k1_relat_1('#skF_10')!='#skF_7' | ~v1_funct_1('#skF_10') | ~v1_relat_1('#skF_10')), inference(superposition, [status(thm), theory('equality')], [c_14821, c_36])).
% 11.57/4.02  tff(c_14835, plain, ('#skF_10'='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_136, c_70, c_6002, c_137, c_76, c_6002, c_6027, c_14828])).
% 11.57/4.02  tff(c_62, plain, (~r2_relset_1('#skF_7', '#skF_8', '#skF_9', '#skF_10')), inference(cnfTransformation, [status(thm)], [f_145])).
% 11.57/4.02  tff(c_14887, plain, (~r2_relset_1('#skF_7', '#skF_8', '#skF_9', '#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_14835, c_62])).
% 11.57/4.02  tff(c_14900, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_5898, c_14887])).
% 11.57/4.02  tff(c_14901, plain, (k1_xboole_0='#skF_8'), inference(splitRight, [status(thm)], [c_5999])).
% 11.57/4.02  tff(c_12, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 11.57/4.02  tff(c_14944, plain, (v1_xboole_0('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_14901, c_12])).
% 11.57/4.02  tff(c_24, plain, (![A_13]: (k2_zfmisc_1(A_13, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_52])).
% 11.57/4.02  tff(c_14943, plain, (![A_13]: (k2_zfmisc_1(A_13, '#skF_8')='#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_14901, c_14901, c_24])).
% 11.57/4.02  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 11.57/4.02  tff(c_4345, plain, (![C_426, A_427, B_428]: (r2_hidden(C_426, A_427) | ~r2_hidden(C_426, B_428) | ~m1_subset_1(B_428, k1_zfmisc_1(A_427)))), inference(cnfTransformation, [status(thm)], [f_62])).
% 11.57/4.02  tff(c_4355, plain, (![A_429, A_430]: (r2_hidden('#skF_1'(A_429), A_430) | ~m1_subset_1(A_429, k1_zfmisc_1(A_430)) | v1_xboole_0(A_429))), inference(resolution, [status(thm)], [c_4, c_4345])).
% 11.57/4.02  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 11.57/4.02  tff(c_4371, plain, (![A_431, A_432]: (~v1_xboole_0(A_431) | ~m1_subset_1(A_432, k1_zfmisc_1(A_431)) | v1_xboole_0(A_432))), inference(resolution, [status(thm)], [c_4355, c_2])).
% 11.57/4.02  tff(c_4388, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_7', '#skF_8')) | v1_xboole_0('#skF_10')), inference(resolution, [status(thm)], [c_66, c_4371])).
% 11.57/4.02  tff(c_4391, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_7', '#skF_8'))), inference(splitLeft, [status(thm)], [c_4388])).
% 11.57/4.02  tff(c_15077, plain, (~v1_xboole_0('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_14943, c_4391])).
% 11.57/4.02  tff(c_15082, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_14944, c_15077])).
% 11.57/4.02  tff(c_15083, plain, (k1_xboole_0='#skF_8'), inference(splitRight, [status(thm)], [c_5996])).
% 11.57/4.02  tff(c_15126, plain, (v1_xboole_0('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_15083, c_12])).
% 11.57/4.02  tff(c_15125, plain, (![A_13]: (k2_zfmisc_1(A_13, '#skF_8')='#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_15083, c_15083, c_24])).
% 11.57/4.02  tff(c_15210, plain, (~v1_xboole_0('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_15125, c_4391])).
% 11.57/4.02  tff(c_15215, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_15126, c_15210])).
% 11.57/4.02  tff(c_15217, plain, (v1_xboole_0(k2_zfmisc_1('#skF_7', '#skF_8'))), inference(splitRight, [status(thm)], [c_4388])).
% 11.57/4.02  tff(c_4389, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_7', '#skF_8')) | v1_xboole_0('#skF_9')), inference(resolution, [status(thm)], [c_72, c_4371])).
% 11.57/4.02  tff(c_15247, plain, (v1_xboole_0('#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_15217, c_4389])).
% 11.57/4.02  tff(c_15218, plain, (![A_962, B_963]: (r2_hidden('#skF_3'(A_962, B_963), B_963) | r2_hidden('#skF_4'(A_962, B_963), A_962) | B_963=A_962)), inference(cnfTransformation, [status(thm)], [f_46])).
% 11.57/4.02  tff(c_15272, plain, (![B_966, A_967]: (~v1_xboole_0(B_966) | r2_hidden('#skF_4'(A_967, B_966), A_967) | B_966=A_967)), inference(resolution, [status(thm)], [c_15218, c_2])).
% 11.57/4.02  tff(c_15288, plain, (![A_968, B_969]: (~v1_xboole_0(A_968) | ~v1_xboole_0(B_969) | B_969=A_968)), inference(resolution, [status(thm)], [c_15272, c_2])).
% 11.57/4.02  tff(c_15304, plain, (![B_970]: (~v1_xboole_0(B_970) | k1_xboole_0=B_970)), inference(resolution, [status(thm)], [c_12, c_15288])).
% 11.57/4.02  tff(c_15321, plain, (k1_xboole_0='#skF_9'), inference(resolution, [status(thm)], [c_15247, c_15304])).
% 11.57/4.02  tff(c_15322, plain, (k2_zfmisc_1('#skF_7', '#skF_8')=k1_xboole_0), inference(resolution, [status(thm)], [c_15217, c_15304])).
% 11.57/4.02  tff(c_15390, plain, (k2_zfmisc_1('#skF_7', '#skF_8')='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_15321, c_15322])).
% 11.57/4.02  tff(c_22, plain, (![B_14, A_13]: (k1_xboole_0=B_14 | k1_xboole_0=A_13 | k2_zfmisc_1(A_13, B_14)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_52])).
% 11.57/4.02  tff(c_15698, plain, (![B_1001, A_1002]: (B_1001='#skF_9' | A_1002='#skF_9' | k2_zfmisc_1(A_1002, B_1001)!='#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_15321, c_15321, c_15321, c_22])).
% 11.57/4.02  tff(c_15712, plain, ('#skF_9'='#skF_8' | '#skF_7'='#skF_9'), inference(superposition, [status(thm), theory('equality')], [c_15390, c_15698])).
% 11.57/4.02  tff(c_15713, plain, ('#skF_7'='#skF_9'), inference(splitLeft, [status(thm)], [c_15712])).
% 11.57/4.02  tff(c_145, plain, (![E_65]: (k1_funct_1('#skF_10', E_65)=k1_funct_1('#skF_9', E_65) | ~r2_hidden(E_65, '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_145])).
% 11.57/4.02  tff(c_155, plain, (k1_funct_1('#skF_10', '#skF_1'('#skF_7'))=k1_funct_1('#skF_9', '#skF_1'('#skF_7')) | v1_xboole_0('#skF_7')), inference(resolution, [status(thm)], [c_4, c_145])).
% 11.57/4.02  tff(c_244, plain, (v1_xboole_0('#skF_7')), inference(splitLeft, [status(thm)], [c_155])).
% 11.57/4.02  tff(c_1817, plain, (![A_228, B_229]: (r2_hidden('#skF_3'(A_228, B_229), B_229) | r2_hidden('#skF_4'(A_228, B_229), A_228) | B_229=A_228)), inference(cnfTransformation, [status(thm)], [f_46])).
% 11.57/4.02  tff(c_1861, plain, (![B_230, A_231]: (~v1_xboole_0(B_230) | r2_hidden('#skF_4'(A_231, B_230), A_231) | B_230=A_231)), inference(resolution, [status(thm)], [c_1817, c_2])).
% 11.57/4.02  tff(c_1877, plain, (![A_232, B_233]: (~v1_xboole_0(A_232) | ~v1_xboole_0(B_233) | B_233=A_232)), inference(resolution, [status(thm)], [c_1861, c_2])).
% 11.57/4.02  tff(c_1908, plain, (![B_235]: (~v1_xboole_0(B_235) | k1_xboole_0=B_235)), inference(resolution, [status(thm)], [c_12, c_1877])).
% 11.57/4.02  tff(c_1935, plain, (k1_xboole_0='#skF_7'), inference(resolution, [status(thm)], [c_244, c_1908])).
% 11.57/4.02  tff(c_26, plain, (![B_14]: (k2_zfmisc_1(k1_xboole_0, B_14)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_52])).
% 11.57/4.02  tff(c_1953, plain, (![B_14]: (k2_zfmisc_1('#skF_7', B_14)='#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_1935, c_1935, c_26])).
% 11.57/4.02  tff(c_270, plain, (![C_95, A_96, B_97]: (r2_hidden(C_95, A_96) | ~r2_hidden(C_95, B_97) | ~m1_subset_1(B_97, k1_zfmisc_1(A_96)))), inference(cnfTransformation, [status(thm)], [f_62])).
% 11.57/4.02  tff(c_1679, plain, (![A_216, A_217]: (r2_hidden('#skF_1'(A_216), A_217) | ~m1_subset_1(A_216, k1_zfmisc_1(A_217)) | v1_xboole_0(A_216))), inference(resolution, [status(thm)], [c_4, c_270])).
% 11.57/4.02  tff(c_1695, plain, (![A_218, A_219]: (~v1_xboole_0(A_218) | ~m1_subset_1(A_219, k1_zfmisc_1(A_218)) | v1_xboole_0(A_219))), inference(resolution, [status(thm)], [c_1679, c_2])).
% 11.57/4.02  tff(c_1712, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_7', '#skF_8')) | v1_xboole_0('#skF_10')), inference(resolution, [status(thm)], [c_66, c_1695])).
% 11.57/4.02  tff(c_1715, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_7', '#skF_8'))), inference(splitLeft, [status(thm)], [c_1712])).
% 11.57/4.02  tff(c_2149, plain, (~v1_xboole_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_1953, c_1715])).
% 11.57/4.02  tff(c_2154, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_244, c_2149])).
% 11.57/4.02  tff(c_2156, plain, (v1_xboole_0(k2_zfmisc_1('#skF_7', '#skF_8'))), inference(splitRight, [status(thm)], [c_1712])).
% 11.57/4.02  tff(c_1713, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_7', '#skF_8')) | v1_xboole_0('#skF_9')), inference(resolution, [status(thm)], [c_72, c_1695])).
% 11.57/4.02  tff(c_2157, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_7', '#skF_8'))), inference(splitLeft, [status(thm)], [c_1713])).
% 11.57/4.02  tff(c_2159, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2156, c_2157])).
% 11.57/4.02  tff(c_2160, plain, (v1_xboole_0('#skF_9')), inference(splitRight, [status(thm)], [c_1713])).
% 11.57/4.02  tff(c_2597, plain, (![A_283, B_284]: (r2_hidden('#skF_3'(A_283, B_284), B_284) | r2_hidden('#skF_4'(A_283, B_284), A_283) | B_284=A_283)), inference(cnfTransformation, [status(thm)], [f_46])).
% 11.57/4.02  tff(c_2654, plain, (![B_286, A_287]: (~v1_xboole_0(B_286) | r2_hidden('#skF_4'(A_287, B_286), A_287) | B_286=A_287)), inference(resolution, [status(thm)], [c_2597, c_2])).
% 11.57/4.02  tff(c_2678, plain, (![A_288, B_289]: (~v1_xboole_0(A_288) | ~v1_xboole_0(B_289) | B_289=A_288)), inference(resolution, [status(thm)], [c_2654, c_2])).
% 11.57/4.02  tff(c_2721, plain, (![B_291]: (~v1_xboole_0(B_291) | k1_xboole_0=B_291)), inference(resolution, [status(thm)], [c_12, c_2678])).
% 11.57/4.02  tff(c_2762, plain, (k1_xboole_0='#skF_9'), inference(resolution, [status(thm)], [c_2160, c_2721])).
% 11.57/4.02  tff(c_28, plain, (![A_15]: (m1_subset_1('#skF_5'(A_15), A_15))), inference(cnfTransformation, [status(thm)], [f_55])).
% 11.57/4.02  tff(c_1714, plain, (![A_218]: (~v1_xboole_0(A_218) | v1_xboole_0('#skF_5'(k1_zfmisc_1(A_218))))), inference(resolution, [status(thm)], [c_28, c_1695])).
% 11.57/4.02  tff(c_2760, plain, (![A_218]: ('#skF_5'(k1_zfmisc_1(A_218))=k1_xboole_0 | ~v1_xboole_0(A_218))), inference(resolution, [status(thm)], [c_1714, c_2721])).
% 11.57/4.02  tff(c_3090, plain, (![A_309]: ('#skF_5'(k1_zfmisc_1(A_309))='#skF_9' | ~v1_xboole_0(A_309))), inference(demodulation, [status(thm), theory('equality')], [c_2762, c_2760])).
% 11.57/4.02  tff(c_3126, plain, (![A_309]: (m1_subset_1('#skF_9', k1_zfmisc_1(A_309)) | ~v1_xboole_0(A_309))), inference(superposition, [status(thm), theory('equality')], [c_3090, c_28])).
% 11.57/4.02  tff(c_2785, plain, (![B_14]: (k2_zfmisc_1('#skF_9', B_14)='#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_2762, c_2762, c_26])).
% 11.57/4.02  tff(c_3146, plain, (![A_310, B_311, C_312, D_313]: (r2_relset_1(A_310, B_311, C_312, C_312) | ~m1_subset_1(D_313, k1_zfmisc_1(k2_zfmisc_1(A_310, B_311))) | ~m1_subset_1(C_312, k1_zfmisc_1(k2_zfmisc_1(A_310, B_311))))), inference(cnfTransformation, [status(thm)], [f_106])).
% 11.57/4.02  tff(c_3602, plain, (![A_346, B_347, C_348]: (r2_relset_1(A_346, B_347, C_348, C_348) | ~m1_subset_1(C_348, k1_zfmisc_1(k2_zfmisc_1(A_346, B_347))))), inference(resolution, [status(thm)], [c_28, c_3146])).
% 11.57/4.02  tff(c_3635, plain, (![B_352, C_353]: (r2_relset_1('#skF_9', B_352, C_353, C_353) | ~m1_subset_1(C_353, k1_zfmisc_1('#skF_9')))), inference(superposition, [status(thm), theory('equality')], [c_2785, c_3602])).
% 11.57/4.02  tff(c_3638, plain, (![B_352]: (r2_relset_1('#skF_9', B_352, '#skF_9', '#skF_9') | ~v1_xboole_0('#skF_9'))), inference(resolution, [status(thm)], [c_3126, c_3635])).
% 11.57/4.02  tff(c_3646, plain, (![B_352]: (r2_relset_1('#skF_9', B_352, '#skF_9', '#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_2160, c_3638])).
% 11.57/4.02  tff(c_2764, plain, (k1_xboole_0='#skF_7'), inference(resolution, [status(thm)], [c_244, c_2721])).
% 11.57/4.02  tff(c_2830, plain, ('#skF_7'='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_2762, c_2764])).
% 11.57/4.02  tff(c_2155, plain, (v1_xboole_0('#skF_10')), inference(splitRight, [status(thm)], [c_1712])).
% 11.57/4.02  tff(c_2763, plain, (k1_xboole_0='#skF_10'), inference(resolution, [status(thm)], [c_2155, c_2721])).
% 11.57/4.02  tff(c_2797, plain, ('#skF_10'='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_2762, c_2763])).
% 11.57/4.02  tff(c_2813, plain, (~r2_relset_1('#skF_7', '#skF_8', '#skF_9', '#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_2797, c_62])).
% 11.57/4.02  tff(c_2995, plain, (~r2_relset_1('#skF_9', '#skF_8', '#skF_9', '#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_2830, c_2813])).
% 11.57/4.02  tff(c_3652, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3646, c_2995])).
% 11.57/4.02  tff(c_3654, plain, (~v1_xboole_0('#skF_7')), inference(splitRight, [status(thm)], [c_155])).
% 11.57/4.02  tff(c_15718, plain, (~v1_xboole_0('#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_15713, c_3654])).
% 11.57/4.02  tff(c_15723, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_15247, c_15718])).
% 11.57/4.02  tff(c_15724, plain, ('#skF_9'='#skF_8'), inference(splitRight, [status(thm)], [c_15712])).
% 11.57/4.02  tff(c_15749, plain, (v1_xboole_0('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_15724, c_15247])).
% 11.57/4.02  tff(c_15340, plain, (![A_13]: (k2_zfmisc_1(A_13, '#skF_9')='#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_15321, c_15321, c_24])).
% 11.57/4.02  tff(c_15741, plain, (![A_13]: (k2_zfmisc_1(A_13, '#skF_8')='#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_15724, c_15724, c_15340])).
% 11.57/4.02  tff(c_4390, plain, (![A_431]: (~v1_xboole_0(A_431) | v1_xboole_0('#skF_5'(k1_zfmisc_1(A_431))))), inference(resolution, [status(thm)], [c_28, c_4371])).
% 11.57/4.02  tff(c_15320, plain, (![A_431]: ('#skF_5'(k1_zfmisc_1(A_431))=k1_xboole_0 | ~v1_xboole_0(A_431))), inference(resolution, [status(thm)], [c_4390, c_15304])).
% 11.57/4.02  tff(c_15558, plain, (![A_989]: ('#skF_5'(k1_zfmisc_1(A_989))='#skF_9' | ~v1_xboole_0(A_989))), inference(demodulation, [status(thm), theory('equality')], [c_15321, c_15320])).
% 11.57/4.02  tff(c_15585, plain, (![A_989]: (m1_subset_1('#skF_9', k1_zfmisc_1(A_989)) | ~v1_xboole_0(A_989))), inference(superposition, [status(thm), theory('equality')], [c_15558, c_28])).
% 11.57/4.02  tff(c_15730, plain, (![A_989]: (m1_subset_1('#skF_8', k1_zfmisc_1(A_989)) | ~v1_xboole_0(A_989))), inference(demodulation, [status(thm), theory('equality')], [c_15724, c_15585])).
% 11.57/4.02  tff(c_15879, plain, (![A_1015, B_1016, C_1017, D_1018]: (r2_relset_1(A_1015, B_1016, C_1017, C_1017) | ~m1_subset_1(D_1018, k1_zfmisc_1(k2_zfmisc_1(A_1015, B_1016))) | ~m1_subset_1(C_1017, k1_zfmisc_1(k2_zfmisc_1(A_1015, B_1016))))), inference(cnfTransformation, [status(thm)], [f_106])).
% 11.57/4.02  tff(c_16560, plain, (![A_1063, B_1064, C_1065]: (r2_relset_1(A_1063, B_1064, C_1065, C_1065) | ~m1_subset_1(C_1065, k1_zfmisc_1(k2_zfmisc_1(A_1063, B_1064))))), inference(resolution, [status(thm)], [c_28, c_15879])).
% 11.57/4.02  tff(c_16573, plain, (![A_1066, B_1067]: (r2_relset_1(A_1066, B_1067, '#skF_8', '#skF_8') | ~v1_xboole_0(k2_zfmisc_1(A_1066, B_1067)))), inference(resolution, [status(thm)], [c_15730, c_16560])).
% 11.57/4.02  tff(c_16576, plain, (![A_13]: (r2_relset_1(A_13, '#skF_8', '#skF_8', '#skF_8') | ~v1_xboole_0('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_15741, c_16573])).
% 11.57/4.02  tff(c_16581, plain, (![A_13]: (r2_relset_1(A_13, '#skF_8', '#skF_8', '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_15749, c_16576])).
% 11.57/4.02  tff(c_15216, plain, (v1_xboole_0('#skF_10')), inference(splitRight, [status(thm)], [c_4388])).
% 11.57/4.02  tff(c_15323, plain, (k1_xboole_0='#skF_10'), inference(resolution, [status(thm)], [c_15216, c_15304])).
% 11.57/4.02  tff(c_15362, plain, ('#skF_10'='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_15321, c_15323])).
% 11.57/4.02  tff(c_15372, plain, (~r2_relset_1('#skF_7', '#skF_8', '#skF_9', '#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_15362, c_62])).
% 11.57/4.02  tff(c_15744, plain, (~r2_relset_1('#skF_7', '#skF_8', '#skF_8', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_15724, c_15724, c_15372])).
% 11.57/4.02  tff(c_16586, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_16581, c_15744])).
% 11.57/4.02  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.57/4.02  
% 11.57/4.02  Inference rules
% 11.57/4.02  ----------------------
% 11.57/4.02  #Ref     : 3
% 11.57/4.02  #Sup     : 3563
% 11.57/4.02  #Fact    : 0
% 11.57/4.02  #Define  : 0
% 11.57/4.02  #Split   : 49
% 11.57/4.02  #Chain   : 0
% 11.57/4.02  #Close   : 0
% 11.57/4.02  
% 11.57/4.02  Ordering : KBO
% 11.57/4.02  
% 11.57/4.02  Simplification rules
% 11.57/4.02  ----------------------
% 11.57/4.02  #Subsume      : 2032
% 11.57/4.02  #Demod        : 3090
% 11.57/4.02  #Tautology    : 1411
% 11.57/4.02  #SimpNegUnit  : 532
% 11.57/4.02  #BackRed      : 730
% 11.57/4.02  
% 11.57/4.02  #Partial instantiations: 0
% 11.57/4.02  #Strategies tried      : 1
% 11.57/4.02  
% 11.57/4.02  Timing (in seconds)
% 11.57/4.02  ----------------------
% 11.57/4.03  Preprocessing        : 0.38
% 11.57/4.03  Parsing              : 0.20
% 11.57/4.03  CNF conversion       : 0.03
% 11.57/4.03  Main loop            : 2.83
% 11.57/4.03  Inferencing          : 0.88
% 11.57/4.03  Reduction            : 0.94
% 11.57/4.03  Demodulation         : 0.65
% 11.57/4.03  BG Simplification    : 0.08
% 11.57/4.03  Subsumption          : 0.71
% 11.57/4.03  Abstraction          : 0.11
% 11.57/4.03  MUC search           : 0.00
% 11.57/4.03  Cooper               : 0.00
% 11.57/4.03  Total                : 3.27
% 11.57/4.03  Index Insertion      : 0.00
% 11.57/4.03  Index Deletion       : 0.00
% 11.57/4.03  Index Matching       : 0.00
% 11.57/4.03  BG Taut test         : 0.00
%------------------------------------------------------------------------------
