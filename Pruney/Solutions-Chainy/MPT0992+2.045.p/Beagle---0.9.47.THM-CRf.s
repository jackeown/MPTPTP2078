%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:13:37 EST 2020

% Result     : Theorem 5.88s
% Output     : CNFRefutation 5.88s
% Verified   : 
% Statistics : Number of formulae       :  174 (2445 expanded)
%              Number of leaves         :   40 ( 766 expanded)
%              Depth                    :   14
%              Number of atoms          :  264 (7640 expanded)
%              Number of equality atoms :   72 (3002 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_partfun1 > k1_relset_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_partfun1,type,(
    k2_partfun1: ( $i * $i * $i * $i ) > $i )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_145,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( r1_tarski(C,A)
         => ( ( B = k1_xboole_0
              & A != k1_xboole_0 )
            | ( v1_funct_1(k2_partfun1(A,B,D,C))
              & v1_funct_2(k2_partfun1(A,B,D,C),C,B)
              & m1_subset_1(k2_partfun1(A,B,D,C),k1_zfmisc_1(k2_zfmisc_1(C,B))) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_funct_2)).

tff(f_75,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_85,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_111,axiom,(
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

tff(f_71,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(A,k1_relat_1(B))
       => k1_relat_1(k7_relat_1(B,A)) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_relat_1)).

tff(f_125,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => k2_partfun1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

tff(f_61,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k1_relat_1(k7_relat_1(B,A)),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_relat_1)).

tff(f_119,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( v1_funct_1(k2_partfun1(A,B,C,D))
        & m1_subset_1(k2_partfun1(A,B,C,D),k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_partfun1)).

tff(f_81,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k7_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).

tff(f_93,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( ( r1_tarski(k1_relat_1(C),A)
          & r1_tarski(k2_relat_1(C),B) )
       => m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_relset_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_29,axiom,(
    ! [A] :
      ( r1_tarski(A,k1_xboole_0)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).

tff(f_37,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_65,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k7_relat_1(B,A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_relat_1)).

tff(c_62,plain,(
    r1_tarski('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_64,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_758,plain,(
    ! [C_150,A_151,B_152] :
      ( v1_relat_1(C_150)
      | ~ m1_subset_1(C_150,k1_zfmisc_1(k2_zfmisc_1(A_151,B_152))) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_775,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_64,c_758])).

tff(c_60,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_74,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_60])).

tff(c_66,plain,(
    v1_funct_2('#skF_4','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_2812,plain,(
    ! [A_412,B_413,C_414] :
      ( k1_relset_1(A_412,B_413,C_414) = k1_relat_1(C_414)
      | ~ m1_subset_1(C_414,k1_zfmisc_1(k2_zfmisc_1(A_412,B_413))) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_2835,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_64,c_2812])).

tff(c_3370,plain,(
    ! [B_488,A_489,C_490] :
      ( k1_xboole_0 = B_488
      | k1_relset_1(A_489,B_488,C_490) = A_489
      | ~ v1_funct_2(C_490,A_489,B_488)
      | ~ m1_subset_1(C_490,k1_zfmisc_1(k2_zfmisc_1(A_489,B_488))) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_3383,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1('#skF_1','#skF_2','#skF_4') = '#skF_1'
    | ~ v1_funct_2('#skF_4','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_64,c_3370])).

tff(c_3401,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_2835,c_3383])).

tff(c_3402,plain,(
    k1_relat_1('#skF_4') = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_3401])).

tff(c_28,plain,(
    ! [B_19,A_18] :
      ( k1_relat_1(k7_relat_1(B_19,A_18)) = A_18
      | ~ r1_tarski(A_18,k1_relat_1(B_19))
      | ~ v1_relat_1(B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_3410,plain,(
    ! [A_18] :
      ( k1_relat_1(k7_relat_1('#skF_4',A_18)) = A_18
      | ~ r1_tarski(A_18,'#skF_1')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3402,c_28])).

tff(c_3420,plain,(
    ! [A_491] :
      ( k1_relat_1(k7_relat_1('#skF_4',A_491)) = A_491
      | ~ r1_tarski(A_491,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_775,c_3410])).

tff(c_68,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_3110,plain,(
    ! [A_453,B_454,C_455,D_456] :
      ( k2_partfun1(A_453,B_454,C_455,D_456) = k7_relat_1(C_455,D_456)
      | ~ m1_subset_1(C_455,k1_zfmisc_1(k2_zfmisc_1(A_453,B_454)))
      | ~ v1_funct_1(C_455) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_3117,plain,(
    ! [D_456] :
      ( k2_partfun1('#skF_1','#skF_2','#skF_4',D_456) = k7_relat_1('#skF_4',D_456)
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_64,c_3110])).

tff(c_3131,plain,(
    ! [D_456] : k2_partfun1('#skF_1','#skF_2','#skF_4',D_456) = k7_relat_1('#skF_4',D_456) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_3117])).

tff(c_24,plain,(
    ! [B_15,A_14] :
      ( r1_tarski(k1_relat_1(k7_relat_1(B_15,A_14)),A_14)
      | ~ v1_relat_1(B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_1764,plain,(
    ! [A_298,B_299,C_300,D_301] :
      ( k2_partfun1(A_298,B_299,C_300,D_301) = k7_relat_1(C_300,D_301)
      | ~ m1_subset_1(C_300,k1_zfmisc_1(k2_zfmisc_1(A_298,B_299)))
      | ~ v1_funct_1(C_300) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_1771,plain,(
    ! [D_301] :
      ( k2_partfun1('#skF_1','#skF_2','#skF_4',D_301) = k7_relat_1('#skF_4',D_301)
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_64,c_1764])).

tff(c_1783,plain,(
    ! [D_301] : k2_partfun1('#skF_1','#skF_2','#skF_4',D_301) = k7_relat_1('#skF_4',D_301) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_1771])).

tff(c_2126,plain,(
    ! [A_328,B_329,C_330,D_331] :
      ( m1_subset_1(k2_partfun1(A_328,B_329,C_330,D_331),k1_zfmisc_1(k2_zfmisc_1(A_328,B_329)))
      | ~ m1_subset_1(C_330,k1_zfmisc_1(k2_zfmisc_1(A_328,B_329)))
      | ~ v1_funct_1(C_330) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_2156,plain,(
    ! [D_301] :
      ( m1_subset_1(k7_relat_1('#skF_4',D_301),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
      | ~ v1_funct_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1783,c_2126])).

tff(c_2177,plain,(
    ! [D_332] : m1_subset_1(k7_relat_1('#skF_4',D_332),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_64,c_2156])).

tff(c_32,plain,(
    ! [C_25,B_24,A_23] :
      ( v5_relat_1(C_25,B_24)
      | ~ m1_subset_1(C_25,k1_zfmisc_1(k2_zfmisc_1(A_23,B_24))) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_2219,plain,(
    ! [D_332] : v5_relat_1(k7_relat_1('#skF_4',D_332),'#skF_2') ),
    inference(resolution,[status(thm)],[c_2177,c_32])).

tff(c_22,plain,(
    ! [A_12,B_13] :
      ( v1_relat_1(k7_relat_1(A_12,B_13))
      | ~ v1_relat_1(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_1697,plain,(
    ! [A_282,B_283,C_284,D_285] :
      ( k2_partfun1(A_282,B_283,C_284,D_285) = k7_relat_1(C_284,D_285)
      | ~ m1_subset_1(C_284,k1_zfmisc_1(k2_zfmisc_1(A_282,B_283)))
      | ~ v1_funct_1(C_284) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_1704,plain,(
    ! [D_285] :
      ( k2_partfun1('#skF_1','#skF_2','#skF_4',D_285) = k7_relat_1('#skF_4',D_285)
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_64,c_1697])).

tff(c_1716,plain,(
    ! [D_285] : k2_partfun1('#skF_1','#skF_2','#skF_4',D_285) = k7_relat_1('#skF_4',D_285) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_1704])).

tff(c_1463,plain,(
    ! [C_252,A_253,B_254] :
      ( m1_subset_1(C_252,k1_zfmisc_1(k2_zfmisc_1(A_253,B_254)))
      | ~ r1_tarski(k2_relat_1(C_252),B_254)
      | ~ r1_tarski(k1_relat_1(C_252),A_253)
      | ~ v1_relat_1(C_252) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_730,plain,(
    ! [A_144,B_145,C_146,D_147] :
      ( v1_funct_1(k2_partfun1(A_144,B_145,C_146,D_147))
      | ~ m1_subset_1(C_146,k1_zfmisc_1(k2_zfmisc_1(A_144,B_145)))
      | ~ v1_funct_1(C_146) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_735,plain,(
    ! [D_147] :
      ( v1_funct_1(k2_partfun1('#skF_1','#skF_2','#skF_4',D_147))
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_64,c_730])).

tff(c_746,plain,(
    ! [D_147] : v1_funct_1(k2_partfun1('#skF_1','#skF_2','#skF_4',D_147)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_735])).

tff(c_58,plain,
    ( ~ m1_subset_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2')))
    | ~ v1_funct_2(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),'#skF_3','#skF_2')
    | ~ v1_funct_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_206,plain,(
    ~ v1_funct_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_58])).

tff(c_750,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_746,c_206])).

tff(c_751,plain,
    ( ~ v1_funct_2(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),'#skF_3','#skF_2')
    | ~ m1_subset_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_813,plain,(
    ~ m1_subset_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_751])).

tff(c_1496,plain,
    ( ~ r1_tarski(k2_relat_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3')),'#skF_2')
    | ~ r1_tarski(k1_relat_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3')),'#skF_3')
    | ~ v1_relat_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3')) ),
    inference(resolution,[status(thm)],[c_1463,c_813])).

tff(c_1669,plain,(
    ~ v1_relat_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_1496])).

tff(c_1719,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_4','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1716,c_1669])).

tff(c_1735,plain,(
    ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_22,c_1719])).

tff(c_1739,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_775,c_1735])).

tff(c_1741,plain,(
    v1_relat_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_1496])).

tff(c_1786,plain,(
    v1_relat_1(k7_relat_1('#skF_4','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1783,c_1741])).

tff(c_20,plain,(
    ! [B_11,A_10] :
      ( r1_tarski(k2_relat_1(B_11),A_10)
      | ~ v5_relat_1(B_11,A_10)
      | ~ v1_relat_1(B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_1740,plain,
    ( ~ r1_tarski(k1_relat_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3')),'#skF_3')
    | ~ r1_tarski(k2_relat_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3')),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_1496])).

tff(c_1882,plain,
    ( ~ r1_tarski(k1_relat_1(k7_relat_1('#skF_4','#skF_3')),'#skF_3')
    | ~ r1_tarski(k2_relat_1(k7_relat_1('#skF_4','#skF_3')),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1783,c_1783,c_1740])).

tff(c_1883,plain,(
    ~ r1_tarski(k2_relat_1(k7_relat_1('#skF_4','#skF_3')),'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_1882])).

tff(c_1886,plain,
    ( ~ v5_relat_1(k7_relat_1('#skF_4','#skF_3'),'#skF_2')
    | ~ v1_relat_1(k7_relat_1('#skF_4','#skF_3')) ),
    inference(resolution,[status(thm)],[c_20,c_1883])).

tff(c_1889,plain,(
    ~ v5_relat_1(k7_relat_1('#skF_4','#skF_3'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1786,c_1886])).

tff(c_2230,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2219,c_1889])).

tff(c_2231,plain,(
    ~ r1_tarski(k1_relat_1(k7_relat_1('#skF_4','#skF_3')),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_1882])).

tff(c_2241,plain,(
    ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_24,c_2231])).

tff(c_2245,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_775,c_2241])).

tff(c_2246,plain,(
    ~ v1_funct_2(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),'#skF_3','#skF_2') ),
    inference(splitRight,[status(thm)],[c_751])).

tff(c_3143,plain,(
    ~ v1_funct_2(k7_relat_1('#skF_4','#skF_3'),'#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3131,c_2246])).

tff(c_2247,plain,(
    m1_subset_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_751])).

tff(c_2833,plain,(
    k1_relset_1('#skF_3','#skF_2',k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3')) = k1_relat_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3')) ),
    inference(resolution,[status(thm)],[c_2247,c_2812])).

tff(c_3136,plain,(
    k1_relset_1('#skF_3','#skF_2',k7_relat_1('#skF_4','#skF_3')) = k1_relat_1(k7_relat_1('#skF_4','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3131,c_3131,c_2833])).

tff(c_3142,plain,(
    m1_subset_1(k7_relat_1('#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3131,c_2247])).

tff(c_3319,plain,(
    ! [B_483,C_484,A_485] :
      ( k1_xboole_0 = B_483
      | v1_funct_2(C_484,A_485,B_483)
      | k1_relset_1(A_485,B_483,C_484) != A_485
      | ~ m1_subset_1(C_484,k1_zfmisc_1(k2_zfmisc_1(A_485,B_483))) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_3325,plain,
    ( k1_xboole_0 = '#skF_2'
    | v1_funct_2(k7_relat_1('#skF_4','#skF_3'),'#skF_3','#skF_2')
    | k1_relset_1('#skF_3','#skF_2',k7_relat_1('#skF_4','#skF_3')) != '#skF_3' ),
    inference(resolution,[status(thm)],[c_3142,c_3319])).

tff(c_3345,plain,
    ( k1_xboole_0 = '#skF_2'
    | v1_funct_2(k7_relat_1('#skF_4','#skF_3'),'#skF_3','#skF_2')
    | k1_relat_1(k7_relat_1('#skF_4','#skF_3')) != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3136,c_3325])).

tff(c_3346,plain,(
    k1_relat_1(k7_relat_1('#skF_4','#skF_3')) != '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_3143,c_74,c_3345])).

tff(c_3426,plain,(
    ~ r1_tarski('#skF_3','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_3420,c_3346])).

tff(c_3472,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_3426])).

tff(c_3473,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_60])).

tff(c_6,plain,(
    ! [A_2] : k2_zfmisc_1(A_2,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_3487,plain,(
    ! [A_2] : k2_zfmisc_1(A_2,'#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3473,c_3473,c_6])).

tff(c_3474,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_60])).

tff(c_3479,plain,(
    '#skF_2' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3473,c_3474])).

tff(c_3511,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3487,c_3479,c_64])).

tff(c_3702,plain,(
    ! [A_522,B_523] :
      ( r1_tarski(A_522,B_523)
      | ~ m1_subset_1(A_522,k1_zfmisc_1(B_523)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_3713,plain,(
    r1_tarski('#skF_4','#skF_1') ),
    inference(resolution,[status(thm)],[c_3511,c_3702])).

tff(c_2,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ r1_tarski(A_1,k1_xboole_0) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_3512,plain,(
    ! [A_1] :
      ( A_1 = '#skF_1'
      | ~ r1_tarski(A_1,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3473,c_3473,c_2])).

tff(c_3718,plain,(
    '#skF_1' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_3713,c_3512])).

tff(c_3480,plain,(
    v1_funct_2('#skF_4','#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3479,c_66])).

tff(c_3729,plain,(
    v1_funct_2('#skF_4','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3718,c_3718,c_3480])).

tff(c_10,plain,(
    ! [A_4] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_4)) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_3485,plain,(
    ! [A_4] : m1_subset_1('#skF_1',k1_zfmisc_1(A_4)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3473,c_10])).

tff(c_3714,plain,(
    ! [A_4] : r1_tarski('#skF_1',A_4) ),
    inference(resolution,[status(thm)],[c_3485,c_3702])).

tff(c_4340,plain,(
    ! [A_4] : r1_tarski('#skF_4',A_4) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3718,c_3714])).

tff(c_3541,plain,(
    ! [A_503,B_504] :
      ( r1_tarski(A_503,B_504)
      | ~ m1_subset_1(A_503,k1_zfmisc_1(B_504)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_3552,plain,(
    r1_tarski('#skF_4','#skF_1') ),
    inference(resolution,[status(thm)],[c_3511,c_3541])).

tff(c_3557,plain,(
    '#skF_1' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_3552,c_3512])).

tff(c_3531,plain,(
    ! [B_499,A_500] :
      ( r1_tarski(k7_relat_1(B_499,A_500),B_499)
      | ~ v1_relat_1(B_499) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_3536,plain,(
    ! [A_500] :
      ( k7_relat_1('#skF_1',A_500) = '#skF_1'
      | ~ v1_relat_1('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_3531,c_3512])).

tff(c_3537,plain,(
    ~ v1_relat_1('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_3536])).

tff(c_3560,plain,(
    ~ v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3557,c_3537])).

tff(c_3569,plain,(
    ! [A_4] : m1_subset_1('#skF_4',k1_zfmisc_1(A_4)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3557,c_3485])).

tff(c_3665,plain,(
    ! [C_516,A_517,B_518] :
      ( v1_relat_1(C_516)
      | ~ m1_subset_1(C_516,k1_zfmisc_1(k2_zfmisc_1(A_517,B_518))) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_3673,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_3569,c_3665])).

tff(c_3681,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3560,c_3673])).

tff(c_3682,plain,(
    ! [A_500] : k7_relat_1('#skF_1',A_500) = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_3536])).

tff(c_3720,plain,(
    ! [A_500] : k7_relat_1('#skF_4',A_500) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3718,c_3718,c_3682])).

tff(c_3730,plain,(
    ! [A_4] : m1_subset_1('#skF_4',k1_zfmisc_1(A_4)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3718,c_3485])).

tff(c_5319,plain,(
    ! [A_751,B_752,C_753,D_754] :
      ( k2_partfun1(A_751,B_752,C_753,D_754) = k7_relat_1(C_753,D_754)
      | ~ m1_subset_1(C_753,k1_zfmisc_1(k2_zfmisc_1(A_751,B_752)))
      | ~ v1_funct_1(C_753) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_5328,plain,(
    ! [A_751,B_752,D_754] :
      ( k2_partfun1(A_751,B_752,'#skF_4',D_754) = k7_relat_1('#skF_4',D_754)
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_3730,c_5319])).

tff(c_5335,plain,(
    ! [A_751,B_752,D_754] : k2_partfun1(A_751,B_752,'#skF_4',D_754) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_3720,c_5328])).

tff(c_14,plain,(
    ! [A_5,B_6] :
      ( m1_subset_1(A_5,k1_zfmisc_1(B_6))
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_8,plain,(
    ! [B_3] : k2_zfmisc_1(k1_xboole_0,B_3) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_3495,plain,(
    ! [B_3] : k2_zfmisc_1('#skF_1',B_3) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3473,c_3473,c_8])).

tff(c_3727,plain,(
    ! [B_3] : k2_zfmisc_1('#skF_4',B_3) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3718,c_3718,c_3495])).

tff(c_3731,plain,(
    '#skF_2' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3718,c_3479])).

tff(c_3513,plain,(
    ! [A_495] :
      ( A_495 = '#skF_1'
      | ~ r1_tarski(A_495,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3473,c_3473,c_2])).

tff(c_3517,plain,(
    '#skF_3' = '#skF_1' ),
    inference(resolution,[status(thm)],[c_62,c_3513])).

tff(c_3724,plain,(
    '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3718,c_3517])).

tff(c_4307,plain,(
    ! [A_607,B_608,C_609,D_610] :
      ( v1_funct_1(k2_partfun1(A_607,B_608,C_609,D_610))
      | ~ m1_subset_1(C_609,k1_zfmisc_1(k2_zfmisc_1(A_607,B_608)))
      | ~ v1_funct_1(C_609) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_4310,plain,(
    ! [A_607,B_608,D_610] :
      ( v1_funct_1(k2_partfun1(A_607,B_608,'#skF_4',D_610))
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_3730,c_4307])).

tff(c_4320,plain,(
    ! [A_607,B_608,D_610] : v1_funct_1(k2_partfun1(A_607,B_608,'#skF_4',D_610)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_4310])).

tff(c_3737,plain,
    ( ~ m1_subset_1(k2_partfun1('#skF_4','#skF_2','#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2')))
    | ~ v1_funct_2(k2_partfun1('#skF_4','#skF_2','#skF_4','#skF_3'),'#skF_3','#skF_2')
    | ~ v1_funct_1(k2_partfun1('#skF_4','#skF_2','#skF_4','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3718,c_3718,c_3718,c_58])).

tff(c_3738,plain,(
    ~ v1_funct_1(k2_partfun1('#skF_4','#skF_2','#skF_4','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_3737])).

tff(c_3856,plain,(
    ~ v1_funct_1(k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3731,c_3724,c_3738])).

tff(c_4324,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4320,c_3856])).

tff(c_4325,plain,
    ( ~ v1_funct_2(k2_partfun1('#skF_4','#skF_2','#skF_4','#skF_3'),'#skF_3','#skF_2')
    | ~ m1_subset_1(k2_partfun1('#skF_4','#skF_2','#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_3737])).

tff(c_4550,plain,
    ( ~ v1_funct_2(k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_4'),'#skF_4','#skF_4')
    | ~ m1_subset_1(k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_4'),k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3727,c_3731,c_3731,c_3724,c_3724,c_3731,c_3731,c_3724,c_3724,c_4325])).

tff(c_4551,plain,(
    ~ m1_subset_1(k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_4'),k1_zfmisc_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_4550])).

tff(c_4634,plain,(
    ~ r1_tarski(k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_4'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_14,c_4551])).

tff(c_5338,plain,(
    ~ r1_tarski('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5335,c_4634])).

tff(c_5343,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4340,c_5338])).

tff(c_5345,plain,(
    m1_subset_1(k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_4'),k1_zfmisc_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_4550])).

tff(c_12,plain,(
    ! [A_5,B_6] :
      ( r1_tarski(A_5,B_6)
      | ~ m1_subset_1(A_5,k1_zfmisc_1(B_6)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_5435,plain,(
    r1_tarski(k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_4'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_5345,c_12])).

tff(c_3725,plain,(
    ! [A_1] :
      ( A_1 = '#skF_4'
      | ~ r1_tarski(A_1,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3718,c_3718,c_3512])).

tff(c_5444,plain,(
    k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_4') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_5435,c_3725])).

tff(c_5344,plain,(
    ~ v1_funct_2(k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_4'),'#skF_4','#skF_4') ),
    inference(splitRight,[status(thm)],[c_4550])).

tff(c_5448,plain,(
    ~ v1_funct_2('#skF_4','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5444,c_5344])).

tff(c_5455,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3729,c_5448])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n013.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 17:16:09 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.88/2.16  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.88/2.17  
% 5.88/2.17  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.88/2.17  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_partfun1 > k1_relset_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
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
% 5.88/2.17  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 5.88/2.17  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.88/2.17  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.88/2.17  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 5.88/2.17  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 5.88/2.17  tff('#skF_2', type, '#skF_2': $i).
% 5.88/2.17  tff('#skF_3', type, '#skF_3': $i).
% 5.88/2.17  tff('#skF_1', type, '#skF_1': $i).
% 5.88/2.17  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 5.88/2.17  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 5.88/2.17  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.88/2.17  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.88/2.17  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.88/2.17  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 5.88/2.17  tff('#skF_4', type, '#skF_4': $i).
% 5.88/2.17  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.88/2.17  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 5.88/2.17  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 5.88/2.17  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 5.88/2.17  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.88/2.17  
% 5.88/2.20  tff(f_145, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r1_tarski(C, A) => (((B = k1_xboole_0) & ~(A = k1_xboole_0)) | ((v1_funct_1(k2_partfun1(A, B, D, C)) & v1_funct_2(k2_partfun1(A, B, D, C), C, B)) & m1_subset_1(k2_partfun1(A, B, D, C), k1_zfmisc_1(k2_zfmisc_1(C, B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_funct_2)).
% 5.88/2.20  tff(f_75, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 5.88/2.20  tff(f_85, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 5.88/2.20  tff(f_111, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 5.88/2.20  tff(f_71, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(A, k1_relat_1(B)) => (k1_relat_1(k7_relat_1(B, A)) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_relat_1)).
% 5.88/2.20  tff(f_125, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (k2_partfun1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_partfun1)).
% 5.88/2.20  tff(f_61, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k7_relat_1(B, A)), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t87_relat_1)).
% 5.88/2.20  tff(f_119, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (v1_funct_1(k2_partfun1(A, B, C, D)) & m1_subset_1(k2_partfun1(A, B, C, D), k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_partfun1)).
% 5.88/2.20  tff(f_81, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 5.88/2.20  tff(f_57, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k7_relat_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 5.88/2.20  tff(f_93, axiom, (![A, B, C]: (v1_relat_1(C) => ((r1_tarski(k1_relat_1(C), A) & r1_tarski(k2_relat_1(C), B)) => m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_relset_1)).
% 5.88/2.20  tff(f_53, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 5.88/2.20  tff(f_35, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 5.88/2.20  tff(f_41, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 5.88/2.20  tff(f_29, axiom, (![A]: (r1_tarski(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_1)).
% 5.88/2.20  tff(f_37, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 5.88/2.20  tff(f_65, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k7_relat_1(B, A), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t88_relat_1)).
% 5.88/2.20  tff(c_62, plain, (r1_tarski('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_145])).
% 5.88/2.20  tff(c_64, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_145])).
% 5.88/2.20  tff(c_758, plain, (![C_150, A_151, B_152]: (v1_relat_1(C_150) | ~m1_subset_1(C_150, k1_zfmisc_1(k2_zfmisc_1(A_151, B_152))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 5.88/2.20  tff(c_775, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_64, c_758])).
% 5.88/2.20  tff(c_60, plain, (k1_xboole_0='#skF_1' | k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_145])).
% 5.88/2.20  tff(c_74, plain, (k1_xboole_0!='#skF_2'), inference(splitLeft, [status(thm)], [c_60])).
% 5.88/2.20  tff(c_66, plain, (v1_funct_2('#skF_4', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_145])).
% 5.88/2.20  tff(c_2812, plain, (![A_412, B_413, C_414]: (k1_relset_1(A_412, B_413, C_414)=k1_relat_1(C_414) | ~m1_subset_1(C_414, k1_zfmisc_1(k2_zfmisc_1(A_412, B_413))))), inference(cnfTransformation, [status(thm)], [f_85])).
% 5.88/2.20  tff(c_2835, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_64, c_2812])).
% 5.88/2.20  tff(c_3370, plain, (![B_488, A_489, C_490]: (k1_xboole_0=B_488 | k1_relset_1(A_489, B_488, C_490)=A_489 | ~v1_funct_2(C_490, A_489, B_488) | ~m1_subset_1(C_490, k1_zfmisc_1(k2_zfmisc_1(A_489, B_488))))), inference(cnfTransformation, [status(thm)], [f_111])).
% 5.88/2.20  tff(c_3383, plain, (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', '#skF_4')='#skF_1' | ~v1_funct_2('#skF_4', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_64, c_3370])).
% 5.88/2.20  tff(c_3401, plain, (k1_xboole_0='#skF_2' | k1_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_66, c_2835, c_3383])).
% 5.88/2.20  tff(c_3402, plain, (k1_relat_1('#skF_4')='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_74, c_3401])).
% 5.88/2.20  tff(c_28, plain, (![B_19, A_18]: (k1_relat_1(k7_relat_1(B_19, A_18))=A_18 | ~r1_tarski(A_18, k1_relat_1(B_19)) | ~v1_relat_1(B_19))), inference(cnfTransformation, [status(thm)], [f_71])).
% 5.88/2.20  tff(c_3410, plain, (![A_18]: (k1_relat_1(k7_relat_1('#skF_4', A_18))=A_18 | ~r1_tarski(A_18, '#skF_1') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_3402, c_28])).
% 5.88/2.20  tff(c_3420, plain, (![A_491]: (k1_relat_1(k7_relat_1('#skF_4', A_491))=A_491 | ~r1_tarski(A_491, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_775, c_3410])).
% 5.88/2.20  tff(c_68, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_145])).
% 5.88/2.20  tff(c_3110, plain, (![A_453, B_454, C_455, D_456]: (k2_partfun1(A_453, B_454, C_455, D_456)=k7_relat_1(C_455, D_456) | ~m1_subset_1(C_455, k1_zfmisc_1(k2_zfmisc_1(A_453, B_454))) | ~v1_funct_1(C_455))), inference(cnfTransformation, [status(thm)], [f_125])).
% 5.88/2.20  tff(c_3117, plain, (![D_456]: (k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_456)=k7_relat_1('#skF_4', D_456) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_64, c_3110])).
% 5.88/2.20  tff(c_3131, plain, (![D_456]: (k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_456)=k7_relat_1('#skF_4', D_456))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_3117])).
% 5.88/2.20  tff(c_24, plain, (![B_15, A_14]: (r1_tarski(k1_relat_1(k7_relat_1(B_15, A_14)), A_14) | ~v1_relat_1(B_15))), inference(cnfTransformation, [status(thm)], [f_61])).
% 5.88/2.20  tff(c_1764, plain, (![A_298, B_299, C_300, D_301]: (k2_partfun1(A_298, B_299, C_300, D_301)=k7_relat_1(C_300, D_301) | ~m1_subset_1(C_300, k1_zfmisc_1(k2_zfmisc_1(A_298, B_299))) | ~v1_funct_1(C_300))), inference(cnfTransformation, [status(thm)], [f_125])).
% 5.88/2.20  tff(c_1771, plain, (![D_301]: (k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_301)=k7_relat_1('#skF_4', D_301) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_64, c_1764])).
% 5.88/2.20  tff(c_1783, plain, (![D_301]: (k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_301)=k7_relat_1('#skF_4', D_301))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_1771])).
% 5.88/2.20  tff(c_2126, plain, (![A_328, B_329, C_330, D_331]: (m1_subset_1(k2_partfun1(A_328, B_329, C_330, D_331), k1_zfmisc_1(k2_zfmisc_1(A_328, B_329))) | ~m1_subset_1(C_330, k1_zfmisc_1(k2_zfmisc_1(A_328, B_329))) | ~v1_funct_1(C_330))), inference(cnfTransformation, [status(thm)], [f_119])).
% 5.88/2.20  tff(c_2156, plain, (![D_301]: (m1_subset_1(k7_relat_1('#skF_4', D_301), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_1783, c_2126])).
% 5.88/2.20  tff(c_2177, plain, (![D_332]: (m1_subset_1(k7_relat_1('#skF_4', D_332), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_64, c_2156])).
% 5.88/2.20  tff(c_32, plain, (![C_25, B_24, A_23]: (v5_relat_1(C_25, B_24) | ~m1_subset_1(C_25, k1_zfmisc_1(k2_zfmisc_1(A_23, B_24))))), inference(cnfTransformation, [status(thm)], [f_81])).
% 5.88/2.20  tff(c_2219, plain, (![D_332]: (v5_relat_1(k7_relat_1('#skF_4', D_332), '#skF_2'))), inference(resolution, [status(thm)], [c_2177, c_32])).
% 5.88/2.20  tff(c_22, plain, (![A_12, B_13]: (v1_relat_1(k7_relat_1(A_12, B_13)) | ~v1_relat_1(A_12))), inference(cnfTransformation, [status(thm)], [f_57])).
% 5.88/2.20  tff(c_1697, plain, (![A_282, B_283, C_284, D_285]: (k2_partfun1(A_282, B_283, C_284, D_285)=k7_relat_1(C_284, D_285) | ~m1_subset_1(C_284, k1_zfmisc_1(k2_zfmisc_1(A_282, B_283))) | ~v1_funct_1(C_284))), inference(cnfTransformation, [status(thm)], [f_125])).
% 5.88/2.20  tff(c_1704, plain, (![D_285]: (k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_285)=k7_relat_1('#skF_4', D_285) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_64, c_1697])).
% 5.88/2.20  tff(c_1716, plain, (![D_285]: (k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_285)=k7_relat_1('#skF_4', D_285))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_1704])).
% 5.88/2.20  tff(c_1463, plain, (![C_252, A_253, B_254]: (m1_subset_1(C_252, k1_zfmisc_1(k2_zfmisc_1(A_253, B_254))) | ~r1_tarski(k2_relat_1(C_252), B_254) | ~r1_tarski(k1_relat_1(C_252), A_253) | ~v1_relat_1(C_252))), inference(cnfTransformation, [status(thm)], [f_93])).
% 5.88/2.20  tff(c_730, plain, (![A_144, B_145, C_146, D_147]: (v1_funct_1(k2_partfun1(A_144, B_145, C_146, D_147)) | ~m1_subset_1(C_146, k1_zfmisc_1(k2_zfmisc_1(A_144, B_145))) | ~v1_funct_1(C_146))), inference(cnfTransformation, [status(thm)], [f_119])).
% 5.88/2.20  tff(c_735, plain, (![D_147]: (v1_funct_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_147)) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_64, c_730])).
% 5.88/2.20  tff(c_746, plain, (![D_147]: (v1_funct_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_147)))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_735])).
% 5.88/2.20  tff(c_58, plain, (~m1_subset_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2'))) | ~v1_funct_2(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), '#skF_3', '#skF_2') | ~v1_funct_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_145])).
% 5.88/2.20  tff(c_206, plain, (~v1_funct_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'))), inference(splitLeft, [status(thm)], [c_58])).
% 5.88/2.20  tff(c_750, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_746, c_206])).
% 5.88/2.20  tff(c_751, plain, (~v1_funct_2(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), '#skF_3', '#skF_2') | ~m1_subset_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(splitRight, [status(thm)], [c_58])).
% 5.88/2.20  tff(c_813, plain, (~m1_subset_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(splitLeft, [status(thm)], [c_751])).
% 5.88/2.20  tff(c_1496, plain, (~r1_tarski(k2_relat_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3')), '#skF_2') | ~r1_tarski(k1_relat_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3')), '#skF_3') | ~v1_relat_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'))), inference(resolution, [status(thm)], [c_1463, c_813])).
% 5.88/2.20  tff(c_1669, plain, (~v1_relat_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'))), inference(splitLeft, [status(thm)], [c_1496])).
% 5.88/2.20  tff(c_1719, plain, (~v1_relat_1(k7_relat_1('#skF_4', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_1716, c_1669])).
% 5.88/2.20  tff(c_1735, plain, (~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_22, c_1719])).
% 5.88/2.20  tff(c_1739, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_775, c_1735])).
% 5.88/2.20  tff(c_1741, plain, (v1_relat_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'))), inference(splitRight, [status(thm)], [c_1496])).
% 5.88/2.20  tff(c_1786, plain, (v1_relat_1(k7_relat_1('#skF_4', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_1783, c_1741])).
% 5.88/2.20  tff(c_20, plain, (![B_11, A_10]: (r1_tarski(k2_relat_1(B_11), A_10) | ~v5_relat_1(B_11, A_10) | ~v1_relat_1(B_11))), inference(cnfTransformation, [status(thm)], [f_53])).
% 5.88/2.20  tff(c_1740, plain, (~r1_tarski(k1_relat_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3')), '#skF_3') | ~r1_tarski(k2_relat_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3')), '#skF_2')), inference(splitRight, [status(thm)], [c_1496])).
% 5.88/2.20  tff(c_1882, plain, (~r1_tarski(k1_relat_1(k7_relat_1('#skF_4', '#skF_3')), '#skF_3') | ~r1_tarski(k2_relat_1(k7_relat_1('#skF_4', '#skF_3')), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1783, c_1783, c_1740])).
% 5.88/2.20  tff(c_1883, plain, (~r1_tarski(k2_relat_1(k7_relat_1('#skF_4', '#skF_3')), '#skF_2')), inference(splitLeft, [status(thm)], [c_1882])).
% 5.88/2.20  tff(c_1886, plain, (~v5_relat_1(k7_relat_1('#skF_4', '#skF_3'), '#skF_2') | ~v1_relat_1(k7_relat_1('#skF_4', '#skF_3'))), inference(resolution, [status(thm)], [c_20, c_1883])).
% 5.88/2.20  tff(c_1889, plain, (~v5_relat_1(k7_relat_1('#skF_4', '#skF_3'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1786, c_1886])).
% 5.88/2.20  tff(c_2230, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2219, c_1889])).
% 5.88/2.20  tff(c_2231, plain, (~r1_tarski(k1_relat_1(k7_relat_1('#skF_4', '#skF_3')), '#skF_3')), inference(splitRight, [status(thm)], [c_1882])).
% 5.88/2.20  tff(c_2241, plain, (~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_24, c_2231])).
% 5.88/2.20  tff(c_2245, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_775, c_2241])).
% 5.88/2.20  tff(c_2246, plain, (~v1_funct_2(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), '#skF_3', '#skF_2')), inference(splitRight, [status(thm)], [c_751])).
% 5.88/2.20  tff(c_3143, plain, (~v1_funct_2(k7_relat_1('#skF_4', '#skF_3'), '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_3131, c_2246])).
% 5.88/2.20  tff(c_2247, plain, (m1_subset_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(splitRight, [status(thm)], [c_751])).
% 5.88/2.20  tff(c_2833, plain, (k1_relset_1('#skF_3', '#skF_2', k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'))=k1_relat_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'))), inference(resolution, [status(thm)], [c_2247, c_2812])).
% 5.88/2.20  tff(c_3136, plain, (k1_relset_1('#skF_3', '#skF_2', k7_relat_1('#skF_4', '#skF_3'))=k1_relat_1(k7_relat_1('#skF_4', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_3131, c_3131, c_2833])).
% 5.88/2.20  tff(c_3142, plain, (m1_subset_1(k7_relat_1('#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_3131, c_2247])).
% 5.88/2.20  tff(c_3319, plain, (![B_483, C_484, A_485]: (k1_xboole_0=B_483 | v1_funct_2(C_484, A_485, B_483) | k1_relset_1(A_485, B_483, C_484)!=A_485 | ~m1_subset_1(C_484, k1_zfmisc_1(k2_zfmisc_1(A_485, B_483))))), inference(cnfTransformation, [status(thm)], [f_111])).
% 5.88/2.20  tff(c_3325, plain, (k1_xboole_0='#skF_2' | v1_funct_2(k7_relat_1('#skF_4', '#skF_3'), '#skF_3', '#skF_2') | k1_relset_1('#skF_3', '#skF_2', k7_relat_1('#skF_4', '#skF_3'))!='#skF_3'), inference(resolution, [status(thm)], [c_3142, c_3319])).
% 5.88/2.20  tff(c_3345, plain, (k1_xboole_0='#skF_2' | v1_funct_2(k7_relat_1('#skF_4', '#skF_3'), '#skF_3', '#skF_2') | k1_relat_1(k7_relat_1('#skF_4', '#skF_3'))!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_3136, c_3325])).
% 5.88/2.20  tff(c_3346, plain, (k1_relat_1(k7_relat_1('#skF_4', '#skF_3'))!='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_3143, c_74, c_3345])).
% 5.88/2.20  tff(c_3426, plain, (~r1_tarski('#skF_3', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_3420, c_3346])).
% 5.88/2.20  tff(c_3472, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_62, c_3426])).
% 5.88/2.20  tff(c_3473, plain, (k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_60])).
% 5.88/2.20  tff(c_6, plain, (![A_2]: (k2_zfmisc_1(A_2, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_35])).
% 5.88/2.20  tff(c_3487, plain, (![A_2]: (k2_zfmisc_1(A_2, '#skF_1')='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_3473, c_3473, c_6])).
% 5.88/2.20  tff(c_3474, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_60])).
% 5.88/2.20  tff(c_3479, plain, ('#skF_2'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_3473, c_3474])).
% 5.88/2.20  tff(c_3511, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_3487, c_3479, c_64])).
% 5.88/2.20  tff(c_3702, plain, (![A_522, B_523]: (r1_tarski(A_522, B_523) | ~m1_subset_1(A_522, k1_zfmisc_1(B_523)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 5.88/2.20  tff(c_3713, plain, (r1_tarski('#skF_4', '#skF_1')), inference(resolution, [status(thm)], [c_3511, c_3702])).
% 5.88/2.20  tff(c_2, plain, (![A_1]: (k1_xboole_0=A_1 | ~r1_tarski(A_1, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_29])).
% 5.88/2.20  tff(c_3512, plain, (![A_1]: (A_1='#skF_1' | ~r1_tarski(A_1, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_3473, c_3473, c_2])).
% 5.88/2.20  tff(c_3718, plain, ('#skF_1'='#skF_4'), inference(resolution, [status(thm)], [c_3713, c_3512])).
% 5.88/2.20  tff(c_3480, plain, (v1_funct_2('#skF_4', '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_3479, c_66])).
% 5.88/2.20  tff(c_3729, plain, (v1_funct_2('#skF_4', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_3718, c_3718, c_3480])).
% 5.88/2.20  tff(c_10, plain, (![A_4]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_4)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 5.88/2.20  tff(c_3485, plain, (![A_4]: (m1_subset_1('#skF_1', k1_zfmisc_1(A_4)))), inference(demodulation, [status(thm), theory('equality')], [c_3473, c_10])).
% 5.88/2.20  tff(c_3714, plain, (![A_4]: (r1_tarski('#skF_1', A_4))), inference(resolution, [status(thm)], [c_3485, c_3702])).
% 5.88/2.20  tff(c_4340, plain, (![A_4]: (r1_tarski('#skF_4', A_4))), inference(demodulation, [status(thm), theory('equality')], [c_3718, c_3714])).
% 5.88/2.20  tff(c_3541, plain, (![A_503, B_504]: (r1_tarski(A_503, B_504) | ~m1_subset_1(A_503, k1_zfmisc_1(B_504)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 5.88/2.20  tff(c_3552, plain, (r1_tarski('#skF_4', '#skF_1')), inference(resolution, [status(thm)], [c_3511, c_3541])).
% 5.88/2.20  tff(c_3557, plain, ('#skF_1'='#skF_4'), inference(resolution, [status(thm)], [c_3552, c_3512])).
% 5.88/2.20  tff(c_3531, plain, (![B_499, A_500]: (r1_tarski(k7_relat_1(B_499, A_500), B_499) | ~v1_relat_1(B_499))), inference(cnfTransformation, [status(thm)], [f_65])).
% 5.88/2.20  tff(c_3536, plain, (![A_500]: (k7_relat_1('#skF_1', A_500)='#skF_1' | ~v1_relat_1('#skF_1'))), inference(resolution, [status(thm)], [c_3531, c_3512])).
% 5.88/2.20  tff(c_3537, plain, (~v1_relat_1('#skF_1')), inference(splitLeft, [status(thm)], [c_3536])).
% 5.88/2.20  tff(c_3560, plain, (~v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_3557, c_3537])).
% 5.88/2.20  tff(c_3569, plain, (![A_4]: (m1_subset_1('#skF_4', k1_zfmisc_1(A_4)))), inference(demodulation, [status(thm), theory('equality')], [c_3557, c_3485])).
% 5.88/2.20  tff(c_3665, plain, (![C_516, A_517, B_518]: (v1_relat_1(C_516) | ~m1_subset_1(C_516, k1_zfmisc_1(k2_zfmisc_1(A_517, B_518))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 5.88/2.20  tff(c_3673, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_3569, c_3665])).
% 5.88/2.20  tff(c_3681, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3560, c_3673])).
% 5.88/2.20  tff(c_3682, plain, (![A_500]: (k7_relat_1('#skF_1', A_500)='#skF_1')), inference(splitRight, [status(thm)], [c_3536])).
% 5.88/2.20  tff(c_3720, plain, (![A_500]: (k7_relat_1('#skF_4', A_500)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_3718, c_3718, c_3682])).
% 5.88/2.20  tff(c_3730, plain, (![A_4]: (m1_subset_1('#skF_4', k1_zfmisc_1(A_4)))), inference(demodulation, [status(thm), theory('equality')], [c_3718, c_3485])).
% 5.88/2.20  tff(c_5319, plain, (![A_751, B_752, C_753, D_754]: (k2_partfun1(A_751, B_752, C_753, D_754)=k7_relat_1(C_753, D_754) | ~m1_subset_1(C_753, k1_zfmisc_1(k2_zfmisc_1(A_751, B_752))) | ~v1_funct_1(C_753))), inference(cnfTransformation, [status(thm)], [f_125])).
% 5.88/2.20  tff(c_5328, plain, (![A_751, B_752, D_754]: (k2_partfun1(A_751, B_752, '#skF_4', D_754)=k7_relat_1('#skF_4', D_754) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_3730, c_5319])).
% 5.88/2.20  tff(c_5335, plain, (![A_751, B_752, D_754]: (k2_partfun1(A_751, B_752, '#skF_4', D_754)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_3720, c_5328])).
% 5.88/2.20  tff(c_14, plain, (![A_5, B_6]: (m1_subset_1(A_5, k1_zfmisc_1(B_6)) | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_41])).
% 5.88/2.20  tff(c_8, plain, (![B_3]: (k2_zfmisc_1(k1_xboole_0, B_3)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_35])).
% 5.88/2.20  tff(c_3495, plain, (![B_3]: (k2_zfmisc_1('#skF_1', B_3)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_3473, c_3473, c_8])).
% 5.88/2.20  tff(c_3727, plain, (![B_3]: (k2_zfmisc_1('#skF_4', B_3)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_3718, c_3718, c_3495])).
% 5.88/2.20  tff(c_3731, plain, ('#skF_2'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_3718, c_3479])).
% 5.88/2.20  tff(c_3513, plain, (![A_495]: (A_495='#skF_1' | ~r1_tarski(A_495, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_3473, c_3473, c_2])).
% 5.88/2.20  tff(c_3517, plain, ('#skF_3'='#skF_1'), inference(resolution, [status(thm)], [c_62, c_3513])).
% 5.88/2.20  tff(c_3724, plain, ('#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_3718, c_3517])).
% 5.88/2.20  tff(c_4307, plain, (![A_607, B_608, C_609, D_610]: (v1_funct_1(k2_partfun1(A_607, B_608, C_609, D_610)) | ~m1_subset_1(C_609, k1_zfmisc_1(k2_zfmisc_1(A_607, B_608))) | ~v1_funct_1(C_609))), inference(cnfTransformation, [status(thm)], [f_119])).
% 5.88/2.20  tff(c_4310, plain, (![A_607, B_608, D_610]: (v1_funct_1(k2_partfun1(A_607, B_608, '#skF_4', D_610)) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_3730, c_4307])).
% 5.88/2.20  tff(c_4320, plain, (![A_607, B_608, D_610]: (v1_funct_1(k2_partfun1(A_607, B_608, '#skF_4', D_610)))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_4310])).
% 5.88/2.20  tff(c_3737, plain, (~m1_subset_1(k2_partfun1('#skF_4', '#skF_2', '#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2'))) | ~v1_funct_2(k2_partfun1('#skF_4', '#skF_2', '#skF_4', '#skF_3'), '#skF_3', '#skF_2') | ~v1_funct_1(k2_partfun1('#skF_4', '#skF_2', '#skF_4', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_3718, c_3718, c_3718, c_58])).
% 5.88/2.20  tff(c_3738, plain, (~v1_funct_1(k2_partfun1('#skF_4', '#skF_2', '#skF_4', '#skF_3'))), inference(splitLeft, [status(thm)], [c_3737])).
% 5.88/2.20  tff(c_3856, plain, (~v1_funct_1(k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_3731, c_3724, c_3738])).
% 5.88/2.20  tff(c_4324, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4320, c_3856])).
% 5.88/2.20  tff(c_4325, plain, (~v1_funct_2(k2_partfun1('#skF_4', '#skF_2', '#skF_4', '#skF_3'), '#skF_3', '#skF_2') | ~m1_subset_1(k2_partfun1('#skF_4', '#skF_2', '#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(splitRight, [status(thm)], [c_3737])).
% 5.88/2.20  tff(c_4550, plain, (~v1_funct_2(k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_4'), '#skF_4', '#skF_4') | ~m1_subset_1(k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_4'), k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_3727, c_3731, c_3731, c_3724, c_3724, c_3731, c_3731, c_3724, c_3724, c_4325])).
% 5.88/2.20  tff(c_4551, plain, (~m1_subset_1(k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_4'), k1_zfmisc_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_4550])).
% 5.88/2.20  tff(c_4634, plain, (~r1_tarski(k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_4'), '#skF_4')), inference(resolution, [status(thm)], [c_14, c_4551])).
% 5.88/2.20  tff(c_5338, plain, (~r1_tarski('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_5335, c_4634])).
% 5.88/2.20  tff(c_5343, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4340, c_5338])).
% 5.88/2.20  tff(c_5345, plain, (m1_subset_1(k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_4'), k1_zfmisc_1('#skF_4'))), inference(splitRight, [status(thm)], [c_4550])).
% 5.88/2.20  tff(c_12, plain, (![A_5, B_6]: (r1_tarski(A_5, B_6) | ~m1_subset_1(A_5, k1_zfmisc_1(B_6)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 5.88/2.20  tff(c_5435, plain, (r1_tarski(k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_4'), '#skF_4')), inference(resolution, [status(thm)], [c_5345, c_12])).
% 5.88/2.20  tff(c_3725, plain, (![A_1]: (A_1='#skF_4' | ~r1_tarski(A_1, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_3718, c_3718, c_3512])).
% 5.88/2.20  tff(c_5444, plain, (k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_4')='#skF_4'), inference(resolution, [status(thm)], [c_5435, c_3725])).
% 5.88/2.20  tff(c_5344, plain, (~v1_funct_2(k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_4'), '#skF_4', '#skF_4')), inference(splitRight, [status(thm)], [c_4550])).
% 5.88/2.20  tff(c_5448, plain, (~v1_funct_2('#skF_4', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_5444, c_5344])).
% 5.88/2.20  tff(c_5455, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3729, c_5448])).
% 5.88/2.20  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.88/2.20  
% 5.88/2.20  Inference rules
% 5.88/2.20  ----------------------
% 5.88/2.20  #Ref     : 0
% 5.88/2.20  #Sup     : 1114
% 5.88/2.20  #Fact    : 0
% 5.88/2.20  #Define  : 0
% 5.88/2.20  #Split   : 15
% 5.88/2.20  #Chain   : 0
% 5.88/2.20  #Close   : 0
% 5.88/2.20  
% 5.88/2.20  Ordering : KBO
% 5.88/2.20  
% 5.88/2.20  Simplification rules
% 5.88/2.20  ----------------------
% 5.88/2.20  #Subsume      : 132
% 5.88/2.20  #Demod        : 896
% 5.88/2.20  #Tautology    : 490
% 5.88/2.20  #SimpNegUnit  : 10
% 5.88/2.20  #BackRed      : 67
% 5.88/2.20  
% 5.88/2.20  #Partial instantiations: 0
% 5.88/2.20  #Strategies tried      : 1
% 5.88/2.20  
% 5.88/2.20  Timing (in seconds)
% 5.88/2.20  ----------------------
% 5.88/2.20  Preprocessing        : 0.37
% 5.88/2.20  Parsing              : 0.20
% 5.88/2.20  CNF conversion       : 0.02
% 5.88/2.20  Main loop            : 0.99
% 5.88/2.20  Inferencing          : 0.38
% 5.88/2.20  Reduction            : 0.31
% 5.88/2.20  Demodulation         : 0.21
% 5.88/2.20  BG Simplification    : 0.04
% 5.88/2.20  Subsumption          : 0.16
% 5.88/2.20  Abstraction          : 0.04
% 5.88/2.20  MUC search           : 0.00
% 5.88/2.20  Cooper               : 0.00
% 5.88/2.20  Total                : 1.41
% 5.88/2.20  Index Insertion      : 0.00
% 5.88/2.20  Index Deletion       : 0.00
% 5.88/2.20  Index Matching       : 0.00
% 5.88/2.20  BG Taut test         : 0.00
%------------------------------------------------------------------------------
