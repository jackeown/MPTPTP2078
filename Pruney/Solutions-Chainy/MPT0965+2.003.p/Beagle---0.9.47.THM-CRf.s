%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:11:00 EST 2020

% Result     : Theorem 4.19s
% Output     : CNFRefutation 4.19s
% Verified   : 
% Statistics : Number of formulae       :   90 ( 135 expanded)
%              Number of leaves         :   36 (  63 expanded)
%              Depth                    :   11
%              Number of atoms          :  137 ( 299 expanded)
%              Number of equality atoms :   32 (  60 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

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

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

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

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_121,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( r2_hidden(C,A)
         => ( B = k1_xboole_0
            | r2_hidden(k1_funct_1(D,C),B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_funct_2)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_86,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_108,axiom,(
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

tff(f_72,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_68,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r2_hidden(A,k1_relat_1(B))
       => r2_hidden(k1_funct_1(B,A),k2_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_funct_1)).

tff(f_90,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_82,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k2_relset_1(A,B,C),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_relset_1)).

tff(f_47,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

tff(f_37,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(f_54,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

tff(c_50,plain,(
    r2_hidden('#skF_4','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_57,plain,(
    ! [B_37,A_38] :
      ( ~ r2_hidden(B_37,A_38)
      | ~ v1_xboole_0(A_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_61,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_50,c_57])).

tff(c_48,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_54,plain,(
    v1_funct_2('#skF_5','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_52,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_1875,plain,(
    ! [A_363,B_364,C_365] :
      ( k1_relset_1(A_363,B_364,C_365) = k1_relat_1(C_365)
      | ~ m1_subset_1(C_365,k1_zfmisc_1(k2_zfmisc_1(A_363,B_364))) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_1889,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_52,c_1875])).

tff(c_2429,plain,(
    ! [B_454,A_455,C_456] :
      ( k1_xboole_0 = B_454
      | k1_relset_1(A_455,B_454,C_456) = A_455
      | ~ v1_funct_2(C_456,A_455,B_454)
      | ~ m1_subset_1(C_456,k1_zfmisc_1(k2_zfmisc_1(A_455,B_454))) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_2444,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relset_1('#skF_2','#skF_3','#skF_5') = '#skF_2'
    | ~ v1_funct_2('#skF_5','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_52,c_2429])).

tff(c_2450,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relat_1('#skF_5') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_1889,c_2444])).

tff(c_2451,plain,(
    k1_relat_1('#skF_5') = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_2450])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_77,plain,(
    ! [C_44,A_45,B_46] :
      ( v1_relat_1(C_44)
      | ~ m1_subset_1(C_44,k1_zfmisc_1(k2_zfmisc_1(A_45,B_46))) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_86,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_52,c_77])).

tff(c_56,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_2207,plain,(
    ! [B_417,A_418] :
      ( r2_hidden(k1_funct_1(B_417,A_418),k2_relat_1(B_417))
      | ~ r2_hidden(A_418,k1_relat_1(B_417))
      | ~ v1_funct_1(B_417)
      | ~ v1_relat_1(B_417) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_264,plain,(
    ! [A_96,B_97,C_98] :
      ( k1_relset_1(A_96,B_97,C_98) = k1_relat_1(C_98)
      | ~ m1_subset_1(C_98,k1_zfmisc_1(k2_zfmisc_1(A_96,B_97))) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_278,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_52,c_264])).

tff(c_1679,plain,(
    ! [B_323,A_324,C_325] :
      ( k1_xboole_0 = B_323
      | k1_relset_1(A_324,B_323,C_325) = A_324
      | ~ v1_funct_2(C_325,A_324,B_323)
      | ~ m1_subset_1(C_325,k1_zfmisc_1(k2_zfmisc_1(A_324,B_323))) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_1698,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relset_1('#skF_2','#skF_3','#skF_5') = '#skF_2'
    | ~ v1_funct_2('#skF_5','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_52,c_1679])).

tff(c_1705,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relat_1('#skF_5') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_278,c_1698])).

tff(c_1706,plain,(
    k1_relat_1('#skF_5') = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_1705])).

tff(c_664,plain,(
    ! [B_150,A_151] :
      ( r2_hidden(k1_funct_1(B_150,A_151),k2_relat_1(B_150))
      | ~ r2_hidden(A_151,k1_relat_1(B_150))
      | ~ v1_funct_1(B_150)
      | ~ v1_relat_1(B_150) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_202,plain,(
    ! [A_84,B_85,C_86] :
      ( k2_relset_1(A_84,B_85,C_86) = k2_relat_1(C_86)
      | ~ m1_subset_1(C_86,k1_zfmisc_1(k2_zfmisc_1(A_84,B_85))) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_211,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_52,c_202])).

tff(c_304,plain,(
    ! [A_102,B_103,C_104] :
      ( m1_subset_1(k2_relset_1(A_102,B_103,C_104),k1_zfmisc_1(B_103))
      | ~ m1_subset_1(C_104,k1_zfmisc_1(k2_zfmisc_1(A_102,B_103))) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_334,plain,
    ( m1_subset_1(k2_relat_1('#skF_5'),k1_zfmisc_1('#skF_3'))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_211,c_304])).

tff(c_344,plain,(
    m1_subset_1(k2_relat_1('#skF_5'),k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_334])).

tff(c_12,plain,(
    ! [A_9,C_11,B_10] :
      ( m1_subset_1(A_9,C_11)
      | ~ m1_subset_1(B_10,k1_zfmisc_1(C_11))
      | ~ r2_hidden(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_352,plain,(
    ! [A_9] :
      ( m1_subset_1(A_9,'#skF_3')
      | ~ r2_hidden(A_9,k2_relat_1('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_344,c_12])).

tff(c_668,plain,(
    ! [A_151] :
      ( m1_subset_1(k1_funct_1('#skF_5',A_151),'#skF_3')
      | ~ r2_hidden(A_151,k1_relat_1('#skF_5'))
      | ~ v1_funct_1('#skF_5')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_664,c_352])).

tff(c_678,plain,(
    ! [A_151] :
      ( m1_subset_1(k1_funct_1('#skF_5',A_151),'#skF_3')
      | ~ r2_hidden(A_151,k1_relat_1('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_56,c_668])).

tff(c_1736,plain,(
    ! [A_327] :
      ( m1_subset_1(k1_funct_1('#skF_5',A_327),'#skF_3')
      | ~ r2_hidden(A_327,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1706,c_678])).

tff(c_93,plain,(
    ! [A_50,B_51] :
      ( r2_hidden(A_50,B_51)
      | v1_xboole_0(B_51)
      | ~ m1_subset_1(A_50,B_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_46,plain,(
    ~ r2_hidden(k1_funct_1('#skF_5','#skF_4'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_101,plain,
    ( v1_xboole_0('#skF_3')
    | ~ m1_subset_1(k1_funct_1('#skF_5','#skF_4'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_93,c_46])).

tff(c_102,plain,(
    ~ m1_subset_1(k1_funct_1('#skF_5','#skF_4'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_101])).

tff(c_1739,plain,(
    ~ r2_hidden('#skF_4','#skF_2') ),
    inference(resolution,[status(thm)],[c_1736,c_102])).

tff(c_1743,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_1739])).

tff(c_1744,plain,(
    v1_xboole_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_101])).

tff(c_1915,plain,(
    ! [A_371,B_372,C_373] :
      ( k2_relset_1(A_371,B_372,C_373) = k2_relat_1(C_373)
      | ~ m1_subset_1(C_373,k1_zfmisc_1(k2_zfmisc_1(A_371,B_372))) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_1929,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_52,c_1915])).

tff(c_2013,plain,(
    ! [A_398,B_399,C_400] :
      ( m1_subset_1(k2_relset_1(A_398,B_399,C_400),k1_zfmisc_1(B_399))
      | ~ m1_subset_1(C_400,k1_zfmisc_1(k2_zfmisc_1(A_398,B_399))) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_2043,plain,
    ( m1_subset_1(k2_relat_1('#skF_5'),k1_zfmisc_1('#skF_3'))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_1929,c_2013])).

tff(c_2053,plain,(
    m1_subset_1(k2_relat_1('#skF_5'),k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_2043])).

tff(c_14,plain,(
    ! [C_14,B_13,A_12] :
      ( ~ v1_xboole_0(C_14)
      | ~ m1_subset_1(B_13,k1_zfmisc_1(C_14))
      | ~ r2_hidden(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_2057,plain,(
    ! [A_12] :
      ( ~ v1_xboole_0('#skF_3')
      | ~ r2_hidden(A_12,k2_relat_1('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_2053,c_14])).

tff(c_2064,plain,(
    ! [A_12] : ~ r2_hidden(A_12,k2_relat_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1744,c_2057])).

tff(c_2211,plain,(
    ! [A_418] :
      ( ~ r2_hidden(A_418,k1_relat_1('#skF_5'))
      | ~ v1_funct_1('#skF_5')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_2207,c_2064])).

tff(c_2225,plain,(
    ! [A_419] : ~ r2_hidden(A_419,k1_relat_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_56,c_2211])).

tff(c_2235,plain,(
    v1_xboole_0(k1_relat_1('#skF_5')) ),
    inference(resolution,[status(thm)],[c_4,c_2225])).

tff(c_2452,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2451,c_2235])).

tff(c_2456,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_61,c_2452])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:22:04 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.19/1.71  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.19/1.71  
% 4.19/1.71  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.19/1.71  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4
% 4.19/1.71  
% 4.19/1.71  %Foreground sorts:
% 4.19/1.71  
% 4.19/1.71  
% 4.19/1.71  %Background operators:
% 4.19/1.71  
% 4.19/1.71  
% 4.19/1.71  %Foreground operators:
% 4.19/1.71  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 4.19/1.71  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.19/1.71  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.19/1.71  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.19/1.71  tff('#skF_1', type, '#skF_1': $i > $i).
% 4.19/1.71  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.19/1.71  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.19/1.71  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 4.19/1.71  tff('#skF_5', type, '#skF_5': $i).
% 4.19/1.71  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.19/1.71  tff('#skF_2', type, '#skF_2': $i).
% 4.19/1.71  tff('#skF_3', type, '#skF_3': $i).
% 4.19/1.71  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 4.19/1.71  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 4.19/1.71  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.19/1.71  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 4.19/1.71  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.19/1.71  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.19/1.71  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.19/1.71  tff('#skF_4', type, '#skF_4': $i).
% 4.19/1.71  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.19/1.71  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 4.19/1.71  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.19/1.71  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.19/1.71  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.19/1.71  
% 4.19/1.73  tff(f_121, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_hidden(C, A) => ((B = k1_xboole_0) | r2_hidden(k1_funct_1(D, C), B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_funct_2)).
% 4.19/1.73  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 4.19/1.73  tff(f_86, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 4.19/1.73  tff(f_108, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 4.19/1.73  tff(f_72, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 4.19/1.73  tff(f_68, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r2_hidden(A, k1_relat_1(B)) => r2_hidden(k1_funct_1(B, A), k2_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_funct_1)).
% 4.19/1.73  tff(f_90, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 4.19/1.73  tff(f_82, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k2_relset_1(A, B, C), k1_zfmisc_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_relset_1)).
% 4.19/1.73  tff(f_47, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset)).
% 4.19/1.73  tff(f_37, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 4.19/1.73  tff(f_54, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_subset)).
% 4.19/1.73  tff(c_50, plain, (r2_hidden('#skF_4', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_121])).
% 4.19/1.73  tff(c_57, plain, (![B_37, A_38]: (~r2_hidden(B_37, A_38) | ~v1_xboole_0(A_38))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.19/1.73  tff(c_61, plain, (~v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_50, c_57])).
% 4.19/1.73  tff(c_48, plain, (k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_121])).
% 4.19/1.73  tff(c_54, plain, (v1_funct_2('#skF_5', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_121])).
% 4.19/1.73  tff(c_52, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_121])).
% 4.19/1.73  tff(c_1875, plain, (![A_363, B_364, C_365]: (k1_relset_1(A_363, B_364, C_365)=k1_relat_1(C_365) | ~m1_subset_1(C_365, k1_zfmisc_1(k2_zfmisc_1(A_363, B_364))))), inference(cnfTransformation, [status(thm)], [f_86])).
% 4.19/1.73  tff(c_1889, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_52, c_1875])).
% 4.19/1.73  tff(c_2429, plain, (![B_454, A_455, C_456]: (k1_xboole_0=B_454 | k1_relset_1(A_455, B_454, C_456)=A_455 | ~v1_funct_2(C_456, A_455, B_454) | ~m1_subset_1(C_456, k1_zfmisc_1(k2_zfmisc_1(A_455, B_454))))), inference(cnfTransformation, [status(thm)], [f_108])).
% 4.19/1.73  tff(c_2444, plain, (k1_xboole_0='#skF_3' | k1_relset_1('#skF_2', '#skF_3', '#skF_5')='#skF_2' | ~v1_funct_2('#skF_5', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_52, c_2429])).
% 4.19/1.73  tff(c_2450, plain, (k1_xboole_0='#skF_3' | k1_relat_1('#skF_5')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_54, c_1889, c_2444])).
% 4.19/1.73  tff(c_2451, plain, (k1_relat_1('#skF_5')='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_48, c_2450])).
% 4.19/1.73  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.19/1.73  tff(c_77, plain, (![C_44, A_45, B_46]: (v1_relat_1(C_44) | ~m1_subset_1(C_44, k1_zfmisc_1(k2_zfmisc_1(A_45, B_46))))), inference(cnfTransformation, [status(thm)], [f_72])).
% 4.19/1.73  tff(c_86, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_52, c_77])).
% 4.19/1.73  tff(c_56, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_121])).
% 4.19/1.73  tff(c_2207, plain, (![B_417, A_418]: (r2_hidden(k1_funct_1(B_417, A_418), k2_relat_1(B_417)) | ~r2_hidden(A_418, k1_relat_1(B_417)) | ~v1_funct_1(B_417) | ~v1_relat_1(B_417))), inference(cnfTransformation, [status(thm)], [f_68])).
% 4.19/1.73  tff(c_264, plain, (![A_96, B_97, C_98]: (k1_relset_1(A_96, B_97, C_98)=k1_relat_1(C_98) | ~m1_subset_1(C_98, k1_zfmisc_1(k2_zfmisc_1(A_96, B_97))))), inference(cnfTransformation, [status(thm)], [f_86])).
% 4.19/1.73  tff(c_278, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_52, c_264])).
% 4.19/1.73  tff(c_1679, plain, (![B_323, A_324, C_325]: (k1_xboole_0=B_323 | k1_relset_1(A_324, B_323, C_325)=A_324 | ~v1_funct_2(C_325, A_324, B_323) | ~m1_subset_1(C_325, k1_zfmisc_1(k2_zfmisc_1(A_324, B_323))))), inference(cnfTransformation, [status(thm)], [f_108])).
% 4.19/1.73  tff(c_1698, plain, (k1_xboole_0='#skF_3' | k1_relset_1('#skF_2', '#skF_3', '#skF_5')='#skF_2' | ~v1_funct_2('#skF_5', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_52, c_1679])).
% 4.19/1.73  tff(c_1705, plain, (k1_xboole_0='#skF_3' | k1_relat_1('#skF_5')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_54, c_278, c_1698])).
% 4.19/1.73  tff(c_1706, plain, (k1_relat_1('#skF_5')='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_48, c_1705])).
% 4.19/1.73  tff(c_664, plain, (![B_150, A_151]: (r2_hidden(k1_funct_1(B_150, A_151), k2_relat_1(B_150)) | ~r2_hidden(A_151, k1_relat_1(B_150)) | ~v1_funct_1(B_150) | ~v1_relat_1(B_150))), inference(cnfTransformation, [status(thm)], [f_68])).
% 4.19/1.73  tff(c_202, plain, (![A_84, B_85, C_86]: (k2_relset_1(A_84, B_85, C_86)=k2_relat_1(C_86) | ~m1_subset_1(C_86, k1_zfmisc_1(k2_zfmisc_1(A_84, B_85))))), inference(cnfTransformation, [status(thm)], [f_90])).
% 4.19/1.73  tff(c_211, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_52, c_202])).
% 4.19/1.73  tff(c_304, plain, (![A_102, B_103, C_104]: (m1_subset_1(k2_relset_1(A_102, B_103, C_104), k1_zfmisc_1(B_103)) | ~m1_subset_1(C_104, k1_zfmisc_1(k2_zfmisc_1(A_102, B_103))))), inference(cnfTransformation, [status(thm)], [f_82])).
% 4.19/1.73  tff(c_334, plain, (m1_subset_1(k2_relat_1('#skF_5'), k1_zfmisc_1('#skF_3')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_211, c_304])).
% 4.19/1.73  tff(c_344, plain, (m1_subset_1(k2_relat_1('#skF_5'), k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_334])).
% 4.19/1.73  tff(c_12, plain, (![A_9, C_11, B_10]: (m1_subset_1(A_9, C_11) | ~m1_subset_1(B_10, k1_zfmisc_1(C_11)) | ~r2_hidden(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_47])).
% 4.19/1.73  tff(c_352, plain, (![A_9]: (m1_subset_1(A_9, '#skF_3') | ~r2_hidden(A_9, k2_relat_1('#skF_5')))), inference(resolution, [status(thm)], [c_344, c_12])).
% 4.19/1.73  tff(c_668, plain, (![A_151]: (m1_subset_1(k1_funct_1('#skF_5', A_151), '#skF_3') | ~r2_hidden(A_151, k1_relat_1('#skF_5')) | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5'))), inference(resolution, [status(thm)], [c_664, c_352])).
% 4.19/1.73  tff(c_678, plain, (![A_151]: (m1_subset_1(k1_funct_1('#skF_5', A_151), '#skF_3') | ~r2_hidden(A_151, k1_relat_1('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_86, c_56, c_668])).
% 4.19/1.73  tff(c_1736, plain, (![A_327]: (m1_subset_1(k1_funct_1('#skF_5', A_327), '#skF_3') | ~r2_hidden(A_327, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_1706, c_678])).
% 4.19/1.73  tff(c_93, plain, (![A_50, B_51]: (r2_hidden(A_50, B_51) | v1_xboole_0(B_51) | ~m1_subset_1(A_50, B_51))), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.19/1.73  tff(c_46, plain, (~r2_hidden(k1_funct_1('#skF_5', '#skF_4'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_121])).
% 4.19/1.73  tff(c_101, plain, (v1_xboole_0('#skF_3') | ~m1_subset_1(k1_funct_1('#skF_5', '#skF_4'), '#skF_3')), inference(resolution, [status(thm)], [c_93, c_46])).
% 4.19/1.73  tff(c_102, plain, (~m1_subset_1(k1_funct_1('#skF_5', '#skF_4'), '#skF_3')), inference(splitLeft, [status(thm)], [c_101])).
% 4.19/1.73  tff(c_1739, plain, (~r2_hidden('#skF_4', '#skF_2')), inference(resolution, [status(thm)], [c_1736, c_102])).
% 4.19/1.73  tff(c_1743, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_50, c_1739])).
% 4.19/1.73  tff(c_1744, plain, (v1_xboole_0('#skF_3')), inference(splitRight, [status(thm)], [c_101])).
% 4.19/1.73  tff(c_1915, plain, (![A_371, B_372, C_373]: (k2_relset_1(A_371, B_372, C_373)=k2_relat_1(C_373) | ~m1_subset_1(C_373, k1_zfmisc_1(k2_zfmisc_1(A_371, B_372))))), inference(cnfTransformation, [status(thm)], [f_90])).
% 4.19/1.73  tff(c_1929, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_52, c_1915])).
% 4.19/1.73  tff(c_2013, plain, (![A_398, B_399, C_400]: (m1_subset_1(k2_relset_1(A_398, B_399, C_400), k1_zfmisc_1(B_399)) | ~m1_subset_1(C_400, k1_zfmisc_1(k2_zfmisc_1(A_398, B_399))))), inference(cnfTransformation, [status(thm)], [f_82])).
% 4.19/1.73  tff(c_2043, plain, (m1_subset_1(k2_relat_1('#skF_5'), k1_zfmisc_1('#skF_3')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_1929, c_2013])).
% 4.19/1.73  tff(c_2053, plain, (m1_subset_1(k2_relat_1('#skF_5'), k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_2043])).
% 4.19/1.73  tff(c_14, plain, (![C_14, B_13, A_12]: (~v1_xboole_0(C_14) | ~m1_subset_1(B_13, k1_zfmisc_1(C_14)) | ~r2_hidden(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_54])).
% 4.19/1.73  tff(c_2057, plain, (![A_12]: (~v1_xboole_0('#skF_3') | ~r2_hidden(A_12, k2_relat_1('#skF_5')))), inference(resolution, [status(thm)], [c_2053, c_14])).
% 4.19/1.73  tff(c_2064, plain, (![A_12]: (~r2_hidden(A_12, k2_relat_1('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_1744, c_2057])).
% 4.19/1.73  tff(c_2211, plain, (![A_418]: (~r2_hidden(A_418, k1_relat_1('#skF_5')) | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5'))), inference(resolution, [status(thm)], [c_2207, c_2064])).
% 4.19/1.73  tff(c_2225, plain, (![A_419]: (~r2_hidden(A_419, k1_relat_1('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_86, c_56, c_2211])).
% 4.19/1.73  tff(c_2235, plain, (v1_xboole_0(k1_relat_1('#skF_5'))), inference(resolution, [status(thm)], [c_4, c_2225])).
% 4.19/1.73  tff(c_2452, plain, (v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2451, c_2235])).
% 4.19/1.73  tff(c_2456, plain, $false, inference(negUnitSimplification, [status(thm)], [c_61, c_2452])).
% 4.19/1.73  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.19/1.73  
% 4.19/1.73  Inference rules
% 4.19/1.73  ----------------------
% 4.19/1.73  #Ref     : 0
% 4.19/1.73  #Sup     : 475
% 4.19/1.73  #Fact    : 0
% 4.19/1.73  #Define  : 0
% 4.19/1.73  #Split   : 13
% 4.19/1.73  #Chain   : 0
% 4.19/1.73  #Close   : 0
% 4.19/1.73  
% 4.19/1.73  Ordering : KBO
% 4.19/1.73  
% 4.19/1.73  Simplification rules
% 4.19/1.73  ----------------------
% 4.19/1.73  #Subsume      : 45
% 4.19/1.73  #Demod        : 115
% 4.19/1.73  #Tautology    : 54
% 4.19/1.73  #SimpNegUnit  : 18
% 4.19/1.73  #BackRed      : 15
% 4.19/1.73  
% 4.19/1.73  #Partial instantiations: 0
% 4.19/1.73  #Strategies tried      : 1
% 4.19/1.73  
% 4.19/1.73  Timing (in seconds)
% 4.19/1.73  ----------------------
% 4.40/1.73  Preprocessing        : 0.32
% 4.40/1.73  Parsing              : 0.17
% 4.40/1.73  CNF conversion       : 0.02
% 4.40/1.73  Main loop            : 0.65
% 4.40/1.73  Inferencing          : 0.26
% 4.40/1.73  Reduction            : 0.17
% 4.40/1.73  Demodulation         : 0.11
% 4.40/1.73  BG Simplification    : 0.03
% 4.40/1.73  Subsumption          : 0.12
% 4.40/1.73  Abstraction          : 0.03
% 4.40/1.73  MUC search           : 0.00
% 4.40/1.73  Cooper               : 0.00
% 4.40/1.73  Total                : 1.00
% 4.40/1.73  Index Insertion      : 0.00
% 4.40/1.73  Index Deletion       : 0.00
% 4.40/1.73  Index Matching       : 0.00
% 4.40/1.73  BG Taut test         : 0.00
%------------------------------------------------------------------------------
