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
% DateTime   : Thu Dec  3 10:10:49 EST 2020

% Result     : Theorem 5.25s
% Output     : CNFRefutation 5.57s
% Verified   : 
% Statistics : Number of formulae       :  106 ( 584 expanded)
%              Number of leaves         :   30 ( 202 expanded)
%              Depth                    :   13
%              Number of atoms          :  186 (1442 expanded)
%              Number of equality atoms :   64 ( 664 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k9_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff(v2_funct_1,type,(
    v2_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

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

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_105,negated_conjecture,(
    ~ ! [A] :
        ( ( v1_relat_1(A)
          & v1_funct_1(A) )
       => ( v1_funct_1(A)
          & v1_funct_2(A,k1_relat_1(A),k2_relat_1(A))
          & m1_subset_1(A,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A)))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_funct_2)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_76,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( ( r1_tarski(k1_relat_1(C),A)
          & r1_tarski(k2_relat_1(C),B) )
       => m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_relset_1)).

tff(f_68,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_48,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ( k1_relat_1(A) = k1_xboole_0
          | k2_relat_1(A) = k1_xboole_0 )
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).

tff(f_94,axiom,(
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

tff(f_52,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_56,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v2_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_funct_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_64,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k1_relset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_relset_1)).

tff(c_52,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_4580,plain,(
    ! [A_419,B_420] :
      ( r2_hidden('#skF_1'(A_419,B_420),A_419)
      | r1_tarski(A_419,B_420) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_4585,plain,(
    ! [A_419] : r1_tarski(A_419,A_419) ),
    inference(resolution,[status(thm)],[c_4580,c_4])).

tff(c_4638,plain,(
    ! [C_444,A_445,B_446] :
      ( m1_subset_1(C_444,k1_zfmisc_1(k2_zfmisc_1(A_445,B_446)))
      | ~ r1_tarski(k2_relat_1(C_444),B_446)
      | ~ r1_tarski(k1_relat_1(C_444),A_445)
      | ~ v1_relat_1(C_444) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_191,plain,(
    ! [A_40,B_41] :
      ( r2_hidden('#skF_1'(A_40,B_41),A_40)
      | r1_tarski(A_40,B_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_196,plain,(
    ! [A_40] : r1_tarski(A_40,A_40) ),
    inference(resolution,[status(thm)],[c_191,c_4])).

tff(c_514,plain,(
    ! [C_111,A_112,B_113] :
      ( m1_subset_1(C_111,k1_zfmisc_1(k2_zfmisc_1(A_112,B_113)))
      | ~ r1_tarski(k2_relat_1(C_111),B_113)
      | ~ r1_tarski(k1_relat_1(C_111),A_112)
      | ~ v1_relat_1(C_111) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_32,plain,(
    ! [A_17,B_18,C_19] :
      ( k1_relset_1(A_17,B_18,C_19) = k1_relat_1(C_19)
      | ~ m1_subset_1(C_19,k1_zfmisc_1(k2_zfmisc_1(A_17,B_18))) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_754,plain,(
    ! [A_144,B_145,C_146] :
      ( k1_relset_1(A_144,B_145,C_146) = k1_relat_1(C_146)
      | ~ r1_tarski(k2_relat_1(C_146),B_145)
      | ~ r1_tarski(k1_relat_1(C_146),A_144)
      | ~ v1_relat_1(C_146) ) ),
    inference(resolution,[status(thm)],[c_514,c_32])).

tff(c_876,plain,(
    ! [A_159,C_160] :
      ( k1_relset_1(A_159,k2_relat_1(C_160),C_160) = k1_relat_1(C_160)
      | ~ r1_tarski(k1_relat_1(C_160),A_159)
      | ~ v1_relat_1(C_160) ) ),
    inference(resolution,[status(thm)],[c_196,c_754])).

tff(c_882,plain,(
    ! [C_160] :
      ( k1_relset_1(k1_relat_1(C_160),k2_relat_1(C_160),C_160) = k1_relat_1(C_160)
      | ~ v1_relat_1(C_160) ) ),
    inference(resolution,[status(thm)],[c_196,c_876])).

tff(c_109,plain,(
    ! [A_33] :
      ( k2_relat_1(A_33) != k1_xboole_0
      | k1_xboole_0 = A_33
      | ~ v1_relat_1(A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_118,plain,
    ( k2_relat_1('#skF_2') != k1_xboole_0
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_52,c_109])).

tff(c_176,plain,(
    k2_relat_1('#skF_2') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_118])).

tff(c_34,plain,(
    ! [C_22,A_20,B_21] :
      ( m1_subset_1(C_22,k1_zfmisc_1(k2_zfmisc_1(A_20,B_21)))
      | ~ r1_tarski(k2_relat_1(C_22),B_21)
      | ~ r1_tarski(k1_relat_1(C_22),A_20)
      | ~ v1_relat_1(C_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_651,plain,(
    ! [B_128,C_129,A_130] :
      ( k1_xboole_0 = B_128
      | v1_funct_2(C_129,A_130,B_128)
      | k1_relset_1(A_130,B_128,C_129) != A_130
      | ~ m1_subset_1(C_129,k1_zfmisc_1(k2_zfmisc_1(A_130,B_128))) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_1972,plain,(
    ! [B_235,C_236,A_237] :
      ( k1_xboole_0 = B_235
      | v1_funct_2(C_236,A_237,B_235)
      | k1_relset_1(A_237,B_235,C_236) != A_237
      | ~ r1_tarski(k2_relat_1(C_236),B_235)
      | ~ r1_tarski(k1_relat_1(C_236),A_237)
      | ~ v1_relat_1(C_236) ) ),
    inference(resolution,[status(thm)],[c_34,c_651])).

tff(c_4061,plain,(
    ! [C_336,A_337] :
      ( k2_relat_1(C_336) = k1_xboole_0
      | v1_funct_2(C_336,A_337,k2_relat_1(C_336))
      | k1_relset_1(A_337,k2_relat_1(C_336),C_336) != A_337
      | ~ r1_tarski(k1_relat_1(C_336),A_337)
      | ~ v1_relat_1(C_336) ) ),
    inference(resolution,[status(thm)],[c_196,c_1972])).

tff(c_50,plain,(
    v1_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_48,plain,
    ( ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_2'),k2_relat_1('#skF_2'))))
    | ~ v1_funct_2('#skF_2',k1_relat_1('#skF_2'),k2_relat_1('#skF_2'))
    | ~ v1_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_54,plain,
    ( ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_2'),k2_relat_1('#skF_2'))))
    | ~ v1_funct_2('#skF_2',k1_relat_1('#skF_2'),k2_relat_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48])).

tff(c_108,plain,(
    ~ v1_funct_2('#skF_2',k1_relat_1('#skF_2'),k2_relat_1('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_54])).

tff(c_4073,plain,
    ( k2_relat_1('#skF_2') = k1_xboole_0
    | k1_relset_1(k1_relat_1('#skF_2'),k2_relat_1('#skF_2'),'#skF_2') != k1_relat_1('#skF_2')
    | ~ r1_tarski(k1_relat_1('#skF_2'),k1_relat_1('#skF_2'))
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_4061,c_108])).

tff(c_4086,plain,
    ( k2_relat_1('#skF_2') = k1_xboole_0
    | k1_relset_1(k1_relat_1('#skF_2'),k2_relat_1('#skF_2'),'#skF_2') != k1_relat_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_196,c_4073])).

tff(c_4087,plain,(
    k1_relset_1(k1_relat_1('#skF_2'),k2_relat_1('#skF_2'),'#skF_2') != k1_relat_1('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_176,c_4086])).

tff(c_4092,plain,(
    ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_882,c_4087])).

tff(c_4096,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_4092])).

tff(c_4097,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_118])).

tff(c_22,plain,(
    ! [A_10] : k2_relat_1(k6_relat_1(A_10)) = A_10 ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_24,plain,(
    ! [A_11] : v1_relat_1(k6_relat_1(A_11)) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_112,plain,(
    ! [A_11] :
      ( k2_relat_1(k6_relat_1(A_11)) != k1_xboole_0
      | k6_relat_1(A_11) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_24,c_109])).

tff(c_120,plain,(
    ! [A_34] :
      ( k1_xboole_0 != A_34
      | k6_relat_1(A_34) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_112])).

tff(c_20,plain,(
    ! [A_10] : k1_relat_1(k6_relat_1(A_10)) = A_10 ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_126,plain,(
    ! [A_34] :
      ( k1_relat_1(k1_xboole_0) = A_34
      | k1_xboole_0 != A_34 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_120,c_20])).

tff(c_4173,plain,(
    k1_relat_1('#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4097,c_4097,c_126])).

tff(c_4180,plain,(
    ! [A_345,B_346] :
      ( r2_hidden('#skF_1'(A_345,B_346),A_345)
      | r1_tarski(A_345,B_346) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_4185,plain,(
    ! [A_345] : r1_tarski(A_345,A_345) ),
    inference(resolution,[status(thm)],[c_4180,c_4])).

tff(c_10,plain,(
    ! [A_6] : k2_zfmisc_1(A_6,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_36,plain,(
    ! [A_23] :
      ( v1_funct_2(k1_xboole_0,A_23,k1_xboole_0)
      | k1_xboole_0 = A_23
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(A_23,k1_xboole_0))) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_57,plain,(
    ! [A_23] :
      ( v1_funct_2(k1_xboole_0,A_23,k1_xboole_0)
      | k1_xboole_0 = A_23
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_36])).

tff(c_4232,plain,(
    ! [A_23] :
      ( v1_funct_2('#skF_2',A_23,'#skF_2')
      | A_23 = '#skF_2'
      | ~ m1_subset_1('#skF_2',k1_zfmisc_1('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4097,c_4097,c_4097,c_4097,c_4097,c_57])).

tff(c_4233,plain,(
    ~ m1_subset_1('#skF_2',k1_zfmisc_1('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_4232])).

tff(c_4098,plain,(
    k2_relat_1('#skF_2') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_118])).

tff(c_4113,plain,(
    k2_relat_1('#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4097,c_4098])).

tff(c_12,plain,(
    ! [B_7] : k2_zfmisc_1(k1_xboole_0,B_7) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_4103,plain,(
    ! [B_7] : k2_zfmisc_1('#skF_2',B_7) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4097,c_4097,c_12])).

tff(c_4287,plain,(
    ! [C_380,A_381,B_382] :
      ( m1_subset_1(C_380,k1_zfmisc_1(k2_zfmisc_1(A_381,B_382)))
      | ~ r1_tarski(k2_relat_1(C_380),B_382)
      | ~ r1_tarski(k1_relat_1(C_380),A_381)
      | ~ v1_relat_1(C_380) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_4302,plain,(
    ! [C_383,B_384] :
      ( m1_subset_1(C_383,k1_zfmisc_1('#skF_2'))
      | ~ r1_tarski(k2_relat_1(C_383),B_384)
      | ~ r1_tarski(k1_relat_1(C_383),'#skF_2')
      | ~ v1_relat_1(C_383) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4103,c_4287])).

tff(c_4308,plain,(
    ! [B_384] :
      ( m1_subset_1('#skF_2',k1_zfmisc_1('#skF_2'))
      | ~ r1_tarski('#skF_2',B_384)
      | ~ r1_tarski(k1_relat_1('#skF_2'),'#skF_2')
      | ~ v1_relat_1('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4113,c_4302])).

tff(c_4314,plain,(
    ! [B_384] :
      ( m1_subset_1('#skF_2',k1_zfmisc_1('#skF_2'))
      | ~ r1_tarski('#skF_2',B_384) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_4185,c_4173,c_4308])).

tff(c_4318,plain,(
    ! [B_385] : ~ r1_tarski('#skF_2',B_385) ),
    inference(negUnitSimplification,[status(thm)],[c_4233,c_4314])).

tff(c_4323,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_4185,c_4318])).

tff(c_4325,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_4232])).

tff(c_4105,plain,(
    ! [A_6] : k2_zfmisc_1(A_6,'#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4097,c_4097,c_10])).

tff(c_4346,plain,(
    ! [A_390,B_391,C_392] :
      ( k1_relset_1(A_390,B_391,C_392) = k1_relat_1(C_392)
      | ~ m1_subset_1(C_392,k1_zfmisc_1(k2_zfmisc_1(A_390,B_391))) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_4365,plain,(
    ! [A_396,C_397] :
      ( k1_relset_1(A_396,'#skF_2',C_397) = k1_relat_1(C_397)
      | ~ m1_subset_1(C_397,k1_zfmisc_1('#skF_2')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4105,c_4346])).

tff(c_4367,plain,(
    ! [A_396] : k1_relset_1(A_396,'#skF_2','#skF_2') = k1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_4325,c_4365])).

tff(c_4395,plain,(
    ! [A_401] : k1_relset_1(A_401,'#skF_2','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4173,c_4367])).

tff(c_30,plain,(
    ! [A_14,B_15,C_16] :
      ( m1_subset_1(k1_relset_1(A_14,B_15,C_16),k1_zfmisc_1(A_14))
      | ~ m1_subset_1(C_16,k1_zfmisc_1(k2_zfmisc_1(A_14,B_15))) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_4400,plain,(
    ! [A_401] :
      ( m1_subset_1('#skF_2',k1_zfmisc_1(A_401))
      | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1(A_401,'#skF_2'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4395,c_30])).

tff(c_4416,plain,(
    ! [A_402] : m1_subset_1('#skF_2',k1_zfmisc_1(A_402)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4325,c_4105,c_4400])).

tff(c_4426,plain,(
    ! [A_17,B_18] : k1_relset_1(A_17,B_18,'#skF_2') = k1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_4416,c_32])).

tff(c_4435,plain,(
    ! [A_17,B_18] : k1_relset_1(A_17,B_18,'#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4173,c_4426])).

tff(c_4411,plain,(
    ! [A_401] : m1_subset_1('#skF_2',k1_zfmisc_1(A_401)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4325,c_4105,c_4400])).

tff(c_40,plain,(
    ! [C_25,B_24] :
      ( v1_funct_2(C_25,k1_xboole_0,B_24)
      | k1_relset_1(k1_xboole_0,B_24,C_25) != k1_xboole_0
      | ~ m1_subset_1(C_25,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_24))) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_56,plain,(
    ! [C_25,B_24] :
      ( v1_funct_2(C_25,k1_xboole_0,B_24)
      | k1_relset_1(k1_xboole_0,B_24,C_25) != k1_xboole_0
      | ~ m1_subset_1(C_25,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_40])).

tff(c_4470,plain,(
    ! [C_408,B_409] :
      ( v1_funct_2(C_408,'#skF_2',B_409)
      | k1_relset_1('#skF_2',B_409,C_408) != '#skF_2'
      | ~ m1_subset_1(C_408,k1_zfmisc_1('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4097,c_4097,c_4097,c_4097,c_56])).

tff(c_4473,plain,(
    ! [B_409] :
      ( v1_funct_2('#skF_2','#skF_2',B_409)
      | k1_relset_1('#skF_2',B_409,'#skF_2') != '#skF_2' ) ),
    inference(resolution,[status(thm)],[c_4411,c_4470])).

tff(c_4479,plain,(
    ! [B_409] : v1_funct_2('#skF_2','#skF_2',B_409) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4435,c_4473])).

tff(c_4114,plain,(
    ~ v1_funct_2('#skF_2',k1_relat_1('#skF_2'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4113,c_108])).

tff(c_4174,plain,(
    ~ v1_funct_2('#skF_2','#skF_2','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4173,c_4114])).

tff(c_4484,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4479,c_4174])).

tff(c_4485,plain,(
    ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_2'),k2_relat_1('#skF_2')))) ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_4647,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_2'),k2_relat_1('#skF_2'))
    | ~ r1_tarski(k1_relat_1('#skF_2'),k1_relat_1('#skF_2'))
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_4638,c_4485])).

tff(c_4659,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_4585,c_4585,c_4647])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:46:24 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.25/2.03  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.25/2.04  
% 5.25/2.04  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.25/2.04  %$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k9_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1
% 5.25/2.04  
% 5.25/2.04  %Foreground sorts:
% 5.25/2.04  
% 5.25/2.04  
% 5.25/2.04  %Background operators:
% 5.25/2.04  
% 5.25/2.04  
% 5.25/2.04  %Foreground operators:
% 5.25/2.04  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 5.25/2.04  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 5.25/2.04  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.25/2.04  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.25/2.04  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.25/2.04  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.25/2.04  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 5.25/2.04  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 5.25/2.04  tff('#skF_2', type, '#skF_2': $i).
% 5.25/2.04  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 5.25/2.04  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 5.25/2.04  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.25/2.04  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.25/2.04  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.25/2.04  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 5.25/2.04  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 5.25/2.04  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.25/2.04  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 5.25/2.04  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 5.25/2.04  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.25/2.04  
% 5.57/2.06  tff(f_105, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => ((v1_funct_1(A) & v1_funct_2(A, k1_relat_1(A), k2_relat_1(A))) & m1_subset_1(A, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_funct_2)).
% 5.57/2.06  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 5.57/2.06  tff(f_76, axiom, (![A, B, C]: (v1_relat_1(C) => ((r1_tarski(k1_relat_1(C), A) & r1_tarski(k2_relat_1(C), B)) => m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_relset_1)).
% 5.57/2.06  tff(f_68, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 5.57/2.06  tff(f_48, axiom, (![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_relat_1)).
% 5.57/2.06  tff(f_94, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 5.57/2.06  tff(f_52, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 5.57/2.06  tff(f_56, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v2_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc4_funct_1)).
% 5.57/2.06  tff(f_38, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 5.57/2.06  tff(f_64, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k1_relset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_relset_1)).
% 5.57/2.06  tff(c_52, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_105])).
% 5.57/2.06  tff(c_4580, plain, (![A_419, B_420]: (r2_hidden('#skF_1'(A_419, B_420), A_419) | r1_tarski(A_419, B_420))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.57/2.06  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.57/2.06  tff(c_4585, plain, (![A_419]: (r1_tarski(A_419, A_419))), inference(resolution, [status(thm)], [c_4580, c_4])).
% 5.57/2.06  tff(c_4638, plain, (![C_444, A_445, B_446]: (m1_subset_1(C_444, k1_zfmisc_1(k2_zfmisc_1(A_445, B_446))) | ~r1_tarski(k2_relat_1(C_444), B_446) | ~r1_tarski(k1_relat_1(C_444), A_445) | ~v1_relat_1(C_444))), inference(cnfTransformation, [status(thm)], [f_76])).
% 5.57/2.06  tff(c_191, plain, (![A_40, B_41]: (r2_hidden('#skF_1'(A_40, B_41), A_40) | r1_tarski(A_40, B_41))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.57/2.06  tff(c_196, plain, (![A_40]: (r1_tarski(A_40, A_40))), inference(resolution, [status(thm)], [c_191, c_4])).
% 5.57/2.06  tff(c_514, plain, (![C_111, A_112, B_113]: (m1_subset_1(C_111, k1_zfmisc_1(k2_zfmisc_1(A_112, B_113))) | ~r1_tarski(k2_relat_1(C_111), B_113) | ~r1_tarski(k1_relat_1(C_111), A_112) | ~v1_relat_1(C_111))), inference(cnfTransformation, [status(thm)], [f_76])).
% 5.57/2.06  tff(c_32, plain, (![A_17, B_18, C_19]: (k1_relset_1(A_17, B_18, C_19)=k1_relat_1(C_19) | ~m1_subset_1(C_19, k1_zfmisc_1(k2_zfmisc_1(A_17, B_18))))), inference(cnfTransformation, [status(thm)], [f_68])).
% 5.57/2.06  tff(c_754, plain, (![A_144, B_145, C_146]: (k1_relset_1(A_144, B_145, C_146)=k1_relat_1(C_146) | ~r1_tarski(k2_relat_1(C_146), B_145) | ~r1_tarski(k1_relat_1(C_146), A_144) | ~v1_relat_1(C_146))), inference(resolution, [status(thm)], [c_514, c_32])).
% 5.57/2.06  tff(c_876, plain, (![A_159, C_160]: (k1_relset_1(A_159, k2_relat_1(C_160), C_160)=k1_relat_1(C_160) | ~r1_tarski(k1_relat_1(C_160), A_159) | ~v1_relat_1(C_160))), inference(resolution, [status(thm)], [c_196, c_754])).
% 5.57/2.06  tff(c_882, plain, (![C_160]: (k1_relset_1(k1_relat_1(C_160), k2_relat_1(C_160), C_160)=k1_relat_1(C_160) | ~v1_relat_1(C_160))), inference(resolution, [status(thm)], [c_196, c_876])).
% 5.57/2.06  tff(c_109, plain, (![A_33]: (k2_relat_1(A_33)!=k1_xboole_0 | k1_xboole_0=A_33 | ~v1_relat_1(A_33))), inference(cnfTransformation, [status(thm)], [f_48])).
% 5.57/2.06  tff(c_118, plain, (k2_relat_1('#skF_2')!=k1_xboole_0 | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_52, c_109])).
% 5.57/2.06  tff(c_176, plain, (k2_relat_1('#skF_2')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_118])).
% 5.57/2.06  tff(c_34, plain, (![C_22, A_20, B_21]: (m1_subset_1(C_22, k1_zfmisc_1(k2_zfmisc_1(A_20, B_21))) | ~r1_tarski(k2_relat_1(C_22), B_21) | ~r1_tarski(k1_relat_1(C_22), A_20) | ~v1_relat_1(C_22))), inference(cnfTransformation, [status(thm)], [f_76])).
% 5.57/2.06  tff(c_651, plain, (![B_128, C_129, A_130]: (k1_xboole_0=B_128 | v1_funct_2(C_129, A_130, B_128) | k1_relset_1(A_130, B_128, C_129)!=A_130 | ~m1_subset_1(C_129, k1_zfmisc_1(k2_zfmisc_1(A_130, B_128))))), inference(cnfTransformation, [status(thm)], [f_94])).
% 5.57/2.06  tff(c_1972, plain, (![B_235, C_236, A_237]: (k1_xboole_0=B_235 | v1_funct_2(C_236, A_237, B_235) | k1_relset_1(A_237, B_235, C_236)!=A_237 | ~r1_tarski(k2_relat_1(C_236), B_235) | ~r1_tarski(k1_relat_1(C_236), A_237) | ~v1_relat_1(C_236))), inference(resolution, [status(thm)], [c_34, c_651])).
% 5.57/2.06  tff(c_4061, plain, (![C_336, A_337]: (k2_relat_1(C_336)=k1_xboole_0 | v1_funct_2(C_336, A_337, k2_relat_1(C_336)) | k1_relset_1(A_337, k2_relat_1(C_336), C_336)!=A_337 | ~r1_tarski(k1_relat_1(C_336), A_337) | ~v1_relat_1(C_336))), inference(resolution, [status(thm)], [c_196, c_1972])).
% 5.57/2.06  tff(c_50, plain, (v1_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_105])).
% 5.57/2.06  tff(c_48, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_2'), k2_relat_1('#skF_2')))) | ~v1_funct_2('#skF_2', k1_relat_1('#skF_2'), k2_relat_1('#skF_2')) | ~v1_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_105])).
% 5.57/2.06  tff(c_54, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_2'), k2_relat_1('#skF_2')))) | ~v1_funct_2('#skF_2', k1_relat_1('#skF_2'), k2_relat_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48])).
% 5.57/2.06  tff(c_108, plain, (~v1_funct_2('#skF_2', k1_relat_1('#skF_2'), k2_relat_1('#skF_2'))), inference(splitLeft, [status(thm)], [c_54])).
% 5.57/2.06  tff(c_4073, plain, (k2_relat_1('#skF_2')=k1_xboole_0 | k1_relset_1(k1_relat_1('#skF_2'), k2_relat_1('#skF_2'), '#skF_2')!=k1_relat_1('#skF_2') | ~r1_tarski(k1_relat_1('#skF_2'), k1_relat_1('#skF_2')) | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_4061, c_108])).
% 5.57/2.06  tff(c_4086, plain, (k2_relat_1('#skF_2')=k1_xboole_0 | k1_relset_1(k1_relat_1('#skF_2'), k2_relat_1('#skF_2'), '#skF_2')!=k1_relat_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_196, c_4073])).
% 5.57/2.06  tff(c_4087, plain, (k1_relset_1(k1_relat_1('#skF_2'), k2_relat_1('#skF_2'), '#skF_2')!=k1_relat_1('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_176, c_4086])).
% 5.57/2.06  tff(c_4092, plain, (~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_882, c_4087])).
% 5.57/2.06  tff(c_4096, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_52, c_4092])).
% 5.57/2.06  tff(c_4097, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_118])).
% 5.57/2.06  tff(c_22, plain, (![A_10]: (k2_relat_1(k6_relat_1(A_10))=A_10)), inference(cnfTransformation, [status(thm)], [f_52])).
% 5.57/2.06  tff(c_24, plain, (![A_11]: (v1_relat_1(k6_relat_1(A_11)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 5.57/2.06  tff(c_112, plain, (![A_11]: (k2_relat_1(k6_relat_1(A_11))!=k1_xboole_0 | k6_relat_1(A_11)=k1_xboole_0)), inference(resolution, [status(thm)], [c_24, c_109])).
% 5.57/2.06  tff(c_120, plain, (![A_34]: (k1_xboole_0!=A_34 | k6_relat_1(A_34)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_22, c_112])).
% 5.57/2.06  tff(c_20, plain, (![A_10]: (k1_relat_1(k6_relat_1(A_10))=A_10)), inference(cnfTransformation, [status(thm)], [f_52])).
% 5.57/2.06  tff(c_126, plain, (![A_34]: (k1_relat_1(k1_xboole_0)=A_34 | k1_xboole_0!=A_34)), inference(superposition, [status(thm), theory('equality')], [c_120, c_20])).
% 5.57/2.06  tff(c_4173, plain, (k1_relat_1('#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_4097, c_4097, c_126])).
% 5.57/2.06  tff(c_4180, plain, (![A_345, B_346]: (r2_hidden('#skF_1'(A_345, B_346), A_345) | r1_tarski(A_345, B_346))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.57/2.06  tff(c_4185, plain, (![A_345]: (r1_tarski(A_345, A_345))), inference(resolution, [status(thm)], [c_4180, c_4])).
% 5.57/2.06  tff(c_10, plain, (![A_6]: (k2_zfmisc_1(A_6, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_38])).
% 5.57/2.06  tff(c_36, plain, (![A_23]: (v1_funct_2(k1_xboole_0, A_23, k1_xboole_0) | k1_xboole_0=A_23 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k2_zfmisc_1(A_23, k1_xboole_0))))), inference(cnfTransformation, [status(thm)], [f_94])).
% 5.57/2.06  tff(c_57, plain, (![A_23]: (v1_funct_2(k1_xboole_0, A_23, k1_xboole_0) | k1_xboole_0=A_23 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_36])).
% 5.57/2.06  tff(c_4232, plain, (![A_23]: (v1_funct_2('#skF_2', A_23, '#skF_2') | A_23='#skF_2' | ~m1_subset_1('#skF_2', k1_zfmisc_1('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_4097, c_4097, c_4097, c_4097, c_4097, c_57])).
% 5.57/2.06  tff(c_4233, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1('#skF_2'))), inference(splitLeft, [status(thm)], [c_4232])).
% 5.57/2.06  tff(c_4098, plain, (k2_relat_1('#skF_2')=k1_xboole_0), inference(splitRight, [status(thm)], [c_118])).
% 5.57/2.06  tff(c_4113, plain, (k2_relat_1('#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_4097, c_4098])).
% 5.57/2.06  tff(c_12, plain, (![B_7]: (k2_zfmisc_1(k1_xboole_0, B_7)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_38])).
% 5.57/2.06  tff(c_4103, plain, (![B_7]: (k2_zfmisc_1('#skF_2', B_7)='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_4097, c_4097, c_12])).
% 5.57/2.06  tff(c_4287, plain, (![C_380, A_381, B_382]: (m1_subset_1(C_380, k1_zfmisc_1(k2_zfmisc_1(A_381, B_382))) | ~r1_tarski(k2_relat_1(C_380), B_382) | ~r1_tarski(k1_relat_1(C_380), A_381) | ~v1_relat_1(C_380))), inference(cnfTransformation, [status(thm)], [f_76])).
% 5.57/2.06  tff(c_4302, plain, (![C_383, B_384]: (m1_subset_1(C_383, k1_zfmisc_1('#skF_2')) | ~r1_tarski(k2_relat_1(C_383), B_384) | ~r1_tarski(k1_relat_1(C_383), '#skF_2') | ~v1_relat_1(C_383))), inference(superposition, [status(thm), theory('equality')], [c_4103, c_4287])).
% 5.57/2.06  tff(c_4308, plain, (![B_384]: (m1_subset_1('#skF_2', k1_zfmisc_1('#skF_2')) | ~r1_tarski('#skF_2', B_384) | ~r1_tarski(k1_relat_1('#skF_2'), '#skF_2') | ~v1_relat_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_4113, c_4302])).
% 5.57/2.06  tff(c_4314, plain, (![B_384]: (m1_subset_1('#skF_2', k1_zfmisc_1('#skF_2')) | ~r1_tarski('#skF_2', B_384))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_4185, c_4173, c_4308])).
% 5.57/2.06  tff(c_4318, plain, (![B_385]: (~r1_tarski('#skF_2', B_385))), inference(negUnitSimplification, [status(thm)], [c_4233, c_4314])).
% 5.57/2.06  tff(c_4323, plain, $false, inference(resolution, [status(thm)], [c_4185, c_4318])).
% 5.57/2.06  tff(c_4325, plain, (m1_subset_1('#skF_2', k1_zfmisc_1('#skF_2'))), inference(splitRight, [status(thm)], [c_4232])).
% 5.57/2.06  tff(c_4105, plain, (![A_6]: (k2_zfmisc_1(A_6, '#skF_2')='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_4097, c_4097, c_10])).
% 5.57/2.06  tff(c_4346, plain, (![A_390, B_391, C_392]: (k1_relset_1(A_390, B_391, C_392)=k1_relat_1(C_392) | ~m1_subset_1(C_392, k1_zfmisc_1(k2_zfmisc_1(A_390, B_391))))), inference(cnfTransformation, [status(thm)], [f_68])).
% 5.57/2.06  tff(c_4365, plain, (![A_396, C_397]: (k1_relset_1(A_396, '#skF_2', C_397)=k1_relat_1(C_397) | ~m1_subset_1(C_397, k1_zfmisc_1('#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_4105, c_4346])).
% 5.57/2.06  tff(c_4367, plain, (![A_396]: (k1_relset_1(A_396, '#skF_2', '#skF_2')=k1_relat_1('#skF_2'))), inference(resolution, [status(thm)], [c_4325, c_4365])).
% 5.57/2.06  tff(c_4395, plain, (![A_401]: (k1_relset_1(A_401, '#skF_2', '#skF_2')='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_4173, c_4367])).
% 5.57/2.06  tff(c_30, plain, (![A_14, B_15, C_16]: (m1_subset_1(k1_relset_1(A_14, B_15, C_16), k1_zfmisc_1(A_14)) | ~m1_subset_1(C_16, k1_zfmisc_1(k2_zfmisc_1(A_14, B_15))))), inference(cnfTransformation, [status(thm)], [f_64])).
% 5.57/2.06  tff(c_4400, plain, (![A_401]: (m1_subset_1('#skF_2', k1_zfmisc_1(A_401)) | ~m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1(A_401, '#skF_2'))))), inference(superposition, [status(thm), theory('equality')], [c_4395, c_30])).
% 5.57/2.06  tff(c_4416, plain, (![A_402]: (m1_subset_1('#skF_2', k1_zfmisc_1(A_402)))), inference(demodulation, [status(thm), theory('equality')], [c_4325, c_4105, c_4400])).
% 5.57/2.06  tff(c_4426, plain, (![A_17, B_18]: (k1_relset_1(A_17, B_18, '#skF_2')=k1_relat_1('#skF_2'))), inference(resolution, [status(thm)], [c_4416, c_32])).
% 5.57/2.06  tff(c_4435, plain, (![A_17, B_18]: (k1_relset_1(A_17, B_18, '#skF_2')='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_4173, c_4426])).
% 5.57/2.06  tff(c_4411, plain, (![A_401]: (m1_subset_1('#skF_2', k1_zfmisc_1(A_401)))), inference(demodulation, [status(thm), theory('equality')], [c_4325, c_4105, c_4400])).
% 5.57/2.06  tff(c_40, plain, (![C_25, B_24]: (v1_funct_2(C_25, k1_xboole_0, B_24) | k1_relset_1(k1_xboole_0, B_24, C_25)!=k1_xboole_0 | ~m1_subset_1(C_25, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_24))))), inference(cnfTransformation, [status(thm)], [f_94])).
% 5.57/2.06  tff(c_56, plain, (![C_25, B_24]: (v1_funct_2(C_25, k1_xboole_0, B_24) | k1_relset_1(k1_xboole_0, B_24, C_25)!=k1_xboole_0 | ~m1_subset_1(C_25, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_40])).
% 5.57/2.06  tff(c_4470, plain, (![C_408, B_409]: (v1_funct_2(C_408, '#skF_2', B_409) | k1_relset_1('#skF_2', B_409, C_408)!='#skF_2' | ~m1_subset_1(C_408, k1_zfmisc_1('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_4097, c_4097, c_4097, c_4097, c_56])).
% 5.57/2.06  tff(c_4473, plain, (![B_409]: (v1_funct_2('#skF_2', '#skF_2', B_409) | k1_relset_1('#skF_2', B_409, '#skF_2')!='#skF_2')), inference(resolution, [status(thm)], [c_4411, c_4470])).
% 5.57/2.06  tff(c_4479, plain, (![B_409]: (v1_funct_2('#skF_2', '#skF_2', B_409))), inference(demodulation, [status(thm), theory('equality')], [c_4435, c_4473])).
% 5.57/2.06  tff(c_4114, plain, (~v1_funct_2('#skF_2', k1_relat_1('#skF_2'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_4113, c_108])).
% 5.57/2.06  tff(c_4174, plain, (~v1_funct_2('#skF_2', '#skF_2', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_4173, c_4114])).
% 5.57/2.06  tff(c_4484, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4479, c_4174])).
% 5.57/2.06  tff(c_4485, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_2'), k2_relat_1('#skF_2'))))), inference(splitRight, [status(thm)], [c_54])).
% 5.57/2.06  tff(c_4647, plain, (~r1_tarski(k2_relat_1('#skF_2'), k2_relat_1('#skF_2')) | ~r1_tarski(k1_relat_1('#skF_2'), k1_relat_1('#skF_2')) | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_4638, c_4485])).
% 5.57/2.06  tff(c_4659, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_52, c_4585, c_4585, c_4647])).
% 5.57/2.06  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.57/2.06  
% 5.57/2.06  Inference rules
% 5.57/2.06  ----------------------
% 5.57/2.06  #Ref     : 5
% 5.57/2.06  #Sup     : 970
% 5.57/2.06  #Fact    : 0
% 5.57/2.06  #Define  : 0
% 5.57/2.06  #Split   : 13
% 5.57/2.06  #Chain   : 0
% 5.57/2.06  #Close   : 0
% 5.57/2.06  
% 5.57/2.06  Ordering : KBO
% 5.57/2.06  
% 5.57/2.06  Simplification rules
% 5.57/2.06  ----------------------
% 5.57/2.06  #Subsume      : 201
% 5.57/2.06  #Demod        : 1103
% 5.57/2.06  #Tautology    : 497
% 5.57/2.06  #SimpNegUnit  : 26
% 5.57/2.06  #BackRed      : 22
% 5.57/2.06  
% 5.57/2.06  #Partial instantiations: 0
% 5.57/2.06  #Strategies tried      : 1
% 5.57/2.06  
% 5.57/2.06  Timing (in seconds)
% 5.57/2.06  ----------------------
% 5.57/2.06  Preprocessing        : 0.34
% 5.57/2.06  Parsing              : 0.18
% 5.57/2.06  CNF conversion       : 0.02
% 5.57/2.06  Main loop            : 0.90
% 5.57/2.06  Inferencing          : 0.31
% 5.57/2.06  Reduction            : 0.31
% 5.57/2.06  Demodulation         : 0.22
% 5.57/2.06  BG Simplification    : 0.04
% 5.57/2.06  Subsumption          : 0.17
% 5.57/2.06  Abstraction          : 0.05
% 5.57/2.06  MUC search           : 0.00
% 5.57/2.06  Cooper               : 0.00
% 5.57/2.06  Total                : 1.29
% 5.57/2.06  Index Insertion      : 0.00
% 5.57/2.06  Index Deletion       : 0.00
% 5.57/2.06  Index Matching       : 0.00
% 5.57/2.06  BG Taut test         : 0.00
%------------------------------------------------------------------------------
