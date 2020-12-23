%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:10:45 EST 2020

% Result     : Theorem 3.91s
% Output     : CNFRefutation 3.91s
% Verified   : 
% Statistics : Number of formulae       :  107 ( 641 expanded)
%              Number of leaves         :   33 ( 223 expanded)
%              Depth                    :   12
%              Number of atoms          :  161 (1625 expanded)
%              Number of equality atoms :   57 ( 417 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_6 > #skF_5 > #skF_2 > #skF_4

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

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

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

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_114,negated_conjecture,(
    ~ ! [A] :
        ( ( v1_relat_1(A)
          & v1_funct_1(A) )
       => ( v1_funct_1(A)
          & v1_funct_2(A,k1_relat_1(A),k2_relat_1(A))
          & m1_subset_1(A,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A)))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_funct_2)).

tff(f_54,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => r1_tarski(A,k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_relat_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_85,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_103,axiom,(
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

tff(f_81,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(B,A)))
         => v1_xboole_0(C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc4_relset_1)).

tff(f_30,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_40,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_46,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(c_62,plain,(
    v1_relat_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_2216,plain,(
    ! [A_311] :
      ( r1_tarski(A_311,k2_zfmisc_1(k1_relat_1(A_311),k2_relat_1(A_311)))
      | ~ v1_relat_1(A_311) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_2196,plain,(
    ! [A_307,B_308] :
      ( m1_subset_1(A_307,k1_zfmisc_1(B_308))
      | ~ r1_tarski(A_307,B_308) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_20,plain,(
    ! [A_9] :
      ( r1_tarski(A_9,k2_zfmisc_1(k1_relat_1(A_9),k2_relat_1(A_9)))
      | ~ v1_relat_1(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_18,plain,(
    ! [A_7,B_8] :
      ( m1_subset_1(A_7,k1_zfmisc_1(B_8))
      | ~ r1_tarski(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_157,plain,(
    ! [A_82,B_83,C_84] :
      ( k1_relset_1(A_82,B_83,C_84) = k1_relat_1(C_84)
      | ~ m1_subset_1(C_84,k1_zfmisc_1(k2_zfmisc_1(A_82,B_83))) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_265,plain,(
    ! [A_102,B_103,A_104] :
      ( k1_relset_1(A_102,B_103,A_104) = k1_relat_1(A_104)
      | ~ r1_tarski(A_104,k2_zfmisc_1(A_102,B_103)) ) ),
    inference(resolution,[status(thm)],[c_18,c_157])).

tff(c_279,plain,(
    ! [A_9] :
      ( k1_relset_1(k1_relat_1(A_9),k2_relat_1(A_9),A_9) = k1_relat_1(A_9)
      | ~ v1_relat_1(A_9) ) ),
    inference(resolution,[status(thm)],[c_20,c_265])).

tff(c_1619,plain,(
    ! [B_260,C_261,A_262] :
      ( k1_xboole_0 = B_260
      | v1_funct_2(C_261,A_262,B_260)
      | k1_relset_1(A_262,B_260,C_261) != A_262
      | ~ m1_subset_1(C_261,k1_zfmisc_1(k2_zfmisc_1(A_262,B_260))) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_1730,plain,(
    ! [B_270,A_271,A_272] :
      ( k1_xboole_0 = B_270
      | v1_funct_2(A_271,A_272,B_270)
      | k1_relset_1(A_272,B_270,A_271) != A_272
      | ~ r1_tarski(A_271,k2_zfmisc_1(A_272,B_270)) ) ),
    inference(resolution,[status(thm)],[c_18,c_1619])).

tff(c_1898,plain,(
    ! [A_293] :
      ( k2_relat_1(A_293) = k1_xboole_0
      | v1_funct_2(A_293,k1_relat_1(A_293),k2_relat_1(A_293))
      | k1_relset_1(k1_relat_1(A_293),k2_relat_1(A_293),A_293) != k1_relat_1(A_293)
      | ~ v1_relat_1(A_293) ) ),
    inference(resolution,[status(thm)],[c_20,c_1730])).

tff(c_60,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_58,plain,
    ( ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_6'),k2_relat_1('#skF_6'))))
    | ~ v1_funct_2('#skF_6',k1_relat_1('#skF_6'),k2_relat_1('#skF_6'))
    | ~ v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_64,plain,
    ( ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_6'),k2_relat_1('#skF_6'))))
    | ~ v1_funct_2('#skF_6',k1_relat_1('#skF_6'),k2_relat_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58])).

tff(c_104,plain,(
    ~ v1_funct_2('#skF_6',k1_relat_1('#skF_6'),k2_relat_1('#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_64])).

tff(c_1905,plain,
    ( k2_relat_1('#skF_6') = k1_xboole_0
    | k1_relset_1(k1_relat_1('#skF_6'),k2_relat_1('#skF_6'),'#skF_6') != k1_relat_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_1898,c_104])).

tff(c_1917,plain,
    ( k2_relat_1('#skF_6') = k1_xboole_0
    | k1_relset_1(k1_relat_1('#skF_6'),k2_relat_1('#skF_6'),'#skF_6') != k1_relat_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_1905])).

tff(c_1922,plain,(
    k1_relset_1(k1_relat_1('#skF_6'),k2_relat_1('#skF_6'),'#skF_6') != k1_relat_1('#skF_6') ),
    inference(splitLeft,[status(thm)],[c_1917])).

tff(c_1925,plain,(
    ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_279,c_1922])).

tff(c_1929,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_1925])).

tff(c_1930,plain,(
    k2_relat_1('#skF_6') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_1917])).

tff(c_130,plain,(
    ! [C_77,B_78,A_79] :
      ( v1_xboole_0(C_77)
      | ~ m1_subset_1(C_77,k1_zfmisc_1(k2_zfmisc_1(B_78,A_79)))
      | ~ v1_xboole_0(A_79) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_169,plain,(
    ! [A_85,A_86,B_87] :
      ( v1_xboole_0(A_85)
      | ~ v1_xboole_0(A_86)
      | ~ r1_tarski(A_85,k2_zfmisc_1(B_87,A_86)) ) ),
    inference(resolution,[status(thm)],[c_18,c_130])).

tff(c_183,plain,(
    ! [A_9] :
      ( v1_xboole_0(A_9)
      | ~ v1_xboole_0(k2_relat_1(A_9))
      | ~ v1_relat_1(A_9) ) ),
    inference(resolution,[status(thm)],[c_20,c_169])).

tff(c_1957,plain,
    ( v1_xboole_0('#skF_6')
    | ~ v1_xboole_0(k1_xboole_0)
    | ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_1930,c_183])).

tff(c_1979,plain,(
    v1_xboole_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_2,c_1957])).

tff(c_4,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_1986,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(resolution,[status(thm)],[c_1979,c_4])).

tff(c_397,plain,(
    ! [B_130,C_131,A_132] :
      ( k1_xboole_0 = B_130
      | v1_funct_2(C_131,A_132,B_130)
      | k1_relset_1(A_132,B_130,C_131) != A_132
      | ~ m1_subset_1(C_131,k1_zfmisc_1(k2_zfmisc_1(A_132,B_130))) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_438,plain,(
    ! [B_137,A_138,A_139] :
      ( k1_xboole_0 = B_137
      | v1_funct_2(A_138,A_139,B_137)
      | k1_relset_1(A_139,B_137,A_138) != A_139
      | ~ r1_tarski(A_138,k2_zfmisc_1(A_139,B_137)) ) ),
    inference(resolution,[status(thm)],[c_18,c_397])).

tff(c_525,plain,(
    ! [A_154] :
      ( k2_relat_1(A_154) = k1_xboole_0
      | v1_funct_2(A_154,k1_relat_1(A_154),k2_relat_1(A_154))
      | k1_relset_1(k1_relat_1(A_154),k2_relat_1(A_154),A_154) != k1_relat_1(A_154)
      | ~ v1_relat_1(A_154) ) ),
    inference(resolution,[status(thm)],[c_20,c_438])).

tff(c_532,plain,
    ( k2_relat_1('#skF_6') = k1_xboole_0
    | k1_relset_1(k1_relat_1('#skF_6'),k2_relat_1('#skF_6'),'#skF_6') != k1_relat_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_525,c_104])).

tff(c_539,plain,
    ( k2_relat_1('#skF_6') = k1_xboole_0
    | k1_relset_1(k1_relat_1('#skF_6'),k2_relat_1('#skF_6'),'#skF_6') != k1_relat_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_532])).

tff(c_540,plain,(
    k1_relset_1(k1_relat_1('#skF_6'),k2_relat_1('#skF_6'),'#skF_6') != k1_relat_1('#skF_6') ),
    inference(splitLeft,[status(thm)],[c_539])).

tff(c_543,plain,(
    ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_279,c_540])).

tff(c_547,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_543])).

tff(c_548,plain,(
    k2_relat_1('#skF_6') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_539])).

tff(c_575,plain,
    ( v1_xboole_0('#skF_6')
    | ~ v1_xboole_0(k1_xboole_0)
    | ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_548,c_183])).

tff(c_596,plain,(
    v1_xboole_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_2,c_575])).

tff(c_604,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(resolution,[status(thm)],[c_596,c_4])).

tff(c_8,plain,(
    ! [A_4] : r1_tarski(k1_xboole_0,A_4) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_280,plain,(
    ! [A_102,B_103] : k1_relset_1(A_102,B_103,k1_xboole_0) = k1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_8,c_265])).

tff(c_12,plain,(
    ! [A_5] : k2_zfmisc_1(A_5,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_46,plain,(
    ! [A_59] :
      ( v1_funct_2(k1_xboole_0,A_59,k1_xboole_0)
      | k1_xboole_0 = A_59
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(A_59,k1_xboole_0))) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_67,plain,(
    ! [A_59] :
      ( v1_funct_2(k1_xboole_0,A_59,k1_xboole_0)
      | k1_xboole_0 = A_59
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_46])).

tff(c_189,plain,(
    ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(splitLeft,[status(thm)],[c_67])).

tff(c_192,plain,(
    ~ r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_18,c_189])).

tff(c_196,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_192])).

tff(c_198,plain,(
    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(splitRight,[status(thm)],[c_67])).

tff(c_14,plain,(
    ! [B_6] : k2_zfmisc_1(k1_xboole_0,B_6) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_50,plain,(
    ! [C_61,B_60] :
      ( v1_funct_2(C_61,k1_xboole_0,B_60)
      | k1_relset_1(k1_xboole_0,B_60,C_61) != k1_xboole_0
      | ~ m1_subset_1(C_61,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_60))) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_316,plain,(
    ! [C_110,B_111] :
      ( v1_funct_2(C_110,k1_xboole_0,B_111)
      | k1_relset_1(k1_xboole_0,B_111,C_110) != k1_xboole_0
      | ~ m1_subset_1(C_110,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_50])).

tff(c_318,plain,(
    ! [B_111] :
      ( v1_funct_2(k1_xboole_0,k1_xboole_0,B_111)
      | k1_relset_1(k1_xboole_0,B_111,k1_xboole_0) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_198,c_316])).

tff(c_323,plain,(
    ! [B_111] :
      ( v1_funct_2(k1_xboole_0,k1_xboole_0,B_111)
      | k1_relat_1(k1_xboole_0) != k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_280,c_318])).

tff(c_330,plain,(
    k1_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_323])).

tff(c_618,plain,(
    k1_relat_1('#skF_6') != '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_604,c_604,c_330])).

tff(c_197,plain,(
    ! [A_59] :
      ( v1_funct_2(k1_xboole_0,A_59,k1_xboole_0)
      | k1_xboole_0 = A_59 ) ),
    inference(splitRight,[status(thm)],[c_67])).

tff(c_859,plain,(
    ! [A_175] :
      ( v1_funct_2('#skF_6',A_175,'#skF_6')
      | A_175 = '#skF_6' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_604,c_604,c_604,c_197])).

tff(c_550,plain,(
    ~ v1_funct_2('#skF_6',k1_relat_1('#skF_6'),k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_548,c_104])).

tff(c_644,plain,(
    ~ v1_funct_2('#skF_6',k1_relat_1('#skF_6'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_604,c_550])).

tff(c_862,plain,(
    k1_relat_1('#skF_6') = '#skF_6' ),
    inference(resolution,[status(thm)],[c_859,c_644])).

tff(c_866,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_618,c_862])).

tff(c_867,plain,(
    ! [B_111] : v1_funct_2(k1_xboole_0,k1_xboole_0,B_111) ),
    inference(splitRight,[status(thm)],[c_323])).

tff(c_2008,plain,(
    ! [B_111] : v1_funct_2('#skF_6','#skF_6',B_111) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1986,c_1986,c_867])).

tff(c_868,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_323])).

tff(c_2009,plain,(
    k1_relat_1('#skF_6') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1986,c_1986,c_868])).

tff(c_1932,plain,(
    ~ v1_funct_2('#skF_6',k1_relat_1('#skF_6'),k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1930,c_104])).

tff(c_2144,plain,(
    ~ v1_funct_2('#skF_6','#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2009,c_1986,c_1932])).

tff(c_2185,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2008,c_2144])).

tff(c_2186,plain,(
    ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_6'),k2_relat_1('#skF_6')))) ),
    inference(splitRight,[status(thm)],[c_64])).

tff(c_2204,plain,(
    ~ r1_tarski('#skF_6',k2_zfmisc_1(k1_relat_1('#skF_6'),k2_relat_1('#skF_6'))) ),
    inference(resolution,[status(thm)],[c_2196,c_2186])).

tff(c_2219,plain,(
    ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_2216,c_2204])).

tff(c_2223,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_2219])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:01:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.91/1.65  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.91/1.66  
% 3.91/1.66  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.91/1.66  %$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_6 > #skF_5 > #skF_2 > #skF_4
% 3.91/1.66  
% 3.91/1.66  %Foreground sorts:
% 3.91/1.66  
% 3.91/1.66  
% 3.91/1.66  %Background operators:
% 3.91/1.66  
% 3.91/1.66  
% 3.91/1.66  %Foreground operators:
% 3.91/1.66  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.91/1.66  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.91/1.66  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.91/1.66  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.91/1.66  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.91/1.66  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 3.91/1.66  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.91/1.66  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.91/1.66  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.91/1.66  tff('#skF_6', type, '#skF_6': $i).
% 3.91/1.66  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 3.91/1.66  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.91/1.66  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.91/1.66  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.91/1.66  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.91/1.66  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.91/1.66  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.91/1.66  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.91/1.66  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.91/1.66  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.91/1.66  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.91/1.66  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 3.91/1.66  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.91/1.66  
% 3.91/1.68  tff(f_114, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => ((v1_funct_1(A) & v1_funct_2(A, k1_relat_1(A), k2_relat_1(A))) & m1_subset_1(A, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_funct_2)).
% 3.91/1.68  tff(f_54, axiom, (![A]: (v1_relat_1(A) => r1_tarski(A, k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t21_relat_1)).
% 3.91/1.68  tff(f_50, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 3.91/1.68  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 3.91/1.68  tff(f_85, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.91/1.68  tff(f_103, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 3.91/1.68  tff(f_81, axiom, (![A, B]: (v1_xboole_0(A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => v1_xboole_0(C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc4_relset_1)).
% 3.91/1.68  tff(f_30, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 3.91/1.68  tff(f_40, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 3.91/1.68  tff(f_46, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 3.91/1.68  tff(c_62, plain, (v1_relat_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_114])).
% 3.91/1.68  tff(c_2216, plain, (![A_311]: (r1_tarski(A_311, k2_zfmisc_1(k1_relat_1(A_311), k2_relat_1(A_311))) | ~v1_relat_1(A_311))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.91/1.68  tff(c_2196, plain, (![A_307, B_308]: (m1_subset_1(A_307, k1_zfmisc_1(B_308)) | ~r1_tarski(A_307, B_308))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.91/1.68  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 3.91/1.68  tff(c_20, plain, (![A_9]: (r1_tarski(A_9, k2_zfmisc_1(k1_relat_1(A_9), k2_relat_1(A_9))) | ~v1_relat_1(A_9))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.91/1.68  tff(c_18, plain, (![A_7, B_8]: (m1_subset_1(A_7, k1_zfmisc_1(B_8)) | ~r1_tarski(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.91/1.68  tff(c_157, plain, (![A_82, B_83, C_84]: (k1_relset_1(A_82, B_83, C_84)=k1_relat_1(C_84) | ~m1_subset_1(C_84, k1_zfmisc_1(k2_zfmisc_1(A_82, B_83))))), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.91/1.68  tff(c_265, plain, (![A_102, B_103, A_104]: (k1_relset_1(A_102, B_103, A_104)=k1_relat_1(A_104) | ~r1_tarski(A_104, k2_zfmisc_1(A_102, B_103)))), inference(resolution, [status(thm)], [c_18, c_157])).
% 3.91/1.68  tff(c_279, plain, (![A_9]: (k1_relset_1(k1_relat_1(A_9), k2_relat_1(A_9), A_9)=k1_relat_1(A_9) | ~v1_relat_1(A_9))), inference(resolution, [status(thm)], [c_20, c_265])).
% 3.91/1.68  tff(c_1619, plain, (![B_260, C_261, A_262]: (k1_xboole_0=B_260 | v1_funct_2(C_261, A_262, B_260) | k1_relset_1(A_262, B_260, C_261)!=A_262 | ~m1_subset_1(C_261, k1_zfmisc_1(k2_zfmisc_1(A_262, B_260))))), inference(cnfTransformation, [status(thm)], [f_103])).
% 3.91/1.68  tff(c_1730, plain, (![B_270, A_271, A_272]: (k1_xboole_0=B_270 | v1_funct_2(A_271, A_272, B_270) | k1_relset_1(A_272, B_270, A_271)!=A_272 | ~r1_tarski(A_271, k2_zfmisc_1(A_272, B_270)))), inference(resolution, [status(thm)], [c_18, c_1619])).
% 3.91/1.68  tff(c_1898, plain, (![A_293]: (k2_relat_1(A_293)=k1_xboole_0 | v1_funct_2(A_293, k1_relat_1(A_293), k2_relat_1(A_293)) | k1_relset_1(k1_relat_1(A_293), k2_relat_1(A_293), A_293)!=k1_relat_1(A_293) | ~v1_relat_1(A_293))), inference(resolution, [status(thm)], [c_20, c_1730])).
% 3.91/1.68  tff(c_60, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_114])).
% 3.91/1.68  tff(c_58, plain, (~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_6'), k2_relat_1('#skF_6')))) | ~v1_funct_2('#skF_6', k1_relat_1('#skF_6'), k2_relat_1('#skF_6')) | ~v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_114])).
% 3.91/1.68  tff(c_64, plain, (~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_6'), k2_relat_1('#skF_6')))) | ~v1_funct_2('#skF_6', k1_relat_1('#skF_6'), k2_relat_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58])).
% 3.91/1.68  tff(c_104, plain, (~v1_funct_2('#skF_6', k1_relat_1('#skF_6'), k2_relat_1('#skF_6'))), inference(splitLeft, [status(thm)], [c_64])).
% 3.91/1.68  tff(c_1905, plain, (k2_relat_1('#skF_6')=k1_xboole_0 | k1_relset_1(k1_relat_1('#skF_6'), k2_relat_1('#skF_6'), '#skF_6')!=k1_relat_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_1898, c_104])).
% 3.91/1.68  tff(c_1917, plain, (k2_relat_1('#skF_6')=k1_xboole_0 | k1_relset_1(k1_relat_1('#skF_6'), k2_relat_1('#skF_6'), '#skF_6')!=k1_relat_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_1905])).
% 3.91/1.68  tff(c_1922, plain, (k1_relset_1(k1_relat_1('#skF_6'), k2_relat_1('#skF_6'), '#skF_6')!=k1_relat_1('#skF_6')), inference(splitLeft, [status(thm)], [c_1917])).
% 3.91/1.68  tff(c_1925, plain, (~v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_279, c_1922])).
% 3.91/1.68  tff(c_1929, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_62, c_1925])).
% 3.91/1.68  tff(c_1930, plain, (k2_relat_1('#skF_6')=k1_xboole_0), inference(splitRight, [status(thm)], [c_1917])).
% 3.91/1.68  tff(c_130, plain, (![C_77, B_78, A_79]: (v1_xboole_0(C_77) | ~m1_subset_1(C_77, k1_zfmisc_1(k2_zfmisc_1(B_78, A_79))) | ~v1_xboole_0(A_79))), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.91/1.68  tff(c_169, plain, (![A_85, A_86, B_87]: (v1_xboole_0(A_85) | ~v1_xboole_0(A_86) | ~r1_tarski(A_85, k2_zfmisc_1(B_87, A_86)))), inference(resolution, [status(thm)], [c_18, c_130])).
% 3.91/1.68  tff(c_183, plain, (![A_9]: (v1_xboole_0(A_9) | ~v1_xboole_0(k2_relat_1(A_9)) | ~v1_relat_1(A_9))), inference(resolution, [status(thm)], [c_20, c_169])).
% 3.91/1.68  tff(c_1957, plain, (v1_xboole_0('#skF_6') | ~v1_xboole_0(k1_xboole_0) | ~v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_1930, c_183])).
% 3.91/1.68  tff(c_1979, plain, (v1_xboole_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_2, c_1957])).
% 3.91/1.68  tff(c_4, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_30])).
% 3.91/1.68  tff(c_1986, plain, (k1_xboole_0='#skF_6'), inference(resolution, [status(thm)], [c_1979, c_4])).
% 3.91/1.68  tff(c_397, plain, (![B_130, C_131, A_132]: (k1_xboole_0=B_130 | v1_funct_2(C_131, A_132, B_130) | k1_relset_1(A_132, B_130, C_131)!=A_132 | ~m1_subset_1(C_131, k1_zfmisc_1(k2_zfmisc_1(A_132, B_130))))), inference(cnfTransformation, [status(thm)], [f_103])).
% 3.91/1.68  tff(c_438, plain, (![B_137, A_138, A_139]: (k1_xboole_0=B_137 | v1_funct_2(A_138, A_139, B_137) | k1_relset_1(A_139, B_137, A_138)!=A_139 | ~r1_tarski(A_138, k2_zfmisc_1(A_139, B_137)))), inference(resolution, [status(thm)], [c_18, c_397])).
% 3.91/1.68  tff(c_525, plain, (![A_154]: (k2_relat_1(A_154)=k1_xboole_0 | v1_funct_2(A_154, k1_relat_1(A_154), k2_relat_1(A_154)) | k1_relset_1(k1_relat_1(A_154), k2_relat_1(A_154), A_154)!=k1_relat_1(A_154) | ~v1_relat_1(A_154))), inference(resolution, [status(thm)], [c_20, c_438])).
% 3.91/1.68  tff(c_532, plain, (k2_relat_1('#skF_6')=k1_xboole_0 | k1_relset_1(k1_relat_1('#skF_6'), k2_relat_1('#skF_6'), '#skF_6')!=k1_relat_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_525, c_104])).
% 3.91/1.68  tff(c_539, plain, (k2_relat_1('#skF_6')=k1_xboole_0 | k1_relset_1(k1_relat_1('#skF_6'), k2_relat_1('#skF_6'), '#skF_6')!=k1_relat_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_532])).
% 3.91/1.68  tff(c_540, plain, (k1_relset_1(k1_relat_1('#skF_6'), k2_relat_1('#skF_6'), '#skF_6')!=k1_relat_1('#skF_6')), inference(splitLeft, [status(thm)], [c_539])).
% 3.91/1.68  tff(c_543, plain, (~v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_279, c_540])).
% 3.91/1.68  tff(c_547, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_62, c_543])).
% 3.91/1.68  tff(c_548, plain, (k2_relat_1('#skF_6')=k1_xboole_0), inference(splitRight, [status(thm)], [c_539])).
% 3.91/1.68  tff(c_575, plain, (v1_xboole_0('#skF_6') | ~v1_xboole_0(k1_xboole_0) | ~v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_548, c_183])).
% 3.91/1.68  tff(c_596, plain, (v1_xboole_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_2, c_575])).
% 3.91/1.68  tff(c_604, plain, (k1_xboole_0='#skF_6'), inference(resolution, [status(thm)], [c_596, c_4])).
% 3.91/1.68  tff(c_8, plain, (![A_4]: (r1_tarski(k1_xboole_0, A_4))), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.91/1.68  tff(c_280, plain, (![A_102, B_103]: (k1_relset_1(A_102, B_103, k1_xboole_0)=k1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_8, c_265])).
% 3.91/1.68  tff(c_12, plain, (![A_5]: (k2_zfmisc_1(A_5, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.91/1.68  tff(c_46, plain, (![A_59]: (v1_funct_2(k1_xboole_0, A_59, k1_xboole_0) | k1_xboole_0=A_59 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k2_zfmisc_1(A_59, k1_xboole_0))))), inference(cnfTransformation, [status(thm)], [f_103])).
% 3.91/1.68  tff(c_67, plain, (![A_59]: (v1_funct_2(k1_xboole_0, A_59, k1_xboole_0) | k1_xboole_0=A_59 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_46])).
% 3.91/1.68  tff(c_189, plain, (~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_xboole_0))), inference(splitLeft, [status(thm)], [c_67])).
% 3.91/1.68  tff(c_192, plain, (~r1_tarski(k1_xboole_0, k1_xboole_0)), inference(resolution, [status(thm)], [c_18, c_189])).
% 3.91/1.68  tff(c_196, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_8, c_192])).
% 3.91/1.68  tff(c_198, plain, (m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_xboole_0))), inference(splitRight, [status(thm)], [c_67])).
% 3.91/1.68  tff(c_14, plain, (![B_6]: (k2_zfmisc_1(k1_xboole_0, B_6)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.91/1.68  tff(c_50, plain, (![C_61, B_60]: (v1_funct_2(C_61, k1_xboole_0, B_60) | k1_relset_1(k1_xboole_0, B_60, C_61)!=k1_xboole_0 | ~m1_subset_1(C_61, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_60))))), inference(cnfTransformation, [status(thm)], [f_103])).
% 3.91/1.68  tff(c_316, plain, (![C_110, B_111]: (v1_funct_2(C_110, k1_xboole_0, B_111) | k1_relset_1(k1_xboole_0, B_111, C_110)!=k1_xboole_0 | ~m1_subset_1(C_110, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_50])).
% 3.91/1.68  tff(c_318, plain, (![B_111]: (v1_funct_2(k1_xboole_0, k1_xboole_0, B_111) | k1_relset_1(k1_xboole_0, B_111, k1_xboole_0)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_198, c_316])).
% 3.91/1.68  tff(c_323, plain, (![B_111]: (v1_funct_2(k1_xboole_0, k1_xboole_0, B_111) | k1_relat_1(k1_xboole_0)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_280, c_318])).
% 3.91/1.68  tff(c_330, plain, (k1_relat_1(k1_xboole_0)!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_323])).
% 3.91/1.68  tff(c_618, plain, (k1_relat_1('#skF_6')!='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_604, c_604, c_330])).
% 3.91/1.68  tff(c_197, plain, (![A_59]: (v1_funct_2(k1_xboole_0, A_59, k1_xboole_0) | k1_xboole_0=A_59)), inference(splitRight, [status(thm)], [c_67])).
% 3.91/1.68  tff(c_859, plain, (![A_175]: (v1_funct_2('#skF_6', A_175, '#skF_6') | A_175='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_604, c_604, c_604, c_197])).
% 3.91/1.68  tff(c_550, plain, (~v1_funct_2('#skF_6', k1_relat_1('#skF_6'), k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_548, c_104])).
% 3.91/1.68  tff(c_644, plain, (~v1_funct_2('#skF_6', k1_relat_1('#skF_6'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_604, c_550])).
% 3.91/1.68  tff(c_862, plain, (k1_relat_1('#skF_6')='#skF_6'), inference(resolution, [status(thm)], [c_859, c_644])).
% 3.91/1.68  tff(c_866, plain, $false, inference(negUnitSimplification, [status(thm)], [c_618, c_862])).
% 3.91/1.68  tff(c_867, plain, (![B_111]: (v1_funct_2(k1_xboole_0, k1_xboole_0, B_111))), inference(splitRight, [status(thm)], [c_323])).
% 3.91/1.68  tff(c_2008, plain, (![B_111]: (v1_funct_2('#skF_6', '#skF_6', B_111))), inference(demodulation, [status(thm), theory('equality')], [c_1986, c_1986, c_867])).
% 3.91/1.68  tff(c_868, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(splitRight, [status(thm)], [c_323])).
% 3.91/1.68  tff(c_2009, plain, (k1_relat_1('#skF_6')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_1986, c_1986, c_868])).
% 3.91/1.68  tff(c_1932, plain, (~v1_funct_2('#skF_6', k1_relat_1('#skF_6'), k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_1930, c_104])).
% 3.91/1.68  tff(c_2144, plain, (~v1_funct_2('#skF_6', '#skF_6', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_2009, c_1986, c_1932])).
% 3.91/1.68  tff(c_2185, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2008, c_2144])).
% 3.91/1.68  tff(c_2186, plain, (~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_6'), k2_relat_1('#skF_6'))))), inference(splitRight, [status(thm)], [c_64])).
% 3.91/1.68  tff(c_2204, plain, (~r1_tarski('#skF_6', k2_zfmisc_1(k1_relat_1('#skF_6'), k2_relat_1('#skF_6')))), inference(resolution, [status(thm)], [c_2196, c_2186])).
% 3.91/1.68  tff(c_2219, plain, (~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_2216, c_2204])).
% 3.91/1.68  tff(c_2223, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_62, c_2219])).
% 3.91/1.68  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.91/1.68  
% 3.91/1.68  Inference rules
% 3.91/1.68  ----------------------
% 3.91/1.68  #Ref     : 0
% 3.91/1.68  #Sup     : 404
% 3.91/1.68  #Fact    : 0
% 3.91/1.68  #Define  : 0
% 3.91/1.68  #Split   : 9
% 3.91/1.68  #Chain   : 0
% 3.91/1.68  #Close   : 0
% 3.91/1.68  
% 3.91/1.68  Ordering : KBO
% 3.91/1.68  
% 3.91/1.68  Simplification rules
% 3.91/1.68  ----------------------
% 3.91/1.68  #Subsume      : 54
% 3.91/1.68  #Demod        : 663
% 3.91/1.68  #Tautology    : 192
% 3.91/1.68  #SimpNegUnit  : 13
% 3.91/1.68  #BackRed      : 153
% 3.91/1.68  
% 3.91/1.68  #Partial instantiations: 0
% 3.91/1.68  #Strategies tried      : 1
% 3.91/1.68  
% 3.91/1.68  Timing (in seconds)
% 3.91/1.68  ----------------------
% 3.91/1.68  Preprocessing        : 0.33
% 3.91/1.68  Parsing              : 0.17
% 3.91/1.68  CNF conversion       : 0.03
% 3.91/1.68  Main loop            : 0.59
% 3.91/1.68  Inferencing          : 0.21
% 3.91/1.68  Reduction            : 0.18
% 3.91/1.68  Demodulation         : 0.13
% 3.91/1.68  BG Simplification    : 0.03
% 4.15/1.68  Subsumption          : 0.11
% 4.15/1.68  Abstraction          : 0.03
% 4.15/1.68  MUC search           : 0.00
% 4.15/1.68  Cooper               : 0.00
% 4.15/1.68  Total                : 0.95
% 4.15/1.68  Index Insertion      : 0.00
% 4.15/1.68  Index Deletion       : 0.00
% 4.15/1.68  Index Matching       : 0.00
% 4.15/1.68  BG Taut test         : 0.00
%------------------------------------------------------------------------------
