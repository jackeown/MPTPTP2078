%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:10:55 EST 2020

% Result     : Theorem 6.42s
% Output     : CNFRefutation 6.76s
% Verified   : 
% Statistics : Number of formulae       :  142 ( 710 expanded)
%              Number of leaves         :   35 ( 259 expanded)
%              Depth                    :   24
%              Number of atoms          :  310 (2022 expanded)
%              Number of equality atoms :   80 ( 417 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_6 > #skF_7 > #skF_3 > #skF_5 > #skF_8 > #skF_2 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_124,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_relat_1(B)
          & v1_funct_1(B) )
       => ( r1_tarski(k2_relat_1(B),A)
         => ( v1_funct_1(B)
            & v1_funct_2(B,k1_relat_1(B),A)
            & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B),A))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_funct_2)).

tff(f_38,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_93,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( ( r1_tarski(k1_relat_1(C),A)
          & r1_tarski(k2_relat_1(C),B) )
       => m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_relset_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_40,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_76,axiom,(
    ! [A,B] :
      ~ ( ~ ( A = k1_xboole_0
            & B != k1_xboole_0 )
        & ! [C] :
            ( ( v1_relat_1(C)
              & v1_funct_1(C) )
           => ~ ( B = k1_relat_1(C)
                & r1_tarski(k2_relat_1(C),A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_funct_1)).

tff(f_59,axiom,(
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

tff(f_81,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

tff(f_44,axiom,(
    ! [A] :
      ( r1_tarski(A,k1_xboole_0)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).

tff(f_85,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).

tff(c_76,plain,(
    v1_relat_1('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_12,plain,(
    ! [B_7] : r1_tarski(B_7,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_72,plain,(
    r1_tarski(k2_relat_1('#skF_8'),'#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_6296,plain,(
    ! [C_653,A_654,B_655] :
      ( m1_subset_1(C_653,k1_zfmisc_1(k2_zfmisc_1(A_654,B_655)))
      | ~ r1_tarski(k2_relat_1(C_653),B_655)
      | ~ r1_tarski(k1_relat_1(C_653),A_654)
      | ~ v1_relat_1(C_653) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_74,plain,(
    v1_funct_1('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_14,plain,(
    ! [A_8] : r1_tarski(k1_xboole_0,A_8) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_38,plain,(
    ! [A_50,B_51] :
      ( k1_xboole_0 = A_50
      | r1_tarski(k2_relat_1('#skF_6'(A_50,B_51)),A_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_193,plain,(
    ! [C_89,B_90,A_91] :
      ( r2_hidden(C_89,B_90)
      | ~ r2_hidden(C_89,A_91)
      | ~ r1_tarski(A_91,B_90) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_210,plain,(
    ! [A_94,B_95,B_96] :
      ( r2_hidden('#skF_1'(A_94,B_95),B_96)
      | ~ r1_tarski(A_94,B_96)
      | r1_tarski(A_94,B_95) ) ),
    inference(resolution,[status(thm)],[c_6,c_193])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_333,plain,(
    ! [A_121,B_122,B_123,B_124] :
      ( r2_hidden('#skF_1'(A_121,B_122),B_123)
      | ~ r1_tarski(B_124,B_123)
      | ~ r1_tarski(A_121,B_124)
      | r1_tarski(A_121,B_122) ) ),
    inference(resolution,[status(thm)],[c_210,c_2])).

tff(c_349,plain,(
    ! [A_125,B_126] :
      ( r2_hidden('#skF_1'(A_125,B_126),'#skF_7')
      | ~ r1_tarski(A_125,k2_relat_1('#skF_8'))
      | r1_tarski(A_125,B_126) ) ),
    inference(resolution,[status(thm)],[c_72,c_333])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_362,plain,(
    ! [A_127] :
      ( ~ r1_tarski(A_127,k2_relat_1('#skF_8'))
      | r1_tarski(A_127,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_349,c_4])).

tff(c_379,plain,(
    ! [B_51] :
      ( r1_tarski(k2_relat_1('#skF_6'(k2_relat_1('#skF_8'),B_51)),'#skF_7')
      | k2_relat_1('#skF_8') = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_38,c_362])).

tff(c_411,plain,(
    k2_relat_1('#skF_8') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_379])).

tff(c_287,plain,(
    ! [A_111,D_112] :
      ( r2_hidden(k1_funct_1(A_111,D_112),k2_relat_1(A_111))
      | ~ r2_hidden(D_112,k1_relat_1(A_111))
      | ~ v1_funct_1(A_111)
      | ~ v1_relat_1(A_111) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_52,plain,(
    ! [B_54,A_53] :
      ( ~ r1_tarski(B_54,A_53)
      | ~ r2_hidden(A_53,B_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_297,plain,(
    ! [A_111,D_112] :
      ( ~ r1_tarski(k2_relat_1(A_111),k1_funct_1(A_111,D_112))
      | ~ r2_hidden(D_112,k1_relat_1(A_111))
      | ~ v1_funct_1(A_111)
      | ~ v1_relat_1(A_111) ) ),
    inference(resolution,[status(thm)],[c_287,c_52])).

tff(c_425,plain,(
    ! [D_112] :
      ( ~ r1_tarski(k1_xboole_0,k1_funct_1('#skF_8',D_112))
      | ~ r2_hidden(D_112,k1_relat_1('#skF_8'))
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_411,c_297])).

tff(c_440,plain,(
    ! [D_130] : ~ r2_hidden(D_130,k1_relat_1('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_14,c_425])).

tff(c_451,plain,(
    ! [B_131] : r1_tarski(k1_relat_1('#skF_8'),B_131) ),
    inference(resolution,[status(thm)],[c_6,c_440])).

tff(c_16,plain,(
    ! [A_9] :
      ( k1_xboole_0 = A_9
      | ~ r1_tarski(A_9,k1_xboole_0) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_494,plain,(
    k1_relat_1('#skF_8') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_451,c_16])).

tff(c_503,plain,(
    ! [C_132,A_133,B_134] :
      ( m1_subset_1(C_132,k1_zfmisc_1(k2_zfmisc_1(A_133,B_134)))
      | ~ r1_tarski(k2_relat_1(C_132),B_134)
      | ~ r1_tarski(k1_relat_1(C_132),A_133)
      | ~ v1_relat_1(C_132) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_54,plain,(
    ! [A_55,B_56,C_57] :
      ( k1_relset_1(A_55,B_56,C_57) = k1_relat_1(C_57)
      | ~ m1_subset_1(C_57,k1_zfmisc_1(k2_zfmisc_1(A_55,B_56))) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_768,plain,(
    ! [A_156,B_157,C_158] :
      ( k1_relset_1(A_156,B_157,C_158) = k1_relat_1(C_158)
      | ~ r1_tarski(k2_relat_1(C_158),B_157)
      | ~ r1_tarski(k1_relat_1(C_158),A_156)
      | ~ v1_relat_1(C_158) ) ),
    inference(resolution,[status(thm)],[c_503,c_54])).

tff(c_772,plain,(
    ! [A_156,B_157] :
      ( k1_relset_1(A_156,B_157,'#skF_8') = k1_relat_1('#skF_8')
      | ~ r1_tarski(k1_xboole_0,B_157)
      | ~ r1_tarski(k1_relat_1('#skF_8'),A_156)
      | ~ v1_relat_1('#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_411,c_768])).

tff(c_781,plain,(
    ! [A_156,B_157] : k1_relset_1(A_156,B_157,'#skF_8') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_14,c_494,c_14,c_494,c_772])).

tff(c_62,plain,(
    ! [C_63,B_62] :
      ( v1_funct_2(C_63,k1_xboole_0,B_62)
      | k1_relset_1(k1_xboole_0,B_62,C_63) != k1_xboole_0
      | ~ m1_subset_1(C_63,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_62))) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_2219,plain,(
    ! [C_297,B_298] :
      ( v1_funct_2(C_297,k1_xboole_0,B_298)
      | k1_relset_1(k1_xboole_0,B_298,C_297) != k1_xboole_0
      | ~ r1_tarski(k2_relat_1(C_297),B_298)
      | ~ r1_tarski(k1_relat_1(C_297),k1_xboole_0)
      | ~ v1_relat_1(C_297) ) ),
    inference(resolution,[status(thm)],[c_503,c_62])).

tff(c_2228,plain,(
    ! [B_298] :
      ( v1_funct_2('#skF_8',k1_xboole_0,B_298)
      | k1_relset_1(k1_xboole_0,B_298,'#skF_8') != k1_xboole_0
      | ~ r1_tarski(k1_xboole_0,B_298)
      | ~ r1_tarski(k1_relat_1('#skF_8'),k1_xboole_0)
      | ~ v1_relat_1('#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_411,c_2219])).

tff(c_2240,plain,(
    ! [B_298] : v1_funct_2('#skF_8',k1_xboole_0,B_298) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_12,c_494,c_14,c_781,c_2228])).

tff(c_70,plain,
    ( ~ m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_8'),'#skF_7')))
    | ~ v1_funct_2('#skF_8',k1_relat_1('#skF_8'),'#skF_7')
    | ~ v1_funct_1('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_78,plain,
    ( ~ m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_8'),'#skF_7')))
    | ~ v1_funct_2('#skF_8',k1_relat_1('#skF_8'),'#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_70])).

tff(c_104,plain,(
    ~ v1_funct_2('#skF_8',k1_relat_1('#skF_8'),'#skF_7') ),
    inference(splitLeft,[status(thm)],[c_78])).

tff(c_497,plain,(
    ~ v1_funct_2('#skF_8',k1_xboole_0,'#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_494,c_104])).

tff(c_2245,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2240,c_497])).

tff(c_2247,plain,(
    k2_relat_1('#skF_8') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_379])).

tff(c_2305,plain,(
    ! [C_308,A_309,B_310] :
      ( m1_subset_1(C_308,k1_zfmisc_1(k2_zfmisc_1(A_309,B_310)))
      | ~ r1_tarski(k2_relat_1(C_308),B_310)
      | ~ r1_tarski(k1_relat_1(C_308),A_309)
      | ~ v1_relat_1(C_308) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_2650,plain,(
    ! [A_345,B_346,C_347] :
      ( k1_relset_1(A_345,B_346,C_347) = k1_relat_1(C_347)
      | ~ r1_tarski(k2_relat_1(C_347),B_346)
      | ~ r1_tarski(k1_relat_1(C_347),A_345)
      | ~ v1_relat_1(C_347) ) ),
    inference(resolution,[status(thm)],[c_2305,c_54])).

tff(c_2658,plain,(
    ! [A_345] :
      ( k1_relset_1(A_345,'#skF_7','#skF_8') = k1_relat_1('#skF_8')
      | ~ r1_tarski(k1_relat_1('#skF_8'),A_345)
      | ~ v1_relat_1('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_72,c_2650])).

tff(c_2677,plain,(
    ! [A_351] :
      ( k1_relset_1(A_351,'#skF_7','#skF_8') = k1_relat_1('#skF_8')
      | ~ r1_tarski(k1_relat_1('#skF_8'),A_351) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_2658])).

tff(c_2682,plain,(
    k1_relset_1(k1_relat_1('#skF_8'),'#skF_7','#skF_8') = k1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_12,c_2677])).

tff(c_56,plain,(
    ! [C_60,A_58,B_59] :
      ( m1_subset_1(C_60,k1_zfmisc_1(k2_zfmisc_1(A_58,B_59)))
      | ~ r1_tarski(k2_relat_1(C_60),B_59)
      | ~ r1_tarski(k1_relat_1(C_60),A_58)
      | ~ v1_relat_1(C_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_2802,plain,(
    ! [B_372,C_373,A_374] :
      ( k1_xboole_0 = B_372
      | v1_funct_2(C_373,A_374,B_372)
      | k1_relset_1(A_374,B_372,C_373) != A_374
      | ~ m1_subset_1(C_373,k1_zfmisc_1(k2_zfmisc_1(A_374,B_372))) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_5430,plain,(
    ! [B_550,C_551,A_552] :
      ( k1_xboole_0 = B_550
      | v1_funct_2(C_551,A_552,B_550)
      | k1_relset_1(A_552,B_550,C_551) != A_552
      | ~ r1_tarski(k2_relat_1(C_551),B_550)
      | ~ r1_tarski(k1_relat_1(C_551),A_552)
      | ~ v1_relat_1(C_551) ) ),
    inference(resolution,[status(thm)],[c_56,c_2802])).

tff(c_5452,plain,(
    ! [A_552] :
      ( k1_xboole_0 = '#skF_7'
      | v1_funct_2('#skF_8',A_552,'#skF_7')
      | k1_relset_1(A_552,'#skF_7','#skF_8') != A_552
      | ~ r1_tarski(k1_relat_1('#skF_8'),A_552)
      | ~ v1_relat_1('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_72,c_5430])).

tff(c_5471,plain,(
    ! [A_552] :
      ( k1_xboole_0 = '#skF_7'
      | v1_funct_2('#skF_8',A_552,'#skF_7')
      | k1_relset_1(A_552,'#skF_7','#skF_8') != A_552
      | ~ r1_tarski(k1_relat_1('#skF_8'),A_552) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_5452])).

tff(c_5486,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(splitLeft,[status(thm)],[c_5471])).

tff(c_46,plain,(
    ! [A_50,B_51] :
      ( k1_xboole_0 = A_50
      | v1_funct_1('#skF_6'(A_50,B_51)) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_50,plain,(
    ! [A_50,B_51] :
      ( k1_xboole_0 = A_50
      | v1_relat_1('#skF_6'(A_50,B_51)) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_42,plain,(
    ! [A_50,B_51] :
      ( k1_xboole_0 = A_50
      | k1_relat_1('#skF_6'(A_50,B_51)) = B_51 ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_2945,plain,(
    ! [A_395,B_396] :
      ( r2_hidden('#skF_3'(A_395,B_396),k1_relat_1(A_395))
      | r2_hidden('#skF_4'(A_395,B_396),B_396)
      | k2_relat_1(A_395) = B_396
      | ~ v1_funct_1(A_395)
      | ~ v1_relat_1(A_395) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_3413,plain,(
    ! [B_468,A_469] :
      ( ~ r1_tarski(B_468,'#skF_4'(A_469,B_468))
      | r2_hidden('#skF_3'(A_469,B_468),k1_relat_1(A_469))
      | k2_relat_1(A_469) = B_468
      | ~ v1_funct_1(A_469)
      | ~ v1_relat_1(A_469) ) ),
    inference(resolution,[status(thm)],[c_2945,c_52])).

tff(c_3418,plain,(
    ! [A_470] :
      ( r2_hidden('#skF_3'(A_470,k1_xboole_0),k1_relat_1(A_470))
      | k2_relat_1(A_470) = k1_xboole_0
      | ~ v1_funct_1(A_470)
      | ~ v1_relat_1(A_470) ) ),
    inference(resolution,[status(thm)],[c_14,c_3413])).

tff(c_3448,plain,(
    ! [A_472,B_473] :
      ( r2_hidden('#skF_3'(A_472,k1_xboole_0),B_473)
      | ~ r1_tarski(k1_relat_1(A_472),B_473)
      | k2_relat_1(A_472) = k1_xboole_0
      | ~ v1_funct_1(A_472)
      | ~ v1_relat_1(A_472) ) ),
    inference(resolution,[status(thm)],[c_3418,c_2])).

tff(c_48,plain,(
    ! [A_50] : v1_relat_1('#skF_6'(A_50,k1_xboole_0)) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_44,plain,(
    ! [A_50] : v1_funct_1('#skF_6'(A_50,k1_xboole_0)) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_40,plain,(
    ! [A_50] : k1_relat_1('#skF_6'(A_50,k1_xboole_0)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_105,plain,(
    ! [A_70] : r1_tarski(k2_relat_1('#skF_6'(A_70,k1_xboole_0)),A_70) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_110,plain,(
    k2_relat_1('#skF_6'(k1_xboole_0,k1_xboole_0)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_105,c_16])).

tff(c_295,plain,(
    ! [D_112] :
      ( r2_hidden(k1_funct_1('#skF_6'(k1_xboole_0,k1_xboole_0),D_112),k1_xboole_0)
      | ~ r2_hidden(D_112,k1_relat_1('#skF_6'(k1_xboole_0,k1_xboole_0)))
      | ~ v1_funct_1('#skF_6'(k1_xboole_0,k1_xboole_0))
      | ~ v1_relat_1('#skF_6'(k1_xboole_0,k1_xboole_0)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_110,c_287])).

tff(c_301,plain,(
    ! [D_115] :
      ( r2_hidden(k1_funct_1('#skF_6'(k1_xboole_0,k1_xboole_0),D_115),k1_xboole_0)
      | ~ r2_hidden(D_115,k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_44,c_40,c_295])).

tff(c_306,plain,(
    ! [D_115] :
      ( ~ r1_tarski(k1_xboole_0,k1_funct_1('#skF_6'(k1_xboole_0,k1_xboole_0),D_115))
      | ~ r2_hidden(D_115,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_301,c_52])).

tff(c_312,plain,(
    ! [D_115] : ~ r2_hidden(D_115,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_306])).

tff(c_3471,plain,(
    ! [A_474] :
      ( ~ r1_tarski(k1_relat_1(A_474),k1_xboole_0)
      | k2_relat_1(A_474) = k1_xboole_0
      | ~ v1_funct_1(A_474)
      | ~ v1_relat_1(A_474) ) ),
    inference(resolution,[status(thm)],[c_3448,c_312])).

tff(c_3523,plain,(
    ! [B_486,A_487] :
      ( ~ r1_tarski(B_486,k1_xboole_0)
      | k2_relat_1('#skF_6'(A_487,B_486)) = k1_xboole_0
      | ~ v1_funct_1('#skF_6'(A_487,B_486))
      | ~ v1_relat_1('#skF_6'(A_487,B_486))
      | k1_xboole_0 = A_487 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_3471])).

tff(c_3534,plain,(
    ! [B_488,A_489] :
      ( ~ r1_tarski(B_488,k1_xboole_0)
      | k2_relat_1('#skF_6'(A_489,B_488)) = k1_xboole_0
      | ~ v1_funct_1('#skF_6'(A_489,B_488))
      | k1_xboole_0 = A_489 ) ),
    inference(resolution,[status(thm)],[c_50,c_3523])).

tff(c_3546,plain,(
    ! [B_490,A_491] :
      ( ~ r1_tarski(B_490,k1_xboole_0)
      | k2_relat_1('#skF_6'(A_491,B_490)) = k1_xboole_0
      | k1_xboole_0 = A_491 ) ),
    inference(resolution,[status(thm)],[c_46,c_3534])).

tff(c_2246,plain,(
    ! [B_51] : r1_tarski(k2_relat_1('#skF_6'(k2_relat_1('#skF_8'),B_51)),'#skF_7') ),
    inference(splitRight,[status(thm)],[c_379])).

tff(c_2409,plain,(
    ! [A_328,C_329] :
      ( r2_hidden('#skF_5'(A_328,k2_relat_1(A_328),C_329),k1_relat_1(A_328))
      | ~ r2_hidden(C_329,k2_relat_1(A_328))
      | ~ v1_funct_1(A_328)
      | ~ v1_relat_1(A_328) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_2423,plain,(
    ! [A_50,C_329] :
      ( r2_hidden('#skF_5'('#skF_6'(A_50,k1_xboole_0),k2_relat_1('#skF_6'(A_50,k1_xboole_0)),C_329),k1_xboole_0)
      | ~ r2_hidden(C_329,k2_relat_1('#skF_6'(A_50,k1_xboole_0)))
      | ~ v1_funct_1('#skF_6'(A_50,k1_xboole_0))
      | ~ v1_relat_1('#skF_6'(A_50,k1_xboole_0)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_2409])).

tff(c_2430,plain,(
    ! [A_50,C_329] :
      ( r2_hidden('#skF_5'('#skF_6'(A_50,k1_xboole_0),k2_relat_1('#skF_6'(A_50,k1_xboole_0)),C_329),k1_xboole_0)
      | ~ r2_hidden(C_329,k2_relat_1('#skF_6'(A_50,k1_xboole_0))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_44,c_2423])).

tff(c_2432,plain,(
    ! [C_330,A_331] : ~ r2_hidden(C_330,k2_relat_1('#skF_6'(A_331,k1_xboole_0))) ),
    inference(negUnitSimplification,[status(thm)],[c_312,c_2430])).

tff(c_2465,plain,(
    ! [A_332,B_333] : r1_tarski(k2_relat_1('#skF_6'(A_332,k1_xboole_0)),B_333) ),
    inference(resolution,[status(thm)],[c_6,c_2432])).

tff(c_2543,plain,(
    ! [A_332] : k2_relat_1('#skF_6'(A_332,k1_xboole_0)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2465,c_16])).

tff(c_2974,plain,(
    ! [A_50,B_396] :
      ( r2_hidden('#skF_3'('#skF_6'(A_50,k1_xboole_0),B_396),k1_xboole_0)
      | r2_hidden('#skF_4'('#skF_6'(A_50,k1_xboole_0),B_396),B_396)
      | k2_relat_1('#skF_6'(A_50,k1_xboole_0)) = B_396
      | ~ v1_funct_1('#skF_6'(A_50,k1_xboole_0))
      | ~ v1_relat_1('#skF_6'(A_50,k1_xboole_0)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_2945])).

tff(c_2983,plain,(
    ! [A_50,B_396] :
      ( r2_hidden('#skF_3'('#skF_6'(A_50,k1_xboole_0),B_396),k1_xboole_0)
      | r2_hidden('#skF_4'('#skF_6'(A_50,k1_xboole_0),B_396),B_396)
      | k1_xboole_0 = B_396 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_44,c_2543,c_2974])).

tff(c_2985,plain,(
    ! [A_397,B_398] :
      ( r2_hidden('#skF_4'('#skF_6'(A_397,k1_xboole_0),B_398),B_398)
      | k1_xboole_0 = B_398 ) ),
    inference(negUnitSimplification,[status(thm)],[c_312,c_2983])).

tff(c_3029,plain,(
    ! [A_402,B_403,B_404] :
      ( r2_hidden('#skF_4'('#skF_6'(A_402,k1_xboole_0),B_403),B_404)
      | ~ r1_tarski(B_403,B_404)
      | k1_xboole_0 = B_403 ) ),
    inference(resolution,[status(thm)],[c_2985,c_2])).

tff(c_3169,plain,(
    ! [A_416,B_417,B_418,B_419] :
      ( r2_hidden('#skF_4'('#skF_6'(A_416,k1_xboole_0),B_417),B_418)
      | ~ r1_tarski(B_419,B_418)
      | ~ r1_tarski(B_417,B_419)
      | k1_xboole_0 = B_417 ) ),
    inference(resolution,[status(thm)],[c_3029,c_2])).

tff(c_3232,plain,(
    ! [A_431,B_432,B_433] :
      ( r2_hidden('#skF_4'('#skF_6'(A_431,k1_xboole_0),B_432),'#skF_7')
      | ~ r1_tarski(B_432,k2_relat_1('#skF_6'(k2_relat_1('#skF_8'),B_433)))
      | k1_xboole_0 = B_432 ) ),
    inference(resolution,[status(thm)],[c_2246,c_3169])).

tff(c_3245,plain,(
    ! [A_431,B_433] :
      ( r2_hidden('#skF_4'('#skF_6'(A_431,k1_xboole_0),k2_relat_1('#skF_6'(k2_relat_1('#skF_8'),B_433))),'#skF_7')
      | k2_relat_1('#skF_6'(k2_relat_1('#skF_8'),B_433)) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_12,c_3232])).

tff(c_3562,plain,(
    ! [A_431,B_490] :
      ( r2_hidden('#skF_4'('#skF_6'(A_431,k1_xboole_0),k1_xboole_0),'#skF_7')
      | k2_relat_1('#skF_6'(k2_relat_1('#skF_8'),B_490)) = k1_xboole_0
      | ~ r1_tarski(B_490,k1_xboole_0)
      | k2_relat_1('#skF_8') = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3546,c_3245])).

tff(c_3670,plain,(
    ! [A_431,B_490] :
      ( r2_hidden('#skF_4'('#skF_6'(A_431,k1_xboole_0),k1_xboole_0),'#skF_7')
      | k2_relat_1('#skF_6'(k2_relat_1('#skF_8'),B_490)) = k1_xboole_0
      | ~ r1_tarski(B_490,k1_xboole_0) ) ),
    inference(negUnitSimplification,[status(thm)],[c_2247,c_3562])).

tff(c_4817,plain,(
    ! [B_545] :
      ( k2_relat_1('#skF_6'(k2_relat_1('#skF_8'),B_545)) = k1_xboole_0
      | ~ r1_tarski(B_545,k1_xboole_0) ) ),
    inference(splitLeft,[status(thm)],[c_3670])).

tff(c_171,plain,(
    ! [A_85,B_86] :
      ( k1_xboole_0 = A_85
      | r1_tarski(k2_relat_1('#skF_6'(A_85,B_86)),A_85) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_8,plain,(
    ! [B_7,A_6] :
      ( B_7 = A_6
      | ~ r1_tarski(B_7,A_6)
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_181,plain,(
    ! [A_85,B_86] :
      ( k2_relat_1('#skF_6'(A_85,B_86)) = A_85
      | ~ r1_tarski(A_85,k2_relat_1('#skF_6'(A_85,B_86)))
      | k1_xboole_0 = A_85 ) ),
    inference(resolution,[status(thm)],[c_171,c_8])).

tff(c_4939,plain,(
    ! [B_545] :
      ( k2_relat_1('#skF_6'(k2_relat_1('#skF_8'),B_545)) = k2_relat_1('#skF_8')
      | ~ r1_tarski(k2_relat_1('#skF_8'),k1_xboole_0)
      | k2_relat_1('#skF_8') = k1_xboole_0
      | ~ r1_tarski(B_545,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4817,c_181])).

tff(c_5000,plain,(
    ! [B_545] :
      ( k2_relat_1('#skF_6'(k2_relat_1('#skF_8'),B_545)) = k2_relat_1('#skF_8')
      | ~ r1_tarski(k2_relat_1('#skF_8'),k1_xboole_0)
      | ~ r1_tarski(B_545,k1_xboole_0) ) ),
    inference(negUnitSimplification,[status(thm)],[c_2247,c_4939])).

tff(c_5009,plain,(
    ~ r1_tarski(k2_relat_1('#skF_8'),k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_5000])).

tff(c_5491,plain,(
    ~ r1_tarski(k2_relat_1('#skF_8'),'#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5486,c_5009])).

tff(c_5588,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_5491])).

tff(c_5591,plain,(
    ! [A_556] :
      ( v1_funct_2('#skF_8',A_556,'#skF_7')
      | k1_relset_1(A_556,'#skF_7','#skF_8') != A_556
      | ~ r1_tarski(k1_relat_1('#skF_8'),A_556) ) ),
    inference(splitRight,[status(thm)],[c_5471])).

tff(c_5595,plain,
    ( v1_funct_2('#skF_8',k1_relat_1('#skF_8'),'#skF_7')
    | k1_relset_1(k1_relat_1('#skF_8'),'#skF_7','#skF_8') != k1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_12,c_5591])).

tff(c_5598,plain,(
    v1_funct_2('#skF_8',k1_relat_1('#skF_8'),'#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2682,c_5595])).

tff(c_5600,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_104,c_5598])).

tff(c_5602,plain,(
    r1_tarski(k2_relat_1('#skF_8'),k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_5000])).

tff(c_5645,plain,
    ( k2_relat_1('#skF_8') = k1_xboole_0
    | ~ r1_tarski(k1_xboole_0,k2_relat_1('#skF_8')) ),
    inference(resolution,[status(thm)],[c_5602,c_8])).

tff(c_5700,plain,(
    k2_relat_1('#skF_8') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_5645])).

tff(c_5702,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2247,c_5700])).

tff(c_5703,plain,(
    ~ m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_8'),'#skF_7'))) ),
    inference(splitRight,[status(thm)],[c_78])).

tff(c_6318,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_8'),'#skF_7')
    | ~ r1_tarski(k1_relat_1('#skF_8'),k1_relat_1('#skF_8'))
    | ~ v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_6296,c_5703])).

tff(c_6327,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_12,c_72,c_6318])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n024.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 09:28:21 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.42/2.30  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.42/2.31  
% 6.42/2.31  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.76/2.31  %$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_6 > #skF_7 > #skF_3 > #skF_5 > #skF_8 > #skF_2 > #skF_1 > #skF_4
% 6.76/2.31  
% 6.76/2.31  %Foreground sorts:
% 6.76/2.31  
% 6.76/2.31  
% 6.76/2.31  %Background operators:
% 6.76/2.31  
% 6.76/2.31  
% 6.76/2.31  %Foreground operators:
% 6.76/2.31  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 6.76/2.31  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 6.76/2.31  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.76/2.31  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 6.76/2.31  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 6.76/2.31  tff('#skF_7', type, '#skF_7': $i).
% 6.76/2.31  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 6.76/2.31  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.76/2.31  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 6.76/2.31  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 6.76/2.31  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 6.76/2.31  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 6.76/2.31  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 6.76/2.31  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 6.76/2.31  tff('#skF_8', type, '#skF_8': $i).
% 6.76/2.31  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.76/2.31  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 6.76/2.31  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 6.76/2.31  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.76/2.31  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 6.76/2.31  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 6.76/2.31  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 6.76/2.31  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 6.76/2.31  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 6.76/2.31  
% 6.76/2.34  tff(f_124, negated_conjecture, ~(![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r1_tarski(k2_relat_1(B), A) => ((v1_funct_1(B) & v1_funct_2(B, k1_relat_1(B), A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B), A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_funct_2)).
% 6.76/2.34  tff(f_38, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 6.76/2.34  tff(f_93, axiom, (![A, B, C]: (v1_relat_1(C) => ((r1_tarski(k1_relat_1(C), A) & r1_tarski(k2_relat_1(C), B)) => m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_relset_1)).
% 6.76/2.34  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 6.76/2.34  tff(f_40, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 6.76/2.34  tff(f_76, axiom, (![A, B]: ~(~((A = k1_xboole_0) & ~(B = k1_xboole_0)) & (![C]: ((v1_relat_1(C) & v1_funct_1(C)) => ~((B = k1_relat_1(C)) & r1_tarski(k2_relat_1(C), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t18_funct_1)).
% 6.76/2.34  tff(f_59, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((B = k2_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: (r2_hidden(D, k1_relat_1(A)) & (C = k1_funct_1(A, D)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_funct_1)).
% 6.76/2.34  tff(f_81, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 6.76/2.34  tff(f_44, axiom, (![A]: (r1_tarski(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_1)).
% 6.76/2.34  tff(f_85, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 6.76/2.34  tff(f_111, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 6.76/2.34  tff(c_76, plain, (v1_relat_1('#skF_8')), inference(cnfTransformation, [status(thm)], [f_124])).
% 6.76/2.34  tff(c_12, plain, (![B_7]: (r1_tarski(B_7, B_7))), inference(cnfTransformation, [status(thm)], [f_38])).
% 6.76/2.34  tff(c_72, plain, (r1_tarski(k2_relat_1('#skF_8'), '#skF_7')), inference(cnfTransformation, [status(thm)], [f_124])).
% 6.76/2.34  tff(c_6296, plain, (![C_653, A_654, B_655]: (m1_subset_1(C_653, k1_zfmisc_1(k2_zfmisc_1(A_654, B_655))) | ~r1_tarski(k2_relat_1(C_653), B_655) | ~r1_tarski(k1_relat_1(C_653), A_654) | ~v1_relat_1(C_653))), inference(cnfTransformation, [status(thm)], [f_93])).
% 6.76/2.34  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 6.76/2.34  tff(c_74, plain, (v1_funct_1('#skF_8')), inference(cnfTransformation, [status(thm)], [f_124])).
% 6.76/2.34  tff(c_14, plain, (![A_8]: (r1_tarski(k1_xboole_0, A_8))), inference(cnfTransformation, [status(thm)], [f_40])).
% 6.76/2.34  tff(c_38, plain, (![A_50, B_51]: (k1_xboole_0=A_50 | r1_tarski(k2_relat_1('#skF_6'(A_50, B_51)), A_50))), inference(cnfTransformation, [status(thm)], [f_76])).
% 6.76/2.34  tff(c_193, plain, (![C_89, B_90, A_91]: (r2_hidden(C_89, B_90) | ~r2_hidden(C_89, A_91) | ~r1_tarski(A_91, B_90))), inference(cnfTransformation, [status(thm)], [f_32])).
% 6.76/2.34  tff(c_210, plain, (![A_94, B_95, B_96]: (r2_hidden('#skF_1'(A_94, B_95), B_96) | ~r1_tarski(A_94, B_96) | r1_tarski(A_94, B_95))), inference(resolution, [status(thm)], [c_6, c_193])).
% 6.76/2.34  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 6.76/2.34  tff(c_333, plain, (![A_121, B_122, B_123, B_124]: (r2_hidden('#skF_1'(A_121, B_122), B_123) | ~r1_tarski(B_124, B_123) | ~r1_tarski(A_121, B_124) | r1_tarski(A_121, B_122))), inference(resolution, [status(thm)], [c_210, c_2])).
% 6.76/2.34  tff(c_349, plain, (![A_125, B_126]: (r2_hidden('#skF_1'(A_125, B_126), '#skF_7') | ~r1_tarski(A_125, k2_relat_1('#skF_8')) | r1_tarski(A_125, B_126))), inference(resolution, [status(thm)], [c_72, c_333])).
% 6.76/2.34  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 6.76/2.34  tff(c_362, plain, (![A_127]: (~r1_tarski(A_127, k2_relat_1('#skF_8')) | r1_tarski(A_127, '#skF_7'))), inference(resolution, [status(thm)], [c_349, c_4])).
% 6.76/2.34  tff(c_379, plain, (![B_51]: (r1_tarski(k2_relat_1('#skF_6'(k2_relat_1('#skF_8'), B_51)), '#skF_7') | k2_relat_1('#skF_8')=k1_xboole_0)), inference(resolution, [status(thm)], [c_38, c_362])).
% 6.76/2.34  tff(c_411, plain, (k2_relat_1('#skF_8')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_379])).
% 6.76/2.34  tff(c_287, plain, (![A_111, D_112]: (r2_hidden(k1_funct_1(A_111, D_112), k2_relat_1(A_111)) | ~r2_hidden(D_112, k1_relat_1(A_111)) | ~v1_funct_1(A_111) | ~v1_relat_1(A_111))), inference(cnfTransformation, [status(thm)], [f_59])).
% 6.76/2.34  tff(c_52, plain, (![B_54, A_53]: (~r1_tarski(B_54, A_53) | ~r2_hidden(A_53, B_54))), inference(cnfTransformation, [status(thm)], [f_81])).
% 6.76/2.34  tff(c_297, plain, (![A_111, D_112]: (~r1_tarski(k2_relat_1(A_111), k1_funct_1(A_111, D_112)) | ~r2_hidden(D_112, k1_relat_1(A_111)) | ~v1_funct_1(A_111) | ~v1_relat_1(A_111))), inference(resolution, [status(thm)], [c_287, c_52])).
% 6.76/2.34  tff(c_425, plain, (![D_112]: (~r1_tarski(k1_xboole_0, k1_funct_1('#skF_8', D_112)) | ~r2_hidden(D_112, k1_relat_1('#skF_8')) | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_411, c_297])).
% 6.76/2.34  tff(c_440, plain, (![D_130]: (~r2_hidden(D_130, k1_relat_1('#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_74, c_14, c_425])).
% 6.76/2.34  tff(c_451, plain, (![B_131]: (r1_tarski(k1_relat_1('#skF_8'), B_131))), inference(resolution, [status(thm)], [c_6, c_440])).
% 6.76/2.34  tff(c_16, plain, (![A_9]: (k1_xboole_0=A_9 | ~r1_tarski(A_9, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_44])).
% 6.76/2.34  tff(c_494, plain, (k1_relat_1('#skF_8')=k1_xboole_0), inference(resolution, [status(thm)], [c_451, c_16])).
% 6.76/2.34  tff(c_503, plain, (![C_132, A_133, B_134]: (m1_subset_1(C_132, k1_zfmisc_1(k2_zfmisc_1(A_133, B_134))) | ~r1_tarski(k2_relat_1(C_132), B_134) | ~r1_tarski(k1_relat_1(C_132), A_133) | ~v1_relat_1(C_132))), inference(cnfTransformation, [status(thm)], [f_93])).
% 6.76/2.34  tff(c_54, plain, (![A_55, B_56, C_57]: (k1_relset_1(A_55, B_56, C_57)=k1_relat_1(C_57) | ~m1_subset_1(C_57, k1_zfmisc_1(k2_zfmisc_1(A_55, B_56))))), inference(cnfTransformation, [status(thm)], [f_85])).
% 6.76/2.34  tff(c_768, plain, (![A_156, B_157, C_158]: (k1_relset_1(A_156, B_157, C_158)=k1_relat_1(C_158) | ~r1_tarski(k2_relat_1(C_158), B_157) | ~r1_tarski(k1_relat_1(C_158), A_156) | ~v1_relat_1(C_158))), inference(resolution, [status(thm)], [c_503, c_54])).
% 6.76/2.34  tff(c_772, plain, (![A_156, B_157]: (k1_relset_1(A_156, B_157, '#skF_8')=k1_relat_1('#skF_8') | ~r1_tarski(k1_xboole_0, B_157) | ~r1_tarski(k1_relat_1('#skF_8'), A_156) | ~v1_relat_1('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_411, c_768])).
% 6.76/2.34  tff(c_781, plain, (![A_156, B_157]: (k1_relset_1(A_156, B_157, '#skF_8')=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_76, c_14, c_494, c_14, c_494, c_772])).
% 6.76/2.34  tff(c_62, plain, (![C_63, B_62]: (v1_funct_2(C_63, k1_xboole_0, B_62) | k1_relset_1(k1_xboole_0, B_62, C_63)!=k1_xboole_0 | ~m1_subset_1(C_63, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_62))))), inference(cnfTransformation, [status(thm)], [f_111])).
% 6.76/2.34  tff(c_2219, plain, (![C_297, B_298]: (v1_funct_2(C_297, k1_xboole_0, B_298) | k1_relset_1(k1_xboole_0, B_298, C_297)!=k1_xboole_0 | ~r1_tarski(k2_relat_1(C_297), B_298) | ~r1_tarski(k1_relat_1(C_297), k1_xboole_0) | ~v1_relat_1(C_297))), inference(resolution, [status(thm)], [c_503, c_62])).
% 6.76/2.34  tff(c_2228, plain, (![B_298]: (v1_funct_2('#skF_8', k1_xboole_0, B_298) | k1_relset_1(k1_xboole_0, B_298, '#skF_8')!=k1_xboole_0 | ~r1_tarski(k1_xboole_0, B_298) | ~r1_tarski(k1_relat_1('#skF_8'), k1_xboole_0) | ~v1_relat_1('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_411, c_2219])).
% 6.76/2.34  tff(c_2240, plain, (![B_298]: (v1_funct_2('#skF_8', k1_xboole_0, B_298))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_12, c_494, c_14, c_781, c_2228])).
% 6.76/2.34  tff(c_70, plain, (~m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_8'), '#skF_7'))) | ~v1_funct_2('#skF_8', k1_relat_1('#skF_8'), '#skF_7') | ~v1_funct_1('#skF_8')), inference(cnfTransformation, [status(thm)], [f_124])).
% 6.76/2.34  tff(c_78, plain, (~m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_8'), '#skF_7'))) | ~v1_funct_2('#skF_8', k1_relat_1('#skF_8'), '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_70])).
% 6.76/2.34  tff(c_104, plain, (~v1_funct_2('#skF_8', k1_relat_1('#skF_8'), '#skF_7')), inference(splitLeft, [status(thm)], [c_78])).
% 6.76/2.34  tff(c_497, plain, (~v1_funct_2('#skF_8', k1_xboole_0, '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_494, c_104])).
% 6.76/2.34  tff(c_2245, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2240, c_497])).
% 6.76/2.34  tff(c_2247, plain, (k2_relat_1('#skF_8')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_379])).
% 6.76/2.34  tff(c_2305, plain, (![C_308, A_309, B_310]: (m1_subset_1(C_308, k1_zfmisc_1(k2_zfmisc_1(A_309, B_310))) | ~r1_tarski(k2_relat_1(C_308), B_310) | ~r1_tarski(k1_relat_1(C_308), A_309) | ~v1_relat_1(C_308))), inference(cnfTransformation, [status(thm)], [f_93])).
% 6.76/2.34  tff(c_2650, plain, (![A_345, B_346, C_347]: (k1_relset_1(A_345, B_346, C_347)=k1_relat_1(C_347) | ~r1_tarski(k2_relat_1(C_347), B_346) | ~r1_tarski(k1_relat_1(C_347), A_345) | ~v1_relat_1(C_347))), inference(resolution, [status(thm)], [c_2305, c_54])).
% 6.76/2.34  tff(c_2658, plain, (![A_345]: (k1_relset_1(A_345, '#skF_7', '#skF_8')=k1_relat_1('#skF_8') | ~r1_tarski(k1_relat_1('#skF_8'), A_345) | ~v1_relat_1('#skF_8'))), inference(resolution, [status(thm)], [c_72, c_2650])).
% 6.76/2.34  tff(c_2677, plain, (![A_351]: (k1_relset_1(A_351, '#skF_7', '#skF_8')=k1_relat_1('#skF_8') | ~r1_tarski(k1_relat_1('#skF_8'), A_351))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_2658])).
% 6.76/2.34  tff(c_2682, plain, (k1_relset_1(k1_relat_1('#skF_8'), '#skF_7', '#skF_8')=k1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_12, c_2677])).
% 6.76/2.34  tff(c_56, plain, (![C_60, A_58, B_59]: (m1_subset_1(C_60, k1_zfmisc_1(k2_zfmisc_1(A_58, B_59))) | ~r1_tarski(k2_relat_1(C_60), B_59) | ~r1_tarski(k1_relat_1(C_60), A_58) | ~v1_relat_1(C_60))), inference(cnfTransformation, [status(thm)], [f_93])).
% 6.76/2.34  tff(c_2802, plain, (![B_372, C_373, A_374]: (k1_xboole_0=B_372 | v1_funct_2(C_373, A_374, B_372) | k1_relset_1(A_374, B_372, C_373)!=A_374 | ~m1_subset_1(C_373, k1_zfmisc_1(k2_zfmisc_1(A_374, B_372))))), inference(cnfTransformation, [status(thm)], [f_111])).
% 6.76/2.34  tff(c_5430, plain, (![B_550, C_551, A_552]: (k1_xboole_0=B_550 | v1_funct_2(C_551, A_552, B_550) | k1_relset_1(A_552, B_550, C_551)!=A_552 | ~r1_tarski(k2_relat_1(C_551), B_550) | ~r1_tarski(k1_relat_1(C_551), A_552) | ~v1_relat_1(C_551))), inference(resolution, [status(thm)], [c_56, c_2802])).
% 6.76/2.34  tff(c_5452, plain, (![A_552]: (k1_xboole_0='#skF_7' | v1_funct_2('#skF_8', A_552, '#skF_7') | k1_relset_1(A_552, '#skF_7', '#skF_8')!=A_552 | ~r1_tarski(k1_relat_1('#skF_8'), A_552) | ~v1_relat_1('#skF_8'))), inference(resolution, [status(thm)], [c_72, c_5430])).
% 6.76/2.34  tff(c_5471, plain, (![A_552]: (k1_xboole_0='#skF_7' | v1_funct_2('#skF_8', A_552, '#skF_7') | k1_relset_1(A_552, '#skF_7', '#skF_8')!=A_552 | ~r1_tarski(k1_relat_1('#skF_8'), A_552))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_5452])).
% 6.76/2.34  tff(c_5486, plain, (k1_xboole_0='#skF_7'), inference(splitLeft, [status(thm)], [c_5471])).
% 6.76/2.34  tff(c_46, plain, (![A_50, B_51]: (k1_xboole_0=A_50 | v1_funct_1('#skF_6'(A_50, B_51)))), inference(cnfTransformation, [status(thm)], [f_76])).
% 6.76/2.34  tff(c_50, plain, (![A_50, B_51]: (k1_xboole_0=A_50 | v1_relat_1('#skF_6'(A_50, B_51)))), inference(cnfTransformation, [status(thm)], [f_76])).
% 6.76/2.34  tff(c_42, plain, (![A_50, B_51]: (k1_xboole_0=A_50 | k1_relat_1('#skF_6'(A_50, B_51))=B_51)), inference(cnfTransformation, [status(thm)], [f_76])).
% 6.76/2.34  tff(c_2945, plain, (![A_395, B_396]: (r2_hidden('#skF_3'(A_395, B_396), k1_relat_1(A_395)) | r2_hidden('#skF_4'(A_395, B_396), B_396) | k2_relat_1(A_395)=B_396 | ~v1_funct_1(A_395) | ~v1_relat_1(A_395))), inference(cnfTransformation, [status(thm)], [f_59])).
% 6.76/2.34  tff(c_3413, plain, (![B_468, A_469]: (~r1_tarski(B_468, '#skF_4'(A_469, B_468)) | r2_hidden('#skF_3'(A_469, B_468), k1_relat_1(A_469)) | k2_relat_1(A_469)=B_468 | ~v1_funct_1(A_469) | ~v1_relat_1(A_469))), inference(resolution, [status(thm)], [c_2945, c_52])).
% 6.76/2.34  tff(c_3418, plain, (![A_470]: (r2_hidden('#skF_3'(A_470, k1_xboole_0), k1_relat_1(A_470)) | k2_relat_1(A_470)=k1_xboole_0 | ~v1_funct_1(A_470) | ~v1_relat_1(A_470))), inference(resolution, [status(thm)], [c_14, c_3413])).
% 6.76/2.34  tff(c_3448, plain, (![A_472, B_473]: (r2_hidden('#skF_3'(A_472, k1_xboole_0), B_473) | ~r1_tarski(k1_relat_1(A_472), B_473) | k2_relat_1(A_472)=k1_xboole_0 | ~v1_funct_1(A_472) | ~v1_relat_1(A_472))), inference(resolution, [status(thm)], [c_3418, c_2])).
% 6.76/2.34  tff(c_48, plain, (![A_50]: (v1_relat_1('#skF_6'(A_50, k1_xboole_0)))), inference(cnfTransformation, [status(thm)], [f_76])).
% 6.76/2.34  tff(c_44, plain, (![A_50]: (v1_funct_1('#skF_6'(A_50, k1_xboole_0)))), inference(cnfTransformation, [status(thm)], [f_76])).
% 6.76/2.34  tff(c_40, plain, (![A_50]: (k1_relat_1('#skF_6'(A_50, k1_xboole_0))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_76])).
% 6.76/2.34  tff(c_105, plain, (![A_70]: (r1_tarski(k2_relat_1('#skF_6'(A_70, k1_xboole_0)), A_70))), inference(cnfTransformation, [status(thm)], [f_76])).
% 6.76/2.34  tff(c_110, plain, (k2_relat_1('#skF_6'(k1_xboole_0, k1_xboole_0))=k1_xboole_0), inference(resolution, [status(thm)], [c_105, c_16])).
% 6.76/2.34  tff(c_295, plain, (![D_112]: (r2_hidden(k1_funct_1('#skF_6'(k1_xboole_0, k1_xboole_0), D_112), k1_xboole_0) | ~r2_hidden(D_112, k1_relat_1('#skF_6'(k1_xboole_0, k1_xboole_0))) | ~v1_funct_1('#skF_6'(k1_xboole_0, k1_xboole_0)) | ~v1_relat_1('#skF_6'(k1_xboole_0, k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_110, c_287])).
% 6.76/2.34  tff(c_301, plain, (![D_115]: (r2_hidden(k1_funct_1('#skF_6'(k1_xboole_0, k1_xboole_0), D_115), k1_xboole_0) | ~r2_hidden(D_115, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_44, c_40, c_295])).
% 6.76/2.34  tff(c_306, plain, (![D_115]: (~r1_tarski(k1_xboole_0, k1_funct_1('#skF_6'(k1_xboole_0, k1_xboole_0), D_115)) | ~r2_hidden(D_115, k1_xboole_0))), inference(resolution, [status(thm)], [c_301, c_52])).
% 6.76/2.34  tff(c_312, plain, (![D_115]: (~r2_hidden(D_115, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_306])).
% 6.76/2.34  tff(c_3471, plain, (![A_474]: (~r1_tarski(k1_relat_1(A_474), k1_xboole_0) | k2_relat_1(A_474)=k1_xboole_0 | ~v1_funct_1(A_474) | ~v1_relat_1(A_474))), inference(resolution, [status(thm)], [c_3448, c_312])).
% 6.76/2.34  tff(c_3523, plain, (![B_486, A_487]: (~r1_tarski(B_486, k1_xboole_0) | k2_relat_1('#skF_6'(A_487, B_486))=k1_xboole_0 | ~v1_funct_1('#skF_6'(A_487, B_486)) | ~v1_relat_1('#skF_6'(A_487, B_486)) | k1_xboole_0=A_487)), inference(superposition, [status(thm), theory('equality')], [c_42, c_3471])).
% 6.76/2.34  tff(c_3534, plain, (![B_488, A_489]: (~r1_tarski(B_488, k1_xboole_0) | k2_relat_1('#skF_6'(A_489, B_488))=k1_xboole_0 | ~v1_funct_1('#skF_6'(A_489, B_488)) | k1_xboole_0=A_489)), inference(resolution, [status(thm)], [c_50, c_3523])).
% 6.76/2.34  tff(c_3546, plain, (![B_490, A_491]: (~r1_tarski(B_490, k1_xboole_0) | k2_relat_1('#skF_6'(A_491, B_490))=k1_xboole_0 | k1_xboole_0=A_491)), inference(resolution, [status(thm)], [c_46, c_3534])).
% 6.76/2.34  tff(c_2246, plain, (![B_51]: (r1_tarski(k2_relat_1('#skF_6'(k2_relat_1('#skF_8'), B_51)), '#skF_7'))), inference(splitRight, [status(thm)], [c_379])).
% 6.76/2.34  tff(c_2409, plain, (![A_328, C_329]: (r2_hidden('#skF_5'(A_328, k2_relat_1(A_328), C_329), k1_relat_1(A_328)) | ~r2_hidden(C_329, k2_relat_1(A_328)) | ~v1_funct_1(A_328) | ~v1_relat_1(A_328))), inference(cnfTransformation, [status(thm)], [f_59])).
% 6.76/2.34  tff(c_2423, plain, (![A_50, C_329]: (r2_hidden('#skF_5'('#skF_6'(A_50, k1_xboole_0), k2_relat_1('#skF_6'(A_50, k1_xboole_0)), C_329), k1_xboole_0) | ~r2_hidden(C_329, k2_relat_1('#skF_6'(A_50, k1_xboole_0))) | ~v1_funct_1('#skF_6'(A_50, k1_xboole_0)) | ~v1_relat_1('#skF_6'(A_50, k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_40, c_2409])).
% 6.76/2.34  tff(c_2430, plain, (![A_50, C_329]: (r2_hidden('#skF_5'('#skF_6'(A_50, k1_xboole_0), k2_relat_1('#skF_6'(A_50, k1_xboole_0)), C_329), k1_xboole_0) | ~r2_hidden(C_329, k2_relat_1('#skF_6'(A_50, k1_xboole_0))))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_44, c_2423])).
% 6.76/2.34  tff(c_2432, plain, (![C_330, A_331]: (~r2_hidden(C_330, k2_relat_1('#skF_6'(A_331, k1_xboole_0))))), inference(negUnitSimplification, [status(thm)], [c_312, c_2430])).
% 6.76/2.34  tff(c_2465, plain, (![A_332, B_333]: (r1_tarski(k2_relat_1('#skF_6'(A_332, k1_xboole_0)), B_333))), inference(resolution, [status(thm)], [c_6, c_2432])).
% 6.76/2.34  tff(c_2543, plain, (![A_332]: (k2_relat_1('#skF_6'(A_332, k1_xboole_0))=k1_xboole_0)), inference(resolution, [status(thm)], [c_2465, c_16])).
% 6.76/2.34  tff(c_2974, plain, (![A_50, B_396]: (r2_hidden('#skF_3'('#skF_6'(A_50, k1_xboole_0), B_396), k1_xboole_0) | r2_hidden('#skF_4'('#skF_6'(A_50, k1_xboole_0), B_396), B_396) | k2_relat_1('#skF_6'(A_50, k1_xboole_0))=B_396 | ~v1_funct_1('#skF_6'(A_50, k1_xboole_0)) | ~v1_relat_1('#skF_6'(A_50, k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_40, c_2945])).
% 6.76/2.34  tff(c_2983, plain, (![A_50, B_396]: (r2_hidden('#skF_3'('#skF_6'(A_50, k1_xboole_0), B_396), k1_xboole_0) | r2_hidden('#skF_4'('#skF_6'(A_50, k1_xboole_0), B_396), B_396) | k1_xboole_0=B_396)), inference(demodulation, [status(thm), theory('equality')], [c_48, c_44, c_2543, c_2974])).
% 6.76/2.34  tff(c_2985, plain, (![A_397, B_398]: (r2_hidden('#skF_4'('#skF_6'(A_397, k1_xboole_0), B_398), B_398) | k1_xboole_0=B_398)), inference(negUnitSimplification, [status(thm)], [c_312, c_2983])).
% 6.76/2.34  tff(c_3029, plain, (![A_402, B_403, B_404]: (r2_hidden('#skF_4'('#skF_6'(A_402, k1_xboole_0), B_403), B_404) | ~r1_tarski(B_403, B_404) | k1_xboole_0=B_403)), inference(resolution, [status(thm)], [c_2985, c_2])).
% 6.76/2.34  tff(c_3169, plain, (![A_416, B_417, B_418, B_419]: (r2_hidden('#skF_4'('#skF_6'(A_416, k1_xboole_0), B_417), B_418) | ~r1_tarski(B_419, B_418) | ~r1_tarski(B_417, B_419) | k1_xboole_0=B_417)), inference(resolution, [status(thm)], [c_3029, c_2])).
% 6.76/2.34  tff(c_3232, plain, (![A_431, B_432, B_433]: (r2_hidden('#skF_4'('#skF_6'(A_431, k1_xboole_0), B_432), '#skF_7') | ~r1_tarski(B_432, k2_relat_1('#skF_6'(k2_relat_1('#skF_8'), B_433))) | k1_xboole_0=B_432)), inference(resolution, [status(thm)], [c_2246, c_3169])).
% 6.76/2.34  tff(c_3245, plain, (![A_431, B_433]: (r2_hidden('#skF_4'('#skF_6'(A_431, k1_xboole_0), k2_relat_1('#skF_6'(k2_relat_1('#skF_8'), B_433))), '#skF_7') | k2_relat_1('#skF_6'(k2_relat_1('#skF_8'), B_433))=k1_xboole_0)), inference(resolution, [status(thm)], [c_12, c_3232])).
% 6.76/2.34  tff(c_3562, plain, (![A_431, B_490]: (r2_hidden('#skF_4'('#skF_6'(A_431, k1_xboole_0), k1_xboole_0), '#skF_7') | k2_relat_1('#skF_6'(k2_relat_1('#skF_8'), B_490))=k1_xboole_0 | ~r1_tarski(B_490, k1_xboole_0) | k2_relat_1('#skF_8')=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_3546, c_3245])).
% 6.76/2.34  tff(c_3670, plain, (![A_431, B_490]: (r2_hidden('#skF_4'('#skF_6'(A_431, k1_xboole_0), k1_xboole_0), '#skF_7') | k2_relat_1('#skF_6'(k2_relat_1('#skF_8'), B_490))=k1_xboole_0 | ~r1_tarski(B_490, k1_xboole_0))), inference(negUnitSimplification, [status(thm)], [c_2247, c_3562])).
% 6.76/2.34  tff(c_4817, plain, (![B_545]: (k2_relat_1('#skF_6'(k2_relat_1('#skF_8'), B_545))=k1_xboole_0 | ~r1_tarski(B_545, k1_xboole_0))), inference(splitLeft, [status(thm)], [c_3670])).
% 6.76/2.34  tff(c_171, plain, (![A_85, B_86]: (k1_xboole_0=A_85 | r1_tarski(k2_relat_1('#skF_6'(A_85, B_86)), A_85))), inference(cnfTransformation, [status(thm)], [f_76])).
% 6.76/2.34  tff(c_8, plain, (![B_7, A_6]: (B_7=A_6 | ~r1_tarski(B_7, A_6) | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_38])).
% 6.76/2.34  tff(c_181, plain, (![A_85, B_86]: (k2_relat_1('#skF_6'(A_85, B_86))=A_85 | ~r1_tarski(A_85, k2_relat_1('#skF_6'(A_85, B_86))) | k1_xboole_0=A_85)), inference(resolution, [status(thm)], [c_171, c_8])).
% 6.76/2.34  tff(c_4939, plain, (![B_545]: (k2_relat_1('#skF_6'(k2_relat_1('#skF_8'), B_545))=k2_relat_1('#skF_8') | ~r1_tarski(k2_relat_1('#skF_8'), k1_xboole_0) | k2_relat_1('#skF_8')=k1_xboole_0 | ~r1_tarski(B_545, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_4817, c_181])).
% 6.76/2.34  tff(c_5000, plain, (![B_545]: (k2_relat_1('#skF_6'(k2_relat_1('#skF_8'), B_545))=k2_relat_1('#skF_8') | ~r1_tarski(k2_relat_1('#skF_8'), k1_xboole_0) | ~r1_tarski(B_545, k1_xboole_0))), inference(negUnitSimplification, [status(thm)], [c_2247, c_4939])).
% 6.76/2.34  tff(c_5009, plain, (~r1_tarski(k2_relat_1('#skF_8'), k1_xboole_0)), inference(splitLeft, [status(thm)], [c_5000])).
% 6.76/2.34  tff(c_5491, plain, (~r1_tarski(k2_relat_1('#skF_8'), '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_5486, c_5009])).
% 6.76/2.34  tff(c_5588, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_72, c_5491])).
% 6.76/2.34  tff(c_5591, plain, (![A_556]: (v1_funct_2('#skF_8', A_556, '#skF_7') | k1_relset_1(A_556, '#skF_7', '#skF_8')!=A_556 | ~r1_tarski(k1_relat_1('#skF_8'), A_556))), inference(splitRight, [status(thm)], [c_5471])).
% 6.76/2.34  tff(c_5595, plain, (v1_funct_2('#skF_8', k1_relat_1('#skF_8'), '#skF_7') | k1_relset_1(k1_relat_1('#skF_8'), '#skF_7', '#skF_8')!=k1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_12, c_5591])).
% 6.76/2.34  tff(c_5598, plain, (v1_funct_2('#skF_8', k1_relat_1('#skF_8'), '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_2682, c_5595])).
% 6.76/2.34  tff(c_5600, plain, $false, inference(negUnitSimplification, [status(thm)], [c_104, c_5598])).
% 6.76/2.34  tff(c_5602, plain, (r1_tarski(k2_relat_1('#skF_8'), k1_xboole_0)), inference(splitRight, [status(thm)], [c_5000])).
% 6.76/2.34  tff(c_5645, plain, (k2_relat_1('#skF_8')=k1_xboole_0 | ~r1_tarski(k1_xboole_0, k2_relat_1('#skF_8'))), inference(resolution, [status(thm)], [c_5602, c_8])).
% 6.76/2.34  tff(c_5700, plain, (k2_relat_1('#skF_8')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_14, c_5645])).
% 6.76/2.34  tff(c_5702, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2247, c_5700])).
% 6.76/2.34  tff(c_5703, plain, (~m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_8'), '#skF_7')))), inference(splitRight, [status(thm)], [c_78])).
% 6.76/2.34  tff(c_6318, plain, (~r1_tarski(k2_relat_1('#skF_8'), '#skF_7') | ~r1_tarski(k1_relat_1('#skF_8'), k1_relat_1('#skF_8')) | ~v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_6296, c_5703])).
% 6.76/2.34  tff(c_6327, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_76, c_12, c_72, c_6318])).
% 6.76/2.34  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.76/2.34  
% 6.76/2.34  Inference rules
% 6.76/2.34  ----------------------
% 6.76/2.34  #Ref     : 0
% 6.76/2.34  #Sup     : 1324
% 6.76/2.34  #Fact    : 0
% 6.76/2.34  #Define  : 0
% 6.76/2.34  #Split   : 20
% 6.76/2.34  #Chain   : 0
% 6.76/2.34  #Close   : 0
% 6.76/2.34  
% 6.76/2.34  Ordering : KBO
% 6.76/2.34  
% 6.76/2.34  Simplification rules
% 6.76/2.34  ----------------------
% 6.76/2.34  #Subsume      : 398
% 6.76/2.34  #Demod        : 1130
% 6.76/2.34  #Tautology    : 303
% 6.76/2.34  #SimpNegUnit  : 63
% 6.76/2.34  #BackRed      : 191
% 6.76/2.34  
% 6.76/2.34  #Partial instantiations: 0
% 6.76/2.34  #Strategies tried      : 1
% 6.76/2.34  
% 6.76/2.34  Timing (in seconds)
% 6.76/2.34  ----------------------
% 6.76/2.34  Preprocessing        : 0.34
% 6.76/2.34  Parsing              : 0.18
% 6.76/2.34  CNF conversion       : 0.03
% 6.76/2.34  Main loop            : 1.27
% 6.76/2.34  Inferencing          : 0.40
% 6.76/2.34  Reduction            : 0.38
% 6.76/2.34  Demodulation         : 0.25
% 6.76/2.34  BG Simplification    : 0.05
% 6.76/2.34  Subsumption          : 0.35
% 6.76/2.34  Abstraction          : 0.06
% 6.76/2.34  MUC search           : 0.00
% 6.76/2.34  Cooper               : 0.00
% 6.76/2.34  Total                : 1.66
% 6.76/2.34  Index Insertion      : 0.00
% 6.76/2.34  Index Deletion       : 0.00
% 6.76/2.34  Index Matching       : 0.00
% 6.76/2.34  BG Taut test         : 0.00
%------------------------------------------------------------------------------
