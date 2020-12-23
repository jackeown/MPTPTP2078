%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:10:51 EST 2020

% Result     : Theorem 6.12s
% Output     : CNFRefutation 6.45s
% Verified   : 
% Statistics : Number of formulae       :  118 ( 313 expanded)
%              Number of leaves         :   43 ( 121 expanded)
%              Depth                    :   11
%              Number of atoms          :  221 ( 812 expanded)
%              Number of equality atoms :   46 ( 108 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v1_partfun1 > r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k9_relat_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k3_tarski > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > np__1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(np__1,type,(
    np__1: $i )).

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

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff(v1_partfun1,type,(
    v1_partfun1: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_160,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_relat_1(B)
          & v1_funct_1(B) )
       => ( r1_tarski(k2_relat_1(B),A)
         => ( v1_funct_1(B)
            & v1_funct_2(B,k1_relat_1(B),A)
            & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B),A))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_funct_2)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_112,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( ( r1_tarski(k1_relat_1(C),A)
          & r1_tarski(k2_relat_1(C),B) )
       => m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_relset_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_104,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_147,axiom,(
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

tff(f_100,axiom,(
    ! [A] :
    ? [B] :
      ( v1_relat_1(B)
      & v1_funct_1(B)
      & k1_relat_1(B) = A
      & ! [C] :
          ( r2_hidden(C,A)
         => k1_funct_1(B,C) = np__1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',s3_funct_1__e7_25__funct_1)).

tff(f_82,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ( k1_relat_1(A) = k1_xboole_0
          | k2_relat_1(A) = k1_xboole_0 )
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).

tff(f_74,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(A,B)
           => ( r1_tarski(k1_relat_1(A),k1_relat_1(B))
              & r1_tarski(k2_relat_1(A),k2_relat_1(B)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_relat_1)).

tff(f_55,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k9_relat_1(A,k1_xboole_0) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t149_relat_1)).

tff(f_61,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( k9_relat_1(B,A) = k1_xboole_0
      <=> r1_xboole_0(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t151_relat_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ~ ( r1_tarski(B,A)
          & r1_xboole_0(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_xboole_1)).

tff(f_129,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => v1_partfun1(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_partfun1)).

tff(f_63,axiom,(
    ! [A,B] : r1_tarski(k2_relat_1(k2_zfmisc_1(A,B)),B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t194_relat_1)).

tff(f_35,axiom,(
    ! [A] :
      ( r1_tarski(A,k1_xboole_0)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).

tff(f_51,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_45,axiom,(
    ! [A] : r1_tarski(A,k1_zfmisc_1(k3_tarski(A))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_zfmisc_1)).

tff(f_122,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( ( v1_funct_1(C)
          & v1_partfun1(C,A) )
       => ( v1_funct_1(C)
          & v1_funct_2(C,A,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_funct_2)).

tff(c_76,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_72,plain,(
    r1_tarski(k2_relat_1('#skF_3'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_5768,plain,(
    ! [C_445,A_446,B_447] :
      ( m1_subset_1(C_445,k1_zfmisc_1(k2_zfmisc_1(A_446,B_447)))
      | ~ r1_tarski(k2_relat_1(C_445),B_447)
      | ~ r1_tarski(k1_relat_1(C_445),A_446)
      | ~ v1_relat_1(C_445) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_74,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_70,plain,
    ( ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),'#skF_2')))
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),'#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_78,plain,
    ( ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),'#skF_2')))
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_70])).

tff(c_100,plain,(
    ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_78])).

tff(c_1030,plain,(
    ! [C_152,A_153,B_154] :
      ( m1_subset_1(C_152,k1_zfmisc_1(k2_zfmisc_1(A_153,B_154)))
      | ~ r1_tarski(k2_relat_1(C_152),B_154)
      | ~ r1_tarski(k1_relat_1(C_152),A_153)
      | ~ v1_relat_1(C_152) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_14,plain,(
    ! [A_7,B_8] :
      ( r1_tarski(A_7,B_8)
      | ~ m1_subset_1(A_7,k1_zfmisc_1(B_8)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_3207,plain,(
    ! [C_282,A_283,B_284] :
      ( r1_tarski(C_282,k2_zfmisc_1(A_283,B_284))
      | ~ r1_tarski(k2_relat_1(C_282),B_284)
      | ~ r1_tarski(k1_relat_1(C_282),A_283)
      | ~ v1_relat_1(C_282) ) ),
    inference(resolution,[status(thm)],[c_1030,c_14])).

tff(c_3261,plain,(
    ! [A_283] :
      ( r1_tarski('#skF_3',k2_zfmisc_1(A_283,'#skF_2'))
      | ~ r1_tarski(k1_relat_1('#skF_3'),A_283)
      | ~ v1_relat_1('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_72,c_3207])).

tff(c_3304,plain,(
    ! [A_285] :
      ( r1_tarski('#skF_3',k2_zfmisc_1(A_285,'#skF_2'))
      | ~ r1_tarski(k1_relat_1('#skF_3'),A_285) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_3261])).

tff(c_3373,plain,(
    r1_tarski('#skF_3',k2_zfmisc_1(k1_relat_1('#skF_3'),'#skF_2')) ),
    inference(resolution,[status(thm)],[c_6,c_3304])).

tff(c_16,plain,(
    ! [A_7,B_8] :
      ( m1_subset_1(A_7,k1_zfmisc_1(B_8))
      | ~ r1_tarski(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_595,plain,(
    ! [A_113,B_114,C_115] :
      ( k1_relset_1(A_113,B_114,C_115) = k1_relat_1(C_115)
      | ~ m1_subset_1(C_115,k1_zfmisc_1(k2_zfmisc_1(A_113,B_114))) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_603,plain,(
    ! [A_113,B_114,A_7] :
      ( k1_relset_1(A_113,B_114,A_7) = k1_relat_1(A_7)
      | ~ r1_tarski(A_7,k2_zfmisc_1(A_113,B_114)) ) ),
    inference(resolution,[status(thm)],[c_16,c_595])).

tff(c_3389,plain,(
    k1_relset_1(k1_relat_1('#skF_3'),'#skF_2','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_3373,c_603])).

tff(c_1129,plain,(
    ! [B_157,C_158,A_159] :
      ( k1_xboole_0 = B_157
      | v1_funct_2(C_158,A_159,B_157)
      | k1_relset_1(A_159,B_157,C_158) != A_159
      | ~ m1_subset_1(C_158,k1_zfmisc_1(k2_zfmisc_1(A_159,B_157))) ) ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_4118,plain,(
    ! [B_316,A_317,A_318] :
      ( k1_xboole_0 = B_316
      | v1_funct_2(A_317,A_318,B_316)
      | k1_relset_1(A_318,B_316,A_317) != A_318
      | ~ r1_tarski(A_317,k2_zfmisc_1(A_318,B_316)) ) ),
    inference(resolution,[status(thm)],[c_16,c_1129])).

tff(c_4127,plain,
    ( k1_xboole_0 = '#skF_2'
    | v1_funct_2('#skF_3',k1_relat_1('#skF_3'),'#skF_2')
    | k1_relset_1(k1_relat_1('#skF_3'),'#skF_2','#skF_3') != k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_3373,c_4118])).

tff(c_4164,plain,
    ( k1_xboole_0 = '#skF_2'
    | v1_funct_2('#skF_3',k1_relat_1('#skF_3'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3389,c_4127])).

tff(c_4165,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_100,c_4164])).

tff(c_42,plain,(
    ! [A_21] : k1_relat_1('#skF_1'(A_21)) = A_21 ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_46,plain,(
    ! [A_21] : v1_relat_1('#skF_1'(A_21)) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_170,plain,(
    ! [A_63] :
      ( k1_relat_1(A_63) != k1_xboole_0
      | k1_xboole_0 = A_63
      | ~ v1_relat_1(A_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_176,plain,(
    ! [A_21] :
      ( k1_relat_1('#skF_1'(A_21)) != k1_xboole_0
      | '#skF_1'(A_21) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_46,c_170])).

tff(c_184,plain,(
    '#skF_1'(k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_176])).

tff(c_529,plain,(
    ! [A_103,B_104] :
      ( r1_tarski(k1_relat_1(A_103),k1_relat_1(B_104))
      | ~ r1_tarski(A_103,B_104)
      | ~ v1_relat_1(B_104)
      | ~ v1_relat_1(A_103) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_537,plain,(
    ! [A_103,A_21] :
      ( r1_tarski(k1_relat_1(A_103),A_21)
      | ~ r1_tarski(A_103,'#skF_1'(A_21))
      | ~ v1_relat_1('#skF_1'(A_21))
      | ~ v1_relat_1(A_103) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_529])).

tff(c_553,plain,(
    ! [A_110,A_111] :
      ( r1_tarski(k1_relat_1(A_110),A_111)
      | ~ r1_tarski(A_110,'#skF_1'(A_111))
      | ~ v1_relat_1(A_110) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_537])).

tff(c_102,plain,(
    ! [A_51] :
      ( k9_relat_1(A_51,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(A_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_113,plain,(
    ! [A_21] : k9_relat_1('#skF_1'(A_21),k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_46,c_102])).

tff(c_426,plain,(
    ! [B_87,A_88] :
      ( r1_xboole_0(k1_relat_1(B_87),A_88)
      | k9_relat_1(B_87,A_88) != k1_xboole_0
      | ~ v1_relat_1(B_87) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_435,plain,(
    ! [A_21,A_88] :
      ( r1_xboole_0(A_21,A_88)
      | k9_relat_1('#skF_1'(A_21),A_88) != k1_xboole_0
      | ~ v1_relat_1('#skF_1'(A_21)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_426])).

tff(c_440,plain,(
    ! [A_89,A_90] :
      ( r1_xboole_0(A_89,A_90)
      | k9_relat_1('#skF_1'(A_89),A_90) != k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_435])).

tff(c_452,plain,(
    ! [A_91] : r1_xboole_0(A_91,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_113,c_440])).

tff(c_10,plain,(
    ! [B_5,A_4] :
      ( ~ r1_xboole_0(B_5,A_4)
      | ~ r1_tarski(B_5,A_4)
      | v1_xboole_0(B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_461,plain,(
    ! [A_91] :
      ( ~ r1_tarski(A_91,k1_xboole_0)
      | v1_xboole_0(A_91) ) ),
    inference(resolution,[status(thm)],[c_452,c_10])).

tff(c_557,plain,(
    ! [A_110] :
      ( v1_xboole_0(k1_relat_1(A_110))
      | ~ r1_tarski(A_110,'#skF_1'(k1_xboole_0))
      | ~ v1_relat_1(A_110) ) ),
    inference(resolution,[status(thm)],[c_553,c_461])).

tff(c_568,plain,(
    ! [A_110] :
      ( v1_xboole_0(k1_relat_1(A_110))
      | ~ r1_tarski(A_110,k1_xboole_0)
      | ~ v1_relat_1(A_110) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_184,c_557])).

tff(c_56,plain,(
    ! [C_39,A_36,B_37] :
      ( v1_partfun1(C_39,A_36)
      | ~ m1_subset_1(C_39,k1_zfmisc_1(k2_zfmisc_1(A_36,B_37)))
      | ~ v1_xboole_0(A_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_2981,plain,(
    ! [C_278,A_279,B_280] :
      ( v1_partfun1(C_278,A_279)
      | ~ v1_xboole_0(A_279)
      | ~ r1_tarski(k2_relat_1(C_278),B_280)
      | ~ r1_tarski(k1_relat_1(C_278),A_279)
      | ~ v1_relat_1(C_278) ) ),
    inference(resolution,[status(thm)],[c_1030,c_56])).

tff(c_3034,plain,(
    ! [A_279] :
      ( v1_partfun1('#skF_3',A_279)
      | ~ v1_xboole_0(A_279)
      | ~ r1_tarski(k1_relat_1('#skF_3'),A_279)
      | ~ v1_relat_1('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_72,c_2981])).

tff(c_3073,plain,(
    ! [A_281] :
      ( v1_partfun1('#skF_3',A_281)
      | ~ v1_xboole_0(A_281)
      | ~ r1_tarski(k1_relat_1('#skF_3'),A_281) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_3034])).

tff(c_3146,plain,
    ( v1_partfun1('#skF_3',k1_relat_1('#skF_3'))
    | ~ v1_xboole_0(k1_relat_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_6,c_3073])).

tff(c_3147,plain,(
    ~ v1_xboole_0(k1_relat_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_3146])).

tff(c_3156,plain,
    ( ~ r1_tarski('#skF_3',k1_xboole_0)
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_568,c_3147])).

tff(c_3161,plain,(
    ~ r1_tarski('#skF_3',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_3156])).

tff(c_4189,plain,(
    ~ r1_tarski('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4165,c_3161])).

tff(c_126,plain,(
    ! [A_53,B_54] : r1_tarski(k2_relat_1(k2_zfmisc_1(A_53,B_54)),B_54) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_8,plain,(
    ! [A_3] :
      ( k1_xboole_0 = A_3
      | ~ r1_tarski(A_3,k1_xboole_0) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_131,plain,(
    ! [A_53] : k2_relat_1(k2_zfmisc_1(A_53,k1_xboole_0)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_126,c_8])).

tff(c_18,plain,(
    ! [A_9,B_10] : v1_relat_1(k2_zfmisc_1(A_9,B_10)) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_150,plain,(
    ! [A_58] :
      ( k2_relat_1(A_58) != k1_xboole_0
      | k1_xboole_0 = A_58
      | ~ v1_relat_1(A_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_392,plain,(
    ! [A_84,B_85] :
      ( k2_relat_1(k2_zfmisc_1(A_84,B_85)) != k1_xboole_0
      | k2_zfmisc_1(A_84,B_85) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_18,c_150])).

tff(c_396,plain,(
    ! [A_53] : k2_zfmisc_1(A_53,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_131,c_392])).

tff(c_4281,plain,(
    ! [A_53] : k2_zfmisc_1(A_53,'#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4165,c_4165,c_396])).

tff(c_12,plain,(
    ! [A_6] : r1_tarski(A_6,k1_zfmisc_1(k3_tarski(A_6))) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_3372,plain,(
    r1_tarski('#skF_3',k2_zfmisc_1(k1_zfmisc_1(k3_tarski(k1_relat_1('#skF_3'))),'#skF_2')) ),
    inference(resolution,[status(thm)],[c_12,c_3304])).

tff(c_4424,plain,(
    r1_tarski('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4281,c_3372])).

tff(c_4429,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4189,c_4424])).

tff(c_4430,plain,(
    v1_partfun1('#skF_3',k1_relat_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_3146])).

tff(c_4432,plain,(
    ! [C_324,A_325,B_326] :
      ( r1_tarski(C_324,k2_zfmisc_1(A_325,B_326))
      | ~ r1_tarski(k2_relat_1(C_324),B_326)
      | ~ r1_tarski(k1_relat_1(C_324),A_325)
      | ~ v1_relat_1(C_324) ) ),
    inference(resolution,[status(thm)],[c_1030,c_14])).

tff(c_4486,plain,(
    ! [A_325] :
      ( r1_tarski('#skF_3',k2_zfmisc_1(A_325,'#skF_2'))
      | ~ r1_tarski(k1_relat_1('#skF_3'),A_325)
      | ~ v1_relat_1('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_72,c_4432])).

tff(c_4530,plain,(
    ! [A_327] :
      ( r1_tarski('#skF_3',k2_zfmisc_1(A_327,'#skF_2'))
      | ~ r1_tarski(k1_relat_1('#skF_3'),A_327) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_4486])).

tff(c_4599,plain,(
    r1_tarski('#skF_3',k2_zfmisc_1(k1_relat_1('#skF_3'),'#skF_2')) ),
    inference(resolution,[status(thm)],[c_6,c_4530])).

tff(c_780,plain,(
    ! [C_134,A_135,B_136] :
      ( v1_funct_2(C_134,A_135,B_136)
      | ~ v1_partfun1(C_134,A_135)
      | ~ v1_funct_1(C_134)
      | ~ m1_subset_1(C_134,k1_zfmisc_1(k2_zfmisc_1(A_135,B_136))) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_788,plain,(
    ! [A_7,A_135,B_136] :
      ( v1_funct_2(A_7,A_135,B_136)
      | ~ v1_partfun1(A_7,A_135)
      | ~ v1_funct_1(A_7)
      | ~ r1_tarski(A_7,k2_zfmisc_1(A_135,B_136)) ) ),
    inference(resolution,[status(thm)],[c_16,c_780])).

tff(c_4606,plain,
    ( v1_funct_2('#skF_3',k1_relat_1('#skF_3'),'#skF_2')
    | ~ v1_partfun1('#skF_3',k1_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_4599,c_788])).

tff(c_4617,plain,(
    v1_funct_2('#skF_3',k1_relat_1('#skF_3'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_4430,c_4606])).

tff(c_4619,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_100,c_4617])).

tff(c_4620,plain,(
    ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),'#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_78])).

tff(c_5791,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_3'),'#skF_2')
    | ~ r1_tarski(k1_relat_1('#skF_3'),k1_relat_1('#skF_3'))
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_5768,c_4620])).

tff(c_5804,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_6,c_72,c_5791])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n006.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 19:08:07 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.12/2.23  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.12/2.24  
% 6.12/2.24  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.45/2.24  %$ v1_funct_2 > v1_partfun1 > r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k9_relat_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k3_tarski > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > np__1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3
% 6.45/2.24  
% 6.45/2.24  %Foreground sorts:
% 6.45/2.24  
% 6.45/2.24  
% 6.45/2.24  %Background operators:
% 6.45/2.24  
% 6.45/2.24  
% 6.45/2.24  %Foreground operators:
% 6.45/2.24  tff(np__1, type, np__1: $i).
% 6.45/2.24  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 6.45/2.24  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.45/2.24  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 6.45/2.24  tff('#skF_1', type, '#skF_1': $i > $i).
% 6.45/2.24  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 6.45/2.24  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.45/2.24  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 6.45/2.24  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 6.45/2.24  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 6.45/2.24  tff('#skF_2', type, '#skF_2': $i).
% 6.45/2.24  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 6.45/2.24  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 6.45/2.24  tff('#skF_3', type, '#skF_3': $i).
% 6.45/2.24  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 6.45/2.24  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 6.45/2.24  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 6.45/2.24  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.45/2.24  tff(k3_tarski, type, k3_tarski: $i > $i).
% 6.45/2.24  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 6.45/2.24  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 6.45/2.24  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.45/2.24  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 6.45/2.24  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 6.45/2.24  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 6.45/2.24  
% 6.45/2.26  tff(f_160, negated_conjecture, ~(![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r1_tarski(k2_relat_1(B), A) => ((v1_funct_1(B) & v1_funct_2(B, k1_relat_1(B), A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B), A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_funct_2)).
% 6.45/2.26  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 6.45/2.26  tff(f_112, axiom, (![A, B, C]: (v1_relat_1(C) => ((r1_tarski(k1_relat_1(C), A) & r1_tarski(k2_relat_1(C), B)) => m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_relset_1)).
% 6.45/2.26  tff(f_49, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 6.45/2.26  tff(f_104, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 6.45/2.26  tff(f_147, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 6.45/2.26  tff(f_100, axiom, (![A]: (?[B]: (((v1_relat_1(B) & v1_funct_1(B)) & (k1_relat_1(B) = A)) & (![C]: (r2_hidden(C, A) => (k1_funct_1(B, C) = np__1)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', s3_funct_1__e7_25__funct_1)).
% 6.45/2.26  tff(f_82, axiom, (![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_relat_1)).
% 6.45/2.26  tff(f_74, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(A, B) => (r1_tarski(k1_relat_1(A), k1_relat_1(B)) & r1_tarski(k2_relat_1(A), k2_relat_1(B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t25_relat_1)).
% 6.45/2.26  tff(f_55, axiom, (![A]: (v1_relat_1(A) => (k9_relat_1(A, k1_xboole_0) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t149_relat_1)).
% 6.45/2.26  tff(f_61, axiom, (![A, B]: (v1_relat_1(B) => ((k9_relat_1(B, A) = k1_xboole_0) <=> r1_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t151_relat_1)).
% 6.45/2.26  tff(f_43, axiom, (![A, B]: (~v1_xboole_0(B) => ~(r1_tarski(B, A) & r1_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_xboole_1)).
% 6.45/2.26  tff(f_129, axiom, (![A, B]: (v1_xboole_0(A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_partfun1(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_partfun1)).
% 6.45/2.26  tff(f_63, axiom, (![A, B]: r1_tarski(k2_relat_1(k2_zfmisc_1(A, B)), B)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t194_relat_1)).
% 6.45/2.26  tff(f_35, axiom, (![A]: (r1_tarski(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_1)).
% 6.45/2.26  tff(f_51, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 6.45/2.26  tff(f_45, axiom, (![A]: r1_tarski(A, k1_zfmisc_1(k3_tarski(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_zfmisc_1)).
% 6.45/2.26  tff(f_122, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v1_partfun1(C, A)) => (v1_funct_1(C) & v1_funct_2(C, A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_funct_2)).
% 6.45/2.26  tff(c_76, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_160])).
% 6.45/2.26  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 6.45/2.26  tff(c_72, plain, (r1_tarski(k2_relat_1('#skF_3'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_160])).
% 6.45/2.26  tff(c_5768, plain, (![C_445, A_446, B_447]: (m1_subset_1(C_445, k1_zfmisc_1(k2_zfmisc_1(A_446, B_447))) | ~r1_tarski(k2_relat_1(C_445), B_447) | ~r1_tarski(k1_relat_1(C_445), A_446) | ~v1_relat_1(C_445))), inference(cnfTransformation, [status(thm)], [f_112])).
% 6.45/2.26  tff(c_74, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_160])).
% 6.45/2.26  tff(c_70, plain, (~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), '#skF_2'))) | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), '#skF_2') | ~v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_160])).
% 6.45/2.26  tff(c_78, plain, (~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), '#skF_2'))) | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_70])).
% 6.45/2.26  tff(c_100, plain, (~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), '#skF_2')), inference(splitLeft, [status(thm)], [c_78])).
% 6.45/2.26  tff(c_1030, plain, (![C_152, A_153, B_154]: (m1_subset_1(C_152, k1_zfmisc_1(k2_zfmisc_1(A_153, B_154))) | ~r1_tarski(k2_relat_1(C_152), B_154) | ~r1_tarski(k1_relat_1(C_152), A_153) | ~v1_relat_1(C_152))), inference(cnfTransformation, [status(thm)], [f_112])).
% 6.45/2.26  tff(c_14, plain, (![A_7, B_8]: (r1_tarski(A_7, B_8) | ~m1_subset_1(A_7, k1_zfmisc_1(B_8)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 6.45/2.26  tff(c_3207, plain, (![C_282, A_283, B_284]: (r1_tarski(C_282, k2_zfmisc_1(A_283, B_284)) | ~r1_tarski(k2_relat_1(C_282), B_284) | ~r1_tarski(k1_relat_1(C_282), A_283) | ~v1_relat_1(C_282))), inference(resolution, [status(thm)], [c_1030, c_14])).
% 6.45/2.26  tff(c_3261, plain, (![A_283]: (r1_tarski('#skF_3', k2_zfmisc_1(A_283, '#skF_2')) | ~r1_tarski(k1_relat_1('#skF_3'), A_283) | ~v1_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_72, c_3207])).
% 6.45/2.26  tff(c_3304, plain, (![A_285]: (r1_tarski('#skF_3', k2_zfmisc_1(A_285, '#skF_2')) | ~r1_tarski(k1_relat_1('#skF_3'), A_285))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_3261])).
% 6.45/2.26  tff(c_3373, plain, (r1_tarski('#skF_3', k2_zfmisc_1(k1_relat_1('#skF_3'), '#skF_2'))), inference(resolution, [status(thm)], [c_6, c_3304])).
% 6.45/2.26  tff(c_16, plain, (![A_7, B_8]: (m1_subset_1(A_7, k1_zfmisc_1(B_8)) | ~r1_tarski(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_49])).
% 6.45/2.26  tff(c_595, plain, (![A_113, B_114, C_115]: (k1_relset_1(A_113, B_114, C_115)=k1_relat_1(C_115) | ~m1_subset_1(C_115, k1_zfmisc_1(k2_zfmisc_1(A_113, B_114))))), inference(cnfTransformation, [status(thm)], [f_104])).
% 6.45/2.26  tff(c_603, plain, (![A_113, B_114, A_7]: (k1_relset_1(A_113, B_114, A_7)=k1_relat_1(A_7) | ~r1_tarski(A_7, k2_zfmisc_1(A_113, B_114)))), inference(resolution, [status(thm)], [c_16, c_595])).
% 6.45/2.26  tff(c_3389, plain, (k1_relset_1(k1_relat_1('#skF_3'), '#skF_2', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_3373, c_603])).
% 6.45/2.26  tff(c_1129, plain, (![B_157, C_158, A_159]: (k1_xboole_0=B_157 | v1_funct_2(C_158, A_159, B_157) | k1_relset_1(A_159, B_157, C_158)!=A_159 | ~m1_subset_1(C_158, k1_zfmisc_1(k2_zfmisc_1(A_159, B_157))))), inference(cnfTransformation, [status(thm)], [f_147])).
% 6.45/2.26  tff(c_4118, plain, (![B_316, A_317, A_318]: (k1_xboole_0=B_316 | v1_funct_2(A_317, A_318, B_316) | k1_relset_1(A_318, B_316, A_317)!=A_318 | ~r1_tarski(A_317, k2_zfmisc_1(A_318, B_316)))), inference(resolution, [status(thm)], [c_16, c_1129])).
% 6.45/2.26  tff(c_4127, plain, (k1_xboole_0='#skF_2' | v1_funct_2('#skF_3', k1_relat_1('#skF_3'), '#skF_2') | k1_relset_1(k1_relat_1('#skF_3'), '#skF_2', '#skF_3')!=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_3373, c_4118])).
% 6.45/2.26  tff(c_4164, plain, (k1_xboole_0='#skF_2' | v1_funct_2('#skF_3', k1_relat_1('#skF_3'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_3389, c_4127])).
% 6.45/2.26  tff(c_4165, plain, (k1_xboole_0='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_100, c_4164])).
% 6.45/2.26  tff(c_42, plain, (![A_21]: (k1_relat_1('#skF_1'(A_21))=A_21)), inference(cnfTransformation, [status(thm)], [f_100])).
% 6.45/2.26  tff(c_46, plain, (![A_21]: (v1_relat_1('#skF_1'(A_21)))), inference(cnfTransformation, [status(thm)], [f_100])).
% 6.45/2.26  tff(c_170, plain, (![A_63]: (k1_relat_1(A_63)!=k1_xboole_0 | k1_xboole_0=A_63 | ~v1_relat_1(A_63))), inference(cnfTransformation, [status(thm)], [f_82])).
% 6.45/2.26  tff(c_176, plain, (![A_21]: (k1_relat_1('#skF_1'(A_21))!=k1_xboole_0 | '#skF_1'(A_21)=k1_xboole_0)), inference(resolution, [status(thm)], [c_46, c_170])).
% 6.45/2.26  tff(c_184, plain, ('#skF_1'(k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_42, c_176])).
% 6.45/2.26  tff(c_529, plain, (![A_103, B_104]: (r1_tarski(k1_relat_1(A_103), k1_relat_1(B_104)) | ~r1_tarski(A_103, B_104) | ~v1_relat_1(B_104) | ~v1_relat_1(A_103))), inference(cnfTransformation, [status(thm)], [f_74])).
% 6.45/2.26  tff(c_537, plain, (![A_103, A_21]: (r1_tarski(k1_relat_1(A_103), A_21) | ~r1_tarski(A_103, '#skF_1'(A_21)) | ~v1_relat_1('#skF_1'(A_21)) | ~v1_relat_1(A_103))), inference(superposition, [status(thm), theory('equality')], [c_42, c_529])).
% 6.45/2.26  tff(c_553, plain, (![A_110, A_111]: (r1_tarski(k1_relat_1(A_110), A_111) | ~r1_tarski(A_110, '#skF_1'(A_111)) | ~v1_relat_1(A_110))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_537])).
% 6.45/2.26  tff(c_102, plain, (![A_51]: (k9_relat_1(A_51, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(A_51))), inference(cnfTransformation, [status(thm)], [f_55])).
% 6.45/2.26  tff(c_113, plain, (![A_21]: (k9_relat_1('#skF_1'(A_21), k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_46, c_102])).
% 6.45/2.26  tff(c_426, plain, (![B_87, A_88]: (r1_xboole_0(k1_relat_1(B_87), A_88) | k9_relat_1(B_87, A_88)!=k1_xboole_0 | ~v1_relat_1(B_87))), inference(cnfTransformation, [status(thm)], [f_61])).
% 6.45/2.26  tff(c_435, plain, (![A_21, A_88]: (r1_xboole_0(A_21, A_88) | k9_relat_1('#skF_1'(A_21), A_88)!=k1_xboole_0 | ~v1_relat_1('#skF_1'(A_21)))), inference(superposition, [status(thm), theory('equality')], [c_42, c_426])).
% 6.45/2.26  tff(c_440, plain, (![A_89, A_90]: (r1_xboole_0(A_89, A_90) | k9_relat_1('#skF_1'(A_89), A_90)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_46, c_435])).
% 6.45/2.26  tff(c_452, plain, (![A_91]: (r1_xboole_0(A_91, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_113, c_440])).
% 6.45/2.26  tff(c_10, plain, (![B_5, A_4]: (~r1_xboole_0(B_5, A_4) | ~r1_tarski(B_5, A_4) | v1_xboole_0(B_5))), inference(cnfTransformation, [status(thm)], [f_43])).
% 6.45/2.26  tff(c_461, plain, (![A_91]: (~r1_tarski(A_91, k1_xboole_0) | v1_xboole_0(A_91))), inference(resolution, [status(thm)], [c_452, c_10])).
% 6.45/2.26  tff(c_557, plain, (![A_110]: (v1_xboole_0(k1_relat_1(A_110)) | ~r1_tarski(A_110, '#skF_1'(k1_xboole_0)) | ~v1_relat_1(A_110))), inference(resolution, [status(thm)], [c_553, c_461])).
% 6.45/2.26  tff(c_568, plain, (![A_110]: (v1_xboole_0(k1_relat_1(A_110)) | ~r1_tarski(A_110, k1_xboole_0) | ~v1_relat_1(A_110))), inference(demodulation, [status(thm), theory('equality')], [c_184, c_557])).
% 6.45/2.26  tff(c_56, plain, (![C_39, A_36, B_37]: (v1_partfun1(C_39, A_36) | ~m1_subset_1(C_39, k1_zfmisc_1(k2_zfmisc_1(A_36, B_37))) | ~v1_xboole_0(A_36))), inference(cnfTransformation, [status(thm)], [f_129])).
% 6.45/2.26  tff(c_2981, plain, (![C_278, A_279, B_280]: (v1_partfun1(C_278, A_279) | ~v1_xboole_0(A_279) | ~r1_tarski(k2_relat_1(C_278), B_280) | ~r1_tarski(k1_relat_1(C_278), A_279) | ~v1_relat_1(C_278))), inference(resolution, [status(thm)], [c_1030, c_56])).
% 6.45/2.26  tff(c_3034, plain, (![A_279]: (v1_partfun1('#skF_3', A_279) | ~v1_xboole_0(A_279) | ~r1_tarski(k1_relat_1('#skF_3'), A_279) | ~v1_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_72, c_2981])).
% 6.45/2.26  tff(c_3073, plain, (![A_281]: (v1_partfun1('#skF_3', A_281) | ~v1_xboole_0(A_281) | ~r1_tarski(k1_relat_1('#skF_3'), A_281))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_3034])).
% 6.45/2.26  tff(c_3146, plain, (v1_partfun1('#skF_3', k1_relat_1('#skF_3')) | ~v1_xboole_0(k1_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_6, c_3073])).
% 6.45/2.26  tff(c_3147, plain, (~v1_xboole_0(k1_relat_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_3146])).
% 6.45/2.26  tff(c_3156, plain, (~r1_tarski('#skF_3', k1_xboole_0) | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_568, c_3147])).
% 6.45/2.26  tff(c_3161, plain, (~r1_tarski('#skF_3', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_76, c_3156])).
% 6.45/2.26  tff(c_4189, plain, (~r1_tarski('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_4165, c_3161])).
% 6.45/2.26  tff(c_126, plain, (![A_53, B_54]: (r1_tarski(k2_relat_1(k2_zfmisc_1(A_53, B_54)), B_54))), inference(cnfTransformation, [status(thm)], [f_63])).
% 6.45/2.26  tff(c_8, plain, (![A_3]: (k1_xboole_0=A_3 | ~r1_tarski(A_3, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_35])).
% 6.45/2.26  tff(c_131, plain, (![A_53]: (k2_relat_1(k2_zfmisc_1(A_53, k1_xboole_0))=k1_xboole_0)), inference(resolution, [status(thm)], [c_126, c_8])).
% 6.45/2.26  tff(c_18, plain, (![A_9, B_10]: (v1_relat_1(k2_zfmisc_1(A_9, B_10)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 6.45/2.26  tff(c_150, plain, (![A_58]: (k2_relat_1(A_58)!=k1_xboole_0 | k1_xboole_0=A_58 | ~v1_relat_1(A_58))), inference(cnfTransformation, [status(thm)], [f_82])).
% 6.45/2.26  tff(c_392, plain, (![A_84, B_85]: (k2_relat_1(k2_zfmisc_1(A_84, B_85))!=k1_xboole_0 | k2_zfmisc_1(A_84, B_85)=k1_xboole_0)), inference(resolution, [status(thm)], [c_18, c_150])).
% 6.45/2.26  tff(c_396, plain, (![A_53]: (k2_zfmisc_1(A_53, k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_131, c_392])).
% 6.45/2.26  tff(c_4281, plain, (![A_53]: (k2_zfmisc_1(A_53, '#skF_2')='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_4165, c_4165, c_396])).
% 6.45/2.26  tff(c_12, plain, (![A_6]: (r1_tarski(A_6, k1_zfmisc_1(k3_tarski(A_6))))), inference(cnfTransformation, [status(thm)], [f_45])).
% 6.45/2.26  tff(c_3372, plain, (r1_tarski('#skF_3', k2_zfmisc_1(k1_zfmisc_1(k3_tarski(k1_relat_1('#skF_3'))), '#skF_2'))), inference(resolution, [status(thm)], [c_12, c_3304])).
% 6.45/2.26  tff(c_4424, plain, (r1_tarski('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_4281, c_3372])).
% 6.45/2.26  tff(c_4429, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4189, c_4424])).
% 6.45/2.26  tff(c_4430, plain, (v1_partfun1('#skF_3', k1_relat_1('#skF_3'))), inference(splitRight, [status(thm)], [c_3146])).
% 6.45/2.26  tff(c_4432, plain, (![C_324, A_325, B_326]: (r1_tarski(C_324, k2_zfmisc_1(A_325, B_326)) | ~r1_tarski(k2_relat_1(C_324), B_326) | ~r1_tarski(k1_relat_1(C_324), A_325) | ~v1_relat_1(C_324))), inference(resolution, [status(thm)], [c_1030, c_14])).
% 6.45/2.26  tff(c_4486, plain, (![A_325]: (r1_tarski('#skF_3', k2_zfmisc_1(A_325, '#skF_2')) | ~r1_tarski(k1_relat_1('#skF_3'), A_325) | ~v1_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_72, c_4432])).
% 6.45/2.26  tff(c_4530, plain, (![A_327]: (r1_tarski('#skF_3', k2_zfmisc_1(A_327, '#skF_2')) | ~r1_tarski(k1_relat_1('#skF_3'), A_327))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_4486])).
% 6.45/2.26  tff(c_4599, plain, (r1_tarski('#skF_3', k2_zfmisc_1(k1_relat_1('#skF_3'), '#skF_2'))), inference(resolution, [status(thm)], [c_6, c_4530])).
% 6.45/2.26  tff(c_780, plain, (![C_134, A_135, B_136]: (v1_funct_2(C_134, A_135, B_136) | ~v1_partfun1(C_134, A_135) | ~v1_funct_1(C_134) | ~m1_subset_1(C_134, k1_zfmisc_1(k2_zfmisc_1(A_135, B_136))))), inference(cnfTransformation, [status(thm)], [f_122])).
% 6.45/2.26  tff(c_788, plain, (![A_7, A_135, B_136]: (v1_funct_2(A_7, A_135, B_136) | ~v1_partfun1(A_7, A_135) | ~v1_funct_1(A_7) | ~r1_tarski(A_7, k2_zfmisc_1(A_135, B_136)))), inference(resolution, [status(thm)], [c_16, c_780])).
% 6.45/2.26  tff(c_4606, plain, (v1_funct_2('#skF_3', k1_relat_1('#skF_3'), '#skF_2') | ~v1_partfun1('#skF_3', k1_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_4599, c_788])).
% 6.45/2.26  tff(c_4617, plain, (v1_funct_2('#skF_3', k1_relat_1('#skF_3'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_4430, c_4606])).
% 6.45/2.26  tff(c_4619, plain, $false, inference(negUnitSimplification, [status(thm)], [c_100, c_4617])).
% 6.45/2.26  tff(c_4620, plain, (~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), '#skF_2')))), inference(splitRight, [status(thm)], [c_78])).
% 6.45/2.26  tff(c_5791, plain, (~r1_tarski(k2_relat_1('#skF_3'), '#skF_2') | ~r1_tarski(k1_relat_1('#skF_3'), k1_relat_1('#skF_3')) | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_5768, c_4620])).
% 6.45/2.26  tff(c_5804, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_76, c_6, c_72, c_5791])).
% 6.45/2.26  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.45/2.26  
% 6.45/2.26  Inference rules
% 6.45/2.26  ----------------------
% 6.45/2.26  #Ref     : 4
% 6.45/2.26  #Sup     : 1163
% 6.45/2.26  #Fact    : 0
% 6.45/2.26  #Define  : 0
% 6.45/2.26  #Split   : 19
% 6.45/2.26  #Chain   : 0
% 6.45/2.26  #Close   : 0
% 6.45/2.26  
% 6.45/2.26  Ordering : KBO
% 6.45/2.26  
% 6.45/2.26  Simplification rules
% 6.45/2.26  ----------------------
% 6.45/2.26  #Subsume      : 375
% 6.45/2.26  #Demod        : 871
% 6.45/2.26  #Tautology    : 328
% 6.45/2.26  #SimpNegUnit  : 104
% 6.45/2.26  #BackRed      : 185
% 6.45/2.26  
% 6.45/2.26  #Partial instantiations: 0
% 6.45/2.26  #Strategies tried      : 1
% 6.45/2.26  
% 6.45/2.26  Timing (in seconds)
% 6.45/2.26  ----------------------
% 6.45/2.26  Preprocessing        : 0.35
% 6.45/2.26  Parsing              : 0.19
% 6.45/2.26  CNF conversion       : 0.02
% 6.45/2.26  Main loop            : 1.14
% 6.45/2.26  Inferencing          : 0.35
% 6.45/2.26  Reduction            : 0.38
% 6.45/2.26  Demodulation         : 0.26
% 6.45/2.26  BG Simplification    : 0.04
% 6.45/2.26  Subsumption          : 0.28
% 6.45/2.26  Abstraction          : 0.05
% 6.45/2.26  MUC search           : 0.00
% 6.45/2.26  Cooper               : 0.00
% 6.45/2.26  Total                : 1.52
% 6.45/2.26  Index Insertion      : 0.00
% 6.45/2.26  Index Deletion       : 0.00
% 6.45/2.26  Index Matching       : 0.00
% 6.45/2.26  BG Taut test         : 0.00
%------------------------------------------------------------------------------
