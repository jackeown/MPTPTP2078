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
% DateTime   : Thu Dec  3 10:14:34 EST 2020

% Result     : Theorem 3.04s
% Output     : CNFRefutation 3.19s
% Verified   : 
% Statistics : Number of formulae       :   98 ( 257 expanded)
%              Number of leaves         :   41 ( 103 expanded)
%              Depth                    :   13
%              Number of atoms          :  188 ( 565 expanded)
%              Number of equality atoms :  100 ( 270 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_enumset1 > k2_relset_1 > k1_enumset1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4

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

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_136,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,k1_tarski(A),B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A),B))) )
       => ( B != k1_xboole_0
         => k2_relset_1(k1_tarski(A),B,C) = k1_tarski(k1_funct_1(C,A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_funct_2)).

tff(f_102,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_85,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ( k1_relat_1(A) = k1_xboole_0
          | k2_relat_1(A) = k1_xboole_0 )
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).

tff(f_93,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( k1_relat_1(B) = k1_tarski(A)
       => k2_relat_1(B) = k1_tarski(k1_funct_1(B,A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_funct_1)).

tff(f_112,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_108,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_37,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_74,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_39,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_68,axiom,(
    ! [A,B,C,D] :
      ( r1_tarski(D,k1_enumset1(A,B,C))
    <=> ~ ( D != k1_xboole_0
          & D != k1_tarski(A)
          & D != k1_tarski(B)
          & D != k1_tarski(C)
          & D != k2_tarski(A,B)
          & D != k2_tarski(B,C)
          & D != k2_tarski(A,C)
          & D != k1_enumset1(A,B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t142_zfmisc_1)).

tff(f_77,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_33,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_35,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_124,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_hidden(C,A)
       => ( B = k1_xboole_0
          | r2_hidden(k1_funct_1(D,C),k2_relset_1(A,B,D)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_funct_2)).

tff(f_98,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

tff(c_60,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_2'),'#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_131,plain,(
    ! [C_58,A_59,B_60] :
      ( v1_relat_1(C_58)
      | ~ m1_subset_1(C_58,k1_zfmisc_1(k2_zfmisc_1(A_59,B_60))) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_135,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_60,c_131])).

tff(c_64,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_40,plain,(
    ! [A_16] :
      ( k1_relat_1(A_16) != k1_xboole_0
      | k1_xboole_0 = A_16
      | ~ v1_relat_1(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_142,plain,
    ( k1_relat_1('#skF_4') != k1_xboole_0
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_135,c_40])).

tff(c_144,plain,(
    k1_relat_1('#skF_4') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_142])).

tff(c_42,plain,(
    ! [B_18,A_17] :
      ( k1_tarski(k1_funct_1(B_18,A_17)) = k2_relat_1(B_18)
      | k1_tarski(A_17) != k1_relat_1(B_18)
      | ~ v1_funct_1(B_18)
      | ~ v1_relat_1(B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_235,plain,(
    ! [A_89,B_90,C_91] :
      ( k2_relset_1(A_89,B_90,C_91) = k2_relat_1(C_91)
      | ~ m1_subset_1(C_91,k1_zfmisc_1(k2_zfmisc_1(A_89,B_90))) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_239,plain,(
    k2_relset_1(k1_tarski('#skF_2'),'#skF_3','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_60,c_235])).

tff(c_56,plain,(
    k2_relset_1(k1_tarski('#skF_2'),'#skF_3','#skF_4') != k1_tarski(k1_funct_1('#skF_4','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_240,plain,(
    k1_tarski(k1_funct_1('#skF_4','#skF_2')) != k2_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_239,c_56])).

tff(c_277,plain,
    ( k1_tarski('#skF_2') != k1_relat_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_240])).

tff(c_280,plain,(
    k1_tarski('#skF_2') != k1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_135,c_64,c_277])).

tff(c_216,plain,(
    ! [C_82,A_83,B_84] :
      ( v4_relat_1(C_82,A_83)
      | ~ m1_subset_1(C_82,k1_zfmisc_1(k2_zfmisc_1(A_83,B_84))) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_220,plain,(
    v4_relat_1('#skF_4',k1_tarski('#skF_2')) ),
    inference(resolution,[status(thm)],[c_60,c_216])).

tff(c_6,plain,(
    ! [A_4] : k2_tarski(A_4,A_4) = k1_tarski(A_4) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_32,plain,(
    ! [B_15,A_14] :
      ( r1_tarski(k1_relat_1(B_15),A_14)
      | ~ v4_relat_1(B_15,A_14)
      | ~ v1_relat_1(B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_8,plain,(
    ! [A_5,B_6] : k1_enumset1(A_5,A_5,B_6) = k2_tarski(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_332,plain,(
    ! [A_110,B_111,C_112,D_113] :
      ( k1_enumset1(A_110,B_111,C_112) = D_113
      | k2_tarski(A_110,C_112) = D_113
      | k2_tarski(B_111,C_112) = D_113
      | k2_tarski(A_110,B_111) = D_113
      | k1_tarski(C_112) = D_113
      | k1_tarski(B_111) = D_113
      | k1_tarski(A_110) = D_113
      | k1_xboole_0 = D_113
      | ~ r1_tarski(D_113,k1_enumset1(A_110,B_111,C_112)) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_351,plain,(
    ! [A_5,B_6,D_113] :
      ( k1_enumset1(A_5,A_5,B_6) = D_113
      | k2_tarski(A_5,B_6) = D_113
      | k2_tarski(A_5,B_6) = D_113
      | k2_tarski(A_5,A_5) = D_113
      | k1_tarski(B_6) = D_113
      | k1_tarski(A_5) = D_113
      | k1_tarski(A_5) = D_113
      | k1_xboole_0 = D_113
      | ~ r1_tarski(D_113,k2_tarski(A_5,B_6)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_332])).

tff(c_432,plain,(
    ! [A_132,B_133,D_134] :
      ( k2_tarski(A_132,B_133) = D_134
      | k2_tarski(A_132,B_133) = D_134
      | k2_tarski(A_132,B_133) = D_134
      | k1_tarski(A_132) = D_134
      | k1_tarski(B_133) = D_134
      | k1_tarski(A_132) = D_134
      | k1_tarski(A_132) = D_134
      | k1_xboole_0 = D_134
      | ~ r1_tarski(D_134,k2_tarski(A_132,B_133)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_8,c_351])).

tff(c_471,plain,(
    ! [A_135,B_136,B_137] :
      ( k2_tarski(A_135,B_136) = k1_relat_1(B_137)
      | k1_tarski(B_136) = k1_relat_1(B_137)
      | k1_tarski(A_135) = k1_relat_1(B_137)
      | k1_relat_1(B_137) = k1_xboole_0
      | ~ v4_relat_1(B_137,k2_tarski(A_135,B_136))
      | ~ v1_relat_1(B_137) ) ),
    inference(resolution,[status(thm)],[c_32,c_432])).

tff(c_474,plain,(
    ! [A_4,B_137] :
      ( k2_tarski(A_4,A_4) = k1_relat_1(B_137)
      | k1_tarski(A_4) = k1_relat_1(B_137)
      | k1_tarski(A_4) = k1_relat_1(B_137)
      | k1_relat_1(B_137) = k1_xboole_0
      | ~ v4_relat_1(B_137,k1_tarski(A_4))
      | ~ v1_relat_1(B_137) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_471])).

tff(c_476,plain,(
    ! [A_138,B_139] :
      ( k1_tarski(A_138) = k1_relat_1(B_139)
      | k1_tarski(A_138) = k1_relat_1(B_139)
      | k1_tarski(A_138) = k1_relat_1(B_139)
      | k1_relat_1(B_139) = k1_xboole_0
      | ~ v4_relat_1(B_139,k1_tarski(A_138))
      | ~ v1_relat_1(B_139) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_474])).

tff(c_482,plain,
    ( k1_tarski('#skF_2') = k1_relat_1('#skF_4')
    | k1_relat_1('#skF_4') = k1_xboole_0
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_220,c_476])).

tff(c_485,plain,
    ( k1_tarski('#skF_2') = k1_relat_1('#skF_4')
    | k1_relat_1('#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_135,c_482])).

tff(c_487,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_144,c_280,c_485])).

tff(c_488,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_142])).

tff(c_489,plain,(
    k1_relat_1('#skF_4') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_142])).

tff(c_516,plain,(
    k1_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_488,c_489])).

tff(c_34,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_504,plain,(
    k2_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_488,c_488,c_34])).

tff(c_653,plain,(
    ! [B_177,A_178] :
      ( k1_tarski(k1_funct_1(B_177,A_178)) = k2_relat_1(B_177)
      | k1_tarski(A_178) != k1_relat_1(B_177)
      | ~ v1_funct_1(B_177)
      | ~ v1_relat_1(B_177) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_642,plain,(
    ! [A_174,B_175,C_176] :
      ( k2_relset_1(A_174,B_175,C_176) = k2_relat_1(C_176)
      | ~ m1_subset_1(C_176,k1_zfmisc_1(k2_zfmisc_1(A_174,B_175))) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_645,plain,(
    k2_relset_1(k1_tarski('#skF_2'),'#skF_3','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_60,c_642])).

tff(c_647,plain,(
    k2_relset_1(k1_tarski('#skF_2'),'#skF_3','#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_504,c_645])).

tff(c_648,plain,(
    k1_tarski(k1_funct_1('#skF_4','#skF_2')) != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_647,c_56])).

tff(c_659,plain,
    ( k2_relat_1('#skF_4') != '#skF_4'
    | k1_tarski('#skF_2') != k1_relat_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_653,c_648])).

tff(c_686,plain,(
    k1_tarski('#skF_2') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_135,c_64,c_516,c_504,c_659])).

tff(c_2,plain,(
    ! [A_1] :
      ( r2_hidden('#skF_1'(A_1),A_1)
      | k1_xboole_0 = A_1 ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_501,plain,(
    ! [A_1] :
      ( r2_hidden('#skF_1'(A_1),A_1)
      | A_1 = '#skF_4' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_488,c_2])).

tff(c_4,plain,(
    ! [A_3] : r1_tarski(k1_xboole_0,A_3) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_502,plain,(
    ! [A_3] : r1_tarski('#skF_4',A_3) ),
    inference(demodulation,[status(thm),theory(equality)],[c_488,c_4])).

tff(c_58,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_505,plain,(
    '#skF_3' != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_488,c_58])).

tff(c_62,plain,(
    v1_funct_2('#skF_4',k1_tarski('#skF_2'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_54,plain,(
    ! [D_33,C_32,A_30,B_31] :
      ( r2_hidden(k1_funct_1(D_33,C_32),k2_relset_1(A_30,B_31,D_33))
      | k1_xboole_0 = B_31
      | ~ r2_hidden(C_32,A_30)
      | ~ m1_subset_1(D_33,k1_zfmisc_1(k2_zfmisc_1(A_30,B_31)))
      | ~ v1_funct_2(D_33,A_30,B_31)
      | ~ v1_funct_1(D_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_689,plain,(
    ! [D_179,C_180,A_181,B_182] :
      ( r2_hidden(k1_funct_1(D_179,C_180),k2_relset_1(A_181,B_182,D_179))
      | B_182 = '#skF_4'
      | ~ r2_hidden(C_180,A_181)
      | ~ m1_subset_1(D_179,k1_zfmisc_1(k2_zfmisc_1(A_181,B_182)))
      | ~ v1_funct_2(D_179,A_181,B_182)
      | ~ v1_funct_1(D_179) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_488,c_54])).

tff(c_695,plain,(
    ! [C_180] :
      ( r2_hidden(k1_funct_1('#skF_4',C_180),'#skF_4')
      | '#skF_3' = '#skF_4'
      | ~ r2_hidden(C_180,k1_tarski('#skF_2'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_2'),'#skF_3')))
      | ~ v1_funct_2('#skF_4',k1_tarski('#skF_2'),'#skF_3')
      | ~ v1_funct_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_647,c_689])).

tff(c_698,plain,(
    ! [C_180] :
      ( r2_hidden(k1_funct_1('#skF_4',C_180),'#skF_4')
      | '#skF_3' = '#skF_4'
      | ~ r2_hidden(C_180,k1_tarski('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_60,c_695])).

tff(c_700,plain,(
    ! [C_183] :
      ( r2_hidden(k1_funct_1('#skF_4',C_183),'#skF_4')
      | ~ r2_hidden(C_183,k1_tarski('#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_505,c_698])).

tff(c_44,plain,(
    ! [B_20,A_19] :
      ( ~ r1_tarski(B_20,A_19)
      | ~ r2_hidden(A_19,B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_703,plain,(
    ! [C_183] :
      ( ~ r1_tarski('#skF_4',k1_funct_1('#skF_4',C_183))
      | ~ r2_hidden(C_183,k1_tarski('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_700,c_44])).

tff(c_707,plain,(
    ! [C_184] : ~ r2_hidden(C_184,k1_tarski('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_502,c_703])).

tff(c_711,plain,(
    k1_tarski('#skF_2') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_501,c_707])).

tff(c_715,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_686,c_711])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:40:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.04/1.45  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.19/1.46  
% 3.19/1.46  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.19/1.46  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_enumset1 > k2_relset_1 > k1_enumset1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4
% 3.19/1.46  
% 3.19/1.46  %Foreground sorts:
% 3.19/1.46  
% 3.19/1.46  
% 3.19/1.46  %Background operators:
% 3.19/1.46  
% 3.19/1.46  
% 3.19/1.46  %Foreground operators:
% 3.19/1.46  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 3.19/1.46  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.19/1.46  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.19/1.46  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.19/1.46  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.19/1.46  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.19/1.46  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.19/1.46  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.19/1.46  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.19/1.46  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.19/1.46  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.19/1.46  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.19/1.46  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.19/1.46  tff('#skF_2', type, '#skF_2': $i).
% 3.19/1.46  tff('#skF_3', type, '#skF_3': $i).
% 3.19/1.46  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.19/1.46  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.19/1.46  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.19/1.46  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.19/1.46  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.19/1.46  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.19/1.46  tff('#skF_4', type, '#skF_4': $i).
% 3.19/1.46  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.19/1.46  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.19/1.46  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.19/1.46  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.19/1.46  
% 3.19/1.48  tff(f_136, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, k1_tarski(A), B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A), B)))) => (~(B = k1_xboole_0) => (k2_relset_1(k1_tarski(A), B, C) = k1_tarski(k1_funct_1(C, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t62_funct_2)).
% 3.19/1.48  tff(f_102, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.19/1.48  tff(f_85, axiom, (![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_relat_1)).
% 3.19/1.48  tff(f_93, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((k1_relat_1(B) = k1_tarski(A)) => (k2_relat_1(B) = k1_tarski(k1_funct_1(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t14_funct_1)).
% 3.19/1.48  tff(f_112, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 3.19/1.48  tff(f_108, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.19/1.48  tff(f_37, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 3.19/1.48  tff(f_74, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d18_relat_1)).
% 3.19/1.48  tff(f_39, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 3.19/1.48  tff(f_68, axiom, (![A, B, C, D]: (r1_tarski(D, k1_enumset1(A, B, C)) <=> ~(((((((~(D = k1_xboole_0) & ~(D = k1_tarski(A))) & ~(D = k1_tarski(B))) & ~(D = k1_tarski(C))) & ~(D = k2_tarski(A, B))) & ~(D = k2_tarski(B, C))) & ~(D = k2_tarski(A, C))) & ~(D = k1_enumset1(A, B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t142_zfmisc_1)).
% 3.19/1.48  tff(f_77, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 3.19/1.48  tff(f_33, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 3.19/1.48  tff(f_35, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 3.19/1.48  tff(f_124, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_hidden(C, A) => ((B = k1_xboole_0) | r2_hidden(k1_funct_1(D, C), k2_relset_1(A, B, D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_funct_2)).
% 3.19/1.48  tff(f_98, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 3.19/1.48  tff(c_60, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_2'), '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_136])).
% 3.19/1.48  tff(c_131, plain, (![C_58, A_59, B_60]: (v1_relat_1(C_58) | ~m1_subset_1(C_58, k1_zfmisc_1(k2_zfmisc_1(A_59, B_60))))), inference(cnfTransformation, [status(thm)], [f_102])).
% 3.19/1.48  tff(c_135, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_60, c_131])).
% 3.19/1.48  tff(c_64, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_136])).
% 3.19/1.48  tff(c_40, plain, (![A_16]: (k1_relat_1(A_16)!=k1_xboole_0 | k1_xboole_0=A_16 | ~v1_relat_1(A_16))), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.19/1.48  tff(c_142, plain, (k1_relat_1('#skF_4')!=k1_xboole_0 | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_135, c_40])).
% 3.19/1.48  tff(c_144, plain, (k1_relat_1('#skF_4')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_142])).
% 3.19/1.48  tff(c_42, plain, (![B_18, A_17]: (k1_tarski(k1_funct_1(B_18, A_17))=k2_relat_1(B_18) | k1_tarski(A_17)!=k1_relat_1(B_18) | ~v1_funct_1(B_18) | ~v1_relat_1(B_18))), inference(cnfTransformation, [status(thm)], [f_93])).
% 3.19/1.48  tff(c_235, plain, (![A_89, B_90, C_91]: (k2_relset_1(A_89, B_90, C_91)=k2_relat_1(C_91) | ~m1_subset_1(C_91, k1_zfmisc_1(k2_zfmisc_1(A_89, B_90))))), inference(cnfTransformation, [status(thm)], [f_112])).
% 3.19/1.48  tff(c_239, plain, (k2_relset_1(k1_tarski('#skF_2'), '#skF_3', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_60, c_235])).
% 3.19/1.48  tff(c_56, plain, (k2_relset_1(k1_tarski('#skF_2'), '#skF_3', '#skF_4')!=k1_tarski(k1_funct_1('#skF_4', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_136])).
% 3.19/1.48  tff(c_240, plain, (k1_tarski(k1_funct_1('#skF_4', '#skF_2'))!=k2_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_239, c_56])).
% 3.19/1.48  tff(c_277, plain, (k1_tarski('#skF_2')!=k1_relat_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_42, c_240])).
% 3.19/1.48  tff(c_280, plain, (k1_tarski('#skF_2')!=k1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_135, c_64, c_277])).
% 3.19/1.48  tff(c_216, plain, (![C_82, A_83, B_84]: (v4_relat_1(C_82, A_83) | ~m1_subset_1(C_82, k1_zfmisc_1(k2_zfmisc_1(A_83, B_84))))), inference(cnfTransformation, [status(thm)], [f_108])).
% 3.19/1.48  tff(c_220, plain, (v4_relat_1('#skF_4', k1_tarski('#skF_2'))), inference(resolution, [status(thm)], [c_60, c_216])).
% 3.19/1.48  tff(c_6, plain, (![A_4]: (k2_tarski(A_4, A_4)=k1_tarski(A_4))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.19/1.48  tff(c_32, plain, (![B_15, A_14]: (r1_tarski(k1_relat_1(B_15), A_14) | ~v4_relat_1(B_15, A_14) | ~v1_relat_1(B_15))), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.19/1.48  tff(c_8, plain, (![A_5, B_6]: (k1_enumset1(A_5, A_5, B_6)=k2_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.19/1.48  tff(c_332, plain, (![A_110, B_111, C_112, D_113]: (k1_enumset1(A_110, B_111, C_112)=D_113 | k2_tarski(A_110, C_112)=D_113 | k2_tarski(B_111, C_112)=D_113 | k2_tarski(A_110, B_111)=D_113 | k1_tarski(C_112)=D_113 | k1_tarski(B_111)=D_113 | k1_tarski(A_110)=D_113 | k1_xboole_0=D_113 | ~r1_tarski(D_113, k1_enumset1(A_110, B_111, C_112)))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.19/1.48  tff(c_351, plain, (![A_5, B_6, D_113]: (k1_enumset1(A_5, A_5, B_6)=D_113 | k2_tarski(A_5, B_6)=D_113 | k2_tarski(A_5, B_6)=D_113 | k2_tarski(A_5, A_5)=D_113 | k1_tarski(B_6)=D_113 | k1_tarski(A_5)=D_113 | k1_tarski(A_5)=D_113 | k1_xboole_0=D_113 | ~r1_tarski(D_113, k2_tarski(A_5, B_6)))), inference(superposition, [status(thm), theory('equality')], [c_8, c_332])).
% 3.19/1.48  tff(c_432, plain, (![A_132, B_133, D_134]: (k2_tarski(A_132, B_133)=D_134 | k2_tarski(A_132, B_133)=D_134 | k2_tarski(A_132, B_133)=D_134 | k1_tarski(A_132)=D_134 | k1_tarski(B_133)=D_134 | k1_tarski(A_132)=D_134 | k1_tarski(A_132)=D_134 | k1_xboole_0=D_134 | ~r1_tarski(D_134, k2_tarski(A_132, B_133)))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_8, c_351])).
% 3.19/1.48  tff(c_471, plain, (![A_135, B_136, B_137]: (k2_tarski(A_135, B_136)=k1_relat_1(B_137) | k1_tarski(B_136)=k1_relat_1(B_137) | k1_tarski(A_135)=k1_relat_1(B_137) | k1_relat_1(B_137)=k1_xboole_0 | ~v4_relat_1(B_137, k2_tarski(A_135, B_136)) | ~v1_relat_1(B_137))), inference(resolution, [status(thm)], [c_32, c_432])).
% 3.19/1.48  tff(c_474, plain, (![A_4, B_137]: (k2_tarski(A_4, A_4)=k1_relat_1(B_137) | k1_tarski(A_4)=k1_relat_1(B_137) | k1_tarski(A_4)=k1_relat_1(B_137) | k1_relat_1(B_137)=k1_xboole_0 | ~v4_relat_1(B_137, k1_tarski(A_4)) | ~v1_relat_1(B_137))), inference(superposition, [status(thm), theory('equality')], [c_6, c_471])).
% 3.19/1.48  tff(c_476, plain, (![A_138, B_139]: (k1_tarski(A_138)=k1_relat_1(B_139) | k1_tarski(A_138)=k1_relat_1(B_139) | k1_tarski(A_138)=k1_relat_1(B_139) | k1_relat_1(B_139)=k1_xboole_0 | ~v4_relat_1(B_139, k1_tarski(A_138)) | ~v1_relat_1(B_139))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_474])).
% 3.19/1.48  tff(c_482, plain, (k1_tarski('#skF_2')=k1_relat_1('#skF_4') | k1_relat_1('#skF_4')=k1_xboole_0 | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_220, c_476])).
% 3.19/1.48  tff(c_485, plain, (k1_tarski('#skF_2')=k1_relat_1('#skF_4') | k1_relat_1('#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_135, c_482])).
% 3.19/1.48  tff(c_487, plain, $false, inference(negUnitSimplification, [status(thm)], [c_144, c_280, c_485])).
% 3.19/1.48  tff(c_488, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_142])).
% 3.19/1.48  tff(c_489, plain, (k1_relat_1('#skF_4')=k1_xboole_0), inference(splitRight, [status(thm)], [c_142])).
% 3.19/1.48  tff(c_516, plain, (k1_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_488, c_489])).
% 3.19/1.48  tff(c_34, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.19/1.48  tff(c_504, plain, (k2_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_488, c_488, c_34])).
% 3.19/1.48  tff(c_653, plain, (![B_177, A_178]: (k1_tarski(k1_funct_1(B_177, A_178))=k2_relat_1(B_177) | k1_tarski(A_178)!=k1_relat_1(B_177) | ~v1_funct_1(B_177) | ~v1_relat_1(B_177))), inference(cnfTransformation, [status(thm)], [f_93])).
% 3.19/1.48  tff(c_642, plain, (![A_174, B_175, C_176]: (k2_relset_1(A_174, B_175, C_176)=k2_relat_1(C_176) | ~m1_subset_1(C_176, k1_zfmisc_1(k2_zfmisc_1(A_174, B_175))))), inference(cnfTransformation, [status(thm)], [f_112])).
% 3.19/1.48  tff(c_645, plain, (k2_relset_1(k1_tarski('#skF_2'), '#skF_3', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_60, c_642])).
% 3.19/1.48  tff(c_647, plain, (k2_relset_1(k1_tarski('#skF_2'), '#skF_3', '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_504, c_645])).
% 3.19/1.48  tff(c_648, plain, (k1_tarski(k1_funct_1('#skF_4', '#skF_2'))!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_647, c_56])).
% 3.19/1.48  tff(c_659, plain, (k2_relat_1('#skF_4')!='#skF_4' | k1_tarski('#skF_2')!=k1_relat_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_653, c_648])).
% 3.19/1.48  tff(c_686, plain, (k1_tarski('#skF_2')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_135, c_64, c_516, c_504, c_659])).
% 3.19/1.48  tff(c_2, plain, (![A_1]: (r2_hidden('#skF_1'(A_1), A_1) | k1_xboole_0=A_1)), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.19/1.48  tff(c_501, plain, (![A_1]: (r2_hidden('#skF_1'(A_1), A_1) | A_1='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_488, c_2])).
% 3.19/1.48  tff(c_4, plain, (![A_3]: (r1_tarski(k1_xboole_0, A_3))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.19/1.48  tff(c_502, plain, (![A_3]: (r1_tarski('#skF_4', A_3))), inference(demodulation, [status(thm), theory('equality')], [c_488, c_4])).
% 3.19/1.48  tff(c_58, plain, (k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_136])).
% 3.19/1.48  tff(c_505, plain, ('#skF_3'!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_488, c_58])).
% 3.19/1.48  tff(c_62, plain, (v1_funct_2('#skF_4', k1_tarski('#skF_2'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_136])).
% 3.19/1.48  tff(c_54, plain, (![D_33, C_32, A_30, B_31]: (r2_hidden(k1_funct_1(D_33, C_32), k2_relset_1(A_30, B_31, D_33)) | k1_xboole_0=B_31 | ~r2_hidden(C_32, A_30) | ~m1_subset_1(D_33, k1_zfmisc_1(k2_zfmisc_1(A_30, B_31))) | ~v1_funct_2(D_33, A_30, B_31) | ~v1_funct_1(D_33))), inference(cnfTransformation, [status(thm)], [f_124])).
% 3.19/1.48  tff(c_689, plain, (![D_179, C_180, A_181, B_182]: (r2_hidden(k1_funct_1(D_179, C_180), k2_relset_1(A_181, B_182, D_179)) | B_182='#skF_4' | ~r2_hidden(C_180, A_181) | ~m1_subset_1(D_179, k1_zfmisc_1(k2_zfmisc_1(A_181, B_182))) | ~v1_funct_2(D_179, A_181, B_182) | ~v1_funct_1(D_179))), inference(demodulation, [status(thm), theory('equality')], [c_488, c_54])).
% 3.19/1.48  tff(c_695, plain, (![C_180]: (r2_hidden(k1_funct_1('#skF_4', C_180), '#skF_4') | '#skF_3'='#skF_4' | ~r2_hidden(C_180, k1_tarski('#skF_2')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_2'), '#skF_3'))) | ~v1_funct_2('#skF_4', k1_tarski('#skF_2'), '#skF_3') | ~v1_funct_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_647, c_689])).
% 3.19/1.48  tff(c_698, plain, (![C_180]: (r2_hidden(k1_funct_1('#skF_4', C_180), '#skF_4') | '#skF_3'='#skF_4' | ~r2_hidden(C_180, k1_tarski('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_60, c_695])).
% 3.19/1.48  tff(c_700, plain, (![C_183]: (r2_hidden(k1_funct_1('#skF_4', C_183), '#skF_4') | ~r2_hidden(C_183, k1_tarski('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_505, c_698])).
% 3.19/1.48  tff(c_44, plain, (![B_20, A_19]: (~r1_tarski(B_20, A_19) | ~r2_hidden(A_19, B_20))), inference(cnfTransformation, [status(thm)], [f_98])).
% 3.19/1.48  tff(c_703, plain, (![C_183]: (~r1_tarski('#skF_4', k1_funct_1('#skF_4', C_183)) | ~r2_hidden(C_183, k1_tarski('#skF_2')))), inference(resolution, [status(thm)], [c_700, c_44])).
% 3.19/1.48  tff(c_707, plain, (![C_184]: (~r2_hidden(C_184, k1_tarski('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_502, c_703])).
% 3.19/1.48  tff(c_711, plain, (k1_tarski('#skF_2')='#skF_4'), inference(resolution, [status(thm)], [c_501, c_707])).
% 3.19/1.48  tff(c_715, plain, $false, inference(negUnitSimplification, [status(thm)], [c_686, c_711])).
% 3.19/1.48  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.19/1.48  
% 3.19/1.48  Inference rules
% 3.19/1.48  ----------------------
% 3.19/1.48  #Ref     : 0
% 3.19/1.48  #Sup     : 140
% 3.19/1.48  #Fact    : 0
% 3.19/1.48  #Define  : 0
% 3.19/1.48  #Split   : 3
% 3.19/1.48  #Chain   : 0
% 3.19/1.48  #Close   : 0
% 3.19/1.48  
% 3.19/1.48  Ordering : KBO
% 3.19/1.48  
% 3.19/1.48  Simplification rules
% 3.19/1.48  ----------------------
% 3.19/1.48  #Subsume      : 22
% 3.19/1.48  #Demod        : 103
% 3.19/1.48  #Tautology    : 72
% 3.19/1.48  #SimpNegUnit  : 5
% 3.19/1.48  #BackRed      : 10
% 3.19/1.48  
% 3.19/1.48  #Partial instantiations: 0
% 3.19/1.48  #Strategies tried      : 1
% 3.19/1.48  
% 3.19/1.48  Timing (in seconds)
% 3.19/1.48  ----------------------
% 3.19/1.48  Preprocessing        : 0.34
% 3.19/1.48  Parsing              : 0.18
% 3.19/1.48  CNF conversion       : 0.02
% 3.19/1.48  Main loop            : 0.38
% 3.19/1.48  Inferencing          : 0.14
% 3.19/1.48  Reduction            : 0.12
% 3.19/1.48  Demodulation         : 0.09
% 3.19/1.48  BG Simplification    : 0.02
% 3.19/1.48  Subsumption          : 0.07
% 3.19/1.48  Abstraction          : 0.02
% 3.19/1.48  MUC search           : 0.00
% 3.19/1.48  Cooper               : 0.00
% 3.19/1.48  Total                : 0.76
% 3.19/1.48  Index Insertion      : 0.00
% 3.19/1.48  Index Deletion       : 0.00
% 3.19/1.48  Index Matching       : 0.00
% 3.19/1.48  BG Taut test         : 0.00
%------------------------------------------------------------------------------
