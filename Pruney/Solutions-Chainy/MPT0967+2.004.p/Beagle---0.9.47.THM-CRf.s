%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:11:13 EST 2020

% Result     : Theorem 4.68s
% Output     : CNFRefutation 5.05s
% Verified   : 
% Statistics : Number of formulae       :  173 (1052 expanded)
%              Number of leaves         :   43 ( 324 expanded)
%              Depth                    :   17
%              Number of atoms          :  322 (3111 expanded)
%              Number of equality atoms :   44 ( 974 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_2

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

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_87,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_xboole_0(k1_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc10_relat_1)).

tff(f_183,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( r1_tarski(B,C)
         => ( ( B = k1_xboole_0
              & A != k1_xboole_0 )
            | ( v1_funct_1(D)
              & v1_funct_2(D,A,C)
              & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,C))) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_funct_2)).

tff(f_91,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_97,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_83,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_65,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_118,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(C,A)))
     => ( r1_tarski(k2_relat_1(D),B)
       => m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(C,B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_relset_1)).

tff(f_112,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_163,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r1_tarski(k2_relset_1(A,B,D),C)
       => ( ( B = k1_xboole_0
            & A != k1_xboole_0 )
          | ( v1_funct_1(D)
            & v1_funct_2(D,A,C)
            & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,C))) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_funct_2)).

tff(f_35,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_77,axiom,(
    ! [A] :
      ( ~ ( ~ r1_xboole_0(A,A)
          & A = k1_xboole_0 )
      & ~ ( A != k1_xboole_0
          & r1_xboole_0(A,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_xboole_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & r2_hidden(C,B) ) )
      & ~ ( ? [C] :
              ( r2_hidden(C,A)
              & r2_hidden(C,B) )
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

tff(f_104,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => v1_xboole_0(C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc3_relset_1)).

tff(f_108,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_144,axiom,(
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

tff(c_30,plain,(
    ! [A_19] :
      ( v1_xboole_0(k1_relat_1(A_19))
      | ~ v1_xboole_0(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_1771,plain,(
    ! [A_303] :
      ( v1_xboole_0(k1_relat_1(A_303))
      | ~ v1_xboole_0(A_303) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_78,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_183])).

tff(c_1358,plain,(
    ! [C_228,A_229,B_230] :
      ( v1_relat_1(C_228)
      | ~ m1_subset_1(C_228,k1_zfmisc_1(k2_zfmisc_1(A_229,B_230))) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_1362,plain,(
    v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_78,c_1358])).

tff(c_18,plain,(
    ! [B_12] : r1_tarski(B_12,B_12) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_1379,plain,(
    ! [C_235,B_236,A_237] :
      ( v5_relat_1(C_235,B_236)
      | ~ m1_subset_1(C_235,k1_zfmisc_1(k2_zfmisc_1(A_237,B_236))) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_1383,plain,(
    v5_relat_1('#skF_6','#skF_4') ),
    inference(resolution,[status(thm)],[c_78,c_1379])).

tff(c_28,plain,(
    ! [B_18,A_17] :
      ( r1_tarski(k2_relat_1(B_18),A_17)
      | ~ v5_relat_1(B_18,A_17)
      | ~ v1_relat_1(B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_76,plain,(
    r1_tarski('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_183])).

tff(c_1439,plain,(
    ! [A_249,C_250,B_251] :
      ( r1_tarski(A_249,C_250)
      | ~ r1_tarski(B_251,C_250)
      | ~ r1_tarski(A_249,B_251) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_1459,plain,(
    ! [A_253] :
      ( r1_tarski(A_253,'#skF_5')
      | ~ r1_tarski(A_253,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_76,c_1439])).

tff(c_20,plain,(
    ! [A_13,C_15,B_14] :
      ( r1_tarski(A_13,C_15)
      | ~ r1_tarski(B_14,C_15)
      | ~ r1_tarski(A_13,B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_1480,plain,(
    ! [A_255,A_256] :
      ( r1_tarski(A_255,'#skF_5')
      | ~ r1_tarski(A_255,A_256)
      | ~ r1_tarski(A_256,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_1459,c_20])).

tff(c_1507,plain,(
    ! [B_262,A_263] :
      ( r1_tarski(k2_relat_1(B_262),'#skF_5')
      | ~ r1_tarski(A_263,'#skF_4')
      | ~ v5_relat_1(B_262,A_263)
      | ~ v1_relat_1(B_262) ) ),
    inference(resolution,[status(thm)],[c_28,c_1480])).

tff(c_1513,plain,
    ( r1_tarski(k2_relat_1('#skF_6'),'#skF_5')
    | ~ r1_tarski('#skF_4','#skF_4')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_1383,c_1507])).

tff(c_1518,plain,(
    r1_tarski(k2_relat_1('#skF_6'),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1362,c_18,c_1513])).

tff(c_1695,plain,(
    ! [D_294,C_295,B_296,A_297] :
      ( m1_subset_1(D_294,k1_zfmisc_1(k2_zfmisc_1(C_295,B_296)))
      | ~ r1_tarski(k2_relat_1(D_294),B_296)
      | ~ m1_subset_1(D_294,k1_zfmisc_1(k2_zfmisc_1(C_295,A_297))) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_1699,plain,(
    ! [B_298] :
      ( m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_3',B_298)))
      | ~ r1_tarski(k2_relat_1('#skF_6'),B_298) ) ),
    inference(resolution,[status(thm)],[c_78,c_1695])).

tff(c_82,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_183])).

tff(c_72,plain,
    ( ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_5')))
    | ~ v1_funct_2('#skF_6','#skF_3','#skF_5')
    | ~ v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_183])).

tff(c_84,plain,
    ( ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_5')))
    | ~ v1_funct_2('#skF_6','#skF_3','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_72])).

tff(c_233,plain,(
    ~ v1_funct_2('#skF_6','#skF_3','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_84])).

tff(c_256,plain,(
    ! [C_93,A_94,B_95] :
      ( v1_relat_1(C_93)
      | ~ m1_subset_1(C_93,k1_zfmisc_1(k2_zfmisc_1(A_94,B_95))) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_260,plain,(
    v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_78,c_256])).

tff(c_298,plain,(
    ! [C_106,B_107,A_108] :
      ( v5_relat_1(C_106,B_107)
      | ~ m1_subset_1(C_106,k1_zfmisc_1(k2_zfmisc_1(A_108,B_107))) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_302,plain,(
    v5_relat_1('#skF_6','#skF_4') ),
    inference(resolution,[status(thm)],[c_78,c_298])).

tff(c_303,plain,(
    ! [B_109,A_110] :
      ( v5_relat_1(B_109,A_110)
      | ~ r1_tarski(k2_relat_1(B_109),A_110)
      | ~ v1_relat_1(B_109) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_317,plain,(
    ! [B_109] :
      ( v5_relat_1(B_109,k2_relat_1(B_109))
      | ~ v1_relat_1(B_109) ) ),
    inference(resolution,[status(thm)],[c_18,c_303])).

tff(c_267,plain,(
    ! [A_98,C_99,B_100] :
      ( r1_tarski(A_98,C_99)
      | ~ r1_tarski(B_100,C_99)
      | ~ r1_tarski(A_98,B_100) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_276,plain,(
    ! [A_98] :
      ( r1_tarski(A_98,'#skF_5')
      | ~ r1_tarski(A_98,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_76,c_267])).

tff(c_387,plain,(
    ! [B_123] :
      ( v5_relat_1(B_123,'#skF_5')
      | ~ v1_relat_1(B_123)
      | ~ r1_tarski(k2_relat_1(B_123),'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_276,c_303])).

tff(c_392,plain,(
    ! [B_18] :
      ( v5_relat_1(B_18,'#skF_5')
      | ~ v5_relat_1(B_18,'#skF_4')
      | ~ v1_relat_1(B_18) ) ),
    inference(resolution,[status(thm)],[c_28,c_387])).

tff(c_414,plain,(
    ! [A_134,A_135,B_136] :
      ( r1_tarski(A_134,A_135)
      | ~ r1_tarski(A_134,k2_relat_1(B_136))
      | ~ v5_relat_1(B_136,A_135)
      | ~ v1_relat_1(B_136) ) ),
    inference(resolution,[status(thm)],[c_28,c_267])).

tff(c_491,plain,(
    ! [B_147,A_148,B_149] :
      ( r1_tarski(k2_relat_1(B_147),A_148)
      | ~ v5_relat_1(B_149,A_148)
      | ~ v1_relat_1(B_149)
      | ~ v5_relat_1(B_147,k2_relat_1(B_149))
      | ~ v1_relat_1(B_147) ) ),
    inference(resolution,[status(thm)],[c_28,c_414])).

tff(c_516,plain,(
    ! [B_151,B_152] :
      ( r1_tarski(k2_relat_1(B_151),'#skF_5')
      | ~ v5_relat_1(B_151,k2_relat_1(B_152))
      | ~ v1_relat_1(B_151)
      | ~ v5_relat_1(B_152,'#skF_4')
      | ~ v1_relat_1(B_152) ) ),
    inference(resolution,[status(thm)],[c_392,c_491])).

tff(c_520,plain,(
    ! [B_109] :
      ( r1_tarski(k2_relat_1(B_109),'#skF_5')
      | ~ v5_relat_1(B_109,'#skF_4')
      | ~ v1_relat_1(B_109) ) ),
    inference(resolution,[status(thm)],[c_317,c_516])).

tff(c_74,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_183])).

tff(c_88,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_74])).

tff(c_80,plain,(
    v1_funct_2('#skF_6','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_183])).

tff(c_395,plain,(
    ! [A_126,B_127,C_128] :
      ( k2_relset_1(A_126,B_127,C_128) = k2_relat_1(C_128)
      | ~ m1_subset_1(C_128,k1_zfmisc_1(k2_zfmisc_1(A_126,B_127))) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_399,plain,(
    k2_relset_1('#skF_3','#skF_4','#skF_6') = k2_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_78,c_395])).

tff(c_1295,plain,(
    ! [B_219,D_220,A_221,C_222] :
      ( k1_xboole_0 = B_219
      | v1_funct_2(D_220,A_221,C_222)
      | ~ r1_tarski(k2_relset_1(A_221,B_219,D_220),C_222)
      | ~ m1_subset_1(D_220,k1_zfmisc_1(k2_zfmisc_1(A_221,B_219)))
      | ~ v1_funct_2(D_220,A_221,B_219)
      | ~ v1_funct_1(D_220) ) ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_1301,plain,(
    ! [C_222] :
      ( k1_xboole_0 = '#skF_4'
      | v1_funct_2('#skF_6','#skF_3',C_222)
      | ~ r1_tarski(k2_relat_1('#skF_6'),C_222)
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4')))
      | ~ v1_funct_2('#skF_6','#skF_3','#skF_4')
      | ~ v1_funct_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_399,c_1295])).

tff(c_1313,plain,(
    ! [C_222] :
      ( k1_xboole_0 = '#skF_4'
      | v1_funct_2('#skF_6','#skF_3',C_222)
      | ~ r1_tarski(k2_relat_1('#skF_6'),C_222) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_80,c_78,c_1301])).

tff(c_1317,plain,(
    ! [C_223] :
      ( v1_funct_2('#skF_6','#skF_3',C_223)
      | ~ r1_tarski(k2_relat_1('#skF_6'),C_223) ) ),
    inference(negUnitSimplification,[status(thm)],[c_88,c_1313])).

tff(c_1321,plain,
    ( v1_funct_2('#skF_6','#skF_3','#skF_5')
    | ~ v5_relat_1('#skF_6','#skF_4')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_520,c_1317])).

tff(c_1342,plain,(
    v1_funct_2('#skF_6','#skF_3','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_260,c_302,c_1321])).

tff(c_1344,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_233,c_1342])).

tff(c_1345,plain,(
    ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_5'))) ),
    inference(splitRight,[status(thm)],[c_84])).

tff(c_1726,plain,(
    ~ r1_tarski(k2_relat_1('#skF_6'),'#skF_5') ),
    inference(resolution,[status(thm)],[c_1699,c_1345])).

tff(c_1740,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1518,c_1726])).

tff(c_1742,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_74])).

tff(c_1741,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_74])).

tff(c_1749,plain,(
    '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1742,c_1741])).

tff(c_6,plain,(
    ! [A_5] :
      ( k1_xboole_0 = A_5
      | ~ v1_xboole_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_1743,plain,(
    ! [A_5] :
      ( A_5 = '#skF_3'
      | ~ v1_xboole_0(A_5) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1741,c_6])).

tff(c_1761,plain,(
    ! [A_5] :
      ( A_5 = '#skF_4'
      | ~ v1_xboole_0(A_5) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1749,c_1743])).

tff(c_1776,plain,(
    ! [A_304] :
      ( k1_relat_1(A_304) = '#skF_4'
      | ~ v1_xboole_0(A_304) ) ),
    inference(resolution,[status(thm)],[c_1771,c_1761])).

tff(c_1786,plain,(
    ! [A_306] :
      ( k1_relat_1(k1_relat_1(A_306)) = '#skF_4'
      | ~ v1_xboole_0(A_306) ) ),
    inference(resolution,[status(thm)],[c_30,c_1776])).

tff(c_1795,plain,(
    ! [A_306] :
      ( v1_xboole_0('#skF_4')
      | ~ v1_xboole_0(k1_relat_1(A_306))
      | ~ v1_xboole_0(A_306) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1786,c_30])).

tff(c_1805,plain,(
    ! [A_307] :
      ( ~ v1_xboole_0(k1_relat_1(A_307))
      | ~ v1_xboole_0(A_307) ) ),
    inference(splitLeft,[status(thm)],[c_1795])).

tff(c_1812,plain,(
    ! [A_19] : ~ v1_xboole_0(A_19) ),
    inference(resolution,[status(thm)],[c_30,c_1805])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_1813,plain,(
    ! [A_1] : r2_hidden('#skF_1'(A_1),A_1) ),
    inference(negUnitSimplification,[status(thm)],[c_1812,c_4])).

tff(c_22,plain,(
    r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_1744,plain,(
    r1_xboole_0('#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1741,c_1741,c_22])).

tff(c_1760,plain,(
    r1_xboole_0('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1749,c_1749,c_1744])).

tff(c_1862,plain,(
    ! [A_330,B_331,C_332] :
      ( ~ r1_xboole_0(A_330,B_331)
      | ~ r2_hidden(C_332,B_331)
      | ~ r2_hidden(C_332,A_330) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_1866,plain,(
    ! [C_333] : ~ r2_hidden(C_333,'#skF_4') ),
    inference(resolution,[status(thm)],[c_1760,c_1862])).

tff(c_1881,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_1813,c_1866])).

tff(c_1882,plain,(
    v1_xboole_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_1795])).

tff(c_1754,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1749,c_78])).

tff(c_2657,plain,(
    ! [C_447,A_448,B_449] :
      ( v1_xboole_0(C_447)
      | ~ m1_subset_1(C_447,k1_zfmisc_1(k2_zfmisc_1(A_448,B_449)))
      | ~ v1_xboole_0(A_448) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_2660,plain,
    ( v1_xboole_0('#skF_6')
    | ~ v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_1754,c_2657])).

tff(c_2663,plain,(
    v1_xboole_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1882,c_2660])).

tff(c_2671,plain,(
    '#skF_6' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_2663,c_1761])).

tff(c_2503,plain,(
    ! [C_412,A_413,B_414] :
      ( v1_relat_1(C_412)
      | ~ m1_subset_1(C_412,k1_zfmisc_1(k2_zfmisc_1(A_413,B_414))) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_2507,plain,(
    v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_1754,c_2503])).

tff(c_2675,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2671,c_2507])).

tff(c_2532,plain,(
    ! [C_421,B_422,A_423] :
      ( v5_relat_1(C_421,B_422)
      | ~ m1_subset_1(C_421,k1_zfmisc_1(k2_zfmisc_1(A_423,B_422))) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_2536,plain,(
    v5_relat_1('#skF_6','#skF_4') ),
    inference(resolution,[status(thm)],[c_1754,c_2532])).

tff(c_2674,plain,(
    v5_relat_1('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2671,c_2536])).

tff(c_2597,plain,(
    ! [A_436,C_437,B_438] :
      ( r1_tarski(A_436,C_437)
      | ~ r1_tarski(B_438,C_437)
      | ~ r1_tarski(A_436,B_438) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_2604,plain,(
    ! [A_439] :
      ( r1_tarski(A_439,'#skF_5')
      | ~ r1_tarski(A_439,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_76,c_2597])).

tff(c_2643,plain,(
    ! [A_445,A_446] :
      ( r1_tarski(A_445,'#skF_5')
      | ~ r1_tarski(A_445,A_446)
      | ~ r1_tarski(A_446,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_2604,c_20])).

tff(c_2756,plain,(
    ! [B_462,A_463] :
      ( r1_tarski(k2_relat_1(B_462),'#skF_5')
      | ~ r1_tarski(A_463,'#skF_4')
      | ~ v5_relat_1(B_462,A_463)
      | ~ v1_relat_1(B_462) ) ),
    inference(resolution,[status(thm)],[c_28,c_2643])).

tff(c_2758,plain,
    ( r1_tarski(k2_relat_1('#skF_4'),'#skF_5')
    | ~ r1_tarski('#skF_4','#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_2674,c_2756])).

tff(c_2765,plain,(
    r1_tarski(k2_relat_1('#skF_4'),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2675,c_18,c_2758])).

tff(c_2678,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2671,c_1754])).

tff(c_2835,plain,(
    ! [D_472,C_473,B_474,A_475] :
      ( m1_subset_1(D_472,k1_zfmisc_1(k2_zfmisc_1(C_473,B_474)))
      | ~ r1_tarski(k2_relat_1(D_472),B_474)
      | ~ m1_subset_1(D_472,k1_zfmisc_1(k2_zfmisc_1(C_473,A_475))) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_2839,plain,(
    ! [B_476] :
      ( m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_4',B_476)))
      | ~ r1_tarski(k2_relat_1('#skF_4'),B_476) ) ),
    inference(resolution,[status(thm)],[c_2678,c_2835])).

tff(c_2066,plain,(
    ! [C_371,A_372,B_373] :
      ( v1_xboole_0(C_371)
      | ~ m1_subset_1(C_371,k1_zfmisc_1(k2_zfmisc_1(A_372,B_373)))
      | ~ v1_xboole_0(A_372) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_2069,plain,
    ( v1_xboole_0('#skF_6')
    | ~ v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_1754,c_2066])).

tff(c_2072,plain,(
    v1_xboole_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1882,c_2069])).

tff(c_2080,plain,(
    '#skF_6' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_2072,c_1761])).

tff(c_1917,plain,
    ( ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_5')))
    | ~ v1_funct_2('#skF_6','#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1749,c_1749,c_84])).

tff(c_1918,plain,(
    ~ v1_funct_2('#skF_6','#skF_4','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_1917])).

tff(c_2085,plain,(
    ~ v1_funct_2('#skF_4','#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2080,c_1918])).

tff(c_1930,plain,(
    ! [C_340,A_341,B_342] :
      ( v1_relat_1(C_340)
      | ~ m1_subset_1(C_340,k1_zfmisc_1(k2_zfmisc_1(A_341,B_342))) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_1934,plain,(
    v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_1754,c_1930])).

tff(c_2084,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2080,c_1934])).

tff(c_1953,plain,(
    ! [C_350,B_351,A_352] :
      ( v5_relat_1(C_350,B_351)
      | ~ m1_subset_1(C_350,k1_zfmisc_1(k2_zfmisc_1(A_352,B_351))) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_1957,plain,(
    v5_relat_1('#skF_6','#skF_4') ),
    inference(resolution,[status(thm)],[c_1754,c_1953])).

tff(c_2082,plain,(
    v5_relat_1('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2080,c_1957])).

tff(c_2010,plain,(
    ! [A_361,C_362,B_363] :
      ( r1_tarski(A_361,C_362)
      | ~ r1_tarski(B_363,C_362)
      | ~ r1_tarski(A_361,B_363) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_2020,plain,(
    ! [A_364] :
      ( r1_tarski(A_364,'#skF_5')
      | ~ r1_tarski(A_364,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_76,c_2010])).

tff(c_2052,plain,(
    ! [A_369,A_370] :
      ( r1_tarski(A_369,'#skF_5')
      | ~ r1_tarski(A_369,A_370)
      | ~ r1_tarski(A_370,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_2020,c_20])).

tff(c_2180,plain,(
    ! [B_390,A_391] :
      ( r1_tarski(k2_relat_1(B_390),'#skF_5')
      | ~ r1_tarski(A_391,'#skF_4')
      | ~ v5_relat_1(B_390,A_391)
      | ~ v1_relat_1(B_390) ) ),
    inference(resolution,[status(thm)],[c_28,c_2052])).

tff(c_2184,plain,
    ( r1_tarski(k2_relat_1('#skF_4'),'#skF_5')
    | ~ r1_tarski('#skF_4','#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_2082,c_2180])).

tff(c_2190,plain,(
    r1_tarski(k2_relat_1('#skF_4'),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2084,c_18,c_2184])).

tff(c_1775,plain,(
    ! [A_303] :
      ( k1_relat_1(A_303) = '#skF_4'
      | ~ v1_xboole_0(A_303) ) ),
    inference(resolution,[status(thm)],[c_1771,c_1761])).

tff(c_1894,plain,(
    k1_relat_1('#skF_4') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_1882,c_1775])).

tff(c_2086,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2080,c_1754])).

tff(c_2250,plain,(
    ! [D_398,C_399,B_400,A_401] :
      ( m1_subset_1(D_398,k1_zfmisc_1(k2_zfmisc_1(C_399,B_400)))
      | ~ r1_tarski(k2_relat_1(D_398),B_400)
      | ~ m1_subset_1(D_398,k1_zfmisc_1(k2_zfmisc_1(C_399,A_401))) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_2254,plain,(
    ! [B_402] :
      ( m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_4',B_402)))
      | ~ r1_tarski(k2_relat_1('#skF_4'),B_402) ) ),
    inference(resolution,[status(thm)],[c_2086,c_2250])).

tff(c_40,plain,(
    ! [A_30,B_31,C_32] :
      ( k1_relset_1(A_30,B_31,C_32) = k1_relat_1(C_32)
      | ~ m1_subset_1(C_32,k1_zfmisc_1(k2_zfmisc_1(A_30,B_31))) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_2276,plain,(
    ! [B_402] :
      ( k1_relset_1('#skF_4',B_402,'#skF_4') = k1_relat_1('#skF_4')
      | ~ r1_tarski(k2_relat_1('#skF_4'),B_402) ) ),
    inference(resolution,[status(thm)],[c_2254,c_40])).

tff(c_2375,plain,(
    ! [B_405] :
      ( k1_relset_1('#skF_4',B_405,'#skF_4') = '#skF_4'
      | ~ r1_tarski(k2_relat_1('#skF_4'),B_405) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1894,c_2276])).

tff(c_2391,plain,(
    k1_relset_1('#skF_4','#skF_5','#skF_4') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_2190,c_2375])).

tff(c_52,plain,(
    ! [C_47,B_46] :
      ( v1_funct_2(C_47,k1_xboole_0,B_46)
      | k1_relset_1(k1_xboole_0,B_46,C_47) != k1_xboole_0
      | ~ m1_subset_1(C_47,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_46))) ) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_2234,plain,(
    ! [C_47,B_46] :
      ( v1_funct_2(C_47,'#skF_4',B_46)
      | k1_relset_1('#skF_4',B_46,C_47) != '#skF_4'
      | ~ m1_subset_1(C_47,k1_zfmisc_1(k2_zfmisc_1('#skF_4',B_46))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1742,c_1742,c_1742,c_1742,c_52])).

tff(c_2480,plain,(
    ! [B_411] :
      ( v1_funct_2('#skF_4','#skF_4',B_411)
      | k1_relset_1('#skF_4',B_411,'#skF_4') != '#skF_4'
      | ~ r1_tarski(k2_relat_1('#skF_4'),B_411) ) ),
    inference(resolution,[status(thm)],[c_2254,c_2234])).

tff(c_2483,plain,
    ( v1_funct_2('#skF_4','#skF_4','#skF_5')
    | k1_relset_1('#skF_4','#skF_5','#skF_4') != '#skF_4' ),
    inference(resolution,[status(thm)],[c_2190,c_2480])).

tff(c_2498,plain,(
    v1_funct_2('#skF_4','#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2391,c_2483])).

tff(c_2500,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2085,c_2498])).

tff(c_2501,plain,(
    ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_5'))) ),
    inference(splitRight,[status(thm)],[c_1917])).

tff(c_2676,plain,(
    ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_5'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2671,c_2501])).

tff(c_2860,plain,(
    ~ r1_tarski(k2_relat_1('#skF_4'),'#skF_5') ),
    inference(resolution,[status(thm)],[c_2839,c_2676])).

tff(c_2890,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2765,c_2860])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:45:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.68/1.89  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.68/1.90  
% 4.68/1.90  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.68/1.91  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_2
% 4.68/1.91  
% 4.68/1.91  %Foreground sorts:
% 4.68/1.91  
% 4.68/1.91  
% 4.68/1.91  %Background operators:
% 4.68/1.91  
% 4.68/1.91  
% 4.68/1.91  %Foreground operators:
% 4.68/1.91  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 4.68/1.91  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.68/1.91  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.68/1.91  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.68/1.91  tff('#skF_1', type, '#skF_1': $i > $i).
% 4.68/1.91  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.68/1.91  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.68/1.91  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 4.68/1.91  tff('#skF_5', type, '#skF_5': $i).
% 4.68/1.91  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.68/1.91  tff('#skF_6', type, '#skF_6': $i).
% 4.68/1.91  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 4.68/1.91  tff('#skF_3', type, '#skF_3': $i).
% 4.68/1.91  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 4.68/1.91  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 4.68/1.91  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.68/1.91  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.68/1.91  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.68/1.91  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.68/1.91  tff('#skF_4', type, '#skF_4': $i).
% 4.68/1.91  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.68/1.91  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 4.68/1.91  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 4.68/1.91  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.68/1.91  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.68/1.91  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.68/1.91  
% 5.05/1.93  tff(f_87, axiom, (![A]: (v1_xboole_0(A) => v1_xboole_0(k1_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc10_relat_1)).
% 5.05/1.93  tff(f_183, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r1_tarski(B, C) => (((B = k1_xboole_0) & ~(A = k1_xboole_0)) | ((v1_funct_1(D) & v1_funct_2(D, A, C)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t9_funct_2)).
% 5.05/1.93  tff(f_91, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 5.05/1.93  tff(f_59, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 5.05/1.93  tff(f_97, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 5.05/1.93  tff(f_83, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 5.05/1.93  tff(f_65, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 5.05/1.93  tff(f_118, axiom, (![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(C, A))) => (r1_tarski(k2_relat_1(D), B) => m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(C, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t14_relset_1)).
% 5.05/1.93  tff(f_112, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 5.05/1.93  tff(f_163, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r1_tarski(k2_relset_1(A, B, D), C) => (((B = k1_xboole_0) & ~(A = k1_xboole_0)) | ((v1_funct_1(D) & v1_funct_2(D, A, C)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_funct_2)).
% 5.05/1.93  tff(f_35, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 5.05/1.93  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 5.05/1.93  tff(f_77, axiom, (![A]: (~(~r1_xboole_0(A, A) & (A = k1_xboole_0)) & ~(~(A = k1_xboole_0) & r1_xboole_0(A, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t66_xboole_1)).
% 5.05/1.93  tff(f_53, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 5.05/1.93  tff(f_104, axiom, (![A, B]: (v1_xboole_0(A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_xboole_0(C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc3_relset_1)).
% 5.05/1.93  tff(f_108, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 5.05/1.93  tff(f_144, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 5.05/1.93  tff(c_30, plain, (![A_19]: (v1_xboole_0(k1_relat_1(A_19)) | ~v1_xboole_0(A_19))), inference(cnfTransformation, [status(thm)], [f_87])).
% 5.05/1.93  tff(c_1771, plain, (![A_303]: (v1_xboole_0(k1_relat_1(A_303)) | ~v1_xboole_0(A_303))), inference(cnfTransformation, [status(thm)], [f_87])).
% 5.05/1.93  tff(c_78, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_183])).
% 5.05/1.93  tff(c_1358, plain, (![C_228, A_229, B_230]: (v1_relat_1(C_228) | ~m1_subset_1(C_228, k1_zfmisc_1(k2_zfmisc_1(A_229, B_230))))), inference(cnfTransformation, [status(thm)], [f_91])).
% 5.05/1.93  tff(c_1362, plain, (v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_78, c_1358])).
% 5.05/1.93  tff(c_18, plain, (![B_12]: (r1_tarski(B_12, B_12))), inference(cnfTransformation, [status(thm)], [f_59])).
% 5.05/1.93  tff(c_1379, plain, (![C_235, B_236, A_237]: (v5_relat_1(C_235, B_236) | ~m1_subset_1(C_235, k1_zfmisc_1(k2_zfmisc_1(A_237, B_236))))), inference(cnfTransformation, [status(thm)], [f_97])).
% 5.05/1.93  tff(c_1383, plain, (v5_relat_1('#skF_6', '#skF_4')), inference(resolution, [status(thm)], [c_78, c_1379])).
% 5.05/1.93  tff(c_28, plain, (![B_18, A_17]: (r1_tarski(k2_relat_1(B_18), A_17) | ~v5_relat_1(B_18, A_17) | ~v1_relat_1(B_18))), inference(cnfTransformation, [status(thm)], [f_83])).
% 5.05/1.93  tff(c_76, plain, (r1_tarski('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_183])).
% 5.05/1.93  tff(c_1439, plain, (![A_249, C_250, B_251]: (r1_tarski(A_249, C_250) | ~r1_tarski(B_251, C_250) | ~r1_tarski(A_249, B_251))), inference(cnfTransformation, [status(thm)], [f_65])).
% 5.05/1.93  tff(c_1459, plain, (![A_253]: (r1_tarski(A_253, '#skF_5') | ~r1_tarski(A_253, '#skF_4'))), inference(resolution, [status(thm)], [c_76, c_1439])).
% 5.05/1.93  tff(c_20, plain, (![A_13, C_15, B_14]: (r1_tarski(A_13, C_15) | ~r1_tarski(B_14, C_15) | ~r1_tarski(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_65])).
% 5.05/1.93  tff(c_1480, plain, (![A_255, A_256]: (r1_tarski(A_255, '#skF_5') | ~r1_tarski(A_255, A_256) | ~r1_tarski(A_256, '#skF_4'))), inference(resolution, [status(thm)], [c_1459, c_20])).
% 5.05/1.93  tff(c_1507, plain, (![B_262, A_263]: (r1_tarski(k2_relat_1(B_262), '#skF_5') | ~r1_tarski(A_263, '#skF_4') | ~v5_relat_1(B_262, A_263) | ~v1_relat_1(B_262))), inference(resolution, [status(thm)], [c_28, c_1480])).
% 5.05/1.93  tff(c_1513, plain, (r1_tarski(k2_relat_1('#skF_6'), '#skF_5') | ~r1_tarski('#skF_4', '#skF_4') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_1383, c_1507])).
% 5.05/1.93  tff(c_1518, plain, (r1_tarski(k2_relat_1('#skF_6'), '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_1362, c_18, c_1513])).
% 5.05/1.93  tff(c_1695, plain, (![D_294, C_295, B_296, A_297]: (m1_subset_1(D_294, k1_zfmisc_1(k2_zfmisc_1(C_295, B_296))) | ~r1_tarski(k2_relat_1(D_294), B_296) | ~m1_subset_1(D_294, k1_zfmisc_1(k2_zfmisc_1(C_295, A_297))))), inference(cnfTransformation, [status(thm)], [f_118])).
% 5.05/1.93  tff(c_1699, plain, (![B_298]: (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_3', B_298))) | ~r1_tarski(k2_relat_1('#skF_6'), B_298))), inference(resolution, [status(thm)], [c_78, c_1695])).
% 5.05/1.93  tff(c_82, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_183])).
% 5.05/1.93  tff(c_72, plain, (~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_5'))) | ~v1_funct_2('#skF_6', '#skF_3', '#skF_5') | ~v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_183])).
% 5.05/1.93  tff(c_84, plain, (~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_5'))) | ~v1_funct_2('#skF_6', '#skF_3', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_82, c_72])).
% 5.05/1.93  tff(c_233, plain, (~v1_funct_2('#skF_6', '#skF_3', '#skF_5')), inference(splitLeft, [status(thm)], [c_84])).
% 5.05/1.93  tff(c_256, plain, (![C_93, A_94, B_95]: (v1_relat_1(C_93) | ~m1_subset_1(C_93, k1_zfmisc_1(k2_zfmisc_1(A_94, B_95))))), inference(cnfTransformation, [status(thm)], [f_91])).
% 5.05/1.93  tff(c_260, plain, (v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_78, c_256])).
% 5.05/1.93  tff(c_298, plain, (![C_106, B_107, A_108]: (v5_relat_1(C_106, B_107) | ~m1_subset_1(C_106, k1_zfmisc_1(k2_zfmisc_1(A_108, B_107))))), inference(cnfTransformation, [status(thm)], [f_97])).
% 5.05/1.93  tff(c_302, plain, (v5_relat_1('#skF_6', '#skF_4')), inference(resolution, [status(thm)], [c_78, c_298])).
% 5.05/1.93  tff(c_303, plain, (![B_109, A_110]: (v5_relat_1(B_109, A_110) | ~r1_tarski(k2_relat_1(B_109), A_110) | ~v1_relat_1(B_109))), inference(cnfTransformation, [status(thm)], [f_83])).
% 5.05/1.93  tff(c_317, plain, (![B_109]: (v5_relat_1(B_109, k2_relat_1(B_109)) | ~v1_relat_1(B_109))), inference(resolution, [status(thm)], [c_18, c_303])).
% 5.05/1.93  tff(c_267, plain, (![A_98, C_99, B_100]: (r1_tarski(A_98, C_99) | ~r1_tarski(B_100, C_99) | ~r1_tarski(A_98, B_100))), inference(cnfTransformation, [status(thm)], [f_65])).
% 5.05/1.93  tff(c_276, plain, (![A_98]: (r1_tarski(A_98, '#skF_5') | ~r1_tarski(A_98, '#skF_4'))), inference(resolution, [status(thm)], [c_76, c_267])).
% 5.05/1.93  tff(c_387, plain, (![B_123]: (v5_relat_1(B_123, '#skF_5') | ~v1_relat_1(B_123) | ~r1_tarski(k2_relat_1(B_123), '#skF_4'))), inference(resolution, [status(thm)], [c_276, c_303])).
% 5.05/1.93  tff(c_392, plain, (![B_18]: (v5_relat_1(B_18, '#skF_5') | ~v5_relat_1(B_18, '#skF_4') | ~v1_relat_1(B_18))), inference(resolution, [status(thm)], [c_28, c_387])).
% 5.05/1.93  tff(c_414, plain, (![A_134, A_135, B_136]: (r1_tarski(A_134, A_135) | ~r1_tarski(A_134, k2_relat_1(B_136)) | ~v5_relat_1(B_136, A_135) | ~v1_relat_1(B_136))), inference(resolution, [status(thm)], [c_28, c_267])).
% 5.05/1.93  tff(c_491, plain, (![B_147, A_148, B_149]: (r1_tarski(k2_relat_1(B_147), A_148) | ~v5_relat_1(B_149, A_148) | ~v1_relat_1(B_149) | ~v5_relat_1(B_147, k2_relat_1(B_149)) | ~v1_relat_1(B_147))), inference(resolution, [status(thm)], [c_28, c_414])).
% 5.05/1.93  tff(c_516, plain, (![B_151, B_152]: (r1_tarski(k2_relat_1(B_151), '#skF_5') | ~v5_relat_1(B_151, k2_relat_1(B_152)) | ~v1_relat_1(B_151) | ~v5_relat_1(B_152, '#skF_4') | ~v1_relat_1(B_152))), inference(resolution, [status(thm)], [c_392, c_491])).
% 5.05/1.93  tff(c_520, plain, (![B_109]: (r1_tarski(k2_relat_1(B_109), '#skF_5') | ~v5_relat_1(B_109, '#skF_4') | ~v1_relat_1(B_109))), inference(resolution, [status(thm)], [c_317, c_516])).
% 5.05/1.93  tff(c_74, plain, (k1_xboole_0='#skF_3' | k1_xboole_0!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_183])).
% 5.05/1.93  tff(c_88, plain, (k1_xboole_0!='#skF_4'), inference(splitLeft, [status(thm)], [c_74])).
% 5.05/1.93  tff(c_80, plain, (v1_funct_2('#skF_6', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_183])).
% 5.05/1.93  tff(c_395, plain, (![A_126, B_127, C_128]: (k2_relset_1(A_126, B_127, C_128)=k2_relat_1(C_128) | ~m1_subset_1(C_128, k1_zfmisc_1(k2_zfmisc_1(A_126, B_127))))), inference(cnfTransformation, [status(thm)], [f_112])).
% 5.05/1.93  tff(c_399, plain, (k2_relset_1('#skF_3', '#skF_4', '#skF_6')=k2_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_78, c_395])).
% 5.05/1.93  tff(c_1295, plain, (![B_219, D_220, A_221, C_222]: (k1_xboole_0=B_219 | v1_funct_2(D_220, A_221, C_222) | ~r1_tarski(k2_relset_1(A_221, B_219, D_220), C_222) | ~m1_subset_1(D_220, k1_zfmisc_1(k2_zfmisc_1(A_221, B_219))) | ~v1_funct_2(D_220, A_221, B_219) | ~v1_funct_1(D_220))), inference(cnfTransformation, [status(thm)], [f_163])).
% 5.05/1.93  tff(c_1301, plain, (![C_222]: (k1_xboole_0='#skF_4' | v1_funct_2('#skF_6', '#skF_3', C_222) | ~r1_tarski(k2_relat_1('#skF_6'), C_222) | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4'))) | ~v1_funct_2('#skF_6', '#skF_3', '#skF_4') | ~v1_funct_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_399, c_1295])).
% 5.05/1.93  tff(c_1313, plain, (![C_222]: (k1_xboole_0='#skF_4' | v1_funct_2('#skF_6', '#skF_3', C_222) | ~r1_tarski(k2_relat_1('#skF_6'), C_222))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_80, c_78, c_1301])).
% 5.05/1.93  tff(c_1317, plain, (![C_223]: (v1_funct_2('#skF_6', '#skF_3', C_223) | ~r1_tarski(k2_relat_1('#skF_6'), C_223))), inference(negUnitSimplification, [status(thm)], [c_88, c_1313])).
% 5.05/1.93  tff(c_1321, plain, (v1_funct_2('#skF_6', '#skF_3', '#skF_5') | ~v5_relat_1('#skF_6', '#skF_4') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_520, c_1317])).
% 5.05/1.93  tff(c_1342, plain, (v1_funct_2('#skF_6', '#skF_3', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_260, c_302, c_1321])).
% 5.05/1.93  tff(c_1344, plain, $false, inference(negUnitSimplification, [status(thm)], [c_233, c_1342])).
% 5.05/1.93  tff(c_1345, plain, (~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_5')))), inference(splitRight, [status(thm)], [c_84])).
% 5.05/1.93  tff(c_1726, plain, (~r1_tarski(k2_relat_1('#skF_6'), '#skF_5')), inference(resolution, [status(thm)], [c_1699, c_1345])).
% 5.05/1.93  tff(c_1740, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1518, c_1726])).
% 5.05/1.93  tff(c_1742, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_74])).
% 5.05/1.93  tff(c_1741, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_74])).
% 5.05/1.93  tff(c_1749, plain, ('#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_1742, c_1741])).
% 5.05/1.93  tff(c_6, plain, (![A_5]: (k1_xboole_0=A_5 | ~v1_xboole_0(A_5))), inference(cnfTransformation, [status(thm)], [f_35])).
% 5.05/1.93  tff(c_1743, plain, (![A_5]: (A_5='#skF_3' | ~v1_xboole_0(A_5))), inference(demodulation, [status(thm), theory('equality')], [c_1741, c_6])).
% 5.05/1.93  tff(c_1761, plain, (![A_5]: (A_5='#skF_4' | ~v1_xboole_0(A_5))), inference(demodulation, [status(thm), theory('equality')], [c_1749, c_1743])).
% 5.05/1.93  tff(c_1776, plain, (![A_304]: (k1_relat_1(A_304)='#skF_4' | ~v1_xboole_0(A_304))), inference(resolution, [status(thm)], [c_1771, c_1761])).
% 5.05/1.93  tff(c_1786, plain, (![A_306]: (k1_relat_1(k1_relat_1(A_306))='#skF_4' | ~v1_xboole_0(A_306))), inference(resolution, [status(thm)], [c_30, c_1776])).
% 5.05/1.93  tff(c_1795, plain, (![A_306]: (v1_xboole_0('#skF_4') | ~v1_xboole_0(k1_relat_1(A_306)) | ~v1_xboole_0(A_306))), inference(superposition, [status(thm), theory('equality')], [c_1786, c_30])).
% 5.05/1.93  tff(c_1805, plain, (![A_307]: (~v1_xboole_0(k1_relat_1(A_307)) | ~v1_xboole_0(A_307))), inference(splitLeft, [status(thm)], [c_1795])).
% 5.05/1.93  tff(c_1812, plain, (![A_19]: (~v1_xboole_0(A_19))), inference(resolution, [status(thm)], [c_30, c_1805])).
% 5.05/1.93  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.05/1.93  tff(c_1813, plain, (![A_1]: (r2_hidden('#skF_1'(A_1), A_1))), inference(negUnitSimplification, [status(thm)], [c_1812, c_4])).
% 5.05/1.93  tff(c_22, plain, (r1_xboole_0(k1_xboole_0, k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_77])).
% 5.05/1.93  tff(c_1744, plain, (r1_xboole_0('#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1741, c_1741, c_22])).
% 5.05/1.93  tff(c_1760, plain, (r1_xboole_0('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1749, c_1749, c_1744])).
% 5.05/1.93  tff(c_1862, plain, (![A_330, B_331, C_332]: (~r1_xboole_0(A_330, B_331) | ~r2_hidden(C_332, B_331) | ~r2_hidden(C_332, A_330))), inference(cnfTransformation, [status(thm)], [f_53])).
% 5.05/1.93  tff(c_1866, plain, (![C_333]: (~r2_hidden(C_333, '#skF_4'))), inference(resolution, [status(thm)], [c_1760, c_1862])).
% 5.05/1.93  tff(c_1881, plain, $false, inference(resolution, [status(thm)], [c_1813, c_1866])).
% 5.05/1.93  tff(c_1882, plain, (v1_xboole_0('#skF_4')), inference(splitRight, [status(thm)], [c_1795])).
% 5.05/1.93  tff(c_1754, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_1749, c_78])).
% 5.05/1.93  tff(c_2657, plain, (![C_447, A_448, B_449]: (v1_xboole_0(C_447) | ~m1_subset_1(C_447, k1_zfmisc_1(k2_zfmisc_1(A_448, B_449))) | ~v1_xboole_0(A_448))), inference(cnfTransformation, [status(thm)], [f_104])).
% 5.05/1.93  tff(c_2660, plain, (v1_xboole_0('#skF_6') | ~v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_1754, c_2657])).
% 5.05/1.93  tff(c_2663, plain, (v1_xboole_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_1882, c_2660])).
% 5.05/1.93  tff(c_2671, plain, ('#skF_6'='#skF_4'), inference(resolution, [status(thm)], [c_2663, c_1761])).
% 5.05/1.93  tff(c_2503, plain, (![C_412, A_413, B_414]: (v1_relat_1(C_412) | ~m1_subset_1(C_412, k1_zfmisc_1(k2_zfmisc_1(A_413, B_414))))), inference(cnfTransformation, [status(thm)], [f_91])).
% 5.05/1.93  tff(c_2507, plain, (v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_1754, c_2503])).
% 5.05/1.93  tff(c_2675, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2671, c_2507])).
% 5.05/1.93  tff(c_2532, plain, (![C_421, B_422, A_423]: (v5_relat_1(C_421, B_422) | ~m1_subset_1(C_421, k1_zfmisc_1(k2_zfmisc_1(A_423, B_422))))), inference(cnfTransformation, [status(thm)], [f_97])).
% 5.05/1.93  tff(c_2536, plain, (v5_relat_1('#skF_6', '#skF_4')), inference(resolution, [status(thm)], [c_1754, c_2532])).
% 5.05/1.93  tff(c_2674, plain, (v5_relat_1('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2671, c_2536])).
% 5.05/1.93  tff(c_2597, plain, (![A_436, C_437, B_438]: (r1_tarski(A_436, C_437) | ~r1_tarski(B_438, C_437) | ~r1_tarski(A_436, B_438))), inference(cnfTransformation, [status(thm)], [f_65])).
% 5.05/1.93  tff(c_2604, plain, (![A_439]: (r1_tarski(A_439, '#skF_5') | ~r1_tarski(A_439, '#skF_4'))), inference(resolution, [status(thm)], [c_76, c_2597])).
% 5.05/1.93  tff(c_2643, plain, (![A_445, A_446]: (r1_tarski(A_445, '#skF_5') | ~r1_tarski(A_445, A_446) | ~r1_tarski(A_446, '#skF_4'))), inference(resolution, [status(thm)], [c_2604, c_20])).
% 5.05/1.93  tff(c_2756, plain, (![B_462, A_463]: (r1_tarski(k2_relat_1(B_462), '#skF_5') | ~r1_tarski(A_463, '#skF_4') | ~v5_relat_1(B_462, A_463) | ~v1_relat_1(B_462))), inference(resolution, [status(thm)], [c_28, c_2643])).
% 5.05/1.93  tff(c_2758, plain, (r1_tarski(k2_relat_1('#skF_4'), '#skF_5') | ~r1_tarski('#skF_4', '#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_2674, c_2756])).
% 5.05/1.93  tff(c_2765, plain, (r1_tarski(k2_relat_1('#skF_4'), '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_2675, c_18, c_2758])).
% 5.05/1.93  tff(c_2678, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_2671, c_1754])).
% 5.05/1.93  tff(c_2835, plain, (![D_472, C_473, B_474, A_475]: (m1_subset_1(D_472, k1_zfmisc_1(k2_zfmisc_1(C_473, B_474))) | ~r1_tarski(k2_relat_1(D_472), B_474) | ~m1_subset_1(D_472, k1_zfmisc_1(k2_zfmisc_1(C_473, A_475))))), inference(cnfTransformation, [status(thm)], [f_118])).
% 5.05/1.93  tff(c_2839, plain, (![B_476]: (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_4', B_476))) | ~r1_tarski(k2_relat_1('#skF_4'), B_476))), inference(resolution, [status(thm)], [c_2678, c_2835])).
% 5.05/1.93  tff(c_2066, plain, (![C_371, A_372, B_373]: (v1_xboole_0(C_371) | ~m1_subset_1(C_371, k1_zfmisc_1(k2_zfmisc_1(A_372, B_373))) | ~v1_xboole_0(A_372))), inference(cnfTransformation, [status(thm)], [f_104])).
% 5.05/1.93  tff(c_2069, plain, (v1_xboole_0('#skF_6') | ~v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_1754, c_2066])).
% 5.05/1.93  tff(c_2072, plain, (v1_xboole_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_1882, c_2069])).
% 5.05/1.93  tff(c_2080, plain, ('#skF_6'='#skF_4'), inference(resolution, [status(thm)], [c_2072, c_1761])).
% 5.05/1.93  tff(c_1917, plain, (~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_5'))) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_1749, c_1749, c_84])).
% 5.05/1.93  tff(c_1918, plain, (~v1_funct_2('#skF_6', '#skF_4', '#skF_5')), inference(splitLeft, [status(thm)], [c_1917])).
% 5.05/1.93  tff(c_2085, plain, (~v1_funct_2('#skF_4', '#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_2080, c_1918])).
% 5.05/1.93  tff(c_1930, plain, (![C_340, A_341, B_342]: (v1_relat_1(C_340) | ~m1_subset_1(C_340, k1_zfmisc_1(k2_zfmisc_1(A_341, B_342))))), inference(cnfTransformation, [status(thm)], [f_91])).
% 5.05/1.93  tff(c_1934, plain, (v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_1754, c_1930])).
% 5.05/1.93  tff(c_2084, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2080, c_1934])).
% 5.05/1.93  tff(c_1953, plain, (![C_350, B_351, A_352]: (v5_relat_1(C_350, B_351) | ~m1_subset_1(C_350, k1_zfmisc_1(k2_zfmisc_1(A_352, B_351))))), inference(cnfTransformation, [status(thm)], [f_97])).
% 5.05/1.93  tff(c_1957, plain, (v5_relat_1('#skF_6', '#skF_4')), inference(resolution, [status(thm)], [c_1754, c_1953])).
% 5.05/1.93  tff(c_2082, plain, (v5_relat_1('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2080, c_1957])).
% 5.05/1.93  tff(c_2010, plain, (![A_361, C_362, B_363]: (r1_tarski(A_361, C_362) | ~r1_tarski(B_363, C_362) | ~r1_tarski(A_361, B_363))), inference(cnfTransformation, [status(thm)], [f_65])).
% 5.05/1.93  tff(c_2020, plain, (![A_364]: (r1_tarski(A_364, '#skF_5') | ~r1_tarski(A_364, '#skF_4'))), inference(resolution, [status(thm)], [c_76, c_2010])).
% 5.05/1.93  tff(c_2052, plain, (![A_369, A_370]: (r1_tarski(A_369, '#skF_5') | ~r1_tarski(A_369, A_370) | ~r1_tarski(A_370, '#skF_4'))), inference(resolution, [status(thm)], [c_2020, c_20])).
% 5.05/1.93  tff(c_2180, plain, (![B_390, A_391]: (r1_tarski(k2_relat_1(B_390), '#skF_5') | ~r1_tarski(A_391, '#skF_4') | ~v5_relat_1(B_390, A_391) | ~v1_relat_1(B_390))), inference(resolution, [status(thm)], [c_28, c_2052])).
% 5.05/1.93  tff(c_2184, plain, (r1_tarski(k2_relat_1('#skF_4'), '#skF_5') | ~r1_tarski('#skF_4', '#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_2082, c_2180])).
% 5.05/1.93  tff(c_2190, plain, (r1_tarski(k2_relat_1('#skF_4'), '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_2084, c_18, c_2184])).
% 5.05/1.93  tff(c_1775, plain, (![A_303]: (k1_relat_1(A_303)='#skF_4' | ~v1_xboole_0(A_303))), inference(resolution, [status(thm)], [c_1771, c_1761])).
% 5.05/1.93  tff(c_1894, plain, (k1_relat_1('#skF_4')='#skF_4'), inference(resolution, [status(thm)], [c_1882, c_1775])).
% 5.05/1.93  tff(c_2086, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_2080, c_1754])).
% 5.05/1.93  tff(c_2250, plain, (![D_398, C_399, B_400, A_401]: (m1_subset_1(D_398, k1_zfmisc_1(k2_zfmisc_1(C_399, B_400))) | ~r1_tarski(k2_relat_1(D_398), B_400) | ~m1_subset_1(D_398, k1_zfmisc_1(k2_zfmisc_1(C_399, A_401))))), inference(cnfTransformation, [status(thm)], [f_118])).
% 5.05/1.93  tff(c_2254, plain, (![B_402]: (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_4', B_402))) | ~r1_tarski(k2_relat_1('#skF_4'), B_402))), inference(resolution, [status(thm)], [c_2086, c_2250])).
% 5.05/1.93  tff(c_40, plain, (![A_30, B_31, C_32]: (k1_relset_1(A_30, B_31, C_32)=k1_relat_1(C_32) | ~m1_subset_1(C_32, k1_zfmisc_1(k2_zfmisc_1(A_30, B_31))))), inference(cnfTransformation, [status(thm)], [f_108])).
% 5.05/1.93  tff(c_2276, plain, (![B_402]: (k1_relset_1('#skF_4', B_402, '#skF_4')=k1_relat_1('#skF_4') | ~r1_tarski(k2_relat_1('#skF_4'), B_402))), inference(resolution, [status(thm)], [c_2254, c_40])).
% 5.05/1.93  tff(c_2375, plain, (![B_405]: (k1_relset_1('#skF_4', B_405, '#skF_4')='#skF_4' | ~r1_tarski(k2_relat_1('#skF_4'), B_405))), inference(demodulation, [status(thm), theory('equality')], [c_1894, c_2276])).
% 5.05/1.93  tff(c_2391, plain, (k1_relset_1('#skF_4', '#skF_5', '#skF_4')='#skF_4'), inference(resolution, [status(thm)], [c_2190, c_2375])).
% 5.05/1.93  tff(c_52, plain, (![C_47, B_46]: (v1_funct_2(C_47, k1_xboole_0, B_46) | k1_relset_1(k1_xboole_0, B_46, C_47)!=k1_xboole_0 | ~m1_subset_1(C_47, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_46))))), inference(cnfTransformation, [status(thm)], [f_144])).
% 5.05/1.93  tff(c_2234, plain, (![C_47, B_46]: (v1_funct_2(C_47, '#skF_4', B_46) | k1_relset_1('#skF_4', B_46, C_47)!='#skF_4' | ~m1_subset_1(C_47, k1_zfmisc_1(k2_zfmisc_1('#skF_4', B_46))))), inference(demodulation, [status(thm), theory('equality')], [c_1742, c_1742, c_1742, c_1742, c_52])).
% 5.05/1.93  tff(c_2480, plain, (![B_411]: (v1_funct_2('#skF_4', '#skF_4', B_411) | k1_relset_1('#skF_4', B_411, '#skF_4')!='#skF_4' | ~r1_tarski(k2_relat_1('#skF_4'), B_411))), inference(resolution, [status(thm)], [c_2254, c_2234])).
% 5.05/1.93  tff(c_2483, plain, (v1_funct_2('#skF_4', '#skF_4', '#skF_5') | k1_relset_1('#skF_4', '#skF_5', '#skF_4')!='#skF_4'), inference(resolution, [status(thm)], [c_2190, c_2480])).
% 5.05/1.93  tff(c_2498, plain, (v1_funct_2('#skF_4', '#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_2391, c_2483])).
% 5.05/1.93  tff(c_2500, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2085, c_2498])).
% 5.05/1.93  tff(c_2501, plain, (~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_5')))), inference(splitRight, [status(thm)], [c_1917])).
% 5.05/1.93  tff(c_2676, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_2671, c_2501])).
% 5.05/1.93  tff(c_2860, plain, (~r1_tarski(k2_relat_1('#skF_4'), '#skF_5')), inference(resolution, [status(thm)], [c_2839, c_2676])).
% 5.05/1.93  tff(c_2890, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2765, c_2860])).
% 5.05/1.93  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.05/1.93  
% 5.05/1.93  Inference rules
% 5.05/1.93  ----------------------
% 5.05/1.93  #Ref     : 0
% 5.05/1.93  #Sup     : 580
% 5.05/1.93  #Fact    : 0
% 5.05/1.93  #Define  : 0
% 5.05/1.93  #Split   : 25
% 5.05/1.93  #Chain   : 0
% 5.05/1.93  #Close   : 0
% 5.05/1.93  
% 5.05/1.93  Ordering : KBO
% 5.05/1.93  
% 5.05/1.93  Simplification rules
% 5.05/1.93  ----------------------
% 5.05/1.93  #Subsume      : 124
% 5.05/1.93  #Demod        : 372
% 5.05/1.93  #Tautology    : 222
% 5.05/1.93  #SimpNegUnit  : 10
% 5.05/1.93  #BackRed      : 50
% 5.05/1.93  
% 5.05/1.93  #Partial instantiations: 0
% 5.05/1.93  #Strategies tried      : 1
% 5.05/1.93  
% 5.05/1.93  Timing (in seconds)
% 5.05/1.93  ----------------------
% 5.05/1.93  Preprocessing        : 0.37
% 5.05/1.93  Parsing              : 0.20
% 5.05/1.93  CNF conversion       : 0.03
% 5.05/1.93  Main loop            : 0.73
% 5.05/1.93  Inferencing          : 0.26
% 5.05/1.93  Reduction            : 0.22
% 5.05/1.93  Demodulation         : 0.15
% 5.05/1.93  BG Simplification    : 0.03
% 5.05/1.93  Subsumption          : 0.16
% 5.05/1.93  Abstraction          : 0.03
% 5.05/1.93  MUC search           : 0.00
% 5.05/1.93  Cooper               : 0.00
% 5.05/1.93  Total                : 1.16
% 5.05/1.93  Index Insertion      : 0.00
% 5.05/1.93  Index Deletion       : 0.00
% 5.05/1.93  Index Matching       : 0.00
% 5.05/1.93  BG Taut test         : 0.00
%------------------------------------------------------------------------------
