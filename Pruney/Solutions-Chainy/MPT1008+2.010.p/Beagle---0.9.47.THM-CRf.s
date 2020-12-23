%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:14:27 EST 2020

% Result     : Theorem 3.52s
% Output     : CNFRefutation 3.52s
% Verified   : 
% Statistics : Number of formulae       :  128 ( 406 expanded)
%              Number of leaves         :   51 ( 155 expanded)
%              Depth                    :   18
%              Number of atoms          :  199 ( 838 expanded)
%              Number of equality atoms :   92 ( 347 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_enumset1 > k2_relset_1 > k1_relset_1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k4_tarski > k2_zfmisc_1 > k2_tarski > k1_funct_1 > k11_relat_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3 > #skF_1

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

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

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

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff(k11_relat_1,type,(
    k11_relat_1: ( $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

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

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_164,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,k1_tarski(A),B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A),B))) )
       => ( B != k1_xboole_0
         => k2_relset_1(k1_tarski(A),B,C) = k1_tarski(k1_funct_1(C,A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_funct_2)).

tff(f_112,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_87,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ( k1_relat_1(A) = k1_xboole_0
          | k2_relat_1(A) = k1_xboole_0 )
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).

tff(f_118,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_76,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_63,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_59,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] : k11_relat_1(A,B) = k9_relat_1(A,k1_tarski(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d16_relat_1)).

tff(f_70,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r2_hidden(A,k1_relat_1(B))
      <=> k11_relat_1(B,A) != k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t205_relat_1)).

tff(f_95,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r2_hidden(A,k1_relat_1(B))
       => k11_relat_1(B,A) = k1_tarski(k1_funct_1(B,A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t117_funct_1)).

tff(f_122,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_79,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_103,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( k1_relat_1(B) = k1_tarski(A)
       => k2_relat_1(B) = k1_tarski(k1_funct_1(B,A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_funct_1)).

tff(f_48,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_152,axiom,(
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

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_134,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(B,A)))
     => ( ! [D] :
            ~ ( r2_hidden(D,B)
              & ! [E] : ~ r2_hidden(k4_tarski(D,E),C) )
      <=> k1_relset_1(B,A,C) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_relset_1)).

tff(f_40,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(c_80,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_4'),'#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_164])).

tff(c_156,plain,(
    ! [C_78,A_79,B_80] :
      ( v1_relat_1(C_78)
      | ~ m1_subset_1(C_78,k1_zfmisc_1(k2_zfmisc_1(A_79,B_80))) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_164,plain,(
    v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_80,c_156])).

tff(c_84,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_164])).

tff(c_40,plain,(
    ! [A_28] :
      ( k2_relat_1(A_28) != k1_xboole_0
      | k1_xboole_0 = A_28
      | ~ v1_relat_1(A_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_172,plain,
    ( k2_relat_1('#skF_6') != k1_xboole_0
    | k1_xboole_0 = '#skF_6' ),
    inference(resolution,[status(thm)],[c_164,c_40])).

tff(c_188,plain,(
    k2_relat_1('#skF_6') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_172])).

tff(c_189,plain,(
    ! [C_81,A_82,B_83] :
      ( v4_relat_1(C_81,A_82)
      | ~ m1_subset_1(C_81,k1_zfmisc_1(k2_zfmisc_1(A_82,B_83))) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_197,plain,(
    v4_relat_1('#skF_6',k1_tarski('#skF_4')) ),
    inference(resolution,[status(thm)],[c_80,c_189])).

tff(c_226,plain,(
    ! [B_92,A_93] :
      ( k7_relat_1(B_92,A_93) = B_92
      | ~ v4_relat_1(B_92,A_93)
      | ~ v1_relat_1(B_92) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_229,plain,
    ( k7_relat_1('#skF_6',k1_tarski('#skF_4')) = '#skF_6'
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_197,c_226])).

tff(c_235,plain,(
    k7_relat_1('#skF_6',k1_tarski('#skF_4')) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_164,c_229])).

tff(c_254,plain,(
    ! [B_98,A_99] :
      ( k2_relat_1(k7_relat_1(B_98,A_99)) = k9_relat_1(B_98,A_99)
      | ~ v1_relat_1(B_98) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_263,plain,
    ( k9_relat_1('#skF_6',k1_tarski('#skF_4')) = k2_relat_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_235,c_254])).

tff(c_270,plain,(
    k9_relat_1('#skF_6',k1_tarski('#skF_4')) = k2_relat_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_164,c_263])).

tff(c_26,plain,(
    ! [A_19,B_21] :
      ( k9_relat_1(A_19,k1_tarski(B_21)) = k11_relat_1(A_19,B_21)
      | ~ v1_relat_1(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_295,plain,
    ( k11_relat_1('#skF_6','#skF_4') = k2_relat_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_270,c_26])).

tff(c_302,plain,(
    k11_relat_1('#skF_6','#skF_4') = k2_relat_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_164,c_295])).

tff(c_30,plain,(
    ! [A_24,B_25] :
      ( r2_hidden(A_24,k1_relat_1(B_25))
      | k11_relat_1(B_25,A_24) = k1_xboole_0
      | ~ v1_relat_1(B_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_604,plain,(
    ! [B_154,A_155] :
      ( k1_tarski(k1_funct_1(B_154,A_155)) = k11_relat_1(B_154,A_155)
      | ~ r2_hidden(A_155,k1_relat_1(B_154))
      | ~ v1_funct_1(B_154)
      | ~ v1_relat_1(B_154) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_624,plain,(
    ! [B_156,A_157] :
      ( k1_tarski(k1_funct_1(B_156,A_157)) = k11_relat_1(B_156,A_157)
      | ~ v1_funct_1(B_156)
      | k11_relat_1(B_156,A_157) = k1_xboole_0
      | ~ v1_relat_1(B_156) ) ),
    inference(resolution,[status(thm)],[c_30,c_604])).

tff(c_424,plain,(
    ! [A_120,B_121,C_122] :
      ( k2_relset_1(A_120,B_121,C_122) = k2_relat_1(C_122)
      | ~ m1_subset_1(C_122,k1_zfmisc_1(k2_zfmisc_1(A_120,B_121))) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_432,plain,(
    k2_relset_1(k1_tarski('#skF_4'),'#skF_5','#skF_6') = k2_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_80,c_424])).

tff(c_76,plain,(
    k2_relset_1(k1_tarski('#skF_4'),'#skF_5','#skF_6') != k1_tarski(k1_funct_1('#skF_6','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_164])).

tff(c_442,plain,(
    k1_tarski(k1_funct_1('#skF_6','#skF_4')) != k2_relat_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_432,c_76])).

tff(c_633,plain,
    ( k11_relat_1('#skF_6','#skF_4') != k2_relat_1('#skF_6')
    | ~ v1_funct_1('#skF_6')
    | k11_relat_1('#skF_6','#skF_4') = k1_xboole_0
    | ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_624,c_442])).

tff(c_645,plain,(
    k2_relat_1('#skF_6') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_164,c_302,c_84,c_302,c_633])).

tff(c_647,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_188,c_645])).

tff(c_648,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_172])).

tff(c_38,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_667,plain,(
    k1_relat_1('#skF_6') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_648,c_648,c_38])).

tff(c_649,plain,(
    k2_relat_1('#skF_6') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_172])).

tff(c_678,plain,(
    k2_relat_1('#skF_6') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_648,c_649])).

tff(c_1025,plain,(
    ! [B_222,A_223] :
      ( k1_tarski(k1_funct_1(B_222,A_223)) = k2_relat_1(B_222)
      | k1_tarski(A_223) != k1_relat_1(B_222)
      | ~ v1_funct_1(B_222)
      | ~ v1_relat_1(B_222) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_22,plain,(
    ! [A_15] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_15)) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_665,plain,(
    ! [A_15] : m1_subset_1('#skF_6',k1_zfmisc_1(A_15)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_648,c_22])).

tff(c_892,plain,(
    ! [A_201,B_202,C_203] :
      ( k2_relset_1(A_201,B_202,C_203) = k2_relat_1(C_203)
      | ~ m1_subset_1(C_203,k1_zfmisc_1(k2_zfmisc_1(A_201,B_202))) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_896,plain,(
    ! [A_201,B_202] : k2_relset_1(A_201,B_202,'#skF_6') = k2_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_665,c_892])).

tff(c_898,plain,(
    ! [A_201,B_202] : k2_relset_1(A_201,B_202,'#skF_6') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_678,c_896])).

tff(c_899,plain,(
    k1_tarski(k1_funct_1('#skF_6','#skF_4')) != '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_898,c_76])).

tff(c_1031,plain,
    ( k2_relat_1('#skF_6') != '#skF_6'
    | k1_tarski('#skF_4') != k1_relat_1('#skF_6')
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_1025,c_899])).

tff(c_1040,plain,(
    k1_tarski('#skF_4') != '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_164,c_84,c_667,c_678,c_1031])).

tff(c_78,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_164])).

tff(c_669,plain,(
    '#skF_5' != '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_648,c_78])).

tff(c_82,plain,(
    v1_funct_2('#skF_6',k1_tarski('#skF_4'),'#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_164])).

tff(c_74,plain,(
    ! [B_58,A_57,C_59] :
      ( k1_xboole_0 = B_58
      | k1_relset_1(A_57,B_58,C_59) = A_57
      | ~ v1_funct_2(C_59,A_57,B_58)
      | ~ m1_subset_1(C_59,k1_zfmisc_1(k2_zfmisc_1(A_57,B_58))) ) ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_1199,plain,(
    ! [B_254,A_255,C_256] :
      ( B_254 = '#skF_6'
      | k1_relset_1(A_255,B_254,C_256) = A_255
      | ~ v1_funct_2(C_256,A_255,B_254)
      | ~ m1_subset_1(C_256,k1_zfmisc_1(k2_zfmisc_1(A_255,B_254))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_648,c_74])).

tff(c_1206,plain,(
    ! [B_258,A_259] :
      ( B_258 = '#skF_6'
      | k1_relset_1(A_259,B_258,'#skF_6') = A_259
      | ~ v1_funct_2('#skF_6',A_259,B_258) ) ),
    inference(resolution,[status(thm)],[c_665,c_1199])).

tff(c_1218,plain,
    ( '#skF_5' = '#skF_6'
    | k1_relset_1(k1_tarski('#skF_4'),'#skF_5','#skF_6') = k1_tarski('#skF_4') ),
    inference(resolution,[status(thm)],[c_82,c_1206])).

tff(c_1226,plain,(
    k1_relset_1(k1_tarski('#skF_4'),'#skF_5','#skF_6') = k1_tarski('#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_669,c_1218])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_1302,plain,(
    ! [D_276,A_277,B_278,C_279] :
      ( r2_hidden(k4_tarski(D_276,'#skF_3'(A_277,B_278,C_279,D_276)),C_279)
      | ~ r2_hidden(D_276,B_278)
      | k1_relset_1(B_278,A_277,C_279) != B_278
      | ~ m1_subset_1(C_279,k1_zfmisc_1(k2_zfmisc_1(B_278,A_277))) ) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_650,plain,(
    ! [C_158,A_159,B_160] :
      ( v4_relat_1(C_158,A_159)
      | ~ m1_subset_1(C_158,k1_zfmisc_1(k2_zfmisc_1(A_159,B_160))) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_659,plain,(
    ! [A_159] : v4_relat_1(k1_xboole_0,A_159) ),
    inference(resolution,[status(thm)],[c_22,c_650])).

tff(c_675,plain,(
    ! [A_159] : v4_relat_1('#skF_6',A_159) ),
    inference(demodulation,[status(thm),theory(equality)],[c_648,c_659])).

tff(c_783,plain,(
    ! [B_184,A_185] :
      ( k7_relat_1(B_184,A_185) = B_184
      | ~ v4_relat_1(B_184,A_185)
      | ~ v1_relat_1(B_184) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_786,plain,(
    ! [A_159] :
      ( k7_relat_1('#skF_6',A_159) = '#skF_6'
      | ~ v1_relat_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_675,c_783])).

tff(c_794,plain,(
    ! [A_189] : k7_relat_1('#skF_6',A_189) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_164,c_786])).

tff(c_28,plain,(
    ! [B_23,A_22] :
      ( k2_relat_1(k7_relat_1(B_23,A_22)) = k9_relat_1(B_23,A_22)
      | ~ v1_relat_1(B_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_799,plain,(
    ! [A_189] :
      ( k9_relat_1('#skF_6',A_189) = k2_relat_1('#skF_6')
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_794,c_28])).

tff(c_806,plain,(
    ! [A_190] : k9_relat_1('#skF_6',A_190) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_164,c_678,c_799])).

tff(c_812,plain,(
    ! [B_21] :
      ( k11_relat_1('#skF_6',B_21) = '#skF_6'
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_806,c_26])).

tff(c_821,plain,(
    ! [B_21] : k11_relat_1('#skF_6',B_21) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_164,c_812])).

tff(c_32,plain,(
    ! [B_25,A_24] :
      ( k11_relat_1(B_25,A_24) != k1_xboole_0
      | ~ r2_hidden(A_24,k1_relat_1(B_25))
      | ~ v1_relat_1(B_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_859,plain,(
    ! [B_196,A_197] :
      ( k11_relat_1(B_196,A_197) != '#skF_6'
      | ~ r2_hidden(A_197,k1_relat_1(B_196))
      | ~ v1_relat_1(B_196) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_648,c_32])).

tff(c_865,plain,(
    ! [A_197] :
      ( k11_relat_1('#skF_6',A_197) != '#skF_6'
      | ~ r2_hidden(A_197,'#skF_6')
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_667,c_859])).

tff(c_872,plain,(
    ! [A_197] : ~ r2_hidden(A_197,'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_164,c_821,c_865])).

tff(c_1314,plain,(
    ! [D_276,B_278,A_277] :
      ( ~ r2_hidden(D_276,B_278)
      | k1_relset_1(B_278,A_277,'#skF_6') != B_278
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(B_278,A_277))) ) ),
    inference(resolution,[status(thm)],[c_1302,c_872])).

tff(c_1332,plain,(
    ! [D_280,B_281,A_282] :
      ( ~ r2_hidden(D_280,B_281)
      | k1_relset_1(B_281,A_282,'#skF_6') != B_281 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_665,c_1314])).

tff(c_1351,plain,(
    ! [A_283,A_284,B_285] :
      ( k1_relset_1(A_283,A_284,'#skF_6') != A_283
      | r1_tarski(A_283,B_285) ) ),
    inference(resolution,[status(thm)],[c_6,c_1332])).

tff(c_1359,plain,(
    ! [B_286] : r1_tarski(k1_tarski('#skF_4'),B_286) ),
    inference(superposition,[status(thm),theory(equality)],[c_1226,c_1351])).

tff(c_14,plain,(
    ! [A_8] : r1_tarski(k1_xboole_0,A_8) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_126,plain,(
    ! [B_73,A_74] :
      ( B_73 = A_74
      | ~ r1_tarski(B_73,A_74)
      | ~ r1_tarski(A_74,B_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_135,plain,(
    ! [A_8] :
      ( k1_xboole_0 = A_8
      | ~ r1_tarski(A_8,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_14,c_126])).

tff(c_661,plain,(
    ! [A_8] :
      ( A_8 = '#skF_6'
      | ~ r1_tarski(A_8,'#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_648,c_648,c_135])).

tff(c_1387,plain,(
    k1_tarski('#skF_4') = '#skF_6' ),
    inference(resolution,[status(thm)],[c_1359,c_661])).

tff(c_1402,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1040,c_1387])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:05:49 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.52/1.61  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.52/1.62  
% 3.52/1.62  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.52/1.62  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_enumset1 > k2_relset_1 > k1_relset_1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k4_tarski > k2_zfmisc_1 > k2_tarski > k1_funct_1 > k11_relat_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3 > #skF_1
% 3.52/1.62  
% 3.52/1.62  %Foreground sorts:
% 3.52/1.62  
% 3.52/1.62  
% 3.52/1.62  %Background operators:
% 3.52/1.62  
% 3.52/1.62  
% 3.52/1.62  %Foreground operators:
% 3.52/1.62  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 3.52/1.62  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.52/1.62  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.52/1.62  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.52/1.62  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.52/1.62  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 3.52/1.62  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 3.52/1.62  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.52/1.62  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.52/1.62  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.52/1.62  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.52/1.62  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.52/1.62  tff('#skF_5', type, '#skF_5': $i).
% 3.52/1.62  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.52/1.62  tff(k11_relat_1, type, k11_relat_1: ($i * $i) > $i).
% 3.52/1.62  tff('#skF_6', type, '#skF_6': $i).
% 3.52/1.62  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.52/1.62  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 3.52/1.62  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 3.52/1.62  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.52/1.62  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.52/1.62  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.52/1.62  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.52/1.62  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.52/1.62  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.52/1.62  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.52/1.62  tff('#skF_4', type, '#skF_4': $i).
% 3.52/1.62  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.52/1.62  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.52/1.62  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 3.52/1.62  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.52/1.62  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.52/1.62  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.52/1.62  
% 3.52/1.64  tff(f_164, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, k1_tarski(A), B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A), B)))) => (~(B = k1_xboole_0) => (k2_relset_1(k1_tarski(A), B, C) = k1_tarski(k1_funct_1(C, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t62_funct_2)).
% 3.52/1.64  tff(f_112, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.52/1.64  tff(f_87, axiom, (![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_relat_1)).
% 3.52/1.64  tff(f_118, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.52/1.64  tff(f_76, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t209_relat_1)).
% 3.52/1.64  tff(f_63, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_relat_1)).
% 3.52/1.64  tff(f_59, axiom, (![A]: (v1_relat_1(A) => (![B]: (k11_relat_1(A, B) = k9_relat_1(A, k1_tarski(B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d16_relat_1)).
% 3.52/1.64  tff(f_70, axiom, (![A, B]: (v1_relat_1(B) => (r2_hidden(A, k1_relat_1(B)) <=> ~(k11_relat_1(B, A) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t205_relat_1)).
% 3.52/1.64  tff(f_95, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r2_hidden(A, k1_relat_1(B)) => (k11_relat_1(B, A) = k1_tarski(k1_funct_1(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t117_funct_1)).
% 3.52/1.64  tff(f_122, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 3.52/1.64  tff(f_79, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 3.52/1.64  tff(f_103, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((k1_relat_1(B) = k1_tarski(A)) => (k2_relat_1(B) = k1_tarski(k1_funct_1(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t14_funct_1)).
% 3.52/1.64  tff(f_48, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 3.52/1.64  tff(f_152, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 3.52/1.64  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 3.52/1.64  tff(f_134, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => ((![D]: ~(r2_hidden(D, B) & (![E]: ~r2_hidden(k4_tarski(D, E), C)))) <=> (k1_relset_1(B, A, C) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t22_relset_1)).
% 3.52/1.64  tff(f_40, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 3.52/1.64  tff(f_38, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.52/1.64  tff(c_80, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_4'), '#skF_5')))), inference(cnfTransformation, [status(thm)], [f_164])).
% 3.52/1.64  tff(c_156, plain, (![C_78, A_79, B_80]: (v1_relat_1(C_78) | ~m1_subset_1(C_78, k1_zfmisc_1(k2_zfmisc_1(A_79, B_80))))), inference(cnfTransformation, [status(thm)], [f_112])).
% 3.52/1.64  tff(c_164, plain, (v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_80, c_156])).
% 3.52/1.64  tff(c_84, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_164])).
% 3.52/1.64  tff(c_40, plain, (![A_28]: (k2_relat_1(A_28)!=k1_xboole_0 | k1_xboole_0=A_28 | ~v1_relat_1(A_28))), inference(cnfTransformation, [status(thm)], [f_87])).
% 3.52/1.64  tff(c_172, plain, (k2_relat_1('#skF_6')!=k1_xboole_0 | k1_xboole_0='#skF_6'), inference(resolution, [status(thm)], [c_164, c_40])).
% 3.52/1.64  tff(c_188, plain, (k2_relat_1('#skF_6')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_172])).
% 3.52/1.64  tff(c_189, plain, (![C_81, A_82, B_83]: (v4_relat_1(C_81, A_82) | ~m1_subset_1(C_81, k1_zfmisc_1(k2_zfmisc_1(A_82, B_83))))), inference(cnfTransformation, [status(thm)], [f_118])).
% 3.52/1.64  tff(c_197, plain, (v4_relat_1('#skF_6', k1_tarski('#skF_4'))), inference(resolution, [status(thm)], [c_80, c_189])).
% 3.52/1.64  tff(c_226, plain, (![B_92, A_93]: (k7_relat_1(B_92, A_93)=B_92 | ~v4_relat_1(B_92, A_93) | ~v1_relat_1(B_92))), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.52/1.64  tff(c_229, plain, (k7_relat_1('#skF_6', k1_tarski('#skF_4'))='#skF_6' | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_197, c_226])).
% 3.52/1.64  tff(c_235, plain, (k7_relat_1('#skF_6', k1_tarski('#skF_4'))='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_164, c_229])).
% 3.52/1.64  tff(c_254, plain, (![B_98, A_99]: (k2_relat_1(k7_relat_1(B_98, A_99))=k9_relat_1(B_98, A_99) | ~v1_relat_1(B_98))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.52/1.64  tff(c_263, plain, (k9_relat_1('#skF_6', k1_tarski('#skF_4'))=k2_relat_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_235, c_254])).
% 3.52/1.64  tff(c_270, plain, (k9_relat_1('#skF_6', k1_tarski('#skF_4'))=k2_relat_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_164, c_263])).
% 3.52/1.64  tff(c_26, plain, (![A_19, B_21]: (k9_relat_1(A_19, k1_tarski(B_21))=k11_relat_1(A_19, B_21) | ~v1_relat_1(A_19))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.52/1.64  tff(c_295, plain, (k11_relat_1('#skF_6', '#skF_4')=k2_relat_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_270, c_26])).
% 3.52/1.64  tff(c_302, plain, (k11_relat_1('#skF_6', '#skF_4')=k2_relat_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_164, c_295])).
% 3.52/1.64  tff(c_30, plain, (![A_24, B_25]: (r2_hidden(A_24, k1_relat_1(B_25)) | k11_relat_1(B_25, A_24)=k1_xboole_0 | ~v1_relat_1(B_25))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.52/1.64  tff(c_604, plain, (![B_154, A_155]: (k1_tarski(k1_funct_1(B_154, A_155))=k11_relat_1(B_154, A_155) | ~r2_hidden(A_155, k1_relat_1(B_154)) | ~v1_funct_1(B_154) | ~v1_relat_1(B_154))), inference(cnfTransformation, [status(thm)], [f_95])).
% 3.52/1.64  tff(c_624, plain, (![B_156, A_157]: (k1_tarski(k1_funct_1(B_156, A_157))=k11_relat_1(B_156, A_157) | ~v1_funct_1(B_156) | k11_relat_1(B_156, A_157)=k1_xboole_0 | ~v1_relat_1(B_156))), inference(resolution, [status(thm)], [c_30, c_604])).
% 3.52/1.64  tff(c_424, plain, (![A_120, B_121, C_122]: (k2_relset_1(A_120, B_121, C_122)=k2_relat_1(C_122) | ~m1_subset_1(C_122, k1_zfmisc_1(k2_zfmisc_1(A_120, B_121))))), inference(cnfTransformation, [status(thm)], [f_122])).
% 3.52/1.64  tff(c_432, plain, (k2_relset_1(k1_tarski('#skF_4'), '#skF_5', '#skF_6')=k2_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_80, c_424])).
% 3.52/1.64  tff(c_76, plain, (k2_relset_1(k1_tarski('#skF_4'), '#skF_5', '#skF_6')!=k1_tarski(k1_funct_1('#skF_6', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_164])).
% 3.52/1.64  tff(c_442, plain, (k1_tarski(k1_funct_1('#skF_6', '#skF_4'))!=k2_relat_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_432, c_76])).
% 3.52/1.64  tff(c_633, plain, (k11_relat_1('#skF_6', '#skF_4')!=k2_relat_1('#skF_6') | ~v1_funct_1('#skF_6') | k11_relat_1('#skF_6', '#skF_4')=k1_xboole_0 | ~v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_624, c_442])).
% 3.52/1.64  tff(c_645, plain, (k2_relat_1('#skF_6')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_164, c_302, c_84, c_302, c_633])).
% 3.52/1.64  tff(c_647, plain, $false, inference(negUnitSimplification, [status(thm)], [c_188, c_645])).
% 3.52/1.64  tff(c_648, plain, (k1_xboole_0='#skF_6'), inference(splitRight, [status(thm)], [c_172])).
% 3.52/1.64  tff(c_38, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.52/1.64  tff(c_667, plain, (k1_relat_1('#skF_6')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_648, c_648, c_38])).
% 3.52/1.64  tff(c_649, plain, (k2_relat_1('#skF_6')=k1_xboole_0), inference(splitRight, [status(thm)], [c_172])).
% 3.52/1.64  tff(c_678, plain, (k2_relat_1('#skF_6')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_648, c_649])).
% 3.52/1.64  tff(c_1025, plain, (![B_222, A_223]: (k1_tarski(k1_funct_1(B_222, A_223))=k2_relat_1(B_222) | k1_tarski(A_223)!=k1_relat_1(B_222) | ~v1_funct_1(B_222) | ~v1_relat_1(B_222))), inference(cnfTransformation, [status(thm)], [f_103])).
% 3.52/1.64  tff(c_22, plain, (![A_15]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_15)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.52/1.64  tff(c_665, plain, (![A_15]: (m1_subset_1('#skF_6', k1_zfmisc_1(A_15)))), inference(demodulation, [status(thm), theory('equality')], [c_648, c_22])).
% 3.52/1.64  tff(c_892, plain, (![A_201, B_202, C_203]: (k2_relset_1(A_201, B_202, C_203)=k2_relat_1(C_203) | ~m1_subset_1(C_203, k1_zfmisc_1(k2_zfmisc_1(A_201, B_202))))), inference(cnfTransformation, [status(thm)], [f_122])).
% 3.52/1.64  tff(c_896, plain, (![A_201, B_202]: (k2_relset_1(A_201, B_202, '#skF_6')=k2_relat_1('#skF_6'))), inference(resolution, [status(thm)], [c_665, c_892])).
% 3.52/1.64  tff(c_898, plain, (![A_201, B_202]: (k2_relset_1(A_201, B_202, '#skF_6')='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_678, c_896])).
% 3.52/1.64  tff(c_899, plain, (k1_tarski(k1_funct_1('#skF_6', '#skF_4'))!='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_898, c_76])).
% 3.52/1.64  tff(c_1031, plain, (k2_relat_1('#skF_6')!='#skF_6' | k1_tarski('#skF_4')!=k1_relat_1('#skF_6') | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_1025, c_899])).
% 3.52/1.64  tff(c_1040, plain, (k1_tarski('#skF_4')!='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_164, c_84, c_667, c_678, c_1031])).
% 3.52/1.64  tff(c_78, plain, (k1_xboole_0!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_164])).
% 3.52/1.64  tff(c_669, plain, ('#skF_5'!='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_648, c_78])).
% 3.52/1.64  tff(c_82, plain, (v1_funct_2('#skF_6', k1_tarski('#skF_4'), '#skF_5')), inference(cnfTransformation, [status(thm)], [f_164])).
% 3.52/1.64  tff(c_74, plain, (![B_58, A_57, C_59]: (k1_xboole_0=B_58 | k1_relset_1(A_57, B_58, C_59)=A_57 | ~v1_funct_2(C_59, A_57, B_58) | ~m1_subset_1(C_59, k1_zfmisc_1(k2_zfmisc_1(A_57, B_58))))), inference(cnfTransformation, [status(thm)], [f_152])).
% 3.52/1.64  tff(c_1199, plain, (![B_254, A_255, C_256]: (B_254='#skF_6' | k1_relset_1(A_255, B_254, C_256)=A_255 | ~v1_funct_2(C_256, A_255, B_254) | ~m1_subset_1(C_256, k1_zfmisc_1(k2_zfmisc_1(A_255, B_254))))), inference(demodulation, [status(thm), theory('equality')], [c_648, c_74])).
% 3.52/1.64  tff(c_1206, plain, (![B_258, A_259]: (B_258='#skF_6' | k1_relset_1(A_259, B_258, '#skF_6')=A_259 | ~v1_funct_2('#skF_6', A_259, B_258))), inference(resolution, [status(thm)], [c_665, c_1199])).
% 3.52/1.64  tff(c_1218, plain, ('#skF_5'='#skF_6' | k1_relset_1(k1_tarski('#skF_4'), '#skF_5', '#skF_6')=k1_tarski('#skF_4')), inference(resolution, [status(thm)], [c_82, c_1206])).
% 3.52/1.64  tff(c_1226, plain, (k1_relset_1(k1_tarski('#skF_4'), '#skF_5', '#skF_6')=k1_tarski('#skF_4')), inference(negUnitSimplification, [status(thm)], [c_669, c_1218])).
% 3.52/1.64  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.52/1.64  tff(c_1302, plain, (![D_276, A_277, B_278, C_279]: (r2_hidden(k4_tarski(D_276, '#skF_3'(A_277, B_278, C_279, D_276)), C_279) | ~r2_hidden(D_276, B_278) | k1_relset_1(B_278, A_277, C_279)!=B_278 | ~m1_subset_1(C_279, k1_zfmisc_1(k2_zfmisc_1(B_278, A_277))))), inference(cnfTransformation, [status(thm)], [f_134])).
% 3.52/1.64  tff(c_650, plain, (![C_158, A_159, B_160]: (v4_relat_1(C_158, A_159) | ~m1_subset_1(C_158, k1_zfmisc_1(k2_zfmisc_1(A_159, B_160))))), inference(cnfTransformation, [status(thm)], [f_118])).
% 3.52/1.64  tff(c_659, plain, (![A_159]: (v4_relat_1(k1_xboole_0, A_159))), inference(resolution, [status(thm)], [c_22, c_650])).
% 3.52/1.64  tff(c_675, plain, (![A_159]: (v4_relat_1('#skF_6', A_159))), inference(demodulation, [status(thm), theory('equality')], [c_648, c_659])).
% 3.52/1.64  tff(c_783, plain, (![B_184, A_185]: (k7_relat_1(B_184, A_185)=B_184 | ~v4_relat_1(B_184, A_185) | ~v1_relat_1(B_184))), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.52/1.64  tff(c_786, plain, (![A_159]: (k7_relat_1('#skF_6', A_159)='#skF_6' | ~v1_relat_1('#skF_6'))), inference(resolution, [status(thm)], [c_675, c_783])).
% 3.52/1.64  tff(c_794, plain, (![A_189]: (k7_relat_1('#skF_6', A_189)='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_164, c_786])).
% 3.52/1.64  tff(c_28, plain, (![B_23, A_22]: (k2_relat_1(k7_relat_1(B_23, A_22))=k9_relat_1(B_23, A_22) | ~v1_relat_1(B_23))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.52/1.64  tff(c_799, plain, (![A_189]: (k9_relat_1('#skF_6', A_189)=k2_relat_1('#skF_6') | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_794, c_28])).
% 3.52/1.64  tff(c_806, plain, (![A_190]: (k9_relat_1('#skF_6', A_190)='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_164, c_678, c_799])).
% 3.52/1.64  tff(c_812, plain, (![B_21]: (k11_relat_1('#skF_6', B_21)='#skF_6' | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_806, c_26])).
% 3.52/1.64  tff(c_821, plain, (![B_21]: (k11_relat_1('#skF_6', B_21)='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_164, c_812])).
% 3.52/1.64  tff(c_32, plain, (![B_25, A_24]: (k11_relat_1(B_25, A_24)!=k1_xboole_0 | ~r2_hidden(A_24, k1_relat_1(B_25)) | ~v1_relat_1(B_25))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.52/1.64  tff(c_859, plain, (![B_196, A_197]: (k11_relat_1(B_196, A_197)!='#skF_6' | ~r2_hidden(A_197, k1_relat_1(B_196)) | ~v1_relat_1(B_196))), inference(demodulation, [status(thm), theory('equality')], [c_648, c_32])).
% 3.52/1.64  tff(c_865, plain, (![A_197]: (k11_relat_1('#skF_6', A_197)!='#skF_6' | ~r2_hidden(A_197, '#skF_6') | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_667, c_859])).
% 3.52/1.64  tff(c_872, plain, (![A_197]: (~r2_hidden(A_197, '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_164, c_821, c_865])).
% 3.52/1.64  tff(c_1314, plain, (![D_276, B_278, A_277]: (~r2_hidden(D_276, B_278) | k1_relset_1(B_278, A_277, '#skF_6')!=B_278 | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(B_278, A_277))))), inference(resolution, [status(thm)], [c_1302, c_872])).
% 3.52/1.64  tff(c_1332, plain, (![D_280, B_281, A_282]: (~r2_hidden(D_280, B_281) | k1_relset_1(B_281, A_282, '#skF_6')!=B_281)), inference(demodulation, [status(thm), theory('equality')], [c_665, c_1314])).
% 3.52/1.64  tff(c_1351, plain, (![A_283, A_284, B_285]: (k1_relset_1(A_283, A_284, '#skF_6')!=A_283 | r1_tarski(A_283, B_285))), inference(resolution, [status(thm)], [c_6, c_1332])).
% 3.52/1.64  tff(c_1359, plain, (![B_286]: (r1_tarski(k1_tarski('#skF_4'), B_286))), inference(superposition, [status(thm), theory('equality')], [c_1226, c_1351])).
% 3.52/1.64  tff(c_14, plain, (![A_8]: (r1_tarski(k1_xboole_0, A_8))), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.52/1.64  tff(c_126, plain, (![B_73, A_74]: (B_73=A_74 | ~r1_tarski(B_73, A_74) | ~r1_tarski(A_74, B_73))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.52/1.64  tff(c_135, plain, (![A_8]: (k1_xboole_0=A_8 | ~r1_tarski(A_8, k1_xboole_0))), inference(resolution, [status(thm)], [c_14, c_126])).
% 3.52/1.64  tff(c_661, plain, (![A_8]: (A_8='#skF_6' | ~r1_tarski(A_8, '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_648, c_648, c_135])).
% 3.52/1.64  tff(c_1387, plain, (k1_tarski('#skF_4')='#skF_6'), inference(resolution, [status(thm)], [c_1359, c_661])).
% 3.52/1.64  tff(c_1402, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1040, c_1387])).
% 3.52/1.64  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.52/1.64  
% 3.52/1.64  Inference rules
% 3.52/1.64  ----------------------
% 3.52/1.64  #Ref     : 0
% 3.52/1.64  #Sup     : 265
% 3.52/1.64  #Fact    : 0
% 3.52/1.64  #Define  : 0
% 3.52/1.64  #Split   : 2
% 3.52/1.64  #Chain   : 0
% 3.52/1.64  #Close   : 0
% 3.52/1.64  
% 3.52/1.64  Ordering : KBO
% 3.52/1.64  
% 3.52/1.64  Simplification rules
% 3.52/1.64  ----------------------
% 3.52/1.64  #Subsume      : 18
% 3.52/1.64  #Demod        : 181
% 3.52/1.64  #Tautology    : 149
% 3.52/1.64  #SimpNegUnit  : 4
% 3.52/1.64  #BackRed      : 13
% 3.52/1.64  
% 3.52/1.64  #Partial instantiations: 0
% 3.52/1.64  #Strategies tried      : 1
% 3.52/1.64  
% 3.52/1.64  Timing (in seconds)
% 3.52/1.64  ----------------------
% 3.52/1.65  Preprocessing        : 0.36
% 3.52/1.65  Parsing              : 0.19
% 3.52/1.65  CNF conversion       : 0.03
% 3.52/1.65  Main loop            : 0.44
% 3.52/1.65  Inferencing          : 0.16
% 3.52/1.65  Reduction            : 0.14
% 3.52/1.65  Demodulation         : 0.09
% 3.52/1.65  BG Simplification    : 0.03
% 3.52/1.65  Subsumption          : 0.08
% 3.52/1.65  Abstraction          : 0.02
% 3.52/1.65  MUC search           : 0.00
% 3.52/1.65  Cooper               : 0.00
% 3.52/1.65  Total                : 0.84
% 3.52/1.65  Index Insertion      : 0.00
% 3.52/1.65  Index Deletion       : 0.00
% 3.52/1.65  Index Matching       : 0.00
% 3.52/1.65  BG Taut test         : 0.00
%------------------------------------------------------------------------------
