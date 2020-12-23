%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:08:05 EST 2020

% Result     : Theorem 3.52s
% Output     : CNFRefutation 3.52s
% Verified   : 
% Statistics : Number of formulae       :  111 ( 269 expanded)
%              Number of leaves         :   37 ( 105 expanded)
%              Depth                    :   10
%              Number of atoms          :  173 ( 602 expanded)
%              Number of equality atoms :   18 (  52 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k2_relset_1 > k9_relat_1 > k7_relat_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_108,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B] :
            ( ~ v1_xboole_0(B)
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(B,A)))
               => ! [D] :
                    ( r2_hidden(D,k2_relset_1(B,A,C))
                  <=> ? [E] :
                        ( m1_subset_1(E,B)
                        & r2_hidden(k4_tarski(E,D),C) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_relset_1)).

tff(f_83,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_73,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_79,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_69,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_63,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_59,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k9_relat_1(C,B))
      <=> ? [D] :
            ( r2_hidden(D,k1_relat_1(C))
            & r2_hidden(k4_tarski(D,A),C)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t143_relat_1)).

tff(f_48,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_89,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(C,A)))
     => ( r1_tarski(k2_relat_1(D),B)
       => m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(C,B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_relset_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

tff(f_37,axiom,(
    ! [A,B,C,D] :
      ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(C,D))
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,D) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l54_zfmisc_1)).

tff(c_40,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_975,plain,(
    ! [A_296,B_297,C_298] :
      ( k2_relset_1(A_296,B_297,C_298) = k2_relat_1(C_298)
      | ~ m1_subset_1(C_298,k1_zfmisc_1(k2_zfmisc_1(A_296,B_297))) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_979,plain,(
    k2_relset_1('#skF_3','#skF_2','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_40,c_975])).

tff(c_700,plain,(
    ! [A_235,B_236,C_237] :
      ( k2_relset_1(A_235,B_236,C_237) = k2_relat_1(C_237)
      | ~ m1_subset_1(C_237,k1_zfmisc_1(k2_zfmisc_1(A_235,B_236))) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_704,plain,(
    k2_relset_1('#skF_3','#skF_2','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_40,c_700])).

tff(c_56,plain,
    ( m1_subset_1('#skF_6','#skF_3')
    | r2_hidden('#skF_7',k2_relset_1('#skF_3','#skF_2','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_77,plain,(
    r2_hidden('#skF_7',k2_relset_1('#skF_3','#skF_2','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_56])).

tff(c_716,plain,(
    r2_hidden('#skF_7',k2_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_704,c_77])).

tff(c_60,plain,(
    ! [C_81,A_82,B_83] :
      ( v1_relat_1(C_81)
      | ~ m1_subset_1(C_81,k1_zfmisc_1(k2_zfmisc_1(A_82,B_83))) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_64,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_40,c_60])).

tff(c_92,plain,(
    ! [C_93,A_94,B_95] :
      ( v4_relat_1(C_93,A_94)
      | ~ m1_subset_1(C_93,k1_zfmisc_1(k2_zfmisc_1(A_94,B_95))) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_96,plain,(
    v4_relat_1('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_40,c_92])).

tff(c_28,plain,(
    ! [B_22,A_21] :
      ( k7_relat_1(B_22,A_21) = B_22
      | ~ v4_relat_1(B_22,A_21)
      | ~ v1_relat_1(B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_99,plain,
    ( k7_relat_1('#skF_4','#skF_3') = '#skF_4'
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_96,c_28])).

tff(c_102,plain,(
    k7_relat_1('#skF_4','#skF_3') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_99])).

tff(c_26,plain,(
    ! [B_20,A_19] :
      ( k2_relat_1(k7_relat_1(B_20,A_19)) = k9_relat_1(B_20,A_19)
      | ~ v1_relat_1(B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_106,plain,
    ( k9_relat_1('#skF_4','#skF_3') = k2_relat_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_102,c_26])).

tff(c_110,plain,(
    k9_relat_1('#skF_4','#skF_3') = k2_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_106])).

tff(c_792,plain,(
    ! [A_249,B_250,C_251] :
      ( r2_hidden('#skF_1'(A_249,B_250,C_251),B_250)
      | ~ r2_hidden(A_249,k9_relat_1(C_251,B_250))
      | ~ v1_relat_1(C_251) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_16,plain,(
    ! [A_11,B_12] :
      ( m1_subset_1(A_11,B_12)
      | ~ r2_hidden(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_811,plain,(
    ! [A_256,B_257,C_258] :
      ( m1_subset_1('#skF_1'(A_256,B_257,C_258),B_257)
      | ~ r2_hidden(A_256,k9_relat_1(C_258,B_257))
      | ~ v1_relat_1(C_258) ) ),
    inference(resolution,[status(thm)],[c_792,c_16])).

tff(c_819,plain,(
    ! [A_256] :
      ( m1_subset_1('#skF_1'(A_256,'#skF_3','#skF_4'),'#skF_3')
      | ~ r2_hidden(A_256,k2_relat_1('#skF_4'))
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_110,c_811])).

tff(c_824,plain,(
    ! [A_259] :
      ( m1_subset_1('#skF_1'(A_259,'#skF_3','#skF_4'),'#skF_3')
      | ~ r2_hidden(A_259,k2_relat_1('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_819])).

tff(c_841,plain,(
    m1_subset_1('#skF_1'('#skF_7','#skF_3','#skF_4'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_716,c_824])).

tff(c_854,plain,(
    ! [A_270,B_271,C_272] :
      ( r2_hidden(k4_tarski('#skF_1'(A_270,B_271,C_272),A_270),C_272)
      | ~ r2_hidden(A_270,k9_relat_1(C_272,B_271))
      | ~ v1_relat_1(C_272) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_451,plain,(
    ! [A_187,B_188,C_189] :
      ( k2_relset_1(A_187,B_188,C_189) = k2_relat_1(C_189)
      | ~ m1_subset_1(C_189,k1_zfmisc_1(k2_zfmisc_1(A_187,B_188))) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_455,plain,(
    k2_relset_1('#skF_3','#skF_2','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_40,c_451])).

tff(c_46,plain,(
    ! [E_77] :
      ( ~ r2_hidden('#skF_5',k2_relset_1('#skF_3','#skF_2','#skF_4'))
      | ~ r2_hidden(k4_tarski(E_77,'#skF_7'),'#skF_4')
      | ~ m1_subset_1(E_77,'#skF_3') ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_420,plain,(
    ~ r2_hidden('#skF_5',k2_relset_1('#skF_3','#skF_2','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_46])).

tff(c_456,plain,(
    ~ r2_hidden('#skF_5',k2_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_455,c_420])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_610,plain,(
    ! [D_224,C_225,B_226,A_227] :
      ( m1_subset_1(D_224,k1_zfmisc_1(k2_zfmisc_1(C_225,B_226)))
      | ~ r1_tarski(k2_relat_1(D_224),B_226)
      | ~ m1_subset_1(D_224,k1_zfmisc_1(k2_zfmisc_1(C_225,A_227))) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_618,plain,(
    ! [B_228] :
      ( m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_3',B_228)))
      | ~ r1_tarski(k2_relat_1('#skF_4'),B_228) ) ),
    inference(resolution,[status(thm)],[c_40,c_610])).

tff(c_297,plain,(
    ! [A_158,B_159,C_160] :
      ( k2_relset_1(A_158,B_159,C_160) = k2_relat_1(C_160)
      | ~ m1_subset_1(C_160,k1_zfmisc_1(k2_zfmisc_1(A_158,B_159))) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_301,plain,(
    k2_relset_1('#skF_3','#skF_2','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_40,c_297])).

tff(c_304,plain,(
    r2_hidden('#skF_7',k2_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_301,c_77])).

tff(c_334,plain,(
    ! [A_166,B_167,C_168] :
      ( r2_hidden('#skF_1'(A_166,B_167,C_168),B_167)
      | ~ r2_hidden(A_166,k9_relat_1(C_168,B_167))
      | ~ v1_relat_1(C_168) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_344,plain,(
    ! [A_173,B_174,C_175] :
      ( m1_subset_1('#skF_1'(A_173,B_174,C_175),B_174)
      | ~ r2_hidden(A_173,k9_relat_1(C_175,B_174))
      | ~ v1_relat_1(C_175) ) ),
    inference(resolution,[status(thm)],[c_334,c_16])).

tff(c_349,plain,(
    ! [A_173] :
      ( m1_subset_1('#skF_1'(A_173,'#skF_3','#skF_4'),'#skF_3')
      | ~ r2_hidden(A_173,k2_relat_1('#skF_4'))
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_110,c_344])).

tff(c_353,plain,(
    ! [A_176] :
      ( m1_subset_1('#skF_1'(A_176,'#skF_3','#skF_4'),'#skF_3')
      | ~ r2_hidden(A_176,k2_relat_1('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_349])).

tff(c_362,plain,(
    m1_subset_1('#skF_1'('#skF_7','#skF_3','#skF_4'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_304,c_353])).

tff(c_371,plain,(
    ! [A_180,B_181,C_182] :
      ( r2_hidden(k4_tarski('#skF_1'(A_180,B_181,C_182),A_180),C_182)
      | ~ r2_hidden(A_180,k9_relat_1(C_182,B_181))
      | ~ v1_relat_1(C_182) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_48,plain,(
    ! [E_77] :
      ( r2_hidden(k4_tarski('#skF_6','#skF_5'),'#skF_4')
      | ~ r2_hidden(k4_tarski(E_77,'#skF_7'),'#skF_4')
      | ~ m1_subset_1(E_77,'#skF_3') ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_295,plain,(
    ! [E_77] :
      ( ~ r2_hidden(k4_tarski(E_77,'#skF_7'),'#skF_4')
      | ~ m1_subset_1(E_77,'#skF_3') ) ),
    inference(splitLeft,[status(thm)],[c_48])).

tff(c_382,plain,(
    ! [B_181] :
      ( ~ m1_subset_1('#skF_1'('#skF_7',B_181,'#skF_4'),'#skF_3')
      | ~ r2_hidden('#skF_7',k9_relat_1('#skF_4',B_181))
      | ~ v1_relat_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_371,c_295])).

tff(c_405,plain,(
    ! [B_183] :
      ( ~ m1_subset_1('#skF_1'('#skF_7',B_183,'#skF_4'),'#skF_3')
      | ~ r2_hidden('#skF_7',k9_relat_1('#skF_4',B_183)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_382])).

tff(c_408,plain,
    ( ~ m1_subset_1('#skF_1'('#skF_7','#skF_3','#skF_4'),'#skF_3')
    | ~ r2_hidden('#skF_7',k2_relat_1('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_110,c_405])).

tff(c_411,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_304,c_362,c_408])).

tff(c_412,plain,(
    r2_hidden(k4_tarski('#skF_6','#skF_5'),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_14,plain,(
    ! [C_10,A_7,B_8] :
      ( r2_hidden(C_10,A_7)
      | ~ r2_hidden(C_10,B_8)
      | ~ m1_subset_1(B_8,k1_zfmisc_1(A_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_421,plain,(
    ! [A_184] :
      ( r2_hidden(k4_tarski('#skF_6','#skF_5'),A_184)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_184)) ) ),
    inference(resolution,[status(thm)],[c_412,c_14])).

tff(c_10,plain,(
    ! [B_4,D_6,A_3,C_5] :
      ( r2_hidden(B_4,D_6)
      | ~ r2_hidden(k4_tarski(A_3,B_4),k2_zfmisc_1(C_5,D_6)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_436,plain,(
    ! [D_6,C_5] :
      ( r2_hidden('#skF_5',D_6)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(C_5,D_6))) ) ),
    inference(resolution,[status(thm)],[c_421,c_10])).

tff(c_658,plain,(
    ! [B_230] :
      ( r2_hidden('#skF_5',B_230)
      | ~ r1_tarski(k2_relat_1('#skF_4'),B_230) ) ),
    inference(resolution,[status(thm)],[c_618,c_436])).

tff(c_662,plain,(
    r2_hidden('#skF_5',k2_relat_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_6,c_658])).

tff(c_666,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_456,c_662])).

tff(c_667,plain,(
    ! [E_77] :
      ( ~ r2_hidden(k4_tarski(E_77,'#skF_7'),'#skF_4')
      | ~ m1_subset_1(E_77,'#skF_3') ) ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_865,plain,(
    ! [B_271] :
      ( ~ m1_subset_1('#skF_1'('#skF_7',B_271,'#skF_4'),'#skF_3')
      | ~ r2_hidden('#skF_7',k9_relat_1('#skF_4',B_271))
      | ~ v1_relat_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_854,c_667])).

tff(c_888,plain,(
    ! [B_273] :
      ( ~ m1_subset_1('#skF_1'('#skF_7',B_273,'#skF_4'),'#skF_3')
      | ~ r2_hidden('#skF_7',k9_relat_1('#skF_4',B_273)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_865])).

tff(c_891,plain,
    ( ~ m1_subset_1('#skF_1'('#skF_7','#skF_3','#skF_4'),'#skF_3')
    | ~ r2_hidden('#skF_7',k2_relat_1('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_110,c_888])).

tff(c_894,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_716,c_841,c_891])).

tff(c_896,plain,(
    ~ r2_hidden('#skF_7',k2_relset_1('#skF_3','#skF_2','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_52,plain,
    ( ~ r2_hidden('#skF_5',k2_relset_1('#skF_3','#skF_2','#skF_4'))
    | r2_hidden('#skF_7',k2_relset_1('#skF_3','#skF_2','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_943,plain,(
    ~ r2_hidden('#skF_5',k2_relset_1('#skF_3','#skF_2','#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_896,c_52])).

tff(c_980,plain,(
    ~ r2_hidden('#skF_5',k2_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_979,c_943])).

tff(c_1186,plain,(
    ! [D_340,C_341,B_342,A_343] :
      ( m1_subset_1(D_340,k1_zfmisc_1(k2_zfmisc_1(C_341,B_342)))
      | ~ r1_tarski(k2_relat_1(D_340),B_342)
      | ~ m1_subset_1(D_340,k1_zfmisc_1(k2_zfmisc_1(C_341,A_343))) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_1202,plain,(
    ! [B_344] :
      ( m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_3',B_344)))
      | ~ r1_tarski(k2_relat_1('#skF_4'),B_344) ) ),
    inference(resolution,[status(thm)],[c_40,c_1186])).

tff(c_54,plain,
    ( r2_hidden(k4_tarski('#skF_6','#skF_5'),'#skF_4')
    | r2_hidden('#skF_7',k2_relset_1('#skF_3','#skF_2','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_935,plain,(
    r2_hidden(k4_tarski('#skF_6','#skF_5'),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_896,c_54])).

tff(c_944,plain,(
    ! [A_292] :
      ( r2_hidden(k4_tarski('#skF_6','#skF_5'),A_292)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_292)) ) ),
    inference(resolution,[status(thm)],[c_935,c_14])).

tff(c_958,plain,(
    ! [D_6,C_5] :
      ( r2_hidden('#skF_5',D_6)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(C_5,D_6))) ) ),
    inference(resolution,[status(thm)],[c_944,c_10])).

tff(c_1242,plain,(
    ! [B_346] :
      ( r2_hidden('#skF_5',B_346)
      | ~ r1_tarski(k2_relat_1('#skF_4'),B_346) ) ),
    inference(resolution,[status(thm)],[c_1202,c_958])).

tff(c_1246,plain,(
    r2_hidden('#skF_5',k2_relat_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_6,c_1242])).

tff(c_1250,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_980,c_1246])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n020.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 19:20:07 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.52/1.55  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.52/1.56  
% 3.52/1.56  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.52/1.56  %$ v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k2_relset_1 > k9_relat_1 > k7_relat_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_4
% 3.52/1.56  
% 3.52/1.56  %Foreground sorts:
% 3.52/1.56  
% 3.52/1.56  
% 3.52/1.56  %Background operators:
% 3.52/1.56  
% 3.52/1.56  
% 3.52/1.56  %Foreground operators:
% 3.52/1.56  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 3.52/1.56  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 3.52/1.56  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.52/1.56  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.52/1.56  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 3.52/1.56  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 3.52/1.56  tff('#skF_7', type, '#skF_7': $i).
% 3.52/1.56  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.52/1.56  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.52/1.56  tff('#skF_5', type, '#skF_5': $i).
% 3.52/1.56  tff('#skF_6', type, '#skF_6': $i).
% 3.52/1.56  tff('#skF_2', type, '#skF_2': $i).
% 3.52/1.56  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 3.52/1.56  tff('#skF_3', type, '#skF_3': $i).
% 3.52/1.56  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.52/1.56  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.52/1.56  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.52/1.56  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.52/1.56  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.52/1.56  tff('#skF_4', type, '#skF_4': $i).
% 3.52/1.56  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.52/1.56  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.52/1.56  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.52/1.56  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.52/1.56  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.52/1.56  
% 3.52/1.58  tff(f_108, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => (![D]: (r2_hidden(D, k2_relset_1(B, A, C)) <=> (?[E]: (m1_subset_1(E, B) & r2_hidden(k4_tarski(E, D), C))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_relset_1)).
% 3.52/1.58  tff(f_83, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 3.52/1.58  tff(f_73, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.52/1.58  tff(f_79, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.52/1.58  tff(f_69, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t209_relat_1)).
% 3.52/1.58  tff(f_63, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_relat_1)).
% 3.52/1.58  tff(f_59, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k9_relat_1(C, B)) <=> (?[D]: ((r2_hidden(D, k1_relat_1(C)) & r2_hidden(k4_tarski(D, A), C)) & r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t143_relat_1)).
% 3.52/1.58  tff(f_48, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_subset)).
% 3.52/1.58  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.52/1.58  tff(f_89, axiom, (![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(C, A))) => (r1_tarski(k2_relat_1(D), B) => m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(C, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t14_relset_1)).
% 3.52/1.58  tff(f_44, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_subset_1)).
% 3.52/1.58  tff(f_37, axiom, (![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(C, D)) <=> (r2_hidden(A, C) & r2_hidden(B, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l54_zfmisc_1)).
% 3.52/1.58  tff(c_40, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_108])).
% 3.52/1.58  tff(c_975, plain, (![A_296, B_297, C_298]: (k2_relset_1(A_296, B_297, C_298)=k2_relat_1(C_298) | ~m1_subset_1(C_298, k1_zfmisc_1(k2_zfmisc_1(A_296, B_297))))), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.52/1.58  tff(c_979, plain, (k2_relset_1('#skF_3', '#skF_2', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_40, c_975])).
% 3.52/1.58  tff(c_700, plain, (![A_235, B_236, C_237]: (k2_relset_1(A_235, B_236, C_237)=k2_relat_1(C_237) | ~m1_subset_1(C_237, k1_zfmisc_1(k2_zfmisc_1(A_235, B_236))))), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.52/1.58  tff(c_704, plain, (k2_relset_1('#skF_3', '#skF_2', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_40, c_700])).
% 3.52/1.58  tff(c_56, plain, (m1_subset_1('#skF_6', '#skF_3') | r2_hidden('#skF_7', k2_relset_1('#skF_3', '#skF_2', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_108])).
% 3.52/1.58  tff(c_77, plain, (r2_hidden('#skF_7', k2_relset_1('#skF_3', '#skF_2', '#skF_4'))), inference(splitLeft, [status(thm)], [c_56])).
% 3.52/1.58  tff(c_716, plain, (r2_hidden('#skF_7', k2_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_704, c_77])).
% 3.52/1.58  tff(c_60, plain, (![C_81, A_82, B_83]: (v1_relat_1(C_81) | ~m1_subset_1(C_81, k1_zfmisc_1(k2_zfmisc_1(A_82, B_83))))), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.52/1.58  tff(c_64, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_40, c_60])).
% 3.52/1.58  tff(c_92, plain, (![C_93, A_94, B_95]: (v4_relat_1(C_93, A_94) | ~m1_subset_1(C_93, k1_zfmisc_1(k2_zfmisc_1(A_94, B_95))))), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.52/1.58  tff(c_96, plain, (v4_relat_1('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_40, c_92])).
% 3.52/1.58  tff(c_28, plain, (![B_22, A_21]: (k7_relat_1(B_22, A_21)=B_22 | ~v4_relat_1(B_22, A_21) | ~v1_relat_1(B_22))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.52/1.58  tff(c_99, plain, (k7_relat_1('#skF_4', '#skF_3')='#skF_4' | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_96, c_28])).
% 3.52/1.58  tff(c_102, plain, (k7_relat_1('#skF_4', '#skF_3')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_64, c_99])).
% 3.52/1.58  tff(c_26, plain, (![B_20, A_19]: (k2_relat_1(k7_relat_1(B_20, A_19))=k9_relat_1(B_20, A_19) | ~v1_relat_1(B_20))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.52/1.58  tff(c_106, plain, (k9_relat_1('#skF_4', '#skF_3')=k2_relat_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_102, c_26])).
% 3.52/1.58  tff(c_110, plain, (k9_relat_1('#skF_4', '#skF_3')=k2_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_106])).
% 3.52/1.58  tff(c_792, plain, (![A_249, B_250, C_251]: (r2_hidden('#skF_1'(A_249, B_250, C_251), B_250) | ~r2_hidden(A_249, k9_relat_1(C_251, B_250)) | ~v1_relat_1(C_251))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.52/1.58  tff(c_16, plain, (![A_11, B_12]: (m1_subset_1(A_11, B_12) | ~r2_hidden(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.52/1.58  tff(c_811, plain, (![A_256, B_257, C_258]: (m1_subset_1('#skF_1'(A_256, B_257, C_258), B_257) | ~r2_hidden(A_256, k9_relat_1(C_258, B_257)) | ~v1_relat_1(C_258))), inference(resolution, [status(thm)], [c_792, c_16])).
% 3.52/1.58  tff(c_819, plain, (![A_256]: (m1_subset_1('#skF_1'(A_256, '#skF_3', '#skF_4'), '#skF_3') | ~r2_hidden(A_256, k2_relat_1('#skF_4')) | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_110, c_811])).
% 3.52/1.58  tff(c_824, plain, (![A_259]: (m1_subset_1('#skF_1'(A_259, '#skF_3', '#skF_4'), '#skF_3') | ~r2_hidden(A_259, k2_relat_1('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_819])).
% 3.52/1.58  tff(c_841, plain, (m1_subset_1('#skF_1'('#skF_7', '#skF_3', '#skF_4'), '#skF_3')), inference(resolution, [status(thm)], [c_716, c_824])).
% 3.52/1.58  tff(c_854, plain, (![A_270, B_271, C_272]: (r2_hidden(k4_tarski('#skF_1'(A_270, B_271, C_272), A_270), C_272) | ~r2_hidden(A_270, k9_relat_1(C_272, B_271)) | ~v1_relat_1(C_272))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.52/1.58  tff(c_451, plain, (![A_187, B_188, C_189]: (k2_relset_1(A_187, B_188, C_189)=k2_relat_1(C_189) | ~m1_subset_1(C_189, k1_zfmisc_1(k2_zfmisc_1(A_187, B_188))))), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.52/1.58  tff(c_455, plain, (k2_relset_1('#skF_3', '#skF_2', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_40, c_451])).
% 3.52/1.58  tff(c_46, plain, (![E_77]: (~r2_hidden('#skF_5', k2_relset_1('#skF_3', '#skF_2', '#skF_4')) | ~r2_hidden(k4_tarski(E_77, '#skF_7'), '#skF_4') | ~m1_subset_1(E_77, '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_108])).
% 3.52/1.58  tff(c_420, plain, (~r2_hidden('#skF_5', k2_relset_1('#skF_3', '#skF_2', '#skF_4'))), inference(splitLeft, [status(thm)], [c_46])).
% 3.52/1.58  tff(c_456, plain, (~r2_hidden('#skF_5', k2_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_455, c_420])).
% 3.52/1.58  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.52/1.58  tff(c_610, plain, (![D_224, C_225, B_226, A_227]: (m1_subset_1(D_224, k1_zfmisc_1(k2_zfmisc_1(C_225, B_226))) | ~r1_tarski(k2_relat_1(D_224), B_226) | ~m1_subset_1(D_224, k1_zfmisc_1(k2_zfmisc_1(C_225, A_227))))), inference(cnfTransformation, [status(thm)], [f_89])).
% 3.52/1.58  tff(c_618, plain, (![B_228]: (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_3', B_228))) | ~r1_tarski(k2_relat_1('#skF_4'), B_228))), inference(resolution, [status(thm)], [c_40, c_610])).
% 3.52/1.58  tff(c_297, plain, (![A_158, B_159, C_160]: (k2_relset_1(A_158, B_159, C_160)=k2_relat_1(C_160) | ~m1_subset_1(C_160, k1_zfmisc_1(k2_zfmisc_1(A_158, B_159))))), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.52/1.58  tff(c_301, plain, (k2_relset_1('#skF_3', '#skF_2', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_40, c_297])).
% 3.52/1.58  tff(c_304, plain, (r2_hidden('#skF_7', k2_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_301, c_77])).
% 3.52/1.58  tff(c_334, plain, (![A_166, B_167, C_168]: (r2_hidden('#skF_1'(A_166, B_167, C_168), B_167) | ~r2_hidden(A_166, k9_relat_1(C_168, B_167)) | ~v1_relat_1(C_168))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.52/1.58  tff(c_344, plain, (![A_173, B_174, C_175]: (m1_subset_1('#skF_1'(A_173, B_174, C_175), B_174) | ~r2_hidden(A_173, k9_relat_1(C_175, B_174)) | ~v1_relat_1(C_175))), inference(resolution, [status(thm)], [c_334, c_16])).
% 3.52/1.58  tff(c_349, plain, (![A_173]: (m1_subset_1('#skF_1'(A_173, '#skF_3', '#skF_4'), '#skF_3') | ~r2_hidden(A_173, k2_relat_1('#skF_4')) | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_110, c_344])).
% 3.52/1.58  tff(c_353, plain, (![A_176]: (m1_subset_1('#skF_1'(A_176, '#skF_3', '#skF_4'), '#skF_3') | ~r2_hidden(A_176, k2_relat_1('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_349])).
% 3.52/1.58  tff(c_362, plain, (m1_subset_1('#skF_1'('#skF_7', '#skF_3', '#skF_4'), '#skF_3')), inference(resolution, [status(thm)], [c_304, c_353])).
% 3.52/1.58  tff(c_371, plain, (![A_180, B_181, C_182]: (r2_hidden(k4_tarski('#skF_1'(A_180, B_181, C_182), A_180), C_182) | ~r2_hidden(A_180, k9_relat_1(C_182, B_181)) | ~v1_relat_1(C_182))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.52/1.58  tff(c_48, plain, (![E_77]: (r2_hidden(k4_tarski('#skF_6', '#skF_5'), '#skF_4') | ~r2_hidden(k4_tarski(E_77, '#skF_7'), '#skF_4') | ~m1_subset_1(E_77, '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_108])).
% 3.52/1.58  tff(c_295, plain, (![E_77]: (~r2_hidden(k4_tarski(E_77, '#skF_7'), '#skF_4') | ~m1_subset_1(E_77, '#skF_3'))), inference(splitLeft, [status(thm)], [c_48])).
% 3.52/1.58  tff(c_382, plain, (![B_181]: (~m1_subset_1('#skF_1'('#skF_7', B_181, '#skF_4'), '#skF_3') | ~r2_hidden('#skF_7', k9_relat_1('#skF_4', B_181)) | ~v1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_371, c_295])).
% 3.52/1.58  tff(c_405, plain, (![B_183]: (~m1_subset_1('#skF_1'('#skF_7', B_183, '#skF_4'), '#skF_3') | ~r2_hidden('#skF_7', k9_relat_1('#skF_4', B_183)))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_382])).
% 3.52/1.58  tff(c_408, plain, (~m1_subset_1('#skF_1'('#skF_7', '#skF_3', '#skF_4'), '#skF_3') | ~r2_hidden('#skF_7', k2_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_110, c_405])).
% 3.52/1.58  tff(c_411, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_304, c_362, c_408])).
% 3.52/1.58  tff(c_412, plain, (r2_hidden(k4_tarski('#skF_6', '#skF_5'), '#skF_4')), inference(splitRight, [status(thm)], [c_48])).
% 3.52/1.58  tff(c_14, plain, (![C_10, A_7, B_8]: (r2_hidden(C_10, A_7) | ~r2_hidden(C_10, B_8) | ~m1_subset_1(B_8, k1_zfmisc_1(A_7)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.52/1.58  tff(c_421, plain, (![A_184]: (r2_hidden(k4_tarski('#skF_6', '#skF_5'), A_184) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_184)))), inference(resolution, [status(thm)], [c_412, c_14])).
% 3.52/1.58  tff(c_10, plain, (![B_4, D_6, A_3, C_5]: (r2_hidden(B_4, D_6) | ~r2_hidden(k4_tarski(A_3, B_4), k2_zfmisc_1(C_5, D_6)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.52/1.58  tff(c_436, plain, (![D_6, C_5]: (r2_hidden('#skF_5', D_6) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(C_5, D_6))))), inference(resolution, [status(thm)], [c_421, c_10])).
% 3.52/1.58  tff(c_658, plain, (![B_230]: (r2_hidden('#skF_5', B_230) | ~r1_tarski(k2_relat_1('#skF_4'), B_230))), inference(resolution, [status(thm)], [c_618, c_436])).
% 3.52/1.58  tff(c_662, plain, (r2_hidden('#skF_5', k2_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_6, c_658])).
% 3.52/1.58  tff(c_666, plain, $false, inference(negUnitSimplification, [status(thm)], [c_456, c_662])).
% 3.52/1.58  tff(c_667, plain, (![E_77]: (~r2_hidden(k4_tarski(E_77, '#skF_7'), '#skF_4') | ~m1_subset_1(E_77, '#skF_3'))), inference(splitRight, [status(thm)], [c_46])).
% 3.52/1.58  tff(c_865, plain, (![B_271]: (~m1_subset_1('#skF_1'('#skF_7', B_271, '#skF_4'), '#skF_3') | ~r2_hidden('#skF_7', k9_relat_1('#skF_4', B_271)) | ~v1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_854, c_667])).
% 3.52/1.58  tff(c_888, plain, (![B_273]: (~m1_subset_1('#skF_1'('#skF_7', B_273, '#skF_4'), '#skF_3') | ~r2_hidden('#skF_7', k9_relat_1('#skF_4', B_273)))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_865])).
% 3.52/1.58  tff(c_891, plain, (~m1_subset_1('#skF_1'('#skF_7', '#skF_3', '#skF_4'), '#skF_3') | ~r2_hidden('#skF_7', k2_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_110, c_888])).
% 3.52/1.58  tff(c_894, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_716, c_841, c_891])).
% 3.52/1.58  tff(c_896, plain, (~r2_hidden('#skF_7', k2_relset_1('#skF_3', '#skF_2', '#skF_4'))), inference(splitRight, [status(thm)], [c_56])).
% 3.52/1.58  tff(c_52, plain, (~r2_hidden('#skF_5', k2_relset_1('#skF_3', '#skF_2', '#skF_4')) | r2_hidden('#skF_7', k2_relset_1('#skF_3', '#skF_2', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_108])).
% 3.52/1.58  tff(c_943, plain, (~r2_hidden('#skF_5', k2_relset_1('#skF_3', '#skF_2', '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_896, c_52])).
% 3.52/1.58  tff(c_980, plain, (~r2_hidden('#skF_5', k2_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_979, c_943])).
% 3.52/1.58  tff(c_1186, plain, (![D_340, C_341, B_342, A_343]: (m1_subset_1(D_340, k1_zfmisc_1(k2_zfmisc_1(C_341, B_342))) | ~r1_tarski(k2_relat_1(D_340), B_342) | ~m1_subset_1(D_340, k1_zfmisc_1(k2_zfmisc_1(C_341, A_343))))), inference(cnfTransformation, [status(thm)], [f_89])).
% 3.52/1.58  tff(c_1202, plain, (![B_344]: (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_3', B_344))) | ~r1_tarski(k2_relat_1('#skF_4'), B_344))), inference(resolution, [status(thm)], [c_40, c_1186])).
% 3.52/1.58  tff(c_54, plain, (r2_hidden(k4_tarski('#skF_6', '#skF_5'), '#skF_4') | r2_hidden('#skF_7', k2_relset_1('#skF_3', '#skF_2', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_108])).
% 3.52/1.58  tff(c_935, plain, (r2_hidden(k4_tarski('#skF_6', '#skF_5'), '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_896, c_54])).
% 3.52/1.58  tff(c_944, plain, (![A_292]: (r2_hidden(k4_tarski('#skF_6', '#skF_5'), A_292) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_292)))), inference(resolution, [status(thm)], [c_935, c_14])).
% 3.52/1.58  tff(c_958, plain, (![D_6, C_5]: (r2_hidden('#skF_5', D_6) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(C_5, D_6))))), inference(resolution, [status(thm)], [c_944, c_10])).
% 3.52/1.58  tff(c_1242, plain, (![B_346]: (r2_hidden('#skF_5', B_346) | ~r1_tarski(k2_relat_1('#skF_4'), B_346))), inference(resolution, [status(thm)], [c_1202, c_958])).
% 3.52/1.58  tff(c_1246, plain, (r2_hidden('#skF_5', k2_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_6, c_1242])).
% 3.52/1.58  tff(c_1250, plain, $false, inference(negUnitSimplification, [status(thm)], [c_980, c_1246])).
% 3.52/1.58  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.52/1.58  
% 3.52/1.58  Inference rules
% 3.52/1.58  ----------------------
% 3.52/1.58  #Ref     : 0
% 3.52/1.58  #Sup     : 254
% 3.52/1.58  #Fact    : 0
% 3.52/1.58  #Define  : 0
% 3.52/1.58  #Split   : 13
% 3.52/1.58  #Chain   : 0
% 3.52/1.58  #Close   : 0
% 3.52/1.58  
% 3.52/1.58  Ordering : KBO
% 3.52/1.58  
% 3.52/1.58  Simplification rules
% 3.52/1.58  ----------------------
% 3.52/1.58  #Subsume      : 22
% 3.52/1.59  #Demod        : 63
% 3.52/1.59  #Tautology    : 58
% 3.52/1.59  #SimpNegUnit  : 4
% 3.52/1.59  #BackRed      : 17
% 3.52/1.59  
% 3.52/1.59  #Partial instantiations: 0
% 3.52/1.59  #Strategies tried      : 1
% 3.52/1.59  
% 3.52/1.59  Timing (in seconds)
% 3.52/1.59  ----------------------
% 3.52/1.59  Preprocessing        : 0.33
% 3.52/1.59  Parsing              : 0.17
% 3.52/1.59  CNF conversion       : 0.03
% 3.52/1.59  Main loop            : 0.49
% 3.52/1.59  Inferencing          : 0.19
% 3.52/1.59  Reduction            : 0.14
% 3.52/1.59  Demodulation         : 0.09
% 3.52/1.59  BG Simplification    : 0.02
% 3.52/1.59  Subsumption          : 0.09
% 3.52/1.59  Abstraction          : 0.02
% 3.52/1.59  MUC search           : 0.00
% 3.52/1.59  Cooper               : 0.00
% 3.52/1.59  Total                : 0.86
% 3.52/1.59  Index Insertion      : 0.00
% 3.52/1.59  Index Deletion       : 0.00
% 3.52/1.59  Index Matching       : 0.00
% 3.52/1.59  BG Taut test         : 0.00
%------------------------------------------------------------------------------
