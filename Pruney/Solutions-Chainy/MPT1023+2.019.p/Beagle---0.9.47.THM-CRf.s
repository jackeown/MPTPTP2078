%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:16:19 EST 2020

% Result     : Theorem 10.88s
% Output     : CNFRefutation 11.18s
% Verified   : 
% Statistics : Number of formulae       :  199 (2044 expanded)
%              Number of leaves         :   37 ( 666 expanded)
%              Depth                    :   12
%              Number of atoms          :  327 (5205 expanded)
%              Number of equality atoms :  126 (1341 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_relset_1,type,(
    r2_relset_1: ( $i * $i * $i * $i ) > $o )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

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

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_55,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

tff(f_132,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ! [D] :
            ( ( v1_funct_1(D)
              & v1_funct_2(D,A,B)
              & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
           => ( ! [E] :
                  ( m1_subset_1(E,A)
                 => k1_funct_1(C,E) = k1_funct_1(D,E) )
             => r2_relset_1(A,B,C,D) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_funct_2)).

tff(f_39,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_45,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_51,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_93,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_81,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

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

tff(f_77,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( ( v1_relat_1(B)
            & v1_funct_1(B) )
         => ( ( k1_relat_1(A) = k1_relat_1(B)
              & ! [C] :
                  ( r2_hidden(C,k1_relat_1(A))
                 => k1_funct_1(A,C) = k1_funct_1(B,C) ) )
           => A = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_funct_1)).

tff(c_101,plain,(
    ! [A_49] :
      ( v1_xboole_0(A_49)
      | r2_hidden('#skF_1'(A_49),A_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_26,plain,(
    ! [A_14,B_15] :
      ( m1_subset_1(A_14,B_15)
      | ~ r2_hidden(A_14,B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_108,plain,(
    ! [A_49] :
      ( m1_subset_1('#skF_1'(A_49),A_49)
      | v1_xboole_0(A_49) ) ),
    inference(resolution,[status(thm)],[c_101,c_26])).

tff(c_130,plain,(
    ! [E_55] :
      ( k1_funct_1('#skF_7',E_55) = k1_funct_1('#skF_6',E_55)
      | ~ m1_subset_1(E_55,'#skF_4') ) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_135,plain,
    ( k1_funct_1('#skF_7','#skF_1'('#skF_4')) = k1_funct_1('#skF_6','#skF_1'('#skF_4'))
    | v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_108,c_130])).

tff(c_209,plain,(
    v1_xboole_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_135])).

tff(c_12,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_147,plain,(
    ! [A_58,B_59] :
      ( r2_hidden('#skF_2'(A_58,B_59),A_58)
      | r1_tarski(A_58,B_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_155,plain,(
    ! [A_58,B_59] :
      ( ~ v1_xboole_0(A_58)
      | r1_tarski(A_58,B_59) ) ),
    inference(resolution,[status(thm)],[c_147,c_2])).

tff(c_220,plain,(
    ! [B_70,A_71] :
      ( B_70 = A_71
      | ~ r1_tarski(B_70,A_71)
      | ~ r1_tarski(A_71,B_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_2484,plain,(
    ! [B_254,A_255] :
      ( B_254 = A_255
      | ~ r1_tarski(B_254,A_255)
      | ~ v1_xboole_0(A_255) ) ),
    inference(resolution,[status(thm)],[c_155,c_220])).

tff(c_2494,plain,(
    ! [B_256,A_257] :
      ( B_256 = A_257
      | ~ v1_xboole_0(B_256)
      | ~ v1_xboole_0(A_257) ) ),
    inference(resolution,[status(thm)],[c_155,c_2484])).

tff(c_2501,plain,(
    ! [A_258] :
      ( A_258 = '#skF_4'
      | ~ v1_xboole_0(A_258) ) ),
    inference(resolution,[status(thm)],[c_209,c_2494])).

tff(c_2510,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_12,c_2501])).

tff(c_2044,plain,(
    ! [B_221,A_222] :
      ( B_221 = A_222
      | ~ r1_tarski(B_221,A_222)
      | ~ v1_xboole_0(A_222) ) ),
    inference(resolution,[status(thm)],[c_155,c_220])).

tff(c_2062,plain,(
    ! [B_223,A_224] :
      ( B_223 = A_224
      | ~ v1_xboole_0(B_223)
      | ~ v1_xboole_0(A_224) ) ),
    inference(resolution,[status(thm)],[c_155,c_2044])).

tff(c_2069,plain,(
    ! [A_225] :
      ( k1_xboole_0 = A_225
      | ~ v1_xboole_0(A_225) ) ),
    inference(resolution,[status(thm)],[c_12,c_2062])).

tff(c_2076,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_209,c_2069])).

tff(c_24,plain,(
    ! [B_13] : k2_zfmisc_1(k1_xboole_0,B_13) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_2093,plain,(
    ! [B_13] : k2_zfmisc_1('#skF_4',B_13) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2076,c_2076,c_24])).

tff(c_66,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_111,plain,(
    ! [A_51,B_52] :
      ( r1_tarski(A_51,B_52)
      | ~ m1_subset_1(A_51,k1_zfmisc_1(B_52)) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_124,plain,(
    r1_tarski('#skF_6',k2_zfmisc_1('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_66,c_111])).

tff(c_230,plain,
    ( k2_zfmisc_1('#skF_4','#skF_5') = '#skF_6'
    | ~ r1_tarski(k2_zfmisc_1('#skF_4','#skF_5'),'#skF_6') ),
    inference(resolution,[status(thm)],[c_124,c_220])).

tff(c_2039,plain,(
    ~ r1_tarski(k2_zfmisc_1('#skF_4','#skF_5'),'#skF_6') ),
    inference(splitLeft,[status(thm)],[c_230])).

tff(c_2043,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_155,c_2039])).

tff(c_2109,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2093,c_2043])).

tff(c_2117,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_209,c_2109])).

tff(c_2118,plain,(
    k2_zfmisc_1('#skF_4','#skF_5') = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_230])).

tff(c_20,plain,(
    ! [B_13,A_12] :
      ( k1_xboole_0 = B_13
      | k1_xboole_0 = A_12
      | k2_zfmisc_1(A_12,B_13) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_2134,plain,
    ( k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 != '#skF_6' ),
    inference(superposition,[status(thm),theory(equality)],[c_2118,c_20])).

tff(c_2452,plain,(
    k1_xboole_0 != '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_2134])).

tff(c_2511,plain,(
    '#skF_6' != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2510,c_2452])).

tff(c_2520,plain,(
    ! [B_13] : k2_zfmisc_1('#skF_4',B_13) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2510,c_2510,c_24])).

tff(c_2553,plain,(
    '#skF_6' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2520,c_2118])).

tff(c_2555,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2511,c_2553])).

tff(c_2557,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_2134])).

tff(c_2584,plain,(
    v1_xboole_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2557,c_12])).

tff(c_2656,plain,(
    ! [B_269,A_270] :
      ( B_269 = A_270
      | ~ r1_tarski(B_269,A_270)
      | ~ v1_xboole_0(A_270) ) ),
    inference(resolution,[status(thm)],[c_155,c_220])).

tff(c_2666,plain,(
    ! [B_271,A_272] :
      ( B_271 = A_272
      | ~ v1_xboole_0(B_271)
      | ~ v1_xboole_0(A_272) ) ),
    inference(resolution,[status(thm)],[c_155,c_2656])).

tff(c_2687,plain,(
    ! [A_275] :
      ( A_275 = '#skF_6'
      | ~ v1_xboole_0(A_275) ) ),
    inference(resolution,[status(thm)],[c_2584,c_2666])).

tff(c_2696,plain,(
    '#skF_6' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_209,c_2687])).

tff(c_2123,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2118,c_66])).

tff(c_2712,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2696,c_2696,c_2123])).

tff(c_2630,plain,(
    ! [B_267] : k2_zfmisc_1('#skF_6',B_267) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2557,c_2557,c_24])).

tff(c_40,plain,(
    ! [A_30,B_31,D_33] :
      ( r2_relset_1(A_30,B_31,D_33,D_33)
      | ~ m1_subset_1(D_33,k1_zfmisc_1(k2_zfmisc_1(A_30,B_31))) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_2637,plain,(
    ! [B_267,D_33] :
      ( r2_relset_1('#skF_6',B_267,D_33,D_33)
      | ~ m1_subset_1(D_33,k1_zfmisc_1('#skF_6')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2630,c_40])).

tff(c_3169,plain,(
    ! [B_312,D_313] :
      ( r2_relset_1('#skF_4',B_312,D_313,D_313)
      | ~ m1_subset_1(D_313,k1_zfmisc_1('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2696,c_2696,c_2637])).

tff(c_3186,plain,(
    ! [B_312] : r2_relset_1('#skF_4',B_312,'#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_2712,c_3169])).

tff(c_2556,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_2134])).

tff(c_2596,plain,
    ( '#skF_6' = '#skF_4'
    | '#skF_5' = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2557,c_2557,c_2556])).

tff(c_2597,plain,(
    '#skF_5' = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_2596])).

tff(c_18,plain,(
    ! [B_11] : r1_tarski(B_11,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_60,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_123,plain,(
    r1_tarski('#skF_7',k2_zfmisc_1('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_60,c_111])).

tff(c_2121,plain,(
    r1_tarski('#skF_7','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2118,c_123])).

tff(c_14,plain,(
    ! [B_11,A_10] :
      ( B_11 = A_10
      | ~ r1_tarski(B_11,A_10)
      | ~ r1_tarski(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_2141,plain,
    ( '#skF_7' = '#skF_6'
    | ~ r1_tarski('#skF_6','#skF_7') ),
    inference(resolution,[status(thm)],[c_2121,c_14])).

tff(c_2160,plain,(
    ~ r1_tarski('#skF_6','#skF_7') ),
    inference(splitLeft,[status(thm)],[c_2141])).

tff(c_2164,plain,(
    ~ v1_xboole_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_155,c_2160])).

tff(c_2231,plain,(
    ! [B_236,A_237] :
      ( B_236 = A_237
      | ~ r1_tarski(B_236,A_237)
      | ~ v1_xboole_0(A_237) ) ),
    inference(resolution,[status(thm)],[c_155,c_220])).

tff(c_2245,plain,(
    ! [B_238,A_239] :
      ( B_238 = A_239
      | ~ v1_xboole_0(B_238)
      | ~ v1_xboole_0(A_239) ) ),
    inference(resolution,[status(thm)],[c_155,c_2231])).

tff(c_2255,plain,(
    ! [A_240] :
      ( k1_xboole_0 = A_240
      | ~ v1_xboole_0(A_240) ) ),
    inference(resolution,[status(thm)],[c_12,c_2245])).

tff(c_2266,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_209,c_2255])).

tff(c_2183,plain,(
    k1_xboole_0 != '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_2134])).

tff(c_2287,plain,(
    '#skF_6' != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2266,c_2183])).

tff(c_2294,plain,(
    ! [B_13] : k2_zfmisc_1('#skF_4',B_13) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2266,c_2266,c_24])).

tff(c_2358,plain,(
    '#skF_6' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2294,c_2118])).

tff(c_2360,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2287,c_2358])).

tff(c_2362,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_2134])).

tff(c_2371,plain,(
    v1_xboole_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2362,c_12])).

tff(c_2374,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2164,c_2371])).

tff(c_2375,plain,(
    '#skF_7' = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_2141])).

tff(c_231,plain,
    ( k2_zfmisc_1('#skF_4','#skF_5') = '#skF_7'
    | ~ r1_tarski(k2_zfmisc_1('#skF_4','#skF_5'),'#skF_7') ),
    inference(resolution,[status(thm)],[c_123,c_220])).

tff(c_2377,plain,
    ( '#skF_7' = '#skF_6'
    | ~ r1_tarski('#skF_6','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2118,c_2118,c_231])).

tff(c_2378,plain,(
    ~ r1_tarski('#skF_6','#skF_7') ),
    inference(splitLeft,[status(thm)],[c_2377])).

tff(c_2396,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_2375,c_2378])).

tff(c_2397,plain,(
    '#skF_7' = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_2377])).

tff(c_56,plain,(
    ~ r2_relset_1('#skF_4','#skF_5','#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_2403,plain,(
    ~ r2_relset_1('#skF_4','#skF_5','#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2397,c_56])).

tff(c_2598,plain,(
    ~ r2_relset_1('#skF_4','#skF_6','#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2597,c_2403])).

tff(c_2701,plain,(
    ~ r2_relset_1('#skF_4','#skF_4','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2696,c_2696,c_2696,c_2598])).

tff(c_3193,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3186,c_2701])).

tff(c_3194,plain,(
    '#skF_6' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_2596])).

tff(c_3203,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3194,c_3194,c_2123])).

tff(c_2582,plain,(
    ! [B_13] : k2_zfmisc_1('#skF_6',B_13) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2557,c_2557,c_24])).

tff(c_3247,plain,(
    ! [B_317] : k2_zfmisc_1('#skF_4',B_317) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3194,c_3194,c_2582])).

tff(c_3684,plain,(
    ! [B_355,D_356] :
      ( r2_relset_1('#skF_4',B_355,D_356,D_356)
      | ~ m1_subset_1(D_356,k1_zfmisc_1('#skF_4')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3247,c_40])).

tff(c_3701,plain,(
    ! [B_355] : r2_relset_1('#skF_4',B_355,'#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_3203,c_3684])).

tff(c_3201,plain,(
    ~ r2_relset_1('#skF_4','#skF_5','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3194,c_3194,c_2403])).

tff(c_3708,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3701,c_3201])).

tff(c_3710,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_135])).

tff(c_12775,plain,(
    ! [A_730,B_731,D_732] :
      ( r2_relset_1(A_730,B_731,D_732,D_732)
      | ~ m1_subset_1(D_732,k1_zfmisc_1(k2_zfmisc_1(A_730,B_731))) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_12801,plain,(
    r2_relset_1('#skF_4','#skF_5','#skF_6','#skF_6') ),
    inference(resolution,[status(thm)],[c_66,c_12775])).

tff(c_157,plain,(
    ! [C_62,A_63,B_64] :
      ( v1_relat_1(C_62)
      | ~ m1_subset_1(C_62,k1_zfmisc_1(k2_zfmisc_1(A_63,B_64))) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_178,plain,(
    v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_60,c_157])).

tff(c_64,plain,(
    v1_funct_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_62,plain,(
    v1_funct_2('#skF_7','#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_12873,plain,(
    ! [A_744,B_745,C_746] :
      ( k1_relset_1(A_744,B_745,C_746) = k1_relat_1(C_746)
      | ~ m1_subset_1(C_746,k1_zfmisc_1(k2_zfmisc_1(A_744,B_745))) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_12906,plain,(
    k1_relset_1('#skF_4','#skF_5','#skF_7') = k1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_60,c_12873])).

tff(c_12984,plain,(
    ! [B_755,A_756,C_757] :
      ( k1_xboole_0 = B_755
      | k1_relset_1(A_756,B_755,C_757) = A_756
      | ~ v1_funct_2(C_757,A_756,B_755)
      | ~ m1_subset_1(C_757,k1_zfmisc_1(k2_zfmisc_1(A_756,B_755))) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_13003,plain,
    ( k1_xboole_0 = '#skF_5'
    | k1_relset_1('#skF_4','#skF_5','#skF_7') = '#skF_4'
    | ~ v1_funct_2('#skF_7','#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_60,c_12984])).

tff(c_13019,plain,
    ( k1_xboole_0 = '#skF_5'
    | k1_relat_1('#skF_7') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_12906,c_13003])).

tff(c_13079,plain,(
    k1_relat_1('#skF_7') = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_13019])).

tff(c_179,plain,(
    v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_66,c_157])).

tff(c_70,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_68,plain,(
    v1_funct_2('#skF_6','#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_12907,plain,(
    k1_relset_1('#skF_4','#skF_5','#skF_6') = k1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_66,c_12873])).

tff(c_13006,plain,
    ( k1_xboole_0 = '#skF_5'
    | k1_relset_1('#skF_4','#skF_5','#skF_6') = '#skF_4'
    | ~ v1_funct_2('#skF_6','#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_66,c_12984])).

tff(c_13022,plain,
    ( k1_xboole_0 = '#skF_5'
    | k1_relat_1('#skF_6') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_12907,c_13006])).

tff(c_13085,plain,(
    k1_relat_1('#skF_6') = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_13022])).

tff(c_13525,plain,(
    ! [A_796,B_797] :
      ( r2_hidden('#skF_3'(A_796,B_797),k1_relat_1(A_796))
      | B_797 = A_796
      | k1_relat_1(B_797) != k1_relat_1(A_796)
      | ~ v1_funct_1(B_797)
      | ~ v1_relat_1(B_797)
      | ~ v1_funct_1(A_796)
      | ~ v1_relat_1(A_796) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_15639,plain,(
    ! [A_894,B_895] :
      ( m1_subset_1('#skF_3'(A_894,B_895),k1_relat_1(A_894))
      | B_895 = A_894
      | k1_relat_1(B_895) != k1_relat_1(A_894)
      | ~ v1_funct_1(B_895)
      | ~ v1_relat_1(B_895)
      | ~ v1_funct_1(A_894)
      | ~ v1_relat_1(A_894) ) ),
    inference(resolution,[status(thm)],[c_13525,c_26])).

tff(c_15642,plain,(
    ! [B_895] :
      ( m1_subset_1('#skF_3'('#skF_6',B_895),'#skF_4')
      | B_895 = '#skF_6'
      | k1_relat_1(B_895) != k1_relat_1('#skF_6')
      | ~ v1_funct_1(B_895)
      | ~ v1_relat_1(B_895)
      | ~ v1_funct_1('#skF_6')
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_13085,c_15639])).

tff(c_21489,plain,(
    ! [B_1031] :
      ( m1_subset_1('#skF_3'('#skF_6',B_1031),'#skF_4')
      | B_1031 = '#skF_6'
      | k1_relat_1(B_1031) != '#skF_4'
      | ~ v1_funct_1(B_1031)
      | ~ v1_relat_1(B_1031) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_179,c_70,c_13085,c_15642])).

tff(c_58,plain,(
    ! [E_41] :
      ( k1_funct_1('#skF_7',E_41) = k1_funct_1('#skF_6',E_41)
      | ~ m1_subset_1(E_41,'#skF_4') ) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_21624,plain,(
    ! [B_1034] :
      ( k1_funct_1('#skF_7','#skF_3'('#skF_6',B_1034)) = k1_funct_1('#skF_6','#skF_3'('#skF_6',B_1034))
      | B_1034 = '#skF_6'
      | k1_relat_1(B_1034) != '#skF_4'
      | ~ v1_funct_1(B_1034)
      | ~ v1_relat_1(B_1034) ) ),
    inference(resolution,[status(thm)],[c_21489,c_58])).

tff(c_32,plain,(
    ! [B_22,A_18] :
      ( k1_funct_1(B_22,'#skF_3'(A_18,B_22)) != k1_funct_1(A_18,'#skF_3'(A_18,B_22))
      | B_22 = A_18
      | k1_relat_1(B_22) != k1_relat_1(A_18)
      | ~ v1_funct_1(B_22)
      | ~ v1_relat_1(B_22)
      | ~ v1_funct_1(A_18)
      | ~ v1_relat_1(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_21631,plain,
    ( k1_relat_1('#skF_7') != k1_relat_1('#skF_6')
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6')
    | '#skF_7' = '#skF_6'
    | k1_relat_1('#skF_7') != '#skF_4'
    | ~ v1_funct_1('#skF_7')
    | ~ v1_relat_1('#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_21624,c_32])).

tff(c_21638,plain,(
    '#skF_7' = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_178,c_64,c_13079,c_179,c_70,c_13079,c_13085,c_21631])).

tff(c_21682,plain,(
    ~ r2_relset_1('#skF_4','#skF_5','#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_21638,c_56])).

tff(c_21694,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12801,c_21682])).

tff(c_21695,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_13022])).

tff(c_21719,plain,(
    v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_21695,c_12])).

tff(c_22,plain,(
    ! [A_12] : k2_zfmisc_1(A_12,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_21718,plain,(
    ! [A_12] : k2_zfmisc_1(A_12,'#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_21695,c_21695,c_22])).

tff(c_3711,plain,(
    ! [B_357,A_358] :
      ( B_357 = A_358
      | ~ r1_tarski(B_357,A_358)
      | ~ r1_tarski(A_358,B_357) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_3769,plain,(
    ! [B_365,A_366] :
      ( B_365 = A_366
      | ~ r1_tarski(B_365,A_366)
      | ~ v1_xboole_0(A_366) ) ),
    inference(resolution,[status(thm)],[c_155,c_3711])).

tff(c_3783,plain,
    ( k2_zfmisc_1('#skF_4','#skF_5') = '#skF_6'
    | ~ v1_xboole_0(k2_zfmisc_1('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_124,c_3769])).

tff(c_12690,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_4','#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_3783])).

tff(c_21751,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_21718,c_12690])).

tff(c_21758,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_21719,c_21751])).

tff(c_21759,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_13019])).

tff(c_21783,plain,(
    v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_21759,c_12])).

tff(c_21782,plain,(
    ! [A_12] : k2_zfmisc_1(A_12,'#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_21759,c_21759,c_22])).

tff(c_21812,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_21782,c_12690])).

tff(c_21819,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_21783,c_21812])).

tff(c_21820,plain,(
    k2_zfmisc_1('#skF_4','#skF_5') = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_3783])).

tff(c_21821,plain,(
    v1_xboole_0(k2_zfmisc_1('#skF_4','#skF_5')) ),
    inference(splitRight,[status(thm)],[c_3783])).

tff(c_21848,plain,(
    v1_xboole_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_21820,c_21821])).

tff(c_3787,plain,(
    ! [B_367,A_368] :
      ( B_367 = A_368
      | ~ v1_xboole_0(B_367)
      | ~ v1_xboole_0(A_368) ) ),
    inference(resolution,[status(thm)],[c_155,c_3769])).

tff(c_3790,plain,(
    ! [A_368] :
      ( k1_xboole_0 = A_368
      | ~ v1_xboole_0(A_368) ) ),
    inference(resolution,[status(thm)],[c_12,c_3787])).

tff(c_21857,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(resolution,[status(thm)],[c_21848,c_3790])).

tff(c_21836,plain,
    ( k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 != '#skF_6' ),
    inference(superposition,[status(thm),theory(equality)],[c_21820,c_20])).

tff(c_22098,plain,
    ( '#skF_5' = '#skF_6'
    | '#skF_6' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_21857,c_21857,c_21857,c_21836])).

tff(c_22099,plain,(
    '#skF_6' = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_22098])).

tff(c_22111,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22099,c_21848])).

tff(c_22117,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3710,c_22111])).

tff(c_22118,plain,(
    '#skF_5' = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_22098])).

tff(c_21823,plain,(
    r1_tarski('#skF_7','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_21820,c_123])).

tff(c_3720,plain,(
    ! [B_59,A_58] :
      ( B_59 = A_58
      | ~ r1_tarski(B_59,A_58)
      | ~ v1_xboole_0(A_58) ) ),
    inference(resolution,[status(thm)],[c_155,c_3711])).

tff(c_21846,plain,
    ( '#skF_7' = '#skF_6'
    | ~ v1_xboole_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_21823,c_3720])).

tff(c_22000,plain,(
    '#skF_7' = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_21848,c_21846])).

tff(c_22006,plain,(
    ~ r2_relset_1('#skF_4','#skF_5','#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22000,c_56])).

tff(c_22120,plain,(
    ~ r2_relset_1('#skF_4','#skF_6','#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22118,c_22006])).

tff(c_21825,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_21820,c_66])).

tff(c_22032,plain,(
    ! [A_1048,B_1049,D_1050] :
      ( r2_relset_1(A_1048,B_1049,D_1050,D_1050)
      | ~ m1_subset_1(D_1050,k1_zfmisc_1(k2_zfmisc_1(A_1048,B_1049))) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_22036,plain,(
    ! [D_1050] :
      ( r2_relset_1('#skF_4','#skF_5',D_1050,D_1050)
      | ~ m1_subset_1(D_1050,k1_zfmisc_1('#skF_6')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_21820,c_22032])).

tff(c_22284,plain,(
    ! [D_1072] :
      ( r2_relset_1('#skF_4','#skF_6',D_1072,D_1072)
      | ~ m1_subset_1(D_1072,k1_zfmisc_1('#skF_6')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22118,c_22036])).

tff(c_22289,plain,(
    r2_relset_1('#skF_4','#skF_6','#skF_6','#skF_6') ),
    inference(resolution,[status(thm)],[c_21825,c_22284])).

tff(c_22303,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_22120,c_22289])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n017.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 13:24:01 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 10.88/4.13  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.88/4.15  
% 10.88/4.15  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.88/4.15  %$ r2_relset_1 > v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_4 > #skF_2
% 10.88/4.15  
% 10.88/4.15  %Foreground sorts:
% 10.88/4.15  
% 10.88/4.15  
% 10.88/4.15  %Background operators:
% 10.88/4.15  
% 10.88/4.15  
% 10.88/4.15  %Foreground operators:
% 10.88/4.15  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 10.88/4.15  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 10.88/4.15  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 10.88/4.15  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 10.88/4.15  tff('#skF_1', type, '#skF_1': $i > $i).
% 10.88/4.15  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 10.88/4.15  tff('#skF_7', type, '#skF_7': $i).
% 10.88/4.15  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 10.88/4.15  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 10.88/4.15  tff('#skF_5', type, '#skF_5': $i).
% 10.88/4.15  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 10.88/4.15  tff('#skF_6', type, '#skF_6': $i).
% 10.88/4.15  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 10.88/4.15  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 10.88/4.15  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 10.88/4.15  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 10.88/4.15  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 10.88/4.15  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 10.88/4.15  tff('#skF_4', type, '#skF_4': $i).
% 10.88/4.15  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 10.88/4.15  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 10.88/4.15  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 10.88/4.15  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 10.88/4.15  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 10.88/4.15  
% 11.18/4.18  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 11.18/4.18  tff(f_55, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_subset)).
% 11.18/4.18  tff(f_132, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((![E]: (m1_subset_1(E, A) => (k1_funct_1(C, E) = k1_funct_1(D, E)))) => r2_relset_1(A, B, C, D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_funct_2)).
% 11.18/4.18  tff(f_39, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 11.18/4.18  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 11.18/4.18  tff(f_45, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 11.18/4.18  tff(f_51, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 11.18/4.18  tff(f_59, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 11.18/4.18  tff(f_93, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 11.18/4.18  tff(f_81, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 11.18/4.18  tff(f_85, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 11.18/4.18  tff(f_111, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 11.18/4.18  tff(f_77, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (((k1_relat_1(A) = k1_relat_1(B)) & (![C]: (r2_hidden(C, k1_relat_1(A)) => (k1_funct_1(A, C) = k1_funct_1(B, C))))) => (A = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t9_funct_1)).
% 11.18/4.18  tff(c_101, plain, (![A_49]: (v1_xboole_0(A_49) | r2_hidden('#skF_1'(A_49), A_49))), inference(cnfTransformation, [status(thm)], [f_31])).
% 11.18/4.18  tff(c_26, plain, (![A_14, B_15]: (m1_subset_1(A_14, B_15) | ~r2_hidden(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_55])).
% 11.18/4.18  tff(c_108, plain, (![A_49]: (m1_subset_1('#skF_1'(A_49), A_49) | v1_xboole_0(A_49))), inference(resolution, [status(thm)], [c_101, c_26])).
% 11.18/4.18  tff(c_130, plain, (![E_55]: (k1_funct_1('#skF_7', E_55)=k1_funct_1('#skF_6', E_55) | ~m1_subset_1(E_55, '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_132])).
% 11.18/4.18  tff(c_135, plain, (k1_funct_1('#skF_7', '#skF_1'('#skF_4'))=k1_funct_1('#skF_6', '#skF_1'('#skF_4')) | v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_108, c_130])).
% 11.18/4.18  tff(c_209, plain, (v1_xboole_0('#skF_4')), inference(splitLeft, [status(thm)], [c_135])).
% 11.18/4.18  tff(c_12, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 11.18/4.18  tff(c_147, plain, (![A_58, B_59]: (r2_hidden('#skF_2'(A_58, B_59), A_58) | r1_tarski(A_58, B_59))), inference(cnfTransformation, [status(thm)], [f_38])).
% 11.18/4.18  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 11.18/4.18  tff(c_155, plain, (![A_58, B_59]: (~v1_xboole_0(A_58) | r1_tarski(A_58, B_59))), inference(resolution, [status(thm)], [c_147, c_2])).
% 11.18/4.18  tff(c_220, plain, (![B_70, A_71]: (B_70=A_71 | ~r1_tarski(B_70, A_71) | ~r1_tarski(A_71, B_70))), inference(cnfTransformation, [status(thm)], [f_45])).
% 11.18/4.18  tff(c_2484, plain, (![B_254, A_255]: (B_254=A_255 | ~r1_tarski(B_254, A_255) | ~v1_xboole_0(A_255))), inference(resolution, [status(thm)], [c_155, c_220])).
% 11.18/4.18  tff(c_2494, plain, (![B_256, A_257]: (B_256=A_257 | ~v1_xboole_0(B_256) | ~v1_xboole_0(A_257))), inference(resolution, [status(thm)], [c_155, c_2484])).
% 11.18/4.18  tff(c_2501, plain, (![A_258]: (A_258='#skF_4' | ~v1_xboole_0(A_258))), inference(resolution, [status(thm)], [c_209, c_2494])).
% 11.18/4.18  tff(c_2510, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_12, c_2501])).
% 11.18/4.18  tff(c_2044, plain, (![B_221, A_222]: (B_221=A_222 | ~r1_tarski(B_221, A_222) | ~v1_xboole_0(A_222))), inference(resolution, [status(thm)], [c_155, c_220])).
% 11.18/4.18  tff(c_2062, plain, (![B_223, A_224]: (B_223=A_224 | ~v1_xboole_0(B_223) | ~v1_xboole_0(A_224))), inference(resolution, [status(thm)], [c_155, c_2044])).
% 11.18/4.18  tff(c_2069, plain, (![A_225]: (k1_xboole_0=A_225 | ~v1_xboole_0(A_225))), inference(resolution, [status(thm)], [c_12, c_2062])).
% 11.18/4.18  tff(c_2076, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_209, c_2069])).
% 11.18/4.18  tff(c_24, plain, (![B_13]: (k2_zfmisc_1(k1_xboole_0, B_13)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_51])).
% 11.18/4.18  tff(c_2093, plain, (![B_13]: (k2_zfmisc_1('#skF_4', B_13)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2076, c_2076, c_24])).
% 11.18/4.18  tff(c_66, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_5')))), inference(cnfTransformation, [status(thm)], [f_132])).
% 11.18/4.18  tff(c_111, plain, (![A_51, B_52]: (r1_tarski(A_51, B_52) | ~m1_subset_1(A_51, k1_zfmisc_1(B_52)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 11.18/4.18  tff(c_124, plain, (r1_tarski('#skF_6', k2_zfmisc_1('#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_66, c_111])).
% 11.18/4.18  tff(c_230, plain, (k2_zfmisc_1('#skF_4', '#skF_5')='#skF_6' | ~r1_tarski(k2_zfmisc_1('#skF_4', '#skF_5'), '#skF_6')), inference(resolution, [status(thm)], [c_124, c_220])).
% 11.18/4.18  tff(c_2039, plain, (~r1_tarski(k2_zfmisc_1('#skF_4', '#skF_5'), '#skF_6')), inference(splitLeft, [status(thm)], [c_230])).
% 11.18/4.18  tff(c_2043, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_155, c_2039])).
% 11.18/4.18  tff(c_2109, plain, (~v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2093, c_2043])).
% 11.18/4.18  tff(c_2117, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_209, c_2109])).
% 11.18/4.18  tff(c_2118, plain, (k2_zfmisc_1('#skF_4', '#skF_5')='#skF_6'), inference(splitRight, [status(thm)], [c_230])).
% 11.18/4.18  tff(c_20, plain, (![B_13, A_12]: (k1_xboole_0=B_13 | k1_xboole_0=A_12 | k2_zfmisc_1(A_12, B_13)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_51])).
% 11.18/4.18  tff(c_2134, plain, (k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4' | k1_xboole_0!='#skF_6'), inference(superposition, [status(thm), theory('equality')], [c_2118, c_20])).
% 11.18/4.18  tff(c_2452, plain, (k1_xboole_0!='#skF_6'), inference(splitLeft, [status(thm)], [c_2134])).
% 11.18/4.18  tff(c_2511, plain, ('#skF_6'!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_2510, c_2452])).
% 11.18/4.18  tff(c_2520, plain, (![B_13]: (k2_zfmisc_1('#skF_4', B_13)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2510, c_2510, c_24])).
% 11.18/4.18  tff(c_2553, plain, ('#skF_6'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_2520, c_2118])).
% 11.18/4.18  tff(c_2555, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2511, c_2553])).
% 11.18/4.18  tff(c_2557, plain, (k1_xboole_0='#skF_6'), inference(splitRight, [status(thm)], [c_2134])).
% 11.18/4.18  tff(c_2584, plain, (v1_xboole_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_2557, c_12])).
% 11.18/4.18  tff(c_2656, plain, (![B_269, A_270]: (B_269=A_270 | ~r1_tarski(B_269, A_270) | ~v1_xboole_0(A_270))), inference(resolution, [status(thm)], [c_155, c_220])).
% 11.18/4.18  tff(c_2666, plain, (![B_271, A_272]: (B_271=A_272 | ~v1_xboole_0(B_271) | ~v1_xboole_0(A_272))), inference(resolution, [status(thm)], [c_155, c_2656])).
% 11.18/4.18  tff(c_2687, plain, (![A_275]: (A_275='#skF_6' | ~v1_xboole_0(A_275))), inference(resolution, [status(thm)], [c_2584, c_2666])).
% 11.18/4.18  tff(c_2696, plain, ('#skF_6'='#skF_4'), inference(resolution, [status(thm)], [c_209, c_2687])).
% 11.18/4.18  tff(c_2123, plain, (m1_subset_1('#skF_6', k1_zfmisc_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_2118, c_66])).
% 11.18/4.18  tff(c_2712, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_2696, c_2696, c_2123])).
% 11.18/4.18  tff(c_2630, plain, (![B_267]: (k2_zfmisc_1('#skF_6', B_267)='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_2557, c_2557, c_24])).
% 11.18/4.18  tff(c_40, plain, (![A_30, B_31, D_33]: (r2_relset_1(A_30, B_31, D_33, D_33) | ~m1_subset_1(D_33, k1_zfmisc_1(k2_zfmisc_1(A_30, B_31))))), inference(cnfTransformation, [status(thm)], [f_93])).
% 11.18/4.18  tff(c_2637, plain, (![B_267, D_33]: (r2_relset_1('#skF_6', B_267, D_33, D_33) | ~m1_subset_1(D_33, k1_zfmisc_1('#skF_6')))), inference(superposition, [status(thm), theory('equality')], [c_2630, c_40])).
% 11.18/4.18  tff(c_3169, plain, (![B_312, D_313]: (r2_relset_1('#skF_4', B_312, D_313, D_313) | ~m1_subset_1(D_313, k1_zfmisc_1('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_2696, c_2696, c_2637])).
% 11.18/4.18  tff(c_3186, plain, (![B_312]: (r2_relset_1('#skF_4', B_312, '#skF_4', '#skF_4'))), inference(resolution, [status(thm)], [c_2712, c_3169])).
% 11.18/4.18  tff(c_2556, plain, (k1_xboole_0='#skF_4' | k1_xboole_0='#skF_5'), inference(splitRight, [status(thm)], [c_2134])).
% 11.18/4.18  tff(c_2596, plain, ('#skF_6'='#skF_4' | '#skF_5'='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_2557, c_2557, c_2556])).
% 11.18/4.18  tff(c_2597, plain, ('#skF_5'='#skF_6'), inference(splitLeft, [status(thm)], [c_2596])).
% 11.18/4.18  tff(c_18, plain, (![B_11]: (r1_tarski(B_11, B_11))), inference(cnfTransformation, [status(thm)], [f_45])).
% 11.18/4.18  tff(c_60, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_5')))), inference(cnfTransformation, [status(thm)], [f_132])).
% 11.18/4.18  tff(c_123, plain, (r1_tarski('#skF_7', k2_zfmisc_1('#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_60, c_111])).
% 11.18/4.18  tff(c_2121, plain, (r1_tarski('#skF_7', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_2118, c_123])).
% 11.18/4.18  tff(c_14, plain, (![B_11, A_10]: (B_11=A_10 | ~r1_tarski(B_11, A_10) | ~r1_tarski(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_45])).
% 11.18/4.18  tff(c_2141, plain, ('#skF_7'='#skF_6' | ~r1_tarski('#skF_6', '#skF_7')), inference(resolution, [status(thm)], [c_2121, c_14])).
% 11.18/4.18  tff(c_2160, plain, (~r1_tarski('#skF_6', '#skF_7')), inference(splitLeft, [status(thm)], [c_2141])).
% 11.18/4.18  tff(c_2164, plain, (~v1_xboole_0('#skF_6')), inference(resolution, [status(thm)], [c_155, c_2160])).
% 11.18/4.18  tff(c_2231, plain, (![B_236, A_237]: (B_236=A_237 | ~r1_tarski(B_236, A_237) | ~v1_xboole_0(A_237))), inference(resolution, [status(thm)], [c_155, c_220])).
% 11.18/4.18  tff(c_2245, plain, (![B_238, A_239]: (B_238=A_239 | ~v1_xboole_0(B_238) | ~v1_xboole_0(A_239))), inference(resolution, [status(thm)], [c_155, c_2231])).
% 11.18/4.18  tff(c_2255, plain, (![A_240]: (k1_xboole_0=A_240 | ~v1_xboole_0(A_240))), inference(resolution, [status(thm)], [c_12, c_2245])).
% 11.18/4.18  tff(c_2266, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_209, c_2255])).
% 11.18/4.18  tff(c_2183, plain, (k1_xboole_0!='#skF_6'), inference(splitLeft, [status(thm)], [c_2134])).
% 11.18/4.18  tff(c_2287, plain, ('#skF_6'!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_2266, c_2183])).
% 11.18/4.18  tff(c_2294, plain, (![B_13]: (k2_zfmisc_1('#skF_4', B_13)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2266, c_2266, c_24])).
% 11.18/4.18  tff(c_2358, plain, ('#skF_6'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_2294, c_2118])).
% 11.18/4.18  tff(c_2360, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2287, c_2358])).
% 11.18/4.18  tff(c_2362, plain, (k1_xboole_0='#skF_6'), inference(splitRight, [status(thm)], [c_2134])).
% 11.18/4.18  tff(c_2371, plain, (v1_xboole_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_2362, c_12])).
% 11.18/4.18  tff(c_2374, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2164, c_2371])).
% 11.18/4.18  tff(c_2375, plain, ('#skF_7'='#skF_6'), inference(splitRight, [status(thm)], [c_2141])).
% 11.18/4.18  tff(c_231, plain, (k2_zfmisc_1('#skF_4', '#skF_5')='#skF_7' | ~r1_tarski(k2_zfmisc_1('#skF_4', '#skF_5'), '#skF_7')), inference(resolution, [status(thm)], [c_123, c_220])).
% 11.18/4.18  tff(c_2377, plain, ('#skF_7'='#skF_6' | ~r1_tarski('#skF_6', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_2118, c_2118, c_231])).
% 11.18/4.18  tff(c_2378, plain, (~r1_tarski('#skF_6', '#skF_7')), inference(splitLeft, [status(thm)], [c_2377])).
% 11.18/4.18  tff(c_2396, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_18, c_2375, c_2378])).
% 11.18/4.18  tff(c_2397, plain, ('#skF_7'='#skF_6'), inference(splitRight, [status(thm)], [c_2377])).
% 11.18/4.18  tff(c_56, plain, (~r2_relset_1('#skF_4', '#skF_5', '#skF_6', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_132])).
% 11.18/4.18  tff(c_2403, plain, (~r2_relset_1('#skF_4', '#skF_5', '#skF_6', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_2397, c_56])).
% 11.18/4.18  tff(c_2598, plain, (~r2_relset_1('#skF_4', '#skF_6', '#skF_6', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_2597, c_2403])).
% 11.18/4.18  tff(c_2701, plain, (~r2_relset_1('#skF_4', '#skF_4', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2696, c_2696, c_2696, c_2598])).
% 11.18/4.18  tff(c_3193, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3186, c_2701])).
% 11.18/4.18  tff(c_3194, plain, ('#skF_6'='#skF_4'), inference(splitRight, [status(thm)], [c_2596])).
% 11.18/4.18  tff(c_3203, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_3194, c_3194, c_2123])).
% 11.18/4.18  tff(c_2582, plain, (![B_13]: (k2_zfmisc_1('#skF_6', B_13)='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_2557, c_2557, c_24])).
% 11.18/4.18  tff(c_3247, plain, (![B_317]: (k2_zfmisc_1('#skF_4', B_317)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_3194, c_3194, c_2582])).
% 11.18/4.18  tff(c_3684, plain, (![B_355, D_356]: (r2_relset_1('#skF_4', B_355, D_356, D_356) | ~m1_subset_1(D_356, k1_zfmisc_1('#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_3247, c_40])).
% 11.18/4.18  tff(c_3701, plain, (![B_355]: (r2_relset_1('#skF_4', B_355, '#skF_4', '#skF_4'))), inference(resolution, [status(thm)], [c_3203, c_3684])).
% 11.18/4.18  tff(c_3201, plain, (~r2_relset_1('#skF_4', '#skF_5', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_3194, c_3194, c_2403])).
% 11.18/4.18  tff(c_3708, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3701, c_3201])).
% 11.18/4.18  tff(c_3710, plain, (~v1_xboole_0('#skF_4')), inference(splitRight, [status(thm)], [c_135])).
% 11.18/4.18  tff(c_12775, plain, (![A_730, B_731, D_732]: (r2_relset_1(A_730, B_731, D_732, D_732) | ~m1_subset_1(D_732, k1_zfmisc_1(k2_zfmisc_1(A_730, B_731))))), inference(cnfTransformation, [status(thm)], [f_93])).
% 11.18/4.18  tff(c_12801, plain, (r2_relset_1('#skF_4', '#skF_5', '#skF_6', '#skF_6')), inference(resolution, [status(thm)], [c_66, c_12775])).
% 11.18/4.18  tff(c_157, plain, (![C_62, A_63, B_64]: (v1_relat_1(C_62) | ~m1_subset_1(C_62, k1_zfmisc_1(k2_zfmisc_1(A_63, B_64))))), inference(cnfTransformation, [status(thm)], [f_81])).
% 11.18/4.18  tff(c_178, plain, (v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_60, c_157])).
% 11.18/4.18  tff(c_64, plain, (v1_funct_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_132])).
% 11.18/4.18  tff(c_62, plain, (v1_funct_2('#skF_7', '#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_132])).
% 11.18/4.18  tff(c_12873, plain, (![A_744, B_745, C_746]: (k1_relset_1(A_744, B_745, C_746)=k1_relat_1(C_746) | ~m1_subset_1(C_746, k1_zfmisc_1(k2_zfmisc_1(A_744, B_745))))), inference(cnfTransformation, [status(thm)], [f_85])).
% 11.18/4.18  tff(c_12906, plain, (k1_relset_1('#skF_4', '#skF_5', '#skF_7')=k1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_60, c_12873])).
% 11.18/4.18  tff(c_12984, plain, (![B_755, A_756, C_757]: (k1_xboole_0=B_755 | k1_relset_1(A_756, B_755, C_757)=A_756 | ~v1_funct_2(C_757, A_756, B_755) | ~m1_subset_1(C_757, k1_zfmisc_1(k2_zfmisc_1(A_756, B_755))))), inference(cnfTransformation, [status(thm)], [f_111])).
% 11.18/4.18  tff(c_13003, plain, (k1_xboole_0='#skF_5' | k1_relset_1('#skF_4', '#skF_5', '#skF_7')='#skF_4' | ~v1_funct_2('#skF_7', '#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_60, c_12984])).
% 11.18/4.18  tff(c_13019, plain, (k1_xboole_0='#skF_5' | k1_relat_1('#skF_7')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_62, c_12906, c_13003])).
% 11.18/4.18  tff(c_13079, plain, (k1_relat_1('#skF_7')='#skF_4'), inference(splitLeft, [status(thm)], [c_13019])).
% 11.18/4.18  tff(c_179, plain, (v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_66, c_157])).
% 11.18/4.18  tff(c_70, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_132])).
% 11.18/4.18  tff(c_68, plain, (v1_funct_2('#skF_6', '#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_132])).
% 11.18/4.18  tff(c_12907, plain, (k1_relset_1('#skF_4', '#skF_5', '#skF_6')=k1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_66, c_12873])).
% 11.18/4.18  tff(c_13006, plain, (k1_xboole_0='#skF_5' | k1_relset_1('#skF_4', '#skF_5', '#skF_6')='#skF_4' | ~v1_funct_2('#skF_6', '#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_66, c_12984])).
% 11.18/4.18  tff(c_13022, plain, (k1_xboole_0='#skF_5' | k1_relat_1('#skF_6')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_68, c_12907, c_13006])).
% 11.18/4.18  tff(c_13085, plain, (k1_relat_1('#skF_6')='#skF_4'), inference(splitLeft, [status(thm)], [c_13022])).
% 11.18/4.18  tff(c_13525, plain, (![A_796, B_797]: (r2_hidden('#skF_3'(A_796, B_797), k1_relat_1(A_796)) | B_797=A_796 | k1_relat_1(B_797)!=k1_relat_1(A_796) | ~v1_funct_1(B_797) | ~v1_relat_1(B_797) | ~v1_funct_1(A_796) | ~v1_relat_1(A_796))), inference(cnfTransformation, [status(thm)], [f_77])).
% 11.18/4.18  tff(c_15639, plain, (![A_894, B_895]: (m1_subset_1('#skF_3'(A_894, B_895), k1_relat_1(A_894)) | B_895=A_894 | k1_relat_1(B_895)!=k1_relat_1(A_894) | ~v1_funct_1(B_895) | ~v1_relat_1(B_895) | ~v1_funct_1(A_894) | ~v1_relat_1(A_894))), inference(resolution, [status(thm)], [c_13525, c_26])).
% 11.18/4.18  tff(c_15642, plain, (![B_895]: (m1_subset_1('#skF_3'('#skF_6', B_895), '#skF_4') | B_895='#skF_6' | k1_relat_1(B_895)!=k1_relat_1('#skF_6') | ~v1_funct_1(B_895) | ~v1_relat_1(B_895) | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_13085, c_15639])).
% 11.18/4.18  tff(c_21489, plain, (![B_1031]: (m1_subset_1('#skF_3'('#skF_6', B_1031), '#skF_4') | B_1031='#skF_6' | k1_relat_1(B_1031)!='#skF_4' | ~v1_funct_1(B_1031) | ~v1_relat_1(B_1031))), inference(demodulation, [status(thm), theory('equality')], [c_179, c_70, c_13085, c_15642])).
% 11.18/4.18  tff(c_58, plain, (![E_41]: (k1_funct_1('#skF_7', E_41)=k1_funct_1('#skF_6', E_41) | ~m1_subset_1(E_41, '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_132])).
% 11.18/4.18  tff(c_21624, plain, (![B_1034]: (k1_funct_1('#skF_7', '#skF_3'('#skF_6', B_1034))=k1_funct_1('#skF_6', '#skF_3'('#skF_6', B_1034)) | B_1034='#skF_6' | k1_relat_1(B_1034)!='#skF_4' | ~v1_funct_1(B_1034) | ~v1_relat_1(B_1034))), inference(resolution, [status(thm)], [c_21489, c_58])).
% 11.18/4.18  tff(c_32, plain, (![B_22, A_18]: (k1_funct_1(B_22, '#skF_3'(A_18, B_22))!=k1_funct_1(A_18, '#skF_3'(A_18, B_22)) | B_22=A_18 | k1_relat_1(B_22)!=k1_relat_1(A_18) | ~v1_funct_1(B_22) | ~v1_relat_1(B_22) | ~v1_funct_1(A_18) | ~v1_relat_1(A_18))), inference(cnfTransformation, [status(thm)], [f_77])).
% 11.18/4.18  tff(c_21631, plain, (k1_relat_1('#skF_7')!=k1_relat_1('#skF_6') | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6') | '#skF_7'='#skF_6' | k1_relat_1('#skF_7')!='#skF_4' | ~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_21624, c_32])).
% 11.18/4.18  tff(c_21638, plain, ('#skF_7'='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_178, c_64, c_13079, c_179, c_70, c_13079, c_13085, c_21631])).
% 11.18/4.18  tff(c_21682, plain, (~r2_relset_1('#skF_4', '#skF_5', '#skF_6', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_21638, c_56])).
% 11.18/4.18  tff(c_21694, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12801, c_21682])).
% 11.18/4.18  tff(c_21695, plain, (k1_xboole_0='#skF_5'), inference(splitRight, [status(thm)], [c_13022])).
% 11.18/4.18  tff(c_21719, plain, (v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_21695, c_12])).
% 11.18/4.18  tff(c_22, plain, (![A_12]: (k2_zfmisc_1(A_12, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_51])).
% 11.18/4.18  tff(c_21718, plain, (![A_12]: (k2_zfmisc_1(A_12, '#skF_5')='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_21695, c_21695, c_22])).
% 11.18/4.18  tff(c_3711, plain, (![B_357, A_358]: (B_357=A_358 | ~r1_tarski(B_357, A_358) | ~r1_tarski(A_358, B_357))), inference(cnfTransformation, [status(thm)], [f_45])).
% 11.18/4.18  tff(c_3769, plain, (![B_365, A_366]: (B_365=A_366 | ~r1_tarski(B_365, A_366) | ~v1_xboole_0(A_366))), inference(resolution, [status(thm)], [c_155, c_3711])).
% 11.18/4.18  tff(c_3783, plain, (k2_zfmisc_1('#skF_4', '#skF_5')='#skF_6' | ~v1_xboole_0(k2_zfmisc_1('#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_124, c_3769])).
% 11.18/4.18  tff(c_12690, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_4', '#skF_5'))), inference(splitLeft, [status(thm)], [c_3783])).
% 11.18/4.18  tff(c_21751, plain, (~v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_21718, c_12690])).
% 11.18/4.18  tff(c_21758, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_21719, c_21751])).
% 11.18/4.18  tff(c_21759, plain, (k1_xboole_0='#skF_5'), inference(splitRight, [status(thm)], [c_13019])).
% 11.18/4.18  tff(c_21783, plain, (v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_21759, c_12])).
% 11.18/4.18  tff(c_21782, plain, (![A_12]: (k2_zfmisc_1(A_12, '#skF_5')='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_21759, c_21759, c_22])).
% 11.18/4.18  tff(c_21812, plain, (~v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_21782, c_12690])).
% 11.18/4.18  tff(c_21819, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_21783, c_21812])).
% 11.18/4.18  tff(c_21820, plain, (k2_zfmisc_1('#skF_4', '#skF_5')='#skF_6'), inference(splitRight, [status(thm)], [c_3783])).
% 11.18/4.18  tff(c_21821, plain, (v1_xboole_0(k2_zfmisc_1('#skF_4', '#skF_5'))), inference(splitRight, [status(thm)], [c_3783])).
% 11.18/4.18  tff(c_21848, plain, (v1_xboole_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_21820, c_21821])).
% 11.18/4.18  tff(c_3787, plain, (![B_367, A_368]: (B_367=A_368 | ~v1_xboole_0(B_367) | ~v1_xboole_0(A_368))), inference(resolution, [status(thm)], [c_155, c_3769])).
% 11.18/4.18  tff(c_3790, plain, (![A_368]: (k1_xboole_0=A_368 | ~v1_xboole_0(A_368))), inference(resolution, [status(thm)], [c_12, c_3787])).
% 11.18/4.18  tff(c_21857, plain, (k1_xboole_0='#skF_6'), inference(resolution, [status(thm)], [c_21848, c_3790])).
% 11.18/4.18  tff(c_21836, plain, (k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4' | k1_xboole_0!='#skF_6'), inference(superposition, [status(thm), theory('equality')], [c_21820, c_20])).
% 11.18/4.18  tff(c_22098, plain, ('#skF_5'='#skF_6' | '#skF_6'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_21857, c_21857, c_21857, c_21836])).
% 11.18/4.18  tff(c_22099, plain, ('#skF_6'='#skF_4'), inference(splitLeft, [status(thm)], [c_22098])).
% 11.18/4.18  tff(c_22111, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_22099, c_21848])).
% 11.18/4.18  tff(c_22117, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3710, c_22111])).
% 11.18/4.18  tff(c_22118, plain, ('#skF_5'='#skF_6'), inference(splitRight, [status(thm)], [c_22098])).
% 11.18/4.18  tff(c_21823, plain, (r1_tarski('#skF_7', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_21820, c_123])).
% 11.18/4.18  tff(c_3720, plain, (![B_59, A_58]: (B_59=A_58 | ~r1_tarski(B_59, A_58) | ~v1_xboole_0(A_58))), inference(resolution, [status(thm)], [c_155, c_3711])).
% 11.18/4.18  tff(c_21846, plain, ('#skF_7'='#skF_6' | ~v1_xboole_0('#skF_6')), inference(resolution, [status(thm)], [c_21823, c_3720])).
% 11.18/4.18  tff(c_22000, plain, ('#skF_7'='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_21848, c_21846])).
% 11.18/4.18  tff(c_22006, plain, (~r2_relset_1('#skF_4', '#skF_5', '#skF_6', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_22000, c_56])).
% 11.18/4.18  tff(c_22120, plain, (~r2_relset_1('#skF_4', '#skF_6', '#skF_6', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_22118, c_22006])).
% 11.18/4.18  tff(c_21825, plain, (m1_subset_1('#skF_6', k1_zfmisc_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_21820, c_66])).
% 11.18/4.18  tff(c_22032, plain, (![A_1048, B_1049, D_1050]: (r2_relset_1(A_1048, B_1049, D_1050, D_1050) | ~m1_subset_1(D_1050, k1_zfmisc_1(k2_zfmisc_1(A_1048, B_1049))))), inference(cnfTransformation, [status(thm)], [f_93])).
% 11.18/4.18  tff(c_22036, plain, (![D_1050]: (r2_relset_1('#skF_4', '#skF_5', D_1050, D_1050) | ~m1_subset_1(D_1050, k1_zfmisc_1('#skF_6')))), inference(superposition, [status(thm), theory('equality')], [c_21820, c_22032])).
% 11.18/4.18  tff(c_22284, plain, (![D_1072]: (r2_relset_1('#skF_4', '#skF_6', D_1072, D_1072) | ~m1_subset_1(D_1072, k1_zfmisc_1('#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_22118, c_22036])).
% 11.18/4.18  tff(c_22289, plain, (r2_relset_1('#skF_4', '#skF_6', '#skF_6', '#skF_6')), inference(resolution, [status(thm)], [c_21825, c_22284])).
% 11.18/4.18  tff(c_22303, plain, $false, inference(negUnitSimplification, [status(thm)], [c_22120, c_22289])).
% 11.18/4.18  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.18/4.18  
% 11.18/4.18  Inference rules
% 11.18/4.18  ----------------------
% 11.18/4.18  #Ref     : 2
% 11.18/4.18  #Sup     : 4972
% 11.18/4.18  #Fact    : 0
% 11.18/4.18  #Define  : 0
% 11.18/4.18  #Split   : 66
% 11.18/4.18  #Chain   : 0
% 11.18/4.18  #Close   : 0
% 11.18/4.18  
% 11.18/4.18  Ordering : KBO
% 11.18/4.18  
% 11.18/4.18  Simplification rules
% 11.18/4.18  ----------------------
% 11.18/4.18  #Subsume      : 1251
% 11.18/4.18  #Demod        : 3986
% 11.18/4.18  #Tautology    : 2082
% 11.18/4.18  #SimpNegUnit  : 311
% 11.18/4.18  #BackRed      : 752
% 11.18/4.18  
% 11.18/4.18  #Partial instantiations: 0
% 11.18/4.18  #Strategies tried      : 1
% 11.18/4.18  
% 11.18/4.18  Timing (in seconds)
% 11.18/4.18  ----------------------
% 11.18/4.18  Preprocessing        : 0.33
% 11.18/4.18  Parsing              : 0.17
% 11.18/4.18  CNF conversion       : 0.02
% 11.18/4.18  Main loop            : 3.07
% 11.18/4.18  Inferencing          : 0.82
% 11.18/4.18  Reduction            : 0.97
% 11.18/4.18  Demodulation         : 0.66
% 11.18/4.18  BG Simplification    : 0.10
% 11.18/4.18  Subsumption          : 0.95
% 11.18/4.18  Abstraction          : 0.12
% 11.18/4.18  MUC search           : 0.00
% 11.18/4.18  Cooper               : 0.00
% 11.18/4.18  Total                : 3.46
% 11.18/4.18  Index Insertion      : 0.00
% 11.18/4.18  Index Deletion       : 0.00
% 11.18/4.18  Index Matching       : 0.00
% 11.18/4.18  BG Taut test         : 0.00
%------------------------------------------------------------------------------
