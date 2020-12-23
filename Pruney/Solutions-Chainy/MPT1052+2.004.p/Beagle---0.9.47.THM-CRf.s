%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:17:09 EST 2020

% Result     : Theorem 8.15s
% Output     : CNFRefutation 8.15s
% Verified   : 
% Statistics : Number of formulae       :  190 (2257 expanded)
%              Number of leaves         :   39 ( 729 expanded)
%              Depth                    :   14
%              Number of atoms          :  289 (4795 expanded)
%              Number of equality atoms :  110 (1046 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k5_partfun1 > k3_partfun1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_2 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k3_partfun1,type,(
    k3_partfun1: ( $i * $i * $i ) > $i )).

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

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_2,type,(
    k1_funct_2: ( $i * $i ) > $i )).

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

tff(k5_partfun1,type,(
    k5_partfun1: ( $i * $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_42,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_113,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & v1_xboole_0(B) )
     => v1_xboole_0(k1_funct_2(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_2)).

tff(f_134,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_relat_1(C)
          & v1_funct_1(C) )
       => ( r2_hidden(C,k1_funct_2(A,B))
         => ( k1_relat_1(C) = A
            & r1_tarski(k2_relat_1(C),B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t169_funct_2)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_121,axiom,(
    ! [A,B,C] :
      ( r2_hidden(C,k1_funct_2(A,B))
     => ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t121_funct_2)).

tff(f_88,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_54,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_106,axiom,(
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

tff(f_32,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_36,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_50,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_44,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_80,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_84,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_66,axiom,(
    ! [A,B] :
      ~ ( A != k1_xboole_0
        & B != k1_xboole_0
        & ~ ( k1_relat_1(k2_zfmisc_1(A,B)) = A
            & k2_relat_1(k2_zfmisc_1(A,B)) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t195_relat_1)).

tff(f_77,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(A,B)
           => ( r1_tarski(k1_relat_1(A),k1_relat_1(B))
              & r1_tarski(k2_relat_1(A),k2_relat_1(B)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_relat_1)).

tff(c_14,plain,(
    ! [B_7] : r1_tarski(B_7,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_3429,plain,(
    ! [A_268,B_269] :
      ( v1_xboole_0(k1_funct_2(A_268,B_269))
      | ~ v1_xboole_0(B_269)
      | v1_xboole_0(A_268) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_68,plain,(
    r2_hidden('#skF_4',k1_funct_2('#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_116,plain,(
    ! [B_39,A_40] :
      ( ~ r2_hidden(B_39,A_40)
      | ~ v1_xboole_0(A_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_120,plain,(
    ~ v1_xboole_0(k1_funct_2('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_68,c_116])).

tff(c_3436,plain,
    ( ~ v1_xboole_0('#skF_3')
    | v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_3429,c_120])).

tff(c_3438,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_3436])).

tff(c_178,plain,(
    ! [A_54,B_55] :
      ( v1_xboole_0(k1_funct_2(A_54,B_55))
      | ~ v1_xboole_0(B_55)
      | v1_xboole_0(A_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_185,plain,
    ( ~ v1_xboole_0('#skF_3')
    | v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_178,c_120])).

tff(c_187,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_185])).

tff(c_66,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_4'),'#skF_3')
    | k1_relat_1('#skF_4') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_126,plain,(
    k1_relat_1('#skF_4') != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_66])).

tff(c_268,plain,(
    ! [C_70,A_71,B_72] :
      ( v1_funct_2(C_70,A_71,B_72)
      | ~ r2_hidden(C_70,k1_funct_2(A_71,B_72)) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_277,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_68,c_268])).

tff(c_58,plain,(
    ! [C_31,A_29,B_30] :
      ( m1_subset_1(C_31,k1_zfmisc_1(k2_zfmisc_1(A_29,B_30)))
      | ~ r2_hidden(C_31,k1_funct_2(A_29,B_30)) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_474,plain,(
    ! [A_94,B_95,C_96] :
      ( k1_relset_1(A_94,B_95,C_96) = k1_relat_1(C_96)
      | ~ m1_subset_1(C_96,k1_zfmisc_1(k2_zfmisc_1(A_94,B_95))) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_1475,plain,(
    ! [A_144,B_145,C_146] :
      ( k1_relset_1(A_144,B_145,C_146) = k1_relat_1(C_146)
      | ~ r2_hidden(C_146,k1_funct_2(A_144,B_145)) ) ),
    inference(resolution,[status(thm)],[c_58,c_474])).

tff(c_1514,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_68,c_1475])).

tff(c_435,plain,(
    ! [C_87,A_88,B_89] :
      ( m1_subset_1(C_87,k1_zfmisc_1(k2_zfmisc_1(A_88,B_89)))
      | ~ r2_hidden(C_87,k1_funct_2(A_88,B_89)) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_24,plain,(
    ! [A_11,B_12] :
      ( r1_tarski(A_11,B_12)
      | ~ m1_subset_1(A_11,k1_zfmisc_1(B_12)) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_858,plain,(
    ! [C_135,A_136,B_137] :
      ( r1_tarski(C_135,k2_zfmisc_1(A_136,B_137))
      | ~ r2_hidden(C_135,k1_funct_2(A_136,B_137)) ) ),
    inference(resolution,[status(thm)],[c_435,c_24])).

tff(c_879,plain,(
    r1_tarski('#skF_4',k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_68,c_858])).

tff(c_26,plain,(
    ! [A_11,B_12] :
      ( m1_subset_1(A_11,k1_zfmisc_1(B_12))
      | ~ r1_tarski(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_1744,plain,(
    ! [B_163,A_164,C_165] :
      ( k1_xboole_0 = B_163
      | k1_relset_1(A_164,B_163,C_165) = A_164
      | ~ v1_funct_2(C_165,A_164,B_163)
      | ~ m1_subset_1(C_165,k1_zfmisc_1(k2_zfmisc_1(A_164,B_163))) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_2547,plain,(
    ! [B_199,A_200,A_201] :
      ( k1_xboole_0 = B_199
      | k1_relset_1(A_200,B_199,A_201) = A_200
      | ~ v1_funct_2(A_201,A_200,B_199)
      | ~ r1_tarski(A_201,k2_zfmisc_1(A_200,B_199)) ) ),
    inference(resolution,[status(thm)],[c_26,c_1744])).

tff(c_2556,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relset_1('#skF_2','#skF_3','#skF_4') = '#skF_2'
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_879,c_2547])).

tff(c_2575,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relat_1('#skF_4') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_277,c_1514,c_2556])).

tff(c_2576,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_126,c_2575])).

tff(c_6,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_2660,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2576,c_6])).

tff(c_2662,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_187,c_2660])).

tff(c_2664,plain,(
    v1_xboole_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_185])).

tff(c_8,plain,(
    ! [A_5] :
      ( k1_xboole_0 = A_5
      | ~ v1_xboole_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_2672,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_2664,c_8])).

tff(c_2663,plain,(
    v1_xboole_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_185])).

tff(c_2668,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_2663,c_8])).

tff(c_2687,plain,(
    '#skF_2' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2672,c_2668])).

tff(c_2695,plain,(
    r2_hidden('#skF_4',k1_funct_2('#skF_3','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2687,c_68])).

tff(c_22,plain,(
    ! [B_10] : k2_zfmisc_1(k1_xboole_0,B_10) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_2677,plain,(
    ! [B_10] : k2_zfmisc_1('#skF_2',B_10) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2668,c_2668,c_22])).

tff(c_2728,plain,(
    ! [B_10] : k2_zfmisc_1('#skF_3',B_10) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2687,c_2687,c_2677])).

tff(c_3182,plain,(
    ! [C_242,A_243,B_244] :
      ( m1_subset_1(C_242,k1_zfmisc_1(k2_zfmisc_1(A_243,B_244)))
      | ~ r2_hidden(C_242,k1_funct_2(A_243,B_244)) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_3242,plain,(
    ! [C_251,B_252] :
      ( m1_subset_1(C_251,k1_zfmisc_1('#skF_3'))
      | ~ r2_hidden(C_251,k1_funct_2('#skF_3',B_252)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2728,c_3182])).

tff(c_3262,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_2695,c_3242])).

tff(c_3272,plain,(
    r1_tarski('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_3262,c_24])).

tff(c_16,plain,(
    ! [A_8] : r1_tarski(k1_xboole_0,A_8) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_155,plain,(
    ! [B_51,A_52] :
      ( B_51 = A_52
      | ~ r1_tarski(B_51,A_52)
      | ~ r1_tarski(A_52,B_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_164,plain,(
    ! [A_8] :
      ( k1_xboole_0 = A_8
      | ~ r1_tarski(A_8,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_16,c_155])).

tff(c_2673,plain,(
    ! [A_8] :
      ( A_8 = '#skF_2'
      | ~ r1_tarski(A_8,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2668,c_2668,c_164])).

tff(c_2776,plain,(
    ! [A_8] :
      ( A_8 = '#skF_3'
      | ~ r1_tarski(A_8,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2687,c_2687,c_2673])).

tff(c_3283,plain,(
    '#skF_3' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_3272,c_2776])).

tff(c_2693,plain,(
    k1_relat_1('#skF_4') != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2687,c_126])).

tff(c_3317,plain,(
    k1_relat_1('#skF_4') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3283,c_2693])).

tff(c_38,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_2680,plain,(
    k1_relat_1('#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2668,c_2668,c_38])).

tff(c_2711,plain,(
    k1_relat_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2687,c_2687,c_2680])).

tff(c_3318,plain,(
    k1_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3283,c_3283,c_2711])).

tff(c_3371,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3317,c_3318])).

tff(c_3372,plain,(
    ~ r1_tarski(k2_relat_1('#skF_4'),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_66])).

tff(c_72,plain,(
    v1_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_3686,plain,(
    ! [C_301,A_302,B_303] :
      ( m1_subset_1(C_301,k1_zfmisc_1(k2_zfmisc_1(A_302,B_303)))
      | ~ r2_hidden(C_301,k1_funct_2(A_302,B_303)) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_4118,plain,(
    ! [C_344,A_345,B_346] :
      ( r1_tarski(C_344,k2_zfmisc_1(A_345,B_346))
      | ~ r2_hidden(C_344,k1_funct_2(A_345,B_346)) ) ),
    inference(resolution,[status(thm)],[c_3686,c_24])).

tff(c_4139,plain,(
    r1_tarski('#skF_4',k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_68,c_4118])).

tff(c_3439,plain,(
    ! [C_270,A_271,B_272] :
      ( v1_relat_1(C_270)
      | ~ m1_subset_1(C_270,k1_zfmisc_1(k2_zfmisc_1(A_271,B_272))) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_3489,plain,(
    ! [A_277,A_278,B_279] :
      ( v1_relat_1(A_277)
      | ~ r1_tarski(A_277,k2_zfmisc_1(A_278,B_279)) ) ),
    inference(resolution,[status(thm)],[c_26,c_3439])).

tff(c_3502,plain,(
    ! [A_278,B_279] : v1_relat_1(k2_zfmisc_1(A_278,B_279)) ),
    inference(resolution,[status(thm)],[c_14,c_3489])).

tff(c_28,plain,(
    ! [A_13,B_14] :
      ( k2_relat_1(k2_zfmisc_1(A_13,B_14)) = B_14
      | k1_xboole_0 = B_14
      | k1_xboole_0 = A_13 ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_3833,plain,(
    ! [A_322,B_323] :
      ( r1_tarski(k2_relat_1(A_322),k2_relat_1(B_323))
      | ~ r1_tarski(A_322,B_323)
      | ~ v1_relat_1(B_323)
      | ~ v1_relat_1(A_322) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_3841,plain,(
    ! [A_322,B_14,A_13] :
      ( r1_tarski(k2_relat_1(A_322),B_14)
      | ~ r1_tarski(A_322,k2_zfmisc_1(A_13,B_14))
      | ~ v1_relat_1(k2_zfmisc_1(A_13,B_14))
      | ~ v1_relat_1(A_322)
      | k1_xboole_0 = B_14
      | k1_xboole_0 = A_13 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_3833])).

tff(c_10680,plain,(
    ! [A_526,B_527,A_528] :
      ( r1_tarski(k2_relat_1(A_526),B_527)
      | ~ r1_tarski(A_526,k2_zfmisc_1(A_528,B_527))
      | ~ v1_relat_1(A_526)
      | k1_xboole_0 = B_527
      | k1_xboole_0 = A_528 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3502,c_3841])).

tff(c_10694,plain,
    ( r1_tarski(k2_relat_1('#skF_4'),'#skF_3')
    | ~ v1_relat_1('#skF_4')
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_4139,c_10680])).

tff(c_10715,plain,
    ( r1_tarski(k2_relat_1('#skF_4'),'#skF_3')
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_10694])).

tff(c_10716,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_3372,c_10715])).

tff(c_10724,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_10716])).

tff(c_10847,plain,(
    ! [A_8] : r1_tarski('#skF_2',A_8) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10724,c_16])).

tff(c_10846,plain,(
    ! [B_10] : k2_zfmisc_1('#skF_2',B_10) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10724,c_10724,c_22])).

tff(c_10,plain,(
    ! [B_7,A_6] :
      ( B_7 = A_6
      | ~ r1_tarski(B_7,A_6)
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_4147,plain,
    ( k2_zfmisc_1('#skF_2','#skF_3') = '#skF_4'
    | ~ r1_tarski(k2_zfmisc_1('#skF_2','#skF_3'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_4139,c_10])).

tff(c_4148,plain,(
    ~ r1_tarski(k2_zfmisc_1('#skF_2','#skF_3'),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_4147])).

tff(c_11159,plain,(
    ~ r1_tarski('#skF_2','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10846,c_4148])).

tff(c_11163,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_10847,c_11159])).

tff(c_11164,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_10716])).

tff(c_11291,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_11164,c_6])).

tff(c_11293,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3438,c_11291])).

tff(c_11294,plain,(
    k2_zfmisc_1('#skF_2','#skF_3') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_4147])).

tff(c_11307,plain,
    ( k2_relat_1('#skF_4') = '#skF_3'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_11294,c_28])).

tff(c_11357,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_11307])).

tff(c_18,plain,(
    ! [B_10,A_9] :
      ( k1_xboole_0 = B_10
      | k1_xboole_0 = A_9
      | k2_zfmisc_1(A_9,B_10) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_11319,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 != '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_11294,c_18])).

tff(c_11356,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_11319])).

tff(c_11358,plain,(
    '#skF_2' != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_11357,c_11356])).

tff(c_11561,plain,(
    ! [B_548] : k2_zfmisc_1('#skF_2',B_548) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_11357,c_11357,c_22])).

tff(c_11574,plain,(
    '#skF_2' = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_11561,c_11294])).

tff(c_11597,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_11358,c_11574])).

tff(c_11598,plain,
    ( k1_xboole_0 = '#skF_3'
    | k2_relat_1('#skF_4') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_11307])).

tff(c_11600,plain,(
    k2_relat_1('#skF_4') = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_11598])).

tff(c_11613,plain,(
    ~ r1_tarski('#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_11600,c_3372])).

tff(c_11616,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_11613])).

tff(c_11617,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_11598])).

tff(c_11669,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_11617,c_6])).

tff(c_11671,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3438,c_11669])).

tff(c_11673,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_11319])).

tff(c_20,plain,(
    ! [A_9] : k2_zfmisc_1(A_9,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_3449,plain,(
    ! [C_273] :
      ( v1_relat_1(C_273)
      | ~ m1_subset_1(C_273,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_3439])).

tff(c_3455,plain,(
    ! [A_274] :
      ( v1_relat_1(A_274)
      | ~ r1_tarski(A_274,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_26,c_3449])).

tff(c_3464,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_14,c_3455])).

tff(c_3373,plain,(
    k1_relat_1('#skF_4') = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_66])).

tff(c_3951,plain,(
    ! [A_333,B_334] :
      ( r1_tarski(k1_relat_1(A_333),k1_relat_1(B_334))
      | ~ r1_tarski(A_333,B_334)
      | ~ v1_relat_1(B_334)
      | ~ v1_relat_1(A_333) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_3962,plain,(
    ! [B_334] :
      ( r1_tarski('#skF_2',k1_relat_1(B_334))
      | ~ r1_tarski('#skF_4',B_334)
      | ~ v1_relat_1(B_334)
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3373,c_3951])).

tff(c_3985,plain,(
    ! [B_335] :
      ( r1_tarski('#skF_2',k1_relat_1(B_335))
      | ~ r1_tarski('#skF_4',B_335)
      | ~ v1_relat_1(B_335) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_3962])).

tff(c_3996,plain,
    ( r1_tarski('#skF_2',k1_xboole_0)
    | ~ r1_tarski('#skF_4',k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_3985])).

tff(c_4003,plain,
    ( r1_tarski('#skF_2',k1_xboole_0)
    | ~ r1_tarski('#skF_4',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3464,c_3996])).

tff(c_4004,plain,(
    ~ r1_tarski('#skF_4',k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_4003])).

tff(c_11680,plain,(
    ~ r1_tarski('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_11673,c_4004])).

tff(c_11725,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_11680])).

tff(c_11726,plain,(
    r1_tarski('#skF_2',k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_4003])).

tff(c_3406,plain,(
    ! [B_265,A_266] :
      ( B_265 = A_266
      | ~ r1_tarski(B_265,A_266)
      | ~ r1_tarski(A_266,B_265) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_3415,plain,(
    ! [A_8] :
      ( k1_xboole_0 = A_8
      | ~ r1_tarski(A_8,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_16,c_3406])).

tff(c_11744,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_11726,c_3415])).

tff(c_11727,plain,(
    r1_tarski('#skF_4',k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_4003])).

tff(c_11835,plain,(
    r1_tarski('#skF_4','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_11744,c_11727])).

tff(c_12067,plain,(
    ! [A_562] :
      ( A_562 = '#skF_2'
      | ~ r1_tarski(A_562,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_11744,c_11744,c_3415])).

tff(c_12081,plain,(
    '#skF_2' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_11835,c_12067])).

tff(c_11799,plain,(
    ! [A_8] : r1_tarski('#skF_2',A_8) ),
    inference(demodulation,[status(thm),theory(equality)],[c_11744,c_16])).

tff(c_12096,plain,(
    ! [A_8] : r1_tarski('#skF_4',A_8) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12081,c_11799])).

tff(c_36,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_11800,plain,(
    k2_relat_1('#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_11744,c_11744,c_36])).

tff(c_12097,plain,(
    k2_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12081,c_12081,c_11800])).

tff(c_12172,plain,(
    ~ r1_tarski('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12097,c_3372])).

tff(c_12175,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12096,c_12172])).

tff(c_12177,plain,(
    v1_xboole_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_3436])).

tff(c_12185,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_12177,c_8])).

tff(c_12176,plain,(
    v1_xboole_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_3436])).

tff(c_12181,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_12176,c_8])).

tff(c_12200,plain,(
    '#skF_2' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12185,c_12181])).

tff(c_12214,plain,(
    r2_hidden('#skF_4',k1_funct_2('#skF_3','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12200,c_68])).

tff(c_12189,plain,(
    ! [A_9] : k2_zfmisc_1(A_9,'#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12181,c_12181,c_20])).

tff(c_12265,plain,(
    ! [A_9] : k2_zfmisc_1(A_9,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12200,c_12200,c_12189])).

tff(c_12544,plain,(
    ! [C_602,A_603,B_604] :
      ( m1_subset_1(C_602,k1_zfmisc_1(k2_zfmisc_1(A_603,B_604)))
      | ~ r2_hidden(C_602,k1_funct_2(A_603,B_604)) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_12689,plain,(
    ! [C_613,A_614] :
      ( m1_subset_1(C_613,k1_zfmisc_1('#skF_3'))
      | ~ r2_hidden(C_613,k1_funct_2(A_614,'#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12265,c_12544])).

tff(c_12705,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_12214,c_12689])).

tff(c_12715,plain,(
    r1_tarski('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_12705,c_24])).

tff(c_12186,plain,(
    ! [A_8] :
      ( A_8 = '#skF_2'
      | ~ r1_tarski(A_8,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12181,c_12181,c_3415])).

tff(c_12326,plain,(
    ! [A_8] :
      ( A_8 = '#skF_3'
      | ~ r1_tarski(A_8,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12200,c_12200,c_12186])).

tff(c_12726,plain,(
    '#skF_3' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_12715,c_12326])).

tff(c_12192,plain,(
    k2_relat_1('#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12181,c_12181,c_36])).

tff(c_12225,plain,(
    k2_relat_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12200,c_12200,c_12192])).

tff(c_12759,plain,(
    k2_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12726,c_12726,c_12225])).

tff(c_12764,plain,(
    ~ r1_tarski(k2_relat_1('#skF_4'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12726,c_3372])).

tff(c_12804,plain,(
    ~ r1_tarski('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12759,c_12764])).

tff(c_12807,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_12804])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n017.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 16:12:16 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.15/2.83  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.15/2.85  
% 8.15/2.85  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.15/2.86  %$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k5_partfun1 > k3_partfun1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_2 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4
% 8.15/2.86  
% 8.15/2.86  %Foreground sorts:
% 8.15/2.86  
% 8.15/2.86  
% 8.15/2.86  %Background operators:
% 8.15/2.86  
% 8.15/2.86  
% 8.15/2.86  %Foreground operators:
% 8.15/2.86  tff(k3_partfun1, type, k3_partfun1: ($i * $i * $i) > $i).
% 8.15/2.86  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 8.15/2.86  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.15/2.86  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 8.15/2.86  tff('#skF_1', type, '#skF_1': $i > $i).
% 8.15/2.86  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 8.15/2.86  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 8.15/2.86  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 8.15/2.86  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 8.15/2.86  tff('#skF_2', type, '#skF_2': $i).
% 8.15/2.86  tff('#skF_3', type, '#skF_3': $i).
% 8.15/2.86  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 8.15/2.86  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 8.15/2.86  tff(k1_funct_2, type, k1_funct_2: ($i * $i) > $i).
% 8.15/2.86  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.15/2.86  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 8.15/2.86  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 8.15/2.86  tff('#skF_4', type, '#skF_4': $i).
% 8.15/2.86  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.15/2.86  tff(k5_partfun1, type, k5_partfun1: ($i * $i * $i) > $i).
% 8.15/2.86  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 8.15/2.86  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 8.15/2.86  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 8.15/2.86  
% 8.15/2.88  tff(f_42, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 8.15/2.88  tff(f_113, axiom, (![A, B]: ((~v1_xboole_0(A) & v1_xboole_0(B)) => v1_xboole_0(k1_funct_2(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc3_funct_2)).
% 8.15/2.88  tff(f_134, negated_conjecture, ~(![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(C, k1_funct_2(A, B)) => ((k1_relat_1(C) = A) & r1_tarski(k2_relat_1(C), B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t169_funct_2)).
% 8.15/2.88  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 8.15/2.88  tff(f_121, axiom, (![A, B, C]: (r2_hidden(C, k1_funct_2(A, B)) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t121_funct_2)).
% 8.15/2.88  tff(f_88, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 8.15/2.88  tff(f_54, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 8.15/2.88  tff(f_106, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 8.15/2.88  tff(f_32, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 8.15/2.88  tff(f_36, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 8.15/2.88  tff(f_50, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 8.15/2.88  tff(f_44, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 8.15/2.88  tff(f_80, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 8.15/2.88  tff(f_84, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 8.15/2.88  tff(f_66, axiom, (![A, B]: ~((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~((k1_relat_1(k2_zfmisc_1(A, B)) = A) & (k2_relat_1(k2_zfmisc_1(A, B)) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t195_relat_1)).
% 8.15/2.88  tff(f_77, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(A, B) => (r1_tarski(k1_relat_1(A), k1_relat_1(B)) & r1_tarski(k2_relat_1(A), k2_relat_1(B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t25_relat_1)).
% 8.15/2.88  tff(c_14, plain, (![B_7]: (r1_tarski(B_7, B_7))), inference(cnfTransformation, [status(thm)], [f_42])).
% 8.15/2.88  tff(c_3429, plain, (![A_268, B_269]: (v1_xboole_0(k1_funct_2(A_268, B_269)) | ~v1_xboole_0(B_269) | v1_xboole_0(A_268))), inference(cnfTransformation, [status(thm)], [f_113])).
% 8.15/2.88  tff(c_68, plain, (r2_hidden('#skF_4', k1_funct_2('#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_134])).
% 8.15/2.88  tff(c_116, plain, (![B_39, A_40]: (~r2_hidden(B_39, A_40) | ~v1_xboole_0(A_40))), inference(cnfTransformation, [status(thm)], [f_31])).
% 8.15/2.88  tff(c_120, plain, (~v1_xboole_0(k1_funct_2('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_68, c_116])).
% 8.15/2.88  tff(c_3436, plain, (~v1_xboole_0('#skF_3') | v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_3429, c_120])).
% 8.15/2.88  tff(c_3438, plain, (~v1_xboole_0('#skF_3')), inference(splitLeft, [status(thm)], [c_3436])).
% 8.15/2.88  tff(c_178, plain, (![A_54, B_55]: (v1_xboole_0(k1_funct_2(A_54, B_55)) | ~v1_xboole_0(B_55) | v1_xboole_0(A_54))), inference(cnfTransformation, [status(thm)], [f_113])).
% 8.15/2.88  tff(c_185, plain, (~v1_xboole_0('#skF_3') | v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_178, c_120])).
% 8.15/2.88  tff(c_187, plain, (~v1_xboole_0('#skF_3')), inference(splitLeft, [status(thm)], [c_185])).
% 8.15/2.88  tff(c_66, plain, (~r1_tarski(k2_relat_1('#skF_4'), '#skF_3') | k1_relat_1('#skF_4')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_134])).
% 8.15/2.88  tff(c_126, plain, (k1_relat_1('#skF_4')!='#skF_2'), inference(splitLeft, [status(thm)], [c_66])).
% 8.15/2.88  tff(c_268, plain, (![C_70, A_71, B_72]: (v1_funct_2(C_70, A_71, B_72) | ~r2_hidden(C_70, k1_funct_2(A_71, B_72)))), inference(cnfTransformation, [status(thm)], [f_121])).
% 8.15/2.88  tff(c_277, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_68, c_268])).
% 8.15/2.88  tff(c_58, plain, (![C_31, A_29, B_30]: (m1_subset_1(C_31, k1_zfmisc_1(k2_zfmisc_1(A_29, B_30))) | ~r2_hidden(C_31, k1_funct_2(A_29, B_30)))), inference(cnfTransformation, [status(thm)], [f_121])).
% 8.15/2.88  tff(c_474, plain, (![A_94, B_95, C_96]: (k1_relset_1(A_94, B_95, C_96)=k1_relat_1(C_96) | ~m1_subset_1(C_96, k1_zfmisc_1(k2_zfmisc_1(A_94, B_95))))), inference(cnfTransformation, [status(thm)], [f_88])).
% 8.15/2.88  tff(c_1475, plain, (![A_144, B_145, C_146]: (k1_relset_1(A_144, B_145, C_146)=k1_relat_1(C_146) | ~r2_hidden(C_146, k1_funct_2(A_144, B_145)))), inference(resolution, [status(thm)], [c_58, c_474])).
% 8.15/2.88  tff(c_1514, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_68, c_1475])).
% 8.15/2.88  tff(c_435, plain, (![C_87, A_88, B_89]: (m1_subset_1(C_87, k1_zfmisc_1(k2_zfmisc_1(A_88, B_89))) | ~r2_hidden(C_87, k1_funct_2(A_88, B_89)))), inference(cnfTransformation, [status(thm)], [f_121])).
% 8.15/2.88  tff(c_24, plain, (![A_11, B_12]: (r1_tarski(A_11, B_12) | ~m1_subset_1(A_11, k1_zfmisc_1(B_12)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 8.15/2.88  tff(c_858, plain, (![C_135, A_136, B_137]: (r1_tarski(C_135, k2_zfmisc_1(A_136, B_137)) | ~r2_hidden(C_135, k1_funct_2(A_136, B_137)))), inference(resolution, [status(thm)], [c_435, c_24])).
% 8.15/2.88  tff(c_879, plain, (r1_tarski('#skF_4', k2_zfmisc_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_68, c_858])).
% 8.15/2.88  tff(c_26, plain, (![A_11, B_12]: (m1_subset_1(A_11, k1_zfmisc_1(B_12)) | ~r1_tarski(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_54])).
% 8.15/2.88  tff(c_1744, plain, (![B_163, A_164, C_165]: (k1_xboole_0=B_163 | k1_relset_1(A_164, B_163, C_165)=A_164 | ~v1_funct_2(C_165, A_164, B_163) | ~m1_subset_1(C_165, k1_zfmisc_1(k2_zfmisc_1(A_164, B_163))))), inference(cnfTransformation, [status(thm)], [f_106])).
% 8.15/2.88  tff(c_2547, plain, (![B_199, A_200, A_201]: (k1_xboole_0=B_199 | k1_relset_1(A_200, B_199, A_201)=A_200 | ~v1_funct_2(A_201, A_200, B_199) | ~r1_tarski(A_201, k2_zfmisc_1(A_200, B_199)))), inference(resolution, [status(thm)], [c_26, c_1744])).
% 8.15/2.88  tff(c_2556, plain, (k1_xboole_0='#skF_3' | k1_relset_1('#skF_2', '#skF_3', '#skF_4')='#skF_2' | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_879, c_2547])).
% 8.15/2.88  tff(c_2575, plain, (k1_xboole_0='#skF_3' | k1_relat_1('#skF_4')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_277, c_1514, c_2556])).
% 8.15/2.88  tff(c_2576, plain, (k1_xboole_0='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_126, c_2575])).
% 8.15/2.88  tff(c_6, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_32])).
% 8.15/2.88  tff(c_2660, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2576, c_6])).
% 8.15/2.88  tff(c_2662, plain, $false, inference(negUnitSimplification, [status(thm)], [c_187, c_2660])).
% 8.15/2.88  tff(c_2664, plain, (v1_xboole_0('#skF_3')), inference(splitRight, [status(thm)], [c_185])).
% 8.15/2.88  tff(c_8, plain, (![A_5]: (k1_xboole_0=A_5 | ~v1_xboole_0(A_5))), inference(cnfTransformation, [status(thm)], [f_36])).
% 8.15/2.88  tff(c_2672, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_2664, c_8])).
% 8.15/2.88  tff(c_2663, plain, (v1_xboole_0('#skF_2')), inference(splitRight, [status(thm)], [c_185])).
% 8.15/2.88  tff(c_2668, plain, (k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_2663, c_8])).
% 8.15/2.88  tff(c_2687, plain, ('#skF_2'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_2672, c_2668])).
% 8.15/2.88  tff(c_2695, plain, (r2_hidden('#skF_4', k1_funct_2('#skF_3', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_2687, c_68])).
% 8.15/2.88  tff(c_22, plain, (![B_10]: (k2_zfmisc_1(k1_xboole_0, B_10)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_50])).
% 8.15/2.88  tff(c_2677, plain, (![B_10]: (k2_zfmisc_1('#skF_2', B_10)='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2668, c_2668, c_22])).
% 8.15/2.88  tff(c_2728, plain, (![B_10]: (k2_zfmisc_1('#skF_3', B_10)='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2687, c_2687, c_2677])).
% 8.15/2.88  tff(c_3182, plain, (![C_242, A_243, B_244]: (m1_subset_1(C_242, k1_zfmisc_1(k2_zfmisc_1(A_243, B_244))) | ~r2_hidden(C_242, k1_funct_2(A_243, B_244)))), inference(cnfTransformation, [status(thm)], [f_121])).
% 8.15/2.88  tff(c_3242, plain, (![C_251, B_252]: (m1_subset_1(C_251, k1_zfmisc_1('#skF_3')) | ~r2_hidden(C_251, k1_funct_2('#skF_3', B_252)))), inference(superposition, [status(thm), theory('equality')], [c_2728, c_3182])).
% 8.15/2.88  tff(c_3262, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_3'))), inference(resolution, [status(thm)], [c_2695, c_3242])).
% 8.15/2.88  tff(c_3272, plain, (r1_tarski('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_3262, c_24])).
% 8.15/2.88  tff(c_16, plain, (![A_8]: (r1_tarski(k1_xboole_0, A_8))), inference(cnfTransformation, [status(thm)], [f_44])).
% 8.15/2.88  tff(c_155, plain, (![B_51, A_52]: (B_51=A_52 | ~r1_tarski(B_51, A_52) | ~r1_tarski(A_52, B_51))), inference(cnfTransformation, [status(thm)], [f_42])).
% 8.15/2.88  tff(c_164, plain, (![A_8]: (k1_xboole_0=A_8 | ~r1_tarski(A_8, k1_xboole_0))), inference(resolution, [status(thm)], [c_16, c_155])).
% 8.15/2.88  tff(c_2673, plain, (![A_8]: (A_8='#skF_2' | ~r1_tarski(A_8, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_2668, c_2668, c_164])).
% 8.15/2.88  tff(c_2776, plain, (![A_8]: (A_8='#skF_3' | ~r1_tarski(A_8, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_2687, c_2687, c_2673])).
% 8.15/2.88  tff(c_3283, plain, ('#skF_3'='#skF_4'), inference(resolution, [status(thm)], [c_3272, c_2776])).
% 8.15/2.88  tff(c_2693, plain, (k1_relat_1('#skF_4')!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_2687, c_126])).
% 8.15/2.88  tff(c_3317, plain, (k1_relat_1('#skF_4')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_3283, c_2693])).
% 8.15/2.88  tff(c_38, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_80])).
% 8.15/2.88  tff(c_2680, plain, (k1_relat_1('#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_2668, c_2668, c_38])).
% 8.15/2.88  tff(c_2711, plain, (k1_relat_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_2687, c_2687, c_2680])).
% 8.15/2.88  tff(c_3318, plain, (k1_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_3283, c_3283, c_2711])).
% 8.15/2.88  tff(c_3371, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3317, c_3318])).
% 8.15/2.88  tff(c_3372, plain, (~r1_tarski(k2_relat_1('#skF_4'), '#skF_3')), inference(splitRight, [status(thm)], [c_66])).
% 8.15/2.88  tff(c_72, plain, (v1_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_134])).
% 8.15/2.88  tff(c_3686, plain, (![C_301, A_302, B_303]: (m1_subset_1(C_301, k1_zfmisc_1(k2_zfmisc_1(A_302, B_303))) | ~r2_hidden(C_301, k1_funct_2(A_302, B_303)))), inference(cnfTransformation, [status(thm)], [f_121])).
% 8.15/2.88  tff(c_4118, plain, (![C_344, A_345, B_346]: (r1_tarski(C_344, k2_zfmisc_1(A_345, B_346)) | ~r2_hidden(C_344, k1_funct_2(A_345, B_346)))), inference(resolution, [status(thm)], [c_3686, c_24])).
% 8.15/2.88  tff(c_4139, plain, (r1_tarski('#skF_4', k2_zfmisc_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_68, c_4118])).
% 8.15/2.88  tff(c_3439, plain, (![C_270, A_271, B_272]: (v1_relat_1(C_270) | ~m1_subset_1(C_270, k1_zfmisc_1(k2_zfmisc_1(A_271, B_272))))), inference(cnfTransformation, [status(thm)], [f_84])).
% 8.15/2.88  tff(c_3489, plain, (![A_277, A_278, B_279]: (v1_relat_1(A_277) | ~r1_tarski(A_277, k2_zfmisc_1(A_278, B_279)))), inference(resolution, [status(thm)], [c_26, c_3439])).
% 8.15/2.88  tff(c_3502, plain, (![A_278, B_279]: (v1_relat_1(k2_zfmisc_1(A_278, B_279)))), inference(resolution, [status(thm)], [c_14, c_3489])).
% 8.15/2.88  tff(c_28, plain, (![A_13, B_14]: (k2_relat_1(k2_zfmisc_1(A_13, B_14))=B_14 | k1_xboole_0=B_14 | k1_xboole_0=A_13)), inference(cnfTransformation, [status(thm)], [f_66])).
% 8.15/2.88  tff(c_3833, plain, (![A_322, B_323]: (r1_tarski(k2_relat_1(A_322), k2_relat_1(B_323)) | ~r1_tarski(A_322, B_323) | ~v1_relat_1(B_323) | ~v1_relat_1(A_322))), inference(cnfTransformation, [status(thm)], [f_77])).
% 8.15/2.88  tff(c_3841, plain, (![A_322, B_14, A_13]: (r1_tarski(k2_relat_1(A_322), B_14) | ~r1_tarski(A_322, k2_zfmisc_1(A_13, B_14)) | ~v1_relat_1(k2_zfmisc_1(A_13, B_14)) | ~v1_relat_1(A_322) | k1_xboole_0=B_14 | k1_xboole_0=A_13)), inference(superposition, [status(thm), theory('equality')], [c_28, c_3833])).
% 8.15/2.88  tff(c_10680, plain, (![A_526, B_527, A_528]: (r1_tarski(k2_relat_1(A_526), B_527) | ~r1_tarski(A_526, k2_zfmisc_1(A_528, B_527)) | ~v1_relat_1(A_526) | k1_xboole_0=B_527 | k1_xboole_0=A_528)), inference(demodulation, [status(thm), theory('equality')], [c_3502, c_3841])).
% 8.15/2.88  tff(c_10694, plain, (r1_tarski(k2_relat_1('#skF_4'), '#skF_3') | ~v1_relat_1('#skF_4') | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_4139, c_10680])).
% 8.15/2.88  tff(c_10715, plain, (r1_tarski(k2_relat_1('#skF_4'), '#skF_3') | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_72, c_10694])).
% 8.15/2.88  tff(c_10716, plain, (k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_3372, c_10715])).
% 8.15/2.88  tff(c_10724, plain, (k1_xboole_0='#skF_2'), inference(splitLeft, [status(thm)], [c_10716])).
% 8.15/2.88  tff(c_10847, plain, (![A_8]: (r1_tarski('#skF_2', A_8))), inference(demodulation, [status(thm), theory('equality')], [c_10724, c_16])).
% 8.15/2.88  tff(c_10846, plain, (![B_10]: (k2_zfmisc_1('#skF_2', B_10)='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_10724, c_10724, c_22])).
% 8.15/2.88  tff(c_10, plain, (![B_7, A_6]: (B_7=A_6 | ~r1_tarski(B_7, A_6) | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_42])).
% 8.15/2.88  tff(c_4147, plain, (k2_zfmisc_1('#skF_2', '#skF_3')='#skF_4' | ~r1_tarski(k2_zfmisc_1('#skF_2', '#skF_3'), '#skF_4')), inference(resolution, [status(thm)], [c_4139, c_10])).
% 8.15/2.88  tff(c_4148, plain, (~r1_tarski(k2_zfmisc_1('#skF_2', '#skF_3'), '#skF_4')), inference(splitLeft, [status(thm)], [c_4147])).
% 8.15/2.88  tff(c_11159, plain, (~r1_tarski('#skF_2', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_10846, c_4148])).
% 8.15/2.88  tff(c_11163, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_10847, c_11159])).
% 8.15/2.88  tff(c_11164, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_10716])).
% 8.15/2.88  tff(c_11291, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_11164, c_6])).
% 8.15/2.88  tff(c_11293, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3438, c_11291])).
% 8.15/2.88  tff(c_11294, plain, (k2_zfmisc_1('#skF_2', '#skF_3')='#skF_4'), inference(splitRight, [status(thm)], [c_4147])).
% 8.15/2.88  tff(c_11307, plain, (k2_relat_1('#skF_4')='#skF_3' | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_11294, c_28])).
% 8.15/2.88  tff(c_11357, plain, (k1_xboole_0='#skF_2'), inference(splitLeft, [status(thm)], [c_11307])).
% 8.15/2.88  tff(c_18, plain, (![B_10, A_9]: (k1_xboole_0=B_10 | k1_xboole_0=A_9 | k2_zfmisc_1(A_9, B_10)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_50])).
% 8.15/2.88  tff(c_11319, plain, (k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2' | k1_xboole_0!='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_11294, c_18])).
% 8.15/2.88  tff(c_11356, plain, (k1_xboole_0!='#skF_4'), inference(splitLeft, [status(thm)], [c_11319])).
% 8.15/2.88  tff(c_11358, plain, ('#skF_2'!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_11357, c_11356])).
% 8.15/2.88  tff(c_11561, plain, (![B_548]: (k2_zfmisc_1('#skF_2', B_548)='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_11357, c_11357, c_22])).
% 8.15/2.88  tff(c_11574, plain, ('#skF_2'='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_11561, c_11294])).
% 8.15/2.88  tff(c_11597, plain, $false, inference(negUnitSimplification, [status(thm)], [c_11358, c_11574])).
% 8.15/2.88  tff(c_11598, plain, (k1_xboole_0='#skF_3' | k2_relat_1('#skF_4')='#skF_3'), inference(splitRight, [status(thm)], [c_11307])).
% 8.15/2.88  tff(c_11600, plain, (k2_relat_1('#skF_4')='#skF_3'), inference(splitLeft, [status(thm)], [c_11598])).
% 8.15/2.88  tff(c_11613, plain, (~r1_tarski('#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_11600, c_3372])).
% 8.15/2.88  tff(c_11616, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_14, c_11613])).
% 8.15/2.88  tff(c_11617, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_11598])).
% 8.15/2.88  tff(c_11669, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_11617, c_6])).
% 8.15/2.88  tff(c_11671, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3438, c_11669])).
% 8.15/2.88  tff(c_11673, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_11319])).
% 8.15/2.88  tff(c_20, plain, (![A_9]: (k2_zfmisc_1(A_9, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_50])).
% 8.15/2.88  tff(c_3449, plain, (![C_273]: (v1_relat_1(C_273) | ~m1_subset_1(C_273, k1_zfmisc_1(k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_20, c_3439])).
% 8.15/2.88  tff(c_3455, plain, (![A_274]: (v1_relat_1(A_274) | ~r1_tarski(A_274, k1_xboole_0))), inference(resolution, [status(thm)], [c_26, c_3449])).
% 8.15/2.88  tff(c_3464, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_14, c_3455])).
% 8.15/2.88  tff(c_3373, plain, (k1_relat_1('#skF_4')='#skF_2'), inference(splitRight, [status(thm)], [c_66])).
% 8.15/2.88  tff(c_3951, plain, (![A_333, B_334]: (r1_tarski(k1_relat_1(A_333), k1_relat_1(B_334)) | ~r1_tarski(A_333, B_334) | ~v1_relat_1(B_334) | ~v1_relat_1(A_333))), inference(cnfTransformation, [status(thm)], [f_77])).
% 8.15/2.88  tff(c_3962, plain, (![B_334]: (r1_tarski('#skF_2', k1_relat_1(B_334)) | ~r1_tarski('#skF_4', B_334) | ~v1_relat_1(B_334) | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_3373, c_3951])).
% 8.15/2.88  tff(c_3985, plain, (![B_335]: (r1_tarski('#skF_2', k1_relat_1(B_335)) | ~r1_tarski('#skF_4', B_335) | ~v1_relat_1(B_335))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_3962])).
% 8.15/2.88  tff(c_3996, plain, (r1_tarski('#skF_2', k1_xboole_0) | ~r1_tarski('#skF_4', k1_xboole_0) | ~v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_38, c_3985])).
% 8.15/2.88  tff(c_4003, plain, (r1_tarski('#skF_2', k1_xboole_0) | ~r1_tarski('#skF_4', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_3464, c_3996])).
% 8.15/2.88  tff(c_4004, plain, (~r1_tarski('#skF_4', k1_xboole_0)), inference(splitLeft, [status(thm)], [c_4003])).
% 8.15/2.88  tff(c_11680, plain, (~r1_tarski('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_11673, c_4004])).
% 8.15/2.88  tff(c_11725, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_14, c_11680])).
% 8.15/2.88  tff(c_11726, plain, (r1_tarski('#skF_2', k1_xboole_0)), inference(splitRight, [status(thm)], [c_4003])).
% 8.15/2.88  tff(c_3406, plain, (![B_265, A_266]: (B_265=A_266 | ~r1_tarski(B_265, A_266) | ~r1_tarski(A_266, B_265))), inference(cnfTransformation, [status(thm)], [f_42])).
% 8.15/2.88  tff(c_3415, plain, (![A_8]: (k1_xboole_0=A_8 | ~r1_tarski(A_8, k1_xboole_0))), inference(resolution, [status(thm)], [c_16, c_3406])).
% 8.15/2.88  tff(c_11744, plain, (k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_11726, c_3415])).
% 8.15/2.88  tff(c_11727, plain, (r1_tarski('#skF_4', k1_xboole_0)), inference(splitRight, [status(thm)], [c_4003])).
% 8.15/2.88  tff(c_11835, plain, (r1_tarski('#skF_4', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_11744, c_11727])).
% 8.15/2.88  tff(c_12067, plain, (![A_562]: (A_562='#skF_2' | ~r1_tarski(A_562, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_11744, c_11744, c_3415])).
% 8.15/2.88  tff(c_12081, plain, ('#skF_2'='#skF_4'), inference(resolution, [status(thm)], [c_11835, c_12067])).
% 8.15/2.88  tff(c_11799, plain, (![A_8]: (r1_tarski('#skF_2', A_8))), inference(demodulation, [status(thm), theory('equality')], [c_11744, c_16])).
% 8.15/2.88  tff(c_12096, plain, (![A_8]: (r1_tarski('#skF_4', A_8))), inference(demodulation, [status(thm), theory('equality')], [c_12081, c_11799])).
% 8.15/2.88  tff(c_36, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_80])).
% 8.15/2.88  tff(c_11800, plain, (k2_relat_1('#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_11744, c_11744, c_36])).
% 8.15/2.88  tff(c_12097, plain, (k2_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_12081, c_12081, c_11800])).
% 8.15/2.88  tff(c_12172, plain, (~r1_tarski('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_12097, c_3372])).
% 8.15/2.88  tff(c_12175, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12096, c_12172])).
% 8.15/2.88  tff(c_12177, plain, (v1_xboole_0('#skF_3')), inference(splitRight, [status(thm)], [c_3436])).
% 8.15/2.88  tff(c_12185, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_12177, c_8])).
% 8.15/2.88  tff(c_12176, plain, (v1_xboole_0('#skF_2')), inference(splitRight, [status(thm)], [c_3436])).
% 8.15/2.88  tff(c_12181, plain, (k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_12176, c_8])).
% 8.15/2.88  tff(c_12200, plain, ('#skF_2'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_12185, c_12181])).
% 8.15/2.88  tff(c_12214, plain, (r2_hidden('#skF_4', k1_funct_2('#skF_3', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_12200, c_68])).
% 8.15/2.88  tff(c_12189, plain, (![A_9]: (k2_zfmisc_1(A_9, '#skF_2')='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_12181, c_12181, c_20])).
% 8.15/2.88  tff(c_12265, plain, (![A_9]: (k2_zfmisc_1(A_9, '#skF_3')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_12200, c_12200, c_12189])).
% 8.15/2.88  tff(c_12544, plain, (![C_602, A_603, B_604]: (m1_subset_1(C_602, k1_zfmisc_1(k2_zfmisc_1(A_603, B_604))) | ~r2_hidden(C_602, k1_funct_2(A_603, B_604)))), inference(cnfTransformation, [status(thm)], [f_121])).
% 8.15/2.88  tff(c_12689, plain, (![C_613, A_614]: (m1_subset_1(C_613, k1_zfmisc_1('#skF_3')) | ~r2_hidden(C_613, k1_funct_2(A_614, '#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_12265, c_12544])).
% 8.15/2.88  tff(c_12705, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_3'))), inference(resolution, [status(thm)], [c_12214, c_12689])).
% 8.15/2.88  tff(c_12715, plain, (r1_tarski('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_12705, c_24])).
% 8.15/2.88  tff(c_12186, plain, (![A_8]: (A_8='#skF_2' | ~r1_tarski(A_8, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_12181, c_12181, c_3415])).
% 8.15/2.88  tff(c_12326, plain, (![A_8]: (A_8='#skF_3' | ~r1_tarski(A_8, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_12200, c_12200, c_12186])).
% 8.15/2.88  tff(c_12726, plain, ('#skF_3'='#skF_4'), inference(resolution, [status(thm)], [c_12715, c_12326])).
% 8.15/2.88  tff(c_12192, plain, (k2_relat_1('#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_12181, c_12181, c_36])).
% 8.15/2.88  tff(c_12225, plain, (k2_relat_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_12200, c_12200, c_12192])).
% 8.15/2.88  tff(c_12759, plain, (k2_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_12726, c_12726, c_12225])).
% 8.15/2.88  tff(c_12764, plain, (~r1_tarski(k2_relat_1('#skF_4'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_12726, c_3372])).
% 8.15/2.88  tff(c_12804, plain, (~r1_tarski('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_12759, c_12764])).
% 8.15/2.88  tff(c_12807, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_14, c_12804])).
% 8.15/2.88  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.15/2.88  
% 8.15/2.88  Inference rules
% 8.15/2.88  ----------------------
% 8.15/2.88  #Ref     : 0
% 8.15/2.88  #Sup     : 2683
% 8.15/2.88  #Fact    : 12
% 8.15/2.88  #Define  : 0
% 8.15/2.88  #Split   : 28
% 8.15/2.88  #Chain   : 0
% 8.15/2.88  #Close   : 0
% 8.15/2.88  
% 8.15/2.88  Ordering : KBO
% 8.15/2.88  
% 8.15/2.88  Simplification rules
% 8.15/2.88  ----------------------
% 8.15/2.88  #Subsume      : 641
% 8.15/2.88  #Demod        : 3030
% 8.15/2.88  #Tautology    : 1395
% 8.15/2.88  #SimpNegUnit  : 147
% 8.15/2.88  #BackRed      : 668
% 8.15/2.88  
% 8.15/2.88  #Partial instantiations: 0
% 8.15/2.88  #Strategies tried      : 1
% 8.15/2.88  
% 8.15/2.88  Timing (in seconds)
% 8.15/2.88  ----------------------
% 8.15/2.88  Preprocessing        : 0.33
% 8.15/2.88  Parsing              : 0.17
% 8.15/2.88  CNF conversion       : 0.02
% 8.15/2.88  Main loop            : 1.77
% 8.15/2.88  Inferencing          : 0.54
% 8.15/2.88  Reduction            : 0.57
% 8.15/2.88  Demodulation         : 0.39
% 8.15/2.88  BG Simplification    : 0.07
% 8.15/2.88  Subsumption          : 0.46
% 8.15/2.88  Abstraction          : 0.07
% 8.15/2.88  MUC search           : 0.00
% 8.15/2.88  Cooper               : 0.00
% 8.15/2.88  Total                : 2.15
% 8.15/2.88  Index Insertion      : 0.00
% 8.15/2.88  Index Deletion       : 0.00
% 8.15/2.88  Index Matching       : 0.00
% 8.15/2.88  BG Taut test         : 0.00
%------------------------------------------------------------------------------
