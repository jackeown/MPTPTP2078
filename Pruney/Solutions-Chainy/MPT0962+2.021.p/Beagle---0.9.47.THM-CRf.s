%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:10:54 EST 2020

% Result     : Theorem 8.85s
% Output     : CNFRefutation 8.85s
% Verified   : 
% Statistics : Number of formulae       :  127 ( 637 expanded)
%              Number of leaves         :   34 ( 216 expanded)
%              Depth                    :   13
%              Number of atoms          :  237 (1560 expanded)
%              Number of equality atoms :   56 ( 256 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2

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

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff(f_138,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_relat_1(B)
          & v1_funct_1(B) )
       => ( r1_tarski(k2_relat_1(B),A)
         => ( v1_funct_1(B)
            & v1_funct_2(B,k1_relat_1(B),A)
            & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B),A))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_funct_2)).

tff(f_44,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_107,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( ( r1_tarski(k1_relat_1(C),A)
          & r1_tarski(k2_relat_1(C),B) )
       => m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_relset_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_76,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_99,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_125,axiom,(
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

tff(f_56,axiom,(
    ! [A] :
      ( ~ ( ~ r1_xboole_0(A,A)
          & A = k1_xboole_0 )
      & ~ ( A != k1_xboole_0
          & r1_xboole_0(A,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_xboole_1)).

tff(f_64,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ~ ( r1_tarski(B,A)
          & r1_xboole_0(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_xboole_1)).

tff(f_95,axiom,(
    ! [A] :
      ( ( ~ v1_xboole_0(A)
        & v1_relat_1(A) )
     => ~ v1_xboole_0(k2_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc9_relat_1)).

tff(f_72,axiom,(
    ! [A,B] :
      ~ ( v1_xboole_0(A)
        & A != B
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_boole)).

tff(f_87,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_xboole_0(k1_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc10_relat_1)).

tff(c_58,plain,(
    v1_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_16,plain,(
    ! [B_11] : r1_tarski(B_11,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_54,plain,(
    r1_tarski(k2_relat_1('#skF_4'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_13708,plain,(
    ! [C_633,A_634,B_635] :
      ( m1_subset_1(C_633,k1_zfmisc_1(k2_zfmisc_1(A_634,B_635)))
      | ~ r1_tarski(k2_relat_1(C_633),B_635)
      | ~ r1_tarski(k1_relat_1(C_633),A_634)
      | ~ v1_relat_1(C_633) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_106,plain,(
    ! [A_52,B_53] :
      ( r2_hidden('#skF_2'(A_52,B_53),A_52)
      | r1_tarski(A_52,B_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_116,plain,(
    ! [A_52,B_53] :
      ( ~ v1_xboole_0(A_52)
      | r1_tarski(A_52,B_53) ) ),
    inference(resolution,[status(thm)],[c_106,c_2])).

tff(c_146,plain,(
    ! [B_58,A_59] :
      ( B_58 = A_59
      | ~ r1_tarski(B_58,A_59)
      | ~ r1_tarski(A_59,B_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_154,plain,
    ( k2_relat_1('#skF_4') = '#skF_3'
    | ~ r1_tarski('#skF_3',k2_relat_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_54,c_146])).

tff(c_185,plain,(
    ~ r1_tarski('#skF_3',k2_relat_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_154])).

tff(c_189,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_116,c_185])).

tff(c_56,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_52,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'),'#skF_3')))
    | ~ v1_funct_2('#skF_4',k1_relat_1('#skF_4'),'#skF_3')
    | ~ v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_60,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'),'#skF_3')))
    | ~ v1_funct_2('#skF_4',k1_relat_1('#skF_4'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_52])).

tff(c_76,plain,(
    ~ v1_funct_2('#skF_4',k1_relat_1('#skF_4'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_60])).

tff(c_900,plain,(
    ! [C_131,A_132,B_133] :
      ( m1_subset_1(C_131,k1_zfmisc_1(k2_zfmisc_1(A_132,B_133)))
      | ~ r1_tarski(k2_relat_1(C_131),B_133)
      | ~ r1_tarski(k1_relat_1(C_131),A_132)
      | ~ v1_relat_1(C_131) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_26,plain,(
    ! [A_17,B_18] :
      ( r1_tarski(A_17,B_18)
      | ~ m1_subset_1(A_17,k1_zfmisc_1(B_18)) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_2952,plain,(
    ! [C_186,A_187,B_188] :
      ( r1_tarski(C_186,k2_zfmisc_1(A_187,B_188))
      | ~ r1_tarski(k2_relat_1(C_186),B_188)
      | ~ r1_tarski(k1_relat_1(C_186),A_187)
      | ~ v1_relat_1(C_186) ) ),
    inference(resolution,[status(thm)],[c_900,c_26])).

tff(c_2957,plain,(
    ! [A_187] :
      ( r1_tarski('#skF_4',k2_zfmisc_1(A_187,'#skF_3'))
      | ~ r1_tarski(k1_relat_1('#skF_4'),A_187)
      | ~ v1_relat_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_54,c_2952])).

tff(c_2966,plain,(
    ! [A_189] :
      ( r1_tarski('#skF_4',k2_zfmisc_1(A_189,'#skF_3'))
      | ~ r1_tarski(k1_relat_1('#skF_4'),A_189) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_2957])).

tff(c_2976,plain,(
    r1_tarski('#skF_4',k2_zfmisc_1(k1_relat_1('#skF_4'),'#skF_3')) ),
    inference(resolution,[status(thm)],[c_16,c_2966])).

tff(c_28,plain,(
    ! [A_17,B_18] :
      ( m1_subset_1(A_17,k1_zfmisc_1(B_18))
      | ~ r1_tarski(A_17,B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_230,plain,(
    ! [A_74,B_75,C_76] :
      ( k1_relset_1(A_74,B_75,C_76) = k1_relat_1(C_76)
      | ~ m1_subset_1(C_76,k1_zfmisc_1(k2_zfmisc_1(A_74,B_75))) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_235,plain,(
    ! [A_74,B_75,A_17] :
      ( k1_relset_1(A_74,B_75,A_17) = k1_relat_1(A_17)
      | ~ r1_tarski(A_17,k2_zfmisc_1(A_74,B_75)) ) ),
    inference(resolution,[status(thm)],[c_28,c_230])).

tff(c_3004,plain,(
    k1_relset_1(k1_relat_1('#skF_4'),'#skF_3','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_2976,c_235])).

tff(c_1036,plain,(
    ! [B_136,C_137,A_138] :
      ( k1_xboole_0 = B_136
      | v1_funct_2(C_137,A_138,B_136)
      | k1_relset_1(A_138,B_136,C_137) != A_138
      | ~ m1_subset_1(C_137,k1_zfmisc_1(k2_zfmisc_1(A_138,B_136))) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_3020,plain,(
    ! [B_190,A_191,A_192] :
      ( k1_xboole_0 = B_190
      | v1_funct_2(A_191,A_192,B_190)
      | k1_relset_1(A_192,B_190,A_191) != A_192
      | ~ r1_tarski(A_191,k2_zfmisc_1(A_192,B_190)) ) ),
    inference(resolution,[status(thm)],[c_28,c_1036])).

tff(c_3023,plain,
    ( k1_xboole_0 = '#skF_3'
    | v1_funct_2('#skF_4',k1_relat_1('#skF_4'),'#skF_3')
    | k1_relset_1(k1_relat_1('#skF_4'),'#skF_3','#skF_4') != k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_2976,c_3020])).

tff(c_3034,plain,
    ( k1_xboole_0 = '#skF_3'
    | v1_funct_2('#skF_4',k1_relat_1('#skF_4'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3004,c_3023])).

tff(c_3035,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_3034])).

tff(c_18,plain,(
    r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_93,plain,(
    ! [B_50,A_51] :
      ( ~ r1_xboole_0(B_50,A_51)
      | ~ r1_tarski(B_50,A_51)
      | v1_xboole_0(B_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_96,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_18,c_93])).

tff(c_99,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_96])).

tff(c_3062,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3035,c_99])).

tff(c_3066,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_189,c_3062])).

tff(c_3067,plain,(
    k2_relat_1('#skF_4') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_154])).

tff(c_34,plain,(
    ! [A_23] :
      ( ~ v1_xboole_0(k2_relat_1(A_23))
      | ~ v1_relat_1(A_23)
      | v1_xboole_0(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_3074,plain,
    ( ~ v1_xboole_0('#skF_3')
    | ~ v1_relat_1('#skF_4')
    | v1_xboole_0('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_3067,c_34])).

tff(c_3078,plain,
    ( ~ v1_xboole_0('#skF_3')
    | v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_3074])).

tff(c_3081,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_3078])).

tff(c_3440,plain,(
    ! [C_254,A_255,B_256] :
      ( m1_subset_1(C_254,k1_zfmisc_1(k2_zfmisc_1(A_255,B_256)))
      | ~ r1_tarski(k2_relat_1(C_254),B_256)
      | ~ r1_tarski(k1_relat_1(C_254),A_255)
      | ~ v1_relat_1(C_254) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_6213,plain,(
    ! [C_309,A_310,B_311] :
      ( r1_tarski(C_309,k2_zfmisc_1(A_310,B_311))
      | ~ r1_tarski(k2_relat_1(C_309),B_311)
      | ~ r1_tarski(k1_relat_1(C_309),A_310)
      | ~ v1_relat_1(C_309) ) ),
    inference(resolution,[status(thm)],[c_3440,c_26])).

tff(c_6226,plain,(
    ! [C_312,A_313] :
      ( r1_tarski(C_312,k2_zfmisc_1(A_313,k2_relat_1(C_312)))
      | ~ r1_tarski(k1_relat_1(C_312),A_313)
      | ~ v1_relat_1(C_312) ) ),
    inference(resolution,[status(thm)],[c_16,c_6213])).

tff(c_6259,plain,(
    ! [A_313] :
      ( r1_tarski('#skF_4',k2_zfmisc_1(A_313,'#skF_3'))
      | ~ r1_tarski(k1_relat_1('#skF_4'),A_313)
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3067,c_6226])).

tff(c_6273,plain,(
    ! [A_314] :
      ( r1_tarski('#skF_4',k2_zfmisc_1(A_314,'#skF_3'))
      | ~ r1_tarski(k1_relat_1('#skF_4'),A_314) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_6259])).

tff(c_6288,plain,(
    r1_tarski('#skF_4',k2_zfmisc_1(k1_relat_1('#skF_4'),'#skF_3')) ),
    inference(resolution,[status(thm)],[c_16,c_6273])).

tff(c_3111,plain,(
    ! [A_203,B_204,C_205] :
      ( k1_relset_1(A_203,B_204,C_205) = k1_relat_1(C_205)
      | ~ m1_subset_1(C_205,k1_zfmisc_1(k2_zfmisc_1(A_203,B_204))) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_3116,plain,(
    ! [A_203,B_204,A_17] :
      ( k1_relset_1(A_203,B_204,A_17) = k1_relat_1(A_17)
      | ~ r1_tarski(A_17,k2_zfmisc_1(A_203,B_204)) ) ),
    inference(resolution,[status(thm)],[c_28,c_3111])).

tff(c_6310,plain,(
    k1_relset_1(k1_relat_1('#skF_4'),'#skF_3','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_6288,c_3116])).

tff(c_3796,plain,(
    ! [B_264,C_265,A_266] :
      ( k1_xboole_0 = B_264
      | v1_funct_2(C_265,A_266,B_264)
      | k1_relset_1(A_266,B_264,C_265) != A_266
      | ~ m1_subset_1(C_265,k1_zfmisc_1(k2_zfmisc_1(A_266,B_264))) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_6443,plain,(
    ! [B_326,A_327,A_328] :
      ( k1_xboole_0 = B_326
      | v1_funct_2(A_327,A_328,B_326)
      | k1_relset_1(A_328,B_326,A_327) != A_328
      | ~ r1_tarski(A_327,k2_zfmisc_1(A_328,B_326)) ) ),
    inference(resolution,[status(thm)],[c_28,c_3796])).

tff(c_6449,plain,
    ( k1_xboole_0 = '#skF_3'
    | v1_funct_2('#skF_4',k1_relat_1('#skF_4'),'#skF_3')
    | k1_relset_1(k1_relat_1('#skF_4'),'#skF_3','#skF_4') != k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_6288,c_6443])).

tff(c_6464,plain,
    ( k1_xboole_0 = '#skF_3'
    | v1_funct_2('#skF_4',k1_relat_1('#skF_4'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6310,c_6449])).

tff(c_6465,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_6464])).

tff(c_6493,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6465,c_99])).

tff(c_6497,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3081,c_6493])).

tff(c_6498,plain,(
    v1_xboole_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_3078])).

tff(c_24,plain,(
    ! [B_16,A_15] :
      ( ~ v1_xboole_0(B_16)
      | B_16 = A_15
      | ~ v1_xboole_0(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_105,plain,(
    ! [A_15] :
      ( k1_xboole_0 = A_15
      | ~ v1_xboole_0(A_15) ) ),
    inference(resolution,[status(thm)],[c_99,c_24])).

tff(c_6511,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_6498,c_105])).

tff(c_32,plain,(
    ! [A_22] :
      ( v1_xboole_0(k1_relat_1(A_22))
      | ~ v1_xboole_0(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_77,plain,(
    ! [B_39,A_40] :
      ( ~ v1_xboole_0(B_39)
      | B_39 = A_40
      | ~ v1_xboole_0(A_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_80,plain,(
    ! [A_22,A_40] :
      ( k1_relat_1(A_22) = A_40
      | ~ v1_xboole_0(A_40)
      | ~ v1_xboole_0(A_22) ) ),
    inference(resolution,[status(thm)],[c_32,c_77])).

tff(c_104,plain,(
    ! [A_22] :
      ( k1_relat_1(A_22) = k1_xboole_0
      | ~ v1_xboole_0(A_22) ) ),
    inference(resolution,[status(thm)],[c_99,c_80])).

tff(c_6510,plain,(
    k1_relat_1('#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_6498,c_104])).

tff(c_6549,plain,(
    k1_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6511,c_6510])).

tff(c_6642,plain,(
    ! [A_339,B_340,C_341] :
      ( k1_relset_1(A_339,B_340,C_341) = k1_relat_1(C_341)
      | ~ m1_subset_1(C_341,k1_zfmisc_1(k2_zfmisc_1(A_339,B_340))) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_6819,plain,(
    ! [A_366,B_367,A_368] :
      ( k1_relset_1(A_366,B_367,A_368) = k1_relat_1(A_368)
      | ~ r1_tarski(A_368,k2_zfmisc_1(A_366,B_367)) ) ),
    inference(resolution,[status(thm)],[c_28,c_6642])).

tff(c_6830,plain,(
    ! [A_369,B_370,A_371] :
      ( k1_relset_1(A_369,B_370,A_371) = k1_relat_1(A_371)
      | ~ v1_xboole_0(A_371) ) ),
    inference(resolution,[status(thm)],[c_116,c_6819])).

tff(c_6832,plain,(
    ! [A_369,B_370] : k1_relset_1(A_369,B_370,'#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_6498,c_6830])).

tff(c_6836,plain,(
    ! [A_369,B_370] : k1_relset_1(A_369,B_370,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6549,c_6832])).

tff(c_6499,plain,(
    v1_xboole_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_3078])).

tff(c_6525,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_6499,c_105])).

tff(c_6540,plain,(
    '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6511,c_6525])).

tff(c_6542,plain,(
    k2_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6540,c_3067])).

tff(c_6998,plain,(
    ! [C_394,A_395,B_396] :
      ( m1_subset_1(C_394,k1_zfmisc_1(k2_zfmisc_1(A_395,B_396)))
      | ~ r1_tarski(k2_relat_1(C_394),B_396)
      | ~ r1_tarski(k1_relat_1(C_394),A_395)
      | ~ v1_relat_1(C_394) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_9072,plain,(
    ! [C_430,A_431,B_432] :
      ( r1_tarski(C_430,k2_zfmisc_1(A_431,B_432))
      | ~ r1_tarski(k2_relat_1(C_430),B_432)
      | ~ r1_tarski(k1_relat_1(C_430),A_431)
      | ~ v1_relat_1(C_430) ) ),
    inference(resolution,[status(thm)],[c_6998,c_26])).

tff(c_12137,plain,(
    ! [C_485,A_486,B_487] :
      ( r1_tarski(C_485,k2_zfmisc_1(A_486,B_487))
      | ~ r1_tarski(k1_relat_1(C_485),A_486)
      | ~ v1_relat_1(C_485)
      | ~ v1_xboole_0(k2_relat_1(C_485)) ) ),
    inference(resolution,[status(thm)],[c_116,c_9072])).

tff(c_12229,plain,(
    ! [C_492,B_493] :
      ( r1_tarski(C_492,k2_zfmisc_1(k1_relat_1(C_492),B_493))
      | ~ v1_relat_1(C_492)
      | ~ v1_xboole_0(k2_relat_1(C_492)) ) ),
    inference(resolution,[status(thm)],[c_16,c_12137])).

tff(c_12320,plain,(
    ! [B_493] :
      ( r1_tarski('#skF_4',k2_zfmisc_1('#skF_4',B_493))
      | ~ v1_relat_1('#skF_4')
      | ~ v1_xboole_0(k2_relat_1('#skF_4')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6549,c_12229])).

tff(c_12336,plain,(
    ! [B_493] : r1_tarski('#skF_4',k2_zfmisc_1('#skF_4',B_493)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6498,c_6542,c_58,c_12320])).

tff(c_44,plain,(
    ! [C_32,B_31] :
      ( v1_funct_2(C_32,k1_xboole_0,B_31)
      | k1_relset_1(k1_xboole_0,B_31,C_32) != k1_xboole_0
      | ~ m1_subset_1(C_32,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_31))) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_6907,plain,(
    ! [C_388,B_389] :
      ( v1_funct_2(C_388,'#skF_4',B_389)
      | k1_relset_1('#skF_4',B_389,C_388) != '#skF_4'
      | ~ m1_subset_1(C_388,k1_zfmisc_1(k2_zfmisc_1('#skF_4',B_389))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6511,c_6511,c_6511,c_6511,c_44])).

tff(c_12832,plain,(
    ! [A_541,B_542] :
      ( v1_funct_2(A_541,'#skF_4',B_542)
      | k1_relset_1('#skF_4',B_542,A_541) != '#skF_4'
      | ~ r1_tarski(A_541,k2_zfmisc_1('#skF_4',B_542)) ) ),
    inference(resolution,[status(thm)],[c_28,c_6907])).

tff(c_12846,plain,(
    ! [B_493] :
      ( v1_funct_2('#skF_4','#skF_4',B_493)
      | k1_relset_1('#skF_4',B_493,'#skF_4') != '#skF_4' ) ),
    inference(resolution,[status(thm)],[c_12336,c_12832])).

tff(c_12870,plain,(
    ! [B_493] : v1_funct_2('#skF_4','#skF_4',B_493) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6836,c_12846])).

tff(c_6543,plain,(
    ~ v1_funct_2('#skF_4',k1_relat_1('#skF_4'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6540,c_76])).

tff(c_6590,plain,(
    ~ v1_funct_2('#skF_4','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6549,c_6543])).

tff(c_12880,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12870,c_6590])).

tff(c_12881,plain,(
    ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'),'#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_60])).

tff(c_13728,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_4'),'#skF_3')
    | ~ r1_tarski(k1_relat_1('#skF_4'),k1_relat_1('#skF_4'))
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_13708,c_12881])).

tff(c_13740,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_16,c_54,c_13728])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:29:41 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.85/2.85  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.85/2.86  
% 8.85/2.86  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.85/2.86  %$ v1_funct_2 > r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2
% 8.85/2.86  
% 8.85/2.86  %Foreground sorts:
% 8.85/2.86  
% 8.85/2.86  
% 8.85/2.86  %Background operators:
% 8.85/2.86  
% 8.85/2.86  
% 8.85/2.86  %Foreground operators:
% 8.85/2.86  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 8.85/2.86  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.85/2.86  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 8.85/2.86  tff('#skF_1', type, '#skF_1': $i > $i).
% 8.85/2.86  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 8.85/2.86  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 8.85/2.86  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 8.85/2.86  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 8.85/2.86  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 8.85/2.86  tff('#skF_3', type, '#skF_3': $i).
% 8.85/2.86  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 8.85/2.86  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 8.85/2.86  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.85/2.86  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 8.85/2.86  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 8.85/2.86  tff('#skF_4', type, '#skF_4': $i).
% 8.85/2.86  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.85/2.86  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 8.85/2.86  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 8.85/2.86  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 8.85/2.86  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 8.85/2.86  
% 8.85/2.88  tff(f_138, negated_conjecture, ~(![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r1_tarski(k2_relat_1(B), A) => ((v1_funct_1(B) & v1_funct_2(B, k1_relat_1(B), A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B), A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_funct_2)).
% 8.85/2.88  tff(f_44, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 8.85/2.88  tff(f_107, axiom, (![A, B, C]: (v1_relat_1(C) => ((r1_tarski(k1_relat_1(C), A) & r1_tarski(k2_relat_1(C), B)) => m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_relset_1)).
% 8.85/2.88  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 8.85/2.88  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 8.85/2.88  tff(f_76, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 8.85/2.88  tff(f_99, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 8.85/2.88  tff(f_125, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 8.85/2.88  tff(f_56, axiom, (![A]: (~(~r1_xboole_0(A, A) & (A = k1_xboole_0)) & ~(~(A = k1_xboole_0) & r1_xboole_0(A, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t66_xboole_1)).
% 8.85/2.88  tff(f_64, axiom, (![A, B]: (~v1_xboole_0(B) => ~(r1_tarski(B, A) & r1_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_xboole_1)).
% 8.85/2.88  tff(f_95, axiom, (![A]: ((~v1_xboole_0(A) & v1_relat_1(A)) => ~v1_xboole_0(k2_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc9_relat_1)).
% 8.85/2.88  tff(f_72, axiom, (![A, B]: ~((v1_xboole_0(A) & ~(A = B)) & v1_xboole_0(B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_boole)).
% 8.85/2.88  tff(f_87, axiom, (![A]: (v1_xboole_0(A) => v1_xboole_0(k1_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc10_relat_1)).
% 8.85/2.88  tff(c_58, plain, (v1_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_138])).
% 8.85/2.88  tff(c_16, plain, (![B_11]: (r1_tarski(B_11, B_11))), inference(cnfTransformation, [status(thm)], [f_44])).
% 8.85/2.88  tff(c_54, plain, (r1_tarski(k2_relat_1('#skF_4'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_138])).
% 8.85/2.88  tff(c_13708, plain, (![C_633, A_634, B_635]: (m1_subset_1(C_633, k1_zfmisc_1(k2_zfmisc_1(A_634, B_635))) | ~r1_tarski(k2_relat_1(C_633), B_635) | ~r1_tarski(k1_relat_1(C_633), A_634) | ~v1_relat_1(C_633))), inference(cnfTransformation, [status(thm)], [f_107])).
% 8.85/2.88  tff(c_106, plain, (![A_52, B_53]: (r2_hidden('#skF_2'(A_52, B_53), A_52) | r1_tarski(A_52, B_53))), inference(cnfTransformation, [status(thm)], [f_38])).
% 8.85/2.88  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 8.85/2.88  tff(c_116, plain, (![A_52, B_53]: (~v1_xboole_0(A_52) | r1_tarski(A_52, B_53))), inference(resolution, [status(thm)], [c_106, c_2])).
% 8.85/2.88  tff(c_146, plain, (![B_58, A_59]: (B_58=A_59 | ~r1_tarski(B_58, A_59) | ~r1_tarski(A_59, B_58))), inference(cnfTransformation, [status(thm)], [f_44])).
% 8.85/2.88  tff(c_154, plain, (k2_relat_1('#skF_4')='#skF_3' | ~r1_tarski('#skF_3', k2_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_54, c_146])).
% 8.85/2.88  tff(c_185, plain, (~r1_tarski('#skF_3', k2_relat_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_154])).
% 8.85/2.88  tff(c_189, plain, (~v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_116, c_185])).
% 8.85/2.88  tff(c_56, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_138])).
% 8.85/2.88  tff(c_52, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'), '#skF_3'))) | ~v1_funct_2('#skF_4', k1_relat_1('#skF_4'), '#skF_3') | ~v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_138])).
% 8.85/2.88  tff(c_60, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'), '#skF_3'))) | ~v1_funct_2('#skF_4', k1_relat_1('#skF_4'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_52])).
% 8.85/2.88  tff(c_76, plain, (~v1_funct_2('#skF_4', k1_relat_1('#skF_4'), '#skF_3')), inference(splitLeft, [status(thm)], [c_60])).
% 8.85/2.88  tff(c_900, plain, (![C_131, A_132, B_133]: (m1_subset_1(C_131, k1_zfmisc_1(k2_zfmisc_1(A_132, B_133))) | ~r1_tarski(k2_relat_1(C_131), B_133) | ~r1_tarski(k1_relat_1(C_131), A_132) | ~v1_relat_1(C_131))), inference(cnfTransformation, [status(thm)], [f_107])).
% 8.85/2.88  tff(c_26, plain, (![A_17, B_18]: (r1_tarski(A_17, B_18) | ~m1_subset_1(A_17, k1_zfmisc_1(B_18)))), inference(cnfTransformation, [status(thm)], [f_76])).
% 8.85/2.88  tff(c_2952, plain, (![C_186, A_187, B_188]: (r1_tarski(C_186, k2_zfmisc_1(A_187, B_188)) | ~r1_tarski(k2_relat_1(C_186), B_188) | ~r1_tarski(k1_relat_1(C_186), A_187) | ~v1_relat_1(C_186))), inference(resolution, [status(thm)], [c_900, c_26])).
% 8.85/2.88  tff(c_2957, plain, (![A_187]: (r1_tarski('#skF_4', k2_zfmisc_1(A_187, '#skF_3')) | ~r1_tarski(k1_relat_1('#skF_4'), A_187) | ~v1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_54, c_2952])).
% 8.85/2.88  tff(c_2966, plain, (![A_189]: (r1_tarski('#skF_4', k2_zfmisc_1(A_189, '#skF_3')) | ~r1_tarski(k1_relat_1('#skF_4'), A_189))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_2957])).
% 8.85/2.88  tff(c_2976, plain, (r1_tarski('#skF_4', k2_zfmisc_1(k1_relat_1('#skF_4'), '#skF_3'))), inference(resolution, [status(thm)], [c_16, c_2966])).
% 8.85/2.88  tff(c_28, plain, (![A_17, B_18]: (m1_subset_1(A_17, k1_zfmisc_1(B_18)) | ~r1_tarski(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_76])).
% 8.85/2.88  tff(c_230, plain, (![A_74, B_75, C_76]: (k1_relset_1(A_74, B_75, C_76)=k1_relat_1(C_76) | ~m1_subset_1(C_76, k1_zfmisc_1(k2_zfmisc_1(A_74, B_75))))), inference(cnfTransformation, [status(thm)], [f_99])).
% 8.85/2.88  tff(c_235, plain, (![A_74, B_75, A_17]: (k1_relset_1(A_74, B_75, A_17)=k1_relat_1(A_17) | ~r1_tarski(A_17, k2_zfmisc_1(A_74, B_75)))), inference(resolution, [status(thm)], [c_28, c_230])).
% 8.85/2.88  tff(c_3004, plain, (k1_relset_1(k1_relat_1('#skF_4'), '#skF_3', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_2976, c_235])).
% 8.85/2.88  tff(c_1036, plain, (![B_136, C_137, A_138]: (k1_xboole_0=B_136 | v1_funct_2(C_137, A_138, B_136) | k1_relset_1(A_138, B_136, C_137)!=A_138 | ~m1_subset_1(C_137, k1_zfmisc_1(k2_zfmisc_1(A_138, B_136))))), inference(cnfTransformation, [status(thm)], [f_125])).
% 8.85/2.88  tff(c_3020, plain, (![B_190, A_191, A_192]: (k1_xboole_0=B_190 | v1_funct_2(A_191, A_192, B_190) | k1_relset_1(A_192, B_190, A_191)!=A_192 | ~r1_tarski(A_191, k2_zfmisc_1(A_192, B_190)))), inference(resolution, [status(thm)], [c_28, c_1036])).
% 8.85/2.88  tff(c_3023, plain, (k1_xboole_0='#skF_3' | v1_funct_2('#skF_4', k1_relat_1('#skF_4'), '#skF_3') | k1_relset_1(k1_relat_1('#skF_4'), '#skF_3', '#skF_4')!=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_2976, c_3020])).
% 8.85/2.88  tff(c_3034, plain, (k1_xboole_0='#skF_3' | v1_funct_2('#skF_4', k1_relat_1('#skF_4'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_3004, c_3023])).
% 8.85/2.88  tff(c_3035, plain, (k1_xboole_0='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_76, c_3034])).
% 8.85/2.88  tff(c_18, plain, (r1_xboole_0(k1_xboole_0, k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_56])).
% 8.85/2.88  tff(c_93, plain, (![B_50, A_51]: (~r1_xboole_0(B_50, A_51) | ~r1_tarski(B_50, A_51) | v1_xboole_0(B_50))), inference(cnfTransformation, [status(thm)], [f_64])).
% 8.85/2.88  tff(c_96, plain, (~r1_tarski(k1_xboole_0, k1_xboole_0) | v1_xboole_0(k1_xboole_0)), inference(resolution, [status(thm)], [c_18, c_93])).
% 8.85/2.88  tff(c_99, plain, (v1_xboole_0(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_16, c_96])).
% 8.85/2.88  tff(c_3062, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_3035, c_99])).
% 8.85/2.88  tff(c_3066, plain, $false, inference(negUnitSimplification, [status(thm)], [c_189, c_3062])).
% 8.85/2.88  tff(c_3067, plain, (k2_relat_1('#skF_4')='#skF_3'), inference(splitRight, [status(thm)], [c_154])).
% 8.85/2.88  tff(c_34, plain, (![A_23]: (~v1_xboole_0(k2_relat_1(A_23)) | ~v1_relat_1(A_23) | v1_xboole_0(A_23))), inference(cnfTransformation, [status(thm)], [f_95])).
% 8.85/2.88  tff(c_3074, plain, (~v1_xboole_0('#skF_3') | ~v1_relat_1('#skF_4') | v1_xboole_0('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_3067, c_34])).
% 8.85/2.88  tff(c_3078, plain, (~v1_xboole_0('#skF_3') | v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_3074])).
% 8.85/2.88  tff(c_3081, plain, (~v1_xboole_0('#skF_3')), inference(splitLeft, [status(thm)], [c_3078])).
% 8.85/2.88  tff(c_3440, plain, (![C_254, A_255, B_256]: (m1_subset_1(C_254, k1_zfmisc_1(k2_zfmisc_1(A_255, B_256))) | ~r1_tarski(k2_relat_1(C_254), B_256) | ~r1_tarski(k1_relat_1(C_254), A_255) | ~v1_relat_1(C_254))), inference(cnfTransformation, [status(thm)], [f_107])).
% 8.85/2.88  tff(c_6213, plain, (![C_309, A_310, B_311]: (r1_tarski(C_309, k2_zfmisc_1(A_310, B_311)) | ~r1_tarski(k2_relat_1(C_309), B_311) | ~r1_tarski(k1_relat_1(C_309), A_310) | ~v1_relat_1(C_309))), inference(resolution, [status(thm)], [c_3440, c_26])).
% 8.85/2.88  tff(c_6226, plain, (![C_312, A_313]: (r1_tarski(C_312, k2_zfmisc_1(A_313, k2_relat_1(C_312))) | ~r1_tarski(k1_relat_1(C_312), A_313) | ~v1_relat_1(C_312))), inference(resolution, [status(thm)], [c_16, c_6213])).
% 8.85/2.88  tff(c_6259, plain, (![A_313]: (r1_tarski('#skF_4', k2_zfmisc_1(A_313, '#skF_3')) | ~r1_tarski(k1_relat_1('#skF_4'), A_313) | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_3067, c_6226])).
% 8.85/2.88  tff(c_6273, plain, (![A_314]: (r1_tarski('#skF_4', k2_zfmisc_1(A_314, '#skF_3')) | ~r1_tarski(k1_relat_1('#skF_4'), A_314))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_6259])).
% 8.85/2.88  tff(c_6288, plain, (r1_tarski('#skF_4', k2_zfmisc_1(k1_relat_1('#skF_4'), '#skF_3'))), inference(resolution, [status(thm)], [c_16, c_6273])).
% 8.85/2.88  tff(c_3111, plain, (![A_203, B_204, C_205]: (k1_relset_1(A_203, B_204, C_205)=k1_relat_1(C_205) | ~m1_subset_1(C_205, k1_zfmisc_1(k2_zfmisc_1(A_203, B_204))))), inference(cnfTransformation, [status(thm)], [f_99])).
% 8.85/2.88  tff(c_3116, plain, (![A_203, B_204, A_17]: (k1_relset_1(A_203, B_204, A_17)=k1_relat_1(A_17) | ~r1_tarski(A_17, k2_zfmisc_1(A_203, B_204)))), inference(resolution, [status(thm)], [c_28, c_3111])).
% 8.85/2.88  tff(c_6310, plain, (k1_relset_1(k1_relat_1('#skF_4'), '#skF_3', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_6288, c_3116])).
% 8.85/2.88  tff(c_3796, plain, (![B_264, C_265, A_266]: (k1_xboole_0=B_264 | v1_funct_2(C_265, A_266, B_264) | k1_relset_1(A_266, B_264, C_265)!=A_266 | ~m1_subset_1(C_265, k1_zfmisc_1(k2_zfmisc_1(A_266, B_264))))), inference(cnfTransformation, [status(thm)], [f_125])).
% 8.85/2.88  tff(c_6443, plain, (![B_326, A_327, A_328]: (k1_xboole_0=B_326 | v1_funct_2(A_327, A_328, B_326) | k1_relset_1(A_328, B_326, A_327)!=A_328 | ~r1_tarski(A_327, k2_zfmisc_1(A_328, B_326)))), inference(resolution, [status(thm)], [c_28, c_3796])).
% 8.85/2.88  tff(c_6449, plain, (k1_xboole_0='#skF_3' | v1_funct_2('#skF_4', k1_relat_1('#skF_4'), '#skF_3') | k1_relset_1(k1_relat_1('#skF_4'), '#skF_3', '#skF_4')!=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_6288, c_6443])).
% 8.85/2.88  tff(c_6464, plain, (k1_xboole_0='#skF_3' | v1_funct_2('#skF_4', k1_relat_1('#skF_4'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_6310, c_6449])).
% 8.85/2.88  tff(c_6465, plain, (k1_xboole_0='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_76, c_6464])).
% 8.85/2.88  tff(c_6493, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_6465, c_99])).
% 8.85/2.88  tff(c_6497, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3081, c_6493])).
% 8.85/2.88  tff(c_6498, plain, (v1_xboole_0('#skF_4')), inference(splitRight, [status(thm)], [c_3078])).
% 8.85/2.88  tff(c_24, plain, (![B_16, A_15]: (~v1_xboole_0(B_16) | B_16=A_15 | ~v1_xboole_0(A_15))), inference(cnfTransformation, [status(thm)], [f_72])).
% 8.85/2.88  tff(c_105, plain, (![A_15]: (k1_xboole_0=A_15 | ~v1_xboole_0(A_15))), inference(resolution, [status(thm)], [c_99, c_24])).
% 8.85/2.88  tff(c_6511, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_6498, c_105])).
% 8.85/2.88  tff(c_32, plain, (![A_22]: (v1_xboole_0(k1_relat_1(A_22)) | ~v1_xboole_0(A_22))), inference(cnfTransformation, [status(thm)], [f_87])).
% 8.85/2.88  tff(c_77, plain, (![B_39, A_40]: (~v1_xboole_0(B_39) | B_39=A_40 | ~v1_xboole_0(A_40))), inference(cnfTransformation, [status(thm)], [f_72])).
% 8.85/2.88  tff(c_80, plain, (![A_22, A_40]: (k1_relat_1(A_22)=A_40 | ~v1_xboole_0(A_40) | ~v1_xboole_0(A_22))), inference(resolution, [status(thm)], [c_32, c_77])).
% 8.85/2.88  tff(c_104, plain, (![A_22]: (k1_relat_1(A_22)=k1_xboole_0 | ~v1_xboole_0(A_22))), inference(resolution, [status(thm)], [c_99, c_80])).
% 8.85/2.88  tff(c_6510, plain, (k1_relat_1('#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_6498, c_104])).
% 8.85/2.88  tff(c_6549, plain, (k1_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_6511, c_6510])).
% 8.85/2.88  tff(c_6642, plain, (![A_339, B_340, C_341]: (k1_relset_1(A_339, B_340, C_341)=k1_relat_1(C_341) | ~m1_subset_1(C_341, k1_zfmisc_1(k2_zfmisc_1(A_339, B_340))))), inference(cnfTransformation, [status(thm)], [f_99])).
% 8.85/2.88  tff(c_6819, plain, (![A_366, B_367, A_368]: (k1_relset_1(A_366, B_367, A_368)=k1_relat_1(A_368) | ~r1_tarski(A_368, k2_zfmisc_1(A_366, B_367)))), inference(resolution, [status(thm)], [c_28, c_6642])).
% 8.85/2.88  tff(c_6830, plain, (![A_369, B_370, A_371]: (k1_relset_1(A_369, B_370, A_371)=k1_relat_1(A_371) | ~v1_xboole_0(A_371))), inference(resolution, [status(thm)], [c_116, c_6819])).
% 8.85/2.88  tff(c_6832, plain, (![A_369, B_370]: (k1_relset_1(A_369, B_370, '#skF_4')=k1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_6498, c_6830])).
% 8.85/2.88  tff(c_6836, plain, (![A_369, B_370]: (k1_relset_1(A_369, B_370, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_6549, c_6832])).
% 8.85/2.88  tff(c_6499, plain, (v1_xboole_0('#skF_3')), inference(splitRight, [status(thm)], [c_3078])).
% 8.85/2.88  tff(c_6525, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_6499, c_105])).
% 8.85/2.88  tff(c_6540, plain, ('#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_6511, c_6525])).
% 8.85/2.88  tff(c_6542, plain, (k2_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_6540, c_3067])).
% 8.85/2.88  tff(c_6998, plain, (![C_394, A_395, B_396]: (m1_subset_1(C_394, k1_zfmisc_1(k2_zfmisc_1(A_395, B_396))) | ~r1_tarski(k2_relat_1(C_394), B_396) | ~r1_tarski(k1_relat_1(C_394), A_395) | ~v1_relat_1(C_394))), inference(cnfTransformation, [status(thm)], [f_107])).
% 8.85/2.88  tff(c_9072, plain, (![C_430, A_431, B_432]: (r1_tarski(C_430, k2_zfmisc_1(A_431, B_432)) | ~r1_tarski(k2_relat_1(C_430), B_432) | ~r1_tarski(k1_relat_1(C_430), A_431) | ~v1_relat_1(C_430))), inference(resolution, [status(thm)], [c_6998, c_26])).
% 8.85/2.88  tff(c_12137, plain, (![C_485, A_486, B_487]: (r1_tarski(C_485, k2_zfmisc_1(A_486, B_487)) | ~r1_tarski(k1_relat_1(C_485), A_486) | ~v1_relat_1(C_485) | ~v1_xboole_0(k2_relat_1(C_485)))), inference(resolution, [status(thm)], [c_116, c_9072])).
% 8.85/2.88  tff(c_12229, plain, (![C_492, B_493]: (r1_tarski(C_492, k2_zfmisc_1(k1_relat_1(C_492), B_493)) | ~v1_relat_1(C_492) | ~v1_xboole_0(k2_relat_1(C_492)))), inference(resolution, [status(thm)], [c_16, c_12137])).
% 8.85/2.88  tff(c_12320, plain, (![B_493]: (r1_tarski('#skF_4', k2_zfmisc_1('#skF_4', B_493)) | ~v1_relat_1('#skF_4') | ~v1_xboole_0(k2_relat_1('#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_6549, c_12229])).
% 8.85/2.88  tff(c_12336, plain, (![B_493]: (r1_tarski('#skF_4', k2_zfmisc_1('#skF_4', B_493)))), inference(demodulation, [status(thm), theory('equality')], [c_6498, c_6542, c_58, c_12320])).
% 8.85/2.88  tff(c_44, plain, (![C_32, B_31]: (v1_funct_2(C_32, k1_xboole_0, B_31) | k1_relset_1(k1_xboole_0, B_31, C_32)!=k1_xboole_0 | ~m1_subset_1(C_32, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_31))))), inference(cnfTransformation, [status(thm)], [f_125])).
% 8.85/2.88  tff(c_6907, plain, (![C_388, B_389]: (v1_funct_2(C_388, '#skF_4', B_389) | k1_relset_1('#skF_4', B_389, C_388)!='#skF_4' | ~m1_subset_1(C_388, k1_zfmisc_1(k2_zfmisc_1('#skF_4', B_389))))), inference(demodulation, [status(thm), theory('equality')], [c_6511, c_6511, c_6511, c_6511, c_44])).
% 8.85/2.88  tff(c_12832, plain, (![A_541, B_542]: (v1_funct_2(A_541, '#skF_4', B_542) | k1_relset_1('#skF_4', B_542, A_541)!='#skF_4' | ~r1_tarski(A_541, k2_zfmisc_1('#skF_4', B_542)))), inference(resolution, [status(thm)], [c_28, c_6907])).
% 8.85/2.88  tff(c_12846, plain, (![B_493]: (v1_funct_2('#skF_4', '#skF_4', B_493) | k1_relset_1('#skF_4', B_493, '#skF_4')!='#skF_4')), inference(resolution, [status(thm)], [c_12336, c_12832])).
% 8.85/2.88  tff(c_12870, plain, (![B_493]: (v1_funct_2('#skF_4', '#skF_4', B_493))), inference(demodulation, [status(thm), theory('equality')], [c_6836, c_12846])).
% 8.85/2.88  tff(c_6543, plain, (~v1_funct_2('#skF_4', k1_relat_1('#skF_4'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_6540, c_76])).
% 8.85/2.88  tff(c_6590, plain, (~v1_funct_2('#skF_4', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_6549, c_6543])).
% 8.85/2.88  tff(c_12880, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12870, c_6590])).
% 8.85/2.88  tff(c_12881, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'), '#skF_3')))), inference(splitRight, [status(thm)], [c_60])).
% 8.85/2.88  tff(c_13728, plain, (~r1_tarski(k2_relat_1('#skF_4'), '#skF_3') | ~r1_tarski(k1_relat_1('#skF_4'), k1_relat_1('#skF_4')) | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_13708, c_12881])).
% 8.85/2.88  tff(c_13740, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_58, c_16, c_54, c_13728])).
% 8.85/2.88  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.85/2.88  
% 8.85/2.88  Inference rules
% 8.85/2.88  ----------------------
% 8.85/2.88  #Ref     : 0
% 8.85/2.88  #Sup     : 3942
% 8.85/2.88  #Fact    : 0
% 8.85/2.88  #Define  : 0
% 8.85/2.88  #Split   : 27
% 8.85/2.88  #Chain   : 0
% 8.85/2.88  #Close   : 0
% 8.85/2.88  
% 8.85/2.88  Ordering : KBO
% 8.85/2.88  
% 8.85/2.88  Simplification rules
% 8.85/2.88  ----------------------
% 8.85/2.88  #Subsume      : 1882
% 8.85/2.88  #Demod        : 1758
% 8.85/2.88  #Tautology    : 589
% 8.85/2.88  #SimpNegUnit  : 6
% 8.85/2.88  #BackRed      : 64
% 8.85/2.88  
% 8.85/2.88  #Partial instantiations: 0
% 8.85/2.88  #Strategies tried      : 1
% 8.85/2.88  
% 8.85/2.88  Timing (in seconds)
% 8.85/2.88  ----------------------
% 8.85/2.88  Preprocessing        : 0.32
% 8.85/2.88  Parsing              : 0.17
% 8.85/2.88  CNF conversion       : 0.02
% 8.85/2.88  Main loop            : 1.79
% 8.85/2.88  Inferencing          : 0.54
% 8.85/2.88  Reduction            : 0.45
% 8.85/2.88  Demodulation         : 0.31
% 8.85/2.88  BG Simplification    : 0.07
% 8.85/2.88  Subsumption          : 0.61
% 8.85/2.88  Abstraction          : 0.09
% 8.85/2.88  MUC search           : 0.00
% 8.85/2.88  Cooper               : 0.00
% 8.85/2.88  Total                : 2.15
% 8.85/2.88  Index Insertion      : 0.00
% 8.85/2.88  Index Deletion       : 0.00
% 8.85/2.88  Index Matching       : 0.00
% 8.85/2.88  BG Taut test         : 0.00
%------------------------------------------------------------------------------
