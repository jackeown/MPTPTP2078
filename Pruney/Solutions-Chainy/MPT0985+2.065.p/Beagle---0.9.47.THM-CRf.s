%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:12:36 EST 2020

% Result     : Theorem 11.15s
% Output     : CNFRefutation 11.34s
% Verified   : 
% Statistics : Number of formulae       :  290 (5143 expanded)
%              Number of leaves         :   46 (1655 expanded)
%              Depth                    :   17
%              Number of atoms          :  467 (12384 expanded)
%              Number of equality atoms :  167 (2887 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v1_partfun1 > r2_hidden > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff(k2_funct_1,type,(
    k2_funct_1: $i > $i )).

tff(v2_funct_1,type,(
    v2_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff(v1_partfun1,type,(
    v1_partfun1: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k6_partfun1,type,(
    k6_partfun1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_163,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( ( v2_funct_1(C)
            & k2_relset_1(A,B,C) = B )
         => ( v1_funct_1(k2_funct_1(C))
            & v1_funct_2(k2_funct_1(C),B,A)
            & m1_subset_1(k2_funct_1(C),k1_zfmisc_1(k2_zfmisc_1(B,A))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_funct_2)).

tff(f_104,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(B,A)))
         => v1_xboole_0(C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc4_relset_1)).

tff(f_75,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).

tff(f_97,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_112,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_93,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k2_relat_1(A) = k1_relat_1(k2_funct_1(A))
          & k1_relat_1(A) = k2_relat_1(k2_funct_1(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).

tff(f_59,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k9_relat_1(A,k1_relat_1(A)) = k2_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_relat_1)).

tff(f_108,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_130,axiom,(
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

tff(f_63,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k10_relat_1(A,k2_relat_1(A)) = k1_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_relat_1)).

tff(f_83,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( v2_funct_1(B)
       => k10_relat_1(B,A) = k9_relat_1(k2_funct_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t155_funct_1)).

tff(f_146,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_funct_1(A)
        & v1_funct_2(A,k1_relat_1(A),k2_relat_1(A))
        & m1_subset_1(A,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A)))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_funct_2)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_34,axiom,(
    ! [A,B] :
      ~ ( v1_xboole_0(A)
        & A != B
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_boole)).

tff(f_40,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_49,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_xboole_0(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_subset_1)).

tff(f_134,axiom,(
    ! [A] :
      ( v1_partfun1(k6_partfun1(A),A)
      & m1_subset_1(k6_partfun1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).

tff(f_136,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_67,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_42,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(c_74,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_8102,plain,(
    ! [C_226,B_227,A_228] :
      ( v1_xboole_0(C_226)
      | ~ m1_subset_1(C_226,k1_zfmisc_1(k2_zfmisc_1(B_227,A_228)))
      | ~ v1_xboole_0(A_228) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_8120,plain,
    ( v1_xboole_0('#skF_3')
    | ~ v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_74,c_8102])).

tff(c_8125,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_8120])).

tff(c_78,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_26,plain,(
    ! [A_15] :
      ( v1_funct_1(k2_funct_1(A_15))
      | ~ v1_funct_1(A_15)
      | ~ v1_relat_1(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_68,plain,
    ( ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_163,plain,(
    ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_68])).

tff(c_166,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_26,c_163])).

tff(c_169,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_166])).

tff(c_184,plain,(
    ! [C_53,A_54,B_55] :
      ( v1_relat_1(C_53)
      | ~ m1_subset_1(C_53,k1_zfmisc_1(k2_zfmisc_1(A_54,B_55))) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_190,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_74,c_184])).

tff(c_203,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_169,c_190])).

tff(c_204,plain,
    ( ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_68])).

tff(c_207,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_204])).

tff(c_351,plain,(
    ! [C_66,A_67,B_68] :
      ( v1_relat_1(C_66)
      | ~ m1_subset_1(C_66,k1_zfmisc_1(k2_zfmisc_1(A_67,B_68))) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_367,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_74,c_351])).

tff(c_72,plain,(
    v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_70,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_8373,plain,(
    ! [A_246,B_247,C_248] :
      ( k2_relset_1(A_246,B_247,C_248) = k2_relat_1(C_248)
      | ~ m1_subset_1(C_248,k1_zfmisc_1(k2_zfmisc_1(A_246,B_247))) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_8382,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_74,c_8373])).

tff(c_8397,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_8382])).

tff(c_34,plain,(
    ! [A_18] :
      ( k1_relat_1(k2_funct_1(A_18)) = k2_relat_1(A_18)
      | ~ v2_funct_1(A_18)
      | ~ v1_funct_1(A_18)
      | ~ v1_relat_1(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_28,plain,(
    ! [A_15] :
      ( v1_relat_1(k2_funct_1(A_15))
      | ~ v1_funct_1(A_15)
      | ~ v1_relat_1(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_8139,plain,(
    ! [A_230] :
      ( k1_relat_1(k2_funct_1(A_230)) = k2_relat_1(A_230)
      | ~ v2_funct_1(A_230)
      | ~ v1_funct_1(A_230)
      | ~ v1_relat_1(A_230) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_18,plain,(
    ! [A_12] :
      ( k9_relat_1(A_12,k1_relat_1(A_12)) = k2_relat_1(A_12)
      | ~ v1_relat_1(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_13093,plain,(
    ! [A_360] :
      ( k9_relat_1(k2_funct_1(A_360),k2_relat_1(A_360)) = k2_relat_1(k2_funct_1(A_360))
      | ~ v1_relat_1(k2_funct_1(A_360))
      | ~ v2_funct_1(A_360)
      | ~ v1_funct_1(A_360)
      | ~ v1_relat_1(A_360) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8139,c_18])).

tff(c_13109,plain,
    ( k9_relat_1(k2_funct_1('#skF_3'),'#skF_2') = k2_relat_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_8397,c_13093])).

tff(c_13122,plain,
    ( k9_relat_1(k2_funct_1('#skF_3'),'#skF_2') = k2_relat_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_367,c_78,c_72,c_13109])).

tff(c_13127,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_13122])).

tff(c_13130,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_28,c_13127])).

tff(c_13134,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_367,c_78,c_13130])).

tff(c_13136,plain,(
    v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_13122])).

tff(c_205,plain,(
    v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_68])).

tff(c_76,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_8513,plain,(
    ! [A_259,B_260,C_261] :
      ( k1_relset_1(A_259,B_260,C_261) = k1_relat_1(C_261)
      | ~ m1_subset_1(C_261,k1_zfmisc_1(k2_zfmisc_1(A_259,B_260))) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_8540,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_74,c_8513])).

tff(c_9121,plain,(
    ! [B_296,A_297,C_298] :
      ( k1_xboole_0 = B_296
      | k1_relset_1(A_297,B_296,C_298) = A_297
      | ~ v1_funct_2(C_298,A_297,B_296)
      | ~ m1_subset_1(C_298,k1_zfmisc_1(k2_zfmisc_1(A_297,B_296))) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_9133,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_1'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_74,c_9121])).

tff(c_9152,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_8540,c_9133])).

tff(c_9156,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_9152])).

tff(c_20,plain,(
    ! [A_13] :
      ( k10_relat_1(A_13,k2_relat_1(A_13)) = k1_relat_1(A_13)
      | ~ v1_relat_1(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_8412,plain,
    ( k10_relat_1('#skF_3','#skF_2') = k1_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_8397,c_20])).

tff(c_8422,plain,(
    k10_relat_1('#skF_3','#skF_2') = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_367,c_8412])).

tff(c_9163,plain,(
    k10_relat_1('#skF_3','#skF_2') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9156,c_8422])).

tff(c_13135,plain,(
    k9_relat_1(k2_funct_1('#skF_3'),'#skF_2') = k2_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_13122])).

tff(c_30,plain,(
    ! [B_17,A_16] :
      ( k9_relat_1(k2_funct_1(B_17),A_16) = k10_relat_1(B_17,A_16)
      | ~ v2_funct_1(B_17)
      | ~ v1_funct_1(B_17)
      | ~ v1_relat_1(B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_13140,plain,
    ( k2_relat_1(k2_funct_1('#skF_3')) = k10_relat_1('#skF_3','#skF_2')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_13135,c_30])).

tff(c_13147,plain,(
    k2_relat_1(k2_funct_1('#skF_3')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_367,c_78,c_72,c_9163,c_13140])).

tff(c_62,plain,(
    ! [A_37] :
      ( m1_subset_1(A_37,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_37),k2_relat_1(A_37))))
      | ~ v1_funct_1(A_37)
      | ~ v1_relat_1(A_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_13173,plain,
    ( m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_3')),'#skF_1')))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_13147,c_62])).

tff(c_13201,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_3')),'#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_13136,c_205,c_13173])).

tff(c_13292,plain,
    ( m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_3'),'#skF_1')))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_13201])).

tff(c_13307,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_367,c_78,c_72,c_8397,c_13292])).

tff(c_13309,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_207,c_13307])).

tff(c_13310,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_9152])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_13381,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_13310,c_2])).

tff(c_13383,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_8125,c_13381])).

tff(c_13384,plain,(
    v1_xboole_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_8120])).

tff(c_141,plain,(
    ! [B_45,A_46] :
      ( ~ v1_xboole_0(B_45)
      | B_45 = A_46
      | ~ v1_xboole_0(A_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_144,plain,(
    ! [A_46] :
      ( k1_xboole_0 = A_46
      | ~ v1_xboole_0(A_46) ) ),
    inference(resolution,[status(thm)],[c_2,c_141])).

tff(c_13391,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_13384,c_144])).

tff(c_8,plain,(
    ! [A_3] : k2_zfmisc_1(A_3,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_13414,plain,(
    ! [A_3] : k2_zfmisc_1(A_3,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_13391,c_13391,c_8])).

tff(c_13385,plain,(
    v1_xboole_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_8120])).

tff(c_13398,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_13385,c_144])).

tff(c_13425,plain,(
    '#skF_2' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_13391,c_13398])).

tff(c_234,plain,(
    ! [B_58,A_59] :
      ( v1_xboole_0(B_58)
      | ~ m1_subset_1(B_58,k1_zfmisc_1(A_59))
      | ~ v1_xboole_0(A_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_251,plain,
    ( v1_xboole_0('#skF_3')
    | ~ v1_xboole_0(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_74,c_234])).

tff(c_300,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_251])).

tff(c_13428,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_1','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_13425,c_300])).

tff(c_13606,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_13384,c_13414,c_13428])).

tff(c_13607,plain,(
    v1_xboole_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_251])).

tff(c_13614,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_13607,c_144])).

tff(c_10,plain,(
    ! [B_4] : k2_zfmisc_1(k1_xboole_0,B_4) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_13630,plain,(
    ! [B_4] : k2_zfmisc_1('#skF_3',B_4) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_13614,c_13614,c_10])).

tff(c_13608,plain,(
    v1_xboole_0(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_251])).

tff(c_13621,plain,(
    k2_zfmisc_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_13608,c_144])).

tff(c_13723,plain,(
    k2_zfmisc_1('#skF_1','#skF_2') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_13614,c_13621])).

tff(c_6,plain,(
    ! [B_4,A_3] :
      ( k1_xboole_0 = B_4
      | k1_xboole_0 = A_3
      | k2_zfmisc_1(A_3,B_4) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_13996,plain,(
    ! [B_401,A_402] :
      ( B_401 = '#skF_3'
      | A_402 = '#skF_3'
      | k2_zfmisc_1(A_402,B_401) != '#skF_3' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_13614,c_13614,c_13614,c_6])).

tff(c_14008,plain,
    ( '#skF_2' = '#skF_3'
    | '#skF_3' = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_13723,c_13996])).

tff(c_14011,plain,(
    '#skF_3' = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_14008])).

tff(c_13629,plain,(
    ! [A_3] : k2_zfmisc_1(A_3,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_13614,c_13614,c_8])).

tff(c_14023,plain,(
    ! [A_3] : k2_zfmisc_1(A_3,'#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_14011,c_14011,c_13629])).

tff(c_14035,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14011,c_207])).

tff(c_14314,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_1'),k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14023,c_14035])).

tff(c_13670,plain,(
    ! [C_370,A_371,B_372] :
      ( v1_relat_1(C_370)
      | ~ m1_subset_1(C_370,k1_zfmisc_1(k2_zfmisc_1(A_371,B_372))) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_13678,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_74,c_13670])).

tff(c_14028,plain,(
    v1_relat_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14011,c_13678])).

tff(c_14040,plain,(
    v1_funct_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14011,c_78])).

tff(c_14039,plain,(
    v2_funct_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14011,c_72])).

tff(c_154,plain,(
    ! [A_51] : m1_subset_1(k6_partfun1(A_51),k1_zfmisc_1(k2_zfmisc_1(A_51,A_51))) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_158,plain,(
    m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_154])).

tff(c_237,plain,
    ( v1_xboole_0(k6_partfun1(k1_xboole_0))
    | ~ v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_158,c_234])).

tff(c_249,plain,(
    v1_xboole_0(k6_partfun1(k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_237])).

tff(c_259,plain,(
    k6_partfun1(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_249,c_144])).

tff(c_13625,plain,(
    k6_partfun1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_13614,c_13614,c_259])).

tff(c_14032,plain,(
    k6_partfun1('#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_14011,c_14011,c_13625])).

tff(c_60,plain,(
    ! [A_36] : k6_relat_1(A_36) = k6_partfun1(A_36) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_24,plain,(
    ! [A_14] : k2_relat_1(k6_relat_1(A_14)) = A_14 ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_79,plain,(
    ! [A_14] : k2_relat_1(k6_partfun1(A_14)) = A_14 ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_24])).

tff(c_14093,plain,(
    k2_relat_1('#skF_1') = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_14032,c_79])).

tff(c_14055,plain,(
    ! [A_403] :
      ( k1_relat_1(k2_funct_1(A_403)) = k2_relat_1(A_403)
      | ~ v2_funct_1(A_403)
      | ~ v1_funct_1(A_403)
      | ~ v1_relat_1(A_403) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_17905,plain,(
    ! [A_515] :
      ( k9_relat_1(k2_funct_1(A_515),k2_relat_1(A_515)) = k2_relat_1(k2_funct_1(A_515))
      | ~ v1_relat_1(k2_funct_1(A_515))
      | ~ v2_funct_1(A_515)
      | ~ v1_funct_1(A_515)
      | ~ v1_relat_1(A_515) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14055,c_18])).

tff(c_17921,plain,
    ( k9_relat_1(k2_funct_1('#skF_1'),'#skF_1') = k2_relat_1(k2_funct_1('#skF_1'))
    | ~ v1_relat_1(k2_funct_1('#skF_1'))
    | ~ v2_funct_1('#skF_1')
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_14093,c_17905])).

tff(c_17931,plain,
    ( k9_relat_1(k2_funct_1('#skF_1'),'#skF_1') = k2_relat_1(k2_funct_1('#skF_1'))
    | ~ v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14028,c_14040,c_14039,c_17921])).

tff(c_17934,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_17931])).

tff(c_17937,plain,
    ( ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_28,c_17934])).

tff(c_17941,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_14028,c_14040,c_17937])).

tff(c_17943,plain,(
    v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_17931])).

tff(c_14036,plain,(
    v1_funct_1(k2_funct_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14011,c_205])).

tff(c_58,plain,(
    ! [A_35] : m1_subset_1(k6_partfun1(A_35),k1_zfmisc_1(k2_zfmisc_1(A_35,A_35))) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_13677,plain,(
    ! [A_35] : v1_relat_1(k6_partfun1(A_35)) ),
    inference(resolution,[status(thm)],[c_58,c_13670])).

tff(c_22,plain,(
    ! [A_14] : k1_relat_1(k6_relat_1(A_14)) = A_14 ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_80,plain,(
    ! [A_14] : k1_relat_1(k6_partfun1(A_14)) = A_14 ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_22])).

tff(c_208,plain,(
    ! [A_56] :
      ( k10_relat_1(A_56,k2_relat_1(A_56)) = k1_relat_1(A_56)
      | ~ v1_relat_1(A_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_217,plain,(
    ! [A_14] :
      ( k10_relat_1(k6_partfun1(A_14),A_14) = k1_relat_1(k6_partfun1(A_14))
      | ~ v1_relat_1(k6_partfun1(A_14)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_79,c_208])).

tff(c_220,plain,(
    ! [A_14] :
      ( k10_relat_1(k6_partfun1(A_14),A_14) = A_14
      | ~ v1_relat_1(k6_partfun1(A_14)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_217])).

tff(c_13979,plain,(
    ! [A_14] : k10_relat_1(k6_partfun1(A_14),A_14) = A_14 ),
    inference(demodulation,[status(thm),theory(equality)],[c_13677,c_220])).

tff(c_14073,plain,(
    k10_relat_1('#skF_1','#skF_1') = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_14032,c_13979])).

tff(c_17942,plain,(
    k9_relat_1(k2_funct_1('#skF_1'),'#skF_1') = k2_relat_1(k2_funct_1('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_17931])).

tff(c_18061,plain,
    ( k2_relat_1(k2_funct_1('#skF_1')) = k10_relat_1('#skF_1','#skF_1')
    | ~ v2_funct_1('#skF_1')
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_17942,c_30])).

tff(c_18068,plain,(
    k2_relat_1(k2_funct_1('#skF_1')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_14028,c_14040,c_14039,c_14073,c_18061])).

tff(c_18094,plain,
    ( m1_subset_1(k2_funct_1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_1')),'#skF_1')))
    | ~ v1_funct_1(k2_funct_1('#skF_1'))
    | ~ v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_18068,c_62])).

tff(c_18122,plain,(
    m1_subset_1(k2_funct_1('#skF_1'),k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_17943,c_14036,c_14023,c_18094])).

tff(c_18124,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_14314,c_18122])).

tff(c_18125,plain,(
    '#skF_2' = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_14008])).

tff(c_18128,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18125,c_207])).

tff(c_18132,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_13630,c_18128])).

tff(c_13647,plain,(
    k2_relat_1('#skF_3') = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_13625,c_79])).

tff(c_18137,plain,(
    ! [A_517] :
      ( k1_relat_1(k2_funct_1(A_517)) = k2_relat_1(A_517)
      | ~ v2_funct_1(A_517)
      | ~ v1_funct_1(A_517)
      | ~ v1_relat_1(A_517) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_24969,plain,(
    ! [A_637] :
      ( k9_relat_1(k2_funct_1(A_637),k2_relat_1(A_637)) = k2_relat_1(k2_funct_1(A_637))
      | ~ v1_relat_1(k2_funct_1(A_637))
      | ~ v2_funct_1(A_637)
      | ~ v1_funct_1(A_637)
      | ~ v1_relat_1(A_637) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18137,c_18])).

tff(c_24988,plain,
    ( k9_relat_1(k2_funct_1('#skF_3'),'#skF_3') = k2_relat_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_13647,c_24969])).

tff(c_24995,plain,
    ( k9_relat_1(k2_funct_1('#skF_3'),'#skF_3') = k2_relat_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_13678,c_78,c_72,c_24988])).

tff(c_24998,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_24995])).

tff(c_25001,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_28,c_24998])).

tff(c_25005,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_13678,c_78,c_25001])).

tff(c_25007,plain,(
    v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_24995])).

tff(c_288,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_259,c_80])).

tff(c_13654,plain,(
    k1_relat_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_13614,c_13614,c_288])).

tff(c_13665,plain,
    ( k10_relat_1('#skF_3','#skF_3') = k1_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_13647,c_20])).

tff(c_13668,plain,
    ( k10_relat_1('#skF_3','#skF_3') = '#skF_3'
    | ~ v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_13654,c_13665])).

tff(c_13871,plain,(
    k10_relat_1('#skF_3','#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_13678,c_13668])).

tff(c_25006,plain,(
    k9_relat_1(k2_funct_1('#skF_3'),'#skF_3') = k2_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_24995])).

tff(c_25011,plain,
    ( k2_relat_1(k2_funct_1('#skF_3')) = k10_relat_1('#skF_3','#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_25006,c_30])).

tff(c_25018,plain,(
    k2_relat_1(k2_funct_1('#skF_3')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_13678,c_78,c_72,c_13871,c_25011])).

tff(c_25044,plain,
    ( m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_3')),'#skF_3')))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_25018,c_62])).

tff(c_25072,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_25007,c_205,c_13629,c_25044])).

tff(c_25074,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_18132,c_25072])).

tff(c_25076,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_204])).

tff(c_25314,plain,(
    ! [C_662,B_663,A_664] :
      ( v1_xboole_0(C_662)
      | ~ m1_subset_1(C_662,k1_zfmisc_1(k2_zfmisc_1(B_663,A_664)))
      | ~ v1_xboole_0(A_664) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_25334,plain,
    ( v1_xboole_0(k2_funct_1('#skF_3'))
    | ~ v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_25076,c_25314])).

tff(c_25342,plain,(
    ~ v1_xboole_0('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_25334])).

tff(c_25219,plain,(
    ! [C_646,A_647,B_648] :
      ( v1_relat_1(C_646)
      | ~ m1_subset_1(C_646,k1_zfmisc_1(k2_zfmisc_1(A_647,B_648))) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_25239,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_74,c_25219])).

tff(c_25566,plain,(
    ! [A_684,B_685,C_686] :
      ( k2_relset_1(A_684,B_685,C_686) = k2_relat_1(C_686)
      | ~ m1_subset_1(C_686,k1_zfmisc_1(k2_zfmisc_1(A_684,B_685))) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_25575,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_74,c_25566])).

tff(c_25590,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_25575])).

tff(c_25075,plain,(
    ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_204])).

tff(c_25500,plain,(
    ! [A_676,B_677,C_678] :
      ( k1_relset_1(A_676,B_677,C_678) = k1_relat_1(C_678)
      | ~ m1_subset_1(C_678,k1_zfmisc_1(k2_zfmisc_1(A_676,B_677))) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_25520,plain,(
    k1_relset_1('#skF_2','#skF_1',k2_funct_1('#skF_3')) = k1_relat_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_25076,c_25500])).

tff(c_26231,plain,(
    ! [B_725,C_726,A_727] :
      ( k1_xboole_0 = B_725
      | v1_funct_2(C_726,A_727,B_725)
      | k1_relset_1(A_727,B_725,C_726) != A_727
      | ~ m1_subset_1(C_726,k1_zfmisc_1(k2_zfmisc_1(A_727,B_725))) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_26237,plain,
    ( k1_xboole_0 = '#skF_1'
    | v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | k1_relset_1('#skF_2','#skF_1',k2_funct_1('#skF_3')) != '#skF_2' ),
    inference(resolution,[status(thm)],[c_25076,c_26231])).

tff(c_26256,plain,
    ( k1_xboole_0 = '#skF_1'
    | v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | k1_relat_1(k2_funct_1('#skF_3')) != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_25520,c_26237])).

tff(c_26257,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_relat_1(k2_funct_1('#skF_3')) != '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_25075,c_26256])).

tff(c_26268,plain,(
    k1_relat_1(k2_funct_1('#skF_3')) != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_26257])).

tff(c_26271,plain,
    ( k2_relat_1('#skF_3') != '#skF_2'
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_26268])).

tff(c_26274,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_25239,c_78,c_72,c_25590,c_26271])).

tff(c_26275,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_26257])).

tff(c_26312,plain,(
    v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26275,c_2])).

tff(c_26314,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_25342,c_26312])).

tff(c_26316,plain,(
    v1_xboole_0('#skF_1') ),
    inference(splitRight,[status(thm)],[c_25334])).

tff(c_26322,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_26316,c_144])).

tff(c_26337,plain,(
    ! [B_4] : k2_zfmisc_1('#skF_1',B_4) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_26322,c_26322,c_10])).

tff(c_25090,plain,(
    ! [B_639,A_640] :
      ( v1_xboole_0(B_639)
      | ~ m1_subset_1(B_639,k1_zfmisc_1(A_640))
      | ~ v1_xboole_0(A_640) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_25111,plain,
    ( v1_xboole_0('#skF_3')
    | ~ v1_xboole_0(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_74,c_25090])).

tff(c_25142,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_25111])).

tff(c_26504,plain,(
    ~ v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26337,c_25142])).

tff(c_26508,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_26316,c_26504])).

tff(c_26510,plain,(
    v1_xboole_0(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_25111])).

tff(c_26509,plain,(
    v1_xboole_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_25111])).

tff(c_26516,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_26509,c_144])).

tff(c_26628,plain,(
    ! [A_739] :
      ( A_739 = '#skF_3'
      | ~ v1_xboole_0(A_739) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26516,c_144])).

tff(c_26635,plain,(
    k2_zfmisc_1('#skF_1','#skF_2') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_26510,c_26628])).

tff(c_26687,plain,(
    ! [B_742,A_743] :
      ( B_742 = '#skF_3'
      | A_743 = '#skF_3'
      | k2_zfmisc_1(A_743,B_742) != '#skF_3' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26516,c_26516,c_26516,c_6])).

tff(c_26697,plain,
    ( '#skF_2' = '#skF_3'
    | '#skF_3' = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_26635,c_26687])).

tff(c_26702,plain,(
    '#skF_3' = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_26697])).

tff(c_26555,plain,(
    ! [C_732,A_733,B_734] :
      ( v1_relat_1(C_732)
      | ~ m1_subset_1(C_732,k1_zfmisc_1(k2_zfmisc_1(A_733,B_734))) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_26567,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_74,c_26555])).

tff(c_26713,plain,(
    v1_relat_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26702,c_26567])).

tff(c_26724,plain,(
    v1_funct_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26702,c_78])).

tff(c_25096,plain,
    ( v1_xboole_0(k6_partfun1(k1_xboole_0))
    | ~ v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_158,c_25090])).

tff(c_25109,plain,(
    v1_xboole_0(k6_partfun1(k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_25096])).

tff(c_25119,plain,(
    k6_partfun1(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_25109,c_144])).

tff(c_25137,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_25119,c_80])).

tff(c_26547,plain,(
    k1_relat_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_26516,c_26516,c_25137])).

tff(c_26714,plain,(
    k1_relat_1('#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_26702,c_26702,c_26547])).

tff(c_26519,plain,(
    k6_partfun1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_26516,c_26516,c_25119])).

tff(c_26540,plain,(
    k2_relat_1('#skF_3') = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_26519,c_79])).

tff(c_26710,plain,(
    k2_relat_1('#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_26702,c_26702,c_26540])).

tff(c_26883,plain,(
    ! [A_755] :
      ( v1_funct_2(A_755,k1_relat_1(A_755),k2_relat_1(A_755))
      | ~ v1_funct_1(A_755)
      | ~ v1_relat_1(A_755) ) ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_26886,plain,
    ( v1_funct_2('#skF_1',k1_relat_1('#skF_1'),'#skF_1')
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_26710,c_26883])).

tff(c_26897,plain,(
    v1_funct_2('#skF_1','#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26713,c_26724,c_26714,c_26886])).

tff(c_12,plain,(
    ! [A_5] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_5)) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_44,plain,(
    ! [A_32] :
      ( v1_funct_2(k1_xboole_0,A_32,k1_xboole_0)
      | k1_xboole_0 = A_32
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(A_32,k1_xboole_0))) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_82,plain,(
    ! [A_32] :
      ( v1_funct_2(k1_xboole_0,A_32,k1_xboole_0)
      | k1_xboole_0 = A_32 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_44])).

tff(c_26520,plain,(
    ! [A_32] :
      ( v1_funct_2('#skF_3',A_32,'#skF_3')
      | A_32 = '#skF_3' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26516,c_26516,c_26516,c_82])).

tff(c_26921,plain,(
    ! [A_32] :
      ( v1_funct_2('#skF_1',A_32,'#skF_1')
      | A_32 = '#skF_1' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26702,c_26702,c_26702,c_26520])).

tff(c_26717,plain,(
    v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26702,c_26509])).

tff(c_26522,plain,(
    ! [A_3] : k2_zfmisc_1(A_3,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_26516,c_26516,c_8])).

tff(c_26708,plain,(
    ! [A_3] : k2_zfmisc_1(A_3,'#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_26702,c_26702,c_26522])).

tff(c_25106,plain,
    ( v1_xboole_0(k2_funct_1('#skF_3'))
    | ~ v1_xboole_0(k2_zfmisc_1('#skF_2','#skF_1')) ),
    inference(resolution,[status(thm)],[c_25076,c_25090])).

tff(c_26957,plain,(
    v1_xboole_0(k2_funct_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26717,c_26708,c_26702,c_25106])).

tff(c_26521,plain,(
    ! [A_46] :
      ( A_46 = '#skF_3'
      | ~ v1_xboole_0(A_46) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26516,c_144])).

tff(c_26707,plain,(
    ! [A_46] :
      ( A_46 = '#skF_1'
      | ~ v1_xboole_0(A_46) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26702,c_26521])).

tff(c_26967,plain,(
    k2_funct_1('#skF_1') = '#skF_1' ),
    inference(resolution,[status(thm)],[c_26957,c_26707])).

tff(c_26719,plain,(
    ~ v1_funct_2(k2_funct_1('#skF_1'),'#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26702,c_25075])).

tff(c_26970,plain,(
    ~ v1_funct_2('#skF_1','#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26967,c_26719])).

tff(c_26998,plain,(
    '#skF_2' = '#skF_1' ),
    inference(resolution,[status(thm)],[c_26921,c_26970])).

tff(c_26999,plain,(
    ~ v1_funct_2('#skF_1','#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26998,c_26970])).

tff(c_27004,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_26897,c_26999])).

tff(c_27006,plain,(
    '#skF_3' != '#skF_1' ),
    inference(splitRight,[status(thm)],[c_26697])).

tff(c_26524,plain,(
    ! [A_5] : m1_subset_1('#skF_3',k1_zfmisc_1(A_5)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26516,c_12])).

tff(c_27579,plain,(
    ! [A_796,B_797,C_798] :
      ( k1_relset_1(A_796,B_797,C_798) = k1_relat_1(C_798)
      | ~ m1_subset_1(C_798,k1_zfmisc_1(k2_zfmisc_1(A_796,B_797))) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_27592,plain,(
    ! [A_796,B_797] : k1_relset_1(A_796,B_797,'#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_26524,c_27579])).

tff(c_27598,plain,(
    ! [A_796,B_797] : k1_relset_1(A_796,B_797,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_26547,c_27592])).

tff(c_50,plain,(
    ! [B_33,C_34,A_32] :
      ( k1_xboole_0 = B_33
      | v1_funct_2(C_34,A_32,B_33)
      | k1_relset_1(A_32,B_33,C_34) != A_32
      | ~ m1_subset_1(C_34,k1_zfmisc_1(k2_zfmisc_1(A_32,B_33))) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_28082,plain,(
    ! [B_827,C_828,A_829] :
      ( B_827 = '#skF_3'
      | v1_funct_2(C_828,A_829,B_827)
      | k1_relset_1(A_829,B_827,C_828) != A_829
      | ~ m1_subset_1(C_828,k1_zfmisc_1(k2_zfmisc_1(A_829,B_827))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26516,c_50])).

tff(c_28095,plain,(
    ! [B_827,A_829] :
      ( B_827 = '#skF_3'
      | v1_funct_2('#skF_3',A_829,B_827)
      | k1_relset_1(A_829,B_827,'#skF_3') != A_829 ) ),
    inference(resolution,[status(thm)],[c_26524,c_28082])).

tff(c_28159,plain,(
    ! [B_832,A_833] :
      ( B_832 = '#skF_3'
      | v1_funct_2('#skF_3',A_833,B_832)
      | A_833 != '#skF_3' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_27598,c_28095])).

tff(c_26523,plain,(
    ! [B_4] : k2_zfmisc_1('#skF_3',B_4) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_26516,c_26516,c_10])).

tff(c_27005,plain,(
    '#skF_2' = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_26697])).

tff(c_27008,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_27005,c_25076])).

tff(c_27013,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26523,c_27008])).

tff(c_14,plain,(
    ! [B_8,A_6] :
      ( v1_xboole_0(B_8)
      | ~ m1_subset_1(B_8,k1_zfmisc_1(A_6))
      | ~ v1_xboole_0(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_27033,plain,
    ( v1_xboole_0(k2_funct_1('#skF_3'))
    | ~ v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_27013,c_14])).

tff(c_27037,plain,(
    v1_xboole_0(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26509,c_27033])).

tff(c_27043,plain,(
    k2_funct_1('#skF_3') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_27037,c_26521])).

tff(c_27009,plain,(
    ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_27005,c_25075])).

tff(c_27046,plain,(
    ~ v1_funct_2('#skF_3','#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_27043,c_27009])).

tff(c_28162,plain,(
    '#skF_3' = '#skF_1' ),
    inference(resolution,[status(thm)],[c_28159,c_27046])).

tff(c_28166,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_27006,c_28162])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:55:14 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 11.15/3.97  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.34/4.01  
% 11.34/4.01  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.34/4.01  %$ v1_funct_2 > v1_partfun1 > r2_hidden > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 11.34/4.01  
% 11.34/4.01  %Foreground sorts:
% 11.34/4.01  
% 11.34/4.01  
% 11.34/4.01  %Background operators:
% 11.34/4.01  
% 11.34/4.01  
% 11.34/4.01  %Foreground operators:
% 11.34/4.01  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 11.34/4.01  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 11.34/4.01  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 11.34/4.01  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 11.34/4.01  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 11.34/4.01  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 11.34/4.01  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 11.34/4.01  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 11.34/4.01  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 11.34/4.01  tff('#skF_2', type, '#skF_2': $i).
% 11.34/4.01  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 11.34/4.01  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 11.34/4.01  tff('#skF_3', type, '#skF_3': $i).
% 11.34/4.01  tff('#skF_1', type, '#skF_1': $i).
% 11.34/4.01  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 11.34/4.01  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 11.34/4.01  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 11.34/4.01  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 11.34/4.01  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 11.34/4.01  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 11.34/4.01  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 11.34/4.01  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 11.34/4.01  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 11.34/4.01  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 11.34/4.01  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 11.34/4.01  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 11.34/4.01  
% 11.34/4.04  tff(f_163, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((v2_funct_1(C) & (k2_relset_1(A, B, C) = B)) => ((v1_funct_1(k2_funct_1(C)) & v1_funct_2(k2_funct_1(C), B, A)) & m1_subset_1(k2_funct_1(C), k1_zfmisc_1(k2_zfmisc_1(B, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_funct_2)).
% 11.34/4.04  tff(f_104, axiom, (![A, B]: (v1_xboole_0(A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => v1_xboole_0(C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc4_relset_1)).
% 11.34/4.04  tff(f_75, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 11.34/4.04  tff(f_97, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 11.34/4.04  tff(f_112, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 11.34/4.04  tff(f_93, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k2_relat_1(A) = k1_relat_1(k2_funct_1(A))) & (k1_relat_1(A) = k2_relat_1(k2_funct_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_funct_1)).
% 11.34/4.04  tff(f_59, axiom, (![A]: (v1_relat_1(A) => (k9_relat_1(A, k1_relat_1(A)) = k2_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t146_relat_1)).
% 11.34/4.04  tff(f_108, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 11.34/4.04  tff(f_130, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 11.34/4.04  tff(f_63, axiom, (![A]: (v1_relat_1(A) => (k10_relat_1(A, k2_relat_1(A)) = k1_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t169_relat_1)).
% 11.34/4.04  tff(f_83, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (v2_funct_1(B) => (k10_relat_1(B, A) = k9_relat_1(k2_funct_1(B), A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t155_funct_1)).
% 11.34/4.04  tff(f_146, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => ((v1_funct_1(A) & v1_funct_2(A, k1_relat_1(A), k2_relat_1(A))) & m1_subset_1(A, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_funct_2)).
% 11.34/4.04  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 11.34/4.04  tff(f_34, axiom, (![A, B]: ~((v1_xboole_0(A) & ~(A = B)) & v1_xboole_0(B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_boole)).
% 11.34/4.04  tff(f_40, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 11.34/4.04  tff(f_49, axiom, (![A]: (v1_xboole_0(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_subset_1)).
% 11.34/4.04  tff(f_134, axiom, (![A]: (v1_partfun1(k6_partfun1(A), A) & m1_subset_1(k6_partfun1(A), k1_zfmisc_1(k2_zfmisc_1(A, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_partfun1)).
% 11.34/4.04  tff(f_136, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 11.34/4.04  tff(f_67, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 11.34/4.04  tff(f_42, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 11.34/4.04  tff(c_74, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_163])).
% 11.34/4.04  tff(c_8102, plain, (![C_226, B_227, A_228]: (v1_xboole_0(C_226) | ~m1_subset_1(C_226, k1_zfmisc_1(k2_zfmisc_1(B_227, A_228))) | ~v1_xboole_0(A_228))), inference(cnfTransformation, [status(thm)], [f_104])).
% 11.34/4.04  tff(c_8120, plain, (v1_xboole_0('#skF_3') | ~v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_74, c_8102])).
% 11.34/4.04  tff(c_8125, plain, (~v1_xboole_0('#skF_2')), inference(splitLeft, [status(thm)], [c_8120])).
% 11.34/4.04  tff(c_78, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_163])).
% 11.34/4.04  tff(c_26, plain, (![A_15]: (v1_funct_1(k2_funct_1(A_15)) | ~v1_funct_1(A_15) | ~v1_relat_1(A_15))), inference(cnfTransformation, [status(thm)], [f_75])).
% 11.34/4.04  tff(c_68, plain, (~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | ~v1_funct_1(k2_funct_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_163])).
% 11.34/4.04  tff(c_163, plain, (~v1_funct_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_68])).
% 11.34/4.04  tff(c_166, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_26, c_163])).
% 11.34/4.04  tff(c_169, plain, (~v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_166])).
% 11.34/4.04  tff(c_184, plain, (![C_53, A_54, B_55]: (v1_relat_1(C_53) | ~m1_subset_1(C_53, k1_zfmisc_1(k2_zfmisc_1(A_54, B_55))))), inference(cnfTransformation, [status(thm)], [f_97])).
% 11.34/4.04  tff(c_190, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_74, c_184])).
% 11.34/4.04  tff(c_203, plain, $false, inference(negUnitSimplification, [status(thm)], [c_169, c_190])).
% 11.34/4.04  tff(c_204, plain, (~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | ~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(splitRight, [status(thm)], [c_68])).
% 11.34/4.04  tff(c_207, plain, (~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(splitLeft, [status(thm)], [c_204])).
% 11.34/4.04  tff(c_351, plain, (![C_66, A_67, B_68]: (v1_relat_1(C_66) | ~m1_subset_1(C_66, k1_zfmisc_1(k2_zfmisc_1(A_67, B_68))))), inference(cnfTransformation, [status(thm)], [f_97])).
% 11.34/4.04  tff(c_367, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_74, c_351])).
% 11.34/4.04  tff(c_72, plain, (v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_163])).
% 11.34/4.04  tff(c_70, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_2'), inference(cnfTransformation, [status(thm)], [f_163])).
% 11.34/4.04  tff(c_8373, plain, (![A_246, B_247, C_248]: (k2_relset_1(A_246, B_247, C_248)=k2_relat_1(C_248) | ~m1_subset_1(C_248, k1_zfmisc_1(k2_zfmisc_1(A_246, B_247))))), inference(cnfTransformation, [status(thm)], [f_112])).
% 11.34/4.04  tff(c_8382, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_74, c_8373])).
% 11.34/4.04  tff(c_8397, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_70, c_8382])).
% 11.34/4.04  tff(c_34, plain, (![A_18]: (k1_relat_1(k2_funct_1(A_18))=k2_relat_1(A_18) | ~v2_funct_1(A_18) | ~v1_funct_1(A_18) | ~v1_relat_1(A_18))), inference(cnfTransformation, [status(thm)], [f_93])).
% 11.34/4.04  tff(c_28, plain, (![A_15]: (v1_relat_1(k2_funct_1(A_15)) | ~v1_funct_1(A_15) | ~v1_relat_1(A_15))), inference(cnfTransformation, [status(thm)], [f_75])).
% 11.34/4.04  tff(c_8139, plain, (![A_230]: (k1_relat_1(k2_funct_1(A_230))=k2_relat_1(A_230) | ~v2_funct_1(A_230) | ~v1_funct_1(A_230) | ~v1_relat_1(A_230))), inference(cnfTransformation, [status(thm)], [f_93])).
% 11.34/4.04  tff(c_18, plain, (![A_12]: (k9_relat_1(A_12, k1_relat_1(A_12))=k2_relat_1(A_12) | ~v1_relat_1(A_12))), inference(cnfTransformation, [status(thm)], [f_59])).
% 11.34/4.04  tff(c_13093, plain, (![A_360]: (k9_relat_1(k2_funct_1(A_360), k2_relat_1(A_360))=k2_relat_1(k2_funct_1(A_360)) | ~v1_relat_1(k2_funct_1(A_360)) | ~v2_funct_1(A_360) | ~v1_funct_1(A_360) | ~v1_relat_1(A_360))), inference(superposition, [status(thm), theory('equality')], [c_8139, c_18])).
% 11.34/4.04  tff(c_13109, plain, (k9_relat_1(k2_funct_1('#skF_3'), '#skF_2')=k2_relat_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_8397, c_13093])).
% 11.34/4.04  tff(c_13122, plain, (k9_relat_1(k2_funct_1('#skF_3'), '#skF_2')=k2_relat_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_367, c_78, c_72, c_13109])).
% 11.34/4.04  tff(c_13127, plain, (~v1_relat_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_13122])).
% 11.34/4.04  tff(c_13130, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_28, c_13127])).
% 11.34/4.04  tff(c_13134, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_367, c_78, c_13130])).
% 11.34/4.04  tff(c_13136, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_13122])).
% 11.34/4.04  tff(c_205, plain, (v1_funct_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_68])).
% 11.34/4.04  tff(c_76, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_163])).
% 11.34/4.04  tff(c_8513, plain, (![A_259, B_260, C_261]: (k1_relset_1(A_259, B_260, C_261)=k1_relat_1(C_261) | ~m1_subset_1(C_261, k1_zfmisc_1(k2_zfmisc_1(A_259, B_260))))), inference(cnfTransformation, [status(thm)], [f_108])).
% 11.34/4.04  tff(c_8540, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_74, c_8513])).
% 11.34/4.04  tff(c_9121, plain, (![B_296, A_297, C_298]: (k1_xboole_0=B_296 | k1_relset_1(A_297, B_296, C_298)=A_297 | ~v1_funct_2(C_298, A_297, B_296) | ~m1_subset_1(C_298, k1_zfmisc_1(k2_zfmisc_1(A_297, B_296))))), inference(cnfTransformation, [status(thm)], [f_130])).
% 11.34/4.04  tff(c_9133, plain, (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_1' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_74, c_9121])).
% 11.34/4.04  tff(c_9152, plain, (k1_xboole_0='#skF_2' | k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_76, c_8540, c_9133])).
% 11.34/4.04  tff(c_9156, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(splitLeft, [status(thm)], [c_9152])).
% 11.34/4.04  tff(c_20, plain, (![A_13]: (k10_relat_1(A_13, k2_relat_1(A_13))=k1_relat_1(A_13) | ~v1_relat_1(A_13))), inference(cnfTransformation, [status(thm)], [f_63])).
% 11.34/4.04  tff(c_8412, plain, (k10_relat_1('#skF_3', '#skF_2')=k1_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_8397, c_20])).
% 11.34/4.04  tff(c_8422, plain, (k10_relat_1('#skF_3', '#skF_2')=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_367, c_8412])).
% 11.34/4.04  tff(c_9163, plain, (k10_relat_1('#skF_3', '#skF_2')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_9156, c_8422])).
% 11.34/4.04  tff(c_13135, plain, (k9_relat_1(k2_funct_1('#skF_3'), '#skF_2')=k2_relat_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_13122])).
% 11.34/4.04  tff(c_30, plain, (![B_17, A_16]: (k9_relat_1(k2_funct_1(B_17), A_16)=k10_relat_1(B_17, A_16) | ~v2_funct_1(B_17) | ~v1_funct_1(B_17) | ~v1_relat_1(B_17))), inference(cnfTransformation, [status(thm)], [f_83])).
% 11.34/4.04  tff(c_13140, plain, (k2_relat_1(k2_funct_1('#skF_3'))=k10_relat_1('#skF_3', '#skF_2') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_13135, c_30])).
% 11.34/4.04  tff(c_13147, plain, (k2_relat_1(k2_funct_1('#skF_3'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_367, c_78, c_72, c_9163, c_13140])).
% 11.34/4.04  tff(c_62, plain, (![A_37]: (m1_subset_1(A_37, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_37), k2_relat_1(A_37)))) | ~v1_funct_1(A_37) | ~v1_relat_1(A_37))), inference(cnfTransformation, [status(thm)], [f_146])).
% 11.34/4.04  tff(c_13173, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_3')), '#skF_1'))) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_13147, c_62])).
% 11.34/4.04  tff(c_13201, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_3')), '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_13136, c_205, c_13173])).
% 11.34/4.04  tff(c_13292, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_3'), '#skF_1'))) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_34, c_13201])).
% 11.34/4.04  tff(c_13307, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_367, c_78, c_72, c_8397, c_13292])).
% 11.34/4.04  tff(c_13309, plain, $false, inference(negUnitSimplification, [status(thm)], [c_207, c_13307])).
% 11.34/4.04  tff(c_13310, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_9152])).
% 11.34/4.04  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 11.34/4.04  tff(c_13381, plain, (v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_13310, c_2])).
% 11.34/4.04  tff(c_13383, plain, $false, inference(negUnitSimplification, [status(thm)], [c_8125, c_13381])).
% 11.34/4.04  tff(c_13384, plain, (v1_xboole_0('#skF_3')), inference(splitRight, [status(thm)], [c_8120])).
% 11.34/4.04  tff(c_141, plain, (![B_45, A_46]: (~v1_xboole_0(B_45) | B_45=A_46 | ~v1_xboole_0(A_46))), inference(cnfTransformation, [status(thm)], [f_34])).
% 11.34/4.04  tff(c_144, plain, (![A_46]: (k1_xboole_0=A_46 | ~v1_xboole_0(A_46))), inference(resolution, [status(thm)], [c_2, c_141])).
% 11.34/4.04  tff(c_13391, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_13384, c_144])).
% 11.34/4.04  tff(c_8, plain, (![A_3]: (k2_zfmisc_1(A_3, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_40])).
% 11.34/4.04  tff(c_13414, plain, (![A_3]: (k2_zfmisc_1(A_3, '#skF_3')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_13391, c_13391, c_8])).
% 11.34/4.04  tff(c_13385, plain, (v1_xboole_0('#skF_2')), inference(splitRight, [status(thm)], [c_8120])).
% 11.34/4.04  tff(c_13398, plain, (k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_13385, c_144])).
% 11.34/4.04  tff(c_13425, plain, ('#skF_2'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_13391, c_13398])).
% 11.34/4.04  tff(c_234, plain, (![B_58, A_59]: (v1_xboole_0(B_58) | ~m1_subset_1(B_58, k1_zfmisc_1(A_59)) | ~v1_xboole_0(A_59))), inference(cnfTransformation, [status(thm)], [f_49])).
% 11.34/4.04  tff(c_251, plain, (v1_xboole_0('#skF_3') | ~v1_xboole_0(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_74, c_234])).
% 11.34/4.04  tff(c_300, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(splitLeft, [status(thm)], [c_251])).
% 11.34/4.04  tff(c_13428, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_1', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_13425, c_300])).
% 11.34/4.04  tff(c_13606, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_13384, c_13414, c_13428])).
% 11.34/4.04  tff(c_13607, plain, (v1_xboole_0('#skF_3')), inference(splitRight, [status(thm)], [c_251])).
% 11.34/4.04  tff(c_13614, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_13607, c_144])).
% 11.34/4.04  tff(c_10, plain, (![B_4]: (k2_zfmisc_1(k1_xboole_0, B_4)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_40])).
% 11.34/4.04  tff(c_13630, plain, (![B_4]: (k2_zfmisc_1('#skF_3', B_4)='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_13614, c_13614, c_10])).
% 11.34/4.04  tff(c_13608, plain, (v1_xboole_0(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(splitRight, [status(thm)], [c_251])).
% 11.34/4.04  tff(c_13621, plain, (k2_zfmisc_1('#skF_1', '#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_13608, c_144])).
% 11.34/4.04  tff(c_13723, plain, (k2_zfmisc_1('#skF_1', '#skF_2')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_13614, c_13621])).
% 11.34/4.04  tff(c_6, plain, (![B_4, A_3]: (k1_xboole_0=B_4 | k1_xboole_0=A_3 | k2_zfmisc_1(A_3, B_4)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_40])).
% 11.34/4.04  tff(c_13996, plain, (![B_401, A_402]: (B_401='#skF_3' | A_402='#skF_3' | k2_zfmisc_1(A_402, B_401)!='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_13614, c_13614, c_13614, c_6])).
% 11.34/4.04  tff(c_14008, plain, ('#skF_2'='#skF_3' | '#skF_3'='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_13723, c_13996])).
% 11.34/4.04  tff(c_14011, plain, ('#skF_3'='#skF_1'), inference(splitLeft, [status(thm)], [c_14008])).
% 11.34/4.04  tff(c_13629, plain, (![A_3]: (k2_zfmisc_1(A_3, '#skF_3')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_13614, c_13614, c_8])).
% 11.34/4.04  tff(c_14023, plain, (![A_3]: (k2_zfmisc_1(A_3, '#skF_1')='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_14011, c_14011, c_13629])).
% 11.34/4.04  tff(c_14035, plain, (~m1_subset_1(k2_funct_1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_14011, c_207])).
% 11.34/4.04  tff(c_14314, plain, (~m1_subset_1(k2_funct_1('#skF_1'), k1_zfmisc_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_14023, c_14035])).
% 11.34/4.04  tff(c_13670, plain, (![C_370, A_371, B_372]: (v1_relat_1(C_370) | ~m1_subset_1(C_370, k1_zfmisc_1(k2_zfmisc_1(A_371, B_372))))), inference(cnfTransformation, [status(thm)], [f_97])).
% 11.34/4.04  tff(c_13678, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_74, c_13670])).
% 11.34/4.04  tff(c_14028, plain, (v1_relat_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_14011, c_13678])).
% 11.34/4.04  tff(c_14040, plain, (v1_funct_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_14011, c_78])).
% 11.34/4.04  tff(c_14039, plain, (v2_funct_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_14011, c_72])).
% 11.34/4.04  tff(c_154, plain, (![A_51]: (m1_subset_1(k6_partfun1(A_51), k1_zfmisc_1(k2_zfmisc_1(A_51, A_51))))), inference(cnfTransformation, [status(thm)], [f_134])).
% 11.34/4.04  tff(c_158, plain, (m1_subset_1(k6_partfun1(k1_xboole_0), k1_zfmisc_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_8, c_154])).
% 11.34/4.04  tff(c_237, plain, (v1_xboole_0(k6_partfun1(k1_xboole_0)) | ~v1_xboole_0(k1_xboole_0)), inference(resolution, [status(thm)], [c_158, c_234])).
% 11.34/4.04  tff(c_249, plain, (v1_xboole_0(k6_partfun1(k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_237])).
% 11.34/4.04  tff(c_259, plain, (k6_partfun1(k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_249, c_144])).
% 11.34/4.04  tff(c_13625, plain, (k6_partfun1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_13614, c_13614, c_259])).
% 11.34/4.04  tff(c_14032, plain, (k6_partfun1('#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_14011, c_14011, c_13625])).
% 11.34/4.04  tff(c_60, plain, (![A_36]: (k6_relat_1(A_36)=k6_partfun1(A_36))), inference(cnfTransformation, [status(thm)], [f_136])).
% 11.34/4.04  tff(c_24, plain, (![A_14]: (k2_relat_1(k6_relat_1(A_14))=A_14)), inference(cnfTransformation, [status(thm)], [f_67])).
% 11.34/4.04  tff(c_79, plain, (![A_14]: (k2_relat_1(k6_partfun1(A_14))=A_14)), inference(demodulation, [status(thm), theory('equality')], [c_60, c_24])).
% 11.34/4.04  tff(c_14093, plain, (k2_relat_1('#skF_1')='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_14032, c_79])).
% 11.34/4.04  tff(c_14055, plain, (![A_403]: (k1_relat_1(k2_funct_1(A_403))=k2_relat_1(A_403) | ~v2_funct_1(A_403) | ~v1_funct_1(A_403) | ~v1_relat_1(A_403))), inference(cnfTransformation, [status(thm)], [f_93])).
% 11.34/4.04  tff(c_17905, plain, (![A_515]: (k9_relat_1(k2_funct_1(A_515), k2_relat_1(A_515))=k2_relat_1(k2_funct_1(A_515)) | ~v1_relat_1(k2_funct_1(A_515)) | ~v2_funct_1(A_515) | ~v1_funct_1(A_515) | ~v1_relat_1(A_515))), inference(superposition, [status(thm), theory('equality')], [c_14055, c_18])).
% 11.34/4.04  tff(c_17921, plain, (k9_relat_1(k2_funct_1('#skF_1'), '#skF_1')=k2_relat_1(k2_funct_1('#skF_1')) | ~v1_relat_1(k2_funct_1('#skF_1')) | ~v2_funct_1('#skF_1') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_14093, c_17905])).
% 11.34/4.04  tff(c_17931, plain, (k9_relat_1(k2_funct_1('#skF_1'), '#skF_1')=k2_relat_1(k2_funct_1('#skF_1')) | ~v1_relat_1(k2_funct_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_14028, c_14040, c_14039, c_17921])).
% 11.34/4.04  tff(c_17934, plain, (~v1_relat_1(k2_funct_1('#skF_1'))), inference(splitLeft, [status(thm)], [c_17931])).
% 11.34/4.04  tff(c_17937, plain, (~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_28, c_17934])).
% 11.34/4.04  tff(c_17941, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_14028, c_14040, c_17937])).
% 11.34/4.04  tff(c_17943, plain, (v1_relat_1(k2_funct_1('#skF_1'))), inference(splitRight, [status(thm)], [c_17931])).
% 11.34/4.04  tff(c_14036, plain, (v1_funct_1(k2_funct_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_14011, c_205])).
% 11.34/4.04  tff(c_58, plain, (![A_35]: (m1_subset_1(k6_partfun1(A_35), k1_zfmisc_1(k2_zfmisc_1(A_35, A_35))))), inference(cnfTransformation, [status(thm)], [f_134])).
% 11.34/4.04  tff(c_13677, plain, (![A_35]: (v1_relat_1(k6_partfun1(A_35)))), inference(resolution, [status(thm)], [c_58, c_13670])).
% 11.34/4.04  tff(c_22, plain, (![A_14]: (k1_relat_1(k6_relat_1(A_14))=A_14)), inference(cnfTransformation, [status(thm)], [f_67])).
% 11.34/4.04  tff(c_80, plain, (![A_14]: (k1_relat_1(k6_partfun1(A_14))=A_14)), inference(demodulation, [status(thm), theory('equality')], [c_60, c_22])).
% 11.34/4.04  tff(c_208, plain, (![A_56]: (k10_relat_1(A_56, k2_relat_1(A_56))=k1_relat_1(A_56) | ~v1_relat_1(A_56))), inference(cnfTransformation, [status(thm)], [f_63])).
% 11.34/4.04  tff(c_217, plain, (![A_14]: (k10_relat_1(k6_partfun1(A_14), A_14)=k1_relat_1(k6_partfun1(A_14)) | ~v1_relat_1(k6_partfun1(A_14)))), inference(superposition, [status(thm), theory('equality')], [c_79, c_208])).
% 11.34/4.04  tff(c_220, plain, (![A_14]: (k10_relat_1(k6_partfun1(A_14), A_14)=A_14 | ~v1_relat_1(k6_partfun1(A_14)))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_217])).
% 11.34/4.04  tff(c_13979, plain, (![A_14]: (k10_relat_1(k6_partfun1(A_14), A_14)=A_14)), inference(demodulation, [status(thm), theory('equality')], [c_13677, c_220])).
% 11.34/4.04  tff(c_14073, plain, (k10_relat_1('#skF_1', '#skF_1')='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_14032, c_13979])).
% 11.34/4.04  tff(c_17942, plain, (k9_relat_1(k2_funct_1('#skF_1'), '#skF_1')=k2_relat_1(k2_funct_1('#skF_1'))), inference(splitRight, [status(thm)], [c_17931])).
% 11.34/4.04  tff(c_18061, plain, (k2_relat_1(k2_funct_1('#skF_1'))=k10_relat_1('#skF_1', '#skF_1') | ~v2_funct_1('#skF_1') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_17942, c_30])).
% 11.34/4.04  tff(c_18068, plain, (k2_relat_1(k2_funct_1('#skF_1'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_14028, c_14040, c_14039, c_14073, c_18061])).
% 11.34/4.04  tff(c_18094, plain, (m1_subset_1(k2_funct_1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_1')), '#skF_1'))) | ~v1_funct_1(k2_funct_1('#skF_1')) | ~v1_relat_1(k2_funct_1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_18068, c_62])).
% 11.34/4.04  tff(c_18122, plain, (m1_subset_1(k2_funct_1('#skF_1'), k1_zfmisc_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_17943, c_14036, c_14023, c_18094])).
% 11.34/4.04  tff(c_18124, plain, $false, inference(negUnitSimplification, [status(thm)], [c_14314, c_18122])).
% 11.34/4.04  tff(c_18125, plain, ('#skF_2'='#skF_3'), inference(splitRight, [status(thm)], [c_14008])).
% 11.34/4.04  tff(c_18128, plain, (~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_18125, c_207])).
% 11.34/4.04  tff(c_18132, plain, (~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_13630, c_18128])).
% 11.34/4.04  tff(c_13647, plain, (k2_relat_1('#skF_3')='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_13625, c_79])).
% 11.34/4.04  tff(c_18137, plain, (![A_517]: (k1_relat_1(k2_funct_1(A_517))=k2_relat_1(A_517) | ~v2_funct_1(A_517) | ~v1_funct_1(A_517) | ~v1_relat_1(A_517))), inference(cnfTransformation, [status(thm)], [f_93])).
% 11.34/4.04  tff(c_24969, plain, (![A_637]: (k9_relat_1(k2_funct_1(A_637), k2_relat_1(A_637))=k2_relat_1(k2_funct_1(A_637)) | ~v1_relat_1(k2_funct_1(A_637)) | ~v2_funct_1(A_637) | ~v1_funct_1(A_637) | ~v1_relat_1(A_637))), inference(superposition, [status(thm), theory('equality')], [c_18137, c_18])).
% 11.34/4.04  tff(c_24988, plain, (k9_relat_1(k2_funct_1('#skF_3'), '#skF_3')=k2_relat_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_13647, c_24969])).
% 11.34/4.04  tff(c_24995, plain, (k9_relat_1(k2_funct_1('#skF_3'), '#skF_3')=k2_relat_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_13678, c_78, c_72, c_24988])).
% 11.34/4.04  tff(c_24998, plain, (~v1_relat_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_24995])).
% 11.34/4.04  tff(c_25001, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_28, c_24998])).
% 11.34/4.04  tff(c_25005, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_13678, c_78, c_25001])).
% 11.34/4.04  tff(c_25007, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_24995])).
% 11.34/4.04  tff(c_288, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_259, c_80])).
% 11.34/4.04  tff(c_13654, plain, (k1_relat_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_13614, c_13614, c_288])).
% 11.34/4.04  tff(c_13665, plain, (k10_relat_1('#skF_3', '#skF_3')=k1_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_13647, c_20])).
% 11.34/4.04  tff(c_13668, plain, (k10_relat_1('#skF_3', '#skF_3')='#skF_3' | ~v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_13654, c_13665])).
% 11.34/4.04  tff(c_13871, plain, (k10_relat_1('#skF_3', '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_13678, c_13668])).
% 11.34/4.04  tff(c_25006, plain, (k9_relat_1(k2_funct_1('#skF_3'), '#skF_3')=k2_relat_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_24995])).
% 11.34/4.04  tff(c_25011, plain, (k2_relat_1(k2_funct_1('#skF_3'))=k10_relat_1('#skF_3', '#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_25006, c_30])).
% 11.34/4.04  tff(c_25018, plain, (k2_relat_1(k2_funct_1('#skF_3'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_13678, c_78, c_72, c_13871, c_25011])).
% 11.34/4.04  tff(c_25044, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_3')), '#skF_3'))) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_25018, c_62])).
% 11.34/4.04  tff(c_25072, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_25007, c_205, c_13629, c_25044])).
% 11.34/4.04  tff(c_25074, plain, $false, inference(negUnitSimplification, [status(thm)], [c_18132, c_25072])).
% 11.34/4.04  tff(c_25076, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(splitRight, [status(thm)], [c_204])).
% 11.34/4.04  tff(c_25314, plain, (![C_662, B_663, A_664]: (v1_xboole_0(C_662) | ~m1_subset_1(C_662, k1_zfmisc_1(k2_zfmisc_1(B_663, A_664))) | ~v1_xboole_0(A_664))), inference(cnfTransformation, [status(thm)], [f_104])).
% 11.34/4.04  tff(c_25334, plain, (v1_xboole_0(k2_funct_1('#skF_3')) | ~v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_25076, c_25314])).
% 11.34/4.04  tff(c_25342, plain, (~v1_xboole_0('#skF_1')), inference(splitLeft, [status(thm)], [c_25334])).
% 11.34/4.04  tff(c_25219, plain, (![C_646, A_647, B_648]: (v1_relat_1(C_646) | ~m1_subset_1(C_646, k1_zfmisc_1(k2_zfmisc_1(A_647, B_648))))), inference(cnfTransformation, [status(thm)], [f_97])).
% 11.34/4.04  tff(c_25239, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_74, c_25219])).
% 11.34/4.04  tff(c_25566, plain, (![A_684, B_685, C_686]: (k2_relset_1(A_684, B_685, C_686)=k2_relat_1(C_686) | ~m1_subset_1(C_686, k1_zfmisc_1(k2_zfmisc_1(A_684, B_685))))), inference(cnfTransformation, [status(thm)], [f_112])).
% 11.34/4.04  tff(c_25575, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_74, c_25566])).
% 11.34/4.04  tff(c_25590, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_70, c_25575])).
% 11.34/4.04  tff(c_25075, plain, (~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_204])).
% 11.34/4.04  tff(c_25500, plain, (![A_676, B_677, C_678]: (k1_relset_1(A_676, B_677, C_678)=k1_relat_1(C_678) | ~m1_subset_1(C_678, k1_zfmisc_1(k2_zfmisc_1(A_676, B_677))))), inference(cnfTransformation, [status(thm)], [f_108])).
% 11.34/4.04  tff(c_25520, plain, (k1_relset_1('#skF_2', '#skF_1', k2_funct_1('#skF_3'))=k1_relat_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_25076, c_25500])).
% 11.34/4.04  tff(c_26231, plain, (![B_725, C_726, A_727]: (k1_xboole_0=B_725 | v1_funct_2(C_726, A_727, B_725) | k1_relset_1(A_727, B_725, C_726)!=A_727 | ~m1_subset_1(C_726, k1_zfmisc_1(k2_zfmisc_1(A_727, B_725))))), inference(cnfTransformation, [status(thm)], [f_130])).
% 11.34/4.04  tff(c_26237, plain, (k1_xboole_0='#skF_1' | v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | k1_relset_1('#skF_2', '#skF_1', k2_funct_1('#skF_3'))!='#skF_2'), inference(resolution, [status(thm)], [c_25076, c_26231])).
% 11.34/4.04  tff(c_26256, plain, (k1_xboole_0='#skF_1' | v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | k1_relat_1(k2_funct_1('#skF_3'))!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_25520, c_26237])).
% 11.34/4.04  tff(c_26257, plain, (k1_xboole_0='#skF_1' | k1_relat_1(k2_funct_1('#skF_3'))!='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_25075, c_26256])).
% 11.34/4.04  tff(c_26268, plain, (k1_relat_1(k2_funct_1('#skF_3'))!='#skF_2'), inference(splitLeft, [status(thm)], [c_26257])).
% 11.34/4.04  tff(c_26271, plain, (k2_relat_1('#skF_3')!='#skF_2' | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_34, c_26268])).
% 11.34/4.04  tff(c_26274, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_25239, c_78, c_72, c_25590, c_26271])).
% 11.34/4.04  tff(c_26275, plain, (k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_26257])).
% 11.34/4.04  tff(c_26312, plain, (v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_26275, c_2])).
% 11.34/4.04  tff(c_26314, plain, $false, inference(negUnitSimplification, [status(thm)], [c_25342, c_26312])).
% 11.34/4.04  tff(c_26316, plain, (v1_xboole_0('#skF_1')), inference(splitRight, [status(thm)], [c_25334])).
% 11.34/4.04  tff(c_26322, plain, (k1_xboole_0='#skF_1'), inference(resolution, [status(thm)], [c_26316, c_144])).
% 11.34/4.04  tff(c_26337, plain, (![B_4]: (k2_zfmisc_1('#skF_1', B_4)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_26322, c_26322, c_10])).
% 11.34/4.04  tff(c_25090, plain, (![B_639, A_640]: (v1_xboole_0(B_639) | ~m1_subset_1(B_639, k1_zfmisc_1(A_640)) | ~v1_xboole_0(A_640))), inference(cnfTransformation, [status(thm)], [f_49])).
% 11.34/4.04  tff(c_25111, plain, (v1_xboole_0('#skF_3') | ~v1_xboole_0(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_74, c_25090])).
% 11.34/4.04  tff(c_25142, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(splitLeft, [status(thm)], [c_25111])).
% 11.34/4.04  tff(c_26504, plain, (~v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_26337, c_25142])).
% 11.34/4.04  tff(c_26508, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_26316, c_26504])).
% 11.34/4.04  tff(c_26510, plain, (v1_xboole_0(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(splitRight, [status(thm)], [c_25111])).
% 11.34/4.04  tff(c_26509, plain, (v1_xboole_0('#skF_3')), inference(splitRight, [status(thm)], [c_25111])).
% 11.34/4.04  tff(c_26516, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_26509, c_144])).
% 11.34/4.04  tff(c_26628, plain, (![A_739]: (A_739='#skF_3' | ~v1_xboole_0(A_739))), inference(demodulation, [status(thm), theory('equality')], [c_26516, c_144])).
% 11.34/4.04  tff(c_26635, plain, (k2_zfmisc_1('#skF_1', '#skF_2')='#skF_3'), inference(resolution, [status(thm)], [c_26510, c_26628])).
% 11.34/4.04  tff(c_26687, plain, (![B_742, A_743]: (B_742='#skF_3' | A_743='#skF_3' | k2_zfmisc_1(A_743, B_742)!='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_26516, c_26516, c_26516, c_6])).
% 11.34/4.04  tff(c_26697, plain, ('#skF_2'='#skF_3' | '#skF_3'='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_26635, c_26687])).
% 11.34/4.04  tff(c_26702, plain, ('#skF_3'='#skF_1'), inference(splitLeft, [status(thm)], [c_26697])).
% 11.34/4.04  tff(c_26555, plain, (![C_732, A_733, B_734]: (v1_relat_1(C_732) | ~m1_subset_1(C_732, k1_zfmisc_1(k2_zfmisc_1(A_733, B_734))))), inference(cnfTransformation, [status(thm)], [f_97])).
% 11.34/4.04  tff(c_26567, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_74, c_26555])).
% 11.34/4.04  tff(c_26713, plain, (v1_relat_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_26702, c_26567])).
% 11.34/4.04  tff(c_26724, plain, (v1_funct_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_26702, c_78])).
% 11.34/4.04  tff(c_25096, plain, (v1_xboole_0(k6_partfun1(k1_xboole_0)) | ~v1_xboole_0(k1_xboole_0)), inference(resolution, [status(thm)], [c_158, c_25090])).
% 11.34/4.04  tff(c_25109, plain, (v1_xboole_0(k6_partfun1(k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_25096])).
% 11.34/4.04  tff(c_25119, plain, (k6_partfun1(k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_25109, c_144])).
% 11.34/4.04  tff(c_25137, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_25119, c_80])).
% 11.34/4.04  tff(c_26547, plain, (k1_relat_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_26516, c_26516, c_25137])).
% 11.34/4.04  tff(c_26714, plain, (k1_relat_1('#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_26702, c_26702, c_26547])).
% 11.34/4.04  tff(c_26519, plain, (k6_partfun1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_26516, c_26516, c_25119])).
% 11.34/4.04  tff(c_26540, plain, (k2_relat_1('#skF_3')='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_26519, c_79])).
% 11.34/4.04  tff(c_26710, plain, (k2_relat_1('#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_26702, c_26702, c_26540])).
% 11.34/4.04  tff(c_26883, plain, (![A_755]: (v1_funct_2(A_755, k1_relat_1(A_755), k2_relat_1(A_755)) | ~v1_funct_1(A_755) | ~v1_relat_1(A_755))), inference(cnfTransformation, [status(thm)], [f_146])).
% 11.34/4.04  tff(c_26886, plain, (v1_funct_2('#skF_1', k1_relat_1('#skF_1'), '#skF_1') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_26710, c_26883])).
% 11.34/4.04  tff(c_26897, plain, (v1_funct_2('#skF_1', '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_26713, c_26724, c_26714, c_26886])).
% 11.34/4.04  tff(c_12, plain, (![A_5]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_5)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 11.34/4.04  tff(c_44, plain, (![A_32]: (v1_funct_2(k1_xboole_0, A_32, k1_xboole_0) | k1_xboole_0=A_32 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k2_zfmisc_1(A_32, k1_xboole_0))))), inference(cnfTransformation, [status(thm)], [f_130])).
% 11.34/4.04  tff(c_82, plain, (![A_32]: (v1_funct_2(k1_xboole_0, A_32, k1_xboole_0) | k1_xboole_0=A_32)), inference(demodulation, [status(thm), theory('equality')], [c_12, c_44])).
% 11.34/4.04  tff(c_26520, plain, (![A_32]: (v1_funct_2('#skF_3', A_32, '#skF_3') | A_32='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_26516, c_26516, c_26516, c_82])).
% 11.34/4.04  tff(c_26921, plain, (![A_32]: (v1_funct_2('#skF_1', A_32, '#skF_1') | A_32='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_26702, c_26702, c_26702, c_26520])).
% 11.34/4.04  tff(c_26717, plain, (v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_26702, c_26509])).
% 11.34/4.04  tff(c_26522, plain, (![A_3]: (k2_zfmisc_1(A_3, '#skF_3')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_26516, c_26516, c_8])).
% 11.34/4.04  tff(c_26708, plain, (![A_3]: (k2_zfmisc_1(A_3, '#skF_1')='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_26702, c_26702, c_26522])).
% 11.34/4.04  tff(c_25106, plain, (v1_xboole_0(k2_funct_1('#skF_3')) | ~v1_xboole_0(k2_zfmisc_1('#skF_2', '#skF_1'))), inference(resolution, [status(thm)], [c_25076, c_25090])).
% 11.34/4.04  tff(c_26957, plain, (v1_xboole_0(k2_funct_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_26717, c_26708, c_26702, c_25106])).
% 11.34/4.04  tff(c_26521, plain, (![A_46]: (A_46='#skF_3' | ~v1_xboole_0(A_46))), inference(demodulation, [status(thm), theory('equality')], [c_26516, c_144])).
% 11.34/4.04  tff(c_26707, plain, (![A_46]: (A_46='#skF_1' | ~v1_xboole_0(A_46))), inference(demodulation, [status(thm), theory('equality')], [c_26702, c_26521])).
% 11.34/4.04  tff(c_26967, plain, (k2_funct_1('#skF_1')='#skF_1'), inference(resolution, [status(thm)], [c_26957, c_26707])).
% 11.34/4.04  tff(c_26719, plain, (~v1_funct_2(k2_funct_1('#skF_1'), '#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_26702, c_25075])).
% 11.34/4.04  tff(c_26970, plain, (~v1_funct_2('#skF_1', '#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_26967, c_26719])).
% 11.34/4.04  tff(c_26998, plain, ('#skF_2'='#skF_1'), inference(resolution, [status(thm)], [c_26921, c_26970])).
% 11.34/4.04  tff(c_26999, plain, (~v1_funct_2('#skF_1', '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_26998, c_26970])).
% 11.34/4.04  tff(c_27004, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_26897, c_26999])).
% 11.34/4.04  tff(c_27006, plain, ('#skF_3'!='#skF_1'), inference(splitRight, [status(thm)], [c_26697])).
% 11.34/4.04  tff(c_26524, plain, (![A_5]: (m1_subset_1('#skF_3', k1_zfmisc_1(A_5)))), inference(demodulation, [status(thm), theory('equality')], [c_26516, c_12])).
% 11.34/4.04  tff(c_27579, plain, (![A_796, B_797, C_798]: (k1_relset_1(A_796, B_797, C_798)=k1_relat_1(C_798) | ~m1_subset_1(C_798, k1_zfmisc_1(k2_zfmisc_1(A_796, B_797))))), inference(cnfTransformation, [status(thm)], [f_108])).
% 11.34/4.04  tff(c_27592, plain, (![A_796, B_797]: (k1_relset_1(A_796, B_797, '#skF_3')=k1_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_26524, c_27579])).
% 11.34/4.04  tff(c_27598, plain, (![A_796, B_797]: (k1_relset_1(A_796, B_797, '#skF_3')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_26547, c_27592])).
% 11.34/4.04  tff(c_50, plain, (![B_33, C_34, A_32]: (k1_xboole_0=B_33 | v1_funct_2(C_34, A_32, B_33) | k1_relset_1(A_32, B_33, C_34)!=A_32 | ~m1_subset_1(C_34, k1_zfmisc_1(k2_zfmisc_1(A_32, B_33))))), inference(cnfTransformation, [status(thm)], [f_130])).
% 11.34/4.04  tff(c_28082, plain, (![B_827, C_828, A_829]: (B_827='#skF_3' | v1_funct_2(C_828, A_829, B_827) | k1_relset_1(A_829, B_827, C_828)!=A_829 | ~m1_subset_1(C_828, k1_zfmisc_1(k2_zfmisc_1(A_829, B_827))))), inference(demodulation, [status(thm), theory('equality')], [c_26516, c_50])).
% 11.34/4.04  tff(c_28095, plain, (![B_827, A_829]: (B_827='#skF_3' | v1_funct_2('#skF_3', A_829, B_827) | k1_relset_1(A_829, B_827, '#skF_3')!=A_829)), inference(resolution, [status(thm)], [c_26524, c_28082])).
% 11.34/4.04  tff(c_28159, plain, (![B_832, A_833]: (B_832='#skF_3' | v1_funct_2('#skF_3', A_833, B_832) | A_833!='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_27598, c_28095])).
% 11.34/4.04  tff(c_26523, plain, (![B_4]: (k2_zfmisc_1('#skF_3', B_4)='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_26516, c_26516, c_10])).
% 11.34/4.04  tff(c_27005, plain, ('#skF_2'='#skF_3'), inference(splitRight, [status(thm)], [c_26697])).
% 11.34/4.04  tff(c_27008, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_27005, c_25076])).
% 11.34/4.04  tff(c_27013, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_26523, c_27008])).
% 11.34/4.04  tff(c_14, plain, (![B_8, A_6]: (v1_xboole_0(B_8) | ~m1_subset_1(B_8, k1_zfmisc_1(A_6)) | ~v1_xboole_0(A_6))), inference(cnfTransformation, [status(thm)], [f_49])).
% 11.34/4.04  tff(c_27033, plain, (v1_xboole_0(k2_funct_1('#skF_3')) | ~v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_27013, c_14])).
% 11.34/4.04  tff(c_27037, plain, (v1_xboole_0(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_26509, c_27033])).
% 11.34/4.04  tff(c_27043, plain, (k2_funct_1('#skF_3')='#skF_3'), inference(resolution, [status(thm)], [c_27037, c_26521])).
% 11.34/4.04  tff(c_27009, plain, (~v1_funct_2(k2_funct_1('#skF_3'), '#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_27005, c_25075])).
% 11.34/4.04  tff(c_27046, plain, (~v1_funct_2('#skF_3', '#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_27043, c_27009])).
% 11.34/4.04  tff(c_28162, plain, ('#skF_3'='#skF_1'), inference(resolution, [status(thm)], [c_28159, c_27046])).
% 11.34/4.04  tff(c_28166, plain, $false, inference(negUnitSimplification, [status(thm)], [c_27006, c_28162])).
% 11.34/4.04  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.34/4.04  
% 11.34/4.04  Inference rules
% 11.34/4.04  ----------------------
% 11.34/4.04  #Ref     : 0
% 11.34/4.04  #Sup     : 7787
% 11.34/4.04  #Fact    : 0
% 11.34/4.04  #Define  : 0
% 11.34/4.04  #Split   : 42
% 11.34/4.04  #Chain   : 0
% 11.34/4.04  #Close   : 0
% 11.34/4.04  
% 11.34/4.04  Ordering : KBO
% 11.34/4.04  
% 11.34/4.04  Simplification rules
% 11.34/4.04  ----------------------
% 11.34/4.04  #Subsume      : 2937
% 11.34/4.04  #Demod        : 4982
% 11.34/4.04  #Tautology    : 1823
% 11.34/4.04  #SimpNegUnit  : 14
% 11.34/4.04  #BackRed      : 318
% 11.34/4.04  
% 11.34/4.04  #Partial instantiations: 0
% 11.34/4.04  #Strategies tried      : 1
% 11.34/4.04  
% 11.34/4.04  Timing (in seconds)
% 11.34/4.04  ----------------------
% 11.34/4.05  Preprocessing        : 0.34
% 11.34/4.05  Parsing              : 0.18
% 11.34/4.05  CNF conversion       : 0.02
% 11.34/4.05  Main loop            : 2.90
% 11.34/4.05  Inferencing          : 0.78
% 11.34/4.05  Reduction            : 1.03
% 11.34/4.05  Demodulation         : 0.77
% 11.34/4.05  BG Simplification    : 0.10
% 11.34/4.05  Subsumption          : 0.81
% 11.34/4.05  Abstraction          : 0.13
% 11.34/4.05  MUC search           : 0.00
% 11.34/4.05  Cooper               : 0.00
% 11.34/4.05  Total                : 3.32
% 11.34/4.05  Index Insertion      : 0.00
% 11.34/4.05  Index Deletion       : 0.00
% 11.34/4.05  Index Matching       : 0.00
% 11.34/4.05  BG Taut test         : 0.00
%------------------------------------------------------------------------------
