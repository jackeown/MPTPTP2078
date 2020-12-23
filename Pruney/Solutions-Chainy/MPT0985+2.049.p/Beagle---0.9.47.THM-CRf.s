%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:12:33 EST 2020

% Result     : Theorem 12.38s
% Output     : CNFRefutation 12.51s
% Verified   : 
% Statistics : Number of formulae       :  246 (1013 expanded)
%              Number of leaves         :   55 ( 351 expanded)
%              Depth                    :   19
%              Number of atoms          :  419 (2695 expanded)
%              Number of equality atoms :  134 ( 550 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r2_hidden > r1_tarski > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k7_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

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

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

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

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_52,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_210,negated_conjecture,(
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

tff(f_141,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(B,A)))
         => v1_xboole_0(C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc4_relset_1)).

tff(f_94,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).

tff(f_128,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_149,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_124,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k2_relat_1(A) = k1_relat_1(k2_funct_1(A))
          & k1_relat_1(A) = k2_relat_1(k2_funct_1(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).

tff(f_68,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k9_relat_1(A,k1_relat_1(A)) = k2_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_relat_1)).

tff(f_145,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_177,axiom,(
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

tff(f_76,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k10_relat_1(A,k2_relat_1(A)) = k1_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_relat_1)).

tff(f_114,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( v2_funct_1(B)
       => k10_relat_1(B,A) = k9_relat_1(k2_funct_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t155_funct_1)).

tff(f_134,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_82,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_72,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_106,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( v2_funct_1(B)
       => k9_relat_1(B,A) = k10_relat_1(k2_funct_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t154_funct_1)).

tff(f_193,axiom,(
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

tff(f_40,axiom,(
    ! [A,B] :
      ~ ( v1_xboole_0(A)
        & A != B
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_boole)).

tff(f_46,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_181,axiom,(
    ! [A] :
      ( v1_partfun1(k6_partfun1(A),A)
      & m1_subset_1(k6_partfun1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).

tff(f_183,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_86,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_98,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v1_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).

tff(f_48,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(c_18,plain,(
    ! [A_9,B_10] :
      ( m1_subset_1(A_9,k1_zfmisc_1(B_10))
      | ~ r1_tarski(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_100,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_210])).

tff(c_1174,plain,(
    ! [C_174,B_175,A_176] :
      ( v1_xboole_0(C_174)
      | ~ m1_subset_1(C_174,k1_zfmisc_1(k2_zfmisc_1(B_175,A_176)))
      | ~ v1_xboole_0(A_176) ) ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_1197,plain,
    ( v1_xboole_0('#skF_3')
    | ~ v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_100,c_1174])).

tff(c_1202,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_1197])).

tff(c_104,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_210])).

tff(c_184,plain,(
    ! [A_69] :
      ( v1_funct_1(k2_funct_1(A_69))
      | ~ v1_funct_1(A_69)
      | ~ v1_relat_1(A_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_94,plain,
    ( ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_210])).

tff(c_183,plain,(
    ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_94])).

tff(c_187,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_184,c_183])).

tff(c_190,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_187])).

tff(c_258,plain,(
    ! [C_79,A_80,B_81] :
      ( v1_relat_1(C_79)
      | ~ m1_subset_1(C_79,k1_zfmisc_1(k2_zfmisc_1(A_80,B_81))) ) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_268,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_100,c_258])).

tff(c_283,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_190,c_268])).

tff(c_284,plain,
    ( ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_94])).

tff(c_296,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_284])).

tff(c_323,plain,(
    ~ r1_tarski(k2_funct_1('#skF_3'),k2_zfmisc_1('#skF_2','#skF_1')) ),
    inference(resolution,[status(thm)],[c_18,c_296])).

tff(c_336,plain,(
    ! [C_90,A_91,B_92] :
      ( v1_relat_1(C_90)
      | ~ m1_subset_1(C_90,k1_zfmisc_1(k2_zfmisc_1(A_91,B_92))) ) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_358,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_100,c_336])).

tff(c_40,plain,(
    ! [A_23] :
      ( v1_relat_1(k2_funct_1(A_23))
      | ~ v1_funct_1(A_23)
      | ~ v1_relat_1(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_98,plain,(
    v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_210])).

tff(c_96,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_210])).

tff(c_2464,plain,(
    ! [A_245,B_246,C_247] :
      ( k2_relset_1(A_245,B_246,C_247) = k2_relat_1(C_247)
      | ~ m1_subset_1(C_247,k1_zfmisc_1(k2_zfmisc_1(A_245,B_246))) ) ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_2477,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_100,c_2464])).

tff(c_2493,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_2477])).

tff(c_1835,plain,(
    ! [A_207] :
      ( k1_relat_1(k2_funct_1(A_207)) = k2_relat_1(A_207)
      | ~ v2_funct_1(A_207)
      | ~ v1_funct_1(A_207)
      | ~ v1_relat_1(A_207) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_26,plain,(
    ! [A_16] :
      ( k9_relat_1(A_16,k1_relat_1(A_16)) = k2_relat_1(A_16)
      | ~ v1_relat_1(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_15246,plain,(
    ! [A_595] :
      ( k9_relat_1(k2_funct_1(A_595),k2_relat_1(A_595)) = k2_relat_1(k2_funct_1(A_595))
      | ~ v1_relat_1(k2_funct_1(A_595))
      | ~ v2_funct_1(A_595)
      | ~ v1_funct_1(A_595)
      | ~ v1_relat_1(A_595) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1835,c_26])).

tff(c_15271,plain,
    ( k9_relat_1(k2_funct_1('#skF_3'),'#skF_2') = k2_relat_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_2493,c_15246])).

tff(c_15293,plain,
    ( k9_relat_1(k2_funct_1('#skF_3'),'#skF_2') = k2_relat_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_358,c_104,c_98,c_15271])).

tff(c_15298,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_15293])).

tff(c_15301,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_40,c_15298])).

tff(c_15305,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_358,c_104,c_15301])).

tff(c_15307,plain,(
    v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_15293])).

tff(c_285,plain,(
    v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_94])).

tff(c_102,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_210])).

tff(c_2615,plain,(
    ! [A_251,B_252,C_253] :
      ( k1_relset_1(A_251,B_252,C_253) = k1_relat_1(C_253)
      | ~ m1_subset_1(C_253,k1_zfmisc_1(k2_zfmisc_1(A_251,B_252))) ) ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_2647,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_100,c_2615])).

tff(c_4498,plain,(
    ! [B_333,A_334,C_335] :
      ( k1_xboole_0 = B_333
      | k1_relset_1(A_334,B_333,C_335) = A_334
      | ~ v1_funct_2(C_335,A_334,B_333)
      | ~ m1_subset_1(C_335,k1_zfmisc_1(k2_zfmisc_1(A_334,B_333))) ) ),
    inference(cnfTransformation,[status(thm)],[f_177])).

tff(c_4517,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_1'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_100,c_4498])).

tff(c_4538,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_2647,c_4517])).

tff(c_4542,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_4538])).

tff(c_30,plain,(
    ! [A_19] :
      ( k10_relat_1(A_19,k2_relat_1(A_19)) = k1_relat_1(A_19)
      | ~ v1_relat_1(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_2509,plain,
    ( k10_relat_1('#skF_3','#skF_2') = k1_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_2493,c_30])).

tff(c_2519,plain,(
    k10_relat_1('#skF_3','#skF_2') = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_358,c_2509])).

tff(c_4553,plain,(
    k10_relat_1('#skF_3','#skF_2') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4542,c_2519])).

tff(c_15306,plain,(
    k9_relat_1(k2_funct_1('#skF_3'),'#skF_2') = k2_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_15293])).

tff(c_48,plain,(
    ! [B_28,A_27] :
      ( k9_relat_1(k2_funct_1(B_28),A_27) = k10_relat_1(B_28,A_27)
      | ~ v2_funct_1(B_28)
      | ~ v1_funct_1(B_28)
      | ~ v1_relat_1(B_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_15311,plain,
    ( k2_relat_1(k2_funct_1('#skF_3')) = k10_relat_1('#skF_3','#skF_2')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_15306,c_48])).

tff(c_15318,plain,(
    k2_relat_1(k2_funct_1('#skF_3')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_358,c_104,c_98,c_4553,c_15311])).

tff(c_608,plain,(
    ! [C_123,A_124,B_125] :
      ( v4_relat_1(C_123,A_124)
      | ~ m1_subset_1(C_123,k1_zfmisc_1(k2_zfmisc_1(A_124,B_125))) ) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_631,plain,(
    v4_relat_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_100,c_608])).

tff(c_847,plain,(
    ! [B_151,A_152] :
      ( k7_relat_1(B_151,A_152) = B_151
      | ~ v4_relat_1(B_151,A_152)
      | ~ v1_relat_1(B_151) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_862,plain,
    ( k7_relat_1('#skF_3','#skF_1') = '#skF_3'
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_631,c_847])).

tff(c_875,plain,(
    k7_relat_1('#skF_3','#skF_1') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_358,c_862])).

tff(c_28,plain,(
    ! [B_18,A_17] :
      ( k2_relat_1(k7_relat_1(B_18,A_17)) = k9_relat_1(B_18,A_17)
      | ~ v1_relat_1(B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_892,plain,
    ( k9_relat_1('#skF_3','#skF_1') = k2_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_875,c_28])).

tff(c_896,plain,(
    k9_relat_1('#skF_3','#skF_1') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_358,c_892])).

tff(c_2496,plain,(
    k9_relat_1('#skF_3','#skF_1') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2493,c_896])).

tff(c_2898,plain,(
    ! [B_271,A_272] :
      ( k10_relat_1(k2_funct_1(B_271),A_272) = k9_relat_1(B_271,A_272)
      | ~ v2_funct_1(B_271)
      | ~ v1_funct_1(B_271)
      | ~ v1_relat_1(B_271) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_15394,plain,(
    ! [B_596] :
      ( k9_relat_1(B_596,k2_relat_1(k2_funct_1(B_596))) = k1_relat_1(k2_funct_1(B_596))
      | ~ v1_relat_1(k2_funct_1(B_596))
      | ~ v2_funct_1(B_596)
      | ~ v1_funct_1(B_596)
      | ~ v1_relat_1(B_596) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2898,c_30])).

tff(c_15423,plain,
    ( k1_relat_1(k2_funct_1('#skF_3')) = k9_relat_1('#skF_3','#skF_1')
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_15318,c_15394])).

tff(c_15458,plain,(
    k1_relat_1(k2_funct_1('#skF_3')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_358,c_104,c_98,c_15307,c_2496,c_15423])).

tff(c_1975,plain,(
    ! [A_223] :
      ( m1_subset_1(A_223,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_223),k2_relat_1(A_223))))
      | ~ v1_funct_1(A_223)
      | ~ v1_relat_1(A_223) ) ),
    inference(cnfTransformation,[status(thm)],[f_193])).

tff(c_16,plain,(
    ! [A_9,B_10] :
      ( r1_tarski(A_9,B_10)
      | ~ m1_subset_1(A_9,k1_zfmisc_1(B_10)) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_2019,plain,(
    ! [A_223] :
      ( r1_tarski(A_223,k2_zfmisc_1(k1_relat_1(A_223),k2_relat_1(A_223)))
      | ~ v1_funct_1(A_223)
      | ~ v1_relat_1(A_223) ) ),
    inference(resolution,[status(thm)],[c_1975,c_16])).

tff(c_15517,plain,
    ( r1_tarski(k2_funct_1('#skF_3'),k2_zfmisc_1('#skF_2',k2_relat_1(k2_funct_1('#skF_3'))))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_15458,c_2019])).

tff(c_15597,plain,(
    r1_tarski(k2_funct_1('#skF_3'),k2_zfmisc_1('#skF_2','#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_15307,c_285,c_15318,c_15517])).

tff(c_15599,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_323,c_15597])).

tff(c_15600,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_4538])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_15662,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_15600,c_2])).

tff(c_15664,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1202,c_15662])).

tff(c_15665,plain,(
    v1_xboole_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_1197])).

tff(c_171,plain,(
    ! [B_64,A_65] :
      ( ~ v1_xboole_0(B_64)
      | B_64 = A_65
      | ~ v1_xboole_0(A_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_174,plain,(
    ! [A_65] :
      ( k1_xboole_0 = A_65
      | ~ v1_xboole_0(A_65) ) ),
    inference(resolution,[status(thm)],[c_2,c_171])).

tff(c_15672,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_15665,c_174])).

tff(c_12,plain,(
    ! [B_7] : k2_zfmisc_1(k1_xboole_0,B_7) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_15709,plain,(
    ! [B_7] : k2_zfmisc_1('#skF_3',B_7) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_15672,c_15672,c_12])).

tff(c_15666,plain,(
    v1_xboole_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_1197])).

tff(c_15679,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_15666,c_174])).

tff(c_15718,plain,(
    '#skF_2' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_15672,c_15679])).

tff(c_15726,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_15718,c_296])).

tff(c_16278,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_15709,c_15726])).

tff(c_16282,plain,(
    ~ r1_tarski(k2_funct_1('#skF_3'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_18,c_16278])).

tff(c_84,plain,(
    ! [A_52] : m1_subset_1(k6_partfun1(A_52),k1_zfmisc_1(k2_zfmisc_1(A_52,A_52))) ),
    inference(cnfTransformation,[status(thm)],[f_181])).

tff(c_15990,plain,(
    ! [A_612] :
      ( v1_xboole_0(k6_partfun1(A_612))
      | ~ v1_xboole_0(A_612) ) ),
    inference(resolution,[status(thm)],[c_84,c_1174])).

tff(c_15707,plain,(
    ! [A_65] :
      ( A_65 = '#skF_3'
      | ~ v1_xboole_0(A_65) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_15672,c_174])).

tff(c_16041,plain,(
    ! [A_617] :
      ( k6_partfun1(A_617) = '#skF_3'
      | ~ v1_xboole_0(A_617) ) ),
    inference(resolution,[status(thm)],[c_15990,c_15707])).

tff(c_16049,plain,(
    k6_partfun1('#skF_3') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_15665,c_16041])).

tff(c_86,plain,(
    ! [A_53] : k6_relat_1(A_53) = k6_partfun1(A_53) ),
    inference(cnfTransformation,[status(thm)],[f_183])).

tff(c_36,plain,(
    ! [A_22] : k2_relat_1(k6_relat_1(A_22)) = A_22 ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_107,plain,(
    ! [A_22] : k2_relat_1(k6_partfun1(A_22)) = A_22 ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_36])).

tff(c_16100,plain,(
    k2_relat_1('#skF_3') = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_16049,c_107])).

tff(c_16126,plain,(
    ! [A_618] :
      ( k1_relat_1(k2_funct_1(A_618)) = k2_relat_1(A_618)
      | ~ v2_funct_1(A_618)
      | ~ v1_funct_1(A_618)
      | ~ v1_relat_1(A_618) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_23420,plain,(
    ! [A_923] :
      ( k9_relat_1(k2_funct_1(A_923),k2_relat_1(A_923)) = k2_relat_1(k2_funct_1(A_923))
      | ~ v1_relat_1(k2_funct_1(A_923))
      | ~ v2_funct_1(A_923)
      | ~ v1_funct_1(A_923)
      | ~ v1_relat_1(A_923) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16126,c_26])).

tff(c_23442,plain,
    ( k9_relat_1(k2_funct_1('#skF_3'),'#skF_3') = k2_relat_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_16100,c_23420])).

tff(c_23455,plain,
    ( k9_relat_1(k2_funct_1('#skF_3'),'#skF_3') = k2_relat_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_358,c_104,c_98,c_23442])).

tff(c_23576,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_23455])).

tff(c_23579,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_40,c_23576])).

tff(c_23583,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_358,c_104,c_23579])).

tff(c_23585,plain,(
    v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_23455])).

tff(c_10,plain,(
    ! [A_6] : k2_zfmisc_1(A_6,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_15710,plain,(
    ! [A_6] : k2_zfmisc_1(A_6,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_15672,c_15672,c_10])).

tff(c_42,plain,(
    ! [A_24] : v1_relat_1(k6_relat_1(A_24)) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_106,plain,(
    ! [A_24] : v1_relat_1(k6_partfun1(A_24)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_42])).

tff(c_34,plain,(
    ! [A_22] : k1_relat_1(k6_relat_1(A_22)) = A_22 ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_108,plain,(
    ! [A_22] : k1_relat_1(k6_partfun1(A_22)) = A_22 ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_34])).

tff(c_444,plain,(
    ! [A_102] :
      ( k10_relat_1(A_102,k2_relat_1(A_102)) = k1_relat_1(A_102)
      | ~ v1_relat_1(A_102) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_453,plain,(
    ! [A_22] :
      ( k10_relat_1(k6_partfun1(A_22),A_22) = k1_relat_1(k6_partfun1(A_22))
      | ~ v1_relat_1(k6_partfun1(A_22)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_107,c_444])).

tff(c_457,plain,(
    ! [A_22] : k10_relat_1(k6_partfun1(A_22),A_22) = A_22 ),
    inference(demodulation,[status(thm),theory(equality)],[c_106,c_108,c_453])).

tff(c_16085,plain,(
    k10_relat_1('#skF_3','#skF_3') = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_16049,c_457])).

tff(c_23584,plain,(
    k9_relat_1(k2_funct_1('#skF_3'),'#skF_3') = k2_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_23455])).

tff(c_23637,plain,
    ( k2_relat_1(k2_funct_1('#skF_3')) = k10_relat_1('#skF_3','#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_23584,c_48])).

tff(c_23646,plain,(
    k2_relat_1(k2_funct_1('#skF_3')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_358,c_104,c_98,c_16085,c_23637])).

tff(c_16458,plain,(
    ! [A_645] :
      ( m1_subset_1(A_645,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_645),k2_relat_1(A_645))))
      | ~ v1_funct_1(A_645)
      | ~ v1_relat_1(A_645) ) ),
    inference(cnfTransformation,[status(thm)],[f_193])).

tff(c_16510,plain,(
    ! [A_645] :
      ( r1_tarski(A_645,k2_zfmisc_1(k1_relat_1(A_645),k2_relat_1(A_645)))
      | ~ v1_funct_1(A_645)
      | ~ v1_relat_1(A_645) ) ),
    inference(resolution,[status(thm)],[c_16458,c_16])).

tff(c_23666,plain,
    ( r1_tarski(k2_funct_1('#skF_3'),k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_3')),'#skF_3'))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_23646,c_16510])).

tff(c_23699,plain,(
    r1_tarski(k2_funct_1('#skF_3'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_23585,c_285,c_15710,c_23666])).

tff(c_23701,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_16282,c_23699])).

tff(c_23703,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_284])).

tff(c_24400,plain,(
    ! [C_1011,B_1012,A_1013] :
      ( v1_xboole_0(C_1011)
      | ~ m1_subset_1(C_1011,k1_zfmisc_1(k2_zfmisc_1(B_1012,A_1013)))
      | ~ v1_xboole_0(A_1013) ) ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_24425,plain,
    ( v1_xboole_0(k2_funct_1('#skF_3'))
    | ~ v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_23703,c_24400])).

tff(c_24433,plain,(
    ~ v1_xboole_0('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_24425])).

tff(c_23702,plain,(
    ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_284])).

tff(c_23754,plain,(
    ! [C_939,A_940,B_941] :
      ( v1_relat_1(C_939)
      | ~ m1_subset_1(C_939,k1_zfmisc_1(k2_zfmisc_1(A_940,B_941))) ) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_23780,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_100,c_23754])).

tff(c_25368,plain,(
    ! [A_1066,B_1067,C_1068] :
      ( k2_relset_1(A_1066,B_1067,C_1068) = k2_relat_1(C_1068)
      | ~ m1_subset_1(C_1068,k1_zfmisc_1(k2_zfmisc_1(A_1066,B_1067))) ) ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_25384,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_100,c_25368])).

tff(c_25401,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_25384])).

tff(c_88,plain,(
    ! [A_54] :
      ( m1_subset_1(A_54,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_54),k2_relat_1(A_54))))
      | ~ v1_funct_1(A_54)
      | ~ v1_relat_1(A_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_193])).

tff(c_25411,plain,
    ( m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),'#skF_2')))
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_25401,c_88])).

tff(c_25423,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),'#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_23780,c_104,c_25411])).

tff(c_58,plain,(
    ! [C_35,A_33,B_34] :
      ( v4_relat_1(C_35,A_33)
      | ~ m1_subset_1(C_35,k1_zfmisc_1(k2_zfmisc_1(A_33,B_34))) ) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_25622,plain,(
    v4_relat_1('#skF_3',k1_relat_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_25423,c_58])).

tff(c_32,plain,(
    ! [B_21,A_20] :
      ( k7_relat_1(B_21,A_20) = B_21
      | ~ v4_relat_1(B_21,A_20)
      | ~ v1_relat_1(B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_25628,plain,
    ( k7_relat_1('#skF_3',k1_relat_1('#skF_3')) = '#skF_3'
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_25622,c_32])).

tff(c_25631,plain,(
    k7_relat_1('#skF_3',k1_relat_1('#skF_3')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_23780,c_25628])).

tff(c_25638,plain,
    ( k9_relat_1('#skF_3',k1_relat_1('#skF_3')) = k2_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_25631,c_28])).

tff(c_25648,plain,(
    k9_relat_1('#skF_3',k1_relat_1('#skF_3')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_23780,c_25401,c_25638])).

tff(c_23777,plain,(
    v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_23703,c_23754])).

tff(c_25417,plain,
    ( k10_relat_1('#skF_3','#skF_2') = k1_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_25401,c_30])).

tff(c_25427,plain,(
    k10_relat_1('#skF_3','#skF_2') = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_23780,c_25417])).

tff(c_26070,plain,(
    ! [B_1104,A_1105] :
      ( k9_relat_1(k2_funct_1(B_1104),A_1105) = k10_relat_1(B_1104,A_1105)
      | ~ v2_funct_1(B_1104)
      | ~ v1_funct_1(B_1104)
      | ~ v1_relat_1(B_1104) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_23897,plain,(
    ! [C_957,A_958,B_959] :
      ( v4_relat_1(C_957,A_958)
      | ~ m1_subset_1(C_957,k1_zfmisc_1(k2_zfmisc_1(A_958,B_959))) ) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_23922,plain,(
    v4_relat_1(k2_funct_1('#skF_3'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_23703,c_23897])).

tff(c_23941,plain,
    ( k7_relat_1(k2_funct_1('#skF_3'),'#skF_2') = k2_funct_1('#skF_3')
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_23922,c_32])).

tff(c_23944,plain,(
    k7_relat_1(k2_funct_1('#skF_3'),'#skF_2') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_23777,c_23941])).

tff(c_24062,plain,(
    ! [B_974,A_975] :
      ( k2_relat_1(k7_relat_1(B_974,A_975)) = k9_relat_1(B_974,A_975)
      | ~ v1_relat_1(B_974) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_24074,plain,
    ( k9_relat_1(k2_funct_1('#skF_3'),'#skF_2') = k2_relat_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_23944,c_24062])).

tff(c_24087,plain,(
    k9_relat_1(k2_funct_1('#skF_3'),'#skF_2') = k2_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_23777,c_24074])).

tff(c_26076,plain,
    ( k2_relat_1(k2_funct_1('#skF_3')) = k10_relat_1('#skF_3','#skF_2')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_26070,c_24087])).

tff(c_26093,plain,(
    k2_relat_1(k2_funct_1('#skF_3')) = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_23780,c_104,c_98,c_25427,c_26076])).

tff(c_26114,plain,
    ( k10_relat_1(k2_funct_1('#skF_3'),k1_relat_1('#skF_3')) = k1_relat_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_26093,c_30])).

tff(c_26130,plain,(
    k10_relat_1(k2_funct_1('#skF_3'),k1_relat_1('#skF_3')) = k1_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_23777,c_26114])).

tff(c_46,plain,(
    ! [B_26,A_25] :
      ( k10_relat_1(k2_funct_1(B_26),A_25) = k9_relat_1(B_26,A_25)
      | ~ v2_funct_1(B_26)
      | ~ v1_funct_1(B_26)
      | ~ v1_relat_1(B_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_26286,plain,
    ( k9_relat_1('#skF_3',k1_relat_1('#skF_3')) = k1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_26130,c_46])).

tff(c_26293,plain,(
    k1_relat_1(k2_funct_1('#skF_3')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_23780,c_104,c_98,c_25648,c_26286])).

tff(c_25500,plain,(
    ! [A_1077,B_1078,C_1079] :
      ( k1_relset_1(A_1077,B_1078,C_1079) = k1_relat_1(C_1079)
      | ~ m1_subset_1(C_1079,k1_zfmisc_1(k2_zfmisc_1(A_1077,B_1078))) ) ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_25529,plain,(
    k1_relset_1('#skF_2','#skF_1',k2_funct_1('#skF_3')) = k1_relat_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_23703,c_25500])).

tff(c_26298,plain,(
    k1_relset_1('#skF_2','#skF_1',k2_funct_1('#skF_3')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_26293,c_25529])).

tff(c_26471,plain,(
    ! [B_1119,C_1120,A_1121] :
      ( k1_xboole_0 = B_1119
      | v1_funct_2(C_1120,A_1121,B_1119)
      | k1_relset_1(A_1121,B_1119,C_1120) != A_1121
      | ~ m1_subset_1(C_1120,k1_zfmisc_1(k2_zfmisc_1(A_1121,B_1119))) ) ),
    inference(cnfTransformation,[status(thm)],[f_177])).

tff(c_26484,plain,
    ( k1_xboole_0 = '#skF_1'
    | v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | k1_relset_1('#skF_2','#skF_1',k2_funct_1('#skF_3')) != '#skF_2' ),
    inference(resolution,[status(thm)],[c_23703,c_26471])).

tff(c_26508,plain,
    ( k1_xboole_0 = '#skF_1'
    | v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26298,c_26484])).

tff(c_26509,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_23702,c_26508])).

tff(c_26571,plain,(
    v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26509,c_2])).

tff(c_26573,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_24433,c_26571])).

tff(c_26575,plain,(
    v1_xboole_0('#skF_1') ),
    inference(splitRight,[status(thm)],[c_24425])).

tff(c_26947,plain,(
    ! [A_1139] :
      ( v1_xboole_0(k6_partfun1(A_1139))
      | ~ v1_xboole_0(A_1139) ) ),
    inference(resolution,[status(thm)],[c_84,c_24400])).

tff(c_6,plain,(
    ! [B_5,A_4] :
      ( ~ v1_xboole_0(B_5)
      | B_5 = A_4
      | ~ v1_xboole_0(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_26582,plain,(
    ! [A_4] :
      ( A_4 = '#skF_1'
      | ~ v1_xboole_0(A_4) ) ),
    inference(resolution,[status(thm)],[c_26575,c_6])).

tff(c_27017,plain,(
    ! [A_1144] :
      ( k6_partfun1(A_1144) = '#skF_1'
      | ~ v1_xboole_0(A_1144) ) ),
    inference(resolution,[status(thm)],[c_26947,c_26582])).

tff(c_27025,plain,(
    k6_partfun1('#skF_1') = '#skF_1' ),
    inference(resolution,[status(thm)],[c_26575,c_27017])).

tff(c_44,plain,(
    ! [A_24] : v1_funct_1(k6_relat_1(A_24)) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_105,plain,(
    ! [A_24] : v1_funct_1(k6_partfun1(A_24)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_44])).

tff(c_26644,plain,(
    ! [A_1126] :
      ( v1_funct_2(A_1126,k1_relat_1(A_1126),k2_relat_1(A_1126))
      | ~ v1_funct_1(A_1126)
      | ~ v1_relat_1(A_1126) ) ),
    inference(cnfTransformation,[status(thm)],[f_193])).

tff(c_26653,plain,(
    ! [A_22] :
      ( v1_funct_2(k6_partfun1(A_22),k1_relat_1(k6_partfun1(A_22)),A_22)
      | ~ v1_funct_1(k6_partfun1(A_22))
      | ~ v1_relat_1(k6_partfun1(A_22)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_107,c_26644])).

tff(c_26657,plain,(
    ! [A_22] : v1_funct_2(k6_partfun1(A_22),A_22,A_22) ),
    inference(demodulation,[status(thm),theory(equality)],[c_106,c_105,c_108,c_26653])).

tff(c_27064,plain,(
    v1_funct_2('#skF_1','#skF_1','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_27025,c_26657])).

tff(c_26581,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_26575,c_174])).

tff(c_14,plain,(
    ! [A_8] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_8)) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_70,plain,(
    ! [A_49] :
      ( v1_funct_2(k1_xboole_0,A_49,k1_xboole_0)
      | k1_xboole_0 = A_49
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(A_49,k1_xboole_0))) ) ),
    inference(cnfTransformation,[status(thm)],[f_177])).

tff(c_110,plain,(
    ! [A_49] :
      ( v1_funct_2(k1_xboole_0,A_49,k1_xboole_0)
      | k1_xboole_0 = A_49 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_70])).

tff(c_27743,plain,(
    ! [A_1177] :
      ( v1_funct_2('#skF_1',A_1177,'#skF_1')
      | A_1177 = '#skF_1' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26581,c_26581,c_26581,c_110])).

tff(c_26574,plain,(
    v1_xboole_0(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_24425])).

tff(c_26658,plain,(
    ! [A_1127] :
      ( A_1127 = '#skF_1'
      | ~ v1_xboole_0(A_1127) ) ),
    inference(resolution,[status(thm)],[c_26575,c_6])).

tff(c_26665,plain,(
    k2_funct_1('#skF_3') = '#skF_1' ),
    inference(resolution,[status(thm)],[c_26574,c_26658])).

tff(c_26677,plain,(
    ~ v1_funct_2('#skF_1','#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26665,c_23702])).

tff(c_27760,plain,(
    '#skF_2' = '#skF_1' ),
    inference(resolution,[status(thm)],[c_27743,c_26677])).

tff(c_27764,plain,(
    ~ v1_funct_2('#skF_1','#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_27760,c_26677])).

tff(c_27770,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_27064,c_27764])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n018.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 11:52:26 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 12.38/4.61  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 12.38/4.64  
% 12.38/4.64  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 12.38/4.64  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r2_hidden > r1_tarski > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k7_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 12.38/4.64  
% 12.38/4.64  %Foreground sorts:
% 12.38/4.64  
% 12.38/4.64  
% 12.38/4.64  %Background operators:
% 12.38/4.64  
% 12.38/4.64  
% 12.38/4.64  %Foreground operators:
% 12.38/4.64  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 12.38/4.64  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 12.38/4.64  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 12.38/4.64  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 12.38/4.64  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 12.38/4.64  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 12.38/4.64  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 12.38/4.64  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 12.38/4.64  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 12.38/4.64  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 12.38/4.64  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 12.38/4.64  tff('#skF_2', type, '#skF_2': $i).
% 12.38/4.64  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 12.38/4.64  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 12.38/4.64  tff('#skF_3', type, '#skF_3': $i).
% 12.38/4.64  tff('#skF_1', type, '#skF_1': $i).
% 12.38/4.64  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 12.38/4.64  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 12.38/4.64  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 12.38/4.64  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 12.38/4.64  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 12.38/4.64  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 12.38/4.64  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 12.38/4.64  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 12.38/4.64  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 12.38/4.64  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 12.38/4.64  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 12.38/4.64  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 12.38/4.64  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 12.38/4.64  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 12.38/4.64  
% 12.51/4.67  tff(f_52, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 12.51/4.67  tff(f_210, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((v2_funct_1(C) & (k2_relset_1(A, B, C) = B)) => ((v1_funct_1(k2_funct_1(C)) & v1_funct_2(k2_funct_1(C), B, A)) & m1_subset_1(k2_funct_1(C), k1_zfmisc_1(k2_zfmisc_1(B, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_funct_2)).
% 12.51/4.67  tff(f_141, axiom, (![A, B]: (v1_xboole_0(A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => v1_xboole_0(C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc4_relset_1)).
% 12.51/4.67  tff(f_94, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 12.51/4.67  tff(f_128, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 12.51/4.67  tff(f_149, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 12.51/4.67  tff(f_124, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k2_relat_1(A) = k1_relat_1(k2_funct_1(A))) & (k1_relat_1(A) = k2_relat_1(k2_funct_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_funct_1)).
% 12.51/4.67  tff(f_68, axiom, (![A]: (v1_relat_1(A) => (k9_relat_1(A, k1_relat_1(A)) = k2_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t146_relat_1)).
% 12.51/4.67  tff(f_145, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 12.51/4.67  tff(f_177, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 12.51/4.67  tff(f_76, axiom, (![A]: (v1_relat_1(A) => (k10_relat_1(A, k2_relat_1(A)) = k1_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t169_relat_1)).
% 12.51/4.67  tff(f_114, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (v2_funct_1(B) => (k10_relat_1(B, A) = k9_relat_1(k2_funct_1(B), A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t155_funct_1)).
% 12.51/4.67  tff(f_134, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 12.51/4.67  tff(f_82, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t209_relat_1)).
% 12.51/4.67  tff(f_72, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_relat_1)).
% 12.51/4.67  tff(f_106, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (v2_funct_1(B) => (k9_relat_1(B, A) = k10_relat_1(k2_funct_1(B), A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t154_funct_1)).
% 12.51/4.67  tff(f_193, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => ((v1_funct_1(A) & v1_funct_2(A, k1_relat_1(A), k2_relat_1(A))) & m1_subset_1(A, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_funct_2)).
% 12.51/4.67  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 12.51/4.67  tff(f_40, axiom, (![A, B]: ~((v1_xboole_0(A) & ~(A = B)) & v1_xboole_0(B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_boole)).
% 12.51/4.67  tff(f_46, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 12.51/4.67  tff(f_181, axiom, (![A]: (v1_partfun1(k6_partfun1(A), A) & m1_subset_1(k6_partfun1(A), k1_zfmisc_1(k2_zfmisc_1(A, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_partfun1)).
% 12.51/4.67  tff(f_183, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 12.51/4.67  tff(f_86, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 12.51/4.67  tff(f_98, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v1_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc3_funct_1)).
% 12.51/4.67  tff(f_48, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 12.51/4.67  tff(c_18, plain, (![A_9, B_10]: (m1_subset_1(A_9, k1_zfmisc_1(B_10)) | ~r1_tarski(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_52])).
% 12.51/4.67  tff(c_100, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_210])).
% 12.51/4.67  tff(c_1174, plain, (![C_174, B_175, A_176]: (v1_xboole_0(C_174) | ~m1_subset_1(C_174, k1_zfmisc_1(k2_zfmisc_1(B_175, A_176))) | ~v1_xboole_0(A_176))), inference(cnfTransformation, [status(thm)], [f_141])).
% 12.51/4.67  tff(c_1197, plain, (v1_xboole_0('#skF_3') | ~v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_100, c_1174])).
% 12.51/4.67  tff(c_1202, plain, (~v1_xboole_0('#skF_2')), inference(splitLeft, [status(thm)], [c_1197])).
% 12.51/4.67  tff(c_104, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_210])).
% 12.51/4.67  tff(c_184, plain, (![A_69]: (v1_funct_1(k2_funct_1(A_69)) | ~v1_funct_1(A_69) | ~v1_relat_1(A_69))), inference(cnfTransformation, [status(thm)], [f_94])).
% 12.51/4.67  tff(c_94, plain, (~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | ~v1_funct_1(k2_funct_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_210])).
% 12.51/4.67  tff(c_183, plain, (~v1_funct_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_94])).
% 12.51/4.67  tff(c_187, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_184, c_183])).
% 12.51/4.67  tff(c_190, plain, (~v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_104, c_187])).
% 12.51/4.67  tff(c_258, plain, (![C_79, A_80, B_81]: (v1_relat_1(C_79) | ~m1_subset_1(C_79, k1_zfmisc_1(k2_zfmisc_1(A_80, B_81))))), inference(cnfTransformation, [status(thm)], [f_128])).
% 12.51/4.67  tff(c_268, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_100, c_258])).
% 12.51/4.67  tff(c_283, plain, $false, inference(negUnitSimplification, [status(thm)], [c_190, c_268])).
% 12.51/4.67  tff(c_284, plain, (~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | ~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(splitRight, [status(thm)], [c_94])).
% 12.51/4.67  tff(c_296, plain, (~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(splitLeft, [status(thm)], [c_284])).
% 12.51/4.67  tff(c_323, plain, (~r1_tarski(k2_funct_1('#skF_3'), k2_zfmisc_1('#skF_2', '#skF_1'))), inference(resolution, [status(thm)], [c_18, c_296])).
% 12.51/4.67  tff(c_336, plain, (![C_90, A_91, B_92]: (v1_relat_1(C_90) | ~m1_subset_1(C_90, k1_zfmisc_1(k2_zfmisc_1(A_91, B_92))))), inference(cnfTransformation, [status(thm)], [f_128])).
% 12.51/4.67  tff(c_358, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_100, c_336])).
% 12.51/4.67  tff(c_40, plain, (![A_23]: (v1_relat_1(k2_funct_1(A_23)) | ~v1_funct_1(A_23) | ~v1_relat_1(A_23))), inference(cnfTransformation, [status(thm)], [f_94])).
% 12.51/4.67  tff(c_98, plain, (v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_210])).
% 12.51/4.67  tff(c_96, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_2'), inference(cnfTransformation, [status(thm)], [f_210])).
% 12.51/4.67  tff(c_2464, plain, (![A_245, B_246, C_247]: (k2_relset_1(A_245, B_246, C_247)=k2_relat_1(C_247) | ~m1_subset_1(C_247, k1_zfmisc_1(k2_zfmisc_1(A_245, B_246))))), inference(cnfTransformation, [status(thm)], [f_149])).
% 12.51/4.67  tff(c_2477, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_100, c_2464])).
% 12.51/4.67  tff(c_2493, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_96, c_2477])).
% 12.51/4.67  tff(c_1835, plain, (![A_207]: (k1_relat_1(k2_funct_1(A_207))=k2_relat_1(A_207) | ~v2_funct_1(A_207) | ~v1_funct_1(A_207) | ~v1_relat_1(A_207))), inference(cnfTransformation, [status(thm)], [f_124])).
% 12.51/4.67  tff(c_26, plain, (![A_16]: (k9_relat_1(A_16, k1_relat_1(A_16))=k2_relat_1(A_16) | ~v1_relat_1(A_16))), inference(cnfTransformation, [status(thm)], [f_68])).
% 12.51/4.67  tff(c_15246, plain, (![A_595]: (k9_relat_1(k2_funct_1(A_595), k2_relat_1(A_595))=k2_relat_1(k2_funct_1(A_595)) | ~v1_relat_1(k2_funct_1(A_595)) | ~v2_funct_1(A_595) | ~v1_funct_1(A_595) | ~v1_relat_1(A_595))), inference(superposition, [status(thm), theory('equality')], [c_1835, c_26])).
% 12.51/4.67  tff(c_15271, plain, (k9_relat_1(k2_funct_1('#skF_3'), '#skF_2')=k2_relat_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_2493, c_15246])).
% 12.51/4.67  tff(c_15293, plain, (k9_relat_1(k2_funct_1('#skF_3'), '#skF_2')=k2_relat_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_358, c_104, c_98, c_15271])).
% 12.51/4.67  tff(c_15298, plain, (~v1_relat_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_15293])).
% 12.51/4.67  tff(c_15301, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_40, c_15298])).
% 12.51/4.67  tff(c_15305, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_358, c_104, c_15301])).
% 12.51/4.67  tff(c_15307, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_15293])).
% 12.51/4.67  tff(c_285, plain, (v1_funct_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_94])).
% 12.51/4.67  tff(c_102, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_210])).
% 12.51/4.67  tff(c_2615, plain, (![A_251, B_252, C_253]: (k1_relset_1(A_251, B_252, C_253)=k1_relat_1(C_253) | ~m1_subset_1(C_253, k1_zfmisc_1(k2_zfmisc_1(A_251, B_252))))), inference(cnfTransformation, [status(thm)], [f_145])).
% 12.51/4.67  tff(c_2647, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_100, c_2615])).
% 12.51/4.67  tff(c_4498, plain, (![B_333, A_334, C_335]: (k1_xboole_0=B_333 | k1_relset_1(A_334, B_333, C_335)=A_334 | ~v1_funct_2(C_335, A_334, B_333) | ~m1_subset_1(C_335, k1_zfmisc_1(k2_zfmisc_1(A_334, B_333))))), inference(cnfTransformation, [status(thm)], [f_177])).
% 12.51/4.67  tff(c_4517, plain, (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_1' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_100, c_4498])).
% 12.51/4.67  tff(c_4538, plain, (k1_xboole_0='#skF_2' | k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_102, c_2647, c_4517])).
% 12.51/4.67  tff(c_4542, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(splitLeft, [status(thm)], [c_4538])).
% 12.51/4.67  tff(c_30, plain, (![A_19]: (k10_relat_1(A_19, k2_relat_1(A_19))=k1_relat_1(A_19) | ~v1_relat_1(A_19))), inference(cnfTransformation, [status(thm)], [f_76])).
% 12.51/4.67  tff(c_2509, plain, (k10_relat_1('#skF_3', '#skF_2')=k1_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_2493, c_30])).
% 12.51/4.67  tff(c_2519, plain, (k10_relat_1('#skF_3', '#skF_2')=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_358, c_2509])).
% 12.51/4.67  tff(c_4553, plain, (k10_relat_1('#skF_3', '#skF_2')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_4542, c_2519])).
% 12.51/4.67  tff(c_15306, plain, (k9_relat_1(k2_funct_1('#skF_3'), '#skF_2')=k2_relat_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_15293])).
% 12.51/4.67  tff(c_48, plain, (![B_28, A_27]: (k9_relat_1(k2_funct_1(B_28), A_27)=k10_relat_1(B_28, A_27) | ~v2_funct_1(B_28) | ~v1_funct_1(B_28) | ~v1_relat_1(B_28))), inference(cnfTransformation, [status(thm)], [f_114])).
% 12.51/4.67  tff(c_15311, plain, (k2_relat_1(k2_funct_1('#skF_3'))=k10_relat_1('#skF_3', '#skF_2') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_15306, c_48])).
% 12.51/4.67  tff(c_15318, plain, (k2_relat_1(k2_funct_1('#skF_3'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_358, c_104, c_98, c_4553, c_15311])).
% 12.51/4.67  tff(c_608, plain, (![C_123, A_124, B_125]: (v4_relat_1(C_123, A_124) | ~m1_subset_1(C_123, k1_zfmisc_1(k2_zfmisc_1(A_124, B_125))))), inference(cnfTransformation, [status(thm)], [f_134])).
% 12.51/4.67  tff(c_631, plain, (v4_relat_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_100, c_608])).
% 12.51/4.67  tff(c_847, plain, (![B_151, A_152]: (k7_relat_1(B_151, A_152)=B_151 | ~v4_relat_1(B_151, A_152) | ~v1_relat_1(B_151))), inference(cnfTransformation, [status(thm)], [f_82])).
% 12.51/4.67  tff(c_862, plain, (k7_relat_1('#skF_3', '#skF_1')='#skF_3' | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_631, c_847])).
% 12.51/4.67  tff(c_875, plain, (k7_relat_1('#skF_3', '#skF_1')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_358, c_862])).
% 12.51/4.67  tff(c_28, plain, (![B_18, A_17]: (k2_relat_1(k7_relat_1(B_18, A_17))=k9_relat_1(B_18, A_17) | ~v1_relat_1(B_18))), inference(cnfTransformation, [status(thm)], [f_72])).
% 12.51/4.67  tff(c_892, plain, (k9_relat_1('#skF_3', '#skF_1')=k2_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_875, c_28])).
% 12.51/4.67  tff(c_896, plain, (k9_relat_1('#skF_3', '#skF_1')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_358, c_892])).
% 12.51/4.67  tff(c_2496, plain, (k9_relat_1('#skF_3', '#skF_1')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_2493, c_896])).
% 12.51/4.67  tff(c_2898, plain, (![B_271, A_272]: (k10_relat_1(k2_funct_1(B_271), A_272)=k9_relat_1(B_271, A_272) | ~v2_funct_1(B_271) | ~v1_funct_1(B_271) | ~v1_relat_1(B_271))), inference(cnfTransformation, [status(thm)], [f_106])).
% 12.51/4.67  tff(c_15394, plain, (![B_596]: (k9_relat_1(B_596, k2_relat_1(k2_funct_1(B_596)))=k1_relat_1(k2_funct_1(B_596)) | ~v1_relat_1(k2_funct_1(B_596)) | ~v2_funct_1(B_596) | ~v1_funct_1(B_596) | ~v1_relat_1(B_596))), inference(superposition, [status(thm), theory('equality')], [c_2898, c_30])).
% 12.51/4.67  tff(c_15423, plain, (k1_relat_1(k2_funct_1('#skF_3'))=k9_relat_1('#skF_3', '#skF_1') | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_15318, c_15394])).
% 12.51/4.67  tff(c_15458, plain, (k1_relat_1(k2_funct_1('#skF_3'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_358, c_104, c_98, c_15307, c_2496, c_15423])).
% 12.51/4.67  tff(c_1975, plain, (![A_223]: (m1_subset_1(A_223, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_223), k2_relat_1(A_223)))) | ~v1_funct_1(A_223) | ~v1_relat_1(A_223))), inference(cnfTransformation, [status(thm)], [f_193])).
% 12.51/4.67  tff(c_16, plain, (![A_9, B_10]: (r1_tarski(A_9, B_10) | ~m1_subset_1(A_9, k1_zfmisc_1(B_10)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 12.51/4.67  tff(c_2019, plain, (![A_223]: (r1_tarski(A_223, k2_zfmisc_1(k1_relat_1(A_223), k2_relat_1(A_223))) | ~v1_funct_1(A_223) | ~v1_relat_1(A_223))), inference(resolution, [status(thm)], [c_1975, c_16])).
% 12.51/4.67  tff(c_15517, plain, (r1_tarski(k2_funct_1('#skF_3'), k2_zfmisc_1('#skF_2', k2_relat_1(k2_funct_1('#skF_3')))) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_15458, c_2019])).
% 12.51/4.67  tff(c_15597, plain, (r1_tarski(k2_funct_1('#skF_3'), k2_zfmisc_1('#skF_2', '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_15307, c_285, c_15318, c_15517])).
% 12.51/4.67  tff(c_15599, plain, $false, inference(negUnitSimplification, [status(thm)], [c_323, c_15597])).
% 12.51/4.67  tff(c_15600, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_4538])).
% 12.51/4.67  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 12.51/4.67  tff(c_15662, plain, (v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_15600, c_2])).
% 12.51/4.67  tff(c_15664, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1202, c_15662])).
% 12.51/4.67  tff(c_15665, plain, (v1_xboole_0('#skF_3')), inference(splitRight, [status(thm)], [c_1197])).
% 12.51/4.67  tff(c_171, plain, (![B_64, A_65]: (~v1_xboole_0(B_64) | B_64=A_65 | ~v1_xboole_0(A_65))), inference(cnfTransformation, [status(thm)], [f_40])).
% 12.51/4.67  tff(c_174, plain, (![A_65]: (k1_xboole_0=A_65 | ~v1_xboole_0(A_65))), inference(resolution, [status(thm)], [c_2, c_171])).
% 12.51/4.67  tff(c_15672, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_15665, c_174])).
% 12.51/4.67  tff(c_12, plain, (![B_7]: (k2_zfmisc_1(k1_xboole_0, B_7)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_46])).
% 12.51/4.67  tff(c_15709, plain, (![B_7]: (k2_zfmisc_1('#skF_3', B_7)='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_15672, c_15672, c_12])).
% 12.51/4.67  tff(c_15666, plain, (v1_xboole_0('#skF_2')), inference(splitRight, [status(thm)], [c_1197])).
% 12.51/4.67  tff(c_15679, plain, (k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_15666, c_174])).
% 12.51/4.67  tff(c_15718, plain, ('#skF_2'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_15672, c_15679])).
% 12.51/4.67  tff(c_15726, plain, (~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_15718, c_296])).
% 12.51/4.67  tff(c_16278, plain, (~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_15709, c_15726])).
% 12.51/4.67  tff(c_16282, plain, (~r1_tarski(k2_funct_1('#skF_3'), '#skF_3')), inference(resolution, [status(thm)], [c_18, c_16278])).
% 12.51/4.67  tff(c_84, plain, (![A_52]: (m1_subset_1(k6_partfun1(A_52), k1_zfmisc_1(k2_zfmisc_1(A_52, A_52))))), inference(cnfTransformation, [status(thm)], [f_181])).
% 12.51/4.67  tff(c_15990, plain, (![A_612]: (v1_xboole_0(k6_partfun1(A_612)) | ~v1_xboole_0(A_612))), inference(resolution, [status(thm)], [c_84, c_1174])).
% 12.51/4.67  tff(c_15707, plain, (![A_65]: (A_65='#skF_3' | ~v1_xboole_0(A_65))), inference(demodulation, [status(thm), theory('equality')], [c_15672, c_174])).
% 12.51/4.67  tff(c_16041, plain, (![A_617]: (k6_partfun1(A_617)='#skF_3' | ~v1_xboole_0(A_617))), inference(resolution, [status(thm)], [c_15990, c_15707])).
% 12.51/4.67  tff(c_16049, plain, (k6_partfun1('#skF_3')='#skF_3'), inference(resolution, [status(thm)], [c_15665, c_16041])).
% 12.51/4.67  tff(c_86, plain, (![A_53]: (k6_relat_1(A_53)=k6_partfun1(A_53))), inference(cnfTransformation, [status(thm)], [f_183])).
% 12.51/4.67  tff(c_36, plain, (![A_22]: (k2_relat_1(k6_relat_1(A_22))=A_22)), inference(cnfTransformation, [status(thm)], [f_86])).
% 12.51/4.67  tff(c_107, plain, (![A_22]: (k2_relat_1(k6_partfun1(A_22))=A_22)), inference(demodulation, [status(thm), theory('equality')], [c_86, c_36])).
% 12.51/4.67  tff(c_16100, plain, (k2_relat_1('#skF_3')='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_16049, c_107])).
% 12.51/4.67  tff(c_16126, plain, (![A_618]: (k1_relat_1(k2_funct_1(A_618))=k2_relat_1(A_618) | ~v2_funct_1(A_618) | ~v1_funct_1(A_618) | ~v1_relat_1(A_618))), inference(cnfTransformation, [status(thm)], [f_124])).
% 12.51/4.67  tff(c_23420, plain, (![A_923]: (k9_relat_1(k2_funct_1(A_923), k2_relat_1(A_923))=k2_relat_1(k2_funct_1(A_923)) | ~v1_relat_1(k2_funct_1(A_923)) | ~v2_funct_1(A_923) | ~v1_funct_1(A_923) | ~v1_relat_1(A_923))), inference(superposition, [status(thm), theory('equality')], [c_16126, c_26])).
% 12.51/4.67  tff(c_23442, plain, (k9_relat_1(k2_funct_1('#skF_3'), '#skF_3')=k2_relat_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_16100, c_23420])).
% 12.51/4.67  tff(c_23455, plain, (k9_relat_1(k2_funct_1('#skF_3'), '#skF_3')=k2_relat_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_358, c_104, c_98, c_23442])).
% 12.51/4.67  tff(c_23576, plain, (~v1_relat_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_23455])).
% 12.51/4.67  tff(c_23579, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_40, c_23576])).
% 12.51/4.67  tff(c_23583, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_358, c_104, c_23579])).
% 12.51/4.67  tff(c_23585, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_23455])).
% 12.51/4.67  tff(c_10, plain, (![A_6]: (k2_zfmisc_1(A_6, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_46])).
% 12.51/4.67  tff(c_15710, plain, (![A_6]: (k2_zfmisc_1(A_6, '#skF_3')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_15672, c_15672, c_10])).
% 12.51/4.67  tff(c_42, plain, (![A_24]: (v1_relat_1(k6_relat_1(A_24)))), inference(cnfTransformation, [status(thm)], [f_98])).
% 12.51/4.67  tff(c_106, plain, (![A_24]: (v1_relat_1(k6_partfun1(A_24)))), inference(demodulation, [status(thm), theory('equality')], [c_86, c_42])).
% 12.51/4.67  tff(c_34, plain, (![A_22]: (k1_relat_1(k6_relat_1(A_22))=A_22)), inference(cnfTransformation, [status(thm)], [f_86])).
% 12.51/4.67  tff(c_108, plain, (![A_22]: (k1_relat_1(k6_partfun1(A_22))=A_22)), inference(demodulation, [status(thm), theory('equality')], [c_86, c_34])).
% 12.51/4.67  tff(c_444, plain, (![A_102]: (k10_relat_1(A_102, k2_relat_1(A_102))=k1_relat_1(A_102) | ~v1_relat_1(A_102))), inference(cnfTransformation, [status(thm)], [f_76])).
% 12.51/4.67  tff(c_453, plain, (![A_22]: (k10_relat_1(k6_partfun1(A_22), A_22)=k1_relat_1(k6_partfun1(A_22)) | ~v1_relat_1(k6_partfun1(A_22)))), inference(superposition, [status(thm), theory('equality')], [c_107, c_444])).
% 12.51/4.67  tff(c_457, plain, (![A_22]: (k10_relat_1(k6_partfun1(A_22), A_22)=A_22)), inference(demodulation, [status(thm), theory('equality')], [c_106, c_108, c_453])).
% 12.51/4.67  tff(c_16085, plain, (k10_relat_1('#skF_3', '#skF_3')='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_16049, c_457])).
% 12.51/4.67  tff(c_23584, plain, (k9_relat_1(k2_funct_1('#skF_3'), '#skF_3')=k2_relat_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_23455])).
% 12.51/4.67  tff(c_23637, plain, (k2_relat_1(k2_funct_1('#skF_3'))=k10_relat_1('#skF_3', '#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_23584, c_48])).
% 12.51/4.67  tff(c_23646, plain, (k2_relat_1(k2_funct_1('#skF_3'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_358, c_104, c_98, c_16085, c_23637])).
% 12.51/4.67  tff(c_16458, plain, (![A_645]: (m1_subset_1(A_645, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_645), k2_relat_1(A_645)))) | ~v1_funct_1(A_645) | ~v1_relat_1(A_645))), inference(cnfTransformation, [status(thm)], [f_193])).
% 12.51/4.67  tff(c_16510, plain, (![A_645]: (r1_tarski(A_645, k2_zfmisc_1(k1_relat_1(A_645), k2_relat_1(A_645))) | ~v1_funct_1(A_645) | ~v1_relat_1(A_645))), inference(resolution, [status(thm)], [c_16458, c_16])).
% 12.51/4.67  tff(c_23666, plain, (r1_tarski(k2_funct_1('#skF_3'), k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_3')), '#skF_3')) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_23646, c_16510])).
% 12.51/4.67  tff(c_23699, plain, (r1_tarski(k2_funct_1('#skF_3'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_23585, c_285, c_15710, c_23666])).
% 12.51/4.67  tff(c_23701, plain, $false, inference(negUnitSimplification, [status(thm)], [c_16282, c_23699])).
% 12.51/4.67  tff(c_23703, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(splitRight, [status(thm)], [c_284])).
% 12.51/4.67  tff(c_24400, plain, (![C_1011, B_1012, A_1013]: (v1_xboole_0(C_1011) | ~m1_subset_1(C_1011, k1_zfmisc_1(k2_zfmisc_1(B_1012, A_1013))) | ~v1_xboole_0(A_1013))), inference(cnfTransformation, [status(thm)], [f_141])).
% 12.51/4.67  tff(c_24425, plain, (v1_xboole_0(k2_funct_1('#skF_3')) | ~v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_23703, c_24400])).
% 12.51/4.67  tff(c_24433, plain, (~v1_xboole_0('#skF_1')), inference(splitLeft, [status(thm)], [c_24425])).
% 12.51/4.67  tff(c_23702, plain, (~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_284])).
% 12.51/4.67  tff(c_23754, plain, (![C_939, A_940, B_941]: (v1_relat_1(C_939) | ~m1_subset_1(C_939, k1_zfmisc_1(k2_zfmisc_1(A_940, B_941))))), inference(cnfTransformation, [status(thm)], [f_128])).
% 12.51/4.67  tff(c_23780, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_100, c_23754])).
% 12.51/4.67  tff(c_25368, plain, (![A_1066, B_1067, C_1068]: (k2_relset_1(A_1066, B_1067, C_1068)=k2_relat_1(C_1068) | ~m1_subset_1(C_1068, k1_zfmisc_1(k2_zfmisc_1(A_1066, B_1067))))), inference(cnfTransformation, [status(thm)], [f_149])).
% 12.51/4.67  tff(c_25384, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_100, c_25368])).
% 12.51/4.67  tff(c_25401, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_96, c_25384])).
% 12.51/4.67  tff(c_88, plain, (![A_54]: (m1_subset_1(A_54, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_54), k2_relat_1(A_54)))) | ~v1_funct_1(A_54) | ~v1_relat_1(A_54))), inference(cnfTransformation, [status(thm)], [f_193])).
% 12.51/4.67  tff(c_25411, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), '#skF_2'))) | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_25401, c_88])).
% 12.51/4.67  tff(c_25423, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_23780, c_104, c_25411])).
% 12.51/4.67  tff(c_58, plain, (![C_35, A_33, B_34]: (v4_relat_1(C_35, A_33) | ~m1_subset_1(C_35, k1_zfmisc_1(k2_zfmisc_1(A_33, B_34))))), inference(cnfTransformation, [status(thm)], [f_134])).
% 12.51/4.67  tff(c_25622, plain, (v4_relat_1('#skF_3', k1_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_25423, c_58])).
% 12.51/4.67  tff(c_32, plain, (![B_21, A_20]: (k7_relat_1(B_21, A_20)=B_21 | ~v4_relat_1(B_21, A_20) | ~v1_relat_1(B_21))), inference(cnfTransformation, [status(thm)], [f_82])).
% 12.51/4.67  tff(c_25628, plain, (k7_relat_1('#skF_3', k1_relat_1('#skF_3'))='#skF_3' | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_25622, c_32])).
% 12.51/4.67  tff(c_25631, plain, (k7_relat_1('#skF_3', k1_relat_1('#skF_3'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_23780, c_25628])).
% 12.51/4.67  tff(c_25638, plain, (k9_relat_1('#skF_3', k1_relat_1('#skF_3'))=k2_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_25631, c_28])).
% 12.51/4.67  tff(c_25648, plain, (k9_relat_1('#skF_3', k1_relat_1('#skF_3'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_23780, c_25401, c_25638])).
% 12.51/4.67  tff(c_23777, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_23703, c_23754])).
% 12.51/4.67  tff(c_25417, plain, (k10_relat_1('#skF_3', '#skF_2')=k1_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_25401, c_30])).
% 12.51/4.67  tff(c_25427, plain, (k10_relat_1('#skF_3', '#skF_2')=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_23780, c_25417])).
% 12.51/4.67  tff(c_26070, plain, (![B_1104, A_1105]: (k9_relat_1(k2_funct_1(B_1104), A_1105)=k10_relat_1(B_1104, A_1105) | ~v2_funct_1(B_1104) | ~v1_funct_1(B_1104) | ~v1_relat_1(B_1104))), inference(cnfTransformation, [status(thm)], [f_114])).
% 12.51/4.67  tff(c_23897, plain, (![C_957, A_958, B_959]: (v4_relat_1(C_957, A_958) | ~m1_subset_1(C_957, k1_zfmisc_1(k2_zfmisc_1(A_958, B_959))))), inference(cnfTransformation, [status(thm)], [f_134])).
% 12.51/4.67  tff(c_23922, plain, (v4_relat_1(k2_funct_1('#skF_3'), '#skF_2')), inference(resolution, [status(thm)], [c_23703, c_23897])).
% 12.51/4.67  tff(c_23941, plain, (k7_relat_1(k2_funct_1('#skF_3'), '#skF_2')=k2_funct_1('#skF_3') | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_23922, c_32])).
% 12.51/4.67  tff(c_23944, plain, (k7_relat_1(k2_funct_1('#skF_3'), '#skF_2')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_23777, c_23941])).
% 12.51/4.67  tff(c_24062, plain, (![B_974, A_975]: (k2_relat_1(k7_relat_1(B_974, A_975))=k9_relat_1(B_974, A_975) | ~v1_relat_1(B_974))), inference(cnfTransformation, [status(thm)], [f_72])).
% 12.51/4.67  tff(c_24074, plain, (k9_relat_1(k2_funct_1('#skF_3'), '#skF_2')=k2_relat_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_23944, c_24062])).
% 12.51/4.67  tff(c_24087, plain, (k9_relat_1(k2_funct_1('#skF_3'), '#skF_2')=k2_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_23777, c_24074])).
% 12.51/4.67  tff(c_26076, plain, (k2_relat_1(k2_funct_1('#skF_3'))=k10_relat_1('#skF_3', '#skF_2') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_26070, c_24087])).
% 12.51/4.67  tff(c_26093, plain, (k2_relat_1(k2_funct_1('#skF_3'))=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_23780, c_104, c_98, c_25427, c_26076])).
% 12.51/4.67  tff(c_26114, plain, (k10_relat_1(k2_funct_1('#skF_3'), k1_relat_1('#skF_3'))=k1_relat_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_26093, c_30])).
% 12.51/4.67  tff(c_26130, plain, (k10_relat_1(k2_funct_1('#skF_3'), k1_relat_1('#skF_3'))=k1_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_23777, c_26114])).
% 12.51/4.67  tff(c_46, plain, (![B_26, A_25]: (k10_relat_1(k2_funct_1(B_26), A_25)=k9_relat_1(B_26, A_25) | ~v2_funct_1(B_26) | ~v1_funct_1(B_26) | ~v1_relat_1(B_26))), inference(cnfTransformation, [status(thm)], [f_106])).
% 12.51/4.67  tff(c_26286, plain, (k9_relat_1('#skF_3', k1_relat_1('#skF_3'))=k1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_26130, c_46])).
% 12.51/4.67  tff(c_26293, plain, (k1_relat_1(k2_funct_1('#skF_3'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_23780, c_104, c_98, c_25648, c_26286])).
% 12.51/4.67  tff(c_25500, plain, (![A_1077, B_1078, C_1079]: (k1_relset_1(A_1077, B_1078, C_1079)=k1_relat_1(C_1079) | ~m1_subset_1(C_1079, k1_zfmisc_1(k2_zfmisc_1(A_1077, B_1078))))), inference(cnfTransformation, [status(thm)], [f_145])).
% 12.51/4.67  tff(c_25529, plain, (k1_relset_1('#skF_2', '#skF_1', k2_funct_1('#skF_3'))=k1_relat_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_23703, c_25500])).
% 12.51/4.67  tff(c_26298, plain, (k1_relset_1('#skF_2', '#skF_1', k2_funct_1('#skF_3'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_26293, c_25529])).
% 12.51/4.67  tff(c_26471, plain, (![B_1119, C_1120, A_1121]: (k1_xboole_0=B_1119 | v1_funct_2(C_1120, A_1121, B_1119) | k1_relset_1(A_1121, B_1119, C_1120)!=A_1121 | ~m1_subset_1(C_1120, k1_zfmisc_1(k2_zfmisc_1(A_1121, B_1119))))), inference(cnfTransformation, [status(thm)], [f_177])).
% 12.51/4.67  tff(c_26484, plain, (k1_xboole_0='#skF_1' | v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | k1_relset_1('#skF_2', '#skF_1', k2_funct_1('#skF_3'))!='#skF_2'), inference(resolution, [status(thm)], [c_23703, c_26471])).
% 12.51/4.67  tff(c_26508, plain, (k1_xboole_0='#skF_1' | v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_26298, c_26484])).
% 12.51/4.67  tff(c_26509, plain, (k1_xboole_0='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_23702, c_26508])).
% 12.51/4.67  tff(c_26571, plain, (v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_26509, c_2])).
% 12.51/4.67  tff(c_26573, plain, $false, inference(negUnitSimplification, [status(thm)], [c_24433, c_26571])).
% 12.51/4.67  tff(c_26575, plain, (v1_xboole_0('#skF_1')), inference(splitRight, [status(thm)], [c_24425])).
% 12.51/4.67  tff(c_26947, plain, (![A_1139]: (v1_xboole_0(k6_partfun1(A_1139)) | ~v1_xboole_0(A_1139))), inference(resolution, [status(thm)], [c_84, c_24400])).
% 12.51/4.67  tff(c_6, plain, (![B_5, A_4]: (~v1_xboole_0(B_5) | B_5=A_4 | ~v1_xboole_0(A_4))), inference(cnfTransformation, [status(thm)], [f_40])).
% 12.51/4.67  tff(c_26582, plain, (![A_4]: (A_4='#skF_1' | ~v1_xboole_0(A_4))), inference(resolution, [status(thm)], [c_26575, c_6])).
% 12.51/4.67  tff(c_27017, plain, (![A_1144]: (k6_partfun1(A_1144)='#skF_1' | ~v1_xboole_0(A_1144))), inference(resolution, [status(thm)], [c_26947, c_26582])).
% 12.51/4.67  tff(c_27025, plain, (k6_partfun1('#skF_1')='#skF_1'), inference(resolution, [status(thm)], [c_26575, c_27017])).
% 12.51/4.67  tff(c_44, plain, (![A_24]: (v1_funct_1(k6_relat_1(A_24)))), inference(cnfTransformation, [status(thm)], [f_98])).
% 12.51/4.67  tff(c_105, plain, (![A_24]: (v1_funct_1(k6_partfun1(A_24)))), inference(demodulation, [status(thm), theory('equality')], [c_86, c_44])).
% 12.51/4.67  tff(c_26644, plain, (![A_1126]: (v1_funct_2(A_1126, k1_relat_1(A_1126), k2_relat_1(A_1126)) | ~v1_funct_1(A_1126) | ~v1_relat_1(A_1126))), inference(cnfTransformation, [status(thm)], [f_193])).
% 12.51/4.67  tff(c_26653, plain, (![A_22]: (v1_funct_2(k6_partfun1(A_22), k1_relat_1(k6_partfun1(A_22)), A_22) | ~v1_funct_1(k6_partfun1(A_22)) | ~v1_relat_1(k6_partfun1(A_22)))), inference(superposition, [status(thm), theory('equality')], [c_107, c_26644])).
% 12.51/4.67  tff(c_26657, plain, (![A_22]: (v1_funct_2(k6_partfun1(A_22), A_22, A_22))), inference(demodulation, [status(thm), theory('equality')], [c_106, c_105, c_108, c_26653])).
% 12.51/4.67  tff(c_27064, plain, (v1_funct_2('#skF_1', '#skF_1', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_27025, c_26657])).
% 12.51/4.67  tff(c_26581, plain, (k1_xboole_0='#skF_1'), inference(resolution, [status(thm)], [c_26575, c_174])).
% 12.51/4.67  tff(c_14, plain, (![A_8]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_8)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 12.51/4.67  tff(c_70, plain, (![A_49]: (v1_funct_2(k1_xboole_0, A_49, k1_xboole_0) | k1_xboole_0=A_49 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k2_zfmisc_1(A_49, k1_xboole_0))))), inference(cnfTransformation, [status(thm)], [f_177])).
% 12.51/4.67  tff(c_110, plain, (![A_49]: (v1_funct_2(k1_xboole_0, A_49, k1_xboole_0) | k1_xboole_0=A_49)), inference(demodulation, [status(thm), theory('equality')], [c_14, c_70])).
% 12.51/4.67  tff(c_27743, plain, (![A_1177]: (v1_funct_2('#skF_1', A_1177, '#skF_1') | A_1177='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_26581, c_26581, c_26581, c_110])).
% 12.51/4.67  tff(c_26574, plain, (v1_xboole_0(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_24425])).
% 12.51/4.67  tff(c_26658, plain, (![A_1127]: (A_1127='#skF_1' | ~v1_xboole_0(A_1127))), inference(resolution, [status(thm)], [c_26575, c_6])).
% 12.51/4.67  tff(c_26665, plain, (k2_funct_1('#skF_3')='#skF_1'), inference(resolution, [status(thm)], [c_26574, c_26658])).
% 12.51/4.67  tff(c_26677, plain, (~v1_funct_2('#skF_1', '#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_26665, c_23702])).
% 12.51/4.67  tff(c_27760, plain, ('#skF_2'='#skF_1'), inference(resolution, [status(thm)], [c_27743, c_26677])).
% 12.51/4.67  tff(c_27764, plain, (~v1_funct_2('#skF_1', '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_27760, c_26677])).
% 12.51/4.67  tff(c_27770, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_27064, c_27764])).
% 12.51/4.67  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 12.51/4.67  
% 12.51/4.67  Inference rules
% 12.51/4.67  ----------------------
% 12.51/4.67  #Ref     : 0
% 12.51/4.67  #Sup     : 6206
% 12.51/4.67  #Fact    : 0
% 12.51/4.67  #Define  : 0
% 12.51/4.67  #Split   : 20
% 12.51/4.67  #Chain   : 0
% 12.51/4.67  #Close   : 0
% 12.51/4.67  
% 12.51/4.67  Ordering : KBO
% 12.51/4.67  
% 12.51/4.67  Simplification rules
% 12.51/4.67  ----------------------
% 12.51/4.67  #Subsume      : 1704
% 12.51/4.67  #Demod        : 6662
% 12.51/4.67  #Tautology    : 2962
% 12.51/4.67  #SimpNegUnit  : 17
% 12.51/4.67  #BackRed      : 395
% 12.51/4.67  
% 12.51/4.67  #Partial instantiations: 0
% 12.51/4.67  #Strategies tried      : 1
% 12.51/4.67  
% 12.51/4.67  Timing (in seconds)
% 12.51/4.67  ----------------------
% 12.51/4.67  Preprocessing        : 0.44
% 12.51/4.67  Parsing              : 0.22
% 12.51/4.67  CNF conversion       : 0.03
% 12.51/4.67  Main loop            : 3.38
% 12.51/4.67  Inferencing          : 0.92
% 12.51/4.67  Reduction            : 1.26
% 12.51/4.67  Demodulation         : 0.94
% 12.51/4.67  BG Simplification    : 0.09
% 12.51/4.67  Subsumption          : 0.87
% 12.51/4.67  Abstraction          : 0.13
% 12.51/4.67  MUC search           : 0.00
% 12.51/4.67  Cooper               : 0.00
% 12.51/4.67  Total                : 3.90
% 12.51/4.67  Index Insertion      : 0.00
% 12.51/4.67  Index Deletion       : 0.00
% 12.51/4.67  Index Matching       : 0.00
% 12.51/4.67  BG Taut test         : 0.00
%------------------------------------------------------------------------------
