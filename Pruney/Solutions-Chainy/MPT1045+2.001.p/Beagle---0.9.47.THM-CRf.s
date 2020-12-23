%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:17:05 EST 2020

% Result     : Theorem 4.18s
% Output     : CNFRefutation 4.50s
% Verified   : 
% Statistics : Number of formulae       :  140 ( 435 expanded)
%              Number of leaves         :   55 ( 158 expanded)
%              Depth                    :   11
%              Number of atoms          :  191 ( 939 expanded)
%              Number of equality atoms :   70 ( 419 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v1_partfun1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k5_partfun1 > k3_partfun1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

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

tff(v1_partfun1,type,(
    v1_partfun1: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(k5_partfun1,type,(
    k5_partfun1: ( $i * $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_155,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( ( B = k1_xboole_0
           => A = k1_xboole_0 )
         => k5_partfun1(A,B,k3_partfun1(C,A,B)) = k1_tarski(C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t161_funct_2)).

tff(f_142,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => k3_partfun1(C,A,B) = C ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_partfun1)).

tff(f_124,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( v1_partfun1(C,A)
      <=> k5_partfun1(A,B,C) = k1_tarski(C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t174_partfun1)).

tff(f_116,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => ( ( v1_funct_1(C)
              & v1_funct_2(C,A,B) )
           => ( v1_funct_1(C)
              & v1_partfun1(C,A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc5_funct_2)).

tff(f_30,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_77,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_102,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_98,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_funct_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_funct_1)).

tff(f_40,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_94,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_136,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r1_tarski(k2_relat_1(B),A)
       => ( v1_funct_1(B)
          & v1_funct_2(B,k1_relat_1(B),A)
          & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B),A))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_funct_2)).

tff(f_70,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_85,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_36,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_48,axiom,(
    ! [A,B] :
      ~ ( v1_xboole_0(A)
        & A != B
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_boole)).

tff(f_50,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_79,axiom,(
    ! [A] : k1_setfam_1(k1_tarski(A)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_setfam_1)).

tff(f_52,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_81,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

tff(f_38,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_75,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
    <=> A != B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_zfmisc_1)).

tff(c_88,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_84,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_405,plain,(
    ! [C_131,A_132,B_133] :
      ( k3_partfun1(C_131,A_132,B_133) = C_131
      | ~ m1_subset_1(C_131,k1_zfmisc_1(k2_zfmisc_1(A_132,B_133)))
      | ~ v1_funct_1(C_131) ) ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_412,plain,
    ( k3_partfun1('#skF_3','#skF_1','#skF_2') = '#skF_3'
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_84,c_405])).

tff(c_426,plain,(
    k3_partfun1('#skF_3','#skF_1','#skF_2') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_412])).

tff(c_80,plain,(
    k5_partfun1('#skF_1','#skF_2',k3_partfun1('#skF_3','#skF_1','#skF_2')) != k1_tarski('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_430,plain,(
    k5_partfun1('#skF_1','#skF_2','#skF_3') != k1_tarski('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_426,c_80])).

tff(c_699,plain,(
    ! [A_177,B_178,C_179] :
      ( k5_partfun1(A_177,B_178,C_179) = k1_tarski(C_179)
      | ~ v1_partfun1(C_179,A_177)
      | ~ m1_subset_1(C_179,k1_zfmisc_1(k2_zfmisc_1(A_177,B_178)))
      | ~ v1_funct_1(C_179) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_709,plain,
    ( k5_partfun1('#skF_1','#skF_2','#skF_3') = k1_tarski('#skF_3')
    | ~ v1_partfun1('#skF_3','#skF_1')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_84,c_699])).

tff(c_724,plain,
    ( k5_partfun1('#skF_1','#skF_2','#skF_3') = k1_tarski('#skF_3')
    | ~ v1_partfun1('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_709])).

tff(c_725,plain,(
    ~ v1_partfun1('#skF_3','#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_430,c_724])).

tff(c_82,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_105,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_82])).

tff(c_86,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_653,plain,(
    ! [C_174,A_175,B_176] :
      ( v1_partfun1(C_174,A_175)
      | ~ v1_funct_2(C_174,A_175,B_176)
      | ~ v1_funct_1(C_174)
      | ~ m1_subset_1(C_174,k1_zfmisc_1(k2_zfmisc_1(A_175,B_176)))
      | v1_xboole_0(B_176) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_663,plain,
    ( v1_partfun1('#skF_3','#skF_1')
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3')
    | v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_84,c_653])).

tff(c_678,plain,
    ( v1_partfun1('#skF_3','#skF_1')
    | v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_86,c_663])).

tff(c_683,plain,(
    v1_xboole_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_678])).

tff(c_4,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_688,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_683,c_4])).

tff(c_696,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_105,c_688])).

tff(c_697,plain,(
    v1_partfun1('#skF_3','#skF_1') ),
    inference(splitRight,[status(thm)],[c_678])).

tff(c_729,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_725,c_697])).

tff(c_730,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_82])).

tff(c_44,plain,(
    ! [A_42] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_42)) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_771,plain,(
    ! [A_42] : m1_subset_1('#skF_1',k1_zfmisc_1(A_42)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_730,c_44])).

tff(c_874,plain,(
    ! [C_200,A_201,B_202] :
      ( v1_relat_1(C_200)
      | ~ m1_subset_1(C_200,k1_zfmisc_1(k2_zfmisc_1(A_201,B_202))) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_888,plain,(
    v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_771,c_874])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_100,plain,(
    ! [A_69] :
      ( v1_funct_1(A_69)
      | ~ v1_xboole_0(A_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_104,plain,(
    v1_funct_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_2,c_100])).

tff(c_732,plain,(
    v1_funct_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_730,c_104])).

tff(c_14,plain,(
    ! [A_6] : r1_tarski(k1_xboole_0,A_6) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_735,plain,(
    ! [A_6] : r1_tarski('#skF_1',A_6) ),
    inference(demodulation,[status(thm),theory(equality)],[c_730,c_14])).

tff(c_56,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_733,plain,(
    k2_relat_1('#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_730,c_730,c_56])).

tff(c_58,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_734,plain,(
    k1_relat_1('#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_730,c_730,c_58])).

tff(c_1174,plain,(
    ! [B_257,A_258] :
      ( v1_funct_2(B_257,k1_relat_1(B_257),A_258)
      | ~ r1_tarski(k2_relat_1(B_257),A_258)
      | ~ v1_funct_1(B_257)
      | ~ v1_relat_1(B_257) ) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_1177,plain,(
    ! [A_258] :
      ( v1_funct_2('#skF_1','#skF_1',A_258)
      | ~ r1_tarski(k2_relat_1('#skF_1'),A_258)
      | ~ v1_funct_1('#skF_1')
      | ~ v1_relat_1('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_734,c_1174])).

tff(c_1179,plain,(
    ! [A_258] : v1_funct_2('#skF_1','#skF_1',A_258) ),
    inference(demodulation,[status(thm),theory(equality)],[c_888,c_732,c_735,c_733,c_1177])).

tff(c_1304,plain,(
    ! [C_277,A_278,B_279] :
      ( v1_partfun1(C_277,A_278)
      | ~ v1_funct_2(C_277,A_278,B_279)
      | ~ v1_funct_1(C_277)
      | ~ m1_subset_1(C_277,k1_zfmisc_1(k2_zfmisc_1(A_278,B_279)))
      | v1_xboole_0(B_279) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_1321,plain,(
    ! [A_278,B_279] :
      ( v1_partfun1('#skF_1',A_278)
      | ~ v1_funct_2('#skF_1',A_278,B_279)
      | ~ v1_funct_1('#skF_1')
      | v1_xboole_0(B_279) ) ),
    inference(resolution,[status(thm)],[c_771,c_1304])).

tff(c_1328,plain,(
    ! [A_280,B_281] :
      ( v1_partfun1('#skF_1',A_280)
      | ~ v1_funct_2('#skF_1',A_280,B_281)
      | v1_xboole_0(B_281) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_732,c_1321])).

tff(c_1336,plain,(
    ! [A_258] :
      ( v1_partfun1('#skF_1','#skF_1')
      | v1_xboole_0(A_258) ) ),
    inference(resolution,[status(thm)],[c_1179,c_1328])).

tff(c_1340,plain,(
    v1_partfun1('#skF_1','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_1336])).

tff(c_1449,plain,(
    ! [A_312,B_313,C_314] :
      ( k5_partfun1(A_312,B_313,C_314) = k1_tarski(C_314)
      | ~ v1_partfun1(C_314,A_312)
      | ~ m1_subset_1(C_314,k1_zfmisc_1(k2_zfmisc_1(A_312,B_313)))
      | ~ v1_funct_1(C_314) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_1466,plain,(
    ! [A_312,B_313] :
      ( k5_partfun1(A_312,B_313,'#skF_1') = k1_tarski('#skF_1')
      | ~ v1_partfun1('#skF_1',A_312)
      | ~ v1_funct_1('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_771,c_1449])).

tff(c_1472,plain,(
    ! [A_315,B_316] :
      ( k5_partfun1(A_315,B_316,'#skF_1') = k1_tarski('#skF_1')
      | ~ v1_partfun1('#skF_1',A_315) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_732,c_1466])).

tff(c_1481,plain,(
    ! [B_316] : k5_partfun1('#skF_1',B_316,'#skF_1') = k1_tarski('#skF_1') ),
    inference(resolution,[status(thm)],[c_1340,c_1472])).

tff(c_1071,plain,(
    ! [C_236,A_237,B_238] :
      ( k3_partfun1(C_236,A_237,B_238) = C_236
      | ~ m1_subset_1(C_236,k1_zfmisc_1(k2_zfmisc_1(A_237,B_238)))
      | ~ v1_funct_1(C_236) ) ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_1085,plain,(
    ! [A_237,B_238] :
      ( k3_partfun1('#skF_1',A_237,B_238) = '#skF_1'
      | ~ v1_funct_1('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_771,c_1071])).

tff(c_1089,plain,(
    ! [A_237,B_238] : k3_partfun1('#skF_1',A_237,B_238) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_732,c_1085])).

tff(c_38,plain,(
    ! [B_39] : k2_zfmisc_1(k1_xboole_0,B_39) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_780,plain,(
    ! [B_39] : k2_zfmisc_1('#skF_1',B_39) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_730,c_730,c_38])).

tff(c_731,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_82])).

tff(c_741,plain,(
    '#skF_2' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_730,c_731])).

tff(c_770,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_741,c_84])).

tff(c_781,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_780,c_770])).

tff(c_851,plain,(
    ! [A_196,B_197] :
      ( r1_tarski(A_196,B_197)
      | ~ m1_subset_1(A_196,k1_zfmisc_1(B_197)) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_862,plain,(
    r1_tarski('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_781,c_851])).

tff(c_980,plain,(
    ! [B_216,A_217] :
      ( B_216 = A_217
      | ~ r1_tarski(B_216,A_217)
      | ~ r1_tarski(A_217,B_216) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_982,plain,
    ( '#skF_3' = '#skF_1'
    | ~ r1_tarski('#skF_1','#skF_3') ),
    inference(resolution,[status(thm)],[c_862,c_980])).

tff(c_989,plain,(
    '#skF_3' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_735,c_982])).

tff(c_826,plain,(
    k5_partfun1('#skF_1','#skF_1',k3_partfun1('#skF_3','#skF_1','#skF_1')) != k1_tarski('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_741,c_741,c_80])).

tff(c_997,plain,(
    k5_partfun1('#skF_1','#skF_1',k3_partfun1('#skF_1','#skF_1','#skF_1')) != k1_tarski('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_989,c_989,c_826])).

tff(c_1090,plain,(
    k5_partfun1('#skF_1','#skF_1','#skF_1') != k1_tarski('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1089,c_997])).

tff(c_1484,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1481,c_1090])).

tff(c_1485,plain,(
    ! [A_258] : v1_xboole_0(A_258) ),
    inference(splitRight,[status(thm)],[c_1336])).

tff(c_16,plain,(
    ! [B_8,A_7] :
      ( ~ v1_xboole_0(B_8)
      | B_8 = A_7
      | ~ v1_xboole_0(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_1520,plain,(
    ! [B_321,A_322] : B_321 = A_322 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1485,c_1485,c_16])).

tff(c_18,plain,(
    ! [A_9] : k5_xboole_0(A_9,A_9) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_805,plain,(
    ! [A_9] : k5_xboole_0(A_9,A_9) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_730,c_18])).

tff(c_46,plain,(
    ! [A_43] : k1_setfam_1(k1_tarski(A_43)) = A_43 ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_20,plain,(
    ! [A_10] : k2_tarski(A_10,A_10) = k1_tarski(A_10) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_828,plain,(
    ! [A_191,B_192] : k1_setfam_1(k2_tarski(A_191,B_192)) = k3_xboole_0(A_191,B_192) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_837,plain,(
    ! [A_10] : k3_xboole_0(A_10,A_10) = k1_setfam_1(k1_tarski(A_10)) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_828])).

tff(c_840,plain,(
    ! [A_10] : k3_xboole_0(A_10,A_10) = A_10 ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_837])).

tff(c_889,plain,(
    ! [A_203,B_204] : k5_xboole_0(A_203,k3_xboole_0(A_203,B_204)) = k4_xboole_0(A_203,B_204) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_898,plain,(
    ! [A_10] : k5_xboole_0(A_10,A_10) = k4_xboole_0(A_10,A_10) ),
    inference(superposition,[status(thm),theory(equality)],[c_840,c_889])).

tff(c_901,plain,(
    ! [A_10] : k4_xboole_0(A_10,A_10) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_805,c_898])).

tff(c_40,plain,(
    ! [B_41] : k4_xboole_0(k1_tarski(B_41),k1_tarski(B_41)) != k1_tarski(B_41) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_902,plain,(
    ! [B_41] : k1_tarski(B_41) != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_901,c_40])).

tff(c_3040,plain,(
    ! [A_322] : A_322 != '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_1520,c_902])).

tff(c_3782,plain,(
    $false ),
    inference(reflexivity,[status(thm),theory(equality)],[c_3040])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.13/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n023.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 19:43:50 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.18/1.76  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.18/1.77  
% 4.18/1.77  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.18/1.77  %$ v1_funct_2 > v1_partfun1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k5_partfun1 > k3_partfun1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 4.18/1.77  
% 4.18/1.77  %Foreground sorts:
% 4.18/1.77  
% 4.18/1.77  
% 4.18/1.77  %Background operators:
% 4.18/1.77  
% 4.18/1.77  
% 4.18/1.77  %Foreground operators:
% 4.18/1.77  tff(k3_partfun1, type, k3_partfun1: ($i * $i * $i) > $i).
% 4.18/1.77  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.18/1.77  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.18/1.77  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.18/1.77  tff(k1_tarski, type, k1_tarski: $i > $i).
% 4.18/1.77  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.18/1.77  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.18/1.77  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 4.18/1.77  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 4.18/1.77  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.18/1.77  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 4.18/1.77  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 4.18/1.77  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.18/1.77  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.18/1.77  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 4.18/1.77  tff('#skF_2', type, '#skF_2': $i).
% 4.18/1.77  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 4.18/1.77  tff('#skF_3', type, '#skF_3': $i).
% 4.18/1.77  tff('#skF_1', type, '#skF_1': $i).
% 4.18/1.77  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 4.18/1.77  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.18/1.77  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 4.18/1.77  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.18/1.77  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.18/1.77  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.18/1.77  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.18/1.77  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.18/1.77  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 4.18/1.77  tff(k5_partfun1, type, k5_partfun1: ($i * $i * $i) > $i).
% 4.18/1.77  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.18/1.77  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.18/1.77  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.18/1.77  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 4.18/1.77  
% 4.50/1.79  tff(f_155, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((B = k1_xboole_0) => (A = k1_xboole_0)) => (k5_partfun1(A, B, k3_partfun1(C, A, B)) = k1_tarski(C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t161_funct_2)).
% 4.50/1.79  tff(f_142, axiom, (![A, B, C]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (k3_partfun1(C, A, B) = C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t87_partfun1)).
% 4.50/1.79  tff(f_124, axiom, (![A, B, C]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (v1_partfun1(C, A) <=> (k5_partfun1(A, B, C) = k1_tarski(C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t174_partfun1)).
% 4.50/1.79  tff(f_116, axiom, (![A, B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) => (v1_funct_1(C) & v1_partfun1(C, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc5_funct_2)).
% 4.50/1.79  tff(f_30, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 4.50/1.79  tff(f_77, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 4.50/1.79  tff(f_102, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 4.50/1.79  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 4.50/1.79  tff(f_98, axiom, (![A]: (v1_xboole_0(A) => v1_funct_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_funct_1)).
% 4.50/1.79  tff(f_40, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 4.50/1.79  tff(f_94, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 4.50/1.79  tff(f_136, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r1_tarski(k2_relat_1(B), A) => ((v1_funct_1(B) & v1_funct_2(B, k1_relat_1(B), A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B), A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_funct_2)).
% 4.50/1.79  tff(f_70, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 4.50/1.79  tff(f_85, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 4.50/1.79  tff(f_36, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 4.50/1.79  tff(f_48, axiom, (![A, B]: ~((v1_xboole_0(A) & ~(A = B)) & v1_xboole_0(B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_boole)).
% 4.50/1.79  tff(f_50, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t92_xboole_1)).
% 4.50/1.79  tff(f_79, axiom, (![A]: (k1_setfam_1(k1_tarski(A)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_setfam_1)).
% 4.50/1.79  tff(f_52, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 4.50/1.79  tff(f_81, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 4.50/1.79  tff(f_38, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 4.50/1.79  tff(f_75, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) <=> ~(A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_zfmisc_1)).
% 4.50/1.79  tff(c_88, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_155])).
% 4.50/1.79  tff(c_84, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_155])).
% 4.50/1.79  tff(c_405, plain, (![C_131, A_132, B_133]: (k3_partfun1(C_131, A_132, B_133)=C_131 | ~m1_subset_1(C_131, k1_zfmisc_1(k2_zfmisc_1(A_132, B_133))) | ~v1_funct_1(C_131))), inference(cnfTransformation, [status(thm)], [f_142])).
% 4.50/1.79  tff(c_412, plain, (k3_partfun1('#skF_3', '#skF_1', '#skF_2')='#skF_3' | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_84, c_405])).
% 4.50/1.79  tff(c_426, plain, (k3_partfun1('#skF_3', '#skF_1', '#skF_2')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_88, c_412])).
% 4.50/1.79  tff(c_80, plain, (k5_partfun1('#skF_1', '#skF_2', k3_partfun1('#skF_3', '#skF_1', '#skF_2'))!=k1_tarski('#skF_3')), inference(cnfTransformation, [status(thm)], [f_155])).
% 4.50/1.79  tff(c_430, plain, (k5_partfun1('#skF_1', '#skF_2', '#skF_3')!=k1_tarski('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_426, c_80])).
% 4.50/1.79  tff(c_699, plain, (![A_177, B_178, C_179]: (k5_partfun1(A_177, B_178, C_179)=k1_tarski(C_179) | ~v1_partfun1(C_179, A_177) | ~m1_subset_1(C_179, k1_zfmisc_1(k2_zfmisc_1(A_177, B_178))) | ~v1_funct_1(C_179))), inference(cnfTransformation, [status(thm)], [f_124])).
% 4.50/1.79  tff(c_709, plain, (k5_partfun1('#skF_1', '#skF_2', '#skF_3')=k1_tarski('#skF_3') | ~v1_partfun1('#skF_3', '#skF_1') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_84, c_699])).
% 4.50/1.79  tff(c_724, plain, (k5_partfun1('#skF_1', '#skF_2', '#skF_3')=k1_tarski('#skF_3') | ~v1_partfun1('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_88, c_709])).
% 4.50/1.79  tff(c_725, plain, (~v1_partfun1('#skF_3', '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_430, c_724])).
% 4.50/1.79  tff(c_82, plain, (k1_xboole_0='#skF_1' | k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_155])).
% 4.50/1.79  tff(c_105, plain, (k1_xboole_0!='#skF_2'), inference(splitLeft, [status(thm)], [c_82])).
% 4.50/1.79  tff(c_86, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_155])).
% 4.50/1.79  tff(c_653, plain, (![C_174, A_175, B_176]: (v1_partfun1(C_174, A_175) | ~v1_funct_2(C_174, A_175, B_176) | ~v1_funct_1(C_174) | ~m1_subset_1(C_174, k1_zfmisc_1(k2_zfmisc_1(A_175, B_176))) | v1_xboole_0(B_176))), inference(cnfTransformation, [status(thm)], [f_116])).
% 4.50/1.79  tff(c_663, plain, (v1_partfun1('#skF_3', '#skF_1') | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3') | v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_84, c_653])).
% 4.50/1.79  tff(c_678, plain, (v1_partfun1('#skF_3', '#skF_1') | v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_88, c_86, c_663])).
% 4.50/1.79  tff(c_683, plain, (v1_xboole_0('#skF_2')), inference(splitLeft, [status(thm)], [c_678])).
% 4.50/1.79  tff(c_4, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_30])).
% 4.50/1.79  tff(c_688, plain, (k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_683, c_4])).
% 4.50/1.79  tff(c_696, plain, $false, inference(negUnitSimplification, [status(thm)], [c_105, c_688])).
% 4.50/1.79  tff(c_697, plain, (v1_partfun1('#skF_3', '#skF_1')), inference(splitRight, [status(thm)], [c_678])).
% 4.50/1.79  tff(c_729, plain, $false, inference(negUnitSimplification, [status(thm)], [c_725, c_697])).
% 4.50/1.79  tff(c_730, plain, (k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_82])).
% 4.50/1.79  tff(c_44, plain, (![A_42]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_42)))), inference(cnfTransformation, [status(thm)], [f_77])).
% 4.50/1.79  tff(c_771, plain, (![A_42]: (m1_subset_1('#skF_1', k1_zfmisc_1(A_42)))), inference(demodulation, [status(thm), theory('equality')], [c_730, c_44])).
% 4.50/1.79  tff(c_874, plain, (![C_200, A_201, B_202]: (v1_relat_1(C_200) | ~m1_subset_1(C_200, k1_zfmisc_1(k2_zfmisc_1(A_201, B_202))))), inference(cnfTransformation, [status(thm)], [f_102])).
% 4.50/1.79  tff(c_888, plain, (v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_771, c_874])).
% 4.50/1.79  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 4.50/1.79  tff(c_100, plain, (![A_69]: (v1_funct_1(A_69) | ~v1_xboole_0(A_69))), inference(cnfTransformation, [status(thm)], [f_98])).
% 4.50/1.79  tff(c_104, plain, (v1_funct_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_100])).
% 4.50/1.79  tff(c_732, plain, (v1_funct_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_730, c_104])).
% 4.50/1.79  tff(c_14, plain, (![A_6]: (r1_tarski(k1_xboole_0, A_6))), inference(cnfTransformation, [status(thm)], [f_40])).
% 4.50/1.79  tff(c_735, plain, (![A_6]: (r1_tarski('#skF_1', A_6))), inference(demodulation, [status(thm), theory('equality')], [c_730, c_14])).
% 4.50/1.79  tff(c_56, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_94])).
% 4.50/1.79  tff(c_733, plain, (k2_relat_1('#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_730, c_730, c_56])).
% 4.50/1.79  tff(c_58, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_94])).
% 4.50/1.79  tff(c_734, plain, (k1_relat_1('#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_730, c_730, c_58])).
% 4.50/1.79  tff(c_1174, plain, (![B_257, A_258]: (v1_funct_2(B_257, k1_relat_1(B_257), A_258) | ~r1_tarski(k2_relat_1(B_257), A_258) | ~v1_funct_1(B_257) | ~v1_relat_1(B_257))), inference(cnfTransformation, [status(thm)], [f_136])).
% 4.50/1.79  tff(c_1177, plain, (![A_258]: (v1_funct_2('#skF_1', '#skF_1', A_258) | ~r1_tarski(k2_relat_1('#skF_1'), A_258) | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_734, c_1174])).
% 4.50/1.79  tff(c_1179, plain, (![A_258]: (v1_funct_2('#skF_1', '#skF_1', A_258))), inference(demodulation, [status(thm), theory('equality')], [c_888, c_732, c_735, c_733, c_1177])).
% 4.50/1.79  tff(c_1304, plain, (![C_277, A_278, B_279]: (v1_partfun1(C_277, A_278) | ~v1_funct_2(C_277, A_278, B_279) | ~v1_funct_1(C_277) | ~m1_subset_1(C_277, k1_zfmisc_1(k2_zfmisc_1(A_278, B_279))) | v1_xboole_0(B_279))), inference(cnfTransformation, [status(thm)], [f_116])).
% 4.50/1.79  tff(c_1321, plain, (![A_278, B_279]: (v1_partfun1('#skF_1', A_278) | ~v1_funct_2('#skF_1', A_278, B_279) | ~v1_funct_1('#skF_1') | v1_xboole_0(B_279))), inference(resolution, [status(thm)], [c_771, c_1304])).
% 4.50/1.79  tff(c_1328, plain, (![A_280, B_281]: (v1_partfun1('#skF_1', A_280) | ~v1_funct_2('#skF_1', A_280, B_281) | v1_xboole_0(B_281))), inference(demodulation, [status(thm), theory('equality')], [c_732, c_1321])).
% 4.50/1.79  tff(c_1336, plain, (![A_258]: (v1_partfun1('#skF_1', '#skF_1') | v1_xboole_0(A_258))), inference(resolution, [status(thm)], [c_1179, c_1328])).
% 4.50/1.79  tff(c_1340, plain, (v1_partfun1('#skF_1', '#skF_1')), inference(splitLeft, [status(thm)], [c_1336])).
% 4.50/1.79  tff(c_1449, plain, (![A_312, B_313, C_314]: (k5_partfun1(A_312, B_313, C_314)=k1_tarski(C_314) | ~v1_partfun1(C_314, A_312) | ~m1_subset_1(C_314, k1_zfmisc_1(k2_zfmisc_1(A_312, B_313))) | ~v1_funct_1(C_314))), inference(cnfTransformation, [status(thm)], [f_124])).
% 4.50/1.79  tff(c_1466, plain, (![A_312, B_313]: (k5_partfun1(A_312, B_313, '#skF_1')=k1_tarski('#skF_1') | ~v1_partfun1('#skF_1', A_312) | ~v1_funct_1('#skF_1'))), inference(resolution, [status(thm)], [c_771, c_1449])).
% 4.50/1.79  tff(c_1472, plain, (![A_315, B_316]: (k5_partfun1(A_315, B_316, '#skF_1')=k1_tarski('#skF_1') | ~v1_partfun1('#skF_1', A_315))), inference(demodulation, [status(thm), theory('equality')], [c_732, c_1466])).
% 4.50/1.79  tff(c_1481, plain, (![B_316]: (k5_partfun1('#skF_1', B_316, '#skF_1')=k1_tarski('#skF_1'))), inference(resolution, [status(thm)], [c_1340, c_1472])).
% 4.50/1.79  tff(c_1071, plain, (![C_236, A_237, B_238]: (k3_partfun1(C_236, A_237, B_238)=C_236 | ~m1_subset_1(C_236, k1_zfmisc_1(k2_zfmisc_1(A_237, B_238))) | ~v1_funct_1(C_236))), inference(cnfTransformation, [status(thm)], [f_142])).
% 4.50/1.79  tff(c_1085, plain, (![A_237, B_238]: (k3_partfun1('#skF_1', A_237, B_238)='#skF_1' | ~v1_funct_1('#skF_1'))), inference(resolution, [status(thm)], [c_771, c_1071])).
% 4.50/1.79  tff(c_1089, plain, (![A_237, B_238]: (k3_partfun1('#skF_1', A_237, B_238)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_732, c_1085])).
% 4.50/1.79  tff(c_38, plain, (![B_39]: (k2_zfmisc_1(k1_xboole_0, B_39)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_70])).
% 4.50/1.79  tff(c_780, plain, (![B_39]: (k2_zfmisc_1('#skF_1', B_39)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_730, c_730, c_38])).
% 4.50/1.79  tff(c_731, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_82])).
% 4.50/1.79  tff(c_741, plain, ('#skF_2'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_730, c_731])).
% 4.50/1.79  tff(c_770, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_741, c_84])).
% 4.50/1.79  tff(c_781, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_780, c_770])).
% 4.50/1.79  tff(c_851, plain, (![A_196, B_197]: (r1_tarski(A_196, B_197) | ~m1_subset_1(A_196, k1_zfmisc_1(B_197)))), inference(cnfTransformation, [status(thm)], [f_85])).
% 4.50/1.79  tff(c_862, plain, (r1_tarski('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_781, c_851])).
% 4.50/1.79  tff(c_980, plain, (![B_216, A_217]: (B_216=A_217 | ~r1_tarski(B_216, A_217) | ~r1_tarski(A_217, B_216))), inference(cnfTransformation, [status(thm)], [f_36])).
% 4.50/1.79  tff(c_982, plain, ('#skF_3'='#skF_1' | ~r1_tarski('#skF_1', '#skF_3')), inference(resolution, [status(thm)], [c_862, c_980])).
% 4.50/1.79  tff(c_989, plain, ('#skF_3'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_735, c_982])).
% 4.50/1.79  tff(c_826, plain, (k5_partfun1('#skF_1', '#skF_1', k3_partfun1('#skF_3', '#skF_1', '#skF_1'))!=k1_tarski('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_741, c_741, c_80])).
% 4.50/1.79  tff(c_997, plain, (k5_partfun1('#skF_1', '#skF_1', k3_partfun1('#skF_1', '#skF_1', '#skF_1'))!=k1_tarski('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_989, c_989, c_826])).
% 4.50/1.79  tff(c_1090, plain, (k5_partfun1('#skF_1', '#skF_1', '#skF_1')!=k1_tarski('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1089, c_997])).
% 4.50/1.79  tff(c_1484, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1481, c_1090])).
% 4.50/1.79  tff(c_1485, plain, (![A_258]: (v1_xboole_0(A_258))), inference(splitRight, [status(thm)], [c_1336])).
% 4.50/1.79  tff(c_16, plain, (![B_8, A_7]: (~v1_xboole_0(B_8) | B_8=A_7 | ~v1_xboole_0(A_7))), inference(cnfTransformation, [status(thm)], [f_48])).
% 4.50/1.79  tff(c_1520, plain, (![B_321, A_322]: (B_321=A_322)), inference(demodulation, [status(thm), theory('equality')], [c_1485, c_1485, c_16])).
% 4.50/1.79  tff(c_18, plain, (![A_9]: (k5_xboole_0(A_9, A_9)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_50])).
% 4.50/1.79  tff(c_805, plain, (![A_9]: (k5_xboole_0(A_9, A_9)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_730, c_18])).
% 4.50/1.79  tff(c_46, plain, (![A_43]: (k1_setfam_1(k1_tarski(A_43))=A_43)), inference(cnfTransformation, [status(thm)], [f_79])).
% 4.50/1.79  tff(c_20, plain, (![A_10]: (k2_tarski(A_10, A_10)=k1_tarski(A_10))), inference(cnfTransformation, [status(thm)], [f_52])).
% 4.50/1.79  tff(c_828, plain, (![A_191, B_192]: (k1_setfam_1(k2_tarski(A_191, B_192))=k3_xboole_0(A_191, B_192))), inference(cnfTransformation, [status(thm)], [f_81])).
% 4.50/1.79  tff(c_837, plain, (![A_10]: (k3_xboole_0(A_10, A_10)=k1_setfam_1(k1_tarski(A_10)))), inference(superposition, [status(thm), theory('equality')], [c_20, c_828])).
% 4.50/1.79  tff(c_840, plain, (![A_10]: (k3_xboole_0(A_10, A_10)=A_10)), inference(demodulation, [status(thm), theory('equality')], [c_46, c_837])).
% 4.50/1.79  tff(c_889, plain, (![A_203, B_204]: (k5_xboole_0(A_203, k3_xboole_0(A_203, B_204))=k4_xboole_0(A_203, B_204))), inference(cnfTransformation, [status(thm)], [f_38])).
% 4.50/1.79  tff(c_898, plain, (![A_10]: (k5_xboole_0(A_10, A_10)=k4_xboole_0(A_10, A_10))), inference(superposition, [status(thm), theory('equality')], [c_840, c_889])).
% 4.50/1.79  tff(c_901, plain, (![A_10]: (k4_xboole_0(A_10, A_10)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_805, c_898])).
% 4.50/1.79  tff(c_40, plain, (![B_41]: (k4_xboole_0(k1_tarski(B_41), k1_tarski(B_41))!=k1_tarski(B_41))), inference(cnfTransformation, [status(thm)], [f_75])).
% 4.50/1.79  tff(c_902, plain, (![B_41]: (k1_tarski(B_41)!='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_901, c_40])).
% 4.50/1.79  tff(c_3040, plain, (![A_322]: (A_322!='#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_1520, c_902])).
% 4.50/1.79  tff(c_3782, plain, $false, inference(reflexivity, [status(thm), theory('equality')], [c_3040])).
% 4.50/1.79  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.50/1.79  
% 4.50/1.79  Inference rules
% 4.50/1.79  ----------------------
% 4.50/1.79  #Ref     : 1
% 4.50/1.79  #Sup     : 744
% 4.50/1.79  #Fact    : 0
% 4.50/1.79  #Define  : 0
% 4.50/1.79  #Split   : 4
% 4.50/1.79  #Chain   : 0
% 4.50/1.79  #Close   : 0
% 4.50/1.79  
% 4.50/1.79  Ordering : KBO
% 4.50/1.79  
% 4.50/1.79  Simplification rules
% 4.50/1.79  ----------------------
% 4.50/1.79  #Subsume      : 54
% 4.50/1.79  #Demod        : 251
% 4.50/1.79  #Tautology    : 202
% 4.50/1.79  #SimpNegUnit  : 7
% 4.50/1.79  #BackRed      : 27
% 4.50/1.79  
% 4.50/1.79  #Partial instantiations: 1364
% 4.50/1.79  #Strategies tried      : 1
% 4.50/1.79  
% 4.50/1.79  Timing (in seconds)
% 4.50/1.79  ----------------------
% 4.50/1.80  Preprocessing        : 0.36
% 4.50/1.80  Parsing              : 0.19
% 4.50/1.80  CNF conversion       : 0.02
% 4.50/1.80  Main loop            : 0.64
% 4.50/1.80  Inferencing          : 0.27
% 4.50/1.80  Reduction            : 0.19
% 4.50/1.80  Demodulation         : 0.13
% 4.50/1.80  BG Simplification    : 0.03
% 4.50/1.80  Subsumption          : 0.10
% 4.50/1.80  Abstraction          : 0.03
% 4.50/1.80  MUC search           : 0.00
% 4.50/1.80  Cooper               : 0.00
% 4.50/1.80  Total                : 1.04
% 4.50/1.80  Index Insertion      : 0.00
% 4.50/1.80  Index Deletion       : 0.00
% 4.50/1.80  Index Matching       : 0.00
% 4.50/1.80  BG Taut test         : 0.00
%------------------------------------------------------------------------------
