%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:12:36 EST 2020

% Result     : Theorem 13.21s
% Output     : CNFRefutation 13.45s
% Verified   : 
% Statistics : Number of formulae       :  260 (4445 expanded)
%              Number of leaves         :   44 (1428 expanded)
%              Depth                    :   15
%              Number of atoms          :  451 (11027 expanded)
%              Number of equality atoms :  120 (2449 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v1_partfun1 > r2_hidden > r1_tarski > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

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

tff(f_170,negated_conjecture,(
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

tff(f_92,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_99,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(B,A)))
         => v1_xboole_0(C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc4_relset_1)).

tff(f_78,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).

tff(f_107,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_88,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k2_relat_1(A) = k1_relat_1(k2_funct_1(A))
          & k1_relat_1(A) = k2_relat_1(k2_funct_1(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).

tff(f_103,axiom,(
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

tff(f_141,axiom,(
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

tff(f_36,axiom,(
    ! [A,B] :
      ~ ( v1_xboole_0(A)
        & A != B
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_boole)).

tff(f_42,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_51,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_xboole_0(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_subset_1)).

tff(f_129,axiom,(
    ! [A] :
      ( v1_partfun1(k6_partfun1(A),A)
      & m1_subset_1(k6_partfun1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).

tff(f_131,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_61,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_28,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_153,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r1_tarski(k2_relat_1(B),A)
       => ( v1_funct_1(B)
          & v1_funct_2(B,k1_relat_1(B),A)
          & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B),A))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_funct_2)).

tff(f_44,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(c_78,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_34926,plain,(
    ! [C_751,A_752,B_753] :
      ( v1_relat_1(C_751)
      | ~ m1_subset_1(C_751,k1_zfmisc_1(k2_zfmisc_1(A_752,B_753))) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_34946,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_78,c_34926])).

tff(c_82,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_507,plain,(
    ! [C_96,B_97,A_98] :
      ( v1_xboole_0(C_96)
      | ~ m1_subset_1(C_96,k1_zfmisc_1(k2_zfmisc_1(B_97,A_98)))
      | ~ v1_xboole_0(A_98) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_525,plain,
    ( v1_xboole_0('#skF_3')
    | ~ v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_78,c_507])).

tff(c_530,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_525])).

tff(c_26,plain,(
    ! [A_17] :
      ( v1_funct_1(k2_funct_1(A_17))
      | ~ v1_funct_1(A_17)
      | ~ v1_relat_1(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_72,plain,
    ( ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_159,plain,(
    ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_72])).

tff(c_162,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_26,c_159])).

tff(c_165,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_162])).

tff(c_247,plain,(
    ! [C_58,A_59,B_60] :
      ( v1_relat_1(C_58)
      | ~ m1_subset_1(C_58,k1_zfmisc_1(k2_zfmisc_1(A_59,B_60))) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_253,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_78,c_247])).

tff(c_266,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_165,c_253])).

tff(c_267,plain,
    ( ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_72])).

tff(c_278,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_267])).

tff(c_280,plain,(
    ! [C_62,A_63,B_64] :
      ( v1_relat_1(C_62)
      | ~ m1_subset_1(C_62,k1_zfmisc_1(k2_zfmisc_1(A_63,B_64))) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_296,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_78,c_280])).

tff(c_76,plain,(
    v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_74,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_979,plain,(
    ! [A_128,B_129,C_130] :
      ( k2_relset_1(A_128,B_129,C_130) = k2_relat_1(C_130)
      | ~ m1_subset_1(C_130,k1_zfmisc_1(k2_zfmisc_1(A_128,B_129))) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_988,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_78,c_979])).

tff(c_1003,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_988])).

tff(c_32,plain,(
    ! [A_18] :
      ( k1_relat_1(k2_funct_1(A_18)) = k2_relat_1(A_18)
      | ~ v2_funct_1(A_18)
      | ~ v1_funct_1(A_18)
      | ~ v1_relat_1(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_28,plain,(
    ! [A_17] :
      ( v1_relat_1(k2_funct_1(A_17))
      | ~ v1_funct_1(A_17)
      | ~ v1_relat_1(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_268,plain,(
    v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_72])).

tff(c_80,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_667,plain,(
    ! [A_112,B_113,C_114] :
      ( k1_relset_1(A_112,B_113,C_114) = k1_relat_1(C_114)
      | ~ m1_subset_1(C_114,k1_zfmisc_1(k2_zfmisc_1(A_112,B_113))) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_686,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_78,c_667])).

tff(c_2373,plain,(
    ! [B_173,A_174,C_175] :
      ( k1_xboole_0 = B_173
      | k1_relset_1(A_174,B_173,C_175) = A_174
      | ~ v1_funct_2(C_175,A_174,B_173)
      | ~ m1_subset_1(C_175,k1_zfmisc_1(k2_zfmisc_1(A_174,B_173))) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_2388,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_1'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_78,c_2373])).

tff(c_2408,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_686,c_2388])).

tff(c_2412,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_2408])).

tff(c_544,plain,(
    ! [A_100] :
      ( k2_relat_1(k2_funct_1(A_100)) = k1_relat_1(A_100)
      | ~ v2_funct_1(A_100)
      | ~ v1_funct_1(A_100)
      | ~ v1_relat_1(A_100) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_62,plain,(
    ! [A_37] :
      ( v1_funct_2(A_37,k1_relat_1(A_37),k2_relat_1(A_37))
      | ~ v1_funct_1(A_37)
      | ~ v1_relat_1(A_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_8302,plain,(
    ! [A_290] :
      ( v1_funct_2(k2_funct_1(A_290),k1_relat_1(k2_funct_1(A_290)),k1_relat_1(A_290))
      | ~ v1_funct_1(k2_funct_1(A_290))
      | ~ v1_relat_1(k2_funct_1(A_290))
      | ~ v2_funct_1(A_290)
      | ~ v1_funct_1(A_290)
      | ~ v1_relat_1(A_290) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_544,c_62])).

tff(c_8305,plain,
    ( v1_funct_2(k2_funct_1('#skF_3'),k1_relat_1(k2_funct_1('#skF_3')),'#skF_1')
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_2412,c_8302])).

tff(c_8319,plain,
    ( v1_funct_2(k2_funct_1('#skF_3'),k1_relat_1(k2_funct_1('#skF_3')),'#skF_1')
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_296,c_82,c_76,c_268,c_8305])).

tff(c_8324,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_8319])).

tff(c_8327,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_28,c_8324])).

tff(c_8331,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_296,c_82,c_8327])).

tff(c_8333,plain,(
    v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_8319])).

tff(c_30,plain,(
    ! [A_18] :
      ( k2_relat_1(k2_funct_1(A_18)) = k1_relat_1(A_18)
      | ~ v2_funct_1(A_18)
      | ~ v1_funct_1(A_18)
      | ~ v1_relat_1(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_717,plain,(
    ! [A_118] :
      ( m1_subset_1(A_118,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_118),k2_relat_1(A_118))))
      | ~ v1_funct_1(A_118)
      | ~ v1_relat_1(A_118) ) ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_9314,plain,(
    ! [A_307] :
      ( m1_subset_1(k2_funct_1(A_307),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(A_307)),k1_relat_1(A_307))))
      | ~ v1_funct_1(k2_funct_1(A_307))
      | ~ v1_relat_1(k2_funct_1(A_307))
      | ~ v2_funct_1(A_307)
      | ~ v1_funct_1(A_307)
      | ~ v1_relat_1(A_307) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_717])).

tff(c_9343,plain,
    ( m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_3')),'#skF_1')))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_2412,c_9314])).

tff(c_9366,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_3')),'#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_296,c_82,c_76,c_8333,c_268,c_9343])).

tff(c_9399,plain,
    ( m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_3'),'#skF_1')))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_9366])).

tff(c_9415,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_296,c_82,c_76,c_1003,c_9399])).

tff(c_9417,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_278,c_9415])).

tff(c_9418,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_2408])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_9455,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_9418,c_2])).

tff(c_9457,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_530,c_9455])).

tff(c_9458,plain,(
    v1_xboole_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_525])).

tff(c_147,plain,(
    ! [B_49,A_50] :
      ( ~ v1_xboole_0(B_49)
      | B_49 = A_50
      | ~ v1_xboole_0(A_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_150,plain,(
    ! [A_50] :
      ( k1_xboole_0 = A_50
      | ~ v1_xboole_0(A_50) ) ),
    inference(resolution,[status(thm)],[c_2,c_147])).

tff(c_9465,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_9458,c_150])).

tff(c_10,plain,(
    ! [A_4] : k2_zfmisc_1(A_4,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_9486,plain,(
    ! [A_4] : k2_zfmisc_1(A_4,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9465,c_9465,c_10])).

tff(c_9459,plain,(
    v1_xboole_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_525])).

tff(c_9472,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_9459,c_150])).

tff(c_9498,plain,(
    '#skF_2' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9465,c_9472])).

tff(c_298,plain,(
    ! [B_65,A_66] :
      ( v1_xboole_0(B_65)
      | ~ m1_subset_1(B_65,k1_zfmisc_1(A_66))
      | ~ v1_xboole_0(A_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_315,plain,
    ( v1_xboole_0('#skF_3')
    | ~ v1_xboole_0(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_78,c_298])).

tff(c_350,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_315])).

tff(c_9501,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_1','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9498,c_350])).

tff(c_9677,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_9458,c_9486,c_9501])).

tff(c_9678,plain,(
    v1_xboole_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_315])).

tff(c_9685,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_9678,c_150])).

tff(c_12,plain,(
    ! [B_5] : k2_zfmisc_1(k1_xboole_0,B_5) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_9692,plain,(
    ! [B_5] : k2_zfmisc_1('#skF_3',B_5) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9685,c_9685,c_12])).

tff(c_9679,plain,(
    v1_xboole_0(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_315])).

tff(c_6,plain,(
    ! [B_3,A_2] :
      ( ~ v1_xboole_0(B_3)
      | B_3 = A_2
      | ~ v1_xboole_0(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_9754,plain,(
    ! [A_319] :
      ( A_319 = '#skF_3'
      | ~ v1_xboole_0(A_319) ) ),
    inference(resolution,[status(thm)],[c_9678,c_6])).

tff(c_9761,plain,(
    k2_zfmisc_1('#skF_1','#skF_2') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_9679,c_9754])).

tff(c_8,plain,(
    ! [B_5,A_4] :
      ( k1_xboole_0 = B_5
      | k1_xboole_0 = A_4
      | k2_zfmisc_1(A_4,B_5) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_9722,plain,(
    ! [B_5,A_4] :
      ( B_5 = '#skF_3'
      | A_4 = '#skF_3'
      | k2_zfmisc_1(A_4,B_5) != '#skF_3' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9685,c_9685,c_9685,c_8])).

tff(c_9841,plain,
    ( '#skF_2' = '#skF_3'
    | '#skF_3' = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_9761,c_9722])).

tff(c_9843,plain,(
    '#skF_3' = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_9841])).

tff(c_9691,plain,(
    ! [A_4] : k2_zfmisc_1(A_4,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9685,c_9685,c_10])).

tff(c_9846,plain,(
    ! [A_4] : k2_zfmisc_1(A_4,'#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9843,c_9843,c_9691])).

tff(c_9858,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9843,c_278])).

tff(c_10072,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_1'),k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9846,c_9858])).

tff(c_9857,plain,(
    v1_relat_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_9843,c_296])).

tff(c_9863,plain,(
    v1_funct_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_9843,c_82])).

tff(c_9862,plain,(
    v2_funct_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_9843,c_76])).

tff(c_9859,plain,(
    v1_funct_1(k2_funct_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9843,c_268])).

tff(c_269,plain,(
    ! [A_61] : m1_subset_1(k6_partfun1(A_61),k1_zfmisc_1(k2_zfmisc_1(A_61,A_61))) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_273,plain,(
    m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_269])).

tff(c_301,plain,
    ( v1_xboole_0(k6_partfun1(k1_xboole_0))
    | ~ v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_273,c_298])).

tff(c_313,plain,(
    v1_xboole_0(k6_partfun1(k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_301])).

tff(c_324,plain,(
    k6_partfun1(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_313,c_150])).

tff(c_58,plain,(
    ! [A_36] : k6_relat_1(A_36) = k6_partfun1(A_36) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_20,plain,(
    ! [A_13] : k1_relat_1(k6_relat_1(A_13)) = A_13 ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_84,plain,(
    ! [A_13] : k1_relat_1(k6_partfun1(A_13)) = A_13 ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_20])).

tff(c_344,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_324,c_84])).

tff(c_9724,plain,(
    k1_relat_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9685,c_9685,c_344])).

tff(c_9851,plain,(
    k1_relat_1('#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9843,c_9843,c_9724])).

tff(c_10057,plain,(
    ! [A_340] :
      ( k2_relat_1(k2_funct_1(A_340)) = k1_relat_1(A_340)
      | ~ v2_funct_1(A_340)
      | ~ v1_funct_1(A_340)
      | ~ v1_relat_1(A_340) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_20669,plain,(
    ! [A_522] :
      ( v1_funct_2(k2_funct_1(A_522),k1_relat_1(k2_funct_1(A_522)),k1_relat_1(A_522))
      | ~ v1_funct_1(k2_funct_1(A_522))
      | ~ v1_relat_1(k2_funct_1(A_522))
      | ~ v2_funct_1(A_522)
      | ~ v1_funct_1(A_522)
      | ~ v1_relat_1(A_522) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10057,c_62])).

tff(c_20678,plain,
    ( v1_funct_2(k2_funct_1('#skF_1'),k1_relat_1(k2_funct_1('#skF_1')),'#skF_1')
    | ~ v1_funct_1(k2_funct_1('#skF_1'))
    | ~ v1_relat_1(k2_funct_1('#skF_1'))
    | ~ v2_funct_1('#skF_1')
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_9851,c_20669])).

tff(c_20683,plain,
    ( v1_funct_2(k2_funct_1('#skF_1'),k1_relat_1(k2_funct_1('#skF_1')),'#skF_1')
    | ~ v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9857,c_9863,c_9862,c_9859,c_20678])).

tff(c_20686,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_20683])).

tff(c_20689,plain,
    ( ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_28,c_20686])).

tff(c_20693,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_9857,c_9863,c_20689])).

tff(c_20695,plain,(
    v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_20683])).

tff(c_10893,plain,(
    ! [A_393] :
      ( m1_subset_1(A_393,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_393),k2_relat_1(A_393))))
      | ~ v1_funct_1(A_393)
      | ~ v1_relat_1(A_393) ) ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_22162,plain,(
    ! [A_539] :
      ( m1_subset_1(k2_funct_1(A_539),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(A_539)),k1_relat_1(A_539))))
      | ~ v1_funct_1(k2_funct_1(A_539))
      | ~ v1_relat_1(k2_funct_1(A_539))
      | ~ v2_funct_1(A_539)
      | ~ v1_funct_1(A_539)
      | ~ v1_relat_1(A_539) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_10893])).

tff(c_22197,plain,
    ( m1_subset_1(k2_funct_1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_1')),'#skF_1')))
    | ~ v1_funct_1(k2_funct_1('#skF_1'))
    | ~ v1_relat_1(k2_funct_1('#skF_1'))
    | ~ v2_funct_1('#skF_1')
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_9851,c_22162])).

tff(c_22211,plain,(
    m1_subset_1(k2_funct_1('#skF_1'),k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9857,c_9863,c_9862,c_20695,c_9859,c_9846,c_22197])).

tff(c_22213,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_10072,c_22211])).

tff(c_22214,plain,(
    '#skF_2' = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_9841])).

tff(c_22217,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22214,c_278])).

tff(c_22221,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9692,c_22217])).

tff(c_22394,plain,(
    ! [A_561] :
      ( k2_relat_1(k2_funct_1(A_561)) = k1_relat_1(A_561)
      | ~ v2_funct_1(A_561)
      | ~ v1_funct_1(A_561)
      | ~ v1_relat_1(A_561) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_33848,plain,(
    ! [A_739] :
      ( v1_funct_2(k2_funct_1(A_739),k1_relat_1(k2_funct_1(A_739)),k1_relat_1(A_739))
      | ~ v1_funct_1(k2_funct_1(A_739))
      | ~ v1_relat_1(k2_funct_1(A_739))
      | ~ v2_funct_1(A_739)
      | ~ v1_funct_1(A_739)
      | ~ v1_relat_1(A_739) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22394,c_62])).

tff(c_33857,plain,
    ( v1_funct_2(k2_funct_1('#skF_3'),k1_relat_1(k2_funct_1('#skF_3')),'#skF_3')
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_9724,c_33848])).

tff(c_33862,plain,
    ( v1_funct_2(k2_funct_1('#skF_3'),k1_relat_1(k2_funct_1('#skF_3')),'#skF_3')
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_296,c_82,c_76,c_268,c_33857])).

tff(c_33865,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_33862])).

tff(c_33868,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_28,c_33865])).

tff(c_33872,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_296,c_82,c_33868])).

tff(c_33874,plain,(
    v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_33862])).

tff(c_22,plain,(
    ! [A_13] : k2_relat_1(k6_relat_1(A_13)) = A_13 ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_83,plain,(
    ! [A_13] : k2_relat_1(k6_partfun1(A_13)) = A_13 ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_22])).

tff(c_338,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_324,c_83])).

tff(c_9729,plain,(
    k2_relat_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9685,c_9685,c_338])).

tff(c_23361,plain,(
    ! [A_597] :
      ( m1_subset_1(A_597,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_597),k2_relat_1(A_597))))
      | ~ v1_funct_1(A_597)
      | ~ v1_relat_1(A_597) ) ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_34871,plain,(
    ! [A_750] :
      ( m1_subset_1(k2_funct_1(A_750),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(A_750),k2_relat_1(k2_funct_1(A_750)))))
      | ~ v1_funct_1(k2_funct_1(A_750))
      | ~ v1_relat_1(k2_funct_1(A_750))
      | ~ v2_funct_1(A_750)
      | ~ v1_funct_1(A_750)
      | ~ v1_relat_1(A_750) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_23361])).

tff(c_34906,plain,
    ( m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3',k2_relat_1(k2_funct_1('#skF_3')))))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_9729,c_34871])).

tff(c_34920,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_296,c_82,c_76,c_33874,c_268,c_9692,c_34906])).

tff(c_34922,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_22221,c_34920])).

tff(c_34924,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_267])).

tff(c_35092,plain,(
    ! [C_771,B_772,A_773] :
      ( v1_xboole_0(C_771)
      | ~ m1_subset_1(C_771,k1_zfmisc_1(k2_zfmisc_1(B_772,A_773)))
      | ~ v1_xboole_0(A_773) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_35112,plain,
    ( v1_xboole_0(k2_funct_1('#skF_3'))
    | ~ v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_34924,c_35092])).

tff(c_35120,plain,(
    ~ v1_xboole_0('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_35112])).

tff(c_35306,plain,(
    ! [A_791,B_792,C_793] :
      ( k2_relset_1(A_791,B_792,C_793) = k2_relat_1(C_793)
      | ~ m1_subset_1(C_793,k1_zfmisc_1(k2_zfmisc_1(A_791,B_792))) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_35315,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_78,c_35306])).

tff(c_35330,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_35315])).

tff(c_34923,plain,(
    ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_267])).

tff(c_35370,plain,(
    ! [A_797,B_798,C_799] :
      ( k1_relset_1(A_797,B_798,C_799) = k1_relat_1(C_799)
      | ~ m1_subset_1(C_799,k1_zfmisc_1(k2_zfmisc_1(A_797,B_798))) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_35390,plain,(
    k1_relset_1('#skF_2','#skF_1',k2_funct_1('#skF_3')) = k1_relat_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_34924,c_35370])).

tff(c_37507,plain,(
    ! [B_874,C_875,A_876] :
      ( k1_xboole_0 = B_874
      | v1_funct_2(C_875,A_876,B_874)
      | k1_relset_1(A_876,B_874,C_875) != A_876
      | ~ m1_subset_1(C_875,k1_zfmisc_1(k2_zfmisc_1(A_876,B_874))) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_37519,plain,
    ( k1_xboole_0 = '#skF_1'
    | v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | k1_relset_1('#skF_2','#skF_1',k2_funct_1('#skF_3')) != '#skF_2' ),
    inference(resolution,[status(thm)],[c_34924,c_37507])).

tff(c_37540,plain,
    ( k1_xboole_0 = '#skF_1'
    | v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | k1_relat_1(k2_funct_1('#skF_3')) != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_35390,c_37519])).

tff(c_37541,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_relat_1(k2_funct_1('#skF_3')) != '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_34923,c_37540])).

tff(c_37551,plain,(
    k1_relat_1(k2_funct_1('#skF_3')) != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_37541])).

tff(c_37554,plain,
    ( k2_relat_1('#skF_3') != '#skF_2'
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_37551])).

tff(c_37557,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_34946,c_82,c_76,c_35330,c_37554])).

tff(c_37558,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_37541])).

tff(c_37599,plain,(
    v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_37558,c_2])).

tff(c_37601,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_35120,c_37599])).

tff(c_37603,plain,(
    v1_xboole_0('#skF_1') ),
    inference(splitRight,[status(thm)],[c_35112])).

tff(c_37609,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_37603,c_150])).

tff(c_37622,plain,(
    ! [B_5] : k2_zfmisc_1('#skF_1',B_5) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_37609,c_37609,c_12])).

tff(c_34961,plain,(
    ! [B_756,A_757] :
      ( v1_xboole_0(B_756)
      | ~ m1_subset_1(B_756,k1_zfmisc_1(A_757))
      | ~ v1_xboole_0(A_757) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_34982,plain,
    ( v1_xboole_0('#skF_3')
    | ~ v1_xboole_0(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_78,c_34961])).

tff(c_35020,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_34982])).

tff(c_37778,plain,(
    ~ v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_37622,c_35020])).

tff(c_37782,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_37603,c_37778])).

tff(c_37783,plain,(
    v1_xboole_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_34982])).

tff(c_37790,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_37783,c_150])).

tff(c_4,plain,(
    ! [A_1] : r1_tarski(k1_xboole_0,A_1) ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_37801,plain,(
    ! [A_1] : r1_tarski('#skF_3',A_1) ),
    inference(demodulation,[status(thm),theory(equality)],[c_37790,c_4])).

tff(c_34967,plain,
    ( v1_xboole_0(k6_partfun1(k1_xboole_0))
    | ~ v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_273,c_34961])).

tff(c_34980,plain,(
    v1_xboole_0(k6_partfun1(k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_34967])).

tff(c_34990,plain,(
    k6_partfun1(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_34980,c_150])).

tff(c_37793,plain,(
    k6_partfun1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_37790,c_37790,c_34990])).

tff(c_37820,plain,(
    k2_relat_1('#skF_3') = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_37793,c_83])).

tff(c_35010,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_34990,c_84])).

tff(c_37831,plain,(
    k1_relat_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_37790,c_37790,c_35010])).

tff(c_39058,plain,(
    ! [B_974,A_975] :
      ( v1_funct_2(B_974,k1_relat_1(B_974),A_975)
      | ~ r1_tarski(k2_relat_1(B_974),A_975)
      | ~ v1_funct_1(B_974)
      | ~ v1_relat_1(B_974) ) ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_39067,plain,(
    ! [A_975] :
      ( v1_funct_2('#skF_3','#skF_3',A_975)
      | ~ r1_tarski(k2_relat_1('#skF_3'),A_975)
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_37831,c_39058])).

tff(c_39073,plain,(
    ! [A_975] : v1_funct_2('#skF_3','#skF_3',A_975) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34946,c_82,c_37801,c_37820,c_39067])).

tff(c_37799,plain,(
    ! [B_5] : k2_zfmisc_1('#skF_3',B_5) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_37790,c_37790,c_12])).

tff(c_37784,plain,(
    v1_xboole_0(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_34982])).

tff(c_37918,plain,(
    ! [A_892] :
      ( A_892 = '#skF_3'
      | ~ v1_xboole_0(A_892) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_37790,c_150])).

tff(c_37925,plain,(
    k2_zfmisc_1('#skF_1','#skF_2') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_37784,c_37918])).

tff(c_37810,plain,(
    ! [B_5,A_4] :
      ( B_5 = '#skF_3'
      | A_4 = '#skF_3'
      | k2_zfmisc_1(A_4,B_5) != '#skF_3' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_37790,c_37790,c_37790,c_8])).

tff(c_37941,plain,
    ( '#skF_2' = '#skF_3'
    | '#skF_3' = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_37925,c_37810])).

tff(c_37943,plain,(
    '#skF_3' = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_37941])).

tff(c_37958,plain,(
    v1_relat_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_37943,c_34946])).

tff(c_37965,plain,(
    v1_funct_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_37943,c_82])).

tff(c_37950,plain,(
    k2_relat_1('#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_37943,c_37943,c_37820])).

tff(c_37951,plain,(
    k1_relat_1('#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_37943,c_37943,c_37831])).

tff(c_38025,plain,
    ( v1_funct_2('#skF_1','#skF_1',k2_relat_1('#skF_1'))
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_37951,c_62])).

tff(c_38029,plain,(
    v1_funct_2('#skF_1','#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_37958,c_37965,c_37950,c_38025])).

tff(c_14,plain,(
    ! [A_6] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_6)) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_42,plain,(
    ! [A_32] :
      ( v1_funct_2(k1_xboole_0,A_32,k1_xboole_0)
      | k1_xboole_0 = A_32
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(A_32,k1_xboole_0))) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_86,plain,(
    ! [A_32] :
      ( v1_funct_2(k1_xboole_0,A_32,k1_xboole_0)
      | k1_xboole_0 = A_32 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_42])).

tff(c_37797,plain,(
    ! [A_32] :
      ( v1_funct_2('#skF_3',A_32,'#skF_3')
      | A_32 = '#skF_3' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_37790,c_37790,c_37790,c_86])).

tff(c_38179,plain,(
    ! [A_32] :
      ( v1_funct_2('#skF_1',A_32,'#skF_1')
      | A_32 = '#skF_1' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_37943,c_37943,c_37943,c_37797])).

tff(c_37956,plain,(
    v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_37943,c_37783])).

tff(c_37798,plain,(
    ! [A_4] : k2_zfmisc_1(A_4,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_37790,c_37790,c_10])).

tff(c_37946,plain,(
    ! [A_4] : k2_zfmisc_1(A_4,'#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_37943,c_37943,c_37798])).

tff(c_34977,plain,
    ( v1_xboole_0(k2_funct_1('#skF_3'))
    | ~ v1_xboole_0(k2_zfmisc_1('#skF_2','#skF_1')) ),
    inference(resolution,[status(thm)],[c_34924,c_34961])).

tff(c_38199,plain,(
    v1_xboole_0(k2_funct_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_37956,c_37946,c_37943,c_34977])).

tff(c_37796,plain,(
    ! [A_50] :
      ( A_50 = '#skF_3'
      | ~ v1_xboole_0(A_50) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_37790,c_150])).

tff(c_37945,plain,(
    ! [A_50] :
      ( A_50 = '#skF_1'
      | ~ v1_xboole_0(A_50) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_37943,c_37796])).

tff(c_38209,plain,(
    k2_funct_1('#skF_1') = '#skF_1' ),
    inference(resolution,[status(thm)],[c_38199,c_37945])).

tff(c_37960,plain,(
    ~ v1_funct_2(k2_funct_1('#skF_1'),'#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_37943,c_34923])).

tff(c_38212,plain,(
    ~ v1_funct_2('#skF_1','#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38209,c_37960])).

tff(c_38245,plain,(
    '#skF_2' = '#skF_1' ),
    inference(resolution,[status(thm)],[c_38179,c_38212])).

tff(c_38246,plain,(
    ~ v1_funct_2('#skF_1','#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38245,c_38212])).

tff(c_38251,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_38029,c_38246])).

tff(c_38252,plain,(
    '#skF_2' = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_37941])).

tff(c_38255,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38252,c_34924])).

tff(c_38260,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_37799,c_38255])).

tff(c_16,plain,(
    ! [B_9,A_7] :
      ( v1_xboole_0(B_9)
      | ~ m1_subset_1(B_9,k1_zfmisc_1(A_7))
      | ~ v1_xboole_0(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_38316,plain,
    ( v1_xboole_0(k2_funct_1('#skF_3'))
    | ~ v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_38260,c_16])).

tff(c_38320,plain,(
    v1_xboole_0(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_37783,c_38316])).

tff(c_38330,plain,(
    k2_funct_1('#skF_3') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_38320,c_37796])).

tff(c_38256,plain,(
    ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38252,c_34923])).

tff(c_38334,plain,(
    ~ v1_funct_2('#skF_3','#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38330,c_38256])).

tff(c_39079,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_39073,c_38334])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n007.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 16:00:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 13.21/5.04  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 13.41/5.07  
% 13.41/5.07  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 13.45/5.07  %$ v1_funct_2 > v1_partfun1 > r2_hidden > r1_tarski > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 13.45/5.07  
% 13.45/5.07  %Foreground sorts:
% 13.45/5.07  
% 13.45/5.07  
% 13.45/5.07  %Background operators:
% 13.45/5.07  
% 13.45/5.07  
% 13.45/5.07  %Foreground operators:
% 13.45/5.07  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 13.45/5.07  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 13.45/5.07  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 13.45/5.07  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 13.45/5.07  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 13.45/5.07  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 13.45/5.07  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 13.45/5.07  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 13.45/5.07  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 13.45/5.07  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 13.45/5.07  tff('#skF_2', type, '#skF_2': $i).
% 13.45/5.07  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 13.45/5.07  tff('#skF_3', type, '#skF_3': $i).
% 13.45/5.07  tff('#skF_1', type, '#skF_1': $i).
% 13.45/5.07  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 13.45/5.07  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 13.45/5.07  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 13.45/5.07  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 13.45/5.07  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 13.45/5.07  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 13.45/5.07  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 13.45/5.07  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 13.45/5.07  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 13.45/5.07  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 13.45/5.07  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 13.45/5.07  
% 13.45/5.10  tff(f_170, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((v2_funct_1(C) & (k2_relset_1(A, B, C) = B)) => ((v1_funct_1(k2_funct_1(C)) & v1_funct_2(k2_funct_1(C), B, A)) & m1_subset_1(k2_funct_1(C), k1_zfmisc_1(k2_zfmisc_1(B, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_funct_2)).
% 13.45/5.10  tff(f_92, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 13.45/5.10  tff(f_99, axiom, (![A, B]: (v1_xboole_0(A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => v1_xboole_0(C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc4_relset_1)).
% 13.45/5.10  tff(f_78, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 13.45/5.10  tff(f_107, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 13.45/5.10  tff(f_88, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k2_relat_1(A) = k1_relat_1(k2_funct_1(A))) & (k1_relat_1(A) = k2_relat_1(k2_funct_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_funct_1)).
% 13.45/5.10  tff(f_103, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 13.45/5.10  tff(f_125, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 13.45/5.10  tff(f_141, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => ((v1_funct_1(A) & v1_funct_2(A, k1_relat_1(A), k2_relat_1(A))) & m1_subset_1(A, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_funct_2)).
% 13.45/5.10  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 13.45/5.10  tff(f_36, axiom, (![A, B]: ~((v1_xboole_0(A) & ~(A = B)) & v1_xboole_0(B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_boole)).
% 13.45/5.10  tff(f_42, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 13.45/5.10  tff(f_51, axiom, (![A]: (v1_xboole_0(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_subset_1)).
% 13.45/5.10  tff(f_129, axiom, (![A]: (v1_partfun1(k6_partfun1(A), A) & m1_subset_1(k6_partfun1(A), k1_zfmisc_1(k2_zfmisc_1(A, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_partfun1)).
% 13.45/5.10  tff(f_131, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 13.45/5.10  tff(f_61, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 13.45/5.10  tff(f_28, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 13.45/5.10  tff(f_153, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r1_tarski(k2_relat_1(B), A) => ((v1_funct_1(B) & v1_funct_2(B, k1_relat_1(B), A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B), A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_funct_2)).
% 13.45/5.10  tff(f_44, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 13.45/5.10  tff(c_78, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_170])).
% 13.45/5.10  tff(c_34926, plain, (![C_751, A_752, B_753]: (v1_relat_1(C_751) | ~m1_subset_1(C_751, k1_zfmisc_1(k2_zfmisc_1(A_752, B_753))))), inference(cnfTransformation, [status(thm)], [f_92])).
% 13.45/5.10  tff(c_34946, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_78, c_34926])).
% 13.45/5.10  tff(c_82, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_170])).
% 13.45/5.10  tff(c_507, plain, (![C_96, B_97, A_98]: (v1_xboole_0(C_96) | ~m1_subset_1(C_96, k1_zfmisc_1(k2_zfmisc_1(B_97, A_98))) | ~v1_xboole_0(A_98))), inference(cnfTransformation, [status(thm)], [f_99])).
% 13.45/5.10  tff(c_525, plain, (v1_xboole_0('#skF_3') | ~v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_78, c_507])).
% 13.45/5.10  tff(c_530, plain, (~v1_xboole_0('#skF_2')), inference(splitLeft, [status(thm)], [c_525])).
% 13.45/5.10  tff(c_26, plain, (![A_17]: (v1_funct_1(k2_funct_1(A_17)) | ~v1_funct_1(A_17) | ~v1_relat_1(A_17))), inference(cnfTransformation, [status(thm)], [f_78])).
% 13.45/5.10  tff(c_72, plain, (~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | ~v1_funct_1(k2_funct_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_170])).
% 13.45/5.10  tff(c_159, plain, (~v1_funct_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_72])).
% 13.45/5.10  tff(c_162, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_26, c_159])).
% 13.45/5.10  tff(c_165, plain, (~v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_82, c_162])).
% 13.45/5.10  tff(c_247, plain, (![C_58, A_59, B_60]: (v1_relat_1(C_58) | ~m1_subset_1(C_58, k1_zfmisc_1(k2_zfmisc_1(A_59, B_60))))), inference(cnfTransformation, [status(thm)], [f_92])).
% 13.45/5.10  tff(c_253, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_78, c_247])).
% 13.45/5.10  tff(c_266, plain, $false, inference(negUnitSimplification, [status(thm)], [c_165, c_253])).
% 13.45/5.10  tff(c_267, plain, (~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | ~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(splitRight, [status(thm)], [c_72])).
% 13.45/5.10  tff(c_278, plain, (~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(splitLeft, [status(thm)], [c_267])).
% 13.45/5.10  tff(c_280, plain, (![C_62, A_63, B_64]: (v1_relat_1(C_62) | ~m1_subset_1(C_62, k1_zfmisc_1(k2_zfmisc_1(A_63, B_64))))), inference(cnfTransformation, [status(thm)], [f_92])).
% 13.45/5.10  tff(c_296, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_78, c_280])).
% 13.45/5.10  tff(c_76, plain, (v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_170])).
% 13.45/5.10  tff(c_74, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_2'), inference(cnfTransformation, [status(thm)], [f_170])).
% 13.45/5.10  tff(c_979, plain, (![A_128, B_129, C_130]: (k2_relset_1(A_128, B_129, C_130)=k2_relat_1(C_130) | ~m1_subset_1(C_130, k1_zfmisc_1(k2_zfmisc_1(A_128, B_129))))), inference(cnfTransformation, [status(thm)], [f_107])).
% 13.45/5.10  tff(c_988, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_78, c_979])).
% 13.45/5.10  tff(c_1003, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_74, c_988])).
% 13.45/5.10  tff(c_32, plain, (![A_18]: (k1_relat_1(k2_funct_1(A_18))=k2_relat_1(A_18) | ~v2_funct_1(A_18) | ~v1_funct_1(A_18) | ~v1_relat_1(A_18))), inference(cnfTransformation, [status(thm)], [f_88])).
% 13.45/5.10  tff(c_28, plain, (![A_17]: (v1_relat_1(k2_funct_1(A_17)) | ~v1_funct_1(A_17) | ~v1_relat_1(A_17))), inference(cnfTransformation, [status(thm)], [f_78])).
% 13.45/5.10  tff(c_268, plain, (v1_funct_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_72])).
% 13.45/5.10  tff(c_80, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_170])).
% 13.45/5.10  tff(c_667, plain, (![A_112, B_113, C_114]: (k1_relset_1(A_112, B_113, C_114)=k1_relat_1(C_114) | ~m1_subset_1(C_114, k1_zfmisc_1(k2_zfmisc_1(A_112, B_113))))), inference(cnfTransformation, [status(thm)], [f_103])).
% 13.45/5.10  tff(c_686, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_78, c_667])).
% 13.45/5.10  tff(c_2373, plain, (![B_173, A_174, C_175]: (k1_xboole_0=B_173 | k1_relset_1(A_174, B_173, C_175)=A_174 | ~v1_funct_2(C_175, A_174, B_173) | ~m1_subset_1(C_175, k1_zfmisc_1(k2_zfmisc_1(A_174, B_173))))), inference(cnfTransformation, [status(thm)], [f_125])).
% 13.45/5.10  tff(c_2388, plain, (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_1' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_78, c_2373])).
% 13.45/5.10  tff(c_2408, plain, (k1_xboole_0='#skF_2' | k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_80, c_686, c_2388])).
% 13.45/5.10  tff(c_2412, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(splitLeft, [status(thm)], [c_2408])).
% 13.45/5.10  tff(c_544, plain, (![A_100]: (k2_relat_1(k2_funct_1(A_100))=k1_relat_1(A_100) | ~v2_funct_1(A_100) | ~v1_funct_1(A_100) | ~v1_relat_1(A_100))), inference(cnfTransformation, [status(thm)], [f_88])).
% 13.45/5.10  tff(c_62, plain, (![A_37]: (v1_funct_2(A_37, k1_relat_1(A_37), k2_relat_1(A_37)) | ~v1_funct_1(A_37) | ~v1_relat_1(A_37))), inference(cnfTransformation, [status(thm)], [f_141])).
% 13.45/5.10  tff(c_8302, plain, (![A_290]: (v1_funct_2(k2_funct_1(A_290), k1_relat_1(k2_funct_1(A_290)), k1_relat_1(A_290)) | ~v1_funct_1(k2_funct_1(A_290)) | ~v1_relat_1(k2_funct_1(A_290)) | ~v2_funct_1(A_290) | ~v1_funct_1(A_290) | ~v1_relat_1(A_290))), inference(superposition, [status(thm), theory('equality')], [c_544, c_62])).
% 13.45/5.10  tff(c_8305, plain, (v1_funct_2(k2_funct_1('#skF_3'), k1_relat_1(k2_funct_1('#skF_3')), '#skF_1') | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_2412, c_8302])).
% 13.45/5.10  tff(c_8319, plain, (v1_funct_2(k2_funct_1('#skF_3'), k1_relat_1(k2_funct_1('#skF_3')), '#skF_1') | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_296, c_82, c_76, c_268, c_8305])).
% 13.45/5.10  tff(c_8324, plain, (~v1_relat_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_8319])).
% 13.45/5.10  tff(c_8327, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_28, c_8324])).
% 13.45/5.10  tff(c_8331, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_296, c_82, c_8327])).
% 13.45/5.10  tff(c_8333, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_8319])).
% 13.45/5.10  tff(c_30, plain, (![A_18]: (k2_relat_1(k2_funct_1(A_18))=k1_relat_1(A_18) | ~v2_funct_1(A_18) | ~v1_funct_1(A_18) | ~v1_relat_1(A_18))), inference(cnfTransformation, [status(thm)], [f_88])).
% 13.45/5.10  tff(c_717, plain, (![A_118]: (m1_subset_1(A_118, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_118), k2_relat_1(A_118)))) | ~v1_funct_1(A_118) | ~v1_relat_1(A_118))), inference(cnfTransformation, [status(thm)], [f_141])).
% 13.45/5.10  tff(c_9314, plain, (![A_307]: (m1_subset_1(k2_funct_1(A_307), k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(A_307)), k1_relat_1(A_307)))) | ~v1_funct_1(k2_funct_1(A_307)) | ~v1_relat_1(k2_funct_1(A_307)) | ~v2_funct_1(A_307) | ~v1_funct_1(A_307) | ~v1_relat_1(A_307))), inference(superposition, [status(thm), theory('equality')], [c_30, c_717])).
% 13.45/5.10  tff(c_9343, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_3')), '#skF_1'))) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_2412, c_9314])).
% 13.45/5.10  tff(c_9366, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_3')), '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_296, c_82, c_76, c_8333, c_268, c_9343])).
% 13.45/5.10  tff(c_9399, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_3'), '#skF_1'))) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_32, c_9366])).
% 13.45/5.10  tff(c_9415, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_296, c_82, c_76, c_1003, c_9399])).
% 13.45/5.10  tff(c_9417, plain, $false, inference(negUnitSimplification, [status(thm)], [c_278, c_9415])).
% 13.45/5.10  tff(c_9418, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_2408])).
% 13.45/5.10  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 13.45/5.10  tff(c_9455, plain, (v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_9418, c_2])).
% 13.45/5.10  tff(c_9457, plain, $false, inference(negUnitSimplification, [status(thm)], [c_530, c_9455])).
% 13.45/5.10  tff(c_9458, plain, (v1_xboole_0('#skF_3')), inference(splitRight, [status(thm)], [c_525])).
% 13.45/5.10  tff(c_147, plain, (![B_49, A_50]: (~v1_xboole_0(B_49) | B_49=A_50 | ~v1_xboole_0(A_50))), inference(cnfTransformation, [status(thm)], [f_36])).
% 13.45/5.10  tff(c_150, plain, (![A_50]: (k1_xboole_0=A_50 | ~v1_xboole_0(A_50))), inference(resolution, [status(thm)], [c_2, c_147])).
% 13.45/5.10  tff(c_9465, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_9458, c_150])).
% 13.45/5.10  tff(c_10, plain, (![A_4]: (k2_zfmisc_1(A_4, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_42])).
% 13.45/5.10  tff(c_9486, plain, (![A_4]: (k2_zfmisc_1(A_4, '#skF_3')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_9465, c_9465, c_10])).
% 13.45/5.10  tff(c_9459, plain, (v1_xboole_0('#skF_2')), inference(splitRight, [status(thm)], [c_525])).
% 13.45/5.10  tff(c_9472, plain, (k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_9459, c_150])).
% 13.45/5.10  tff(c_9498, plain, ('#skF_2'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_9465, c_9472])).
% 13.45/5.10  tff(c_298, plain, (![B_65, A_66]: (v1_xboole_0(B_65) | ~m1_subset_1(B_65, k1_zfmisc_1(A_66)) | ~v1_xboole_0(A_66))), inference(cnfTransformation, [status(thm)], [f_51])).
% 13.45/5.10  tff(c_315, plain, (v1_xboole_0('#skF_3') | ~v1_xboole_0(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_78, c_298])).
% 13.45/5.10  tff(c_350, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(splitLeft, [status(thm)], [c_315])).
% 13.45/5.10  tff(c_9501, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_1', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_9498, c_350])).
% 13.45/5.10  tff(c_9677, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_9458, c_9486, c_9501])).
% 13.45/5.10  tff(c_9678, plain, (v1_xboole_0('#skF_3')), inference(splitRight, [status(thm)], [c_315])).
% 13.45/5.10  tff(c_9685, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_9678, c_150])).
% 13.45/5.10  tff(c_12, plain, (![B_5]: (k2_zfmisc_1(k1_xboole_0, B_5)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_42])).
% 13.45/5.10  tff(c_9692, plain, (![B_5]: (k2_zfmisc_1('#skF_3', B_5)='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_9685, c_9685, c_12])).
% 13.45/5.10  tff(c_9679, plain, (v1_xboole_0(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(splitRight, [status(thm)], [c_315])).
% 13.45/5.10  tff(c_6, plain, (![B_3, A_2]: (~v1_xboole_0(B_3) | B_3=A_2 | ~v1_xboole_0(A_2))), inference(cnfTransformation, [status(thm)], [f_36])).
% 13.45/5.10  tff(c_9754, plain, (![A_319]: (A_319='#skF_3' | ~v1_xboole_0(A_319))), inference(resolution, [status(thm)], [c_9678, c_6])).
% 13.45/5.10  tff(c_9761, plain, (k2_zfmisc_1('#skF_1', '#skF_2')='#skF_3'), inference(resolution, [status(thm)], [c_9679, c_9754])).
% 13.45/5.10  tff(c_8, plain, (![B_5, A_4]: (k1_xboole_0=B_5 | k1_xboole_0=A_4 | k2_zfmisc_1(A_4, B_5)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_42])).
% 13.45/5.10  tff(c_9722, plain, (![B_5, A_4]: (B_5='#skF_3' | A_4='#skF_3' | k2_zfmisc_1(A_4, B_5)!='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_9685, c_9685, c_9685, c_8])).
% 13.45/5.10  tff(c_9841, plain, ('#skF_2'='#skF_3' | '#skF_3'='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_9761, c_9722])).
% 13.45/5.10  tff(c_9843, plain, ('#skF_3'='#skF_1'), inference(splitLeft, [status(thm)], [c_9841])).
% 13.45/5.10  tff(c_9691, plain, (![A_4]: (k2_zfmisc_1(A_4, '#skF_3')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_9685, c_9685, c_10])).
% 13.45/5.10  tff(c_9846, plain, (![A_4]: (k2_zfmisc_1(A_4, '#skF_1')='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_9843, c_9843, c_9691])).
% 13.45/5.10  tff(c_9858, plain, (~m1_subset_1(k2_funct_1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_9843, c_278])).
% 13.45/5.10  tff(c_10072, plain, (~m1_subset_1(k2_funct_1('#skF_1'), k1_zfmisc_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_9846, c_9858])).
% 13.45/5.10  tff(c_9857, plain, (v1_relat_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_9843, c_296])).
% 13.45/5.10  tff(c_9863, plain, (v1_funct_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_9843, c_82])).
% 13.45/5.10  tff(c_9862, plain, (v2_funct_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_9843, c_76])).
% 13.45/5.10  tff(c_9859, plain, (v1_funct_1(k2_funct_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_9843, c_268])).
% 13.45/5.10  tff(c_269, plain, (![A_61]: (m1_subset_1(k6_partfun1(A_61), k1_zfmisc_1(k2_zfmisc_1(A_61, A_61))))), inference(cnfTransformation, [status(thm)], [f_129])).
% 13.45/5.10  tff(c_273, plain, (m1_subset_1(k6_partfun1(k1_xboole_0), k1_zfmisc_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_10, c_269])).
% 13.45/5.10  tff(c_301, plain, (v1_xboole_0(k6_partfun1(k1_xboole_0)) | ~v1_xboole_0(k1_xboole_0)), inference(resolution, [status(thm)], [c_273, c_298])).
% 13.45/5.10  tff(c_313, plain, (v1_xboole_0(k6_partfun1(k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_301])).
% 13.45/5.10  tff(c_324, plain, (k6_partfun1(k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_313, c_150])).
% 13.45/5.10  tff(c_58, plain, (![A_36]: (k6_relat_1(A_36)=k6_partfun1(A_36))), inference(cnfTransformation, [status(thm)], [f_131])).
% 13.45/5.10  tff(c_20, plain, (![A_13]: (k1_relat_1(k6_relat_1(A_13))=A_13)), inference(cnfTransformation, [status(thm)], [f_61])).
% 13.45/5.10  tff(c_84, plain, (![A_13]: (k1_relat_1(k6_partfun1(A_13))=A_13)), inference(demodulation, [status(thm), theory('equality')], [c_58, c_20])).
% 13.45/5.10  tff(c_344, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_324, c_84])).
% 13.45/5.10  tff(c_9724, plain, (k1_relat_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_9685, c_9685, c_344])).
% 13.45/5.10  tff(c_9851, plain, (k1_relat_1('#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_9843, c_9843, c_9724])).
% 13.45/5.10  tff(c_10057, plain, (![A_340]: (k2_relat_1(k2_funct_1(A_340))=k1_relat_1(A_340) | ~v2_funct_1(A_340) | ~v1_funct_1(A_340) | ~v1_relat_1(A_340))), inference(cnfTransformation, [status(thm)], [f_88])).
% 13.45/5.10  tff(c_20669, plain, (![A_522]: (v1_funct_2(k2_funct_1(A_522), k1_relat_1(k2_funct_1(A_522)), k1_relat_1(A_522)) | ~v1_funct_1(k2_funct_1(A_522)) | ~v1_relat_1(k2_funct_1(A_522)) | ~v2_funct_1(A_522) | ~v1_funct_1(A_522) | ~v1_relat_1(A_522))), inference(superposition, [status(thm), theory('equality')], [c_10057, c_62])).
% 13.45/5.10  tff(c_20678, plain, (v1_funct_2(k2_funct_1('#skF_1'), k1_relat_1(k2_funct_1('#skF_1')), '#skF_1') | ~v1_funct_1(k2_funct_1('#skF_1')) | ~v1_relat_1(k2_funct_1('#skF_1')) | ~v2_funct_1('#skF_1') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_9851, c_20669])).
% 13.45/5.10  tff(c_20683, plain, (v1_funct_2(k2_funct_1('#skF_1'), k1_relat_1(k2_funct_1('#skF_1')), '#skF_1') | ~v1_relat_1(k2_funct_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_9857, c_9863, c_9862, c_9859, c_20678])).
% 13.45/5.10  tff(c_20686, plain, (~v1_relat_1(k2_funct_1('#skF_1'))), inference(splitLeft, [status(thm)], [c_20683])).
% 13.45/5.10  tff(c_20689, plain, (~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_28, c_20686])).
% 13.45/5.10  tff(c_20693, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_9857, c_9863, c_20689])).
% 13.45/5.10  tff(c_20695, plain, (v1_relat_1(k2_funct_1('#skF_1'))), inference(splitRight, [status(thm)], [c_20683])).
% 13.45/5.10  tff(c_10893, plain, (![A_393]: (m1_subset_1(A_393, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_393), k2_relat_1(A_393)))) | ~v1_funct_1(A_393) | ~v1_relat_1(A_393))), inference(cnfTransformation, [status(thm)], [f_141])).
% 13.45/5.10  tff(c_22162, plain, (![A_539]: (m1_subset_1(k2_funct_1(A_539), k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(A_539)), k1_relat_1(A_539)))) | ~v1_funct_1(k2_funct_1(A_539)) | ~v1_relat_1(k2_funct_1(A_539)) | ~v2_funct_1(A_539) | ~v1_funct_1(A_539) | ~v1_relat_1(A_539))), inference(superposition, [status(thm), theory('equality')], [c_30, c_10893])).
% 13.45/5.10  tff(c_22197, plain, (m1_subset_1(k2_funct_1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_1')), '#skF_1'))) | ~v1_funct_1(k2_funct_1('#skF_1')) | ~v1_relat_1(k2_funct_1('#skF_1')) | ~v2_funct_1('#skF_1') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_9851, c_22162])).
% 13.45/5.10  tff(c_22211, plain, (m1_subset_1(k2_funct_1('#skF_1'), k1_zfmisc_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_9857, c_9863, c_9862, c_20695, c_9859, c_9846, c_22197])).
% 13.45/5.10  tff(c_22213, plain, $false, inference(negUnitSimplification, [status(thm)], [c_10072, c_22211])).
% 13.45/5.10  tff(c_22214, plain, ('#skF_2'='#skF_3'), inference(splitRight, [status(thm)], [c_9841])).
% 13.45/5.10  tff(c_22217, plain, (~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_22214, c_278])).
% 13.45/5.10  tff(c_22221, plain, (~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_9692, c_22217])).
% 13.45/5.10  tff(c_22394, plain, (![A_561]: (k2_relat_1(k2_funct_1(A_561))=k1_relat_1(A_561) | ~v2_funct_1(A_561) | ~v1_funct_1(A_561) | ~v1_relat_1(A_561))), inference(cnfTransformation, [status(thm)], [f_88])).
% 13.45/5.10  tff(c_33848, plain, (![A_739]: (v1_funct_2(k2_funct_1(A_739), k1_relat_1(k2_funct_1(A_739)), k1_relat_1(A_739)) | ~v1_funct_1(k2_funct_1(A_739)) | ~v1_relat_1(k2_funct_1(A_739)) | ~v2_funct_1(A_739) | ~v1_funct_1(A_739) | ~v1_relat_1(A_739))), inference(superposition, [status(thm), theory('equality')], [c_22394, c_62])).
% 13.45/5.10  tff(c_33857, plain, (v1_funct_2(k2_funct_1('#skF_3'), k1_relat_1(k2_funct_1('#skF_3')), '#skF_3') | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_9724, c_33848])).
% 13.45/5.10  tff(c_33862, plain, (v1_funct_2(k2_funct_1('#skF_3'), k1_relat_1(k2_funct_1('#skF_3')), '#skF_3') | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_296, c_82, c_76, c_268, c_33857])).
% 13.45/5.10  tff(c_33865, plain, (~v1_relat_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_33862])).
% 13.45/5.10  tff(c_33868, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_28, c_33865])).
% 13.45/5.10  tff(c_33872, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_296, c_82, c_33868])).
% 13.45/5.10  tff(c_33874, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_33862])).
% 13.45/5.10  tff(c_22, plain, (![A_13]: (k2_relat_1(k6_relat_1(A_13))=A_13)), inference(cnfTransformation, [status(thm)], [f_61])).
% 13.45/5.10  tff(c_83, plain, (![A_13]: (k2_relat_1(k6_partfun1(A_13))=A_13)), inference(demodulation, [status(thm), theory('equality')], [c_58, c_22])).
% 13.45/5.10  tff(c_338, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_324, c_83])).
% 13.45/5.10  tff(c_9729, plain, (k2_relat_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_9685, c_9685, c_338])).
% 13.45/5.10  tff(c_23361, plain, (![A_597]: (m1_subset_1(A_597, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_597), k2_relat_1(A_597)))) | ~v1_funct_1(A_597) | ~v1_relat_1(A_597))), inference(cnfTransformation, [status(thm)], [f_141])).
% 13.45/5.10  tff(c_34871, plain, (![A_750]: (m1_subset_1(k2_funct_1(A_750), k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(A_750), k2_relat_1(k2_funct_1(A_750))))) | ~v1_funct_1(k2_funct_1(A_750)) | ~v1_relat_1(k2_funct_1(A_750)) | ~v2_funct_1(A_750) | ~v1_funct_1(A_750) | ~v1_relat_1(A_750))), inference(superposition, [status(thm), theory('equality')], [c_32, c_23361])).
% 13.45/5.10  tff(c_34906, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', k2_relat_1(k2_funct_1('#skF_3'))))) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_9729, c_34871])).
% 13.45/5.10  tff(c_34920, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_296, c_82, c_76, c_33874, c_268, c_9692, c_34906])).
% 13.45/5.10  tff(c_34922, plain, $false, inference(negUnitSimplification, [status(thm)], [c_22221, c_34920])).
% 13.45/5.10  tff(c_34924, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(splitRight, [status(thm)], [c_267])).
% 13.45/5.10  tff(c_35092, plain, (![C_771, B_772, A_773]: (v1_xboole_0(C_771) | ~m1_subset_1(C_771, k1_zfmisc_1(k2_zfmisc_1(B_772, A_773))) | ~v1_xboole_0(A_773))), inference(cnfTransformation, [status(thm)], [f_99])).
% 13.45/5.10  tff(c_35112, plain, (v1_xboole_0(k2_funct_1('#skF_3')) | ~v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_34924, c_35092])).
% 13.45/5.10  tff(c_35120, plain, (~v1_xboole_0('#skF_1')), inference(splitLeft, [status(thm)], [c_35112])).
% 13.45/5.10  tff(c_35306, plain, (![A_791, B_792, C_793]: (k2_relset_1(A_791, B_792, C_793)=k2_relat_1(C_793) | ~m1_subset_1(C_793, k1_zfmisc_1(k2_zfmisc_1(A_791, B_792))))), inference(cnfTransformation, [status(thm)], [f_107])).
% 13.45/5.10  tff(c_35315, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_78, c_35306])).
% 13.45/5.10  tff(c_35330, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_74, c_35315])).
% 13.45/5.10  tff(c_34923, plain, (~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_267])).
% 13.45/5.10  tff(c_35370, plain, (![A_797, B_798, C_799]: (k1_relset_1(A_797, B_798, C_799)=k1_relat_1(C_799) | ~m1_subset_1(C_799, k1_zfmisc_1(k2_zfmisc_1(A_797, B_798))))), inference(cnfTransformation, [status(thm)], [f_103])).
% 13.45/5.10  tff(c_35390, plain, (k1_relset_1('#skF_2', '#skF_1', k2_funct_1('#skF_3'))=k1_relat_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_34924, c_35370])).
% 13.45/5.10  tff(c_37507, plain, (![B_874, C_875, A_876]: (k1_xboole_0=B_874 | v1_funct_2(C_875, A_876, B_874) | k1_relset_1(A_876, B_874, C_875)!=A_876 | ~m1_subset_1(C_875, k1_zfmisc_1(k2_zfmisc_1(A_876, B_874))))), inference(cnfTransformation, [status(thm)], [f_125])).
% 13.45/5.10  tff(c_37519, plain, (k1_xboole_0='#skF_1' | v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | k1_relset_1('#skF_2', '#skF_1', k2_funct_1('#skF_3'))!='#skF_2'), inference(resolution, [status(thm)], [c_34924, c_37507])).
% 13.45/5.10  tff(c_37540, plain, (k1_xboole_0='#skF_1' | v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | k1_relat_1(k2_funct_1('#skF_3'))!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_35390, c_37519])).
% 13.45/5.10  tff(c_37541, plain, (k1_xboole_0='#skF_1' | k1_relat_1(k2_funct_1('#skF_3'))!='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_34923, c_37540])).
% 13.45/5.10  tff(c_37551, plain, (k1_relat_1(k2_funct_1('#skF_3'))!='#skF_2'), inference(splitLeft, [status(thm)], [c_37541])).
% 13.45/5.10  tff(c_37554, plain, (k2_relat_1('#skF_3')!='#skF_2' | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_32, c_37551])).
% 13.45/5.10  tff(c_37557, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_34946, c_82, c_76, c_35330, c_37554])).
% 13.45/5.10  tff(c_37558, plain, (k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_37541])).
% 13.45/5.10  tff(c_37599, plain, (v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_37558, c_2])).
% 13.45/5.10  tff(c_37601, plain, $false, inference(negUnitSimplification, [status(thm)], [c_35120, c_37599])).
% 13.45/5.10  tff(c_37603, plain, (v1_xboole_0('#skF_1')), inference(splitRight, [status(thm)], [c_35112])).
% 13.45/5.10  tff(c_37609, plain, (k1_xboole_0='#skF_1'), inference(resolution, [status(thm)], [c_37603, c_150])).
% 13.45/5.10  tff(c_37622, plain, (![B_5]: (k2_zfmisc_1('#skF_1', B_5)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_37609, c_37609, c_12])).
% 13.45/5.10  tff(c_34961, plain, (![B_756, A_757]: (v1_xboole_0(B_756) | ~m1_subset_1(B_756, k1_zfmisc_1(A_757)) | ~v1_xboole_0(A_757))), inference(cnfTransformation, [status(thm)], [f_51])).
% 13.45/5.10  tff(c_34982, plain, (v1_xboole_0('#skF_3') | ~v1_xboole_0(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_78, c_34961])).
% 13.45/5.10  tff(c_35020, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(splitLeft, [status(thm)], [c_34982])).
% 13.45/5.10  tff(c_37778, plain, (~v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_37622, c_35020])).
% 13.45/5.10  tff(c_37782, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_37603, c_37778])).
% 13.45/5.10  tff(c_37783, plain, (v1_xboole_0('#skF_3')), inference(splitRight, [status(thm)], [c_34982])).
% 13.45/5.10  tff(c_37790, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_37783, c_150])).
% 13.45/5.10  tff(c_4, plain, (![A_1]: (r1_tarski(k1_xboole_0, A_1))), inference(cnfTransformation, [status(thm)], [f_28])).
% 13.45/5.10  tff(c_37801, plain, (![A_1]: (r1_tarski('#skF_3', A_1))), inference(demodulation, [status(thm), theory('equality')], [c_37790, c_4])).
% 13.45/5.10  tff(c_34967, plain, (v1_xboole_0(k6_partfun1(k1_xboole_0)) | ~v1_xboole_0(k1_xboole_0)), inference(resolution, [status(thm)], [c_273, c_34961])).
% 13.45/5.10  tff(c_34980, plain, (v1_xboole_0(k6_partfun1(k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_34967])).
% 13.45/5.10  tff(c_34990, plain, (k6_partfun1(k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_34980, c_150])).
% 13.45/5.10  tff(c_37793, plain, (k6_partfun1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_37790, c_37790, c_34990])).
% 13.45/5.10  tff(c_37820, plain, (k2_relat_1('#skF_3')='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_37793, c_83])).
% 13.45/5.10  tff(c_35010, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_34990, c_84])).
% 13.45/5.10  tff(c_37831, plain, (k1_relat_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_37790, c_37790, c_35010])).
% 13.45/5.10  tff(c_39058, plain, (![B_974, A_975]: (v1_funct_2(B_974, k1_relat_1(B_974), A_975) | ~r1_tarski(k2_relat_1(B_974), A_975) | ~v1_funct_1(B_974) | ~v1_relat_1(B_974))), inference(cnfTransformation, [status(thm)], [f_153])).
% 13.45/5.10  tff(c_39067, plain, (![A_975]: (v1_funct_2('#skF_3', '#skF_3', A_975) | ~r1_tarski(k2_relat_1('#skF_3'), A_975) | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_37831, c_39058])).
% 13.45/5.10  tff(c_39073, plain, (![A_975]: (v1_funct_2('#skF_3', '#skF_3', A_975))), inference(demodulation, [status(thm), theory('equality')], [c_34946, c_82, c_37801, c_37820, c_39067])).
% 13.45/5.10  tff(c_37799, plain, (![B_5]: (k2_zfmisc_1('#skF_3', B_5)='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_37790, c_37790, c_12])).
% 13.45/5.10  tff(c_37784, plain, (v1_xboole_0(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(splitRight, [status(thm)], [c_34982])).
% 13.45/5.10  tff(c_37918, plain, (![A_892]: (A_892='#skF_3' | ~v1_xboole_0(A_892))), inference(demodulation, [status(thm), theory('equality')], [c_37790, c_150])).
% 13.45/5.10  tff(c_37925, plain, (k2_zfmisc_1('#skF_1', '#skF_2')='#skF_3'), inference(resolution, [status(thm)], [c_37784, c_37918])).
% 13.45/5.10  tff(c_37810, plain, (![B_5, A_4]: (B_5='#skF_3' | A_4='#skF_3' | k2_zfmisc_1(A_4, B_5)!='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_37790, c_37790, c_37790, c_8])).
% 13.45/5.10  tff(c_37941, plain, ('#skF_2'='#skF_3' | '#skF_3'='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_37925, c_37810])).
% 13.45/5.10  tff(c_37943, plain, ('#skF_3'='#skF_1'), inference(splitLeft, [status(thm)], [c_37941])).
% 13.45/5.10  tff(c_37958, plain, (v1_relat_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_37943, c_34946])).
% 13.45/5.10  tff(c_37965, plain, (v1_funct_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_37943, c_82])).
% 13.45/5.10  tff(c_37950, plain, (k2_relat_1('#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_37943, c_37943, c_37820])).
% 13.45/5.10  tff(c_37951, plain, (k1_relat_1('#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_37943, c_37943, c_37831])).
% 13.45/5.10  tff(c_38025, plain, (v1_funct_2('#skF_1', '#skF_1', k2_relat_1('#skF_1')) | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_37951, c_62])).
% 13.45/5.10  tff(c_38029, plain, (v1_funct_2('#skF_1', '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_37958, c_37965, c_37950, c_38025])).
% 13.45/5.10  tff(c_14, plain, (![A_6]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_6)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 13.45/5.10  tff(c_42, plain, (![A_32]: (v1_funct_2(k1_xboole_0, A_32, k1_xboole_0) | k1_xboole_0=A_32 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k2_zfmisc_1(A_32, k1_xboole_0))))), inference(cnfTransformation, [status(thm)], [f_125])).
% 13.45/5.10  tff(c_86, plain, (![A_32]: (v1_funct_2(k1_xboole_0, A_32, k1_xboole_0) | k1_xboole_0=A_32)), inference(demodulation, [status(thm), theory('equality')], [c_14, c_42])).
% 13.45/5.10  tff(c_37797, plain, (![A_32]: (v1_funct_2('#skF_3', A_32, '#skF_3') | A_32='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_37790, c_37790, c_37790, c_86])).
% 13.45/5.10  tff(c_38179, plain, (![A_32]: (v1_funct_2('#skF_1', A_32, '#skF_1') | A_32='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_37943, c_37943, c_37943, c_37797])).
% 13.45/5.10  tff(c_37956, plain, (v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_37943, c_37783])).
% 13.45/5.10  tff(c_37798, plain, (![A_4]: (k2_zfmisc_1(A_4, '#skF_3')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_37790, c_37790, c_10])).
% 13.45/5.10  tff(c_37946, plain, (![A_4]: (k2_zfmisc_1(A_4, '#skF_1')='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_37943, c_37943, c_37798])).
% 13.45/5.10  tff(c_34977, plain, (v1_xboole_0(k2_funct_1('#skF_3')) | ~v1_xboole_0(k2_zfmisc_1('#skF_2', '#skF_1'))), inference(resolution, [status(thm)], [c_34924, c_34961])).
% 13.45/5.10  tff(c_38199, plain, (v1_xboole_0(k2_funct_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_37956, c_37946, c_37943, c_34977])).
% 13.45/5.10  tff(c_37796, plain, (![A_50]: (A_50='#skF_3' | ~v1_xboole_0(A_50))), inference(demodulation, [status(thm), theory('equality')], [c_37790, c_150])).
% 13.45/5.10  tff(c_37945, plain, (![A_50]: (A_50='#skF_1' | ~v1_xboole_0(A_50))), inference(demodulation, [status(thm), theory('equality')], [c_37943, c_37796])).
% 13.45/5.10  tff(c_38209, plain, (k2_funct_1('#skF_1')='#skF_1'), inference(resolution, [status(thm)], [c_38199, c_37945])).
% 13.45/5.10  tff(c_37960, plain, (~v1_funct_2(k2_funct_1('#skF_1'), '#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_37943, c_34923])).
% 13.45/5.10  tff(c_38212, plain, (~v1_funct_2('#skF_1', '#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_38209, c_37960])).
% 13.45/5.10  tff(c_38245, plain, ('#skF_2'='#skF_1'), inference(resolution, [status(thm)], [c_38179, c_38212])).
% 13.45/5.10  tff(c_38246, plain, (~v1_funct_2('#skF_1', '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_38245, c_38212])).
% 13.45/5.10  tff(c_38251, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_38029, c_38246])).
% 13.45/5.10  tff(c_38252, plain, ('#skF_2'='#skF_3'), inference(splitRight, [status(thm)], [c_37941])).
% 13.45/5.10  tff(c_38255, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_38252, c_34924])).
% 13.45/5.10  tff(c_38260, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_37799, c_38255])).
% 13.45/5.10  tff(c_16, plain, (![B_9, A_7]: (v1_xboole_0(B_9) | ~m1_subset_1(B_9, k1_zfmisc_1(A_7)) | ~v1_xboole_0(A_7))), inference(cnfTransformation, [status(thm)], [f_51])).
% 13.45/5.10  tff(c_38316, plain, (v1_xboole_0(k2_funct_1('#skF_3')) | ~v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_38260, c_16])).
% 13.45/5.10  tff(c_38320, plain, (v1_xboole_0(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_37783, c_38316])).
% 13.45/5.10  tff(c_38330, plain, (k2_funct_1('#skF_3')='#skF_3'), inference(resolution, [status(thm)], [c_38320, c_37796])).
% 13.45/5.10  tff(c_38256, plain, (~v1_funct_2(k2_funct_1('#skF_3'), '#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_38252, c_34923])).
% 13.45/5.10  tff(c_38334, plain, (~v1_funct_2('#skF_3', '#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_38330, c_38256])).
% 13.45/5.10  tff(c_39079, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_39073, c_38334])).
% 13.45/5.10  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 13.45/5.10  
% 13.45/5.10  Inference rules
% 13.45/5.10  ----------------------
% 13.45/5.10  #Ref     : 0
% 13.45/5.10  #Sup     : 11219
% 13.45/5.10  #Fact    : 0
% 13.45/5.10  #Define  : 0
% 13.45/5.10  #Split   : 48
% 13.45/5.10  #Chain   : 0
% 13.45/5.10  #Close   : 0
% 13.45/5.10  
% 13.45/5.10  Ordering : KBO
% 13.45/5.10  
% 13.45/5.10  Simplification rules
% 13.45/5.10  ----------------------
% 13.45/5.10  #Subsume      : 4690
% 13.45/5.10  #Demod        : 6747
% 13.45/5.10  #Tautology    : 2109
% 13.45/5.10  #SimpNegUnit  : 11
% 13.45/5.10  #BackRed      : 233
% 13.45/5.10  
% 13.45/5.10  #Partial instantiations: 0
% 13.45/5.10  #Strategies tried      : 1
% 13.45/5.10  
% 13.45/5.10  Timing (in seconds)
% 13.45/5.10  ----------------------
% 13.45/5.10  Preprocessing        : 0.35
% 13.45/5.10  Parsing              : 0.19
% 13.45/5.10  CNF conversion       : 0.02
% 13.45/5.10  Main loop            : 3.95
% 13.45/5.10  Inferencing          : 0.95
% 13.45/5.10  Reduction            : 1.29
% 13.45/5.10  Demodulation         : 0.96
% 13.45/5.10  BG Simplification    : 0.12
% 13.45/5.10  Subsumption          : 1.35
% 13.45/5.10  Abstraction          : 0.16
% 13.45/5.10  MUC search           : 0.00
% 13.45/5.10  Cooper               : 0.00
% 13.45/5.10  Total                : 4.37
% 13.45/5.10  Index Insertion      : 0.00
% 13.45/5.10  Index Deletion       : 0.00
% 13.45/5.10  Index Matching       : 0.00
% 13.45/5.10  BG Taut test         : 0.00
%------------------------------------------------------------------------------
