%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:10:41 EST 2020

% Result     : Theorem 8.51s
% Output     : CNFRefutation 8.51s
% Verified   : 
% Statistics : Number of formulae       :  123 ( 309 expanded)
%              Number of leaves         :   42 ( 114 expanded)
%              Depth                    :   11
%              Number of atoms          :  190 ( 670 expanded)
%              Number of equality atoms :   54 ( 213 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v1_partfun1 > r2_hidden > r1_tarski > m1_subset_1 > v5_ordinal1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k8_relat_1 > k7_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k8_relat_1,type,(
    k8_relat_1: ( $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(v5_ordinal1,type,(
    v5_ordinal1: $i > $o )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff(v1_partfun1,type,(
    v1_partfun1: ( $i * $i ) > $o )).

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

tff(f_166,negated_conjecture,(
    ~ ! [A] :
        ( ( v1_relat_1(A)
          & v1_funct_1(A) )
       => ( v1_funct_1(A)
          & v1_funct_2(A,k1_relat_1(A),k2_relat_1(A))
          & m1_subset_1(A,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A)))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_funct_2)).

tff(f_80,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => r1_tarski(A,k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_relat_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_28,axiom,(
    ! [A] :
    ? [B] : m1_subset_1(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',existence_m1_subset_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(f_118,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_88,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ( k1_relat_1(A) = k1_xboole_0
          | k2_relat_1(A) = k1_xboole_0 )
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).

tff(f_155,axiom,(
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

tff(f_35,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_58,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

tff(f_137,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => v1_partfun1(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_partfun1)).

tff(f_130,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( ( v1_funct_1(C)
          & v1_partfun1(C,A) )
       => ( v1_funct_1(C)
          & v1_funct_2(C,A,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_funct_2)).

tff(f_114,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_72,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k8_relat_1(k1_xboole_0,A) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t137_relat_1)).

tff(f_68,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(A,k2_relat_1(B))
       => k2_relat_1(k8_relat_1(A,B)) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t120_relat_1)).

tff(f_33,axiom,(
    ! [A] :
    ? [B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
      & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc2_subset_1)).

tff(c_78,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_12743,plain,(
    ! [A_613] :
      ( r1_tarski(A_613,k2_zfmisc_1(k1_relat_1(A_613),k2_relat_1(A_613)))
      | ~ v1_relat_1(A_613) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_12624,plain,(
    ! [A_597,B_598] :
      ( m1_subset_1(A_597,k1_zfmisc_1(B_598))
      | ~ r1_tarski(A_597,B_598) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_2,plain,(
    ! [A_1] : m1_subset_1('#skF_1'(A_1),A_1) ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_10,plain,(
    ! [A_6,B_7] :
      ( r2_hidden(A_6,B_7)
      | v1_xboole_0(B_7)
      | ~ m1_subset_1(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_28,plain,(
    ! [A_21] :
      ( r1_tarski(A_21,k2_zfmisc_1(k1_relat_1(A_21),k2_relat_1(A_21)))
      | ~ v1_relat_1(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_14,plain,(
    ! [A_8,B_9] :
      ( m1_subset_1(A_8,k1_zfmisc_1(B_9))
      | ~ r1_tarski(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_779,plain,(
    ! [A_138,B_139,C_140] :
      ( k1_relset_1(A_138,B_139,C_140) = k1_relat_1(C_140)
      | ~ m1_subset_1(C_140,k1_zfmisc_1(k2_zfmisc_1(A_138,B_139))) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_1025,plain,(
    ! [A_173,B_174,A_175] :
      ( k1_relset_1(A_173,B_174,A_175) = k1_relat_1(A_175)
      | ~ r1_tarski(A_175,k2_zfmisc_1(A_173,B_174)) ) ),
    inference(resolution,[status(thm)],[c_14,c_779])).

tff(c_1044,plain,(
    ! [A_21] :
      ( k1_relset_1(k1_relat_1(A_21),k2_relat_1(A_21),A_21) = k1_relat_1(A_21)
      | ~ v1_relat_1(A_21) ) ),
    inference(resolution,[status(thm)],[c_28,c_1025])).

tff(c_159,plain,(
    ! [A_60] :
      ( k2_relat_1(A_60) != k1_xboole_0
      | k1_xboole_0 = A_60
      | ~ v1_relat_1(A_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_168,plain,
    ( k2_relat_1('#skF_3') != k1_xboole_0
    | k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_78,c_159])).

tff(c_172,plain,(
    k2_relat_1('#skF_3') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_168])).

tff(c_1336,plain,(
    ! [B_194,C_195,A_196] :
      ( k1_xboole_0 = B_194
      | v1_funct_2(C_195,A_196,B_194)
      | k1_relset_1(A_196,B_194,C_195) != A_196
      | ~ m1_subset_1(C_195,k1_zfmisc_1(k2_zfmisc_1(A_196,B_194))) ) ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_3735,plain,(
    ! [B_290,A_291,A_292] :
      ( k1_xboole_0 = B_290
      | v1_funct_2(A_291,A_292,B_290)
      | k1_relset_1(A_292,B_290,A_291) != A_292
      | ~ r1_tarski(A_291,k2_zfmisc_1(A_292,B_290)) ) ),
    inference(resolution,[status(thm)],[c_14,c_1336])).

tff(c_11028,plain,(
    ! [A_427] :
      ( k2_relat_1(A_427) = k1_xboole_0
      | v1_funct_2(A_427,k1_relat_1(A_427),k2_relat_1(A_427))
      | k1_relset_1(k1_relat_1(A_427),k2_relat_1(A_427),A_427) != k1_relat_1(A_427)
      | ~ v1_relat_1(A_427) ) ),
    inference(resolution,[status(thm)],[c_28,c_3735])).

tff(c_76,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_74,plain,
    ( ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))))
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_80,plain,
    ( ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))))
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74])).

tff(c_87,plain,(
    ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_80])).

tff(c_11035,plain,
    ( k2_relat_1('#skF_3') = k1_xboole_0
    | k1_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k1_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_11028,c_87])).

tff(c_11116,plain,
    ( k2_relat_1('#skF_3') = k1_xboole_0
    | k1_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_11035])).

tff(c_11117,plain,(
    k1_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k1_relat_1('#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_172,c_11116])).

tff(c_11127,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1044,c_11117])).

tff(c_11131,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_11127])).

tff(c_11132,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_168])).

tff(c_124,plain,(
    ! [A_54] :
      ( k1_relat_1(A_54) != k1_xboole_0
      | k1_xboole_0 = A_54
      | ~ v1_relat_1(A_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_133,plain,
    ( k1_relat_1('#skF_3') != k1_xboole_0
    | k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_78,c_124])).

tff(c_134,plain,(
    k1_relat_1('#skF_3') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_133])).

tff(c_11136,plain,(
    k1_relat_1('#skF_3') != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_11132,c_134])).

tff(c_8,plain,(
    ! [A_5] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_5)) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_62,plain,(
    ! [A_43] :
      ( v1_funct_2(k1_xboole_0,A_43,k1_xboole_0)
      | k1_xboole_0 = A_43
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(A_43,k1_xboole_0))) ) ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_82,plain,(
    ! [A_43] :
      ( v1_funct_2(k1_xboole_0,A_43,k1_xboole_0)
      | k1_xboole_0 = A_43 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_62])).

tff(c_11182,plain,(
    ! [A_434] :
      ( v1_funct_2('#skF_3',A_434,'#skF_3')
      | A_434 = '#skF_3' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_11132,c_11132,c_11132,c_82])).

tff(c_11133,plain,(
    k2_relat_1('#skF_3') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_168])).

tff(c_11156,plain,(
    k2_relat_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_11132,c_11133])).

tff(c_11157,plain,(
    ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_11156,c_87])).

tff(c_11185,plain,(
    k1_relat_1('#skF_3') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_11182,c_11157])).

tff(c_11189,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_11136,c_11185])).

tff(c_11190,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_133])).

tff(c_11200,plain,(
    ! [A_5] : m1_subset_1('#skF_3',k1_zfmisc_1(A_5)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_11190,c_8])).

tff(c_11421,plain,(
    ! [C_469,B_470,A_471] :
      ( ~ v1_xboole_0(C_469)
      | ~ m1_subset_1(B_470,k1_zfmisc_1(C_469))
      | ~ r2_hidden(A_471,B_470) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_11434,plain,(
    ! [A_5,A_471] :
      ( ~ v1_xboole_0(A_5)
      | ~ r2_hidden(A_471,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_11200,c_11421])).

tff(c_11439,plain,(
    ! [A_472] : ~ r2_hidden(A_472,'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_11434])).

tff(c_11444,plain,(
    ! [A_6] :
      ( v1_xboole_0('#skF_3')
      | ~ m1_subset_1(A_6,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_10,c_11439])).

tff(c_11463,plain,(
    ! [A_476] : ~ m1_subset_1(A_476,'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_11444])).

tff(c_11468,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_2,c_11463])).

tff(c_11469,plain,(
    v1_xboole_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_11444])).

tff(c_11191,plain,(
    k1_relat_1('#skF_3') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_133])).

tff(c_11211,plain,(
    k1_relat_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_11190,c_11191])).

tff(c_11596,plain,(
    ! [C_503,A_504,B_505] :
      ( v1_partfun1(C_503,A_504)
      | ~ m1_subset_1(C_503,k1_zfmisc_1(k2_zfmisc_1(A_504,B_505)))
      | ~ v1_xboole_0(A_504) ) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_11675,plain,(
    ! [A_520,A_521,B_522] :
      ( v1_partfun1(A_520,A_521)
      | ~ v1_xboole_0(A_521)
      | ~ r1_tarski(A_520,k2_zfmisc_1(A_521,B_522)) ) ),
    inference(resolution,[status(thm)],[c_14,c_11596])).

tff(c_11738,plain,(
    ! [A_526] :
      ( v1_partfun1(A_526,k1_relat_1(A_526))
      | ~ v1_xboole_0(k1_relat_1(A_526))
      | ~ v1_relat_1(A_526) ) ),
    inference(resolution,[status(thm)],[c_28,c_11675])).

tff(c_11747,plain,
    ( v1_partfun1('#skF_3','#skF_3')
    | ~ v1_xboole_0(k1_relat_1('#skF_3'))
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_11211,c_11738])).

tff(c_11749,plain,(
    v1_partfun1('#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_11469,c_11211,c_11747])).

tff(c_12519,plain,(
    ! [C_581,A_582,B_583] :
      ( v1_funct_2(C_581,A_582,B_583)
      | ~ v1_partfun1(C_581,A_582)
      | ~ v1_funct_1(C_581)
      | ~ m1_subset_1(C_581,k1_zfmisc_1(k2_zfmisc_1(A_582,B_583))) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_12531,plain,(
    ! [A_582,B_583] :
      ( v1_funct_2('#skF_3',A_582,B_583)
      | ~ v1_partfun1('#skF_3',A_582)
      | ~ v1_funct_1('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_11200,c_12519])).

tff(c_12551,plain,(
    ! [A_584,B_585] :
      ( v1_funct_2('#skF_3',A_584,B_585)
      | ~ v1_partfun1('#skF_3',A_584) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_12531])).

tff(c_11295,plain,(
    ! [C_454,A_455,B_456] :
      ( v1_relat_1(C_454)
      | ~ m1_subset_1(C_454,k1_zfmisc_1(k2_zfmisc_1(A_455,B_456))) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_11320,plain,(
    ! [A_455,B_456] : v1_relat_1('#skF_1'(k1_zfmisc_1(k2_zfmisc_1(A_455,B_456)))) ),
    inference(resolution,[status(thm)],[c_2,c_11295])).

tff(c_11375,plain,(
    ! [A_463,B_464] : v1_relat_1('#skF_1'(k1_zfmisc_1(k2_zfmisc_1(A_463,B_464)))) ),
    inference(resolution,[status(thm)],[c_2,c_11295])).

tff(c_24,plain,(
    ! [A_19] :
      ( k8_relat_1(k1_xboole_0,A_19) = k1_xboole_0
      | ~ v1_relat_1(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_11195,plain,(
    ! [A_19] :
      ( k8_relat_1('#skF_3',A_19) = '#skF_3'
      | ~ v1_relat_1(A_19) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_11190,c_11190,c_24])).

tff(c_11390,plain,(
    ! [A_463,B_464] : k8_relat_1('#skF_3','#skF_1'(k1_zfmisc_1(k2_zfmisc_1(A_463,B_464)))) = '#skF_3' ),
    inference(resolution,[status(thm)],[c_11375,c_11195])).

tff(c_11251,plain,(
    ! [A_444,B_445] :
      ( r1_tarski(A_444,B_445)
      | ~ m1_subset_1(A_444,k1_zfmisc_1(B_445)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_11269,plain,(
    ! [A_5] : r1_tarski('#skF_3',A_5) ),
    inference(resolution,[status(thm)],[c_11200,c_11251])).

tff(c_11780,plain,(
    ! [A_531,B_532] :
      ( k2_relat_1(k8_relat_1(A_531,B_532)) = A_531
      | ~ r1_tarski(A_531,k2_relat_1(B_532))
      | ~ v1_relat_1(B_532) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_11796,plain,(
    ! [B_533] :
      ( k2_relat_1(k8_relat_1('#skF_3',B_533)) = '#skF_3'
      | ~ v1_relat_1(B_533) ) ),
    inference(resolution,[status(thm)],[c_11269,c_11780])).

tff(c_11814,plain,(
    ! [A_463,B_464] :
      ( k2_relat_1('#skF_3') = '#skF_3'
      | ~ v1_relat_1('#skF_1'(k1_zfmisc_1(k2_zfmisc_1(A_463,B_464)))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_11390,c_11796])).

tff(c_11827,plain,(
    k2_relat_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_11320,c_11814])).

tff(c_11212,plain,(
    ~ v1_funct_2('#skF_3','#skF_3',k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_11211,c_87])).

tff(c_11834,plain,(
    ~ v1_funct_2('#skF_3','#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_11827,c_11212])).

tff(c_12554,plain,(
    ~ v1_partfun1('#skF_3','#skF_3') ),
    inference(resolution,[status(thm)],[c_12551,c_11834])).

tff(c_12558,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_11749,c_12554])).

tff(c_12559,plain,(
    ! [A_5] : ~ v1_xboole_0(A_5) ),
    inference(splitRight,[status(thm)],[c_11434])).

tff(c_4,plain,(
    ! [A_3] : v1_xboole_0('#skF_2'(A_3)) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_12562,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_12559,c_4])).

tff(c_12563,plain,(
    ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3')))) ),
    inference(splitRight,[status(thm)],[c_80])).

tff(c_12631,plain,(
    ~ r1_tarski('#skF_3',k2_zfmisc_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))) ),
    inference(resolution,[status(thm)],[c_12624,c_12563])).

tff(c_12746,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_12743,c_12631])).

tff(c_12750,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_12746])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n019.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 20:04:22 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.51/3.00  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.51/3.01  
% 8.51/3.01  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.51/3.01  %$ v1_funct_2 > v5_relat_1 > v1_partfun1 > r2_hidden > r1_tarski > m1_subset_1 > v5_ordinal1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k8_relat_1 > k7_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1 > #skF_3
% 8.51/3.01  
% 8.51/3.01  %Foreground sorts:
% 8.51/3.01  
% 8.51/3.01  
% 8.51/3.01  %Background operators:
% 8.51/3.01  
% 8.51/3.01  
% 8.51/3.01  %Foreground operators:
% 8.51/3.01  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 8.51/3.01  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 8.51/3.01  tff('#skF_2', type, '#skF_2': $i > $i).
% 8.51/3.01  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.51/3.01  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 8.51/3.01  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 8.51/3.01  tff('#skF_1', type, '#skF_1': $i > $i).
% 8.51/3.01  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 8.51/3.01  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 8.51/3.01  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 8.51/3.01  tff(v5_ordinal1, type, v5_ordinal1: $i > $o).
% 8.51/3.01  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 8.51/3.01  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 8.51/3.01  tff('#skF_3', type, '#skF_3': $i).
% 8.51/3.01  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 8.51/3.01  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 8.51/3.01  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 8.51/3.01  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.51/3.01  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 8.51/3.01  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 8.51/3.01  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 8.51/3.01  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 8.51/3.01  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.51/3.01  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 8.51/3.01  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 8.51/3.01  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 8.51/3.01  
% 8.51/3.03  tff(f_166, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => ((v1_funct_1(A) & v1_funct_2(A, k1_relat_1(A), k2_relat_1(A))) & m1_subset_1(A, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_funct_2)).
% 8.51/3.03  tff(f_80, axiom, (![A]: (v1_relat_1(A) => r1_tarski(A, k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t21_relat_1)).
% 8.51/3.03  tff(f_45, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 8.51/3.03  tff(f_28, axiom, (![A]: (?[B]: m1_subset_1(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', existence_m1_subset_1)).
% 8.51/3.03  tff(f_41, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 8.51/3.03  tff(f_118, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 8.51/3.03  tff(f_88, axiom, (![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_relat_1)).
% 8.51/3.03  tff(f_155, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 8.51/3.03  tff(f_35, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 8.51/3.03  tff(f_58, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_subset)).
% 8.51/3.03  tff(f_137, axiom, (![A, B]: (v1_xboole_0(A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_partfun1(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_partfun1)).
% 8.51/3.03  tff(f_130, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v1_partfun1(C, A)) => (v1_funct_1(C) & v1_funct_2(C, A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_funct_2)).
% 8.51/3.03  tff(f_114, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 8.51/3.03  tff(f_72, axiom, (![A]: (v1_relat_1(A) => (k8_relat_1(k1_xboole_0, A) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t137_relat_1)).
% 8.51/3.03  tff(f_68, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(A, k2_relat_1(B)) => (k2_relat_1(k8_relat_1(A, B)) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t120_relat_1)).
% 8.51/3.03  tff(f_33, axiom, (![A]: (?[B]: (m1_subset_1(B, k1_zfmisc_1(A)) & v1_xboole_0(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', rc2_subset_1)).
% 8.51/3.03  tff(c_78, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_166])).
% 8.51/3.03  tff(c_12743, plain, (![A_613]: (r1_tarski(A_613, k2_zfmisc_1(k1_relat_1(A_613), k2_relat_1(A_613))) | ~v1_relat_1(A_613))), inference(cnfTransformation, [status(thm)], [f_80])).
% 8.51/3.03  tff(c_12624, plain, (![A_597, B_598]: (m1_subset_1(A_597, k1_zfmisc_1(B_598)) | ~r1_tarski(A_597, B_598))), inference(cnfTransformation, [status(thm)], [f_45])).
% 8.51/3.03  tff(c_2, plain, (![A_1]: (m1_subset_1('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_28])).
% 8.51/3.03  tff(c_10, plain, (![A_6, B_7]: (r2_hidden(A_6, B_7) | v1_xboole_0(B_7) | ~m1_subset_1(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_41])).
% 8.51/3.03  tff(c_28, plain, (![A_21]: (r1_tarski(A_21, k2_zfmisc_1(k1_relat_1(A_21), k2_relat_1(A_21))) | ~v1_relat_1(A_21))), inference(cnfTransformation, [status(thm)], [f_80])).
% 8.51/3.03  tff(c_14, plain, (![A_8, B_9]: (m1_subset_1(A_8, k1_zfmisc_1(B_9)) | ~r1_tarski(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_45])).
% 8.51/3.03  tff(c_779, plain, (![A_138, B_139, C_140]: (k1_relset_1(A_138, B_139, C_140)=k1_relat_1(C_140) | ~m1_subset_1(C_140, k1_zfmisc_1(k2_zfmisc_1(A_138, B_139))))), inference(cnfTransformation, [status(thm)], [f_118])).
% 8.51/3.03  tff(c_1025, plain, (![A_173, B_174, A_175]: (k1_relset_1(A_173, B_174, A_175)=k1_relat_1(A_175) | ~r1_tarski(A_175, k2_zfmisc_1(A_173, B_174)))), inference(resolution, [status(thm)], [c_14, c_779])).
% 8.51/3.03  tff(c_1044, plain, (![A_21]: (k1_relset_1(k1_relat_1(A_21), k2_relat_1(A_21), A_21)=k1_relat_1(A_21) | ~v1_relat_1(A_21))), inference(resolution, [status(thm)], [c_28, c_1025])).
% 8.51/3.03  tff(c_159, plain, (![A_60]: (k2_relat_1(A_60)!=k1_xboole_0 | k1_xboole_0=A_60 | ~v1_relat_1(A_60))), inference(cnfTransformation, [status(thm)], [f_88])).
% 8.51/3.03  tff(c_168, plain, (k2_relat_1('#skF_3')!=k1_xboole_0 | k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_78, c_159])).
% 8.51/3.03  tff(c_172, plain, (k2_relat_1('#skF_3')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_168])).
% 8.51/3.03  tff(c_1336, plain, (![B_194, C_195, A_196]: (k1_xboole_0=B_194 | v1_funct_2(C_195, A_196, B_194) | k1_relset_1(A_196, B_194, C_195)!=A_196 | ~m1_subset_1(C_195, k1_zfmisc_1(k2_zfmisc_1(A_196, B_194))))), inference(cnfTransformation, [status(thm)], [f_155])).
% 8.51/3.03  tff(c_3735, plain, (![B_290, A_291, A_292]: (k1_xboole_0=B_290 | v1_funct_2(A_291, A_292, B_290) | k1_relset_1(A_292, B_290, A_291)!=A_292 | ~r1_tarski(A_291, k2_zfmisc_1(A_292, B_290)))), inference(resolution, [status(thm)], [c_14, c_1336])).
% 8.51/3.03  tff(c_11028, plain, (![A_427]: (k2_relat_1(A_427)=k1_xboole_0 | v1_funct_2(A_427, k1_relat_1(A_427), k2_relat_1(A_427)) | k1_relset_1(k1_relat_1(A_427), k2_relat_1(A_427), A_427)!=k1_relat_1(A_427) | ~v1_relat_1(A_427))), inference(resolution, [status(thm)], [c_28, c_3735])).
% 8.51/3.03  tff(c_76, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_166])).
% 8.51/3.03  tff(c_74, plain, (~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3')))) | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_166])).
% 8.51/3.03  tff(c_80, plain, (~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3')))) | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_74])).
% 8.51/3.03  tff(c_87, plain, (~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_80])).
% 8.51/3.03  tff(c_11035, plain, (k2_relat_1('#skF_3')=k1_xboole_0 | k1_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k1_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_11028, c_87])).
% 8.51/3.03  tff(c_11116, plain, (k2_relat_1('#skF_3')=k1_xboole_0 | k1_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_11035])).
% 8.51/3.03  tff(c_11117, plain, (k1_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k1_relat_1('#skF_3')), inference(negUnitSimplification, [status(thm)], [c_172, c_11116])).
% 8.51/3.03  tff(c_11127, plain, (~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1044, c_11117])).
% 8.51/3.03  tff(c_11131, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_78, c_11127])).
% 8.51/3.03  tff(c_11132, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_168])).
% 8.51/3.03  tff(c_124, plain, (![A_54]: (k1_relat_1(A_54)!=k1_xboole_0 | k1_xboole_0=A_54 | ~v1_relat_1(A_54))), inference(cnfTransformation, [status(thm)], [f_88])).
% 8.51/3.03  tff(c_133, plain, (k1_relat_1('#skF_3')!=k1_xboole_0 | k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_78, c_124])).
% 8.51/3.03  tff(c_134, plain, (k1_relat_1('#skF_3')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_133])).
% 8.51/3.03  tff(c_11136, plain, (k1_relat_1('#skF_3')!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_11132, c_134])).
% 8.51/3.03  tff(c_8, plain, (![A_5]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_5)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 8.51/3.03  tff(c_62, plain, (![A_43]: (v1_funct_2(k1_xboole_0, A_43, k1_xboole_0) | k1_xboole_0=A_43 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k2_zfmisc_1(A_43, k1_xboole_0))))), inference(cnfTransformation, [status(thm)], [f_155])).
% 8.51/3.03  tff(c_82, plain, (![A_43]: (v1_funct_2(k1_xboole_0, A_43, k1_xboole_0) | k1_xboole_0=A_43)), inference(demodulation, [status(thm), theory('equality')], [c_8, c_62])).
% 8.51/3.03  tff(c_11182, plain, (![A_434]: (v1_funct_2('#skF_3', A_434, '#skF_3') | A_434='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_11132, c_11132, c_11132, c_82])).
% 8.51/3.03  tff(c_11133, plain, (k2_relat_1('#skF_3')=k1_xboole_0), inference(splitRight, [status(thm)], [c_168])).
% 8.51/3.03  tff(c_11156, plain, (k2_relat_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_11132, c_11133])).
% 8.51/3.03  tff(c_11157, plain, (~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_11156, c_87])).
% 8.51/3.03  tff(c_11185, plain, (k1_relat_1('#skF_3')='#skF_3'), inference(resolution, [status(thm)], [c_11182, c_11157])).
% 8.51/3.03  tff(c_11189, plain, $false, inference(negUnitSimplification, [status(thm)], [c_11136, c_11185])).
% 8.51/3.03  tff(c_11190, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_133])).
% 8.51/3.03  tff(c_11200, plain, (![A_5]: (m1_subset_1('#skF_3', k1_zfmisc_1(A_5)))), inference(demodulation, [status(thm), theory('equality')], [c_11190, c_8])).
% 8.51/3.03  tff(c_11421, plain, (![C_469, B_470, A_471]: (~v1_xboole_0(C_469) | ~m1_subset_1(B_470, k1_zfmisc_1(C_469)) | ~r2_hidden(A_471, B_470))), inference(cnfTransformation, [status(thm)], [f_58])).
% 8.51/3.03  tff(c_11434, plain, (![A_5, A_471]: (~v1_xboole_0(A_5) | ~r2_hidden(A_471, '#skF_3'))), inference(resolution, [status(thm)], [c_11200, c_11421])).
% 8.51/3.03  tff(c_11439, plain, (![A_472]: (~r2_hidden(A_472, '#skF_3'))), inference(splitLeft, [status(thm)], [c_11434])).
% 8.51/3.03  tff(c_11444, plain, (![A_6]: (v1_xboole_0('#skF_3') | ~m1_subset_1(A_6, '#skF_3'))), inference(resolution, [status(thm)], [c_10, c_11439])).
% 8.51/3.03  tff(c_11463, plain, (![A_476]: (~m1_subset_1(A_476, '#skF_3'))), inference(splitLeft, [status(thm)], [c_11444])).
% 8.51/3.03  tff(c_11468, plain, $false, inference(resolution, [status(thm)], [c_2, c_11463])).
% 8.51/3.03  tff(c_11469, plain, (v1_xboole_0('#skF_3')), inference(splitRight, [status(thm)], [c_11444])).
% 8.51/3.03  tff(c_11191, plain, (k1_relat_1('#skF_3')=k1_xboole_0), inference(splitRight, [status(thm)], [c_133])).
% 8.51/3.03  tff(c_11211, plain, (k1_relat_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_11190, c_11191])).
% 8.51/3.03  tff(c_11596, plain, (![C_503, A_504, B_505]: (v1_partfun1(C_503, A_504) | ~m1_subset_1(C_503, k1_zfmisc_1(k2_zfmisc_1(A_504, B_505))) | ~v1_xboole_0(A_504))), inference(cnfTransformation, [status(thm)], [f_137])).
% 8.51/3.03  tff(c_11675, plain, (![A_520, A_521, B_522]: (v1_partfun1(A_520, A_521) | ~v1_xboole_0(A_521) | ~r1_tarski(A_520, k2_zfmisc_1(A_521, B_522)))), inference(resolution, [status(thm)], [c_14, c_11596])).
% 8.51/3.03  tff(c_11738, plain, (![A_526]: (v1_partfun1(A_526, k1_relat_1(A_526)) | ~v1_xboole_0(k1_relat_1(A_526)) | ~v1_relat_1(A_526))), inference(resolution, [status(thm)], [c_28, c_11675])).
% 8.51/3.03  tff(c_11747, plain, (v1_partfun1('#skF_3', '#skF_3') | ~v1_xboole_0(k1_relat_1('#skF_3')) | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_11211, c_11738])).
% 8.51/3.03  tff(c_11749, plain, (v1_partfun1('#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_11469, c_11211, c_11747])).
% 8.51/3.03  tff(c_12519, plain, (![C_581, A_582, B_583]: (v1_funct_2(C_581, A_582, B_583) | ~v1_partfun1(C_581, A_582) | ~v1_funct_1(C_581) | ~m1_subset_1(C_581, k1_zfmisc_1(k2_zfmisc_1(A_582, B_583))))), inference(cnfTransformation, [status(thm)], [f_130])).
% 8.51/3.03  tff(c_12531, plain, (![A_582, B_583]: (v1_funct_2('#skF_3', A_582, B_583) | ~v1_partfun1('#skF_3', A_582) | ~v1_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_11200, c_12519])).
% 8.51/3.03  tff(c_12551, plain, (![A_584, B_585]: (v1_funct_2('#skF_3', A_584, B_585) | ~v1_partfun1('#skF_3', A_584))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_12531])).
% 8.51/3.03  tff(c_11295, plain, (![C_454, A_455, B_456]: (v1_relat_1(C_454) | ~m1_subset_1(C_454, k1_zfmisc_1(k2_zfmisc_1(A_455, B_456))))), inference(cnfTransformation, [status(thm)], [f_114])).
% 8.51/3.03  tff(c_11320, plain, (![A_455, B_456]: (v1_relat_1('#skF_1'(k1_zfmisc_1(k2_zfmisc_1(A_455, B_456)))))), inference(resolution, [status(thm)], [c_2, c_11295])).
% 8.51/3.03  tff(c_11375, plain, (![A_463, B_464]: (v1_relat_1('#skF_1'(k1_zfmisc_1(k2_zfmisc_1(A_463, B_464)))))), inference(resolution, [status(thm)], [c_2, c_11295])).
% 8.51/3.03  tff(c_24, plain, (![A_19]: (k8_relat_1(k1_xboole_0, A_19)=k1_xboole_0 | ~v1_relat_1(A_19))), inference(cnfTransformation, [status(thm)], [f_72])).
% 8.51/3.03  tff(c_11195, plain, (![A_19]: (k8_relat_1('#skF_3', A_19)='#skF_3' | ~v1_relat_1(A_19))), inference(demodulation, [status(thm), theory('equality')], [c_11190, c_11190, c_24])).
% 8.51/3.03  tff(c_11390, plain, (![A_463, B_464]: (k8_relat_1('#skF_3', '#skF_1'(k1_zfmisc_1(k2_zfmisc_1(A_463, B_464))))='#skF_3')), inference(resolution, [status(thm)], [c_11375, c_11195])).
% 8.51/3.03  tff(c_11251, plain, (![A_444, B_445]: (r1_tarski(A_444, B_445) | ~m1_subset_1(A_444, k1_zfmisc_1(B_445)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 8.51/3.03  tff(c_11269, plain, (![A_5]: (r1_tarski('#skF_3', A_5))), inference(resolution, [status(thm)], [c_11200, c_11251])).
% 8.51/3.03  tff(c_11780, plain, (![A_531, B_532]: (k2_relat_1(k8_relat_1(A_531, B_532))=A_531 | ~r1_tarski(A_531, k2_relat_1(B_532)) | ~v1_relat_1(B_532))), inference(cnfTransformation, [status(thm)], [f_68])).
% 8.51/3.03  tff(c_11796, plain, (![B_533]: (k2_relat_1(k8_relat_1('#skF_3', B_533))='#skF_3' | ~v1_relat_1(B_533))), inference(resolution, [status(thm)], [c_11269, c_11780])).
% 8.51/3.03  tff(c_11814, plain, (![A_463, B_464]: (k2_relat_1('#skF_3')='#skF_3' | ~v1_relat_1('#skF_1'(k1_zfmisc_1(k2_zfmisc_1(A_463, B_464)))))), inference(superposition, [status(thm), theory('equality')], [c_11390, c_11796])).
% 8.51/3.03  tff(c_11827, plain, (k2_relat_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_11320, c_11814])).
% 8.51/3.03  tff(c_11212, plain, (~v1_funct_2('#skF_3', '#skF_3', k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_11211, c_87])).
% 8.51/3.03  tff(c_11834, plain, (~v1_funct_2('#skF_3', '#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_11827, c_11212])).
% 8.51/3.03  tff(c_12554, plain, (~v1_partfun1('#skF_3', '#skF_3')), inference(resolution, [status(thm)], [c_12551, c_11834])).
% 8.51/3.03  tff(c_12558, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_11749, c_12554])).
% 8.51/3.03  tff(c_12559, plain, (![A_5]: (~v1_xboole_0(A_5))), inference(splitRight, [status(thm)], [c_11434])).
% 8.51/3.03  tff(c_4, plain, (![A_3]: (v1_xboole_0('#skF_2'(A_3)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 8.51/3.03  tff(c_12562, plain, $false, inference(negUnitSimplification, [status(thm)], [c_12559, c_4])).
% 8.51/3.03  tff(c_12563, plain, (~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'))))), inference(splitRight, [status(thm)], [c_80])).
% 8.51/3.03  tff(c_12631, plain, (~r1_tarski('#skF_3', k2_zfmisc_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3')))), inference(resolution, [status(thm)], [c_12624, c_12563])).
% 8.51/3.03  tff(c_12746, plain, (~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_12743, c_12631])).
% 8.51/3.03  tff(c_12750, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_78, c_12746])).
% 8.51/3.03  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.51/3.03  
% 8.51/3.03  Inference rules
% 8.51/3.03  ----------------------
% 8.51/3.03  #Ref     : 0
% 8.51/3.03  #Sup     : 2864
% 8.51/3.03  #Fact    : 0
% 8.51/3.03  #Define  : 0
% 8.51/3.03  #Split   : 20
% 8.51/3.03  #Chain   : 0
% 8.51/3.03  #Close   : 0
% 8.51/3.03  
% 8.51/3.03  Ordering : KBO
% 8.51/3.03  
% 8.51/3.03  Simplification rules
% 8.51/3.03  ----------------------
% 8.51/3.03  #Subsume      : 811
% 8.51/3.03  #Demod        : 3122
% 8.51/3.03  #Tautology    : 1048
% 8.51/3.03  #SimpNegUnit  : 104
% 8.51/3.03  #BackRed      : 51
% 8.51/3.03  
% 8.51/3.03  #Partial instantiations: 0
% 8.51/3.03  #Strategies tried      : 1
% 8.51/3.03  
% 8.51/3.03  Timing (in seconds)
% 8.51/3.03  ----------------------
% 8.51/3.03  Preprocessing        : 0.35
% 8.51/3.03  Parsing              : 0.19
% 8.51/3.03  CNF conversion       : 0.02
% 8.51/3.03  Main loop            : 1.91
% 8.51/3.03  Inferencing          : 0.57
% 8.51/3.03  Reduction            : 0.71
% 8.51/3.03  Demodulation         : 0.53
% 8.51/3.04  BG Simplification    : 0.06
% 8.51/3.04  Subsumption          : 0.44
% 8.51/3.04  Abstraction          : 0.08
% 8.51/3.04  MUC search           : 0.00
% 8.51/3.04  Cooper               : 0.00
% 8.51/3.04  Total                : 2.30
% 8.51/3.04  Index Insertion      : 0.00
% 8.51/3.04  Index Deletion       : 0.00
% 8.51/3.04  Index Matching       : 0.00
% 8.51/3.04  BG Taut test         : 0.00
%------------------------------------------------------------------------------
