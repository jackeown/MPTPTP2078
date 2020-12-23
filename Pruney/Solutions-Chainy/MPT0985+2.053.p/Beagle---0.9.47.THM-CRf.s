%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:12:34 EST 2020

% Result     : Theorem 18.76s
% Output     : CNFRefutation 18.86s
% Verified   : 
% Statistics : Number of formulae       :  211 ( 822 expanded)
%              Number of leaves         :   57 ( 294 expanded)
%              Depth                    :   13
%              Number of atoms          :  354 (2170 expanded)
%              Number of equality atoms :  105 ( 536 expanded)
%              Maximal formula depth    :   12 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r2_hidden > r1_tarski > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k9_relat_1 > k7_relat_1 > k5_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k6_relat_1 > k6_partfun1 > k4_relat_1 > k2_subset_1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1

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

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

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

tff('#skF_4',type,(
    '#skF_4': $i )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k4_relat_1,type,(
    k4_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_262,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( ( v2_funct_1(C)
            & k2_relset_1(A,B,C) = B )
         => ( v1_funct_1(k2_funct_1(C))
            & v1_funct_2(k2_funct_1(C),B,A)
            & m1_subset_1(k2_funct_1(C),k1_zfmisc_1(k2_zfmisc_1(B,A))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_funct_2)).

tff(f_196,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_190,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_84,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ( k1_relat_1(A) = k1_xboole_0
          | k2_relat_1(A) = k1_xboole_0 )
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).

tff(f_119,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).

tff(f_200,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_111,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => k2_funct_1(A) = k4_relat_1(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_funct_1)).

tff(f_58,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => v1_relat_1(k4_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_relat_1)).

tff(f_76,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( k2_relat_1(A) = k1_relat_1(k4_relat_1(A))
        & k1_relat_1(A) = k2_relat_1(k4_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_relat_1)).

tff(f_226,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_funct_1(A)
        & v1_funct_2(A,k1_relat_1(A),k2_relat_1(A))
        & m1_subset_1(A,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A)))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_funct_2)).

tff(f_54,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_245,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r1_tarski(B,C)
       => ( ( B = k1_xboole_0
            & A != k1_xboole_0 )
          | ( v1_funct_1(D)
            & v1_funct_2(D,A,C)
            & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,C))) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_funct_2)).

tff(f_33,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_216,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_99,axiom,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_relat_1)).

tff(f_94,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_35,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_37,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_48,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

tff(f_41,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_127,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v2_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_funct_1)).

tff(f_214,axiom,(
    ! [A] :
      ( v1_partfun1(k6_partfun1(A),A)
      & m1_subset_1(k6_partfun1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_partfun1)).

tff(f_210,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( ( v1_funct_1(C)
          & v1_partfun1(C,A) )
       => ( v1_funct_1(C)
          & v1_funct_2(C,A,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_funct_2)).

tff(c_118,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_4') = '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_262])).

tff(c_122,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_262])).

tff(c_25876,plain,(
    ! [C_1032,A_1033,B_1034] :
      ( v4_relat_1(C_1032,A_1033)
      | ~ m1_subset_1(C_1032,k1_zfmisc_1(k2_zfmisc_1(A_1033,B_1034))) ) ),
    inference(cnfTransformation,[status(thm)],[f_196])).

tff(c_25902,plain,(
    v4_relat_1('#skF_4','#skF_2') ),
    inference(resolution,[status(thm)],[c_122,c_25876])).

tff(c_25445,plain,(
    ! [C_990,A_991,B_992] :
      ( v1_relat_1(C_990)
      | ~ m1_subset_1(C_990,k1_zfmisc_1(k2_zfmisc_1(A_991,B_992))) ) ),
    inference(cnfTransformation,[status(thm)],[f_190])).

tff(c_25467,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_122,c_25445])).

tff(c_38,plain,(
    ! [A_21] :
      ( k1_relat_1(A_21) != k1_xboole_0
      | k1_xboole_0 = A_21
      | ~ v1_relat_1(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_25483,plain,
    ( k1_relat_1('#skF_4') != k1_xboole_0
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_25467,c_38])).

tff(c_25485,plain,(
    k1_relat_1('#skF_4') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_25483])).

tff(c_126,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_262])).

tff(c_56,plain,(
    ! [A_27] :
      ( v1_funct_1(k2_funct_1(A_27))
      | ~ v1_funct_1(A_27)
      | ~ v1_relat_1(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_116,plain,
    ( ~ m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2')))
    | ~ v1_funct_2(k2_funct_1('#skF_4'),'#skF_3','#skF_2')
    | ~ v1_funct_1(k2_funct_1('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_262])).

tff(c_275,plain,(
    ~ v1_funct_1(k2_funct_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_116])).

tff(c_278,plain,
    ( ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_56,c_275])).

tff(c_281,plain,(
    ~ v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_126,c_278])).

tff(c_593,plain,(
    ! [C_102,A_103,B_104] :
      ( v1_relat_1(C_102)
      | ~ m1_subset_1(C_102,k1_zfmisc_1(k2_zfmisc_1(A_103,B_104))) ) ),
    inference(cnfTransformation,[status(thm)],[f_190])).

tff(c_603,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_122,c_593])).

tff(c_614,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_281,c_603])).

tff(c_616,plain,(
    v1_funct_1(k2_funct_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_116])).

tff(c_26818,plain,(
    ! [A_1073,B_1074,C_1075] :
      ( k2_relset_1(A_1073,B_1074,C_1075) = k2_relat_1(C_1075)
      | ~ m1_subset_1(C_1075,k1_zfmisc_1(k2_zfmisc_1(A_1073,B_1074))) ) ),
    inference(cnfTransformation,[status(thm)],[f_200])).

tff(c_26837,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_122,c_26818])).

tff(c_26851,plain,(
    k2_relat_1('#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_118,c_26837])).

tff(c_1452,plain,(
    ! [C_198,A_199,B_200] :
      ( v4_relat_1(C_198,A_199)
      | ~ m1_subset_1(C_198,k1_zfmisc_1(k2_zfmisc_1(A_199,B_200))) ) ),
    inference(cnfTransformation,[status(thm)],[f_196])).

tff(c_1474,plain,(
    v4_relat_1('#skF_4','#skF_2') ),
    inference(resolution,[status(thm)],[c_122,c_1452])).

tff(c_900,plain,(
    ! [C_130,A_131,B_132] :
      ( v1_relat_1(C_130)
      | ~ m1_subset_1(C_130,k1_zfmisc_1(k2_zfmisc_1(A_131,B_132))) ) ),
    inference(cnfTransformation,[status(thm)],[f_190])).

tff(c_918,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_122,c_900])).

tff(c_934,plain,
    ( k1_relat_1('#skF_4') != k1_xboole_0
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_918,c_38])).

tff(c_953,plain,(
    k1_relat_1('#skF_4') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_934])).

tff(c_120,plain,(
    v2_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_262])).

tff(c_1508,plain,(
    ! [A_206] :
      ( k4_relat_1(A_206) = k2_funct_1(A_206)
      | ~ v2_funct_1(A_206)
      | ~ v1_funct_1(A_206)
      | ~ v1_relat_1(A_206) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_1517,plain,
    ( k4_relat_1('#skF_4') = k2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_120,c_1508])).

tff(c_1526,plain,(
    k4_relat_1('#skF_4') = k2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_918,c_126,c_1517])).

tff(c_24,plain,(
    ! [A_15] :
      ( v1_relat_1(k4_relat_1(A_15))
      | ~ v1_relat_1(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_1536,plain,
    ( v1_relat_1(k2_funct_1('#skF_4'))
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1526,c_24])).

tff(c_1544,plain,(
    v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_918,c_1536])).

tff(c_32,plain,(
    ! [A_20] :
      ( k2_relat_1(k4_relat_1(A_20)) = k1_relat_1(A_20)
      | ~ v1_relat_1(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_1530,plain,
    ( k2_relat_1(k2_funct_1('#skF_4')) = k1_relat_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1526,c_32])).

tff(c_1540,plain,(
    k2_relat_1(k2_funct_1('#skF_4')) = k1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_918,c_1530])).

tff(c_2131,plain,(
    ! [A_225,B_226,C_227] :
      ( k2_relset_1(A_225,B_226,C_227) = k2_relat_1(C_227)
      | ~ m1_subset_1(C_227,k1_zfmisc_1(k2_zfmisc_1(A_225,B_226))) ) ),
    inference(cnfTransformation,[status(thm)],[f_200])).

tff(c_2144,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_122,c_2131])).

tff(c_2155,plain,(
    k2_relat_1('#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_118,c_2144])).

tff(c_34,plain,(
    ! [A_20] :
      ( k1_relat_1(k4_relat_1(A_20)) = k2_relat_1(A_20)
      | ~ v1_relat_1(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_1533,plain,
    ( k1_relat_1(k2_funct_1('#skF_4')) = k2_relat_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1526,c_34])).

tff(c_1542,plain,(
    k1_relat_1(k2_funct_1('#skF_4')) = k2_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_918,c_1533])).

tff(c_2159,plain,(
    k1_relat_1(k2_funct_1('#skF_4')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2155,c_1542])).

tff(c_100,plain,(
    ! [A_56] :
      ( v1_funct_2(A_56,k1_relat_1(A_56),k2_relat_1(A_56))
      | ~ v1_funct_1(A_56)
      | ~ v1_relat_1(A_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_226])).

tff(c_2190,plain,
    ( v1_funct_2(k2_funct_1('#skF_4'),'#skF_3',k2_relat_1(k2_funct_1('#skF_4')))
    | ~ v1_funct_1(k2_funct_1('#skF_4'))
    | ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_2159,c_100])).

tff(c_2214,plain,(
    v1_funct_2(k2_funct_1('#skF_4'),'#skF_3',k1_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1544,c_616,c_1540,c_2190])).

tff(c_2236,plain,(
    ! [A_228] :
      ( m1_subset_1(A_228,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_228),k2_relat_1(A_228))))
      | ~ v1_funct_1(A_228)
      | ~ v1_relat_1(A_228) ) ),
    inference(cnfTransformation,[status(thm)],[f_226])).

tff(c_2256,plain,
    ( m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_3',k2_relat_1(k2_funct_1('#skF_4')))))
    | ~ v1_funct_1(k2_funct_1('#skF_4'))
    | ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_2159,c_2236])).

tff(c_2309,plain,(
    m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_3',k1_relat_1('#skF_4')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1544,c_616,c_1540,c_2256])).

tff(c_22,plain,(
    ! [B_14,A_13] :
      ( r1_tarski(k1_relat_1(B_14),A_13)
      | ~ v4_relat_1(B_14,A_13)
      | ~ v1_relat_1(B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_3551,plain,(
    ! [B_307,D_308,A_309,C_310] :
      ( k1_xboole_0 = B_307
      | m1_subset_1(D_308,k1_zfmisc_1(k2_zfmisc_1(A_309,C_310)))
      | ~ r1_tarski(B_307,C_310)
      | ~ m1_subset_1(D_308,k1_zfmisc_1(k2_zfmisc_1(A_309,B_307)))
      | ~ v1_funct_2(D_308,A_309,B_307)
      | ~ v1_funct_1(D_308) ) ),
    inference(cnfTransformation,[status(thm)],[f_245])).

tff(c_24035,plain,(
    ! [B_904,D_905,A_906,A_907] :
      ( k1_relat_1(B_904) = k1_xboole_0
      | m1_subset_1(D_905,k1_zfmisc_1(k2_zfmisc_1(A_906,A_907)))
      | ~ m1_subset_1(D_905,k1_zfmisc_1(k2_zfmisc_1(A_906,k1_relat_1(B_904))))
      | ~ v1_funct_2(D_905,A_906,k1_relat_1(B_904))
      | ~ v1_funct_1(D_905)
      | ~ v4_relat_1(B_904,A_907)
      | ~ v1_relat_1(B_904) ) ),
    inference(resolution,[status(thm)],[c_22,c_3551])).

tff(c_24055,plain,(
    ! [A_907] :
      ( k1_relat_1('#skF_4') = k1_xboole_0
      | m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_3',A_907)))
      | ~ v1_funct_2(k2_funct_1('#skF_4'),'#skF_3',k1_relat_1('#skF_4'))
      | ~ v1_funct_1(k2_funct_1('#skF_4'))
      | ~ v4_relat_1('#skF_4',A_907)
      | ~ v1_relat_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_2309,c_24035])).

tff(c_24086,plain,(
    ! [A_907] :
      ( k1_relat_1('#skF_4') = k1_xboole_0
      | m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_3',A_907)))
      | ~ v4_relat_1('#skF_4',A_907) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_918,c_616,c_2214,c_24055])).

tff(c_24103,plain,(
    ! [A_908] :
      ( m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_3',A_908)))
      | ~ v4_relat_1('#skF_4',A_908) ) ),
    inference(negUnitSimplification,[status(thm)],[c_953,c_24086])).

tff(c_615,plain,
    ( ~ v1_funct_2(k2_funct_1('#skF_4'),'#skF_3','#skF_2')
    | ~ m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_116])).

tff(c_671,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_615])).

tff(c_24168,plain,(
    ~ v4_relat_1('#skF_4','#skF_2') ),
    inference(resolution,[status(thm)],[c_24103,c_671])).

tff(c_24228,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1474,c_24168])).

tff(c_24229,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_934])).

tff(c_8,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_24248,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24229,c_8])).

tff(c_163,plain,(
    ! [A_67] : k6_relat_1(A_67) = k6_partfun1(A_67) ),
    inference(cnfTransformation,[status(thm)],[f_216])).

tff(c_50,plain,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_169,plain,(
    k6_partfun1(k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_163,c_50])).

tff(c_96,plain,(
    ! [A_55] : k6_relat_1(A_55) = k6_partfun1(A_55) ),
    inference(cnfTransformation,[status(thm)],[f_216])).

tff(c_46,plain,(
    ! [A_23] : k2_relat_1(k6_relat_1(A_23)) = A_23 ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_134,plain,(
    ! [A_23] : k2_relat_1(k6_partfun1(A_23)) = A_23 ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_46])).

tff(c_181,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_169,c_134])).

tff(c_24243,plain,(
    k2_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_24229,c_24229,c_181])).

tff(c_24746,plain,(
    ! [A_953] :
      ( k4_relat_1(A_953) = k2_funct_1(A_953)
      | ~ v2_funct_1(A_953)
      | ~ v1_funct_1(A_953)
      | ~ v1_relat_1(A_953) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_24752,plain,
    ( k4_relat_1('#skF_4') = k2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_120,c_24746])).

tff(c_24758,plain,(
    k4_relat_1('#skF_4') = k2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_918,c_126,c_24752])).

tff(c_24765,plain,
    ( k1_relat_1(k2_funct_1('#skF_4')) = k2_relat_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_24758,c_34])).

tff(c_24774,plain,(
    k1_relat_1(k2_funct_1('#skF_4')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_918,c_24243,c_24765])).

tff(c_24768,plain,
    ( v1_relat_1(k2_funct_1('#skF_4'))
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_24758,c_24])).

tff(c_24776,plain,(
    v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_918,c_24768])).

tff(c_25184,plain,(
    ! [A_973] :
      ( k1_relat_1(A_973) != '#skF_4'
      | A_973 = '#skF_4'
      | ~ v1_relat_1(A_973) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24229,c_24229,c_38])).

tff(c_25190,plain,
    ( k1_relat_1(k2_funct_1('#skF_4')) != '#skF_4'
    | k2_funct_1('#skF_4') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_24776,c_25184])).

tff(c_25210,plain,(
    k2_funct_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_24774,c_25190])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_10,plain,(
    ! [A_6] : k2_subset_1(A_6) = A_6 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_12,plain,(
    ! [A_7] : m1_subset_1(k2_subset_1(A_7),k1_zfmisc_1(A_7)) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_136,plain,(
    ! [A_7] : m1_subset_1(A_7,k1_zfmisc_1(A_7)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_12])).

tff(c_24372,plain,(
    ! [C_910,B_911,A_912] :
      ( ~ v1_xboole_0(C_910)
      | ~ m1_subset_1(B_911,k1_zfmisc_1(C_910))
      | ~ r2_hidden(A_912,B_911) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_24399,plain,(
    ! [A_914,A_915] :
      ( ~ v1_xboole_0(A_914)
      | ~ r2_hidden(A_915,A_914) ) ),
    inference(resolution,[status(thm)],[c_136,c_24372])).

tff(c_24405,plain,(
    ! [A_916,B_917] :
      ( ~ v1_xboole_0(A_916)
      | r1_tarski(A_916,B_917) ) ),
    inference(resolution,[status(thm)],[c_6,c_24399])).

tff(c_16,plain,(
    ! [A_8,B_9] :
      ( m1_subset_1(A_8,k1_zfmisc_1(B_9))
      | ~ r1_tarski(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_727,plain,(
    ~ r1_tarski(k2_funct_1('#skF_4'),k2_zfmisc_1('#skF_3','#skF_2')) ),
    inference(resolution,[status(thm)],[c_16,c_671])).

tff(c_24409,plain,(
    ~ v1_xboole_0(k2_funct_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_24405,c_727])).

tff(c_25230,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_25210,c_24409])).

tff(c_25244,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_24248,c_25230])).

tff(c_25246,plain,(
    m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_615])).

tff(c_25464,plain,(
    v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_25246,c_25445])).

tff(c_26050,plain,(
    ! [A_1055] :
      ( k4_relat_1(A_1055) = k2_funct_1(A_1055)
      | ~ v2_funct_1(A_1055)
      | ~ v1_funct_1(A_1055)
      | ~ v1_relat_1(A_1055) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_26059,plain,
    ( k4_relat_1('#skF_4') = k2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_120,c_26050])).

tff(c_26068,plain,(
    k4_relat_1('#skF_4') = k2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_25467,c_126,c_26059])).

tff(c_26072,plain,
    ( k2_relat_1(k2_funct_1('#skF_4')) = k1_relat_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_26068,c_32])).

tff(c_26082,plain,(
    k2_relat_1(k2_funct_1('#skF_4')) = k1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_25467,c_26072])).

tff(c_26075,plain,
    ( k1_relat_1(k2_funct_1('#skF_4')) = k2_relat_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_26068,c_34])).

tff(c_26084,plain,(
    k1_relat_1(k2_funct_1('#skF_4')) = k2_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_25467,c_26075])).

tff(c_26200,plain,
    ( v1_funct_2(k2_funct_1('#skF_4'),k2_relat_1('#skF_4'),k2_relat_1(k2_funct_1('#skF_4')))
    | ~ v1_funct_1(k2_funct_1('#skF_4'))
    | ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_26084,c_100])).

tff(c_26219,plain,(
    v1_funct_2(k2_funct_1('#skF_4'),k2_relat_1('#skF_4'),k1_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_25464,c_616,c_26082,c_26200])).

tff(c_26857,plain,(
    v1_funct_2(k2_funct_1('#skF_4'),'#skF_3',k1_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26851,c_26219])).

tff(c_26859,plain,(
    k1_relat_1(k2_funct_1('#skF_4')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_26851,c_26084])).

tff(c_98,plain,(
    ! [A_56] :
      ( m1_subset_1(A_56,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_56),k2_relat_1(A_56))))
      | ~ v1_funct_1(A_56)
      | ~ v1_relat_1(A_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_226])).

tff(c_26890,plain,
    ( m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_3',k2_relat_1(k2_funct_1('#skF_4')))))
    | ~ v1_funct_1(k2_funct_1('#skF_4'))
    | ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_26859,c_98])).

tff(c_26918,plain,(
    m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_3',k1_relat_1('#skF_4')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_25464,c_616,c_26082,c_26890])).

tff(c_27534,plain,(
    ! [B_1113,D_1114,A_1115,C_1116] :
      ( k1_xboole_0 = B_1113
      | v1_funct_2(D_1114,A_1115,C_1116)
      | ~ r1_tarski(B_1113,C_1116)
      | ~ m1_subset_1(D_1114,k1_zfmisc_1(k2_zfmisc_1(A_1115,B_1113)))
      | ~ v1_funct_2(D_1114,A_1115,B_1113)
      | ~ v1_funct_1(D_1114) ) ),
    inference(cnfTransformation,[status(thm)],[f_245])).

tff(c_47816,plain,(
    ! [B_1724,D_1725,A_1726,A_1727] :
      ( k1_relat_1(B_1724) = k1_xboole_0
      | v1_funct_2(D_1725,A_1726,A_1727)
      | ~ m1_subset_1(D_1725,k1_zfmisc_1(k2_zfmisc_1(A_1726,k1_relat_1(B_1724))))
      | ~ v1_funct_2(D_1725,A_1726,k1_relat_1(B_1724))
      | ~ v1_funct_1(D_1725)
      | ~ v4_relat_1(B_1724,A_1727)
      | ~ v1_relat_1(B_1724) ) ),
    inference(resolution,[status(thm)],[c_22,c_27534])).

tff(c_47836,plain,(
    ! [A_1727] :
      ( k1_relat_1('#skF_4') = k1_xboole_0
      | v1_funct_2(k2_funct_1('#skF_4'),'#skF_3',A_1727)
      | ~ v1_funct_2(k2_funct_1('#skF_4'),'#skF_3',k1_relat_1('#skF_4'))
      | ~ v1_funct_1(k2_funct_1('#skF_4'))
      | ~ v4_relat_1('#skF_4',A_1727)
      | ~ v1_relat_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_26918,c_47816])).

tff(c_47867,plain,(
    ! [A_1727] :
      ( k1_relat_1('#skF_4') = k1_xboole_0
      | v1_funct_2(k2_funct_1('#skF_4'),'#skF_3',A_1727)
      | ~ v4_relat_1('#skF_4',A_1727) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_25467,c_616,c_26857,c_47836])).

tff(c_47884,plain,(
    ! [A_1728] :
      ( v1_funct_2(k2_funct_1('#skF_4'),'#skF_3',A_1728)
      | ~ v4_relat_1('#skF_4',A_1728) ) ),
    inference(negUnitSimplification,[status(thm)],[c_25485,c_47867])).

tff(c_25245,plain,(
    ~ v1_funct_2(k2_funct_1('#skF_4'),'#skF_3','#skF_2') ),
    inference(splitRight,[status(thm)],[c_615])).

tff(c_47887,plain,(
    ~ v4_relat_1('#skF_4','#skF_2') ),
    inference(resolution,[status(thm)],[c_47884,c_25245])).

tff(c_47891,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_25902,c_47887])).

tff(c_47892,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_25483])).

tff(c_47905,plain,(
    k2_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_47892,c_47892,c_181])).

tff(c_49207,plain,(
    ! [A_1827,B_1828,C_1829] :
      ( k2_relset_1(A_1827,B_1828,C_1829) = k2_relat_1(C_1829)
      | ~ m1_subset_1(C_1829,k1_zfmisc_1(k2_zfmisc_1(A_1827,B_1828))) ) ),
    inference(cnfTransformation,[status(thm)],[f_200])).

tff(c_49226,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_122,c_49207])).

tff(c_49240,plain,(
    '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_118,c_47905,c_49226])).

tff(c_36,plain,(
    ! [A_21] :
      ( k2_relat_1(A_21) != k1_xboole_0
      | k1_xboole_0 = A_21
      | ~ v1_relat_1(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_48433,plain,(
    ! [A_1771] :
      ( k2_relat_1(A_1771) != '#skF_4'
      | A_1771 = '#skF_4'
      | ~ v1_relat_1(A_1771) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_47892,c_47892,c_36])).

tff(c_48453,plain,
    ( k2_relat_1(k2_funct_1('#skF_4')) != '#skF_4'
    | k2_funct_1('#skF_4') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_25464,c_48433])).

tff(c_48528,plain,(
    k2_relat_1(k2_funct_1('#skF_4')) != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_48453])).

tff(c_44,plain,(
    ! [A_23] : k1_relat_1(k6_relat_1(A_23)) = A_23 ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_191,plain,(
    ! [A_68] : k1_relat_1(k6_partfun1(A_68)) = A_68 ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_44])).

tff(c_200,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_169,c_191])).

tff(c_47904,plain,(
    k1_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_47892,c_47892,c_200])).

tff(c_48578,plain,(
    ! [A_1785] :
      ( k4_relat_1(A_1785) = k2_funct_1(A_1785)
      | ~ v2_funct_1(A_1785)
      | ~ v1_funct_1(A_1785)
      | ~ v1_relat_1(A_1785) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_48584,plain,
    ( k4_relat_1('#skF_4') = k2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_120,c_48578])).

tff(c_48590,plain,(
    k4_relat_1('#skF_4') = k2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_25467,c_126,c_48584])).

tff(c_48594,plain,
    ( k2_relat_1(k2_funct_1('#skF_4')) = k1_relat_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_48590,c_32])).

tff(c_48604,plain,(
    k2_relat_1(k2_funct_1('#skF_4')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_25467,c_47904,c_48594])).

tff(c_48606,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_48528,c_48604])).

tff(c_48607,plain,(
    k2_funct_1('#skF_4') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_48453])).

tff(c_48613,plain,(
    ~ v1_funct_2('#skF_4','#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48607,c_25245])).

tff(c_49244,plain,(
    ~ v1_funct_2('#skF_4','#skF_4','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_49240,c_48613])).

tff(c_64,plain,(
    ! [A_29] : v1_relat_1(k6_relat_1(A_29)) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_130,plain,(
    ! [A_29] : v1_relat_1(k6_partfun1(A_29)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_64])).

tff(c_223,plain,(
    ! [A_73] :
      ( k2_relat_1(A_73) != k1_xboole_0
      | k1_xboole_0 = A_73
      | ~ v1_relat_1(A_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_235,plain,(
    ! [A_29] :
      ( k2_relat_1(k6_partfun1(A_29)) != k1_xboole_0
      | k6_partfun1(A_29) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_130,c_223])).

tff(c_246,plain,(
    ! [A_74] :
      ( k1_xboole_0 != A_74
      | k6_partfun1(A_74) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_134,c_235])).

tff(c_92,plain,(
    ! [A_54] : v1_partfun1(k6_partfun1(A_54),A_54) ),
    inference(cnfTransformation,[status(thm)],[f_214])).

tff(c_252,plain,(
    ! [A_74] :
      ( v1_partfun1(k1_xboole_0,A_74)
      | k1_xboole_0 != A_74 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_246,c_92])).

tff(c_48111,plain,(
    v1_partfun1('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_47892,c_47892,c_252])).

tff(c_48612,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48607,c_25246])).

tff(c_49243,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_49240,c_48612])).

tff(c_49437,plain,(
    ! [C_1842,A_1843,B_1844] :
      ( v1_funct_2(C_1842,A_1843,B_1844)
      | ~ v1_partfun1(C_1842,A_1843)
      | ~ v1_funct_1(C_1842)
      | ~ m1_subset_1(C_1842,k1_zfmisc_1(k2_zfmisc_1(A_1843,B_1844))) ) ),
    inference(cnfTransformation,[status(thm)],[f_210])).

tff(c_49440,plain,
    ( v1_funct_2('#skF_4','#skF_4','#skF_2')
    | ~ v1_partfun1('#skF_4','#skF_4')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_49243,c_49437])).

tff(c_49463,plain,(
    v1_funct_2('#skF_4','#skF_4','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_126,c_48111,c_49440])).

tff(c_49465,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_49244,c_49463])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:12:41 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 18.76/9.90  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 18.86/9.92  
% 18.86/9.92  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 18.86/9.93  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r2_hidden > r1_tarski > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k9_relat_1 > k7_relat_1 > k5_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k6_relat_1 > k6_partfun1 > k4_relat_1 > k2_subset_1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 18.86/9.93  
% 18.86/9.93  %Foreground sorts:
% 18.86/9.93  
% 18.86/9.93  
% 18.86/9.93  %Background operators:
% 18.86/9.93  
% 18.86/9.93  
% 18.86/9.93  %Foreground operators:
% 18.86/9.93  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 18.86/9.93  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 18.86/9.93  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 18.86/9.93  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 18.86/9.93  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 18.86/9.93  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 18.86/9.93  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 18.86/9.93  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 18.86/9.93  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 18.86/9.93  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 18.86/9.93  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 18.86/9.93  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 18.86/9.93  tff('#skF_2', type, '#skF_2': $i).
% 18.86/9.93  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 18.86/9.93  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 18.86/9.93  tff('#skF_3', type, '#skF_3': $i).
% 18.86/9.93  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 18.86/9.93  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 18.86/9.93  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 18.86/9.93  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 18.86/9.93  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 18.86/9.93  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 18.86/9.93  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 18.86/9.93  tff('#skF_4', type, '#skF_4': $i).
% 18.86/9.93  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 18.86/9.93  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 18.86/9.93  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 18.86/9.93  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 18.86/9.93  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 18.86/9.93  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 18.86/9.93  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 18.86/9.93  tff(k4_relat_1, type, k4_relat_1: $i > $i).
% 18.86/9.93  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 18.86/9.93  
% 18.86/9.95  tff(f_262, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((v2_funct_1(C) & (k2_relset_1(A, B, C) = B)) => ((v1_funct_1(k2_funct_1(C)) & v1_funct_2(k2_funct_1(C), B, A)) & m1_subset_1(k2_funct_1(C), k1_zfmisc_1(k2_zfmisc_1(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_funct_2)).
% 18.86/9.95  tff(f_196, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 18.86/9.95  tff(f_190, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 18.86/9.95  tff(f_84, axiom, (![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_relat_1)).
% 18.86/9.95  tff(f_119, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 18.86/9.95  tff(f_200, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 18.86/9.95  tff(f_111, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => (k2_funct_1(A) = k4_relat_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d9_funct_1)).
% 18.86/9.95  tff(f_58, axiom, (![A]: (v1_relat_1(A) => v1_relat_1(k4_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k4_relat_1)).
% 18.86/9.95  tff(f_76, axiom, (![A]: (v1_relat_1(A) => ((k2_relat_1(A) = k1_relat_1(k4_relat_1(A))) & (k1_relat_1(A) = k2_relat_1(k4_relat_1(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t37_relat_1)).
% 18.86/9.95  tff(f_226, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => ((v1_funct_1(A) & v1_funct_2(A, k1_relat_1(A), k2_relat_1(A))) & m1_subset_1(A, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_funct_2)).
% 18.86/9.95  tff(f_54, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d18_relat_1)).
% 18.86/9.95  tff(f_245, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r1_tarski(B, C) => (((B = k1_xboole_0) & ~(A = k1_xboole_0)) | ((v1_funct_1(D) & v1_funct_2(D, A, C)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t9_funct_2)).
% 18.86/9.95  tff(f_33, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 18.86/9.95  tff(f_216, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 18.86/9.95  tff(f_99, axiom, (k6_relat_1(k1_xboole_0) = k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t81_relat_1)).
% 18.86/9.95  tff(f_94, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 18.86/9.95  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 18.86/9.95  tff(f_35, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 18.86/9.95  tff(f_37, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 18.86/9.95  tff(f_48, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_subset)).
% 18.86/9.95  tff(f_41, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 18.86/9.95  tff(f_127, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v2_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc4_funct_1)).
% 18.86/9.95  tff(f_214, axiom, (![A]: (v1_partfun1(k6_partfun1(A), A) & m1_subset_1(k6_partfun1(A), k1_zfmisc_1(k2_zfmisc_1(A, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_partfun1)).
% 18.86/9.95  tff(f_210, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v1_partfun1(C, A)) => (v1_funct_1(C) & v1_funct_2(C, A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_funct_2)).
% 18.86/9.95  tff(c_118, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_4')='#skF_3'), inference(cnfTransformation, [status(thm)], [f_262])).
% 18.86/9.95  tff(c_122, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_262])).
% 18.86/9.95  tff(c_25876, plain, (![C_1032, A_1033, B_1034]: (v4_relat_1(C_1032, A_1033) | ~m1_subset_1(C_1032, k1_zfmisc_1(k2_zfmisc_1(A_1033, B_1034))))), inference(cnfTransformation, [status(thm)], [f_196])).
% 18.86/9.95  tff(c_25902, plain, (v4_relat_1('#skF_4', '#skF_2')), inference(resolution, [status(thm)], [c_122, c_25876])).
% 18.86/9.95  tff(c_25445, plain, (![C_990, A_991, B_992]: (v1_relat_1(C_990) | ~m1_subset_1(C_990, k1_zfmisc_1(k2_zfmisc_1(A_991, B_992))))), inference(cnfTransformation, [status(thm)], [f_190])).
% 18.86/9.95  tff(c_25467, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_122, c_25445])).
% 18.86/9.95  tff(c_38, plain, (![A_21]: (k1_relat_1(A_21)!=k1_xboole_0 | k1_xboole_0=A_21 | ~v1_relat_1(A_21))), inference(cnfTransformation, [status(thm)], [f_84])).
% 18.86/9.95  tff(c_25483, plain, (k1_relat_1('#skF_4')!=k1_xboole_0 | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_25467, c_38])).
% 18.86/9.95  tff(c_25485, plain, (k1_relat_1('#skF_4')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_25483])).
% 18.86/9.95  tff(c_126, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_262])).
% 18.86/9.95  tff(c_56, plain, (![A_27]: (v1_funct_1(k2_funct_1(A_27)) | ~v1_funct_1(A_27) | ~v1_relat_1(A_27))), inference(cnfTransformation, [status(thm)], [f_119])).
% 18.86/9.95  tff(c_116, plain, (~m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2'))) | ~v1_funct_2(k2_funct_1('#skF_4'), '#skF_3', '#skF_2') | ~v1_funct_1(k2_funct_1('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_262])).
% 18.86/9.95  tff(c_275, plain, (~v1_funct_1(k2_funct_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_116])).
% 18.86/9.95  tff(c_278, plain, (~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_56, c_275])).
% 18.86/9.95  tff(c_281, plain, (~v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_126, c_278])).
% 18.86/9.95  tff(c_593, plain, (![C_102, A_103, B_104]: (v1_relat_1(C_102) | ~m1_subset_1(C_102, k1_zfmisc_1(k2_zfmisc_1(A_103, B_104))))), inference(cnfTransformation, [status(thm)], [f_190])).
% 18.86/9.95  tff(c_603, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_122, c_593])).
% 18.86/9.95  tff(c_614, plain, $false, inference(negUnitSimplification, [status(thm)], [c_281, c_603])).
% 18.86/9.95  tff(c_616, plain, (v1_funct_1(k2_funct_1('#skF_4'))), inference(splitRight, [status(thm)], [c_116])).
% 18.86/9.95  tff(c_26818, plain, (![A_1073, B_1074, C_1075]: (k2_relset_1(A_1073, B_1074, C_1075)=k2_relat_1(C_1075) | ~m1_subset_1(C_1075, k1_zfmisc_1(k2_zfmisc_1(A_1073, B_1074))))), inference(cnfTransformation, [status(thm)], [f_200])).
% 18.86/9.95  tff(c_26837, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_122, c_26818])).
% 18.86/9.95  tff(c_26851, plain, (k2_relat_1('#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_118, c_26837])).
% 18.86/9.95  tff(c_1452, plain, (![C_198, A_199, B_200]: (v4_relat_1(C_198, A_199) | ~m1_subset_1(C_198, k1_zfmisc_1(k2_zfmisc_1(A_199, B_200))))), inference(cnfTransformation, [status(thm)], [f_196])).
% 18.86/9.95  tff(c_1474, plain, (v4_relat_1('#skF_4', '#skF_2')), inference(resolution, [status(thm)], [c_122, c_1452])).
% 18.86/9.95  tff(c_900, plain, (![C_130, A_131, B_132]: (v1_relat_1(C_130) | ~m1_subset_1(C_130, k1_zfmisc_1(k2_zfmisc_1(A_131, B_132))))), inference(cnfTransformation, [status(thm)], [f_190])).
% 18.86/9.95  tff(c_918, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_122, c_900])).
% 18.86/9.95  tff(c_934, plain, (k1_relat_1('#skF_4')!=k1_xboole_0 | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_918, c_38])).
% 18.86/9.95  tff(c_953, plain, (k1_relat_1('#skF_4')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_934])).
% 18.86/9.95  tff(c_120, plain, (v2_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_262])).
% 18.86/9.95  tff(c_1508, plain, (![A_206]: (k4_relat_1(A_206)=k2_funct_1(A_206) | ~v2_funct_1(A_206) | ~v1_funct_1(A_206) | ~v1_relat_1(A_206))), inference(cnfTransformation, [status(thm)], [f_111])).
% 18.86/9.95  tff(c_1517, plain, (k4_relat_1('#skF_4')=k2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_120, c_1508])).
% 18.86/9.95  tff(c_1526, plain, (k4_relat_1('#skF_4')=k2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_918, c_126, c_1517])).
% 18.86/9.95  tff(c_24, plain, (![A_15]: (v1_relat_1(k4_relat_1(A_15)) | ~v1_relat_1(A_15))), inference(cnfTransformation, [status(thm)], [f_58])).
% 18.86/9.95  tff(c_1536, plain, (v1_relat_1(k2_funct_1('#skF_4')) | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1526, c_24])).
% 18.86/9.95  tff(c_1544, plain, (v1_relat_1(k2_funct_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_918, c_1536])).
% 18.86/9.95  tff(c_32, plain, (![A_20]: (k2_relat_1(k4_relat_1(A_20))=k1_relat_1(A_20) | ~v1_relat_1(A_20))), inference(cnfTransformation, [status(thm)], [f_76])).
% 18.86/9.95  tff(c_1530, plain, (k2_relat_1(k2_funct_1('#skF_4'))=k1_relat_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1526, c_32])).
% 18.86/9.95  tff(c_1540, plain, (k2_relat_1(k2_funct_1('#skF_4'))=k1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_918, c_1530])).
% 18.86/9.95  tff(c_2131, plain, (![A_225, B_226, C_227]: (k2_relset_1(A_225, B_226, C_227)=k2_relat_1(C_227) | ~m1_subset_1(C_227, k1_zfmisc_1(k2_zfmisc_1(A_225, B_226))))), inference(cnfTransformation, [status(thm)], [f_200])).
% 18.86/9.95  tff(c_2144, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_122, c_2131])).
% 18.86/9.95  tff(c_2155, plain, (k2_relat_1('#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_118, c_2144])).
% 18.86/9.95  tff(c_34, plain, (![A_20]: (k1_relat_1(k4_relat_1(A_20))=k2_relat_1(A_20) | ~v1_relat_1(A_20))), inference(cnfTransformation, [status(thm)], [f_76])).
% 18.86/9.95  tff(c_1533, plain, (k1_relat_1(k2_funct_1('#skF_4'))=k2_relat_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1526, c_34])).
% 18.86/9.95  tff(c_1542, plain, (k1_relat_1(k2_funct_1('#skF_4'))=k2_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_918, c_1533])).
% 18.86/9.95  tff(c_2159, plain, (k1_relat_1(k2_funct_1('#skF_4'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_2155, c_1542])).
% 18.86/9.95  tff(c_100, plain, (![A_56]: (v1_funct_2(A_56, k1_relat_1(A_56), k2_relat_1(A_56)) | ~v1_funct_1(A_56) | ~v1_relat_1(A_56))), inference(cnfTransformation, [status(thm)], [f_226])).
% 18.86/9.95  tff(c_2190, plain, (v1_funct_2(k2_funct_1('#skF_4'), '#skF_3', k2_relat_1(k2_funct_1('#skF_4'))) | ~v1_funct_1(k2_funct_1('#skF_4')) | ~v1_relat_1(k2_funct_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_2159, c_100])).
% 18.86/9.95  tff(c_2214, plain, (v1_funct_2(k2_funct_1('#skF_4'), '#skF_3', k1_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_1544, c_616, c_1540, c_2190])).
% 18.86/9.95  tff(c_2236, plain, (![A_228]: (m1_subset_1(A_228, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_228), k2_relat_1(A_228)))) | ~v1_funct_1(A_228) | ~v1_relat_1(A_228))), inference(cnfTransformation, [status(thm)], [f_226])).
% 18.86/9.95  tff(c_2256, plain, (m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', k2_relat_1(k2_funct_1('#skF_4'))))) | ~v1_funct_1(k2_funct_1('#skF_4')) | ~v1_relat_1(k2_funct_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_2159, c_2236])).
% 18.86/9.95  tff(c_2309, plain, (m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', k1_relat_1('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_1544, c_616, c_1540, c_2256])).
% 18.86/9.95  tff(c_22, plain, (![B_14, A_13]: (r1_tarski(k1_relat_1(B_14), A_13) | ~v4_relat_1(B_14, A_13) | ~v1_relat_1(B_14))), inference(cnfTransformation, [status(thm)], [f_54])).
% 18.86/9.95  tff(c_3551, plain, (![B_307, D_308, A_309, C_310]: (k1_xboole_0=B_307 | m1_subset_1(D_308, k1_zfmisc_1(k2_zfmisc_1(A_309, C_310))) | ~r1_tarski(B_307, C_310) | ~m1_subset_1(D_308, k1_zfmisc_1(k2_zfmisc_1(A_309, B_307))) | ~v1_funct_2(D_308, A_309, B_307) | ~v1_funct_1(D_308))), inference(cnfTransformation, [status(thm)], [f_245])).
% 18.86/9.95  tff(c_24035, plain, (![B_904, D_905, A_906, A_907]: (k1_relat_1(B_904)=k1_xboole_0 | m1_subset_1(D_905, k1_zfmisc_1(k2_zfmisc_1(A_906, A_907))) | ~m1_subset_1(D_905, k1_zfmisc_1(k2_zfmisc_1(A_906, k1_relat_1(B_904)))) | ~v1_funct_2(D_905, A_906, k1_relat_1(B_904)) | ~v1_funct_1(D_905) | ~v4_relat_1(B_904, A_907) | ~v1_relat_1(B_904))), inference(resolution, [status(thm)], [c_22, c_3551])).
% 18.86/9.95  tff(c_24055, plain, (![A_907]: (k1_relat_1('#skF_4')=k1_xboole_0 | m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', A_907))) | ~v1_funct_2(k2_funct_1('#skF_4'), '#skF_3', k1_relat_1('#skF_4')) | ~v1_funct_1(k2_funct_1('#skF_4')) | ~v4_relat_1('#skF_4', A_907) | ~v1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_2309, c_24035])).
% 18.86/9.95  tff(c_24086, plain, (![A_907]: (k1_relat_1('#skF_4')=k1_xboole_0 | m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', A_907))) | ~v4_relat_1('#skF_4', A_907))), inference(demodulation, [status(thm), theory('equality')], [c_918, c_616, c_2214, c_24055])).
% 18.86/9.95  tff(c_24103, plain, (![A_908]: (m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', A_908))) | ~v4_relat_1('#skF_4', A_908))), inference(negUnitSimplification, [status(thm)], [c_953, c_24086])).
% 18.86/9.95  tff(c_615, plain, (~v1_funct_2(k2_funct_1('#skF_4'), '#skF_3', '#skF_2') | ~m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(splitRight, [status(thm)], [c_116])).
% 18.86/9.95  tff(c_671, plain, (~m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(splitLeft, [status(thm)], [c_615])).
% 18.86/9.95  tff(c_24168, plain, (~v4_relat_1('#skF_4', '#skF_2')), inference(resolution, [status(thm)], [c_24103, c_671])).
% 18.86/9.95  tff(c_24228, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1474, c_24168])).
% 18.86/9.95  tff(c_24229, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_934])).
% 18.86/9.95  tff(c_8, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 18.86/9.95  tff(c_24248, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_24229, c_8])).
% 18.86/9.95  tff(c_163, plain, (![A_67]: (k6_relat_1(A_67)=k6_partfun1(A_67))), inference(cnfTransformation, [status(thm)], [f_216])).
% 18.86/9.95  tff(c_50, plain, (k6_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_99])).
% 18.86/9.95  tff(c_169, plain, (k6_partfun1(k1_xboole_0)=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_163, c_50])).
% 18.86/9.95  tff(c_96, plain, (![A_55]: (k6_relat_1(A_55)=k6_partfun1(A_55))), inference(cnfTransformation, [status(thm)], [f_216])).
% 18.86/9.95  tff(c_46, plain, (![A_23]: (k2_relat_1(k6_relat_1(A_23))=A_23)), inference(cnfTransformation, [status(thm)], [f_94])).
% 18.86/9.95  tff(c_134, plain, (![A_23]: (k2_relat_1(k6_partfun1(A_23))=A_23)), inference(demodulation, [status(thm), theory('equality')], [c_96, c_46])).
% 18.86/9.95  tff(c_181, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_169, c_134])).
% 18.86/9.95  tff(c_24243, plain, (k2_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_24229, c_24229, c_181])).
% 18.86/9.95  tff(c_24746, plain, (![A_953]: (k4_relat_1(A_953)=k2_funct_1(A_953) | ~v2_funct_1(A_953) | ~v1_funct_1(A_953) | ~v1_relat_1(A_953))), inference(cnfTransformation, [status(thm)], [f_111])).
% 18.86/9.95  tff(c_24752, plain, (k4_relat_1('#skF_4')=k2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_120, c_24746])).
% 18.86/9.95  tff(c_24758, plain, (k4_relat_1('#skF_4')=k2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_918, c_126, c_24752])).
% 18.86/9.95  tff(c_24765, plain, (k1_relat_1(k2_funct_1('#skF_4'))=k2_relat_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_24758, c_34])).
% 18.86/9.95  tff(c_24774, plain, (k1_relat_1(k2_funct_1('#skF_4'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_918, c_24243, c_24765])).
% 18.86/9.95  tff(c_24768, plain, (v1_relat_1(k2_funct_1('#skF_4')) | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_24758, c_24])).
% 18.86/9.95  tff(c_24776, plain, (v1_relat_1(k2_funct_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_918, c_24768])).
% 18.86/9.95  tff(c_25184, plain, (![A_973]: (k1_relat_1(A_973)!='#skF_4' | A_973='#skF_4' | ~v1_relat_1(A_973))), inference(demodulation, [status(thm), theory('equality')], [c_24229, c_24229, c_38])).
% 18.86/9.95  tff(c_25190, plain, (k1_relat_1(k2_funct_1('#skF_4'))!='#skF_4' | k2_funct_1('#skF_4')='#skF_4'), inference(resolution, [status(thm)], [c_24776, c_25184])).
% 18.86/9.95  tff(c_25210, plain, (k2_funct_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_24774, c_25190])).
% 18.86/9.95  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 18.86/9.95  tff(c_10, plain, (![A_6]: (k2_subset_1(A_6)=A_6)), inference(cnfTransformation, [status(thm)], [f_35])).
% 18.86/9.95  tff(c_12, plain, (![A_7]: (m1_subset_1(k2_subset_1(A_7), k1_zfmisc_1(A_7)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 18.86/9.95  tff(c_136, plain, (![A_7]: (m1_subset_1(A_7, k1_zfmisc_1(A_7)))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_12])).
% 18.86/9.95  tff(c_24372, plain, (![C_910, B_911, A_912]: (~v1_xboole_0(C_910) | ~m1_subset_1(B_911, k1_zfmisc_1(C_910)) | ~r2_hidden(A_912, B_911))), inference(cnfTransformation, [status(thm)], [f_48])).
% 18.86/9.95  tff(c_24399, plain, (![A_914, A_915]: (~v1_xboole_0(A_914) | ~r2_hidden(A_915, A_914))), inference(resolution, [status(thm)], [c_136, c_24372])).
% 18.86/9.95  tff(c_24405, plain, (![A_916, B_917]: (~v1_xboole_0(A_916) | r1_tarski(A_916, B_917))), inference(resolution, [status(thm)], [c_6, c_24399])).
% 18.86/9.95  tff(c_16, plain, (![A_8, B_9]: (m1_subset_1(A_8, k1_zfmisc_1(B_9)) | ~r1_tarski(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_41])).
% 18.86/9.95  tff(c_727, plain, (~r1_tarski(k2_funct_1('#skF_4'), k2_zfmisc_1('#skF_3', '#skF_2'))), inference(resolution, [status(thm)], [c_16, c_671])).
% 18.86/9.95  tff(c_24409, plain, (~v1_xboole_0(k2_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_24405, c_727])).
% 18.86/9.95  tff(c_25230, plain, (~v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_25210, c_24409])).
% 18.86/9.95  tff(c_25244, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_24248, c_25230])).
% 18.86/9.95  tff(c_25246, plain, (m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(splitRight, [status(thm)], [c_615])).
% 18.86/9.95  tff(c_25464, plain, (v1_relat_1(k2_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_25246, c_25445])).
% 18.86/9.95  tff(c_26050, plain, (![A_1055]: (k4_relat_1(A_1055)=k2_funct_1(A_1055) | ~v2_funct_1(A_1055) | ~v1_funct_1(A_1055) | ~v1_relat_1(A_1055))), inference(cnfTransformation, [status(thm)], [f_111])).
% 18.86/9.95  tff(c_26059, plain, (k4_relat_1('#skF_4')=k2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_120, c_26050])).
% 18.86/9.95  tff(c_26068, plain, (k4_relat_1('#skF_4')=k2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_25467, c_126, c_26059])).
% 18.86/9.95  tff(c_26072, plain, (k2_relat_1(k2_funct_1('#skF_4'))=k1_relat_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_26068, c_32])).
% 18.86/9.95  tff(c_26082, plain, (k2_relat_1(k2_funct_1('#skF_4'))=k1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_25467, c_26072])).
% 18.86/9.95  tff(c_26075, plain, (k1_relat_1(k2_funct_1('#skF_4'))=k2_relat_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_26068, c_34])).
% 18.86/9.95  tff(c_26084, plain, (k1_relat_1(k2_funct_1('#skF_4'))=k2_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_25467, c_26075])).
% 18.86/9.95  tff(c_26200, plain, (v1_funct_2(k2_funct_1('#skF_4'), k2_relat_1('#skF_4'), k2_relat_1(k2_funct_1('#skF_4'))) | ~v1_funct_1(k2_funct_1('#skF_4')) | ~v1_relat_1(k2_funct_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_26084, c_100])).
% 18.86/9.95  tff(c_26219, plain, (v1_funct_2(k2_funct_1('#skF_4'), k2_relat_1('#skF_4'), k1_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_25464, c_616, c_26082, c_26200])).
% 18.86/9.95  tff(c_26857, plain, (v1_funct_2(k2_funct_1('#skF_4'), '#skF_3', k1_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_26851, c_26219])).
% 18.86/9.95  tff(c_26859, plain, (k1_relat_1(k2_funct_1('#skF_4'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_26851, c_26084])).
% 18.86/9.95  tff(c_98, plain, (![A_56]: (m1_subset_1(A_56, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_56), k2_relat_1(A_56)))) | ~v1_funct_1(A_56) | ~v1_relat_1(A_56))), inference(cnfTransformation, [status(thm)], [f_226])).
% 18.86/9.95  tff(c_26890, plain, (m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', k2_relat_1(k2_funct_1('#skF_4'))))) | ~v1_funct_1(k2_funct_1('#skF_4')) | ~v1_relat_1(k2_funct_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_26859, c_98])).
% 18.86/9.95  tff(c_26918, plain, (m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', k1_relat_1('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_25464, c_616, c_26082, c_26890])).
% 18.86/9.95  tff(c_27534, plain, (![B_1113, D_1114, A_1115, C_1116]: (k1_xboole_0=B_1113 | v1_funct_2(D_1114, A_1115, C_1116) | ~r1_tarski(B_1113, C_1116) | ~m1_subset_1(D_1114, k1_zfmisc_1(k2_zfmisc_1(A_1115, B_1113))) | ~v1_funct_2(D_1114, A_1115, B_1113) | ~v1_funct_1(D_1114))), inference(cnfTransformation, [status(thm)], [f_245])).
% 18.86/9.95  tff(c_47816, plain, (![B_1724, D_1725, A_1726, A_1727]: (k1_relat_1(B_1724)=k1_xboole_0 | v1_funct_2(D_1725, A_1726, A_1727) | ~m1_subset_1(D_1725, k1_zfmisc_1(k2_zfmisc_1(A_1726, k1_relat_1(B_1724)))) | ~v1_funct_2(D_1725, A_1726, k1_relat_1(B_1724)) | ~v1_funct_1(D_1725) | ~v4_relat_1(B_1724, A_1727) | ~v1_relat_1(B_1724))), inference(resolution, [status(thm)], [c_22, c_27534])).
% 18.86/9.95  tff(c_47836, plain, (![A_1727]: (k1_relat_1('#skF_4')=k1_xboole_0 | v1_funct_2(k2_funct_1('#skF_4'), '#skF_3', A_1727) | ~v1_funct_2(k2_funct_1('#skF_4'), '#skF_3', k1_relat_1('#skF_4')) | ~v1_funct_1(k2_funct_1('#skF_4')) | ~v4_relat_1('#skF_4', A_1727) | ~v1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_26918, c_47816])).
% 18.86/9.95  tff(c_47867, plain, (![A_1727]: (k1_relat_1('#skF_4')=k1_xboole_0 | v1_funct_2(k2_funct_1('#skF_4'), '#skF_3', A_1727) | ~v4_relat_1('#skF_4', A_1727))), inference(demodulation, [status(thm), theory('equality')], [c_25467, c_616, c_26857, c_47836])).
% 18.86/9.95  tff(c_47884, plain, (![A_1728]: (v1_funct_2(k2_funct_1('#skF_4'), '#skF_3', A_1728) | ~v4_relat_1('#skF_4', A_1728))), inference(negUnitSimplification, [status(thm)], [c_25485, c_47867])).
% 18.86/9.95  tff(c_25245, plain, (~v1_funct_2(k2_funct_1('#skF_4'), '#skF_3', '#skF_2')), inference(splitRight, [status(thm)], [c_615])).
% 18.86/9.95  tff(c_47887, plain, (~v4_relat_1('#skF_4', '#skF_2')), inference(resolution, [status(thm)], [c_47884, c_25245])).
% 18.86/9.95  tff(c_47891, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_25902, c_47887])).
% 18.86/9.95  tff(c_47892, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_25483])).
% 18.86/9.95  tff(c_47905, plain, (k2_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_47892, c_47892, c_181])).
% 18.86/9.95  tff(c_49207, plain, (![A_1827, B_1828, C_1829]: (k2_relset_1(A_1827, B_1828, C_1829)=k2_relat_1(C_1829) | ~m1_subset_1(C_1829, k1_zfmisc_1(k2_zfmisc_1(A_1827, B_1828))))), inference(cnfTransformation, [status(thm)], [f_200])).
% 18.86/9.95  tff(c_49226, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_122, c_49207])).
% 18.86/9.95  tff(c_49240, plain, ('#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_118, c_47905, c_49226])).
% 18.86/9.95  tff(c_36, plain, (![A_21]: (k2_relat_1(A_21)!=k1_xboole_0 | k1_xboole_0=A_21 | ~v1_relat_1(A_21))), inference(cnfTransformation, [status(thm)], [f_84])).
% 18.86/9.95  tff(c_48433, plain, (![A_1771]: (k2_relat_1(A_1771)!='#skF_4' | A_1771='#skF_4' | ~v1_relat_1(A_1771))), inference(demodulation, [status(thm), theory('equality')], [c_47892, c_47892, c_36])).
% 18.86/9.95  tff(c_48453, plain, (k2_relat_1(k2_funct_1('#skF_4'))!='#skF_4' | k2_funct_1('#skF_4')='#skF_4'), inference(resolution, [status(thm)], [c_25464, c_48433])).
% 18.86/9.95  tff(c_48528, plain, (k2_relat_1(k2_funct_1('#skF_4'))!='#skF_4'), inference(splitLeft, [status(thm)], [c_48453])).
% 18.86/9.95  tff(c_44, plain, (![A_23]: (k1_relat_1(k6_relat_1(A_23))=A_23)), inference(cnfTransformation, [status(thm)], [f_94])).
% 18.86/9.95  tff(c_191, plain, (![A_68]: (k1_relat_1(k6_partfun1(A_68))=A_68)), inference(demodulation, [status(thm), theory('equality')], [c_96, c_44])).
% 18.86/9.95  tff(c_200, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_169, c_191])).
% 18.86/9.95  tff(c_47904, plain, (k1_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_47892, c_47892, c_200])).
% 18.86/9.95  tff(c_48578, plain, (![A_1785]: (k4_relat_1(A_1785)=k2_funct_1(A_1785) | ~v2_funct_1(A_1785) | ~v1_funct_1(A_1785) | ~v1_relat_1(A_1785))), inference(cnfTransformation, [status(thm)], [f_111])).
% 18.86/9.95  tff(c_48584, plain, (k4_relat_1('#skF_4')=k2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_120, c_48578])).
% 18.86/9.95  tff(c_48590, plain, (k4_relat_1('#skF_4')=k2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_25467, c_126, c_48584])).
% 18.86/9.95  tff(c_48594, plain, (k2_relat_1(k2_funct_1('#skF_4'))=k1_relat_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_48590, c_32])).
% 18.86/9.95  tff(c_48604, plain, (k2_relat_1(k2_funct_1('#skF_4'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_25467, c_47904, c_48594])).
% 18.86/9.95  tff(c_48606, plain, $false, inference(negUnitSimplification, [status(thm)], [c_48528, c_48604])).
% 18.86/9.95  tff(c_48607, plain, (k2_funct_1('#skF_4')='#skF_4'), inference(splitRight, [status(thm)], [c_48453])).
% 18.86/9.95  tff(c_48613, plain, (~v1_funct_2('#skF_4', '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_48607, c_25245])).
% 18.86/9.95  tff(c_49244, plain, (~v1_funct_2('#skF_4', '#skF_4', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_49240, c_48613])).
% 18.86/9.95  tff(c_64, plain, (![A_29]: (v1_relat_1(k6_relat_1(A_29)))), inference(cnfTransformation, [status(thm)], [f_127])).
% 18.86/9.95  tff(c_130, plain, (![A_29]: (v1_relat_1(k6_partfun1(A_29)))), inference(demodulation, [status(thm), theory('equality')], [c_96, c_64])).
% 18.86/9.95  tff(c_223, plain, (![A_73]: (k2_relat_1(A_73)!=k1_xboole_0 | k1_xboole_0=A_73 | ~v1_relat_1(A_73))), inference(cnfTransformation, [status(thm)], [f_84])).
% 18.86/9.95  tff(c_235, plain, (![A_29]: (k2_relat_1(k6_partfun1(A_29))!=k1_xboole_0 | k6_partfun1(A_29)=k1_xboole_0)), inference(resolution, [status(thm)], [c_130, c_223])).
% 18.86/9.95  tff(c_246, plain, (![A_74]: (k1_xboole_0!=A_74 | k6_partfun1(A_74)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_134, c_235])).
% 18.86/9.95  tff(c_92, plain, (![A_54]: (v1_partfun1(k6_partfun1(A_54), A_54))), inference(cnfTransformation, [status(thm)], [f_214])).
% 18.86/9.95  tff(c_252, plain, (![A_74]: (v1_partfun1(k1_xboole_0, A_74) | k1_xboole_0!=A_74)), inference(superposition, [status(thm), theory('equality')], [c_246, c_92])).
% 18.86/9.95  tff(c_48111, plain, (v1_partfun1('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_47892, c_47892, c_252])).
% 18.86/9.95  tff(c_48612, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_48607, c_25246])).
% 18.86/9.95  tff(c_49243, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_49240, c_48612])).
% 18.86/9.95  tff(c_49437, plain, (![C_1842, A_1843, B_1844]: (v1_funct_2(C_1842, A_1843, B_1844) | ~v1_partfun1(C_1842, A_1843) | ~v1_funct_1(C_1842) | ~m1_subset_1(C_1842, k1_zfmisc_1(k2_zfmisc_1(A_1843, B_1844))))), inference(cnfTransformation, [status(thm)], [f_210])).
% 18.86/9.95  tff(c_49440, plain, (v1_funct_2('#skF_4', '#skF_4', '#skF_2') | ~v1_partfun1('#skF_4', '#skF_4') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_49243, c_49437])).
% 18.86/9.95  tff(c_49463, plain, (v1_funct_2('#skF_4', '#skF_4', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_126, c_48111, c_49440])).
% 18.86/9.95  tff(c_49465, plain, $false, inference(negUnitSimplification, [status(thm)], [c_49244, c_49463])).
% 18.86/9.95  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 18.86/9.95  
% 18.86/9.95  Inference rules
% 18.86/9.95  ----------------------
% 18.86/9.95  #Ref     : 0
% 18.86/9.95  #Sup     : 11162
% 18.86/9.95  #Fact    : 0
% 18.86/9.95  #Define  : 0
% 18.86/9.95  #Split   : 121
% 18.86/9.95  #Chain   : 0
% 18.86/9.95  #Close   : 0
% 18.86/9.95  
% 18.86/9.95  Ordering : KBO
% 18.86/9.95  
% 18.86/9.95  Simplification rules
% 18.86/9.95  ----------------------
% 18.86/9.95  #Subsume      : 4348
% 18.86/9.95  #Demod        : 13523
% 18.86/9.95  #Tautology    : 3881
% 18.86/9.95  #SimpNegUnit  : 817
% 18.86/9.95  #BackRed      : 312
% 18.86/9.95  
% 18.86/9.95  #Partial instantiations: 0
% 18.86/9.95  #Strategies tried      : 1
% 18.86/9.95  
% 18.86/9.95  Timing (in seconds)
% 18.86/9.95  ----------------------
% 18.86/9.95  Preprocessing        : 0.40
% 18.86/9.95  Parsing              : 0.21
% 18.86/9.95  CNF conversion       : 0.03
% 18.86/9.95  Main loop            : 8.75
% 18.86/9.95  Inferencing          : 1.83
% 18.86/9.95  Reduction            : 3.76
% 18.86/9.96  Demodulation         : 2.94
% 18.86/9.96  BG Simplification    : 0.18
% 18.86/9.96  Subsumption          : 2.49
% 18.86/9.96  Abstraction          : 0.25
% 18.86/9.96  MUC search           : 0.00
% 18.86/9.96  Cooper               : 0.00
% 18.86/9.96  Total                : 9.20
% 18.86/9.96  Index Insertion      : 0.00
% 18.86/9.96  Index Deletion       : 0.00
% 18.86/9.96  Index Matching       : 0.00
% 18.86/9.96  BG Taut test         : 0.00
%------------------------------------------------------------------------------
