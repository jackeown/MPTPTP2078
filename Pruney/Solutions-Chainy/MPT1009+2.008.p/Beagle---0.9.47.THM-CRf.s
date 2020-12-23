%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:14:43 EST 2020

% Result     : Theorem 5.53s
% Output     : CNFRefutation 5.66s
% Verified   : 
% Statistics : Number of formulae       :  115 ( 498 expanded)
%              Number of leaves         :   40 ( 185 expanded)
%              Depth                    :   14
%              Number of atoms          :  183 (1135 expanded)
%              Number of equality atoms :   44 ( 241 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k1_enumset1 > k9_relat_1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k7_relset_1,type,(
    k7_relset_1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

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

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_117,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,k1_tarski(A),B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A),B))) )
       => ( B != k1_xboole_0
         => r1_tarski(k7_relset_1(k1_tarski(A),B,D,C),k1_tarski(k1_funct_1(D,A))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_funct_2)).

tff(f_87,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_75,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k9_relat_1(B,A),k2_relat_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t144_relat_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_47,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_93,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_49,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_83,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( k1_relat_1(B) = k1_tarski(A)
       => k2_relat_1(B) = k1_tarski(k1_funct_1(B,A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_funct_1)).

tff(f_65,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k1_tarski(B))
    <=> ( A = k1_xboole_0
        | A = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).

tff(f_71,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_105,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( ( r1_tarski(k1_relat_1(C),A)
          & r1_tarski(k2_relat_1(C),B) )
       => m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_relset_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_97,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(c_58,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_1'),'#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_150,plain,(
    ! [C_53,A_54,B_55] :
      ( v1_relat_1(C_53)
      | ~ m1_subset_1(C_53,k1_zfmisc_1(k2_zfmisc_1(A_54,B_55))) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_167,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_58,c_150])).

tff(c_40,plain,(
    ! [B_21,A_20] :
      ( r1_tarski(k9_relat_1(B_21,A_20),k2_relat_1(B_21))
      | ~ v1_relat_1(B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_28,plain,(
    ! [A_11,B_12] :
      ( m1_subset_1(A_11,k1_zfmisc_1(B_12))
      | ~ r1_tarski(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_22,plain,(
    ! [B_9] : k2_zfmisc_1(k1_xboole_0,B_9) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_277,plain,(
    ! [C_77,B_78,A_79] :
      ( v5_relat_1(C_77,B_78)
      | ~ m1_subset_1(C_77,k1_zfmisc_1(k2_zfmisc_1(A_79,B_78))) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_427,plain,(
    ! [C_95,B_96] :
      ( v5_relat_1(C_95,B_96)
      | ~ m1_subset_1(C_95,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_277])).

tff(c_434,plain,(
    ! [A_11,B_96] :
      ( v5_relat_1(A_11,B_96)
      | ~ r1_tarski(A_11,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_28,c_427])).

tff(c_24,plain,(
    ! [A_10] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_10)) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_109,plain,(
    ! [A_47,B_48] :
      ( r1_tarski(A_47,B_48)
      | ~ m1_subset_1(A_47,k1_zfmisc_1(B_48)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_121,plain,(
    ! [A_10] : r1_tarski(k1_xboole_0,A_10) ),
    inference(resolution,[status(thm)],[c_24,c_109])).

tff(c_62,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_606,plain,(
    ! [B_118,A_119] :
      ( k1_tarski(k1_funct_1(B_118,A_119)) = k2_relat_1(B_118)
      | k1_tarski(A_119) != k1_relat_1(B_118)
      | ~ v1_funct_1(B_118)
      | ~ v1_relat_1(B_118) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_54,plain,(
    ~ r1_tarski(k7_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4','#skF_3'),k1_tarski(k1_funct_1('#skF_4','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_615,plain,
    ( ~ r1_tarski(k7_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4','#skF_3'),k2_relat_1('#skF_4'))
    | k1_tarski('#skF_1') != k1_relat_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_606,c_54])).

tff(c_621,plain,
    ( ~ r1_tarski(k7_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4','#skF_3'),k2_relat_1('#skF_4'))
    | k1_tarski('#skF_1') != k1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_167,c_62,c_615])).

tff(c_641,plain,(
    k1_tarski('#skF_1') != k1_relat_1('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_621])).

tff(c_298,plain,(
    ! [C_80,A_81,B_82] :
      ( v4_relat_1(C_80,A_81)
      | ~ m1_subset_1(C_80,k1_zfmisc_1(k2_zfmisc_1(A_81,B_82))) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_317,plain,(
    v4_relat_1('#skF_4',k1_tarski('#skF_1')) ),
    inference(resolution,[status(thm)],[c_58,c_298])).

tff(c_34,plain,(
    ! [B_17,A_16] :
      ( r1_tarski(k1_relat_1(B_17),A_16)
      | ~ v4_relat_1(B_17,A_16)
      | ~ v1_relat_1(B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_362,plain,(
    ! [B_87,A_88] :
      ( k1_tarski(B_87) = A_88
      | k1_xboole_0 = A_88
      | ~ r1_tarski(A_88,k1_tarski(B_87)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_2858,plain,(
    ! [B_287,B_288] :
      ( k1_tarski(B_287) = k1_relat_1(B_288)
      | k1_relat_1(B_288) = k1_xboole_0
      | ~ v4_relat_1(B_288,k1_tarski(B_287))
      | ~ v1_relat_1(B_288) ) ),
    inference(resolution,[status(thm)],[c_34,c_362])).

tff(c_2912,plain,
    ( k1_tarski('#skF_1') = k1_relat_1('#skF_4')
    | k1_relat_1('#skF_4') = k1_xboole_0
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_317,c_2858])).

tff(c_2945,plain,
    ( k1_tarski('#skF_1') = k1_relat_1('#skF_4')
    | k1_relat_1('#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_167,c_2912])).

tff(c_2946,plain,(
    k1_relat_1('#skF_4') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_641,c_2945])).

tff(c_38,plain,(
    ! [B_19,A_18] :
      ( r1_tarski(k2_relat_1(B_19),A_18)
      | ~ v5_relat_1(B_19,A_18)
      | ~ v1_relat_1(B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_20,plain,(
    ! [A_8] : k2_zfmisc_1(A_8,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_840,plain,(
    ! [C_152,A_153,B_154] :
      ( m1_subset_1(C_152,k1_zfmisc_1(k2_zfmisc_1(A_153,B_154)))
      | ~ r1_tarski(k2_relat_1(C_152),B_154)
      | ~ r1_tarski(k1_relat_1(C_152),A_153)
      | ~ v1_relat_1(C_152) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_3603,plain,(
    ! [C_302,A_303] :
      ( m1_subset_1(C_302,k1_zfmisc_1(k1_xboole_0))
      | ~ r1_tarski(k2_relat_1(C_302),k1_xboole_0)
      | ~ r1_tarski(k1_relat_1(C_302),A_303)
      | ~ v1_relat_1(C_302) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_840])).

tff(c_3628,plain,(
    ! [B_304,A_305] :
      ( m1_subset_1(B_304,k1_zfmisc_1(k1_xboole_0))
      | ~ r1_tarski(k1_relat_1(B_304),A_305)
      | ~ v5_relat_1(B_304,k1_xboole_0)
      | ~ v1_relat_1(B_304) ) ),
    inference(resolution,[status(thm)],[c_38,c_3603])).

tff(c_3634,plain,(
    ! [A_305] :
      ( m1_subset_1('#skF_4',k1_zfmisc_1(k1_xboole_0))
      | ~ r1_tarski(k1_xboole_0,A_305)
      | ~ v5_relat_1('#skF_4',k1_xboole_0)
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2946,c_3628])).

tff(c_3656,plain,
    ( m1_subset_1('#skF_4',k1_zfmisc_1(k1_xboole_0))
    | ~ v5_relat_1('#skF_4',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_167,c_121,c_3634])).

tff(c_3667,plain,(
    ~ v5_relat_1('#skF_4',k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_3656])).

tff(c_3671,plain,(
    ~ r1_tarski('#skF_4',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_434,c_3667])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_3765,plain,(
    ! [C_309,B_310] :
      ( m1_subset_1(C_309,k1_zfmisc_1(k1_xboole_0))
      | ~ r1_tarski(k2_relat_1(C_309),B_310)
      | ~ r1_tarski(k1_relat_1(C_309),k1_xboole_0)
      | ~ v1_relat_1(C_309) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_840])).

tff(c_3950,plain,(
    ! [C_314] :
      ( m1_subset_1(C_314,k1_zfmisc_1(k1_xboole_0))
      | ~ r1_tarski(k1_relat_1(C_314),k1_xboole_0)
      | ~ v1_relat_1(C_314) ) ),
    inference(resolution,[status(thm)],[c_6,c_3765])).

tff(c_3956,plain,
    ( m1_subset_1('#skF_4',k1_zfmisc_1(k1_xboole_0))
    | ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_2946,c_3950])).

tff(c_3976,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_167,c_6,c_3956])).

tff(c_26,plain,(
    ! [A_11,B_12] :
      ( r1_tarski(A_11,B_12)
      | ~ m1_subset_1(A_11,k1_zfmisc_1(B_12)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_4001,plain,(
    r1_tarski('#skF_4',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_3976,c_26])).

tff(c_4013,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3671,c_4001])).

tff(c_4014,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k1_xboole_0)) ),
    inference(splitRight,[status(thm)],[c_3656])).

tff(c_4199,plain,(
    r1_tarski('#skF_4',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_4014,c_26])).

tff(c_124,plain,(
    ! [B_50,A_51] :
      ( B_50 = A_51
      | ~ r1_tarski(B_50,A_51)
      | ~ r1_tarski(A_51,B_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_132,plain,(
    ! [A_10] :
      ( k1_xboole_0 = A_10
      | ~ r1_tarski(A_10,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_121,c_124])).

tff(c_4233,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_4199,c_132])).

tff(c_4340,plain,(
    ! [A_10] : r1_tarski('#skF_4',A_10) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4233,c_121])).

tff(c_4015,plain,(
    v5_relat_1('#skF_4',k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_3656])).

tff(c_399,plain,(
    ! [B_93,A_94] :
      ( r1_tarski(k2_relat_1(B_93),A_94)
      | ~ v5_relat_1(B_93,A_94)
      | ~ v1_relat_1(B_93) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_425,plain,(
    ! [B_93] :
      ( k2_relat_1(B_93) = k1_xboole_0
      | ~ v5_relat_1(B_93,k1_xboole_0)
      | ~ v1_relat_1(B_93) ) ),
    inference(resolution,[status(thm)],[c_399,c_132])).

tff(c_4018,plain,
    ( k2_relat_1('#skF_4') = k1_xboole_0
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_4015,c_425])).

tff(c_4021,plain,(
    k2_relat_1('#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_167,c_4018])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_1265,plain,(
    ! [B_203,A_204] :
      ( k2_relat_1(B_203) = A_204
      | ~ r1_tarski(A_204,k2_relat_1(B_203))
      | ~ v5_relat_1(B_203,A_204)
      | ~ v1_relat_1(B_203) ) ),
    inference(resolution,[status(thm)],[c_399,c_2])).

tff(c_1850,plain,(
    ! [B_260,A_261] :
      ( k9_relat_1(B_260,A_261) = k2_relat_1(B_260)
      | ~ v5_relat_1(B_260,k9_relat_1(B_260,A_261))
      | ~ v1_relat_1(B_260) ) ),
    inference(resolution,[status(thm)],[c_40,c_1265])).

tff(c_1884,plain,(
    ! [A_11,A_261] :
      ( k9_relat_1(A_11,A_261) = k2_relat_1(A_11)
      | ~ v1_relat_1(A_11)
      | ~ r1_tarski(A_11,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_434,c_1850])).

tff(c_4201,plain,(
    ! [A_261] :
      ( k9_relat_1('#skF_4',A_261) = k2_relat_1('#skF_4')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_4199,c_1884])).

tff(c_4222,plain,(
    ! [A_261] : k9_relat_1('#skF_4',A_261) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_167,c_4021,c_4201])).

tff(c_4636,plain,(
    ! [A_261] : k9_relat_1('#skF_4',A_261) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4233,c_4222])).

tff(c_717,plain,(
    ! [A_130,B_131,C_132,D_133] :
      ( k7_relset_1(A_130,B_131,C_132,D_133) = k9_relat_1(C_132,D_133)
      | ~ m1_subset_1(C_132,k1_zfmisc_1(k2_zfmisc_1(A_130,B_131))) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_731,plain,(
    ! [D_133] : k7_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4',D_133) = k9_relat_1('#skF_4',D_133) ),
    inference(resolution,[status(thm)],[c_58,c_717])).

tff(c_758,plain,(
    ~ r1_tarski(k9_relat_1('#skF_4','#skF_3'),k1_tarski(k1_funct_1('#skF_4','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_731,c_54])).

tff(c_4637,plain,(
    ~ r1_tarski('#skF_4',k1_tarski(k1_funct_1('#skF_4','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4636,c_758])).

tff(c_4641,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4340,c_4637])).

tff(c_4643,plain,(
    k1_tarski('#skF_1') = k1_relat_1('#skF_4') ),
    inference(splitRight,[status(thm)],[c_621])).

tff(c_4649,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'),'#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4643,c_58])).

tff(c_4700,plain,(
    ! [A_323,B_324,C_325,D_326] :
      ( k7_relset_1(A_323,B_324,C_325,D_326) = k9_relat_1(C_325,D_326)
      | ~ m1_subset_1(C_325,k1_zfmisc_1(k2_zfmisc_1(A_323,B_324))) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_4713,plain,(
    ! [D_326] : k7_relset_1(k1_relat_1('#skF_4'),'#skF_2','#skF_4',D_326) = k9_relat_1('#skF_4',D_326) ),
    inference(resolution,[status(thm)],[c_4649,c_4700])).

tff(c_4642,plain,(
    ~ r1_tarski(k7_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4','#skF_3'),k2_relat_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_621])).

tff(c_4780,plain,(
    ~ r1_tarski(k7_relset_1(k1_relat_1('#skF_4'),'#skF_2','#skF_4','#skF_3'),k2_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4643,c_4642])).

tff(c_4782,plain,(
    ~ r1_tarski(k9_relat_1('#skF_4','#skF_3'),k2_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4713,c_4780])).

tff(c_4795,plain,(
    ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_40,c_4782])).

tff(c_4799,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_167,c_4795])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:45:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.53/2.06  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.53/2.06  
% 5.53/2.06  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.53/2.07  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k1_enumset1 > k9_relat_1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 5.53/2.07  
% 5.53/2.07  %Foreground sorts:
% 5.53/2.07  
% 5.53/2.07  
% 5.53/2.07  %Background operators:
% 5.53/2.07  
% 5.53/2.07  
% 5.53/2.07  %Foreground operators:
% 5.53/2.07  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 5.53/2.07  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.53/2.07  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.53/2.07  tff(k1_tarski, type, k1_tarski: $i > $i).
% 5.53/2.07  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.53/2.07  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.53/2.07  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 5.53/2.07  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 5.53/2.07  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 5.53/2.07  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 5.53/2.07  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 5.53/2.07  tff('#skF_2', type, '#skF_2': $i).
% 5.53/2.07  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 5.53/2.07  tff('#skF_3', type, '#skF_3': $i).
% 5.53/2.07  tff('#skF_1', type, '#skF_1': $i).
% 5.53/2.07  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 5.53/2.07  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.53/2.07  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 5.53/2.07  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.53/2.07  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.53/2.07  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 5.53/2.07  tff('#skF_4', type, '#skF_4': $i).
% 5.53/2.07  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.53/2.07  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 5.53/2.07  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 5.53/2.07  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.53/2.07  
% 5.66/2.09  tff(f_117, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, k1_tarski(A), B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A), B)))) => (~(B = k1_xboole_0) => r1_tarski(k7_relset_1(k1_tarski(A), B, D, C), k1_tarski(k1_funct_1(D, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_funct_2)).
% 5.66/2.09  tff(f_87, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 5.66/2.09  tff(f_75, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k9_relat_1(B, A), k2_relat_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t144_relat_1)).
% 5.66/2.09  tff(f_53, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 5.66/2.09  tff(f_47, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 5.66/2.09  tff(f_93, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 5.66/2.09  tff(f_49, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 5.66/2.09  tff(f_83, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((k1_relat_1(B) = k1_tarski(A)) => (k2_relat_1(B) = k1_tarski(k1_funct_1(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t14_funct_1)).
% 5.66/2.09  tff(f_65, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d18_relat_1)).
% 5.66/2.09  tff(f_41, axiom, (![A, B]: (r1_tarski(A, k1_tarski(B)) <=> ((A = k1_xboole_0) | (A = k1_tarski(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_zfmisc_1)).
% 5.66/2.09  tff(f_71, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 5.66/2.09  tff(f_105, axiom, (![A, B, C]: (v1_relat_1(C) => ((r1_tarski(k1_relat_1(C), A) & r1_tarski(k2_relat_1(C), B)) => m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_relset_1)).
% 5.66/2.09  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 5.66/2.09  tff(f_97, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 5.66/2.09  tff(c_58, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_1'), '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_117])).
% 5.66/2.09  tff(c_150, plain, (![C_53, A_54, B_55]: (v1_relat_1(C_53) | ~m1_subset_1(C_53, k1_zfmisc_1(k2_zfmisc_1(A_54, B_55))))), inference(cnfTransformation, [status(thm)], [f_87])).
% 5.66/2.09  tff(c_167, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_58, c_150])).
% 5.66/2.09  tff(c_40, plain, (![B_21, A_20]: (r1_tarski(k9_relat_1(B_21, A_20), k2_relat_1(B_21)) | ~v1_relat_1(B_21))), inference(cnfTransformation, [status(thm)], [f_75])).
% 5.66/2.09  tff(c_28, plain, (![A_11, B_12]: (m1_subset_1(A_11, k1_zfmisc_1(B_12)) | ~r1_tarski(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_53])).
% 5.66/2.09  tff(c_22, plain, (![B_9]: (k2_zfmisc_1(k1_xboole_0, B_9)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_47])).
% 5.66/2.09  tff(c_277, plain, (![C_77, B_78, A_79]: (v5_relat_1(C_77, B_78) | ~m1_subset_1(C_77, k1_zfmisc_1(k2_zfmisc_1(A_79, B_78))))), inference(cnfTransformation, [status(thm)], [f_93])).
% 5.66/2.09  tff(c_427, plain, (![C_95, B_96]: (v5_relat_1(C_95, B_96) | ~m1_subset_1(C_95, k1_zfmisc_1(k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_22, c_277])).
% 5.66/2.09  tff(c_434, plain, (![A_11, B_96]: (v5_relat_1(A_11, B_96) | ~r1_tarski(A_11, k1_xboole_0))), inference(resolution, [status(thm)], [c_28, c_427])).
% 5.66/2.09  tff(c_24, plain, (![A_10]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_10)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 5.66/2.09  tff(c_109, plain, (![A_47, B_48]: (r1_tarski(A_47, B_48) | ~m1_subset_1(A_47, k1_zfmisc_1(B_48)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 5.66/2.09  tff(c_121, plain, (![A_10]: (r1_tarski(k1_xboole_0, A_10))), inference(resolution, [status(thm)], [c_24, c_109])).
% 5.66/2.09  tff(c_62, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_117])).
% 5.66/2.09  tff(c_606, plain, (![B_118, A_119]: (k1_tarski(k1_funct_1(B_118, A_119))=k2_relat_1(B_118) | k1_tarski(A_119)!=k1_relat_1(B_118) | ~v1_funct_1(B_118) | ~v1_relat_1(B_118))), inference(cnfTransformation, [status(thm)], [f_83])).
% 5.66/2.09  tff(c_54, plain, (~r1_tarski(k7_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4', '#skF_3'), k1_tarski(k1_funct_1('#skF_4', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_117])).
% 5.66/2.09  tff(c_615, plain, (~r1_tarski(k7_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4', '#skF_3'), k2_relat_1('#skF_4')) | k1_tarski('#skF_1')!=k1_relat_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_606, c_54])).
% 5.66/2.09  tff(c_621, plain, (~r1_tarski(k7_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4', '#skF_3'), k2_relat_1('#skF_4')) | k1_tarski('#skF_1')!=k1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_167, c_62, c_615])).
% 5.66/2.09  tff(c_641, plain, (k1_tarski('#skF_1')!=k1_relat_1('#skF_4')), inference(splitLeft, [status(thm)], [c_621])).
% 5.66/2.09  tff(c_298, plain, (![C_80, A_81, B_82]: (v4_relat_1(C_80, A_81) | ~m1_subset_1(C_80, k1_zfmisc_1(k2_zfmisc_1(A_81, B_82))))), inference(cnfTransformation, [status(thm)], [f_93])).
% 5.66/2.09  tff(c_317, plain, (v4_relat_1('#skF_4', k1_tarski('#skF_1'))), inference(resolution, [status(thm)], [c_58, c_298])).
% 5.66/2.09  tff(c_34, plain, (![B_17, A_16]: (r1_tarski(k1_relat_1(B_17), A_16) | ~v4_relat_1(B_17, A_16) | ~v1_relat_1(B_17))), inference(cnfTransformation, [status(thm)], [f_65])).
% 5.66/2.09  tff(c_362, plain, (![B_87, A_88]: (k1_tarski(B_87)=A_88 | k1_xboole_0=A_88 | ~r1_tarski(A_88, k1_tarski(B_87)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 5.66/2.09  tff(c_2858, plain, (![B_287, B_288]: (k1_tarski(B_287)=k1_relat_1(B_288) | k1_relat_1(B_288)=k1_xboole_0 | ~v4_relat_1(B_288, k1_tarski(B_287)) | ~v1_relat_1(B_288))), inference(resolution, [status(thm)], [c_34, c_362])).
% 5.66/2.09  tff(c_2912, plain, (k1_tarski('#skF_1')=k1_relat_1('#skF_4') | k1_relat_1('#skF_4')=k1_xboole_0 | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_317, c_2858])).
% 5.66/2.09  tff(c_2945, plain, (k1_tarski('#skF_1')=k1_relat_1('#skF_4') | k1_relat_1('#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_167, c_2912])).
% 5.66/2.09  tff(c_2946, plain, (k1_relat_1('#skF_4')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_641, c_2945])).
% 5.66/2.09  tff(c_38, plain, (![B_19, A_18]: (r1_tarski(k2_relat_1(B_19), A_18) | ~v5_relat_1(B_19, A_18) | ~v1_relat_1(B_19))), inference(cnfTransformation, [status(thm)], [f_71])).
% 5.66/2.09  tff(c_20, plain, (![A_8]: (k2_zfmisc_1(A_8, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_47])).
% 5.66/2.09  tff(c_840, plain, (![C_152, A_153, B_154]: (m1_subset_1(C_152, k1_zfmisc_1(k2_zfmisc_1(A_153, B_154))) | ~r1_tarski(k2_relat_1(C_152), B_154) | ~r1_tarski(k1_relat_1(C_152), A_153) | ~v1_relat_1(C_152))), inference(cnfTransformation, [status(thm)], [f_105])).
% 5.66/2.09  tff(c_3603, plain, (![C_302, A_303]: (m1_subset_1(C_302, k1_zfmisc_1(k1_xboole_0)) | ~r1_tarski(k2_relat_1(C_302), k1_xboole_0) | ~r1_tarski(k1_relat_1(C_302), A_303) | ~v1_relat_1(C_302))), inference(superposition, [status(thm), theory('equality')], [c_20, c_840])).
% 5.66/2.09  tff(c_3628, plain, (![B_304, A_305]: (m1_subset_1(B_304, k1_zfmisc_1(k1_xboole_0)) | ~r1_tarski(k1_relat_1(B_304), A_305) | ~v5_relat_1(B_304, k1_xboole_0) | ~v1_relat_1(B_304))), inference(resolution, [status(thm)], [c_38, c_3603])).
% 5.66/2.09  tff(c_3634, plain, (![A_305]: (m1_subset_1('#skF_4', k1_zfmisc_1(k1_xboole_0)) | ~r1_tarski(k1_xboole_0, A_305) | ~v5_relat_1('#skF_4', k1_xboole_0) | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_2946, c_3628])).
% 5.66/2.09  tff(c_3656, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k1_xboole_0)) | ~v5_relat_1('#skF_4', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_167, c_121, c_3634])).
% 5.66/2.09  tff(c_3667, plain, (~v5_relat_1('#skF_4', k1_xboole_0)), inference(splitLeft, [status(thm)], [c_3656])).
% 5.66/2.09  tff(c_3671, plain, (~r1_tarski('#skF_4', k1_xboole_0)), inference(resolution, [status(thm)], [c_434, c_3667])).
% 5.66/2.09  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.66/2.09  tff(c_3765, plain, (![C_309, B_310]: (m1_subset_1(C_309, k1_zfmisc_1(k1_xboole_0)) | ~r1_tarski(k2_relat_1(C_309), B_310) | ~r1_tarski(k1_relat_1(C_309), k1_xboole_0) | ~v1_relat_1(C_309))), inference(superposition, [status(thm), theory('equality')], [c_22, c_840])).
% 5.66/2.09  tff(c_3950, plain, (![C_314]: (m1_subset_1(C_314, k1_zfmisc_1(k1_xboole_0)) | ~r1_tarski(k1_relat_1(C_314), k1_xboole_0) | ~v1_relat_1(C_314))), inference(resolution, [status(thm)], [c_6, c_3765])).
% 5.66/2.09  tff(c_3956, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k1_xboole_0)) | ~r1_tarski(k1_xboole_0, k1_xboole_0) | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_2946, c_3950])).
% 5.66/2.09  tff(c_3976, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_167, c_6, c_3956])).
% 5.66/2.09  tff(c_26, plain, (![A_11, B_12]: (r1_tarski(A_11, B_12) | ~m1_subset_1(A_11, k1_zfmisc_1(B_12)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 5.66/2.09  tff(c_4001, plain, (r1_tarski('#skF_4', k1_xboole_0)), inference(resolution, [status(thm)], [c_3976, c_26])).
% 5.66/2.09  tff(c_4013, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3671, c_4001])).
% 5.66/2.09  tff(c_4014, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k1_xboole_0))), inference(splitRight, [status(thm)], [c_3656])).
% 5.66/2.09  tff(c_4199, plain, (r1_tarski('#skF_4', k1_xboole_0)), inference(resolution, [status(thm)], [c_4014, c_26])).
% 5.66/2.09  tff(c_124, plain, (![B_50, A_51]: (B_50=A_51 | ~r1_tarski(B_50, A_51) | ~r1_tarski(A_51, B_50))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.66/2.09  tff(c_132, plain, (![A_10]: (k1_xboole_0=A_10 | ~r1_tarski(A_10, k1_xboole_0))), inference(resolution, [status(thm)], [c_121, c_124])).
% 5.66/2.09  tff(c_4233, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_4199, c_132])).
% 5.66/2.09  tff(c_4340, plain, (![A_10]: (r1_tarski('#skF_4', A_10))), inference(demodulation, [status(thm), theory('equality')], [c_4233, c_121])).
% 5.66/2.09  tff(c_4015, plain, (v5_relat_1('#skF_4', k1_xboole_0)), inference(splitRight, [status(thm)], [c_3656])).
% 5.66/2.09  tff(c_399, plain, (![B_93, A_94]: (r1_tarski(k2_relat_1(B_93), A_94) | ~v5_relat_1(B_93, A_94) | ~v1_relat_1(B_93))), inference(cnfTransformation, [status(thm)], [f_71])).
% 5.66/2.09  tff(c_425, plain, (![B_93]: (k2_relat_1(B_93)=k1_xboole_0 | ~v5_relat_1(B_93, k1_xboole_0) | ~v1_relat_1(B_93))), inference(resolution, [status(thm)], [c_399, c_132])).
% 5.66/2.09  tff(c_4018, plain, (k2_relat_1('#skF_4')=k1_xboole_0 | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_4015, c_425])).
% 5.66/2.09  tff(c_4021, plain, (k2_relat_1('#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_167, c_4018])).
% 5.66/2.09  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.66/2.09  tff(c_1265, plain, (![B_203, A_204]: (k2_relat_1(B_203)=A_204 | ~r1_tarski(A_204, k2_relat_1(B_203)) | ~v5_relat_1(B_203, A_204) | ~v1_relat_1(B_203))), inference(resolution, [status(thm)], [c_399, c_2])).
% 5.66/2.09  tff(c_1850, plain, (![B_260, A_261]: (k9_relat_1(B_260, A_261)=k2_relat_1(B_260) | ~v5_relat_1(B_260, k9_relat_1(B_260, A_261)) | ~v1_relat_1(B_260))), inference(resolution, [status(thm)], [c_40, c_1265])).
% 5.66/2.09  tff(c_1884, plain, (![A_11, A_261]: (k9_relat_1(A_11, A_261)=k2_relat_1(A_11) | ~v1_relat_1(A_11) | ~r1_tarski(A_11, k1_xboole_0))), inference(resolution, [status(thm)], [c_434, c_1850])).
% 5.66/2.09  tff(c_4201, plain, (![A_261]: (k9_relat_1('#skF_4', A_261)=k2_relat_1('#skF_4') | ~v1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_4199, c_1884])).
% 5.66/2.09  tff(c_4222, plain, (![A_261]: (k9_relat_1('#skF_4', A_261)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_167, c_4021, c_4201])).
% 5.66/2.09  tff(c_4636, plain, (![A_261]: (k9_relat_1('#skF_4', A_261)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_4233, c_4222])).
% 5.66/2.09  tff(c_717, plain, (![A_130, B_131, C_132, D_133]: (k7_relset_1(A_130, B_131, C_132, D_133)=k9_relat_1(C_132, D_133) | ~m1_subset_1(C_132, k1_zfmisc_1(k2_zfmisc_1(A_130, B_131))))), inference(cnfTransformation, [status(thm)], [f_97])).
% 5.66/2.09  tff(c_731, plain, (![D_133]: (k7_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4', D_133)=k9_relat_1('#skF_4', D_133))), inference(resolution, [status(thm)], [c_58, c_717])).
% 5.66/2.09  tff(c_758, plain, (~r1_tarski(k9_relat_1('#skF_4', '#skF_3'), k1_tarski(k1_funct_1('#skF_4', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_731, c_54])).
% 5.66/2.09  tff(c_4637, plain, (~r1_tarski('#skF_4', k1_tarski(k1_funct_1('#skF_4', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_4636, c_758])).
% 5.66/2.09  tff(c_4641, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4340, c_4637])).
% 5.66/2.09  tff(c_4643, plain, (k1_tarski('#skF_1')=k1_relat_1('#skF_4')), inference(splitRight, [status(thm)], [c_621])).
% 5.66/2.09  tff(c_4649, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'), '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_4643, c_58])).
% 5.66/2.09  tff(c_4700, plain, (![A_323, B_324, C_325, D_326]: (k7_relset_1(A_323, B_324, C_325, D_326)=k9_relat_1(C_325, D_326) | ~m1_subset_1(C_325, k1_zfmisc_1(k2_zfmisc_1(A_323, B_324))))), inference(cnfTransformation, [status(thm)], [f_97])).
% 5.66/2.09  tff(c_4713, plain, (![D_326]: (k7_relset_1(k1_relat_1('#skF_4'), '#skF_2', '#skF_4', D_326)=k9_relat_1('#skF_4', D_326))), inference(resolution, [status(thm)], [c_4649, c_4700])).
% 5.66/2.09  tff(c_4642, plain, (~r1_tarski(k7_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4', '#skF_3'), k2_relat_1('#skF_4'))), inference(splitRight, [status(thm)], [c_621])).
% 5.66/2.09  tff(c_4780, plain, (~r1_tarski(k7_relset_1(k1_relat_1('#skF_4'), '#skF_2', '#skF_4', '#skF_3'), k2_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_4643, c_4642])).
% 5.66/2.09  tff(c_4782, plain, (~r1_tarski(k9_relat_1('#skF_4', '#skF_3'), k2_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_4713, c_4780])).
% 5.66/2.09  tff(c_4795, plain, (~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_40, c_4782])).
% 5.66/2.09  tff(c_4799, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_167, c_4795])).
% 5.66/2.09  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.66/2.09  
% 5.66/2.09  Inference rules
% 5.66/2.09  ----------------------
% 5.66/2.09  #Ref     : 0
% 5.66/2.09  #Sup     : 987
% 5.66/2.09  #Fact    : 0
% 5.66/2.09  #Define  : 0
% 5.66/2.09  #Split   : 3
% 5.66/2.09  #Chain   : 0
% 5.66/2.09  #Close   : 0
% 5.66/2.09  
% 5.66/2.09  Ordering : KBO
% 5.66/2.09  
% 5.66/2.09  Simplification rules
% 5.66/2.09  ----------------------
% 5.66/2.09  #Subsume      : 91
% 5.66/2.09  #Demod        : 1672
% 5.66/2.09  #Tautology    : 558
% 5.66/2.09  #SimpNegUnit  : 2
% 5.66/2.09  #BackRed      : 84
% 5.66/2.09  
% 5.66/2.09  #Partial instantiations: 0
% 5.66/2.09  #Strategies tried      : 1
% 5.66/2.09  
% 5.66/2.09  Timing (in seconds)
% 5.66/2.09  ----------------------
% 5.66/2.09  Preprocessing        : 0.33
% 5.66/2.09  Parsing              : 0.17
% 5.66/2.09  CNF conversion       : 0.02
% 5.66/2.09  Main loop            : 0.94
% 5.66/2.09  Inferencing          : 0.30
% 5.66/2.09  Reduction            : 0.37
% 5.66/2.09  Demodulation         : 0.29
% 5.66/2.09  BG Simplification    : 0.04
% 5.66/2.09  Subsumption          : 0.17
% 5.66/2.09  Abstraction          : 0.04
% 5.66/2.09  MUC search           : 0.00
% 5.66/2.09  Cooper               : 0.00
% 5.66/2.09  Total                : 1.31
% 5.66/2.09  Index Insertion      : 0.00
% 5.66/2.09  Index Deletion       : 0.00
% 5.66/2.09  Index Matching       : 0.00
% 5.66/2.09  BG Taut test         : 0.00
%------------------------------------------------------------------------------
