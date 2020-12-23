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
% DateTime   : Thu Dec  3 10:15:02 EST 2020

% Result     : Theorem 3.03s
% Output     : CNFRefutation 3.34s
% Verified   : 
% Statistics : Number of formulae       :  117 (1059 expanded)
%              Number of leaves         :   43 ( 396 expanded)
%              Depth                    :   18
%              Number of atoms          :  232 (2999 expanded)
%              Number of equality atoms :   53 ( 971 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k2_relset_1 > k1_relset_1 > k1_enumset1 > k9_relat_1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

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

tff('#skF_5',type,(
    '#skF_5': $i )).

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

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

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

tff(f_44,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_152,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,k1_tarski(A),B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A),B))) )
       => ( B != k1_xboole_0
         => r1_tarski(k7_relset_1(k1_tarski(A),B,D,C),k1_tarski(k1_funct_1(D,A))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_funct_2)).

tff(f_36,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_117,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( ( k1_relat_1(C) = A
          & ! [D] :
              ( r2_hidden(D,A)
             => r2_hidden(k1_funct_1(C,D),B) ) )
       => ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_funct_2)).

tff(f_54,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_80,axiom,(
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

tff(f_58,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_140,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_hidden(C,A)
       => ( B = k1_xboole_0
          | r2_hidden(k1_funct_1(D,C),k2_relset_1(A,B,D)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_funct_2)).

tff(f_50,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_42,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_100,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r1_tarski(k2_relat_1(B),A)
       => ( v1_funct_1(B)
          & v1_funct_2(B,k1_relat_1(B),A)
          & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B),A))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_funct_2)).

tff(f_62,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_88,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => r1_tarski(k7_relset_1(A,B,D,C),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_funct_2)).

tff(f_128,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,k1_tarski(A),B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A),B))) )
     => ( B != k1_xboole_0
       => k2_relset_1(k1_tarski(A),B,C) = k1_tarski(k1_funct_1(C,A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_funct_2)).

tff(c_12,plain,(
    ! [A_9,B_10] : v1_relat_1(k2_zfmisc_1(A_9,B_10)) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_64,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_2'),'#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_88,plain,(
    ! [B_49,A_50] :
      ( v1_relat_1(B_49)
      | ~ m1_subset_1(B_49,k1_zfmisc_1(A_50))
      | ~ v1_relat_1(A_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_91,plain,
    ( v1_relat_1('#skF_5')
    | ~ v1_relat_1(k2_zfmisc_1(k1_tarski('#skF_2'),'#skF_3')) ),
    inference(resolution,[status(thm)],[c_64,c_88])).

tff(c_94,plain,(
    v1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_91])).

tff(c_68,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_46,plain,(
    ! [C_35,B_34] :
      ( r2_hidden('#skF_1'(k1_relat_1(C_35),B_34,C_35),k1_relat_1(C_35))
      | m1_subset_1(C_35,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(C_35),B_34)))
      | ~ v1_funct_1(C_35)
      | ~ v1_relat_1(C_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_62,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_66,plain,(
    v1_funct_2('#skF_5',k1_tarski('#skF_2'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_112,plain,(
    ! [A_62,B_63,C_64] :
      ( k1_relset_1(A_62,B_63,C_64) = k1_relat_1(C_64)
      | ~ m1_subset_1(C_64,k1_zfmisc_1(k2_zfmisc_1(A_62,B_63))) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_116,plain,(
    k1_relset_1(k1_tarski('#skF_2'),'#skF_3','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_64,c_112])).

tff(c_232,plain,(
    ! [B_100,A_101,C_102] :
      ( k1_xboole_0 = B_100
      | k1_relset_1(A_101,B_100,C_102) = A_101
      | ~ v1_funct_2(C_102,A_101,B_100)
      | ~ m1_subset_1(C_102,k1_zfmisc_1(k2_zfmisc_1(A_101,B_100))) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_238,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relset_1(k1_tarski('#skF_2'),'#skF_3','#skF_5') = k1_tarski('#skF_2')
    | ~ v1_funct_2('#skF_5',k1_tarski('#skF_2'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_64,c_232])).

tff(c_242,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_tarski('#skF_2') = k1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_116,c_238])).

tff(c_243,plain,(
    k1_tarski('#skF_2') = k1_relat_1('#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_242])).

tff(c_249,plain,(
    v1_funct_2('#skF_5',k1_relat_1('#skF_5'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_243,c_66])).

tff(c_248,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_5'),'#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_243,c_64])).

tff(c_121,plain,(
    ! [A_65,B_66,C_67] :
      ( k2_relset_1(A_65,B_66,C_67) = k2_relat_1(C_67)
      | ~ m1_subset_1(C_67,k1_zfmisc_1(k2_zfmisc_1(A_65,B_66))) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_125,plain,(
    k2_relset_1(k1_tarski('#skF_2'),'#skF_3','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_64,c_121])).

tff(c_245,plain,(
    k2_relset_1(k1_relat_1('#skF_5'),'#skF_3','#skF_5') = k2_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_243,c_125])).

tff(c_406,plain,(
    ! [D_130,C_131,A_132,B_133] :
      ( r2_hidden(k1_funct_1(D_130,C_131),k2_relset_1(A_132,B_133,D_130))
      | k1_xboole_0 = B_133
      | ~ r2_hidden(C_131,A_132)
      | ~ m1_subset_1(D_130,k1_zfmisc_1(k2_zfmisc_1(A_132,B_133)))
      | ~ v1_funct_2(D_130,A_132,B_133)
      | ~ v1_funct_1(D_130) ) ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_417,plain,(
    ! [C_131] :
      ( r2_hidden(k1_funct_1('#skF_5',C_131),k2_relat_1('#skF_5'))
      | k1_xboole_0 = '#skF_3'
      | ~ r2_hidden(C_131,k1_relat_1('#skF_5'))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_5'),'#skF_3')))
      | ~ v1_funct_2('#skF_5',k1_relat_1('#skF_5'),'#skF_3')
      | ~ v1_funct_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_245,c_406])).

tff(c_424,plain,(
    ! [C_131] :
      ( r2_hidden(k1_funct_1('#skF_5',C_131),k2_relat_1('#skF_5'))
      | k1_xboole_0 = '#skF_3'
      | ~ r2_hidden(C_131,k1_relat_1('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_249,c_248,c_417])).

tff(c_426,plain,(
    ! [C_134] :
      ( r2_hidden(k1_funct_1('#skF_5',C_134),k2_relat_1('#skF_5'))
      | ~ r2_hidden(C_134,k1_relat_1('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_424])).

tff(c_48,plain,(
    ! [C_35,B_34] :
      ( ~ r2_hidden(k1_funct_1(C_35,'#skF_1'(k1_relat_1(C_35),B_34,C_35)),B_34)
      | v1_funct_2(C_35,k1_relat_1(C_35),B_34)
      | ~ v1_funct_1(C_35)
      | ~ v1_relat_1(C_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_434,plain,
    ( v1_funct_2('#skF_5',k1_relat_1('#skF_5'),k2_relat_1('#skF_5'))
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5')
    | ~ r2_hidden('#skF_1'(k1_relat_1('#skF_5'),k2_relat_1('#skF_5'),'#skF_5'),k1_relat_1('#skF_5')) ),
    inference(resolution,[status(thm)],[c_426,c_48])).

tff(c_440,plain,
    ( v1_funct_2('#skF_5',k1_relat_1('#skF_5'),k2_relat_1('#skF_5'))
    | ~ r2_hidden('#skF_1'(k1_relat_1('#skF_5'),k2_relat_1('#skF_5'),'#skF_5'),k1_relat_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_68,c_434])).

tff(c_441,plain,(
    ~ r2_hidden('#skF_1'(k1_relat_1('#skF_5'),k2_relat_1('#skF_5'),'#skF_5'),k1_relat_1('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_440])).

tff(c_444,plain,
    ( m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_5'),k2_relat_1('#skF_5'))))
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_46,c_441])).

tff(c_450,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_5'),k2_relat_1('#skF_5')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_68,c_444])).

tff(c_14,plain,(
    ! [C_13,B_12,A_11] :
      ( v5_relat_1(C_13,B_12)
      | ~ m1_subset_1(C_13,k1_zfmisc_1(k2_zfmisc_1(A_11,B_12))) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_490,plain,(
    v5_relat_1('#skF_5',k2_relat_1('#skF_5')) ),
    inference(resolution,[status(thm)],[c_450,c_14])).

tff(c_10,plain,(
    ! [B_8,A_7] :
      ( r1_tarski(k2_relat_1(B_8),A_7)
      | ~ v5_relat_1(B_8,A_7)
      | ~ v1_relat_1(B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_148,plain,(
    ! [B_81,A_82] :
      ( m1_subset_1(B_81,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B_81),A_82)))
      | ~ r1_tarski(k2_relat_1(B_81),A_82)
      | ~ v1_funct_1(B_81)
      | ~ v1_relat_1(B_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_22,plain,(
    ! [A_20,B_21,C_22,D_23] :
      ( k7_relset_1(A_20,B_21,C_22,D_23) = k9_relat_1(C_22,D_23)
      | ~ m1_subset_1(C_22,k1_zfmisc_1(k2_zfmisc_1(A_20,B_21))) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_341,plain,(
    ! [B_106,A_107,D_108] :
      ( k7_relset_1(k1_relat_1(B_106),A_107,B_106,D_108) = k9_relat_1(B_106,D_108)
      | ~ r1_tarski(k2_relat_1(B_106),A_107)
      | ~ v1_funct_1(B_106)
      | ~ v1_relat_1(B_106) ) ),
    inference(resolution,[status(thm)],[c_148,c_22])).

tff(c_344,plain,(
    ! [B_8,A_7,D_108] :
      ( k7_relset_1(k1_relat_1(B_8),A_7,B_8,D_108) = k9_relat_1(B_8,D_108)
      | ~ v1_funct_1(B_8)
      | ~ v5_relat_1(B_8,A_7)
      | ~ v1_relat_1(B_8) ) ),
    inference(resolution,[status(thm)],[c_10,c_341])).

tff(c_50,plain,(
    ! [C_35,B_34] :
      ( r2_hidden('#skF_1'(k1_relat_1(C_35),B_34,C_35),k1_relat_1(C_35))
      | v1_funct_2(C_35,k1_relat_1(C_35),B_34)
      | ~ v1_funct_1(C_35)
      | ~ v1_relat_1(C_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_447,plain,
    ( v1_funct_2('#skF_5',k1_relat_1('#skF_5'),k2_relat_1('#skF_5'))
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_50,c_441])).

tff(c_453,plain,(
    v1_funct_2('#skF_5',k1_relat_1('#skF_5'),k2_relat_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_68,c_447])).

tff(c_36,plain,(
    ! [A_27,B_28,D_30,C_29] :
      ( r1_tarski(k7_relset_1(A_27,B_28,D_30,C_29),B_28)
      | ~ m1_subset_1(D_30,k1_zfmisc_1(k2_zfmisc_1(A_27,B_28)))
      | ~ v1_funct_2(D_30,A_27,B_28)
      | ~ v1_funct_1(D_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_455,plain,(
    ! [C_29] :
      ( r1_tarski(k7_relset_1(k1_relat_1('#skF_5'),k2_relat_1('#skF_5'),'#skF_5',C_29),k2_relat_1('#skF_5'))
      | ~ v1_funct_2('#skF_5',k1_relat_1('#skF_5'),k2_relat_1('#skF_5'))
      | ~ v1_funct_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_450,c_36])).

tff(c_563,plain,(
    ! [C_138] : r1_tarski(k7_relset_1(k1_relat_1('#skF_5'),k2_relat_1('#skF_5'),'#skF_5',C_138),k2_relat_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_453,c_455])).

tff(c_567,plain,(
    ! [D_108] :
      ( r1_tarski(k9_relat_1('#skF_5',D_108),k2_relat_1('#skF_5'))
      | ~ v1_funct_1('#skF_5')
      | ~ v5_relat_1('#skF_5',k2_relat_1('#skF_5'))
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_344,c_563])).

tff(c_569,plain,(
    ! [D_108] : r1_tarski(k9_relat_1('#skF_5',D_108),k2_relat_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_490,c_68,c_567])).

tff(c_401,plain,(
    ! [A_127,B_128,C_129] :
      ( k2_relset_1(k1_tarski(A_127),B_128,C_129) = k1_tarski(k1_funct_1(C_129,A_127))
      | k1_xboole_0 = B_128
      | ~ m1_subset_1(C_129,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A_127),B_128)))
      | ~ v1_funct_2(C_129,k1_tarski(A_127),B_128)
      | ~ v1_funct_1(C_129) ) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_404,plain,(
    ! [B_128,C_129] :
      ( k2_relset_1(k1_tarski('#skF_2'),B_128,C_129) = k1_tarski(k1_funct_1(C_129,'#skF_2'))
      | k1_xboole_0 = B_128
      | ~ m1_subset_1(C_129,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_5'),B_128)))
      | ~ v1_funct_2(C_129,k1_tarski('#skF_2'),B_128)
      | ~ v1_funct_1(C_129) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_243,c_401])).

tff(c_602,plain,(
    ! [B_141,C_142] :
      ( k2_relset_1(k1_relat_1('#skF_5'),B_141,C_142) = k1_tarski(k1_funct_1(C_142,'#skF_2'))
      | k1_xboole_0 = B_141
      | ~ m1_subset_1(C_142,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_5'),B_141)))
      | ~ v1_funct_2(C_142,k1_relat_1('#skF_5'),B_141)
      | ~ v1_funct_1(C_142) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_243,c_243,c_404])).

tff(c_608,plain,
    ( k2_relset_1(k1_relat_1('#skF_5'),'#skF_3','#skF_5') = k1_tarski(k1_funct_1('#skF_5','#skF_2'))
    | k1_xboole_0 = '#skF_3'
    | ~ v1_funct_2('#skF_5',k1_relat_1('#skF_5'),'#skF_3')
    | ~ v1_funct_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_248,c_602])).

tff(c_618,plain,
    ( k1_tarski(k1_funct_1('#skF_5','#skF_2')) = k2_relat_1('#skF_5')
    | k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_249,c_245,c_608])).

tff(c_619,plain,(
    k1_tarski(k1_funct_1('#skF_5','#skF_2')) = k2_relat_1('#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_618])).

tff(c_132,plain,(
    ! [A_72,B_73,C_74,D_75] :
      ( k7_relset_1(A_72,B_73,C_74,D_75) = k9_relat_1(C_74,D_75)
      | ~ m1_subset_1(C_74,k1_zfmisc_1(k2_zfmisc_1(A_72,B_73))) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_135,plain,(
    ! [D_75] : k7_relset_1(k1_tarski('#skF_2'),'#skF_3','#skF_5',D_75) = k9_relat_1('#skF_5',D_75) ),
    inference(resolution,[status(thm)],[c_64,c_132])).

tff(c_60,plain,(
    ~ r1_tarski(k7_relset_1(k1_tarski('#skF_2'),'#skF_3','#skF_5','#skF_4'),k1_tarski(k1_funct_1('#skF_5','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_136,plain,(
    ~ r1_tarski(k9_relat_1('#skF_5','#skF_4'),k1_tarski(k1_funct_1('#skF_5','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_135,c_60])).

tff(c_623,plain,(
    ~ r1_tarski(k9_relat_1('#skF_5','#skF_4'),k2_relat_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_619,c_136])).

tff(c_626,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_569,c_623])).

tff(c_628,plain,(
    r2_hidden('#skF_1'(k1_relat_1('#skF_5'),k2_relat_1('#skF_5'),'#skF_5'),k1_relat_1('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_440])).

tff(c_44,plain,(
    ! [C_35,B_34] :
      ( ~ r2_hidden(k1_funct_1(C_35,'#skF_1'(k1_relat_1(C_35),B_34,C_35)),B_34)
      | m1_subset_1(C_35,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(C_35),B_34)))
      | ~ v1_funct_1(C_35)
      | ~ v1_relat_1(C_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_430,plain,
    ( m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_5'),k2_relat_1('#skF_5'))))
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5')
    | ~ r2_hidden('#skF_1'(k1_relat_1('#skF_5'),k2_relat_1('#skF_5'),'#skF_5'),k1_relat_1('#skF_5')) ),
    inference(resolution,[status(thm)],[c_426,c_44])).

tff(c_437,plain,
    ( m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_5'),k2_relat_1('#skF_5'))))
    | ~ r2_hidden('#skF_1'(k1_relat_1('#skF_5'),k2_relat_1('#skF_5'),'#skF_5'),k1_relat_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_68,c_430])).

tff(c_652,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_5'),k2_relat_1('#skF_5')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_628,c_437])).

tff(c_689,plain,(
    v5_relat_1('#skF_5',k2_relat_1('#skF_5')) ),
    inference(resolution,[status(thm)],[c_652,c_14])).

tff(c_627,plain,(
    v1_funct_2('#skF_5',k1_relat_1('#skF_5'),k2_relat_1('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_440])).

tff(c_654,plain,(
    ! [C_29] :
      ( r1_tarski(k7_relset_1(k1_relat_1('#skF_5'),k2_relat_1('#skF_5'),'#skF_5',C_29),k2_relat_1('#skF_5'))
      | ~ v1_funct_2('#skF_5',k1_relat_1('#skF_5'),k2_relat_1('#skF_5'))
      | ~ v1_funct_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_652,c_36])).

tff(c_742,plain,(
    ! [C_146] : r1_tarski(k7_relset_1(k1_relat_1('#skF_5'),k2_relat_1('#skF_5'),'#skF_5',C_146),k2_relat_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_627,c_654])).

tff(c_746,plain,(
    ! [D_108] :
      ( r1_tarski(k9_relat_1('#skF_5',D_108),k2_relat_1('#skF_5'))
      | ~ v1_funct_1('#skF_5')
      | ~ v5_relat_1('#skF_5',k2_relat_1('#skF_5'))
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_344,c_742])).

tff(c_748,plain,(
    ! [D_108] : r1_tarski(k9_relat_1('#skF_5',D_108),k2_relat_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_689,c_68,c_746])).

tff(c_800,plain,(
    ! [B_152,C_153] :
      ( k2_relset_1(k1_relat_1('#skF_5'),B_152,C_153) = k1_tarski(k1_funct_1(C_153,'#skF_2'))
      | k1_xboole_0 = B_152
      | ~ m1_subset_1(C_153,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_5'),B_152)))
      | ~ v1_funct_2(C_153,k1_relat_1('#skF_5'),B_152)
      | ~ v1_funct_1(C_153) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_243,c_243,c_404])).

tff(c_806,plain,
    ( k2_relset_1(k1_relat_1('#skF_5'),'#skF_3','#skF_5') = k1_tarski(k1_funct_1('#skF_5','#skF_2'))
    | k1_xboole_0 = '#skF_3'
    | ~ v1_funct_2('#skF_5',k1_relat_1('#skF_5'),'#skF_3')
    | ~ v1_funct_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_248,c_800])).

tff(c_816,plain,
    ( k1_tarski(k1_funct_1('#skF_5','#skF_2')) = k2_relat_1('#skF_5')
    | k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_249,c_245,c_806])).

tff(c_817,plain,(
    k1_tarski(k1_funct_1('#skF_5','#skF_2')) = k2_relat_1('#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_816])).

tff(c_821,plain,(
    ~ r1_tarski(k9_relat_1('#skF_5','#skF_4'),k2_relat_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_817,c_136])).

tff(c_824,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_748,c_821])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n018.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 11:15:56 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.03/1.44  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.03/1.45  
% 3.03/1.45  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.03/1.45  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k2_relset_1 > k1_relset_1 > k1_enumset1 > k9_relat_1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4
% 3.03/1.45  
% 3.03/1.45  %Foreground sorts:
% 3.03/1.45  
% 3.03/1.45  
% 3.03/1.45  %Background operators:
% 3.03/1.45  
% 3.03/1.45  
% 3.03/1.45  %Foreground operators:
% 3.03/1.45  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 3.03/1.45  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 3.03/1.45  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.03/1.45  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.03/1.45  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.03/1.45  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.03/1.45  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.03/1.45  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.03/1.45  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.03/1.45  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 3.03/1.45  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.03/1.45  tff('#skF_5', type, '#skF_5': $i).
% 3.03/1.45  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.03/1.45  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.03/1.45  tff('#skF_2', type, '#skF_2': $i).
% 3.03/1.45  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 3.03/1.45  tff('#skF_3', type, '#skF_3': $i).
% 3.03/1.45  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.03/1.45  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.03/1.45  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.03/1.45  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.03/1.45  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.03/1.45  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.03/1.45  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.03/1.45  tff('#skF_4', type, '#skF_4': $i).
% 3.03/1.45  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.03/1.45  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.03/1.45  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.03/1.45  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.03/1.45  
% 3.34/1.47  tff(f_44, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 3.34/1.47  tff(f_152, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, k1_tarski(A), B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A), B)))) => (~(B = k1_xboole_0) => r1_tarski(k7_relset_1(k1_tarski(A), B, D, C), k1_tarski(k1_funct_1(D, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_funct_2)).
% 3.34/1.47  tff(f_36, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 3.34/1.47  tff(f_117, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (((k1_relat_1(C) = A) & (![D]: (r2_hidden(D, A) => r2_hidden(k1_funct_1(C, D), B)))) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_funct_2)).
% 3.34/1.47  tff(f_54, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.34/1.47  tff(f_80, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 3.34/1.47  tff(f_58, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 3.34/1.47  tff(f_140, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_hidden(C, A) => ((B = k1_xboole_0) | r2_hidden(k1_funct_1(D, C), k2_relset_1(A, B, D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_funct_2)).
% 3.34/1.47  tff(f_50, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.34/1.47  tff(f_42, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 3.34/1.47  tff(f_100, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r1_tarski(k2_relat_1(B), A) => ((v1_funct_1(B) & v1_funct_2(B, k1_relat_1(B), A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B), A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_funct_2)).
% 3.34/1.47  tff(f_62, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 3.34/1.47  tff(f_88, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => r1_tarski(k7_relset_1(A, B, D, C), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_funct_2)).
% 3.34/1.47  tff(f_128, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, k1_tarski(A), B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A), B)))) => (~(B = k1_xboole_0) => (k2_relset_1(k1_tarski(A), B, C) = k1_tarski(k1_funct_1(C, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t62_funct_2)).
% 3.34/1.47  tff(c_12, plain, (![A_9, B_10]: (v1_relat_1(k2_zfmisc_1(A_9, B_10)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.34/1.47  tff(c_64, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_2'), '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_152])).
% 3.34/1.47  tff(c_88, plain, (![B_49, A_50]: (v1_relat_1(B_49) | ~m1_subset_1(B_49, k1_zfmisc_1(A_50)) | ~v1_relat_1(A_50))), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.34/1.47  tff(c_91, plain, (v1_relat_1('#skF_5') | ~v1_relat_1(k2_zfmisc_1(k1_tarski('#skF_2'), '#skF_3'))), inference(resolution, [status(thm)], [c_64, c_88])).
% 3.34/1.47  tff(c_94, plain, (v1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_12, c_91])).
% 3.34/1.47  tff(c_68, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_152])).
% 3.34/1.47  tff(c_46, plain, (![C_35, B_34]: (r2_hidden('#skF_1'(k1_relat_1(C_35), B_34, C_35), k1_relat_1(C_35)) | m1_subset_1(C_35, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(C_35), B_34))) | ~v1_funct_1(C_35) | ~v1_relat_1(C_35))), inference(cnfTransformation, [status(thm)], [f_117])).
% 3.34/1.47  tff(c_62, plain, (k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_152])).
% 3.34/1.47  tff(c_66, plain, (v1_funct_2('#skF_5', k1_tarski('#skF_2'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_152])).
% 3.34/1.47  tff(c_112, plain, (![A_62, B_63, C_64]: (k1_relset_1(A_62, B_63, C_64)=k1_relat_1(C_64) | ~m1_subset_1(C_64, k1_zfmisc_1(k2_zfmisc_1(A_62, B_63))))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.34/1.47  tff(c_116, plain, (k1_relset_1(k1_tarski('#skF_2'), '#skF_3', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_64, c_112])).
% 3.34/1.47  tff(c_232, plain, (![B_100, A_101, C_102]: (k1_xboole_0=B_100 | k1_relset_1(A_101, B_100, C_102)=A_101 | ~v1_funct_2(C_102, A_101, B_100) | ~m1_subset_1(C_102, k1_zfmisc_1(k2_zfmisc_1(A_101, B_100))))), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.34/1.47  tff(c_238, plain, (k1_xboole_0='#skF_3' | k1_relset_1(k1_tarski('#skF_2'), '#skF_3', '#skF_5')=k1_tarski('#skF_2') | ~v1_funct_2('#skF_5', k1_tarski('#skF_2'), '#skF_3')), inference(resolution, [status(thm)], [c_64, c_232])).
% 3.34/1.47  tff(c_242, plain, (k1_xboole_0='#skF_3' | k1_tarski('#skF_2')=k1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_116, c_238])).
% 3.34/1.47  tff(c_243, plain, (k1_tarski('#skF_2')=k1_relat_1('#skF_5')), inference(negUnitSimplification, [status(thm)], [c_62, c_242])).
% 3.34/1.47  tff(c_249, plain, (v1_funct_2('#skF_5', k1_relat_1('#skF_5'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_243, c_66])).
% 3.34/1.47  tff(c_248, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_5'), '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_243, c_64])).
% 3.34/1.47  tff(c_121, plain, (![A_65, B_66, C_67]: (k2_relset_1(A_65, B_66, C_67)=k2_relat_1(C_67) | ~m1_subset_1(C_67, k1_zfmisc_1(k2_zfmisc_1(A_65, B_66))))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.34/1.47  tff(c_125, plain, (k2_relset_1(k1_tarski('#skF_2'), '#skF_3', '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_64, c_121])).
% 3.34/1.47  tff(c_245, plain, (k2_relset_1(k1_relat_1('#skF_5'), '#skF_3', '#skF_5')=k2_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_243, c_125])).
% 3.34/1.47  tff(c_406, plain, (![D_130, C_131, A_132, B_133]: (r2_hidden(k1_funct_1(D_130, C_131), k2_relset_1(A_132, B_133, D_130)) | k1_xboole_0=B_133 | ~r2_hidden(C_131, A_132) | ~m1_subset_1(D_130, k1_zfmisc_1(k2_zfmisc_1(A_132, B_133))) | ~v1_funct_2(D_130, A_132, B_133) | ~v1_funct_1(D_130))), inference(cnfTransformation, [status(thm)], [f_140])).
% 3.34/1.47  tff(c_417, plain, (![C_131]: (r2_hidden(k1_funct_1('#skF_5', C_131), k2_relat_1('#skF_5')) | k1_xboole_0='#skF_3' | ~r2_hidden(C_131, k1_relat_1('#skF_5')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_5'), '#skF_3'))) | ~v1_funct_2('#skF_5', k1_relat_1('#skF_5'), '#skF_3') | ~v1_funct_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_245, c_406])).
% 3.34/1.47  tff(c_424, plain, (![C_131]: (r2_hidden(k1_funct_1('#skF_5', C_131), k2_relat_1('#skF_5')) | k1_xboole_0='#skF_3' | ~r2_hidden(C_131, k1_relat_1('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_249, c_248, c_417])).
% 3.34/1.47  tff(c_426, plain, (![C_134]: (r2_hidden(k1_funct_1('#skF_5', C_134), k2_relat_1('#skF_5')) | ~r2_hidden(C_134, k1_relat_1('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_62, c_424])).
% 3.34/1.47  tff(c_48, plain, (![C_35, B_34]: (~r2_hidden(k1_funct_1(C_35, '#skF_1'(k1_relat_1(C_35), B_34, C_35)), B_34) | v1_funct_2(C_35, k1_relat_1(C_35), B_34) | ~v1_funct_1(C_35) | ~v1_relat_1(C_35))), inference(cnfTransformation, [status(thm)], [f_117])).
% 3.34/1.47  tff(c_434, plain, (v1_funct_2('#skF_5', k1_relat_1('#skF_5'), k2_relat_1('#skF_5')) | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5') | ~r2_hidden('#skF_1'(k1_relat_1('#skF_5'), k2_relat_1('#skF_5'), '#skF_5'), k1_relat_1('#skF_5'))), inference(resolution, [status(thm)], [c_426, c_48])).
% 3.34/1.47  tff(c_440, plain, (v1_funct_2('#skF_5', k1_relat_1('#skF_5'), k2_relat_1('#skF_5')) | ~r2_hidden('#skF_1'(k1_relat_1('#skF_5'), k2_relat_1('#skF_5'), '#skF_5'), k1_relat_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_94, c_68, c_434])).
% 3.34/1.47  tff(c_441, plain, (~r2_hidden('#skF_1'(k1_relat_1('#skF_5'), k2_relat_1('#skF_5'), '#skF_5'), k1_relat_1('#skF_5'))), inference(splitLeft, [status(thm)], [c_440])).
% 3.34/1.47  tff(c_444, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_5'), k2_relat_1('#skF_5')))) | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_46, c_441])).
% 3.34/1.47  tff(c_450, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_5'), k2_relat_1('#skF_5'))))), inference(demodulation, [status(thm), theory('equality')], [c_94, c_68, c_444])).
% 3.34/1.47  tff(c_14, plain, (![C_13, B_12, A_11]: (v5_relat_1(C_13, B_12) | ~m1_subset_1(C_13, k1_zfmisc_1(k2_zfmisc_1(A_11, B_12))))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.34/1.47  tff(c_490, plain, (v5_relat_1('#skF_5', k2_relat_1('#skF_5'))), inference(resolution, [status(thm)], [c_450, c_14])).
% 3.34/1.47  tff(c_10, plain, (![B_8, A_7]: (r1_tarski(k2_relat_1(B_8), A_7) | ~v5_relat_1(B_8, A_7) | ~v1_relat_1(B_8))), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.34/1.47  tff(c_148, plain, (![B_81, A_82]: (m1_subset_1(B_81, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B_81), A_82))) | ~r1_tarski(k2_relat_1(B_81), A_82) | ~v1_funct_1(B_81) | ~v1_relat_1(B_81))), inference(cnfTransformation, [status(thm)], [f_100])).
% 3.34/1.47  tff(c_22, plain, (![A_20, B_21, C_22, D_23]: (k7_relset_1(A_20, B_21, C_22, D_23)=k9_relat_1(C_22, D_23) | ~m1_subset_1(C_22, k1_zfmisc_1(k2_zfmisc_1(A_20, B_21))))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.34/1.47  tff(c_341, plain, (![B_106, A_107, D_108]: (k7_relset_1(k1_relat_1(B_106), A_107, B_106, D_108)=k9_relat_1(B_106, D_108) | ~r1_tarski(k2_relat_1(B_106), A_107) | ~v1_funct_1(B_106) | ~v1_relat_1(B_106))), inference(resolution, [status(thm)], [c_148, c_22])).
% 3.34/1.47  tff(c_344, plain, (![B_8, A_7, D_108]: (k7_relset_1(k1_relat_1(B_8), A_7, B_8, D_108)=k9_relat_1(B_8, D_108) | ~v1_funct_1(B_8) | ~v5_relat_1(B_8, A_7) | ~v1_relat_1(B_8))), inference(resolution, [status(thm)], [c_10, c_341])).
% 3.34/1.47  tff(c_50, plain, (![C_35, B_34]: (r2_hidden('#skF_1'(k1_relat_1(C_35), B_34, C_35), k1_relat_1(C_35)) | v1_funct_2(C_35, k1_relat_1(C_35), B_34) | ~v1_funct_1(C_35) | ~v1_relat_1(C_35))), inference(cnfTransformation, [status(thm)], [f_117])).
% 3.34/1.47  tff(c_447, plain, (v1_funct_2('#skF_5', k1_relat_1('#skF_5'), k2_relat_1('#skF_5')) | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_50, c_441])).
% 3.34/1.47  tff(c_453, plain, (v1_funct_2('#skF_5', k1_relat_1('#skF_5'), k2_relat_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_94, c_68, c_447])).
% 3.34/1.47  tff(c_36, plain, (![A_27, B_28, D_30, C_29]: (r1_tarski(k7_relset_1(A_27, B_28, D_30, C_29), B_28) | ~m1_subset_1(D_30, k1_zfmisc_1(k2_zfmisc_1(A_27, B_28))) | ~v1_funct_2(D_30, A_27, B_28) | ~v1_funct_1(D_30))), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.34/1.47  tff(c_455, plain, (![C_29]: (r1_tarski(k7_relset_1(k1_relat_1('#skF_5'), k2_relat_1('#skF_5'), '#skF_5', C_29), k2_relat_1('#skF_5')) | ~v1_funct_2('#skF_5', k1_relat_1('#skF_5'), k2_relat_1('#skF_5')) | ~v1_funct_1('#skF_5'))), inference(resolution, [status(thm)], [c_450, c_36])).
% 3.34/1.47  tff(c_563, plain, (![C_138]: (r1_tarski(k7_relset_1(k1_relat_1('#skF_5'), k2_relat_1('#skF_5'), '#skF_5', C_138), k2_relat_1('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_453, c_455])).
% 3.34/1.47  tff(c_567, plain, (![D_108]: (r1_tarski(k9_relat_1('#skF_5', D_108), k2_relat_1('#skF_5')) | ~v1_funct_1('#skF_5') | ~v5_relat_1('#skF_5', k2_relat_1('#skF_5')) | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_344, c_563])).
% 3.34/1.47  tff(c_569, plain, (![D_108]: (r1_tarski(k9_relat_1('#skF_5', D_108), k2_relat_1('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_94, c_490, c_68, c_567])).
% 3.34/1.47  tff(c_401, plain, (![A_127, B_128, C_129]: (k2_relset_1(k1_tarski(A_127), B_128, C_129)=k1_tarski(k1_funct_1(C_129, A_127)) | k1_xboole_0=B_128 | ~m1_subset_1(C_129, k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A_127), B_128))) | ~v1_funct_2(C_129, k1_tarski(A_127), B_128) | ~v1_funct_1(C_129))), inference(cnfTransformation, [status(thm)], [f_128])).
% 3.34/1.47  tff(c_404, plain, (![B_128, C_129]: (k2_relset_1(k1_tarski('#skF_2'), B_128, C_129)=k1_tarski(k1_funct_1(C_129, '#skF_2')) | k1_xboole_0=B_128 | ~m1_subset_1(C_129, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_5'), B_128))) | ~v1_funct_2(C_129, k1_tarski('#skF_2'), B_128) | ~v1_funct_1(C_129))), inference(superposition, [status(thm), theory('equality')], [c_243, c_401])).
% 3.34/1.47  tff(c_602, plain, (![B_141, C_142]: (k2_relset_1(k1_relat_1('#skF_5'), B_141, C_142)=k1_tarski(k1_funct_1(C_142, '#skF_2')) | k1_xboole_0=B_141 | ~m1_subset_1(C_142, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_5'), B_141))) | ~v1_funct_2(C_142, k1_relat_1('#skF_5'), B_141) | ~v1_funct_1(C_142))), inference(demodulation, [status(thm), theory('equality')], [c_243, c_243, c_404])).
% 3.34/1.47  tff(c_608, plain, (k2_relset_1(k1_relat_1('#skF_5'), '#skF_3', '#skF_5')=k1_tarski(k1_funct_1('#skF_5', '#skF_2')) | k1_xboole_0='#skF_3' | ~v1_funct_2('#skF_5', k1_relat_1('#skF_5'), '#skF_3') | ~v1_funct_1('#skF_5')), inference(resolution, [status(thm)], [c_248, c_602])).
% 3.34/1.47  tff(c_618, plain, (k1_tarski(k1_funct_1('#skF_5', '#skF_2'))=k2_relat_1('#skF_5') | k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_68, c_249, c_245, c_608])).
% 3.34/1.47  tff(c_619, plain, (k1_tarski(k1_funct_1('#skF_5', '#skF_2'))=k2_relat_1('#skF_5')), inference(negUnitSimplification, [status(thm)], [c_62, c_618])).
% 3.34/1.47  tff(c_132, plain, (![A_72, B_73, C_74, D_75]: (k7_relset_1(A_72, B_73, C_74, D_75)=k9_relat_1(C_74, D_75) | ~m1_subset_1(C_74, k1_zfmisc_1(k2_zfmisc_1(A_72, B_73))))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.34/1.47  tff(c_135, plain, (![D_75]: (k7_relset_1(k1_tarski('#skF_2'), '#skF_3', '#skF_5', D_75)=k9_relat_1('#skF_5', D_75))), inference(resolution, [status(thm)], [c_64, c_132])).
% 3.34/1.47  tff(c_60, plain, (~r1_tarski(k7_relset_1(k1_tarski('#skF_2'), '#skF_3', '#skF_5', '#skF_4'), k1_tarski(k1_funct_1('#skF_5', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_152])).
% 3.34/1.47  tff(c_136, plain, (~r1_tarski(k9_relat_1('#skF_5', '#skF_4'), k1_tarski(k1_funct_1('#skF_5', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_135, c_60])).
% 3.34/1.47  tff(c_623, plain, (~r1_tarski(k9_relat_1('#skF_5', '#skF_4'), k2_relat_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_619, c_136])).
% 3.34/1.47  tff(c_626, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_569, c_623])).
% 3.34/1.47  tff(c_628, plain, (r2_hidden('#skF_1'(k1_relat_1('#skF_5'), k2_relat_1('#skF_5'), '#skF_5'), k1_relat_1('#skF_5'))), inference(splitRight, [status(thm)], [c_440])).
% 3.34/1.47  tff(c_44, plain, (![C_35, B_34]: (~r2_hidden(k1_funct_1(C_35, '#skF_1'(k1_relat_1(C_35), B_34, C_35)), B_34) | m1_subset_1(C_35, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(C_35), B_34))) | ~v1_funct_1(C_35) | ~v1_relat_1(C_35))), inference(cnfTransformation, [status(thm)], [f_117])).
% 3.34/1.47  tff(c_430, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_5'), k2_relat_1('#skF_5')))) | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5') | ~r2_hidden('#skF_1'(k1_relat_1('#skF_5'), k2_relat_1('#skF_5'), '#skF_5'), k1_relat_1('#skF_5'))), inference(resolution, [status(thm)], [c_426, c_44])).
% 3.34/1.47  tff(c_437, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_5'), k2_relat_1('#skF_5')))) | ~r2_hidden('#skF_1'(k1_relat_1('#skF_5'), k2_relat_1('#skF_5'), '#skF_5'), k1_relat_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_94, c_68, c_430])).
% 3.34/1.47  tff(c_652, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_5'), k2_relat_1('#skF_5'))))), inference(demodulation, [status(thm), theory('equality')], [c_628, c_437])).
% 3.34/1.47  tff(c_689, plain, (v5_relat_1('#skF_5', k2_relat_1('#skF_5'))), inference(resolution, [status(thm)], [c_652, c_14])).
% 3.34/1.47  tff(c_627, plain, (v1_funct_2('#skF_5', k1_relat_1('#skF_5'), k2_relat_1('#skF_5'))), inference(splitRight, [status(thm)], [c_440])).
% 3.34/1.47  tff(c_654, plain, (![C_29]: (r1_tarski(k7_relset_1(k1_relat_1('#skF_5'), k2_relat_1('#skF_5'), '#skF_5', C_29), k2_relat_1('#skF_5')) | ~v1_funct_2('#skF_5', k1_relat_1('#skF_5'), k2_relat_1('#skF_5')) | ~v1_funct_1('#skF_5'))), inference(resolution, [status(thm)], [c_652, c_36])).
% 3.34/1.47  tff(c_742, plain, (![C_146]: (r1_tarski(k7_relset_1(k1_relat_1('#skF_5'), k2_relat_1('#skF_5'), '#skF_5', C_146), k2_relat_1('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_627, c_654])).
% 3.34/1.47  tff(c_746, plain, (![D_108]: (r1_tarski(k9_relat_1('#skF_5', D_108), k2_relat_1('#skF_5')) | ~v1_funct_1('#skF_5') | ~v5_relat_1('#skF_5', k2_relat_1('#skF_5')) | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_344, c_742])).
% 3.34/1.47  tff(c_748, plain, (![D_108]: (r1_tarski(k9_relat_1('#skF_5', D_108), k2_relat_1('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_94, c_689, c_68, c_746])).
% 3.34/1.47  tff(c_800, plain, (![B_152, C_153]: (k2_relset_1(k1_relat_1('#skF_5'), B_152, C_153)=k1_tarski(k1_funct_1(C_153, '#skF_2')) | k1_xboole_0=B_152 | ~m1_subset_1(C_153, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_5'), B_152))) | ~v1_funct_2(C_153, k1_relat_1('#skF_5'), B_152) | ~v1_funct_1(C_153))), inference(demodulation, [status(thm), theory('equality')], [c_243, c_243, c_404])).
% 3.34/1.47  tff(c_806, plain, (k2_relset_1(k1_relat_1('#skF_5'), '#skF_3', '#skF_5')=k1_tarski(k1_funct_1('#skF_5', '#skF_2')) | k1_xboole_0='#skF_3' | ~v1_funct_2('#skF_5', k1_relat_1('#skF_5'), '#skF_3') | ~v1_funct_1('#skF_5')), inference(resolution, [status(thm)], [c_248, c_800])).
% 3.34/1.47  tff(c_816, plain, (k1_tarski(k1_funct_1('#skF_5', '#skF_2'))=k2_relat_1('#skF_5') | k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_68, c_249, c_245, c_806])).
% 3.34/1.47  tff(c_817, plain, (k1_tarski(k1_funct_1('#skF_5', '#skF_2'))=k2_relat_1('#skF_5')), inference(negUnitSimplification, [status(thm)], [c_62, c_816])).
% 3.34/1.47  tff(c_821, plain, (~r1_tarski(k9_relat_1('#skF_5', '#skF_4'), k2_relat_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_817, c_136])).
% 3.34/1.47  tff(c_824, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_748, c_821])).
% 3.34/1.47  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.34/1.47  
% 3.34/1.47  Inference rules
% 3.34/1.47  ----------------------
% 3.34/1.47  #Ref     : 0
% 3.34/1.47  #Sup     : 148
% 3.34/1.47  #Fact    : 0
% 3.34/1.47  #Define  : 0
% 3.34/1.47  #Split   : 1
% 3.34/1.47  #Chain   : 0
% 3.34/1.47  #Close   : 0
% 3.34/1.47  
% 3.34/1.47  Ordering : KBO
% 3.34/1.47  
% 3.34/1.47  Simplification rules
% 3.34/1.47  ----------------------
% 3.34/1.47  #Subsume      : 10
% 3.34/1.47  #Demod        : 209
% 3.34/1.47  #Tautology    : 88
% 3.34/1.47  #SimpNegUnit  : 10
% 3.34/1.47  #BackRed      : 11
% 3.34/1.47  
% 3.34/1.47  #Partial instantiations: 0
% 3.34/1.47  #Strategies tried      : 1
% 3.34/1.47  
% 3.34/1.47  Timing (in seconds)
% 3.34/1.47  ----------------------
% 3.34/1.48  Preprocessing        : 0.36
% 3.34/1.48  Parsing              : 0.19
% 3.34/1.48  CNF conversion       : 0.02
% 3.34/1.48  Main loop            : 0.35
% 3.34/1.48  Inferencing          : 0.13
% 3.34/1.48  Reduction            : 0.12
% 3.34/1.48  Demodulation         : 0.09
% 3.34/1.48  BG Simplification    : 0.02
% 3.34/1.48  Subsumption          : 0.05
% 3.34/1.48  Abstraction          : 0.02
% 3.34/1.48  MUC search           : 0.00
% 3.34/1.48  Cooper               : 0.00
% 3.34/1.48  Total                : 0.76
% 3.34/1.48  Index Insertion      : 0.00
% 3.34/1.48  Index Deletion       : 0.00
% 3.34/1.48  Index Matching       : 0.00
% 3.34/1.48  BG Taut test         : 0.00
%------------------------------------------------------------------------------
