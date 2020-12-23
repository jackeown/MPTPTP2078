%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:14:45 EST 2020

% Result     : Theorem 2.64s
% Output     : CNFRefutation 2.64s
% Verified   : 
% Statistics : Number of formulae       :   93 ( 263 expanded)
%              Number of leaves         :   39 ( 103 expanded)
%              Depth                    :   11
%              Number of atoms          :  122 ( 533 expanded)
%              Number of equality atoms :   50 ( 186 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    4 (   2 average)

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

tff(f_106,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,k1_tarski(A),B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A),B))) )
       => ( B != k1_xboole_0
         => r1_tarski(k7_relset_1(k1_tarski(A),B,D,C),k1_tarski(k1_funct_1(D,A))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_funct_2)).

tff(f_84,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_61,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k9_relat_1(B,A),k2_relat_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t144_relat_1)).

tff(f_72,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ( k1_relat_1(A) = k1_xboole_0
          | k2_relat_1(A) = k1_xboole_0 )
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).

tff(f_90,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k1_tarski(B))
    <=> ( A = k1_xboole_0
        | A = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).

tff(f_94,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_80,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( k1_relat_1(B) = k1_tarski(A)
       => k2_relat_1(B) = k1_tarski(k1_funct_1(B,A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_funct_1)).

tff(f_64,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_33,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_45,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(c_52,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_1'),'#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_91,plain,(
    ! [C_38,A_39,B_40] :
      ( v1_relat_1(C_38)
      | ~ m1_subset_1(C_38,k1_zfmisc_1(k2_zfmisc_1(A_39,B_40))) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_99,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_52,c_91])).

tff(c_28,plain,(
    ! [B_16,A_15] :
      ( r1_tarski(k9_relat_1(B_16,A_15),k2_relat_1(B_16))
      | ~ v1_relat_1(B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_36,plain,(
    ! [A_17] :
      ( k1_relat_1(A_17) != k1_xboole_0
      | k1_xboole_0 = A_17
      | ~ v1_relat_1(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_108,plain,
    ( k1_relat_1('#skF_4') != k1_xboole_0
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_99,c_36])).

tff(c_147,plain,(
    k1_relat_1('#skF_4') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_108])).

tff(c_194,plain,(
    ! [C_51,A_52,B_53] :
      ( v4_relat_1(C_51,A_52)
      | ~ m1_subset_1(C_51,k1_zfmisc_1(k2_zfmisc_1(A_52,B_53))) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_202,plain,(
    v4_relat_1('#skF_4',k1_tarski('#skF_1')) ),
    inference(resolution,[status(thm)],[c_52,c_194])).

tff(c_234,plain,(
    ! [B_60,A_61] :
      ( r1_tarski(k1_relat_1(B_60),A_61)
      | ~ v4_relat_1(B_60,A_61)
      | ~ v1_relat_1(B_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_14,plain,(
    ! [B_8,A_7] :
      ( k1_tarski(B_8) = A_7
      | k1_xboole_0 = A_7
      | ~ r1_tarski(A_7,k1_tarski(B_8)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_308,plain,(
    ! [B_74,B_75] :
      ( k1_tarski(B_74) = k1_relat_1(B_75)
      | k1_relat_1(B_75) = k1_xboole_0
      | ~ v4_relat_1(B_75,k1_tarski(B_74))
      | ~ v1_relat_1(B_75) ) ),
    inference(resolution,[status(thm)],[c_234,c_14])).

tff(c_311,plain,
    ( k1_tarski('#skF_1') = k1_relat_1('#skF_4')
    | k1_relat_1('#skF_4') = k1_xboole_0
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_202,c_308])).

tff(c_318,plain,
    ( k1_tarski('#skF_1') = k1_relat_1('#skF_4')
    | k1_relat_1('#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_99,c_311])).

tff(c_319,plain,(
    k1_tarski('#skF_1') = k1_relat_1('#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_147,c_318])).

tff(c_326,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'),'#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_319,c_52])).

tff(c_427,plain,(
    ! [A_81,B_82,C_83,D_84] :
      ( k7_relset_1(A_81,B_82,C_83,D_84) = k9_relat_1(C_83,D_84)
      | ~ m1_subset_1(C_83,k1_zfmisc_1(k2_zfmisc_1(A_81,B_82))) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_433,plain,(
    ! [D_84] : k7_relset_1(k1_relat_1('#skF_4'),'#skF_2','#skF_4',D_84) = k9_relat_1('#skF_4',D_84) ),
    inference(resolution,[status(thm)],[c_326,c_427])).

tff(c_56,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_38,plain,(
    ! [B_19,A_18] :
      ( k1_tarski(k1_funct_1(B_19,A_18)) = k2_relat_1(B_19)
      | k1_tarski(A_18) != k1_relat_1(B_19)
      | ~ v1_funct_1(B_19)
      | ~ v1_relat_1(B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_48,plain,(
    ~ r1_tarski(k7_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4','#skF_3'),k1_tarski(k1_funct_1('#skF_4','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_325,plain,(
    ~ r1_tarski(k7_relset_1(k1_relat_1('#skF_4'),'#skF_2','#skF_4','#skF_3'),k1_tarski(k1_funct_1('#skF_4','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_319,c_48])).

tff(c_375,plain,
    ( ~ r1_tarski(k7_relset_1(k1_relat_1('#skF_4'),'#skF_2','#skF_4','#skF_3'),k2_relat_1('#skF_4'))
    | k1_tarski('#skF_1') != k1_relat_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_325])).

tff(c_377,plain,(
    ~ r1_tarski(k7_relset_1(k1_relat_1('#skF_4'),'#skF_2','#skF_4','#skF_3'),k2_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_99,c_56,c_319,c_375])).

tff(c_443,plain,(
    ~ r1_tarski(k9_relat_1('#skF_4','#skF_3'),k2_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_433,c_377])).

tff(c_456,plain,(
    ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_28,c_443])).

tff(c_460,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_99,c_456])).

tff(c_461,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_108])).

tff(c_30,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_469,plain,(
    k2_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_461,c_461,c_30])).

tff(c_34,plain,(
    ! [A_17] :
      ( k2_relat_1(A_17) != k1_xboole_0
      | k1_xboole_0 = A_17
      | ~ v1_relat_1(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_107,plain,
    ( k2_relat_1('#skF_4') != k1_xboole_0
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_99,c_34])).

tff(c_146,plain,(
    k2_relat_1('#skF_4') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_107])).

tff(c_463,plain,(
    k2_relat_1('#skF_4') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_461,c_146])).

tff(c_502,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_469,c_463])).

tff(c_503,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_107])).

tff(c_8,plain,(
    ! [A_3] : r1_tarski(k1_xboole_0,A_3) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_512,plain,(
    ! [A_3] : r1_tarski('#skF_4',A_3) ),
    inference(demodulation,[status(thm),theory(equality)],[c_503,c_8])).

tff(c_504,plain,(
    k2_relat_1('#skF_4') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_107])).

tff(c_519,plain,(
    k2_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_503,c_504])).

tff(c_541,plain,(
    ! [B_94,A_95] :
      ( r1_tarski(k9_relat_1(B_94,A_95),k2_relat_1(B_94))
      | ~ v1_relat_1(B_94) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_546,plain,(
    ! [A_95] :
      ( r1_tarski(k9_relat_1('#skF_4',A_95),'#skF_4')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_519,c_541])).

tff(c_565,plain,(
    ! [A_97] : r1_tarski(k9_relat_1('#skF_4',A_97),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_99,c_546])).

tff(c_109,plain,(
    ! [B_41,A_42] :
      ( B_41 = A_42
      | ~ r1_tarski(B_41,A_42)
      | ~ r1_tarski(A_42,B_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_118,plain,(
    ! [A_3] :
      ( k1_xboole_0 = A_3
      | ~ r1_tarski(A_3,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_8,c_109])).

tff(c_505,plain,(
    ! [A_3] :
      ( A_3 = '#skF_4'
      | ~ r1_tarski(A_3,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_503,c_503,c_118])).

tff(c_571,plain,(
    ! [A_97] : k9_relat_1('#skF_4',A_97) = '#skF_4' ),
    inference(resolution,[status(thm)],[c_565,c_505])).

tff(c_20,plain,(
    ! [A_9] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_9)) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_509,plain,(
    ! [A_9] : m1_subset_1('#skF_4',k1_zfmisc_1(A_9)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_503,c_20])).

tff(c_688,plain,(
    ! [A_122,B_123,C_124,D_125] :
      ( k7_relset_1(A_122,B_123,C_124,D_125) = k9_relat_1(C_124,D_125)
      | ~ m1_subset_1(C_124,k1_zfmisc_1(k2_zfmisc_1(A_122,B_123))) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_691,plain,(
    ! [A_122,B_123,D_125] : k7_relset_1(A_122,B_123,'#skF_4',D_125) = k9_relat_1('#skF_4',D_125) ),
    inference(resolution,[status(thm)],[c_509,c_688])).

tff(c_693,plain,(
    ! [A_122,B_123,D_125] : k7_relset_1(A_122,B_123,'#skF_4',D_125) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_571,c_691])).

tff(c_694,plain,(
    ~ r1_tarski('#skF_4',k1_tarski(k1_funct_1('#skF_4','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_693,c_48])).

tff(c_697,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_512,c_694])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:05:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.64/1.35  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.64/1.36  
% 2.64/1.36  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.64/1.36  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k1_enumset1 > k9_relat_1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.64/1.36  
% 2.64/1.36  %Foreground sorts:
% 2.64/1.36  
% 2.64/1.36  
% 2.64/1.36  %Background operators:
% 2.64/1.36  
% 2.64/1.36  
% 2.64/1.36  %Foreground operators:
% 2.64/1.36  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.64/1.36  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.64/1.36  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.64/1.36  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.64/1.36  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.64/1.36  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.64/1.36  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.64/1.36  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 2.64/1.36  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.64/1.36  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.64/1.36  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.64/1.36  tff('#skF_2', type, '#skF_2': $i).
% 2.64/1.36  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.64/1.36  tff('#skF_3', type, '#skF_3': $i).
% 2.64/1.36  tff('#skF_1', type, '#skF_1': $i).
% 2.64/1.36  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.64/1.36  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.64/1.36  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.64/1.36  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.64/1.36  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.64/1.36  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.64/1.36  tff('#skF_4', type, '#skF_4': $i).
% 2.64/1.36  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.64/1.36  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.64/1.36  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.64/1.36  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.64/1.36  
% 2.64/1.38  tff(f_106, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, k1_tarski(A), B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A), B)))) => (~(B = k1_xboole_0) => r1_tarski(k7_relset_1(k1_tarski(A), B, D, C), k1_tarski(k1_funct_1(D, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_funct_2)).
% 2.64/1.38  tff(f_84, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.64/1.38  tff(f_61, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k9_relat_1(B, A), k2_relat_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t144_relat_1)).
% 2.64/1.38  tff(f_72, axiom, (![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_relat_1)).
% 2.64/1.38  tff(f_90, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.64/1.38  tff(f_57, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d18_relat_1)).
% 2.64/1.38  tff(f_43, axiom, (![A, B]: (r1_tarski(A, k1_tarski(B)) <=> ((A = k1_xboole_0) | (A = k1_tarski(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_zfmisc_1)).
% 2.64/1.38  tff(f_94, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 2.64/1.38  tff(f_80, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((k1_relat_1(B) = k1_tarski(A)) => (k2_relat_1(B) = k1_tarski(k1_funct_1(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t14_funct_1)).
% 2.64/1.38  tff(f_64, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 2.64/1.38  tff(f_33, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.64/1.38  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.64/1.38  tff(f_45, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 2.64/1.38  tff(c_52, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_1'), '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_106])).
% 2.64/1.38  tff(c_91, plain, (![C_38, A_39, B_40]: (v1_relat_1(C_38) | ~m1_subset_1(C_38, k1_zfmisc_1(k2_zfmisc_1(A_39, B_40))))), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.64/1.38  tff(c_99, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_52, c_91])).
% 2.64/1.38  tff(c_28, plain, (![B_16, A_15]: (r1_tarski(k9_relat_1(B_16, A_15), k2_relat_1(B_16)) | ~v1_relat_1(B_16))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.64/1.38  tff(c_36, plain, (![A_17]: (k1_relat_1(A_17)!=k1_xboole_0 | k1_xboole_0=A_17 | ~v1_relat_1(A_17))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.64/1.38  tff(c_108, plain, (k1_relat_1('#skF_4')!=k1_xboole_0 | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_99, c_36])).
% 2.64/1.38  tff(c_147, plain, (k1_relat_1('#skF_4')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_108])).
% 2.64/1.38  tff(c_194, plain, (![C_51, A_52, B_53]: (v4_relat_1(C_51, A_52) | ~m1_subset_1(C_51, k1_zfmisc_1(k2_zfmisc_1(A_52, B_53))))), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.64/1.38  tff(c_202, plain, (v4_relat_1('#skF_4', k1_tarski('#skF_1'))), inference(resolution, [status(thm)], [c_52, c_194])).
% 2.64/1.38  tff(c_234, plain, (![B_60, A_61]: (r1_tarski(k1_relat_1(B_60), A_61) | ~v4_relat_1(B_60, A_61) | ~v1_relat_1(B_60))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.64/1.38  tff(c_14, plain, (![B_8, A_7]: (k1_tarski(B_8)=A_7 | k1_xboole_0=A_7 | ~r1_tarski(A_7, k1_tarski(B_8)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.64/1.38  tff(c_308, plain, (![B_74, B_75]: (k1_tarski(B_74)=k1_relat_1(B_75) | k1_relat_1(B_75)=k1_xboole_0 | ~v4_relat_1(B_75, k1_tarski(B_74)) | ~v1_relat_1(B_75))), inference(resolution, [status(thm)], [c_234, c_14])).
% 2.64/1.38  tff(c_311, plain, (k1_tarski('#skF_1')=k1_relat_1('#skF_4') | k1_relat_1('#skF_4')=k1_xboole_0 | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_202, c_308])).
% 2.64/1.38  tff(c_318, plain, (k1_tarski('#skF_1')=k1_relat_1('#skF_4') | k1_relat_1('#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_99, c_311])).
% 2.64/1.38  tff(c_319, plain, (k1_tarski('#skF_1')=k1_relat_1('#skF_4')), inference(negUnitSimplification, [status(thm)], [c_147, c_318])).
% 2.64/1.38  tff(c_326, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'), '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_319, c_52])).
% 2.64/1.38  tff(c_427, plain, (![A_81, B_82, C_83, D_84]: (k7_relset_1(A_81, B_82, C_83, D_84)=k9_relat_1(C_83, D_84) | ~m1_subset_1(C_83, k1_zfmisc_1(k2_zfmisc_1(A_81, B_82))))), inference(cnfTransformation, [status(thm)], [f_94])).
% 2.64/1.38  tff(c_433, plain, (![D_84]: (k7_relset_1(k1_relat_1('#skF_4'), '#skF_2', '#skF_4', D_84)=k9_relat_1('#skF_4', D_84))), inference(resolution, [status(thm)], [c_326, c_427])).
% 2.64/1.38  tff(c_56, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_106])).
% 2.64/1.38  tff(c_38, plain, (![B_19, A_18]: (k1_tarski(k1_funct_1(B_19, A_18))=k2_relat_1(B_19) | k1_tarski(A_18)!=k1_relat_1(B_19) | ~v1_funct_1(B_19) | ~v1_relat_1(B_19))), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.64/1.38  tff(c_48, plain, (~r1_tarski(k7_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4', '#skF_3'), k1_tarski(k1_funct_1('#skF_4', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_106])).
% 2.64/1.38  tff(c_325, plain, (~r1_tarski(k7_relset_1(k1_relat_1('#skF_4'), '#skF_2', '#skF_4', '#skF_3'), k1_tarski(k1_funct_1('#skF_4', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_319, c_48])).
% 2.64/1.38  tff(c_375, plain, (~r1_tarski(k7_relset_1(k1_relat_1('#skF_4'), '#skF_2', '#skF_4', '#skF_3'), k2_relat_1('#skF_4')) | k1_tarski('#skF_1')!=k1_relat_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_38, c_325])).
% 2.64/1.38  tff(c_377, plain, (~r1_tarski(k7_relset_1(k1_relat_1('#skF_4'), '#skF_2', '#skF_4', '#skF_3'), k2_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_99, c_56, c_319, c_375])).
% 2.64/1.38  tff(c_443, plain, (~r1_tarski(k9_relat_1('#skF_4', '#skF_3'), k2_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_433, c_377])).
% 2.64/1.38  tff(c_456, plain, (~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_28, c_443])).
% 2.64/1.38  tff(c_460, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_99, c_456])).
% 2.64/1.38  tff(c_461, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_108])).
% 2.64/1.38  tff(c_30, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.64/1.38  tff(c_469, plain, (k2_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_461, c_461, c_30])).
% 2.64/1.38  tff(c_34, plain, (![A_17]: (k2_relat_1(A_17)!=k1_xboole_0 | k1_xboole_0=A_17 | ~v1_relat_1(A_17))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.64/1.38  tff(c_107, plain, (k2_relat_1('#skF_4')!=k1_xboole_0 | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_99, c_34])).
% 2.64/1.38  tff(c_146, plain, (k2_relat_1('#skF_4')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_107])).
% 2.64/1.38  tff(c_463, plain, (k2_relat_1('#skF_4')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_461, c_146])).
% 2.64/1.38  tff(c_502, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_469, c_463])).
% 2.64/1.38  tff(c_503, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_107])).
% 2.64/1.38  tff(c_8, plain, (![A_3]: (r1_tarski(k1_xboole_0, A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.64/1.38  tff(c_512, plain, (![A_3]: (r1_tarski('#skF_4', A_3))), inference(demodulation, [status(thm), theory('equality')], [c_503, c_8])).
% 2.64/1.38  tff(c_504, plain, (k2_relat_1('#skF_4')=k1_xboole_0), inference(splitRight, [status(thm)], [c_107])).
% 2.64/1.38  tff(c_519, plain, (k2_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_503, c_504])).
% 2.64/1.38  tff(c_541, plain, (![B_94, A_95]: (r1_tarski(k9_relat_1(B_94, A_95), k2_relat_1(B_94)) | ~v1_relat_1(B_94))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.64/1.38  tff(c_546, plain, (![A_95]: (r1_tarski(k9_relat_1('#skF_4', A_95), '#skF_4') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_519, c_541])).
% 2.64/1.38  tff(c_565, plain, (![A_97]: (r1_tarski(k9_relat_1('#skF_4', A_97), '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_99, c_546])).
% 2.64/1.38  tff(c_109, plain, (![B_41, A_42]: (B_41=A_42 | ~r1_tarski(B_41, A_42) | ~r1_tarski(A_42, B_41))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.64/1.38  tff(c_118, plain, (![A_3]: (k1_xboole_0=A_3 | ~r1_tarski(A_3, k1_xboole_0))), inference(resolution, [status(thm)], [c_8, c_109])).
% 2.64/1.38  tff(c_505, plain, (![A_3]: (A_3='#skF_4' | ~r1_tarski(A_3, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_503, c_503, c_118])).
% 2.64/1.38  tff(c_571, plain, (![A_97]: (k9_relat_1('#skF_4', A_97)='#skF_4')), inference(resolution, [status(thm)], [c_565, c_505])).
% 2.64/1.38  tff(c_20, plain, (![A_9]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_9)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.64/1.38  tff(c_509, plain, (![A_9]: (m1_subset_1('#skF_4', k1_zfmisc_1(A_9)))), inference(demodulation, [status(thm), theory('equality')], [c_503, c_20])).
% 2.64/1.38  tff(c_688, plain, (![A_122, B_123, C_124, D_125]: (k7_relset_1(A_122, B_123, C_124, D_125)=k9_relat_1(C_124, D_125) | ~m1_subset_1(C_124, k1_zfmisc_1(k2_zfmisc_1(A_122, B_123))))), inference(cnfTransformation, [status(thm)], [f_94])).
% 2.64/1.38  tff(c_691, plain, (![A_122, B_123, D_125]: (k7_relset_1(A_122, B_123, '#skF_4', D_125)=k9_relat_1('#skF_4', D_125))), inference(resolution, [status(thm)], [c_509, c_688])).
% 2.64/1.38  tff(c_693, plain, (![A_122, B_123, D_125]: (k7_relset_1(A_122, B_123, '#skF_4', D_125)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_571, c_691])).
% 2.64/1.38  tff(c_694, plain, (~r1_tarski('#skF_4', k1_tarski(k1_funct_1('#skF_4', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_693, c_48])).
% 2.64/1.38  tff(c_697, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_512, c_694])).
% 2.64/1.38  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.64/1.38  
% 2.64/1.38  Inference rules
% 2.64/1.38  ----------------------
% 2.64/1.38  #Ref     : 0
% 2.64/1.38  #Sup     : 119
% 2.64/1.38  #Fact    : 0
% 2.64/1.38  #Define  : 0
% 2.64/1.38  #Split   : 2
% 2.64/1.38  #Chain   : 0
% 2.64/1.38  #Close   : 0
% 2.64/1.38  
% 2.64/1.38  Ordering : KBO
% 2.64/1.38  
% 2.64/1.38  Simplification rules
% 2.64/1.38  ----------------------
% 2.64/1.38  #Subsume      : 4
% 2.64/1.38  #Demod        : 127
% 2.64/1.38  #Tautology    : 83
% 2.64/1.38  #SimpNegUnit  : 6
% 2.64/1.38  #BackRed      : 29
% 2.64/1.38  
% 2.64/1.38  #Partial instantiations: 0
% 2.64/1.38  #Strategies tried      : 1
% 2.64/1.38  
% 2.64/1.38  Timing (in seconds)
% 2.64/1.38  ----------------------
% 2.64/1.38  Preprocessing        : 0.32
% 2.64/1.38  Parsing              : 0.17
% 2.64/1.38  CNF conversion       : 0.02
% 2.64/1.38  Main loop            : 0.30
% 2.64/1.38  Inferencing          : 0.10
% 2.64/1.38  Reduction            : 0.10
% 2.64/1.38  Demodulation         : 0.07
% 2.64/1.38  BG Simplification    : 0.02
% 2.64/1.38  Subsumption          : 0.05
% 2.64/1.38  Abstraction          : 0.01
% 2.64/1.38  MUC search           : 0.00
% 2.64/1.38  Cooper               : 0.00
% 2.64/1.38  Total                : 0.65
% 2.64/1.38  Index Insertion      : 0.00
% 2.64/1.38  Index Deletion       : 0.00
% 2.64/1.38  Index Matching       : 0.00
% 2.64/1.38  BG Taut test         : 0.00
%------------------------------------------------------------------------------
