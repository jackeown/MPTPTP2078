%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:14:36 EST 2020

% Result     : Theorem 2.34s
% Output     : CNFRefutation 2.64s
% Verified   : 
% Statistics : Number of formulae       :   83 ( 266 expanded)
%              Number of leaves         :   40 ( 113 expanded)
%              Depth                    :   13
%              Number of atoms          :  113 ( 639 expanded)
%              Number of equality atoms :   59 ( 303 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_relat_1 > v1_funct_1 > k8_relset_1 > k7_relset_1 > k2_enumset1 > k2_relset_1 > k1_relset_1 > k1_enumset1 > k9_relat_1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > k11_relat_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k8_relset_1,type,(
    k8_relset_1: ( $i * $i * $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

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

tff(k11_relat_1,type,(
    k11_relat_1: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_115,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,k1_tarski(A),B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A),B))) )
       => ( B != k1_xboole_0
         => k2_relset_1(k1_tarski(A),B,C) = k1_tarski(k1_funct_1(C,A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_funct_2)).

tff(f_59,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_63,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_91,axiom,(
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

tff(f_43,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] : k11_relat_1(A,B) = k9_relat_1(A,k1_tarski(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d16_relat_1)).

tff(f_47,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k9_relat_1(A,k1_relat_1(A)) = k2_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_relat_1)).

tff(f_67,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_103,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( ( B = k1_xboole_0
         => A = k1_xboole_0 )
       => k8_relset_1(A,B,C,B) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_funct_2)).

tff(f_73,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(B,A)))
     => ( k7_relset_1(B,A,C,k8_relset_1(B,A,C,A)) = k2_relset_1(B,A,C)
        & k8_relset_1(B,A,C,k7_relset_1(B,A,C,B)) = k1_relset_1(B,A,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_relset_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

tff(f_55,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r2_hidden(A,k1_relat_1(B))
       => k11_relat_1(B,A) = k1_tarski(k1_funct_1(B,A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t117_funct_1)).

tff(c_56,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_3'),'#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_95,plain,(
    ! [C_44,A_45,B_46] :
      ( v1_relat_1(C_44)
      | ~ m1_subset_1(C_44,k1_zfmisc_1(k2_zfmisc_1(A_45,B_46))) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_99,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_56,c_95])).

tff(c_54,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_58,plain,(
    v1_funct_2('#skF_5',k1_tarski('#skF_3'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_127,plain,(
    ! [A_59,B_60,C_61] :
      ( k1_relset_1(A_59,B_60,C_61) = k1_relat_1(C_61)
      | ~ m1_subset_1(C_61,k1_zfmisc_1(k2_zfmisc_1(A_59,B_60))) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_131,plain,(
    k1_relset_1(k1_tarski('#skF_3'),'#skF_4','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_56,c_127])).

tff(c_200,plain,(
    ! [B_84,A_85,C_86] :
      ( k1_xboole_0 = B_84
      | k1_relset_1(A_85,B_84,C_86) = A_85
      | ~ v1_funct_2(C_86,A_85,B_84)
      | ~ m1_subset_1(C_86,k1_zfmisc_1(k2_zfmisc_1(A_85,B_84))) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_203,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relset_1(k1_tarski('#skF_3'),'#skF_4','#skF_5') = k1_tarski('#skF_3')
    | ~ v1_funct_2('#skF_5',k1_tarski('#skF_3'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_56,c_200])).

tff(c_206,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_tarski('#skF_3') = k1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_131,c_203])).

tff(c_207,plain,(
    k1_tarski('#skF_3') = k1_relat_1('#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_206])).

tff(c_20,plain,(
    ! [A_12,B_14] :
      ( k9_relat_1(A_12,k1_tarski(B_14)) = k11_relat_1(A_12,B_14)
      | ~ v1_relat_1(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_328,plain,(
    ! [A_91] :
      ( k9_relat_1(A_91,k1_relat_1('#skF_5')) = k11_relat_1(A_91,'#skF_3')
      | ~ v1_relat_1(A_91) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_207,c_20])).

tff(c_22,plain,(
    ! [A_15] :
      ( k9_relat_1(A_15,k1_relat_1(A_15)) = k2_relat_1(A_15)
      | ~ v1_relat_1(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_335,plain,
    ( k11_relat_1('#skF_5','#skF_3') = k2_relat_1('#skF_5')
    | ~ v1_relat_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_328,c_22])).

tff(c_345,plain,(
    k11_relat_1('#skF_5','#skF_3') = k2_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_99,c_99,c_335])).

tff(c_225,plain,(
    ! [A_12] :
      ( k9_relat_1(A_12,k1_relat_1('#skF_5')) = k11_relat_1(A_12,'#skF_3')
      | ~ v1_relat_1(A_12) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_207,c_20])).

tff(c_143,plain,(
    ! [A_66,B_67,C_68,D_69] :
      ( k7_relset_1(A_66,B_67,C_68,D_69) = k9_relat_1(C_68,D_69)
      | ~ m1_subset_1(C_68,k1_zfmisc_1(k2_zfmisc_1(A_66,B_67))) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_146,plain,(
    ! [D_69] : k7_relset_1(k1_tarski('#skF_3'),'#skF_4','#skF_5',D_69) = k9_relat_1('#skF_5',D_69) ),
    inference(resolution,[status(thm)],[c_56,c_143])).

tff(c_208,plain,(
    ! [D_69] : k7_relset_1(k1_relat_1('#skF_5'),'#skF_4','#skF_5',D_69) = k9_relat_1('#skF_5',D_69) ),
    inference(demodulation,[status(thm),theory(equality)],[c_207,c_146])).

tff(c_60,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_212,plain,(
    v1_funct_2('#skF_5',k1_relat_1('#skF_5'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_207,c_58])).

tff(c_211,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_5'),'#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_207,c_56])).

tff(c_474,plain,(
    ! [B_102,A_103,C_104] :
      ( k1_xboole_0 = B_102
      | k8_relset_1(A_103,B_102,C_104,B_102) = A_103
      | ~ m1_subset_1(C_104,k1_zfmisc_1(k2_zfmisc_1(A_103,B_102)))
      | ~ v1_funct_2(C_104,A_103,B_102)
      | ~ v1_funct_1(C_104) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_476,plain,
    ( k1_xboole_0 = '#skF_4'
    | k8_relset_1(k1_relat_1('#skF_5'),'#skF_4','#skF_5','#skF_4') = k1_relat_1('#skF_5')
    | ~ v1_funct_2('#skF_5',k1_relat_1('#skF_5'),'#skF_4')
    | ~ v1_funct_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_211,c_474])).

tff(c_479,plain,
    ( k1_xboole_0 = '#skF_4'
    | k8_relset_1(k1_relat_1('#skF_5'),'#skF_4','#skF_5','#skF_4') = k1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_212,c_476])).

tff(c_480,plain,(
    k8_relset_1(k1_relat_1('#skF_5'),'#skF_4','#skF_5','#skF_4') = k1_relat_1('#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_479])).

tff(c_356,plain,(
    ! [B_92,A_93,C_94] :
      ( k7_relset_1(B_92,A_93,C_94,k8_relset_1(B_92,A_93,C_94,A_93)) = k2_relset_1(B_92,A_93,C_94)
      | ~ m1_subset_1(C_94,k1_zfmisc_1(k2_zfmisc_1(B_92,A_93))) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_359,plain,(
    k7_relset_1(k1_relat_1('#skF_5'),'#skF_4','#skF_5',k8_relset_1(k1_relat_1('#skF_5'),'#skF_4','#skF_5','#skF_4')) = k2_relset_1(k1_relat_1('#skF_5'),'#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_211,c_356])).

tff(c_482,plain,(
    k7_relset_1(k1_relat_1('#skF_5'),'#skF_4','#skF_5',k1_relat_1('#skF_5')) = k2_relset_1(k1_relat_1('#skF_5'),'#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_480,c_359])).

tff(c_483,plain,(
    k2_relset_1(k1_relat_1('#skF_5'),'#skF_4','#skF_5') = k9_relat_1('#skF_5',k1_relat_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_208,c_482])).

tff(c_4,plain,(
    ! [C_5] : r2_hidden(C_5,k1_tarski(C_5)) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_231,plain,(
    r2_hidden('#skF_3',k1_relat_1('#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_207,c_4])).

tff(c_24,plain,(
    ! [B_17,A_16] :
      ( k1_tarski(k1_funct_1(B_17,A_16)) = k11_relat_1(B_17,A_16)
      | ~ r2_hidden(A_16,k1_relat_1(B_17))
      | ~ v1_funct_1(B_17)
      | ~ v1_relat_1(B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_240,plain,
    ( k1_tarski(k1_funct_1('#skF_5','#skF_3')) = k11_relat_1('#skF_5','#skF_3')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_231,c_24])).

tff(c_243,plain,(
    k1_tarski(k1_funct_1('#skF_5','#skF_3')) = k11_relat_1('#skF_5','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_99,c_60,c_240])).

tff(c_52,plain,(
    k2_relset_1(k1_tarski('#skF_3'),'#skF_4','#skF_5') != k1_tarski(k1_funct_1('#skF_5','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_210,plain,(
    k2_relset_1(k1_relat_1('#skF_5'),'#skF_4','#skF_5') != k1_tarski(k1_funct_1('#skF_5','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_207,c_52])).

tff(c_317,plain,(
    k2_relset_1(k1_relat_1('#skF_5'),'#skF_4','#skF_5') != k11_relat_1('#skF_5','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_243,c_210])).

tff(c_350,plain,(
    k2_relset_1(k1_relat_1('#skF_5'),'#skF_4','#skF_5') != k2_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_345,c_317])).

tff(c_488,plain,(
    k9_relat_1('#skF_5',k1_relat_1('#skF_5')) != k2_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_483,c_350])).

tff(c_495,plain,
    ( k11_relat_1('#skF_5','#skF_3') != k2_relat_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_225,c_488])).

tff(c_501,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_99,c_345,c_495])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:11:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.34/1.42  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.64/1.43  
% 2.64/1.43  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.64/1.43  %$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_relat_1 > v1_funct_1 > k8_relset_1 > k7_relset_1 > k2_enumset1 > k2_relset_1 > k1_relset_1 > k1_enumset1 > k9_relat_1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > k11_relat_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 2.64/1.43  
% 2.64/1.43  %Foreground sorts:
% 2.64/1.43  
% 2.64/1.43  
% 2.64/1.43  %Background operators:
% 2.64/1.43  
% 2.64/1.43  
% 2.64/1.43  %Foreground operators:
% 2.64/1.43  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 2.64/1.43  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.64/1.43  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.64/1.43  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.64/1.43  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.64/1.43  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 2.64/1.43  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.64/1.43  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.64/1.43  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.64/1.43  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 2.64/1.43  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.64/1.43  tff('#skF_5', type, '#skF_5': $i).
% 2.64/1.43  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.64/1.43  tff(k11_relat_1, type, k11_relat_1: ($i * $i) > $i).
% 2.64/1.43  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.64/1.43  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.64/1.43  tff('#skF_3', type, '#skF_3': $i).
% 2.64/1.43  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.64/1.43  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.64/1.43  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.64/1.43  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.64/1.43  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.64/1.43  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.64/1.43  tff('#skF_4', type, '#skF_4': $i).
% 2.64/1.43  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.64/1.43  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.64/1.43  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.64/1.43  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.64/1.43  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.64/1.43  
% 2.64/1.44  tff(f_115, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, k1_tarski(A), B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A), B)))) => (~(B = k1_xboole_0) => (k2_relset_1(k1_tarski(A), B, C) = k1_tarski(k1_funct_1(C, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t62_funct_2)).
% 2.64/1.44  tff(f_59, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.64/1.44  tff(f_63, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.64/1.44  tff(f_91, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 2.64/1.44  tff(f_43, axiom, (![A]: (v1_relat_1(A) => (![B]: (k11_relat_1(A, B) = k9_relat_1(A, k1_tarski(B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d16_relat_1)).
% 2.64/1.44  tff(f_47, axiom, (![A]: (v1_relat_1(A) => (k9_relat_1(A, k1_relat_1(A)) = k2_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t146_relat_1)).
% 2.64/1.44  tff(f_67, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 2.64/1.44  tff(f_103, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((B = k1_xboole_0) => (A = k1_xboole_0)) => (k8_relset_1(A, B, C, B) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_funct_2)).
% 2.64/1.44  tff(f_73, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => ((k7_relset_1(B, A, C, k8_relset_1(B, A, C, A)) = k2_relset_1(B, A, C)) & (k8_relset_1(B, A, C, k7_relset_1(B, A, C, B)) = k1_relset_1(B, A, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_relset_1)).
% 2.64/1.44  tff(f_32, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 2.64/1.44  tff(f_55, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r2_hidden(A, k1_relat_1(B)) => (k11_relat_1(B, A) = k1_tarski(k1_funct_1(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t117_funct_1)).
% 2.64/1.44  tff(c_56, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_3'), '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_115])).
% 2.64/1.44  tff(c_95, plain, (![C_44, A_45, B_46]: (v1_relat_1(C_44) | ~m1_subset_1(C_44, k1_zfmisc_1(k2_zfmisc_1(A_45, B_46))))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.64/1.44  tff(c_99, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_56, c_95])).
% 2.64/1.44  tff(c_54, plain, (k1_xboole_0!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_115])).
% 2.64/1.44  tff(c_58, plain, (v1_funct_2('#skF_5', k1_tarski('#skF_3'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_115])).
% 2.64/1.44  tff(c_127, plain, (![A_59, B_60, C_61]: (k1_relset_1(A_59, B_60, C_61)=k1_relat_1(C_61) | ~m1_subset_1(C_61, k1_zfmisc_1(k2_zfmisc_1(A_59, B_60))))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.64/1.44  tff(c_131, plain, (k1_relset_1(k1_tarski('#skF_3'), '#skF_4', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_56, c_127])).
% 2.64/1.44  tff(c_200, plain, (![B_84, A_85, C_86]: (k1_xboole_0=B_84 | k1_relset_1(A_85, B_84, C_86)=A_85 | ~v1_funct_2(C_86, A_85, B_84) | ~m1_subset_1(C_86, k1_zfmisc_1(k2_zfmisc_1(A_85, B_84))))), inference(cnfTransformation, [status(thm)], [f_91])).
% 2.64/1.44  tff(c_203, plain, (k1_xboole_0='#skF_4' | k1_relset_1(k1_tarski('#skF_3'), '#skF_4', '#skF_5')=k1_tarski('#skF_3') | ~v1_funct_2('#skF_5', k1_tarski('#skF_3'), '#skF_4')), inference(resolution, [status(thm)], [c_56, c_200])).
% 2.64/1.44  tff(c_206, plain, (k1_xboole_0='#skF_4' | k1_tarski('#skF_3')=k1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_131, c_203])).
% 2.64/1.44  tff(c_207, plain, (k1_tarski('#skF_3')=k1_relat_1('#skF_5')), inference(negUnitSimplification, [status(thm)], [c_54, c_206])).
% 2.64/1.44  tff(c_20, plain, (![A_12, B_14]: (k9_relat_1(A_12, k1_tarski(B_14))=k11_relat_1(A_12, B_14) | ~v1_relat_1(A_12))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.64/1.44  tff(c_328, plain, (![A_91]: (k9_relat_1(A_91, k1_relat_1('#skF_5'))=k11_relat_1(A_91, '#skF_3') | ~v1_relat_1(A_91))), inference(superposition, [status(thm), theory('equality')], [c_207, c_20])).
% 2.64/1.44  tff(c_22, plain, (![A_15]: (k9_relat_1(A_15, k1_relat_1(A_15))=k2_relat_1(A_15) | ~v1_relat_1(A_15))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.64/1.44  tff(c_335, plain, (k11_relat_1('#skF_5', '#skF_3')=k2_relat_1('#skF_5') | ~v1_relat_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_328, c_22])).
% 2.64/1.44  tff(c_345, plain, (k11_relat_1('#skF_5', '#skF_3')=k2_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_99, c_99, c_335])).
% 2.64/1.44  tff(c_225, plain, (![A_12]: (k9_relat_1(A_12, k1_relat_1('#skF_5'))=k11_relat_1(A_12, '#skF_3') | ~v1_relat_1(A_12))), inference(superposition, [status(thm), theory('equality')], [c_207, c_20])).
% 2.64/1.44  tff(c_143, plain, (![A_66, B_67, C_68, D_69]: (k7_relset_1(A_66, B_67, C_68, D_69)=k9_relat_1(C_68, D_69) | ~m1_subset_1(C_68, k1_zfmisc_1(k2_zfmisc_1(A_66, B_67))))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.64/1.44  tff(c_146, plain, (![D_69]: (k7_relset_1(k1_tarski('#skF_3'), '#skF_4', '#skF_5', D_69)=k9_relat_1('#skF_5', D_69))), inference(resolution, [status(thm)], [c_56, c_143])).
% 2.64/1.44  tff(c_208, plain, (![D_69]: (k7_relset_1(k1_relat_1('#skF_5'), '#skF_4', '#skF_5', D_69)=k9_relat_1('#skF_5', D_69))), inference(demodulation, [status(thm), theory('equality')], [c_207, c_146])).
% 2.64/1.44  tff(c_60, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_115])).
% 2.64/1.44  tff(c_212, plain, (v1_funct_2('#skF_5', k1_relat_1('#skF_5'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_207, c_58])).
% 2.64/1.44  tff(c_211, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_5'), '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_207, c_56])).
% 2.64/1.44  tff(c_474, plain, (![B_102, A_103, C_104]: (k1_xboole_0=B_102 | k8_relset_1(A_103, B_102, C_104, B_102)=A_103 | ~m1_subset_1(C_104, k1_zfmisc_1(k2_zfmisc_1(A_103, B_102))) | ~v1_funct_2(C_104, A_103, B_102) | ~v1_funct_1(C_104))), inference(cnfTransformation, [status(thm)], [f_103])).
% 2.64/1.44  tff(c_476, plain, (k1_xboole_0='#skF_4' | k8_relset_1(k1_relat_1('#skF_5'), '#skF_4', '#skF_5', '#skF_4')=k1_relat_1('#skF_5') | ~v1_funct_2('#skF_5', k1_relat_1('#skF_5'), '#skF_4') | ~v1_funct_1('#skF_5')), inference(resolution, [status(thm)], [c_211, c_474])).
% 2.64/1.44  tff(c_479, plain, (k1_xboole_0='#skF_4' | k8_relset_1(k1_relat_1('#skF_5'), '#skF_4', '#skF_5', '#skF_4')=k1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_212, c_476])).
% 2.64/1.44  tff(c_480, plain, (k8_relset_1(k1_relat_1('#skF_5'), '#skF_4', '#skF_5', '#skF_4')=k1_relat_1('#skF_5')), inference(negUnitSimplification, [status(thm)], [c_54, c_479])).
% 2.64/1.44  tff(c_356, plain, (![B_92, A_93, C_94]: (k7_relset_1(B_92, A_93, C_94, k8_relset_1(B_92, A_93, C_94, A_93))=k2_relset_1(B_92, A_93, C_94) | ~m1_subset_1(C_94, k1_zfmisc_1(k2_zfmisc_1(B_92, A_93))))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.64/1.44  tff(c_359, plain, (k7_relset_1(k1_relat_1('#skF_5'), '#skF_4', '#skF_5', k8_relset_1(k1_relat_1('#skF_5'), '#skF_4', '#skF_5', '#skF_4'))=k2_relset_1(k1_relat_1('#skF_5'), '#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_211, c_356])).
% 2.64/1.44  tff(c_482, plain, (k7_relset_1(k1_relat_1('#skF_5'), '#skF_4', '#skF_5', k1_relat_1('#skF_5'))=k2_relset_1(k1_relat_1('#skF_5'), '#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_480, c_359])).
% 2.64/1.44  tff(c_483, plain, (k2_relset_1(k1_relat_1('#skF_5'), '#skF_4', '#skF_5')=k9_relat_1('#skF_5', k1_relat_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_208, c_482])).
% 2.64/1.44  tff(c_4, plain, (![C_5]: (r2_hidden(C_5, k1_tarski(C_5)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.64/1.44  tff(c_231, plain, (r2_hidden('#skF_3', k1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_207, c_4])).
% 2.64/1.44  tff(c_24, plain, (![B_17, A_16]: (k1_tarski(k1_funct_1(B_17, A_16))=k11_relat_1(B_17, A_16) | ~r2_hidden(A_16, k1_relat_1(B_17)) | ~v1_funct_1(B_17) | ~v1_relat_1(B_17))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.64/1.44  tff(c_240, plain, (k1_tarski(k1_funct_1('#skF_5', '#skF_3'))=k11_relat_1('#skF_5', '#skF_3') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_231, c_24])).
% 2.64/1.44  tff(c_243, plain, (k1_tarski(k1_funct_1('#skF_5', '#skF_3'))=k11_relat_1('#skF_5', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_99, c_60, c_240])).
% 2.64/1.44  tff(c_52, plain, (k2_relset_1(k1_tarski('#skF_3'), '#skF_4', '#skF_5')!=k1_tarski(k1_funct_1('#skF_5', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_115])).
% 2.64/1.44  tff(c_210, plain, (k2_relset_1(k1_relat_1('#skF_5'), '#skF_4', '#skF_5')!=k1_tarski(k1_funct_1('#skF_5', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_207, c_52])).
% 2.64/1.44  tff(c_317, plain, (k2_relset_1(k1_relat_1('#skF_5'), '#skF_4', '#skF_5')!=k11_relat_1('#skF_5', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_243, c_210])).
% 2.64/1.44  tff(c_350, plain, (k2_relset_1(k1_relat_1('#skF_5'), '#skF_4', '#skF_5')!=k2_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_345, c_317])).
% 2.64/1.44  tff(c_488, plain, (k9_relat_1('#skF_5', k1_relat_1('#skF_5'))!=k2_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_483, c_350])).
% 2.64/1.44  tff(c_495, plain, (k11_relat_1('#skF_5', '#skF_3')!=k2_relat_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_225, c_488])).
% 2.64/1.44  tff(c_501, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_99, c_345, c_495])).
% 2.64/1.44  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.64/1.44  
% 2.64/1.44  Inference rules
% 2.64/1.44  ----------------------
% 2.64/1.44  #Ref     : 0
% 2.64/1.44  #Sup     : 103
% 2.64/1.44  #Fact    : 0
% 2.64/1.44  #Define  : 0
% 2.64/1.44  #Split   : 0
% 2.64/1.44  #Chain   : 0
% 2.64/1.44  #Close   : 0
% 2.64/1.44  
% 2.64/1.44  Ordering : KBO
% 2.64/1.44  
% 2.64/1.44  Simplification rules
% 2.64/1.44  ----------------------
% 2.64/1.44  #Subsume      : 3
% 2.64/1.44  #Demod        : 73
% 2.64/1.44  #Tautology    : 64
% 2.64/1.44  #SimpNegUnit  : 5
% 2.64/1.44  #BackRed      : 11
% 2.64/1.44  
% 2.64/1.44  #Partial instantiations: 0
% 2.64/1.44  #Strategies tried      : 1
% 2.64/1.44  
% 2.64/1.44  Timing (in seconds)
% 2.64/1.44  ----------------------
% 2.64/1.45  Preprocessing        : 0.35
% 2.64/1.45  Parsing              : 0.19
% 2.64/1.45  CNF conversion       : 0.02
% 2.64/1.45  Main loop            : 0.29
% 2.64/1.45  Inferencing          : 0.11
% 2.64/1.45  Reduction            : 0.09
% 2.64/1.45  Demodulation         : 0.06
% 2.64/1.45  BG Simplification    : 0.02
% 2.64/1.45  Subsumption          : 0.06
% 2.64/1.45  Abstraction          : 0.01
% 2.64/1.45  MUC search           : 0.00
% 2.64/1.45  Cooper               : 0.00
% 2.64/1.45  Total                : 0.67
% 2.64/1.45  Index Insertion      : 0.00
% 2.64/1.45  Index Deletion       : 0.00
% 2.64/1.45  Index Matching       : 0.00
% 2.64/1.45  BG Taut test         : 0.00
%------------------------------------------------------------------------------
