%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:07:45 EST 2020

% Result     : Theorem 2.61s
% Output     : CNFRefutation 2.61s
% Verified   : 
% Statistics : Number of formulae       :   69 (  88 expanded)
%              Number of leaves         :   32 (  43 expanded)
%              Depth                    :   16
%              Number of atoms          :  107 ( 149 expanded)
%              Number of equality atoms :    9 (   9 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k6_relset_1 > k8_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k8_relat_1,type,(
    k8_relat_1: ( $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_relset_1,type,(
    r2_relset_1: ( $i * $i * $i * $i ) > $o )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k6_relset_1,type,(
    k6_relset_1: ( $i * $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_89,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B)))
       => ( r1_tarski(B,C)
         => r2_relset_1(A,B,k6_relset_1(A,B,C,D),D) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_relset_1)).

tff(f_82,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_64,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_70,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_54,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_42,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_32,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => r1_tarski(k1_zfmisc_1(A),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_zfmisc_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_48,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

tff(f_60,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k2_relat_1(B),A)
       => k8_relat_1(A,B) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t125_relat_1)).

tff(f_74,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k6_relset_1(A,B,C,D) = k8_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_relset_1)).

tff(c_36,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_143,plain,(
    ! [A_68,B_69,D_70] :
      ( r2_relset_1(A_68,B_69,D_70,D_70)
      | ~ m1_subset_1(D_70,k1_zfmisc_1(k2_zfmisc_1(A_68,B_69))) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_150,plain,(
    r2_relset_1('#skF_1','#skF_2','#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_36,c_143])).

tff(c_49,plain,(
    ! [C_36,A_37,B_38] :
      ( v1_relat_1(C_36)
      | ~ m1_subset_1(C_36,k1_zfmisc_1(k2_zfmisc_1(A_37,B_38))) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_58,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_36,c_49])).

tff(c_98,plain,(
    ! [C_54,B_55,A_56] :
      ( v5_relat_1(C_54,B_55)
      | ~ m1_subset_1(C_54,k1_zfmisc_1(k2_zfmisc_1(A_56,B_55))) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_107,plain,(
    v5_relat_1('#skF_4','#skF_2') ),
    inference(resolution,[status(thm)],[c_36,c_98])).

tff(c_16,plain,(
    ! [B_12,A_11] :
      ( r1_tarski(k2_relat_1(B_12),A_11)
      | ~ v5_relat_1(B_12,A_11)
      | ~ v1_relat_1(B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_34,plain,(
    r1_tarski('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_10,plain,(
    ! [A_6,B_7] :
      ( m1_subset_1(A_6,k1_zfmisc_1(B_7))
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_4,plain,(
    ! [A_3] : ~ v1_xboole_0(k1_zfmisc_1(A_3)) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( r1_tarski(k1_zfmisc_1(A_1),k1_zfmisc_1(B_2))
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_6,plain,(
    ! [A_4,B_5] :
      ( r2_hidden(A_4,B_5)
      | v1_xboole_0(B_5)
      | ~ m1_subset_1(A_4,B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_135,plain,(
    ! [A_64,C_65,B_66] :
      ( m1_subset_1(A_64,C_65)
      | ~ m1_subset_1(B_66,k1_zfmisc_1(C_65))
      | ~ r2_hidden(A_64,B_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_151,plain,(
    ! [A_71,B_72,A_73] :
      ( m1_subset_1(A_71,B_72)
      | ~ r2_hidden(A_71,A_73)
      | ~ r1_tarski(A_73,B_72) ) ),
    inference(resolution,[status(thm)],[c_10,c_135])).

tff(c_183,plain,(
    ! [A_85,B_86,B_87] :
      ( m1_subset_1(A_85,B_86)
      | ~ r1_tarski(B_87,B_86)
      | v1_xboole_0(B_87)
      | ~ m1_subset_1(A_85,B_87) ) ),
    inference(resolution,[status(thm)],[c_6,c_151])).

tff(c_187,plain,(
    ! [A_85,B_2,A_1] :
      ( m1_subset_1(A_85,k1_zfmisc_1(B_2))
      | v1_xboole_0(k1_zfmisc_1(A_1))
      | ~ m1_subset_1(A_85,k1_zfmisc_1(A_1))
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(resolution,[status(thm)],[c_2,c_183])).

tff(c_209,plain,(
    ! [A_98,B_99,A_100] :
      ( m1_subset_1(A_98,k1_zfmisc_1(B_99))
      | ~ m1_subset_1(A_98,k1_zfmisc_1(A_100))
      | ~ r1_tarski(A_100,B_99) ) ),
    inference(negUnitSimplification,[status(thm)],[c_4,c_187])).

tff(c_217,plain,(
    ! [A_102,B_103,B_104] :
      ( m1_subset_1(A_102,k1_zfmisc_1(B_103))
      | ~ r1_tarski(B_104,B_103)
      | ~ r1_tarski(A_102,B_104) ) ),
    inference(resolution,[status(thm)],[c_10,c_209])).

tff(c_230,plain,(
    ! [A_105] :
      ( m1_subset_1(A_105,k1_zfmisc_1('#skF_3'))
      | ~ r1_tarski(A_105,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_34,c_217])).

tff(c_8,plain,(
    ! [A_6,B_7] :
      ( r1_tarski(A_6,B_7)
      | ~ m1_subset_1(A_6,k1_zfmisc_1(B_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_250,plain,(
    ! [A_110] :
      ( r1_tarski(A_110,'#skF_3')
      | ~ r1_tarski(A_110,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_230,c_8])).

tff(c_354,plain,(
    ! [B_123] :
      ( r1_tarski(k2_relat_1(B_123),'#skF_3')
      | ~ v5_relat_1(B_123,'#skF_2')
      | ~ v1_relat_1(B_123) ) ),
    inference(resolution,[status(thm)],[c_16,c_250])).

tff(c_14,plain,(
    ! [B_12,A_11] :
      ( v5_relat_1(B_12,A_11)
      | ~ r1_tarski(k2_relat_1(B_12),A_11)
      | ~ v1_relat_1(B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_369,plain,(
    ! [B_124] :
      ( v5_relat_1(B_124,'#skF_3')
      | ~ v5_relat_1(B_124,'#skF_2')
      | ~ v1_relat_1(B_124) ) ),
    inference(resolution,[status(thm)],[c_354,c_14])).

tff(c_375,plain,
    ( v5_relat_1('#skF_4','#skF_3')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_107,c_369])).

tff(c_379,plain,(
    v5_relat_1('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_375])).

tff(c_108,plain,(
    ! [A_57,B_58] :
      ( k8_relat_1(A_57,B_58) = B_58
      | ~ r1_tarski(k2_relat_1(B_58),A_57)
      | ~ v1_relat_1(B_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_112,plain,(
    ! [A_11,B_12] :
      ( k8_relat_1(A_11,B_12) = B_12
      | ~ v5_relat_1(B_12,A_11)
      | ~ v1_relat_1(B_12) ) ),
    inference(resolution,[status(thm)],[c_16,c_108])).

tff(c_382,plain,
    ( k8_relat_1('#skF_3','#skF_4') = '#skF_4'
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_379,c_112])).

tff(c_385,plain,(
    k8_relat_1('#skF_3','#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_382])).

tff(c_164,plain,(
    ! [A_77,B_78,C_79,D_80] :
      ( k6_relset_1(A_77,B_78,C_79,D_80) = k8_relat_1(C_79,D_80)
      | ~ m1_subset_1(D_80,k1_zfmisc_1(k2_zfmisc_1(A_77,B_78))) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_171,plain,(
    ! [C_79] : k6_relset_1('#skF_1','#skF_2',C_79,'#skF_4') = k8_relat_1(C_79,'#skF_4') ),
    inference(resolution,[status(thm)],[c_36,c_164])).

tff(c_32,plain,(
    ~ r2_relset_1('#skF_1','#skF_2',k6_relset_1('#skF_1','#skF_2','#skF_3','#skF_4'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_172,plain,(
    ~ r2_relset_1('#skF_1','#skF_2',k8_relat_1('#skF_3','#skF_4'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_171,c_32])).

tff(c_420,plain,(
    ~ r2_relset_1('#skF_1','#skF_2','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_385,c_172])).

tff(c_423,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_150,c_420])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n022.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 14:13:10 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.61/1.41  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.61/1.42  
% 2.61/1.42  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.61/1.42  %$ r2_relset_1 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k6_relset_1 > k8_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.61/1.42  
% 2.61/1.42  %Foreground sorts:
% 2.61/1.42  
% 2.61/1.42  
% 2.61/1.42  %Background operators:
% 2.61/1.42  
% 2.61/1.42  
% 2.61/1.42  %Foreground operators:
% 2.61/1.42  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 2.61/1.42  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.61/1.42  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 2.61/1.42  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.61/1.42  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.61/1.42  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.61/1.42  tff(k6_relset_1, type, k6_relset_1: ($i * $i * $i * $i) > $i).
% 2.61/1.42  tff('#skF_2', type, '#skF_2': $i).
% 2.61/1.42  tff('#skF_3', type, '#skF_3': $i).
% 2.61/1.42  tff('#skF_1', type, '#skF_1': $i).
% 2.61/1.42  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.61/1.42  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.61/1.42  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.61/1.42  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.61/1.42  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.61/1.42  tff('#skF_4', type, '#skF_4': $i).
% 2.61/1.42  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.61/1.42  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.61/1.42  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.61/1.42  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.61/1.42  
% 2.61/1.44  tff(f_89, negated_conjecture, ~(![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (r1_tarski(B, C) => r2_relset_1(A, B, k6_relset_1(A, B, C, D), D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_relset_1)).
% 2.61/1.44  tff(f_82, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 2.61/1.44  tff(f_64, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.61/1.44  tff(f_70, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.61/1.44  tff(f_54, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 2.61/1.44  tff(f_42, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 2.61/1.44  tff(f_32, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_subset_1)).
% 2.61/1.44  tff(f_29, axiom, (![A, B]: (r1_tarski(A, B) => r1_tarski(k1_zfmisc_1(A), k1_zfmisc_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_zfmisc_1)).
% 2.61/1.44  tff(f_38, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 2.61/1.44  tff(f_48, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset)).
% 2.61/1.44  tff(f_60, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(B), A) => (k8_relat_1(A, B) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t125_relat_1)).
% 2.61/1.44  tff(f_74, axiom, (![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k6_relset_1(A, B, C, D) = k8_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_relset_1)).
% 2.61/1.44  tff(c_36, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.61/1.44  tff(c_143, plain, (![A_68, B_69, D_70]: (r2_relset_1(A_68, B_69, D_70, D_70) | ~m1_subset_1(D_70, k1_zfmisc_1(k2_zfmisc_1(A_68, B_69))))), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.61/1.44  tff(c_150, plain, (r2_relset_1('#skF_1', '#skF_2', '#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_36, c_143])).
% 2.61/1.44  tff(c_49, plain, (![C_36, A_37, B_38]: (v1_relat_1(C_36) | ~m1_subset_1(C_36, k1_zfmisc_1(k2_zfmisc_1(A_37, B_38))))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.61/1.44  tff(c_58, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_36, c_49])).
% 2.61/1.44  tff(c_98, plain, (![C_54, B_55, A_56]: (v5_relat_1(C_54, B_55) | ~m1_subset_1(C_54, k1_zfmisc_1(k2_zfmisc_1(A_56, B_55))))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.61/1.44  tff(c_107, plain, (v5_relat_1('#skF_4', '#skF_2')), inference(resolution, [status(thm)], [c_36, c_98])).
% 2.61/1.44  tff(c_16, plain, (![B_12, A_11]: (r1_tarski(k2_relat_1(B_12), A_11) | ~v5_relat_1(B_12, A_11) | ~v1_relat_1(B_12))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.61/1.44  tff(c_34, plain, (r1_tarski('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.61/1.44  tff(c_10, plain, (![A_6, B_7]: (m1_subset_1(A_6, k1_zfmisc_1(B_7)) | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.61/1.44  tff(c_4, plain, (![A_3]: (~v1_xboole_0(k1_zfmisc_1(A_3)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.61/1.44  tff(c_2, plain, (![A_1, B_2]: (r1_tarski(k1_zfmisc_1(A_1), k1_zfmisc_1(B_2)) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.61/1.44  tff(c_6, plain, (![A_4, B_5]: (r2_hidden(A_4, B_5) | v1_xboole_0(B_5) | ~m1_subset_1(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.61/1.44  tff(c_135, plain, (![A_64, C_65, B_66]: (m1_subset_1(A_64, C_65) | ~m1_subset_1(B_66, k1_zfmisc_1(C_65)) | ~r2_hidden(A_64, B_66))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.61/1.44  tff(c_151, plain, (![A_71, B_72, A_73]: (m1_subset_1(A_71, B_72) | ~r2_hidden(A_71, A_73) | ~r1_tarski(A_73, B_72))), inference(resolution, [status(thm)], [c_10, c_135])).
% 2.61/1.44  tff(c_183, plain, (![A_85, B_86, B_87]: (m1_subset_1(A_85, B_86) | ~r1_tarski(B_87, B_86) | v1_xboole_0(B_87) | ~m1_subset_1(A_85, B_87))), inference(resolution, [status(thm)], [c_6, c_151])).
% 2.61/1.44  tff(c_187, plain, (![A_85, B_2, A_1]: (m1_subset_1(A_85, k1_zfmisc_1(B_2)) | v1_xboole_0(k1_zfmisc_1(A_1)) | ~m1_subset_1(A_85, k1_zfmisc_1(A_1)) | ~r1_tarski(A_1, B_2))), inference(resolution, [status(thm)], [c_2, c_183])).
% 2.61/1.44  tff(c_209, plain, (![A_98, B_99, A_100]: (m1_subset_1(A_98, k1_zfmisc_1(B_99)) | ~m1_subset_1(A_98, k1_zfmisc_1(A_100)) | ~r1_tarski(A_100, B_99))), inference(negUnitSimplification, [status(thm)], [c_4, c_187])).
% 2.61/1.44  tff(c_217, plain, (![A_102, B_103, B_104]: (m1_subset_1(A_102, k1_zfmisc_1(B_103)) | ~r1_tarski(B_104, B_103) | ~r1_tarski(A_102, B_104))), inference(resolution, [status(thm)], [c_10, c_209])).
% 2.61/1.44  tff(c_230, plain, (![A_105]: (m1_subset_1(A_105, k1_zfmisc_1('#skF_3')) | ~r1_tarski(A_105, '#skF_2'))), inference(resolution, [status(thm)], [c_34, c_217])).
% 2.61/1.44  tff(c_8, plain, (![A_6, B_7]: (r1_tarski(A_6, B_7) | ~m1_subset_1(A_6, k1_zfmisc_1(B_7)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.61/1.44  tff(c_250, plain, (![A_110]: (r1_tarski(A_110, '#skF_3') | ~r1_tarski(A_110, '#skF_2'))), inference(resolution, [status(thm)], [c_230, c_8])).
% 2.61/1.44  tff(c_354, plain, (![B_123]: (r1_tarski(k2_relat_1(B_123), '#skF_3') | ~v5_relat_1(B_123, '#skF_2') | ~v1_relat_1(B_123))), inference(resolution, [status(thm)], [c_16, c_250])).
% 2.61/1.44  tff(c_14, plain, (![B_12, A_11]: (v5_relat_1(B_12, A_11) | ~r1_tarski(k2_relat_1(B_12), A_11) | ~v1_relat_1(B_12))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.61/1.44  tff(c_369, plain, (![B_124]: (v5_relat_1(B_124, '#skF_3') | ~v5_relat_1(B_124, '#skF_2') | ~v1_relat_1(B_124))), inference(resolution, [status(thm)], [c_354, c_14])).
% 2.61/1.44  tff(c_375, plain, (v5_relat_1('#skF_4', '#skF_3') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_107, c_369])).
% 2.61/1.44  tff(c_379, plain, (v5_relat_1('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_375])).
% 2.61/1.44  tff(c_108, plain, (![A_57, B_58]: (k8_relat_1(A_57, B_58)=B_58 | ~r1_tarski(k2_relat_1(B_58), A_57) | ~v1_relat_1(B_58))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.61/1.44  tff(c_112, plain, (![A_11, B_12]: (k8_relat_1(A_11, B_12)=B_12 | ~v5_relat_1(B_12, A_11) | ~v1_relat_1(B_12))), inference(resolution, [status(thm)], [c_16, c_108])).
% 2.61/1.44  tff(c_382, plain, (k8_relat_1('#skF_3', '#skF_4')='#skF_4' | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_379, c_112])).
% 2.61/1.44  tff(c_385, plain, (k8_relat_1('#skF_3', '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_58, c_382])).
% 2.61/1.44  tff(c_164, plain, (![A_77, B_78, C_79, D_80]: (k6_relset_1(A_77, B_78, C_79, D_80)=k8_relat_1(C_79, D_80) | ~m1_subset_1(D_80, k1_zfmisc_1(k2_zfmisc_1(A_77, B_78))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.61/1.44  tff(c_171, plain, (![C_79]: (k6_relset_1('#skF_1', '#skF_2', C_79, '#skF_4')=k8_relat_1(C_79, '#skF_4'))), inference(resolution, [status(thm)], [c_36, c_164])).
% 2.61/1.44  tff(c_32, plain, (~r2_relset_1('#skF_1', '#skF_2', k6_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.61/1.44  tff(c_172, plain, (~r2_relset_1('#skF_1', '#skF_2', k8_relat_1('#skF_3', '#skF_4'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_171, c_32])).
% 2.61/1.44  tff(c_420, plain, (~r2_relset_1('#skF_1', '#skF_2', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_385, c_172])).
% 2.61/1.44  tff(c_423, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_150, c_420])).
% 2.61/1.44  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.61/1.44  
% 2.61/1.44  Inference rules
% 2.61/1.44  ----------------------
% 2.61/1.44  #Ref     : 0
% 2.61/1.44  #Sup     : 85
% 2.61/1.44  #Fact    : 0
% 2.61/1.44  #Define  : 0
% 2.61/1.44  #Split   : 2
% 2.61/1.44  #Chain   : 0
% 2.61/1.44  #Close   : 0
% 2.61/1.44  
% 2.61/1.44  Ordering : KBO
% 2.61/1.44  
% 2.61/1.44  Simplification rules
% 2.61/1.44  ----------------------
% 2.61/1.44  #Subsume      : 4
% 2.61/1.44  #Demod        : 13
% 2.61/1.44  #Tautology    : 15
% 2.61/1.44  #SimpNegUnit  : 1
% 2.61/1.44  #BackRed      : 2
% 2.61/1.44  
% 2.61/1.44  #Partial instantiations: 0
% 2.61/1.44  #Strategies tried      : 1
% 2.61/1.44  
% 2.61/1.44  Timing (in seconds)
% 2.61/1.44  ----------------------
% 2.61/1.44  Preprocessing        : 0.33
% 2.61/1.44  Parsing              : 0.18
% 2.61/1.44  CNF conversion       : 0.02
% 2.61/1.44  Main loop            : 0.27
% 2.61/1.44  Inferencing          : 0.11
% 2.61/1.44  Reduction            : 0.07
% 2.61/1.44  Demodulation         : 0.05
% 2.61/1.44  BG Simplification    : 0.02
% 2.61/1.44  Subsumption          : 0.05
% 2.61/1.44  Abstraction          : 0.02
% 2.61/1.44  MUC search           : 0.00
% 2.61/1.44  Cooper               : 0.00
% 2.61/1.44  Total                : 0.63
% 2.61/1.44  Index Insertion      : 0.00
% 2.61/1.44  Index Deletion       : 0.00
% 2.61/1.44  Index Matching       : 0.00
% 2.61/1.44  BG Taut test         : 0.00
%------------------------------------------------------------------------------
