%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:07:04 EST 2020

% Result     : Theorem 3.09s
% Output     : CNFRefutation 3.09s
% Verified   : 
% Statistics : Number of formulae       :   65 ( 151 expanded)
%              Number of leaves         :   28 (  62 expanded)
%              Depth                    :    8
%              Number of atoms          :   90 ( 261 expanded)
%              Number of equality atoms :    4 (  10 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k2_zfmisc_1 > k2_xboole_0 > #nlpp > k3_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k3_relat_1,type,(
    k3_relat_1: $i > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

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

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_66,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_77,negated_conjecture,(
    ~ ! [A,B,C] :
        ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
       => r1_tarski(k3_relat_1(C),k2_xboole_0(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_relset_1)).

tff(f_48,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_72,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_60,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(k2_xboole_0(A,C),k2_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_xboole_1)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_xboole_0(A,B),C)
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).

tff(f_54,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_64,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k3_relat_1(A) = k2_xboole_0(k1_relat_1(A),k2_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_relat_1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(C,B) )
     => r1_tarski(k2_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_xboole_1)).

tff(c_22,plain,(
    ! [A_20,B_21] : v1_relat_1(k2_zfmisc_1(A_20,B_21)) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_30,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_65,plain,(
    ! [B_29,A_30] :
      ( v1_relat_1(B_29)
      | ~ m1_subset_1(B_29,k1_zfmisc_1(A_30))
      | ~ v1_relat_1(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_68,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_30,c_65])).

tff(c_71,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_68])).

tff(c_101,plain,(
    ! [C_38,B_39,A_40] :
      ( v5_relat_1(C_38,B_39)
      | ~ m1_subset_1(C_38,k1_zfmisc_1(k2_zfmisc_1(A_40,B_39))) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_105,plain,(
    v5_relat_1('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_30,c_101])).

tff(c_18,plain,(
    ! [B_18,A_17] :
      ( r1_tarski(k2_relat_1(B_18),A_17)
      | ~ v5_relat_1(B_18,A_17)
      | ~ v1_relat_1(B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_123,plain,(
    ! [A_52,C_53,B_54] :
      ( r1_tarski(k2_xboole_0(A_52,C_53),k2_xboole_0(B_54,C_53))
      | ~ r1_tarski(A_52,B_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_4,plain,(
    ! [A_3,C_5,B_4] :
      ( r1_tarski(A_3,C_5)
      | ~ r1_tarski(k2_xboole_0(A_3,B_4),C_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_168,plain,(
    ! [A_58,B_59,C_60] :
      ( r1_tarski(A_58,k2_xboole_0(B_59,C_60))
      | ~ r1_tarski(A_58,B_59) ) ),
    inference(resolution,[status(thm)],[c_123,c_4])).

tff(c_193,plain,(
    ! [A_58,B_2,A_1] :
      ( r1_tarski(A_58,k2_xboole_0(B_2,A_1))
      | ~ r1_tarski(A_58,A_1) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_168])).

tff(c_107,plain,(
    ! [C_43,A_44,B_45] :
      ( v4_relat_1(C_43,A_44)
      | ~ m1_subset_1(C_43,k1_zfmisc_1(k2_zfmisc_1(A_44,B_45))) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_111,plain,(
    v4_relat_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_30,c_107])).

tff(c_14,plain,(
    ! [B_16,A_15] :
      ( r1_tarski(k1_relat_1(B_16),A_15)
      | ~ v4_relat_1(B_16,A_15)
      | ~ v1_relat_1(B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_20,plain,(
    ! [A_19] :
      ( k2_xboole_0(k1_relat_1(A_19),k2_relat_1(A_19)) = k3_relat_1(A_19)
      | ~ v1_relat_1(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_150,plain,(
    ! [A_55,C_56,B_57] :
      ( r1_tarski(k2_xboole_0(A_55,C_56),B_57)
      | ~ r1_tarski(C_56,B_57)
      | ~ r1_tarski(A_55,B_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_820,plain,(
    ! [A_121,B_122] :
      ( r1_tarski(k3_relat_1(A_121),B_122)
      | ~ r1_tarski(k2_relat_1(A_121),B_122)
      | ~ r1_tarski(k1_relat_1(A_121),B_122)
      | ~ v1_relat_1(A_121) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_150])).

tff(c_28,plain,(
    ~ r1_tarski(k3_relat_1('#skF_3'),k2_xboole_0('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_201,plain,(
    ~ r1_tarski(k3_relat_1('#skF_3'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_168,c_28])).

tff(c_846,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_3'),'#skF_1')
    | ~ r1_tarski(k1_relat_1('#skF_3'),'#skF_1')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_820,c_201])).

tff(c_864,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_3'),'#skF_1')
    | ~ r1_tarski(k1_relat_1('#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_71,c_846])).

tff(c_868,plain,(
    ~ r1_tarski(k1_relat_1('#skF_3'),'#skF_1') ),
    inference(splitLeft,[status(thm)],[c_864])).

tff(c_871,plain,
    ( ~ v4_relat_1('#skF_3','#skF_1')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_14,c_868])).

tff(c_875,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_71,c_111,c_871])).

tff(c_877,plain,(
    r1_tarski(k1_relat_1('#skF_3'),'#skF_1') ),
    inference(splitRight,[status(thm)],[c_864])).

tff(c_149,plain,(
    ! [A_52,B_54,C_53] :
      ( r1_tarski(A_52,k2_xboole_0(B_54,C_53))
      | ~ r1_tarski(A_52,B_54) ) ),
    inference(resolution,[status(thm)],[c_123,c_4])).

tff(c_849,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_3'),k2_xboole_0('#skF_1','#skF_2'))
    | ~ r1_tarski(k1_relat_1('#skF_3'),k2_xboole_0('#skF_1','#skF_2'))
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_820,c_28])).

tff(c_867,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_3'),k2_xboole_0('#skF_1','#skF_2'))
    | ~ r1_tarski(k1_relat_1('#skF_3'),k2_xboole_0('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_71,c_849])).

tff(c_884,plain,(
    ~ r1_tarski(k1_relat_1('#skF_3'),k2_xboole_0('#skF_1','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_867])).

tff(c_1064,plain,(
    ~ r1_tarski(k1_relat_1('#skF_3'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_149,c_884])).

tff(c_1072,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_877,c_1064])).

tff(c_1073,plain,(
    ~ r1_tarski(k2_relat_1('#skF_3'),k2_xboole_0('#skF_1','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_867])).

tff(c_1187,plain,(
    ~ r1_tarski(k2_relat_1('#skF_3'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_193,c_1073])).

tff(c_1194,plain,
    ( ~ v5_relat_1('#skF_3','#skF_2')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_18,c_1187])).

tff(c_1198,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_71,c_105,c_1194])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.11/0.33  % Computer   : n010.cluster.edu
% 0.11/0.33  % Model      : x86_64 x86_64
% 0.11/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.33  % Memory     : 8042.1875MB
% 0.11/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.33  % CPULimit   : 60
% 0.11/0.33  % DateTime   : Tue Dec  1 14:13:44 EST 2020
% 0.11/0.33  % CPUTime    : 
% 0.11/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.09/1.57  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.09/1.58  
% 3.09/1.58  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.09/1.58  %$ v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k2_zfmisc_1 > k2_xboole_0 > #nlpp > k3_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 3.09/1.58  
% 3.09/1.58  %Foreground sorts:
% 3.09/1.58  
% 3.09/1.58  
% 3.09/1.58  %Background operators:
% 3.09/1.58  
% 3.09/1.58  
% 3.09/1.58  %Foreground operators:
% 3.09/1.58  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.09/1.58  tff(k3_relat_1, type, k3_relat_1: $i > $i).
% 3.09/1.58  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.09/1.58  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.09/1.58  tff('#skF_2', type, '#skF_2': $i).
% 3.09/1.58  tff('#skF_3', type, '#skF_3': $i).
% 3.09/1.58  tff('#skF_1', type, '#skF_1': $i).
% 3.09/1.58  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.09/1.58  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.09/1.58  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.09/1.58  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.09/1.58  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.09/1.58  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.09/1.58  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.09/1.58  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.09/1.58  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.09/1.58  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.09/1.58  
% 3.09/1.59  tff(f_66, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 3.09/1.59  tff(f_77, negated_conjecture, ~(![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => r1_tarski(k3_relat_1(C), k2_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t19_relset_1)).
% 3.09/1.59  tff(f_48, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 3.09/1.59  tff(f_72, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.09/1.59  tff(f_60, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 3.09/1.59  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 3.09/1.59  tff(f_41, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(k2_xboole_0(A, C), k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t9_xboole_1)).
% 3.09/1.59  tff(f_31, axiom, (![A, B, C]: (r1_tarski(k2_xboole_0(A, B), C) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_xboole_1)).
% 3.09/1.59  tff(f_54, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d18_relat_1)).
% 3.09/1.59  tff(f_64, axiom, (![A]: (v1_relat_1(A) => (k3_relat_1(A) = k2_xboole_0(k1_relat_1(A), k2_relat_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d6_relat_1)).
% 3.09/1.59  tff(f_37, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(C, B)) => r1_tarski(k2_xboole_0(A, C), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_xboole_1)).
% 3.09/1.59  tff(c_22, plain, (![A_20, B_21]: (v1_relat_1(k2_zfmisc_1(A_20, B_21)))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.09/1.59  tff(c_30, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.09/1.59  tff(c_65, plain, (![B_29, A_30]: (v1_relat_1(B_29) | ~m1_subset_1(B_29, k1_zfmisc_1(A_30)) | ~v1_relat_1(A_30))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.09/1.59  tff(c_68, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_30, c_65])).
% 3.09/1.59  tff(c_71, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_22, c_68])).
% 3.09/1.59  tff(c_101, plain, (![C_38, B_39, A_40]: (v5_relat_1(C_38, B_39) | ~m1_subset_1(C_38, k1_zfmisc_1(k2_zfmisc_1(A_40, B_39))))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.09/1.59  tff(c_105, plain, (v5_relat_1('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_30, c_101])).
% 3.09/1.59  tff(c_18, plain, (![B_18, A_17]: (r1_tarski(k2_relat_1(B_18), A_17) | ~v5_relat_1(B_18, A_17) | ~v1_relat_1(B_18))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.09/1.59  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.09/1.59  tff(c_123, plain, (![A_52, C_53, B_54]: (r1_tarski(k2_xboole_0(A_52, C_53), k2_xboole_0(B_54, C_53)) | ~r1_tarski(A_52, B_54))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.09/1.59  tff(c_4, plain, (![A_3, C_5, B_4]: (r1_tarski(A_3, C_5) | ~r1_tarski(k2_xboole_0(A_3, B_4), C_5))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.09/1.59  tff(c_168, plain, (![A_58, B_59, C_60]: (r1_tarski(A_58, k2_xboole_0(B_59, C_60)) | ~r1_tarski(A_58, B_59))), inference(resolution, [status(thm)], [c_123, c_4])).
% 3.09/1.59  tff(c_193, plain, (![A_58, B_2, A_1]: (r1_tarski(A_58, k2_xboole_0(B_2, A_1)) | ~r1_tarski(A_58, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_168])).
% 3.09/1.59  tff(c_107, plain, (![C_43, A_44, B_45]: (v4_relat_1(C_43, A_44) | ~m1_subset_1(C_43, k1_zfmisc_1(k2_zfmisc_1(A_44, B_45))))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.09/1.59  tff(c_111, plain, (v4_relat_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_30, c_107])).
% 3.09/1.59  tff(c_14, plain, (![B_16, A_15]: (r1_tarski(k1_relat_1(B_16), A_15) | ~v4_relat_1(B_16, A_15) | ~v1_relat_1(B_16))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.09/1.59  tff(c_20, plain, (![A_19]: (k2_xboole_0(k1_relat_1(A_19), k2_relat_1(A_19))=k3_relat_1(A_19) | ~v1_relat_1(A_19))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.09/1.59  tff(c_150, plain, (![A_55, C_56, B_57]: (r1_tarski(k2_xboole_0(A_55, C_56), B_57) | ~r1_tarski(C_56, B_57) | ~r1_tarski(A_55, B_57))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.09/1.59  tff(c_820, plain, (![A_121, B_122]: (r1_tarski(k3_relat_1(A_121), B_122) | ~r1_tarski(k2_relat_1(A_121), B_122) | ~r1_tarski(k1_relat_1(A_121), B_122) | ~v1_relat_1(A_121))), inference(superposition, [status(thm), theory('equality')], [c_20, c_150])).
% 3.09/1.59  tff(c_28, plain, (~r1_tarski(k3_relat_1('#skF_3'), k2_xboole_0('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.09/1.59  tff(c_201, plain, (~r1_tarski(k3_relat_1('#skF_3'), '#skF_1')), inference(resolution, [status(thm)], [c_168, c_28])).
% 3.09/1.59  tff(c_846, plain, (~r1_tarski(k2_relat_1('#skF_3'), '#skF_1') | ~r1_tarski(k1_relat_1('#skF_3'), '#skF_1') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_820, c_201])).
% 3.09/1.59  tff(c_864, plain, (~r1_tarski(k2_relat_1('#skF_3'), '#skF_1') | ~r1_tarski(k1_relat_1('#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_71, c_846])).
% 3.09/1.59  tff(c_868, plain, (~r1_tarski(k1_relat_1('#skF_3'), '#skF_1')), inference(splitLeft, [status(thm)], [c_864])).
% 3.09/1.59  tff(c_871, plain, (~v4_relat_1('#skF_3', '#skF_1') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_14, c_868])).
% 3.09/1.59  tff(c_875, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_71, c_111, c_871])).
% 3.09/1.59  tff(c_877, plain, (r1_tarski(k1_relat_1('#skF_3'), '#skF_1')), inference(splitRight, [status(thm)], [c_864])).
% 3.09/1.59  tff(c_149, plain, (![A_52, B_54, C_53]: (r1_tarski(A_52, k2_xboole_0(B_54, C_53)) | ~r1_tarski(A_52, B_54))), inference(resolution, [status(thm)], [c_123, c_4])).
% 3.09/1.59  tff(c_849, plain, (~r1_tarski(k2_relat_1('#skF_3'), k2_xboole_0('#skF_1', '#skF_2')) | ~r1_tarski(k1_relat_1('#skF_3'), k2_xboole_0('#skF_1', '#skF_2')) | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_820, c_28])).
% 3.09/1.59  tff(c_867, plain, (~r1_tarski(k2_relat_1('#skF_3'), k2_xboole_0('#skF_1', '#skF_2')) | ~r1_tarski(k1_relat_1('#skF_3'), k2_xboole_0('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_71, c_849])).
% 3.09/1.59  tff(c_884, plain, (~r1_tarski(k1_relat_1('#skF_3'), k2_xboole_0('#skF_1', '#skF_2'))), inference(splitLeft, [status(thm)], [c_867])).
% 3.09/1.59  tff(c_1064, plain, (~r1_tarski(k1_relat_1('#skF_3'), '#skF_1')), inference(resolution, [status(thm)], [c_149, c_884])).
% 3.09/1.59  tff(c_1072, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_877, c_1064])).
% 3.09/1.59  tff(c_1073, plain, (~r1_tarski(k2_relat_1('#skF_3'), k2_xboole_0('#skF_1', '#skF_2'))), inference(splitRight, [status(thm)], [c_867])).
% 3.09/1.59  tff(c_1187, plain, (~r1_tarski(k2_relat_1('#skF_3'), '#skF_2')), inference(resolution, [status(thm)], [c_193, c_1073])).
% 3.09/1.59  tff(c_1194, plain, (~v5_relat_1('#skF_3', '#skF_2') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_18, c_1187])).
% 3.09/1.59  tff(c_1198, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_71, c_105, c_1194])).
% 3.09/1.59  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.09/1.59  
% 3.09/1.59  Inference rules
% 3.09/1.59  ----------------------
% 3.09/1.59  #Ref     : 0
% 3.09/1.59  #Sup     : 310
% 3.09/1.59  #Fact    : 0
% 3.09/1.59  #Define  : 0
% 3.09/1.59  #Split   : 2
% 3.09/1.59  #Chain   : 0
% 3.09/1.59  #Close   : 0
% 3.09/1.59  
% 3.09/1.59  Ordering : KBO
% 3.09/1.59  
% 3.09/1.59  Simplification rules
% 3.09/1.59  ----------------------
% 3.09/1.59  #Subsume      : 55
% 3.09/1.59  #Demod        : 34
% 3.09/1.59  #Tautology    : 21
% 3.09/1.59  #SimpNegUnit  : 0
% 3.09/1.59  #BackRed      : 0
% 3.09/1.59  
% 3.09/1.59  #Partial instantiations: 0
% 3.09/1.59  #Strategies tried      : 1
% 3.09/1.59  
% 3.09/1.59  Timing (in seconds)
% 3.09/1.59  ----------------------
% 3.09/1.59  Preprocessing        : 0.25
% 3.09/1.59  Parsing              : 0.14
% 3.09/1.59  CNF conversion       : 0.02
% 3.09/1.59  Main loop            : 0.49
% 3.09/1.59  Inferencing          : 0.15
% 3.09/1.59  Reduction            : 0.16
% 3.09/1.59  Demodulation         : 0.12
% 3.09/1.59  BG Simplification    : 0.02
% 3.09/1.59  Subsumption          : 0.12
% 3.09/1.59  Abstraction          : 0.02
% 3.09/1.59  MUC search           : 0.00
% 3.09/1.60  Cooper               : 0.00
% 3.09/1.60  Total                : 0.77
% 3.09/1.60  Index Insertion      : 0.00
% 3.09/1.60  Index Deletion       : 0.00
% 3.09/1.60  Index Matching       : 0.00
% 3.09/1.60  BG Taut test         : 0.00
%------------------------------------------------------------------------------
