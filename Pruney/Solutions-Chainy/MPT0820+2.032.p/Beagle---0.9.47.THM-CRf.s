%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:07:04 EST 2020

% Result     : Theorem 3.13s
% Output     : CNFRefutation 3.26s
% Verified   : 
% Statistics : Number of formulae       :   66 ( 151 expanded)
%              Number of leaves         :   28 (  62 expanded)
%              Depth                    :    8
%              Number of atoms          :   91 ( 260 expanded)
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_77,negated_conjecture,(
    ~ ! [A,B,C] :
        ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
       => r1_tarski(k3_relat_1(C),k2_xboole_0(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_relset_1)).

tff(f_48,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_72,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_60,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_35,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_33,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_54,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_64,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k3_relat_1(A) = k2_xboole_0(k1_relat_1(A),k2_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_relat_1)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(C,B) )
     => r1_tarski(k2_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_xboole_1)).

tff(c_22,plain,(
    ! [A_19,B_20] : v1_relat_1(k2_zfmisc_1(A_19,B_20)) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_30,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_72,plain,(
    ! [B_30,A_31] :
      ( v1_relat_1(B_30)
      | ~ m1_subset_1(B_30,k1_zfmisc_1(A_31))
      | ~ v1_relat_1(A_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_75,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_30,c_72])).

tff(c_78,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_75])).

tff(c_134,plain,(
    ! [C_42,B_43,A_44] :
      ( v5_relat_1(C_42,B_43)
      | ~ m1_subset_1(C_42,k1_zfmisc_1(k2_zfmisc_1(A_44,B_43))) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_138,plain,(
    v5_relat_1('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_30,c_134])).

tff(c_18,plain,(
    ! [B_17,A_16] :
      ( r1_tarski(k2_relat_1(B_17),A_16)
      | ~ v5_relat_1(B_17,A_16)
      | ~ v1_relat_1(B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_33,plain,(
    ! [B_28,A_29] : k2_xboole_0(B_28,A_29) = k2_xboole_0(A_29,B_28) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_6,plain,(
    ! [A_6,B_7] : r1_tarski(A_6,k2_xboole_0(A_6,B_7)) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_51,plain,(
    ! [B_28,A_29] : r1_tarski(B_28,k2_xboole_0(A_29,B_28)) ),
    inference(superposition,[status(thm),theory(equality)],[c_33,c_6])).

tff(c_178,plain,(
    ! [A_55,C_56,B_57] :
      ( r1_tarski(A_55,C_56)
      | ~ r1_tarski(B_57,C_56)
      | ~ r1_tarski(A_55,B_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_189,plain,(
    ! [A_55,A_29,B_28] :
      ( r1_tarski(A_55,k2_xboole_0(A_29,B_28))
      | ~ r1_tarski(A_55,B_28) ) ),
    inference(resolution,[status(thm)],[c_51,c_178])).

tff(c_148,plain,(
    ! [C_47,A_48,B_49] :
      ( v4_relat_1(C_47,A_48)
      | ~ m1_subset_1(C_47,k1_zfmisc_1(k2_zfmisc_1(A_48,B_49))) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_152,plain,(
    v4_relat_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_30,c_148])).

tff(c_14,plain,(
    ! [B_15,A_14] :
      ( r1_tarski(k1_relat_1(B_15),A_14)
      | ~ v4_relat_1(B_15,A_14)
      | ~ v1_relat_1(B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_20,plain,(
    ! [A_18] :
      ( k2_xboole_0(k1_relat_1(A_18),k2_relat_1(A_18)) = k3_relat_1(A_18)
      | ~ v1_relat_1(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_287,plain,(
    ! [A_72,C_73,B_74] :
      ( r1_tarski(k2_xboole_0(A_72,C_73),B_74)
      | ~ r1_tarski(C_73,B_74)
      | ~ r1_tarski(A_72,B_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_820,plain,(
    ! [A_126,B_127] :
      ( r1_tarski(k3_relat_1(A_126),B_127)
      | ~ r1_tarski(k2_relat_1(A_126),B_127)
      | ~ r1_tarski(k1_relat_1(A_126),B_127)
      | ~ v1_relat_1(A_126) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_287])).

tff(c_191,plain,(
    ! [A_58,A_59,B_60] :
      ( r1_tarski(A_58,k2_xboole_0(A_59,B_60))
      | ~ r1_tarski(A_58,A_59) ) ),
    inference(resolution,[status(thm)],[c_6,c_178])).

tff(c_28,plain,(
    ~ r1_tarski(k3_relat_1('#skF_3'),k2_xboole_0('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_217,plain,(
    ~ r1_tarski(k3_relat_1('#skF_3'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_191,c_28])).

tff(c_834,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_3'),'#skF_1')
    | ~ r1_tarski(k1_relat_1('#skF_3'),'#skF_1')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_820,c_217])).

tff(c_848,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_3'),'#skF_1')
    | ~ r1_tarski(k1_relat_1('#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_834])).

tff(c_853,plain,(
    ~ r1_tarski(k1_relat_1('#skF_3'),'#skF_1') ),
    inference(splitLeft,[status(thm)],[c_848])).

tff(c_856,plain,
    ( ~ v4_relat_1('#skF_3','#skF_1')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_14,c_853])).

tff(c_860,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_152,c_856])).

tff(c_862,plain,(
    r1_tarski(k1_relat_1('#skF_3'),'#skF_1') ),
    inference(splitRight,[status(thm)],[c_848])).

tff(c_190,plain,(
    ! [A_55,A_6,B_7] :
      ( r1_tarski(A_55,k2_xboole_0(A_6,B_7))
      | ~ r1_tarski(A_55,A_6) ) ),
    inference(resolution,[status(thm)],[c_6,c_178])).

tff(c_839,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_3'),k2_xboole_0('#skF_1','#skF_2'))
    | ~ r1_tarski(k1_relat_1('#skF_3'),k2_xboole_0('#skF_1','#skF_2'))
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_820,c_28])).

tff(c_852,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_3'),k2_xboole_0('#skF_1','#skF_2'))
    | ~ r1_tarski(k1_relat_1('#skF_3'),k2_xboole_0('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_839])).

tff(c_869,plain,(
    ~ r1_tarski(k1_relat_1('#skF_3'),k2_xboole_0('#skF_1','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_852])).

tff(c_890,plain,(
    ~ r1_tarski(k1_relat_1('#skF_3'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_190,c_869])).

tff(c_898,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_862,c_890])).

tff(c_899,plain,(
    ~ r1_tarski(k2_relat_1('#skF_3'),k2_xboole_0('#skF_1','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_852])).

tff(c_984,plain,(
    ~ r1_tarski(k2_relat_1('#skF_3'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_189,c_899])).

tff(c_988,plain,
    ( ~ v5_relat_1('#skF_3','#skF_2')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_18,c_984])).

tff(c_992,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_138,c_988])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.35  % Computer   : n024.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 18:05:51 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.13/1.54  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.13/1.55  
% 3.13/1.55  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.13/1.55  %$ v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k2_zfmisc_1 > k2_xboole_0 > #nlpp > k3_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 3.13/1.55  
% 3.13/1.55  %Foreground sorts:
% 3.13/1.55  
% 3.13/1.55  
% 3.13/1.55  %Background operators:
% 3.13/1.55  
% 3.13/1.55  
% 3.13/1.55  %Foreground operators:
% 3.13/1.55  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.13/1.55  tff(k3_relat_1, type, k3_relat_1: $i > $i).
% 3.13/1.55  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.13/1.55  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.13/1.55  tff('#skF_2', type, '#skF_2': $i).
% 3.13/1.55  tff('#skF_3', type, '#skF_3': $i).
% 3.13/1.55  tff('#skF_1', type, '#skF_1': $i).
% 3.13/1.55  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.13/1.55  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.13/1.55  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.13/1.55  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.13/1.55  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.13/1.55  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.13/1.55  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.13/1.55  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.13/1.55  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.13/1.55  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.13/1.55  
% 3.26/1.56  tff(f_66, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 3.26/1.56  tff(f_77, negated_conjecture, ~(![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => r1_tarski(k3_relat_1(C), k2_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t19_relset_1)).
% 3.26/1.56  tff(f_48, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 3.26/1.56  tff(f_72, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.26/1.56  tff(f_60, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 3.26/1.56  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 3.26/1.56  tff(f_35, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 3.26/1.56  tff(f_33, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 3.26/1.56  tff(f_54, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d18_relat_1)).
% 3.26/1.56  tff(f_64, axiom, (![A]: (v1_relat_1(A) => (k3_relat_1(A) = k2_xboole_0(k1_relat_1(A), k2_relat_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d6_relat_1)).
% 3.26/1.56  tff(f_41, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(C, B)) => r1_tarski(k2_xboole_0(A, C), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_xboole_1)).
% 3.26/1.56  tff(c_22, plain, (![A_19, B_20]: (v1_relat_1(k2_zfmisc_1(A_19, B_20)))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.26/1.56  tff(c_30, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.26/1.56  tff(c_72, plain, (![B_30, A_31]: (v1_relat_1(B_30) | ~m1_subset_1(B_30, k1_zfmisc_1(A_31)) | ~v1_relat_1(A_31))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.26/1.56  tff(c_75, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_30, c_72])).
% 3.26/1.56  tff(c_78, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_22, c_75])).
% 3.26/1.56  tff(c_134, plain, (![C_42, B_43, A_44]: (v5_relat_1(C_42, B_43) | ~m1_subset_1(C_42, k1_zfmisc_1(k2_zfmisc_1(A_44, B_43))))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.26/1.56  tff(c_138, plain, (v5_relat_1('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_30, c_134])).
% 3.26/1.56  tff(c_18, plain, (![B_17, A_16]: (r1_tarski(k2_relat_1(B_17), A_16) | ~v5_relat_1(B_17, A_16) | ~v1_relat_1(B_17))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.26/1.56  tff(c_33, plain, (![B_28, A_29]: (k2_xboole_0(B_28, A_29)=k2_xboole_0(A_29, B_28))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.26/1.56  tff(c_6, plain, (![A_6, B_7]: (r1_tarski(A_6, k2_xboole_0(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.26/1.56  tff(c_51, plain, (![B_28, A_29]: (r1_tarski(B_28, k2_xboole_0(A_29, B_28)))), inference(superposition, [status(thm), theory('equality')], [c_33, c_6])).
% 3.26/1.56  tff(c_178, plain, (![A_55, C_56, B_57]: (r1_tarski(A_55, C_56) | ~r1_tarski(B_57, C_56) | ~r1_tarski(A_55, B_57))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.26/1.56  tff(c_189, plain, (![A_55, A_29, B_28]: (r1_tarski(A_55, k2_xboole_0(A_29, B_28)) | ~r1_tarski(A_55, B_28))), inference(resolution, [status(thm)], [c_51, c_178])).
% 3.26/1.56  tff(c_148, plain, (![C_47, A_48, B_49]: (v4_relat_1(C_47, A_48) | ~m1_subset_1(C_47, k1_zfmisc_1(k2_zfmisc_1(A_48, B_49))))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.26/1.56  tff(c_152, plain, (v4_relat_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_30, c_148])).
% 3.26/1.56  tff(c_14, plain, (![B_15, A_14]: (r1_tarski(k1_relat_1(B_15), A_14) | ~v4_relat_1(B_15, A_14) | ~v1_relat_1(B_15))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.26/1.56  tff(c_20, plain, (![A_18]: (k2_xboole_0(k1_relat_1(A_18), k2_relat_1(A_18))=k3_relat_1(A_18) | ~v1_relat_1(A_18))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.26/1.56  tff(c_287, plain, (![A_72, C_73, B_74]: (r1_tarski(k2_xboole_0(A_72, C_73), B_74) | ~r1_tarski(C_73, B_74) | ~r1_tarski(A_72, B_74))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.26/1.56  tff(c_820, plain, (![A_126, B_127]: (r1_tarski(k3_relat_1(A_126), B_127) | ~r1_tarski(k2_relat_1(A_126), B_127) | ~r1_tarski(k1_relat_1(A_126), B_127) | ~v1_relat_1(A_126))), inference(superposition, [status(thm), theory('equality')], [c_20, c_287])).
% 3.26/1.56  tff(c_191, plain, (![A_58, A_59, B_60]: (r1_tarski(A_58, k2_xboole_0(A_59, B_60)) | ~r1_tarski(A_58, A_59))), inference(resolution, [status(thm)], [c_6, c_178])).
% 3.26/1.56  tff(c_28, plain, (~r1_tarski(k3_relat_1('#skF_3'), k2_xboole_0('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.26/1.56  tff(c_217, plain, (~r1_tarski(k3_relat_1('#skF_3'), '#skF_1')), inference(resolution, [status(thm)], [c_191, c_28])).
% 3.26/1.56  tff(c_834, plain, (~r1_tarski(k2_relat_1('#skF_3'), '#skF_1') | ~r1_tarski(k1_relat_1('#skF_3'), '#skF_1') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_820, c_217])).
% 3.26/1.56  tff(c_848, plain, (~r1_tarski(k2_relat_1('#skF_3'), '#skF_1') | ~r1_tarski(k1_relat_1('#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_834])).
% 3.26/1.56  tff(c_853, plain, (~r1_tarski(k1_relat_1('#skF_3'), '#skF_1')), inference(splitLeft, [status(thm)], [c_848])).
% 3.26/1.56  tff(c_856, plain, (~v4_relat_1('#skF_3', '#skF_1') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_14, c_853])).
% 3.26/1.56  tff(c_860, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_78, c_152, c_856])).
% 3.26/1.56  tff(c_862, plain, (r1_tarski(k1_relat_1('#skF_3'), '#skF_1')), inference(splitRight, [status(thm)], [c_848])).
% 3.26/1.56  tff(c_190, plain, (![A_55, A_6, B_7]: (r1_tarski(A_55, k2_xboole_0(A_6, B_7)) | ~r1_tarski(A_55, A_6))), inference(resolution, [status(thm)], [c_6, c_178])).
% 3.26/1.56  tff(c_839, plain, (~r1_tarski(k2_relat_1('#skF_3'), k2_xboole_0('#skF_1', '#skF_2')) | ~r1_tarski(k1_relat_1('#skF_3'), k2_xboole_0('#skF_1', '#skF_2')) | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_820, c_28])).
% 3.26/1.56  tff(c_852, plain, (~r1_tarski(k2_relat_1('#skF_3'), k2_xboole_0('#skF_1', '#skF_2')) | ~r1_tarski(k1_relat_1('#skF_3'), k2_xboole_0('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_839])).
% 3.26/1.56  tff(c_869, plain, (~r1_tarski(k1_relat_1('#skF_3'), k2_xboole_0('#skF_1', '#skF_2'))), inference(splitLeft, [status(thm)], [c_852])).
% 3.26/1.56  tff(c_890, plain, (~r1_tarski(k1_relat_1('#skF_3'), '#skF_1')), inference(resolution, [status(thm)], [c_190, c_869])).
% 3.26/1.56  tff(c_898, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_862, c_890])).
% 3.26/1.56  tff(c_899, plain, (~r1_tarski(k2_relat_1('#skF_3'), k2_xboole_0('#skF_1', '#skF_2'))), inference(splitRight, [status(thm)], [c_852])).
% 3.26/1.56  tff(c_984, plain, (~r1_tarski(k2_relat_1('#skF_3'), '#skF_2')), inference(resolution, [status(thm)], [c_189, c_899])).
% 3.26/1.56  tff(c_988, plain, (~v5_relat_1('#skF_3', '#skF_2') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_18, c_984])).
% 3.26/1.56  tff(c_992, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_78, c_138, c_988])).
% 3.26/1.56  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.26/1.56  
% 3.26/1.56  Inference rules
% 3.26/1.56  ----------------------
% 3.26/1.56  #Ref     : 0
% 3.26/1.56  #Sup     : 234
% 3.26/1.56  #Fact    : 0
% 3.26/1.56  #Define  : 0
% 3.26/1.56  #Split   : 2
% 3.26/1.56  #Chain   : 0
% 3.26/1.56  #Close   : 0
% 3.26/1.56  
% 3.26/1.56  Ordering : KBO
% 3.26/1.56  
% 3.26/1.56  Simplification rules
% 3.26/1.56  ----------------------
% 3.26/1.56  #Subsume      : 24
% 3.26/1.56  #Demod        : 53
% 3.26/1.56  #Tautology    : 53
% 3.26/1.56  #SimpNegUnit  : 0
% 3.26/1.56  #BackRed      : 0
% 3.26/1.56  
% 3.26/1.56  #Partial instantiations: 0
% 3.26/1.56  #Strategies tried      : 1
% 3.26/1.56  
% 3.26/1.56  Timing (in seconds)
% 3.26/1.56  ----------------------
% 3.26/1.57  Preprocessing        : 0.27
% 3.26/1.57  Parsing              : 0.15
% 3.26/1.57  CNF conversion       : 0.02
% 3.26/1.57  Main loop            : 0.51
% 3.26/1.57  Inferencing          : 0.18
% 3.26/1.57  Reduction            : 0.17
% 3.26/1.57  Demodulation         : 0.14
% 3.26/1.57  BG Simplification    : 0.02
% 3.26/1.57  Subsumption          : 0.09
% 3.26/1.57  Abstraction          : 0.02
% 3.26/1.57  MUC search           : 0.00
% 3.26/1.57  Cooper               : 0.00
% 3.26/1.57  Total                : 0.81
% 3.26/1.57  Index Insertion      : 0.00
% 3.26/1.57  Index Deletion       : 0.00
% 3.26/1.57  Index Matching       : 0.00
% 3.26/1.57  BG Taut test         : 0.00
%------------------------------------------------------------------------------
