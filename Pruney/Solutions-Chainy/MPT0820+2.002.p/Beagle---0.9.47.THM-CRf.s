%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:07:00 EST 2020

% Result     : Theorem 2.40s
% Output     : CNFRefutation 2.63s
% Verified   : 
% Statistics : Number of formulae       :   61 (  94 expanded)
%              Number of leaves         :   31 (  46 expanded)
%              Depth                    :    8
%              Number of atoms          :   72 ( 134 expanded)
%              Number of equality atoms :    9 (  12 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k2_enumset1 > k1_enumset1 > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k3_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k3_relat_1,type,(
    k3_relat_1: $i > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

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

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

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

tff(f_74,negated_conjecture,(
    ~ ! [A,B,C] :
        ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
       => r1_tarski(k3_relat_1(C),k2_xboole_0(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_relset_1)).

tff(f_63,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_69,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_29,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(A,k2_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_xboole_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_37,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_43,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_59,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k3_relat_1(A) = k2_xboole_0(k1_relat_1(A),k2_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_relat_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(C,B) )
     => r1_tarski(k2_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_xboole_1)).

tff(c_32,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_157,plain,(
    ! [C_40,A_41,B_42] :
      ( v1_relat_1(C_40)
      | ~ m1_subset_1(C_40,k1_zfmisc_1(k2_zfmisc_1(A_41,B_42))) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_161,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_32,c_157])).

tff(c_211,plain,(
    ! [C_57,B_58,A_59] :
      ( v5_relat_1(C_57,B_58)
      | ~ m1_subset_1(C_57,k1_zfmisc_1(k2_zfmisc_1(A_59,B_58))) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_215,plain,(
    v5_relat_1('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_32,c_211])).

tff(c_20,plain,(
    ! [B_19,A_18] :
      ( r1_tarski(k2_relat_1(B_19),A_18)
      | ~ v5_relat_1(B_19,A_18)
      | ~ v1_relat_1(B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_2,plain,(
    ! [A_1,C_3,B_2] :
      ( r1_tarski(A_1,k2_xboole_0(C_3,B_2))
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_185,plain,(
    ! [C_48,A_49,B_50] :
      ( v4_relat_1(C_48,A_49)
      | ~ m1_subset_1(C_48,k1_zfmisc_1(k2_zfmisc_1(A_49,B_50))) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_189,plain,(
    v4_relat_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_185])).

tff(c_16,plain,(
    ! [B_17,A_16] :
      ( r1_tarski(k1_relat_1(B_17),A_16)
      | ~ v4_relat_1(B_17,A_16)
      | ~ v1_relat_1(B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_6,plain,(
    ! [B_8,A_7] : k2_tarski(B_8,A_7) = k2_tarski(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_66,plain,(
    ! [A_29,B_30] : k3_tarski(k2_tarski(A_29,B_30)) = k2_xboole_0(A_29,B_30) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_95,plain,(
    ! [B_36,A_37] : k3_tarski(k2_tarski(B_36,A_37)) = k2_xboole_0(A_37,B_36) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_66])).

tff(c_12,plain,(
    ! [A_14,B_15] : k3_tarski(k2_tarski(A_14,B_15)) = k2_xboole_0(A_14,B_15) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_118,plain,(
    ! [B_38,A_39] : k2_xboole_0(B_38,A_39) = k2_xboole_0(A_39,B_38) ),
    inference(superposition,[status(thm),theory(equality)],[c_95,c_12])).

tff(c_133,plain,(
    ! [A_1,B_38,A_39] :
      ( r1_tarski(A_1,k2_xboole_0(B_38,A_39))
      | ~ r1_tarski(A_1,B_38) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_118,c_2])).

tff(c_22,plain,(
    ! [A_20] :
      ( k2_xboole_0(k1_relat_1(A_20),k2_relat_1(A_20)) = k3_relat_1(A_20)
      | ~ v1_relat_1(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_262,plain,(
    ! [A_68,C_69,B_70] :
      ( r1_tarski(k2_xboole_0(A_68,C_69),B_70)
      | ~ r1_tarski(C_69,B_70)
      | ~ r1_tarski(A_68,B_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_312,plain,(
    ! [A_83,B_84] :
      ( r1_tarski(k3_relat_1(A_83),B_84)
      | ~ r1_tarski(k2_relat_1(A_83),B_84)
      | ~ r1_tarski(k1_relat_1(A_83),B_84)
      | ~ v1_relat_1(A_83) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_262])).

tff(c_30,plain,(
    ~ r1_tarski(k3_relat_1('#skF_3'),k2_xboole_0('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_321,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_3'),k2_xboole_0('#skF_1','#skF_2'))
    | ~ r1_tarski(k1_relat_1('#skF_3'),k2_xboole_0('#skF_1','#skF_2'))
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_312,c_30])).

tff(c_330,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_3'),k2_xboole_0('#skF_1','#skF_2'))
    | ~ r1_tarski(k1_relat_1('#skF_3'),k2_xboole_0('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_161,c_321])).

tff(c_338,plain,(
    ~ r1_tarski(k1_relat_1('#skF_3'),k2_xboole_0('#skF_1','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_330])).

tff(c_351,plain,(
    ~ r1_tarski(k1_relat_1('#skF_3'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_133,c_338])).

tff(c_355,plain,
    ( ~ v4_relat_1('#skF_3','#skF_1')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_16,c_351])).

tff(c_359,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_161,c_189,c_355])).

tff(c_360,plain,(
    ~ r1_tarski(k2_relat_1('#skF_3'),k2_xboole_0('#skF_1','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_330])).

tff(c_375,plain,(
    ~ r1_tarski(k2_relat_1('#skF_3'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_2,c_360])).

tff(c_378,plain,
    ( ~ v5_relat_1('#skF_3','#skF_2')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_20,c_375])).

tff(c_382,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_161,c_215,c_378])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.05/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.05/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.33  % Computer   : n017.cluster.edu
% 0.14/0.33  % Model      : x86_64 x86_64
% 0.14/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.33  % Memory     : 8042.1875MB
% 0.14/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 15:58:01 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.40/1.30  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.40/1.31  
% 2.40/1.31  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.40/1.31  %$ v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k2_enumset1 > k1_enumset1 > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k3_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 2.40/1.31  
% 2.40/1.31  %Foreground sorts:
% 2.40/1.31  
% 2.40/1.31  
% 2.40/1.31  %Background operators:
% 2.40/1.31  
% 2.40/1.31  
% 2.40/1.31  %Foreground operators:
% 2.40/1.31  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.40/1.31  tff(k3_relat_1, type, k3_relat_1: $i > $i).
% 2.40/1.31  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.40/1.31  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.40/1.31  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.40/1.31  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.40/1.31  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.40/1.31  tff('#skF_2', type, '#skF_2': $i).
% 2.40/1.31  tff('#skF_3', type, '#skF_3': $i).
% 2.40/1.31  tff('#skF_1', type, '#skF_1': $i).
% 2.40/1.31  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.40/1.31  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.40/1.31  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.40/1.31  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.40/1.31  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.40/1.31  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.40/1.31  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.40/1.31  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.40/1.31  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.40/1.31  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.40/1.31  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.40/1.31  
% 2.63/1.32  tff(f_74, negated_conjecture, ~(![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => r1_tarski(k3_relat_1(C), k2_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t19_relset_1)).
% 2.63/1.32  tff(f_63, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.63/1.32  tff(f_69, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.63/1.32  tff(f_55, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 2.63/1.32  tff(f_29, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(A, k2_xboole_0(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_xboole_1)).
% 2.63/1.32  tff(f_49, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d18_relat_1)).
% 2.63/1.32  tff(f_37, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 2.63/1.32  tff(f_43, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 2.63/1.32  tff(f_59, axiom, (![A]: (v1_relat_1(A) => (k3_relat_1(A) = k2_xboole_0(k1_relat_1(A), k2_relat_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d6_relat_1)).
% 2.63/1.32  tff(f_35, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(C, B)) => r1_tarski(k2_xboole_0(A, C), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_xboole_1)).
% 2.63/1.32  tff(c_32, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.63/1.32  tff(c_157, plain, (![C_40, A_41, B_42]: (v1_relat_1(C_40) | ~m1_subset_1(C_40, k1_zfmisc_1(k2_zfmisc_1(A_41, B_42))))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.63/1.32  tff(c_161, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_32, c_157])).
% 2.63/1.32  tff(c_211, plain, (![C_57, B_58, A_59]: (v5_relat_1(C_57, B_58) | ~m1_subset_1(C_57, k1_zfmisc_1(k2_zfmisc_1(A_59, B_58))))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.63/1.32  tff(c_215, plain, (v5_relat_1('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_32, c_211])).
% 2.63/1.32  tff(c_20, plain, (![B_19, A_18]: (r1_tarski(k2_relat_1(B_19), A_18) | ~v5_relat_1(B_19, A_18) | ~v1_relat_1(B_19))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.63/1.32  tff(c_2, plain, (![A_1, C_3, B_2]: (r1_tarski(A_1, k2_xboole_0(C_3, B_2)) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.63/1.32  tff(c_185, plain, (![C_48, A_49, B_50]: (v4_relat_1(C_48, A_49) | ~m1_subset_1(C_48, k1_zfmisc_1(k2_zfmisc_1(A_49, B_50))))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.63/1.32  tff(c_189, plain, (v4_relat_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_32, c_185])).
% 2.63/1.32  tff(c_16, plain, (![B_17, A_16]: (r1_tarski(k1_relat_1(B_17), A_16) | ~v4_relat_1(B_17, A_16) | ~v1_relat_1(B_17))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.63/1.32  tff(c_6, plain, (![B_8, A_7]: (k2_tarski(B_8, A_7)=k2_tarski(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.63/1.32  tff(c_66, plain, (![A_29, B_30]: (k3_tarski(k2_tarski(A_29, B_30))=k2_xboole_0(A_29, B_30))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.63/1.32  tff(c_95, plain, (![B_36, A_37]: (k3_tarski(k2_tarski(B_36, A_37))=k2_xboole_0(A_37, B_36))), inference(superposition, [status(thm), theory('equality')], [c_6, c_66])).
% 2.63/1.32  tff(c_12, plain, (![A_14, B_15]: (k3_tarski(k2_tarski(A_14, B_15))=k2_xboole_0(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.63/1.32  tff(c_118, plain, (![B_38, A_39]: (k2_xboole_0(B_38, A_39)=k2_xboole_0(A_39, B_38))), inference(superposition, [status(thm), theory('equality')], [c_95, c_12])).
% 2.63/1.32  tff(c_133, plain, (![A_1, B_38, A_39]: (r1_tarski(A_1, k2_xboole_0(B_38, A_39)) | ~r1_tarski(A_1, B_38))), inference(superposition, [status(thm), theory('equality')], [c_118, c_2])).
% 2.63/1.32  tff(c_22, plain, (![A_20]: (k2_xboole_0(k1_relat_1(A_20), k2_relat_1(A_20))=k3_relat_1(A_20) | ~v1_relat_1(A_20))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.63/1.32  tff(c_262, plain, (![A_68, C_69, B_70]: (r1_tarski(k2_xboole_0(A_68, C_69), B_70) | ~r1_tarski(C_69, B_70) | ~r1_tarski(A_68, B_70))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.63/1.32  tff(c_312, plain, (![A_83, B_84]: (r1_tarski(k3_relat_1(A_83), B_84) | ~r1_tarski(k2_relat_1(A_83), B_84) | ~r1_tarski(k1_relat_1(A_83), B_84) | ~v1_relat_1(A_83))), inference(superposition, [status(thm), theory('equality')], [c_22, c_262])).
% 2.63/1.32  tff(c_30, plain, (~r1_tarski(k3_relat_1('#skF_3'), k2_xboole_0('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.63/1.32  tff(c_321, plain, (~r1_tarski(k2_relat_1('#skF_3'), k2_xboole_0('#skF_1', '#skF_2')) | ~r1_tarski(k1_relat_1('#skF_3'), k2_xboole_0('#skF_1', '#skF_2')) | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_312, c_30])).
% 2.63/1.32  tff(c_330, plain, (~r1_tarski(k2_relat_1('#skF_3'), k2_xboole_0('#skF_1', '#skF_2')) | ~r1_tarski(k1_relat_1('#skF_3'), k2_xboole_0('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_161, c_321])).
% 2.63/1.32  tff(c_338, plain, (~r1_tarski(k1_relat_1('#skF_3'), k2_xboole_0('#skF_1', '#skF_2'))), inference(splitLeft, [status(thm)], [c_330])).
% 2.63/1.32  tff(c_351, plain, (~r1_tarski(k1_relat_1('#skF_3'), '#skF_1')), inference(resolution, [status(thm)], [c_133, c_338])).
% 2.63/1.32  tff(c_355, plain, (~v4_relat_1('#skF_3', '#skF_1') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_16, c_351])).
% 2.63/1.32  tff(c_359, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_161, c_189, c_355])).
% 2.63/1.32  tff(c_360, plain, (~r1_tarski(k2_relat_1('#skF_3'), k2_xboole_0('#skF_1', '#skF_2'))), inference(splitRight, [status(thm)], [c_330])).
% 2.63/1.32  tff(c_375, plain, (~r1_tarski(k2_relat_1('#skF_3'), '#skF_2')), inference(resolution, [status(thm)], [c_2, c_360])).
% 2.63/1.32  tff(c_378, plain, (~v5_relat_1('#skF_3', '#skF_2') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_20, c_375])).
% 2.63/1.32  tff(c_382, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_161, c_215, c_378])).
% 2.63/1.32  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.63/1.32  
% 2.63/1.32  Inference rules
% 2.63/1.32  ----------------------
% 2.63/1.32  #Ref     : 0
% 2.63/1.32  #Sup     : 80
% 2.63/1.32  #Fact    : 0
% 2.63/1.32  #Define  : 0
% 2.63/1.32  #Split   : 2
% 2.63/1.32  #Chain   : 0
% 2.63/1.32  #Close   : 0
% 2.63/1.32  
% 2.63/1.32  Ordering : KBO
% 2.63/1.32  
% 2.63/1.32  Simplification rules
% 2.63/1.32  ----------------------
% 2.63/1.32  #Subsume      : 13
% 2.63/1.32  #Demod        : 13
% 2.63/1.32  #Tautology    : 31
% 2.63/1.32  #SimpNegUnit  : 0
% 2.63/1.32  #BackRed      : 0
% 2.63/1.32  
% 2.63/1.32  #Partial instantiations: 0
% 2.63/1.32  #Strategies tried      : 1
% 2.63/1.32  
% 2.63/1.32  Timing (in seconds)
% 2.63/1.32  ----------------------
% 2.63/1.33  Preprocessing        : 0.31
% 2.63/1.33  Parsing              : 0.17
% 2.63/1.33  CNF conversion       : 0.02
% 2.63/1.33  Main loop            : 0.23
% 2.63/1.33  Inferencing          : 0.09
% 2.63/1.33  Reduction            : 0.07
% 2.63/1.33  Demodulation         : 0.05
% 2.63/1.33  BG Simplification    : 0.01
% 2.63/1.33  Subsumption          : 0.04
% 2.63/1.33  Abstraction          : 0.01
% 2.63/1.33  MUC search           : 0.00
% 2.63/1.33  Cooper               : 0.00
% 2.63/1.33  Total                : 0.58
% 2.63/1.33  Index Insertion      : 0.00
% 2.63/1.33  Index Deletion       : 0.00
% 2.63/1.33  Index Matching       : 0.00
% 2.63/1.33  BG Taut test         : 0.00
%------------------------------------------------------------------------------
