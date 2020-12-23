%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:07:05 EST 2020

% Result     : Theorem 3.08s
% Output     : CNFRefutation 3.08s
% Verified   : 
% Statistics : Number of formulae       :   60 (  99 expanded)
%              Number of leaves         :   29 (  45 expanded)
%              Depth                    :    8
%              Number of atoms          :   85 ( 160 expanded)
%              Number of equality atoms :    5 (   7 expanded)
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

tff(f_70,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_81,negated_conjecture,(
    ~ ! [A,B,C] :
        ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
       => r1_tarski(k3_relat_1(C),k2_xboole_0(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_relset_1)).

tff(f_52,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_76,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_64,axiom,(
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

tff(f_58,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_33,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_xboole_0(A,B),C)
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).

tff(f_68,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k3_relat_1(A) = k2_xboole_0(k1_relat_1(A),k2_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_relat_1)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(C,B) )
     => r1_tarski(k2_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_xboole_1)).

tff(c_24,plain,(
    ! [A_22,B_23] : v1_relat_1(k2_zfmisc_1(A_22,B_23)) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_32,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_49,plain,(
    ! [B_36,A_37] :
      ( v1_relat_1(B_36)
      | ~ m1_subset_1(B_36,k1_zfmisc_1(A_37))
      | ~ v1_relat_1(A_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_52,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_32,c_49])).

tff(c_55,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_52])).

tff(c_215,plain,(
    ! [C_64,B_65,A_66] :
      ( v5_relat_1(C_64,B_65)
      | ~ m1_subset_1(C_64,k1_zfmisc_1(k2_zfmisc_1(A_66,B_65))) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_219,plain,(
    v5_relat_1('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_32,c_215])).

tff(c_20,plain,(
    ! [B_20,A_19] :
      ( r1_tarski(k2_relat_1(B_20),A_19)
      | ~ v5_relat_1(B_20,A_19)
      | ~ v1_relat_1(B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_2,plain,(
    ! [A_1,C_3,B_2] :
      ( r1_tarski(A_1,k2_xboole_0(C_3,B_2))
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_123,plain,(
    ! [C_50,A_51,B_52] :
      ( v4_relat_1(C_50,A_51)
      | ~ m1_subset_1(C_50,k1_zfmisc_1(k2_zfmisc_1(A_51,B_52))) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_127,plain,(
    v4_relat_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_123])).

tff(c_118,plain,(
    ! [B_48,A_49] :
      ( r1_tarski(k1_relat_1(B_48),A_49)
      | ~ v4_relat_1(B_48,A_49)
      | ~ v1_relat_1(B_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_6,plain,(
    ! [A_7,B_8] :
      ( k2_xboole_0(A_7,B_8) = B_8
      | ~ r1_tarski(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_370,plain,(
    ! [B_83,A_84] :
      ( k2_xboole_0(k1_relat_1(B_83),A_84) = A_84
      | ~ v4_relat_1(B_83,A_84)
      | ~ v1_relat_1(B_83) ) ),
    inference(resolution,[status(thm)],[c_118,c_6])).

tff(c_8,plain,(
    ! [A_9,B_10] : r1_tarski(A_9,k2_xboole_0(A_9,B_10)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_56,plain,(
    ! [A_38,C_39,B_40] :
      ( r1_tarski(A_38,C_39)
      | ~ r1_tarski(k2_xboole_0(A_38,B_40),C_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_66,plain,(
    ! [A_38,B_40,B_10] : r1_tarski(A_38,k2_xboole_0(k2_xboole_0(A_38,B_40),B_10)) ),
    inference(resolution,[status(thm)],[c_8,c_56])).

tff(c_400,plain,(
    ! [B_83,A_84,B_10] :
      ( r1_tarski(k1_relat_1(B_83),k2_xboole_0(A_84,B_10))
      | ~ v4_relat_1(B_83,A_84)
      | ~ v1_relat_1(B_83) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_370,c_66])).

tff(c_22,plain,(
    ! [A_21] :
      ( k2_xboole_0(k1_relat_1(A_21),k2_relat_1(A_21)) = k3_relat_1(A_21)
      | ~ v1_relat_1(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_220,plain,(
    ! [A_67,C_68,B_69] :
      ( r1_tarski(k2_xboole_0(A_67,C_68),B_69)
      | ~ r1_tarski(C_68,B_69)
      | ~ r1_tarski(A_67,B_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_1266,plain,(
    ! [A_144,B_145] :
      ( r1_tarski(k3_relat_1(A_144),B_145)
      | ~ r1_tarski(k2_relat_1(A_144),B_145)
      | ~ r1_tarski(k1_relat_1(A_144),B_145)
      | ~ v1_relat_1(A_144) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_220])).

tff(c_30,plain,(
    ~ r1_tarski(k3_relat_1('#skF_3'),k2_xboole_0('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_1278,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_3'),k2_xboole_0('#skF_1','#skF_2'))
    | ~ r1_tarski(k1_relat_1('#skF_3'),k2_xboole_0('#skF_1','#skF_2'))
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_1266,c_30])).

tff(c_1286,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_3'),k2_xboole_0('#skF_1','#skF_2'))
    | ~ r1_tarski(k1_relat_1('#skF_3'),k2_xboole_0('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_55,c_1278])).

tff(c_1294,plain,(
    ~ r1_tarski(k1_relat_1('#skF_3'),k2_xboole_0('#skF_1','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_1286])).

tff(c_1297,plain,
    ( ~ v4_relat_1('#skF_3','#skF_1')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_400,c_1294])).

tff(c_1307,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_55,c_127,c_1297])).

tff(c_1308,plain,(
    ~ r1_tarski(k2_relat_1('#skF_3'),k2_xboole_0('#skF_1','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_1286])).

tff(c_1325,plain,(
    ~ r1_tarski(k2_relat_1('#skF_3'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_2,c_1308])).

tff(c_1328,plain,
    ( ~ v5_relat_1('#skF_3','#skF_2')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_20,c_1325])).

tff(c_1332,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_55,c_219,c_1328])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:33:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.08/1.46  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.08/1.47  
% 3.08/1.47  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.08/1.47  %$ v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k2_zfmisc_1 > k2_xboole_0 > #nlpp > k3_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 3.08/1.47  
% 3.08/1.47  %Foreground sorts:
% 3.08/1.47  
% 3.08/1.47  
% 3.08/1.47  %Background operators:
% 3.08/1.47  
% 3.08/1.47  
% 3.08/1.47  %Foreground operators:
% 3.08/1.47  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.08/1.47  tff(k3_relat_1, type, k3_relat_1: $i > $i).
% 3.08/1.47  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.08/1.47  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.08/1.47  tff('#skF_2', type, '#skF_2': $i).
% 3.08/1.47  tff('#skF_3', type, '#skF_3': $i).
% 3.08/1.47  tff('#skF_1', type, '#skF_1': $i).
% 3.08/1.47  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.08/1.47  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.08/1.47  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.08/1.47  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.08/1.47  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.08/1.47  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.08/1.47  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.08/1.47  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.08/1.47  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.08/1.47  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.08/1.47  
% 3.08/1.48  tff(f_70, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 3.08/1.48  tff(f_81, negated_conjecture, ~(![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => r1_tarski(k3_relat_1(C), k2_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t19_relset_1)).
% 3.08/1.48  tff(f_52, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 3.08/1.48  tff(f_76, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.08/1.48  tff(f_64, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 3.08/1.48  tff(f_29, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(A, k2_xboole_0(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_xboole_1)).
% 3.08/1.48  tff(f_58, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d18_relat_1)).
% 3.08/1.48  tff(f_37, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 3.08/1.48  tff(f_39, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 3.08/1.48  tff(f_33, axiom, (![A, B, C]: (r1_tarski(k2_xboole_0(A, B), C) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_xboole_1)).
% 3.08/1.48  tff(f_68, axiom, (![A]: (v1_relat_1(A) => (k3_relat_1(A) = k2_xboole_0(k1_relat_1(A), k2_relat_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d6_relat_1)).
% 3.08/1.48  tff(f_45, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(C, B)) => r1_tarski(k2_xboole_0(A, C), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_xboole_1)).
% 3.08/1.48  tff(c_24, plain, (![A_22, B_23]: (v1_relat_1(k2_zfmisc_1(A_22, B_23)))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.08/1.48  tff(c_32, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.08/1.48  tff(c_49, plain, (![B_36, A_37]: (v1_relat_1(B_36) | ~m1_subset_1(B_36, k1_zfmisc_1(A_37)) | ~v1_relat_1(A_37))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.08/1.48  tff(c_52, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_32, c_49])).
% 3.08/1.48  tff(c_55, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_24, c_52])).
% 3.08/1.48  tff(c_215, plain, (![C_64, B_65, A_66]: (v5_relat_1(C_64, B_65) | ~m1_subset_1(C_64, k1_zfmisc_1(k2_zfmisc_1(A_66, B_65))))), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.08/1.48  tff(c_219, plain, (v5_relat_1('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_32, c_215])).
% 3.08/1.48  tff(c_20, plain, (![B_20, A_19]: (r1_tarski(k2_relat_1(B_20), A_19) | ~v5_relat_1(B_20, A_19) | ~v1_relat_1(B_20))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.08/1.48  tff(c_2, plain, (![A_1, C_3, B_2]: (r1_tarski(A_1, k2_xboole_0(C_3, B_2)) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.08/1.48  tff(c_123, plain, (![C_50, A_51, B_52]: (v4_relat_1(C_50, A_51) | ~m1_subset_1(C_50, k1_zfmisc_1(k2_zfmisc_1(A_51, B_52))))), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.08/1.48  tff(c_127, plain, (v4_relat_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_32, c_123])).
% 3.08/1.48  tff(c_118, plain, (![B_48, A_49]: (r1_tarski(k1_relat_1(B_48), A_49) | ~v4_relat_1(B_48, A_49) | ~v1_relat_1(B_48))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.08/1.48  tff(c_6, plain, (![A_7, B_8]: (k2_xboole_0(A_7, B_8)=B_8 | ~r1_tarski(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.08/1.48  tff(c_370, plain, (![B_83, A_84]: (k2_xboole_0(k1_relat_1(B_83), A_84)=A_84 | ~v4_relat_1(B_83, A_84) | ~v1_relat_1(B_83))), inference(resolution, [status(thm)], [c_118, c_6])).
% 3.08/1.48  tff(c_8, plain, (![A_9, B_10]: (r1_tarski(A_9, k2_xboole_0(A_9, B_10)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.08/1.48  tff(c_56, plain, (![A_38, C_39, B_40]: (r1_tarski(A_38, C_39) | ~r1_tarski(k2_xboole_0(A_38, B_40), C_39))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.08/1.48  tff(c_66, plain, (![A_38, B_40, B_10]: (r1_tarski(A_38, k2_xboole_0(k2_xboole_0(A_38, B_40), B_10)))), inference(resolution, [status(thm)], [c_8, c_56])).
% 3.08/1.48  tff(c_400, plain, (![B_83, A_84, B_10]: (r1_tarski(k1_relat_1(B_83), k2_xboole_0(A_84, B_10)) | ~v4_relat_1(B_83, A_84) | ~v1_relat_1(B_83))), inference(superposition, [status(thm), theory('equality')], [c_370, c_66])).
% 3.08/1.48  tff(c_22, plain, (![A_21]: (k2_xboole_0(k1_relat_1(A_21), k2_relat_1(A_21))=k3_relat_1(A_21) | ~v1_relat_1(A_21))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.08/1.48  tff(c_220, plain, (![A_67, C_68, B_69]: (r1_tarski(k2_xboole_0(A_67, C_68), B_69) | ~r1_tarski(C_68, B_69) | ~r1_tarski(A_67, B_69))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.08/1.48  tff(c_1266, plain, (![A_144, B_145]: (r1_tarski(k3_relat_1(A_144), B_145) | ~r1_tarski(k2_relat_1(A_144), B_145) | ~r1_tarski(k1_relat_1(A_144), B_145) | ~v1_relat_1(A_144))), inference(superposition, [status(thm), theory('equality')], [c_22, c_220])).
% 3.08/1.48  tff(c_30, plain, (~r1_tarski(k3_relat_1('#skF_3'), k2_xboole_0('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.08/1.48  tff(c_1278, plain, (~r1_tarski(k2_relat_1('#skF_3'), k2_xboole_0('#skF_1', '#skF_2')) | ~r1_tarski(k1_relat_1('#skF_3'), k2_xboole_0('#skF_1', '#skF_2')) | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_1266, c_30])).
% 3.08/1.48  tff(c_1286, plain, (~r1_tarski(k2_relat_1('#skF_3'), k2_xboole_0('#skF_1', '#skF_2')) | ~r1_tarski(k1_relat_1('#skF_3'), k2_xboole_0('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_55, c_1278])).
% 3.08/1.48  tff(c_1294, plain, (~r1_tarski(k1_relat_1('#skF_3'), k2_xboole_0('#skF_1', '#skF_2'))), inference(splitLeft, [status(thm)], [c_1286])).
% 3.08/1.48  tff(c_1297, plain, (~v4_relat_1('#skF_3', '#skF_1') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_400, c_1294])).
% 3.08/1.48  tff(c_1307, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_55, c_127, c_1297])).
% 3.08/1.48  tff(c_1308, plain, (~r1_tarski(k2_relat_1('#skF_3'), k2_xboole_0('#skF_1', '#skF_2'))), inference(splitRight, [status(thm)], [c_1286])).
% 3.08/1.48  tff(c_1325, plain, (~r1_tarski(k2_relat_1('#skF_3'), '#skF_2')), inference(resolution, [status(thm)], [c_2, c_1308])).
% 3.08/1.48  tff(c_1328, plain, (~v5_relat_1('#skF_3', '#skF_2') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_20, c_1325])).
% 3.08/1.48  tff(c_1332, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_55, c_219, c_1328])).
% 3.08/1.48  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.08/1.48  
% 3.08/1.48  Inference rules
% 3.08/1.48  ----------------------
% 3.08/1.48  #Ref     : 0
% 3.08/1.48  #Sup     : 332
% 3.08/1.48  #Fact    : 0
% 3.08/1.48  #Define  : 0
% 3.08/1.48  #Split   : 2
% 3.08/1.48  #Chain   : 0
% 3.08/1.48  #Close   : 0
% 3.08/1.48  
% 3.08/1.48  Ordering : KBO
% 3.08/1.48  
% 3.08/1.48  Simplification rules
% 3.08/1.48  ----------------------
% 3.08/1.48  #Subsume      : 62
% 3.08/1.48  #Demod        : 38
% 3.08/1.48  #Tautology    : 77
% 3.08/1.48  #SimpNegUnit  : 0
% 3.08/1.48  #BackRed      : 0
% 3.08/1.48  
% 3.08/1.48  #Partial instantiations: 0
% 3.08/1.48  #Strategies tried      : 1
% 3.08/1.48  
% 3.08/1.48  Timing (in seconds)
% 3.08/1.48  ----------------------
% 3.25/1.49  Preprocessing        : 0.27
% 3.25/1.49  Parsing              : 0.15
% 3.25/1.49  CNF conversion       : 0.02
% 3.25/1.49  Main loop            : 0.44
% 3.25/1.49  Inferencing          : 0.18
% 3.25/1.49  Reduction            : 0.12
% 3.25/1.49  Demodulation         : 0.09
% 3.25/1.49  BG Simplification    : 0.02
% 3.25/1.49  Subsumption          : 0.08
% 3.25/1.49  Abstraction          : 0.02
% 3.25/1.49  MUC search           : 0.00
% 3.25/1.49  Cooper               : 0.00
% 3.25/1.49  Total                : 0.74
% 3.25/1.49  Index Insertion      : 0.00
% 3.25/1.49  Index Deletion       : 0.00
% 3.25/1.49  Index Matching       : 0.00
% 3.25/1.49  BG Taut test         : 0.00
%------------------------------------------------------------------------------
