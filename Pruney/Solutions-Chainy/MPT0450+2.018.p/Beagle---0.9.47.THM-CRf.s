%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:58:38 EST 2020

% Result     : Theorem 2.00s
% Output     : CNFRefutation 2.12s
% Verified   : 
% Statistics : Number of formulae       :   56 (  91 expanded)
%              Number of leaves         :   29 (  45 expanded)
%              Depth                    :    7
%              Number of atoms          :   64 ( 126 expanded)
%              Number of equality atoms :    2 (  12 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > m1_subset_1 > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k3_relat_1 > k1_zfmisc_1 > k1_setfam_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k3_relat_1,type,(
    k3_relat_1: $i > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_81,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ! [B] :
            ( v1_relat_1(B)
           => r1_tarski(k3_relat_1(k3_xboole_0(A,B)),k3_xboole_0(k3_relat_1(A),k3_relat_1(B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_relat_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

tff(f_37,axiom,(
    ! [A,B,C] : r1_tarski(k2_xboole_0(k3_xboole_0(A,B),k3_xboole_0(A,C)),k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_xboole_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_64,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_73,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(A,B)
           => r1_tarski(k3_relat_1(A),k3_relat_1(B)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_relat_1)).

tff(f_29,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(A,C) )
     => r1_tarski(A,k3_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_xboole_1)).

tff(c_36,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_2,plain,(
    ! [A_1] : k2_xboole_0(A_1,A_1) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_120,plain,(
    ! [A_80,B_81,C_82] : r1_tarski(k2_xboole_0(k3_xboole_0(A_80,B_81),k3_xboole_0(A_80,C_82)),k2_xboole_0(B_81,C_82)) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_127,plain,(
    ! [A_80,B_81] : r1_tarski(k3_xboole_0(A_80,B_81),k2_xboole_0(B_81,B_81)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_120])).

tff(c_134,plain,(
    ! [A_83,B_84] : r1_tarski(k3_xboole_0(A_83,B_84),B_84) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_127])).

tff(c_28,plain,(
    ! [A_42,B_43] :
      ( m1_subset_1(A_42,k1_zfmisc_1(B_43))
      | ~ r1_tarski(A_42,B_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_82,plain,(
    ! [B_64,A_65] :
      ( v1_relat_1(B_64)
      | ~ m1_subset_1(B_64,k1_zfmisc_1(A_65))
      | ~ v1_relat_1(A_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_86,plain,(
    ! [A_42,B_43] :
      ( v1_relat_1(A_42)
      | ~ v1_relat_1(B_43)
      | ~ r1_tarski(A_42,B_43) ) ),
    inference(resolution,[status(thm)],[c_28,c_82])).

tff(c_138,plain,(
    ! [A_83,B_84] :
      ( v1_relat_1(k3_xboole_0(A_83,B_84))
      | ~ v1_relat_1(B_84) ) ),
    inference(resolution,[status(thm)],[c_134,c_86])).

tff(c_132,plain,(
    ! [A_80,B_81] : r1_tarski(k3_xboole_0(A_80,B_81),B_81) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_127])).

tff(c_32,plain,(
    ! [A_47,B_49] :
      ( r1_tarski(k3_relat_1(A_47),k3_relat_1(B_49))
      | ~ r1_tarski(A_47,B_49)
      | ~ v1_relat_1(B_49)
      | ~ v1_relat_1(A_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_38,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_4,plain,(
    ! [A_3,B_4] : r1_tarski(k3_xboole_0(A_3,B_4),A_3) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_142,plain,(
    ! [A_87,B_88] :
      ( r1_tarski(k3_relat_1(A_87),k3_relat_1(B_88))
      | ~ r1_tarski(A_87,B_88)
      | ~ v1_relat_1(B_88)
      | ~ v1_relat_1(A_87) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_102,plain,(
    ! [A_73,B_74,C_75] :
      ( r1_tarski(A_73,k3_xboole_0(B_74,C_75))
      | ~ r1_tarski(A_73,C_75)
      | ~ r1_tarski(A_73,B_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_34,plain,(
    ~ r1_tarski(k3_relat_1(k3_xboole_0('#skF_1','#skF_2')),k3_xboole_0(k3_relat_1('#skF_1'),k3_relat_1('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_110,plain,
    ( ~ r1_tarski(k3_relat_1(k3_xboole_0('#skF_1','#skF_2')),k3_relat_1('#skF_2'))
    | ~ r1_tarski(k3_relat_1(k3_xboole_0('#skF_1','#skF_2')),k3_relat_1('#skF_1')) ),
    inference(resolution,[status(thm)],[c_102,c_34])).

tff(c_140,plain,(
    ~ r1_tarski(k3_relat_1(k3_xboole_0('#skF_1','#skF_2')),k3_relat_1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_110])).

tff(c_145,plain,
    ( ~ r1_tarski(k3_xboole_0('#skF_1','#skF_2'),'#skF_1')
    | ~ v1_relat_1('#skF_1')
    | ~ v1_relat_1(k3_xboole_0('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_142,c_140])).

tff(c_151,plain,(
    ~ v1_relat_1(k3_xboole_0('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_4,c_145])).

tff(c_155,plain,(
    ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_138,c_151])).

tff(c_162,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_155])).

tff(c_163,plain,(
    ~ r1_tarski(k3_relat_1(k3_xboole_0('#skF_1','#skF_2')),k3_relat_1('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_110])).

tff(c_173,plain,
    ( ~ r1_tarski(k3_xboole_0('#skF_1','#skF_2'),'#skF_2')
    | ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1(k3_xboole_0('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_32,c_163])).

tff(c_176,plain,(
    ~ v1_relat_1(k3_xboole_0('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_132,c_173])).

tff(c_179,plain,(
    ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_138,c_176])).

tff(c_186,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_179])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:42:09 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.00/1.20  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.00/1.20  
% 2.00/1.20  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.00/1.20  %$ r1_tarski > m1_subset_1 > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k3_relat_1 > k1_zfmisc_1 > k1_setfam_1 > #skF_2 > #skF_1
% 2.00/1.20  
% 2.00/1.20  %Foreground sorts:
% 2.00/1.20  
% 2.00/1.20  
% 2.00/1.20  %Background operators:
% 2.00/1.20  
% 2.00/1.20  
% 2.00/1.20  %Foreground operators:
% 2.00/1.20  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.00/1.20  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.00/1.20  tff(k3_relat_1, type, k3_relat_1: $i > $i).
% 2.00/1.20  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.00/1.20  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.00/1.20  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.00/1.20  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.00/1.20  tff('#skF_2', type, '#skF_2': $i).
% 2.00/1.20  tff('#skF_1', type, '#skF_1': $i).
% 2.00/1.20  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.00/1.20  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.00/1.20  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.00/1.20  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.00/1.20  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.00/1.20  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.00/1.20  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.00/1.20  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.00/1.20  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.00/1.20  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.00/1.20  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.00/1.20  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.00/1.20  
% 2.12/1.22  tff(f_81, negated_conjecture, ~(![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => r1_tarski(k3_relat_1(k3_xboole_0(A, B)), k3_xboole_0(k3_relat_1(A), k3_relat_1(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t34_relat_1)).
% 2.12/1.22  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k2_xboole_0)).
% 2.12/1.22  tff(f_37, axiom, (![A, B, C]: r1_tarski(k2_xboole_0(k3_xboole_0(A, B), k3_xboole_0(A, C)), k2_xboole_0(B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_xboole_1)).
% 2.12/1.22  tff(f_57, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 2.12/1.22  tff(f_64, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 2.12/1.22  tff(f_73, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(A, B) => r1_tarski(k3_relat_1(A), k3_relat_1(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_relat_1)).
% 2.12/1.22  tff(f_29, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 2.12/1.22  tff(f_35, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(A, C)) => r1_tarski(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t19_xboole_1)).
% 2.12/1.22  tff(c_36, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.12/1.22  tff(c_2, plain, (![A_1]: (k2_xboole_0(A_1, A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.12/1.22  tff(c_120, plain, (![A_80, B_81, C_82]: (r1_tarski(k2_xboole_0(k3_xboole_0(A_80, B_81), k3_xboole_0(A_80, C_82)), k2_xboole_0(B_81, C_82)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.12/1.22  tff(c_127, plain, (![A_80, B_81]: (r1_tarski(k3_xboole_0(A_80, B_81), k2_xboole_0(B_81, B_81)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_120])).
% 2.12/1.22  tff(c_134, plain, (![A_83, B_84]: (r1_tarski(k3_xboole_0(A_83, B_84), B_84))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_127])).
% 2.12/1.22  tff(c_28, plain, (![A_42, B_43]: (m1_subset_1(A_42, k1_zfmisc_1(B_43)) | ~r1_tarski(A_42, B_43))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.12/1.22  tff(c_82, plain, (![B_64, A_65]: (v1_relat_1(B_64) | ~m1_subset_1(B_64, k1_zfmisc_1(A_65)) | ~v1_relat_1(A_65))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.12/1.22  tff(c_86, plain, (![A_42, B_43]: (v1_relat_1(A_42) | ~v1_relat_1(B_43) | ~r1_tarski(A_42, B_43))), inference(resolution, [status(thm)], [c_28, c_82])).
% 2.12/1.22  tff(c_138, plain, (![A_83, B_84]: (v1_relat_1(k3_xboole_0(A_83, B_84)) | ~v1_relat_1(B_84))), inference(resolution, [status(thm)], [c_134, c_86])).
% 2.12/1.22  tff(c_132, plain, (![A_80, B_81]: (r1_tarski(k3_xboole_0(A_80, B_81), B_81))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_127])).
% 2.12/1.22  tff(c_32, plain, (![A_47, B_49]: (r1_tarski(k3_relat_1(A_47), k3_relat_1(B_49)) | ~r1_tarski(A_47, B_49) | ~v1_relat_1(B_49) | ~v1_relat_1(A_47))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.12/1.22  tff(c_38, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.12/1.22  tff(c_4, plain, (![A_3, B_4]: (r1_tarski(k3_xboole_0(A_3, B_4), A_3))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.12/1.22  tff(c_142, plain, (![A_87, B_88]: (r1_tarski(k3_relat_1(A_87), k3_relat_1(B_88)) | ~r1_tarski(A_87, B_88) | ~v1_relat_1(B_88) | ~v1_relat_1(A_87))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.12/1.22  tff(c_102, plain, (![A_73, B_74, C_75]: (r1_tarski(A_73, k3_xboole_0(B_74, C_75)) | ~r1_tarski(A_73, C_75) | ~r1_tarski(A_73, B_74))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.12/1.22  tff(c_34, plain, (~r1_tarski(k3_relat_1(k3_xboole_0('#skF_1', '#skF_2')), k3_xboole_0(k3_relat_1('#skF_1'), k3_relat_1('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.12/1.22  tff(c_110, plain, (~r1_tarski(k3_relat_1(k3_xboole_0('#skF_1', '#skF_2')), k3_relat_1('#skF_2')) | ~r1_tarski(k3_relat_1(k3_xboole_0('#skF_1', '#skF_2')), k3_relat_1('#skF_1'))), inference(resolution, [status(thm)], [c_102, c_34])).
% 2.12/1.22  tff(c_140, plain, (~r1_tarski(k3_relat_1(k3_xboole_0('#skF_1', '#skF_2')), k3_relat_1('#skF_1'))), inference(splitLeft, [status(thm)], [c_110])).
% 2.12/1.22  tff(c_145, plain, (~r1_tarski(k3_xboole_0('#skF_1', '#skF_2'), '#skF_1') | ~v1_relat_1('#skF_1') | ~v1_relat_1(k3_xboole_0('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_142, c_140])).
% 2.12/1.22  tff(c_151, plain, (~v1_relat_1(k3_xboole_0('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_4, c_145])).
% 2.12/1.22  tff(c_155, plain, (~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_138, c_151])).
% 2.12/1.22  tff(c_162, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_36, c_155])).
% 2.12/1.22  tff(c_163, plain, (~r1_tarski(k3_relat_1(k3_xboole_0('#skF_1', '#skF_2')), k3_relat_1('#skF_2'))), inference(splitRight, [status(thm)], [c_110])).
% 2.12/1.22  tff(c_173, plain, (~r1_tarski(k3_xboole_0('#skF_1', '#skF_2'), '#skF_2') | ~v1_relat_1('#skF_2') | ~v1_relat_1(k3_xboole_0('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_32, c_163])).
% 2.12/1.22  tff(c_176, plain, (~v1_relat_1(k3_xboole_0('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_132, c_173])).
% 2.12/1.22  tff(c_179, plain, (~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_138, c_176])).
% 2.12/1.22  tff(c_186, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_36, c_179])).
% 2.12/1.22  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.12/1.22  
% 2.12/1.22  Inference rules
% 2.12/1.22  ----------------------
% 2.12/1.22  #Ref     : 0
% 2.12/1.22  #Sup     : 29
% 2.12/1.22  #Fact    : 0
% 2.12/1.22  #Define  : 0
% 2.12/1.22  #Split   : 1
% 2.12/1.22  #Chain   : 0
% 2.12/1.22  #Close   : 0
% 2.12/1.22  
% 2.12/1.22  Ordering : KBO
% 2.12/1.22  
% 2.12/1.22  Simplification rules
% 2.12/1.22  ----------------------
% 2.12/1.22  #Subsume      : 0
% 2.12/1.22  #Demod        : 9
% 2.12/1.22  #Tautology    : 14
% 2.12/1.22  #SimpNegUnit  : 0
% 2.12/1.22  #BackRed      : 0
% 2.12/1.22  
% 2.12/1.22  #Partial instantiations: 0
% 2.12/1.22  #Strategies tried      : 1
% 2.12/1.22  
% 2.12/1.22  Timing (in seconds)
% 2.12/1.22  ----------------------
% 2.12/1.22  Preprocessing        : 0.31
% 2.12/1.22  Parsing              : 0.17
% 2.12/1.22  CNF conversion       : 0.02
% 2.12/1.22  Main loop            : 0.15
% 2.12/1.22  Inferencing          : 0.06
% 2.12/1.22  Reduction            : 0.04
% 2.12/1.22  Demodulation         : 0.03
% 2.12/1.22  BG Simplification    : 0.01
% 2.12/1.22  Subsumption          : 0.03
% 2.12/1.22  Abstraction          : 0.01
% 2.12/1.22  MUC search           : 0.00
% 2.12/1.22  Cooper               : 0.00
% 2.12/1.22  Total                : 0.49
% 2.12/1.22  Index Insertion      : 0.00
% 2.12/1.22  Index Deletion       : 0.00
% 2.12/1.22  Index Matching       : 0.00
% 2.12/1.22  BG Taut test         : 0.00
%------------------------------------------------------------------------------
