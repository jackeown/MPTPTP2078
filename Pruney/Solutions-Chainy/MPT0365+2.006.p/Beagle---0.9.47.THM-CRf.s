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
% DateTime   : Thu Dec  3 09:56:43 EST 2020

% Result     : Theorem 1.85s
% Output     : CNFRefutation 1.85s
% Verified   : 
% Statistics : Number of formulae       :   41 (  77 expanded)
%              Number of leaves         :   16 (  33 expanded)
%              Depth                    :    9
%              Number of atoms          :   72 ( 200 expanded)
%              Number of equality atoms :    7 (  18 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > m1_subset_1 > k3_subset_1 > #nlpp > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_65,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => ! [C] :
            ( m1_subset_1(C,k1_zfmisc_1(A))
           => ( ( r1_xboole_0(B,C)
                & r1_xboole_0(k3_subset_1(A,B),k3_subset_1(A,C)) )
             => B = k3_subset_1(A,C) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_subset_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k3_subset_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(A))
         => ( r1_xboole_0(B,C)
          <=> r1_tarski(B,k3_subset_1(A,C)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_subset_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(A))
         => ( r1_tarski(B,C)
          <=> r1_tarski(k3_subset_1(A,C),k3_subset_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_subset_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(c_18,plain,(
    k3_subset_1('#skF_1','#skF_3') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_26,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_24,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_22,plain,(
    r1_xboole_0('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( m1_subset_1(k3_subset_1(A_3,B_4),k1_zfmisc_1(A_3))
      | ~ m1_subset_1(B_4,k1_zfmisc_1(A_3)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_20,plain,(
    r1_xboole_0(k3_subset_1('#skF_1','#skF_2'),k3_subset_1('#skF_1','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_16,plain,(
    ! [B_10,A_9,C_12] :
      ( r1_tarski(B_10,k3_subset_1(A_9,C_12))
      | ~ r1_xboole_0(B_10,C_12)
      | ~ m1_subset_1(C_12,k1_zfmisc_1(A_9))
      | ~ m1_subset_1(B_10,k1_zfmisc_1(A_9)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_64,plain,(
    ! [B_32,C_33,A_34] :
      ( r1_tarski(B_32,C_33)
      | ~ r1_tarski(k3_subset_1(A_34,C_33),k3_subset_1(A_34,B_32))
      | ~ m1_subset_1(C_33,k1_zfmisc_1(A_34))
      | ~ m1_subset_1(B_32,k1_zfmisc_1(A_34)) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_96,plain,(
    ! [C_38,C_39,A_40] :
      ( r1_tarski(C_38,C_39)
      | ~ m1_subset_1(C_39,k1_zfmisc_1(A_40))
      | ~ r1_xboole_0(k3_subset_1(A_40,C_39),C_38)
      | ~ m1_subset_1(C_38,k1_zfmisc_1(A_40))
      | ~ m1_subset_1(k3_subset_1(A_40,C_39),k1_zfmisc_1(A_40)) ) ),
    inference(resolution,[status(thm)],[c_16,c_64])).

tff(c_100,plain,
    ( r1_tarski(k3_subset_1('#skF_1','#skF_3'),'#skF_2')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1('#skF_1'))
    | ~ m1_subset_1(k3_subset_1('#skF_1','#skF_3'),k1_zfmisc_1('#skF_1'))
    | ~ m1_subset_1(k3_subset_1('#skF_1','#skF_2'),k1_zfmisc_1('#skF_1')) ),
    inference(resolution,[status(thm)],[c_20,c_96])).

tff(c_105,plain,
    ( r1_tarski(k3_subset_1('#skF_1','#skF_3'),'#skF_2')
    | ~ m1_subset_1(k3_subset_1('#skF_1','#skF_3'),k1_zfmisc_1('#skF_1'))
    | ~ m1_subset_1(k3_subset_1('#skF_1','#skF_2'),k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_100])).

tff(c_106,plain,(
    ~ m1_subset_1(k3_subset_1('#skF_1','#skF_2'),k1_zfmisc_1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_105])).

tff(c_109,plain,(
    ~ m1_subset_1('#skF_2',k1_zfmisc_1('#skF_1')) ),
    inference(resolution,[status(thm)],[c_8,c_106])).

tff(c_113,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_109])).

tff(c_114,plain,
    ( ~ m1_subset_1(k3_subset_1('#skF_1','#skF_3'),k1_zfmisc_1('#skF_1'))
    | r1_tarski(k3_subset_1('#skF_1','#skF_3'),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_105])).

tff(c_116,plain,(
    ~ m1_subset_1(k3_subset_1('#skF_1','#skF_3'),k1_zfmisc_1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_114])).

tff(c_119,plain,(
    ~ m1_subset_1('#skF_3',k1_zfmisc_1('#skF_1')) ),
    inference(resolution,[status(thm)],[c_8,c_116])).

tff(c_123,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_119])).

tff(c_124,plain,(
    r1_tarski(k3_subset_1('#skF_1','#skF_3'),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_114])).

tff(c_37,plain,(
    ! [B_19,A_20,C_21] :
      ( r1_tarski(B_19,k3_subset_1(A_20,C_21))
      | ~ r1_xboole_0(B_19,C_21)
      | ~ m1_subset_1(C_21,k1_zfmisc_1(A_20))
      | ~ m1_subset_1(B_19,k1_zfmisc_1(A_20)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_40,plain,(
    ! [A_20,C_21,B_19] :
      ( k3_subset_1(A_20,C_21) = B_19
      | ~ r1_tarski(k3_subset_1(A_20,C_21),B_19)
      | ~ r1_xboole_0(B_19,C_21)
      | ~ m1_subset_1(C_21,k1_zfmisc_1(A_20))
      | ~ m1_subset_1(B_19,k1_zfmisc_1(A_20)) ) ),
    inference(resolution,[status(thm)],[c_37,c_2])).

tff(c_128,plain,
    ( k3_subset_1('#skF_1','#skF_3') = '#skF_2'
    | ~ r1_xboole_0('#skF_2','#skF_3')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1('#skF_1'))
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1('#skF_1')) ),
    inference(resolution,[status(thm)],[c_124,c_40])).

tff(c_133,plain,(
    k3_subset_1('#skF_1','#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_24,c_22,c_128])).

tff(c_135,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_18,c_133])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n018.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 20:13:42 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.85/1.22  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.85/1.22  
% 1.85/1.22  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.85/1.22  %$ r1_xboole_0 > r1_tarski > m1_subset_1 > k3_subset_1 > #nlpp > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1
% 1.85/1.22  
% 1.85/1.22  %Foreground sorts:
% 1.85/1.22  
% 1.85/1.22  
% 1.85/1.22  %Background operators:
% 1.85/1.22  
% 1.85/1.22  
% 1.85/1.22  %Foreground operators:
% 1.85/1.22  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.85/1.22  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.85/1.22  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 1.85/1.22  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.85/1.22  tff('#skF_2', type, '#skF_2': $i).
% 1.85/1.22  tff('#skF_3', type, '#skF_3': $i).
% 1.85/1.22  tff('#skF_1', type, '#skF_1': $i).
% 1.85/1.22  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.85/1.22  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.85/1.22  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.85/1.22  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.85/1.22  
% 1.85/1.24  tff(f_65, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => ((r1_xboole_0(B, C) & r1_xboole_0(k3_subset_1(A, B), k3_subset_1(A, C))) => (B = k3_subset_1(A, C))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_subset_1)).
% 1.85/1.24  tff(f_35, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k3_subset_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 1.85/1.24  tff(f_53, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (r1_xboole_0(B, C) <=> r1_tarski(B, k3_subset_1(A, C))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_subset_1)).
% 1.85/1.24  tff(f_44, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (r1_tarski(B, C) <=> r1_tarski(k3_subset_1(A, C), k3_subset_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_subset_1)).
% 1.85/1.24  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 1.85/1.24  tff(c_18, plain, (k3_subset_1('#skF_1', '#skF_3')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_65])).
% 1.85/1.24  tff(c_26, plain, (m1_subset_1('#skF_2', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_65])).
% 1.85/1.24  tff(c_24, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_65])).
% 1.85/1.24  tff(c_22, plain, (r1_xboole_0('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_65])).
% 1.85/1.24  tff(c_8, plain, (![A_3, B_4]: (m1_subset_1(k3_subset_1(A_3, B_4), k1_zfmisc_1(A_3)) | ~m1_subset_1(B_4, k1_zfmisc_1(A_3)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.85/1.24  tff(c_20, plain, (r1_xboole_0(k3_subset_1('#skF_1', '#skF_2'), k3_subset_1('#skF_1', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_65])).
% 1.85/1.24  tff(c_16, plain, (![B_10, A_9, C_12]: (r1_tarski(B_10, k3_subset_1(A_9, C_12)) | ~r1_xboole_0(B_10, C_12) | ~m1_subset_1(C_12, k1_zfmisc_1(A_9)) | ~m1_subset_1(B_10, k1_zfmisc_1(A_9)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 1.85/1.24  tff(c_64, plain, (![B_32, C_33, A_34]: (r1_tarski(B_32, C_33) | ~r1_tarski(k3_subset_1(A_34, C_33), k3_subset_1(A_34, B_32)) | ~m1_subset_1(C_33, k1_zfmisc_1(A_34)) | ~m1_subset_1(B_32, k1_zfmisc_1(A_34)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 1.85/1.24  tff(c_96, plain, (![C_38, C_39, A_40]: (r1_tarski(C_38, C_39) | ~m1_subset_1(C_39, k1_zfmisc_1(A_40)) | ~r1_xboole_0(k3_subset_1(A_40, C_39), C_38) | ~m1_subset_1(C_38, k1_zfmisc_1(A_40)) | ~m1_subset_1(k3_subset_1(A_40, C_39), k1_zfmisc_1(A_40)))), inference(resolution, [status(thm)], [c_16, c_64])).
% 1.85/1.24  tff(c_100, plain, (r1_tarski(k3_subset_1('#skF_1', '#skF_3'), '#skF_2') | ~m1_subset_1('#skF_2', k1_zfmisc_1('#skF_1')) | ~m1_subset_1(k3_subset_1('#skF_1', '#skF_3'), k1_zfmisc_1('#skF_1')) | ~m1_subset_1(k3_subset_1('#skF_1', '#skF_2'), k1_zfmisc_1('#skF_1'))), inference(resolution, [status(thm)], [c_20, c_96])).
% 1.85/1.24  tff(c_105, plain, (r1_tarski(k3_subset_1('#skF_1', '#skF_3'), '#skF_2') | ~m1_subset_1(k3_subset_1('#skF_1', '#skF_3'), k1_zfmisc_1('#skF_1')) | ~m1_subset_1(k3_subset_1('#skF_1', '#skF_2'), k1_zfmisc_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_100])).
% 1.85/1.24  tff(c_106, plain, (~m1_subset_1(k3_subset_1('#skF_1', '#skF_2'), k1_zfmisc_1('#skF_1'))), inference(splitLeft, [status(thm)], [c_105])).
% 1.85/1.24  tff(c_109, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1('#skF_1'))), inference(resolution, [status(thm)], [c_8, c_106])).
% 1.85/1.24  tff(c_113, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_26, c_109])).
% 1.85/1.24  tff(c_114, plain, (~m1_subset_1(k3_subset_1('#skF_1', '#skF_3'), k1_zfmisc_1('#skF_1')) | r1_tarski(k3_subset_1('#skF_1', '#skF_3'), '#skF_2')), inference(splitRight, [status(thm)], [c_105])).
% 1.85/1.24  tff(c_116, plain, (~m1_subset_1(k3_subset_1('#skF_1', '#skF_3'), k1_zfmisc_1('#skF_1'))), inference(splitLeft, [status(thm)], [c_114])).
% 1.85/1.24  tff(c_119, plain, (~m1_subset_1('#skF_3', k1_zfmisc_1('#skF_1'))), inference(resolution, [status(thm)], [c_8, c_116])).
% 1.85/1.24  tff(c_123, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_24, c_119])).
% 1.85/1.24  tff(c_124, plain, (r1_tarski(k3_subset_1('#skF_1', '#skF_3'), '#skF_2')), inference(splitRight, [status(thm)], [c_114])).
% 1.85/1.24  tff(c_37, plain, (![B_19, A_20, C_21]: (r1_tarski(B_19, k3_subset_1(A_20, C_21)) | ~r1_xboole_0(B_19, C_21) | ~m1_subset_1(C_21, k1_zfmisc_1(A_20)) | ~m1_subset_1(B_19, k1_zfmisc_1(A_20)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 1.85/1.24  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.85/1.24  tff(c_40, plain, (![A_20, C_21, B_19]: (k3_subset_1(A_20, C_21)=B_19 | ~r1_tarski(k3_subset_1(A_20, C_21), B_19) | ~r1_xboole_0(B_19, C_21) | ~m1_subset_1(C_21, k1_zfmisc_1(A_20)) | ~m1_subset_1(B_19, k1_zfmisc_1(A_20)))), inference(resolution, [status(thm)], [c_37, c_2])).
% 1.85/1.24  tff(c_128, plain, (k3_subset_1('#skF_1', '#skF_3')='#skF_2' | ~r1_xboole_0('#skF_2', '#skF_3') | ~m1_subset_1('#skF_3', k1_zfmisc_1('#skF_1')) | ~m1_subset_1('#skF_2', k1_zfmisc_1('#skF_1'))), inference(resolution, [status(thm)], [c_124, c_40])).
% 1.85/1.24  tff(c_133, plain, (k3_subset_1('#skF_1', '#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_26, c_24, c_22, c_128])).
% 1.85/1.24  tff(c_135, plain, $false, inference(negUnitSimplification, [status(thm)], [c_18, c_133])).
% 1.85/1.24  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.85/1.24  
% 1.85/1.24  Inference rules
% 1.85/1.24  ----------------------
% 1.85/1.24  #Ref     : 0
% 1.85/1.24  #Sup     : 19
% 1.85/1.24  #Fact    : 0
% 1.85/1.24  #Define  : 0
% 1.85/1.24  #Split   : 2
% 1.85/1.24  #Chain   : 0
% 1.85/1.24  #Close   : 0
% 1.85/1.24  
% 1.85/1.24  Ordering : KBO
% 1.85/1.24  
% 1.85/1.24  Simplification rules
% 1.85/1.24  ----------------------
% 1.85/1.24  #Subsume      : 1
% 1.85/1.24  #Demod        : 10
% 1.85/1.24  #Tautology    : 7
% 1.85/1.24  #SimpNegUnit  : 1
% 1.85/1.24  #BackRed      : 0
% 1.85/1.24  
% 1.85/1.24  #Partial instantiations: 0
% 1.85/1.24  #Strategies tried      : 1
% 1.85/1.24  
% 1.85/1.24  Timing (in seconds)
% 1.85/1.24  ----------------------
% 1.85/1.24  Preprocessing        : 0.27
% 1.85/1.24  Parsing              : 0.15
% 1.85/1.24  CNF conversion       : 0.02
% 1.85/1.24  Main loop            : 0.16
% 1.85/1.24  Inferencing          : 0.06
% 1.85/1.24  Reduction            : 0.04
% 1.85/1.24  Demodulation         : 0.03
% 1.85/1.24  BG Simplification    : 0.01
% 1.85/1.24  Subsumption          : 0.04
% 1.85/1.24  Abstraction          : 0.01
% 1.85/1.24  MUC search           : 0.00
% 1.85/1.24  Cooper               : 0.00
% 1.85/1.24  Total                : 0.46
% 1.85/1.24  Index Insertion      : 0.00
% 1.85/1.24  Index Deletion       : 0.00
% 1.85/1.24  Index Matching       : 0.00
% 1.85/1.24  BG Taut test         : 0.00
%------------------------------------------------------------------------------
