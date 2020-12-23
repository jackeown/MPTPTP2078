%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:58:05 EST 2020

% Result     : Theorem 1.86s
% Output     : CNFRefutation 1.86s
% Verified   : 
% Statistics : Number of formulae       :   48 (  71 expanded)
%              Number of leaves         :   17 (  30 expanded)
%              Depth                    :    9
%              Number of atoms          :   57 ( 108 expanded)
%              Number of equality atoms :   15 (  33 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > m1_subset_1 > m1_setfam_1 > k5_setfam_1 > #nlpp > k3_tarski > k1_zfmisc_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(m1_setfam_1,type,(
    m1_setfam_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k5_setfam_1,type,(
    k5_setfam_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_54,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
       => ( m1_setfam_1(B,A)
        <=> k5_setfam_1(A,B) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_setfam_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => k5_setfam_1(A,B) = k3_tarski(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k5_setfam_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_35,axiom,(
    ! [A,B] :
      ( m1_setfam_1(B,A)
    <=> r1_tarski(A,k3_tarski(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d12_setfam_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => m1_subset_1(k5_setfam_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_setfam_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(c_22,plain,
    ( k5_setfam_1('#skF_1','#skF_2') != '#skF_1'
    | ~ m1_setfam_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_53,plain,(
    ~ m1_setfam_1('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_22])).

tff(c_28,plain,
    ( m1_setfam_1('#skF_2','#skF_1')
    | k5_setfam_1('#skF_1','#skF_2') = '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_54,plain,(
    k5_setfam_1('#skF_1','#skF_2') = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_28])).

tff(c_20,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k1_zfmisc_1('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_73,plain,(
    ! [A_23,B_24] :
      ( k5_setfam_1(A_23,B_24) = k3_tarski(B_24)
      | ~ m1_subset_1(B_24,k1_zfmisc_1(k1_zfmisc_1(A_23))) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_80,plain,(
    k5_setfam_1('#skF_1','#skF_2') = k3_tarski('#skF_2') ),
    inference(resolution,[status(thm)],[c_20,c_73])).

tff(c_83,plain,(
    k3_tarski('#skF_2') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_80])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_36,plain,(
    ! [B_14,A_15] :
      ( m1_setfam_1(B_14,A_15)
      | ~ r1_tarski(A_15,k3_tarski(B_14)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_41,plain,(
    ! [B_14] : m1_setfam_1(B_14,k3_tarski(B_14)) ),
    inference(resolution,[status(thm)],[c_6,c_36])).

tff(c_87,plain,(
    m1_setfam_1('#skF_2','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_83,c_41])).

tff(c_97,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_53,c_87])).

tff(c_98,plain,(
    m1_setfam_1('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_28])).

tff(c_100,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_53,c_98])).

tff(c_102,plain,(
    m1_setfam_1('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_22])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( r1_tarski(A_3,k3_tarski(B_4))
      | ~ m1_setfam_1(B_4,A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_122,plain,(
    ! [A_27,B_28] :
      ( k5_setfam_1(A_27,B_28) = k3_tarski(B_28)
      | ~ m1_subset_1(B_28,k1_zfmisc_1(k1_zfmisc_1(A_27))) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_131,plain,(
    k5_setfam_1('#skF_1','#skF_2') = k3_tarski('#skF_2') ),
    inference(resolution,[status(thm)],[c_20,c_122])).

tff(c_101,plain,(
    k5_setfam_1('#skF_1','#skF_2') != '#skF_1' ),
    inference(splitRight,[status(thm)],[c_22])).

tff(c_132,plain,(
    k3_tarski('#skF_2') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_131,c_101])).

tff(c_157,plain,(
    ! [A_32,B_33] :
      ( m1_subset_1(k5_setfam_1(A_32,B_33),k1_zfmisc_1(A_32))
      | ~ m1_subset_1(B_33,k1_zfmisc_1(k1_zfmisc_1(A_32))) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_170,plain,
    ( m1_subset_1(k3_tarski('#skF_2'),k1_zfmisc_1('#skF_1'))
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k1_zfmisc_1('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_131,c_157])).

tff(c_174,plain,(
    m1_subset_1(k3_tarski('#skF_2'),k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_170])).

tff(c_16,plain,(
    ! [A_9,B_10] :
      ( r1_tarski(A_9,B_10)
      | ~ m1_subset_1(A_9,k1_zfmisc_1(B_10)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_178,plain,(
    r1_tarski(k3_tarski('#skF_2'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_174,c_16])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_180,plain,
    ( k3_tarski('#skF_2') = '#skF_1'
    | ~ r1_tarski('#skF_1',k3_tarski('#skF_2')) ),
    inference(resolution,[status(thm)],[c_178,c_2])).

tff(c_183,plain,(
    ~ r1_tarski('#skF_1',k3_tarski('#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_132,c_180])).

tff(c_186,plain,(
    ~ m1_setfam_1('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_8,c_183])).

tff(c_190,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_186])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n009.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 14:48:56 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.86/1.18  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.86/1.19  
% 1.86/1.19  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.86/1.19  %$ r1_tarski > m1_subset_1 > m1_setfam_1 > k5_setfam_1 > #nlpp > k3_tarski > k1_zfmisc_1 > #skF_2 > #skF_1
% 1.86/1.19  
% 1.86/1.19  %Foreground sorts:
% 1.86/1.19  
% 1.86/1.19  
% 1.86/1.19  %Background operators:
% 1.86/1.19  
% 1.86/1.19  
% 1.86/1.19  %Foreground operators:
% 1.86/1.19  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.86/1.19  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.86/1.19  tff('#skF_2', type, '#skF_2': $i).
% 1.86/1.19  tff('#skF_1', type, '#skF_1': $i).
% 1.86/1.19  tff(m1_setfam_1, type, m1_setfam_1: ($i * $i) > $o).
% 1.86/1.19  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.86/1.19  tff(k5_setfam_1, type, k5_setfam_1: ($i * $i) > $i).
% 1.86/1.19  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.86/1.19  tff(k3_tarski, type, k3_tarski: $i > $i).
% 1.86/1.19  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.86/1.19  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.86/1.19  
% 1.86/1.20  tff(f_54, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (m1_setfam_1(B, A) <=> (k5_setfam_1(A, B) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_setfam_1)).
% 1.86/1.20  tff(f_43, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (k5_setfam_1(A, B) = k3_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k5_setfam_1)).
% 1.86/1.20  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 1.86/1.20  tff(f_35, axiom, (![A, B]: (m1_setfam_1(B, A) <=> r1_tarski(A, k3_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d12_setfam_1)).
% 1.86/1.20  tff(f_39, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => m1_subset_1(k5_setfam_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k5_setfam_1)).
% 1.86/1.20  tff(f_47, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 1.86/1.20  tff(c_22, plain, (k5_setfam_1('#skF_1', '#skF_2')!='#skF_1' | ~m1_setfam_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_54])).
% 1.86/1.20  tff(c_53, plain, (~m1_setfam_1('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_22])).
% 1.86/1.20  tff(c_28, plain, (m1_setfam_1('#skF_2', '#skF_1') | k5_setfam_1('#skF_1', '#skF_2')='#skF_1'), inference(cnfTransformation, [status(thm)], [f_54])).
% 1.86/1.20  tff(c_54, plain, (k5_setfam_1('#skF_1', '#skF_2')='#skF_1'), inference(splitLeft, [status(thm)], [c_28])).
% 1.86/1.20  tff(c_20, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k1_zfmisc_1('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_54])).
% 1.86/1.20  tff(c_73, plain, (![A_23, B_24]: (k5_setfam_1(A_23, B_24)=k3_tarski(B_24) | ~m1_subset_1(B_24, k1_zfmisc_1(k1_zfmisc_1(A_23))))), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.86/1.20  tff(c_80, plain, (k5_setfam_1('#skF_1', '#skF_2')=k3_tarski('#skF_2')), inference(resolution, [status(thm)], [c_20, c_73])).
% 1.86/1.20  tff(c_83, plain, (k3_tarski('#skF_2')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_54, c_80])).
% 1.86/1.20  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.86/1.20  tff(c_36, plain, (![B_14, A_15]: (m1_setfam_1(B_14, A_15) | ~r1_tarski(A_15, k3_tarski(B_14)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.86/1.20  tff(c_41, plain, (![B_14]: (m1_setfam_1(B_14, k3_tarski(B_14)))), inference(resolution, [status(thm)], [c_6, c_36])).
% 1.86/1.20  tff(c_87, plain, (m1_setfam_1('#skF_2', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_83, c_41])).
% 1.86/1.20  tff(c_97, plain, $false, inference(negUnitSimplification, [status(thm)], [c_53, c_87])).
% 1.86/1.20  tff(c_98, plain, (m1_setfam_1('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_28])).
% 1.86/1.20  tff(c_100, plain, $false, inference(negUnitSimplification, [status(thm)], [c_53, c_98])).
% 1.86/1.20  tff(c_102, plain, (m1_setfam_1('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_22])).
% 1.86/1.20  tff(c_8, plain, (![A_3, B_4]: (r1_tarski(A_3, k3_tarski(B_4)) | ~m1_setfam_1(B_4, A_3))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.86/1.20  tff(c_122, plain, (![A_27, B_28]: (k5_setfam_1(A_27, B_28)=k3_tarski(B_28) | ~m1_subset_1(B_28, k1_zfmisc_1(k1_zfmisc_1(A_27))))), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.86/1.20  tff(c_131, plain, (k5_setfam_1('#skF_1', '#skF_2')=k3_tarski('#skF_2')), inference(resolution, [status(thm)], [c_20, c_122])).
% 1.86/1.20  tff(c_101, plain, (k5_setfam_1('#skF_1', '#skF_2')!='#skF_1'), inference(splitRight, [status(thm)], [c_22])).
% 1.86/1.20  tff(c_132, plain, (k3_tarski('#skF_2')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_131, c_101])).
% 1.86/1.20  tff(c_157, plain, (![A_32, B_33]: (m1_subset_1(k5_setfam_1(A_32, B_33), k1_zfmisc_1(A_32)) | ~m1_subset_1(B_33, k1_zfmisc_1(k1_zfmisc_1(A_32))))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.86/1.20  tff(c_170, plain, (m1_subset_1(k3_tarski('#skF_2'), k1_zfmisc_1('#skF_1')) | ~m1_subset_1('#skF_2', k1_zfmisc_1(k1_zfmisc_1('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_131, c_157])).
% 1.86/1.20  tff(c_174, plain, (m1_subset_1(k3_tarski('#skF_2'), k1_zfmisc_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_170])).
% 1.86/1.20  tff(c_16, plain, (![A_9, B_10]: (r1_tarski(A_9, B_10) | ~m1_subset_1(A_9, k1_zfmisc_1(B_10)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 1.86/1.20  tff(c_178, plain, (r1_tarski(k3_tarski('#skF_2'), '#skF_1')), inference(resolution, [status(thm)], [c_174, c_16])).
% 1.86/1.20  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.86/1.20  tff(c_180, plain, (k3_tarski('#skF_2')='#skF_1' | ~r1_tarski('#skF_1', k3_tarski('#skF_2'))), inference(resolution, [status(thm)], [c_178, c_2])).
% 1.86/1.20  tff(c_183, plain, (~r1_tarski('#skF_1', k3_tarski('#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_132, c_180])).
% 1.86/1.20  tff(c_186, plain, (~m1_setfam_1('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_8, c_183])).
% 1.86/1.20  tff(c_190, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_102, c_186])).
% 1.86/1.20  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.86/1.20  
% 1.86/1.20  Inference rules
% 1.86/1.20  ----------------------
% 1.86/1.20  #Ref     : 0
% 1.86/1.20  #Sup     : 34
% 1.86/1.20  #Fact    : 0
% 1.86/1.20  #Define  : 0
% 1.86/1.20  #Split   : 5
% 1.86/1.20  #Chain   : 0
% 1.86/1.20  #Close   : 0
% 1.86/1.20  
% 1.86/1.20  Ordering : KBO
% 1.86/1.20  
% 1.86/1.20  Simplification rules
% 1.86/1.20  ----------------------
% 1.86/1.20  #Subsume      : 1
% 1.86/1.20  #Demod        : 9
% 1.86/1.20  #Tautology    : 16
% 1.86/1.20  #SimpNegUnit  : 4
% 1.86/1.20  #BackRed      : 1
% 1.86/1.20  
% 1.86/1.20  #Partial instantiations: 0
% 1.86/1.20  #Strategies tried      : 1
% 1.86/1.20  
% 1.86/1.20  Timing (in seconds)
% 1.86/1.20  ----------------------
% 1.86/1.20  Preprocessing        : 0.28
% 1.86/1.20  Parsing              : 0.15
% 1.86/1.20  CNF conversion       : 0.02
% 1.86/1.20  Main loop            : 0.15
% 1.86/1.20  Inferencing          : 0.06
% 1.86/1.20  Reduction            : 0.04
% 1.86/1.20  Demodulation         : 0.03
% 1.86/1.20  BG Simplification    : 0.01
% 1.86/1.20  Subsumption          : 0.03
% 1.86/1.20  Abstraction          : 0.01
% 1.86/1.20  MUC search           : 0.00
% 1.86/1.20  Cooper               : 0.00
% 1.86/1.21  Total                : 0.47
% 1.86/1.21  Index Insertion      : 0.00
% 1.86/1.21  Index Deletion       : 0.00
% 1.86/1.21  Index Matching       : 0.00
% 1.86/1.21  BG Taut test         : 0.00
%------------------------------------------------------------------------------
