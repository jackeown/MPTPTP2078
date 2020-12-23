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
% DateTime   : Thu Dec  3 09:56:30 EST 2020

% Result     : Theorem 2.63s
% Output     : CNFRefutation 2.63s
% Verified   : 
% Statistics : Number of formulae       :   40 (  54 expanded)
%              Number of leaves         :   20 (  28 expanded)
%              Depth                    :    7
%              Number of atoms          :   51 (  83 expanded)
%              Number of equality atoms :    9 (  11 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > m1_subset_1 > k4_subset_1 > k4_xboole_0 > k3_subset_1 > k2_xboole_0 > #nlpp > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff(k4_subset_1,type,(
    k4_subset_1: ( $i * $i * $i ) > $i )).

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_62,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => ! [C] :
            ( m1_subset_1(C,k1_zfmisc_1(A))
           => r1_tarski(k3_subset_1(A,k4_subset_1(A,B,C)),k3_subset_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_subset_1)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => m1_subset_1(k4_subset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_subset_1)).

tff(f_29,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_33,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k4_xboole_0(A,B),C)
     => r1_tarski(A,k2_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_xboole_1)).

tff(f_54,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(A))
         => ( r1_tarski(B,C)
          <=> r1_tarski(k3_subset_1(A,C),k3_subset_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_subset_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(c_20,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_18,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_87,plain,(
    ! [A_30,B_31,C_32] :
      ( k4_subset_1(A_30,B_31,C_32) = k2_xboole_0(B_31,C_32)
      | ~ m1_subset_1(C_32,k1_zfmisc_1(A_30))
      | ~ m1_subset_1(B_31,k1_zfmisc_1(A_30)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_126,plain,(
    ! [B_39] :
      ( k4_subset_1('#skF_1',B_39,'#skF_2') = k2_xboole_0(B_39,'#skF_2')
      | ~ m1_subset_1(B_39,k1_zfmisc_1('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_20,c_87])).

tff(c_133,plain,(
    k4_subset_1('#skF_1','#skF_3','#skF_2') = k2_xboole_0('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_18,c_126])).

tff(c_8,plain,(
    ! [A_8,B_9,C_10] :
      ( m1_subset_1(k4_subset_1(A_8,B_9,C_10),k1_zfmisc_1(A_8))
      | ~ m1_subset_1(C_10,k1_zfmisc_1(A_8))
      | ~ m1_subset_1(B_9,k1_zfmisc_1(A_8)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_148,plain,
    ( m1_subset_1(k2_xboole_0('#skF_3','#skF_2'),k1_zfmisc_1('#skF_1'))
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1('#skF_1'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_133,c_8])).

tff(c_152,plain,(
    m1_subset_1(k2_xboole_0('#skF_3','#skF_2'),k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_20,c_148])).

tff(c_4,plain,(
    ! [A_3,B_4] : r1_tarski(k4_xboole_0(A_3,B_4),A_3) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_55,plain,(
    ! [A_23,B_24,C_25] :
      ( r1_tarski(A_23,k2_xboole_0(B_24,C_25))
      | ~ r1_tarski(k4_xboole_0(A_23,B_24),C_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_59,plain,(
    ! [A_3,B_4] : r1_tarski(A_3,k2_xboole_0(B_4,A_3)) ),
    inference(resolution,[status(thm)],[c_4,c_55])).

tff(c_331,plain,(
    ! [A_47,C_48,B_49] :
      ( r1_tarski(k3_subset_1(A_47,C_48),k3_subset_1(A_47,B_49))
      | ~ r1_tarski(B_49,C_48)
      | ~ m1_subset_1(C_48,k1_zfmisc_1(A_47))
      | ~ m1_subset_1(B_49,k1_zfmisc_1(A_47)) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_169,plain,(
    ! [B_43] :
      ( k4_subset_1('#skF_1',B_43,'#skF_3') = k2_xboole_0(B_43,'#skF_3')
      | ~ m1_subset_1(B_43,k1_zfmisc_1('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_18,c_87])).

tff(c_182,plain,(
    k4_subset_1('#skF_1','#skF_2','#skF_3') = k2_xboole_0('#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_20,c_169])).

tff(c_189,plain,(
    k4_subset_1('#skF_1','#skF_2','#skF_3') = k2_xboole_0('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_182])).

tff(c_16,plain,(
    ~ r1_tarski(k3_subset_1('#skF_1',k4_subset_1('#skF_1','#skF_2','#skF_3')),k3_subset_1('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_223,plain,(
    ~ r1_tarski(k3_subset_1('#skF_1',k2_xboole_0('#skF_3','#skF_2')),k3_subset_1('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_189,c_16])).

tff(c_337,plain,
    ( ~ r1_tarski('#skF_2',k2_xboole_0('#skF_3','#skF_2'))
    | ~ m1_subset_1(k2_xboole_0('#skF_3','#skF_2'),k1_zfmisc_1('#skF_1'))
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1('#skF_1')) ),
    inference(resolution,[status(thm)],[c_331,c_223])).

tff(c_342,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_152,c_59,c_337])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n009.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 15:04:11 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.63/1.52  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.63/1.52  
% 2.63/1.52  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.63/1.53  %$ r1_tarski > m1_subset_1 > k4_subset_1 > k4_xboole_0 > k3_subset_1 > k2_xboole_0 > #nlpp > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1
% 2.63/1.53  
% 2.63/1.53  %Foreground sorts:
% 2.63/1.53  
% 2.63/1.53  
% 2.63/1.53  %Background operators:
% 2.63/1.53  
% 2.63/1.53  
% 2.63/1.53  %Foreground operators:
% 2.63/1.53  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.63/1.53  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.63/1.53  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.63/1.53  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 2.63/1.53  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 2.63/1.53  tff('#skF_2', type, '#skF_2': $i).
% 2.63/1.53  tff('#skF_3', type, '#skF_3': $i).
% 2.63/1.53  tff('#skF_1', type, '#skF_1': $i).
% 2.63/1.53  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.63/1.53  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.63/1.53  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.63/1.53  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.63/1.53  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.63/1.53  
% 2.63/1.54  tff(f_62, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => r1_tarski(k3_subset_1(A, k4_subset_1(A, B, C)), k3_subset_1(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_subset_1)).
% 2.63/1.54  tff(f_45, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 2.63/1.54  tff(f_39, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => m1_subset_1(k4_subset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k4_subset_1)).
% 2.63/1.54  tff(f_29, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 2.63/1.54  tff(f_33, axiom, (![A, B, C]: (r1_tarski(k4_xboole_0(A, B), C) => r1_tarski(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_xboole_1)).
% 2.63/1.54  tff(f_54, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (r1_tarski(B, C) <=> r1_tarski(k3_subset_1(A, C), k3_subset_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_subset_1)).
% 2.63/1.54  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 2.63/1.54  tff(c_20, plain, (m1_subset_1('#skF_2', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.63/1.54  tff(c_18, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.63/1.54  tff(c_87, plain, (![A_30, B_31, C_32]: (k4_subset_1(A_30, B_31, C_32)=k2_xboole_0(B_31, C_32) | ~m1_subset_1(C_32, k1_zfmisc_1(A_30)) | ~m1_subset_1(B_31, k1_zfmisc_1(A_30)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.63/1.54  tff(c_126, plain, (![B_39]: (k4_subset_1('#skF_1', B_39, '#skF_2')=k2_xboole_0(B_39, '#skF_2') | ~m1_subset_1(B_39, k1_zfmisc_1('#skF_1')))), inference(resolution, [status(thm)], [c_20, c_87])).
% 2.63/1.54  tff(c_133, plain, (k4_subset_1('#skF_1', '#skF_3', '#skF_2')=k2_xboole_0('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_18, c_126])).
% 2.63/1.54  tff(c_8, plain, (![A_8, B_9, C_10]: (m1_subset_1(k4_subset_1(A_8, B_9, C_10), k1_zfmisc_1(A_8)) | ~m1_subset_1(C_10, k1_zfmisc_1(A_8)) | ~m1_subset_1(B_9, k1_zfmisc_1(A_8)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.63/1.54  tff(c_148, plain, (m1_subset_1(k2_xboole_0('#skF_3', '#skF_2'), k1_zfmisc_1('#skF_1')) | ~m1_subset_1('#skF_2', k1_zfmisc_1('#skF_1')) | ~m1_subset_1('#skF_3', k1_zfmisc_1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_133, c_8])).
% 2.63/1.54  tff(c_152, plain, (m1_subset_1(k2_xboole_0('#skF_3', '#skF_2'), k1_zfmisc_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_20, c_148])).
% 2.63/1.54  tff(c_4, plain, (![A_3, B_4]: (r1_tarski(k4_xboole_0(A_3, B_4), A_3))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.63/1.54  tff(c_55, plain, (![A_23, B_24, C_25]: (r1_tarski(A_23, k2_xboole_0(B_24, C_25)) | ~r1_tarski(k4_xboole_0(A_23, B_24), C_25))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.63/1.54  tff(c_59, plain, (![A_3, B_4]: (r1_tarski(A_3, k2_xboole_0(B_4, A_3)))), inference(resolution, [status(thm)], [c_4, c_55])).
% 2.63/1.54  tff(c_331, plain, (![A_47, C_48, B_49]: (r1_tarski(k3_subset_1(A_47, C_48), k3_subset_1(A_47, B_49)) | ~r1_tarski(B_49, C_48) | ~m1_subset_1(C_48, k1_zfmisc_1(A_47)) | ~m1_subset_1(B_49, k1_zfmisc_1(A_47)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.63/1.54  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.63/1.54  tff(c_169, plain, (![B_43]: (k4_subset_1('#skF_1', B_43, '#skF_3')=k2_xboole_0(B_43, '#skF_3') | ~m1_subset_1(B_43, k1_zfmisc_1('#skF_1')))), inference(resolution, [status(thm)], [c_18, c_87])).
% 2.63/1.54  tff(c_182, plain, (k4_subset_1('#skF_1', '#skF_2', '#skF_3')=k2_xboole_0('#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_20, c_169])).
% 2.63/1.54  tff(c_189, plain, (k4_subset_1('#skF_1', '#skF_2', '#skF_3')=k2_xboole_0('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_182])).
% 2.63/1.54  tff(c_16, plain, (~r1_tarski(k3_subset_1('#skF_1', k4_subset_1('#skF_1', '#skF_2', '#skF_3')), k3_subset_1('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.63/1.54  tff(c_223, plain, (~r1_tarski(k3_subset_1('#skF_1', k2_xboole_0('#skF_3', '#skF_2')), k3_subset_1('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_189, c_16])).
% 2.63/1.54  tff(c_337, plain, (~r1_tarski('#skF_2', k2_xboole_0('#skF_3', '#skF_2')) | ~m1_subset_1(k2_xboole_0('#skF_3', '#skF_2'), k1_zfmisc_1('#skF_1')) | ~m1_subset_1('#skF_2', k1_zfmisc_1('#skF_1'))), inference(resolution, [status(thm)], [c_331, c_223])).
% 2.63/1.54  tff(c_342, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_20, c_152, c_59, c_337])).
% 2.63/1.54  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.63/1.54  
% 2.63/1.54  Inference rules
% 2.63/1.54  ----------------------
% 2.63/1.54  #Ref     : 0
% 2.63/1.54  #Sup     : 80
% 2.63/1.54  #Fact    : 0
% 2.63/1.54  #Define  : 0
% 2.63/1.54  #Split   : 0
% 2.63/1.54  #Chain   : 0
% 2.63/1.54  #Close   : 0
% 2.63/1.54  
% 2.63/1.54  Ordering : KBO
% 2.63/1.54  
% 2.63/1.54  Simplification rules
% 2.63/1.54  ----------------------
% 2.63/1.54  #Subsume      : 4
% 2.63/1.54  #Demod        : 47
% 2.63/1.54  #Tautology    : 31
% 2.63/1.54  #SimpNegUnit  : 0
% 2.63/1.54  #BackRed      : 1
% 2.63/1.54  
% 2.63/1.54  #Partial instantiations: 0
% 2.63/1.54  #Strategies tried      : 1
% 2.63/1.54  
% 2.63/1.54  Timing (in seconds)
% 2.63/1.54  ----------------------
% 2.63/1.54  Preprocessing        : 0.35
% 2.63/1.54  Parsing              : 0.17
% 2.63/1.54  CNF conversion       : 0.02
% 2.63/1.54  Main loop            : 0.36
% 2.63/1.54  Inferencing          : 0.12
% 2.63/1.54  Reduction            : 0.13
% 2.63/1.54  Demodulation         : 0.11
% 2.63/1.54  BG Simplification    : 0.02
% 2.63/1.54  Subsumption          : 0.07
% 2.63/1.54  Abstraction          : 0.02
% 2.63/1.54  MUC search           : 0.00
% 2.63/1.55  Cooper               : 0.00
% 2.63/1.55  Total                : 0.74
% 2.63/1.55  Index Insertion      : 0.00
% 2.63/1.55  Index Deletion       : 0.00
% 2.63/1.55  Index Matching       : 0.00
% 2.63/1.55  BG Taut test         : 0.00
%------------------------------------------------------------------------------
