%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:53:30 EST 2020

% Result     : Theorem 1.84s
% Output     : CNFRefutation 1.84s
% Verified   : 
% Statistics : Number of formulae       :   41 (  48 expanded)
%              Number of leaves         :   21 (  24 expanded)
%              Depth                    :    8
%              Number of atoms          :   47 (  61 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_zfmisc_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_37,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(A,k2_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_xboole_1)).

tff(f_45,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ~ ( ~ r1_xboole_0(A,k3_xboole_0(B,C))
        & r1_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_xboole_1)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k5_xboole_0(B,C))
    <=> ( r1_tarski(A,k2_xboole_0(B,C))
        & r1_xboole_0(A,k3_xboole_0(B,C)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t107_xboole_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => r1_tarski(k1_zfmisc_1(A),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_zfmisc_1)).

tff(f_53,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),k5_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t96_xboole_1)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(C,B) )
     => r1_tarski(k2_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_xboole_1)).

tff(f_60,negated_conjecture,(
    ~ ! [A,B] : r1_tarski(k2_xboole_0(k1_zfmisc_1(k4_xboole_0(A,B)),k1_zfmisc_1(k4_xboole_0(B,A))),k1_zfmisc_1(k5_xboole_0(A,B))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t86_zfmisc_1)).

tff(c_10,plain,(
    ! [A_7,B_8] : r1_tarski(k4_xboole_0(A_7,B_8),A_7) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_8,plain,(
    ! [A_4,C_6,B_5] :
      ( r1_tarski(A_4,k2_xboole_0(C_6,B_5))
      | ~ r1_tarski(A_4,B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_14,plain,(
    ! [A_12,B_13] : r1_xboole_0(k4_xboole_0(A_12,B_13),B_13) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_12,plain,(
    ! [A_9,B_10,C_11] :
      ( ~ r1_xboole_0(A_9,B_10)
      | r1_xboole_0(A_9,k3_xboole_0(B_10,C_11)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_52,plain,(
    ! [A_49,B_50,C_51] :
      ( r1_tarski(A_49,k5_xboole_0(B_50,C_51))
      | ~ r1_xboole_0(A_49,k3_xboole_0(B_50,C_51))
      | ~ r1_tarski(A_49,k2_xboole_0(B_50,C_51)) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_64,plain,(
    ! [A_9,B_10,C_11] :
      ( r1_tarski(A_9,k5_xboole_0(B_10,C_11))
      | ~ r1_tarski(A_9,k2_xboole_0(B_10,C_11))
      | ~ r1_xboole_0(A_9,B_10) ) ),
    inference(resolution,[status(thm)],[c_12,c_52])).

tff(c_20,plain,(
    ! [A_19,B_20] :
      ( r1_tarski(k1_zfmisc_1(A_19),k1_zfmisc_1(B_20))
      | ~ r1_tarski(A_19,B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_18,plain,(
    ! [A_17,B_18] : r1_tarski(k4_xboole_0(A_17,B_18),k5_xboole_0(A_17,B_18)) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_42,plain,(
    ! [A_46,C_47,B_48] :
      ( r1_tarski(k2_xboole_0(A_46,C_47),B_48)
      | ~ r1_tarski(C_47,B_48)
      | ~ r1_tarski(A_46,B_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_22,plain,(
    ~ r1_tarski(k2_xboole_0(k1_zfmisc_1(k4_xboole_0('#skF_1','#skF_2')),k1_zfmisc_1(k4_xboole_0('#skF_2','#skF_1'))),k1_zfmisc_1(k5_xboole_0('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_50,plain,
    ( ~ r1_tarski(k1_zfmisc_1(k4_xboole_0('#skF_2','#skF_1')),k1_zfmisc_1(k5_xboole_0('#skF_1','#skF_2')))
    | ~ r1_tarski(k1_zfmisc_1(k4_xboole_0('#skF_1','#skF_2')),k1_zfmisc_1(k5_xboole_0('#skF_1','#skF_2'))) ),
    inference(resolution,[status(thm)],[c_42,c_22])).

tff(c_77,plain,(
    ~ r1_tarski(k1_zfmisc_1(k4_xboole_0('#skF_1','#skF_2')),k1_zfmisc_1(k5_xboole_0('#skF_1','#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_50])).

tff(c_80,plain,(
    ~ r1_tarski(k4_xboole_0('#skF_1','#skF_2'),k5_xboole_0('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_20,c_77])).

tff(c_84,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_80])).

tff(c_85,plain,(
    ~ r1_tarski(k1_zfmisc_1(k4_xboole_0('#skF_2','#skF_1')),k1_zfmisc_1(k5_xboole_0('#skF_1','#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_90,plain,(
    ~ r1_tarski(k4_xboole_0('#skF_2','#skF_1'),k5_xboole_0('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_20,c_85])).

tff(c_93,plain,
    ( ~ r1_tarski(k4_xboole_0('#skF_2','#skF_1'),k2_xboole_0('#skF_1','#skF_2'))
    | ~ r1_xboole_0(k4_xboole_0('#skF_2','#skF_1'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_64,c_90])).

tff(c_96,plain,(
    ~ r1_tarski(k4_xboole_0('#skF_2','#skF_1'),k2_xboole_0('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_93])).

tff(c_99,plain,(
    ~ r1_tarski(k4_xboole_0('#skF_2','#skF_1'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_8,c_96])).

tff(c_103,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_99])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n011.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 14:23:42 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.84/1.18  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.84/1.18  
% 1.84/1.18  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.84/1.19  %$ r1_xboole_0 > r1_tarski > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_zfmisc_1 > #skF_2 > #skF_1
% 1.84/1.19  
% 1.84/1.19  %Foreground sorts:
% 1.84/1.19  
% 1.84/1.19  
% 1.84/1.19  %Background operators:
% 1.84/1.19  
% 1.84/1.19  
% 1.84/1.19  %Foreground operators:
% 1.84/1.19  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.84/1.19  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.84/1.19  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 1.84/1.19  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.84/1.19  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.84/1.19  tff('#skF_2', type, '#skF_2': $i).
% 1.84/1.19  tff('#skF_1', type, '#skF_1': $i).
% 1.84/1.19  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.84/1.19  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.84/1.19  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.84/1.19  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.84/1.19  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.84/1.19  
% 1.84/1.20  tff(f_37, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 1.84/1.20  tff(f_35, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(A, k2_xboole_0(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_xboole_1)).
% 1.84/1.20  tff(f_45, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_xboole_1)).
% 1.84/1.20  tff(f_43, axiom, (![A, B, C]: ~(~r1_xboole_0(A, k3_xboole_0(B, C)) & r1_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t74_xboole_1)).
% 1.84/1.20  tff(f_31, axiom, (![A, B, C]: (r1_tarski(A, k5_xboole_0(B, C)) <=> (r1_tarski(A, k2_xboole_0(B, C)) & r1_xboole_0(A, k3_xboole_0(B, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t107_xboole_1)).
% 1.84/1.20  tff(f_57, axiom, (![A, B]: (r1_tarski(A, B) => r1_tarski(k1_zfmisc_1(A), k1_zfmisc_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_zfmisc_1)).
% 1.84/1.20  tff(f_53, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), k5_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t96_xboole_1)).
% 1.84/1.20  tff(f_51, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(C, B)) => r1_tarski(k2_xboole_0(A, C), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_xboole_1)).
% 1.84/1.20  tff(f_60, negated_conjecture, ~(![A, B]: r1_tarski(k2_xboole_0(k1_zfmisc_1(k4_xboole_0(A, B)), k1_zfmisc_1(k4_xboole_0(B, A))), k1_zfmisc_1(k5_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t86_zfmisc_1)).
% 1.84/1.20  tff(c_10, plain, (![A_7, B_8]: (r1_tarski(k4_xboole_0(A_7, B_8), A_7))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.84/1.20  tff(c_8, plain, (![A_4, C_6, B_5]: (r1_tarski(A_4, k2_xboole_0(C_6, B_5)) | ~r1_tarski(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.84/1.20  tff(c_14, plain, (![A_12, B_13]: (r1_xboole_0(k4_xboole_0(A_12, B_13), B_13))), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.84/1.20  tff(c_12, plain, (![A_9, B_10, C_11]: (~r1_xboole_0(A_9, B_10) | r1_xboole_0(A_9, k3_xboole_0(B_10, C_11)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.84/1.20  tff(c_52, plain, (![A_49, B_50, C_51]: (r1_tarski(A_49, k5_xboole_0(B_50, C_51)) | ~r1_xboole_0(A_49, k3_xboole_0(B_50, C_51)) | ~r1_tarski(A_49, k2_xboole_0(B_50, C_51)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.84/1.20  tff(c_64, plain, (![A_9, B_10, C_11]: (r1_tarski(A_9, k5_xboole_0(B_10, C_11)) | ~r1_tarski(A_9, k2_xboole_0(B_10, C_11)) | ~r1_xboole_0(A_9, B_10))), inference(resolution, [status(thm)], [c_12, c_52])).
% 1.84/1.20  tff(c_20, plain, (![A_19, B_20]: (r1_tarski(k1_zfmisc_1(A_19), k1_zfmisc_1(B_20)) | ~r1_tarski(A_19, B_20))), inference(cnfTransformation, [status(thm)], [f_57])).
% 1.84/1.20  tff(c_18, plain, (![A_17, B_18]: (r1_tarski(k4_xboole_0(A_17, B_18), k5_xboole_0(A_17, B_18)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 1.84/1.20  tff(c_42, plain, (![A_46, C_47, B_48]: (r1_tarski(k2_xboole_0(A_46, C_47), B_48) | ~r1_tarski(C_47, B_48) | ~r1_tarski(A_46, B_48))), inference(cnfTransformation, [status(thm)], [f_51])).
% 1.84/1.20  tff(c_22, plain, (~r1_tarski(k2_xboole_0(k1_zfmisc_1(k4_xboole_0('#skF_1', '#skF_2')), k1_zfmisc_1(k4_xboole_0('#skF_2', '#skF_1'))), k1_zfmisc_1(k5_xboole_0('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_60])).
% 1.84/1.20  tff(c_50, plain, (~r1_tarski(k1_zfmisc_1(k4_xboole_0('#skF_2', '#skF_1')), k1_zfmisc_1(k5_xboole_0('#skF_1', '#skF_2'))) | ~r1_tarski(k1_zfmisc_1(k4_xboole_0('#skF_1', '#skF_2')), k1_zfmisc_1(k5_xboole_0('#skF_1', '#skF_2')))), inference(resolution, [status(thm)], [c_42, c_22])).
% 1.84/1.20  tff(c_77, plain, (~r1_tarski(k1_zfmisc_1(k4_xboole_0('#skF_1', '#skF_2')), k1_zfmisc_1(k5_xboole_0('#skF_1', '#skF_2')))), inference(splitLeft, [status(thm)], [c_50])).
% 1.84/1.20  tff(c_80, plain, (~r1_tarski(k4_xboole_0('#skF_1', '#skF_2'), k5_xboole_0('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_20, c_77])).
% 1.84/1.20  tff(c_84, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_18, c_80])).
% 1.84/1.20  tff(c_85, plain, (~r1_tarski(k1_zfmisc_1(k4_xboole_0('#skF_2', '#skF_1')), k1_zfmisc_1(k5_xboole_0('#skF_1', '#skF_2')))), inference(splitRight, [status(thm)], [c_50])).
% 1.84/1.20  tff(c_90, plain, (~r1_tarski(k4_xboole_0('#skF_2', '#skF_1'), k5_xboole_0('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_20, c_85])).
% 1.84/1.20  tff(c_93, plain, (~r1_tarski(k4_xboole_0('#skF_2', '#skF_1'), k2_xboole_0('#skF_1', '#skF_2')) | ~r1_xboole_0(k4_xboole_0('#skF_2', '#skF_1'), '#skF_1')), inference(resolution, [status(thm)], [c_64, c_90])).
% 1.84/1.20  tff(c_96, plain, (~r1_tarski(k4_xboole_0('#skF_2', '#skF_1'), k2_xboole_0('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_93])).
% 1.84/1.20  tff(c_99, plain, (~r1_tarski(k4_xboole_0('#skF_2', '#skF_1'), '#skF_2')), inference(resolution, [status(thm)], [c_8, c_96])).
% 1.84/1.20  tff(c_103, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_10, c_99])).
% 1.84/1.20  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.84/1.20  
% 1.84/1.20  Inference rules
% 1.84/1.20  ----------------------
% 1.84/1.20  #Ref     : 0
% 1.84/1.20  #Sup     : 13
% 1.84/1.20  #Fact    : 0
% 1.84/1.20  #Define  : 0
% 1.84/1.20  #Split   : 1
% 1.84/1.20  #Chain   : 0
% 1.84/1.20  #Close   : 0
% 1.84/1.20  
% 1.84/1.20  Ordering : KBO
% 1.84/1.20  
% 1.84/1.20  Simplification rules
% 1.84/1.20  ----------------------
% 1.84/1.20  #Subsume      : 0
% 1.84/1.20  #Demod        : 3
% 1.84/1.20  #Tautology    : 3
% 1.84/1.20  #SimpNegUnit  : 0
% 1.84/1.20  #BackRed      : 0
% 1.84/1.20  
% 1.84/1.20  #Partial instantiations: 0
% 1.84/1.20  #Strategies tried      : 1
% 1.84/1.20  
% 1.84/1.20  Timing (in seconds)
% 1.84/1.20  ----------------------
% 1.84/1.20  Preprocessing        : 0.27
% 1.84/1.20  Parsing              : 0.15
% 1.84/1.20  CNF conversion       : 0.02
% 1.84/1.20  Main loop            : 0.16
% 1.84/1.20  Inferencing          : 0.07
% 1.84/1.20  Reduction            : 0.04
% 1.84/1.20  Demodulation         : 0.03
% 1.84/1.20  BG Simplification    : 0.01
% 1.84/1.20  Subsumption          : 0.03
% 1.84/1.20  Abstraction          : 0.01
% 1.84/1.20  MUC search           : 0.00
% 1.84/1.20  Cooper               : 0.00
% 1.84/1.20  Total                : 0.46
% 1.84/1.20  Index Insertion      : 0.00
% 1.84/1.20  Index Deletion       : 0.00
% 1.84/1.20  Index Matching       : 0.00
% 1.84/1.20  BG Taut test         : 0.00
%------------------------------------------------------------------------------
