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
% DateTime   : Thu Dec  3 09:54:56 EST 2020

% Result     : Theorem 5.30s
% Output     : CNFRefutation 5.30s
% Verified   : 
% Statistics : Number of formulae       :   49 (  59 expanded)
%              Number of leaves         :   21 (  28 expanded)
%              Depth                    :   11
%              Number of atoms          :   55 (  77 expanded)
%              Number of equality atoms :   18 (  30 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_68,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( r1_tarski(A,B)
          & k3_xboole_0(B,C) = k1_tarski(D)
          & r2_hidden(D,A) )
       => k3_xboole_0(A,C) = k1_tarski(D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_zfmisc_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => k2_xboole_0(k1_tarski(A),B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_zfmisc_1)).

tff(f_55,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_39,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(A,C) )
     => r1_tarski(A,k3_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_51,axiom,(
    ! [A,B,C] : k3_xboole_0(A,k2_xboole_0(B,C)) = k2_xboole_0(k3_xboole_0(A,B),k3_xboole_0(A,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(c_30,plain,(
    r2_hidden('#skF_4','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_476,plain,(
    ! [A_49,B_50] :
      ( k2_xboole_0(k1_tarski(A_49),B_50) = B_50
      | ~ r2_hidden(A_49,B_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_24,plain,(
    ! [A_22,B_23] : r1_tarski(A_22,k2_xboole_0(A_22,B_23)) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_503,plain,(
    ! [A_49,B_50] :
      ( r1_tarski(k1_tarski(A_49),B_50)
      | ~ r2_hidden(A_49,B_50) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_476,c_24])).

tff(c_32,plain,(
    k3_xboole_0('#skF_2','#skF_3') = k1_tarski('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_70,plain,(
    ! [B_33,A_34] : k3_xboole_0(B_33,A_34) = k3_xboole_0(A_34,B_33) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_12,plain,(
    ! [A_7,B_8] : r1_tarski(k3_xboole_0(A_7,B_8),A_7) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_127,plain,(
    ! [B_35,A_36] : r1_tarski(k3_xboole_0(B_35,A_36),A_36) ),
    inference(superposition,[status(thm),theory(equality)],[c_70,c_12])).

tff(c_136,plain,(
    r1_tarski(k1_tarski('#skF_4'),'#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_127])).

tff(c_14,plain,(
    ! [A_9,B_10,C_11] :
      ( r1_tarski(A_9,k3_xboole_0(B_10,C_11))
      | ~ r1_tarski(A_9,C_11)
      | ~ r1_tarski(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_28,plain,(
    k3_xboole_0('#skF_1','#skF_3') != k1_tarski('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_115,plain,(
    k3_xboole_0('#skF_3','#skF_2') = k1_tarski('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_70])).

tff(c_34,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_285,plain,(
    ! [A_43,B_44] :
      ( k2_xboole_0(A_43,B_44) = B_44
      | ~ r1_tarski(A_43,B_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_314,plain,(
    k2_xboole_0('#skF_1','#skF_2') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_34,c_285])).

tff(c_1375,plain,(
    ! [A_71,B_72,C_73] : k2_xboole_0(k3_xboole_0(A_71,B_72),k3_xboole_0(A_71,C_73)) = k3_xboole_0(A_71,k2_xboole_0(B_72,C_73)) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_4937,plain,(
    ! [A_125,B_126,C_127] : r1_tarski(k3_xboole_0(A_125,B_126),k3_xboole_0(A_125,k2_xboole_0(B_126,C_127))) ),
    inference(superposition,[status(thm),theory(equality)],[c_1375,c_24])).

tff(c_5406,plain,(
    ! [A_133] : r1_tarski(k3_xboole_0(A_133,'#skF_1'),k3_xboole_0(A_133,'#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_314,c_4937])).

tff(c_5455,plain,(
    r1_tarski(k3_xboole_0('#skF_3','#skF_1'),k1_tarski('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_115,c_5406])).

tff(c_5485,plain,(
    r1_tarski(k3_xboole_0('#skF_1','#skF_3'),k1_tarski('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_5455])).

tff(c_4,plain,(
    ! [B_4,A_3] :
      ( B_4 = A_3
      | ~ r1_tarski(B_4,A_3)
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_5490,plain,
    ( k3_xboole_0('#skF_1','#skF_3') = k1_tarski('#skF_4')
    | ~ r1_tarski(k1_tarski('#skF_4'),k3_xboole_0('#skF_1','#skF_3')) ),
    inference(resolution,[status(thm)],[c_5485,c_4])).

tff(c_5497,plain,(
    ~ r1_tarski(k1_tarski('#skF_4'),k3_xboole_0('#skF_1','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_5490])).

tff(c_5501,plain,
    ( ~ r1_tarski(k1_tarski('#skF_4'),'#skF_3')
    | ~ r1_tarski(k1_tarski('#skF_4'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_14,c_5497])).

tff(c_5507,plain,(
    ~ r1_tarski(k1_tarski('#skF_4'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_136,c_5501])).

tff(c_5511,plain,(
    ~ r2_hidden('#skF_4','#skF_1') ),
    inference(resolution,[status(thm)],[c_503,c_5507])).

tff(c_5515,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_5511])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n022.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 15:32:25 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.30/2.00  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.30/2.00  
% 5.30/2.00  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.30/2.00  %$ r2_hidden > r1_tarski > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 5.30/2.00  
% 5.30/2.00  %Foreground sorts:
% 5.30/2.00  
% 5.30/2.00  
% 5.30/2.00  %Background operators:
% 5.30/2.00  
% 5.30/2.00  
% 5.30/2.00  %Foreground operators:
% 5.30/2.00  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.30/2.00  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.30/2.00  tff(k1_tarski, type, k1_tarski: $i > $i).
% 5.30/2.00  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.30/2.00  tff('#skF_2', type, '#skF_2': $i).
% 5.30/2.00  tff('#skF_3', type, '#skF_3': $i).
% 5.30/2.00  tff('#skF_1', type, '#skF_1': $i).
% 5.30/2.00  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.30/2.00  tff('#skF_4', type, '#skF_4': $i).
% 5.30/2.00  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.30/2.00  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 5.30/2.00  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 5.30/2.00  
% 5.30/2.01  tff(f_68, negated_conjecture, ~(![A, B, C, D]: (((r1_tarski(A, B) & (k3_xboole_0(B, C) = k1_tarski(D))) & r2_hidden(D, A)) => (k3_xboole_0(A, C) = k1_tarski(D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_zfmisc_1)).
% 5.30/2.01  tff(f_59, axiom, (![A, B]: (r2_hidden(A, B) => (k2_xboole_0(k1_tarski(A), B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_zfmisc_1)).
% 5.30/2.01  tff(f_55, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 5.30/2.01  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 5.30/2.01  tff(f_39, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 5.30/2.01  tff(f_45, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(A, C)) => r1_tarski(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t19_xboole_1)).
% 5.30/2.01  tff(f_37, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 5.30/2.01  tff(f_51, axiom, (![A, B, C]: (k3_xboole_0(A, k2_xboole_0(B, C)) = k2_xboole_0(k3_xboole_0(A, B), k3_xboole_0(A, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t23_xboole_1)).
% 5.30/2.01  tff(f_33, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 5.30/2.01  tff(c_30, plain, (r2_hidden('#skF_4', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_68])).
% 5.30/2.01  tff(c_476, plain, (![A_49, B_50]: (k2_xboole_0(k1_tarski(A_49), B_50)=B_50 | ~r2_hidden(A_49, B_50))), inference(cnfTransformation, [status(thm)], [f_59])).
% 5.30/2.01  tff(c_24, plain, (![A_22, B_23]: (r1_tarski(A_22, k2_xboole_0(A_22, B_23)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 5.30/2.01  tff(c_503, plain, (![A_49, B_50]: (r1_tarski(k1_tarski(A_49), B_50) | ~r2_hidden(A_49, B_50))), inference(superposition, [status(thm), theory('equality')], [c_476, c_24])).
% 5.30/2.01  tff(c_32, plain, (k3_xboole_0('#skF_2', '#skF_3')=k1_tarski('#skF_4')), inference(cnfTransformation, [status(thm)], [f_68])).
% 5.30/2.01  tff(c_70, plain, (![B_33, A_34]: (k3_xboole_0(B_33, A_34)=k3_xboole_0(A_34, B_33))), inference(cnfTransformation, [status(thm)], [f_27])).
% 5.30/2.01  tff(c_12, plain, (![A_7, B_8]: (r1_tarski(k3_xboole_0(A_7, B_8), A_7))), inference(cnfTransformation, [status(thm)], [f_39])).
% 5.30/2.01  tff(c_127, plain, (![B_35, A_36]: (r1_tarski(k3_xboole_0(B_35, A_36), A_36))), inference(superposition, [status(thm), theory('equality')], [c_70, c_12])).
% 5.30/2.01  tff(c_136, plain, (r1_tarski(k1_tarski('#skF_4'), '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_32, c_127])).
% 5.30/2.01  tff(c_14, plain, (![A_9, B_10, C_11]: (r1_tarski(A_9, k3_xboole_0(B_10, C_11)) | ~r1_tarski(A_9, C_11) | ~r1_tarski(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_45])).
% 5.30/2.01  tff(c_28, plain, (k3_xboole_0('#skF_1', '#skF_3')!=k1_tarski('#skF_4')), inference(cnfTransformation, [status(thm)], [f_68])).
% 5.30/2.01  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 5.30/2.01  tff(c_115, plain, (k3_xboole_0('#skF_3', '#skF_2')=k1_tarski('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_32, c_70])).
% 5.30/2.01  tff(c_34, plain, (r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_68])).
% 5.30/2.01  tff(c_285, plain, (![A_43, B_44]: (k2_xboole_0(A_43, B_44)=B_44 | ~r1_tarski(A_43, B_44))), inference(cnfTransformation, [status(thm)], [f_37])).
% 5.30/2.01  tff(c_314, plain, (k2_xboole_0('#skF_1', '#skF_2')='#skF_2'), inference(resolution, [status(thm)], [c_34, c_285])).
% 5.30/2.01  tff(c_1375, plain, (![A_71, B_72, C_73]: (k2_xboole_0(k3_xboole_0(A_71, B_72), k3_xboole_0(A_71, C_73))=k3_xboole_0(A_71, k2_xboole_0(B_72, C_73)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 5.30/2.01  tff(c_4937, plain, (![A_125, B_126, C_127]: (r1_tarski(k3_xboole_0(A_125, B_126), k3_xboole_0(A_125, k2_xboole_0(B_126, C_127))))), inference(superposition, [status(thm), theory('equality')], [c_1375, c_24])).
% 5.30/2.02  tff(c_5406, plain, (![A_133]: (r1_tarski(k3_xboole_0(A_133, '#skF_1'), k3_xboole_0(A_133, '#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_314, c_4937])).
% 5.30/2.02  tff(c_5455, plain, (r1_tarski(k3_xboole_0('#skF_3', '#skF_1'), k1_tarski('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_115, c_5406])).
% 5.30/2.02  tff(c_5485, plain, (r1_tarski(k3_xboole_0('#skF_1', '#skF_3'), k1_tarski('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_5455])).
% 5.30/2.02  tff(c_4, plain, (![B_4, A_3]: (B_4=A_3 | ~r1_tarski(B_4, A_3) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 5.30/2.02  tff(c_5490, plain, (k3_xboole_0('#skF_1', '#skF_3')=k1_tarski('#skF_4') | ~r1_tarski(k1_tarski('#skF_4'), k3_xboole_0('#skF_1', '#skF_3'))), inference(resolution, [status(thm)], [c_5485, c_4])).
% 5.30/2.02  tff(c_5497, plain, (~r1_tarski(k1_tarski('#skF_4'), k3_xboole_0('#skF_1', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_28, c_5490])).
% 5.30/2.02  tff(c_5501, plain, (~r1_tarski(k1_tarski('#skF_4'), '#skF_3') | ~r1_tarski(k1_tarski('#skF_4'), '#skF_1')), inference(resolution, [status(thm)], [c_14, c_5497])).
% 5.30/2.02  tff(c_5507, plain, (~r1_tarski(k1_tarski('#skF_4'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_136, c_5501])).
% 5.30/2.02  tff(c_5511, plain, (~r2_hidden('#skF_4', '#skF_1')), inference(resolution, [status(thm)], [c_503, c_5507])).
% 5.30/2.02  tff(c_5515, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_30, c_5511])).
% 5.30/2.02  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.30/2.02  
% 5.30/2.02  Inference rules
% 5.30/2.02  ----------------------
% 5.30/2.02  #Ref     : 0
% 5.30/2.02  #Sup     : 1370
% 5.30/2.02  #Fact    : 0
% 5.30/2.02  #Define  : 0
% 5.30/2.02  #Split   : 3
% 5.30/2.02  #Chain   : 0
% 5.30/2.02  #Close   : 0
% 5.30/2.02  
% 5.30/2.02  Ordering : KBO
% 5.30/2.02  
% 5.30/2.02  Simplification rules
% 5.30/2.02  ----------------------
% 5.30/2.02  #Subsume      : 22
% 5.30/2.02  #Demod        : 1150
% 5.30/2.02  #Tautology    : 862
% 5.30/2.02  #SimpNegUnit  : 1
% 5.30/2.02  #BackRed      : 1
% 5.30/2.02  
% 5.30/2.02  #Partial instantiations: 0
% 5.30/2.02  #Strategies tried      : 1
% 5.30/2.02  
% 5.30/2.02  Timing (in seconds)
% 5.30/2.02  ----------------------
% 5.30/2.02  Preprocessing        : 0.30
% 5.30/2.02  Parsing              : 0.16
% 5.30/2.02  CNF conversion       : 0.02
% 5.30/2.02  Main loop            : 0.97
% 5.30/2.02  Inferencing          : 0.28
% 5.30/2.02  Reduction            : 0.45
% 5.30/2.02  Demodulation         : 0.37
% 5.30/2.02  BG Simplification    : 0.03
% 5.30/2.02  Subsumption          : 0.15
% 5.30/2.02  Abstraction          : 0.05
% 5.30/2.02  MUC search           : 0.00
% 5.30/2.02  Cooper               : 0.00
% 5.30/2.02  Total                : 1.30
% 5.30/2.02  Index Insertion      : 0.00
% 5.30/2.02  Index Deletion       : 0.00
% 5.30/2.02  Index Matching       : 0.00
% 5.30/2.02  BG Taut test         : 0.00
%------------------------------------------------------------------------------
