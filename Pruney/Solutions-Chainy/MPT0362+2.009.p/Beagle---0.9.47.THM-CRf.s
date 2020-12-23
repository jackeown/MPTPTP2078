%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:56:33 EST 2020

% Result     : Theorem 13.05s
% Output     : CNFRefutation 13.05s
% Verified   : 
% Statistics : Number of formulae       :   45 (  60 expanded)
%              Number of leaves         :   22 (  30 expanded)
%              Depth                    :    7
%              Number of atoms          :   50 (  80 expanded)
%              Number of equality atoms :   13 (  20 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > m1_subset_1 > k9_subset_1 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_43,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k4_xboole_0(B,C))
     => ( r1_tarski(A,B)
        & r1_xboole_0(A,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_xboole_1)).

tff(f_63,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => ! [C] :
            ( m1_subset_1(C,k1_zfmisc_1(A))
           => r1_tarski(k3_subset_1(A,B),k3_subset_1(A,k9_subset_1(A,B,C))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_subset_1)).

tff(f_55,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => m1_subset_1(k9_subset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k9_subset_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(k4_xboole_0(C,B),k4_xboole_0(C,A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_xboole_1)).

tff(c_78,plain,(
    ! [A_39,B_40] : k4_xboole_0(A_39,k4_xboole_0(A_39,B_40)) = k3_xboole_0(A_39,B_40) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_29,plain,(
    ! [A_21,B_22,C_23] :
      ( r1_tarski(A_21,B_22)
      | ~ r1_tarski(A_21,k4_xboole_0(B_22,C_23)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_34,plain,(
    ! [B_22,C_23] : r1_tarski(k4_xboole_0(B_22,C_23),B_22) ),
    inference(resolution,[status(thm)],[c_6,c_29])).

tff(c_107,plain,(
    ! [A_39,B_40] : r1_tarski(k3_xboole_0(A_39,B_40),A_39) ),
    inference(superposition,[status(thm),theory(equality)],[c_78,c_34])).

tff(c_24,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_327,plain,(
    ! [A_67,B_68,C_69] :
      ( k9_subset_1(A_67,B_68,C_69) = k3_xboole_0(B_68,C_69)
      | ~ m1_subset_1(C_69,k1_zfmisc_1(A_67)) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_335,plain,(
    ! [B_68] : k9_subset_1('#skF_1',B_68,'#skF_3') = k3_xboole_0(B_68,'#skF_3') ),
    inference(resolution,[status(thm)],[c_24,c_327])).

tff(c_288,plain,(
    ! [A_59,B_60,C_61] :
      ( m1_subset_1(k9_subset_1(A_59,B_60,C_61),k1_zfmisc_1(A_59))
      | ~ m1_subset_1(C_61,k1_zfmisc_1(A_59)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_16,plain,(
    ! [A_11,B_12] :
      ( k4_xboole_0(A_11,B_12) = k3_subset_1(A_11,B_12)
      | ~ m1_subset_1(B_12,k1_zfmisc_1(A_11)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_1400,plain,(
    ! [A_156,B_157,C_158] :
      ( k4_xboole_0(A_156,k9_subset_1(A_156,B_157,C_158)) = k3_subset_1(A_156,k9_subset_1(A_156,B_157,C_158))
      | ~ m1_subset_1(C_158,k1_zfmisc_1(A_156)) ) ),
    inference(resolution,[status(thm)],[c_288,c_16])).

tff(c_1408,plain,(
    ! [B_157] : k4_xboole_0('#skF_1',k9_subset_1('#skF_1',B_157,'#skF_3')) = k3_subset_1('#skF_1',k9_subset_1('#skF_1',B_157,'#skF_3')) ),
    inference(resolution,[status(thm)],[c_24,c_1400])).

tff(c_2124,plain,(
    ! [B_224] : k4_xboole_0('#skF_1',k3_xboole_0(B_224,'#skF_3')) = k3_subset_1('#skF_1',k3_xboole_0(B_224,'#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_335,c_335,c_1408])).

tff(c_26,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_196,plain,(
    ! [A_57,B_58] :
      ( k4_xboole_0(A_57,B_58) = k3_subset_1(A_57,B_58)
      | ~ m1_subset_1(B_58,k1_zfmisc_1(A_57)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_204,plain,(
    k4_xboole_0('#skF_1','#skF_2') = k3_subset_1('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_26,c_196])).

tff(c_12,plain,(
    ! [C_8,B_7,A_6] :
      ( r1_tarski(k4_xboole_0(C_8,B_7),k4_xboole_0(C_8,A_6))
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_254,plain,(
    ! [A_6] :
      ( r1_tarski(k3_subset_1('#skF_1','#skF_2'),k4_xboole_0('#skF_1',A_6))
      | ~ r1_tarski(A_6,'#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_204,c_12])).

tff(c_23880,plain,(
    ! [B_1311] :
      ( r1_tarski(k3_subset_1('#skF_1','#skF_2'),k3_subset_1('#skF_1',k3_xboole_0(B_1311,'#skF_3')))
      | ~ r1_tarski(k3_xboole_0(B_1311,'#skF_3'),'#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2124,c_254])).

tff(c_22,plain,(
    ~ r1_tarski(k3_subset_1('#skF_1','#skF_2'),k3_subset_1('#skF_1',k9_subset_1('#skF_1','#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_337,plain,(
    ~ r1_tarski(k3_subset_1('#skF_1','#skF_2'),k3_subset_1('#skF_1',k3_xboole_0('#skF_2','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_335,c_22])).

tff(c_23891,plain,(
    ~ r1_tarski(k3_xboole_0('#skF_2','#skF_3'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_23880,c_337])).

tff(c_23901,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_107,c_23891])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.05/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.05/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:58:34 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 13.05/6.50  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 13.05/6.50  
% 13.05/6.50  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 13.05/6.51  %$ r1_xboole_0 > r1_tarski > m1_subset_1 > k9_subset_1 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1
% 13.05/6.51  
% 13.05/6.51  %Foreground sorts:
% 13.05/6.51  
% 13.05/6.51  
% 13.05/6.51  %Background operators:
% 13.05/6.51  
% 13.05/6.51  
% 13.05/6.51  %Foreground operators:
% 13.05/6.51  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 13.05/6.51  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 13.05/6.51  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 13.05/6.51  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 13.05/6.51  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 13.05/6.51  tff('#skF_2', type, '#skF_2': $i).
% 13.05/6.51  tff('#skF_3', type, '#skF_3': $i).
% 13.05/6.51  tff('#skF_1', type, '#skF_1': $i).
% 13.05/6.51  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 13.05/6.51  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 13.05/6.51  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 13.05/6.51  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 13.05/6.51  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 13.05/6.51  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 13.05/6.51  
% 13.05/6.52  tff(f_43, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 13.05/6.52  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 13.05/6.52  tff(f_37, axiom, (![A, B, C]: (r1_tarski(A, k4_xboole_0(B, C)) => (r1_tarski(A, B) & r1_xboole_0(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t106_xboole_1)).
% 13.05/6.52  tff(f_63, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => r1_tarski(k3_subset_1(A, B), k3_subset_1(A, k9_subset_1(A, B, C))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t42_subset_1)).
% 13.05/6.52  tff(f_55, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 13.05/6.52  tff(f_51, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => m1_subset_1(k9_subset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k9_subset_1)).
% 13.05/6.52  tff(f_47, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 13.05/6.52  tff(f_41, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(k4_xboole_0(C, B), k4_xboole_0(C, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t34_xboole_1)).
% 13.05/6.52  tff(c_78, plain, (![A_39, B_40]: (k4_xboole_0(A_39, k4_xboole_0(A_39, B_40))=k3_xboole_0(A_39, B_40))), inference(cnfTransformation, [status(thm)], [f_43])).
% 13.05/6.52  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 13.05/6.52  tff(c_29, plain, (![A_21, B_22, C_23]: (r1_tarski(A_21, B_22) | ~r1_tarski(A_21, k4_xboole_0(B_22, C_23)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 13.05/6.52  tff(c_34, plain, (![B_22, C_23]: (r1_tarski(k4_xboole_0(B_22, C_23), B_22))), inference(resolution, [status(thm)], [c_6, c_29])).
% 13.05/6.52  tff(c_107, plain, (![A_39, B_40]: (r1_tarski(k3_xboole_0(A_39, B_40), A_39))), inference(superposition, [status(thm), theory('equality')], [c_78, c_34])).
% 13.05/6.52  tff(c_24, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_63])).
% 13.05/6.52  tff(c_327, plain, (![A_67, B_68, C_69]: (k9_subset_1(A_67, B_68, C_69)=k3_xboole_0(B_68, C_69) | ~m1_subset_1(C_69, k1_zfmisc_1(A_67)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 13.05/6.52  tff(c_335, plain, (![B_68]: (k9_subset_1('#skF_1', B_68, '#skF_3')=k3_xboole_0(B_68, '#skF_3'))), inference(resolution, [status(thm)], [c_24, c_327])).
% 13.05/6.52  tff(c_288, plain, (![A_59, B_60, C_61]: (m1_subset_1(k9_subset_1(A_59, B_60, C_61), k1_zfmisc_1(A_59)) | ~m1_subset_1(C_61, k1_zfmisc_1(A_59)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 13.05/6.52  tff(c_16, plain, (![A_11, B_12]: (k4_xboole_0(A_11, B_12)=k3_subset_1(A_11, B_12) | ~m1_subset_1(B_12, k1_zfmisc_1(A_11)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 13.05/6.52  tff(c_1400, plain, (![A_156, B_157, C_158]: (k4_xboole_0(A_156, k9_subset_1(A_156, B_157, C_158))=k3_subset_1(A_156, k9_subset_1(A_156, B_157, C_158)) | ~m1_subset_1(C_158, k1_zfmisc_1(A_156)))), inference(resolution, [status(thm)], [c_288, c_16])).
% 13.05/6.52  tff(c_1408, plain, (![B_157]: (k4_xboole_0('#skF_1', k9_subset_1('#skF_1', B_157, '#skF_3'))=k3_subset_1('#skF_1', k9_subset_1('#skF_1', B_157, '#skF_3')))), inference(resolution, [status(thm)], [c_24, c_1400])).
% 13.05/6.52  tff(c_2124, plain, (![B_224]: (k4_xboole_0('#skF_1', k3_xboole_0(B_224, '#skF_3'))=k3_subset_1('#skF_1', k3_xboole_0(B_224, '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_335, c_335, c_1408])).
% 13.05/6.52  tff(c_26, plain, (m1_subset_1('#skF_2', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_63])).
% 13.05/6.52  tff(c_196, plain, (![A_57, B_58]: (k4_xboole_0(A_57, B_58)=k3_subset_1(A_57, B_58) | ~m1_subset_1(B_58, k1_zfmisc_1(A_57)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 13.05/6.52  tff(c_204, plain, (k4_xboole_0('#skF_1', '#skF_2')=k3_subset_1('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_26, c_196])).
% 13.05/6.52  tff(c_12, plain, (![C_8, B_7, A_6]: (r1_tarski(k4_xboole_0(C_8, B_7), k4_xboole_0(C_8, A_6)) | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_41])).
% 13.05/6.52  tff(c_254, plain, (![A_6]: (r1_tarski(k3_subset_1('#skF_1', '#skF_2'), k4_xboole_0('#skF_1', A_6)) | ~r1_tarski(A_6, '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_204, c_12])).
% 13.05/6.52  tff(c_23880, plain, (![B_1311]: (r1_tarski(k3_subset_1('#skF_1', '#skF_2'), k3_subset_1('#skF_1', k3_xboole_0(B_1311, '#skF_3'))) | ~r1_tarski(k3_xboole_0(B_1311, '#skF_3'), '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_2124, c_254])).
% 13.05/6.52  tff(c_22, plain, (~r1_tarski(k3_subset_1('#skF_1', '#skF_2'), k3_subset_1('#skF_1', k9_subset_1('#skF_1', '#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_63])).
% 13.05/6.52  tff(c_337, plain, (~r1_tarski(k3_subset_1('#skF_1', '#skF_2'), k3_subset_1('#skF_1', k3_xboole_0('#skF_2', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_335, c_22])).
% 13.05/6.52  tff(c_23891, plain, (~r1_tarski(k3_xboole_0('#skF_2', '#skF_3'), '#skF_2')), inference(resolution, [status(thm)], [c_23880, c_337])).
% 13.05/6.52  tff(c_23901, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_107, c_23891])).
% 13.05/6.52  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 13.05/6.52  
% 13.05/6.52  Inference rules
% 13.05/6.52  ----------------------
% 13.05/6.52  #Ref     : 0
% 13.05/6.52  #Sup     : 5898
% 13.05/6.52  #Fact    : 0
% 13.05/6.52  #Define  : 0
% 13.05/6.52  #Split   : 16
% 13.05/6.52  #Chain   : 0
% 13.05/6.52  #Close   : 0
% 13.05/6.52  
% 13.05/6.52  Ordering : KBO
% 13.05/6.52  
% 13.05/6.52  Simplification rules
% 13.05/6.52  ----------------------
% 13.05/6.52  #Subsume      : 172
% 13.05/6.52  #Demod        : 2035
% 13.05/6.52  #Tautology    : 1350
% 13.05/6.52  #SimpNegUnit  : 0
% 13.05/6.52  #BackRed      : 4
% 13.05/6.52  
% 13.05/6.52  #Partial instantiations: 0
% 13.05/6.52  #Strategies tried      : 1
% 13.05/6.52  
% 13.05/6.52  Timing (in seconds)
% 13.05/6.52  ----------------------
% 13.05/6.52  Preprocessing        : 0.28
% 13.05/6.52  Parsing              : 0.15
% 13.05/6.52  CNF conversion       : 0.02
% 13.05/6.52  Main loop            : 5.48
% 13.05/6.52  Inferencing          : 0.98
% 13.05/6.52  Reduction            : 2.65
% 13.05/6.52  Demodulation         : 2.28
% 13.05/6.52  BG Simplification    : 0.10
% 13.05/6.52  Subsumption          : 1.43
% 13.05/6.52  Abstraction          : 0.11
% 13.05/6.52  MUC search           : 0.00
% 13.05/6.52  Cooper               : 0.00
% 13.05/6.52  Total                : 5.79
% 13.05/6.52  Index Insertion      : 0.00
% 13.05/6.52  Index Deletion       : 0.00
% 13.05/6.52  Index Matching       : 0.00
% 13.05/6.52  BG Taut test         : 0.00
%------------------------------------------------------------------------------
