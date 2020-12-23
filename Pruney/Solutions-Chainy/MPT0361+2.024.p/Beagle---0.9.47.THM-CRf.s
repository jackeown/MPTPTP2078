%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:56:30 EST 2020

% Result     : Theorem 2.33s
% Output     : CNFRefutation 2.33s
% Verified   : 
% Statistics : Number of formulae       :   43 (  60 expanded)
%              Number of leaves         :   22 (  31 expanded)
%              Depth                    :    9
%              Number of atoms          :   54 (  91 expanded)
%              Number of equality atoms :   10 (  15 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > m1_subset_1 > k4_subset_1 > k4_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

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

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_65,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => ! [C] :
            ( m1_subset_1(C,k1_zfmisc_1(A))
           => r1_tarski(k3_subset_1(A,k4_subset_1(A,B,C)),k3_subset_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_subset_1)).

tff(f_57,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_39,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => m1_subset_1(k4_subset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_subset_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_37,axiom,(
    ! [A,B,C,D] :
      ( ( r1_tarski(A,B)
        & r1_tarski(C,D) )
     => r1_tarski(k4_xboole_0(A,D),k4_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_xboole_1)).

tff(c_24,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_22,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_144,plain,(
    ! [A_46,B_47,C_48] :
      ( k4_subset_1(A_46,B_47,C_48) = k2_xboole_0(B_47,C_48)
      | ~ m1_subset_1(C_48,k1_zfmisc_1(A_46))
      | ~ m1_subset_1(B_47,k1_zfmisc_1(A_46)) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_154,plain,(
    ! [B_49] :
      ( k4_subset_1('#skF_1',B_49,'#skF_3') = k2_xboole_0(B_49,'#skF_3')
      | ~ m1_subset_1(B_49,k1_zfmisc_1('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_22,c_144])).

tff(c_167,plain,(
    k4_subset_1('#skF_1','#skF_2','#skF_3') = k2_xboole_0('#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_24,c_154])).

tff(c_20,plain,(
    ~ r1_tarski(k3_subset_1('#skF_1',k4_subset_1('#skF_1','#skF_2','#skF_3')),k3_subset_1('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_206,plain,(
    ~ r1_tarski(k3_subset_1('#skF_1',k2_xboole_0('#skF_2','#skF_3')),k3_subset_1('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_167,c_20])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_10,plain,(
    ! [A_7,B_8] : r1_tarski(A_7,k2_xboole_0(A_7,B_8)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_16,plain,(
    ! [A_13,B_14,C_15] :
      ( m1_subset_1(k4_subset_1(A_13,B_14,C_15),k1_zfmisc_1(A_13))
      | ~ m1_subset_1(C_15,k1_zfmisc_1(A_13))
      | ~ m1_subset_1(B_14,k1_zfmisc_1(A_13)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_210,plain,
    ( m1_subset_1(k2_xboole_0('#skF_2','#skF_3'),k1_zfmisc_1('#skF_1'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1('#skF_1'))
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_167,c_16])).

tff(c_214,plain,(
    m1_subset_1(k2_xboole_0('#skF_2','#skF_3'),k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_22,c_210])).

tff(c_14,plain,(
    ! [A_11,B_12] :
      ( k4_xboole_0(A_11,B_12) = k3_subset_1(A_11,B_12)
      | ~ m1_subset_1(B_12,k1_zfmisc_1(A_11)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_230,plain,(
    k4_xboole_0('#skF_1',k2_xboole_0('#skF_2','#skF_3')) = k3_subset_1('#skF_1',k2_xboole_0('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_214,c_14])).

tff(c_48,plain,(
    ! [A_29,B_30] :
      ( k4_xboole_0(A_29,B_30) = k3_subset_1(A_29,B_30)
      | ~ m1_subset_1(B_30,k1_zfmisc_1(A_29)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_56,plain,(
    k4_xboole_0('#skF_1','#skF_2') = k3_subset_1('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_24,c_48])).

tff(c_65,plain,(
    ! [A_31,D_32,B_33,C_34] :
      ( r1_tarski(k4_xboole_0(A_31,D_32),k4_xboole_0(B_33,C_34))
      | ~ r1_tarski(C_34,D_32)
      | ~ r1_tarski(A_31,B_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_73,plain,(
    ! [A_31,D_32] :
      ( r1_tarski(k4_xboole_0(A_31,D_32),k3_subset_1('#skF_1','#skF_2'))
      | ~ r1_tarski('#skF_2',D_32)
      | ~ r1_tarski(A_31,'#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_56,c_65])).

tff(c_464,plain,
    ( r1_tarski(k3_subset_1('#skF_1',k2_xboole_0('#skF_2','#skF_3')),k3_subset_1('#skF_1','#skF_2'))
    | ~ r1_tarski('#skF_2',k2_xboole_0('#skF_2','#skF_3'))
    | ~ r1_tarski('#skF_1','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_230,c_73])).

tff(c_485,plain,(
    r1_tarski(k3_subset_1('#skF_1',k2_xboole_0('#skF_2','#skF_3')),k3_subset_1('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_10,c_464])).

tff(c_487,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_206,c_485])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:27:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.33/1.37  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.33/1.37  
% 2.33/1.37  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.33/1.38  %$ r1_tarski > m1_subset_1 > k4_subset_1 > k4_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1
% 2.33/1.38  
% 2.33/1.38  %Foreground sorts:
% 2.33/1.38  
% 2.33/1.38  
% 2.33/1.38  %Background operators:
% 2.33/1.38  
% 2.33/1.38  
% 2.33/1.38  %Foreground operators:
% 2.33/1.38  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.33/1.38  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.33/1.38  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.33/1.38  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.33/1.38  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 2.33/1.38  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 2.33/1.38  tff('#skF_2', type, '#skF_2': $i).
% 2.33/1.38  tff('#skF_3', type, '#skF_3': $i).
% 2.33/1.38  tff('#skF_1', type, '#skF_1': $i).
% 2.33/1.38  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.33/1.38  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.33/1.38  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.33/1.38  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.33/1.38  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.33/1.38  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.33/1.38  
% 2.33/1.39  tff(f_65, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => r1_tarski(k3_subset_1(A, k4_subset_1(A, B, C)), k3_subset_1(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_subset_1)).
% 2.33/1.39  tff(f_57, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 2.33/1.39  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.33/1.39  tff(f_39, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 2.33/1.39  tff(f_51, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => m1_subset_1(k4_subset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k4_subset_1)).
% 2.33/1.39  tff(f_45, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 2.33/1.39  tff(f_37, axiom, (![A, B, C, D]: ((r1_tarski(A, B) & r1_tarski(C, D)) => r1_tarski(k4_xboole_0(A, D), k4_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t35_xboole_1)).
% 2.33/1.39  tff(c_24, plain, (m1_subset_1('#skF_2', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.33/1.39  tff(c_22, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.33/1.39  tff(c_144, plain, (![A_46, B_47, C_48]: (k4_subset_1(A_46, B_47, C_48)=k2_xboole_0(B_47, C_48) | ~m1_subset_1(C_48, k1_zfmisc_1(A_46)) | ~m1_subset_1(B_47, k1_zfmisc_1(A_46)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.33/1.39  tff(c_154, plain, (![B_49]: (k4_subset_1('#skF_1', B_49, '#skF_3')=k2_xboole_0(B_49, '#skF_3') | ~m1_subset_1(B_49, k1_zfmisc_1('#skF_1')))), inference(resolution, [status(thm)], [c_22, c_144])).
% 2.33/1.39  tff(c_167, plain, (k4_subset_1('#skF_1', '#skF_2', '#skF_3')=k2_xboole_0('#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_24, c_154])).
% 2.33/1.39  tff(c_20, plain, (~r1_tarski(k3_subset_1('#skF_1', k4_subset_1('#skF_1', '#skF_2', '#skF_3')), k3_subset_1('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.33/1.39  tff(c_206, plain, (~r1_tarski(k3_subset_1('#skF_1', k2_xboole_0('#skF_2', '#skF_3')), k3_subset_1('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_167, c_20])).
% 2.33/1.39  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.33/1.39  tff(c_10, plain, (![A_7, B_8]: (r1_tarski(A_7, k2_xboole_0(A_7, B_8)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.33/1.39  tff(c_16, plain, (![A_13, B_14, C_15]: (m1_subset_1(k4_subset_1(A_13, B_14, C_15), k1_zfmisc_1(A_13)) | ~m1_subset_1(C_15, k1_zfmisc_1(A_13)) | ~m1_subset_1(B_14, k1_zfmisc_1(A_13)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.33/1.39  tff(c_210, plain, (m1_subset_1(k2_xboole_0('#skF_2', '#skF_3'), k1_zfmisc_1('#skF_1')) | ~m1_subset_1('#skF_3', k1_zfmisc_1('#skF_1')) | ~m1_subset_1('#skF_2', k1_zfmisc_1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_167, c_16])).
% 2.33/1.39  tff(c_214, plain, (m1_subset_1(k2_xboole_0('#skF_2', '#skF_3'), k1_zfmisc_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_22, c_210])).
% 2.33/1.39  tff(c_14, plain, (![A_11, B_12]: (k4_xboole_0(A_11, B_12)=k3_subset_1(A_11, B_12) | ~m1_subset_1(B_12, k1_zfmisc_1(A_11)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.33/1.39  tff(c_230, plain, (k4_xboole_0('#skF_1', k2_xboole_0('#skF_2', '#skF_3'))=k3_subset_1('#skF_1', k2_xboole_0('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_214, c_14])).
% 2.33/1.39  tff(c_48, plain, (![A_29, B_30]: (k4_xboole_0(A_29, B_30)=k3_subset_1(A_29, B_30) | ~m1_subset_1(B_30, k1_zfmisc_1(A_29)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.33/1.39  tff(c_56, plain, (k4_xboole_0('#skF_1', '#skF_2')=k3_subset_1('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_24, c_48])).
% 2.33/1.39  tff(c_65, plain, (![A_31, D_32, B_33, C_34]: (r1_tarski(k4_xboole_0(A_31, D_32), k4_xboole_0(B_33, C_34)) | ~r1_tarski(C_34, D_32) | ~r1_tarski(A_31, B_33))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.33/1.39  tff(c_73, plain, (![A_31, D_32]: (r1_tarski(k4_xboole_0(A_31, D_32), k3_subset_1('#skF_1', '#skF_2')) | ~r1_tarski('#skF_2', D_32) | ~r1_tarski(A_31, '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_56, c_65])).
% 2.33/1.39  tff(c_464, plain, (r1_tarski(k3_subset_1('#skF_1', k2_xboole_0('#skF_2', '#skF_3')), k3_subset_1('#skF_1', '#skF_2')) | ~r1_tarski('#skF_2', k2_xboole_0('#skF_2', '#skF_3')) | ~r1_tarski('#skF_1', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_230, c_73])).
% 2.33/1.39  tff(c_485, plain, (r1_tarski(k3_subset_1('#skF_1', k2_xboole_0('#skF_2', '#skF_3')), k3_subset_1('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_10, c_464])).
% 2.33/1.39  tff(c_487, plain, $false, inference(negUnitSimplification, [status(thm)], [c_206, c_485])).
% 2.33/1.39  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.33/1.39  
% 2.33/1.39  Inference rules
% 2.33/1.39  ----------------------
% 2.33/1.39  #Ref     : 0
% 2.33/1.39  #Sup     : 121
% 2.33/1.39  #Fact    : 0
% 2.33/1.39  #Define  : 0
% 2.33/1.39  #Split   : 2
% 2.33/1.39  #Chain   : 0
% 2.33/1.39  #Close   : 0
% 2.33/1.39  
% 2.33/1.39  Ordering : KBO
% 2.33/1.39  
% 2.33/1.39  Simplification rules
% 2.33/1.39  ----------------------
% 2.33/1.39  #Subsume      : 2
% 2.33/1.39  #Demod        : 60
% 2.33/1.39  #Tautology    : 30
% 2.33/1.39  #SimpNegUnit  : 1
% 2.33/1.39  #BackRed      : 1
% 2.33/1.39  
% 2.33/1.39  #Partial instantiations: 0
% 2.33/1.39  #Strategies tried      : 1
% 2.33/1.39  
% 2.33/1.39  Timing (in seconds)
% 2.33/1.39  ----------------------
% 2.33/1.39  Preprocessing        : 0.30
% 2.33/1.39  Parsing              : 0.17
% 2.33/1.39  CNF conversion       : 0.02
% 2.33/1.39  Main loop            : 0.28
% 2.33/1.39  Inferencing          : 0.10
% 2.33/1.39  Reduction            : 0.09
% 2.33/1.39  Demodulation         : 0.07
% 2.33/1.39  BG Simplification    : 0.02
% 2.33/1.39  Subsumption          : 0.06
% 2.33/1.39  Abstraction          : 0.02
% 2.33/1.39  MUC search           : 0.00
% 2.33/1.39  Cooper               : 0.00
% 2.33/1.39  Total                : 0.61
% 2.33/1.39  Index Insertion      : 0.00
% 2.33/1.39  Index Deletion       : 0.00
% 2.33/1.39  Index Matching       : 0.00
% 2.33/1.39  BG Taut test         : 0.00
%------------------------------------------------------------------------------
