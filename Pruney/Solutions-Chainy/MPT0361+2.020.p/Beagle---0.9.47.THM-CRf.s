%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:56:29 EST 2020

% Result     : Theorem 2.66s
% Output     : CNFRefutation 2.66s
% Verified   : 
% Statistics : Number of formulae       :   46 (  77 expanded)
%              Number of leaves         :   21 (  35 expanded)
%              Depth                    :    8
%              Number of atoms          :   56 ( 116 expanded)
%              Number of equality atoms :   15 (  30 expanded)
%              Maximal formula depth    :    7 (   4 average)
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

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_61,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => ! [C] :
            ( m1_subset_1(C,k1_zfmisc_1(A))
           => r1_tarski(k3_subset_1(A,k4_subset_1(A,B,C)),k3_subset_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_subset_1)).

tff(f_53,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(f_33,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k4_xboole_0(A,B),C)
     => r1_tarski(A,k2_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_xboole_1)).

tff(f_47,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => m1_subset_1(k4_subset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_subset_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(k4_xboole_0(C,B),k4_xboole_0(C,A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_xboole_1)).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_20,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_18,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_219,plain,(
    ! [A_46,B_47,C_48] :
      ( k4_subset_1(A_46,B_47,C_48) = k2_xboole_0(B_47,C_48)
      | ~ m1_subset_1(C_48,k1_zfmisc_1(A_46))
      | ~ m1_subset_1(B_47,k1_zfmisc_1(A_46)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_248,plain,(
    ! [B_52] :
      ( k4_subset_1('#skF_1',B_52,'#skF_3') = k2_xboole_0(B_52,'#skF_3')
      | ~ m1_subset_1(B_52,k1_zfmisc_1('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_18,c_219])).

tff(c_254,plain,(
    k4_subset_1('#skF_1','#skF_2','#skF_3') = k2_xboole_0('#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_20,c_248])).

tff(c_257,plain,(
    k4_subset_1('#skF_1','#skF_2','#skF_3') = k2_xboole_0('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_254])).

tff(c_16,plain,(
    ~ r1_tarski(k3_subset_1('#skF_1',k4_subset_1('#skF_1','#skF_2','#skF_3')),k3_subset_1('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_260,plain,(
    ~ r1_tarski(k3_subset_1('#skF_1',k2_xboole_0('#skF_3','#skF_2')),k3_subset_1('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_257,c_16])).

tff(c_6,plain,(
    ! [A_6,B_7] : r1_tarski(k4_xboole_0(A_6,B_7),A_6) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_55,plain,(
    ! [A_24,B_25,C_26] :
      ( r1_tarski(A_24,k2_xboole_0(B_25,C_26))
      | ~ r1_tarski(k4_xboole_0(A_24,B_25),C_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_59,plain,(
    ! [A_6,B_7] : r1_tarski(A_6,k2_xboole_0(B_7,A_6)) ),
    inference(resolution,[status(thm)],[c_6,c_55])).

tff(c_309,plain,(
    ! [A_55,B_56,C_57] :
      ( m1_subset_1(k4_subset_1(A_55,B_56,C_57),k1_zfmisc_1(A_55))
      | ~ m1_subset_1(C_57,k1_zfmisc_1(A_55))
      | ~ m1_subset_1(B_56,k1_zfmisc_1(A_55)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_10,plain,(
    ! [A_11,B_12] :
      ( k4_xboole_0(A_11,B_12) = k3_subset_1(A_11,B_12)
      | ~ m1_subset_1(B_12,k1_zfmisc_1(A_11)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_442,plain,(
    ! [A_62,B_63,C_64] :
      ( k4_xboole_0(A_62,k4_subset_1(A_62,B_63,C_64)) = k3_subset_1(A_62,k4_subset_1(A_62,B_63,C_64))
      | ~ m1_subset_1(C_64,k1_zfmisc_1(A_62))
      | ~ m1_subset_1(B_63,k1_zfmisc_1(A_62)) ) ),
    inference(resolution,[status(thm)],[c_309,c_10])).

tff(c_539,plain,(
    ! [B_70] :
      ( k4_xboole_0('#skF_1',k4_subset_1('#skF_1',B_70,'#skF_3')) = k3_subset_1('#skF_1',k4_subset_1('#skF_1',B_70,'#skF_3'))
      | ~ m1_subset_1(B_70,k1_zfmisc_1('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_18,c_442])).

tff(c_558,plain,(
    k4_xboole_0('#skF_1',k4_subset_1('#skF_1','#skF_2','#skF_3')) = k3_subset_1('#skF_1',k4_subset_1('#skF_1','#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_20,c_539])).

tff(c_566,plain,(
    k4_xboole_0('#skF_1',k2_xboole_0('#skF_3','#skF_2')) = k3_subset_1('#skF_1',k2_xboole_0('#skF_3','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_257,c_257,c_558])).

tff(c_87,plain,(
    ! [A_31,B_32] :
      ( k4_xboole_0(A_31,B_32) = k3_subset_1(A_31,B_32)
      | ~ m1_subset_1(B_32,k1_zfmisc_1(A_31)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_95,plain,(
    k4_xboole_0('#skF_1','#skF_2') = k3_subset_1('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_20,c_87])).

tff(c_136,plain,(
    ! [C_36,B_37,A_38] :
      ( r1_tarski(k4_xboole_0(C_36,B_37),k4_xboole_0(C_36,A_38))
      | ~ r1_tarski(A_38,B_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_145,plain,(
    ! [B_37] :
      ( r1_tarski(k4_xboole_0('#skF_1',B_37),k3_subset_1('#skF_1','#skF_2'))
      | ~ r1_tarski('#skF_2',B_37) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_95,c_136])).

tff(c_629,plain,
    ( r1_tarski(k3_subset_1('#skF_1',k2_xboole_0('#skF_3','#skF_2')),k3_subset_1('#skF_1','#skF_2'))
    | ~ r1_tarski('#skF_2',k2_xboole_0('#skF_3','#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_566,c_145])).

tff(c_656,plain,(
    r1_tarski(k3_subset_1('#skF_1',k2_xboole_0('#skF_3','#skF_2')),k3_subset_1('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_59,c_629])).

tff(c_658,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_260,c_656])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n012.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 11:55:22 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.66/1.34  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.66/1.35  
% 2.66/1.35  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.66/1.35  %$ r1_tarski > m1_subset_1 > k4_subset_1 > k4_xboole_0 > k3_subset_1 > k2_xboole_0 > #nlpp > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1
% 2.66/1.35  
% 2.66/1.35  %Foreground sorts:
% 2.66/1.35  
% 2.66/1.35  
% 2.66/1.35  %Background operators:
% 2.66/1.35  
% 2.66/1.35  
% 2.66/1.35  %Foreground operators:
% 2.66/1.35  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.66/1.35  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.66/1.35  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.66/1.35  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 2.66/1.35  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 2.66/1.35  tff('#skF_2', type, '#skF_2': $i).
% 2.66/1.35  tff('#skF_3', type, '#skF_3': $i).
% 2.66/1.35  tff('#skF_1', type, '#skF_1': $i).
% 2.66/1.35  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.66/1.35  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.66/1.35  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.66/1.35  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.66/1.35  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.66/1.35  
% 2.66/1.37  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 2.66/1.37  tff(f_61, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => r1_tarski(k3_subset_1(A, k4_subset_1(A, B, C)), k3_subset_1(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_subset_1)).
% 2.66/1.37  tff(f_53, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 2.66/1.37  tff(f_33, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 2.66/1.37  tff(f_37, axiom, (![A, B, C]: (r1_tarski(k4_xboole_0(A, B), C) => r1_tarski(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_xboole_1)).
% 2.66/1.37  tff(f_47, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => m1_subset_1(k4_subset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k4_subset_1)).
% 2.66/1.37  tff(f_41, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_subset_1)).
% 2.66/1.37  tff(f_31, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(k4_xboole_0(C, B), k4_xboole_0(C, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t34_xboole_1)).
% 2.66/1.37  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.66/1.37  tff(c_20, plain, (m1_subset_1('#skF_2', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.66/1.37  tff(c_18, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.66/1.37  tff(c_219, plain, (![A_46, B_47, C_48]: (k4_subset_1(A_46, B_47, C_48)=k2_xboole_0(B_47, C_48) | ~m1_subset_1(C_48, k1_zfmisc_1(A_46)) | ~m1_subset_1(B_47, k1_zfmisc_1(A_46)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.66/1.37  tff(c_248, plain, (![B_52]: (k4_subset_1('#skF_1', B_52, '#skF_3')=k2_xboole_0(B_52, '#skF_3') | ~m1_subset_1(B_52, k1_zfmisc_1('#skF_1')))), inference(resolution, [status(thm)], [c_18, c_219])).
% 2.66/1.37  tff(c_254, plain, (k4_subset_1('#skF_1', '#skF_2', '#skF_3')=k2_xboole_0('#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_20, c_248])).
% 2.66/1.37  tff(c_257, plain, (k4_subset_1('#skF_1', '#skF_2', '#skF_3')=k2_xboole_0('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_254])).
% 2.66/1.37  tff(c_16, plain, (~r1_tarski(k3_subset_1('#skF_1', k4_subset_1('#skF_1', '#skF_2', '#skF_3')), k3_subset_1('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.66/1.37  tff(c_260, plain, (~r1_tarski(k3_subset_1('#skF_1', k2_xboole_0('#skF_3', '#skF_2')), k3_subset_1('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_257, c_16])).
% 2.66/1.37  tff(c_6, plain, (![A_6, B_7]: (r1_tarski(k4_xboole_0(A_6, B_7), A_6))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.66/1.37  tff(c_55, plain, (![A_24, B_25, C_26]: (r1_tarski(A_24, k2_xboole_0(B_25, C_26)) | ~r1_tarski(k4_xboole_0(A_24, B_25), C_26))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.66/1.37  tff(c_59, plain, (![A_6, B_7]: (r1_tarski(A_6, k2_xboole_0(B_7, A_6)))), inference(resolution, [status(thm)], [c_6, c_55])).
% 2.66/1.37  tff(c_309, plain, (![A_55, B_56, C_57]: (m1_subset_1(k4_subset_1(A_55, B_56, C_57), k1_zfmisc_1(A_55)) | ~m1_subset_1(C_57, k1_zfmisc_1(A_55)) | ~m1_subset_1(B_56, k1_zfmisc_1(A_55)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.66/1.37  tff(c_10, plain, (![A_11, B_12]: (k4_xboole_0(A_11, B_12)=k3_subset_1(A_11, B_12) | ~m1_subset_1(B_12, k1_zfmisc_1(A_11)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.66/1.37  tff(c_442, plain, (![A_62, B_63, C_64]: (k4_xboole_0(A_62, k4_subset_1(A_62, B_63, C_64))=k3_subset_1(A_62, k4_subset_1(A_62, B_63, C_64)) | ~m1_subset_1(C_64, k1_zfmisc_1(A_62)) | ~m1_subset_1(B_63, k1_zfmisc_1(A_62)))), inference(resolution, [status(thm)], [c_309, c_10])).
% 2.66/1.37  tff(c_539, plain, (![B_70]: (k4_xboole_0('#skF_1', k4_subset_1('#skF_1', B_70, '#skF_3'))=k3_subset_1('#skF_1', k4_subset_1('#skF_1', B_70, '#skF_3')) | ~m1_subset_1(B_70, k1_zfmisc_1('#skF_1')))), inference(resolution, [status(thm)], [c_18, c_442])).
% 2.66/1.37  tff(c_558, plain, (k4_xboole_0('#skF_1', k4_subset_1('#skF_1', '#skF_2', '#skF_3'))=k3_subset_1('#skF_1', k4_subset_1('#skF_1', '#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_20, c_539])).
% 2.66/1.37  tff(c_566, plain, (k4_xboole_0('#skF_1', k2_xboole_0('#skF_3', '#skF_2'))=k3_subset_1('#skF_1', k2_xboole_0('#skF_3', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_257, c_257, c_558])).
% 2.66/1.37  tff(c_87, plain, (![A_31, B_32]: (k4_xboole_0(A_31, B_32)=k3_subset_1(A_31, B_32) | ~m1_subset_1(B_32, k1_zfmisc_1(A_31)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.66/1.37  tff(c_95, plain, (k4_xboole_0('#skF_1', '#skF_2')=k3_subset_1('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_20, c_87])).
% 2.66/1.37  tff(c_136, plain, (![C_36, B_37, A_38]: (r1_tarski(k4_xboole_0(C_36, B_37), k4_xboole_0(C_36, A_38)) | ~r1_tarski(A_38, B_37))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.66/1.37  tff(c_145, plain, (![B_37]: (r1_tarski(k4_xboole_0('#skF_1', B_37), k3_subset_1('#skF_1', '#skF_2')) | ~r1_tarski('#skF_2', B_37))), inference(superposition, [status(thm), theory('equality')], [c_95, c_136])).
% 2.66/1.37  tff(c_629, plain, (r1_tarski(k3_subset_1('#skF_1', k2_xboole_0('#skF_3', '#skF_2')), k3_subset_1('#skF_1', '#skF_2')) | ~r1_tarski('#skF_2', k2_xboole_0('#skF_3', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_566, c_145])).
% 2.66/1.37  tff(c_656, plain, (r1_tarski(k3_subset_1('#skF_1', k2_xboole_0('#skF_3', '#skF_2')), k3_subset_1('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_59, c_629])).
% 2.66/1.37  tff(c_658, plain, $false, inference(negUnitSimplification, [status(thm)], [c_260, c_656])).
% 2.66/1.37  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.66/1.37  
% 2.66/1.37  Inference rules
% 2.66/1.37  ----------------------
% 2.66/1.37  #Ref     : 0
% 2.66/1.37  #Sup     : 158
% 2.66/1.37  #Fact    : 0
% 2.66/1.37  #Define  : 0
% 2.66/1.37  #Split   : 1
% 2.66/1.37  #Chain   : 0
% 2.66/1.37  #Close   : 0
% 2.66/1.37  
% 2.66/1.37  Ordering : KBO
% 2.66/1.37  
% 2.66/1.37  Simplification rules
% 2.66/1.37  ----------------------
% 2.66/1.37  #Subsume      : 14
% 2.66/1.37  #Demod        : 48
% 2.66/1.37  #Tautology    : 39
% 2.66/1.37  #SimpNegUnit  : 1
% 2.66/1.37  #BackRed      : 1
% 2.66/1.37  
% 2.66/1.37  #Partial instantiations: 0
% 2.66/1.37  #Strategies tried      : 1
% 2.66/1.37  
% 2.66/1.37  Timing (in seconds)
% 2.66/1.37  ----------------------
% 2.66/1.37  Preprocessing        : 0.28
% 2.66/1.37  Parsing              : 0.15
% 2.66/1.37  CNF conversion       : 0.02
% 2.66/1.37  Main loop            : 0.34
% 2.66/1.37  Inferencing          : 0.12
% 2.66/1.37  Reduction            : 0.12
% 2.66/1.37  Demodulation         : 0.10
% 2.66/1.37  BG Simplification    : 0.01
% 2.66/1.37  Subsumption          : 0.06
% 2.66/1.37  Abstraction          : 0.02
% 2.66/1.37  MUC search           : 0.00
% 2.66/1.37  Cooper               : 0.00
% 2.66/1.37  Total                : 0.65
% 2.66/1.37  Index Insertion      : 0.00
% 2.66/1.37  Index Deletion       : 0.00
% 2.66/1.37  Index Matching       : 0.00
% 2.66/1.37  BG Taut test         : 0.00
%------------------------------------------------------------------------------
