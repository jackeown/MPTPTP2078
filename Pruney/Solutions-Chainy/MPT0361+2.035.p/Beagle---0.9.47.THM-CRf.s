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
% DateTime   : Thu Dec  3 09:56:31 EST 2020

% Result     : Theorem 1.94s
% Output     : CNFRefutation 2.24s
% Verified   : 
% Statistics : Number of formulae       :   40 (  65 expanded)
%              Number of leaves         :   19 (  31 expanded)
%              Depth                    :    8
%              Number of atoms          :   48 ( 102 expanded)
%              Number of equality atoms :   12 (  21 expanded)
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

tff(f_55,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => ! [C] :
            ( m1_subset_1(C,k1_zfmisc_1(A))
           => r1_tarski(k3_subset_1(A,k4_subset_1(A,B,C)),k3_subset_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_subset_1)).

tff(f_47,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(f_31,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => m1_subset_1(k4_subset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_subset_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_29,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(k4_xboole_0(C,B),k4_xboole_0(C,A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_xboole_1)).

tff(c_16,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_14,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_78,plain,(
    ! [A_26,B_27,C_28] :
      ( k4_subset_1(A_26,B_27,C_28) = k2_xboole_0(B_27,C_28)
      | ~ m1_subset_1(C_28,k1_zfmisc_1(A_26))
      | ~ m1_subset_1(B_27,k1_zfmisc_1(A_26)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_149,plain,(
    ! [B_33] :
      ( k4_subset_1('#skF_1',B_33,'#skF_3') = k2_xboole_0(B_33,'#skF_3')
      | ~ m1_subset_1(B_33,k1_zfmisc_1('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_14,c_78])).

tff(c_170,plain,(
    k4_subset_1('#skF_1','#skF_2','#skF_3') = k2_xboole_0('#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_16,c_149])).

tff(c_12,plain,(
    ~ r1_tarski(k3_subset_1('#skF_1',k4_subset_1('#skF_1','#skF_2','#skF_3')),k3_subset_1('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_195,plain,(
    ~ r1_tarski(k3_subset_1('#skF_1',k2_xboole_0('#skF_2','#skF_3')),k3_subset_1('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_170,c_12])).

tff(c_4,plain,(
    ! [A_4,B_5] : r1_tarski(A_4,k2_xboole_0(A_4,B_5)) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_104,plain,(
    ! [A_30,B_31,C_32] :
      ( m1_subset_1(k4_subset_1(A_30,B_31,C_32),k1_zfmisc_1(A_30))
      | ~ m1_subset_1(C_32,k1_zfmisc_1(A_30))
      | ~ m1_subset_1(B_31,k1_zfmisc_1(A_30)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_6,plain,(
    ! [A_6,B_7] :
      ( k4_xboole_0(A_6,B_7) = k3_subset_1(A_6,B_7)
      | ~ m1_subset_1(B_7,k1_zfmisc_1(A_6)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_220,plain,(
    ! [A_34,B_35,C_36] :
      ( k4_xboole_0(A_34,k4_subset_1(A_34,B_35,C_36)) = k3_subset_1(A_34,k4_subset_1(A_34,B_35,C_36))
      | ~ m1_subset_1(C_36,k1_zfmisc_1(A_34))
      | ~ m1_subset_1(B_35,k1_zfmisc_1(A_34)) ) ),
    inference(resolution,[status(thm)],[c_104,c_6])).

tff(c_266,plain,(
    ! [B_37] :
      ( k4_xboole_0('#skF_1',k4_subset_1('#skF_1',B_37,'#skF_3')) = k3_subset_1('#skF_1',k4_subset_1('#skF_1',B_37,'#skF_3'))
      | ~ m1_subset_1(B_37,k1_zfmisc_1('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_14,c_220])).

tff(c_288,plain,(
    k4_xboole_0('#skF_1',k4_subset_1('#skF_1','#skF_2','#skF_3')) = k3_subset_1('#skF_1',k4_subset_1('#skF_1','#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_16,c_266])).

tff(c_297,plain,(
    k4_xboole_0('#skF_1',k2_xboole_0('#skF_2','#skF_3')) = k3_subset_1('#skF_1',k2_xboole_0('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_170,c_170,c_288])).

tff(c_18,plain,(
    ! [A_17,B_18] :
      ( k4_xboole_0(A_17,B_18) = k3_subset_1(A_17,B_18)
      | ~ m1_subset_1(B_18,k1_zfmisc_1(A_17)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_26,plain,(
    k4_xboole_0('#skF_1','#skF_2') = k3_subset_1('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_16,c_18])).

tff(c_2,plain,(
    ! [C_3,B_2,A_1] :
      ( r1_tarski(k4_xboole_0(C_3,B_2),k4_xboole_0(C_3,A_1))
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_44,plain,(
    ! [B_2] :
      ( r1_tarski(k4_xboole_0('#skF_1',B_2),k3_subset_1('#skF_1','#skF_2'))
      | ~ r1_tarski('#skF_2',B_2) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_2])).

tff(c_334,plain,
    ( r1_tarski(k3_subset_1('#skF_1',k2_xboole_0('#skF_2','#skF_3')),k3_subset_1('#skF_1','#skF_2'))
    | ~ r1_tarski('#skF_2',k2_xboole_0('#skF_2','#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_297,c_44])).

tff(c_344,plain,(
    r1_tarski(k3_subset_1('#skF_1',k2_xboole_0('#skF_2','#skF_3')),k3_subset_1('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_334])).

tff(c_346,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_195,c_344])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.32  % Computer   : n020.cluster.edu
% 0.12/0.32  % Model      : x86_64 x86_64
% 0.12/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.32  % Memory     : 8042.1875MB
% 0.12/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.32  % CPULimit   : 60
% 0.12/0.32  % DateTime   : Tue Dec  1 17:26:07 EST 2020
% 0.12/0.32  % CPUTime    : 
% 0.12/0.33  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.94/1.23  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.94/1.23  
% 1.94/1.23  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.24/1.23  %$ r1_tarski > m1_subset_1 > k4_subset_1 > k4_xboole_0 > k3_subset_1 > k2_xboole_0 > #nlpp > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1
% 2.24/1.23  
% 2.24/1.23  %Foreground sorts:
% 2.24/1.23  
% 2.24/1.23  
% 2.24/1.23  %Background operators:
% 2.24/1.23  
% 2.24/1.23  
% 2.24/1.23  %Foreground operators:
% 2.24/1.23  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.24/1.23  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.24/1.23  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.24/1.23  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 2.24/1.23  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 2.24/1.23  tff('#skF_2', type, '#skF_2': $i).
% 2.24/1.23  tff('#skF_3', type, '#skF_3': $i).
% 2.24/1.23  tff('#skF_1', type, '#skF_1': $i).
% 2.24/1.23  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.24/1.23  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.24/1.23  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.24/1.23  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.24/1.23  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.24/1.23  
% 2.24/1.24  tff(f_55, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => r1_tarski(k3_subset_1(A, k4_subset_1(A, B, C)), k3_subset_1(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_subset_1)).
% 2.24/1.24  tff(f_47, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 2.24/1.24  tff(f_31, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 2.24/1.24  tff(f_41, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => m1_subset_1(k4_subset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k4_subset_1)).
% 2.24/1.24  tff(f_35, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 2.24/1.24  tff(f_29, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(k4_xboole_0(C, B), k4_xboole_0(C, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t34_xboole_1)).
% 2.24/1.24  tff(c_16, plain, (m1_subset_1('#skF_2', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.24/1.24  tff(c_14, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.24/1.24  tff(c_78, plain, (![A_26, B_27, C_28]: (k4_subset_1(A_26, B_27, C_28)=k2_xboole_0(B_27, C_28) | ~m1_subset_1(C_28, k1_zfmisc_1(A_26)) | ~m1_subset_1(B_27, k1_zfmisc_1(A_26)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.24/1.24  tff(c_149, plain, (![B_33]: (k4_subset_1('#skF_1', B_33, '#skF_3')=k2_xboole_0(B_33, '#skF_3') | ~m1_subset_1(B_33, k1_zfmisc_1('#skF_1')))), inference(resolution, [status(thm)], [c_14, c_78])).
% 2.24/1.24  tff(c_170, plain, (k4_subset_1('#skF_1', '#skF_2', '#skF_3')=k2_xboole_0('#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_16, c_149])).
% 2.24/1.24  tff(c_12, plain, (~r1_tarski(k3_subset_1('#skF_1', k4_subset_1('#skF_1', '#skF_2', '#skF_3')), k3_subset_1('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.24/1.24  tff(c_195, plain, (~r1_tarski(k3_subset_1('#skF_1', k2_xboole_0('#skF_2', '#skF_3')), k3_subset_1('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_170, c_12])).
% 2.24/1.24  tff(c_4, plain, (![A_4, B_5]: (r1_tarski(A_4, k2_xboole_0(A_4, B_5)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.24/1.24  tff(c_104, plain, (![A_30, B_31, C_32]: (m1_subset_1(k4_subset_1(A_30, B_31, C_32), k1_zfmisc_1(A_30)) | ~m1_subset_1(C_32, k1_zfmisc_1(A_30)) | ~m1_subset_1(B_31, k1_zfmisc_1(A_30)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.24/1.24  tff(c_6, plain, (![A_6, B_7]: (k4_xboole_0(A_6, B_7)=k3_subset_1(A_6, B_7) | ~m1_subset_1(B_7, k1_zfmisc_1(A_6)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.24/1.24  tff(c_220, plain, (![A_34, B_35, C_36]: (k4_xboole_0(A_34, k4_subset_1(A_34, B_35, C_36))=k3_subset_1(A_34, k4_subset_1(A_34, B_35, C_36)) | ~m1_subset_1(C_36, k1_zfmisc_1(A_34)) | ~m1_subset_1(B_35, k1_zfmisc_1(A_34)))), inference(resolution, [status(thm)], [c_104, c_6])).
% 2.24/1.24  tff(c_266, plain, (![B_37]: (k4_xboole_0('#skF_1', k4_subset_1('#skF_1', B_37, '#skF_3'))=k3_subset_1('#skF_1', k4_subset_1('#skF_1', B_37, '#skF_3')) | ~m1_subset_1(B_37, k1_zfmisc_1('#skF_1')))), inference(resolution, [status(thm)], [c_14, c_220])).
% 2.24/1.24  tff(c_288, plain, (k4_xboole_0('#skF_1', k4_subset_1('#skF_1', '#skF_2', '#skF_3'))=k3_subset_1('#skF_1', k4_subset_1('#skF_1', '#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_16, c_266])).
% 2.24/1.24  tff(c_297, plain, (k4_xboole_0('#skF_1', k2_xboole_0('#skF_2', '#skF_3'))=k3_subset_1('#skF_1', k2_xboole_0('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_170, c_170, c_288])).
% 2.24/1.24  tff(c_18, plain, (![A_17, B_18]: (k4_xboole_0(A_17, B_18)=k3_subset_1(A_17, B_18) | ~m1_subset_1(B_18, k1_zfmisc_1(A_17)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.24/1.24  tff(c_26, plain, (k4_xboole_0('#skF_1', '#skF_2')=k3_subset_1('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_16, c_18])).
% 2.24/1.24  tff(c_2, plain, (![C_3, B_2, A_1]: (r1_tarski(k4_xboole_0(C_3, B_2), k4_xboole_0(C_3, A_1)) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.24/1.24  tff(c_44, plain, (![B_2]: (r1_tarski(k4_xboole_0('#skF_1', B_2), k3_subset_1('#skF_1', '#skF_2')) | ~r1_tarski('#skF_2', B_2))), inference(superposition, [status(thm), theory('equality')], [c_26, c_2])).
% 2.24/1.24  tff(c_334, plain, (r1_tarski(k3_subset_1('#skF_1', k2_xboole_0('#skF_2', '#skF_3')), k3_subset_1('#skF_1', '#skF_2')) | ~r1_tarski('#skF_2', k2_xboole_0('#skF_2', '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_297, c_44])).
% 2.24/1.24  tff(c_344, plain, (r1_tarski(k3_subset_1('#skF_1', k2_xboole_0('#skF_2', '#skF_3')), k3_subset_1('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_334])).
% 2.24/1.24  tff(c_346, plain, $false, inference(negUnitSimplification, [status(thm)], [c_195, c_344])).
% 2.24/1.24  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.24/1.24  
% 2.24/1.24  Inference rules
% 2.24/1.24  ----------------------
% 2.24/1.24  #Ref     : 0
% 2.24/1.24  #Sup     : 94
% 2.24/1.24  #Fact    : 0
% 2.24/1.24  #Define  : 0
% 2.24/1.24  #Split   : 4
% 2.24/1.24  #Chain   : 0
% 2.24/1.24  #Close   : 0
% 2.24/1.24  
% 2.24/1.24  Ordering : KBO
% 2.24/1.24  
% 2.24/1.24  Simplification rules
% 2.24/1.24  ----------------------
% 2.24/1.24  #Subsume      : 4
% 2.24/1.24  #Demod        : 16
% 2.24/1.24  #Tautology    : 17
% 2.24/1.24  #SimpNegUnit  : 1
% 2.24/1.24  #BackRed      : 1
% 2.24/1.24  
% 2.24/1.24  #Partial instantiations: 0
% 2.24/1.24  #Strategies tried      : 1
% 2.24/1.24  
% 2.24/1.24  Timing (in seconds)
% 2.24/1.24  ----------------------
% 2.24/1.25  Preprocessing        : 0.27
% 2.24/1.25  Parsing              : 0.15
% 2.24/1.25  CNF conversion       : 0.02
% 2.24/1.25  Main loop            : 0.23
% 2.24/1.25  Inferencing          : 0.08
% 2.24/1.25  Reduction            : 0.07
% 2.24/1.25  Demodulation         : 0.05
% 2.24/1.25  BG Simplification    : 0.01
% 2.24/1.25  Subsumption          : 0.04
% 2.24/1.25  Abstraction          : 0.02
% 2.24/1.25  MUC search           : 0.00
% 2.24/1.25  Cooper               : 0.00
% 2.24/1.25  Total                : 0.53
% 2.24/1.25  Index Insertion      : 0.00
% 2.24/1.25  Index Deletion       : 0.00
% 2.24/1.25  Index Matching       : 0.00
% 2.24/1.25  BG Taut test         : 0.00
%------------------------------------------------------------------------------
