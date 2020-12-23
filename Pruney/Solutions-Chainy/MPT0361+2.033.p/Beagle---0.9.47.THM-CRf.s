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
% DateTime   : Thu Dec  3 09:56:31 EST 2020

% Result     : Theorem 3.49s
% Output     : CNFRefutation 3.49s
% Verified   : 
% Statistics : Number of formulae       :   49 (  67 expanded)
%              Number of leaves         :   23 (  33 expanded)
%              Depth                    :   11
%              Number of atoms          :   61 ( 101 expanded)
%              Number of equality atoms :   11 (  16 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > k4_subset_1 > k4_xboole_0 > k3_subset_1 > k2_xboole_0 > #nlpp > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

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

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_36,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(A,k2_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_xboole_1)).

tff(f_66,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => ! [C] :
            ( m1_subset_1(C,k1_zfmisc_1(A))
           => r1_tarski(k3_subset_1(A,k4_subset_1(A,B,C)),k3_subset_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_subset_1)).

tff(f_46,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_58,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(f_52,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => m1_subset_1(k4_subset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_subset_1)).

tff(f_38,axiom,(
    ! [A,B,C] : k4_xboole_0(k4_xboole_0(A,B),C) = k4_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

tff(f_42,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k2_xboole_0(B,C))
     => r1_tarski(k4_xboole_0(A,B),C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_xboole_1)).

tff(c_27,plain,(
    ! [A_29,B_30] :
      ( r2_hidden('#skF_1'(A_29,B_30),A_29)
      | r1_tarski(A_29,B_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_32,plain,(
    ! [A_29] : r1_tarski(A_29,A_29) ),
    inference(resolution,[status(thm)],[c_27,c_4])).

tff(c_8,plain,(
    ! [A_6,C_8,B_7] :
      ( r1_tarski(A_6,k2_xboole_0(C_8,B_7))
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_24,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_59,plain,(
    ! [A_41,B_42] :
      ( k4_xboole_0(A_41,B_42) = k3_subset_1(A_41,B_42)
      | ~ m1_subset_1(B_42,k1_zfmisc_1(A_41)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_67,plain,(
    k4_xboole_0('#skF_2','#skF_3') = k3_subset_1('#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_24,c_59])).

tff(c_22,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_105,plain,(
    ! [A_45,B_46,C_47] :
      ( k4_subset_1(A_45,B_46,C_47) = k2_xboole_0(B_46,C_47)
      | ~ m1_subset_1(C_47,k1_zfmisc_1(A_45))
      | ~ m1_subset_1(B_46,k1_zfmisc_1(A_45)) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_146,plain,(
    ! [B_51] :
      ( k4_subset_1('#skF_2',B_51,'#skF_4') = k2_xboole_0(B_51,'#skF_4')
      | ~ m1_subset_1(B_51,k1_zfmisc_1('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_22,c_105])).

tff(c_154,plain,(
    k4_subset_1('#skF_2','#skF_3','#skF_4') = k2_xboole_0('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_24,c_146])).

tff(c_164,plain,(
    ! [A_52,B_53,C_54] :
      ( m1_subset_1(k4_subset_1(A_52,B_53,C_54),k1_zfmisc_1(A_52))
      | ~ m1_subset_1(C_54,k1_zfmisc_1(A_52))
      | ~ m1_subset_1(B_53,k1_zfmisc_1(A_52)) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_180,plain,
    ( m1_subset_1(k2_xboole_0('#skF_3','#skF_4'),k1_zfmisc_1('#skF_2'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_2'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1('#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_154,c_164])).

tff(c_195,plain,(
    m1_subset_1(k2_xboole_0('#skF_3','#skF_4'),k1_zfmisc_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_22,c_180])).

tff(c_14,plain,(
    ! [A_15,B_16] :
      ( k4_xboole_0(A_15,B_16) = k3_subset_1(A_15,B_16)
      | ~ m1_subset_1(B_16,k1_zfmisc_1(A_15)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_216,plain,(
    k4_xboole_0('#skF_2',k2_xboole_0('#skF_3','#skF_4')) = k3_subset_1('#skF_2',k2_xboole_0('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_195,c_14])).

tff(c_10,plain,(
    ! [A_9,B_10,C_11] : k4_xboole_0(k4_xboole_0(A_9,B_10),C_11) = k4_xboole_0(A_9,k2_xboole_0(B_10,C_11)) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_55,plain,(
    ! [A_38,B_39,C_40] :
      ( r1_tarski(k4_xboole_0(A_38,B_39),C_40)
      | ~ r1_tarski(A_38,k2_xboole_0(B_39,C_40)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_549,plain,(
    ! [A_62,B_63,C_64,C_65] :
      ( r1_tarski(k4_xboole_0(A_62,k2_xboole_0(B_63,C_64)),C_65)
      | ~ r1_tarski(k4_xboole_0(A_62,B_63),k2_xboole_0(C_64,C_65)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_55])).

tff(c_558,plain,(
    ! [C_65] :
      ( r1_tarski(k3_subset_1('#skF_2',k2_xboole_0('#skF_3','#skF_4')),C_65)
      | ~ r1_tarski(k4_xboole_0('#skF_2','#skF_3'),k2_xboole_0('#skF_4',C_65)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_216,c_549])).

tff(c_1236,plain,(
    ! [C_97] :
      ( r1_tarski(k3_subset_1('#skF_2',k2_xboole_0('#skF_3','#skF_4')),C_97)
      | ~ r1_tarski(k3_subset_1('#skF_2','#skF_3'),k2_xboole_0('#skF_4',C_97)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_67,c_558])).

tff(c_20,plain,(
    ~ r1_tarski(k3_subset_1('#skF_2',k4_subset_1('#skF_2','#skF_3','#skF_4')),k3_subset_1('#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_159,plain,(
    ~ r1_tarski(k3_subset_1('#skF_2',k2_xboole_0('#skF_3','#skF_4')),k3_subset_1('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_154,c_20])).

tff(c_1243,plain,(
    ~ r1_tarski(k3_subset_1('#skF_2','#skF_3'),k2_xboole_0('#skF_4',k3_subset_1('#skF_2','#skF_3'))) ),
    inference(resolution,[status(thm)],[c_1236,c_159])).

tff(c_1305,plain,(
    ~ r1_tarski(k3_subset_1('#skF_2','#skF_3'),k3_subset_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_8,c_1243])).

tff(c_1310,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_1305])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:10:19 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.49/1.68  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.49/1.68  
% 3.49/1.68  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.49/1.68  %$ r2_hidden > r1_tarski > m1_subset_1 > k4_subset_1 > k4_xboole_0 > k3_subset_1 > k2_xboole_0 > #nlpp > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 3.49/1.68  
% 3.49/1.68  %Foreground sorts:
% 3.49/1.68  
% 3.49/1.68  
% 3.49/1.68  %Background operators:
% 3.49/1.68  
% 3.49/1.68  
% 3.49/1.68  %Foreground operators:
% 3.49/1.68  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.49/1.68  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.49/1.68  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.49/1.68  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.49/1.68  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 3.49/1.68  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 3.49/1.68  tff('#skF_2', type, '#skF_2': $i).
% 3.49/1.68  tff('#skF_3', type, '#skF_3': $i).
% 3.49/1.68  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.49/1.68  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.49/1.68  tff('#skF_4', type, '#skF_4': $i).
% 3.49/1.68  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.49/1.68  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.49/1.68  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.49/1.68  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.49/1.68  
% 3.49/1.70  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 3.49/1.70  tff(f_36, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(A, k2_xboole_0(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_xboole_1)).
% 3.49/1.70  tff(f_66, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => r1_tarski(k3_subset_1(A, k4_subset_1(A, B, C)), k3_subset_1(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_subset_1)).
% 3.49/1.70  tff(f_46, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 3.49/1.70  tff(f_58, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 3.49/1.70  tff(f_52, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => m1_subset_1(k4_subset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k4_subset_1)).
% 3.49/1.70  tff(f_38, axiom, (![A, B, C]: (k4_xboole_0(k4_xboole_0(A, B), C) = k4_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_xboole_1)).
% 3.49/1.70  tff(f_42, axiom, (![A, B, C]: (r1_tarski(A, k2_xboole_0(B, C)) => r1_tarski(k4_xboole_0(A, B), C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_xboole_1)).
% 3.49/1.70  tff(c_27, plain, (![A_29, B_30]: (r2_hidden('#skF_1'(A_29, B_30), A_29) | r1_tarski(A_29, B_30))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.49/1.70  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.49/1.70  tff(c_32, plain, (![A_29]: (r1_tarski(A_29, A_29))), inference(resolution, [status(thm)], [c_27, c_4])).
% 3.49/1.70  tff(c_8, plain, (![A_6, C_8, B_7]: (r1_tarski(A_6, k2_xboole_0(C_8, B_7)) | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.49/1.70  tff(c_24, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.49/1.70  tff(c_59, plain, (![A_41, B_42]: (k4_xboole_0(A_41, B_42)=k3_subset_1(A_41, B_42) | ~m1_subset_1(B_42, k1_zfmisc_1(A_41)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.49/1.70  tff(c_67, plain, (k4_xboole_0('#skF_2', '#skF_3')=k3_subset_1('#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_24, c_59])).
% 3.49/1.70  tff(c_22, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.49/1.70  tff(c_105, plain, (![A_45, B_46, C_47]: (k4_subset_1(A_45, B_46, C_47)=k2_xboole_0(B_46, C_47) | ~m1_subset_1(C_47, k1_zfmisc_1(A_45)) | ~m1_subset_1(B_46, k1_zfmisc_1(A_45)))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.49/1.70  tff(c_146, plain, (![B_51]: (k4_subset_1('#skF_2', B_51, '#skF_4')=k2_xboole_0(B_51, '#skF_4') | ~m1_subset_1(B_51, k1_zfmisc_1('#skF_2')))), inference(resolution, [status(thm)], [c_22, c_105])).
% 3.49/1.70  tff(c_154, plain, (k4_subset_1('#skF_2', '#skF_3', '#skF_4')=k2_xboole_0('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_24, c_146])).
% 3.49/1.70  tff(c_164, plain, (![A_52, B_53, C_54]: (m1_subset_1(k4_subset_1(A_52, B_53, C_54), k1_zfmisc_1(A_52)) | ~m1_subset_1(C_54, k1_zfmisc_1(A_52)) | ~m1_subset_1(B_53, k1_zfmisc_1(A_52)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.49/1.70  tff(c_180, plain, (m1_subset_1(k2_xboole_0('#skF_3', '#skF_4'), k1_zfmisc_1('#skF_2')) | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_2')) | ~m1_subset_1('#skF_3', k1_zfmisc_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_154, c_164])).
% 3.49/1.70  tff(c_195, plain, (m1_subset_1(k2_xboole_0('#skF_3', '#skF_4'), k1_zfmisc_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_22, c_180])).
% 3.49/1.70  tff(c_14, plain, (![A_15, B_16]: (k4_xboole_0(A_15, B_16)=k3_subset_1(A_15, B_16) | ~m1_subset_1(B_16, k1_zfmisc_1(A_15)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.49/1.70  tff(c_216, plain, (k4_xboole_0('#skF_2', k2_xboole_0('#skF_3', '#skF_4'))=k3_subset_1('#skF_2', k2_xboole_0('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_195, c_14])).
% 3.49/1.70  tff(c_10, plain, (![A_9, B_10, C_11]: (k4_xboole_0(k4_xboole_0(A_9, B_10), C_11)=k4_xboole_0(A_9, k2_xboole_0(B_10, C_11)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.49/1.70  tff(c_55, plain, (![A_38, B_39, C_40]: (r1_tarski(k4_xboole_0(A_38, B_39), C_40) | ~r1_tarski(A_38, k2_xboole_0(B_39, C_40)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.49/1.70  tff(c_549, plain, (![A_62, B_63, C_64, C_65]: (r1_tarski(k4_xboole_0(A_62, k2_xboole_0(B_63, C_64)), C_65) | ~r1_tarski(k4_xboole_0(A_62, B_63), k2_xboole_0(C_64, C_65)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_55])).
% 3.49/1.70  tff(c_558, plain, (![C_65]: (r1_tarski(k3_subset_1('#skF_2', k2_xboole_0('#skF_3', '#skF_4')), C_65) | ~r1_tarski(k4_xboole_0('#skF_2', '#skF_3'), k2_xboole_0('#skF_4', C_65)))), inference(superposition, [status(thm), theory('equality')], [c_216, c_549])).
% 3.49/1.70  tff(c_1236, plain, (![C_97]: (r1_tarski(k3_subset_1('#skF_2', k2_xboole_0('#skF_3', '#skF_4')), C_97) | ~r1_tarski(k3_subset_1('#skF_2', '#skF_3'), k2_xboole_0('#skF_4', C_97)))), inference(demodulation, [status(thm), theory('equality')], [c_67, c_558])).
% 3.49/1.70  tff(c_20, plain, (~r1_tarski(k3_subset_1('#skF_2', k4_subset_1('#skF_2', '#skF_3', '#skF_4')), k3_subset_1('#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.49/1.70  tff(c_159, plain, (~r1_tarski(k3_subset_1('#skF_2', k2_xboole_0('#skF_3', '#skF_4')), k3_subset_1('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_154, c_20])).
% 3.49/1.70  tff(c_1243, plain, (~r1_tarski(k3_subset_1('#skF_2', '#skF_3'), k2_xboole_0('#skF_4', k3_subset_1('#skF_2', '#skF_3')))), inference(resolution, [status(thm)], [c_1236, c_159])).
% 3.49/1.70  tff(c_1305, plain, (~r1_tarski(k3_subset_1('#skF_2', '#skF_3'), k3_subset_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_8, c_1243])).
% 3.49/1.70  tff(c_1310, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_32, c_1305])).
% 3.49/1.70  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.49/1.70  
% 3.49/1.70  Inference rules
% 3.49/1.70  ----------------------
% 3.49/1.70  #Ref     : 0
% 3.49/1.70  #Sup     : 353
% 3.49/1.70  #Fact    : 0
% 3.49/1.70  #Define  : 0
% 3.49/1.70  #Split   : 0
% 3.49/1.70  #Chain   : 0
% 3.49/1.70  #Close   : 0
% 3.49/1.70  
% 3.49/1.70  Ordering : KBO
% 3.49/1.70  
% 3.49/1.70  Simplification rules
% 3.49/1.70  ----------------------
% 3.49/1.70  #Subsume      : 3
% 3.49/1.70  #Demod        : 142
% 3.49/1.70  #Tautology    : 74
% 3.49/1.70  #SimpNegUnit  : 0
% 3.49/1.70  #BackRed      : 1
% 3.49/1.70  
% 3.49/1.70  #Partial instantiations: 0
% 3.49/1.70  #Strategies tried      : 1
% 3.49/1.70  
% 3.49/1.70  Timing (in seconds)
% 3.49/1.70  ----------------------
% 3.49/1.70  Preprocessing        : 0.29
% 3.49/1.70  Parsing              : 0.15
% 3.49/1.70  CNF conversion       : 0.02
% 3.49/1.70  Main loop            : 0.51
% 3.49/1.70  Inferencing          : 0.17
% 3.49/1.70  Reduction            : 0.18
% 3.49/1.70  Demodulation         : 0.13
% 3.49/1.70  BG Simplification    : 0.02
% 3.49/1.70  Subsumption          : 0.10
% 3.49/1.70  Abstraction          : 0.03
% 3.49/1.70  MUC search           : 0.00
% 3.49/1.70  Cooper               : 0.00
% 3.49/1.70  Total                : 0.83
% 3.49/1.70  Index Insertion      : 0.00
% 3.49/1.70  Index Deletion       : 0.00
% 3.49/1.70  Index Matching       : 0.00
% 3.49/1.70  BG Taut test         : 0.00
%------------------------------------------------------------------------------
