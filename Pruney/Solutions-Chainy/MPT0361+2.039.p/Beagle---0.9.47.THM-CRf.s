%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:56:32 EST 2020

% Result     : Theorem 4.56s
% Output     : CNFRefutation 4.56s
% Verified   : 
% Statistics : Number of formulae       :   50 (  96 expanded)
%              Number of leaves         :   21 (  42 expanded)
%              Depth                    :   10
%              Number of atoms          :   73 ( 176 expanded)
%              Number of equality atoms :   10 (  21 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > m1_subset_1 > k4_subset_1 > k3_subset_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

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

tff(f_66,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => ! [C] :
            ( m1_subset_1(C,k1_zfmisc_1(A))
           => r1_tarski(k3_subset_1(A,k4_subset_1(A,B,C)),k3_subset_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_subset_1)).

tff(f_49,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => m1_subset_1(k4_subset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_subset_1)).

tff(f_27,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k3_subset_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,k3_subset_1(A,B)) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

tff(f_58,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(A))
         => ( r1_tarski(k3_subset_1(A,B),C)
           => r1_tarski(k3_subset_1(A,C),B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_subset_1)).

tff(c_20,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_18,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_58,plain,(
    ! [A_28,B_29,C_30] :
      ( k4_subset_1(A_28,B_29,C_30) = k2_xboole_0(B_29,C_30)
      | ~ m1_subset_1(C_30,k1_zfmisc_1(A_28))
      | ~ m1_subset_1(B_29,k1_zfmisc_1(A_28)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_68,plain,(
    ! [B_31] :
      ( k4_subset_1('#skF_1',B_31,'#skF_3') = k2_xboole_0(B_31,'#skF_3')
      | ~ m1_subset_1(B_31,k1_zfmisc_1('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_18,c_58])).

tff(c_81,plain,(
    k4_subset_1('#skF_1','#skF_2','#skF_3') = k2_xboole_0('#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_20,c_68])).

tff(c_105,plain,(
    ! [A_33,B_34,C_35] :
      ( m1_subset_1(k4_subset_1(A_33,B_34,C_35),k1_zfmisc_1(A_33))
      | ~ m1_subset_1(C_35,k1_zfmisc_1(A_33))
      | ~ m1_subset_1(B_34,k1_zfmisc_1(A_33)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_120,plain,
    ( m1_subset_1(k2_xboole_0('#skF_2','#skF_3'),k1_zfmisc_1('#skF_1'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1('#skF_1'))
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_81,c_105])).

tff(c_129,plain,(
    m1_subset_1(k2_xboole_0('#skF_2','#skF_3'),k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_18,c_120])).

tff(c_2,plain,(
    ! [A_1,B_2] : r1_tarski(A_1,k2_xboole_0(A_1,B_2)) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_6,plain,(
    ! [A_5,B_6] :
      ( m1_subset_1(k3_subset_1(A_5,B_6),k1_zfmisc_1(A_5))
      | ~ m1_subset_1(B_6,k1_zfmisc_1(A_5)) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_549,plain,(
    ! [A_41,B_42,B_43] :
      ( k4_subset_1(A_41,B_42,k3_subset_1(A_41,B_43)) = k2_xboole_0(B_42,k3_subset_1(A_41,B_43))
      | ~ m1_subset_1(B_42,k1_zfmisc_1(A_41))
      | ~ m1_subset_1(B_43,k1_zfmisc_1(A_41)) ) ),
    inference(resolution,[status(thm)],[c_6,c_58])).

tff(c_658,plain,(
    ! [B_44] :
      ( k4_subset_1('#skF_1','#skF_3',k3_subset_1('#skF_1',B_44)) = k2_xboole_0('#skF_3',k3_subset_1('#skF_1',B_44))
      | ~ m1_subset_1(B_44,k1_zfmisc_1('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_18,c_549])).

tff(c_724,plain,(
    k4_subset_1('#skF_1','#skF_3',k3_subset_1('#skF_1','#skF_2')) = k2_xboole_0('#skF_3',k3_subset_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_20,c_658])).

tff(c_8,plain,(
    ! [A_7,B_8,C_9] :
      ( m1_subset_1(k4_subset_1(A_7,B_8,C_9),k1_zfmisc_1(A_7))
      | ~ m1_subset_1(C_9,k1_zfmisc_1(A_7))
      | ~ m1_subset_1(B_8,k1_zfmisc_1(A_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_737,plain,
    ( m1_subset_1(k2_xboole_0('#skF_3',k3_subset_1('#skF_1','#skF_2')),k1_zfmisc_1('#skF_1'))
    | ~ m1_subset_1(k3_subset_1('#skF_1','#skF_2'),k1_zfmisc_1('#skF_1'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_724,c_8])).

tff(c_741,plain,
    ( m1_subset_1(k2_xboole_0('#skF_3',k3_subset_1('#skF_1','#skF_2')),k1_zfmisc_1('#skF_1'))
    | ~ m1_subset_1(k3_subset_1('#skF_1','#skF_2'),k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_737])).

tff(c_1148,plain,(
    ~ m1_subset_1(k3_subset_1('#skF_1','#skF_2'),k1_zfmisc_1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_741])).

tff(c_1151,plain,(
    ~ m1_subset_1('#skF_2',k1_zfmisc_1('#skF_1')) ),
    inference(resolution,[status(thm)],[c_6,c_1148])).

tff(c_1155,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_1151])).

tff(c_1157,plain,(
    m1_subset_1(k3_subset_1('#skF_1','#skF_2'),k1_zfmisc_1('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_741])).

tff(c_32,plain,(
    ! [A_26,B_27] :
      ( k3_subset_1(A_26,k3_subset_1(A_26,B_27)) = B_27
      | ~ m1_subset_1(B_27,k1_zfmisc_1(A_26)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_41,plain,(
    k3_subset_1('#skF_1',k3_subset_1('#skF_1','#skF_2')) = '#skF_2' ),
    inference(resolution,[status(thm)],[c_20,c_32])).

tff(c_230,plain,(
    ! [A_36,C_37,B_38] :
      ( r1_tarski(k3_subset_1(A_36,C_37),B_38)
      | ~ r1_tarski(k3_subset_1(A_36,B_38),C_37)
      | ~ m1_subset_1(C_37,k1_zfmisc_1(A_36))
      | ~ m1_subset_1(B_38,k1_zfmisc_1(A_36)) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_238,plain,(
    ! [C_37] :
      ( r1_tarski(k3_subset_1('#skF_1',C_37),k3_subset_1('#skF_1','#skF_2'))
      | ~ r1_tarski('#skF_2',C_37)
      | ~ m1_subset_1(C_37,k1_zfmisc_1('#skF_1'))
      | ~ m1_subset_1(k3_subset_1('#skF_1','#skF_2'),k1_zfmisc_1('#skF_1')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_41,c_230])).

tff(c_2466,plain,(
    ! [C_62] :
      ( r1_tarski(k3_subset_1('#skF_1',C_62),k3_subset_1('#skF_1','#skF_2'))
      | ~ r1_tarski('#skF_2',C_62)
      | ~ m1_subset_1(C_62,k1_zfmisc_1('#skF_1')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1157,c_238])).

tff(c_16,plain,(
    ~ r1_tarski(k3_subset_1('#skF_1',k4_subset_1('#skF_1','#skF_2','#skF_3')),k3_subset_1('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_86,plain,(
    ~ r1_tarski(k3_subset_1('#skF_1',k2_xboole_0('#skF_2','#skF_3')),k3_subset_1('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_81,c_16])).

tff(c_2471,plain,
    ( ~ r1_tarski('#skF_2',k2_xboole_0('#skF_2','#skF_3'))
    | ~ m1_subset_1(k2_xboole_0('#skF_2','#skF_3'),k1_zfmisc_1('#skF_1')) ),
    inference(resolution,[status(thm)],[c_2466,c_86])).

tff(c_2552,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_129,c_2,c_2471])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n004.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 09:32:38 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.56/1.86  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.56/1.86  
% 4.56/1.86  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.56/1.86  %$ r1_tarski > m1_subset_1 > k4_subset_1 > k3_subset_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1
% 4.56/1.86  
% 4.56/1.86  %Foreground sorts:
% 4.56/1.86  
% 4.56/1.86  
% 4.56/1.86  %Background operators:
% 4.56/1.86  
% 4.56/1.86  
% 4.56/1.86  %Foreground operators:
% 4.56/1.86  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.56/1.86  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.56/1.86  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.56/1.86  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 4.56/1.86  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 4.56/1.86  tff('#skF_2', type, '#skF_2': $i).
% 4.56/1.86  tff('#skF_3', type, '#skF_3': $i).
% 4.56/1.86  tff('#skF_1', type, '#skF_1': $i).
% 4.56/1.86  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.56/1.86  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.56/1.86  tff(k3_tarski, type, k3_tarski: $i > $i).
% 4.56/1.86  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.56/1.86  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.56/1.86  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.56/1.86  
% 4.56/1.87  tff(f_66, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => r1_tarski(k3_subset_1(A, k4_subset_1(A, B, C)), k3_subset_1(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_subset_1)).
% 4.56/1.87  tff(f_49, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 4.56/1.87  tff(f_39, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => m1_subset_1(k4_subset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k4_subset_1)).
% 4.56/1.87  tff(f_27, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 4.56/1.87  tff(f_33, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k3_subset_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 4.56/1.87  tff(f_43, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, k3_subset_1(A, B)) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 4.56/1.87  tff(f_58, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (r1_tarski(k3_subset_1(A, B), C) => r1_tarski(k3_subset_1(A, C), B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_subset_1)).
% 4.56/1.87  tff(c_20, plain, (m1_subset_1('#skF_2', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_66])).
% 4.56/1.87  tff(c_18, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_66])).
% 4.56/1.87  tff(c_58, plain, (![A_28, B_29, C_30]: (k4_subset_1(A_28, B_29, C_30)=k2_xboole_0(B_29, C_30) | ~m1_subset_1(C_30, k1_zfmisc_1(A_28)) | ~m1_subset_1(B_29, k1_zfmisc_1(A_28)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 4.56/1.87  tff(c_68, plain, (![B_31]: (k4_subset_1('#skF_1', B_31, '#skF_3')=k2_xboole_0(B_31, '#skF_3') | ~m1_subset_1(B_31, k1_zfmisc_1('#skF_1')))), inference(resolution, [status(thm)], [c_18, c_58])).
% 4.56/1.87  tff(c_81, plain, (k4_subset_1('#skF_1', '#skF_2', '#skF_3')=k2_xboole_0('#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_20, c_68])).
% 4.56/1.87  tff(c_105, plain, (![A_33, B_34, C_35]: (m1_subset_1(k4_subset_1(A_33, B_34, C_35), k1_zfmisc_1(A_33)) | ~m1_subset_1(C_35, k1_zfmisc_1(A_33)) | ~m1_subset_1(B_34, k1_zfmisc_1(A_33)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.56/1.87  tff(c_120, plain, (m1_subset_1(k2_xboole_0('#skF_2', '#skF_3'), k1_zfmisc_1('#skF_1')) | ~m1_subset_1('#skF_3', k1_zfmisc_1('#skF_1')) | ~m1_subset_1('#skF_2', k1_zfmisc_1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_81, c_105])).
% 4.56/1.87  tff(c_129, plain, (m1_subset_1(k2_xboole_0('#skF_2', '#skF_3'), k1_zfmisc_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_18, c_120])).
% 4.56/1.87  tff(c_2, plain, (![A_1, B_2]: (r1_tarski(A_1, k2_xboole_0(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.56/1.87  tff(c_6, plain, (![A_5, B_6]: (m1_subset_1(k3_subset_1(A_5, B_6), k1_zfmisc_1(A_5)) | ~m1_subset_1(B_6, k1_zfmisc_1(A_5)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.56/1.87  tff(c_549, plain, (![A_41, B_42, B_43]: (k4_subset_1(A_41, B_42, k3_subset_1(A_41, B_43))=k2_xboole_0(B_42, k3_subset_1(A_41, B_43)) | ~m1_subset_1(B_42, k1_zfmisc_1(A_41)) | ~m1_subset_1(B_43, k1_zfmisc_1(A_41)))), inference(resolution, [status(thm)], [c_6, c_58])).
% 4.56/1.87  tff(c_658, plain, (![B_44]: (k4_subset_1('#skF_1', '#skF_3', k3_subset_1('#skF_1', B_44))=k2_xboole_0('#skF_3', k3_subset_1('#skF_1', B_44)) | ~m1_subset_1(B_44, k1_zfmisc_1('#skF_1')))), inference(resolution, [status(thm)], [c_18, c_549])).
% 4.56/1.87  tff(c_724, plain, (k4_subset_1('#skF_1', '#skF_3', k3_subset_1('#skF_1', '#skF_2'))=k2_xboole_0('#skF_3', k3_subset_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_20, c_658])).
% 4.56/1.87  tff(c_8, plain, (![A_7, B_8, C_9]: (m1_subset_1(k4_subset_1(A_7, B_8, C_9), k1_zfmisc_1(A_7)) | ~m1_subset_1(C_9, k1_zfmisc_1(A_7)) | ~m1_subset_1(B_8, k1_zfmisc_1(A_7)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.56/1.87  tff(c_737, plain, (m1_subset_1(k2_xboole_0('#skF_3', k3_subset_1('#skF_1', '#skF_2')), k1_zfmisc_1('#skF_1')) | ~m1_subset_1(k3_subset_1('#skF_1', '#skF_2'), k1_zfmisc_1('#skF_1')) | ~m1_subset_1('#skF_3', k1_zfmisc_1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_724, c_8])).
% 4.56/1.87  tff(c_741, plain, (m1_subset_1(k2_xboole_0('#skF_3', k3_subset_1('#skF_1', '#skF_2')), k1_zfmisc_1('#skF_1')) | ~m1_subset_1(k3_subset_1('#skF_1', '#skF_2'), k1_zfmisc_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_737])).
% 4.56/1.87  tff(c_1148, plain, (~m1_subset_1(k3_subset_1('#skF_1', '#skF_2'), k1_zfmisc_1('#skF_1'))), inference(splitLeft, [status(thm)], [c_741])).
% 4.56/1.87  tff(c_1151, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1('#skF_1'))), inference(resolution, [status(thm)], [c_6, c_1148])).
% 4.56/1.87  tff(c_1155, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_20, c_1151])).
% 4.56/1.87  tff(c_1157, plain, (m1_subset_1(k3_subset_1('#skF_1', '#skF_2'), k1_zfmisc_1('#skF_1'))), inference(splitRight, [status(thm)], [c_741])).
% 4.56/1.87  tff(c_32, plain, (![A_26, B_27]: (k3_subset_1(A_26, k3_subset_1(A_26, B_27))=B_27 | ~m1_subset_1(B_27, k1_zfmisc_1(A_26)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.56/1.87  tff(c_41, plain, (k3_subset_1('#skF_1', k3_subset_1('#skF_1', '#skF_2'))='#skF_2'), inference(resolution, [status(thm)], [c_20, c_32])).
% 4.56/1.87  tff(c_230, plain, (![A_36, C_37, B_38]: (r1_tarski(k3_subset_1(A_36, C_37), B_38) | ~r1_tarski(k3_subset_1(A_36, B_38), C_37) | ~m1_subset_1(C_37, k1_zfmisc_1(A_36)) | ~m1_subset_1(B_38, k1_zfmisc_1(A_36)))), inference(cnfTransformation, [status(thm)], [f_58])).
% 4.56/1.87  tff(c_238, plain, (![C_37]: (r1_tarski(k3_subset_1('#skF_1', C_37), k3_subset_1('#skF_1', '#skF_2')) | ~r1_tarski('#skF_2', C_37) | ~m1_subset_1(C_37, k1_zfmisc_1('#skF_1')) | ~m1_subset_1(k3_subset_1('#skF_1', '#skF_2'), k1_zfmisc_1('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_41, c_230])).
% 4.56/1.87  tff(c_2466, plain, (![C_62]: (r1_tarski(k3_subset_1('#skF_1', C_62), k3_subset_1('#skF_1', '#skF_2')) | ~r1_tarski('#skF_2', C_62) | ~m1_subset_1(C_62, k1_zfmisc_1('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_1157, c_238])).
% 4.56/1.87  tff(c_16, plain, (~r1_tarski(k3_subset_1('#skF_1', k4_subset_1('#skF_1', '#skF_2', '#skF_3')), k3_subset_1('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_66])).
% 4.56/1.87  tff(c_86, plain, (~r1_tarski(k3_subset_1('#skF_1', k2_xboole_0('#skF_2', '#skF_3')), k3_subset_1('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_81, c_16])).
% 4.56/1.87  tff(c_2471, plain, (~r1_tarski('#skF_2', k2_xboole_0('#skF_2', '#skF_3')) | ~m1_subset_1(k2_xboole_0('#skF_2', '#skF_3'), k1_zfmisc_1('#skF_1'))), inference(resolution, [status(thm)], [c_2466, c_86])).
% 4.56/1.87  tff(c_2552, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_129, c_2, c_2471])).
% 4.56/1.87  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.56/1.87  
% 4.56/1.87  Inference rules
% 4.56/1.87  ----------------------
% 4.56/1.87  #Ref     : 0
% 4.56/1.87  #Sup     : 688
% 4.56/1.87  #Fact    : 0
% 4.56/1.87  #Define  : 0
% 4.56/1.87  #Split   : 2
% 4.56/1.87  #Chain   : 0
% 4.56/1.87  #Close   : 0
% 4.56/1.87  
% 4.56/1.87  Ordering : KBO
% 4.56/1.87  
% 4.56/1.87  Simplification rules
% 4.56/1.87  ----------------------
% 4.56/1.87  #Subsume      : 2
% 4.56/1.87  #Demod        : 310
% 4.56/1.87  #Tautology    : 198
% 4.56/1.87  #SimpNegUnit  : 0
% 4.56/1.87  #BackRed      : 1
% 4.56/1.87  
% 4.56/1.87  #Partial instantiations: 0
% 4.56/1.87  #Strategies tried      : 1
% 4.56/1.88  
% 4.56/1.88  Timing (in seconds)
% 4.56/1.88  ----------------------
% 4.56/1.88  Preprocessing        : 0.31
% 4.56/1.88  Parsing              : 0.17
% 4.56/1.88  CNF conversion       : 0.02
% 4.56/1.88  Main loop            : 0.76
% 4.56/1.88  Inferencing          : 0.22
% 4.56/1.88  Reduction            : 0.26
% 4.56/1.88  Demodulation         : 0.20
% 4.56/1.88  BG Simplification    : 0.03
% 4.56/1.88  Subsumption          : 0.18
% 4.56/1.88  Abstraction          : 0.05
% 4.56/1.88  MUC search           : 0.00
% 4.56/1.88  Cooper               : 0.00
% 4.56/1.88  Total                : 1.10
% 4.56/1.88  Index Insertion      : 0.00
% 4.56/1.88  Index Deletion       : 0.00
% 4.56/1.88  Index Matching       : 0.00
% 4.56/1.88  BG Taut test         : 0.00
%------------------------------------------------------------------------------
