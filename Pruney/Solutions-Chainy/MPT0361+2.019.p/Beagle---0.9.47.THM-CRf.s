%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:56:29 EST 2020

% Result     : Theorem 4.84s
% Output     : CNFRefutation 5.16s
% Verified   : 
% Statistics : Number of formulae       :   53 ( 104 expanded)
%              Number of leaves         :   21 (  44 expanded)
%              Depth                    :   10
%              Number of atoms          :   75 ( 185 expanded)
%              Number of equality atoms :   14 (  29 expanded)
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

tff(f_70,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => ! [C] :
            ( m1_subset_1(C,k1_zfmisc_1(A))
           => r1_tarski(k3_subset_1(A,k4_subset_1(A,B,C)),k3_subset_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_subset_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_53,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => m1_subset_1(k4_subset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_subset_1)).

tff(f_29,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k3_subset_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,k3_subset_1(A,B)) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

tff(f_62,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(A))
         => ( r1_tarski(k3_subset_1(A,B),C)
           => r1_tarski(k3_subset_1(A,C),B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_subset_1)).

tff(c_22,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_20,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_200,plain,(
    ! [A_41,B_42,C_43] :
      ( k4_subset_1(A_41,B_42,C_43) = k2_xboole_0(B_42,C_43)
      | ~ m1_subset_1(C_43,k1_zfmisc_1(A_41))
      | ~ m1_subset_1(B_42,k1_zfmisc_1(A_41)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_213,plain,(
    ! [B_44] :
      ( k4_subset_1('#skF_1',B_44,'#skF_3') = k2_xboole_0(B_44,'#skF_3')
      | ~ m1_subset_1(B_44,k1_zfmisc_1('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_20,c_200])).

tff(c_227,plain,(
    k4_subset_1('#skF_1','#skF_2','#skF_3') = k2_xboole_0('#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_22,c_213])).

tff(c_234,plain,(
    k4_subset_1('#skF_1','#skF_2','#skF_3') = k2_xboole_0('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_227])).

tff(c_10,plain,(
    ! [A_9,B_10,C_11] :
      ( m1_subset_1(k4_subset_1(A_9,B_10,C_11),k1_zfmisc_1(A_9))
      | ~ m1_subset_1(C_11,k1_zfmisc_1(A_9))
      | ~ m1_subset_1(B_10,k1_zfmisc_1(A_9)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_264,plain,
    ( m1_subset_1(k2_xboole_0('#skF_3','#skF_2'),k1_zfmisc_1('#skF_1'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1('#skF_1'))
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_234,c_10])).

tff(c_268,plain,(
    m1_subset_1(k2_xboole_0('#skF_3','#skF_2'),k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_20,c_264])).

tff(c_24,plain,(
    ! [B_24,A_25] : k2_xboole_0(B_24,A_25) = k2_xboole_0(A_25,B_24) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_4,plain,(
    ! [A_3,B_4] : r1_tarski(A_3,k2_xboole_0(A_3,B_4)) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_39,plain,(
    ! [A_25,B_24] : r1_tarski(A_25,k2_xboole_0(B_24,A_25)) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_4])).

tff(c_8,plain,(
    ! [A_7,B_8] :
      ( m1_subset_1(k3_subset_1(A_7,B_8),k1_zfmisc_1(A_7))
      | ~ m1_subset_1(B_8,k1_zfmisc_1(A_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_419,plain,(
    ! [A_49,B_50,B_51] :
      ( k4_subset_1(A_49,B_50,k3_subset_1(A_49,B_51)) = k2_xboole_0(B_50,k3_subset_1(A_49,B_51))
      | ~ m1_subset_1(B_50,k1_zfmisc_1(A_49))
      | ~ m1_subset_1(B_51,k1_zfmisc_1(A_49)) ) ),
    inference(resolution,[status(thm)],[c_8,c_200])).

tff(c_472,plain,(
    ! [B_52] :
      ( k4_subset_1('#skF_1','#skF_3',k3_subset_1('#skF_1',B_52)) = k2_xboole_0('#skF_3',k3_subset_1('#skF_1',B_52))
      | ~ m1_subset_1(B_52,k1_zfmisc_1('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_20,c_419])).

tff(c_502,plain,(
    k4_subset_1('#skF_1','#skF_3',k3_subset_1('#skF_1','#skF_2')) = k2_xboole_0('#skF_3',k3_subset_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_22,c_472])).

tff(c_545,plain,
    ( m1_subset_1(k2_xboole_0('#skF_3',k3_subset_1('#skF_1','#skF_2')),k1_zfmisc_1('#skF_1'))
    | ~ m1_subset_1(k3_subset_1('#skF_1','#skF_2'),k1_zfmisc_1('#skF_1'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_502,c_10])).

tff(c_549,plain,
    ( m1_subset_1(k2_xboole_0('#skF_3',k3_subset_1('#skF_1','#skF_2')),k1_zfmisc_1('#skF_1'))
    | ~ m1_subset_1(k3_subset_1('#skF_1','#skF_2'),k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_545])).

tff(c_1205,plain,(
    ~ m1_subset_1(k3_subset_1('#skF_1','#skF_2'),k1_zfmisc_1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_549])).

tff(c_1208,plain,(
    ~ m1_subset_1('#skF_2',k1_zfmisc_1('#skF_1')) ),
    inference(resolution,[status(thm)],[c_8,c_1205])).

tff(c_1212,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_1208])).

tff(c_1214,plain,(
    m1_subset_1(k3_subset_1('#skF_1','#skF_2'),k1_zfmisc_1('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_549])).

tff(c_95,plain,(
    ! [A_32,B_33] :
      ( k3_subset_1(A_32,k3_subset_1(A_32,B_33)) = B_33
      | ~ m1_subset_1(B_33,k1_zfmisc_1(A_32)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_104,plain,(
    k3_subset_1('#skF_1',k3_subset_1('#skF_1','#skF_2')) = '#skF_2' ),
    inference(resolution,[status(thm)],[c_22,c_95])).

tff(c_288,plain,(
    ! [A_45,C_46,B_47] :
      ( r1_tarski(k3_subset_1(A_45,C_46),B_47)
      | ~ r1_tarski(k3_subset_1(A_45,B_47),C_46)
      | ~ m1_subset_1(C_46,k1_zfmisc_1(A_45))
      | ~ m1_subset_1(B_47,k1_zfmisc_1(A_45)) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_292,plain,(
    ! [C_46] :
      ( r1_tarski(k3_subset_1('#skF_1',C_46),k3_subset_1('#skF_1','#skF_2'))
      | ~ r1_tarski('#skF_2',C_46)
      | ~ m1_subset_1(C_46,k1_zfmisc_1('#skF_1'))
      | ~ m1_subset_1(k3_subset_1('#skF_1','#skF_2'),k1_zfmisc_1('#skF_1')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_104,c_288])).

tff(c_2452,plain,(
    ! [C_78] :
      ( r1_tarski(k3_subset_1('#skF_1',C_78),k3_subset_1('#skF_1','#skF_2'))
      | ~ r1_tarski('#skF_2',C_78)
      | ~ m1_subset_1(C_78,k1_zfmisc_1('#skF_1')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1214,c_292])).

tff(c_18,plain,(
    ~ r1_tarski(k3_subset_1('#skF_1',k4_subset_1('#skF_1','#skF_2','#skF_3')),k3_subset_1('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_260,plain,(
    ~ r1_tarski(k3_subset_1('#skF_1',k2_xboole_0('#skF_3','#skF_2')),k3_subset_1('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_234,c_18])).

tff(c_2455,plain,
    ( ~ r1_tarski('#skF_2',k2_xboole_0('#skF_3','#skF_2'))
    | ~ m1_subset_1(k2_xboole_0('#skF_3','#skF_2'),k1_zfmisc_1('#skF_1')) ),
    inference(resolution,[status(thm)],[c_2452,c_260])).

tff(c_2511,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_268,c_39,c_2455])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n016.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 20:04:34 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.84/1.94  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.16/1.95  
% 5.16/1.95  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.16/1.95  %$ r1_tarski > m1_subset_1 > k4_subset_1 > k4_xboole_0 > k3_subset_1 > k2_xboole_0 > #nlpp > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1
% 5.16/1.95  
% 5.16/1.95  %Foreground sorts:
% 5.16/1.95  
% 5.16/1.95  
% 5.16/1.95  %Background operators:
% 5.16/1.95  
% 5.16/1.95  
% 5.16/1.95  %Foreground operators:
% 5.16/1.95  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.16/1.95  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 5.16/1.95  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.16/1.95  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 5.16/1.95  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 5.16/1.95  tff('#skF_2', type, '#skF_2': $i).
% 5.16/1.95  tff('#skF_3', type, '#skF_3': $i).
% 5.16/1.95  tff('#skF_1', type, '#skF_1': $i).
% 5.16/1.95  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.16/1.95  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.16/1.95  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.16/1.95  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 5.16/1.95  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.16/1.95  
% 5.16/1.97  tff(f_70, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => r1_tarski(k3_subset_1(A, k4_subset_1(A, B, C)), k3_subset_1(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_subset_1)).
% 5.16/1.97  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 5.16/1.97  tff(f_53, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 5.16/1.97  tff(f_43, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => m1_subset_1(k4_subset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k4_subset_1)).
% 5.16/1.97  tff(f_29, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 5.16/1.97  tff(f_37, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k3_subset_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 5.16/1.97  tff(f_47, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, k3_subset_1(A, B)) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 5.16/1.97  tff(f_62, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (r1_tarski(k3_subset_1(A, B), C) => r1_tarski(k3_subset_1(A, C), B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_subset_1)).
% 5.16/1.97  tff(c_22, plain, (m1_subset_1('#skF_2', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_70])).
% 5.16/1.97  tff(c_20, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_70])).
% 5.16/1.97  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 5.16/1.97  tff(c_200, plain, (![A_41, B_42, C_43]: (k4_subset_1(A_41, B_42, C_43)=k2_xboole_0(B_42, C_43) | ~m1_subset_1(C_43, k1_zfmisc_1(A_41)) | ~m1_subset_1(B_42, k1_zfmisc_1(A_41)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 5.16/1.97  tff(c_213, plain, (![B_44]: (k4_subset_1('#skF_1', B_44, '#skF_3')=k2_xboole_0(B_44, '#skF_3') | ~m1_subset_1(B_44, k1_zfmisc_1('#skF_1')))), inference(resolution, [status(thm)], [c_20, c_200])).
% 5.16/1.97  tff(c_227, plain, (k4_subset_1('#skF_1', '#skF_2', '#skF_3')=k2_xboole_0('#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_22, c_213])).
% 5.16/1.97  tff(c_234, plain, (k4_subset_1('#skF_1', '#skF_2', '#skF_3')=k2_xboole_0('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_227])).
% 5.16/1.97  tff(c_10, plain, (![A_9, B_10, C_11]: (m1_subset_1(k4_subset_1(A_9, B_10, C_11), k1_zfmisc_1(A_9)) | ~m1_subset_1(C_11, k1_zfmisc_1(A_9)) | ~m1_subset_1(B_10, k1_zfmisc_1(A_9)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 5.16/1.97  tff(c_264, plain, (m1_subset_1(k2_xboole_0('#skF_3', '#skF_2'), k1_zfmisc_1('#skF_1')) | ~m1_subset_1('#skF_3', k1_zfmisc_1('#skF_1')) | ~m1_subset_1('#skF_2', k1_zfmisc_1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_234, c_10])).
% 5.16/1.97  tff(c_268, plain, (m1_subset_1(k2_xboole_0('#skF_3', '#skF_2'), k1_zfmisc_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_20, c_264])).
% 5.16/1.97  tff(c_24, plain, (![B_24, A_25]: (k2_xboole_0(B_24, A_25)=k2_xboole_0(A_25, B_24))), inference(cnfTransformation, [status(thm)], [f_27])).
% 5.16/1.97  tff(c_4, plain, (![A_3, B_4]: (r1_tarski(A_3, k2_xboole_0(A_3, B_4)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 5.16/1.97  tff(c_39, plain, (![A_25, B_24]: (r1_tarski(A_25, k2_xboole_0(B_24, A_25)))), inference(superposition, [status(thm), theory('equality')], [c_24, c_4])).
% 5.16/1.97  tff(c_8, plain, (![A_7, B_8]: (m1_subset_1(k3_subset_1(A_7, B_8), k1_zfmisc_1(A_7)) | ~m1_subset_1(B_8, k1_zfmisc_1(A_7)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 5.16/1.97  tff(c_419, plain, (![A_49, B_50, B_51]: (k4_subset_1(A_49, B_50, k3_subset_1(A_49, B_51))=k2_xboole_0(B_50, k3_subset_1(A_49, B_51)) | ~m1_subset_1(B_50, k1_zfmisc_1(A_49)) | ~m1_subset_1(B_51, k1_zfmisc_1(A_49)))), inference(resolution, [status(thm)], [c_8, c_200])).
% 5.16/1.97  tff(c_472, plain, (![B_52]: (k4_subset_1('#skF_1', '#skF_3', k3_subset_1('#skF_1', B_52))=k2_xboole_0('#skF_3', k3_subset_1('#skF_1', B_52)) | ~m1_subset_1(B_52, k1_zfmisc_1('#skF_1')))), inference(resolution, [status(thm)], [c_20, c_419])).
% 5.16/1.97  tff(c_502, plain, (k4_subset_1('#skF_1', '#skF_3', k3_subset_1('#skF_1', '#skF_2'))=k2_xboole_0('#skF_3', k3_subset_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_22, c_472])).
% 5.16/1.97  tff(c_545, plain, (m1_subset_1(k2_xboole_0('#skF_3', k3_subset_1('#skF_1', '#skF_2')), k1_zfmisc_1('#skF_1')) | ~m1_subset_1(k3_subset_1('#skF_1', '#skF_2'), k1_zfmisc_1('#skF_1')) | ~m1_subset_1('#skF_3', k1_zfmisc_1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_502, c_10])).
% 5.16/1.97  tff(c_549, plain, (m1_subset_1(k2_xboole_0('#skF_3', k3_subset_1('#skF_1', '#skF_2')), k1_zfmisc_1('#skF_1')) | ~m1_subset_1(k3_subset_1('#skF_1', '#skF_2'), k1_zfmisc_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_545])).
% 5.16/1.97  tff(c_1205, plain, (~m1_subset_1(k3_subset_1('#skF_1', '#skF_2'), k1_zfmisc_1('#skF_1'))), inference(splitLeft, [status(thm)], [c_549])).
% 5.16/1.97  tff(c_1208, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1('#skF_1'))), inference(resolution, [status(thm)], [c_8, c_1205])).
% 5.16/1.97  tff(c_1212, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_22, c_1208])).
% 5.16/1.97  tff(c_1214, plain, (m1_subset_1(k3_subset_1('#skF_1', '#skF_2'), k1_zfmisc_1('#skF_1'))), inference(splitRight, [status(thm)], [c_549])).
% 5.16/1.97  tff(c_95, plain, (![A_32, B_33]: (k3_subset_1(A_32, k3_subset_1(A_32, B_33))=B_33 | ~m1_subset_1(B_33, k1_zfmisc_1(A_32)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 5.16/1.97  tff(c_104, plain, (k3_subset_1('#skF_1', k3_subset_1('#skF_1', '#skF_2'))='#skF_2'), inference(resolution, [status(thm)], [c_22, c_95])).
% 5.16/1.97  tff(c_288, plain, (![A_45, C_46, B_47]: (r1_tarski(k3_subset_1(A_45, C_46), B_47) | ~r1_tarski(k3_subset_1(A_45, B_47), C_46) | ~m1_subset_1(C_46, k1_zfmisc_1(A_45)) | ~m1_subset_1(B_47, k1_zfmisc_1(A_45)))), inference(cnfTransformation, [status(thm)], [f_62])).
% 5.16/1.97  tff(c_292, plain, (![C_46]: (r1_tarski(k3_subset_1('#skF_1', C_46), k3_subset_1('#skF_1', '#skF_2')) | ~r1_tarski('#skF_2', C_46) | ~m1_subset_1(C_46, k1_zfmisc_1('#skF_1')) | ~m1_subset_1(k3_subset_1('#skF_1', '#skF_2'), k1_zfmisc_1('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_104, c_288])).
% 5.16/1.97  tff(c_2452, plain, (![C_78]: (r1_tarski(k3_subset_1('#skF_1', C_78), k3_subset_1('#skF_1', '#skF_2')) | ~r1_tarski('#skF_2', C_78) | ~m1_subset_1(C_78, k1_zfmisc_1('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_1214, c_292])).
% 5.16/1.97  tff(c_18, plain, (~r1_tarski(k3_subset_1('#skF_1', k4_subset_1('#skF_1', '#skF_2', '#skF_3')), k3_subset_1('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_70])).
% 5.16/1.97  tff(c_260, plain, (~r1_tarski(k3_subset_1('#skF_1', k2_xboole_0('#skF_3', '#skF_2')), k3_subset_1('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_234, c_18])).
% 5.16/1.97  tff(c_2455, plain, (~r1_tarski('#skF_2', k2_xboole_0('#skF_3', '#skF_2')) | ~m1_subset_1(k2_xboole_0('#skF_3', '#skF_2'), k1_zfmisc_1('#skF_1'))), inference(resolution, [status(thm)], [c_2452, c_260])).
% 5.16/1.97  tff(c_2511, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_268, c_39, c_2455])).
% 5.16/1.97  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.16/1.97  
% 5.16/1.97  Inference rules
% 5.16/1.97  ----------------------
% 5.16/1.97  #Ref     : 0
% 5.16/1.97  #Sup     : 662
% 5.16/1.97  #Fact    : 0
% 5.16/1.97  #Define  : 0
% 5.16/1.97  #Split   : 2
% 5.16/1.97  #Chain   : 0
% 5.16/1.97  #Close   : 0
% 5.16/1.97  
% 5.16/1.97  Ordering : KBO
% 5.16/1.97  
% 5.16/1.97  Simplification rules
% 5.16/1.97  ----------------------
% 5.16/1.97  #Subsume      : 14
% 5.16/1.97  #Demod        : 431
% 5.16/1.97  #Tautology    : 227
% 5.16/1.97  #SimpNegUnit  : 0
% 5.16/1.97  #BackRed      : 1
% 5.16/1.97  
% 5.16/1.97  #Partial instantiations: 0
% 5.16/1.97  #Strategies tried      : 1
% 5.16/1.97  
% 5.16/1.97  Timing (in seconds)
% 5.16/1.97  ----------------------
% 5.16/1.98  Preprocessing        : 0.29
% 5.16/1.98  Parsing              : 0.16
% 5.33/1.98  CNF conversion       : 0.02
% 5.33/1.98  Main loop            : 0.90
% 5.33/1.98  Inferencing          : 0.24
% 5.33/1.98  Reduction            : 0.37
% 5.33/1.98  Demodulation         : 0.30
% 5.33/1.98  BG Simplification    : 0.03
% 5.33/1.98  Subsumption          : 0.18
% 5.33/1.98  Abstraction          : 0.05
% 5.33/1.98  MUC search           : 0.00
% 5.33/1.98  Cooper               : 0.00
% 5.33/1.98  Total                : 1.24
% 5.33/1.98  Index Insertion      : 0.00
% 5.33/1.98  Index Deletion       : 0.00
% 5.33/1.98  Index Matching       : 0.00
% 5.33/1.98  BG Taut test         : 0.00
%------------------------------------------------------------------------------
