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
% DateTime   : Thu Dec  3 10:25:33 EST 2020

% Result     : Theorem 1.65s
% Output     : CNFRefutation 1.77s
% Verified   : 
% Statistics : Number of formulae       :   47 (  51 expanded)
%              Number of leaves         :   27 (  29 expanded)
%              Depth                    :    8
%              Number of atoms          :   46 (  50 expanded)
%              Number of equality atoms :   21 (  23 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > m1_subset_1 > v1_xboole_0 > k6_subset_1 > k4_xboole_0 > #nlpp > k9_setfam_1 > k4_yellow_0 > k3_yellow_1 > k3_tarski > k2_yellow_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k3_yellow_1,type,(
    k3_yellow_1: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k2_yellow_1,type,(
    k2_yellow_1: $i > $i )).

tff(k9_setfam_1,type,(
    k9_setfam_1: $i > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k6_subset_1,type,(
    k6_subset_1: ( $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff(k4_yellow_0,type,(
    k4_yellow_0: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_40,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_33,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_42,axiom,(
    ! [A,B] : k6_subset_1(A,B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

tff(f_37,axiom,(
    ! [A,B] : m1_subset_1(k6_subset_1(A,B),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_subset_1)).

tff(f_48,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(f_50,axiom,(
    ! [A] : k9_setfam_1(A) = k1_zfmisc_1(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_setfam_1)).

tff(f_59,axiom,(
    ! [A] : k3_yellow_1(A) = k2_yellow_1(k9_setfam_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_yellow_1)).

tff(f_35,axiom,(
    ! [A] : k3_tarski(k1_zfmisc_1(A)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t99_zfmisc_1)).

tff(f_57,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ( r2_hidden(k3_tarski(A),A)
       => k4_yellow_0(k2_yellow_1(A)) = k3_tarski(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_yellow_1)).

tff(f_62,negated_conjecture,(
    ~ ! [A] : k4_yellow_0(k3_yellow_1(A)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_yellow_1)).

tff(c_12,plain,(
    ! [A_9] : ~ v1_xboole_0(k1_zfmisc_1(A_9)) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_6,plain,(
    ! [A_5] : k4_xboole_0(A_5,k1_xboole_0) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_14,plain,(
    ! [A_10,B_11] : k6_subset_1(A_10,B_11) = k4_xboole_0(A_10,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_10,plain,(
    ! [A_7,B_8] : m1_subset_1(k6_subset_1(A_7,B_8),k1_zfmisc_1(A_7)) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_84,plain,(
    ! [A_29,B_30] : m1_subset_1(k4_xboole_0(A_29,B_30),k1_zfmisc_1(A_29)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_10])).

tff(c_87,plain,(
    ! [A_5] : m1_subset_1(A_5,k1_zfmisc_1(A_5)) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_84])).

tff(c_16,plain,(
    ! [A_12,B_13] :
      ( r2_hidden(A_12,B_13)
      | v1_xboole_0(B_13)
      | ~ m1_subset_1(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_18,plain,(
    ! [A_14] : k9_setfam_1(A_14) = k1_zfmisc_1(A_14) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_22,plain,(
    ! [A_16] : k2_yellow_1(k9_setfam_1(A_16)) = k3_yellow_1(A_16) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_25,plain,(
    ! [A_16] : k2_yellow_1(k1_zfmisc_1(A_16)) = k3_yellow_1(A_16) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_22])).

tff(c_8,plain,(
    ! [A_6] : k3_tarski(k1_zfmisc_1(A_6)) = A_6 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_89,plain,(
    ! [A_32] :
      ( k4_yellow_0(k2_yellow_1(A_32)) = k3_tarski(A_32)
      | ~ r2_hidden(k3_tarski(A_32),A_32)
      | v1_xboole_0(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_96,plain,(
    ! [A_6] :
      ( k4_yellow_0(k2_yellow_1(k1_zfmisc_1(A_6))) = k3_tarski(k1_zfmisc_1(A_6))
      | ~ r2_hidden(A_6,k1_zfmisc_1(A_6))
      | v1_xboole_0(k1_zfmisc_1(A_6)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_89])).

tff(c_98,plain,(
    ! [A_6] :
      ( k4_yellow_0(k3_yellow_1(A_6)) = A_6
      | ~ r2_hidden(A_6,k1_zfmisc_1(A_6))
      | v1_xboole_0(k1_zfmisc_1(A_6)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_25,c_8,c_96])).

tff(c_100,plain,(
    ! [A_33] :
      ( k4_yellow_0(k3_yellow_1(A_33)) = A_33
      | ~ r2_hidden(A_33,k1_zfmisc_1(A_33)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_12,c_98])).

tff(c_104,plain,(
    ! [A_12] :
      ( k4_yellow_0(k3_yellow_1(A_12)) = A_12
      | v1_xboole_0(k1_zfmisc_1(A_12))
      | ~ m1_subset_1(A_12,k1_zfmisc_1(A_12)) ) ),
    inference(resolution,[status(thm)],[c_16,c_100])).

tff(c_107,plain,(
    ! [A_12] :
      ( k4_yellow_0(k3_yellow_1(A_12)) = A_12
      | v1_xboole_0(k1_zfmisc_1(A_12)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_87,c_104])).

tff(c_108,plain,(
    ! [A_12] : k4_yellow_0(k3_yellow_1(A_12)) = A_12 ),
    inference(negUnitSimplification,[status(thm)],[c_12,c_107])).

tff(c_24,plain,(
    k4_yellow_0(k3_yellow_1('#skF_2')) != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_112,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_108,c_24])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.05/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.05/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n020.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 13:02:52 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.65/1.12  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.65/1.13  
% 1.65/1.13  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.65/1.13  %$ r2_hidden > m1_subset_1 > v1_xboole_0 > k6_subset_1 > k4_xboole_0 > #nlpp > k9_setfam_1 > k4_yellow_0 > k3_yellow_1 > k3_tarski > k2_yellow_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_2
% 1.65/1.13  
% 1.65/1.13  %Foreground sorts:
% 1.65/1.13  
% 1.65/1.13  
% 1.65/1.13  %Background operators:
% 1.65/1.13  
% 1.65/1.13  
% 1.65/1.13  %Foreground operators:
% 1.65/1.13  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.65/1.13  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.65/1.13  tff(k3_yellow_1, type, k3_yellow_1: $i > $i).
% 1.65/1.13  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.65/1.13  tff('#skF_1', type, '#skF_1': $i > $i).
% 1.65/1.13  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.65/1.13  tff(k2_yellow_1, type, k2_yellow_1: $i > $i).
% 1.65/1.13  tff(k9_setfam_1, type, k9_setfam_1: $i > $i).
% 1.65/1.13  tff('#skF_2', type, '#skF_2': $i).
% 1.65/1.13  tff(k6_subset_1, type, k6_subset_1: ($i * $i) > $i).
% 1.65/1.13  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.65/1.13  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.65/1.13  tff(k3_tarski, type, k3_tarski: $i > $i).
% 1.65/1.13  tff(k4_yellow_0, type, k4_yellow_0: $i > $i).
% 1.65/1.13  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.65/1.13  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.65/1.13  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.65/1.13  
% 1.77/1.14  tff(f_40, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_subset_1)).
% 1.77/1.14  tff(f_33, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 1.77/1.14  tff(f_42, axiom, (![A, B]: (k6_subset_1(A, B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 1.77/1.14  tff(f_37, axiom, (![A, B]: m1_subset_1(k6_subset_1(A, B), k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_subset_1)).
% 1.77/1.14  tff(f_48, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 1.77/1.14  tff(f_50, axiom, (![A]: (k9_setfam_1(A) = k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k9_setfam_1)).
% 1.77/1.14  tff(f_59, axiom, (![A]: (k3_yellow_1(A) = k2_yellow_1(k9_setfam_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_yellow_1)).
% 1.77/1.14  tff(f_35, axiom, (![A]: (k3_tarski(k1_zfmisc_1(A)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t99_zfmisc_1)).
% 1.77/1.14  tff(f_57, axiom, (![A]: (~v1_xboole_0(A) => (r2_hidden(k3_tarski(A), A) => (k4_yellow_0(k2_yellow_1(A)) = k3_tarski(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t14_yellow_1)).
% 1.77/1.14  tff(f_62, negated_conjecture, ~(![A]: (k4_yellow_0(k3_yellow_1(A)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t19_yellow_1)).
% 1.77/1.14  tff(c_12, plain, (![A_9]: (~v1_xboole_0(k1_zfmisc_1(A_9)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 1.77/1.14  tff(c_6, plain, (![A_5]: (k4_xboole_0(A_5, k1_xboole_0)=A_5)), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.77/1.14  tff(c_14, plain, (![A_10, B_11]: (k6_subset_1(A_10, B_11)=k4_xboole_0(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.77/1.14  tff(c_10, plain, (![A_7, B_8]: (m1_subset_1(k6_subset_1(A_7, B_8), k1_zfmisc_1(A_7)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.77/1.14  tff(c_84, plain, (![A_29, B_30]: (m1_subset_1(k4_xboole_0(A_29, B_30), k1_zfmisc_1(A_29)))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_10])).
% 1.77/1.14  tff(c_87, plain, (![A_5]: (m1_subset_1(A_5, k1_zfmisc_1(A_5)))), inference(superposition, [status(thm), theory('equality')], [c_6, c_84])).
% 1.77/1.14  tff(c_16, plain, (![A_12, B_13]: (r2_hidden(A_12, B_13) | v1_xboole_0(B_13) | ~m1_subset_1(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_48])).
% 1.77/1.14  tff(c_18, plain, (![A_14]: (k9_setfam_1(A_14)=k1_zfmisc_1(A_14))), inference(cnfTransformation, [status(thm)], [f_50])).
% 1.77/1.14  tff(c_22, plain, (![A_16]: (k2_yellow_1(k9_setfam_1(A_16))=k3_yellow_1(A_16))), inference(cnfTransformation, [status(thm)], [f_59])).
% 1.77/1.14  tff(c_25, plain, (![A_16]: (k2_yellow_1(k1_zfmisc_1(A_16))=k3_yellow_1(A_16))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_22])).
% 1.77/1.14  tff(c_8, plain, (![A_6]: (k3_tarski(k1_zfmisc_1(A_6))=A_6)), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.77/1.14  tff(c_89, plain, (![A_32]: (k4_yellow_0(k2_yellow_1(A_32))=k3_tarski(A_32) | ~r2_hidden(k3_tarski(A_32), A_32) | v1_xboole_0(A_32))), inference(cnfTransformation, [status(thm)], [f_57])).
% 1.77/1.14  tff(c_96, plain, (![A_6]: (k4_yellow_0(k2_yellow_1(k1_zfmisc_1(A_6)))=k3_tarski(k1_zfmisc_1(A_6)) | ~r2_hidden(A_6, k1_zfmisc_1(A_6)) | v1_xboole_0(k1_zfmisc_1(A_6)))), inference(superposition, [status(thm), theory('equality')], [c_8, c_89])).
% 1.77/1.14  tff(c_98, plain, (![A_6]: (k4_yellow_0(k3_yellow_1(A_6))=A_6 | ~r2_hidden(A_6, k1_zfmisc_1(A_6)) | v1_xboole_0(k1_zfmisc_1(A_6)))), inference(demodulation, [status(thm), theory('equality')], [c_25, c_8, c_96])).
% 1.77/1.14  tff(c_100, plain, (![A_33]: (k4_yellow_0(k3_yellow_1(A_33))=A_33 | ~r2_hidden(A_33, k1_zfmisc_1(A_33)))), inference(negUnitSimplification, [status(thm)], [c_12, c_98])).
% 1.77/1.14  tff(c_104, plain, (![A_12]: (k4_yellow_0(k3_yellow_1(A_12))=A_12 | v1_xboole_0(k1_zfmisc_1(A_12)) | ~m1_subset_1(A_12, k1_zfmisc_1(A_12)))), inference(resolution, [status(thm)], [c_16, c_100])).
% 1.77/1.14  tff(c_107, plain, (![A_12]: (k4_yellow_0(k3_yellow_1(A_12))=A_12 | v1_xboole_0(k1_zfmisc_1(A_12)))), inference(demodulation, [status(thm), theory('equality')], [c_87, c_104])).
% 1.77/1.14  tff(c_108, plain, (![A_12]: (k4_yellow_0(k3_yellow_1(A_12))=A_12)), inference(negUnitSimplification, [status(thm)], [c_12, c_107])).
% 1.77/1.14  tff(c_24, plain, (k4_yellow_0(k3_yellow_1('#skF_2'))!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_62])).
% 1.77/1.14  tff(c_112, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_108, c_24])).
% 1.77/1.14  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.77/1.14  
% 1.77/1.14  Inference rules
% 1.77/1.14  ----------------------
% 1.77/1.14  #Ref     : 0
% 1.77/1.14  #Sup     : 16
% 1.77/1.14  #Fact    : 0
% 1.77/1.14  #Define  : 0
% 1.77/1.14  #Split   : 0
% 1.77/1.14  #Chain   : 0
% 1.77/1.14  #Close   : 0
% 1.77/1.14  
% 1.77/1.14  Ordering : KBO
% 1.77/1.14  
% 1.77/1.14  Simplification rules
% 1.77/1.14  ----------------------
% 1.77/1.14  #Subsume      : 0
% 1.77/1.14  #Demod        : 7
% 1.77/1.14  #Tautology    : 13
% 1.77/1.14  #SimpNegUnit  : 2
% 1.77/1.14  #BackRed      : 1
% 1.77/1.14  
% 1.77/1.14  #Partial instantiations: 0
% 1.77/1.14  #Strategies tried      : 1
% 1.77/1.14  
% 1.77/1.14  Timing (in seconds)
% 1.77/1.14  ----------------------
% 1.77/1.15  Preprocessing        : 0.28
% 1.77/1.15  Parsing              : 0.15
% 1.77/1.15  CNF conversion       : 0.02
% 1.77/1.15  Main loop            : 0.10
% 1.77/1.15  Inferencing          : 0.04
% 1.77/1.15  Reduction            : 0.03
% 1.77/1.15  Demodulation         : 0.02
% 1.77/1.15  BG Simplification    : 0.01
% 1.77/1.15  Subsumption          : 0.01
% 1.77/1.15  Abstraction          : 0.01
% 1.77/1.15  MUC search           : 0.00
% 1.77/1.15  Cooper               : 0.00
% 1.77/1.15  Total                : 0.40
% 1.77/1.15  Index Insertion      : 0.00
% 1.77/1.15  Index Deletion       : 0.00
% 1.77/1.15  Index Matching       : 0.00
% 1.77/1.15  BG Taut test         : 0.00
%------------------------------------------------------------------------------
