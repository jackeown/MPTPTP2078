%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:25:31 EST 2020

% Result     : Theorem 1.60s
% Output     : CNFRefutation 1.74s
% Verified   : 
% Statistics : Number of formulae       :   35 (  35 expanded)
%              Number of leaves         :   22 (  22 expanded)
%              Depth                    :    7
%              Number of atoms          :   31 (  31 expanded)
%              Number of equality atoms :   14 (  14 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_xboole_0 > #nlpp > k9_setfam_1 > k3_yellow_1 > k3_yellow_0 > k2_yellow_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_3 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k3_yellow_1,type,(
    k3_yellow_1: $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k2_yellow_1,type,(
    k2_yellow_1: $i > $i )).

tff(k3_yellow_0,type,(
    k3_yellow_0: $i > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k9_setfam_1,type,(
    k9_setfam_1: $i > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(f_27,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_34,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_37,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_39,axiom,(
    ! [A] : k9_setfam_1(A) = k1_zfmisc_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_setfam_1)).

tff(f_48,axiom,(
    ! [A] : k3_yellow_1(A) = k2_yellow_1(k9_setfam_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_yellow_1)).

tff(f_46,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ( r2_hidden(k1_xboole_0,A)
       => k3_yellow_0(k2_yellow_1(A)) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_yellow_1)).

tff(f_51,negated_conjecture,(
    ~ ! [A] : k3_yellow_0(k3_yellow_1(A)) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_yellow_1)).

tff(c_2,plain,(
    ! [A_1] : r1_tarski(k1_xboole_0,A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_6,plain,(
    ! [C_6,A_2] :
      ( r2_hidden(C_6,k1_zfmisc_1(A_2))
      | ~ r1_tarski(C_6,A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_16,plain,(
    ! [A_7] : ~ v1_xboole_0(k1_zfmisc_1(A_7)) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_18,plain,(
    ! [A_8] : k9_setfam_1(A_8) = k1_zfmisc_1(A_8) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_22,plain,(
    ! [A_10] : k2_yellow_1(k9_setfam_1(A_10)) = k3_yellow_1(A_10) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_25,plain,(
    ! [A_10] : k2_yellow_1(k1_zfmisc_1(A_10)) = k3_yellow_1(A_10) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_22])).

tff(c_52,plain,(
    ! [A_19] :
      ( k3_yellow_0(k2_yellow_1(A_19)) = k1_xboole_0
      | ~ r2_hidden(k1_xboole_0,A_19)
      | v1_xboole_0(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_61,plain,(
    ! [A_10] :
      ( k3_yellow_0(k3_yellow_1(A_10)) = k1_xboole_0
      | ~ r2_hidden(k1_xboole_0,k1_zfmisc_1(A_10))
      | v1_xboole_0(k1_zfmisc_1(A_10)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_25,c_52])).

tff(c_65,plain,(
    ! [A_20] :
      ( k3_yellow_0(k3_yellow_1(A_20)) = k1_xboole_0
      | ~ r2_hidden(k1_xboole_0,k1_zfmisc_1(A_20)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_16,c_61])).

tff(c_69,plain,(
    ! [A_2] :
      ( k3_yellow_0(k3_yellow_1(A_2)) = k1_xboole_0
      | ~ r1_tarski(k1_xboole_0,A_2) ) ),
    inference(resolution,[status(thm)],[c_6,c_65])).

tff(c_72,plain,(
    ! [A_2] : k3_yellow_0(k3_yellow_1(A_2)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_69])).

tff(c_24,plain,(
    k3_yellow_0(k3_yellow_1('#skF_3')) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_82,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_24])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:57:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.60/1.14  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.74/1.14  
% 1.74/1.14  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.74/1.15  %$ r2_hidden > r1_tarski > v1_xboole_0 > #nlpp > k9_setfam_1 > k3_yellow_1 > k3_yellow_0 > k2_yellow_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_3 > #skF_2 > #skF_1
% 1.74/1.15  
% 1.74/1.15  %Foreground sorts:
% 1.74/1.15  
% 1.74/1.15  
% 1.74/1.15  %Background operators:
% 1.74/1.15  
% 1.74/1.15  
% 1.74/1.15  %Foreground operators:
% 1.74/1.15  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.74/1.15  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.74/1.15  tff(k3_yellow_1, type, k3_yellow_1: $i > $i).
% 1.74/1.15  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.74/1.15  tff(k2_yellow_1, type, k2_yellow_1: $i > $i).
% 1.74/1.15  tff(k3_yellow_0, type, k3_yellow_0: $i > $i).
% 1.74/1.15  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.74/1.15  tff(k9_setfam_1, type, k9_setfam_1: $i > $i).
% 1.74/1.15  tff('#skF_3', type, '#skF_3': $i).
% 1.74/1.15  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.74/1.15  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.74/1.15  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.74/1.15  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 1.74/1.15  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.74/1.15  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.74/1.15  
% 1.74/1.16  tff(f_27, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 1.74/1.16  tff(f_34, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 1.74/1.16  tff(f_37, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_subset_1)).
% 1.74/1.16  tff(f_39, axiom, (![A]: (k9_setfam_1(A) = k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k9_setfam_1)).
% 1.74/1.16  tff(f_48, axiom, (![A]: (k3_yellow_1(A) = k2_yellow_1(k9_setfam_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_yellow_1)).
% 1.74/1.16  tff(f_46, axiom, (![A]: (~v1_xboole_0(A) => (r2_hidden(k1_xboole_0, A) => (k3_yellow_0(k2_yellow_1(A)) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t13_yellow_1)).
% 1.74/1.16  tff(f_51, negated_conjecture, ~(![A]: (k3_yellow_0(k3_yellow_1(A)) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t18_yellow_1)).
% 1.74/1.16  tff(c_2, plain, (![A_1]: (r1_tarski(k1_xboole_0, A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.74/1.16  tff(c_6, plain, (![C_6, A_2]: (r2_hidden(C_6, k1_zfmisc_1(A_2)) | ~r1_tarski(C_6, A_2))), inference(cnfTransformation, [status(thm)], [f_34])).
% 1.74/1.16  tff(c_16, plain, (![A_7]: (~v1_xboole_0(k1_zfmisc_1(A_7)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.74/1.16  tff(c_18, plain, (![A_8]: (k9_setfam_1(A_8)=k1_zfmisc_1(A_8))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.74/1.16  tff(c_22, plain, (![A_10]: (k2_yellow_1(k9_setfam_1(A_10))=k3_yellow_1(A_10))), inference(cnfTransformation, [status(thm)], [f_48])).
% 1.74/1.16  tff(c_25, plain, (![A_10]: (k2_yellow_1(k1_zfmisc_1(A_10))=k3_yellow_1(A_10))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_22])).
% 1.74/1.16  tff(c_52, plain, (![A_19]: (k3_yellow_0(k2_yellow_1(A_19))=k1_xboole_0 | ~r2_hidden(k1_xboole_0, A_19) | v1_xboole_0(A_19))), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.74/1.16  tff(c_61, plain, (![A_10]: (k3_yellow_0(k3_yellow_1(A_10))=k1_xboole_0 | ~r2_hidden(k1_xboole_0, k1_zfmisc_1(A_10)) | v1_xboole_0(k1_zfmisc_1(A_10)))), inference(superposition, [status(thm), theory('equality')], [c_25, c_52])).
% 1.74/1.16  tff(c_65, plain, (![A_20]: (k3_yellow_0(k3_yellow_1(A_20))=k1_xboole_0 | ~r2_hidden(k1_xboole_0, k1_zfmisc_1(A_20)))), inference(negUnitSimplification, [status(thm)], [c_16, c_61])).
% 1.74/1.16  tff(c_69, plain, (![A_2]: (k3_yellow_0(k3_yellow_1(A_2))=k1_xboole_0 | ~r1_tarski(k1_xboole_0, A_2))), inference(resolution, [status(thm)], [c_6, c_65])).
% 1.74/1.16  tff(c_72, plain, (![A_2]: (k3_yellow_0(k3_yellow_1(A_2))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_2, c_69])).
% 1.74/1.16  tff(c_24, plain, (k3_yellow_0(k3_yellow_1('#skF_3'))!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_51])).
% 1.74/1.16  tff(c_82, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_72, c_24])).
% 1.74/1.16  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.74/1.16  
% 1.74/1.16  Inference rules
% 1.74/1.16  ----------------------
% 1.74/1.16  #Ref     : 0
% 1.74/1.16  #Sup     : 10
% 1.74/1.16  #Fact    : 0
% 1.74/1.16  #Define  : 0
% 1.74/1.16  #Split   : 0
% 1.74/1.16  #Chain   : 0
% 1.74/1.16  #Close   : 0
% 1.74/1.16  
% 1.74/1.16  Ordering : KBO
% 1.74/1.16  
% 1.74/1.16  Simplification rules
% 1.74/1.16  ----------------------
% 1.74/1.16  #Subsume      : 0
% 1.74/1.16  #Demod        : 4
% 1.74/1.16  #Tautology    : 8
% 1.74/1.16  #SimpNegUnit  : 1
% 1.74/1.16  #BackRed      : 1
% 1.74/1.16  
% 1.74/1.16  #Partial instantiations: 0
% 1.74/1.16  #Strategies tried      : 1
% 1.74/1.16  
% 1.74/1.16  Timing (in seconds)
% 1.74/1.16  ----------------------
% 1.74/1.16  Preprocessing        : 0.28
% 1.74/1.16  Parsing              : 0.14
% 1.74/1.16  CNF conversion       : 0.02
% 1.74/1.16  Main loop            : 0.09
% 1.74/1.16  Inferencing          : 0.03
% 1.74/1.16  Reduction            : 0.03
% 1.74/1.16  Demodulation         : 0.02
% 1.74/1.16  BG Simplification    : 0.01
% 1.74/1.16  Subsumption          : 0.01
% 1.74/1.16  Abstraction          : 0.01
% 1.74/1.16  MUC search           : 0.00
% 1.74/1.16  Cooper               : 0.00
% 1.74/1.16  Total                : 0.39
% 1.74/1.16  Index Insertion      : 0.00
% 1.74/1.16  Index Deletion       : 0.00
% 1.74/1.16  Index Matching       : 0.00
% 1.74/1.16  BG Taut test         : 0.00
%------------------------------------------------------------------------------
