%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:25:30 EST 2020

% Result     : Theorem 1.72s
% Output     : CNFRefutation 1.72s
% Verified   : 
% Statistics : Number of formulae       :   39 (  42 expanded)
%              Number of leaves         :   23 (  25 expanded)
%              Depth                    :    8
%              Number of atoms          :   40 (  45 expanded)
%              Number of equality atoms :   15 (  16 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_xboole_0 > #nlpp > k9_setfam_1 > k3_yellow_1 > k3_yellow_0 > k2_yellow_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k3_yellow_1,type,(
    k3_yellow_1: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k2_yellow_1,type,(
    k2_yellow_1: $i > $i )).

tff(k3_yellow_0,type,(
    k3_yellow_0: $i > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k9_setfam_1,type,(
    k9_setfam_1: $i > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(f_33,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_40,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_42,axiom,(
    ! [A] : k9_setfam_1(A) = k1_zfmisc_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_setfam_1)).

tff(f_51,axiom,(
    ! [A] : k3_yellow_1(A) = k2_yellow_1(k9_setfam_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_yellow_1)).

tff(f_49,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ( r2_hidden(k1_xboole_0,A)
       => k3_yellow_0(k2_yellow_1(A)) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_yellow_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_54,negated_conjecture,(
    ~ ! [A] : k3_yellow_0(k3_yellow_1(A)) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_yellow_1)).

tff(c_6,plain,(
    ! [A_5] : r1_tarski(k1_xboole_0,A_5) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_10,plain,(
    ! [C_10,A_6] :
      ( r2_hidden(C_10,k1_zfmisc_1(A_6))
      | ~ r1_tarski(C_10,A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_20,plain,(
    ! [A_11] : k9_setfam_1(A_11) = k1_zfmisc_1(A_11) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_24,plain,(
    ! [A_13] : k2_yellow_1(k9_setfam_1(A_13)) = k3_yellow_1(A_13) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_27,plain,(
    ! [A_13] : k2_yellow_1(k1_zfmisc_1(A_13)) = k3_yellow_1(A_13) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_24])).

tff(c_69,plain,(
    ! [A_26] :
      ( k3_yellow_0(k2_yellow_1(A_26)) = k1_xboole_0
      | ~ r2_hidden(k1_xboole_0,A_26)
      | v1_xboole_0(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_82,plain,(
    ! [A_28] :
      ( k3_yellow_0(k3_yellow_1(A_28)) = k1_xboole_0
      | ~ r2_hidden(k1_xboole_0,k1_zfmisc_1(A_28))
      | v1_xboole_0(k1_zfmisc_1(A_28)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_27,c_69])).

tff(c_86,plain,(
    ! [A_6] :
      ( k3_yellow_0(k3_yellow_1(A_6)) = k1_xboole_0
      | v1_xboole_0(k1_zfmisc_1(A_6))
      | ~ r1_tarski(k1_xboole_0,A_6) ) ),
    inference(resolution,[status(thm)],[c_10,c_82])).

tff(c_90,plain,(
    ! [A_29] :
      ( k3_yellow_0(k3_yellow_1(A_29)) = k1_xboole_0
      | v1_xboole_0(k1_zfmisc_1(A_29)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_86])).

tff(c_59,plain,(
    ! [C_22,A_23] :
      ( r2_hidden(C_22,k1_zfmisc_1(A_23))
      | ~ r1_tarski(C_22,A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_67,plain,(
    ! [A_23,C_22] :
      ( ~ v1_xboole_0(k1_zfmisc_1(A_23))
      | ~ r1_tarski(C_22,A_23) ) ),
    inference(resolution,[status(thm)],[c_59,c_2])).

tff(c_94,plain,(
    ! [C_30,A_31] :
      ( ~ r1_tarski(C_30,A_31)
      | k3_yellow_0(k3_yellow_1(A_31)) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_90,c_67])).

tff(c_100,plain,(
    ! [A_5] : k3_yellow_0(k3_yellow_1(A_5)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_6,c_94])).

tff(c_26,plain,(
    k3_yellow_0(k3_yellow_1('#skF_4')) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_105,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_26])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n017.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 20:10:16 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.72/1.12  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.72/1.13  
% 1.72/1.13  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.72/1.13  %$ r2_hidden > r1_tarski > v1_xboole_0 > #nlpp > k9_setfam_1 > k3_yellow_1 > k3_yellow_0 > k2_yellow_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2
% 1.72/1.13  
% 1.72/1.13  %Foreground sorts:
% 1.72/1.13  
% 1.72/1.13  
% 1.72/1.13  %Background operators:
% 1.72/1.13  
% 1.72/1.13  
% 1.72/1.13  %Foreground operators:
% 1.72/1.13  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.72/1.13  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.72/1.13  tff(k3_yellow_1, type, k3_yellow_1: $i > $i).
% 1.72/1.13  tff('#skF_1', type, '#skF_1': $i > $i).
% 1.72/1.13  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.72/1.13  tff(k2_yellow_1, type, k2_yellow_1: $i > $i).
% 1.72/1.13  tff(k3_yellow_0, type, k3_yellow_0: $i > $i).
% 1.72/1.13  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 1.72/1.13  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.72/1.13  tff(k9_setfam_1, type, k9_setfam_1: $i > $i).
% 1.72/1.13  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.72/1.13  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.72/1.13  tff('#skF_4', type, '#skF_4': $i).
% 1.72/1.13  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.72/1.13  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 1.72/1.13  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.72/1.13  
% 1.72/1.14  tff(f_33, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 1.72/1.14  tff(f_40, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 1.72/1.14  tff(f_42, axiom, (![A]: (k9_setfam_1(A) = k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k9_setfam_1)).
% 1.72/1.14  tff(f_51, axiom, (![A]: (k3_yellow_1(A) = k2_yellow_1(k9_setfam_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_yellow_1)).
% 1.72/1.14  tff(f_49, axiom, (![A]: (~v1_xboole_0(A) => (r2_hidden(k1_xboole_0, A) => (k3_yellow_0(k2_yellow_1(A)) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t13_yellow_1)).
% 1.72/1.14  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 1.72/1.14  tff(f_54, negated_conjecture, ~(![A]: (k3_yellow_0(k3_yellow_1(A)) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t18_yellow_1)).
% 1.72/1.14  tff(c_6, plain, (![A_5]: (r1_tarski(k1_xboole_0, A_5))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.72/1.14  tff(c_10, plain, (![C_10, A_6]: (r2_hidden(C_10, k1_zfmisc_1(A_6)) | ~r1_tarski(C_10, A_6))), inference(cnfTransformation, [status(thm)], [f_40])).
% 1.72/1.14  tff(c_20, plain, (![A_11]: (k9_setfam_1(A_11)=k1_zfmisc_1(A_11))), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.72/1.14  tff(c_24, plain, (![A_13]: (k2_yellow_1(k9_setfam_1(A_13))=k3_yellow_1(A_13))), inference(cnfTransformation, [status(thm)], [f_51])).
% 1.72/1.14  tff(c_27, plain, (![A_13]: (k2_yellow_1(k1_zfmisc_1(A_13))=k3_yellow_1(A_13))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_24])).
% 1.72/1.14  tff(c_69, plain, (![A_26]: (k3_yellow_0(k2_yellow_1(A_26))=k1_xboole_0 | ~r2_hidden(k1_xboole_0, A_26) | v1_xboole_0(A_26))), inference(cnfTransformation, [status(thm)], [f_49])).
% 1.72/1.14  tff(c_82, plain, (![A_28]: (k3_yellow_0(k3_yellow_1(A_28))=k1_xboole_0 | ~r2_hidden(k1_xboole_0, k1_zfmisc_1(A_28)) | v1_xboole_0(k1_zfmisc_1(A_28)))), inference(superposition, [status(thm), theory('equality')], [c_27, c_69])).
% 1.72/1.14  tff(c_86, plain, (![A_6]: (k3_yellow_0(k3_yellow_1(A_6))=k1_xboole_0 | v1_xboole_0(k1_zfmisc_1(A_6)) | ~r1_tarski(k1_xboole_0, A_6))), inference(resolution, [status(thm)], [c_10, c_82])).
% 1.72/1.14  tff(c_90, plain, (![A_29]: (k3_yellow_0(k3_yellow_1(A_29))=k1_xboole_0 | v1_xboole_0(k1_zfmisc_1(A_29)))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_86])).
% 1.72/1.14  tff(c_59, plain, (![C_22, A_23]: (r2_hidden(C_22, k1_zfmisc_1(A_23)) | ~r1_tarski(C_22, A_23))), inference(cnfTransformation, [status(thm)], [f_40])).
% 1.72/1.14  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.72/1.14  tff(c_67, plain, (![A_23, C_22]: (~v1_xboole_0(k1_zfmisc_1(A_23)) | ~r1_tarski(C_22, A_23))), inference(resolution, [status(thm)], [c_59, c_2])).
% 1.72/1.14  tff(c_94, plain, (![C_30, A_31]: (~r1_tarski(C_30, A_31) | k3_yellow_0(k3_yellow_1(A_31))=k1_xboole_0)), inference(resolution, [status(thm)], [c_90, c_67])).
% 1.72/1.14  tff(c_100, plain, (![A_5]: (k3_yellow_0(k3_yellow_1(A_5))=k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_94])).
% 1.72/1.14  tff(c_26, plain, (k3_yellow_0(k3_yellow_1('#skF_4'))!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_54])).
% 1.72/1.14  tff(c_105, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_100, c_26])).
% 1.72/1.14  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.72/1.14  
% 1.72/1.14  Inference rules
% 1.72/1.14  ----------------------
% 1.72/1.14  #Ref     : 0
% 1.72/1.14  #Sup     : 15
% 1.72/1.14  #Fact    : 0
% 1.72/1.14  #Define  : 0
% 1.72/1.14  #Split   : 0
% 1.72/1.14  #Chain   : 0
% 1.72/1.14  #Close   : 0
% 1.72/1.14  
% 1.72/1.14  Ordering : KBO
% 1.72/1.14  
% 1.72/1.14  Simplification rules
% 1.72/1.14  ----------------------
% 1.72/1.14  #Subsume      : 2
% 1.72/1.14  #Demod        : 5
% 1.72/1.14  #Tautology    : 10
% 1.72/1.14  #SimpNegUnit  : 0
% 1.72/1.14  #BackRed      : 1
% 1.72/1.14  
% 1.72/1.14  #Partial instantiations: 0
% 1.72/1.14  #Strategies tried      : 1
% 1.72/1.14  
% 1.72/1.14  Timing (in seconds)
% 1.72/1.14  ----------------------
% 1.72/1.14  Preprocessing        : 0.28
% 1.72/1.14  Parsing              : 0.15
% 1.72/1.14  CNF conversion       : 0.02
% 1.72/1.14  Main loop            : 0.10
% 1.72/1.14  Inferencing          : 0.04
% 1.72/1.14  Reduction            : 0.03
% 1.72/1.14  Demodulation         : 0.02
% 1.72/1.14  BG Simplification    : 0.01
% 1.72/1.14  Subsumption          : 0.02
% 1.72/1.14  Abstraction          : 0.01
% 1.72/1.14  MUC search           : 0.00
% 1.72/1.14  Cooper               : 0.00
% 1.72/1.14  Total                : 0.41
% 1.72/1.14  Index Insertion      : 0.00
% 1.72/1.14  Index Deletion       : 0.00
% 1.72/1.14  Index Matching       : 0.00
% 1.72/1.15  BG Taut test         : 0.00
%------------------------------------------------------------------------------
