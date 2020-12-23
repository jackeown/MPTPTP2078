%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:25:32 EST 2020

% Result     : Theorem 1.67s
% Output     : CNFRefutation 1.67s
% Verified   : 
% Statistics : Number of formulae       :   39 (  44 expanded)
%              Number of leaves         :   23 (  26 expanded)
%              Depth                    :    6
%              Number of atoms          :   41 (  50 expanded)
%              Number of equality atoms :   17 (  21 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_xboole_0 > #nlpp > k9_setfam_1 > k4_yellow_0 > k3_yellow_1 > k3_tarski > k2_yellow_1 > k1_zfmisc_1 > #skF_3 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k3_yellow_1,type,(
    k3_yellow_1: $i > $i )).

tff(k2_yellow_1,type,(
    k2_yellow_1: $i > $i )).

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

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff(k4_yellow_0,type,(
    k4_yellow_0: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_45,axiom,(
    ! [A] : k3_tarski(k1_zfmisc_1(A)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t99_zfmisc_1)).

tff(f_47,axiom,(
    ! [A] : k9_setfam_1(A) = k1_zfmisc_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_setfam_1)).

tff(f_56,axiom,(
    ! [A] : k3_yellow_1(A) = k2_yellow_1(k9_setfam_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_yellow_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_54,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ( r2_hidden(k3_tarski(A),A)
       => k4_yellow_0(k2_yellow_1(A)) = k3_tarski(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_yellow_1)).

tff(f_36,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_boole)).

tff(f_59,negated_conjecture,(
    ~ ! [A] : k4_yellow_0(k3_yellow_1(A)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_yellow_1)).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_22,plain,(
    ! [A_10] : k3_tarski(k1_zfmisc_1(A_10)) = A_10 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_24,plain,(
    ! [A_11] : k9_setfam_1(A_11) = k1_zfmisc_1(A_11) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_28,plain,(
    ! [A_13] : k2_yellow_1(k9_setfam_1(A_13)) = k3_yellow_1(A_13) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_31,plain,(
    ! [A_13] : k2_yellow_1(k1_zfmisc_1(A_13)) = k3_yellow_1(A_13) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_28])).

tff(c_12,plain,(
    ! [C_9,A_5] :
      ( r2_hidden(C_9,k1_zfmisc_1(A_5))
      | ~ r1_tarski(C_9,A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_80,plain,(
    ! [A_28] :
      ( k4_yellow_0(k2_yellow_1(A_28)) = k3_tarski(A_28)
      | ~ r2_hidden(k3_tarski(A_28),A_28)
      | v1_xboole_0(A_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_84,plain,(
    ! [A_5] :
      ( k4_yellow_0(k2_yellow_1(k1_zfmisc_1(A_5))) = k3_tarski(k1_zfmisc_1(A_5))
      | v1_xboole_0(k1_zfmisc_1(A_5))
      | ~ r1_tarski(k3_tarski(k1_zfmisc_1(A_5)),A_5) ) ),
    inference(resolution,[status(thm)],[c_12,c_80])).

tff(c_92,plain,(
    ! [A_29] :
      ( k4_yellow_0(k3_yellow_1(A_29)) = A_29
      | v1_xboole_0(k1_zfmisc_1(A_29)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_22,c_31,c_22,c_84])).

tff(c_62,plain,(
    ! [C_20,A_21] :
      ( r2_hidden(C_20,k1_zfmisc_1(A_21))
      | ~ r1_tarski(C_20,A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_8,plain,(
    ! [B_4,A_3] :
      ( ~ v1_xboole_0(B_4)
      | ~ r2_hidden(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_66,plain,(
    ! [A_21,C_20] :
      ( ~ v1_xboole_0(k1_zfmisc_1(A_21))
      | ~ r1_tarski(C_20,A_21) ) ),
    inference(resolution,[status(thm)],[c_62,c_8])).

tff(c_96,plain,(
    ! [C_30,A_31] :
      ( ~ r1_tarski(C_30,A_31)
      | k4_yellow_0(k3_yellow_1(A_31)) = A_31 ) ),
    inference(resolution,[status(thm)],[c_92,c_66])).

tff(c_99,plain,(
    ! [B_2] : k4_yellow_0(k3_yellow_1(B_2)) = B_2 ),
    inference(resolution,[status(thm)],[c_6,c_96])).

tff(c_30,plain,(
    k4_yellow_0(k3_yellow_1('#skF_3')) != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_104,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_99,c_30])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n001.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 15:05:45 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.67/1.13  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.67/1.13  
% 1.67/1.13  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.67/1.13  %$ r2_hidden > r1_tarski > v1_xboole_0 > #nlpp > k9_setfam_1 > k4_yellow_0 > k3_yellow_1 > k3_tarski > k2_yellow_1 > k1_zfmisc_1 > #skF_3 > #skF_2 > #skF_1
% 1.67/1.13  
% 1.67/1.13  %Foreground sorts:
% 1.67/1.13  
% 1.67/1.13  
% 1.67/1.13  %Background operators:
% 1.67/1.13  
% 1.67/1.13  
% 1.67/1.13  %Foreground operators:
% 1.67/1.13  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.67/1.13  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.67/1.13  tff(k3_yellow_1, type, k3_yellow_1: $i > $i).
% 1.67/1.13  tff(k2_yellow_1, type, k2_yellow_1: $i > $i).
% 1.67/1.13  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.67/1.13  tff(k9_setfam_1, type, k9_setfam_1: $i > $i).
% 1.67/1.13  tff('#skF_3', type, '#skF_3': $i).
% 1.67/1.13  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.67/1.13  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.67/1.13  tff(k3_tarski, type, k3_tarski: $i > $i).
% 1.67/1.13  tff(k4_yellow_0, type, k4_yellow_0: $i > $i).
% 1.67/1.13  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.67/1.13  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 1.67/1.13  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.67/1.13  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.67/1.13  
% 1.67/1.14  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 1.67/1.14  tff(f_45, axiom, (![A]: (k3_tarski(k1_zfmisc_1(A)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t99_zfmisc_1)).
% 1.67/1.14  tff(f_47, axiom, (![A]: (k9_setfam_1(A) = k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k9_setfam_1)).
% 1.67/1.14  tff(f_56, axiom, (![A]: (k3_yellow_1(A) = k2_yellow_1(k9_setfam_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_yellow_1)).
% 1.67/1.14  tff(f_43, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 1.67/1.14  tff(f_54, axiom, (![A]: (~v1_xboole_0(A) => (r2_hidden(k3_tarski(A), A) => (k4_yellow_0(k2_yellow_1(A)) = k3_tarski(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t14_yellow_1)).
% 1.67/1.14  tff(f_36, axiom, (![A, B]: ~(r2_hidden(A, B) & v1_xboole_0(B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_boole)).
% 1.67/1.14  tff(f_59, negated_conjecture, ~(![A]: (k4_yellow_0(k3_yellow_1(A)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t19_yellow_1)).
% 1.67/1.14  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.67/1.14  tff(c_22, plain, (![A_10]: (k3_tarski(k1_zfmisc_1(A_10))=A_10)), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.67/1.14  tff(c_24, plain, (![A_11]: (k9_setfam_1(A_11)=k1_zfmisc_1(A_11))), inference(cnfTransformation, [status(thm)], [f_47])).
% 1.67/1.14  tff(c_28, plain, (![A_13]: (k2_yellow_1(k9_setfam_1(A_13))=k3_yellow_1(A_13))), inference(cnfTransformation, [status(thm)], [f_56])).
% 1.67/1.14  tff(c_31, plain, (![A_13]: (k2_yellow_1(k1_zfmisc_1(A_13))=k3_yellow_1(A_13))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_28])).
% 1.67/1.14  tff(c_12, plain, (![C_9, A_5]: (r2_hidden(C_9, k1_zfmisc_1(A_5)) | ~r1_tarski(C_9, A_5))), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.67/1.14  tff(c_80, plain, (![A_28]: (k4_yellow_0(k2_yellow_1(A_28))=k3_tarski(A_28) | ~r2_hidden(k3_tarski(A_28), A_28) | v1_xboole_0(A_28))), inference(cnfTransformation, [status(thm)], [f_54])).
% 1.67/1.14  tff(c_84, plain, (![A_5]: (k4_yellow_0(k2_yellow_1(k1_zfmisc_1(A_5)))=k3_tarski(k1_zfmisc_1(A_5)) | v1_xboole_0(k1_zfmisc_1(A_5)) | ~r1_tarski(k3_tarski(k1_zfmisc_1(A_5)), A_5))), inference(resolution, [status(thm)], [c_12, c_80])).
% 1.67/1.14  tff(c_92, plain, (![A_29]: (k4_yellow_0(k3_yellow_1(A_29))=A_29 | v1_xboole_0(k1_zfmisc_1(A_29)))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_22, c_31, c_22, c_84])).
% 1.67/1.14  tff(c_62, plain, (![C_20, A_21]: (r2_hidden(C_20, k1_zfmisc_1(A_21)) | ~r1_tarski(C_20, A_21))), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.67/1.14  tff(c_8, plain, (![B_4, A_3]: (~v1_xboole_0(B_4) | ~r2_hidden(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_36])).
% 1.67/1.14  tff(c_66, plain, (![A_21, C_20]: (~v1_xboole_0(k1_zfmisc_1(A_21)) | ~r1_tarski(C_20, A_21))), inference(resolution, [status(thm)], [c_62, c_8])).
% 1.67/1.14  tff(c_96, plain, (![C_30, A_31]: (~r1_tarski(C_30, A_31) | k4_yellow_0(k3_yellow_1(A_31))=A_31)), inference(resolution, [status(thm)], [c_92, c_66])).
% 1.67/1.14  tff(c_99, plain, (![B_2]: (k4_yellow_0(k3_yellow_1(B_2))=B_2)), inference(resolution, [status(thm)], [c_6, c_96])).
% 1.67/1.14  tff(c_30, plain, (k4_yellow_0(k3_yellow_1('#skF_3'))!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_59])).
% 1.67/1.14  tff(c_104, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_99, c_30])).
% 1.67/1.14  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.67/1.14  
% 1.67/1.14  Inference rules
% 1.67/1.14  ----------------------
% 1.67/1.14  #Ref     : 0
% 1.67/1.14  #Sup     : 13
% 1.67/1.14  #Fact    : 0
% 1.67/1.14  #Define  : 0
% 1.67/1.14  #Split   : 0
% 1.67/1.14  #Chain   : 0
% 1.67/1.14  #Close   : 0
% 1.67/1.14  
% 1.67/1.14  Ordering : KBO
% 1.67/1.14  
% 1.67/1.14  Simplification rules
% 1.67/1.14  ----------------------
% 1.67/1.14  #Subsume      : 0
% 1.67/1.14  #Demod        : 12
% 1.67/1.14  #Tautology    : 11
% 1.67/1.14  #SimpNegUnit  : 0
% 1.67/1.14  #BackRed      : 1
% 1.67/1.14  
% 1.67/1.14  #Partial instantiations: 0
% 1.67/1.14  #Strategies tried      : 1
% 1.67/1.14  
% 1.67/1.14  Timing (in seconds)
% 1.67/1.14  ----------------------
% 1.67/1.15  Preprocessing        : 0.29
% 1.67/1.15  Parsing              : 0.15
% 1.67/1.15  CNF conversion       : 0.02
% 1.67/1.15  Main loop            : 0.10
% 1.67/1.15  Inferencing          : 0.04
% 1.67/1.15  Reduction            : 0.03
% 1.67/1.15  Demodulation         : 0.03
% 1.67/1.15  BG Simplification    : 0.01
% 1.67/1.15  Subsumption          : 0.01
% 1.67/1.15  Abstraction          : 0.01
% 1.67/1.15  MUC search           : 0.00
% 1.67/1.15  Cooper               : 0.00
% 1.67/1.15  Total                : 0.41
% 1.67/1.15  Index Insertion      : 0.00
% 1.67/1.15  Index Deletion       : 0.00
% 1.67/1.15  Index Matching       : 0.00
% 1.67/1.15  BG Taut test         : 0.00
%------------------------------------------------------------------------------
