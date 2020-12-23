%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:57:11 EST 2020

% Result     : Theorem 2.25s
% Output     : CNFRefutation 2.25s
% Verified   : 
% Statistics : Number of formulae       :   38 (  40 expanded)
%              Number of leaves         :   21 (  23 expanded)
%              Depth                    :    9
%              Number of atoms          :   44 (  49 expanded)
%              Number of equality atoms :   12 (  16 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_xboole_0 > k4_tarski > k2_zfmisc_1 > #nlpp > k1_setfam_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_4 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_66,negated_conjecture,(
    ~ ! [A] :
        ( r2_hidden(k1_xboole_0,A)
       => k1_setfam_1(A) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_setfam_1)).

tff(f_61,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => r1_tarski(k1_setfam_1(B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_setfam_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_54,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_48,axiom,(
    ! [A,B,C,D] :
      ~ ( r1_tarski(A,k2_zfmisc_1(B,C))
        & r2_hidden(D,A)
        & ! [E,F] :
            ~ ( r2_hidden(E,B)
              & r2_hidden(F,C)
              & D = k4_tarski(E,F) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t103_zfmisc_1)).

tff(f_57,axiom,(
    ! [A,B] : ~ r2_hidden(A,k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_zfmisc_1)).

tff(f_35,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(c_24,plain,(
    k1_setfam_1('#skF_4') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_26,plain,(
    r2_hidden(k1_xboole_0,'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_22,plain,(
    ! [B_17,A_16] :
      ( r1_tarski(k1_setfam_1(B_17),A_16)
      | ~ r2_hidden(A_16,B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_18,plain,(
    ! [B_13] : k2_zfmisc_1(k1_xboole_0,B_13) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_90,plain,(
    ! [A_31,B_32,C_33,D_34] :
      ( r2_hidden('#skF_2'(A_31,B_32,C_33,D_34),B_32)
      | ~ r2_hidden(D_34,A_31)
      | ~ r1_tarski(A_31,k2_zfmisc_1(B_32,C_33)) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_16,plain,(
    ! [A_12] : k2_zfmisc_1(A_12,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_50,plain,(
    ! [A_21,B_22] : ~ r2_hidden(A_21,k2_zfmisc_1(A_21,B_22)) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_53,plain,(
    ! [A_12] : ~ r2_hidden(A_12,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_50])).

tff(c_97,plain,(
    ! [D_34,A_31,C_33] :
      ( ~ r2_hidden(D_34,A_31)
      | ~ r1_tarski(A_31,k2_zfmisc_1(k1_xboole_0,C_33)) ) ),
    inference(resolution,[status(thm)],[c_90,c_53])).

tff(c_112,plain,(
    ! [D_39,A_40] :
      ( ~ r2_hidden(D_39,A_40)
      | ~ r1_tarski(A_40,k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_97])).

tff(c_129,plain,(
    ! [A_41] :
      ( ~ r1_tarski(A_41,k1_xboole_0)
      | v1_xboole_0(A_41) ) ),
    inference(resolution,[status(thm)],[c_4,c_112])).

tff(c_144,plain,(
    ! [B_46] :
      ( v1_xboole_0(k1_setfam_1(B_46))
      | ~ r2_hidden(k1_xboole_0,B_46) ) ),
    inference(resolution,[status(thm)],[c_22,c_129])).

tff(c_6,plain,(
    ! [A_5] :
      ( k1_xboole_0 = A_5
      | ~ v1_xboole_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_149,plain,(
    ! [B_47] :
      ( k1_setfam_1(B_47) = k1_xboole_0
      | ~ r2_hidden(k1_xboole_0,B_47) ) ),
    inference(resolution,[status(thm)],[c_144,c_6])).

tff(c_152,plain,(
    k1_setfam_1('#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_26,c_149])).

tff(c_156,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_152])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.35  % Computer   : n024.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 19:31:06 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.25/1.58  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.25/1.59  
% 2.25/1.59  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.25/1.59  %$ r2_hidden > r1_tarski > v1_xboole_0 > k4_tarski > k2_zfmisc_1 > #nlpp > k1_setfam_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_4 > #skF_3
% 2.25/1.59  
% 2.25/1.59  %Foreground sorts:
% 2.25/1.59  
% 2.25/1.59  
% 2.25/1.59  %Background operators:
% 2.25/1.59  
% 2.25/1.59  
% 2.25/1.59  %Foreground operators:
% 2.25/1.59  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.25/1.59  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.25/1.59  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.25/1.59  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.25/1.59  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.25/1.59  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.25/1.59  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 2.25/1.59  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.25/1.59  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.25/1.59  tff('#skF_4', type, '#skF_4': $i).
% 2.25/1.59  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.25/1.59  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 2.25/1.59  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.25/1.59  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.25/1.59  
% 2.25/1.61  tff(f_66, negated_conjecture, ~(![A]: (r2_hidden(k1_xboole_0, A) => (k1_setfam_1(A) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_setfam_1)).
% 2.25/1.61  tff(f_61, axiom, (![A, B]: (r2_hidden(A, B) => r1_tarski(k1_setfam_1(B), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_setfam_1)).
% 2.25/1.61  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 2.25/1.61  tff(f_54, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 2.25/1.61  tff(f_48, axiom, (![A, B, C, D]: ~((r1_tarski(A, k2_zfmisc_1(B, C)) & r2_hidden(D, A)) & (![E, F]: ~((r2_hidden(E, B) & r2_hidden(F, C)) & (D = k4_tarski(E, F)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t103_zfmisc_1)).
% 2.25/1.61  tff(f_57, axiom, (![A, B]: ~r2_hidden(A, k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t152_zfmisc_1)).
% 2.25/1.61  tff(f_35, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 2.25/1.61  tff(c_24, plain, (k1_setfam_1('#skF_4')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.25/1.61  tff(c_26, plain, (r2_hidden(k1_xboole_0, '#skF_4')), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.25/1.61  tff(c_22, plain, (![B_17, A_16]: (r1_tarski(k1_setfam_1(B_17), A_16) | ~r2_hidden(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.25/1.61  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.25/1.61  tff(c_18, plain, (![B_13]: (k2_zfmisc_1(k1_xboole_0, B_13)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.25/1.61  tff(c_90, plain, (![A_31, B_32, C_33, D_34]: (r2_hidden('#skF_2'(A_31, B_32, C_33, D_34), B_32) | ~r2_hidden(D_34, A_31) | ~r1_tarski(A_31, k2_zfmisc_1(B_32, C_33)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.25/1.61  tff(c_16, plain, (![A_12]: (k2_zfmisc_1(A_12, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.25/1.61  tff(c_50, plain, (![A_21, B_22]: (~r2_hidden(A_21, k2_zfmisc_1(A_21, B_22)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.25/1.61  tff(c_53, plain, (![A_12]: (~r2_hidden(A_12, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_16, c_50])).
% 2.25/1.61  tff(c_97, plain, (![D_34, A_31, C_33]: (~r2_hidden(D_34, A_31) | ~r1_tarski(A_31, k2_zfmisc_1(k1_xboole_0, C_33)))), inference(resolution, [status(thm)], [c_90, c_53])).
% 2.25/1.61  tff(c_112, plain, (![D_39, A_40]: (~r2_hidden(D_39, A_40) | ~r1_tarski(A_40, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_97])).
% 2.25/1.61  tff(c_129, plain, (![A_41]: (~r1_tarski(A_41, k1_xboole_0) | v1_xboole_0(A_41))), inference(resolution, [status(thm)], [c_4, c_112])).
% 2.25/1.61  tff(c_144, plain, (![B_46]: (v1_xboole_0(k1_setfam_1(B_46)) | ~r2_hidden(k1_xboole_0, B_46))), inference(resolution, [status(thm)], [c_22, c_129])).
% 2.25/1.61  tff(c_6, plain, (![A_5]: (k1_xboole_0=A_5 | ~v1_xboole_0(A_5))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.25/1.61  tff(c_149, plain, (![B_47]: (k1_setfam_1(B_47)=k1_xboole_0 | ~r2_hidden(k1_xboole_0, B_47))), inference(resolution, [status(thm)], [c_144, c_6])).
% 2.25/1.61  tff(c_152, plain, (k1_setfam_1('#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_26, c_149])).
% 2.25/1.61  tff(c_156, plain, $false, inference(negUnitSimplification, [status(thm)], [c_24, c_152])).
% 2.25/1.61  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.25/1.61  
% 2.25/1.61  Inference rules
% 2.25/1.61  ----------------------
% 2.25/1.61  #Ref     : 0
% 2.25/1.61  #Sup     : 27
% 2.25/1.61  #Fact    : 0
% 2.25/1.61  #Define  : 0
% 2.25/1.61  #Split   : 0
% 2.25/1.61  #Chain   : 0
% 2.25/1.61  #Close   : 0
% 2.25/1.61  
% 2.25/1.61  Ordering : KBO
% 2.25/1.61  
% 2.25/1.61  Simplification rules
% 2.25/1.61  ----------------------
% 2.25/1.61  #Subsume      : 2
% 2.25/1.61  #Demod        : 2
% 2.25/1.61  #Tautology    : 12
% 2.25/1.61  #SimpNegUnit  : 1
% 2.25/1.61  #BackRed      : 0
% 2.25/1.61  
% 2.25/1.61  #Partial instantiations: 0
% 2.25/1.61  #Strategies tried      : 1
% 2.25/1.61  
% 2.25/1.61  Timing (in seconds)
% 2.25/1.61  ----------------------
% 2.25/1.61  Preprocessing        : 0.44
% 2.25/1.61  Parsing              : 0.23
% 2.25/1.61  CNF conversion       : 0.03
% 2.25/1.61  Main loop            : 0.24
% 2.25/1.61  Inferencing          : 0.10
% 2.25/1.61  Reduction            : 0.06
% 2.25/1.62  Demodulation         : 0.04
% 2.25/1.62  BG Simplification    : 0.02
% 2.25/1.62  Subsumption          : 0.04
% 2.25/1.62  Abstraction          : 0.01
% 2.25/1.62  MUC search           : 0.00
% 2.25/1.62  Cooper               : 0.00
% 2.25/1.62  Total                : 0.72
% 2.25/1.62  Index Insertion      : 0.00
% 2.25/1.62  Index Deletion       : 0.00
% 2.25/1.62  Index Matching       : 0.00
% 2.25/1.62  BG Taut test         : 0.00
%------------------------------------------------------------------------------
