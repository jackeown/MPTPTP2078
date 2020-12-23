%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:57:11 EST 2020

% Result     : Theorem 1.86s
% Output     : CNFRefutation 1.86s
% Verified   : 
% Statistics : Number of formulae       :   34 (  35 expanded)
%              Number of leaves         :   19 (  20 expanded)
%              Depth                    :    8
%              Number of atoms          :   42 (  44 expanded)
%              Number of equality atoms :   10 (  11 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > k2_zfmisc_1 > #nlpp > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_73,negated_conjecture,(
    ~ ! [A] :
        ( r2_hidden(k1_xboole_0,A)
       => k1_setfam_1(A) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_setfam_1)).

tff(f_68,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => r1_tarski(k1_setfam_1(B),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_setfam_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & r2_hidden(C,B) ) )
      & ~ ( ? [C] :
              ( r2_hidden(C,A)
              & r2_hidden(C,B) )
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

tff(f_61,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_64,axiom,(
    ! [A,B] : ~ r2_hidden(A,k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_zfmisc_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ~ ( r1_tarski(B,A)
          & r1_xboole_0(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_xboole_1)).

tff(f_29,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(c_22,plain,(
    k1_setfam_1('#skF_2') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_24,plain,(
    r2_hidden(k1_xboole_0,'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_20,plain,(
    ! [B_14,A_13] :
      ( r1_tarski(k1_setfam_1(B_14),A_13)
      | ~ r2_hidden(A_13,B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_71,plain,(
    ! [A_29,B_30] :
      ( r2_hidden('#skF_1'(A_29,B_30),B_30)
      | r1_xboole_0(A_29,B_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_14,plain,(
    ! [A_9] : k2_zfmisc_1(A_9,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_48,plain,(
    ! [A_18,B_19] : ~ r2_hidden(A_18,k2_zfmisc_1(A_18,B_19)) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_51,plain,(
    ! [A_9] : ~ r2_hidden(A_9,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_48])).

tff(c_88,plain,(
    ! [A_33] : r1_xboole_0(A_33,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_71,c_51])).

tff(c_10,plain,(
    ! [B_8,A_7] :
      ( ~ r1_xboole_0(B_8,A_7)
      | ~ r1_tarski(B_8,A_7)
      | v1_xboole_0(B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_93,plain,(
    ! [A_34] :
      ( ~ r1_tarski(A_34,k1_xboole_0)
      | v1_xboole_0(A_34) ) ),
    inference(resolution,[status(thm)],[c_88,c_10])).

tff(c_99,plain,(
    ! [B_35] :
      ( v1_xboole_0(k1_setfam_1(B_35))
      | ~ r2_hidden(k1_xboole_0,B_35) ) ),
    inference(resolution,[status(thm)],[c_20,c_93])).

tff(c_2,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_111,plain,(
    ! [B_39] :
      ( k1_setfam_1(B_39) = k1_xboole_0
      | ~ r2_hidden(k1_xboole_0,B_39) ) ),
    inference(resolution,[status(thm)],[c_99,c_2])).

tff(c_114,plain,(
    k1_setfam_1('#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_24,c_111])).

tff(c_118,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_22,c_114])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n006.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 11:45:07 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.86/1.17  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.86/1.18  
% 1.86/1.18  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.86/1.18  %$ r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > k2_zfmisc_1 > #nlpp > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_1
% 1.86/1.18  
% 1.86/1.18  %Foreground sorts:
% 1.86/1.18  
% 1.86/1.18  
% 1.86/1.18  %Background operators:
% 1.86/1.18  
% 1.86/1.18  
% 1.86/1.18  %Foreground operators:
% 1.86/1.18  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.86/1.18  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.86/1.18  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.86/1.18  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.86/1.18  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.86/1.18  tff('#skF_2', type, '#skF_2': $i).
% 1.86/1.18  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.86/1.18  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.86/1.18  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.86/1.18  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.86/1.18  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.86/1.18  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 1.86/1.18  
% 1.86/1.19  tff(f_73, negated_conjecture, ~(![A]: (r2_hidden(k1_xboole_0, A) => (k1_setfam_1(A) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_setfam_1)).
% 1.86/1.19  tff(f_68, axiom, (![A, B]: (r2_hidden(A, B) => r1_tarski(k1_setfam_1(B), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_setfam_1)).
% 1.86/1.19  tff(f_47, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 1.86/1.19  tff(f_61, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 1.86/1.19  tff(f_64, axiom, (![A, B]: ~r2_hidden(A, k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t152_zfmisc_1)).
% 1.86/1.19  tff(f_55, axiom, (![A, B]: (~v1_xboole_0(B) => ~(r1_tarski(B, A) & r1_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_xboole_1)).
% 1.86/1.19  tff(f_29, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 1.86/1.19  tff(c_22, plain, (k1_setfam_1('#skF_2')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_73])).
% 1.86/1.19  tff(c_24, plain, (r2_hidden(k1_xboole_0, '#skF_2')), inference(cnfTransformation, [status(thm)], [f_73])).
% 1.86/1.19  tff(c_20, plain, (![B_14, A_13]: (r1_tarski(k1_setfam_1(B_14), A_13) | ~r2_hidden(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_68])).
% 1.86/1.19  tff(c_71, plain, (![A_29, B_30]: (r2_hidden('#skF_1'(A_29, B_30), B_30) | r1_xboole_0(A_29, B_30))), inference(cnfTransformation, [status(thm)], [f_47])).
% 1.86/1.19  tff(c_14, plain, (![A_9]: (k2_zfmisc_1(A_9, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_61])).
% 1.86/1.19  tff(c_48, plain, (![A_18, B_19]: (~r2_hidden(A_18, k2_zfmisc_1(A_18, B_19)))), inference(cnfTransformation, [status(thm)], [f_64])).
% 1.86/1.19  tff(c_51, plain, (![A_9]: (~r2_hidden(A_9, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_14, c_48])).
% 1.86/1.19  tff(c_88, plain, (![A_33]: (r1_xboole_0(A_33, k1_xboole_0))), inference(resolution, [status(thm)], [c_71, c_51])).
% 1.86/1.19  tff(c_10, plain, (![B_8, A_7]: (~r1_xboole_0(B_8, A_7) | ~r1_tarski(B_8, A_7) | v1_xboole_0(B_8))), inference(cnfTransformation, [status(thm)], [f_55])).
% 1.86/1.19  tff(c_93, plain, (![A_34]: (~r1_tarski(A_34, k1_xboole_0) | v1_xboole_0(A_34))), inference(resolution, [status(thm)], [c_88, c_10])).
% 1.86/1.19  tff(c_99, plain, (![B_35]: (v1_xboole_0(k1_setfam_1(B_35)) | ~r2_hidden(k1_xboole_0, B_35))), inference(resolution, [status(thm)], [c_20, c_93])).
% 1.86/1.19  tff(c_2, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.86/1.19  tff(c_111, plain, (![B_39]: (k1_setfam_1(B_39)=k1_xboole_0 | ~r2_hidden(k1_xboole_0, B_39))), inference(resolution, [status(thm)], [c_99, c_2])).
% 1.86/1.19  tff(c_114, plain, (k1_setfam_1('#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_24, c_111])).
% 1.86/1.19  tff(c_118, plain, $false, inference(negUnitSimplification, [status(thm)], [c_22, c_114])).
% 1.86/1.19  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.86/1.19  
% 1.86/1.19  Inference rules
% 1.86/1.19  ----------------------
% 1.86/1.19  #Ref     : 0
% 1.86/1.19  #Sup     : 19
% 1.86/1.19  #Fact    : 0
% 1.86/1.19  #Define  : 0
% 1.86/1.19  #Split   : 1
% 1.86/1.19  #Chain   : 0
% 1.86/1.19  #Close   : 0
% 1.86/1.19  
% 1.86/1.19  Ordering : KBO
% 1.86/1.19  
% 1.86/1.19  Simplification rules
% 1.86/1.19  ----------------------
% 1.86/1.19  #Subsume      : 3
% 1.86/1.19  #Demod        : 0
% 1.86/1.19  #Tautology    : 8
% 1.86/1.19  #SimpNegUnit  : 1
% 1.86/1.19  #BackRed      : 0
% 1.86/1.19  
% 1.86/1.19  #Partial instantiations: 0
% 1.86/1.19  #Strategies tried      : 1
% 1.86/1.19  
% 1.86/1.19  Timing (in seconds)
% 1.86/1.19  ----------------------
% 1.86/1.19  Preprocessing        : 0.29
% 1.86/1.19  Parsing              : 0.16
% 1.86/1.19  CNF conversion       : 0.02
% 1.86/1.19  Main loop            : 0.13
% 1.86/1.19  Inferencing          : 0.06
% 1.86/1.19  Reduction            : 0.03
% 1.86/1.19  Demodulation         : 0.02
% 1.86/1.19  BG Simplification    : 0.01
% 1.86/1.19  Subsumption          : 0.02
% 1.86/1.19  Abstraction          : 0.00
% 1.86/1.19  MUC search           : 0.00
% 1.86/1.19  Cooper               : 0.00
% 1.86/1.19  Total                : 0.45
% 1.86/1.19  Index Insertion      : 0.00
% 1.86/1.19  Index Deletion       : 0.00
% 1.86/1.19  Index Matching       : 0.00
% 1.86/1.19  BG Taut test         : 0.00
%------------------------------------------------------------------------------
