%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:58:07 EST 2020

% Result     : Theorem 1.82s
% Output     : CNFRefutation 1.91s
% Verified   : 
% Statistics : Number of formulae       :   41 (  50 expanded)
%              Number of leaves         :   23 (  28 expanded)
%              Depth                    :    8
%              Number of atoms          :   42 (  57 expanded)
%              Number of equality atoms :    8 (  11 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > k2_enumset1 > k1_enumset1 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_3 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_56,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_59,negated_conjecture,(
    ~ ! [A] : m1_subset_1(k1_tarski(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(A))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_setfam_1)).

tff(f_34,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_52,axiom,(
    k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_zfmisc_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_51,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_38,axiom,(
    ! [A] :
      ( r1_tarski(A,k1_xboole_0)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).

tff(c_58,plain,(
    ! [A_24,B_25] :
      ( m1_subset_1(A_24,k1_zfmisc_1(B_25))
      | ~ r1_tarski(A_24,B_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_36,plain,(
    ~ m1_subset_1(k1_tarski(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1('#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_65,plain,(
    ~ r1_tarski(k1_tarski(k1_xboole_0),k1_zfmisc_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_58,c_36])).

tff(c_8,plain,(
    ! [A_6] : r1_tarski(k1_xboole_0,A_6) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_30,plain,(
    k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_107,plain,(
    ! [A_38,B_39] :
      ( r2_hidden('#skF_1'(A_38,B_39),A_38)
      | r1_tarski(A_38,B_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_18,plain,(
    ! [C_18,A_14] :
      ( r1_tarski(C_18,A_14)
      | ~ r2_hidden(C_18,k1_zfmisc_1(A_14)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_165,plain,(
    ! [A_51,B_52] :
      ( r1_tarski('#skF_1'(k1_zfmisc_1(A_51),B_52),A_51)
      | r1_tarski(k1_zfmisc_1(A_51),B_52) ) ),
    inference(resolution,[status(thm)],[c_107,c_18])).

tff(c_10,plain,(
    ! [A_7] :
      ( k1_xboole_0 = A_7
      | ~ r1_tarski(A_7,k1_xboole_0) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_173,plain,(
    ! [B_52] :
      ( '#skF_1'(k1_zfmisc_1(k1_xboole_0),B_52) = k1_xboole_0
      | r1_tarski(k1_zfmisc_1(k1_xboole_0),B_52) ) ),
    inference(resolution,[status(thm)],[c_165,c_10])).

tff(c_182,plain,(
    ! [B_53] :
      ( '#skF_1'(k1_tarski(k1_xboole_0),B_53) = k1_xboole_0
      | r1_tarski(k1_tarski(k1_xboole_0),B_53) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_30,c_173])).

tff(c_190,plain,(
    '#skF_1'(k1_tarski(k1_xboole_0),k1_zfmisc_1('#skF_4')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_182,c_65])).

tff(c_20,plain,(
    ! [C_18,A_14] :
      ( r2_hidden(C_18,k1_zfmisc_1(A_14))
      | ~ r1_tarski(C_18,A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_118,plain,(
    ! [A_40,B_41] :
      ( ~ r2_hidden('#skF_1'(A_40,B_41),B_41)
      | r1_tarski(A_40,B_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_133,plain,(
    ! [A_40,A_14] :
      ( r1_tarski(A_40,k1_zfmisc_1(A_14))
      | ~ r1_tarski('#skF_1'(A_40,k1_zfmisc_1(A_14)),A_14) ) ),
    inference(resolution,[status(thm)],[c_20,c_118])).

tff(c_195,plain,
    ( r1_tarski(k1_tarski(k1_xboole_0),k1_zfmisc_1('#skF_4'))
    | ~ r1_tarski(k1_xboole_0,'#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_190,c_133])).

tff(c_205,plain,(
    r1_tarski(k1_tarski(k1_xboole_0),k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_195])).

tff(c_207,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_65,c_205])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:02:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.82/1.17  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.91/1.17  
% 1.91/1.17  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.91/1.17  %$ r2_hidden > r1_tarski > m1_subset_1 > k2_enumset1 > k1_enumset1 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 1.91/1.17  
% 1.91/1.17  %Foreground sorts:
% 1.91/1.17  
% 1.91/1.17  
% 1.91/1.17  %Background operators:
% 1.91/1.17  
% 1.91/1.17  
% 1.91/1.17  %Foreground operators:
% 1.91/1.17  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.91/1.17  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.91/1.17  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.91/1.17  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.91/1.17  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 1.91/1.17  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.91/1.17  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.91/1.17  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.91/1.17  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.91/1.17  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.91/1.17  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.91/1.17  tff('#skF_4', type, '#skF_4': $i).
% 1.91/1.17  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.91/1.17  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 1.91/1.17  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.91/1.17  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.91/1.17  
% 1.91/1.18  tff(f_56, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 1.91/1.18  tff(f_59, negated_conjecture, ~(![A]: m1_subset_1(k1_tarski(k1_xboole_0), k1_zfmisc_1(k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t61_setfam_1)).
% 1.91/1.18  tff(f_34, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 1.91/1.18  tff(f_52, axiom, (k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_zfmisc_1)).
% 1.91/1.18  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 1.91/1.18  tff(f_51, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 1.91/1.18  tff(f_38, axiom, (![A]: (r1_tarski(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_1)).
% 1.91/1.18  tff(c_58, plain, (![A_24, B_25]: (m1_subset_1(A_24, k1_zfmisc_1(B_25)) | ~r1_tarski(A_24, B_25))), inference(cnfTransformation, [status(thm)], [f_56])).
% 1.91/1.18  tff(c_36, plain, (~m1_subset_1(k1_tarski(k1_xboole_0), k1_zfmisc_1(k1_zfmisc_1('#skF_4')))), inference(cnfTransformation, [status(thm)], [f_59])).
% 1.91/1.18  tff(c_65, plain, (~r1_tarski(k1_tarski(k1_xboole_0), k1_zfmisc_1('#skF_4'))), inference(resolution, [status(thm)], [c_58, c_36])).
% 1.91/1.18  tff(c_8, plain, (![A_6]: (r1_tarski(k1_xboole_0, A_6))), inference(cnfTransformation, [status(thm)], [f_34])).
% 1.91/1.18  tff(c_30, plain, (k1_zfmisc_1(k1_xboole_0)=k1_tarski(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_52])).
% 1.91/1.18  tff(c_107, plain, (![A_38, B_39]: (r2_hidden('#skF_1'(A_38, B_39), A_38) | r1_tarski(A_38, B_39))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.91/1.18  tff(c_18, plain, (![C_18, A_14]: (r1_tarski(C_18, A_14) | ~r2_hidden(C_18, k1_zfmisc_1(A_14)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 1.91/1.18  tff(c_165, plain, (![A_51, B_52]: (r1_tarski('#skF_1'(k1_zfmisc_1(A_51), B_52), A_51) | r1_tarski(k1_zfmisc_1(A_51), B_52))), inference(resolution, [status(thm)], [c_107, c_18])).
% 1.91/1.18  tff(c_10, plain, (![A_7]: (k1_xboole_0=A_7 | ~r1_tarski(A_7, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_38])).
% 1.91/1.18  tff(c_173, plain, (![B_52]: ('#skF_1'(k1_zfmisc_1(k1_xboole_0), B_52)=k1_xboole_0 | r1_tarski(k1_zfmisc_1(k1_xboole_0), B_52))), inference(resolution, [status(thm)], [c_165, c_10])).
% 1.91/1.18  tff(c_182, plain, (![B_53]: ('#skF_1'(k1_tarski(k1_xboole_0), B_53)=k1_xboole_0 | r1_tarski(k1_tarski(k1_xboole_0), B_53))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_30, c_173])).
% 1.91/1.18  tff(c_190, plain, ('#skF_1'(k1_tarski(k1_xboole_0), k1_zfmisc_1('#skF_4'))=k1_xboole_0), inference(resolution, [status(thm)], [c_182, c_65])).
% 1.91/1.18  tff(c_20, plain, (![C_18, A_14]: (r2_hidden(C_18, k1_zfmisc_1(A_14)) | ~r1_tarski(C_18, A_14))), inference(cnfTransformation, [status(thm)], [f_51])).
% 1.91/1.18  tff(c_118, plain, (![A_40, B_41]: (~r2_hidden('#skF_1'(A_40, B_41), B_41) | r1_tarski(A_40, B_41))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.91/1.18  tff(c_133, plain, (![A_40, A_14]: (r1_tarski(A_40, k1_zfmisc_1(A_14)) | ~r1_tarski('#skF_1'(A_40, k1_zfmisc_1(A_14)), A_14))), inference(resolution, [status(thm)], [c_20, c_118])).
% 1.91/1.18  tff(c_195, plain, (r1_tarski(k1_tarski(k1_xboole_0), k1_zfmisc_1('#skF_4')) | ~r1_tarski(k1_xboole_0, '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_190, c_133])).
% 1.91/1.18  tff(c_205, plain, (r1_tarski(k1_tarski(k1_xboole_0), k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_195])).
% 1.91/1.18  tff(c_207, plain, $false, inference(negUnitSimplification, [status(thm)], [c_65, c_205])).
% 1.91/1.18  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.91/1.18  
% 1.91/1.18  Inference rules
% 1.91/1.18  ----------------------
% 1.91/1.18  #Ref     : 0
% 1.91/1.18  #Sup     : 38
% 1.91/1.18  #Fact    : 0
% 1.91/1.18  #Define  : 0
% 1.91/1.18  #Split   : 0
% 1.91/1.18  #Chain   : 0
% 1.91/1.18  #Close   : 0
% 1.91/1.18  
% 1.91/1.18  Ordering : KBO
% 1.91/1.18  
% 1.91/1.18  Simplification rules
% 1.91/1.18  ----------------------
% 1.91/1.18  #Subsume      : 0
% 1.91/1.18  #Demod        : 6
% 1.91/1.18  #Tautology    : 16
% 1.91/1.18  #SimpNegUnit  : 1
% 1.91/1.18  #BackRed      : 0
% 1.91/1.18  
% 1.91/1.18  #Partial instantiations: 0
% 1.91/1.18  #Strategies tried      : 1
% 1.91/1.18  
% 1.91/1.18  Timing (in seconds)
% 1.91/1.18  ----------------------
% 1.91/1.19  Preprocessing        : 0.29
% 1.91/1.19  Parsing              : 0.14
% 1.91/1.19  CNF conversion       : 0.02
% 1.91/1.19  Main loop            : 0.14
% 1.91/1.19  Inferencing          : 0.05
% 1.91/1.19  Reduction            : 0.04
% 1.91/1.19  Demodulation         : 0.03
% 1.91/1.19  BG Simplification    : 0.01
% 1.91/1.19  Subsumption          : 0.02
% 1.91/1.19  Abstraction          : 0.01
% 1.91/1.19  MUC search           : 0.00
% 1.91/1.19  Cooper               : 0.00
% 1.91/1.19  Total                : 0.45
% 1.91/1.19  Index Insertion      : 0.00
% 1.91/1.19  Index Deletion       : 0.00
% 1.91/1.19  Index Matching       : 0.00
% 1.91/1.19  BG Taut test         : 0.00
%------------------------------------------------------------------------------
