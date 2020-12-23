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
% DateTime   : Thu Dec  3 09:58:07 EST 2020

% Result     : Theorem 1.93s
% Output     : CNFRefutation 2.12s
% Verified   : 
% Statistics : Number of formulae       :   44 (  44 expanded)
%              Number of leaves         :   31 (  31 expanded)
%              Depth                    :    5
%              Number of atoms          :   33 (  33 expanded)
%              Number of equality atoms :    3 (   3 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_tarski > k1_setfam_1 > k1_xboole_0 > #skF_3 > #skF_5 > #skF_2 > #skF_1 > #skF_4

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

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_50,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_48,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

tff(f_46,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_71,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_75,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(k1_tarski(A),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_subset_1)).

tff(f_80,negated_conjecture,(
    ~ ! [A] : m1_subset_1(k1_tarski(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(A))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_setfam_1)).

tff(c_133,plain,(
    ! [A_70,B_71] :
      ( r2_hidden('#skF_1'(A_70,B_71),A_70)
      | r1_tarski(A_70,B_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_14,plain,(
    ! [A_12] : r1_xboole_0(A_12,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_12,plain,(
    ! [A_11] : k3_xboole_0(A_11,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_123,plain,(
    ! [A_66,B_67,C_68] :
      ( ~ r1_xboole_0(A_66,B_67)
      | ~ r2_hidden(C_68,k3_xboole_0(A_66,B_67)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_129,plain,(
    ! [A_11,C_68] :
      ( ~ r1_xboole_0(A_11,k1_xboole_0)
      | ~ r2_hidden(C_68,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_123])).

tff(c_131,plain,(
    ! [C_68] : ~ r2_hidden(C_68,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_129])).

tff(c_150,plain,(
    ! [B_71] : r1_tarski(k1_xboole_0,B_71) ),
    inference(resolution,[status(thm)],[c_133,c_131])).

tff(c_32,plain,(
    ! [C_45,A_41] :
      ( r2_hidden(C_45,k1_zfmisc_1(A_41))
      | ~ r1_tarski(C_45,A_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_108,plain,(
    ! [A_62,B_63] :
      ( m1_subset_1(k1_tarski(A_62),k1_zfmisc_1(B_63))
      | ~ r2_hidden(A_62,B_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_46,plain,(
    ~ m1_subset_1(k1_tarski(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1('#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_112,plain,(
    ~ r2_hidden(k1_xboole_0,k1_zfmisc_1('#skF_5')) ),
    inference(resolution,[status(thm)],[c_108,c_46])).

tff(c_116,plain,(
    ~ r1_tarski(k1_xboole_0,'#skF_5') ),
    inference(resolution,[status(thm)],[c_32,c_112])).

tff(c_157,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_150,c_116])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n001.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 13:04:44 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.93/1.38  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.93/1.38  
% 1.93/1.38  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.93/1.39  %$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_tarski > k1_setfam_1 > k1_xboole_0 > #skF_3 > #skF_5 > #skF_2 > #skF_1 > #skF_4
% 1.93/1.39  
% 1.93/1.39  %Foreground sorts:
% 1.93/1.39  
% 1.93/1.39  
% 1.93/1.39  %Background operators:
% 1.93/1.39  
% 1.93/1.39  
% 1.93/1.39  %Foreground operators:
% 1.93/1.39  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.93/1.39  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.93/1.39  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.93/1.39  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.93/1.39  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 1.93/1.39  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 1.93/1.39  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.93/1.39  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.93/1.39  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.93/1.39  tff('#skF_5', type, '#skF_5': $i).
% 1.93/1.39  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.93/1.39  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.93/1.39  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 1.93/1.39  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.93/1.39  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 1.93/1.39  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.93/1.39  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.93/1.39  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 1.93/1.39  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.93/1.39  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 1.93/1.39  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.93/1.39  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 1.93/1.39  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.93/1.39  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 1.93/1.39  
% 2.12/1.40  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 2.12/1.40  tff(f_50, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 2.12/1.40  tff(f_48, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 2.12/1.40  tff(f_46, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 2.12/1.40  tff(f_71, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 2.12/1.40  tff(f_75, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(k1_tarski(A), k1_zfmisc_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_subset_1)).
% 2.12/1.40  tff(f_80, negated_conjecture, ~(![A]: m1_subset_1(k1_tarski(k1_xboole_0), k1_zfmisc_1(k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t61_setfam_1)).
% 2.12/1.40  tff(c_133, plain, (![A_70, B_71]: (r2_hidden('#skF_1'(A_70, B_71), A_70) | r1_tarski(A_70, B_71))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.12/1.40  tff(c_14, plain, (![A_12]: (r1_xboole_0(A_12, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.12/1.40  tff(c_12, plain, (![A_11]: (k3_xboole_0(A_11, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.12/1.40  tff(c_123, plain, (![A_66, B_67, C_68]: (~r1_xboole_0(A_66, B_67) | ~r2_hidden(C_68, k3_xboole_0(A_66, B_67)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.12/1.40  tff(c_129, plain, (![A_11, C_68]: (~r1_xboole_0(A_11, k1_xboole_0) | ~r2_hidden(C_68, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_12, c_123])).
% 2.12/1.40  tff(c_131, plain, (![C_68]: (~r2_hidden(C_68, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_129])).
% 2.12/1.40  tff(c_150, plain, (![B_71]: (r1_tarski(k1_xboole_0, B_71))), inference(resolution, [status(thm)], [c_133, c_131])).
% 2.12/1.40  tff(c_32, plain, (![C_45, A_41]: (r2_hidden(C_45, k1_zfmisc_1(A_41)) | ~r1_tarski(C_45, A_41))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.12/1.40  tff(c_108, plain, (![A_62, B_63]: (m1_subset_1(k1_tarski(A_62), k1_zfmisc_1(B_63)) | ~r2_hidden(A_62, B_63))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.12/1.40  tff(c_46, plain, (~m1_subset_1(k1_tarski(k1_xboole_0), k1_zfmisc_1(k1_zfmisc_1('#skF_5')))), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.12/1.40  tff(c_112, plain, (~r2_hidden(k1_xboole_0, k1_zfmisc_1('#skF_5'))), inference(resolution, [status(thm)], [c_108, c_46])).
% 2.12/1.40  tff(c_116, plain, (~r1_tarski(k1_xboole_0, '#skF_5')), inference(resolution, [status(thm)], [c_32, c_112])).
% 2.12/1.40  tff(c_157, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_150, c_116])).
% 2.12/1.40  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.12/1.40  
% 2.12/1.40  Inference rules
% 2.12/1.40  ----------------------
% 2.12/1.40  #Ref     : 0
% 2.12/1.40  #Sup     : 23
% 2.12/1.40  #Fact    : 0
% 2.12/1.40  #Define  : 0
% 2.12/1.40  #Split   : 0
% 2.12/1.40  #Chain   : 0
% 2.12/1.40  #Close   : 0
% 2.12/1.40  
% 2.12/1.40  Ordering : KBO
% 2.12/1.40  
% 2.12/1.40  Simplification rules
% 2.12/1.40  ----------------------
% 2.12/1.40  #Subsume      : 0
% 2.12/1.40  #Demod        : 2
% 2.12/1.40  #Tautology    : 13
% 2.12/1.40  #SimpNegUnit  : 0
% 2.12/1.40  #BackRed      : 1
% 2.12/1.40  
% 2.12/1.40  #Partial instantiations: 0
% 2.12/1.40  #Strategies tried      : 1
% 2.12/1.40  
% 2.12/1.40  Timing (in seconds)
% 2.12/1.40  ----------------------
% 2.12/1.40  Preprocessing        : 0.41
% 2.12/1.40  Parsing              : 0.24
% 2.12/1.40  CNF conversion       : 0.02
% 2.12/1.40  Main loop            : 0.12
% 2.12/1.40  Inferencing          : 0.04
% 2.12/1.40  Reduction            : 0.04
% 2.12/1.40  Demodulation         : 0.03
% 2.12/1.40  BG Simplification    : 0.01
% 2.12/1.40  Subsumption          : 0.02
% 2.12/1.40  Abstraction          : 0.01
% 2.12/1.40  MUC search           : 0.00
% 2.12/1.40  Cooper               : 0.00
% 2.12/1.40  Total                : 0.55
% 2.12/1.40  Index Insertion      : 0.00
% 2.12/1.40  Index Deletion       : 0.00
% 2.12/1.40  Index Matching       : 0.00
% 2.12/1.40  BG Taut test         : 0.00
%------------------------------------------------------------------------------
