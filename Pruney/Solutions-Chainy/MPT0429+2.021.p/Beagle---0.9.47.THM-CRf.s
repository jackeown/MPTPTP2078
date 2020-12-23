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
% DateTime   : Thu Dec  3 09:58:08 EST 2020

% Result     : Theorem 2.02s
% Output     : CNFRefutation 2.02s
% Verified   : 
% Statistics : Number of formulae       :   45 (  45 expanded)
%              Number of leaves         :   30 (  30 expanded)
%              Depth                    :    6
%              Number of atoms          :   36 (  36 expanded)
%              Number of equality atoms :    4 (   4 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_tarski > k1_setfam_1 > k1_xboole_0 > #skF_3 > #skF_2 > #skF_1

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

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff(f_65,axiom,(
    k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_zfmisc_1)).

tff(f_69,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => r1_tarski(k1_zfmisc_1(A),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_zfmisc_1)).

tff(f_75,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_78,negated_conjecture,(
    ~ ! [A] : m1_subset_1(k1_tarski(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(A))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_setfam_1)).

tff(c_140,plain,(
    ! [A_69,B_70] :
      ( r2_hidden('#skF_1'(A_69,B_70),A_69)
      | r1_tarski(A_69,B_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_14,plain,(
    ! [A_12] : r1_xboole_0(A_12,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_12,plain,(
    ! [A_11] : k3_xboole_0(A_11,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_122,plain,(
    ! [A_61,B_62,C_63] :
      ( ~ r1_xboole_0(A_61,B_62)
      | ~ r2_hidden(C_63,k3_xboole_0(A_61,B_62)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_128,plain,(
    ! [A_11,C_63] :
      ( ~ r1_xboole_0(A_11,k1_xboole_0)
      | ~ r2_hidden(C_63,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_122])).

tff(c_130,plain,(
    ! [C_63] : ~ r2_hidden(C_63,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_128])).

tff(c_154,plain,(
    ! [B_70] : r1_tarski(k1_xboole_0,B_70) ),
    inference(resolution,[status(thm)],[c_140,c_130])).

tff(c_30,plain,(
    k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_132,plain,(
    ! [A_65,B_66] :
      ( r1_tarski(k1_zfmisc_1(A_65),k1_zfmisc_1(B_66))
      | ~ r1_tarski(A_65,B_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_135,plain,(
    ! [B_66] :
      ( r1_tarski(k1_tarski(k1_xboole_0),k1_zfmisc_1(B_66))
      | ~ r1_tarski(k1_xboole_0,B_66) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_132])).

tff(c_168,plain,(
    ! [B_66] : r1_tarski(k1_tarski(k1_xboole_0),k1_zfmisc_1(B_66)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_154,c_135])).

tff(c_62,plain,(
    ! [A_50,B_51] :
      ( m1_subset_1(A_50,k1_zfmisc_1(B_51))
      | ~ r1_tarski(A_50,B_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_40,plain,(
    ~ m1_subset_1(k1_tarski(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_69,plain,(
    ~ r1_tarski(k1_tarski(k1_xboole_0),k1_zfmisc_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_62,c_40])).

tff(c_171,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_168,c_69])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n014.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 17:36:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.02/1.28  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.02/1.28  
% 2.02/1.28  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.02/1.28  %$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_tarski > k1_setfam_1 > k1_xboole_0 > #skF_3 > #skF_2 > #skF_1
% 2.02/1.28  
% 2.02/1.28  %Foreground sorts:
% 2.02/1.28  
% 2.02/1.28  
% 2.02/1.28  %Background operators:
% 2.02/1.28  
% 2.02/1.28  
% 2.02/1.28  %Foreground operators:
% 2.02/1.28  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.02/1.28  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.02/1.28  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.02/1.28  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.02/1.28  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.02/1.28  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.02/1.28  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.02/1.28  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.02/1.28  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.02/1.28  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.02/1.28  tff('#skF_3', type, '#skF_3': $i).
% 2.02/1.28  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.02/1.28  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.02/1.28  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.02/1.28  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.02/1.28  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.02/1.28  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.02/1.28  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.02/1.28  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.02/1.28  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.02/1.28  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.02/1.28  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.02/1.28  
% 2.02/1.29  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 2.02/1.29  tff(f_50, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 2.02/1.29  tff(f_48, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 2.02/1.29  tff(f_46, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 2.02/1.29  tff(f_65, axiom, (k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_zfmisc_1)).
% 2.02/1.29  tff(f_69, axiom, (![A, B]: (r1_tarski(A, B) => r1_tarski(k1_zfmisc_1(A), k1_zfmisc_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_zfmisc_1)).
% 2.02/1.29  tff(f_75, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 2.02/1.29  tff(f_78, negated_conjecture, ~(![A]: m1_subset_1(k1_tarski(k1_xboole_0), k1_zfmisc_1(k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t61_setfam_1)).
% 2.02/1.29  tff(c_140, plain, (![A_69, B_70]: (r2_hidden('#skF_1'(A_69, B_70), A_69) | r1_tarski(A_69, B_70))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.02/1.29  tff(c_14, plain, (![A_12]: (r1_xboole_0(A_12, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.02/1.29  tff(c_12, plain, (![A_11]: (k3_xboole_0(A_11, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.02/1.29  tff(c_122, plain, (![A_61, B_62, C_63]: (~r1_xboole_0(A_61, B_62) | ~r2_hidden(C_63, k3_xboole_0(A_61, B_62)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.02/1.29  tff(c_128, plain, (![A_11, C_63]: (~r1_xboole_0(A_11, k1_xboole_0) | ~r2_hidden(C_63, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_12, c_122])).
% 2.02/1.29  tff(c_130, plain, (![C_63]: (~r2_hidden(C_63, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_128])).
% 2.02/1.29  tff(c_154, plain, (![B_70]: (r1_tarski(k1_xboole_0, B_70))), inference(resolution, [status(thm)], [c_140, c_130])).
% 2.02/1.29  tff(c_30, plain, (k1_zfmisc_1(k1_xboole_0)=k1_tarski(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.02/1.29  tff(c_132, plain, (![A_65, B_66]: (r1_tarski(k1_zfmisc_1(A_65), k1_zfmisc_1(B_66)) | ~r1_tarski(A_65, B_66))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.02/1.29  tff(c_135, plain, (![B_66]: (r1_tarski(k1_tarski(k1_xboole_0), k1_zfmisc_1(B_66)) | ~r1_tarski(k1_xboole_0, B_66))), inference(superposition, [status(thm), theory('equality')], [c_30, c_132])).
% 2.02/1.29  tff(c_168, plain, (![B_66]: (r1_tarski(k1_tarski(k1_xboole_0), k1_zfmisc_1(B_66)))), inference(demodulation, [status(thm), theory('equality')], [c_154, c_135])).
% 2.02/1.29  tff(c_62, plain, (![A_50, B_51]: (m1_subset_1(A_50, k1_zfmisc_1(B_51)) | ~r1_tarski(A_50, B_51))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.02/1.29  tff(c_40, plain, (~m1_subset_1(k1_tarski(k1_xboole_0), k1_zfmisc_1(k1_zfmisc_1('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.02/1.29  tff(c_69, plain, (~r1_tarski(k1_tarski(k1_xboole_0), k1_zfmisc_1('#skF_3'))), inference(resolution, [status(thm)], [c_62, c_40])).
% 2.02/1.29  tff(c_171, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_168, c_69])).
% 2.02/1.29  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.02/1.29  
% 2.02/1.29  Inference rules
% 2.02/1.29  ----------------------
% 2.02/1.29  #Ref     : 0
% 2.02/1.29  #Sup     : 29
% 2.02/1.29  #Fact    : 0
% 2.02/1.29  #Define  : 0
% 2.02/1.29  #Split   : 0
% 2.02/1.29  #Chain   : 0
% 2.02/1.29  #Close   : 0
% 2.02/1.29  
% 2.02/1.29  Ordering : KBO
% 2.02/1.29  
% 2.02/1.29  Simplification rules
% 2.02/1.29  ----------------------
% 2.02/1.29  #Subsume      : 0
% 2.02/1.29  #Demod        : 3
% 2.02/1.29  #Tautology    : 18
% 2.02/1.29  #SimpNegUnit  : 0
% 2.02/1.29  #BackRed      : 1
% 2.02/1.29  
% 2.02/1.29  #Partial instantiations: 0
% 2.02/1.29  #Strategies tried      : 1
% 2.02/1.29  
% 2.02/1.29  Timing (in seconds)
% 2.02/1.29  ----------------------
% 2.02/1.29  Preprocessing        : 0.35
% 2.02/1.29  Parsing              : 0.19
% 2.02/1.29  CNF conversion       : 0.02
% 2.02/1.29  Main loop            : 0.13
% 2.02/1.29  Inferencing          : 0.05
% 2.02/1.29  Reduction            : 0.04
% 2.02/1.29  Demodulation         : 0.03
% 2.02/1.29  BG Simplification    : 0.01
% 2.02/1.29  Subsumption          : 0.02
% 2.02/1.29  Abstraction          : 0.01
% 2.02/1.30  MUC search           : 0.00
% 2.02/1.30  Cooper               : 0.00
% 2.02/1.30  Total                : 0.50
% 2.02/1.30  Index Insertion      : 0.00
% 2.02/1.30  Index Deletion       : 0.00
% 2.02/1.30  Index Matching       : 0.00
% 2.02/1.30  BG Taut test         : 0.00
%------------------------------------------------------------------------------
