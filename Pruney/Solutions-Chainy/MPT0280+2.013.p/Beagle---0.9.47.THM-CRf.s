%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:53:25 EST 2020

% Result     : Theorem 2.12s
% Output     : CNFRefutation 2.12s
% Verified   : 
% Statistics : Number of formulae       :   45 (  52 expanded)
%              Number of leaves         :   27 (  30 expanded)
%              Depth                    :    5
%              Number of atoms          :   40 (  54 expanded)
%              Number of equality atoms :    8 (   8 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

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

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i ) > $i )).

tff(f_50,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_48,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

tff(f_66,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_64,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => r1_tarski(A,k3_tarski(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l49_zfmisc_1)).

tff(f_70,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => r1_tarski(k1_zfmisc_1(A),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_zfmisc_1)).

tff(f_27,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_33,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(C,B) )
     => r1_tarski(k2_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_xboole_1)).

tff(f_73,negated_conjecture,(
    ~ ! [A,B] : r1_tarski(k2_xboole_0(k1_zfmisc_1(A),k1_zfmisc_1(B)),k1_zfmisc_1(k2_xboole_0(A,B))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_zfmisc_1)).

tff(c_66,plain,(
    ! [A_61,B_62] : k1_enumset1(A_61,A_61,B_62) = k2_tarski(A_61,B_62) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_8,plain,(
    ! [E_12,A_6,B_7] : r2_hidden(E_12,k1_enumset1(A_6,B_7,E_12)) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_75,plain,(
    ! [B_62,A_61] : r2_hidden(B_62,k2_tarski(A_61,B_62)) ),
    inference(superposition,[status(thm),theory(equality)],[c_66,c_8])).

tff(c_54,plain,(
    ! [A_59,B_60] : k3_tarski(k2_tarski(A_59,B_60)) = k2_xboole_0(A_59,B_60) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_42,plain,(
    ! [A_40,B_41] :
      ( r1_tarski(A_40,k3_tarski(B_41))
      | ~ r2_hidden(A_40,B_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_97,plain,(
    ! [A_72,A_73,B_74] :
      ( r1_tarski(A_72,k2_xboole_0(A_73,B_74))
      | ~ r2_hidden(A_72,k2_tarski(A_73,B_74)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_54,c_42])).

tff(c_104,plain,(
    ! [B_62,A_61] : r1_tarski(B_62,k2_xboole_0(A_61,B_62)) ),
    inference(resolution,[status(thm)],[c_75,c_97])).

tff(c_46,plain,(
    ! [A_44,B_45] :
      ( r1_tarski(k1_zfmisc_1(A_44),k1_zfmisc_1(B_45))
      | ~ r1_tarski(A_44,B_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_2,plain,(
    ! [A_1,B_2] : r1_tarski(A_1,k2_xboole_0(A_1,B_2)) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_117,plain,(
    ! [A_81,C_82,B_83] :
      ( r1_tarski(k2_xboole_0(A_81,C_82),B_83)
      | ~ r1_tarski(C_82,B_83)
      | ~ r1_tarski(A_81,B_83) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_48,plain,(
    ~ r1_tarski(k2_xboole_0(k1_zfmisc_1('#skF_3'),k1_zfmisc_1('#skF_4')),k1_zfmisc_1(k2_xboole_0('#skF_3','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_121,plain,
    ( ~ r1_tarski(k1_zfmisc_1('#skF_4'),k1_zfmisc_1(k2_xboole_0('#skF_3','#skF_4')))
    | ~ r1_tarski(k1_zfmisc_1('#skF_3'),k1_zfmisc_1(k2_xboole_0('#skF_3','#skF_4'))) ),
    inference(resolution,[status(thm)],[c_117,c_48])).

tff(c_152,plain,(
    ~ r1_tarski(k1_zfmisc_1('#skF_3'),k1_zfmisc_1(k2_xboole_0('#skF_3','#skF_4'))) ),
    inference(splitLeft,[status(thm)],[c_121])).

tff(c_155,plain,(
    ~ r1_tarski('#skF_3',k2_xboole_0('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_46,c_152])).

tff(c_159,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_155])).

tff(c_160,plain,(
    ~ r1_tarski(k1_zfmisc_1('#skF_4'),k1_zfmisc_1(k2_xboole_0('#skF_3','#skF_4'))) ),
    inference(splitRight,[status(thm)],[c_121])).

tff(c_164,plain,(
    ~ r1_tarski('#skF_4',k2_xboole_0('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_46,c_160])).

tff(c_168,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_164])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n019.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 16:40:22 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.12/1.24  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.12/1.25  
% 2.12/1.25  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.12/1.25  %$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 2.12/1.25  
% 2.12/1.25  %Foreground sorts:
% 2.12/1.25  
% 2.12/1.25  
% 2.12/1.25  %Background operators:
% 2.12/1.25  
% 2.12/1.25  
% 2.12/1.25  %Foreground operators:
% 2.12/1.25  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.12/1.25  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.12/1.25  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.12/1.25  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.12/1.25  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.12/1.25  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.12/1.25  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 2.12/1.25  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.12/1.25  tff('#skF_3', type, '#skF_3': $i).
% 2.12/1.25  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.12/1.25  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.12/1.25  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.12/1.25  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.12/1.25  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.12/1.25  tff('#skF_4', type, '#skF_4': $i).
% 2.12/1.25  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.12/1.25  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.12/1.25  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.12/1.25  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 2.12/1.25  
% 2.12/1.26  tff(f_50, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 2.12/1.26  tff(f_48, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_enumset1)).
% 2.12/1.26  tff(f_66, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 2.12/1.26  tff(f_64, axiom, (![A, B]: (r2_hidden(A, B) => r1_tarski(A, k3_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l49_zfmisc_1)).
% 2.12/1.26  tff(f_70, axiom, (![A, B]: (r1_tarski(A, B) => r1_tarski(k1_zfmisc_1(A), k1_zfmisc_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_zfmisc_1)).
% 2.12/1.26  tff(f_27, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 2.12/1.26  tff(f_33, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(C, B)) => r1_tarski(k2_xboole_0(A, C), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_xboole_1)).
% 2.12/1.26  tff(f_73, negated_conjecture, ~(![A, B]: r1_tarski(k2_xboole_0(k1_zfmisc_1(A), k1_zfmisc_1(B)), k1_zfmisc_1(k2_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t81_zfmisc_1)).
% 2.12/1.26  tff(c_66, plain, (![A_61, B_62]: (k1_enumset1(A_61, A_61, B_62)=k2_tarski(A_61, B_62))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.12/1.26  tff(c_8, plain, (![E_12, A_6, B_7]: (r2_hidden(E_12, k1_enumset1(A_6, B_7, E_12)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.12/1.26  tff(c_75, plain, (![B_62, A_61]: (r2_hidden(B_62, k2_tarski(A_61, B_62)))), inference(superposition, [status(thm), theory('equality')], [c_66, c_8])).
% 2.12/1.26  tff(c_54, plain, (![A_59, B_60]: (k3_tarski(k2_tarski(A_59, B_60))=k2_xboole_0(A_59, B_60))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.12/1.26  tff(c_42, plain, (![A_40, B_41]: (r1_tarski(A_40, k3_tarski(B_41)) | ~r2_hidden(A_40, B_41))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.12/1.26  tff(c_97, plain, (![A_72, A_73, B_74]: (r1_tarski(A_72, k2_xboole_0(A_73, B_74)) | ~r2_hidden(A_72, k2_tarski(A_73, B_74)))), inference(superposition, [status(thm), theory('equality')], [c_54, c_42])).
% 2.12/1.26  tff(c_104, plain, (![B_62, A_61]: (r1_tarski(B_62, k2_xboole_0(A_61, B_62)))), inference(resolution, [status(thm)], [c_75, c_97])).
% 2.12/1.26  tff(c_46, plain, (![A_44, B_45]: (r1_tarski(k1_zfmisc_1(A_44), k1_zfmisc_1(B_45)) | ~r1_tarski(A_44, B_45))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.12/1.26  tff(c_2, plain, (![A_1, B_2]: (r1_tarski(A_1, k2_xboole_0(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.12/1.26  tff(c_117, plain, (![A_81, C_82, B_83]: (r1_tarski(k2_xboole_0(A_81, C_82), B_83) | ~r1_tarski(C_82, B_83) | ~r1_tarski(A_81, B_83))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.12/1.26  tff(c_48, plain, (~r1_tarski(k2_xboole_0(k1_zfmisc_1('#skF_3'), k1_zfmisc_1('#skF_4')), k1_zfmisc_1(k2_xboole_0('#skF_3', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.12/1.26  tff(c_121, plain, (~r1_tarski(k1_zfmisc_1('#skF_4'), k1_zfmisc_1(k2_xboole_0('#skF_3', '#skF_4'))) | ~r1_tarski(k1_zfmisc_1('#skF_3'), k1_zfmisc_1(k2_xboole_0('#skF_3', '#skF_4')))), inference(resolution, [status(thm)], [c_117, c_48])).
% 2.12/1.26  tff(c_152, plain, (~r1_tarski(k1_zfmisc_1('#skF_3'), k1_zfmisc_1(k2_xboole_0('#skF_3', '#skF_4')))), inference(splitLeft, [status(thm)], [c_121])).
% 2.12/1.26  tff(c_155, plain, (~r1_tarski('#skF_3', k2_xboole_0('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_46, c_152])).
% 2.12/1.26  tff(c_159, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2, c_155])).
% 2.12/1.26  tff(c_160, plain, (~r1_tarski(k1_zfmisc_1('#skF_4'), k1_zfmisc_1(k2_xboole_0('#skF_3', '#skF_4')))), inference(splitRight, [status(thm)], [c_121])).
% 2.12/1.26  tff(c_164, plain, (~r1_tarski('#skF_4', k2_xboole_0('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_46, c_160])).
% 2.12/1.26  tff(c_168, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_104, c_164])).
% 2.12/1.26  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.12/1.26  
% 2.12/1.26  Inference rules
% 2.12/1.26  ----------------------
% 2.12/1.26  #Ref     : 0
% 2.12/1.26  #Sup     : 23
% 2.12/1.26  #Fact    : 0
% 2.12/1.26  #Define  : 0
% 2.12/1.26  #Split   : 1
% 2.12/1.26  #Chain   : 0
% 2.12/1.26  #Close   : 0
% 2.12/1.26  
% 2.12/1.26  Ordering : KBO
% 2.12/1.26  
% 2.12/1.26  Simplification rules
% 2.12/1.26  ----------------------
% 2.12/1.26  #Subsume      : 0
% 2.12/1.26  #Demod        : 4
% 2.12/1.26  #Tautology    : 15
% 2.12/1.26  #SimpNegUnit  : 0
% 2.12/1.26  #BackRed      : 0
% 2.12/1.26  
% 2.12/1.26  #Partial instantiations: 0
% 2.12/1.26  #Strategies tried      : 1
% 2.12/1.26  
% 2.12/1.26  Timing (in seconds)
% 2.12/1.26  ----------------------
% 2.12/1.26  Preprocessing        : 0.33
% 2.12/1.26  Parsing              : 0.17
% 2.12/1.26  CNF conversion       : 0.02
% 2.12/1.26  Main loop            : 0.15
% 2.12/1.26  Inferencing          : 0.05
% 2.12/1.26  Reduction            : 0.05
% 2.12/1.26  Demodulation         : 0.04
% 2.12/1.26  BG Simplification    : 0.01
% 2.12/1.26  Subsumption          : 0.03
% 2.12/1.26  Abstraction          : 0.01
% 2.12/1.27  MUC search           : 0.00
% 2.12/1.27  Cooper               : 0.00
% 2.12/1.27  Total                : 0.51
% 2.12/1.27  Index Insertion      : 0.00
% 2.12/1.27  Index Deletion       : 0.00
% 2.12/1.27  Index Matching       : 0.00
% 2.12/1.27  BG Taut test         : 0.00
%------------------------------------------------------------------------------
