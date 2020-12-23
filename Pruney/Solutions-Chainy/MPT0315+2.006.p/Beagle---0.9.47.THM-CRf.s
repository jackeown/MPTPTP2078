%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:53:56 EST 2020

% Result     : Theorem 1.84s
% Output     : CNFRefutation 1.84s
% Verified   : 
% Statistics : Number of formulae       :   33 (  45 expanded)
%              Number of leaves         :   15 (  23 expanded)
%              Depth                    :    4
%              Number of atoms          :   31 (  56 expanded)
%              Number of equality atoms :   17 (  26 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > k3_xboole_0 > k2_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(f_35,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_44,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( r1_xboole_0(A,B)
          | r1_xboole_0(C,D) )
       => r1_xboole_0(k2_zfmisc_1(A,C),k2_zfmisc_1(B,D)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t127_zfmisc_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_37,axiom,(
    ! [A,B,C,D] : k2_zfmisc_1(k3_xboole_0(A,B),k3_xboole_0(C,D)) = k3_xboole_0(k2_zfmisc_1(A,C),k2_zfmisc_1(B,D)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t123_zfmisc_1)).

tff(c_8,plain,(
    ! [A_3] : k2_zfmisc_1(A_3,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_10,plain,(
    ! [B_4] : k2_zfmisc_1(k1_xboole_0,B_4) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_16,plain,
    ( r1_xboole_0('#skF_3','#skF_4')
    | r1_xboole_0('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_39,plain,(
    r1_xboole_0('#skF_1','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_16])).

tff(c_41,plain,(
    ! [A_13,B_14] :
      ( k3_xboole_0(A_13,B_14) = k1_xboole_0
      | ~ r1_xboole_0(A_13,B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_49,plain,(
    k3_xboole_0('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_39,c_41])).

tff(c_12,plain,(
    ! [A_5,C_7,B_6,D_8] : k3_xboole_0(k2_zfmisc_1(A_5,C_7),k2_zfmisc_1(B_6,D_8)) = k2_zfmisc_1(k3_xboole_0(A_5,B_6),k3_xboole_0(C_7,D_8)) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( r1_xboole_0(A_1,B_2)
      | k3_xboole_0(A_1,B_2) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_14,plain,(
    ~ r1_xboole_0(k2_zfmisc_1('#skF_1','#skF_3'),k2_zfmisc_1('#skF_2','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_57,plain,(
    k3_xboole_0(k2_zfmisc_1('#skF_1','#skF_3'),k2_zfmisc_1('#skF_2','#skF_4')) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_4,c_14])).

tff(c_69,plain,(
    k2_zfmisc_1(k3_xboole_0('#skF_1','#skF_2'),k3_xboole_0('#skF_3','#skF_4')) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_57])).

tff(c_72,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_49,c_69])).

tff(c_73,plain,(
    r1_xboole_0('#skF_3','#skF_4') ),
    inference(splitRight,[status(thm)],[c_16])).

tff(c_80,plain,(
    ! [A_19,B_20] :
      ( k3_xboole_0(A_19,B_20) = k1_xboole_0
      | ~ r1_xboole_0(A_19,B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_88,plain,(
    k3_xboole_0('#skF_3','#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_73,c_80])).

tff(c_96,plain,(
    k3_xboole_0(k2_zfmisc_1('#skF_1','#skF_3'),k2_zfmisc_1('#skF_2','#skF_4')) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_4,c_14])).

tff(c_108,plain,(
    k2_zfmisc_1(k3_xboole_0('#skF_1','#skF_2'),k3_xboole_0('#skF_3','#skF_4')) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_96])).

tff(c_111,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_88,c_108])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 11:41:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.84/1.18  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.84/1.18  
% 1.84/1.18  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.84/1.18  %$ r1_xboole_0 > k3_xboole_0 > k2_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 1.84/1.18  
% 1.84/1.18  %Foreground sorts:
% 1.84/1.18  
% 1.84/1.18  
% 1.84/1.18  %Background operators:
% 1.84/1.18  
% 1.84/1.18  
% 1.84/1.18  %Foreground operators:
% 1.84/1.18  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.84/1.18  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.84/1.18  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.84/1.18  tff('#skF_2', type, '#skF_2': $i).
% 1.84/1.18  tff('#skF_3', type, '#skF_3': $i).
% 1.84/1.18  tff('#skF_1', type, '#skF_1': $i).
% 1.84/1.18  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.84/1.18  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.84/1.18  tff('#skF_4', type, '#skF_4': $i).
% 1.84/1.18  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.84/1.18  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.84/1.18  
% 1.84/1.19  tff(f_35, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 1.84/1.19  tff(f_44, negated_conjecture, ~(![A, B, C, D]: ((r1_xboole_0(A, B) | r1_xboole_0(C, D)) => r1_xboole_0(k2_zfmisc_1(A, C), k2_zfmisc_1(B, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t127_zfmisc_1)).
% 1.84/1.19  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 1.84/1.19  tff(f_37, axiom, (![A, B, C, D]: (k2_zfmisc_1(k3_xboole_0(A, B), k3_xboole_0(C, D)) = k3_xboole_0(k2_zfmisc_1(A, C), k2_zfmisc_1(B, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t123_zfmisc_1)).
% 1.84/1.19  tff(c_8, plain, (![A_3]: (k2_zfmisc_1(A_3, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.84/1.19  tff(c_10, plain, (![B_4]: (k2_zfmisc_1(k1_xboole_0, B_4)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.84/1.19  tff(c_16, plain, (r1_xboole_0('#skF_3', '#skF_4') | r1_xboole_0('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_44])).
% 1.84/1.19  tff(c_39, plain, (r1_xboole_0('#skF_1', '#skF_2')), inference(splitLeft, [status(thm)], [c_16])).
% 1.84/1.19  tff(c_41, plain, (![A_13, B_14]: (k3_xboole_0(A_13, B_14)=k1_xboole_0 | ~r1_xboole_0(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.84/1.19  tff(c_49, plain, (k3_xboole_0('#skF_1', '#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_39, c_41])).
% 1.84/1.19  tff(c_12, plain, (![A_5, C_7, B_6, D_8]: (k3_xboole_0(k2_zfmisc_1(A_5, C_7), k2_zfmisc_1(B_6, D_8))=k2_zfmisc_1(k3_xboole_0(A_5, B_6), k3_xboole_0(C_7, D_8)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.84/1.19  tff(c_4, plain, (![A_1, B_2]: (r1_xboole_0(A_1, B_2) | k3_xboole_0(A_1, B_2)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.84/1.19  tff(c_14, plain, (~r1_xboole_0(k2_zfmisc_1('#skF_1', '#skF_3'), k2_zfmisc_1('#skF_2', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_44])).
% 1.84/1.19  tff(c_57, plain, (k3_xboole_0(k2_zfmisc_1('#skF_1', '#skF_3'), k2_zfmisc_1('#skF_2', '#skF_4'))!=k1_xboole_0), inference(resolution, [status(thm)], [c_4, c_14])).
% 1.84/1.19  tff(c_69, plain, (k2_zfmisc_1(k3_xboole_0('#skF_1', '#skF_2'), k3_xboole_0('#skF_3', '#skF_4'))!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_12, c_57])).
% 1.84/1.19  tff(c_72, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_10, c_49, c_69])).
% 1.84/1.19  tff(c_73, plain, (r1_xboole_0('#skF_3', '#skF_4')), inference(splitRight, [status(thm)], [c_16])).
% 1.84/1.19  tff(c_80, plain, (![A_19, B_20]: (k3_xboole_0(A_19, B_20)=k1_xboole_0 | ~r1_xboole_0(A_19, B_20))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.84/1.19  tff(c_88, plain, (k3_xboole_0('#skF_3', '#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_73, c_80])).
% 1.84/1.19  tff(c_96, plain, (k3_xboole_0(k2_zfmisc_1('#skF_1', '#skF_3'), k2_zfmisc_1('#skF_2', '#skF_4'))!=k1_xboole_0), inference(resolution, [status(thm)], [c_4, c_14])).
% 1.84/1.19  tff(c_108, plain, (k2_zfmisc_1(k3_xboole_0('#skF_1', '#skF_2'), k3_xboole_0('#skF_3', '#skF_4'))!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_12, c_96])).
% 1.84/1.19  tff(c_111, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_8, c_88, c_108])).
% 1.84/1.19  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.84/1.19  
% 1.84/1.19  Inference rules
% 1.84/1.19  ----------------------
% 1.84/1.19  #Ref     : 0
% 1.84/1.19  #Sup     : 21
% 1.84/1.19  #Fact    : 0
% 1.84/1.19  #Define  : 0
% 1.84/1.19  #Split   : 1
% 1.84/1.19  #Chain   : 0
% 1.84/1.19  #Close   : 0
% 1.84/1.19  
% 1.84/1.19  Ordering : KBO
% 1.84/1.19  
% 1.84/1.19  Simplification rules
% 1.84/1.19  ----------------------
% 1.84/1.19  #Subsume      : 0
% 1.84/1.19  #Demod        : 6
% 1.84/1.19  #Tautology    : 16
% 1.84/1.19  #SimpNegUnit  : 0
% 1.84/1.19  #BackRed      : 2
% 1.84/1.19  
% 1.84/1.19  #Partial instantiations: 0
% 1.84/1.19  #Strategies tried      : 1
% 1.84/1.19  
% 1.84/1.19  Timing (in seconds)
% 1.84/1.19  ----------------------
% 1.84/1.20  Preprocessing        : 0.30
% 1.84/1.20  Parsing              : 0.15
% 1.84/1.20  CNF conversion       : 0.02
% 1.84/1.20  Main loop            : 0.11
% 1.84/1.20  Inferencing          : 0.04
% 1.84/1.20  Reduction            : 0.04
% 1.84/1.20  Demodulation         : 0.03
% 1.84/1.20  BG Simplification    : 0.01
% 1.84/1.20  Subsumption          : 0.01
% 1.84/1.20  Abstraction          : 0.01
% 1.84/1.20  MUC search           : 0.00
% 1.84/1.20  Cooper               : 0.00
% 1.84/1.20  Total                : 0.44
% 1.84/1.20  Index Insertion      : 0.00
% 1.84/1.20  Index Deletion       : 0.00
% 1.84/1.20  Index Matching       : 0.00
% 1.84/1.20  BG Taut test         : 0.00
%------------------------------------------------------------------------------
