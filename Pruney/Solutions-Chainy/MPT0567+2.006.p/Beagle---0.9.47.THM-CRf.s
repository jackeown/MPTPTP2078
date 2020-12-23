%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:01:15 EST 2020

% Result     : Theorem 4.88s
% Output     : CNFRefutation 4.88s
% Verified   : 
% Statistics : Number of formulae       :   41 (  62 expanded)
%              Number of leaves         :   23 (  32 expanded)
%              Depth                    :    8
%              Number of atoms          :   47 (  93 expanded)
%              Number of equality atoms :   18 (  36 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > v1_relat_1 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k10_relat_1 > #nlpp > k1_tarski > k1_xboole_0 > #skF_4 > #skF_6 > #skF_2 > #skF_5 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_50,axiom,(
    ! [A,B] :
      ( A != B
     => r1_xboole_0(k1_tarski(A),k1_tarski(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_zfmisc_1)).

tff(f_73,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => k10_relat_1(A,k1_xboole_0) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t171_relat_1)).

tff(f_68,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B,C] :
          ( C = k10_relat_1(A,B)
        <=> ! [D] :
              ( r2_hidden(D,C)
            <=> ? [E] :
                  ( r2_hidden(k4_tarski(D,E),A)
                  & r2_hidden(E,B) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d14_relat_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_43,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

tff(c_12,plain,(
    ! [A_10,B_11] :
      ( r1_xboole_0(k1_tarski(A_10),k1_tarski(B_11))
      | B_11 = A_10 ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_36,plain,(
    k10_relat_1('#skF_6',k1_xboole_0) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_38,plain,(
    v1_relat_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_7818,plain,(
    ! [A_3505,B_3506,C_3507] :
      ( r2_hidden('#skF_3'(A_3505,B_3506,C_3507),B_3506)
      | r2_hidden('#skF_4'(A_3505,B_3506,C_3507),C_3507)
      | k10_relat_1(A_3505,B_3506) = C_3507
      | ~ v1_relat_1(A_3505) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_46,plain,(
    ! [A_61,B_62] :
      ( r1_xboole_0(k1_tarski(A_61),k1_tarski(B_62))
      | B_62 = A_61 ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( k3_xboole_0(A_1,B_2) = k1_xboole_0
      | ~ r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_69,plain,(
    ! [A_68,B_69] :
      ( k3_xboole_0(k1_tarski(A_68),k1_tarski(B_69)) = k1_xboole_0
      | B_69 = A_68 ) ),
    inference(resolution,[status(thm)],[c_46,c_2])).

tff(c_8,plain,(
    ! [A_3,B_4,C_7] :
      ( ~ r1_xboole_0(A_3,B_4)
      | ~ r2_hidden(C_7,k3_xboole_0(A_3,B_4)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_75,plain,(
    ! [A_68,B_69,C_7] :
      ( ~ r1_xboole_0(k1_tarski(A_68),k1_tarski(B_69))
      | ~ r2_hidden(C_7,k1_xboole_0)
      | B_69 = A_68 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_69,c_8])).

tff(c_124,plain,(
    ! [C_7] : ~ r2_hidden(C_7,k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_75])).

tff(c_8500,plain,(
    ! [A_3590,B_3591] :
      ( r2_hidden('#skF_3'(A_3590,B_3591,k1_xboole_0),B_3591)
      | k10_relat_1(A_3590,B_3591) = k1_xboole_0
      | ~ v1_relat_1(A_3590) ) ),
    inference(resolution,[status(thm)],[c_7818,c_124])).

tff(c_8534,plain,(
    ! [A_3592] :
      ( k10_relat_1(A_3592,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(A_3592) ) ),
    inference(resolution,[status(thm)],[c_8500,c_124])).

tff(c_8537,plain,(
    k10_relat_1('#skF_6',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_38,c_8534])).

tff(c_8541,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_8537])).

tff(c_8543,plain,(
    ! [A_3593,B_3594] :
      ( ~ r1_xboole_0(k1_tarski(A_3593),k1_tarski(B_3594))
      | B_3594 = A_3593 ) ),
    inference(splitRight,[status(thm)],[c_75])).

tff(c_8556,plain,(
    ! [B_3599,A_3600] : B_3599 = A_3600 ),
    inference(resolution,[status(thm)],[c_12,c_8543])).

tff(c_8794,plain,(
    ! [B_3599] : k1_xboole_0 != B_3599 ),
    inference(superposition,[status(thm),theory(equality)],[c_8556,c_36])).

tff(c_8828,plain,(
    $false ),
    inference(reflexivity,[status(thm),theory(equality)],[c_8794])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n008.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:11:30 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.88/1.92  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.88/1.92  
% 4.88/1.92  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.88/1.92  %$ r2_hidden > r1_xboole_0 > v1_relat_1 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k10_relat_1 > #nlpp > k1_tarski > k1_xboole_0 > #skF_4 > #skF_6 > #skF_2 > #skF_5 > #skF_3 > #skF_1
% 4.88/1.92  
% 4.88/1.92  %Foreground sorts:
% 4.88/1.92  
% 4.88/1.92  
% 4.88/1.92  %Background operators:
% 4.88/1.92  
% 4.88/1.92  
% 4.88/1.92  %Foreground operators:
% 4.88/1.92  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.88/1.92  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.88/1.92  tff(k1_tarski, type, k1_tarski: $i > $i).
% 4.88/1.92  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.88/1.92  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 4.88/1.92  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.88/1.92  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 4.88/1.92  tff('#skF_6', type, '#skF_6': $i).
% 4.88/1.92  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 4.88/1.92  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 4.88/1.92  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.88/1.92  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 4.88/1.92  tff('#skF_5', type, '#skF_5': ($i * $i * $i * $i) > $i).
% 4.88/1.92  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.88/1.92  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 4.88/1.92  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.88/1.92  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.88/1.92  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 4.88/1.92  
% 4.88/1.93  tff(f_50, axiom, (![A, B]: (~(A = B) => r1_xboole_0(k1_tarski(A), k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_zfmisc_1)).
% 4.88/1.93  tff(f_73, negated_conjecture, ~(![A]: (v1_relat_1(A) => (k10_relat_1(A, k1_xboole_0) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t171_relat_1)).
% 4.88/1.93  tff(f_68, axiom, (![A]: (v1_relat_1(A) => (![B, C]: ((C = k10_relat_1(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (?[E]: (r2_hidden(k4_tarski(D, E), A) & r2_hidden(E, B))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d14_relat_1)).
% 4.88/1.93  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 4.88/1.93  tff(f_43, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 4.88/1.93  tff(c_12, plain, (![A_10, B_11]: (r1_xboole_0(k1_tarski(A_10), k1_tarski(B_11)) | B_11=A_10)), inference(cnfTransformation, [status(thm)], [f_50])).
% 4.88/1.93  tff(c_36, plain, (k10_relat_1('#skF_6', k1_xboole_0)!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_73])).
% 4.88/1.93  tff(c_38, plain, (v1_relat_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_73])).
% 4.88/1.93  tff(c_7818, plain, (![A_3505, B_3506, C_3507]: (r2_hidden('#skF_3'(A_3505, B_3506, C_3507), B_3506) | r2_hidden('#skF_4'(A_3505, B_3506, C_3507), C_3507) | k10_relat_1(A_3505, B_3506)=C_3507 | ~v1_relat_1(A_3505))), inference(cnfTransformation, [status(thm)], [f_68])).
% 4.88/1.93  tff(c_46, plain, (![A_61, B_62]: (r1_xboole_0(k1_tarski(A_61), k1_tarski(B_62)) | B_62=A_61)), inference(cnfTransformation, [status(thm)], [f_50])).
% 4.88/1.93  tff(c_2, plain, (![A_1, B_2]: (k3_xboole_0(A_1, B_2)=k1_xboole_0 | ~r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 4.88/1.93  tff(c_69, plain, (![A_68, B_69]: (k3_xboole_0(k1_tarski(A_68), k1_tarski(B_69))=k1_xboole_0 | B_69=A_68)), inference(resolution, [status(thm)], [c_46, c_2])).
% 4.88/1.93  tff(c_8, plain, (![A_3, B_4, C_7]: (~r1_xboole_0(A_3, B_4) | ~r2_hidden(C_7, k3_xboole_0(A_3, B_4)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.88/1.93  tff(c_75, plain, (![A_68, B_69, C_7]: (~r1_xboole_0(k1_tarski(A_68), k1_tarski(B_69)) | ~r2_hidden(C_7, k1_xboole_0) | B_69=A_68)), inference(superposition, [status(thm), theory('equality')], [c_69, c_8])).
% 4.88/1.93  tff(c_124, plain, (![C_7]: (~r2_hidden(C_7, k1_xboole_0))), inference(splitLeft, [status(thm)], [c_75])).
% 4.88/1.93  tff(c_8500, plain, (![A_3590, B_3591]: (r2_hidden('#skF_3'(A_3590, B_3591, k1_xboole_0), B_3591) | k10_relat_1(A_3590, B_3591)=k1_xboole_0 | ~v1_relat_1(A_3590))), inference(resolution, [status(thm)], [c_7818, c_124])).
% 4.88/1.93  tff(c_8534, plain, (![A_3592]: (k10_relat_1(A_3592, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(A_3592))), inference(resolution, [status(thm)], [c_8500, c_124])).
% 4.88/1.93  tff(c_8537, plain, (k10_relat_1('#skF_6', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_38, c_8534])).
% 4.88/1.93  tff(c_8541, plain, $false, inference(negUnitSimplification, [status(thm)], [c_36, c_8537])).
% 4.88/1.93  tff(c_8543, plain, (![A_3593, B_3594]: (~r1_xboole_0(k1_tarski(A_3593), k1_tarski(B_3594)) | B_3594=A_3593)), inference(splitRight, [status(thm)], [c_75])).
% 4.88/1.93  tff(c_8556, plain, (![B_3599, A_3600]: (B_3599=A_3600)), inference(resolution, [status(thm)], [c_12, c_8543])).
% 4.88/1.93  tff(c_8794, plain, (![B_3599]: (k1_xboole_0!=B_3599)), inference(superposition, [status(thm), theory('equality')], [c_8556, c_36])).
% 4.88/1.93  tff(c_8828, plain, $false, inference(reflexivity, [status(thm), theory('equality')], [c_8794])).
% 4.88/1.93  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.88/1.93  
% 4.88/1.93  Inference rules
% 4.88/1.93  ----------------------
% 4.88/1.93  #Ref     : 2
% 4.88/1.93  #Sup     : 1100
% 4.88/1.93  #Fact    : 10
% 4.88/1.93  #Define  : 0
% 4.88/1.93  #Split   : 2
% 4.88/1.93  #Chain   : 0
% 4.88/1.93  #Close   : 0
% 4.88/1.93  
% 4.88/1.93  Ordering : KBO
% 4.88/1.93  
% 4.88/1.93  Simplification rules
% 4.88/1.93  ----------------------
% 4.88/1.93  #Subsume      : 202
% 4.88/1.93  #Demod        : 91
% 4.88/1.93  #Tautology    : 96
% 4.88/1.93  #SimpNegUnit  : 2
% 4.88/1.93  #BackRed      : 2
% 4.88/1.93  
% 4.88/1.93  #Partial instantiations: 1920
% 4.88/1.93  #Strategies tried      : 1
% 4.88/1.93  
% 4.88/1.93  Timing (in seconds)
% 4.88/1.93  ----------------------
% 4.88/1.94  Preprocessing        : 0.29
% 4.88/1.94  Parsing              : 0.15
% 4.88/1.94  CNF conversion       : 0.03
% 4.88/1.94  Main loop            : 0.90
% 4.88/1.94  Inferencing          : 0.41
% 4.88/1.94  Reduction            : 0.23
% 4.88/1.94  Demodulation         : 0.13
% 4.88/1.94  BG Simplification    : 0.05
% 4.88/1.94  Subsumption          : 0.15
% 4.88/1.94  Abstraction          : 0.04
% 4.88/1.94  MUC search           : 0.00
% 4.88/1.94  Cooper               : 0.00
% 4.88/1.94  Total                : 1.21
% 4.88/1.94  Index Insertion      : 0.00
% 4.88/1.94  Index Deletion       : 0.00
% 4.88/1.94  Index Matching       : 0.00
% 4.88/1.94  BG Taut test         : 0.00
%------------------------------------------------------------------------------
