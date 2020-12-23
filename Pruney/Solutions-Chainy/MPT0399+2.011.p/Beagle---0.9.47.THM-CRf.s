%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:57:33 EST 2020

% Result     : Theorem 1.62s
% Output     : CNFRefutation 1.75s
% Verified   : 
% Statistics : Number of formulae       :   32 (  33 expanded)
%              Number of leaves         :   19 (  20 expanded)
%              Depth                    :    7
%              Number of atoms          :   33 (  35 expanded)
%              Number of equality atoms :    9 (  10 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > r1_setfam_1 > v1_xboole_0 > k2_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_1 > #skF_4 > #skF_3 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r1_setfam_1,type,(
    r1_setfam_1: ( $i * $i ) > $o )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(f_61,negated_conjecture,(
    ~ ! [A] :
        ( r1_setfam_1(A,k1_xboole_0)
       => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_setfam_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_56,axiom,(
    ! [A,B] :
      ( r1_setfam_1(A,B)
    <=> ! [C] :
          ~ ( r2_hidden(C,A)
            & ! [D] :
                ~ ( r2_hidden(D,B)
                  & r1_tarski(C,D) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_setfam_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_44,axiom,(
    ! [A,B] : ~ r2_hidden(A,k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_zfmisc_1)).

tff(f_35,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(c_24,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_26,plain,(
    r1_setfam_1('#skF_4',k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_104,plain,(
    ! [A_44,B_45,C_46] :
      ( r2_hidden('#skF_3'(A_44,B_45,C_46),B_45)
      | ~ r2_hidden(C_46,A_44)
      | ~ r1_setfam_1(A_44,B_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_10,plain,(
    ! [A_6] : k2_zfmisc_1(A_6,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_50,plain,(
    ! [A_25,B_26] : ~ r2_hidden(A_25,k2_zfmisc_1(A_25,B_26)) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_53,plain,(
    ! [A_6] : ~ r2_hidden(A_6,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_50])).

tff(c_114,plain,(
    ! [C_47,A_48] :
      ( ~ r2_hidden(C_47,A_48)
      | ~ r1_setfam_1(A_48,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_104,c_53])).

tff(c_127,plain,(
    ! [A_49] :
      ( ~ r1_setfam_1(A_49,k1_xboole_0)
      | v1_xboole_0(A_49) ) ),
    inference(resolution,[status(thm)],[c_4,c_114])).

tff(c_142,plain,(
    v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_26,c_127])).

tff(c_6,plain,(
    ! [A_5] :
      ( k1_xboole_0 = A_5
      | ~ v1_xboole_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_145,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_142,c_6])).

tff(c_149,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_145])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n010.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 09:37:44 EST 2020
% 0.12/0.35  % CPUTime    : 
% 0.12/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.62/1.12  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.62/1.13  
% 1.62/1.13  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.75/1.13  %$ r2_hidden > r1_tarski > r1_setfam_1 > v1_xboole_0 > k2_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_1 > #skF_4 > #skF_3 > #skF_2
% 1.75/1.13  
% 1.75/1.13  %Foreground sorts:
% 1.75/1.13  
% 1.75/1.13  
% 1.75/1.13  %Background operators:
% 1.75/1.13  
% 1.75/1.13  
% 1.75/1.13  %Foreground operators:
% 1.75/1.13  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.75/1.13  tff(r1_setfam_1, type, r1_setfam_1: ($i * $i) > $o).
% 1.75/1.13  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.75/1.13  tff('#skF_1', type, '#skF_1': $i > $i).
% 1.75/1.13  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.75/1.13  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.75/1.13  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.75/1.13  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.75/1.13  tff('#skF_4', type, '#skF_4': $i).
% 1.75/1.13  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 1.75/1.13  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.75/1.13  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 1.75/1.13  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.75/1.13  
% 1.75/1.14  tff(f_61, negated_conjecture, ~(![A]: (r1_setfam_1(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t21_setfam_1)).
% 1.75/1.14  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 1.75/1.14  tff(f_56, axiom, (![A, B]: (r1_setfam_1(A, B) <=> (![C]: ~(r2_hidden(C, A) & (![D]: ~(r2_hidden(D, B) & r1_tarski(C, D))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_setfam_1)).
% 1.75/1.14  tff(f_41, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 1.75/1.14  tff(f_44, axiom, (![A, B]: ~r2_hidden(A, k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t152_zfmisc_1)).
% 1.75/1.14  tff(f_35, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 1.75/1.14  tff(c_24, plain, (k1_xboole_0!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_61])).
% 1.75/1.14  tff(c_26, plain, (r1_setfam_1('#skF_4', k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_61])).
% 1.75/1.14  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.75/1.14  tff(c_104, plain, (![A_44, B_45, C_46]: (r2_hidden('#skF_3'(A_44, B_45, C_46), B_45) | ~r2_hidden(C_46, A_44) | ~r1_setfam_1(A_44, B_45))), inference(cnfTransformation, [status(thm)], [f_56])).
% 1.75/1.14  tff(c_10, plain, (![A_6]: (k2_zfmisc_1(A_6, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.75/1.14  tff(c_50, plain, (![A_25, B_26]: (~r2_hidden(A_25, k2_zfmisc_1(A_25, B_26)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 1.75/1.14  tff(c_53, plain, (![A_6]: (~r2_hidden(A_6, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_10, c_50])).
% 1.75/1.14  tff(c_114, plain, (![C_47, A_48]: (~r2_hidden(C_47, A_48) | ~r1_setfam_1(A_48, k1_xboole_0))), inference(resolution, [status(thm)], [c_104, c_53])).
% 1.75/1.14  tff(c_127, plain, (![A_49]: (~r1_setfam_1(A_49, k1_xboole_0) | v1_xboole_0(A_49))), inference(resolution, [status(thm)], [c_4, c_114])).
% 1.75/1.14  tff(c_142, plain, (v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_26, c_127])).
% 1.75/1.14  tff(c_6, plain, (![A_5]: (k1_xboole_0=A_5 | ~v1_xboole_0(A_5))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.75/1.14  tff(c_145, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_142, c_6])).
% 1.75/1.14  tff(c_149, plain, $false, inference(negUnitSimplification, [status(thm)], [c_24, c_145])).
% 1.75/1.14  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.75/1.14  
% 1.75/1.14  Inference rules
% 1.75/1.14  ----------------------
% 1.75/1.14  #Ref     : 0
% 1.75/1.14  #Sup     : 25
% 1.75/1.14  #Fact    : 0
% 1.75/1.14  #Define  : 0
% 1.75/1.14  #Split   : 0
% 1.75/1.14  #Chain   : 0
% 1.75/1.14  #Close   : 0
% 1.75/1.14  
% 1.75/1.14  Ordering : KBO
% 1.75/1.14  
% 1.75/1.14  Simplification rules
% 1.75/1.14  ----------------------
% 1.75/1.14  #Subsume      : 1
% 1.75/1.14  #Demod        : 1
% 1.75/1.14  #Tautology    : 12
% 1.75/1.14  #SimpNegUnit  : 1
% 1.75/1.14  #BackRed      : 0
% 1.75/1.14  
% 1.75/1.14  #Partial instantiations: 0
% 1.75/1.14  #Strategies tried      : 1
% 1.75/1.14  
% 1.75/1.14  Timing (in seconds)
% 1.75/1.14  ----------------------
% 1.75/1.14  Preprocessing        : 0.27
% 1.75/1.14  Parsing              : 0.14
% 1.75/1.14  CNF conversion       : 0.02
% 1.75/1.14  Main loop            : 0.11
% 1.75/1.14  Inferencing          : 0.05
% 1.75/1.14  Reduction            : 0.03
% 1.75/1.14  Demodulation         : 0.02
% 1.75/1.14  BG Simplification    : 0.01
% 1.75/1.14  Subsumption          : 0.02
% 1.75/1.14  Abstraction          : 0.00
% 1.75/1.14  MUC search           : 0.00
% 1.75/1.14  Cooper               : 0.00
% 1.75/1.14  Total                : 0.41
% 1.75/1.14  Index Insertion      : 0.00
% 1.75/1.14  Index Deletion       : 0.00
% 1.75/1.14  Index Matching       : 0.00
% 1.75/1.14  BG Taut test         : 0.00
%------------------------------------------------------------------------------
