%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:57:33 EST 2020

% Result     : Theorem 1.79s
% Output     : CNFRefutation 1.79s
% Verified   : 
% Statistics : Number of formulae       :   33 (  34 expanded)
%              Number of leaves         :   20 (  21 expanded)
%              Depth                    :    7
%              Number of atoms          :   33 (  35 expanded)
%              Number of equality atoms :    9 (  10 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > r1_setfam_1 > v1_xboole_0 > k4_xboole_0 > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_4 > #skF_3 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r1_setfam_1,type,(
    r1_setfam_1: ( $i * $i ) > $o )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

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

tff(f_59,negated_conjecture,(
    ~ ! [A] :
        ( r1_setfam_1(A,k1_xboole_0)
       => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_setfam_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_54,axiom,(
    ! [A,B] :
      ( r1_setfam_1(A,B)
    <=> ! [C] :
          ~ ( r2_hidden(C,A)
            & ! [D] :
                ~ ( r2_hidden(D,B)
                  & r1_tarski(C,D) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_setfam_1)).

tff(f_37,axiom,(
    ! [A] : k4_xboole_0(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).

tff(f_42,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,k1_tarski(B)) = A
    <=> ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_zfmisc_1)).

tff(f_35,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(c_22,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_24,plain,(
    r1_setfam_1('#skF_4',k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_92,plain,(
    ! [A_39,B_40,C_41] :
      ( r2_hidden('#skF_3'(A_39,B_40,C_41),B_40)
      | ~ r2_hidden(C_41,A_39)
      | ~ r1_setfam_1(A_39,B_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_8,plain,(
    ! [A_6] : k4_xboole_0(k1_xboole_0,A_6) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_64,plain,(
    ! [B_32,A_33] :
      ( ~ r2_hidden(B_32,A_33)
      | k4_xboole_0(A_33,k1_tarski(B_32)) != A_33 ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_73,plain,(
    ! [B_32] : ~ r2_hidden(B_32,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_64])).

tff(c_108,plain,(
    ! [C_45,A_46] :
      ( ~ r2_hidden(C_45,A_46)
      | ~ r1_setfam_1(A_46,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_92,c_73])).

tff(c_121,plain,(
    ! [A_47] :
      ( ~ r1_setfam_1(A_47,k1_xboole_0)
      | v1_xboole_0(A_47) ) ),
    inference(resolution,[status(thm)],[c_4,c_108])).

tff(c_136,plain,(
    v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_24,c_121])).

tff(c_6,plain,(
    ! [A_5] :
      ( k1_xboole_0 = A_5
      | ~ v1_xboole_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_139,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_136,c_6])).

tff(c_143,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_22,c_139])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n021.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 12:06:04 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.79/1.15  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.79/1.16  
% 1.79/1.16  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.79/1.16  %$ r2_hidden > r1_tarski > r1_setfam_1 > v1_xboole_0 > k4_xboole_0 > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_4 > #skF_3 > #skF_2
% 1.79/1.16  
% 1.79/1.16  %Foreground sorts:
% 1.79/1.16  
% 1.79/1.16  
% 1.79/1.16  %Background operators:
% 1.79/1.16  
% 1.79/1.16  
% 1.79/1.16  %Foreground operators:
% 1.79/1.16  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.79/1.16  tff(r1_setfam_1, type, r1_setfam_1: ($i * $i) > $o).
% 1.79/1.16  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.79/1.16  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.79/1.16  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.79/1.16  tff('#skF_1', type, '#skF_1': $i > $i).
% 1.79/1.16  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.79/1.16  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.79/1.16  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.79/1.16  tff('#skF_4', type, '#skF_4': $i).
% 1.79/1.16  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 1.79/1.16  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.79/1.16  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 1.79/1.16  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.79/1.16  
% 1.79/1.17  tff(f_59, negated_conjecture, ~(![A]: (r1_setfam_1(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t21_setfam_1)).
% 1.79/1.17  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 1.79/1.17  tff(f_54, axiom, (![A, B]: (r1_setfam_1(A, B) <=> (![C]: ~(r2_hidden(C, A) & (![D]: ~(r2_hidden(D, B) & r1_tarski(C, D))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_setfam_1)).
% 1.79/1.17  tff(f_37, axiom, (![A]: (k4_xboole_0(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_boole)).
% 1.79/1.17  tff(f_42, axiom, (![A, B]: ((k4_xboole_0(A, k1_tarski(B)) = A) <=> ~r2_hidden(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_zfmisc_1)).
% 1.79/1.17  tff(f_35, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 1.79/1.17  tff(c_22, plain, (k1_xboole_0!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_59])).
% 1.79/1.17  tff(c_24, plain, (r1_setfam_1('#skF_4', k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_59])).
% 1.79/1.17  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.79/1.17  tff(c_92, plain, (![A_39, B_40, C_41]: (r2_hidden('#skF_3'(A_39, B_40, C_41), B_40) | ~r2_hidden(C_41, A_39) | ~r1_setfam_1(A_39, B_40))), inference(cnfTransformation, [status(thm)], [f_54])).
% 1.79/1.17  tff(c_8, plain, (![A_6]: (k4_xboole_0(k1_xboole_0, A_6)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.79/1.17  tff(c_64, plain, (![B_32, A_33]: (~r2_hidden(B_32, A_33) | k4_xboole_0(A_33, k1_tarski(B_32))!=A_33)), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.79/1.17  tff(c_73, plain, (![B_32]: (~r2_hidden(B_32, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_8, c_64])).
% 1.79/1.17  tff(c_108, plain, (![C_45, A_46]: (~r2_hidden(C_45, A_46) | ~r1_setfam_1(A_46, k1_xboole_0))), inference(resolution, [status(thm)], [c_92, c_73])).
% 1.79/1.17  tff(c_121, plain, (![A_47]: (~r1_setfam_1(A_47, k1_xboole_0) | v1_xboole_0(A_47))), inference(resolution, [status(thm)], [c_4, c_108])).
% 1.79/1.17  tff(c_136, plain, (v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_24, c_121])).
% 1.79/1.17  tff(c_6, plain, (![A_5]: (k1_xboole_0=A_5 | ~v1_xboole_0(A_5))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.79/1.17  tff(c_139, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_136, c_6])).
% 1.79/1.17  tff(c_143, plain, $false, inference(negUnitSimplification, [status(thm)], [c_22, c_139])).
% 1.79/1.17  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.79/1.17  
% 1.79/1.17  Inference rules
% 1.79/1.17  ----------------------
% 1.79/1.17  #Ref     : 0
% 1.79/1.17  #Sup     : 23
% 1.79/1.17  #Fact    : 0
% 1.79/1.17  #Define  : 0
% 1.79/1.17  #Split   : 0
% 1.79/1.17  #Chain   : 0
% 1.79/1.17  #Close   : 0
% 1.79/1.17  
% 1.79/1.17  Ordering : KBO
% 1.79/1.17  
% 1.79/1.17  Simplification rules
% 1.79/1.17  ----------------------
% 1.79/1.17  #Subsume      : 0
% 1.79/1.17  #Demod        : 1
% 1.79/1.17  #Tautology    : 11
% 1.79/1.17  #SimpNegUnit  : 1
% 1.79/1.17  #BackRed      : 0
% 1.79/1.17  
% 1.79/1.17  #Partial instantiations: 0
% 1.79/1.17  #Strategies tried      : 1
% 1.79/1.17  
% 1.79/1.17  Timing (in seconds)
% 1.79/1.17  ----------------------
% 1.79/1.17  Preprocessing        : 0.29
% 1.79/1.17  Parsing              : 0.16
% 1.79/1.17  CNF conversion       : 0.02
% 1.79/1.17  Main loop            : 0.13
% 1.79/1.17  Inferencing          : 0.06
% 1.79/1.17  Reduction            : 0.03
% 1.79/1.17  Demodulation         : 0.02
% 1.79/1.17  BG Simplification    : 0.01
% 1.79/1.17  Subsumption          : 0.02
% 1.79/1.17  Abstraction          : 0.01
% 1.79/1.17  MUC search           : 0.00
% 1.79/1.17  Cooper               : 0.00
% 1.79/1.17  Total                : 0.44
% 1.79/1.17  Index Insertion      : 0.00
% 1.79/1.17  Index Deletion       : 0.00
% 1.79/1.17  Index Matching       : 0.00
% 1.79/1.17  BG Taut test         : 0.00
%------------------------------------------------------------------------------
