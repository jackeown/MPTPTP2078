%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:57:32 EST 2020

% Result     : Theorem 1.92s
% Output     : CNFRefutation 2.06s
% Verified   : 
% Statistics : Number of formulae       :   40 (  44 expanded)
%              Number of leaves         :   22 (  25 expanded)
%              Depth                    :    7
%              Number of atoms          :   47 (  55 expanded)
%              Number of equality atoms :    8 (   9 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > r1_setfam_1 > v1_xboole_0 > k2_zfmisc_1 > #nlpp > k1_subset_1 > k1_xboole_0 > #skF_1 > #skF_4 > #skF_3 > #skF_5 > #skF_2

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

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k1_subset_1,type,(
    k1_subset_1: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(f_65,negated_conjecture,(
    ~ ! [A] :
        ( r1_setfam_1(A,k1_xboole_0)
       => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_setfam_1)).

tff(f_46,axiom,(
    ! [A] : k1_subset_1(A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_subset_1)).

tff(f_48,axiom,(
    ! [A] : v1_xboole_0(k1_subset_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc13_subset_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_60,axiom,(
    ! [A,B] :
      ( r1_setfam_1(A,B)
    <=> ! [C] :
          ~ ( r2_hidden(C,A)
            & ! [D] :
                ~ ( r2_hidden(D,B)
                  & r1_tarski(C,D) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_setfam_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_44,axiom,(
    ! [A,B] :
      ( ( r1_tarski(A,k2_zfmisc_1(A,B))
        | r1_tarski(A,k2_zfmisc_1(B,A)) )
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t135_zfmisc_1)).

tff(c_28,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_16,plain,(
    ! [A_12] : k1_subset_1(A_12) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_18,plain,(
    ! [A_13] : v1_xboole_0(k1_subset_1(A_13)) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_31,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_18])).

tff(c_30,plain,(
    r1_setfam_1('#skF_5',k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_179,plain,(
    ! [A_79,B_80,C_81] :
      ( r2_hidden('#skF_4'(A_79,B_80,C_81),B_80)
      | ~ r2_hidden(C_81,A_79)
      | ~ r1_setfam_1(A_79,B_80) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_190,plain,(
    ! [B_82,C_83,A_84] :
      ( ~ v1_xboole_0(B_82)
      | ~ r2_hidden(C_83,A_84)
      | ~ r1_setfam_1(A_84,B_82) ) ),
    inference(resolution,[status(thm)],[c_179,c_2])).

tff(c_209,plain,(
    ! [B_85,A_86] :
      ( ~ v1_xboole_0(B_85)
      | ~ r1_setfam_1(A_86,B_85)
      | v1_xboole_0(A_86) ) ),
    inference(resolution,[status(thm)],[c_4,c_190])).

tff(c_218,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_30,c_209])).

tff(c_223,plain,(
    v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_31,c_218])).

tff(c_54,plain,(
    ! [A_40,B_41] :
      ( r2_hidden('#skF_2'(A_40,B_41),A_40)
      | r1_tarski(A_40,B_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_65,plain,(
    ! [A_43,B_44] :
      ( ~ v1_xboole_0(A_43)
      | r1_tarski(A_43,B_44) ) ),
    inference(resolution,[status(thm)],[c_54,c_2])).

tff(c_14,plain,(
    ! [A_10,B_11] :
      ( ~ r1_tarski(A_10,k2_zfmisc_1(A_10,B_11))
      | k1_xboole_0 = A_10 ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_74,plain,(
    ! [A_43] :
      ( k1_xboole_0 = A_43
      | ~ v1_xboole_0(A_43) ) ),
    inference(resolution,[status(thm)],[c_65,c_14])).

tff(c_226,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_223,c_74])).

tff(c_230,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_226])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:46:05 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.92/1.23  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.92/1.23  
% 1.92/1.23  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.92/1.23  %$ r2_hidden > r1_tarski > r1_setfam_1 > v1_xboole_0 > k2_zfmisc_1 > #nlpp > k1_subset_1 > k1_xboole_0 > #skF_1 > #skF_4 > #skF_3 > #skF_5 > #skF_2
% 1.92/1.23  
% 1.92/1.23  %Foreground sorts:
% 1.92/1.23  
% 1.92/1.23  
% 1.92/1.23  %Background operators:
% 1.92/1.23  
% 1.92/1.23  
% 1.92/1.23  %Foreground operators:
% 1.92/1.23  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.92/1.23  tff(r1_setfam_1, type, r1_setfam_1: ($i * $i) > $o).
% 1.92/1.23  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.92/1.23  tff('#skF_1', type, '#skF_1': $i > $i).
% 1.92/1.23  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.92/1.23  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 1.92/1.23  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 1.92/1.23  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.92/1.23  tff('#skF_5', type, '#skF_5': $i).
% 1.92/1.23  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.92/1.23  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.92/1.23  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.92/1.23  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 1.92/1.23  tff(k1_subset_1, type, k1_subset_1: $i > $i).
% 1.92/1.23  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.92/1.23  
% 2.06/1.24  tff(f_65, negated_conjecture, ~(![A]: (r1_setfam_1(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t21_setfam_1)).
% 2.06/1.24  tff(f_46, axiom, (![A]: (k1_subset_1(A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_subset_1)).
% 2.06/1.24  tff(f_48, axiom, (![A]: v1_xboole_0(k1_subset_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc13_subset_1)).
% 2.06/1.24  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 2.06/1.24  tff(f_60, axiom, (![A, B]: (r1_setfam_1(A, B) <=> (![C]: ~(r2_hidden(C, A) & (![D]: ~(r2_hidden(D, B) & r1_tarski(C, D))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_setfam_1)).
% 2.06/1.24  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 2.06/1.24  tff(f_44, axiom, (![A, B]: ((r1_tarski(A, k2_zfmisc_1(A, B)) | r1_tarski(A, k2_zfmisc_1(B, A))) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t135_zfmisc_1)).
% 2.06/1.24  tff(c_28, plain, (k1_xboole_0!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.06/1.24  tff(c_16, plain, (![A_12]: (k1_subset_1(A_12)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.06/1.24  tff(c_18, plain, (![A_13]: (v1_xboole_0(k1_subset_1(A_13)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.06/1.24  tff(c_31, plain, (v1_xboole_0(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_16, c_18])).
% 2.06/1.24  tff(c_30, plain, (r1_setfam_1('#skF_5', k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.06/1.24  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.06/1.24  tff(c_179, plain, (![A_79, B_80, C_81]: (r2_hidden('#skF_4'(A_79, B_80, C_81), B_80) | ~r2_hidden(C_81, A_79) | ~r1_setfam_1(A_79, B_80))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.06/1.24  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.06/1.24  tff(c_190, plain, (![B_82, C_83, A_84]: (~v1_xboole_0(B_82) | ~r2_hidden(C_83, A_84) | ~r1_setfam_1(A_84, B_82))), inference(resolution, [status(thm)], [c_179, c_2])).
% 2.06/1.24  tff(c_209, plain, (![B_85, A_86]: (~v1_xboole_0(B_85) | ~r1_setfam_1(A_86, B_85) | v1_xboole_0(A_86))), inference(resolution, [status(thm)], [c_4, c_190])).
% 2.06/1.24  tff(c_218, plain, (~v1_xboole_0(k1_xboole_0) | v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_30, c_209])).
% 2.06/1.24  tff(c_223, plain, (v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_31, c_218])).
% 2.06/1.24  tff(c_54, plain, (![A_40, B_41]: (r2_hidden('#skF_2'(A_40, B_41), A_40) | r1_tarski(A_40, B_41))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.06/1.24  tff(c_65, plain, (![A_43, B_44]: (~v1_xboole_0(A_43) | r1_tarski(A_43, B_44))), inference(resolution, [status(thm)], [c_54, c_2])).
% 2.06/1.24  tff(c_14, plain, (![A_10, B_11]: (~r1_tarski(A_10, k2_zfmisc_1(A_10, B_11)) | k1_xboole_0=A_10)), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.06/1.24  tff(c_74, plain, (![A_43]: (k1_xboole_0=A_43 | ~v1_xboole_0(A_43))), inference(resolution, [status(thm)], [c_65, c_14])).
% 2.06/1.24  tff(c_226, plain, (k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_223, c_74])).
% 2.06/1.24  tff(c_230, plain, $false, inference(negUnitSimplification, [status(thm)], [c_28, c_226])).
% 2.06/1.24  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.06/1.24  
% 2.06/1.24  Inference rules
% 2.06/1.24  ----------------------
% 2.06/1.24  #Ref     : 0
% 2.06/1.24  #Sup     : 45
% 2.06/1.24  #Fact    : 0
% 2.06/1.24  #Define  : 0
% 2.06/1.24  #Split   : 0
% 2.06/1.24  #Chain   : 0
% 2.06/1.24  #Close   : 0
% 2.06/1.24  
% 2.06/1.24  Ordering : KBO
% 2.06/1.24  
% 2.06/1.24  Simplification rules
% 2.06/1.24  ----------------------
% 2.06/1.24  #Subsume      : 3
% 2.06/1.24  #Demod        : 2
% 2.06/1.24  #Tautology    : 9
% 2.06/1.24  #SimpNegUnit  : 1
% 2.06/1.24  #BackRed      : 0
% 2.06/1.24  
% 2.06/1.24  #Partial instantiations: 0
% 2.06/1.24  #Strategies tried      : 1
% 2.06/1.24  
% 2.06/1.24  Timing (in seconds)
% 2.06/1.24  ----------------------
% 2.06/1.25  Preprocessing        : 0.29
% 2.06/1.25  Parsing              : 0.15
% 2.06/1.25  CNF conversion       : 0.02
% 2.06/1.25  Main loop            : 0.20
% 2.06/1.25  Inferencing          : 0.08
% 2.06/1.25  Reduction            : 0.05
% 2.06/1.25  Demodulation         : 0.03
% 2.06/1.25  BG Simplification    : 0.02
% 2.06/1.25  Subsumption          : 0.04
% 2.06/1.25  Abstraction          : 0.01
% 2.06/1.25  MUC search           : 0.00
% 2.06/1.25  Cooper               : 0.00
% 2.06/1.25  Total                : 0.52
% 2.06/1.25  Index Insertion      : 0.00
% 2.06/1.25  Index Deletion       : 0.00
% 2.06/1.25  Index Matching       : 0.00
% 2.06/1.25  BG Taut test         : 0.00
%------------------------------------------------------------------------------
