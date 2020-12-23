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
% DateTime   : Thu Dec  3 09:57:34 EST 2020

% Result     : Theorem 1.60s
% Output     : CNFRefutation 1.60s
% Verified   : 
% Statistics : Number of formulae       :   40 (  60 expanded)
%              Number of leaves         :   21 (  30 expanded)
%              Depth                    :   10
%              Number of atoms          :   45 (  84 expanded)
%              Number of equality atoms :    7 (  13 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > r1_setfam_1 > m1_subset_1 > v1_xboole_0 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_1 > #skF_4 > #skF_3 > #skF_5

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_2',type,(
    '#skF_2': $i > $i )).

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

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_61,negated_conjecture,(
    ~ ! [A] :
        ( r1_setfam_1(A,k1_xboole_0)
       => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_setfam_1)).

tff(f_34,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_49,axiom,(
    ! [A,B] :
      ( r1_setfam_1(A,B)
    <=> ! [C] :
          ~ ( r2_hidden(C,A)
            & ! [D] :
                ~ ( r2_hidden(D,B)
                  & r1_tarski(C,D) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_setfam_1)).

tff(f_37,axiom,(
    ! [A] :
    ? [B] : m1_subset_1(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',existence_m1_subset_1)).

tff(f_56,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(c_18,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_20,plain,(
    r1_setfam_1('#skF_5',k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_4,plain,(
    ! [A_1] :
      ( r2_hidden('#skF_1'(A_1),A_1)
      | k1_xboole_0 = A_1 ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_77,plain,(
    ! [A_36,B_37,C_38] :
      ( r2_hidden('#skF_4'(A_36,B_37,C_38),B_37)
      | ~ r2_hidden(C_38,A_36)
      | ~ r1_setfam_1(A_36,B_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_6,plain,(
    ! [A_3] : m1_subset_1('#skF_2'(A_3),A_3) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_24,plain,(
    ! [C_24,B_25,A_26] :
      ( ~ v1_xboole_0(C_24)
      | ~ m1_subset_1(B_25,k1_zfmisc_1(C_24))
      | ~ r2_hidden(A_26,B_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_29,plain,(
    ! [C_27,A_28] :
      ( ~ v1_xboole_0(C_27)
      | ~ r2_hidden(A_28,'#skF_2'(k1_zfmisc_1(C_27))) ) ),
    inference(resolution,[status(thm)],[c_6,c_24])).

tff(c_40,plain,(
    ! [C_29] :
      ( ~ v1_xboole_0(C_29)
      | '#skF_2'(k1_zfmisc_1(C_29)) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_4,c_29])).

tff(c_56,plain,(
    ! [C_33] :
      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(C_33))
      | ~ v1_xboole_0(C_33) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_6])).

tff(c_16,plain,(
    ! [C_19,B_18,A_17] :
      ( ~ v1_xboole_0(C_19)
      | ~ m1_subset_1(B_18,k1_zfmisc_1(C_19))
      | ~ r2_hidden(A_17,B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_59,plain,(
    ! [A_17,C_33] :
      ( ~ r2_hidden(A_17,k1_xboole_0)
      | ~ v1_xboole_0(C_33) ) ),
    inference(resolution,[status(thm)],[c_56,c_16])).

tff(c_60,plain,(
    ! [C_33] : ~ v1_xboole_0(C_33) ),
    inference(splitLeft,[status(thm)],[c_59])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_62,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_2])).

tff(c_63,plain,(
    ! [A_17] : ~ r2_hidden(A_17,k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_59])).

tff(c_88,plain,(
    ! [C_39,A_40] :
      ( ~ r2_hidden(C_39,A_40)
      | ~ r1_setfam_1(A_40,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_77,c_63])).

tff(c_101,plain,(
    ! [A_41] :
      ( ~ r1_setfam_1(A_41,k1_xboole_0)
      | k1_xboole_0 = A_41 ) ),
    inference(resolution,[status(thm)],[c_4,c_88])).

tff(c_108,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_20,c_101])).

tff(c_114,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_18,c_108])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n023.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 14:45:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.60/1.15  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.60/1.15  
% 1.60/1.15  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.60/1.16  %$ r2_hidden > r1_tarski > r1_setfam_1 > m1_subset_1 > v1_xboole_0 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_1 > #skF_4 > #skF_3 > #skF_5
% 1.60/1.16  
% 1.60/1.16  %Foreground sorts:
% 1.60/1.16  
% 1.60/1.16  
% 1.60/1.16  %Background operators:
% 1.60/1.16  
% 1.60/1.16  
% 1.60/1.16  %Foreground operators:
% 1.60/1.16  tff('#skF_2', type, '#skF_2': $i > $i).
% 1.60/1.16  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.60/1.16  tff(r1_setfam_1, type, r1_setfam_1: ($i * $i) > $o).
% 1.60/1.16  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.60/1.16  tff('#skF_1', type, '#skF_1': $i > $i).
% 1.60/1.16  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.60/1.16  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 1.60/1.16  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 1.60/1.16  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.60/1.16  tff('#skF_5', type, '#skF_5': $i).
% 1.60/1.16  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.60/1.16  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.60/1.16  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.60/1.16  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.60/1.16  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.60/1.16  
% 1.60/1.17  tff(f_61, negated_conjecture, ~(![A]: (r1_setfam_1(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t21_setfam_1)).
% 1.60/1.17  tff(f_34, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 1.60/1.17  tff(f_49, axiom, (![A, B]: (r1_setfam_1(A, B) <=> (![C]: ~(r2_hidden(C, A) & (![D]: ~(r2_hidden(D, B) & r1_tarski(C, D))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_setfam_1)).
% 1.60/1.17  tff(f_37, axiom, (![A]: (?[B]: m1_subset_1(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', existence_m1_subset_1)).
% 1.60/1.17  tff(f_56, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_subset)).
% 1.60/1.17  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 1.60/1.17  tff(c_18, plain, (k1_xboole_0!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_61])).
% 1.60/1.17  tff(c_20, plain, (r1_setfam_1('#skF_5', k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_61])).
% 1.60/1.17  tff(c_4, plain, (![A_1]: (r2_hidden('#skF_1'(A_1), A_1) | k1_xboole_0=A_1)), inference(cnfTransformation, [status(thm)], [f_34])).
% 1.60/1.17  tff(c_77, plain, (![A_36, B_37, C_38]: (r2_hidden('#skF_4'(A_36, B_37, C_38), B_37) | ~r2_hidden(C_38, A_36) | ~r1_setfam_1(A_36, B_37))), inference(cnfTransformation, [status(thm)], [f_49])).
% 1.60/1.17  tff(c_6, plain, (![A_3]: (m1_subset_1('#skF_2'(A_3), A_3))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.60/1.17  tff(c_24, plain, (![C_24, B_25, A_26]: (~v1_xboole_0(C_24) | ~m1_subset_1(B_25, k1_zfmisc_1(C_24)) | ~r2_hidden(A_26, B_25))), inference(cnfTransformation, [status(thm)], [f_56])).
% 1.60/1.17  tff(c_29, plain, (![C_27, A_28]: (~v1_xboole_0(C_27) | ~r2_hidden(A_28, '#skF_2'(k1_zfmisc_1(C_27))))), inference(resolution, [status(thm)], [c_6, c_24])).
% 1.60/1.17  tff(c_40, plain, (![C_29]: (~v1_xboole_0(C_29) | '#skF_2'(k1_zfmisc_1(C_29))=k1_xboole_0)), inference(resolution, [status(thm)], [c_4, c_29])).
% 1.60/1.17  tff(c_56, plain, (![C_33]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(C_33)) | ~v1_xboole_0(C_33))), inference(superposition, [status(thm), theory('equality')], [c_40, c_6])).
% 1.60/1.17  tff(c_16, plain, (![C_19, B_18, A_17]: (~v1_xboole_0(C_19) | ~m1_subset_1(B_18, k1_zfmisc_1(C_19)) | ~r2_hidden(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_56])).
% 1.60/1.17  tff(c_59, plain, (![A_17, C_33]: (~r2_hidden(A_17, k1_xboole_0) | ~v1_xboole_0(C_33))), inference(resolution, [status(thm)], [c_56, c_16])).
% 1.60/1.17  tff(c_60, plain, (![C_33]: (~v1_xboole_0(C_33))), inference(splitLeft, [status(thm)], [c_59])).
% 1.60/1.17  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 1.60/1.17  tff(c_62, plain, $false, inference(negUnitSimplification, [status(thm)], [c_60, c_2])).
% 1.60/1.17  tff(c_63, plain, (![A_17]: (~r2_hidden(A_17, k1_xboole_0))), inference(splitRight, [status(thm)], [c_59])).
% 1.60/1.17  tff(c_88, plain, (![C_39, A_40]: (~r2_hidden(C_39, A_40) | ~r1_setfam_1(A_40, k1_xboole_0))), inference(resolution, [status(thm)], [c_77, c_63])).
% 1.60/1.17  tff(c_101, plain, (![A_41]: (~r1_setfam_1(A_41, k1_xboole_0) | k1_xboole_0=A_41)), inference(resolution, [status(thm)], [c_4, c_88])).
% 1.60/1.17  tff(c_108, plain, (k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_20, c_101])).
% 1.60/1.17  tff(c_114, plain, $false, inference(negUnitSimplification, [status(thm)], [c_18, c_108])).
% 1.60/1.17  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.60/1.17  
% 1.60/1.17  Inference rules
% 1.60/1.17  ----------------------
% 1.60/1.17  #Ref     : 0
% 1.60/1.17  #Sup     : 17
% 1.60/1.17  #Fact    : 0
% 1.60/1.17  #Define  : 0
% 1.60/1.17  #Split   : 1
% 1.60/1.17  #Chain   : 0
% 1.60/1.17  #Close   : 0
% 1.60/1.17  
% 1.60/1.17  Ordering : KBO
% 1.60/1.17  
% 1.60/1.17  Simplification rules
% 1.60/1.17  ----------------------
% 1.60/1.17  #Subsume      : 4
% 1.60/1.17  #Demod        : 0
% 1.60/1.17  #Tautology    : 4
% 1.60/1.17  #SimpNegUnit  : 2
% 1.60/1.17  #BackRed      : 1
% 1.60/1.17  
% 1.60/1.17  #Partial instantiations: 0
% 1.60/1.17  #Strategies tried      : 1
% 1.60/1.17  
% 1.60/1.17  Timing (in seconds)
% 1.60/1.17  ----------------------
% 1.60/1.17  Preprocessing        : 0.27
% 1.60/1.17  Parsing              : 0.14
% 1.60/1.17  CNF conversion       : 0.02
% 1.60/1.17  Main loop            : 0.11
% 1.60/1.17  Inferencing          : 0.05
% 1.60/1.17  Reduction            : 0.03
% 1.60/1.17  Demodulation         : 0.02
% 1.60/1.17  BG Simplification    : 0.01
% 1.60/1.17  Subsumption          : 0.02
% 1.60/1.17  Abstraction          : 0.00
% 1.60/1.17  MUC search           : 0.00
% 1.60/1.17  Cooper               : 0.00
% 1.60/1.17  Total                : 0.40
% 1.60/1.17  Index Insertion      : 0.00
% 1.60/1.17  Index Deletion       : 0.00
% 1.60/1.17  Index Matching       : 0.00
% 1.60/1.17  BG Taut test         : 0.00
%------------------------------------------------------------------------------
