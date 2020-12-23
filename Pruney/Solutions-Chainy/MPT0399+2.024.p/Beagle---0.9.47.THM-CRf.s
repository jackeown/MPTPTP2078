%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:57:35 EST 2020

% Result     : Theorem 1.73s
% Output     : CNFRefutation 1.73s
% Verified   : 
% Statistics : Number of formulae       :   39 (  48 expanded)
%              Number of leaves         :   22 (  27 expanded)
%              Depth                    :   10
%              Number of atoms          :   42 (  59 expanded)
%              Number of equality atoms :    8 (  11 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_subset_1 > r2_hidden > r1_tarski > r1_setfam_1 > m1_subset_1 > v1_xboole_0 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_4 > #skF_1 > #skF_5 > #skF_3 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_4',type,(
    '#skF_4': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r1_setfam_1,type,(
    r1_setfam_1: ( $i * $i ) > $o )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(v1_subset_1,type,(
    v1_subset_1: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_64,negated_conjecture,(
    ~ ! [A] :
        ( r1_setfam_1(A,k1_xboole_0)
       => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_setfam_1)).

tff(f_34,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_46,axiom,(
    ! [A,B] :
      ( r1_setfam_1(A,B)
    <=> ! [C] :
          ~ ( r2_hidden(C,A)
            & ! [D] :
                ~ ( r2_hidden(D,B)
                  & r1_tarski(C,D) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_setfam_1)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_52,axiom,(
    ! [A] :
    ? [B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
      & ~ v1_subset_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc3_subset_1)).

tff(f_59,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

tff(c_20,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_22,plain,(
    r1_setfam_1('#skF_5',k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_4,plain,(
    ! [A_1] :
      ( r2_hidden('#skF_1'(A_1),A_1)
      | k1_xboole_0 = A_1 ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_76,plain,(
    ! [A_36,B_37,C_38] :
      ( r2_hidden('#skF_3'(A_36,B_37,C_38),B_37)
      | ~ r2_hidden(C_38,A_36)
      | ~ r1_setfam_1(A_36,B_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_16,plain,(
    ! [A_15] : m1_subset_1('#skF_4'(A_15),k1_zfmisc_1(A_15)) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_27,plain,(
    ! [C_25,B_26,A_27] :
      ( ~ v1_xboole_0(C_25)
      | ~ m1_subset_1(B_26,k1_zfmisc_1(C_25))
      | ~ r2_hidden(A_27,B_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_31,plain,(
    ! [A_28,A_29] :
      ( ~ v1_xboole_0(A_28)
      | ~ r2_hidden(A_29,'#skF_4'(A_28)) ) ),
    inference(resolution,[status(thm)],[c_16,c_27])).

tff(c_43,plain,(
    ! [A_33] :
      ( ~ v1_xboole_0(A_33)
      | '#skF_4'(A_33) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_4,c_31])).

tff(c_47,plain,(
    '#skF_4'(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2,c_43])).

tff(c_30,plain,(
    ! [A_15,A_27] :
      ( ~ v1_xboole_0(A_15)
      | ~ r2_hidden(A_27,'#skF_4'(A_15)) ) ),
    inference(resolution,[status(thm)],[c_16,c_27])).

tff(c_51,plain,(
    ! [A_27] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | ~ r2_hidden(A_27,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_47,c_30])).

tff(c_61,plain,(
    ! [A_27] : ~ r2_hidden(A_27,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_51])).

tff(c_98,plain,(
    ! [C_41,A_42] :
      ( ~ r2_hidden(C_41,A_42)
      | ~ r1_setfam_1(A_42,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_76,c_61])).

tff(c_117,plain,(
    ! [A_46] :
      ( ~ r1_setfam_1(A_46,k1_xboole_0)
      | k1_xboole_0 = A_46 ) ),
    inference(resolution,[status(thm)],[c_4,c_98])).

tff(c_128,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_22,c_117])).

tff(c_135,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_20,c_128])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n003.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 17:19:57 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.73/1.20  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.73/1.20  
% 1.73/1.20  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.73/1.21  %$ v1_subset_1 > r2_hidden > r1_tarski > r1_setfam_1 > m1_subset_1 > v1_xboole_0 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_4 > #skF_1 > #skF_5 > #skF_3 > #skF_2
% 1.73/1.21  
% 1.73/1.21  %Foreground sorts:
% 1.73/1.21  
% 1.73/1.21  
% 1.73/1.21  %Background operators:
% 1.73/1.21  
% 1.73/1.21  
% 1.73/1.21  %Foreground operators:
% 1.73/1.21  tff('#skF_4', type, '#skF_4': $i > $i).
% 1.73/1.21  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.73/1.21  tff(r1_setfam_1, type, r1_setfam_1: ($i * $i) > $o).
% 1.73/1.21  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.73/1.21  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 1.73/1.21  tff('#skF_1', type, '#skF_1': $i > $i).
% 1.73/1.21  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.73/1.21  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.73/1.21  tff('#skF_5', type, '#skF_5': $i).
% 1.73/1.21  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.73/1.21  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.73/1.21  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 1.73/1.21  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.73/1.21  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 1.73/1.21  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.73/1.21  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.73/1.21  
% 1.73/1.22  tff(f_64, negated_conjecture, ~(![A]: (r1_setfam_1(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t21_setfam_1)).
% 1.73/1.22  tff(f_34, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 1.73/1.22  tff(f_46, axiom, (![A, B]: (r1_setfam_1(A, B) <=> (![C]: ~(r2_hidden(C, A) & (![D]: ~(r2_hidden(D, B) & r1_tarski(C, D))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_setfam_1)).
% 1.73/1.22  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 1.73/1.22  tff(f_52, axiom, (![A]: (?[B]: (m1_subset_1(B, k1_zfmisc_1(A)) & ~v1_subset_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', rc3_subset_1)).
% 1.73/1.22  tff(f_59, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_subset)).
% 1.73/1.22  tff(c_20, plain, (k1_xboole_0!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_64])).
% 1.73/1.22  tff(c_22, plain, (r1_setfam_1('#skF_5', k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_64])).
% 1.73/1.22  tff(c_4, plain, (![A_1]: (r2_hidden('#skF_1'(A_1), A_1) | k1_xboole_0=A_1)), inference(cnfTransformation, [status(thm)], [f_34])).
% 1.73/1.22  tff(c_76, plain, (![A_36, B_37, C_38]: (r2_hidden('#skF_3'(A_36, B_37, C_38), B_37) | ~r2_hidden(C_38, A_36) | ~r1_setfam_1(A_36, B_37))), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.73/1.22  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 1.73/1.22  tff(c_16, plain, (![A_15]: (m1_subset_1('#skF_4'(A_15), k1_zfmisc_1(A_15)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 1.73/1.22  tff(c_27, plain, (![C_25, B_26, A_27]: (~v1_xboole_0(C_25) | ~m1_subset_1(B_26, k1_zfmisc_1(C_25)) | ~r2_hidden(A_27, B_26))), inference(cnfTransformation, [status(thm)], [f_59])).
% 1.73/1.22  tff(c_31, plain, (![A_28, A_29]: (~v1_xboole_0(A_28) | ~r2_hidden(A_29, '#skF_4'(A_28)))), inference(resolution, [status(thm)], [c_16, c_27])).
% 1.73/1.22  tff(c_43, plain, (![A_33]: (~v1_xboole_0(A_33) | '#skF_4'(A_33)=k1_xboole_0)), inference(resolution, [status(thm)], [c_4, c_31])).
% 1.73/1.22  tff(c_47, plain, ('#skF_4'(k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_2, c_43])).
% 1.73/1.22  tff(c_30, plain, (![A_15, A_27]: (~v1_xboole_0(A_15) | ~r2_hidden(A_27, '#skF_4'(A_15)))), inference(resolution, [status(thm)], [c_16, c_27])).
% 1.73/1.22  tff(c_51, plain, (![A_27]: (~v1_xboole_0(k1_xboole_0) | ~r2_hidden(A_27, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_47, c_30])).
% 1.73/1.22  tff(c_61, plain, (![A_27]: (~r2_hidden(A_27, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_51])).
% 1.73/1.22  tff(c_98, plain, (![C_41, A_42]: (~r2_hidden(C_41, A_42) | ~r1_setfam_1(A_42, k1_xboole_0))), inference(resolution, [status(thm)], [c_76, c_61])).
% 1.73/1.22  tff(c_117, plain, (![A_46]: (~r1_setfam_1(A_46, k1_xboole_0) | k1_xboole_0=A_46)), inference(resolution, [status(thm)], [c_4, c_98])).
% 1.73/1.22  tff(c_128, plain, (k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_22, c_117])).
% 1.73/1.22  tff(c_135, plain, $false, inference(negUnitSimplification, [status(thm)], [c_20, c_128])).
% 1.73/1.22  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.73/1.22  
% 1.73/1.22  Inference rules
% 1.73/1.22  ----------------------
% 1.73/1.22  #Ref     : 0
% 1.73/1.22  #Sup     : 22
% 1.73/1.22  #Fact    : 0
% 1.73/1.22  #Define  : 0
% 1.73/1.22  #Split   : 0
% 1.73/1.22  #Chain   : 0
% 1.73/1.22  #Close   : 0
% 1.73/1.22  
% 1.73/1.22  Ordering : KBO
% 1.73/1.22  
% 1.73/1.22  Simplification rules
% 1.73/1.22  ----------------------
% 1.73/1.22  #Subsume      : 2
% 1.73/1.22  #Demod        : 4
% 1.73/1.22  #Tautology    : 5
% 1.73/1.22  #SimpNegUnit  : 1
% 1.73/1.22  #BackRed      : 0
% 1.73/1.22  
% 1.73/1.22  #Partial instantiations: 0
% 1.73/1.22  #Strategies tried      : 1
% 1.73/1.22  
% 1.73/1.22  Timing (in seconds)
% 1.73/1.22  ----------------------
% 1.73/1.22  Preprocessing        : 0.29
% 1.73/1.22  Parsing              : 0.16
% 1.73/1.22  CNF conversion       : 0.02
% 1.73/1.22  Main loop            : 0.12
% 1.73/1.22  Inferencing          : 0.05
% 1.73/1.22  Reduction            : 0.03
% 1.73/1.22  Demodulation         : 0.02
% 1.73/1.22  BG Simplification    : 0.01
% 1.73/1.22  Subsumption          : 0.02
% 1.73/1.22  Abstraction          : 0.01
% 1.73/1.22  MUC search           : 0.00
% 1.73/1.22  Cooper               : 0.00
% 1.73/1.22  Total                : 0.44
% 1.73/1.22  Index Insertion      : 0.00
% 1.73/1.22  Index Deletion       : 0.00
% 1.73/1.22  Index Matching       : 0.00
% 1.73/1.22  BG Taut test         : 0.00
%------------------------------------------------------------------------------
