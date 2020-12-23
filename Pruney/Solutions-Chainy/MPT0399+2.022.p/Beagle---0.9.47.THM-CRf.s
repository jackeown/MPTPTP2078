%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:57:34 EST 2020

% Result     : Theorem 1.60s
% Output     : CNFRefutation 1.60s
% Verified   : 
% Statistics : Number of formulae       :   35 (  36 expanded)
%              Number of leaves         :   20 (  21 expanded)
%              Depth                    :    8
%              Number of atoms          :   37 (  39 expanded)
%              Number of equality atoms :   10 (  11 expanded)
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

tff(f_62,negated_conjecture,(
    ~ ! [A] :
        ( r1_setfam_1(A,k1_xboole_0)
       => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_setfam_1)).

tff(f_38,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_57,axiom,(
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

tff(f_42,axiom,(
    ! [A,B] :
      ( v1_xboole_0(B)
     => v1_xboole_0(k2_zfmisc_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_zfmisc_1)).

tff(f_30,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_45,axiom,(
    ! [A,B] : ~ r2_hidden(A,k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_zfmisc_1)).

tff(c_20,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_22,plain,(
    r1_setfam_1('#skF_4',k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_6,plain,(
    ! [A_2] :
      ( r2_hidden('#skF_1'(A_2),A_2)
      | k1_xboole_0 = A_2 ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_102,plain,(
    ! [A_39,B_40,C_41] :
      ( r2_hidden('#skF_3'(A_39,B_40,C_41),B_40)
      | ~ r2_hidden(C_41,A_39)
      | ~ r1_setfam_1(A_39,B_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_31,plain,(
    ! [A_24,B_25] :
      ( v1_xboole_0(k2_zfmisc_1(A_24,B_25))
      | ~ v1_xboole_0(B_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_4,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_36,plain,(
    ! [A_26,B_27] :
      ( k2_zfmisc_1(A_26,B_27) = k1_xboole_0
      | ~ v1_xboole_0(B_27) ) ),
    inference(resolution,[status(thm)],[c_31,c_4])).

tff(c_43,plain,(
    ! [A_28] : k2_zfmisc_1(A_28,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2,c_36])).

tff(c_10,plain,(
    ! [A_6,B_7] : ~ r2_hidden(A_6,k2_zfmisc_1(A_6,B_7)) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_51,plain,(
    ! [A_28] : ~ r2_hidden(A_28,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_43,c_10])).

tff(c_114,plain,(
    ! [C_45,A_46] :
      ( ~ r2_hidden(C_45,A_46)
      | ~ r1_setfam_1(A_46,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_102,c_51])).

tff(c_127,plain,(
    ! [A_47] :
      ( ~ r1_setfam_1(A_47,k1_xboole_0)
      | k1_xboole_0 = A_47 ) ),
    inference(resolution,[status(thm)],[c_6,c_114])).

tff(c_134,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_22,c_127])).

tff(c_140,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_20,c_134])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n002.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 12:52:37 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.60/1.16  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.60/1.16  
% 1.60/1.16  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.60/1.16  %$ r2_hidden > r1_tarski > r1_setfam_1 > v1_xboole_0 > k2_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_1 > #skF_4 > #skF_3 > #skF_2
% 1.60/1.16  
% 1.60/1.16  %Foreground sorts:
% 1.60/1.16  
% 1.60/1.16  
% 1.60/1.16  %Background operators:
% 1.60/1.16  
% 1.60/1.16  
% 1.60/1.16  %Foreground operators:
% 1.60/1.16  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.60/1.16  tff(r1_setfam_1, type, r1_setfam_1: ($i * $i) > $o).
% 1.60/1.16  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.60/1.16  tff('#skF_1', type, '#skF_1': $i > $i).
% 1.60/1.16  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.60/1.16  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.60/1.16  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.60/1.16  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.60/1.16  tff('#skF_4', type, '#skF_4': $i).
% 1.60/1.16  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 1.60/1.16  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.60/1.16  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 1.60/1.16  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.60/1.16  
% 1.60/1.17  tff(f_62, negated_conjecture, ~(![A]: (r1_setfam_1(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t21_setfam_1)).
% 1.60/1.17  tff(f_38, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 1.60/1.17  tff(f_57, axiom, (![A, B]: (r1_setfam_1(A, B) <=> (![C]: ~(r2_hidden(C, A) & (![D]: ~(r2_hidden(D, B) & r1_tarski(C, D))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_setfam_1)).
% 1.60/1.17  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 1.60/1.17  tff(f_42, axiom, (![A, B]: (v1_xboole_0(B) => v1_xboole_0(k2_zfmisc_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc3_zfmisc_1)).
% 1.60/1.17  tff(f_30, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 1.60/1.17  tff(f_45, axiom, (![A, B]: ~r2_hidden(A, k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t152_zfmisc_1)).
% 1.60/1.17  tff(c_20, plain, (k1_xboole_0!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_62])).
% 1.60/1.17  tff(c_22, plain, (r1_setfam_1('#skF_4', k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_62])).
% 1.60/1.17  tff(c_6, plain, (![A_2]: (r2_hidden('#skF_1'(A_2), A_2) | k1_xboole_0=A_2)), inference(cnfTransformation, [status(thm)], [f_38])).
% 1.60/1.17  tff(c_102, plain, (![A_39, B_40, C_41]: (r2_hidden('#skF_3'(A_39, B_40, C_41), B_40) | ~r2_hidden(C_41, A_39) | ~r1_setfam_1(A_39, B_40))), inference(cnfTransformation, [status(thm)], [f_57])).
% 1.60/1.17  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 1.60/1.17  tff(c_31, plain, (![A_24, B_25]: (v1_xboole_0(k2_zfmisc_1(A_24, B_25)) | ~v1_xboole_0(B_25))), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.60/1.17  tff(c_4, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_30])).
% 1.60/1.17  tff(c_36, plain, (![A_26, B_27]: (k2_zfmisc_1(A_26, B_27)=k1_xboole_0 | ~v1_xboole_0(B_27))), inference(resolution, [status(thm)], [c_31, c_4])).
% 1.60/1.17  tff(c_43, plain, (![A_28]: (k2_zfmisc_1(A_28, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_36])).
% 1.60/1.17  tff(c_10, plain, (![A_6, B_7]: (~r2_hidden(A_6, k2_zfmisc_1(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.60/1.17  tff(c_51, plain, (![A_28]: (~r2_hidden(A_28, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_43, c_10])).
% 1.60/1.17  tff(c_114, plain, (![C_45, A_46]: (~r2_hidden(C_45, A_46) | ~r1_setfam_1(A_46, k1_xboole_0))), inference(resolution, [status(thm)], [c_102, c_51])).
% 1.60/1.17  tff(c_127, plain, (![A_47]: (~r1_setfam_1(A_47, k1_xboole_0) | k1_xboole_0=A_47)), inference(resolution, [status(thm)], [c_6, c_114])).
% 1.60/1.17  tff(c_134, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_22, c_127])).
% 1.60/1.17  tff(c_140, plain, $false, inference(negUnitSimplification, [status(thm)], [c_20, c_134])).
% 1.60/1.17  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.60/1.17  
% 1.60/1.17  Inference rules
% 1.60/1.17  ----------------------
% 1.60/1.17  #Ref     : 0
% 1.60/1.17  #Sup     : 24
% 1.60/1.17  #Fact    : 0
% 1.60/1.17  #Define  : 0
% 1.60/1.17  #Split   : 0
% 1.60/1.17  #Chain   : 0
% 1.60/1.17  #Close   : 0
% 1.60/1.17  
% 1.60/1.17  Ordering : KBO
% 1.60/1.17  
% 1.60/1.17  Simplification rules
% 1.60/1.17  ----------------------
% 1.60/1.17  #Subsume      : 1
% 1.60/1.17  #Demod        : 7
% 1.60/1.17  #Tautology    : 12
% 1.60/1.17  #SimpNegUnit  : 1
% 1.60/1.17  #BackRed      : 0
% 1.60/1.17  
% 1.60/1.17  #Partial instantiations: 0
% 1.60/1.17  #Strategies tried      : 1
% 1.60/1.17  
% 1.60/1.17  Timing (in seconds)
% 1.60/1.17  ----------------------
% 1.80/1.18  Preprocessing        : 0.27
% 1.80/1.18  Parsing              : 0.15
% 1.80/1.18  CNF conversion       : 0.02
% 1.80/1.18  Main loop            : 0.12
% 1.80/1.18  Inferencing          : 0.05
% 1.80/1.18  Reduction            : 0.03
% 1.80/1.18  Demodulation         : 0.02
% 1.80/1.18  BG Simplification    : 0.01
% 1.80/1.18  Subsumption          : 0.02
% 1.80/1.18  Abstraction          : 0.01
% 1.80/1.18  MUC search           : 0.00
% 1.80/1.18  Cooper               : 0.00
% 1.80/1.18  Total                : 0.42
% 1.80/1.18  Index Insertion      : 0.00
% 1.80/1.18  Index Deletion       : 0.00
% 1.80/1.18  Index Matching       : 0.00
% 1.80/1.18  BG Taut test         : 0.00
%------------------------------------------------------------------------------
