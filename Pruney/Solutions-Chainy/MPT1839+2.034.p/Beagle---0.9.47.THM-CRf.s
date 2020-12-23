%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:28:25 EST 2020

% Result     : Theorem 2.27s
% Output     : CNFRefutation 2.27s
% Verified   : 
% Statistics : Number of formulae       :   43 (  47 expanded)
%              Number of leaves         :   24 (  28 expanded)
%              Depth                    :    8
%              Number of atoms          :   51 (  66 expanded)
%              Number of equality atoms :    9 (   9 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_zfmisc_1 > v1_xboole_0 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_setfam_1 > #skF_5 > #skF_2 > #skF_4 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_zfmisc_1,type,(
    v1_zfmisc_1: $i > $o )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_76,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v1_xboole_0(A)
          & v1_zfmisc_1(A) )
       => ! [B] :
            ( ~ v1_xboole_0(k3_xboole_0(A,B))
           => r1_tarski(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tex_2)).

tff(f_45,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_64,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ! [B] :
          ( ( ~ v1_xboole_0(B)
            & v1_zfmisc_1(B) )
         => ( r1_tarski(A,B)
           => A = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tex_2)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( C = k3_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

tff(c_38,plain,(
    ~ r1_tarski('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_44,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_42,plain,(
    v1_zfmisc_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_84,plain,(
    ! [A_44,B_45] : k4_xboole_0(A_44,k4_xboole_0(A_44,B_45)) = k3_xboole_0(A_44,B_45) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_26,plain,(
    ! [A_12,B_13] : r1_tarski(k4_xboole_0(A_12,B_13),A_12) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_93,plain,(
    ! [A_44,B_45] : r1_tarski(k3_xboole_0(A_44,B_45),A_44) ),
    inference(superposition,[status(thm),theory(equality)],[c_84,c_26])).

tff(c_150,plain,(
    ! [B_59,A_60] :
      ( B_59 = A_60
      | ~ r1_tarski(A_60,B_59)
      | ~ v1_zfmisc_1(B_59)
      | v1_xboole_0(B_59)
      | v1_xboole_0(A_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_304,plain,(
    ! [A_79,B_80] :
      ( k3_xboole_0(A_79,B_80) = A_79
      | ~ v1_zfmisc_1(A_79)
      | v1_xboole_0(A_79)
      | v1_xboole_0(k3_xboole_0(A_79,B_80)) ) ),
    inference(resolution,[status(thm)],[c_93,c_150])).

tff(c_40,plain,(
    ~ v1_xboole_0(k3_xboole_0('#skF_4','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_307,plain,
    ( k3_xboole_0('#skF_4','#skF_5') = '#skF_4'
    | ~ v1_zfmisc_1('#skF_4')
    | v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_304,c_40])).

tff(c_310,plain,
    ( k3_xboole_0('#skF_4','#skF_5') = '#skF_4'
    | v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_307])).

tff(c_311,plain,(
    k3_xboole_0('#skF_4','#skF_5') = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_310])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_65,plain,(
    ! [D_35,B_36,A_37] :
      ( r2_hidden(D_35,B_36)
      | ~ r2_hidden(D_35,k3_xboole_0(A_37,B_36)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_183,plain,(
    ! [A_64,B_65,B_66] :
      ( r2_hidden('#skF_1'(k3_xboole_0(A_64,B_65),B_66),B_65)
      | r1_tarski(k3_xboole_0(A_64,B_65),B_66) ) ),
    inference(resolution,[status(thm)],[c_6,c_65])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_200,plain,(
    ! [A_64,B_65] : r1_tarski(k3_xboole_0(A_64,B_65),B_65) ),
    inference(resolution,[status(thm)],[c_183,c_4])).

tff(c_322,plain,(
    r1_tarski('#skF_4','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_311,c_200])).

tff(c_348,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_322])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n004.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 17:29:08 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.27/1.71  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.27/1.71  
% 2.27/1.71  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.27/1.71  %$ r2_hidden > r1_tarski > v1_zfmisc_1 > v1_xboole_0 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_setfam_1 > #skF_5 > #skF_2 > #skF_4 > #skF_3 > #skF_1
% 2.27/1.71  
% 2.27/1.71  %Foreground sorts:
% 2.27/1.71  
% 2.27/1.71  
% 2.27/1.71  %Background operators:
% 2.27/1.71  
% 2.27/1.71  
% 2.27/1.71  %Foreground operators:
% 2.27/1.71  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.27/1.71  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.27/1.71  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.27/1.71  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.27/1.71  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.27/1.71  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.27/1.71  tff('#skF_5', type, '#skF_5': $i).
% 2.27/1.71  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.27/1.71  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.27/1.71  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.27/1.71  tff('#skF_4', type, '#skF_4': $i).
% 2.27/1.71  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 2.27/1.71  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.27/1.71  tff(v1_zfmisc_1, type, v1_zfmisc_1: $i > $o).
% 2.27/1.71  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.27/1.71  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.27/1.71  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.27/1.71  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.27/1.71  
% 2.27/1.72  tff(f_76, negated_conjecture, ~(![A]: ((~v1_xboole_0(A) & v1_zfmisc_1(A)) => (![B]: (~v1_xboole_0(k3_xboole_0(A, B)) => r1_tarski(A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_tex_2)).
% 2.27/1.72  tff(f_45, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 2.27/1.72  tff(f_43, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 2.27/1.72  tff(f_64, axiom, (![A]: (~v1_xboole_0(A) => (![B]: ((~v1_xboole_0(B) & v1_zfmisc_1(B)) => (r1_tarski(A, B) => (A = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_tex_2)).
% 2.27/1.72  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 2.27/1.72  tff(f_41, axiom, (![A, B, C]: ((C = k3_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_xboole_0)).
% 2.27/1.72  tff(c_38, plain, (~r1_tarski('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.27/1.72  tff(c_44, plain, (~v1_xboole_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.27/1.72  tff(c_42, plain, (v1_zfmisc_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.27/1.72  tff(c_84, plain, (![A_44, B_45]: (k4_xboole_0(A_44, k4_xboole_0(A_44, B_45))=k3_xboole_0(A_44, B_45))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.27/1.72  tff(c_26, plain, (![A_12, B_13]: (r1_tarski(k4_xboole_0(A_12, B_13), A_12))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.27/1.72  tff(c_93, plain, (![A_44, B_45]: (r1_tarski(k3_xboole_0(A_44, B_45), A_44))), inference(superposition, [status(thm), theory('equality')], [c_84, c_26])).
% 2.27/1.72  tff(c_150, plain, (![B_59, A_60]: (B_59=A_60 | ~r1_tarski(A_60, B_59) | ~v1_zfmisc_1(B_59) | v1_xboole_0(B_59) | v1_xboole_0(A_60))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.27/1.72  tff(c_304, plain, (![A_79, B_80]: (k3_xboole_0(A_79, B_80)=A_79 | ~v1_zfmisc_1(A_79) | v1_xboole_0(A_79) | v1_xboole_0(k3_xboole_0(A_79, B_80)))), inference(resolution, [status(thm)], [c_93, c_150])).
% 2.27/1.72  tff(c_40, plain, (~v1_xboole_0(k3_xboole_0('#skF_4', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.27/1.72  tff(c_307, plain, (k3_xboole_0('#skF_4', '#skF_5')='#skF_4' | ~v1_zfmisc_1('#skF_4') | v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_304, c_40])).
% 2.27/1.72  tff(c_310, plain, (k3_xboole_0('#skF_4', '#skF_5')='#skF_4' | v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_307])).
% 2.27/1.72  tff(c_311, plain, (k3_xboole_0('#skF_4', '#skF_5')='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_44, c_310])).
% 2.27/1.72  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.27/1.72  tff(c_65, plain, (![D_35, B_36, A_37]: (r2_hidden(D_35, B_36) | ~r2_hidden(D_35, k3_xboole_0(A_37, B_36)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.27/1.72  tff(c_183, plain, (![A_64, B_65, B_66]: (r2_hidden('#skF_1'(k3_xboole_0(A_64, B_65), B_66), B_65) | r1_tarski(k3_xboole_0(A_64, B_65), B_66))), inference(resolution, [status(thm)], [c_6, c_65])).
% 2.27/1.72  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.27/1.72  tff(c_200, plain, (![A_64, B_65]: (r1_tarski(k3_xboole_0(A_64, B_65), B_65))), inference(resolution, [status(thm)], [c_183, c_4])).
% 2.27/1.72  tff(c_322, plain, (r1_tarski('#skF_4', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_311, c_200])).
% 2.27/1.72  tff(c_348, plain, $false, inference(negUnitSimplification, [status(thm)], [c_38, c_322])).
% 2.27/1.72  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.27/1.72  
% 2.27/1.72  Inference rules
% 2.27/1.72  ----------------------
% 2.27/1.72  #Ref     : 0
% 2.27/1.72  #Sup     : 70
% 2.27/1.72  #Fact    : 0
% 2.27/1.72  #Define  : 0
% 2.27/1.72  #Split   : 0
% 2.27/1.72  #Chain   : 0
% 2.27/1.72  #Close   : 0
% 2.27/1.72  
% 2.27/1.72  Ordering : KBO
% 2.27/1.72  
% 2.27/1.72  Simplification rules
% 2.27/1.72  ----------------------
% 2.27/1.72  #Subsume      : 2
% 2.27/1.72  #Demod        : 15
% 2.27/1.72  #Tautology    : 24
% 2.27/1.72  #SimpNegUnit  : 3
% 2.27/1.72  #BackRed      : 1
% 2.27/1.72  
% 2.27/1.72  #Partial instantiations: 0
% 2.27/1.72  #Strategies tried      : 1
% 2.27/1.72  
% 2.27/1.72  Timing (in seconds)
% 2.27/1.72  ----------------------
% 2.27/1.73  Preprocessing        : 0.55
% 2.27/1.73  Parsing              : 0.31
% 2.27/1.73  CNF conversion       : 0.04
% 2.27/1.73  Main loop            : 0.20
% 2.27/1.73  Inferencing          : 0.08
% 2.27/1.73  Reduction            : 0.05
% 2.27/1.73  Demodulation         : 0.04
% 2.27/1.73  BG Simplification    : 0.02
% 2.27/1.73  Subsumption          : 0.04
% 2.27/1.73  Abstraction          : 0.01
% 2.27/1.73  MUC search           : 0.00
% 2.27/1.73  Cooper               : 0.00
% 2.27/1.73  Total                : 0.77
% 2.27/1.73  Index Insertion      : 0.00
% 2.27/1.73  Index Deletion       : 0.00
% 2.27/1.73  Index Matching       : 0.00
% 2.27/1.73  BG Taut test         : 0.00
%------------------------------------------------------------------------------
