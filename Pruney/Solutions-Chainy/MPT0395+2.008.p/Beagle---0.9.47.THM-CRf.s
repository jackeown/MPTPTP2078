%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:57:29 EST 2020

% Result     : Theorem 2.27s
% Output     : CNFRefutation 2.27s
% Verified   : 
% Statistics : Number of formulae       :   41 (  48 expanded)
%              Number of leaves         :   23 (  28 expanded)
%              Depth                    :    8
%              Number of atoms          :   50 (  69 expanded)
%              Number of equality atoms :    7 (   8 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > r1_setfam_1 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_setfam_1 > #skF_1 > #skF_4 > #skF_3 > #skF_5 > #skF_6 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r1_setfam_1,type,(
    r1_setfam_1: ( $i * $i ) > $o )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_68,negated_conjecture,(
    ~ ! [A,B] :
        ( r1_tarski(A,B)
       => r1_setfam_1(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_setfam_1)).

tff(f_61,axiom,(
    ! [A,B] :
      ( r1_setfam_1(A,B)
    <=> ! [C] :
          ~ ( r2_hidden(C,A)
            & ! [D] :
                ~ ( r2_hidden(D,B)
                  & r1_tarski(C,D) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_setfam_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_47,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(c_42,plain,(
    ~ r1_setfam_1('#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_38,plain,(
    ! [A_15,B_16] :
      ( r2_hidden('#skF_3'(A_15,B_16),A_15)
      | r1_setfam_1(A_15,B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_44,plain,(
    r1_tarski('#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_56,plain,(
    ! [A_32,B_33] :
      ( k3_xboole_0(A_32,B_33) = A_32
      | ~ r1_tarski(A_32,B_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_64,plain,(
    k3_xboole_0('#skF_5','#skF_6') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_44,c_56])).

tff(c_2,plain,(
    ! [D_6,A_1,B_2] :
      ( r2_hidden(D_6,k4_xboole_0(A_1,B_2))
      | r2_hidden(D_6,B_2)
      | ~ r2_hidden(D_6,A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_105,plain,(
    ! [A_44,B_45] : k4_xboole_0(A_44,k4_xboole_0(A_44,B_45)) = k3_xboole_0(A_44,B_45) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_4,plain,(
    ! [D_6,B_2,A_1] :
      ( ~ r2_hidden(D_6,B_2)
      | ~ r2_hidden(D_6,k4_xboole_0(A_1,B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_174,plain,(
    ! [D_61,A_62,B_63] :
      ( ~ r2_hidden(D_61,k4_xboole_0(A_62,B_63))
      | ~ r2_hidden(D_61,k3_xboole_0(A_62,B_63)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_105,c_4])).

tff(c_258,plain,(
    ! [D_70,A_71,B_72] :
      ( ~ r2_hidden(D_70,k3_xboole_0(A_71,B_72))
      | r2_hidden(D_70,B_72)
      | ~ r2_hidden(D_70,A_71) ) ),
    inference(resolution,[status(thm)],[c_2,c_174])).

tff(c_276,plain,(
    ! [D_73] :
      ( ~ r2_hidden(D_73,'#skF_5')
      | r2_hidden(D_73,'#skF_6')
      | ~ r2_hidden(D_73,'#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_64,c_258])).

tff(c_523,plain,(
    ! [B_98] :
      ( r2_hidden('#skF_3'('#skF_5',B_98),'#skF_6')
      | ~ r2_hidden('#skF_3'('#skF_5',B_98),'#skF_5')
      | r1_setfam_1('#skF_5',B_98) ) ),
    inference(resolution,[status(thm)],[c_38,c_276])).

tff(c_529,plain,(
    ! [B_99] :
      ( r2_hidden('#skF_3'('#skF_5',B_99),'#skF_6')
      | r1_setfam_1('#skF_5',B_99) ) ),
    inference(resolution,[status(thm)],[c_38,c_523])).

tff(c_24,plain,(
    ! [B_8] : r1_tarski(B_8,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_132,plain,(
    ! [A_49,B_50,D_51] :
      ( ~ r1_tarski('#skF_3'(A_49,B_50),D_51)
      | ~ r2_hidden(D_51,B_50)
      | r1_setfam_1(A_49,B_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_137,plain,(
    ! [A_49,B_50] :
      ( ~ r2_hidden('#skF_3'(A_49,B_50),B_50)
      | r1_setfam_1(A_49,B_50) ) ),
    inference(resolution,[status(thm)],[c_24,c_132])).

tff(c_533,plain,(
    r1_setfam_1('#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_529,c_137])).

tff(c_537,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_42,c_533])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n009.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 15:03:26 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.27/1.34  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.27/1.35  
% 2.27/1.35  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.27/1.35  %$ r2_hidden > r1_tarski > r1_setfam_1 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_setfam_1 > #skF_1 > #skF_4 > #skF_3 > #skF_5 > #skF_6 > #skF_2
% 2.27/1.35  
% 2.27/1.35  %Foreground sorts:
% 2.27/1.35  
% 2.27/1.35  
% 2.27/1.35  %Background operators:
% 2.27/1.35  
% 2.27/1.35  
% 2.27/1.35  %Foreground operators:
% 2.27/1.35  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.27/1.35  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.27/1.35  tff(r1_setfam_1, type, r1_setfam_1: ($i * $i) > $o).
% 2.27/1.35  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.27/1.35  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.27/1.35  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 2.27/1.35  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.27/1.35  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.27/1.35  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.27/1.35  tff('#skF_5', type, '#skF_5': $i).
% 2.27/1.35  tff('#skF_6', type, '#skF_6': $i).
% 2.27/1.35  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.27/1.35  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.27/1.35  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.27/1.35  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.27/1.35  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.27/1.35  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.27/1.35  
% 2.27/1.36  tff(f_68, negated_conjecture, ~(![A, B]: (r1_tarski(A, B) => r1_setfam_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_setfam_1)).
% 2.27/1.36  tff(f_61, axiom, (![A, B]: (r1_setfam_1(A, B) <=> (![C]: ~(r2_hidden(C, A) & (![D]: ~(r2_hidden(D, B) & r1_tarski(C, D))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_setfam_1)).
% 2.27/1.36  tff(f_45, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 2.27/1.36  tff(f_35, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 2.27/1.36  tff(f_47, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 2.27/1.36  tff(f_41, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.27/1.36  tff(c_42, plain, (~r1_setfam_1('#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.27/1.36  tff(c_38, plain, (![A_15, B_16]: (r2_hidden('#skF_3'(A_15, B_16), A_15) | r1_setfam_1(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.27/1.36  tff(c_44, plain, (r1_tarski('#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.27/1.36  tff(c_56, plain, (![A_32, B_33]: (k3_xboole_0(A_32, B_33)=A_32 | ~r1_tarski(A_32, B_33))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.27/1.36  tff(c_64, plain, (k3_xboole_0('#skF_5', '#skF_6')='#skF_5'), inference(resolution, [status(thm)], [c_44, c_56])).
% 2.27/1.36  tff(c_2, plain, (![D_6, A_1, B_2]: (r2_hidden(D_6, k4_xboole_0(A_1, B_2)) | r2_hidden(D_6, B_2) | ~r2_hidden(D_6, A_1))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.27/1.36  tff(c_105, plain, (![A_44, B_45]: (k4_xboole_0(A_44, k4_xboole_0(A_44, B_45))=k3_xboole_0(A_44, B_45))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.27/1.36  tff(c_4, plain, (![D_6, B_2, A_1]: (~r2_hidden(D_6, B_2) | ~r2_hidden(D_6, k4_xboole_0(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.27/1.36  tff(c_174, plain, (![D_61, A_62, B_63]: (~r2_hidden(D_61, k4_xboole_0(A_62, B_63)) | ~r2_hidden(D_61, k3_xboole_0(A_62, B_63)))), inference(superposition, [status(thm), theory('equality')], [c_105, c_4])).
% 2.27/1.36  tff(c_258, plain, (![D_70, A_71, B_72]: (~r2_hidden(D_70, k3_xboole_0(A_71, B_72)) | r2_hidden(D_70, B_72) | ~r2_hidden(D_70, A_71))), inference(resolution, [status(thm)], [c_2, c_174])).
% 2.27/1.36  tff(c_276, plain, (![D_73]: (~r2_hidden(D_73, '#skF_5') | r2_hidden(D_73, '#skF_6') | ~r2_hidden(D_73, '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_64, c_258])).
% 2.27/1.36  tff(c_523, plain, (![B_98]: (r2_hidden('#skF_3'('#skF_5', B_98), '#skF_6') | ~r2_hidden('#skF_3'('#skF_5', B_98), '#skF_5') | r1_setfam_1('#skF_5', B_98))), inference(resolution, [status(thm)], [c_38, c_276])).
% 2.27/1.36  tff(c_529, plain, (![B_99]: (r2_hidden('#skF_3'('#skF_5', B_99), '#skF_6') | r1_setfam_1('#skF_5', B_99))), inference(resolution, [status(thm)], [c_38, c_523])).
% 2.27/1.36  tff(c_24, plain, (![B_8]: (r1_tarski(B_8, B_8))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.27/1.36  tff(c_132, plain, (![A_49, B_50, D_51]: (~r1_tarski('#skF_3'(A_49, B_50), D_51) | ~r2_hidden(D_51, B_50) | r1_setfam_1(A_49, B_50))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.27/1.36  tff(c_137, plain, (![A_49, B_50]: (~r2_hidden('#skF_3'(A_49, B_50), B_50) | r1_setfam_1(A_49, B_50))), inference(resolution, [status(thm)], [c_24, c_132])).
% 2.27/1.36  tff(c_533, plain, (r1_setfam_1('#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_529, c_137])).
% 2.27/1.36  tff(c_537, plain, $false, inference(negUnitSimplification, [status(thm)], [c_42, c_42, c_533])).
% 2.27/1.36  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.27/1.36  
% 2.27/1.36  Inference rules
% 2.27/1.36  ----------------------
% 2.27/1.36  #Ref     : 0
% 2.27/1.36  #Sup     : 116
% 2.27/1.36  #Fact    : 0
% 2.27/1.36  #Define  : 0
% 2.27/1.36  #Split   : 1
% 2.27/1.36  #Chain   : 0
% 2.27/1.36  #Close   : 0
% 2.27/1.36  
% 2.27/1.36  Ordering : KBO
% 2.27/1.36  
% 2.27/1.36  Simplification rules
% 2.27/1.36  ----------------------
% 2.27/1.36  #Subsume      : 7
% 2.27/1.36  #Demod        : 39
% 2.27/1.36  #Tautology    : 40
% 2.27/1.36  #SimpNegUnit  : 1
% 2.27/1.36  #BackRed      : 0
% 2.27/1.36  
% 2.27/1.36  #Partial instantiations: 0
% 2.27/1.36  #Strategies tried      : 1
% 2.27/1.36  
% 2.27/1.36  Timing (in seconds)
% 2.27/1.36  ----------------------
% 2.27/1.37  Preprocessing        : 0.32
% 2.27/1.37  Parsing              : 0.16
% 2.27/1.37  CNF conversion       : 0.02
% 2.27/1.37  Main loop            : 0.27
% 2.27/1.37  Inferencing          : 0.10
% 2.27/1.37  Reduction            : 0.08
% 2.27/1.37  Demodulation         : 0.06
% 2.27/1.37  BG Simplification    : 0.02
% 2.27/1.37  Subsumption          : 0.06
% 2.27/1.37  Abstraction          : 0.02
% 2.27/1.37  MUC search           : 0.00
% 2.27/1.37  Cooper               : 0.00
% 2.27/1.37  Total                : 0.62
% 2.27/1.37  Index Insertion      : 0.00
% 2.27/1.37  Index Deletion       : 0.00
% 2.27/1.37  Index Matching       : 0.00
% 2.27/1.37  BG Taut test         : 0.00
%------------------------------------------------------------------------------
