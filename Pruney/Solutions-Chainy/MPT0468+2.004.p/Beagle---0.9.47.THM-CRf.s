%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:58:49 EST 2020

% Result     : Theorem 1.80s
% Output     : CNFRefutation 1.80s
% Verified   : 
% Statistics : Number of formulae       :   36 (  38 expanded)
%              Number of leaves         :   21 (  23 expanded)
%              Depth                    :    6
%              Number of atoms          :   39 (  45 expanded)
%              Number of equality atoms :   10 (  12 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_relat_1 > k4_xboole_0 > k4_tarski > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_3 > #skF_4 > #skF_2 > #skF_1

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

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_66,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ( ! [B,C] : ~ r2_hidden(k4_tarski(B,C),A)
         => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_relat_1)).

tff(f_57,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( r1_tarski(A,B)
        <=> ! [C,D] :
              ( r2_hidden(k4_tarski(C,D),A)
             => r2_hidden(k4_tarski(C,D),B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_relat_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_40,axiom,(
    ! [A] : k4_xboole_0(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).

tff(f_47,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,k1_tarski(B)) = A
    <=> ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_zfmisc_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(c_28,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_32,plain,(
    v1_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_151,plain,(
    ! [A_61,B_62] :
      ( r2_hidden(k4_tarski('#skF_2'(A_61,B_62),'#skF_3'(A_61,B_62)),A_61)
      | r1_tarski(A_61,B_62)
      | ~ v1_relat_1(A_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_30,plain,(
    ! [B_31,C_32] : ~ r2_hidden(k4_tarski(B_31,C_32),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_165,plain,(
    ! [B_62] :
      ( r1_tarski('#skF_4',B_62)
      | ~ v1_relat_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_151,c_30])).

tff(c_174,plain,(
    ! [B_63] : r1_tarski('#skF_4',B_63) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_165])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_14,plain,(
    ! [A_8] : k4_xboole_0(k1_xboole_0,A_8) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_67,plain,(
    ! [B_44,A_45] :
      ( ~ r2_hidden(B_44,A_45)
      | k4_xboole_0(A_45,k1_tarski(B_44)) != A_45 ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_73,plain,(
    ! [B_46] : ~ r2_hidden(B_46,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_67])).

tff(c_79,plain,(
    ! [B_47] : r1_tarski(k1_xboole_0,B_47) ),
    inference(resolution,[status(thm)],[c_6,c_73])).

tff(c_8,plain,(
    ! [B_7,A_6] :
      ( B_7 = A_6
      | ~ r1_tarski(B_7,A_6)
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_82,plain,(
    ! [B_47] :
      ( k1_xboole_0 = B_47
      | ~ r1_tarski(B_47,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_79,c_8])).

tff(c_181,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_174,c_82])).

tff(c_189,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_181])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n011.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 13:32:27 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.80/1.18  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.80/1.18  
% 1.80/1.18  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.80/1.19  %$ r2_hidden > r1_tarski > v1_relat_1 > k4_xboole_0 > k4_tarski > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 1.80/1.19  
% 1.80/1.19  %Foreground sorts:
% 1.80/1.19  
% 1.80/1.19  
% 1.80/1.19  %Background operators:
% 1.80/1.19  
% 1.80/1.19  
% 1.80/1.19  %Foreground operators:
% 1.80/1.19  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.80/1.19  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.80/1.19  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.80/1.19  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.80/1.19  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 1.80/1.19  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.80/1.19  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 1.80/1.19  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.80/1.19  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.80/1.19  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.80/1.19  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.80/1.19  tff('#skF_4', type, '#skF_4': $i).
% 1.80/1.19  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.80/1.19  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 1.80/1.19  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.80/1.19  
% 1.80/1.20  tff(f_66, negated_conjecture, ~(![A]: (v1_relat_1(A) => ((![B, C]: ~r2_hidden(k4_tarski(B, C), A)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t56_relat_1)).
% 1.80/1.20  tff(f_57, axiom, (![A]: (v1_relat_1(A) => (![B]: (r1_tarski(A, B) <=> (![C, D]: (r2_hidden(k4_tarski(C, D), A) => r2_hidden(k4_tarski(C, D), B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_relat_1)).
% 1.80/1.20  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 1.80/1.20  tff(f_40, axiom, (![A]: (k4_xboole_0(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_boole)).
% 1.80/1.20  tff(f_47, axiom, (![A, B]: ((k4_xboole_0(A, k1_tarski(B)) = A) <=> ~r2_hidden(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_zfmisc_1)).
% 1.80/1.20  tff(f_38, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 1.80/1.20  tff(c_28, plain, (k1_xboole_0!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_66])).
% 1.80/1.20  tff(c_32, plain, (v1_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_66])).
% 1.80/1.20  tff(c_151, plain, (![A_61, B_62]: (r2_hidden(k4_tarski('#skF_2'(A_61, B_62), '#skF_3'(A_61, B_62)), A_61) | r1_tarski(A_61, B_62) | ~v1_relat_1(A_61))), inference(cnfTransformation, [status(thm)], [f_57])).
% 1.80/1.20  tff(c_30, plain, (![B_31, C_32]: (~r2_hidden(k4_tarski(B_31, C_32), '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_66])).
% 1.80/1.20  tff(c_165, plain, (![B_62]: (r1_tarski('#skF_4', B_62) | ~v1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_151, c_30])).
% 1.80/1.20  tff(c_174, plain, (![B_63]: (r1_tarski('#skF_4', B_63))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_165])).
% 1.80/1.20  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.80/1.20  tff(c_14, plain, (![A_8]: (k4_xboole_0(k1_xboole_0, A_8)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_40])).
% 1.80/1.20  tff(c_67, plain, (![B_44, A_45]: (~r2_hidden(B_44, A_45) | k4_xboole_0(A_45, k1_tarski(B_44))!=A_45)), inference(cnfTransformation, [status(thm)], [f_47])).
% 1.80/1.20  tff(c_73, plain, (![B_46]: (~r2_hidden(B_46, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_14, c_67])).
% 1.80/1.20  tff(c_79, plain, (![B_47]: (r1_tarski(k1_xboole_0, B_47))), inference(resolution, [status(thm)], [c_6, c_73])).
% 1.80/1.20  tff(c_8, plain, (![B_7, A_6]: (B_7=A_6 | ~r1_tarski(B_7, A_6) | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_38])).
% 1.80/1.20  tff(c_82, plain, (![B_47]: (k1_xboole_0=B_47 | ~r1_tarski(B_47, k1_xboole_0))), inference(resolution, [status(thm)], [c_79, c_8])).
% 1.80/1.20  tff(c_181, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_174, c_82])).
% 1.80/1.20  tff(c_189, plain, $false, inference(negUnitSimplification, [status(thm)], [c_28, c_181])).
% 1.80/1.20  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.80/1.20  
% 1.80/1.20  Inference rules
% 1.80/1.20  ----------------------
% 1.80/1.20  #Ref     : 0
% 1.80/1.20  #Sup     : 29
% 1.80/1.20  #Fact    : 0
% 1.80/1.20  #Define  : 0
% 1.80/1.20  #Split   : 0
% 1.80/1.20  #Chain   : 0
% 1.80/1.20  #Close   : 0
% 1.80/1.20  
% 1.80/1.20  Ordering : KBO
% 1.80/1.20  
% 1.80/1.20  Simplification rules
% 1.80/1.20  ----------------------
% 1.80/1.20  #Subsume      : 1
% 1.80/1.20  #Demod        : 9
% 1.80/1.20  #Tautology    : 20
% 1.80/1.20  #SimpNegUnit  : 3
% 1.80/1.20  #BackRed      : 0
% 1.80/1.20  
% 1.80/1.20  #Partial instantiations: 0
% 1.80/1.20  #Strategies tried      : 1
% 1.80/1.20  
% 1.80/1.20  Timing (in seconds)
% 1.80/1.20  ----------------------
% 1.80/1.20  Preprocessing        : 0.29
% 1.80/1.20  Parsing              : 0.15
% 1.80/1.20  CNF conversion       : 0.02
% 1.80/1.20  Main loop            : 0.14
% 1.80/1.20  Inferencing          : 0.05
% 1.80/1.20  Reduction            : 0.04
% 1.80/1.20  Demodulation         : 0.03
% 1.80/1.20  BG Simplification    : 0.01
% 1.80/1.20  Subsumption          : 0.03
% 1.80/1.20  Abstraction          : 0.01
% 1.80/1.20  MUC search           : 0.00
% 1.80/1.20  Cooper               : 0.00
% 1.80/1.20  Total                : 0.46
% 1.80/1.20  Index Insertion      : 0.00
% 1.80/1.20  Index Deletion       : 0.00
% 1.80/1.20  Index Matching       : 0.00
% 1.80/1.20  BG Taut test         : 0.00
%------------------------------------------------------------------------------
