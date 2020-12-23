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
% DateTime   : Thu Dec  3 10:00:34 EST 2020

% Result     : Theorem 2.07s
% Output     : CNFRefutation 2.07s
% Verified   : 
% Statistics : Number of formulae       :   47 (  64 expanded)
%              Number of leaves         :   28 (  36 expanded)
%              Depth                    :    9
%              Number of atoms          :   44 (  69 expanded)
%              Number of equality atoms :   10 (  21 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > v1_xboole_0 > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k4_tarski > k2_tarski > #nlpp > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_4 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_37,axiom,(
    ? [A] : v1_xboole_0(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc1_xboole_0)).

tff(f_35,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_78,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => k9_relat_1(A,k1_xboole_0) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t149_relat_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_73,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k9_relat_1(C,B))
      <=> ? [D] :
            ( r2_hidden(D,k1_relat_1(C))
            & r2_hidden(k4_tarski(D,A),C)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t143_relat_1)).

tff(f_39,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_62,axiom,(
    ! [A,B,C] :
      ~ ( r1_xboole_0(k2_tarski(A,B),C)
        & r2_hidden(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_zfmisc_1)).

tff(c_8,plain,(
    v1_xboole_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_38,plain,(
    ! [A_41] :
      ( k1_xboole_0 = A_41
      | ~ v1_xboole_0(A_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_42,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_8,c_38])).

tff(c_34,plain,(
    k9_relat_1('#skF_4',k1_xboole_0) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_45,plain,(
    k9_relat_1('#skF_4','#skF_2') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_42,c_34])).

tff(c_36,plain,(
    v1_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_107,plain,(
    ! [A_62,B_63,C_64] :
      ( r2_hidden('#skF_3'(A_62,B_63,C_64),B_63)
      | ~ r2_hidden(A_62,k9_relat_1(C_64,B_63))
      | ~ v1_relat_1(C_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_10,plain,(
    ! [A_6] : r1_xboole_0(A_6,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_46,plain,(
    ! [A_6] : r1_xboole_0(A_6,'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_10])).

tff(c_76,plain,(
    ! [A_51,C_52,B_53] :
      ( ~ r2_hidden(A_51,C_52)
      | ~ r1_xboole_0(k2_tarski(A_51,B_53),C_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_81,plain,(
    ! [A_51] : ~ r2_hidden(A_51,'#skF_2') ),
    inference(resolution,[status(thm)],[c_46,c_76])).

tff(c_117,plain,(
    ! [A_65,C_66] :
      ( ~ r2_hidden(A_65,k9_relat_1(C_66,'#skF_2'))
      | ~ v1_relat_1(C_66) ) ),
    inference(resolution,[status(thm)],[c_107,c_81])).

tff(c_133,plain,(
    ! [C_70] :
      ( ~ v1_relat_1(C_70)
      | v1_xboole_0(k9_relat_1(C_70,'#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_4,c_117])).

tff(c_6,plain,(
    ! [A_5] :
      ( k1_xboole_0 = A_5
      | ~ v1_xboole_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_44,plain,(
    ! [A_5] :
      ( A_5 = '#skF_2'
      | ~ v1_xboole_0(A_5) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_6])).

tff(c_141,plain,(
    ! [C_71] :
      ( k9_relat_1(C_71,'#skF_2') = '#skF_2'
      | ~ v1_relat_1(C_71) ) ),
    inference(resolution,[status(thm)],[c_133,c_44])).

tff(c_144,plain,(
    k9_relat_1('#skF_4','#skF_2') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_36,c_141])).

tff(c_148,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_45,c_144])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n008.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 14:02:30 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.07/1.18  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.07/1.18  
% 2.07/1.18  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.07/1.18  %$ r2_hidden > r1_xboole_0 > v1_xboole_0 > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k4_tarski > k2_tarski > #nlpp > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_4 > #skF_3
% 2.07/1.18  
% 2.07/1.18  %Foreground sorts:
% 2.07/1.18  
% 2.07/1.18  
% 2.07/1.18  %Background operators:
% 2.07/1.18  
% 2.07/1.18  
% 2.07/1.18  %Foreground operators:
% 2.07/1.18  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.07/1.18  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.07/1.18  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.07/1.18  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.07/1.18  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.07/1.18  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.07/1.18  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.07/1.18  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.07/1.18  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.07/1.18  tff('#skF_2', type, '#skF_2': $i).
% 2.07/1.18  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.07/1.18  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.07/1.18  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.07/1.18  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.07/1.18  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.07/1.18  tff('#skF_4', type, '#skF_4': $i).
% 2.07/1.18  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 2.07/1.18  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.07/1.18  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.07/1.18  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.07/1.18  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.07/1.18  
% 2.07/1.19  tff(f_37, axiom, (?[A]: v1_xboole_0(A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', rc1_xboole_0)).
% 2.07/1.19  tff(f_35, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 2.07/1.19  tff(f_78, negated_conjecture, ~(![A]: (v1_relat_1(A) => (k9_relat_1(A, k1_xboole_0) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t149_relat_1)).
% 2.07/1.19  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 2.07/1.19  tff(f_73, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k9_relat_1(C, B)) <=> (?[D]: ((r2_hidden(D, k1_relat_1(C)) & r2_hidden(k4_tarski(D, A), C)) & r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t143_relat_1)).
% 2.07/1.19  tff(f_39, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 2.07/1.19  tff(f_62, axiom, (![A, B, C]: ~(r1_xboole_0(k2_tarski(A, B), C) & r2_hidden(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_zfmisc_1)).
% 2.07/1.19  tff(c_8, plain, (v1_xboole_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.07/1.19  tff(c_38, plain, (![A_41]: (k1_xboole_0=A_41 | ~v1_xboole_0(A_41))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.07/1.19  tff(c_42, plain, (k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_8, c_38])).
% 2.07/1.19  tff(c_34, plain, (k9_relat_1('#skF_4', k1_xboole_0)!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.07/1.19  tff(c_45, plain, (k9_relat_1('#skF_4', '#skF_2')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_42, c_42, c_34])).
% 2.07/1.19  tff(c_36, plain, (v1_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.07/1.19  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.07/1.19  tff(c_107, plain, (![A_62, B_63, C_64]: (r2_hidden('#skF_3'(A_62, B_63, C_64), B_63) | ~r2_hidden(A_62, k9_relat_1(C_64, B_63)) | ~v1_relat_1(C_64))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.07/1.19  tff(c_10, plain, (![A_6]: (r1_xboole_0(A_6, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.07/1.19  tff(c_46, plain, (![A_6]: (r1_xboole_0(A_6, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_10])).
% 2.07/1.19  tff(c_76, plain, (![A_51, C_52, B_53]: (~r2_hidden(A_51, C_52) | ~r1_xboole_0(k2_tarski(A_51, B_53), C_52))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.07/1.19  tff(c_81, plain, (![A_51]: (~r2_hidden(A_51, '#skF_2'))), inference(resolution, [status(thm)], [c_46, c_76])).
% 2.07/1.19  tff(c_117, plain, (![A_65, C_66]: (~r2_hidden(A_65, k9_relat_1(C_66, '#skF_2')) | ~v1_relat_1(C_66))), inference(resolution, [status(thm)], [c_107, c_81])).
% 2.07/1.19  tff(c_133, plain, (![C_70]: (~v1_relat_1(C_70) | v1_xboole_0(k9_relat_1(C_70, '#skF_2')))), inference(resolution, [status(thm)], [c_4, c_117])).
% 2.07/1.19  tff(c_6, plain, (![A_5]: (k1_xboole_0=A_5 | ~v1_xboole_0(A_5))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.07/1.19  tff(c_44, plain, (![A_5]: (A_5='#skF_2' | ~v1_xboole_0(A_5))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_6])).
% 2.07/1.19  tff(c_141, plain, (![C_71]: (k9_relat_1(C_71, '#skF_2')='#skF_2' | ~v1_relat_1(C_71))), inference(resolution, [status(thm)], [c_133, c_44])).
% 2.07/1.19  tff(c_144, plain, (k9_relat_1('#skF_4', '#skF_2')='#skF_2'), inference(resolution, [status(thm)], [c_36, c_141])).
% 2.07/1.19  tff(c_148, plain, $false, inference(negUnitSimplification, [status(thm)], [c_45, c_144])).
% 2.07/1.19  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.07/1.19  
% 2.07/1.19  Inference rules
% 2.07/1.19  ----------------------
% 2.07/1.19  #Ref     : 0
% 2.07/1.19  #Sup     : 22
% 2.07/1.19  #Fact    : 0
% 2.07/1.19  #Define  : 0
% 2.07/1.19  #Split   : 0
% 2.07/1.19  #Chain   : 0
% 2.07/1.19  #Close   : 0
% 2.07/1.19  
% 2.07/1.19  Ordering : KBO
% 2.07/1.19  
% 2.07/1.19  Simplification rules
% 2.07/1.19  ----------------------
% 2.07/1.19  #Subsume      : 1
% 2.07/1.19  #Demod        : 5
% 2.07/1.19  #Tautology    : 11
% 2.07/1.19  #SimpNegUnit  : 1
% 2.07/1.19  #BackRed      : 3
% 2.07/1.19  
% 2.07/1.19  #Partial instantiations: 0
% 2.07/1.19  #Strategies tried      : 1
% 2.07/1.19  
% 2.07/1.19  Timing (in seconds)
% 2.07/1.19  ----------------------
% 2.07/1.20  Preprocessing        : 0.31
% 2.07/1.20  Parsing              : 0.16
% 2.07/1.20  CNF conversion       : 0.02
% 2.07/1.20  Main loop            : 0.13
% 2.07/1.20  Inferencing          : 0.05
% 2.07/1.20  Reduction            : 0.04
% 2.07/1.20  Demodulation         : 0.03
% 2.07/1.20  BG Simplification    : 0.01
% 2.07/1.20  Subsumption          : 0.02
% 2.07/1.20  Abstraction          : 0.01
% 2.07/1.20  MUC search           : 0.00
% 2.07/1.20  Cooper               : 0.00
% 2.07/1.20  Total                : 0.47
% 2.07/1.20  Index Insertion      : 0.00
% 2.07/1.20  Index Deletion       : 0.00
% 2.07/1.20  Index Matching       : 0.00
% 2.07/1.20  BG Taut test         : 0.00
%------------------------------------------------------------------------------
