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
% DateTime   : Thu Dec  3 10:02:24 EST 2020

% Result     : Theorem 2.23s
% Output     : CNFRefutation 2.23s
% Verified   : 
% Statistics : Number of formulae       :   48 (  59 expanded)
%              Number of leaves         :   30 (  36 expanded)
%              Depth                    :    6
%              Number of atoms          :   51 (  73 expanded)
%              Number of equality atoms :   13 (  19 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > v1_xboole_0 > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k7_relat_1 > k3_xboole_0 > k2_tarski > #nlpp > k1_setfam_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_87,negated_conjecture,(
    ~ ! [A,B,C] :
        ( v1_relat_1(C)
       => ( r1_xboole_0(A,B)
         => k7_relat_1(k7_relat_1(C,A),B) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t207_relat_1)).

tff(f_32,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_76,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(A)
        & v1_xboole_0(B) )
     => ( v1_xboole_0(k7_relat_1(A,B))
        & v1_relat_1(k7_relat_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc16_relat_1)).

tff(f_54,axiom,(
    ! [A,B] :
      ~ ( v1_xboole_0(A)
        & A != B
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_boole)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_46,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_80,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k7_relat_1(k7_relat_1(C,A),B) = k7_relat_1(C,k3_xboole_0(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_relat_1)).

tff(c_38,plain,(
    v1_relat_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_6,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_114,plain,(
    ! [A_66,B_67] :
      ( v1_xboole_0(k7_relat_1(A_66,B_67))
      | ~ v1_xboole_0(B_67)
      | ~ v1_relat_1(A_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_45,plain,(
    ! [B_49,A_50] :
      ( ~ v1_xboole_0(B_49)
      | B_49 = A_50
      | ~ v1_xboole_0(A_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_48,plain,(
    ! [A_50] :
      ( k1_xboole_0 = A_50
      | ~ v1_xboole_0(A_50) ) ),
    inference(resolution,[status(thm)],[c_6,c_45])).

tff(c_122,plain,(
    ! [A_68,B_69] :
      ( k7_relat_1(A_68,B_69) = k1_xboole_0
      | ~ v1_xboole_0(B_69)
      | ~ v1_relat_1(A_68) ) ),
    inference(resolution,[status(thm)],[c_114,c_48])).

tff(c_132,plain,(
    ! [A_70] :
      ( k7_relat_1(A_70,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(A_70) ) ),
    inference(resolution,[status(thm)],[c_6,c_122])).

tff(c_140,plain,(
    k7_relat_1('#skF_5',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_38,c_132])).

tff(c_36,plain,(
    r1_xboole_0('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_73,plain,(
    ! [A_56,B_57,C_58] :
      ( ~ r1_xboole_0(A_56,B_57)
      | ~ r2_hidden(C_58,k3_xboole_0(A_56,B_57)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_79,plain,(
    ! [A_59,B_60] :
      ( ~ r1_xboole_0(A_59,B_60)
      | v1_xboole_0(k3_xboole_0(A_59,B_60)) ) ),
    inference(resolution,[status(thm)],[c_4,c_73])).

tff(c_87,plain,(
    ! [A_61,B_62] :
      ( k3_xboole_0(A_61,B_62) = k1_xboole_0
      | ~ r1_xboole_0(A_61,B_62) ) ),
    inference(resolution,[status(thm)],[c_79,c_48])).

tff(c_91,plain,(
    k3_xboole_0('#skF_3','#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_36,c_87])).

tff(c_274,plain,(
    ! [C_90,A_91,B_92] :
      ( k7_relat_1(k7_relat_1(C_90,A_91),B_92) = k7_relat_1(C_90,k3_xboole_0(A_91,B_92))
      | ~ v1_relat_1(C_90) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_34,plain,(
    k7_relat_1(k7_relat_1('#skF_5','#skF_3'),'#skF_4') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_296,plain,
    ( k7_relat_1('#skF_5',k3_xboole_0('#skF_3','#skF_4')) != k1_xboole_0
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_274,c_34])).

tff(c_318,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_140,c_91,c_296])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:15:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.23/1.31  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.23/1.32  
% 2.23/1.32  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.23/1.32  %$ r2_hidden > r1_xboole_0 > v1_xboole_0 > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k7_relat_1 > k3_xboole_0 > k2_tarski > #nlpp > k1_setfam_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2
% 2.23/1.32  
% 2.23/1.32  %Foreground sorts:
% 2.23/1.32  
% 2.23/1.32  
% 2.23/1.32  %Background operators:
% 2.23/1.32  
% 2.23/1.32  
% 2.23/1.32  %Foreground operators:
% 2.23/1.32  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.23/1.32  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.23/1.32  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.23/1.32  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.23/1.32  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.23/1.32  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.23/1.32  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.23/1.32  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.23/1.32  tff('#skF_5', type, '#skF_5': $i).
% 2.23/1.32  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.23/1.32  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.23/1.32  tff('#skF_3', type, '#skF_3': $i).
% 2.23/1.32  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.23/1.32  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.23/1.32  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.23/1.32  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.23/1.32  tff('#skF_4', type, '#skF_4': $i).
% 2.23/1.32  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.23/1.32  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.23/1.32  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.23/1.32  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.23/1.32  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.23/1.32  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.23/1.32  
% 2.23/1.33  tff(f_87, negated_conjecture, ~(![A, B, C]: (v1_relat_1(C) => (r1_xboole_0(A, B) => (k7_relat_1(k7_relat_1(C, A), B) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t207_relat_1)).
% 2.23/1.33  tff(f_32, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.23/1.33  tff(f_76, axiom, (![A, B]: ((v1_relat_1(A) & v1_xboole_0(B)) => (v1_xboole_0(k7_relat_1(A, B)) & v1_relat_1(k7_relat_1(A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc16_relat_1)).
% 2.23/1.33  tff(f_54, axiom, (![A, B]: ~((v1_xboole_0(A) & ~(A = B)) & v1_xboole_0(B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_boole)).
% 2.23/1.33  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 2.23/1.33  tff(f_46, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 2.23/1.33  tff(f_80, axiom, (![A, B, C]: (v1_relat_1(C) => (k7_relat_1(k7_relat_1(C, A), B) = k7_relat_1(C, k3_xboole_0(A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_relat_1)).
% 2.23/1.33  tff(c_38, plain, (v1_relat_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.23/1.33  tff(c_6, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.23/1.33  tff(c_114, plain, (![A_66, B_67]: (v1_xboole_0(k7_relat_1(A_66, B_67)) | ~v1_xboole_0(B_67) | ~v1_relat_1(A_66))), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.23/1.33  tff(c_45, plain, (![B_49, A_50]: (~v1_xboole_0(B_49) | B_49=A_50 | ~v1_xboole_0(A_50))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.23/1.33  tff(c_48, plain, (![A_50]: (k1_xboole_0=A_50 | ~v1_xboole_0(A_50))), inference(resolution, [status(thm)], [c_6, c_45])).
% 2.23/1.33  tff(c_122, plain, (![A_68, B_69]: (k7_relat_1(A_68, B_69)=k1_xboole_0 | ~v1_xboole_0(B_69) | ~v1_relat_1(A_68))), inference(resolution, [status(thm)], [c_114, c_48])).
% 2.23/1.33  tff(c_132, plain, (![A_70]: (k7_relat_1(A_70, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(A_70))), inference(resolution, [status(thm)], [c_6, c_122])).
% 2.23/1.33  tff(c_140, plain, (k7_relat_1('#skF_5', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_38, c_132])).
% 2.23/1.33  tff(c_36, plain, (r1_xboole_0('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.23/1.33  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.23/1.33  tff(c_73, plain, (![A_56, B_57, C_58]: (~r1_xboole_0(A_56, B_57) | ~r2_hidden(C_58, k3_xboole_0(A_56, B_57)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.23/1.33  tff(c_79, plain, (![A_59, B_60]: (~r1_xboole_0(A_59, B_60) | v1_xboole_0(k3_xboole_0(A_59, B_60)))), inference(resolution, [status(thm)], [c_4, c_73])).
% 2.23/1.33  tff(c_87, plain, (![A_61, B_62]: (k3_xboole_0(A_61, B_62)=k1_xboole_0 | ~r1_xboole_0(A_61, B_62))), inference(resolution, [status(thm)], [c_79, c_48])).
% 2.23/1.33  tff(c_91, plain, (k3_xboole_0('#skF_3', '#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_36, c_87])).
% 2.23/1.33  tff(c_274, plain, (![C_90, A_91, B_92]: (k7_relat_1(k7_relat_1(C_90, A_91), B_92)=k7_relat_1(C_90, k3_xboole_0(A_91, B_92)) | ~v1_relat_1(C_90))), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.23/1.33  tff(c_34, plain, (k7_relat_1(k7_relat_1('#skF_5', '#skF_3'), '#skF_4')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.23/1.33  tff(c_296, plain, (k7_relat_1('#skF_5', k3_xboole_0('#skF_3', '#skF_4'))!=k1_xboole_0 | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_274, c_34])).
% 2.23/1.33  tff(c_318, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_38, c_140, c_91, c_296])).
% 2.23/1.33  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.23/1.33  
% 2.23/1.33  Inference rules
% 2.23/1.33  ----------------------
% 2.23/1.33  #Ref     : 0
% 2.23/1.33  #Sup     : 68
% 2.23/1.33  #Fact    : 0
% 2.23/1.33  #Define  : 0
% 2.23/1.33  #Split   : 0
% 2.23/1.33  #Chain   : 0
% 2.23/1.33  #Close   : 0
% 2.23/1.33  
% 2.23/1.33  Ordering : KBO
% 2.23/1.33  
% 2.23/1.33  Simplification rules
% 2.23/1.33  ----------------------
% 2.23/1.33  #Subsume      : 2
% 2.23/1.33  #Demod        : 35
% 2.23/1.33  #Tautology    : 34
% 2.23/1.33  #SimpNegUnit  : 1
% 2.23/1.33  #BackRed      : 0
% 2.23/1.33  
% 2.23/1.33  #Partial instantiations: 0
% 2.23/1.33  #Strategies tried      : 1
% 2.23/1.33  
% 2.23/1.33  Timing (in seconds)
% 2.23/1.33  ----------------------
% 2.23/1.33  Preprocessing        : 0.34
% 2.23/1.33  Parsing              : 0.18
% 2.23/1.33  CNF conversion       : 0.03
% 2.23/1.33  Main loop            : 0.19
% 2.23/1.33  Inferencing          : 0.08
% 2.23/1.33  Reduction            : 0.05
% 2.23/1.33  Demodulation         : 0.04
% 2.23/1.33  BG Simplification    : 0.02
% 2.23/1.33  Subsumption          : 0.03
% 2.23/1.33  Abstraction          : 0.01
% 2.23/1.33  MUC search           : 0.00
% 2.23/1.33  Cooper               : 0.00
% 2.23/1.33  Total                : 0.56
% 2.23/1.33  Index Insertion      : 0.00
% 2.23/1.33  Index Deletion       : 0.00
% 2.23/1.33  Index Matching       : 0.00
% 2.23/1.33  BG Taut test         : 0.00
%------------------------------------------------------------------------------
