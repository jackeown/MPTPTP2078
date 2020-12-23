%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:02:25 EST 2020

% Result     : Theorem 2.08s
% Output     : CNFRefutation 2.08s
% Verified   : 
% Statistics : Number of formulae       :   48 (  71 expanded)
%              Number of leaves         :   29 (  40 expanded)
%              Depth                    :    9
%              Number of atoms          :   50 ( 101 expanded)
%              Number of equality atoms :   12 (  23 expanded)
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

tff(f_82,negated_conjecture,(
    ~ ! [A,B,C] :
        ( v1_relat_1(C)
       => ( r1_xboole_0(A,B)
         => k7_relat_1(k7_relat_1(C,A),B) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t207_relat_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_49,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_35,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_71,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(A)
        & v1_xboole_0(B) )
     => ( v1_xboole_0(k7_relat_1(A,B))
        & v1_relat_1(k7_relat_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc16_relat_1)).

tff(f_75,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k7_relat_1(k7_relat_1(C,A),B) = k7_relat_1(C,k3_xboole_0(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_relat_1)).

tff(c_36,plain,(
    v1_relat_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_34,plain,(
    r1_xboole_0('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_68,plain,(
    ! [A_57,B_58,C_59] :
      ( ~ r1_xboole_0(A_57,B_58)
      | ~ r2_hidden(C_59,k3_xboole_0(A_57,B_58)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_74,plain,(
    ! [A_60,B_61] :
      ( ~ r1_xboole_0(A_60,B_61)
      | v1_xboole_0(k3_xboole_0(A_60,B_61)) ) ),
    inference(resolution,[status(thm)],[c_4,c_68])).

tff(c_6,plain,(
    ! [A_5] :
      ( k1_xboole_0 = A_5
      | ~ v1_xboole_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_79,plain,(
    ! [A_62,B_63] :
      ( k3_xboole_0(A_62,B_63) = k1_xboole_0
      | ~ r1_xboole_0(A_62,B_63) ) ),
    inference(resolution,[status(thm)],[c_74,c_6])).

tff(c_83,plain,(
    k3_xboole_0('#skF_3','#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_34,c_79])).

tff(c_73,plain,(
    ! [A_57,B_58] :
      ( ~ r1_xboole_0(A_57,B_58)
      | v1_xboole_0(k3_xboole_0(A_57,B_58)) ) ),
    inference(resolution,[status(thm)],[c_4,c_68])).

tff(c_87,plain,
    ( ~ r1_xboole_0('#skF_3','#skF_4')
    | v1_xboole_0(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_83,c_73])).

tff(c_94,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_87])).

tff(c_62,plain,(
    ! [A_53,B_54] :
      ( v1_xboole_0(k7_relat_1(A_53,B_54))
      | ~ v1_xboole_0(B_54)
      | ~ v1_relat_1(A_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_119,plain,(
    ! [A_68,B_69] :
      ( k7_relat_1(A_68,B_69) = k1_xboole_0
      | ~ v1_xboole_0(B_69)
      | ~ v1_relat_1(A_68) ) ),
    inference(resolution,[status(thm)],[c_62,c_6])).

tff(c_129,plain,(
    ! [A_70] :
      ( k7_relat_1(A_70,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(A_70) ) ),
    inference(resolution,[status(thm)],[c_94,c_119])).

tff(c_137,plain,(
    k7_relat_1('#skF_5',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_36,c_129])).

tff(c_268,plain,(
    ! [C_84,A_85,B_86] :
      ( k7_relat_1(k7_relat_1(C_84,A_85),B_86) = k7_relat_1(C_84,k3_xboole_0(A_85,B_86))
      | ~ v1_relat_1(C_84) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_32,plain,(
    k7_relat_1(k7_relat_1('#skF_5','#skF_3'),'#skF_4') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_294,plain,
    ( k7_relat_1('#skF_5',k3_xboole_0('#skF_3','#skF_4')) != k1_xboole_0
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_268,c_32])).

tff(c_323,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_137,c_83,c_294])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n008.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 17:46:15 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.08/1.31  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.08/1.32  
% 2.08/1.32  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.08/1.32  %$ r2_hidden > r1_xboole_0 > v1_xboole_0 > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k7_relat_1 > k3_xboole_0 > k2_tarski > #nlpp > k1_setfam_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2
% 2.08/1.32  
% 2.08/1.32  %Foreground sorts:
% 2.08/1.32  
% 2.08/1.32  
% 2.08/1.32  %Background operators:
% 2.08/1.32  
% 2.08/1.32  
% 2.08/1.32  %Foreground operators:
% 2.08/1.32  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.08/1.32  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.08/1.32  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.08/1.32  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.08/1.32  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.08/1.32  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.08/1.32  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.08/1.32  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.08/1.32  tff('#skF_5', type, '#skF_5': $i).
% 2.08/1.32  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.08/1.32  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.08/1.32  tff('#skF_3', type, '#skF_3': $i).
% 2.08/1.32  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.08/1.32  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.08/1.32  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.08/1.32  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.08/1.32  tff('#skF_4', type, '#skF_4': $i).
% 2.08/1.32  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.08/1.32  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.08/1.32  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.08/1.32  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.08/1.32  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.08/1.32  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.08/1.32  
% 2.08/1.33  tff(f_82, negated_conjecture, ~(![A, B, C]: (v1_relat_1(C) => (r1_xboole_0(A, B) => (k7_relat_1(k7_relat_1(C, A), B) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t207_relat_1)).
% 2.08/1.33  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 2.08/1.33  tff(f_49, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 2.08/1.33  tff(f_35, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 2.08/1.33  tff(f_71, axiom, (![A, B]: ((v1_relat_1(A) & v1_xboole_0(B)) => (v1_xboole_0(k7_relat_1(A, B)) & v1_relat_1(k7_relat_1(A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc16_relat_1)).
% 2.08/1.33  tff(f_75, axiom, (![A, B, C]: (v1_relat_1(C) => (k7_relat_1(k7_relat_1(C, A), B) = k7_relat_1(C, k3_xboole_0(A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_relat_1)).
% 2.08/1.33  tff(c_36, plain, (v1_relat_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.08/1.33  tff(c_34, plain, (r1_xboole_0('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.08/1.33  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.08/1.33  tff(c_68, plain, (![A_57, B_58, C_59]: (~r1_xboole_0(A_57, B_58) | ~r2_hidden(C_59, k3_xboole_0(A_57, B_58)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.08/1.33  tff(c_74, plain, (![A_60, B_61]: (~r1_xboole_0(A_60, B_61) | v1_xboole_0(k3_xboole_0(A_60, B_61)))), inference(resolution, [status(thm)], [c_4, c_68])).
% 2.08/1.33  tff(c_6, plain, (![A_5]: (k1_xboole_0=A_5 | ~v1_xboole_0(A_5))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.08/1.33  tff(c_79, plain, (![A_62, B_63]: (k3_xboole_0(A_62, B_63)=k1_xboole_0 | ~r1_xboole_0(A_62, B_63))), inference(resolution, [status(thm)], [c_74, c_6])).
% 2.08/1.33  tff(c_83, plain, (k3_xboole_0('#skF_3', '#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_34, c_79])).
% 2.08/1.33  tff(c_73, plain, (![A_57, B_58]: (~r1_xboole_0(A_57, B_58) | v1_xboole_0(k3_xboole_0(A_57, B_58)))), inference(resolution, [status(thm)], [c_4, c_68])).
% 2.08/1.33  tff(c_87, plain, (~r1_xboole_0('#skF_3', '#skF_4') | v1_xboole_0(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_83, c_73])).
% 2.08/1.33  tff(c_94, plain, (v1_xboole_0(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_34, c_87])).
% 2.08/1.33  tff(c_62, plain, (![A_53, B_54]: (v1_xboole_0(k7_relat_1(A_53, B_54)) | ~v1_xboole_0(B_54) | ~v1_relat_1(A_53))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.08/1.33  tff(c_119, plain, (![A_68, B_69]: (k7_relat_1(A_68, B_69)=k1_xboole_0 | ~v1_xboole_0(B_69) | ~v1_relat_1(A_68))), inference(resolution, [status(thm)], [c_62, c_6])).
% 2.08/1.33  tff(c_129, plain, (![A_70]: (k7_relat_1(A_70, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(A_70))), inference(resolution, [status(thm)], [c_94, c_119])).
% 2.08/1.33  tff(c_137, plain, (k7_relat_1('#skF_5', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_36, c_129])).
% 2.08/1.33  tff(c_268, plain, (![C_84, A_85, B_86]: (k7_relat_1(k7_relat_1(C_84, A_85), B_86)=k7_relat_1(C_84, k3_xboole_0(A_85, B_86)) | ~v1_relat_1(C_84))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.08/1.33  tff(c_32, plain, (k7_relat_1(k7_relat_1('#skF_5', '#skF_3'), '#skF_4')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.08/1.33  tff(c_294, plain, (k7_relat_1('#skF_5', k3_xboole_0('#skF_3', '#skF_4'))!=k1_xboole_0 | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_268, c_32])).
% 2.08/1.33  tff(c_323, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_36, c_137, c_83, c_294])).
% 2.08/1.33  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.08/1.33  
% 2.08/1.33  Inference rules
% 2.08/1.33  ----------------------
% 2.08/1.33  #Ref     : 0
% 2.08/1.33  #Sup     : 68
% 2.08/1.33  #Fact    : 0
% 2.08/1.33  #Define  : 0
% 2.08/1.33  #Split   : 0
% 2.08/1.33  #Chain   : 0
% 2.08/1.33  #Close   : 0
% 2.08/1.33  
% 2.08/1.33  Ordering : KBO
% 2.08/1.33  
% 2.08/1.33  Simplification rules
% 2.08/1.33  ----------------------
% 2.08/1.33  #Subsume      : 1
% 2.08/1.33  #Demod        : 38
% 2.08/1.33  #Tautology    : 38
% 2.08/1.33  #SimpNegUnit  : 1
% 2.08/1.33  #BackRed      : 0
% 2.08/1.33  
% 2.08/1.33  #Partial instantiations: 0
% 2.08/1.33  #Strategies tried      : 1
% 2.08/1.33  
% 2.08/1.33  Timing (in seconds)
% 2.08/1.33  ----------------------
% 2.08/1.33  Preprocessing        : 0.30
% 2.08/1.33  Parsing              : 0.16
% 2.08/1.33  CNF conversion       : 0.02
% 2.08/1.33  Main loop            : 0.25
% 2.08/1.33  Inferencing          : 0.10
% 2.08/1.33  Reduction            : 0.07
% 2.08/1.33  Demodulation         : 0.05
% 2.08/1.33  BG Simplification    : 0.01
% 2.08/1.34  Subsumption          : 0.04
% 2.08/1.34  Abstraction          : 0.02
% 2.08/1.34  MUC search           : 0.00
% 2.08/1.34  Cooper               : 0.00
% 2.08/1.34  Total                : 0.58
% 2.08/1.34  Index Insertion      : 0.00
% 2.08/1.34  Index Deletion       : 0.00
% 2.08/1.34  Index Matching       : 0.00
% 2.08/1.34  BG Taut test         : 0.00
%------------------------------------------------------------------------------
