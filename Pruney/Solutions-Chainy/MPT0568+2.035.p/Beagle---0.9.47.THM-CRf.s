%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:01:25 EST 2020

% Result     : Theorem 1.88s
% Output     : CNFRefutation 2.05s
% Verified   : 
% Statistics : Number of formulae       :   58 (  68 expanded)
%              Number of leaves         :   37 (  41 expanded)
%              Depth                    :    9
%              Number of atoms          :   48 (  60 expanded)
%              Number of equality atoms :   19 (  28 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_relat_1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k2_relat_1 > k1_tarski > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_5 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_2',type,(
    '#skF_2': $i > $i )).

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

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_44,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_34,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_42,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_63,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k4_xboole_0(B,k1_tarski(C)))
    <=> ( r2_hidden(A,B)
        & A != C ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_zfmisc_1)).

tff(f_75,axiom,(
    ! [A] :
      ( v1_relat_1(A)
    <=> ! [B] :
          ~ ( r2_hidden(B,A)
            & ! [C,D] : B != k4_tarski(C,D) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_relat_1)).

tff(f_82,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_79,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k10_relat_1(B,A),k1_relat_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t167_relat_1)).

tff(f_40,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_85,negated_conjecture,(
    ~ ! [A] : k10_relat_1(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t172_relat_1)).

tff(c_165,plain,(
    ! [A_82,B_83] :
      ( r2_hidden('#skF_1'(A_82,B_83),A_82)
      | r1_tarski(A_82,B_83) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_18,plain,(
    ! [A_12] : k5_xboole_0(A_12,A_12) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_8,plain,(
    ! [A_6] : k3_xboole_0(A_6,A_6) = A_6 ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_136,plain,(
    ! [A_78,B_79] : k5_xboole_0(A_78,k3_xboole_0(A_78,B_79)) = k4_xboole_0(A_78,B_79) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_145,plain,(
    ! [A_6] : k5_xboole_0(A_6,A_6) = k4_xboole_0(A_6,A_6) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_136])).

tff(c_149,plain,(
    ! [A_80] : k4_xboole_0(A_80,A_80) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_145])).

tff(c_34,plain,(
    ! [C_36,B_35] : ~ r2_hidden(C_36,k4_xboole_0(B_35,k1_tarski(C_36))) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_154,plain,(
    ! [C_36] : ~ r2_hidden(C_36,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_149,c_34])).

tff(c_170,plain,(
    ! [B_83] : r1_tarski(k1_xboole_0,B_83) ),
    inference(resolution,[status(thm)],[c_165,c_154])).

tff(c_44,plain,(
    ! [A_39] :
      ( r2_hidden('#skF_2'(A_39),A_39)
      | v1_relat_1(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_159,plain,(
    ! [C_81] : ~ r2_hidden(C_81,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_149,c_34])).

tff(c_164,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_44,c_159])).

tff(c_50,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_129,plain,(
    ! [B_76,A_77] :
      ( r1_tarski(k10_relat_1(B_76,A_77),k1_relat_1(B_76))
      | ~ v1_relat_1(B_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_134,plain,(
    ! [A_77] :
      ( r1_tarski(k10_relat_1(k1_xboole_0,A_77),k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_129])).

tff(c_190,plain,(
    ! [A_86] : r1_tarski(k10_relat_1(k1_xboole_0,A_86),k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_164,c_134])).

tff(c_10,plain,(
    ! [B_9,A_8] :
      ( B_9 = A_8
      | ~ r1_tarski(B_9,A_8)
      | ~ r1_tarski(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_195,plain,(
    ! [A_86] :
      ( k10_relat_1(k1_xboole_0,A_86) = k1_xboole_0
      | ~ r1_tarski(k1_xboole_0,k10_relat_1(k1_xboole_0,A_86)) ) ),
    inference(resolution,[status(thm)],[c_190,c_10])).

tff(c_199,plain,(
    ! [A_86] : k10_relat_1(k1_xboole_0,A_86) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_170,c_195])).

tff(c_52,plain,(
    k10_relat_1(k1_xboole_0,'#skF_5') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_204,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_199,c_52])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:41:49 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.88/1.22  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.88/1.22  
% 1.88/1.22  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.88/1.23  %$ r2_hidden > r1_tarski > v1_relat_1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k2_relat_1 > k1_tarski > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_5 > #skF_1 > #skF_4
% 1.88/1.23  
% 1.88/1.23  %Foreground sorts:
% 1.88/1.23  
% 1.88/1.23  
% 1.88/1.23  %Background operators:
% 1.88/1.23  
% 1.88/1.23  
% 1.88/1.23  %Foreground operators:
% 1.88/1.23  tff('#skF_2', type, '#skF_2': $i > $i).
% 1.88/1.23  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.88/1.23  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.88/1.23  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.88/1.23  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.88/1.23  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 1.88/1.23  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.88/1.23  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 1.88/1.23  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 1.88/1.23  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 1.88/1.23  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.88/1.23  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.88/1.23  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.88/1.23  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.88/1.23  tff('#skF_5', type, '#skF_5': $i).
% 1.88/1.23  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.88/1.23  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 1.88/1.23  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.88/1.23  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 1.88/1.23  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.88/1.23  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.88/1.23  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.88/1.23  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 1.88/1.23  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.88/1.23  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.88/1.23  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 1.88/1.23  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 1.88/1.23  
% 2.02/1.24  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 2.02/1.24  tff(f_44, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t92_xboole_1)).
% 2.02/1.24  tff(f_34, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 2.02/1.24  tff(f_42, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 2.02/1.24  tff(f_63, axiom, (![A, B, C]: (r2_hidden(A, k4_xboole_0(B, k1_tarski(C))) <=> (r2_hidden(A, B) & ~(A = C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_zfmisc_1)).
% 2.02/1.24  tff(f_75, axiom, (![A]: (v1_relat_1(A) <=> (![B]: ~(r2_hidden(B, A) & (![C, D]: ~(B = k4_tarski(C, D))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_relat_1)).
% 2.02/1.24  tff(f_82, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 2.05/1.24  tff(f_79, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k10_relat_1(B, A), k1_relat_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t167_relat_1)).
% 2.05/1.24  tff(f_40, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.05/1.24  tff(f_85, negated_conjecture, ~(![A]: (k10_relat_1(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t172_relat_1)).
% 2.05/1.24  tff(c_165, plain, (![A_82, B_83]: (r2_hidden('#skF_1'(A_82, B_83), A_82) | r1_tarski(A_82, B_83))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.05/1.24  tff(c_18, plain, (![A_12]: (k5_xboole_0(A_12, A_12)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.05/1.24  tff(c_8, plain, (![A_6]: (k3_xboole_0(A_6, A_6)=A_6)), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.05/1.24  tff(c_136, plain, (![A_78, B_79]: (k5_xboole_0(A_78, k3_xboole_0(A_78, B_79))=k4_xboole_0(A_78, B_79))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.05/1.24  tff(c_145, plain, (![A_6]: (k5_xboole_0(A_6, A_6)=k4_xboole_0(A_6, A_6))), inference(superposition, [status(thm), theory('equality')], [c_8, c_136])).
% 2.05/1.24  tff(c_149, plain, (![A_80]: (k4_xboole_0(A_80, A_80)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_18, c_145])).
% 2.05/1.24  tff(c_34, plain, (![C_36, B_35]: (~r2_hidden(C_36, k4_xboole_0(B_35, k1_tarski(C_36))))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.05/1.24  tff(c_154, plain, (![C_36]: (~r2_hidden(C_36, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_149, c_34])).
% 2.05/1.24  tff(c_170, plain, (![B_83]: (r1_tarski(k1_xboole_0, B_83))), inference(resolution, [status(thm)], [c_165, c_154])).
% 2.05/1.24  tff(c_44, plain, (![A_39]: (r2_hidden('#skF_2'(A_39), A_39) | v1_relat_1(A_39))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.05/1.24  tff(c_159, plain, (![C_81]: (~r2_hidden(C_81, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_149, c_34])).
% 2.05/1.24  tff(c_164, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_44, c_159])).
% 2.05/1.24  tff(c_50, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.05/1.24  tff(c_129, plain, (![B_76, A_77]: (r1_tarski(k10_relat_1(B_76, A_77), k1_relat_1(B_76)) | ~v1_relat_1(B_76))), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.05/1.24  tff(c_134, plain, (![A_77]: (r1_tarski(k10_relat_1(k1_xboole_0, A_77), k1_xboole_0) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_50, c_129])).
% 2.05/1.24  tff(c_190, plain, (![A_86]: (r1_tarski(k10_relat_1(k1_xboole_0, A_86), k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_164, c_134])).
% 2.05/1.24  tff(c_10, plain, (![B_9, A_8]: (B_9=A_8 | ~r1_tarski(B_9, A_8) | ~r1_tarski(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.05/1.24  tff(c_195, plain, (![A_86]: (k10_relat_1(k1_xboole_0, A_86)=k1_xboole_0 | ~r1_tarski(k1_xboole_0, k10_relat_1(k1_xboole_0, A_86)))), inference(resolution, [status(thm)], [c_190, c_10])).
% 2.05/1.24  tff(c_199, plain, (![A_86]: (k10_relat_1(k1_xboole_0, A_86)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_170, c_195])).
% 2.05/1.24  tff(c_52, plain, (k10_relat_1(k1_xboole_0, '#skF_5')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.05/1.24  tff(c_204, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_199, c_52])).
% 2.05/1.24  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.05/1.24  
% 2.05/1.24  Inference rules
% 2.05/1.24  ----------------------
% 2.05/1.24  #Ref     : 0
% 2.05/1.24  #Sup     : 33
% 2.05/1.24  #Fact    : 0
% 2.05/1.24  #Define  : 0
% 2.05/1.24  #Split   : 0
% 2.05/1.24  #Chain   : 0
% 2.05/1.24  #Close   : 0
% 2.05/1.24  
% 2.05/1.24  Ordering : KBO
% 2.05/1.24  
% 2.05/1.24  Simplification rules
% 2.05/1.24  ----------------------
% 2.05/1.24  #Subsume      : 0
% 2.05/1.24  #Demod        : 9
% 2.05/1.24  #Tautology    : 25
% 2.05/1.24  #SimpNegUnit  : 0
% 2.05/1.24  #BackRed      : 2
% 2.05/1.24  
% 2.05/1.24  #Partial instantiations: 0
% 2.05/1.24  #Strategies tried      : 1
% 2.05/1.24  
% 2.05/1.24  Timing (in seconds)
% 2.05/1.24  ----------------------
% 2.05/1.24  Preprocessing        : 0.32
% 2.05/1.24  Parsing              : 0.17
% 2.05/1.24  CNF conversion       : 0.02
% 2.05/1.24  Main loop            : 0.13
% 2.05/1.24  Inferencing          : 0.05
% 2.05/1.24  Reduction            : 0.04
% 2.05/1.24  Demodulation         : 0.03
% 2.05/1.24  BG Simplification    : 0.01
% 2.05/1.24  Subsumption          : 0.02
% 2.05/1.24  Abstraction          : 0.01
% 2.05/1.24  MUC search           : 0.00
% 2.05/1.24  Cooper               : 0.00
% 2.05/1.24  Total                : 0.48
% 2.05/1.24  Index Insertion      : 0.00
% 2.05/1.24  Index Deletion       : 0.00
% 2.05/1.24  Index Matching       : 0.00
% 2.05/1.24  BG Taut test         : 0.00
%------------------------------------------------------------------------------
