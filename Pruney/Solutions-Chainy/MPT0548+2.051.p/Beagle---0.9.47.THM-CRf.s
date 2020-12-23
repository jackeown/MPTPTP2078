%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:00:42 EST 2020

% Result     : Theorem 2.11s
% Output     : CNFRefutation 2.42s
% Verified   : 
% Statistics : Number of formulae       :   50 (  74 expanded)
%              Number of leaves         :   30 (  39 expanded)
%              Depth                    :    8
%              Number of atoms          :   43 (  80 expanded)
%              Number of equality atoms :   19 (  34 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > v1_relat_1 > k9_relat_1 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k2_relat_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_5 > #skF_1 > #skF_4

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

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_45,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_90,axiom,(
    ! [A] :
      ( v1_relat_1(A)
    <=> ! [B] :
          ~ ( r2_hidden(B,A)
            & ! [C,D] : B != k4_tarski(C,D) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_relat_1)).

tff(f_41,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_43,axiom,(
    ! [A] : k4_xboole_0(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).

tff(f_39,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_98,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k9_relat_1(A,k1_xboole_0) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t149_relat_1)).

tff(f_101,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_94,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k9_relat_1(B,A) = k9_relat_1(B,k3_xboole_0(k1_relat_1(B),A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t145_relat_1)).

tff(f_104,negated_conjecture,(
    ~ ! [A] : k9_relat_1(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t150_relat_1)).

tff(c_10,plain,(
    ! [A_9] : r1_xboole_0(A_9,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_36,plain,(
    ! [A_22] :
      ( r2_hidden('#skF_2'(A_22),A_22)
      | v1_relat_1(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_115,plain,(
    ! [A_59,B_60] : k4_xboole_0(A_59,k4_xboole_0(A_59,B_60)) = k3_xboole_0(A_59,B_60) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_8,plain,(
    ! [A_8] : k4_xboole_0(k1_xboole_0,A_8) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_157,plain,(
    ! [B_64] : k3_xboole_0(k1_xboole_0,B_64) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_115,c_8])).

tff(c_4,plain,(
    ! [A_1,B_2,C_5] :
      ( ~ r1_xboole_0(A_1,B_2)
      | ~ r2_hidden(C_5,k3_xboole_0(A_1,B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_162,plain,(
    ! [B_64,C_5] :
      ( ~ r1_xboole_0(k1_xboole_0,B_64)
      | ~ r2_hidden(C_5,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_157,c_4])).

tff(c_188,plain,(
    ! [C_67] : ~ r2_hidden(C_67,k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_162])).

tff(c_193,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_36,c_188])).

tff(c_40,plain,(
    ! [A_42] :
      ( k9_relat_1(A_42,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(A_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_197,plain,(
    k9_relat_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_193,c_40])).

tff(c_125,plain,(
    ! [B_60] : k3_xboole_0(k1_xboole_0,B_60) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_115,c_8])).

tff(c_44,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_417,plain,(
    ! [B_86,A_87] :
      ( k9_relat_1(B_86,k3_xboole_0(k1_relat_1(B_86),A_87)) = k9_relat_1(B_86,A_87)
      | ~ v1_relat_1(B_86) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_426,plain,(
    ! [A_87] :
      ( k9_relat_1(k1_xboole_0,k3_xboole_0(k1_xboole_0,A_87)) = k9_relat_1(k1_xboole_0,A_87)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_417])).

tff(c_430,plain,(
    ! [A_87] : k9_relat_1(k1_xboole_0,A_87) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_193,c_197,c_125,c_426])).

tff(c_46,plain,(
    k9_relat_1(k1_xboole_0,'#skF_5') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_434,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_430,c_46])).

tff(c_436,plain,(
    ! [B_88] : ~ r1_xboole_0(k1_xboole_0,B_88) ),
    inference(splitRight,[status(thm)],[c_162])).

tff(c_441,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_10,c_436])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:53:47 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.11/1.32  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.42/1.33  
% 2.42/1.33  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.42/1.33  %$ r2_hidden > r1_xboole_0 > v1_relat_1 > k9_relat_1 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k2_relat_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_5 > #skF_1 > #skF_4
% 2.42/1.33  
% 2.42/1.33  %Foreground sorts:
% 2.42/1.33  
% 2.42/1.33  
% 2.42/1.33  %Background operators:
% 2.42/1.33  
% 2.42/1.33  
% 2.42/1.33  %Foreground operators:
% 2.42/1.33  tff('#skF_2', type, '#skF_2': $i > $i).
% 2.42/1.33  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.42/1.33  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.42/1.33  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.42/1.33  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.42/1.33  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.42/1.33  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.42/1.33  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.42/1.33  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.42/1.33  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.42/1.33  tff('#skF_5', type, '#skF_5': $i).
% 2.42/1.33  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.42/1.33  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.42/1.33  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.42/1.33  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.42/1.33  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.42/1.33  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.42/1.33  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.42/1.33  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.42/1.33  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.42/1.33  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 2.42/1.33  
% 2.42/1.34  tff(f_45, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 2.42/1.34  tff(f_90, axiom, (![A]: (v1_relat_1(A) <=> (![B]: ~(r2_hidden(B, A) & (![C, D]: ~(B = k4_tarski(C, D))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_relat_1)).
% 2.42/1.34  tff(f_41, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 2.42/1.34  tff(f_43, axiom, (![A]: (k4_xboole_0(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_boole)).
% 2.42/1.34  tff(f_39, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 2.42/1.34  tff(f_98, axiom, (![A]: (v1_relat_1(A) => (k9_relat_1(A, k1_xboole_0) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t149_relat_1)).
% 2.42/1.34  tff(f_101, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 2.42/1.34  tff(f_94, axiom, (![A, B]: (v1_relat_1(B) => (k9_relat_1(B, A) = k9_relat_1(B, k3_xboole_0(k1_relat_1(B), A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t145_relat_1)).
% 2.42/1.34  tff(f_104, negated_conjecture, ~(![A]: (k9_relat_1(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t150_relat_1)).
% 2.42/1.34  tff(c_10, plain, (![A_9]: (r1_xboole_0(A_9, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.42/1.34  tff(c_36, plain, (![A_22]: (r2_hidden('#skF_2'(A_22), A_22) | v1_relat_1(A_22))), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.42/1.34  tff(c_115, plain, (![A_59, B_60]: (k4_xboole_0(A_59, k4_xboole_0(A_59, B_60))=k3_xboole_0(A_59, B_60))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.42/1.34  tff(c_8, plain, (![A_8]: (k4_xboole_0(k1_xboole_0, A_8)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.42/1.34  tff(c_157, plain, (![B_64]: (k3_xboole_0(k1_xboole_0, B_64)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_115, c_8])).
% 2.42/1.34  tff(c_4, plain, (![A_1, B_2, C_5]: (~r1_xboole_0(A_1, B_2) | ~r2_hidden(C_5, k3_xboole_0(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.42/1.34  tff(c_162, plain, (![B_64, C_5]: (~r1_xboole_0(k1_xboole_0, B_64) | ~r2_hidden(C_5, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_157, c_4])).
% 2.42/1.34  tff(c_188, plain, (![C_67]: (~r2_hidden(C_67, k1_xboole_0))), inference(splitLeft, [status(thm)], [c_162])).
% 2.42/1.34  tff(c_193, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_36, c_188])).
% 2.42/1.34  tff(c_40, plain, (![A_42]: (k9_relat_1(A_42, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(A_42))), inference(cnfTransformation, [status(thm)], [f_98])).
% 2.42/1.34  tff(c_197, plain, (k9_relat_1(k1_xboole_0, k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_193, c_40])).
% 2.42/1.34  tff(c_125, plain, (![B_60]: (k3_xboole_0(k1_xboole_0, B_60)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_115, c_8])).
% 2.42/1.34  tff(c_44, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_101])).
% 2.42/1.34  tff(c_417, plain, (![B_86, A_87]: (k9_relat_1(B_86, k3_xboole_0(k1_relat_1(B_86), A_87))=k9_relat_1(B_86, A_87) | ~v1_relat_1(B_86))), inference(cnfTransformation, [status(thm)], [f_94])).
% 2.42/1.34  tff(c_426, plain, (![A_87]: (k9_relat_1(k1_xboole_0, k3_xboole_0(k1_xboole_0, A_87))=k9_relat_1(k1_xboole_0, A_87) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_44, c_417])).
% 2.42/1.34  tff(c_430, plain, (![A_87]: (k9_relat_1(k1_xboole_0, A_87)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_193, c_197, c_125, c_426])).
% 2.42/1.34  tff(c_46, plain, (k9_relat_1(k1_xboole_0, '#skF_5')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_104])).
% 2.42/1.34  tff(c_434, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_430, c_46])).
% 2.42/1.34  tff(c_436, plain, (![B_88]: (~r1_xboole_0(k1_xboole_0, B_88))), inference(splitRight, [status(thm)], [c_162])).
% 2.42/1.34  tff(c_441, plain, $false, inference(resolution, [status(thm)], [c_10, c_436])).
% 2.42/1.34  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.42/1.34  
% 2.42/1.34  Inference rules
% 2.42/1.34  ----------------------
% 2.42/1.34  #Ref     : 0
% 2.42/1.34  #Sup     : 97
% 2.42/1.34  #Fact    : 0
% 2.42/1.34  #Define  : 0
% 2.42/1.34  #Split   : 1
% 2.42/1.34  #Chain   : 0
% 2.42/1.34  #Close   : 0
% 2.42/1.34  
% 2.42/1.34  Ordering : KBO
% 2.42/1.34  
% 2.42/1.34  Simplification rules
% 2.42/1.34  ----------------------
% 2.42/1.34  #Subsume      : 2
% 2.42/1.34  #Demod        : 36
% 2.42/1.34  #Tautology    : 67
% 2.42/1.34  #SimpNegUnit  : 4
% 2.42/1.34  #BackRed      : 1
% 2.42/1.34  
% 2.42/1.34  #Partial instantiations: 0
% 2.42/1.34  #Strategies tried      : 1
% 2.42/1.34  
% 2.42/1.34  Timing (in seconds)
% 2.42/1.34  ----------------------
% 2.42/1.34  Preprocessing        : 0.32
% 2.42/1.34  Parsing              : 0.17
% 2.42/1.34  CNF conversion       : 0.02
% 2.42/1.34  Main loop            : 0.22
% 2.42/1.34  Inferencing          : 0.08
% 2.42/1.34  Reduction            : 0.07
% 2.42/1.34  Demodulation         : 0.05
% 2.42/1.34  BG Simplification    : 0.01
% 2.42/1.34  Subsumption          : 0.03
% 2.42/1.34  Abstraction          : 0.01
% 2.42/1.34  MUC search           : 0.00
% 2.42/1.34  Cooper               : 0.00
% 2.42/1.34  Total                : 0.57
% 2.42/1.34  Index Insertion      : 0.00
% 2.42/1.34  Index Deletion       : 0.00
% 2.42/1.34  Index Matching       : 0.00
% 2.42/1.35  BG Taut test         : 0.00
%------------------------------------------------------------------------------
