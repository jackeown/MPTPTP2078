%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:01:27 EST 2020

% Result     : Theorem 2.41s
% Output     : CNFRefutation 2.84s
% Verified   : 
% Statistics : Number of formulae       :   49 ( 110 expanded)
%              Number of leaves         :   29 (  53 expanded)
%              Depth                    :    8
%              Number of atoms          :   44 ( 160 expanded)
%              Number of equality atoms :   15 (  57 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v1_relat_1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k4_tarski > k2_tarski > k10_relat_1 > #nlpp > k1_tarski > k1_xboole_0 > #skF_5 > #skF_6 > #skF_1 > #skF_2 > #skF_4 > #skF_8 > #skF_3 > #skF_7

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_5',type,(
    '#skF_5': $i > $i )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

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

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(f_67,axiom,(
    ! [A] :
      ( v1_relat_1(A)
    <=> ! [B] :
          ~ ( r2_hidden(B,A)
            & ! [C,D] : B != k4_tarski(C,D) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_relat_1)).

tff(f_27,axiom,(
    ! [A] : k4_xboole_0(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).

tff(f_44,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,k1_tarski(B)) = A
    <=> ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_zfmisc_1)).

tff(f_57,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B,C] :
          ( C = k10_relat_1(A,B)
        <=> ! [D] :
              ( r2_hidden(D,C)
            <=> ? [E] :
                  ( r2_hidden(k4_tarski(D,E),A)
                  & r2_hidden(E,B) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d14_relat_1)).

tff(f_70,negated_conjecture,(
    ~ ! [A] : k10_relat_1(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t172_relat_1)).

tff(c_42,plain,(
    ! [A_67] :
      ( r2_hidden('#skF_5'(A_67),A_67)
      | v1_relat_1(A_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_2,plain,(
    ! [A_1] : k4_xboole_0(k1_xboole_0,A_1) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_72,plain,(
    ! [B_93,A_94] :
      ( ~ r2_hidden(B_93,A_94)
      | k4_xboole_0(A_94,k1_tarski(B_93)) != A_94 ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_78,plain,(
    ! [B_95] : ~ r2_hidden(B_95,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_72])).

tff(c_83,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_42,c_78])).

tff(c_216,plain,(
    ! [D_151,A_152,B_153] :
      ( r2_hidden(k4_tarski(D_151,'#skF_4'(A_152,B_153,k10_relat_1(A_152,B_153),D_151)),A_152)
      | ~ r2_hidden(D_151,k10_relat_1(A_152,B_153))
      | ~ v1_relat_1(A_152) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_77,plain,(
    ! [B_93] : ~ r2_hidden(B_93,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_72])).

tff(c_234,plain,(
    ! [D_151,B_153] :
      ( ~ r2_hidden(D_151,k10_relat_1(k1_xboole_0,B_153))
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_216,c_77])).

tff(c_242,plain,(
    ! [D_154,B_155] : ~ r2_hidden(D_154,k10_relat_1(k1_xboole_0,B_155)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_83,c_234])).

tff(c_257,plain,(
    ! [B_155] : v1_relat_1(k10_relat_1(k1_xboole_0,B_155)) ),
    inference(resolution,[status(thm)],[c_42,c_242])).

tff(c_258,plain,(
    ! [A_156,B_157,C_158] :
      ( r2_hidden('#skF_2'(A_156,B_157,C_158),B_157)
      | r2_hidden('#skF_3'(A_156,B_157,C_158),C_158)
      | k10_relat_1(A_156,B_157) = C_158
      | ~ v1_relat_1(A_156) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_401,plain,(
    ! [A_181,C_182] :
      ( r2_hidden('#skF_3'(A_181,k1_xboole_0,C_182),C_182)
      | k10_relat_1(A_181,k1_xboole_0) = C_182
      | ~ v1_relat_1(A_181) ) ),
    inference(resolution,[status(thm)],[c_258,c_77])).

tff(c_495,plain,(
    ! [A_186] :
      ( k10_relat_1(A_186,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(A_186) ) ),
    inference(resolution,[status(thm)],[c_401,c_77])).

tff(c_523,plain,(
    ! [B_155] : k10_relat_1(k10_relat_1(k1_xboole_0,B_155),k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_257,c_495])).

tff(c_241,plain,(
    ! [D_151,B_153] : ~ r2_hidden(D_151,k10_relat_1(k1_xboole_0,B_153)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_83,c_234])).

tff(c_653,plain,(
    ! [B_188,A_189] :
      ( k10_relat_1(k1_xboole_0,B_188) = k10_relat_1(A_189,k1_xboole_0)
      | ~ v1_relat_1(A_189) ) ),
    inference(resolution,[status(thm)],[c_401,c_241])).

tff(c_661,plain,(
    ! [B_188,B_155] : k10_relat_1(k1_xboole_0,B_188) = k10_relat_1(k10_relat_1(k1_xboole_0,B_155),k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_257,c_653])).

tff(c_674,plain,(
    ! [B_188] : k10_relat_1(k1_xboole_0,B_188) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_523,c_661])).

tff(c_44,plain,(
    k10_relat_1(k1_xboole_0,'#skF_8') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_695,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_674,c_44])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n005.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 12:35:32 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.41/1.46  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.41/1.46  
% 2.41/1.46  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.84/1.47  %$ r2_hidden > v1_relat_1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k4_tarski > k2_tarski > k10_relat_1 > #nlpp > k1_tarski > k1_xboole_0 > #skF_5 > #skF_6 > #skF_1 > #skF_2 > #skF_4 > #skF_8 > #skF_3 > #skF_7
% 2.84/1.47  
% 2.84/1.47  %Foreground sorts:
% 2.84/1.47  
% 2.84/1.47  
% 2.84/1.47  %Background operators:
% 2.84/1.47  
% 2.84/1.47  
% 2.84/1.47  %Foreground operators:
% 2.84/1.47  tff('#skF_5', type, '#skF_5': $i > $i).
% 2.84/1.47  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 2.84/1.47  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.84/1.47  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.84/1.47  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.84/1.47  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.84/1.47  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.84/1.47  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.84/1.47  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.84/1.47  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.84/1.47  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.84/1.47  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.84/1.47  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.84/1.47  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.84/1.47  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.84/1.47  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i) > $i).
% 2.84/1.47  tff('#skF_8', type, '#skF_8': $i).
% 2.84/1.47  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.84/1.47  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 2.84/1.47  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.84/1.47  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 2.84/1.47  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.84/1.47  tff('#skF_7', type, '#skF_7': ($i * $i) > $i).
% 2.84/1.47  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.84/1.47  
% 2.84/1.48  tff(f_67, axiom, (![A]: (v1_relat_1(A) <=> (![B]: ~(r2_hidden(B, A) & (![C, D]: ~(B = k4_tarski(C, D))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_relat_1)).
% 2.84/1.48  tff(f_27, axiom, (![A]: (k4_xboole_0(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_boole)).
% 2.84/1.48  tff(f_44, axiom, (![A, B]: ((k4_xboole_0(A, k1_tarski(B)) = A) <=> ~r2_hidden(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_zfmisc_1)).
% 2.84/1.48  tff(f_57, axiom, (![A]: (v1_relat_1(A) => (![B, C]: ((C = k10_relat_1(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (?[E]: (r2_hidden(k4_tarski(D, E), A) & r2_hidden(E, B))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d14_relat_1)).
% 2.84/1.48  tff(f_70, negated_conjecture, ~(![A]: (k10_relat_1(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t172_relat_1)).
% 2.84/1.48  tff(c_42, plain, (![A_67]: (r2_hidden('#skF_5'(A_67), A_67) | v1_relat_1(A_67))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.84/1.48  tff(c_2, plain, (![A_1]: (k4_xboole_0(k1_xboole_0, A_1)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.84/1.48  tff(c_72, plain, (![B_93, A_94]: (~r2_hidden(B_93, A_94) | k4_xboole_0(A_94, k1_tarski(B_93))!=A_94)), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.84/1.48  tff(c_78, plain, (![B_95]: (~r2_hidden(B_95, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_2, c_72])).
% 2.84/1.48  tff(c_83, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_42, c_78])).
% 2.84/1.48  tff(c_216, plain, (![D_151, A_152, B_153]: (r2_hidden(k4_tarski(D_151, '#skF_4'(A_152, B_153, k10_relat_1(A_152, B_153), D_151)), A_152) | ~r2_hidden(D_151, k10_relat_1(A_152, B_153)) | ~v1_relat_1(A_152))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.84/1.48  tff(c_77, plain, (![B_93]: (~r2_hidden(B_93, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_2, c_72])).
% 2.84/1.48  tff(c_234, plain, (![D_151, B_153]: (~r2_hidden(D_151, k10_relat_1(k1_xboole_0, B_153)) | ~v1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_216, c_77])).
% 2.84/1.48  tff(c_242, plain, (![D_154, B_155]: (~r2_hidden(D_154, k10_relat_1(k1_xboole_0, B_155)))), inference(demodulation, [status(thm), theory('equality')], [c_83, c_234])).
% 2.84/1.48  tff(c_257, plain, (![B_155]: (v1_relat_1(k10_relat_1(k1_xboole_0, B_155)))), inference(resolution, [status(thm)], [c_42, c_242])).
% 2.84/1.48  tff(c_258, plain, (![A_156, B_157, C_158]: (r2_hidden('#skF_2'(A_156, B_157, C_158), B_157) | r2_hidden('#skF_3'(A_156, B_157, C_158), C_158) | k10_relat_1(A_156, B_157)=C_158 | ~v1_relat_1(A_156))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.84/1.48  tff(c_401, plain, (![A_181, C_182]: (r2_hidden('#skF_3'(A_181, k1_xboole_0, C_182), C_182) | k10_relat_1(A_181, k1_xboole_0)=C_182 | ~v1_relat_1(A_181))), inference(resolution, [status(thm)], [c_258, c_77])).
% 2.84/1.48  tff(c_495, plain, (![A_186]: (k10_relat_1(A_186, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(A_186))), inference(resolution, [status(thm)], [c_401, c_77])).
% 2.84/1.48  tff(c_523, plain, (![B_155]: (k10_relat_1(k10_relat_1(k1_xboole_0, B_155), k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_257, c_495])).
% 2.84/1.48  tff(c_241, plain, (![D_151, B_153]: (~r2_hidden(D_151, k10_relat_1(k1_xboole_0, B_153)))), inference(demodulation, [status(thm), theory('equality')], [c_83, c_234])).
% 2.84/1.48  tff(c_653, plain, (![B_188, A_189]: (k10_relat_1(k1_xboole_0, B_188)=k10_relat_1(A_189, k1_xboole_0) | ~v1_relat_1(A_189))), inference(resolution, [status(thm)], [c_401, c_241])).
% 2.84/1.48  tff(c_661, plain, (![B_188, B_155]: (k10_relat_1(k1_xboole_0, B_188)=k10_relat_1(k10_relat_1(k1_xboole_0, B_155), k1_xboole_0))), inference(resolution, [status(thm)], [c_257, c_653])).
% 2.84/1.48  tff(c_674, plain, (![B_188]: (k10_relat_1(k1_xboole_0, B_188)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_523, c_661])).
% 2.84/1.48  tff(c_44, plain, (k10_relat_1(k1_xboole_0, '#skF_8')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.84/1.48  tff(c_695, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_674, c_44])).
% 2.84/1.48  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.84/1.48  
% 2.84/1.48  Inference rules
% 2.84/1.48  ----------------------
% 2.84/1.48  #Ref     : 1
% 2.84/1.48  #Sup     : 136
% 2.84/1.48  #Fact    : 0
% 2.84/1.48  #Define  : 0
% 2.84/1.48  #Split   : 0
% 2.84/1.48  #Chain   : 0
% 2.84/1.48  #Close   : 0
% 2.84/1.48  
% 2.84/1.48  Ordering : KBO
% 2.84/1.48  
% 2.84/1.48  Simplification rules
% 2.84/1.48  ----------------------
% 2.84/1.48  #Subsume      : 30
% 2.84/1.48  #Demod        : 52
% 2.84/1.48  #Tautology    : 36
% 2.84/1.48  #SimpNegUnit  : 6
% 2.84/1.48  #BackRed      : 10
% 2.84/1.48  
% 2.84/1.48  #Partial instantiations: 0
% 2.84/1.48  #Strategies tried      : 1
% 2.84/1.48  
% 2.84/1.48  Timing (in seconds)
% 2.84/1.48  ----------------------
% 2.84/1.48  Preprocessing        : 0.33
% 2.84/1.48  Parsing              : 0.17
% 2.84/1.48  CNF conversion       : 0.03
% 2.84/1.48  Main loop            : 0.30
% 2.84/1.48  Inferencing          : 0.12
% 2.84/1.48  Reduction            : 0.07
% 2.84/1.48  Demodulation         : 0.04
% 2.84/1.48  BG Simplification    : 0.02
% 2.84/1.48  Subsumption          : 0.07
% 2.84/1.48  Abstraction          : 0.02
% 2.84/1.48  MUC search           : 0.00
% 2.84/1.48  Cooper               : 0.00
% 2.84/1.48  Total                : 0.65
% 2.84/1.48  Index Insertion      : 0.00
% 2.84/1.48  Index Deletion       : 0.00
% 2.84/1.48  Index Matching       : 0.00
% 2.84/1.48  BG Taut test         : 0.00
%------------------------------------------------------------------------------
