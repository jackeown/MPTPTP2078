%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:54:04 EST 2020

% Result     : Theorem 2.56s
% Output     : CNFRefutation 2.56s
% Verified   : 
% Statistics : Number of formulae       :   51 (  74 expanded)
%              Number of leaves         :   26 (  38 expanded)
%              Depth                    :    8
%              Number of atoms          :   50 (  90 expanded)
%              Number of equality atoms :   16 (  34 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_tarski > k2_zfmisc_1 > k2_tarski > #nlpp > k1_tarski > o_0_0_xboole_0 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(o_0_0_xboole_0,type,(
    o_0_0_xboole_0: $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

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

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(f_72,negated_conjecture,(
    ~ ! [A,B] :
        ( A != k1_xboole_0
       => ( k2_zfmisc_1(k1_tarski(B),A) != k1_xboole_0
          & k2_zfmisc_1(A,k1_tarski(B)) != k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t130_zfmisc_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_32,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_o_0_0_xboole_0)).

tff(f_36,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_56,axiom,(
    ! [A,B,C,D] :
      ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(k1_tarski(C),D))
    <=> ( A = C
        & r2_hidden(B,D) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t128_zfmisc_1)).

tff(f_62,axiom,(
    ! [A,B,C,D] :
      ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(C,k1_tarski(D)))
    <=> ( r2_hidden(A,C)
        & B = D ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t129_zfmisc_1)).

tff(c_38,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_6,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_39,plain,(
    ! [A_42] :
      ( k1_xboole_0 = A_42
      | ~ v1_xboole_0(A_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_43,plain,(
    o_0_0_xboole_0 = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_6,c_39])).

tff(c_44,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_43,c_6])).

tff(c_36,plain,
    ( k2_zfmisc_1('#skF_2',k1_tarski('#skF_3')) = k1_xboole_0
    | k2_zfmisc_1(k1_tarski('#skF_3'),'#skF_2') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_78,plain,(
    k2_zfmisc_1(k1_tarski('#skF_3'),'#skF_2') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_36])).

tff(c_103,plain,(
    ! [C_68,B_69,D_70] :
      ( r2_hidden(k4_tarski(C_68,B_69),k2_zfmisc_1(k1_tarski(C_68),D_70))
      | ~ r2_hidden(B_69,D_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_131,plain,(
    ! [B_73] :
      ( r2_hidden(k4_tarski('#skF_3',B_73),k1_xboole_0)
      | ~ r2_hidden(B_73,'#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_78,c_103])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_140,plain,(
    ! [B_73] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | ~ r2_hidden(B_73,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_131,c_2])).

tff(c_148,plain,(
    ! [B_74] : ~ r2_hidden(B_74,'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_140])).

tff(c_153,plain,(
    v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_4,c_148])).

tff(c_8,plain,(
    ! [A_5] :
      ( k1_xboole_0 = A_5
      | ~ v1_xboole_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_156,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_153,c_8])).

tff(c_160,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_156])).

tff(c_161,plain,(
    k2_zfmisc_1('#skF_2',k1_tarski('#skF_3')) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_36])).

tff(c_188,plain,(
    ! [A_98,D_99,C_100] :
      ( r2_hidden(k4_tarski(A_98,D_99),k2_zfmisc_1(C_100,k1_tarski(D_99)))
      | ~ r2_hidden(A_98,C_100) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_263,plain,(
    ! [C_108,D_109,A_110] :
      ( ~ v1_xboole_0(k2_zfmisc_1(C_108,k1_tarski(D_109)))
      | ~ r2_hidden(A_110,C_108) ) ),
    inference(resolution,[status(thm)],[c_188,c_2])).

tff(c_265,plain,(
    ! [A_110] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | ~ r2_hidden(A_110,'#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_161,c_263])).

tff(c_269,plain,(
    ! [A_111] : ~ r2_hidden(A_111,'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_265])).

tff(c_274,plain,(
    v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_4,c_269])).

tff(c_277,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_274,c_8])).

tff(c_281,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_277])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 14:24:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.56/1.61  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.56/1.62  
% 2.56/1.62  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.56/1.62  %$ r2_hidden > v1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_tarski > k2_zfmisc_1 > k2_tarski > #nlpp > k1_tarski > o_0_0_xboole_0 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3
% 2.56/1.62  
% 2.56/1.62  %Foreground sorts:
% 2.56/1.62  
% 2.56/1.62  
% 2.56/1.62  %Background operators:
% 2.56/1.62  
% 2.56/1.62  
% 2.56/1.62  %Foreground operators:
% 2.56/1.62  tff(o_0_0_xboole_0, type, o_0_0_xboole_0: $i).
% 2.56/1.62  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.56/1.62  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.56/1.62  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.56/1.62  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.56/1.62  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.56/1.62  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.56/1.62  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.56/1.62  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.56/1.62  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.56/1.62  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.56/1.62  tff('#skF_2', type, '#skF_2': $i).
% 2.56/1.62  tff('#skF_3', type, '#skF_3': $i).
% 2.56/1.62  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.56/1.62  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.56/1.62  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.56/1.62  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.56/1.62  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.56/1.62  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.56/1.62  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.56/1.62  
% 2.56/1.64  tff(f_72, negated_conjecture, ~(![A, B]: (~(A = k1_xboole_0) => (~(k2_zfmisc_1(k1_tarski(B), A) = k1_xboole_0) & ~(k2_zfmisc_1(A, k1_tarski(B)) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t130_zfmisc_1)).
% 2.56/1.64  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 2.56/1.64  tff(f_32, axiom, v1_xboole_0(o_0_0_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_o_0_0_xboole_0)).
% 2.56/1.64  tff(f_36, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 2.56/1.64  tff(f_56, axiom, (![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(k1_tarski(C), D)) <=> ((A = C) & r2_hidden(B, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t128_zfmisc_1)).
% 2.56/1.64  tff(f_62, axiom, (![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(C, k1_tarski(D))) <=> (r2_hidden(A, C) & (B = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t129_zfmisc_1)).
% 2.56/1.64  tff(c_38, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.56/1.64  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.56/1.64  tff(c_6, plain, (v1_xboole_0(o_0_0_xboole_0)), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.56/1.64  tff(c_39, plain, (![A_42]: (k1_xboole_0=A_42 | ~v1_xboole_0(A_42))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.56/1.64  tff(c_43, plain, (o_0_0_xboole_0=k1_xboole_0), inference(resolution, [status(thm)], [c_6, c_39])).
% 2.56/1.64  tff(c_44, plain, (v1_xboole_0(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_43, c_6])).
% 2.56/1.64  tff(c_36, plain, (k2_zfmisc_1('#skF_2', k1_tarski('#skF_3'))=k1_xboole_0 | k2_zfmisc_1(k1_tarski('#skF_3'), '#skF_2')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.56/1.64  tff(c_78, plain, (k2_zfmisc_1(k1_tarski('#skF_3'), '#skF_2')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_36])).
% 2.56/1.64  tff(c_103, plain, (![C_68, B_69, D_70]: (r2_hidden(k4_tarski(C_68, B_69), k2_zfmisc_1(k1_tarski(C_68), D_70)) | ~r2_hidden(B_69, D_70))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.56/1.64  tff(c_131, plain, (![B_73]: (r2_hidden(k4_tarski('#skF_3', B_73), k1_xboole_0) | ~r2_hidden(B_73, '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_78, c_103])).
% 2.56/1.64  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.56/1.64  tff(c_140, plain, (![B_73]: (~v1_xboole_0(k1_xboole_0) | ~r2_hidden(B_73, '#skF_2'))), inference(resolution, [status(thm)], [c_131, c_2])).
% 2.56/1.64  tff(c_148, plain, (![B_74]: (~r2_hidden(B_74, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_140])).
% 2.56/1.64  tff(c_153, plain, (v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_4, c_148])).
% 2.56/1.64  tff(c_8, plain, (![A_5]: (k1_xboole_0=A_5 | ~v1_xboole_0(A_5))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.56/1.64  tff(c_156, plain, (k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_153, c_8])).
% 2.56/1.64  tff(c_160, plain, $false, inference(negUnitSimplification, [status(thm)], [c_38, c_156])).
% 2.56/1.64  tff(c_161, plain, (k2_zfmisc_1('#skF_2', k1_tarski('#skF_3'))=k1_xboole_0), inference(splitRight, [status(thm)], [c_36])).
% 2.56/1.64  tff(c_188, plain, (![A_98, D_99, C_100]: (r2_hidden(k4_tarski(A_98, D_99), k2_zfmisc_1(C_100, k1_tarski(D_99))) | ~r2_hidden(A_98, C_100))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.56/1.64  tff(c_263, plain, (![C_108, D_109, A_110]: (~v1_xboole_0(k2_zfmisc_1(C_108, k1_tarski(D_109))) | ~r2_hidden(A_110, C_108))), inference(resolution, [status(thm)], [c_188, c_2])).
% 2.56/1.64  tff(c_265, plain, (![A_110]: (~v1_xboole_0(k1_xboole_0) | ~r2_hidden(A_110, '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_161, c_263])).
% 2.56/1.64  tff(c_269, plain, (![A_111]: (~r2_hidden(A_111, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_265])).
% 2.56/1.64  tff(c_274, plain, (v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_4, c_269])).
% 2.56/1.64  tff(c_277, plain, (k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_274, c_8])).
% 2.56/1.64  tff(c_281, plain, $false, inference(negUnitSimplification, [status(thm)], [c_38, c_277])).
% 2.56/1.64  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.56/1.64  
% 2.56/1.64  Inference rules
% 2.56/1.64  ----------------------
% 2.56/1.64  #Ref     : 0
% 2.56/1.64  #Sup     : 51
% 2.56/1.64  #Fact    : 0
% 2.56/1.64  #Define  : 0
% 2.56/1.64  #Split   : 1
% 2.56/1.64  #Chain   : 0
% 2.56/1.64  #Close   : 0
% 2.56/1.64  
% 2.56/1.64  Ordering : KBO
% 2.56/1.64  
% 2.56/1.64  Simplification rules
% 2.56/1.64  ----------------------
% 2.56/1.64  #Subsume      : 2
% 2.56/1.64  #Demod        : 3
% 2.56/1.64  #Tautology    : 26
% 2.56/1.64  #SimpNegUnit  : 4
% 2.56/1.64  #BackRed      : 3
% 2.56/1.64  
% 2.56/1.64  #Partial instantiations: 0
% 2.56/1.64  #Strategies tried      : 1
% 2.56/1.64  
% 2.56/1.64  Timing (in seconds)
% 2.56/1.64  ----------------------
% 2.56/1.65  Preprocessing        : 0.52
% 2.56/1.65  Parsing              : 0.27
% 2.56/1.65  CNF conversion       : 0.04
% 2.56/1.65  Main loop            : 0.30
% 2.56/1.65  Inferencing          : 0.11
% 2.56/1.65  Reduction            : 0.08
% 2.56/1.65  Demodulation         : 0.05
% 2.56/1.65  BG Simplification    : 0.02
% 2.56/1.65  Subsumption          : 0.05
% 2.56/1.65  Abstraction          : 0.01
% 2.56/1.65  MUC search           : 0.00
% 2.56/1.65  Cooper               : 0.00
% 2.56/1.65  Total                : 0.87
% 2.56/1.65  Index Insertion      : 0.00
% 2.56/1.65  Index Deletion       : 0.00
% 2.56/1.65  Index Matching       : 0.00
% 2.56/1.65  BG Taut test         : 0.00
%------------------------------------------------------------------------------
