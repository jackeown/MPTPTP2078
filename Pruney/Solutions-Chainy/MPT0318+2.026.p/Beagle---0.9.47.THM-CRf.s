%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:54:05 EST 2020

% Result     : Theorem 2.14s
% Output     : CNFRefutation 2.14s
% Verified   : 
% Statistics : Number of formulae       :   53 (  70 expanded)
%              Number of leaves         :   30 (  38 expanded)
%              Depth                    :    7
%              Number of atoms          :   51 (  84 expanded)
%              Number of equality atoms :   16 (  32 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > v1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_tarski > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
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

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

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

tff(f_89,negated_conjecture,(
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

tff(f_53,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_51,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

tff(f_49,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_73,axiom,(
    ! [A,B,C,D] :
      ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(k1_tarski(C),D))
    <=> ( A = C
        & r2_hidden(B,D) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t128_zfmisc_1)).

tff(f_35,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_79,axiom,(
    ! [A,B,C,D] :
      ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(C,k1_tarski(D)))
    <=> ( r2_hidden(A,C)
        & B = D ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t129_zfmisc_1)).

tff(c_44,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_14,plain,(
    ! [A_12] : r1_xboole_0(A_12,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_12,plain,(
    ! [A_11] : k3_xboole_0(A_11,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_78,plain,(
    ! [A_58,B_59,C_60] :
      ( ~ r1_xboole_0(A_58,B_59)
      | ~ r2_hidden(C_60,k3_xboole_0(A_58,B_59)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_85,plain,(
    ! [A_11,C_60] :
      ( ~ r1_xboole_0(A_11,k1_xboole_0)
      | ~ r2_hidden(C_60,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_78])).

tff(c_88,plain,(
    ! [C_60] : ~ r2_hidden(C_60,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_85])).

tff(c_42,plain,
    ( k2_zfmisc_1('#skF_3',k1_tarski('#skF_4')) = k1_xboole_0
    | k2_zfmisc_1(k1_tarski('#skF_4'),'#skF_3') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_89,plain,(
    k2_zfmisc_1(k1_tarski('#skF_4'),'#skF_3') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_42])).

tff(c_172,plain,(
    ! [C_89,B_90,D_91] :
      ( r2_hidden(k4_tarski(C_89,B_90),k2_zfmisc_1(k1_tarski(C_89),D_91))
      | ~ r2_hidden(B_90,D_91) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_188,plain,(
    ! [B_90] :
      ( r2_hidden(k4_tarski('#skF_4',B_90),k1_xboole_0)
      | ~ r2_hidden(B_90,'#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_89,c_172])).

tff(c_195,plain,(
    ! [B_92] : ~ r2_hidden(B_92,'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_88,c_188])).

tff(c_200,plain,(
    v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_4,c_195])).

tff(c_6,plain,(
    ! [A_5] :
      ( k1_xboole_0 = A_5
      | ~ v1_xboole_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_203,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_200,c_6])).

tff(c_207,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_203])).

tff(c_208,plain,(
    k2_zfmisc_1('#skF_3',k1_tarski('#skF_4')) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_305,plain,(
    ! [A_122,D_123,C_124] :
      ( r2_hidden(k4_tarski(A_122,D_123),k2_zfmisc_1(C_124,k1_tarski(D_123)))
      | ~ r2_hidden(A_122,C_124) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_322,plain,(
    ! [A_122] :
      ( r2_hidden(k4_tarski(A_122,'#skF_4'),k1_xboole_0)
      | ~ r2_hidden(A_122,'#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_208,c_305])).

tff(c_329,plain,(
    ! [A_125] : ~ r2_hidden(A_125,'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_88,c_322])).

tff(c_334,plain,(
    v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_4,c_329])).

tff(c_337,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_334,c_6])).

tff(c_341,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_337])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n018.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 11:37:26 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.14/1.25  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.14/1.25  
% 2.14/1.25  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.14/1.25  %$ r2_hidden > r1_xboole_0 > v1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_tarski > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2
% 2.14/1.25  
% 2.14/1.25  %Foreground sorts:
% 2.14/1.25  
% 2.14/1.25  
% 2.14/1.25  %Background operators:
% 2.14/1.25  
% 2.14/1.25  
% 2.14/1.25  %Foreground operators:
% 2.14/1.25  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.14/1.25  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.14/1.25  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.14/1.25  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.14/1.25  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.14/1.25  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.14/1.25  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.14/1.25  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.14/1.25  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.14/1.25  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.14/1.25  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.14/1.25  tff('#skF_3', type, '#skF_3': $i).
% 2.14/1.25  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.14/1.25  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.14/1.25  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.14/1.25  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.14/1.25  tff('#skF_4', type, '#skF_4': $i).
% 2.14/1.25  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.14/1.25  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.14/1.25  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.14/1.25  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.14/1.25  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.14/1.25  
% 2.14/1.26  tff(f_89, negated_conjecture, ~(![A, B]: (~(A = k1_xboole_0) => (~(k2_zfmisc_1(k1_tarski(B), A) = k1_xboole_0) & ~(k2_zfmisc_1(A, k1_tarski(B)) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t130_zfmisc_1)).
% 2.14/1.26  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 2.14/1.26  tff(f_53, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 2.14/1.26  tff(f_51, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 2.14/1.26  tff(f_49, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 2.14/1.26  tff(f_73, axiom, (![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(k1_tarski(C), D)) <=> ((A = C) & r2_hidden(B, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t128_zfmisc_1)).
% 2.14/1.26  tff(f_35, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 2.14/1.26  tff(f_79, axiom, (![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(C, k1_tarski(D))) <=> (r2_hidden(A, C) & (B = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t129_zfmisc_1)).
% 2.14/1.26  tff(c_44, plain, (k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.14/1.26  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.14/1.26  tff(c_14, plain, (![A_12]: (r1_xboole_0(A_12, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.14/1.26  tff(c_12, plain, (![A_11]: (k3_xboole_0(A_11, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.14/1.26  tff(c_78, plain, (![A_58, B_59, C_60]: (~r1_xboole_0(A_58, B_59) | ~r2_hidden(C_60, k3_xboole_0(A_58, B_59)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.14/1.26  tff(c_85, plain, (![A_11, C_60]: (~r1_xboole_0(A_11, k1_xboole_0) | ~r2_hidden(C_60, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_12, c_78])).
% 2.14/1.26  tff(c_88, plain, (![C_60]: (~r2_hidden(C_60, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_85])).
% 2.14/1.26  tff(c_42, plain, (k2_zfmisc_1('#skF_3', k1_tarski('#skF_4'))=k1_xboole_0 | k2_zfmisc_1(k1_tarski('#skF_4'), '#skF_3')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.14/1.26  tff(c_89, plain, (k2_zfmisc_1(k1_tarski('#skF_4'), '#skF_3')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_42])).
% 2.14/1.26  tff(c_172, plain, (![C_89, B_90, D_91]: (r2_hidden(k4_tarski(C_89, B_90), k2_zfmisc_1(k1_tarski(C_89), D_91)) | ~r2_hidden(B_90, D_91))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.14/1.26  tff(c_188, plain, (![B_90]: (r2_hidden(k4_tarski('#skF_4', B_90), k1_xboole_0) | ~r2_hidden(B_90, '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_89, c_172])).
% 2.14/1.26  tff(c_195, plain, (![B_92]: (~r2_hidden(B_92, '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_88, c_188])).
% 2.14/1.26  tff(c_200, plain, (v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_4, c_195])).
% 2.14/1.26  tff(c_6, plain, (![A_5]: (k1_xboole_0=A_5 | ~v1_xboole_0(A_5))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.14/1.26  tff(c_203, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_200, c_6])).
% 2.14/1.26  tff(c_207, plain, $false, inference(negUnitSimplification, [status(thm)], [c_44, c_203])).
% 2.14/1.26  tff(c_208, plain, (k2_zfmisc_1('#skF_3', k1_tarski('#skF_4'))=k1_xboole_0), inference(splitRight, [status(thm)], [c_42])).
% 2.14/1.26  tff(c_305, plain, (![A_122, D_123, C_124]: (r2_hidden(k4_tarski(A_122, D_123), k2_zfmisc_1(C_124, k1_tarski(D_123))) | ~r2_hidden(A_122, C_124))), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.14/1.26  tff(c_322, plain, (![A_122]: (r2_hidden(k4_tarski(A_122, '#skF_4'), k1_xboole_0) | ~r2_hidden(A_122, '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_208, c_305])).
% 2.14/1.26  tff(c_329, plain, (![A_125]: (~r2_hidden(A_125, '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_88, c_322])).
% 2.14/1.26  tff(c_334, plain, (v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_4, c_329])).
% 2.14/1.26  tff(c_337, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_334, c_6])).
% 2.14/1.26  tff(c_341, plain, $false, inference(negUnitSimplification, [status(thm)], [c_44, c_337])).
% 2.14/1.26  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.14/1.26  
% 2.14/1.26  Inference rules
% 2.14/1.26  ----------------------
% 2.14/1.26  #Ref     : 0
% 2.14/1.26  #Sup     : 61
% 2.14/1.26  #Fact    : 0
% 2.14/1.26  #Define  : 0
% 2.14/1.27  #Split   : 1
% 2.14/1.27  #Chain   : 0
% 2.14/1.27  #Close   : 0
% 2.14/1.27  
% 2.14/1.27  Ordering : KBO
% 2.14/1.27  
% 2.14/1.27  Simplification rules
% 2.14/1.27  ----------------------
% 2.14/1.27  #Subsume      : 4
% 2.14/1.27  #Demod        : 13
% 2.14/1.27  #Tautology    : 36
% 2.14/1.27  #SimpNegUnit  : 6
% 2.14/1.27  #BackRed      : 0
% 2.14/1.27  
% 2.14/1.27  #Partial instantiations: 0
% 2.14/1.27  #Strategies tried      : 1
% 2.14/1.27  
% 2.14/1.27  Timing (in seconds)
% 2.14/1.27  ----------------------
% 2.14/1.27  Preprocessing        : 0.32
% 2.14/1.27  Parsing              : 0.17
% 2.14/1.27  CNF conversion       : 0.02
% 2.14/1.27  Main loop            : 0.18
% 2.14/1.27  Inferencing          : 0.07
% 2.14/1.27  Reduction            : 0.05
% 2.14/1.27  Demodulation         : 0.03
% 2.14/1.27  BG Simplification    : 0.01
% 2.14/1.27  Subsumption          : 0.03
% 2.14/1.27  Abstraction          : 0.01
% 2.14/1.27  MUC search           : 0.00
% 2.14/1.27  Cooper               : 0.00
% 2.14/1.27  Total                : 0.52
% 2.14/1.27  Index Insertion      : 0.00
% 2.14/1.27  Index Deletion       : 0.00
% 2.14/1.27  Index Matching       : 0.00
% 2.14/1.27  BG Taut test         : 0.00
%------------------------------------------------------------------------------
