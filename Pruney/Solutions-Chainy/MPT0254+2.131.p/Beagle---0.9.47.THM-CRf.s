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
% DateTime   : Thu Dec  3 09:51:36 EST 2020

% Result     : Theorem 2.15s
% Output     : CNFRefutation 2.15s
% Verified   : 
% Statistics : Number of formulae       :   57 ( 107 expanded)
%              Number of leaves         :   32 (  50 expanded)
%              Depth                    :   12
%              Number of atoms          :   52 ( 112 expanded)
%              Number of equality atoms :   23 (  61 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
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

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_84,negated_conjecture,(
    ~ ! [A,B] : k2_xboole_0(k1_tarski(A),B) != k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_zfmisc_1)).

tff(f_50,axiom,(
    ! [A,B] : k4_xboole_0(A,k2_xboole_0(A,B)) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).

tff(f_46,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_38,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(A)
     => ~ v1_xboole_0(k2_xboole_0(B,A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc5_xboole_0)).

tff(f_32,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_44,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_42,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_54,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_65,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

tff(f_78,axiom,(
    ! [A,B] :
      ~ ( r1_xboole_0(k1_tarski(A),B)
        & r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l24_zfmisc_1)).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_58,plain,(
    k2_xboole_0(k1_tarski('#skF_3'),'#skF_4') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_105,plain,(
    ! [A_48,B_49] : k4_xboole_0(A_48,k2_xboole_0(A_48,B_49)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_112,plain,(
    k4_xboole_0(k1_tarski('#skF_3'),k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_58,c_105])).

tff(c_16,plain,(
    ! [A_9] : k4_xboole_0(A_9,k1_xboole_0) = A_9 ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_140,plain,(
    k1_tarski('#skF_3') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_112,c_16])).

tff(c_148,plain,(
    k2_xboole_0(k1_xboole_0,'#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_140,c_58])).

tff(c_8,plain,(
    ! [B_5,A_4] :
      ( ~ v1_xboole_0(k2_xboole_0(B_5,A_4))
      | v1_xboole_0(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_165,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | v1_xboole_0('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_148,c_8])).

tff(c_172,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_165])).

tff(c_6,plain,(
    ! [A_3] :
      ( k1_xboole_0 = A_3
      | ~ v1_xboole_0(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_178,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_172,c_6])).

tff(c_14,plain,(
    ! [A_8] : r1_tarski(k1_xboole_0,A_8) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_186,plain,(
    ! [A_8] : r1_tarski('#skF_4',A_8) ),
    inference(demodulation,[status(thm),theory(equality)],[c_178,c_14])).

tff(c_12,plain,(
    ! [A_6,B_7] :
      ( k4_xboole_0(A_6,B_7) = k1_xboole_0
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_288,plain,(
    ! [A_68,B_69] :
      ( k4_xboole_0(A_68,B_69) = '#skF_4'
      | ~ r1_tarski(A_68,B_69) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_178,c_12])).

tff(c_292,plain,(
    ! [A_8] : k4_xboole_0('#skF_4',A_8) = '#skF_4' ),
    inference(resolution,[status(thm)],[c_186,c_288])).

tff(c_338,plain,(
    ! [A_74,B_75] :
      ( r1_xboole_0(A_74,B_75)
      | k4_xboole_0(A_74,B_75) != A_74 ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_30,plain,(
    ! [D_24,A_19] : r2_hidden(D_24,k2_tarski(A_19,D_24)) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_181,plain,(
    k1_tarski('#skF_3') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_178,c_140])).

tff(c_256,plain,(
    ! [A_64,B_65] :
      ( ~ r2_hidden(A_64,B_65)
      | ~ r1_xboole_0(k1_tarski(A_64),B_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_260,plain,(
    ! [B_66] :
      ( ~ r2_hidden('#skF_3',B_66)
      | ~ r1_xboole_0('#skF_4',B_66) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_181,c_256])).

tff(c_280,plain,(
    ! [A_19] : ~ r1_xboole_0('#skF_4',k2_tarski(A_19,'#skF_3')) ),
    inference(resolution,[status(thm)],[c_30,c_260])).

tff(c_341,plain,(
    ! [A_19] : k4_xboole_0('#skF_4',k2_tarski(A_19,'#skF_3')) != '#skF_4' ),
    inference(resolution,[status(thm)],[c_338,c_280])).

tff(c_358,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_292,c_341])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n018.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 19:43:42 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.15/1.23  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.15/1.24  
% 2.15/1.24  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.15/1.24  %$ r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2 > #skF_4
% 2.15/1.24  
% 2.15/1.24  %Foreground sorts:
% 2.15/1.24  
% 2.15/1.24  
% 2.15/1.24  %Background operators:
% 2.15/1.24  
% 2.15/1.24  
% 2.15/1.24  %Foreground operators:
% 2.15/1.24  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.15/1.24  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.15/1.24  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.15/1.24  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.15/1.24  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.15/1.24  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.15/1.24  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.15/1.24  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.15/1.24  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.15/1.24  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.15/1.24  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.15/1.24  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.15/1.24  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.15/1.24  tff('#skF_3', type, '#skF_3': $i).
% 2.15/1.24  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.15/1.24  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.15/1.24  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.15/1.24  tff('#skF_4', type, '#skF_4': $i).
% 2.15/1.24  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.15/1.24  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.15/1.24  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.15/1.24  
% 2.15/1.25  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.15/1.25  tff(f_84, negated_conjecture, ~(![A, B]: ~(k2_xboole_0(k1_tarski(A), B) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_zfmisc_1)).
% 2.15/1.25  tff(f_50, axiom, (![A, B]: (k4_xboole_0(A, k2_xboole_0(A, B)) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_xboole_1)).
% 2.15/1.25  tff(f_46, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 2.15/1.25  tff(f_38, axiom, (![A, B]: (~v1_xboole_0(A) => ~v1_xboole_0(k2_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc5_xboole_0)).
% 2.15/1.25  tff(f_32, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 2.15/1.25  tff(f_44, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.15/1.25  tff(f_42, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 2.15/1.25  tff(f_54, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 2.15/1.25  tff(f_65, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_tarski)).
% 2.15/1.25  tff(f_78, axiom, (![A, B]: ~(r1_xboole_0(k1_tarski(A), B) & r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l24_zfmisc_1)).
% 2.15/1.25  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 2.15/1.25  tff(c_58, plain, (k2_xboole_0(k1_tarski('#skF_3'), '#skF_4')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.15/1.25  tff(c_105, plain, (![A_48, B_49]: (k4_xboole_0(A_48, k2_xboole_0(A_48, B_49))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.15/1.25  tff(c_112, plain, (k4_xboole_0(k1_tarski('#skF_3'), k1_xboole_0)=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_58, c_105])).
% 2.15/1.25  tff(c_16, plain, (![A_9]: (k4_xboole_0(A_9, k1_xboole_0)=A_9)), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.15/1.25  tff(c_140, plain, (k1_tarski('#skF_3')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_112, c_16])).
% 2.15/1.25  tff(c_148, plain, (k2_xboole_0(k1_xboole_0, '#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_140, c_58])).
% 2.15/1.25  tff(c_8, plain, (![B_5, A_4]: (~v1_xboole_0(k2_xboole_0(B_5, A_4)) | v1_xboole_0(A_4))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.15/1.25  tff(c_165, plain, (~v1_xboole_0(k1_xboole_0) | v1_xboole_0('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_148, c_8])).
% 2.15/1.25  tff(c_172, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_165])).
% 2.15/1.25  tff(c_6, plain, (![A_3]: (k1_xboole_0=A_3 | ~v1_xboole_0(A_3))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.15/1.25  tff(c_178, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_172, c_6])).
% 2.15/1.25  tff(c_14, plain, (![A_8]: (r1_tarski(k1_xboole_0, A_8))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.15/1.25  tff(c_186, plain, (![A_8]: (r1_tarski('#skF_4', A_8))), inference(demodulation, [status(thm), theory('equality')], [c_178, c_14])).
% 2.15/1.25  tff(c_12, plain, (![A_6, B_7]: (k4_xboole_0(A_6, B_7)=k1_xboole_0 | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.15/1.25  tff(c_288, plain, (![A_68, B_69]: (k4_xboole_0(A_68, B_69)='#skF_4' | ~r1_tarski(A_68, B_69))), inference(demodulation, [status(thm), theory('equality')], [c_178, c_12])).
% 2.15/1.25  tff(c_292, plain, (![A_8]: (k4_xboole_0('#skF_4', A_8)='#skF_4')), inference(resolution, [status(thm)], [c_186, c_288])).
% 2.15/1.25  tff(c_338, plain, (![A_74, B_75]: (r1_xboole_0(A_74, B_75) | k4_xboole_0(A_74, B_75)!=A_74)), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.15/1.25  tff(c_30, plain, (![D_24, A_19]: (r2_hidden(D_24, k2_tarski(A_19, D_24)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.15/1.25  tff(c_181, plain, (k1_tarski('#skF_3')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_178, c_140])).
% 2.15/1.25  tff(c_256, plain, (![A_64, B_65]: (~r2_hidden(A_64, B_65) | ~r1_xboole_0(k1_tarski(A_64), B_65))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.15/1.25  tff(c_260, plain, (![B_66]: (~r2_hidden('#skF_3', B_66) | ~r1_xboole_0('#skF_4', B_66))), inference(superposition, [status(thm), theory('equality')], [c_181, c_256])).
% 2.15/1.25  tff(c_280, plain, (![A_19]: (~r1_xboole_0('#skF_4', k2_tarski(A_19, '#skF_3')))), inference(resolution, [status(thm)], [c_30, c_260])).
% 2.15/1.25  tff(c_341, plain, (![A_19]: (k4_xboole_0('#skF_4', k2_tarski(A_19, '#skF_3'))!='#skF_4')), inference(resolution, [status(thm)], [c_338, c_280])).
% 2.15/1.25  tff(c_358, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_292, c_341])).
% 2.15/1.25  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.15/1.25  
% 2.15/1.25  Inference rules
% 2.15/1.25  ----------------------
% 2.15/1.25  #Ref     : 0
% 2.15/1.25  #Sup     : 71
% 2.15/1.25  #Fact    : 0
% 2.15/1.25  #Define  : 0
% 2.15/1.25  #Split   : 0
% 2.15/1.25  #Chain   : 0
% 2.15/1.25  #Close   : 0
% 2.15/1.25  
% 2.15/1.25  Ordering : KBO
% 2.15/1.25  
% 2.15/1.25  Simplification rules
% 2.15/1.25  ----------------------
% 2.15/1.25  #Subsume      : 3
% 2.15/1.25  #Demod        : 27
% 2.15/1.25  #Tautology    : 54
% 2.15/1.25  #SimpNegUnit  : 0
% 2.15/1.25  #BackRed      : 11
% 2.15/1.25  
% 2.15/1.25  #Partial instantiations: 0
% 2.15/1.25  #Strategies tried      : 1
% 2.15/1.25  
% 2.15/1.25  Timing (in seconds)
% 2.15/1.25  ----------------------
% 2.15/1.26  Preprocessing        : 0.31
% 2.15/1.26  Parsing              : 0.16
% 2.15/1.26  CNF conversion       : 0.02
% 2.15/1.26  Main loop            : 0.18
% 2.15/1.26  Inferencing          : 0.06
% 2.15/1.26  Reduction            : 0.06
% 2.15/1.26  Demodulation         : 0.04
% 2.15/1.26  BG Simplification    : 0.01
% 2.15/1.26  Subsumption          : 0.03
% 2.15/1.26  Abstraction          : 0.01
% 2.15/1.26  MUC search           : 0.00
% 2.15/1.26  Cooper               : 0.00
% 2.15/1.26  Total                : 0.52
% 2.15/1.26  Index Insertion      : 0.00
% 2.15/1.26  Index Deletion       : 0.00
% 2.15/1.26  Index Matching       : 0.00
% 2.15/1.26  BG Taut test         : 0.00
%------------------------------------------------------------------------------
