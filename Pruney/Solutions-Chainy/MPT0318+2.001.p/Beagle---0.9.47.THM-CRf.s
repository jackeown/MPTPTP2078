%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:54:02 EST 2020

% Result     : Theorem 2.19s
% Output     : CNFRefutation 2.19s
% Verified   : 
% Statistics : Number of formulae       :   69 ( 252 expanded)
%              Number of leaves         :   32 (  96 expanded)
%              Depth                    :   13
%              Number of atoms          :   67 ( 356 expanded)
%              Number of equality atoms :   44 ( 328 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_3 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_65,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_79,negated_conjecture,(
    ~ ! [A,B] :
        ( A != k1_xboole_0
       => ( k2_zfmisc_1(k1_tarski(B),A) != k1_xboole_0
          & k2_zfmisc_1(A,k1_tarski(B)) != k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t130_zfmisc_1)).

tff(f_32,axiom,(
    ! [A,B] : k2_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

tff(f_36,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_57,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_67,axiom,(
    k3_tarski(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_zfmisc_1)).

tff(f_34,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_66,axiom,(
    k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_zfmisc_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_30,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',antisymmetry_r2_hidden)).

tff(c_42,plain,(
    ! [B_43] : k2_zfmisc_1(k1_xboole_0,B_43) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_52,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_50,plain,
    ( k2_zfmisc_1('#skF_3',k1_tarski('#skF_4')) = k1_xboole_0
    | k2_zfmisc_1(k1_tarski('#skF_4'),'#skF_3') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_109,plain,(
    k2_zfmisc_1(k1_tarski('#skF_4'),'#skF_3') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_50])).

tff(c_214,plain,(
    ! [B_67,A_68] :
      ( k1_xboole_0 = B_67
      | k1_xboole_0 = A_68
      | k2_zfmisc_1(A_68,B_67) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_217,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_tarski('#skF_4') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_109,c_214])).

tff(c_226,plain,(
    k1_tarski('#skF_4') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_217])).

tff(c_4,plain,(
    ! [A_3] : k2_xboole_0(A_3,A_3) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_8,plain,(
    ! [A_6] : k2_tarski(A_6,A_6) = k1_tarski(A_6) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_171,plain,(
    ! [A_61,B_62] : k3_tarski(k2_tarski(A_61,B_62)) = k2_xboole_0(A_61,B_62) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_183,plain,(
    ! [A_6] : k3_tarski(k1_tarski(A_6)) = k2_xboole_0(A_6,A_6) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_171])).

tff(c_186,plain,(
    ! [A_6] : k3_tarski(k1_tarski(A_6)) = A_6 ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_183])).

tff(c_239,plain,(
    k3_tarski(k1_xboole_0) = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_226,c_186])).

tff(c_46,plain,(
    k3_tarski(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_244,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_239,c_46])).

tff(c_6,plain,(
    ! [A_5] : r1_tarski(k1_xboole_0,A_5) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_260,plain,(
    ! [A_5] : r1_tarski('#skF_4',A_5) ),
    inference(demodulation,[status(thm),theory(equality)],[c_244,c_6])).

tff(c_254,plain,(
    k1_tarski('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_244,c_226])).

tff(c_44,plain,(
    k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_259,plain,(
    k1_zfmisc_1('#skF_4') = k1_tarski('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_244,c_244,c_44])).

tff(c_303,plain,(
    k1_zfmisc_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_254,c_259])).

tff(c_24,plain,(
    ! [C_38,A_34] :
      ( r2_hidden(C_38,k1_zfmisc_1(A_34))
      | ~ r1_tarski(C_38,A_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_358,plain,(
    ! [C_79] :
      ( r2_hidden(C_79,'#skF_4')
      | ~ r1_tarski(C_79,'#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_303,c_24])).

tff(c_147,plain,(
    ! [C_55,A_56] :
      ( r2_hidden(C_55,k1_zfmisc_1(A_56))
      | ~ r1_tarski(C_55,A_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( ~ r2_hidden(B_2,A_1)
      | ~ r2_hidden(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_153,plain,(
    ! [A_56,C_55] :
      ( ~ r2_hidden(k1_zfmisc_1(A_56),C_55)
      | ~ r1_tarski(C_55,A_56) ) ),
    inference(resolution,[status(thm)],[c_147,c_2])).

tff(c_362,plain,(
    ! [A_56] :
      ( ~ r1_tarski('#skF_4',A_56)
      | ~ r1_tarski(k1_zfmisc_1(A_56),'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_358,c_153])).

tff(c_369,plain,(
    ! [A_80] : ~ r1_tarski(k1_zfmisc_1(A_80),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_260,c_362])).

tff(c_371,plain,(
    ~ r1_tarski('#skF_4','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_303,c_369])).

tff(c_374,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_260,c_371])).

tff(c_375,plain,(
    k2_zfmisc_1('#skF_3',k1_tarski('#skF_4')) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_454,plain,(
    ! [B_94,A_95] :
      ( k1_xboole_0 = B_94
      | k1_xboole_0 = A_95
      | k2_zfmisc_1(A_95,B_94) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_457,plain,
    ( k1_tarski('#skF_4') = k1_xboole_0
    | k1_xboole_0 = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_375,c_454])).

tff(c_466,plain,(
    k1_tarski('#skF_4') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_457])).

tff(c_376,plain,(
    k2_zfmisc_1(k1_tarski('#skF_4'),'#skF_3') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_471,plain,(
    k2_zfmisc_1(k1_xboole_0,'#skF_3') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_466,c_376])).

tff(c_475,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_471])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n023.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 18:58:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.19/1.28  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.19/1.29  
% 2.19/1.29  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.19/1.29  %$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 2.19/1.29  
% 2.19/1.29  %Foreground sorts:
% 2.19/1.29  
% 2.19/1.29  
% 2.19/1.29  %Background operators:
% 2.19/1.29  
% 2.19/1.29  
% 2.19/1.29  %Foreground operators:
% 2.19/1.29  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.19/1.29  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.19/1.29  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.19/1.29  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.19/1.29  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.19/1.29  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.19/1.29  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.19/1.29  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.19/1.29  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.19/1.29  tff('#skF_3', type, '#skF_3': $i).
% 2.19/1.29  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.19/1.29  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.19/1.29  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.19/1.29  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.19/1.29  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.19/1.29  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.19/1.29  tff('#skF_4', type, '#skF_4': $i).
% 2.19/1.29  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.19/1.29  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.19/1.29  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.19/1.29  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.19/1.29  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.19/1.29  
% 2.19/1.30  tff(f_65, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 2.19/1.30  tff(f_79, negated_conjecture, ~(![A, B]: (~(A = k1_xboole_0) => (~(k2_zfmisc_1(k1_tarski(B), A) = k1_xboole_0) & ~(k2_zfmisc_1(A, k1_tarski(B)) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t130_zfmisc_1)).
% 2.19/1.30  tff(f_32, axiom, (![A, B]: (k2_xboole_0(A, A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k2_xboole_0)).
% 2.19/1.30  tff(f_36, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 2.19/1.30  tff(f_57, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 2.19/1.30  tff(f_67, axiom, (k3_tarski(k1_xboole_0) = k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_zfmisc_1)).
% 2.19/1.30  tff(f_34, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.19/1.30  tff(f_66, axiom, (k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_zfmisc_1)).
% 2.19/1.30  tff(f_55, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 2.19/1.30  tff(f_30, axiom, (![A, B]: (r2_hidden(A, B) => ~r2_hidden(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', antisymmetry_r2_hidden)).
% 2.19/1.30  tff(c_42, plain, (![B_43]: (k2_zfmisc_1(k1_xboole_0, B_43)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.19/1.30  tff(c_52, plain, (k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.19/1.30  tff(c_50, plain, (k2_zfmisc_1('#skF_3', k1_tarski('#skF_4'))=k1_xboole_0 | k2_zfmisc_1(k1_tarski('#skF_4'), '#skF_3')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.19/1.30  tff(c_109, plain, (k2_zfmisc_1(k1_tarski('#skF_4'), '#skF_3')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_50])).
% 2.19/1.30  tff(c_214, plain, (![B_67, A_68]: (k1_xboole_0=B_67 | k1_xboole_0=A_68 | k2_zfmisc_1(A_68, B_67)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.19/1.30  tff(c_217, plain, (k1_xboole_0='#skF_3' | k1_tarski('#skF_4')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_109, c_214])).
% 2.19/1.30  tff(c_226, plain, (k1_tarski('#skF_4')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_52, c_217])).
% 2.19/1.30  tff(c_4, plain, (![A_3]: (k2_xboole_0(A_3, A_3)=A_3)), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.19/1.30  tff(c_8, plain, (![A_6]: (k2_tarski(A_6, A_6)=k1_tarski(A_6))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.19/1.30  tff(c_171, plain, (![A_61, B_62]: (k3_tarski(k2_tarski(A_61, B_62))=k2_xboole_0(A_61, B_62))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.19/1.30  tff(c_183, plain, (![A_6]: (k3_tarski(k1_tarski(A_6))=k2_xboole_0(A_6, A_6))), inference(superposition, [status(thm), theory('equality')], [c_8, c_171])).
% 2.19/1.30  tff(c_186, plain, (![A_6]: (k3_tarski(k1_tarski(A_6))=A_6)), inference(demodulation, [status(thm), theory('equality')], [c_4, c_183])).
% 2.19/1.30  tff(c_239, plain, (k3_tarski(k1_xboole_0)='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_226, c_186])).
% 2.19/1.30  tff(c_46, plain, (k3_tarski(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.19/1.30  tff(c_244, plain, (k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_239, c_46])).
% 2.19/1.30  tff(c_6, plain, (![A_5]: (r1_tarski(k1_xboole_0, A_5))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.19/1.30  tff(c_260, plain, (![A_5]: (r1_tarski('#skF_4', A_5))), inference(demodulation, [status(thm), theory('equality')], [c_244, c_6])).
% 2.19/1.30  tff(c_254, plain, (k1_tarski('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_244, c_226])).
% 2.19/1.30  tff(c_44, plain, (k1_zfmisc_1(k1_xboole_0)=k1_tarski(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.19/1.30  tff(c_259, plain, (k1_zfmisc_1('#skF_4')=k1_tarski('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_244, c_244, c_44])).
% 2.19/1.30  tff(c_303, plain, (k1_zfmisc_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_254, c_259])).
% 2.19/1.30  tff(c_24, plain, (![C_38, A_34]: (r2_hidden(C_38, k1_zfmisc_1(A_34)) | ~r1_tarski(C_38, A_34))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.19/1.30  tff(c_358, plain, (![C_79]: (r2_hidden(C_79, '#skF_4') | ~r1_tarski(C_79, '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_303, c_24])).
% 2.19/1.30  tff(c_147, plain, (![C_55, A_56]: (r2_hidden(C_55, k1_zfmisc_1(A_56)) | ~r1_tarski(C_55, A_56))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.19/1.30  tff(c_2, plain, (![B_2, A_1]: (~r2_hidden(B_2, A_1) | ~r2_hidden(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_30])).
% 2.19/1.30  tff(c_153, plain, (![A_56, C_55]: (~r2_hidden(k1_zfmisc_1(A_56), C_55) | ~r1_tarski(C_55, A_56))), inference(resolution, [status(thm)], [c_147, c_2])).
% 2.19/1.30  tff(c_362, plain, (![A_56]: (~r1_tarski('#skF_4', A_56) | ~r1_tarski(k1_zfmisc_1(A_56), '#skF_4'))), inference(resolution, [status(thm)], [c_358, c_153])).
% 2.19/1.30  tff(c_369, plain, (![A_80]: (~r1_tarski(k1_zfmisc_1(A_80), '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_260, c_362])).
% 2.19/1.30  tff(c_371, plain, (~r1_tarski('#skF_4', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_303, c_369])).
% 2.19/1.30  tff(c_374, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_260, c_371])).
% 2.19/1.30  tff(c_375, plain, (k2_zfmisc_1('#skF_3', k1_tarski('#skF_4'))=k1_xboole_0), inference(splitRight, [status(thm)], [c_50])).
% 2.19/1.30  tff(c_454, plain, (![B_94, A_95]: (k1_xboole_0=B_94 | k1_xboole_0=A_95 | k2_zfmisc_1(A_95, B_94)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.19/1.30  tff(c_457, plain, (k1_tarski('#skF_4')=k1_xboole_0 | k1_xboole_0='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_375, c_454])).
% 2.19/1.30  tff(c_466, plain, (k1_tarski('#skF_4')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_52, c_457])).
% 2.19/1.30  tff(c_376, plain, (k2_zfmisc_1(k1_tarski('#skF_4'), '#skF_3')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_50])).
% 2.19/1.30  tff(c_471, plain, (k2_zfmisc_1(k1_xboole_0, '#skF_3')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_466, c_376])).
% 2.19/1.30  tff(c_475, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_42, c_471])).
% 2.19/1.30  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.19/1.30  
% 2.19/1.30  Inference rules
% 2.19/1.30  ----------------------
% 2.19/1.30  #Ref     : 0
% 2.19/1.30  #Sup     : 105
% 2.19/1.30  #Fact    : 0
% 2.19/1.30  #Define  : 0
% 2.19/1.30  #Split   : 1
% 2.19/1.30  #Chain   : 0
% 2.19/1.30  #Close   : 0
% 2.19/1.30  
% 2.19/1.30  Ordering : KBO
% 2.19/1.30  
% 2.19/1.30  Simplification rules
% 2.19/1.30  ----------------------
% 2.19/1.30  #Subsume      : 0
% 2.19/1.30  #Demod        : 54
% 2.19/1.30  #Tautology    : 81
% 2.19/1.30  #SimpNegUnit  : 2
% 2.19/1.30  #BackRed      : 13
% 2.19/1.30  
% 2.19/1.30  #Partial instantiations: 0
% 2.19/1.30  #Strategies tried      : 1
% 2.19/1.30  
% 2.19/1.30  Timing (in seconds)
% 2.19/1.30  ----------------------
% 2.19/1.31  Preprocessing        : 0.31
% 2.19/1.31  Parsing              : 0.16
% 2.19/1.31  CNF conversion       : 0.02
% 2.19/1.31  Main loop            : 0.21
% 2.19/1.31  Inferencing          : 0.07
% 2.19/1.31  Reduction            : 0.07
% 2.19/1.31  Demodulation         : 0.05
% 2.19/1.31  BG Simplification    : 0.02
% 2.19/1.31  Subsumption          : 0.04
% 2.19/1.31  Abstraction          : 0.01
% 2.19/1.31  MUC search           : 0.00
% 2.19/1.31  Cooper               : 0.00
% 2.19/1.31  Total                : 0.55
% 2.19/1.31  Index Insertion      : 0.00
% 2.19/1.31  Index Deletion       : 0.00
% 2.19/1.31  Index Matching       : 0.00
% 2.19/1.31  BG Taut test         : 0.00
%------------------------------------------------------------------------------
