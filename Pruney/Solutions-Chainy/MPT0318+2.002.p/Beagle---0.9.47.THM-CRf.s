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
% DateTime   : Thu Dec  3 09:54:02 EST 2020

% Result     : Theorem 2.17s
% Output     : CNFRefutation 2.31s
% Verified   : 
% Statistics : Number of formulae       :   58 ( 125 expanded)
%              Number of leaves         :   29 (  55 expanded)
%              Depth                    :    8
%              Number of atoms          :   56 ( 180 expanded)
%              Number of equality atoms :   36 ( 156 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_zfmisc_1 > k2_tarski > #nlpp > k3_tarski > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_3 > #skF_4 > #skF_2 > #skF_1

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

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_61,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_77,negated_conjecture,(
    ~ ! [A,B] :
        ( A != k1_xboole_0
       => ( k2_zfmisc_1(k1_tarski(B),A) != k1_xboole_0
          & k2_zfmisc_1(A,k1_tarski(B)) != k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t130_zfmisc_1)).

tff(f_65,axiom,(
    ! [A] : k3_tarski(k1_tarski(A)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_zfmisc_1)).

tff(f_63,axiom,(
    k3_tarski(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_zfmisc_1)).

tff(f_32,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_62,axiom,(
    k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_zfmisc_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_30,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',antisymmetry_r2_hidden)).

tff(c_38,plain,(
    ! [B_39] : k2_zfmisc_1(k1_xboole_0,B_39) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_50,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_48,plain,
    ( k2_zfmisc_1('#skF_3',k1_tarski('#skF_4')) = k1_xboole_0
    | k2_zfmisc_1(k1_tarski('#skF_4'),'#skF_3') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_113,plain,(
    k2_zfmisc_1(k1_tarski('#skF_4'),'#skF_3') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_48])).

tff(c_203,plain,(
    ! [B_64,A_65] :
      ( k1_xboole_0 = B_64
      | k1_xboole_0 = A_65
      | k2_zfmisc_1(A_65,B_64) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_206,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_tarski('#skF_4') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_113,c_203])).

tff(c_215,plain,(
    k1_tarski('#skF_4') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_206])).

tff(c_44,plain,(
    ! [A_40] : k3_tarski(k1_tarski(A_40)) = A_40 ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_228,plain,(
    k3_tarski(k1_xboole_0) = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_215,c_44])).

tff(c_42,plain,(
    k3_tarski(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_233,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_228,c_42])).

tff(c_4,plain,(
    ! [A_3] : r1_tarski(k1_xboole_0,A_3) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_252,plain,(
    ! [A_3] : r1_tarski('#skF_4',A_3) ),
    inference(demodulation,[status(thm),theory(equality)],[c_233,c_4])).

tff(c_243,plain,(
    k1_tarski('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_233,c_215])).

tff(c_40,plain,(
    k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_145,plain,(
    ! [C_53,A_54] :
      ( r2_hidden(C_53,k1_zfmisc_1(A_54))
      | ~ r1_tarski(C_53,A_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_150,plain,(
    ! [C_53] :
      ( r2_hidden(C_53,k1_tarski(k1_xboole_0))
      | ~ r1_tarski(C_53,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_145])).

tff(c_169,plain,(
    ! [C_59] :
      ( r2_hidden(C_59,k1_tarski(k1_xboole_0))
      | ~ r1_tarski(C_59,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_145])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( ~ r2_hidden(B_2,A_1)
      | ~ r2_hidden(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_192,plain,(
    ! [C_63] :
      ( ~ r2_hidden(k1_tarski(k1_xboole_0),C_63)
      | ~ r1_tarski(C_63,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_169,c_2])).

tff(c_201,plain,(
    ~ r1_tarski(k1_tarski(k1_xboole_0),k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_150,c_192])).

tff(c_341,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_252,c_243,c_233,c_233,c_201])).

tff(c_342,plain,(
    k2_zfmisc_1('#skF_3',k1_tarski('#skF_4')) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_433,plain,(
    ! [B_88,A_89] :
      ( k1_xboole_0 = B_88
      | k1_xboole_0 = A_89
      | k2_zfmisc_1(A_89,B_88) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_436,plain,
    ( k1_tarski('#skF_4') = k1_xboole_0
    | k1_xboole_0 = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_342,c_433])).

tff(c_445,plain,(
    k1_tarski('#skF_4') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_436])).

tff(c_343,plain,(
    k2_zfmisc_1(k1_tarski('#skF_4'),'#skF_3') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_450,plain,(
    k2_zfmisc_1(k1_xboole_0,'#skF_3') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_445,c_343])).

tff(c_454,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_450])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.11  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.10/0.32  % Computer   : n005.cluster.edu
% 0.10/0.32  % Model      : x86_64 x86_64
% 0.10/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.10/0.32  % Memory     : 8042.1875MB
% 0.10/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.10/0.32  % CPULimit   : 60
% 0.10/0.32  % DateTime   : Tue Dec  1 12:20:47 EST 2020
% 0.10/0.32  % CPUTime    : 
% 0.10/0.32  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.17/1.22  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.17/1.23  
% 2.17/1.23  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.17/1.23  %$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_zfmisc_1 > k2_tarski > #nlpp > k3_tarski > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 2.17/1.23  
% 2.17/1.23  %Foreground sorts:
% 2.17/1.23  
% 2.17/1.23  
% 2.17/1.23  %Background operators:
% 2.17/1.23  
% 2.17/1.23  
% 2.17/1.23  %Foreground operators:
% 2.17/1.23  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.17/1.23  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.17/1.23  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.17/1.23  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.17/1.23  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.17/1.23  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.17/1.23  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.17/1.23  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.17/1.23  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.17/1.23  tff('#skF_3', type, '#skF_3': $i).
% 2.17/1.23  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.17/1.23  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.17/1.23  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.17/1.23  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.17/1.23  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.17/1.23  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.17/1.23  tff('#skF_4', type, '#skF_4': $i).
% 2.17/1.23  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.17/1.23  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.17/1.23  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.17/1.23  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.17/1.23  
% 2.31/1.24  tff(f_61, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 2.31/1.24  tff(f_77, negated_conjecture, ~(![A, B]: (~(A = k1_xboole_0) => (~(k2_zfmisc_1(k1_tarski(B), A) = k1_xboole_0) & ~(k2_zfmisc_1(A, k1_tarski(B)) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t130_zfmisc_1)).
% 2.31/1.24  tff(f_65, axiom, (![A]: (k3_tarski(k1_tarski(A)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_zfmisc_1)).
% 2.31/1.24  tff(f_63, axiom, (k3_tarski(k1_xboole_0) = k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_zfmisc_1)).
% 2.31/1.24  tff(f_32, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.31/1.24  tff(f_62, axiom, (k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_zfmisc_1)).
% 2.31/1.24  tff(f_53, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 2.31/1.24  tff(f_30, axiom, (![A, B]: (r2_hidden(A, B) => ~r2_hidden(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', antisymmetry_r2_hidden)).
% 2.31/1.24  tff(c_38, plain, (![B_39]: (k2_zfmisc_1(k1_xboole_0, B_39)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.31/1.24  tff(c_50, plain, (k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.31/1.24  tff(c_48, plain, (k2_zfmisc_1('#skF_3', k1_tarski('#skF_4'))=k1_xboole_0 | k2_zfmisc_1(k1_tarski('#skF_4'), '#skF_3')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.31/1.24  tff(c_113, plain, (k2_zfmisc_1(k1_tarski('#skF_4'), '#skF_3')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_48])).
% 2.31/1.24  tff(c_203, plain, (![B_64, A_65]: (k1_xboole_0=B_64 | k1_xboole_0=A_65 | k2_zfmisc_1(A_65, B_64)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.31/1.24  tff(c_206, plain, (k1_xboole_0='#skF_3' | k1_tarski('#skF_4')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_113, c_203])).
% 2.31/1.24  tff(c_215, plain, (k1_tarski('#skF_4')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_50, c_206])).
% 2.31/1.24  tff(c_44, plain, (![A_40]: (k3_tarski(k1_tarski(A_40))=A_40)), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.31/1.24  tff(c_228, plain, (k3_tarski(k1_xboole_0)='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_215, c_44])).
% 2.31/1.24  tff(c_42, plain, (k3_tarski(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.31/1.24  tff(c_233, plain, (k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_228, c_42])).
% 2.31/1.24  tff(c_4, plain, (![A_3]: (r1_tarski(k1_xboole_0, A_3))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.31/1.24  tff(c_252, plain, (![A_3]: (r1_tarski('#skF_4', A_3))), inference(demodulation, [status(thm), theory('equality')], [c_233, c_4])).
% 2.31/1.24  tff(c_243, plain, (k1_tarski('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_233, c_215])).
% 2.31/1.24  tff(c_40, plain, (k1_zfmisc_1(k1_xboole_0)=k1_tarski(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.31/1.24  tff(c_145, plain, (![C_53, A_54]: (r2_hidden(C_53, k1_zfmisc_1(A_54)) | ~r1_tarski(C_53, A_54))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.31/1.24  tff(c_150, plain, (![C_53]: (r2_hidden(C_53, k1_tarski(k1_xboole_0)) | ~r1_tarski(C_53, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_40, c_145])).
% 2.31/1.24  tff(c_169, plain, (![C_59]: (r2_hidden(C_59, k1_tarski(k1_xboole_0)) | ~r1_tarski(C_59, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_40, c_145])).
% 2.31/1.24  tff(c_2, plain, (![B_2, A_1]: (~r2_hidden(B_2, A_1) | ~r2_hidden(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_30])).
% 2.31/1.24  tff(c_192, plain, (![C_63]: (~r2_hidden(k1_tarski(k1_xboole_0), C_63) | ~r1_tarski(C_63, k1_xboole_0))), inference(resolution, [status(thm)], [c_169, c_2])).
% 2.31/1.24  tff(c_201, plain, (~r1_tarski(k1_tarski(k1_xboole_0), k1_xboole_0)), inference(resolution, [status(thm)], [c_150, c_192])).
% 2.31/1.24  tff(c_341, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_252, c_243, c_233, c_233, c_201])).
% 2.31/1.24  tff(c_342, plain, (k2_zfmisc_1('#skF_3', k1_tarski('#skF_4'))=k1_xboole_0), inference(splitRight, [status(thm)], [c_48])).
% 2.31/1.24  tff(c_433, plain, (![B_88, A_89]: (k1_xboole_0=B_88 | k1_xboole_0=A_89 | k2_zfmisc_1(A_89, B_88)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.31/1.24  tff(c_436, plain, (k1_tarski('#skF_4')=k1_xboole_0 | k1_xboole_0='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_342, c_433])).
% 2.31/1.24  tff(c_445, plain, (k1_tarski('#skF_4')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_50, c_436])).
% 2.31/1.24  tff(c_343, plain, (k2_zfmisc_1(k1_tarski('#skF_4'), '#skF_3')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_48])).
% 2.31/1.24  tff(c_450, plain, (k2_zfmisc_1(k1_xboole_0, '#skF_3')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_445, c_343])).
% 2.31/1.24  tff(c_454, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_38, c_450])).
% 2.31/1.24  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.31/1.24  
% 2.31/1.24  Inference rules
% 2.31/1.24  ----------------------
% 2.31/1.24  #Ref     : 0
% 2.31/1.24  #Sup     : 98
% 2.31/1.24  #Fact    : 0
% 2.31/1.24  #Define  : 0
% 2.31/1.24  #Split   : 1
% 2.31/1.24  #Chain   : 0
% 2.31/1.24  #Close   : 0
% 2.31/1.24  
% 2.31/1.24  Ordering : KBO
% 2.31/1.24  
% 2.31/1.24  Simplification rules
% 2.31/1.24  ----------------------
% 2.31/1.24  #Subsume      : 0
% 2.31/1.24  #Demod        : 55
% 2.31/1.24  #Tautology    : 69
% 2.31/1.24  #SimpNegUnit  : 2
% 2.31/1.24  #BackRed      : 16
% 2.31/1.24  
% 2.31/1.24  #Partial instantiations: 0
% 2.31/1.24  #Strategies tried      : 1
% 2.31/1.24  
% 2.31/1.24  Timing (in seconds)
% 2.31/1.24  ----------------------
% 2.31/1.24  Preprocessing        : 0.34
% 2.31/1.24  Parsing              : 0.17
% 2.31/1.25  CNF conversion       : 0.02
% 2.31/1.25  Main loop            : 0.23
% 2.31/1.25  Inferencing          : 0.08
% 2.31/1.25  Reduction            : 0.08
% 2.31/1.25  Demodulation         : 0.06
% 2.31/1.25  BG Simplification    : 0.02
% 2.31/1.25  Subsumption          : 0.04
% 2.31/1.25  Abstraction          : 0.01
% 2.31/1.25  MUC search           : 0.00
% 2.31/1.25  Cooper               : 0.00
% 2.31/1.25  Total                : 0.59
% 2.31/1.25  Index Insertion      : 0.00
% 2.31/1.25  Index Deletion       : 0.00
% 2.31/1.25  Index Matching       : 0.00
% 2.31/1.25  BG Taut test         : 0.00
%------------------------------------------------------------------------------
