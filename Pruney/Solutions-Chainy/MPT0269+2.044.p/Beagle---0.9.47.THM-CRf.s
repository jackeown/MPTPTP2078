%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:52:49 EST 2020

% Result     : Theorem 2.87s
% Output     : CNFRefutation 2.87s
% Verified   : 
% Statistics : Number of formulae       :   60 (  66 expanded)
%              Number of leaves         :   32 (  36 expanded)
%              Depth                    :   11
%              Number of atoms          :   48 (  60 expanded)
%              Number of equality atoms :   40 (  52 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
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

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(f_74,negated_conjecture,(
    ~ ! [A,B] :
        ~ ( k4_xboole_0(A,k1_tarski(B)) = k1_xboole_0
          & A != k1_xboole_0
          & A != k1_tarski(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_zfmisc_1)).

tff(f_64,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,k1_tarski(B)) = A
    <=> ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_zfmisc_1)).

tff(f_31,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

tff(f_29,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_59,axiom,(
    ! [A] : k3_tarski(k1_tarski(A)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_zfmisc_1)).

tff(f_39,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_57,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_35,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k5_xboole_0(k5_xboole_0(A,B),k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_xboole_1)).

tff(f_33,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => k3_xboole_0(B,k1_tarski(A)) = k1_tarski(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l31_zfmisc_1)).

tff(c_38,plain,(
    k1_tarski('#skF_2') != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_40,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_131,plain,(
    ! [A_57,B_58] :
      ( k4_xboole_0(A_57,k1_tarski(B_58)) = A_57
      | r2_hidden(B_58,A_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_42,plain,(
    k4_xboole_0('#skF_1',k1_tarski('#skF_2')) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_137,plain,
    ( k1_xboole_0 = '#skF_1'
    | r2_hidden('#skF_2','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_131,c_42])).

tff(c_145,plain,(
    r2_hidden('#skF_2','#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_137])).

tff(c_6,plain,(
    ! [A_5] : k5_xboole_0(A_5,k1_xboole_0) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_4,plain,(
    ! [A_3,B_4] : k5_xboole_0(A_3,k3_xboole_0(A_3,B_4)) = k4_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_32,plain,(
    ! [A_44] : k3_tarski(k1_tarski(A_44)) = A_44 ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_14,plain,(
    ! [A_12] : k2_tarski(A_12,A_12) = k1_tarski(A_12) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_100,plain,(
    ! [A_52,B_53] : k3_tarski(k2_tarski(A_52,B_53)) = k2_xboole_0(A_52,B_53) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_109,plain,(
    ! [A_12] : k3_tarski(k1_tarski(A_12)) = k2_xboole_0(A_12,A_12) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_100])).

tff(c_112,plain,(
    ! [A_12] : k2_xboole_0(A_12,A_12) = A_12 ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_109])).

tff(c_2,plain,(
    ! [A_1] : k3_xboole_0(A_1,A_1) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_10,plain,(
    ! [A_9] : k5_xboole_0(A_9,A_9) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_382,plain,(
    ! [A_77,B_78] : k5_xboole_0(k5_xboole_0(A_77,B_78),k2_xboole_0(A_77,B_78)) = k3_xboole_0(A_77,B_78) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_428,plain,(
    ! [A_9] : k5_xboole_0(k1_xboole_0,k2_xboole_0(A_9,A_9)) = k3_xboole_0(A_9,A_9) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_382])).

tff(c_432,plain,(
    ! [A_9] : k5_xboole_0(k1_xboole_0,A_9) = A_9 ),
    inference(demodulation,[status(thm),theory(equality)],[c_112,c_2,c_428])).

tff(c_228,plain,(
    ! [A_71,B_72,C_73] : k5_xboole_0(k5_xboole_0(A_71,B_72),C_73) = k5_xboole_0(A_71,k5_xboole_0(B_72,C_73)) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_269,plain,(
    ! [A_9,C_73] : k5_xboole_0(A_9,k5_xboole_0(A_9,C_73)) = k5_xboole_0(k1_xboole_0,C_73) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_228])).

tff(c_541,plain,(
    ! [A_85,C_86] : k5_xboole_0(A_85,k5_xboole_0(A_85,C_86)) = C_86 ),
    inference(demodulation,[status(thm),theory(equality)],[c_432,c_269])).

tff(c_1224,plain,(
    ! [A_116,B_117] : k5_xboole_0(A_116,k4_xboole_0(A_116,B_117)) = k3_xboole_0(A_116,B_117) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_541])).

tff(c_1279,plain,(
    k3_xboole_0('#skF_1',k1_tarski('#skF_2')) = k5_xboole_0('#skF_1',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_1224])).

tff(c_1289,plain,(
    k3_xboole_0('#skF_1',k1_tarski('#skF_2')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_1279])).

tff(c_28,plain,(
    ! [B_41,A_40] :
      ( k3_xboole_0(B_41,k1_tarski(A_40)) = k1_tarski(A_40)
      | ~ r2_hidden(A_40,B_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_1293,plain,
    ( k1_tarski('#skF_2') = '#skF_1'
    | ~ r2_hidden('#skF_2','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_1289,c_28])).

tff(c_1303,plain,(
    k1_tarski('#skF_2') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_145,c_1293])).

tff(c_1305,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_1303])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.00/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n019.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 12:46:52 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.87/1.41  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.87/1.41  
% 2.87/1.41  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.87/1.41  %$ r2_hidden > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1
% 2.87/1.41  
% 2.87/1.41  %Foreground sorts:
% 2.87/1.41  
% 2.87/1.41  
% 2.87/1.41  %Background operators:
% 2.87/1.41  
% 2.87/1.41  
% 2.87/1.41  %Foreground operators:
% 2.87/1.41  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.87/1.41  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.87/1.41  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.87/1.41  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.87/1.41  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.87/1.41  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.87/1.41  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.87/1.41  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.87/1.41  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.87/1.41  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.87/1.41  tff('#skF_2', type, '#skF_2': $i).
% 2.87/1.41  tff('#skF_1', type, '#skF_1': $i).
% 2.87/1.41  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.87/1.41  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.87/1.41  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.87/1.41  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.87/1.41  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.87/1.41  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.87/1.41  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.87/1.41  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.87/1.41  
% 2.87/1.43  tff(f_74, negated_conjecture, ~(![A, B]: ~(((k4_xboole_0(A, k1_tarski(B)) = k1_xboole_0) & ~(A = k1_xboole_0)) & ~(A = k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t66_zfmisc_1)).
% 2.87/1.43  tff(f_64, axiom, (![A, B]: ((k4_xboole_0(A, k1_tarski(B)) = A) <=> ~r2_hidden(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_zfmisc_1)).
% 2.87/1.43  tff(f_31, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 2.87/1.43  tff(f_29, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 2.87/1.43  tff(f_59, axiom, (![A]: (k3_tarski(k1_tarski(A)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_zfmisc_1)).
% 2.87/1.43  tff(f_39, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 2.87/1.43  tff(f_57, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 2.87/1.43  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 2.87/1.43  tff(f_35, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t92_xboole_1)).
% 2.87/1.43  tff(f_37, axiom, (![A, B]: (k3_xboole_0(A, B) = k5_xboole_0(k5_xboole_0(A, B), k2_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t95_xboole_1)).
% 2.87/1.43  tff(f_33, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_xboole_1)).
% 2.87/1.43  tff(f_55, axiom, (![A, B]: (r2_hidden(A, B) => (k3_xboole_0(B, k1_tarski(A)) = k1_tarski(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l31_zfmisc_1)).
% 2.87/1.43  tff(c_38, plain, (k1_tarski('#skF_2')!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.87/1.43  tff(c_40, plain, (k1_xboole_0!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.87/1.43  tff(c_131, plain, (![A_57, B_58]: (k4_xboole_0(A_57, k1_tarski(B_58))=A_57 | r2_hidden(B_58, A_57))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.87/1.43  tff(c_42, plain, (k4_xboole_0('#skF_1', k1_tarski('#skF_2'))=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.87/1.43  tff(c_137, plain, (k1_xboole_0='#skF_1' | r2_hidden('#skF_2', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_131, c_42])).
% 2.87/1.43  tff(c_145, plain, (r2_hidden('#skF_2', '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_40, c_137])).
% 2.87/1.43  tff(c_6, plain, (![A_5]: (k5_xboole_0(A_5, k1_xboole_0)=A_5)), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.87/1.43  tff(c_4, plain, (![A_3, B_4]: (k5_xboole_0(A_3, k3_xboole_0(A_3, B_4))=k4_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.87/1.43  tff(c_32, plain, (![A_44]: (k3_tarski(k1_tarski(A_44))=A_44)), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.87/1.43  tff(c_14, plain, (![A_12]: (k2_tarski(A_12, A_12)=k1_tarski(A_12))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.87/1.43  tff(c_100, plain, (![A_52, B_53]: (k3_tarski(k2_tarski(A_52, B_53))=k2_xboole_0(A_52, B_53))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.87/1.43  tff(c_109, plain, (![A_12]: (k3_tarski(k1_tarski(A_12))=k2_xboole_0(A_12, A_12))), inference(superposition, [status(thm), theory('equality')], [c_14, c_100])).
% 2.87/1.43  tff(c_112, plain, (![A_12]: (k2_xboole_0(A_12, A_12)=A_12)), inference(demodulation, [status(thm), theory('equality')], [c_32, c_109])).
% 2.87/1.43  tff(c_2, plain, (![A_1]: (k3_xboole_0(A_1, A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.87/1.43  tff(c_10, plain, (![A_9]: (k5_xboole_0(A_9, A_9)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.87/1.43  tff(c_382, plain, (![A_77, B_78]: (k5_xboole_0(k5_xboole_0(A_77, B_78), k2_xboole_0(A_77, B_78))=k3_xboole_0(A_77, B_78))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.87/1.43  tff(c_428, plain, (![A_9]: (k5_xboole_0(k1_xboole_0, k2_xboole_0(A_9, A_9))=k3_xboole_0(A_9, A_9))), inference(superposition, [status(thm), theory('equality')], [c_10, c_382])).
% 2.87/1.43  tff(c_432, plain, (![A_9]: (k5_xboole_0(k1_xboole_0, A_9)=A_9)), inference(demodulation, [status(thm), theory('equality')], [c_112, c_2, c_428])).
% 2.87/1.43  tff(c_228, plain, (![A_71, B_72, C_73]: (k5_xboole_0(k5_xboole_0(A_71, B_72), C_73)=k5_xboole_0(A_71, k5_xboole_0(B_72, C_73)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.87/1.43  tff(c_269, plain, (![A_9, C_73]: (k5_xboole_0(A_9, k5_xboole_0(A_9, C_73))=k5_xboole_0(k1_xboole_0, C_73))), inference(superposition, [status(thm), theory('equality')], [c_10, c_228])).
% 2.87/1.43  tff(c_541, plain, (![A_85, C_86]: (k5_xboole_0(A_85, k5_xboole_0(A_85, C_86))=C_86)), inference(demodulation, [status(thm), theory('equality')], [c_432, c_269])).
% 2.87/1.43  tff(c_1224, plain, (![A_116, B_117]: (k5_xboole_0(A_116, k4_xboole_0(A_116, B_117))=k3_xboole_0(A_116, B_117))), inference(superposition, [status(thm), theory('equality')], [c_4, c_541])).
% 2.87/1.43  tff(c_1279, plain, (k3_xboole_0('#skF_1', k1_tarski('#skF_2'))=k5_xboole_0('#skF_1', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_42, c_1224])).
% 2.87/1.43  tff(c_1289, plain, (k3_xboole_0('#skF_1', k1_tarski('#skF_2'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_6, c_1279])).
% 2.87/1.43  tff(c_28, plain, (![B_41, A_40]: (k3_xboole_0(B_41, k1_tarski(A_40))=k1_tarski(A_40) | ~r2_hidden(A_40, B_41))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.87/1.43  tff(c_1293, plain, (k1_tarski('#skF_2')='#skF_1' | ~r2_hidden('#skF_2', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_1289, c_28])).
% 2.87/1.43  tff(c_1303, plain, (k1_tarski('#skF_2')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_145, c_1293])).
% 2.87/1.43  tff(c_1305, plain, $false, inference(negUnitSimplification, [status(thm)], [c_38, c_1303])).
% 2.87/1.43  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.87/1.43  
% 2.87/1.43  Inference rules
% 2.87/1.43  ----------------------
% 2.87/1.43  #Ref     : 0
% 2.87/1.43  #Sup     : 310
% 2.87/1.43  #Fact    : 0
% 2.87/1.43  #Define  : 0
% 2.87/1.43  #Split   : 0
% 2.87/1.43  #Chain   : 0
% 2.87/1.43  #Close   : 0
% 2.87/1.43  
% 2.87/1.43  Ordering : KBO
% 2.87/1.43  
% 2.87/1.43  Simplification rules
% 2.87/1.43  ----------------------
% 2.87/1.43  #Subsume      : 5
% 2.87/1.43  #Demod        : 160
% 2.87/1.43  #Tautology    : 200
% 2.87/1.43  #SimpNegUnit  : 3
% 2.87/1.43  #BackRed      : 2
% 2.87/1.43  
% 2.87/1.43  #Partial instantiations: 0
% 2.87/1.43  #Strategies tried      : 1
% 2.87/1.43  
% 2.87/1.43  Timing (in seconds)
% 2.87/1.43  ----------------------
% 2.87/1.43  Preprocessing        : 0.32
% 2.87/1.43  Parsing              : 0.17
% 2.87/1.43  CNF conversion       : 0.02
% 2.87/1.43  Main loop            : 0.37
% 2.87/1.43  Inferencing          : 0.15
% 2.87/1.43  Reduction            : 0.13
% 2.87/1.43  Demodulation         : 0.10
% 2.87/1.43  BG Simplification    : 0.02
% 2.87/1.43  Subsumption          : 0.05
% 2.87/1.43  Abstraction          : 0.02
% 2.87/1.43  MUC search           : 0.00
% 2.87/1.43  Cooper               : 0.00
% 2.87/1.43  Total                : 0.72
% 2.87/1.43  Index Insertion      : 0.00
% 2.87/1.43  Index Deletion       : 0.00
% 2.87/1.43  Index Matching       : 0.00
% 2.87/1.43  BG Taut test         : 0.00
%------------------------------------------------------------------------------
