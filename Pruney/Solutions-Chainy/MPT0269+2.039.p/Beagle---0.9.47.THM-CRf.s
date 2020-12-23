%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:52:49 EST 2020

% Result     : Theorem 2.52s
% Output     : CNFRefutation 2.52s
% Verified   : 
% Statistics : Number of formulae       :   54 (  63 expanded)
%              Number of leaves         :   28 (  33 expanded)
%              Depth                    :    9
%              Number of atoms          :   54 (  67 expanded)
%              Number of equality atoms :   47 (  60 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2 > #skF_4

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

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_81,negated_conjecture,(
    ~ ! [A,B] :
        ~ ( k4_xboole_0(A,k1_tarski(B)) = k1_xboole_0
          & A != k1_xboole_0
          & A != k1_tarski(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_zfmisc_1)).

tff(f_50,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_48,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

tff(f_29,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

tff(f_33,axiom,(
    ! [A,B] : k4_xboole_0(A,k2_xboole_0(A,B)) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).

tff(f_71,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,k1_tarski(B)) = A
    <=> ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_zfmisc_1)).

tff(f_31,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_35,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_66,axiom,(
    ! [A,B,C] :
      ~ ( k1_tarski(A) = k2_xboole_0(B,C)
        & B != C
        & B != k1_xboole_0
        & C != k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_zfmisc_1)).

tff(c_46,plain,(
    k1_tarski('#skF_4') != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_34,plain,(
    ! [A_18] : k2_tarski(A_18,A_18) = k1_tarski(A_18) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_99,plain,(
    ! [D_33,A_34] : r2_hidden(D_33,k2_tarski(A_34,D_33)) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_102,plain,(
    ! [A_18] : r2_hidden(A_18,k1_tarski(A_18)) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_99])).

tff(c_4,plain,(
    ! [A_3] : k2_xboole_0(A_3,k1_xboole_0) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_109,plain,(
    ! [A_38,B_39] : k4_xboole_0(A_38,k2_xboole_0(A_38,B_39)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_119,plain,(
    ! [A_3] : k4_xboole_0(A_3,A_3) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_109])).

tff(c_355,plain,(
    ! [B_54,A_55] :
      ( ~ r2_hidden(B_54,A_55)
      | k4_xboole_0(A_55,k1_tarski(B_54)) != A_55 ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_362,plain,(
    ! [B_54] :
      ( ~ r2_hidden(B_54,k1_tarski(B_54))
      | k1_tarski(B_54) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_119,c_355])).

tff(c_372,plain,(
    ! [B_54] : k1_tarski(B_54) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_362])).

tff(c_48,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_6,plain,(
    ! [A_4] : k4_xboole_0(A_4,k1_xboole_0) = A_4 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_161,plain,(
    ! [A_43,B_44] : k4_xboole_0(A_43,k4_xboole_0(A_43,B_44)) = k3_xboole_0(A_43,B_44) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_189,plain,(
    ! [A_4] : k4_xboole_0(A_4,A_4) = k3_xboole_0(A_4,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_161])).

tff(c_202,plain,(
    ! [A_4] : k3_xboole_0(A_4,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_119,c_189])).

tff(c_326,plain,(
    ! [A_52,B_53] : k5_xboole_0(A_52,k3_xboole_0(A_52,B_53)) = k4_xboole_0(A_52,B_53) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_341,plain,(
    ! [A_4] : k5_xboole_0(A_4,k1_xboole_0) = k4_xboole_0(A_4,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_202,c_326])).

tff(c_352,plain,(
    ! [A_4] : k5_xboole_0(A_4,k1_xboole_0) = A_4 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_341])).

tff(c_50,plain,(
    k4_xboole_0('#skF_3',k1_tarski('#skF_4')) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_415,plain,(
    ! [A_60,B_61] : k5_xboole_0(A_60,k4_xboole_0(B_61,A_60)) = k2_xboole_0(A_60,B_61) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_436,plain,(
    k5_xboole_0(k1_tarski('#skF_4'),k1_xboole_0) = k2_xboole_0(k1_tarski('#skF_4'),'#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_415])).

tff(c_447,plain,(
    k2_xboole_0(k1_tarski('#skF_4'),'#skF_3') = k1_tarski('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_352,c_436])).

tff(c_760,plain,(
    ! [C_80,B_81,A_82] :
      ( k1_xboole_0 = C_80
      | k1_xboole_0 = B_81
      | C_80 = B_81
      | k2_xboole_0(B_81,C_80) != k1_tarski(A_82) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_766,plain,(
    ! [A_82] :
      ( k1_xboole_0 = '#skF_3'
      | k1_tarski('#skF_4') = k1_xboole_0
      | k1_tarski('#skF_4') = '#skF_3'
      | k1_tarski(A_82) != k1_tarski('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_447,c_760])).

tff(c_773,plain,(
    ! [A_82] : k1_tarski(A_82) != k1_tarski('#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_372,c_48,c_766])).

tff(c_779,plain,(
    $false ),
    inference(reflexivity,[status(thm),theory(equality)],[c_773])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n011.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 10:20:12 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.52/1.35  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.52/1.35  
% 2.52/1.35  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.52/1.35  %$ r2_hidden > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2 > #skF_4
% 2.52/1.35  
% 2.52/1.35  %Foreground sorts:
% 2.52/1.35  
% 2.52/1.35  
% 2.52/1.35  %Background operators:
% 2.52/1.35  
% 2.52/1.35  
% 2.52/1.35  %Foreground operators:
% 2.52/1.35  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.52/1.35  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.52/1.35  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.52/1.35  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.52/1.35  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.52/1.35  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.52/1.35  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.52/1.35  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.52/1.35  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.52/1.35  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.52/1.35  tff('#skF_3', type, '#skF_3': $i).
% 2.52/1.35  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.52/1.35  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.52/1.35  tff('#skF_4', type, '#skF_4': $i).
% 2.52/1.35  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.52/1.35  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.52/1.35  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.52/1.35  
% 2.52/1.37  tff(f_81, negated_conjecture, ~(![A, B]: ~(((k4_xboole_0(A, k1_tarski(B)) = k1_xboole_0) & ~(A = k1_xboole_0)) & ~(A = k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t66_zfmisc_1)).
% 2.52/1.37  tff(f_50, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 2.52/1.37  tff(f_48, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_tarski)).
% 2.52/1.37  tff(f_29, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 2.52/1.37  tff(f_33, axiom, (![A, B]: (k4_xboole_0(A, k2_xboole_0(A, B)) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_xboole_1)).
% 2.52/1.37  tff(f_71, axiom, (![A, B]: ((k4_xboole_0(A, k1_tarski(B)) = A) <=> ~r2_hidden(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_zfmisc_1)).
% 2.52/1.37  tff(f_31, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 2.52/1.37  tff(f_35, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 2.52/1.37  tff(f_27, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 2.52/1.37  tff(f_39, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_xboole_1)).
% 2.52/1.37  tff(f_66, axiom, (![A, B, C]: ~((((k1_tarski(A) = k2_xboole_0(B, C)) & ~(B = C)) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_zfmisc_1)).
% 2.52/1.37  tff(c_46, plain, (k1_tarski('#skF_4')!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.52/1.37  tff(c_34, plain, (![A_18]: (k2_tarski(A_18, A_18)=k1_tarski(A_18))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.52/1.37  tff(c_99, plain, (![D_33, A_34]: (r2_hidden(D_33, k2_tarski(A_34, D_33)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.52/1.37  tff(c_102, plain, (![A_18]: (r2_hidden(A_18, k1_tarski(A_18)))), inference(superposition, [status(thm), theory('equality')], [c_34, c_99])).
% 2.52/1.37  tff(c_4, plain, (![A_3]: (k2_xboole_0(A_3, k1_xboole_0)=A_3)), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.52/1.37  tff(c_109, plain, (![A_38, B_39]: (k4_xboole_0(A_38, k2_xboole_0(A_38, B_39))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.52/1.37  tff(c_119, plain, (![A_3]: (k4_xboole_0(A_3, A_3)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_4, c_109])).
% 2.52/1.37  tff(c_355, plain, (![B_54, A_55]: (~r2_hidden(B_54, A_55) | k4_xboole_0(A_55, k1_tarski(B_54))!=A_55)), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.52/1.37  tff(c_362, plain, (![B_54]: (~r2_hidden(B_54, k1_tarski(B_54)) | k1_tarski(B_54)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_119, c_355])).
% 2.52/1.37  tff(c_372, plain, (![B_54]: (k1_tarski(B_54)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_102, c_362])).
% 2.52/1.37  tff(c_48, plain, (k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.52/1.37  tff(c_6, plain, (![A_4]: (k4_xboole_0(A_4, k1_xboole_0)=A_4)), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.52/1.37  tff(c_161, plain, (![A_43, B_44]: (k4_xboole_0(A_43, k4_xboole_0(A_43, B_44))=k3_xboole_0(A_43, B_44))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.52/1.37  tff(c_189, plain, (![A_4]: (k4_xboole_0(A_4, A_4)=k3_xboole_0(A_4, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_6, c_161])).
% 2.52/1.37  tff(c_202, plain, (![A_4]: (k3_xboole_0(A_4, k1_xboole_0)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_119, c_189])).
% 2.52/1.37  tff(c_326, plain, (![A_52, B_53]: (k5_xboole_0(A_52, k3_xboole_0(A_52, B_53))=k4_xboole_0(A_52, B_53))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.52/1.37  tff(c_341, plain, (![A_4]: (k5_xboole_0(A_4, k1_xboole_0)=k4_xboole_0(A_4, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_202, c_326])).
% 2.52/1.37  tff(c_352, plain, (![A_4]: (k5_xboole_0(A_4, k1_xboole_0)=A_4)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_341])).
% 2.52/1.37  tff(c_50, plain, (k4_xboole_0('#skF_3', k1_tarski('#skF_4'))=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.52/1.37  tff(c_415, plain, (![A_60, B_61]: (k5_xboole_0(A_60, k4_xboole_0(B_61, A_60))=k2_xboole_0(A_60, B_61))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.52/1.37  tff(c_436, plain, (k5_xboole_0(k1_tarski('#skF_4'), k1_xboole_0)=k2_xboole_0(k1_tarski('#skF_4'), '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_50, c_415])).
% 2.52/1.37  tff(c_447, plain, (k2_xboole_0(k1_tarski('#skF_4'), '#skF_3')=k1_tarski('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_352, c_436])).
% 2.52/1.37  tff(c_760, plain, (![C_80, B_81, A_82]: (k1_xboole_0=C_80 | k1_xboole_0=B_81 | C_80=B_81 | k2_xboole_0(B_81, C_80)!=k1_tarski(A_82))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.52/1.37  tff(c_766, plain, (![A_82]: (k1_xboole_0='#skF_3' | k1_tarski('#skF_4')=k1_xboole_0 | k1_tarski('#skF_4')='#skF_3' | k1_tarski(A_82)!=k1_tarski('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_447, c_760])).
% 2.52/1.37  tff(c_773, plain, (![A_82]: (k1_tarski(A_82)!=k1_tarski('#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_46, c_372, c_48, c_766])).
% 2.52/1.37  tff(c_779, plain, $false, inference(reflexivity, [status(thm), theory('equality')], [c_773])).
% 2.52/1.37  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.52/1.37  
% 2.52/1.37  Inference rules
% 2.52/1.37  ----------------------
% 2.52/1.37  #Ref     : 1
% 2.52/1.37  #Sup     : 168
% 2.52/1.37  #Fact    : 0
% 2.52/1.37  #Define  : 0
% 2.52/1.37  #Split   : 0
% 2.52/1.37  #Chain   : 0
% 2.52/1.37  #Close   : 0
% 2.52/1.37  
% 2.52/1.37  Ordering : KBO
% 2.52/1.37  
% 2.52/1.37  Simplification rules
% 2.52/1.37  ----------------------
% 2.52/1.37  #Subsume      : 3
% 2.52/1.37  #Demod        : 92
% 2.52/1.37  #Tautology    : 138
% 2.52/1.37  #SimpNegUnit  : 14
% 2.52/1.37  #BackRed      : 0
% 2.52/1.37  
% 2.52/1.37  #Partial instantiations: 0
% 2.52/1.37  #Strategies tried      : 1
% 2.52/1.37  
% 2.52/1.37  Timing (in seconds)
% 2.52/1.37  ----------------------
% 2.52/1.37  Preprocessing        : 0.32
% 2.52/1.37  Parsing              : 0.17
% 2.52/1.37  CNF conversion       : 0.02
% 2.52/1.37  Main loop            : 0.27
% 2.52/1.37  Inferencing          : 0.10
% 2.52/1.37  Reduction            : 0.10
% 2.52/1.37  Demodulation         : 0.07
% 2.52/1.37  BG Simplification    : 0.02
% 2.52/1.37  Subsumption          : 0.04
% 2.52/1.37  Abstraction          : 0.02
% 2.52/1.37  MUC search           : 0.00
% 2.52/1.37  Cooper               : 0.00
% 2.52/1.37  Total                : 0.62
% 2.52/1.37  Index Insertion      : 0.00
% 2.52/1.37  Index Deletion       : 0.00
% 2.52/1.37  Index Matching       : 0.00
% 2.52/1.37  BG Taut test         : 0.00
%------------------------------------------------------------------------------
