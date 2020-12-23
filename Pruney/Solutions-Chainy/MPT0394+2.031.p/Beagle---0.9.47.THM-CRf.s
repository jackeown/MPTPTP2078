%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:57:25 EST 2020

% Result     : Theorem 1.91s
% Output     : CNFRefutation 1.91s
% Verified   : 
% Statistics : Number of formulae       :   50 (  72 expanded)
%              Number of leaves         :   27 (  35 expanded)
%              Depth                    :   11
%              Number of atoms          :   51 (  81 expanded)
%              Number of equality atoms :   40 (  60 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_setfam_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2 > #skF_4

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

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

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

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_48,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_44,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).

tff(f_27,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_31,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,k1_tarski(B)) = A
    <=> ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_zfmisc_1)).

tff(f_65,axiom,(
    ! [A] : k1_setfam_1(k1_tarski(A)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_setfam_1)).

tff(f_46,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_xboole_0(k1_tarski(A),k1_tarski(B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_enumset1)).

tff(f_63,axiom,(
    ! [A,B] :
      ~ ( A != k1_xboole_0
        & B != k1_xboole_0
        & k1_setfam_1(k2_xboole_0(A,B)) != k3_xboole_0(k1_setfam_1(A),k1_setfam_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_setfam_1)).

tff(f_68,negated_conjecture,(
    ~ ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

tff(c_32,plain,(
    ! [A_15] : k2_tarski(A_15,A_15) = k1_tarski(A_15) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_69,plain,(
    ! [D_25,B_26] : r2_hidden(D_25,k2_tarski(D_25,B_26)) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_72,plain,(
    ! [A_15] : r2_hidden(A_15,k1_tarski(A_15)) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_69])).

tff(c_2,plain,(
    ! [A_1] : k3_xboole_0(A_1,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_6,plain,(
    ! [A_4] : r1_xboole_0(A_4,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_79,plain,(
    ! [A_30,B_31] :
      ( k4_xboole_0(A_30,B_31) = A_30
      | ~ r1_xboole_0(A_30,B_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_83,plain,(
    ! [A_4] : k4_xboole_0(A_4,k1_xboole_0) = A_4 ),
    inference(resolution,[status(thm)],[c_6,c_79])).

tff(c_107,plain,(
    ! [A_37,B_38] : k4_xboole_0(A_37,k4_xboole_0(A_37,B_38)) = k3_xboole_0(A_37,B_38) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_125,plain,(
    ! [A_4] : k4_xboole_0(A_4,A_4) = k3_xboole_0(A_4,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_83,c_107])).

tff(c_128,plain,(
    ! [A_4] : k4_xboole_0(A_4,A_4) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_125])).

tff(c_160,plain,(
    ! [B_40,A_41] :
      ( ~ r2_hidden(B_40,A_41)
      | k4_xboole_0(A_41,k1_tarski(B_40)) != A_41 ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_164,plain,(
    ! [B_40] :
      ( ~ r2_hidden(B_40,k1_tarski(B_40))
      | k1_tarski(B_40) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_128,c_160])).

tff(c_169,plain,(
    ! [B_40] : k1_tarski(B_40) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_164])).

tff(c_40,plain,(
    ! [A_20] : k1_setfam_1(k1_tarski(A_20)) = A_20 ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_30,plain,(
    ! [A_13,B_14] : k2_xboole_0(k1_tarski(A_13),k1_tarski(B_14)) = k2_tarski(A_13,B_14) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_290,plain,(
    ! [A_57,B_58] :
      ( k3_xboole_0(k1_setfam_1(A_57),k1_setfam_1(B_58)) = k1_setfam_1(k2_xboole_0(A_57,B_58))
      | k1_xboole_0 = B_58
      | k1_xboole_0 = A_57 ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_310,plain,(
    ! [A_20,B_58] :
      ( k1_setfam_1(k2_xboole_0(k1_tarski(A_20),B_58)) = k3_xboole_0(A_20,k1_setfam_1(B_58))
      | k1_xboole_0 = B_58
      | k1_tarski(A_20) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_290])).

tff(c_363,plain,(
    ! [A_65,B_66] :
      ( k1_setfam_1(k2_xboole_0(k1_tarski(A_65),B_66)) = k3_xboole_0(A_65,k1_setfam_1(B_66))
      | k1_xboole_0 = B_66 ) ),
    inference(negUnitSimplification,[status(thm)],[c_169,c_310])).

tff(c_386,plain,(
    ! [A_13,B_14] :
      ( k3_xboole_0(A_13,k1_setfam_1(k1_tarski(B_14))) = k1_setfam_1(k2_tarski(A_13,B_14))
      | k1_tarski(B_14) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_363])).

tff(c_393,plain,(
    ! [A_13,B_14] :
      ( k1_setfam_1(k2_tarski(A_13,B_14)) = k3_xboole_0(A_13,B_14)
      | k1_tarski(B_14) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_386])).

tff(c_394,plain,(
    ! [A_13,B_14] : k1_setfam_1(k2_tarski(A_13,B_14)) = k3_xboole_0(A_13,B_14) ),
    inference(negUnitSimplification,[status(thm)],[c_169,c_393])).

tff(c_42,plain,(
    k1_setfam_1(k2_tarski('#skF_3','#skF_4')) != k3_xboole_0('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_397,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_394,c_42])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n004.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 20:20:38 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.91/1.28  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.91/1.29  
% 1.91/1.29  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.91/1.29  %$ r2_hidden > r1_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_setfam_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2 > #skF_4
% 1.91/1.29  
% 1.91/1.29  %Foreground sorts:
% 1.91/1.29  
% 1.91/1.29  
% 1.91/1.29  %Background operators:
% 1.91/1.29  
% 1.91/1.29  
% 1.91/1.29  %Foreground operators:
% 1.91/1.29  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 1.91/1.29  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.91/1.29  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.91/1.29  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.91/1.29  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.91/1.29  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.91/1.29  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.91/1.29  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.91/1.29  tff('#skF_3', type, '#skF_3': $i).
% 1.91/1.29  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 1.91/1.29  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.91/1.29  tff('#skF_4', type, '#skF_4': $i).
% 1.91/1.29  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.91/1.29  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.91/1.29  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.91/1.29  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 1.91/1.29  
% 1.91/1.30  tff(f_48, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 1.91/1.30  tff(f_44, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_tarski)).
% 1.91/1.30  tff(f_27, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 1.91/1.30  tff(f_31, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 1.91/1.30  tff(f_35, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_xboole_1)).
% 1.91/1.30  tff(f_29, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 1.91/1.30  tff(f_53, axiom, (![A, B]: ((k4_xboole_0(A, k1_tarski(B)) = A) <=> ~r2_hidden(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_zfmisc_1)).
% 1.91/1.30  tff(f_65, axiom, (![A]: (k1_setfam_1(k1_tarski(A)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_setfam_1)).
% 1.91/1.30  tff(f_46, axiom, (![A, B]: (k2_tarski(A, B) = k2_xboole_0(k1_tarski(A), k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_enumset1)).
% 1.91/1.30  tff(f_63, axiom, (![A, B]: ~((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(k1_setfam_1(k2_xboole_0(A, B)) = k3_xboole_0(k1_setfam_1(A), k1_setfam_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_setfam_1)).
% 1.91/1.30  tff(f_68, negated_conjecture, ~(![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 1.91/1.30  tff(c_32, plain, (![A_15]: (k2_tarski(A_15, A_15)=k1_tarski(A_15))), inference(cnfTransformation, [status(thm)], [f_48])).
% 1.91/1.30  tff(c_69, plain, (![D_25, B_26]: (r2_hidden(D_25, k2_tarski(D_25, B_26)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 1.91/1.30  tff(c_72, plain, (![A_15]: (r2_hidden(A_15, k1_tarski(A_15)))), inference(superposition, [status(thm), theory('equality')], [c_32, c_69])).
% 1.91/1.30  tff(c_2, plain, (![A_1]: (k3_xboole_0(A_1, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.91/1.30  tff(c_6, plain, (![A_4]: (r1_xboole_0(A_4, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.91/1.30  tff(c_79, plain, (![A_30, B_31]: (k4_xboole_0(A_30, B_31)=A_30 | ~r1_xboole_0(A_30, B_31))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.91/1.30  tff(c_83, plain, (![A_4]: (k4_xboole_0(A_4, k1_xboole_0)=A_4)), inference(resolution, [status(thm)], [c_6, c_79])).
% 1.91/1.30  tff(c_107, plain, (![A_37, B_38]: (k4_xboole_0(A_37, k4_xboole_0(A_37, B_38))=k3_xboole_0(A_37, B_38))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.91/1.30  tff(c_125, plain, (![A_4]: (k4_xboole_0(A_4, A_4)=k3_xboole_0(A_4, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_83, c_107])).
% 1.91/1.30  tff(c_128, plain, (![A_4]: (k4_xboole_0(A_4, A_4)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_2, c_125])).
% 1.91/1.30  tff(c_160, plain, (![B_40, A_41]: (~r2_hidden(B_40, A_41) | k4_xboole_0(A_41, k1_tarski(B_40))!=A_41)), inference(cnfTransformation, [status(thm)], [f_53])).
% 1.91/1.30  tff(c_164, plain, (![B_40]: (~r2_hidden(B_40, k1_tarski(B_40)) | k1_tarski(B_40)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_128, c_160])).
% 1.91/1.30  tff(c_169, plain, (![B_40]: (k1_tarski(B_40)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_72, c_164])).
% 1.91/1.30  tff(c_40, plain, (![A_20]: (k1_setfam_1(k1_tarski(A_20))=A_20)), inference(cnfTransformation, [status(thm)], [f_65])).
% 1.91/1.30  tff(c_30, plain, (![A_13, B_14]: (k2_xboole_0(k1_tarski(A_13), k1_tarski(B_14))=k2_tarski(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.91/1.30  tff(c_290, plain, (![A_57, B_58]: (k3_xboole_0(k1_setfam_1(A_57), k1_setfam_1(B_58))=k1_setfam_1(k2_xboole_0(A_57, B_58)) | k1_xboole_0=B_58 | k1_xboole_0=A_57)), inference(cnfTransformation, [status(thm)], [f_63])).
% 1.91/1.30  tff(c_310, plain, (![A_20, B_58]: (k1_setfam_1(k2_xboole_0(k1_tarski(A_20), B_58))=k3_xboole_0(A_20, k1_setfam_1(B_58)) | k1_xboole_0=B_58 | k1_tarski(A_20)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_40, c_290])).
% 1.91/1.30  tff(c_363, plain, (![A_65, B_66]: (k1_setfam_1(k2_xboole_0(k1_tarski(A_65), B_66))=k3_xboole_0(A_65, k1_setfam_1(B_66)) | k1_xboole_0=B_66)), inference(negUnitSimplification, [status(thm)], [c_169, c_310])).
% 1.91/1.30  tff(c_386, plain, (![A_13, B_14]: (k3_xboole_0(A_13, k1_setfam_1(k1_tarski(B_14)))=k1_setfam_1(k2_tarski(A_13, B_14)) | k1_tarski(B_14)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_30, c_363])).
% 1.91/1.30  tff(c_393, plain, (![A_13, B_14]: (k1_setfam_1(k2_tarski(A_13, B_14))=k3_xboole_0(A_13, B_14) | k1_tarski(B_14)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_40, c_386])).
% 1.91/1.30  tff(c_394, plain, (![A_13, B_14]: (k1_setfam_1(k2_tarski(A_13, B_14))=k3_xboole_0(A_13, B_14))), inference(negUnitSimplification, [status(thm)], [c_169, c_393])).
% 1.91/1.30  tff(c_42, plain, (k1_setfam_1(k2_tarski('#skF_3', '#skF_4'))!=k3_xboole_0('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_68])).
% 1.91/1.30  tff(c_397, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_394, c_42])).
% 1.91/1.30  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.91/1.30  
% 1.91/1.30  Inference rules
% 1.91/1.30  ----------------------
% 1.91/1.30  #Ref     : 0
% 1.91/1.30  #Sup     : 78
% 1.91/1.30  #Fact    : 0
% 1.91/1.30  #Define  : 0
% 1.91/1.30  #Split   : 0
% 1.91/1.30  #Chain   : 0
% 1.91/1.30  #Close   : 0
% 1.91/1.30  
% 1.91/1.30  Ordering : KBO
% 1.91/1.30  
% 1.91/1.30  Simplification rules
% 1.91/1.30  ----------------------
% 1.91/1.30  #Subsume      : 1
% 1.91/1.30  #Demod        : 38
% 1.91/1.30  #Tautology    : 56
% 1.91/1.30  #SimpNegUnit  : 10
% 1.91/1.30  #BackRed      : 1
% 1.91/1.30  
% 1.91/1.30  #Partial instantiations: 0
% 1.91/1.30  #Strategies tried      : 1
% 1.91/1.30  
% 1.91/1.30  Timing (in seconds)
% 1.91/1.30  ----------------------
% 1.91/1.30  Preprocessing        : 0.29
% 1.91/1.30  Parsing              : 0.15
% 1.91/1.30  CNF conversion       : 0.02
% 1.91/1.30  Main loop            : 0.20
% 1.91/1.31  Inferencing          : 0.08
% 1.91/1.31  Reduction            : 0.07
% 1.91/1.31  Demodulation         : 0.05
% 1.91/1.31  BG Simplification    : 0.01
% 1.91/1.31  Subsumption          : 0.03
% 1.91/1.31  Abstraction          : 0.01
% 1.91/1.31  MUC search           : 0.00
% 1.91/1.31  Cooper               : 0.00
% 1.91/1.31  Total                : 0.52
% 1.91/1.31  Index Insertion      : 0.00
% 1.91/1.31  Index Deletion       : 0.00
% 1.91/1.31  Index Matching       : 0.00
% 1.91/1.31  BG Taut test         : 0.00
%------------------------------------------------------------------------------
