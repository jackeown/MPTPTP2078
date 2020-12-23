%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:57:21 EST 2020

% Result     : Theorem 2.23s
% Output     : CNFRefutation 2.23s
% Verified   : 
% Statistics : Number of formulae       :   51 (  80 expanded)
%              Number of leaves         :   25 (  37 expanded)
%              Depth                    :   10
%              Number of atoms          :   54 (  96 expanded)
%              Number of equality atoms :   37 (  59 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_47,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_45,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_59,axiom,(
    ! [A,B] :
      ( k3_xboole_0(A,k1_tarski(B)) = k1_tarski(B)
     => r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l29_zfmisc_1)).

tff(f_71,axiom,(
    ! [A] : k1_setfam_1(k1_tarski(A)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_setfam_1)).

tff(f_51,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_xboole_0(k1_tarski(A),k1_tarski(B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_enumset1)).

tff(f_69,axiom,(
    ! [A,B] :
      ~ ( A != k1_xboole_0
        & B != k1_xboole_0
        & k1_setfam_1(k2_xboole_0(A,B)) != k3_xboole_0(k1_setfam_1(A),k1_setfam_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_setfam_1)).

tff(f_74,negated_conjecture,(
    ~ ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

tff(c_12,plain,(
    ! [A_10] : k3_xboole_0(A_10,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_6,plain,(
    ! [A_3,B_4] :
      ( r1_xboole_0(A_3,B_4)
      | k3_xboole_0(A_3,B_4) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_168,plain,(
    ! [A_37,B_38,C_39] :
      ( ~ r1_xboole_0(A_37,B_38)
      | ~ r2_hidden(C_39,k3_xboole_0(A_37,B_38)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_180,plain,(
    ! [A_10,C_39] :
      ( ~ r1_xboole_0(A_10,k1_xboole_0)
      | ~ r2_hidden(C_39,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_168])).

tff(c_181,plain,(
    ! [C_39] : ~ r2_hidden(C_39,k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_180])).

tff(c_55,plain,(
    ! [B_26,A_27] : k3_xboole_0(B_26,A_27) = k3_xboole_0(A_27,B_26) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_71,plain,(
    ! [A_27] : k3_xboole_0(k1_xboole_0,A_27) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_55,c_12])).

tff(c_205,plain,(
    ! [B_46,A_47] :
      ( r2_hidden(B_46,A_47)
      | k3_xboole_0(A_47,k1_tarski(B_46)) != k1_tarski(B_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_209,plain,(
    ! [B_46] :
      ( r2_hidden(B_46,k1_xboole_0)
      | k1_tarski(B_46) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_71,c_205])).

tff(c_218,plain,(
    ! [B_46] : k1_tarski(B_46) != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_181,c_209])).

tff(c_26,plain,(
    ! [A_22] : k1_setfam_1(k1_tarski(A_22)) = A_22 ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_16,plain,(
    ! [A_13,B_14] : k2_xboole_0(k1_tarski(A_13),k1_tarski(B_14)) = k2_tarski(A_13,B_14) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_257,plain,(
    ! [A_53,B_54] :
      ( k3_xboole_0(k1_setfam_1(A_53),k1_setfam_1(B_54)) = k1_setfam_1(k2_xboole_0(A_53,B_54))
      | k1_xboole_0 = B_54
      | k1_xboole_0 = A_53 ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_290,plain,(
    ! [A_53,A_22] :
      ( k1_setfam_1(k2_xboole_0(A_53,k1_tarski(A_22))) = k3_xboole_0(k1_setfam_1(A_53),A_22)
      | k1_tarski(A_22) = k1_xboole_0
      | k1_xboole_0 = A_53 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_257])).

tff(c_544,plain,(
    ! [A_76,A_77] :
      ( k1_setfam_1(k2_xboole_0(A_76,k1_tarski(A_77))) = k3_xboole_0(k1_setfam_1(A_76),A_77)
      | k1_xboole_0 = A_76 ) ),
    inference(negUnitSimplification,[status(thm)],[c_218,c_290])).

tff(c_559,plain,(
    ! [A_13,B_14] :
      ( k3_xboole_0(k1_setfam_1(k1_tarski(A_13)),B_14) = k1_setfam_1(k2_tarski(A_13,B_14))
      | k1_tarski(A_13) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_544])).

tff(c_562,plain,(
    ! [A_13,B_14] :
      ( k1_setfam_1(k2_tarski(A_13,B_14)) = k3_xboole_0(A_13,B_14)
      | k1_tarski(A_13) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_559])).

tff(c_563,plain,(
    ! [A_13,B_14] : k1_setfam_1(k2_tarski(A_13,B_14)) = k3_xboole_0(A_13,B_14) ),
    inference(negUnitSimplification,[status(thm)],[c_218,c_562])).

tff(c_28,plain,(
    k1_setfam_1(k2_tarski('#skF_2','#skF_3')) != k3_xboole_0('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_29,plain,(
    k1_setfam_1(k2_tarski('#skF_2','#skF_3')) != k3_xboole_0('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_28])).

tff(c_564,plain,(
    k3_xboole_0('#skF_2','#skF_3') != k3_xboole_0('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_563,c_29])).

tff(c_567,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_564])).

tff(c_578,plain,(
    ! [A_80] : ~ r1_xboole_0(A_80,k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_180])).

tff(c_582,plain,(
    ! [A_3] : k3_xboole_0(A_3,k1_xboole_0) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_6,c_578])).

tff(c_586,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_582])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n008.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 11:29:45 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.23/1.26  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.23/1.26  
% 2.23/1.26  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.23/1.26  %$ r2_hidden > r1_xboole_0 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.23/1.26  
% 2.23/1.26  %Foreground sorts:
% 2.23/1.26  
% 2.23/1.26  
% 2.23/1.26  %Background operators:
% 2.23/1.26  
% 2.23/1.26  
% 2.23/1.26  %Foreground operators:
% 2.23/1.26  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.23/1.26  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.23/1.26  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.23/1.26  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.23/1.26  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.23/1.26  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.23/1.26  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.23/1.26  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.23/1.26  tff('#skF_2', type, '#skF_2': $i).
% 2.23/1.26  tff('#skF_3', type, '#skF_3': $i).
% 2.23/1.26  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.23/1.26  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.23/1.26  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.23/1.26  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.23/1.26  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.23/1.26  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.23/1.26  
% 2.23/1.28  tff(f_47, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 2.23/1.28  tff(f_31, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 2.23/1.28  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 2.23/1.28  tff(f_45, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 2.23/1.28  tff(f_59, axiom, (![A, B]: ((k3_xboole_0(A, k1_tarski(B)) = k1_tarski(B)) => r2_hidden(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l29_zfmisc_1)).
% 2.23/1.28  tff(f_71, axiom, (![A]: (k1_setfam_1(k1_tarski(A)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_setfam_1)).
% 2.23/1.28  tff(f_51, axiom, (![A, B]: (k2_tarski(A, B) = k2_xboole_0(k1_tarski(A), k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_enumset1)).
% 2.23/1.28  tff(f_69, axiom, (![A, B]: ~((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(k1_setfam_1(k2_xboole_0(A, B)) = k3_xboole_0(k1_setfam_1(A), k1_setfam_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_setfam_1)).
% 2.23/1.28  tff(f_74, negated_conjecture, ~(![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 2.23/1.28  tff(c_12, plain, (![A_10]: (k3_xboole_0(A_10, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.23/1.28  tff(c_6, plain, (![A_3, B_4]: (r1_xboole_0(A_3, B_4) | k3_xboole_0(A_3, B_4)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.23/1.28  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.23/1.28  tff(c_168, plain, (![A_37, B_38, C_39]: (~r1_xboole_0(A_37, B_38) | ~r2_hidden(C_39, k3_xboole_0(A_37, B_38)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.23/1.28  tff(c_180, plain, (![A_10, C_39]: (~r1_xboole_0(A_10, k1_xboole_0) | ~r2_hidden(C_39, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_12, c_168])).
% 2.23/1.28  tff(c_181, plain, (![C_39]: (~r2_hidden(C_39, k1_xboole_0))), inference(splitLeft, [status(thm)], [c_180])).
% 2.23/1.28  tff(c_55, plain, (![B_26, A_27]: (k3_xboole_0(B_26, A_27)=k3_xboole_0(A_27, B_26))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.23/1.28  tff(c_71, plain, (![A_27]: (k3_xboole_0(k1_xboole_0, A_27)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_55, c_12])).
% 2.23/1.28  tff(c_205, plain, (![B_46, A_47]: (r2_hidden(B_46, A_47) | k3_xboole_0(A_47, k1_tarski(B_46))!=k1_tarski(B_46))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.23/1.28  tff(c_209, plain, (![B_46]: (r2_hidden(B_46, k1_xboole_0) | k1_tarski(B_46)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_71, c_205])).
% 2.23/1.28  tff(c_218, plain, (![B_46]: (k1_tarski(B_46)!=k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_181, c_209])).
% 2.23/1.28  tff(c_26, plain, (![A_22]: (k1_setfam_1(k1_tarski(A_22))=A_22)), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.23/1.28  tff(c_16, plain, (![A_13, B_14]: (k2_xboole_0(k1_tarski(A_13), k1_tarski(B_14))=k2_tarski(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.23/1.28  tff(c_257, plain, (![A_53, B_54]: (k3_xboole_0(k1_setfam_1(A_53), k1_setfam_1(B_54))=k1_setfam_1(k2_xboole_0(A_53, B_54)) | k1_xboole_0=B_54 | k1_xboole_0=A_53)), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.23/1.28  tff(c_290, plain, (![A_53, A_22]: (k1_setfam_1(k2_xboole_0(A_53, k1_tarski(A_22)))=k3_xboole_0(k1_setfam_1(A_53), A_22) | k1_tarski(A_22)=k1_xboole_0 | k1_xboole_0=A_53)), inference(superposition, [status(thm), theory('equality')], [c_26, c_257])).
% 2.23/1.28  tff(c_544, plain, (![A_76, A_77]: (k1_setfam_1(k2_xboole_0(A_76, k1_tarski(A_77)))=k3_xboole_0(k1_setfam_1(A_76), A_77) | k1_xboole_0=A_76)), inference(negUnitSimplification, [status(thm)], [c_218, c_290])).
% 2.23/1.28  tff(c_559, plain, (![A_13, B_14]: (k3_xboole_0(k1_setfam_1(k1_tarski(A_13)), B_14)=k1_setfam_1(k2_tarski(A_13, B_14)) | k1_tarski(A_13)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_16, c_544])).
% 2.23/1.28  tff(c_562, plain, (![A_13, B_14]: (k1_setfam_1(k2_tarski(A_13, B_14))=k3_xboole_0(A_13, B_14) | k1_tarski(A_13)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_26, c_559])).
% 2.23/1.28  tff(c_563, plain, (![A_13, B_14]: (k1_setfam_1(k2_tarski(A_13, B_14))=k3_xboole_0(A_13, B_14))), inference(negUnitSimplification, [status(thm)], [c_218, c_562])).
% 2.23/1.28  tff(c_28, plain, (k1_setfam_1(k2_tarski('#skF_2', '#skF_3'))!=k3_xboole_0('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.23/1.28  tff(c_29, plain, (k1_setfam_1(k2_tarski('#skF_2', '#skF_3'))!=k3_xboole_0('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_28])).
% 2.23/1.28  tff(c_564, plain, (k3_xboole_0('#skF_2', '#skF_3')!=k3_xboole_0('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_563, c_29])).
% 2.23/1.28  tff(c_567, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2, c_564])).
% 2.23/1.28  tff(c_578, plain, (![A_80]: (~r1_xboole_0(A_80, k1_xboole_0))), inference(splitRight, [status(thm)], [c_180])).
% 2.23/1.28  tff(c_582, plain, (![A_3]: (k3_xboole_0(A_3, k1_xboole_0)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_578])).
% 2.23/1.28  tff(c_586, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12, c_582])).
% 2.23/1.28  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.23/1.28  
% 2.23/1.28  Inference rules
% 2.23/1.28  ----------------------
% 2.23/1.28  #Ref     : 0
% 2.23/1.28  #Sup     : 136
% 2.23/1.28  #Fact    : 0
% 2.23/1.28  #Define  : 0
% 2.23/1.28  #Split   : 1
% 2.23/1.28  #Chain   : 0
% 2.23/1.28  #Close   : 0
% 2.23/1.28  
% 2.23/1.28  Ordering : KBO
% 2.23/1.28  
% 2.23/1.28  Simplification rules
% 2.23/1.28  ----------------------
% 2.23/1.28  #Subsume      : 23
% 2.23/1.28  #Demod        : 54
% 2.23/1.28  #Tautology    : 72
% 2.23/1.28  #SimpNegUnit  : 9
% 2.23/1.28  #BackRed      : 1
% 2.23/1.28  
% 2.23/1.28  #Partial instantiations: 0
% 2.23/1.28  #Strategies tried      : 1
% 2.23/1.28  
% 2.23/1.28  Timing (in seconds)
% 2.23/1.28  ----------------------
% 2.23/1.28  Preprocessing        : 0.28
% 2.23/1.28  Parsing              : 0.15
% 2.23/1.28  CNF conversion       : 0.02
% 2.23/1.28  Main loop            : 0.27
% 2.23/1.28  Inferencing          : 0.10
% 2.23/1.28  Reduction            : 0.09
% 2.23/1.28  Demodulation         : 0.07
% 2.23/1.28  BG Simplification    : 0.01
% 2.23/1.28  Subsumption          : 0.04
% 2.23/1.28  Abstraction          : 0.02
% 2.23/1.28  MUC search           : 0.00
% 2.23/1.28  Cooper               : 0.00
% 2.23/1.28  Total                : 0.57
% 2.23/1.28  Index Insertion      : 0.00
% 2.23/1.28  Index Deletion       : 0.00
% 2.23/1.28  Index Matching       : 0.00
% 2.23/1.28  BG Taut test         : 0.00
%------------------------------------------------------------------------------
