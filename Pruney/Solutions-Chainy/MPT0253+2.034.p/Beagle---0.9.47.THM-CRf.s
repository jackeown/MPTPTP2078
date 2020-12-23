%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:51:18 EST 2020

% Result     : Theorem 22.80s
% Output     : CNFRefutation 22.80s
% Verified   : 
% Statistics : Number of formulae       :   54 (  68 expanded)
%              Number of leaves         :   29 (  37 expanded)
%              Depth                    :    7
%              Number of atoms          :   49 (  67 expanded)
%              Number of equality atoms :   28 (  42 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

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

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff(f_68,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( r2_hidden(A,B)
          & r2_hidden(C,B) )
       => k2_xboole_0(k2_tarski(A,C),B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_zfmisc_1)).

tff(f_29,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k5_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

tff(f_35,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

tff(f_39,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_37,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_61,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_tarski(A,B),C)
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_41,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(k5_xboole_0(A,B),k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_xboole_1)).

tff(c_40,plain,(
    r2_hidden('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_38,plain,(
    r2_hidden('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_4,plain,(
    ! [B_4,A_3] : k5_xboole_0(B_4,A_3) = k5_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_67,plain,(
    ! [B_48,A_49] : k5_xboole_0(B_48,A_49) = k5_xboole_0(A_49,B_48) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_8,plain,(
    ! [A_7] : k5_xboole_0(A_7,k1_xboole_0) = A_7 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_83,plain,(
    ! [A_49] : k5_xboole_0(k1_xboole_0,A_49) = A_49 ),
    inference(superposition,[status(thm),theory(equality)],[c_67,c_8])).

tff(c_12,plain,(
    ! [A_11] : k5_xboole_0(A_11,A_11) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_227,plain,(
    ! [A_68,B_69,C_70] : k5_xboole_0(k5_xboole_0(A_68,B_69),C_70) = k5_xboole_0(A_68,k5_xboole_0(B_69,C_70)) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_273,plain,(
    ! [A_11,C_70] : k5_xboole_0(A_11,k5_xboole_0(A_11,C_70)) = k5_xboole_0(k1_xboole_0,C_70) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_227])).

tff(c_294,plain,(
    ! [A_71,C_72] : k5_xboole_0(A_71,k5_xboole_0(A_71,C_72)) = C_72 ),
    inference(demodulation,[status(thm),theory(equality)],[c_83,c_273])).

tff(c_334,plain,(
    ! [A_3,B_4] : k5_xboole_0(A_3,k5_xboole_0(B_4,A_3)) = B_4 ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_294])).

tff(c_727,plain,(
    ! [A_81,B_82,C_83] :
      ( r1_tarski(k2_tarski(A_81,B_82),C_83)
      | ~ r2_hidden(B_82,C_83)
      | ~ r2_hidden(A_81,C_83) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_6,plain,(
    ! [A_5,B_6] :
      ( k3_xboole_0(A_5,B_6) = A_5
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_9278,plain,(
    ! [A_181,B_182,C_183] :
      ( k3_xboole_0(k2_tarski(A_181,B_182),C_183) = k2_tarski(A_181,B_182)
      | ~ r2_hidden(B_182,C_183)
      | ~ r2_hidden(A_181,C_183) ) ),
    inference(resolution,[status(thm)],[c_727,c_6])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_356,plain,(
    ! [A_73,B_74] : k5_xboole_0(k5_xboole_0(A_73,B_74),k3_xboole_0(A_73,B_74)) = k2_xboole_0(A_73,B_74) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_402,plain,(
    ! [B_2,A_1] : k5_xboole_0(k5_xboole_0(B_2,A_1),k3_xboole_0(A_1,B_2)) = k2_xboole_0(B_2,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_356])).

tff(c_9323,plain,(
    ! [C_183,A_181,B_182] :
      ( k5_xboole_0(k5_xboole_0(C_183,k2_tarski(A_181,B_182)),k2_tarski(A_181,B_182)) = k2_xboole_0(C_183,k2_tarski(A_181,B_182))
      | ~ r2_hidden(B_182,C_183)
      | ~ r2_hidden(A_181,C_183) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_9278,c_402])).

tff(c_41204,plain,(
    ! [C_298,A_299,B_300] :
      ( k2_xboole_0(C_298,k2_tarski(A_299,B_300)) = C_298
      | ~ r2_hidden(B_300,C_298)
      | ~ r2_hidden(A_299,C_298) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_334,c_4,c_9323])).

tff(c_5528,plain,(
    ! [B_155,A_156] : k5_xboole_0(k5_xboole_0(B_155,A_156),k3_xboole_0(A_156,B_155)) = k2_xboole_0(A_156,B_155) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_356])).

tff(c_5564,plain,(
    ! [B_155,A_156] : k2_xboole_0(B_155,A_156) = k2_xboole_0(A_156,B_155) ),
    inference(superposition,[status(thm),theory(equality)],[c_5528,c_402])).

tff(c_36,plain,(
    k2_xboole_0(k2_tarski('#skF_1','#skF_3'),'#skF_2') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_5816,plain,(
    k2_xboole_0('#skF_2',k2_tarski('#skF_1','#skF_3')) != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5564,c_36])).

tff(c_41270,plain,
    ( ~ r2_hidden('#skF_3','#skF_2')
    | ~ r2_hidden('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_41204,c_5816])).

tff(c_41341,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_41270])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:15:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 22.80/14.41  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 22.80/14.42  
% 22.80/14.42  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 22.80/14.42  %$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 22.80/14.42  
% 22.80/14.42  %Foreground sorts:
% 22.80/14.42  
% 22.80/14.42  
% 22.80/14.42  %Background operators:
% 22.80/14.42  
% 22.80/14.42  
% 22.80/14.42  %Foreground operators:
% 22.80/14.42  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 22.80/14.42  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 22.80/14.42  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 22.80/14.42  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 22.80/14.42  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 22.80/14.42  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 22.80/14.42  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 22.80/14.42  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 22.80/14.42  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 22.80/14.42  tff('#skF_2', type, '#skF_2': $i).
% 22.80/14.42  tff('#skF_3', type, '#skF_3': $i).
% 22.80/14.42  tff('#skF_1', type, '#skF_1': $i).
% 22.80/14.42  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 22.80/14.42  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 22.80/14.42  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 22.80/14.42  tff(k3_tarski, type, k3_tarski: $i > $i).
% 22.80/14.42  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 22.80/14.42  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 22.80/14.42  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 22.80/14.42  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 22.80/14.42  
% 22.80/14.43  tff(f_68, negated_conjecture, ~(![A, B, C]: ((r2_hidden(A, B) & r2_hidden(C, B)) => (k2_xboole_0(k2_tarski(A, C), B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_zfmisc_1)).
% 22.80/14.43  tff(f_29, axiom, (![A, B]: (k5_xboole_0(A, B) = k5_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 22.80/14.43  tff(f_35, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 22.80/14.43  tff(f_39, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t92_xboole_1)).
% 22.80/14.43  tff(f_37, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_xboole_1)).
% 22.80/14.43  tff(f_61, axiom, (![A, B, C]: (r1_tarski(k2_tarski(A, B), C) <=> (r2_hidden(A, C) & r2_hidden(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 22.80/14.43  tff(f_33, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 22.80/14.43  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 22.80/14.43  tff(f_41, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(k5_xboole_0(A, B), k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t94_xboole_1)).
% 22.80/14.43  tff(c_40, plain, (r2_hidden('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_68])).
% 22.80/14.43  tff(c_38, plain, (r2_hidden('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_68])).
% 22.80/14.43  tff(c_4, plain, (![B_4, A_3]: (k5_xboole_0(B_4, A_3)=k5_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 22.80/14.43  tff(c_67, plain, (![B_48, A_49]: (k5_xboole_0(B_48, A_49)=k5_xboole_0(A_49, B_48))), inference(cnfTransformation, [status(thm)], [f_29])).
% 22.80/14.43  tff(c_8, plain, (![A_7]: (k5_xboole_0(A_7, k1_xboole_0)=A_7)), inference(cnfTransformation, [status(thm)], [f_35])).
% 22.80/14.43  tff(c_83, plain, (![A_49]: (k5_xboole_0(k1_xboole_0, A_49)=A_49)), inference(superposition, [status(thm), theory('equality')], [c_67, c_8])).
% 22.80/14.43  tff(c_12, plain, (![A_11]: (k5_xboole_0(A_11, A_11)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 22.80/14.43  tff(c_227, plain, (![A_68, B_69, C_70]: (k5_xboole_0(k5_xboole_0(A_68, B_69), C_70)=k5_xboole_0(A_68, k5_xboole_0(B_69, C_70)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 22.80/14.43  tff(c_273, plain, (![A_11, C_70]: (k5_xboole_0(A_11, k5_xboole_0(A_11, C_70))=k5_xboole_0(k1_xboole_0, C_70))), inference(superposition, [status(thm), theory('equality')], [c_12, c_227])).
% 22.80/14.43  tff(c_294, plain, (![A_71, C_72]: (k5_xboole_0(A_71, k5_xboole_0(A_71, C_72))=C_72)), inference(demodulation, [status(thm), theory('equality')], [c_83, c_273])).
% 22.80/14.43  tff(c_334, plain, (![A_3, B_4]: (k5_xboole_0(A_3, k5_xboole_0(B_4, A_3))=B_4)), inference(superposition, [status(thm), theory('equality')], [c_4, c_294])).
% 22.80/14.43  tff(c_727, plain, (![A_81, B_82, C_83]: (r1_tarski(k2_tarski(A_81, B_82), C_83) | ~r2_hidden(B_82, C_83) | ~r2_hidden(A_81, C_83))), inference(cnfTransformation, [status(thm)], [f_61])).
% 22.80/14.43  tff(c_6, plain, (![A_5, B_6]: (k3_xboole_0(A_5, B_6)=A_5 | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_33])).
% 22.80/14.43  tff(c_9278, plain, (![A_181, B_182, C_183]: (k3_xboole_0(k2_tarski(A_181, B_182), C_183)=k2_tarski(A_181, B_182) | ~r2_hidden(B_182, C_183) | ~r2_hidden(A_181, C_183))), inference(resolution, [status(thm)], [c_727, c_6])).
% 22.80/14.43  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 22.80/14.43  tff(c_356, plain, (![A_73, B_74]: (k5_xboole_0(k5_xboole_0(A_73, B_74), k3_xboole_0(A_73, B_74))=k2_xboole_0(A_73, B_74))), inference(cnfTransformation, [status(thm)], [f_41])).
% 22.80/14.43  tff(c_402, plain, (![B_2, A_1]: (k5_xboole_0(k5_xboole_0(B_2, A_1), k3_xboole_0(A_1, B_2))=k2_xboole_0(B_2, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_356])).
% 22.80/14.43  tff(c_9323, plain, (![C_183, A_181, B_182]: (k5_xboole_0(k5_xboole_0(C_183, k2_tarski(A_181, B_182)), k2_tarski(A_181, B_182))=k2_xboole_0(C_183, k2_tarski(A_181, B_182)) | ~r2_hidden(B_182, C_183) | ~r2_hidden(A_181, C_183))), inference(superposition, [status(thm), theory('equality')], [c_9278, c_402])).
% 22.80/14.43  tff(c_41204, plain, (![C_298, A_299, B_300]: (k2_xboole_0(C_298, k2_tarski(A_299, B_300))=C_298 | ~r2_hidden(B_300, C_298) | ~r2_hidden(A_299, C_298))), inference(demodulation, [status(thm), theory('equality')], [c_334, c_4, c_9323])).
% 22.80/14.43  tff(c_5528, plain, (![B_155, A_156]: (k5_xboole_0(k5_xboole_0(B_155, A_156), k3_xboole_0(A_156, B_155))=k2_xboole_0(A_156, B_155))), inference(superposition, [status(thm), theory('equality')], [c_4, c_356])).
% 22.80/14.43  tff(c_5564, plain, (![B_155, A_156]: (k2_xboole_0(B_155, A_156)=k2_xboole_0(A_156, B_155))), inference(superposition, [status(thm), theory('equality')], [c_5528, c_402])).
% 22.80/14.43  tff(c_36, plain, (k2_xboole_0(k2_tarski('#skF_1', '#skF_3'), '#skF_2')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_68])).
% 22.80/14.43  tff(c_5816, plain, (k2_xboole_0('#skF_2', k2_tarski('#skF_1', '#skF_3'))!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_5564, c_36])).
% 22.80/14.43  tff(c_41270, plain, (~r2_hidden('#skF_3', '#skF_2') | ~r2_hidden('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_41204, c_5816])).
% 22.80/14.43  tff(c_41341, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_41270])).
% 22.80/14.43  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 22.80/14.43  
% 22.80/14.43  Inference rules
% 22.80/14.43  ----------------------
% 22.80/14.43  #Ref     : 0
% 22.80/14.43  #Sup     : 10791
% 22.80/14.43  #Fact    : 0
% 22.80/14.43  #Define  : 0
% 22.80/14.43  #Split   : 0
% 22.80/14.43  #Chain   : 0
% 22.80/14.43  #Close   : 0
% 22.80/14.43  
% 22.80/14.43  Ordering : KBO
% 22.80/14.43  
% 22.80/14.43  Simplification rules
% 22.80/14.43  ----------------------
% 22.80/14.43  #Subsume      : 682
% 22.80/14.43  #Demod        : 13932
% 22.80/14.43  #Tautology    : 3082
% 22.80/14.43  #SimpNegUnit  : 0
% 22.80/14.43  #BackRed      : 3
% 22.80/14.43  
% 22.80/14.43  #Partial instantiations: 0
% 22.80/14.43  #Strategies tried      : 1
% 22.80/14.43  
% 22.80/14.43  Timing (in seconds)
% 22.80/14.43  ----------------------
% 22.80/14.43  Preprocessing        : 0.50
% 22.80/14.43  Parsing              : 0.25
% 22.80/14.43  CNF conversion       : 0.03
% 22.80/14.43  Main loop            : 13.01
% 22.80/14.43  Inferencing          : 1.56
% 22.80/14.43  Reduction            : 9.34
% 22.80/14.43  Demodulation         : 8.86
% 22.80/14.43  BG Simplification    : 0.30
% 22.80/14.43  Subsumption          : 1.46
% 22.80/14.43  Abstraction          : 0.48
% 22.80/14.43  MUC search           : 0.00
% 22.80/14.43  Cooper               : 0.00
% 22.80/14.43  Total                : 13.55
% 22.80/14.43  Index Insertion      : 0.00
% 22.80/14.43  Index Deletion       : 0.00
% 22.80/14.43  Index Matching       : 0.00
% 22.80/14.43  BG Taut test         : 0.00
%------------------------------------------------------------------------------
