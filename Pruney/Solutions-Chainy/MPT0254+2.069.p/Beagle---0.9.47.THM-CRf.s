%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:51:28 EST 2020

% Result     : Theorem 2.11s
% Output     : CNFRefutation 2.11s
% Verified   : 
% Statistics : Number of formulae       :   53 ( 114 expanded)
%              Number of leaves         :   30 (  52 expanded)
%              Depth                    :   10
%              Number of atoms          :   43 ( 112 expanded)
%              Number of equality atoms :   20 (  69 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_5 > #skF_2 > #skF_4 > #skF_3 > #skF_1

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

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_43,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_76,negated_conjecture,(
    ~ ! [A,B] : k2_xboole_0(k1_tarski(A),B) != k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_zfmisc_1)).

tff(f_53,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_49,axiom,(
    ! [A] :
      ( r1_tarski(A,k1_xboole_0)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).

tff(f_51,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_45,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_41,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_64,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_62,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).

tff(c_8,plain,(
    ! [A_8] : k2_xboole_0(A_8,k1_xboole_0) = A_8 ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_123,plain,(
    ! [B_45,A_46] : k2_xboole_0(B_45,A_46) = k2_xboole_0(A_46,B_45) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_46,plain,(
    k2_xboole_0(k1_tarski('#skF_4'),'#skF_5') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_68,plain,(
    ! [A_35,B_36] : r1_tarski(A_35,k2_xboole_0(A_35,B_36)) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_71,plain,(
    r1_tarski(k1_tarski('#skF_4'),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_68])).

tff(c_12,plain,(
    ! [A_10] :
      ( k1_xboole_0 = A_10
      | ~ r1_tarski(A_10,k1_xboole_0) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_86,plain,(
    k1_tarski('#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_71,c_12])).

tff(c_88,plain,(
    k2_xboole_0(k1_xboole_0,'#skF_5') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_46])).

tff(c_138,plain,(
    k2_xboole_0('#skF_5',k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_123,c_88])).

tff(c_184,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_138])).

tff(c_14,plain,(
    ! [A_11] : r1_xboole_0(A_11,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_198,plain,(
    ! [A_11] : r1_xboole_0(A_11,'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_184,c_14])).

tff(c_10,plain,(
    ! [A_9] : k3_xboole_0(A_9,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_197,plain,(
    ! [A_9] : k3_xboole_0(A_9,'#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_184,c_184,c_10])).

tff(c_325,plain,(
    ! [A_56,B_57,C_58] :
      ( ~ r1_xboole_0(A_56,B_57)
      | ~ r2_hidden(C_58,k3_xboole_0(A_56,B_57)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_328,plain,(
    ! [A_9,C_58] :
      ( ~ r1_xboole_0(A_9,'#skF_5')
      | ~ r2_hidden(C_58,'#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_197,c_325])).

tff(c_330,plain,(
    ! [C_58] : ~ r2_hidden(C_58,'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_198,c_328])).

tff(c_104,plain,(
    ! [A_43] : k2_tarski(A_43,A_43) = k1_tarski(A_43) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_20,plain,(
    ! [D_19,A_14] : r2_hidden(D_19,k2_tarski(A_14,D_19)) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_119,plain,(
    ! [A_44] : r2_hidden(A_44,k1_tarski(A_44)) ),
    inference(superposition,[status(thm),theory(equality)],[c_104,c_20])).

tff(c_122,plain,(
    r2_hidden('#skF_4',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_86,c_119])).

tff(c_192,plain,(
    r2_hidden('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_184,c_122])).

tff(c_332,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_330,c_192])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:00:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.11/1.23  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.11/1.24  
% 2.11/1.24  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.11/1.24  %$ r2_hidden > r1_xboole_0 > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_5 > #skF_2 > #skF_4 > #skF_3 > #skF_1
% 2.11/1.24  
% 2.11/1.24  %Foreground sorts:
% 2.11/1.24  
% 2.11/1.24  
% 2.11/1.24  %Background operators:
% 2.11/1.24  
% 2.11/1.24  
% 2.11/1.24  %Foreground operators:
% 2.11/1.24  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.11/1.24  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.11/1.24  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.11/1.24  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.11/1.24  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.11/1.24  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.11/1.24  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.11/1.24  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.11/1.24  tff('#skF_5', type, '#skF_5': $i).
% 2.11/1.24  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.11/1.24  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.11/1.24  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.11/1.24  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.11/1.24  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.11/1.24  tff('#skF_4', type, '#skF_4': $i).
% 2.11/1.24  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 2.11/1.24  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.11/1.24  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.11/1.24  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.11/1.24  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.11/1.24  
% 2.11/1.25  tff(f_43, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 2.11/1.25  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 2.11/1.25  tff(f_76, negated_conjecture, ~(![A, B]: ~(k2_xboole_0(k1_tarski(A), B) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_zfmisc_1)).
% 2.11/1.25  tff(f_53, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 2.11/1.25  tff(f_49, axiom, (![A]: (r1_tarski(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_1)).
% 2.11/1.25  tff(f_51, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 2.11/1.25  tff(f_45, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 2.11/1.25  tff(f_41, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 2.11/1.25  tff(f_64, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 2.11/1.25  tff(f_62, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_tarski)).
% 2.11/1.25  tff(c_8, plain, (![A_8]: (k2_xboole_0(A_8, k1_xboole_0)=A_8)), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.11/1.25  tff(c_123, plain, (![B_45, A_46]: (k2_xboole_0(B_45, A_46)=k2_xboole_0(A_46, B_45))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.11/1.25  tff(c_46, plain, (k2_xboole_0(k1_tarski('#skF_4'), '#skF_5')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.11/1.25  tff(c_68, plain, (![A_35, B_36]: (r1_tarski(A_35, k2_xboole_0(A_35, B_36)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.11/1.25  tff(c_71, plain, (r1_tarski(k1_tarski('#skF_4'), k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_46, c_68])).
% 2.11/1.25  tff(c_12, plain, (![A_10]: (k1_xboole_0=A_10 | ~r1_tarski(A_10, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.11/1.25  tff(c_86, plain, (k1_tarski('#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_71, c_12])).
% 2.11/1.25  tff(c_88, plain, (k2_xboole_0(k1_xboole_0, '#skF_5')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_86, c_46])).
% 2.11/1.25  tff(c_138, plain, (k2_xboole_0('#skF_5', k1_xboole_0)=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_123, c_88])).
% 2.11/1.25  tff(c_184, plain, (k1_xboole_0='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_8, c_138])).
% 2.11/1.25  tff(c_14, plain, (![A_11]: (r1_xboole_0(A_11, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.11/1.25  tff(c_198, plain, (![A_11]: (r1_xboole_0(A_11, '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_184, c_14])).
% 2.11/1.25  tff(c_10, plain, (![A_9]: (k3_xboole_0(A_9, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.11/1.25  tff(c_197, plain, (![A_9]: (k3_xboole_0(A_9, '#skF_5')='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_184, c_184, c_10])).
% 2.11/1.25  tff(c_325, plain, (![A_56, B_57, C_58]: (~r1_xboole_0(A_56, B_57) | ~r2_hidden(C_58, k3_xboole_0(A_56, B_57)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.11/1.25  tff(c_328, plain, (![A_9, C_58]: (~r1_xboole_0(A_9, '#skF_5') | ~r2_hidden(C_58, '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_197, c_325])).
% 2.11/1.25  tff(c_330, plain, (![C_58]: (~r2_hidden(C_58, '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_198, c_328])).
% 2.11/1.25  tff(c_104, plain, (![A_43]: (k2_tarski(A_43, A_43)=k1_tarski(A_43))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.11/1.25  tff(c_20, plain, (![D_19, A_14]: (r2_hidden(D_19, k2_tarski(A_14, D_19)))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.11/1.25  tff(c_119, plain, (![A_44]: (r2_hidden(A_44, k1_tarski(A_44)))), inference(superposition, [status(thm), theory('equality')], [c_104, c_20])).
% 2.11/1.25  tff(c_122, plain, (r2_hidden('#skF_4', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_86, c_119])).
% 2.11/1.25  tff(c_192, plain, (r2_hidden('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_184, c_122])).
% 2.11/1.25  tff(c_332, plain, $false, inference(negUnitSimplification, [status(thm)], [c_330, c_192])).
% 2.11/1.25  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.11/1.25  
% 2.11/1.25  Inference rules
% 2.11/1.25  ----------------------
% 2.11/1.25  #Ref     : 0
% 2.11/1.25  #Sup     : 70
% 2.11/1.25  #Fact    : 0
% 2.11/1.25  #Define  : 0
% 2.11/1.25  #Split   : 0
% 2.11/1.25  #Chain   : 0
% 2.11/1.25  #Close   : 0
% 2.11/1.25  
% 2.11/1.25  Ordering : KBO
% 2.11/1.25  
% 2.11/1.25  Simplification rules
% 2.11/1.25  ----------------------
% 2.11/1.25  #Subsume      : 0
% 2.11/1.25  #Demod        : 38
% 2.11/1.25  #Tautology    : 56
% 2.11/1.25  #SimpNegUnit  : 1
% 2.11/1.25  #BackRed      : 10
% 2.11/1.25  
% 2.11/1.25  #Partial instantiations: 0
% 2.11/1.25  #Strategies tried      : 1
% 2.11/1.25  
% 2.11/1.25  Timing (in seconds)
% 2.11/1.25  ----------------------
% 2.11/1.26  Preprocessing        : 0.31
% 2.11/1.26  Parsing              : 0.16
% 2.11/1.26  CNF conversion       : 0.02
% 2.11/1.26  Main loop            : 0.18
% 2.11/1.26  Inferencing          : 0.05
% 2.11/1.26  Reduction            : 0.07
% 2.11/1.26  Demodulation         : 0.05
% 2.11/1.26  BG Simplification    : 0.01
% 2.11/1.26  Subsumption          : 0.03
% 2.11/1.26  Abstraction          : 0.01
% 2.11/1.26  MUC search           : 0.00
% 2.11/1.26  Cooper               : 0.00
% 2.11/1.26  Total                : 0.52
% 2.11/1.26  Index Insertion      : 0.00
% 2.11/1.26  Index Deletion       : 0.00
% 2.11/1.26  Index Matching       : 0.00
% 2.11/1.26  BG Taut test         : 0.00
%------------------------------------------------------------------------------
