%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:51:47 EST 2020

% Result     : Theorem 2.09s
% Output     : CNFRefutation 2.09s
% Verified   : 
% Statistics : Number of formulae       :   62 ( 111 expanded)
%              Number of leaves         :   32 (  52 expanded)
%              Depth                    :   10
%              Number of atoms          :   58 ( 128 expanded)
%              Number of equality atoms :   18 (  42 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_xboole_0 > #skF_2 > #skF_4 > #skF_7 > #skF_5 > #skF_6 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(f_28,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_89,negated_conjecture,(
    ~ ! [A,B,C] : k2_xboole_0(k2_tarski(A,B),C) != k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_zfmisc_1)).

tff(f_60,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(A)
     => ~ v1_xboole_0(k2_xboole_0(B,A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc5_xboole_0)).

tff(f_32,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_66,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_68,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_64,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_46,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_77,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).

tff(c_4,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_48,plain,(
    k2_xboole_0(k2_tarski('#skF_5','#skF_6'),'#skF_7') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_130,plain,(
    ! [B_47,A_48] :
      ( ~ v1_xboole_0(k2_xboole_0(B_47,A_48))
      | v1_xboole_0(A_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_133,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | v1_xboole_0('#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_130])).

tff(c_141,plain,(
    v1_xboole_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_133])).

tff(c_6,plain,(
    ! [A_3] :
      ( k1_xboole_0 = A_3
      | ~ v1_xboole_0(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_145,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(resolution,[status(thm)],[c_141,c_6])).

tff(c_18,plain,(
    ! [A_15] : r1_xboole_0(A_15,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_150,plain,(
    ! [A_15] : r1_xboole_0(A_15,'#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_145,c_18])).

tff(c_59,plain,(
    ! [B_43,A_44] : k2_xboole_0(B_43,A_44) = k2_xboole_0(A_44,B_43) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_20,plain,(
    ! [A_16,B_17] : r1_tarski(A_16,k2_xboole_0(A_16,B_17)) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_74,plain,(
    ! [A_44,B_43] : r1_tarski(A_44,k2_xboole_0(B_43,A_44)) ),
    inference(superposition,[status(thm),theory(equality)],[c_59,c_20])).

tff(c_111,plain,(
    r1_tarski('#skF_7',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_74])).

tff(c_147,plain,(
    r1_tarski('#skF_7','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_145,c_111])).

tff(c_217,plain,(
    ! [A_52,B_53] :
      ( k3_xboole_0(A_52,B_53) = A_52
      | ~ r1_tarski(A_52,B_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_227,plain,(
    k3_xboole_0('#skF_7','#skF_7') = '#skF_7' ),
    inference(resolution,[status(thm)],[c_147,c_217])).

tff(c_407,plain,(
    ! [A_64,B_65,C_66] :
      ( ~ r1_xboole_0(A_64,B_65)
      | ~ r2_hidden(C_66,k3_xboole_0(A_64,B_65)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_422,plain,(
    ! [C_66] :
      ( ~ r1_xboole_0('#skF_7','#skF_7')
      | ~ r2_hidden(C_66,'#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_227,c_407])).

tff(c_428,plain,(
    ! [C_66] : ~ r2_hidden(C_66,'#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_150,c_422])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_124,plain,(
    k2_xboole_0('#skF_7',k2_tarski('#skF_5','#skF_6')) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_48])).

tff(c_166,plain,(
    k2_xboole_0('#skF_7',k2_tarski('#skF_5','#skF_6')) = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_145,c_124])).

tff(c_14,plain,(
    ! [B_12,A_11] :
      ( ~ v1_xboole_0(k2_xboole_0(B_12,A_11))
      | v1_xboole_0(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_170,plain,
    ( ~ v1_xboole_0('#skF_7')
    | v1_xboole_0(k2_tarski('#skF_5','#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_166,c_14])).

tff(c_180,plain,(
    v1_xboole_0(k2_tarski('#skF_5','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_141,c_170])).

tff(c_149,plain,(
    ! [A_3] :
      ( A_3 = '#skF_7'
      | ~ v1_xboole_0(A_3) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_145,c_6])).

tff(c_186,plain,(
    k2_tarski('#skF_5','#skF_6') = '#skF_7' ),
    inference(resolution,[status(thm)],[c_180,c_149])).

tff(c_26,plain,(
    ! [D_23,B_19] : r2_hidden(D_23,k2_tarski(D_23,B_19)) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_196,plain,(
    r2_hidden('#skF_5','#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_186,c_26])).

tff(c_432,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_428,c_196])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 21:02:00 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.09/1.31  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.09/1.32  
% 2.09/1.32  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.09/1.32  %$ r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_xboole_0 > #skF_2 > #skF_4 > #skF_7 > #skF_5 > #skF_6 > #skF_3 > #skF_1
% 2.09/1.32  
% 2.09/1.32  %Foreground sorts:
% 2.09/1.32  
% 2.09/1.32  
% 2.09/1.32  %Background operators:
% 2.09/1.32  
% 2.09/1.32  
% 2.09/1.32  %Foreground operators:
% 2.09/1.32  tff('#skF_2', type, '#skF_2': $i > $i).
% 2.09/1.32  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.09/1.32  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.09/1.32  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.09/1.32  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.09/1.32  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 2.09/1.32  tff('#skF_7', type, '#skF_7': $i).
% 2.09/1.32  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.09/1.32  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.09/1.32  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.09/1.32  tff('#skF_5', type, '#skF_5': $i).
% 2.09/1.32  tff('#skF_6', type, '#skF_6': $i).
% 2.09/1.32  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.09/1.32  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.09/1.32  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.09/1.32  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.09/1.32  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 2.09/1.32  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.09/1.32  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.09/1.32  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.09/1.32  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.09/1.32  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.09/1.32  
% 2.09/1.33  tff(f_28, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.09/1.33  tff(f_89, negated_conjecture, ~(![A, B, C]: ~(k2_xboole_0(k2_tarski(A, B), C) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t50_zfmisc_1)).
% 2.09/1.33  tff(f_60, axiom, (![A, B]: (~v1_xboole_0(A) => ~v1_xboole_0(k2_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc5_xboole_0)).
% 2.09/1.33  tff(f_32, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 2.09/1.33  tff(f_66, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 2.09/1.33  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 2.09/1.33  tff(f_68, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 2.09/1.33  tff(f_64, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 2.09/1.33  tff(f_46, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 2.09/1.33  tff(f_77, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_tarski)).
% 2.09/1.33  tff(c_4, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_28])).
% 2.09/1.33  tff(c_48, plain, (k2_xboole_0(k2_tarski('#skF_5', '#skF_6'), '#skF_7')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.09/1.33  tff(c_130, plain, (![B_47, A_48]: (~v1_xboole_0(k2_xboole_0(B_47, A_48)) | v1_xboole_0(A_48))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.09/1.33  tff(c_133, plain, (~v1_xboole_0(k1_xboole_0) | v1_xboole_0('#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_48, c_130])).
% 2.09/1.33  tff(c_141, plain, (v1_xboole_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_133])).
% 2.09/1.33  tff(c_6, plain, (![A_3]: (k1_xboole_0=A_3 | ~v1_xboole_0(A_3))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.09/1.33  tff(c_145, plain, (k1_xboole_0='#skF_7'), inference(resolution, [status(thm)], [c_141, c_6])).
% 2.09/1.33  tff(c_18, plain, (![A_15]: (r1_xboole_0(A_15, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.09/1.33  tff(c_150, plain, (![A_15]: (r1_xboole_0(A_15, '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_145, c_18])).
% 2.09/1.33  tff(c_59, plain, (![B_43, A_44]: (k2_xboole_0(B_43, A_44)=k2_xboole_0(A_44, B_43))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.09/1.33  tff(c_20, plain, (![A_16, B_17]: (r1_tarski(A_16, k2_xboole_0(A_16, B_17)))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.09/1.33  tff(c_74, plain, (![A_44, B_43]: (r1_tarski(A_44, k2_xboole_0(B_43, A_44)))), inference(superposition, [status(thm), theory('equality')], [c_59, c_20])).
% 2.09/1.33  tff(c_111, plain, (r1_tarski('#skF_7', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_48, c_74])).
% 2.09/1.33  tff(c_147, plain, (r1_tarski('#skF_7', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_145, c_111])).
% 2.09/1.33  tff(c_217, plain, (![A_52, B_53]: (k3_xboole_0(A_52, B_53)=A_52 | ~r1_tarski(A_52, B_53))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.09/1.33  tff(c_227, plain, (k3_xboole_0('#skF_7', '#skF_7')='#skF_7'), inference(resolution, [status(thm)], [c_147, c_217])).
% 2.09/1.33  tff(c_407, plain, (![A_64, B_65, C_66]: (~r1_xboole_0(A_64, B_65) | ~r2_hidden(C_66, k3_xboole_0(A_64, B_65)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.09/1.33  tff(c_422, plain, (![C_66]: (~r1_xboole_0('#skF_7', '#skF_7') | ~r2_hidden(C_66, '#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_227, c_407])).
% 2.09/1.33  tff(c_428, plain, (![C_66]: (~r2_hidden(C_66, '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_150, c_422])).
% 2.09/1.33  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.09/1.33  tff(c_124, plain, (k2_xboole_0('#skF_7', k2_tarski('#skF_5', '#skF_6'))=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_2, c_48])).
% 2.09/1.33  tff(c_166, plain, (k2_xboole_0('#skF_7', k2_tarski('#skF_5', '#skF_6'))='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_145, c_124])).
% 2.09/1.33  tff(c_14, plain, (![B_12, A_11]: (~v1_xboole_0(k2_xboole_0(B_12, A_11)) | v1_xboole_0(A_11))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.09/1.33  tff(c_170, plain, (~v1_xboole_0('#skF_7') | v1_xboole_0(k2_tarski('#skF_5', '#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_166, c_14])).
% 2.09/1.33  tff(c_180, plain, (v1_xboole_0(k2_tarski('#skF_5', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_141, c_170])).
% 2.09/1.33  tff(c_149, plain, (![A_3]: (A_3='#skF_7' | ~v1_xboole_0(A_3))), inference(demodulation, [status(thm), theory('equality')], [c_145, c_6])).
% 2.09/1.33  tff(c_186, plain, (k2_tarski('#skF_5', '#skF_6')='#skF_7'), inference(resolution, [status(thm)], [c_180, c_149])).
% 2.09/1.33  tff(c_26, plain, (![D_23, B_19]: (r2_hidden(D_23, k2_tarski(D_23, B_19)))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.09/1.33  tff(c_196, plain, (r2_hidden('#skF_5', '#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_186, c_26])).
% 2.09/1.33  tff(c_432, plain, $false, inference(negUnitSimplification, [status(thm)], [c_428, c_196])).
% 2.09/1.33  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.09/1.33  
% 2.09/1.33  Inference rules
% 2.09/1.33  ----------------------
% 2.09/1.33  #Ref     : 0
% 2.09/1.33  #Sup     : 100
% 2.09/1.33  #Fact    : 0
% 2.09/1.33  #Define  : 0
% 2.09/1.33  #Split   : 1
% 2.09/1.33  #Chain   : 0
% 2.09/1.33  #Close   : 0
% 2.09/1.33  
% 2.09/1.33  Ordering : KBO
% 2.09/1.33  
% 2.09/1.33  Simplification rules
% 2.09/1.33  ----------------------
% 2.09/1.33  #Subsume      : 6
% 2.09/1.33  #Demod        : 55
% 2.09/1.33  #Tautology    : 71
% 2.09/1.33  #SimpNegUnit  : 2
% 2.09/1.33  #BackRed      : 10
% 2.09/1.33  
% 2.09/1.33  #Partial instantiations: 0
% 2.09/1.33  #Strategies tried      : 1
% 2.09/1.33  
% 2.09/1.33  Timing (in seconds)
% 2.09/1.33  ----------------------
% 2.09/1.33  Preprocessing        : 0.30
% 2.09/1.33  Parsing              : 0.15
% 2.09/1.33  CNF conversion       : 0.02
% 2.09/1.33  Main loop            : 0.21
% 2.09/1.33  Inferencing          : 0.07
% 2.09/1.33  Reduction            : 0.08
% 2.09/1.34  Demodulation         : 0.06
% 2.09/1.34  BG Simplification    : 0.01
% 2.09/1.34  Subsumption          : 0.04
% 2.09/1.34  Abstraction          : 0.01
% 2.09/1.34  MUC search           : 0.00
% 2.09/1.34  Cooper               : 0.00
% 2.09/1.34  Total                : 0.54
% 2.09/1.34  Index Insertion      : 0.00
% 2.09/1.34  Index Deletion       : 0.00
% 2.09/1.34  Index Matching       : 0.00
% 2.09/1.34  BG Taut test         : 0.00
%------------------------------------------------------------------------------
