%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:51:41 EST 2020

% Result     : Theorem 1.99s
% Output     : CNFRefutation 2.07s
% Verified   : 
% Statistics : Number of formulae       :   58 ( 117 expanded)
%              Number of leaves         :   30 (  53 expanded)
%              Depth                    :   11
%              Number of atoms          :   53 ( 139 expanded)
%              Number of equality atoms :   22 (  49 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > v1_xboole_0 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3 > #skF_1

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_77,negated_conjecture,(
    ~ ! [A,B,C] : k2_xboole_0(k2_tarski(A,B),C) != k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_zfmisc_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(A)
     => ~ v1_xboole_0(k2_xboole_0(B,A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc5_xboole_0)).

tff(f_30,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_54,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_52,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

tff(f_44,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_56,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_73,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_65,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_44,plain,(
    k2_xboole_0(k2_tarski('#skF_4','#skF_5'),'#skF_6') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_10,plain,(
    ! [B_8,A_7] :
      ( ~ v1_xboole_0(k2_xboole_0(B_8,A_7))
      | v1_xboole_0(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_114,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | v1_xboole_0('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_10])).

tff(c_118,plain,(
    v1_xboole_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_114])).

tff(c_4,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_123,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(resolution,[status(thm)],[c_118,c_4])).

tff(c_14,plain,(
    ! [A_10] : r1_xboole_0(A_10,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_127,plain,(
    ! [A_10] : r1_xboole_0(A_10,'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_123,c_14])).

tff(c_12,plain,(
    ! [A_9] : k3_xboole_0(A_9,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_126,plain,(
    ! [A_9] : k3_xboole_0(A_9,'#skF_6') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_123,c_123,c_12])).

tff(c_297,plain,(
    ! [A_52,B_53,C_54] :
      ( ~ r1_xboole_0(A_52,B_53)
      | ~ r2_hidden(C_54,k3_xboole_0(A_52,B_53)) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_300,plain,(
    ! [A_9,C_54] :
      ( ~ r1_xboole_0(A_9,'#skF_6')
      | ~ r2_hidden(C_54,'#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_126,c_297])).

tff(c_302,plain,(
    ! [C_54] : ~ r2_hidden(C_54,'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_127,c_300])).

tff(c_124,plain,(
    k2_xboole_0(k2_tarski('#skF_4','#skF_5'),'#skF_6') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_123,c_44])).

tff(c_16,plain,(
    ! [B_12,A_11] : k2_tarski(B_12,A_11) = k2_tarski(A_11,B_12) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_157,plain,(
    ! [A_44,B_45] : k3_tarski(k2_tarski(A_44,B_45)) = k2_xboole_0(A_44,B_45) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_181,plain,(
    ! [B_48,A_49] : k3_tarski(k2_tarski(B_48,A_49)) = k2_xboole_0(A_49,B_48) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_157])).

tff(c_42,plain,(
    ! [A_28,B_29] : k3_tarski(k2_tarski(A_28,B_29)) = k2_xboole_0(A_28,B_29) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_204,plain,(
    ! [B_50,A_51] : k2_xboole_0(B_50,A_51) = k2_xboole_0(A_51,B_50) ),
    inference(superposition,[status(thm),theory(equality)],[c_181,c_42])).

tff(c_246,plain,(
    k2_xboole_0('#skF_6',k2_tarski('#skF_4','#skF_5')) = '#skF_6' ),
    inference(superposition,[status(thm),theory(equality)],[c_124,c_204])).

tff(c_258,plain,
    ( ~ v1_xboole_0('#skF_6')
    | v1_xboole_0(k2_tarski('#skF_4','#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_246,c_10])).

tff(c_262,plain,(
    v1_xboole_0(k2_tarski('#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_118,c_258])).

tff(c_125,plain,(
    ! [A_1] :
      ( A_1 = '#skF_6'
      | ~ v1_xboole_0(A_1) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_123,c_4])).

tff(c_267,plain,(
    k2_tarski('#skF_4','#skF_5') = '#skF_6' ),
    inference(resolution,[status(thm)],[c_262,c_125])).

tff(c_22,plain,(
    ! [D_18,B_14] : r2_hidden(D_18,k2_tarski(D_18,B_14)) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_284,plain,(
    r2_hidden('#skF_4','#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_267,c_22])).

tff(c_305,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_302,c_284])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n004.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 15:56:53 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.99/1.22  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.99/1.23  
% 1.99/1.23  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.99/1.23  %$ r2_hidden > r1_xboole_0 > v1_xboole_0 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3 > #skF_1
% 1.99/1.23  
% 1.99/1.23  %Foreground sorts:
% 1.99/1.23  
% 1.99/1.23  
% 1.99/1.23  %Background operators:
% 1.99/1.23  
% 1.99/1.23  
% 1.99/1.23  %Foreground operators:
% 1.99/1.23  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.99/1.23  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.99/1.23  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.99/1.23  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 1.99/1.23  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.99/1.23  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.99/1.23  tff('#skF_5', type, '#skF_5': $i).
% 1.99/1.23  tff('#skF_6', type, '#skF_6': $i).
% 1.99/1.23  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.99/1.23  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.99/1.23  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 1.99/1.23  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.99/1.23  tff(k3_tarski, type, k3_tarski: $i > $i).
% 1.99/1.23  tff('#skF_4', type, '#skF_4': $i).
% 1.99/1.23  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 1.99/1.23  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.99/1.23  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.99/1.23  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.99/1.23  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.99/1.23  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.99/1.23  
% 2.07/1.24  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.07/1.24  tff(f_77, negated_conjecture, ~(![A, B, C]: ~(k2_xboole_0(k2_tarski(A, B), C) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t50_zfmisc_1)).
% 2.07/1.24  tff(f_50, axiom, (![A, B]: (~v1_xboole_0(A) => ~v1_xboole_0(k2_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc5_xboole_0)).
% 2.07/1.24  tff(f_30, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 2.07/1.24  tff(f_54, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 2.07/1.24  tff(f_52, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 2.07/1.24  tff(f_44, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 2.07/1.24  tff(f_56, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 2.07/1.24  tff(f_73, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 2.07/1.24  tff(f_65, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_tarski)).
% 2.07/1.24  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 2.07/1.24  tff(c_44, plain, (k2_xboole_0(k2_tarski('#skF_4', '#skF_5'), '#skF_6')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.07/1.24  tff(c_10, plain, (![B_8, A_7]: (~v1_xboole_0(k2_xboole_0(B_8, A_7)) | v1_xboole_0(A_7))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.07/1.24  tff(c_114, plain, (~v1_xboole_0(k1_xboole_0) | v1_xboole_0('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_44, c_10])).
% 2.07/1.24  tff(c_118, plain, (v1_xboole_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_114])).
% 2.07/1.24  tff(c_4, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_30])).
% 2.07/1.24  tff(c_123, plain, (k1_xboole_0='#skF_6'), inference(resolution, [status(thm)], [c_118, c_4])).
% 2.07/1.24  tff(c_14, plain, (![A_10]: (r1_xboole_0(A_10, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.07/1.24  tff(c_127, plain, (![A_10]: (r1_xboole_0(A_10, '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_123, c_14])).
% 2.07/1.24  tff(c_12, plain, (![A_9]: (k3_xboole_0(A_9, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.07/1.24  tff(c_126, plain, (![A_9]: (k3_xboole_0(A_9, '#skF_6')='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_123, c_123, c_12])).
% 2.07/1.24  tff(c_297, plain, (![A_52, B_53, C_54]: (~r1_xboole_0(A_52, B_53) | ~r2_hidden(C_54, k3_xboole_0(A_52, B_53)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.07/1.24  tff(c_300, plain, (![A_9, C_54]: (~r1_xboole_0(A_9, '#skF_6') | ~r2_hidden(C_54, '#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_126, c_297])).
% 2.07/1.24  tff(c_302, plain, (![C_54]: (~r2_hidden(C_54, '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_127, c_300])).
% 2.07/1.24  tff(c_124, plain, (k2_xboole_0(k2_tarski('#skF_4', '#skF_5'), '#skF_6')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_123, c_44])).
% 2.07/1.24  tff(c_16, plain, (![B_12, A_11]: (k2_tarski(B_12, A_11)=k2_tarski(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.07/1.24  tff(c_157, plain, (![A_44, B_45]: (k3_tarski(k2_tarski(A_44, B_45))=k2_xboole_0(A_44, B_45))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.07/1.24  tff(c_181, plain, (![B_48, A_49]: (k3_tarski(k2_tarski(B_48, A_49))=k2_xboole_0(A_49, B_48))), inference(superposition, [status(thm), theory('equality')], [c_16, c_157])).
% 2.07/1.24  tff(c_42, plain, (![A_28, B_29]: (k3_tarski(k2_tarski(A_28, B_29))=k2_xboole_0(A_28, B_29))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.07/1.24  tff(c_204, plain, (![B_50, A_51]: (k2_xboole_0(B_50, A_51)=k2_xboole_0(A_51, B_50))), inference(superposition, [status(thm), theory('equality')], [c_181, c_42])).
% 2.07/1.24  tff(c_246, plain, (k2_xboole_0('#skF_6', k2_tarski('#skF_4', '#skF_5'))='#skF_6'), inference(superposition, [status(thm), theory('equality')], [c_124, c_204])).
% 2.07/1.24  tff(c_258, plain, (~v1_xboole_0('#skF_6') | v1_xboole_0(k2_tarski('#skF_4', '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_246, c_10])).
% 2.07/1.24  tff(c_262, plain, (v1_xboole_0(k2_tarski('#skF_4', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_118, c_258])).
% 2.07/1.24  tff(c_125, plain, (![A_1]: (A_1='#skF_6' | ~v1_xboole_0(A_1))), inference(demodulation, [status(thm), theory('equality')], [c_123, c_4])).
% 2.07/1.24  tff(c_267, plain, (k2_tarski('#skF_4', '#skF_5')='#skF_6'), inference(resolution, [status(thm)], [c_262, c_125])).
% 2.07/1.24  tff(c_22, plain, (![D_18, B_14]: (r2_hidden(D_18, k2_tarski(D_18, B_14)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.07/1.24  tff(c_284, plain, (r2_hidden('#skF_4', '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_267, c_22])).
% 2.07/1.24  tff(c_305, plain, $false, inference(negUnitSimplification, [status(thm)], [c_302, c_284])).
% 2.07/1.24  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.07/1.24  
% 2.07/1.24  Inference rules
% 2.07/1.24  ----------------------
% 2.07/1.24  #Ref     : 0
% 2.07/1.24  #Sup     : 67
% 2.07/1.24  #Fact    : 0
% 2.07/1.24  #Define  : 0
% 2.07/1.24  #Split   : 0
% 2.07/1.24  #Chain   : 0
% 2.07/1.24  #Close   : 0
% 2.07/1.24  
% 2.07/1.24  Ordering : KBO
% 2.07/1.24  
% 2.07/1.24  Simplification rules
% 2.07/1.24  ----------------------
% 2.07/1.24  #Subsume      : 0
% 2.07/1.24  #Demod        : 24
% 2.07/1.24  #Tautology    : 50
% 2.07/1.24  #SimpNegUnit  : 2
% 2.07/1.24  #BackRed      : 10
% 2.07/1.24  
% 2.07/1.24  #Partial instantiations: 0
% 2.07/1.24  #Strategies tried      : 1
% 2.07/1.24  
% 2.07/1.24  Timing (in seconds)
% 2.07/1.24  ----------------------
% 2.07/1.24  Preprocessing        : 0.31
% 2.07/1.24  Parsing              : 0.16
% 2.07/1.24  CNF conversion       : 0.02
% 2.07/1.24  Main loop            : 0.17
% 2.07/1.24  Inferencing          : 0.06
% 2.07/1.24  Reduction            : 0.06
% 2.07/1.24  Demodulation         : 0.05
% 2.07/1.24  BG Simplification    : 0.01
% 2.07/1.24  Subsumption          : 0.03
% 2.07/1.24  Abstraction          : 0.01
% 2.07/1.24  MUC search           : 0.00
% 2.07/1.24  Cooper               : 0.00
% 2.07/1.24  Total                : 0.51
% 2.07/1.25  Index Insertion      : 0.00
% 2.07/1.25  Index Deletion       : 0.00
% 2.07/1.25  Index Matching       : 0.00
% 2.07/1.25  BG Taut test         : 0.00
%------------------------------------------------------------------------------
