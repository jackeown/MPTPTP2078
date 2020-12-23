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
% DateTime   : Thu Dec  3 09:51:47 EST 2020

% Result     : Theorem 2.11s
% Output     : CNFRefutation 2.22s
% Verified   : 
% Statistics : Number of formulae       :   54 ( 131 expanded)
%              Number of leaves         :   26 (  56 expanded)
%              Depth                    :   14
%              Number of atoms          :   59 ( 186 expanded)
%              Number of equality atoms :   13 (  45 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_xboole_0 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_xboole_0 > #skF_1 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(f_33,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_43,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_69,negated_conjecture,(
    ~ ! [A,B,C] : k2_xboole_0(k2_tarski(A,B),C) != k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_zfmisc_1)).

tff(f_42,axiom,(
    ! [A,B,C] :
      ( C = k2_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            | r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_xboole_0)).

tff(f_53,axiom,(
    ! [A,B] :
      ~ ( v1_xboole_0(A)
        & A != B
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_boole)).

tff(f_45,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_65,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_tarski(A,B),C)
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).

tff(c_6,plain,(
    ! [A_3] :
      ( v1_xboole_0(A_3)
      | r2_hidden('#skF_1'(A_3),A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_26,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_61,plain,(
    ! [B_32,A_33] : k2_xboole_0(B_32,A_33) = k2_xboole_0(A_33,B_32) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_44,plain,(
    k2_xboole_0(k2_tarski('#skF_4','#skF_5'),'#skF_6') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_76,plain,(
    k2_xboole_0('#skF_6',k2_tarski('#skF_4','#skF_5')) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_61,c_44])).

tff(c_136,plain,(
    ! [D_39,A_40,B_41] :
      ( ~ r2_hidden(D_39,A_40)
      | r2_hidden(D_39,k2_xboole_0(A_40,B_41)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_154,plain,(
    ! [D_45] :
      ( ~ r2_hidden(D_45,'#skF_6')
      | r2_hidden(D_45,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_76,c_136])).

tff(c_4,plain,(
    ! [B_6,A_3] :
      ( ~ r2_hidden(B_6,A_3)
      | ~ v1_xboole_0(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_157,plain,(
    ! [D_45] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | ~ r2_hidden(D_45,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_154,c_4])).

tff(c_161,plain,(
    ! [D_46] : ~ r2_hidden(D_46,'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_157])).

tff(c_166,plain,(
    v1_xboole_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_6,c_161])).

tff(c_47,plain,(
    ! [B_29,A_30] :
      ( ~ v1_xboole_0(B_29)
      | B_29 = A_30
      | ~ v1_xboole_0(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_50,plain,(
    ! [A_30] :
      ( k1_xboole_0 = A_30
      | ~ v1_xboole_0(A_30) ) ),
    inference(resolution,[status(thm)],[c_26,c_47])).

tff(c_172,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(resolution,[status(thm)],[c_166,c_50])).

tff(c_28,plain,(
    ! [A_13] : r1_tarski(k1_xboole_0,A_13) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_184,plain,(
    ! [A_13] : r1_tarski('#skF_6',A_13) ),
    inference(demodulation,[status(thm),theory(equality)],[c_172,c_28])).

tff(c_160,plain,(
    ! [D_45] : ~ r2_hidden(D_45,'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_157])).

tff(c_151,plain,(
    ! [D_39] :
      ( ~ r2_hidden(D_39,k2_tarski('#skF_4','#skF_5'))
      | r2_hidden(D_39,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_136])).

tff(c_180,plain,(
    ! [D_39] :
      ( ~ r2_hidden(D_39,k2_tarski('#skF_4','#skF_5'))
      | r2_hidden(D_39,'#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_172,c_151])).

tff(c_199,plain,(
    ! [D_50] : ~ r2_hidden(D_50,k2_tarski('#skF_4','#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_160,c_180])).

tff(c_204,plain,(
    v1_xboole_0(k2_tarski('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_6,c_199])).

tff(c_30,plain,(
    ! [B_15,A_14] :
      ( ~ v1_xboole_0(B_15)
      | B_15 = A_14
      | ~ v1_xboole_0(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_173,plain,(
    ! [A_14] :
      ( A_14 = '#skF_6'
      | ~ v1_xboole_0(A_14) ) ),
    inference(resolution,[status(thm)],[c_166,c_30])).

tff(c_221,plain,(
    k2_tarski('#skF_4','#skF_5') = '#skF_6' ),
    inference(resolution,[status(thm)],[c_204,c_173])).

tff(c_42,plain,(
    ! [A_23,C_25,B_24] :
      ( r2_hidden(A_23,C_25)
      | ~ r1_tarski(k2_tarski(A_23,B_24),C_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_229,plain,(
    ! [C_25] :
      ( r2_hidden('#skF_4',C_25)
      | ~ r1_tarski('#skF_6',C_25) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_221,c_42])).

tff(c_238,plain,(
    ! [C_54] : r2_hidden('#skF_4',C_54) ),
    inference(demodulation,[status(thm),theory(equality)],[c_184,c_229])).

tff(c_246,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_238,c_160])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n023.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 19:02:05 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.11/1.33  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.11/1.34  
% 2.11/1.34  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.11/1.35  %$ r2_hidden > r1_tarski > v1_xboole_0 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_xboole_0 > #skF_1 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3
% 2.11/1.35  
% 2.11/1.35  %Foreground sorts:
% 2.11/1.35  
% 2.11/1.35  
% 2.11/1.35  %Background operators:
% 2.11/1.35  
% 2.11/1.35  
% 2.11/1.35  %Foreground operators:
% 2.11/1.35  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.11/1.35  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.11/1.35  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.11/1.35  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.11/1.35  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.11/1.35  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.11/1.35  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.11/1.35  tff('#skF_5', type, '#skF_5': $i).
% 2.11/1.35  tff('#skF_6', type, '#skF_6': $i).
% 2.11/1.35  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.11/1.35  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.11/1.35  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.11/1.35  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.11/1.35  tff('#skF_4', type, '#skF_4': $i).
% 2.11/1.35  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 2.11/1.35  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.11/1.35  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.11/1.35  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.11/1.35  
% 2.22/1.36  tff(f_33, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 2.22/1.36  tff(f_43, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.22/1.36  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 2.22/1.36  tff(f_69, negated_conjecture, ~(![A, B, C]: ~(k2_xboole_0(k2_tarski(A, B), C) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t50_zfmisc_1)).
% 2.22/1.36  tff(f_42, axiom, (![A, B, C]: ((C = k2_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) | r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_xboole_0)).
% 2.22/1.36  tff(f_53, axiom, (![A, B]: ~((v1_xboole_0(A) & ~(A = B)) & v1_xboole_0(B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_boole)).
% 2.22/1.36  tff(f_45, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.22/1.36  tff(f_65, axiom, (![A, B, C]: (r1_tarski(k2_tarski(A, B), C) <=> (r2_hidden(A, C) & r2_hidden(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 2.22/1.36  tff(c_6, plain, (![A_3]: (v1_xboole_0(A_3) | r2_hidden('#skF_1'(A_3), A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.22/1.36  tff(c_26, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.22/1.36  tff(c_61, plain, (![B_32, A_33]: (k2_xboole_0(B_32, A_33)=k2_xboole_0(A_33, B_32))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.22/1.36  tff(c_44, plain, (k2_xboole_0(k2_tarski('#skF_4', '#skF_5'), '#skF_6')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.22/1.36  tff(c_76, plain, (k2_xboole_0('#skF_6', k2_tarski('#skF_4', '#skF_5'))=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_61, c_44])).
% 2.22/1.36  tff(c_136, plain, (![D_39, A_40, B_41]: (~r2_hidden(D_39, A_40) | r2_hidden(D_39, k2_xboole_0(A_40, B_41)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.22/1.36  tff(c_154, plain, (![D_45]: (~r2_hidden(D_45, '#skF_6') | r2_hidden(D_45, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_76, c_136])).
% 2.22/1.36  tff(c_4, plain, (![B_6, A_3]: (~r2_hidden(B_6, A_3) | ~v1_xboole_0(A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.22/1.36  tff(c_157, plain, (![D_45]: (~v1_xboole_0(k1_xboole_0) | ~r2_hidden(D_45, '#skF_6'))), inference(resolution, [status(thm)], [c_154, c_4])).
% 2.22/1.36  tff(c_161, plain, (![D_46]: (~r2_hidden(D_46, '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_157])).
% 2.22/1.36  tff(c_166, plain, (v1_xboole_0('#skF_6')), inference(resolution, [status(thm)], [c_6, c_161])).
% 2.22/1.36  tff(c_47, plain, (![B_29, A_30]: (~v1_xboole_0(B_29) | B_29=A_30 | ~v1_xboole_0(A_30))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.22/1.36  tff(c_50, plain, (![A_30]: (k1_xboole_0=A_30 | ~v1_xboole_0(A_30))), inference(resolution, [status(thm)], [c_26, c_47])).
% 2.22/1.36  tff(c_172, plain, (k1_xboole_0='#skF_6'), inference(resolution, [status(thm)], [c_166, c_50])).
% 2.22/1.36  tff(c_28, plain, (![A_13]: (r1_tarski(k1_xboole_0, A_13))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.22/1.36  tff(c_184, plain, (![A_13]: (r1_tarski('#skF_6', A_13))), inference(demodulation, [status(thm), theory('equality')], [c_172, c_28])).
% 2.22/1.36  tff(c_160, plain, (![D_45]: (~r2_hidden(D_45, '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_157])).
% 2.22/1.36  tff(c_151, plain, (![D_39]: (~r2_hidden(D_39, k2_tarski('#skF_4', '#skF_5')) | r2_hidden(D_39, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_44, c_136])).
% 2.22/1.36  tff(c_180, plain, (![D_39]: (~r2_hidden(D_39, k2_tarski('#skF_4', '#skF_5')) | r2_hidden(D_39, '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_172, c_151])).
% 2.22/1.36  tff(c_199, plain, (![D_50]: (~r2_hidden(D_50, k2_tarski('#skF_4', '#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_160, c_180])).
% 2.22/1.36  tff(c_204, plain, (v1_xboole_0(k2_tarski('#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_6, c_199])).
% 2.22/1.36  tff(c_30, plain, (![B_15, A_14]: (~v1_xboole_0(B_15) | B_15=A_14 | ~v1_xboole_0(A_14))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.22/1.36  tff(c_173, plain, (![A_14]: (A_14='#skF_6' | ~v1_xboole_0(A_14))), inference(resolution, [status(thm)], [c_166, c_30])).
% 2.22/1.36  tff(c_221, plain, (k2_tarski('#skF_4', '#skF_5')='#skF_6'), inference(resolution, [status(thm)], [c_204, c_173])).
% 2.22/1.36  tff(c_42, plain, (![A_23, C_25, B_24]: (r2_hidden(A_23, C_25) | ~r1_tarski(k2_tarski(A_23, B_24), C_25))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.22/1.36  tff(c_229, plain, (![C_25]: (r2_hidden('#skF_4', C_25) | ~r1_tarski('#skF_6', C_25))), inference(superposition, [status(thm), theory('equality')], [c_221, c_42])).
% 2.22/1.36  tff(c_238, plain, (![C_54]: (r2_hidden('#skF_4', C_54))), inference(demodulation, [status(thm), theory('equality')], [c_184, c_229])).
% 2.22/1.36  tff(c_246, plain, $false, inference(resolution, [status(thm)], [c_238, c_160])).
% 2.22/1.36  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.22/1.36  
% 2.22/1.36  Inference rules
% 2.22/1.36  ----------------------
% 2.22/1.36  #Ref     : 0
% 2.22/1.36  #Sup     : 48
% 2.22/1.36  #Fact    : 0
% 2.22/1.36  #Define  : 0
% 2.22/1.36  #Split   : 0
% 2.22/1.36  #Chain   : 0
% 2.22/1.36  #Close   : 0
% 2.22/1.36  
% 2.22/1.36  Ordering : KBO
% 2.22/1.36  
% 2.22/1.36  Simplification rules
% 2.22/1.36  ----------------------
% 2.22/1.36  #Subsume      : 5
% 2.22/1.36  #Demod        : 15
% 2.22/1.36  #Tautology    : 28
% 2.22/1.36  #SimpNegUnit  : 1
% 2.22/1.36  #BackRed      : 8
% 2.22/1.36  
% 2.22/1.36  #Partial instantiations: 0
% 2.22/1.36  #Strategies tried      : 1
% 2.22/1.36  
% 2.22/1.36  Timing (in seconds)
% 2.22/1.36  ----------------------
% 2.22/1.36  Preprocessing        : 0.39
% 2.22/1.36  Parsing              : 0.19
% 2.22/1.36  CNF conversion       : 0.03
% 2.22/1.36  Main loop            : 0.19
% 2.22/1.36  Inferencing          : 0.06
% 2.22/1.37  Reduction            : 0.06
% 2.22/1.37  Demodulation         : 0.05
% 2.22/1.37  BG Simplification    : 0.02
% 2.22/1.37  Subsumption          : 0.04
% 2.22/1.37  Abstraction          : 0.02
% 2.22/1.37  MUC search           : 0.00
% 2.22/1.37  Cooper               : 0.00
% 2.22/1.37  Total                : 0.62
% 2.22/1.37  Index Insertion      : 0.00
% 2.22/1.37  Index Deletion       : 0.00
% 2.22/1.37  Index Matching       : 0.00
% 2.22/1.37  BG Taut test         : 0.00
%------------------------------------------------------------------------------
