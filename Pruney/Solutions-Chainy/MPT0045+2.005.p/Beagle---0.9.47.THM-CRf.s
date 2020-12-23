%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:42:45 EST 2020

% Result     : Theorem 2.46s
% Output     : CNFRefutation 2.66s
% Verified   : 
% Statistics : Number of formulae       :   49 ( 122 expanded)
%              Number of leaves         :   17 (  49 expanded)
%              Depth                    :   10
%              Number of atoms          :   69 ( 237 expanded)
%              Number of equality atoms :   15 (  52 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k4_xboole_0 > #nlpp > k1_xboole_0 > #skF_5 > #skF_2 > #skF_4 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_53,negated_conjecture,(
    ~ ! [A,B] :
        ( r1_tarski(A,k4_xboole_0(B,A))
       => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_xboole_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_46,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_42,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_48,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

tff(c_32,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_181,plain,(
    ! [A_35,B_36] :
      ( r2_hidden('#skF_1'(A_35,B_36),A_35)
      | r1_tarski(A_35,B_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_196,plain,(
    ! [A_37] : r1_tarski(A_37,A_37) ),
    inference(resolution,[status(thm)],[c_181,c_4])).

tff(c_28,plain,(
    ! [A_12,B_13] :
      ( k4_xboole_0(A_12,B_13) = k1_xboole_0
      | ~ r1_tarski(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_200,plain,(
    ! [A_37] : k4_xboole_0(A_37,A_37) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_196,c_28])).

tff(c_788,plain,(
    ! [A_89,B_90,C_91] :
      ( r2_hidden('#skF_2'(A_89,B_90,C_91),A_89)
      | r2_hidden('#skF_3'(A_89,B_90,C_91),C_91)
      | k4_xboole_0(A_89,B_90) = C_91 ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_22,plain,(
    ! [A_6,B_7,C_8] :
      ( ~ r2_hidden('#skF_2'(A_6,B_7,C_8),B_7)
      | r2_hidden('#skF_3'(A_6,B_7,C_8),C_8)
      | k4_xboole_0(A_6,B_7) = C_8 ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_795,plain,(
    ! [A_89,C_91] :
      ( r2_hidden('#skF_3'(A_89,A_89,C_91),C_91)
      | k4_xboole_0(A_89,A_89) = C_91 ) ),
    inference(resolution,[status(thm)],[c_788,c_22])).

tff(c_851,plain,(
    ! [A_92,C_93] :
      ( r2_hidden('#skF_3'(A_92,A_92,C_93),C_93)
      | k1_xboole_0 = C_93 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_200,c_795])).

tff(c_202,plain,(
    ! [A_38] : k4_xboole_0(A_38,A_38) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_196,c_28])).

tff(c_30,plain,(
    ! [A_14,B_15] : r1_tarski(k4_xboole_0(A_14,B_15),A_14) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_217,plain,(
    ! [A_38] : r1_tarski(k1_xboole_0,A_38) ),
    inference(superposition,[status(thm),theory(equality)],[c_202,c_30])).

tff(c_34,plain,(
    r1_tarski('#skF_4',k4_xboole_0('#skF_5','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_36,plain,(
    ! [A_18,B_19] :
      ( k4_xboole_0(A_18,B_19) = k1_xboole_0
      | ~ r1_tarski(A_18,B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_44,plain,(
    k4_xboole_0('#skF_4',k4_xboole_0('#skF_5','#skF_4')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_34,c_36])).

tff(c_308,plain,(
    ! [D_52,A_53,B_54] :
      ( r2_hidden(D_52,k4_xboole_0(A_53,B_54))
      | r2_hidden(D_52,B_54)
      | ~ r2_hidden(D_52,A_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_400,plain,(
    ! [D_62] :
      ( r2_hidden(D_62,k1_xboole_0)
      | r2_hidden(D_62,k4_xboole_0('#skF_5','#skF_4'))
      | ~ r2_hidden(D_62,'#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_308])).

tff(c_10,plain,(
    ! [D_11,B_7,A_6] :
      ( ~ r2_hidden(D_11,B_7)
      | ~ r2_hidden(D_11,k4_xboole_0(A_6,B_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_420,plain,(
    ! [D_63] :
      ( r2_hidden(D_63,k1_xboole_0)
      | ~ r2_hidden(D_63,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_400,c_10])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_422,plain,(
    ! [D_63,B_2] :
      ( r2_hidden(D_63,B_2)
      | ~ r1_tarski(k1_xboole_0,B_2)
      | ~ r2_hidden(D_63,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_420,c_2])).

tff(c_436,plain,(
    ! [D_63,B_2] :
      ( r2_hidden(D_63,B_2)
      | ~ r2_hidden(D_63,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_217,c_422])).

tff(c_858,plain,(
    ! [A_92,B_2] :
      ( r2_hidden('#skF_3'(A_92,A_92,'#skF_4'),B_2)
      | k1_xboole_0 = '#skF_4' ) ),
    inference(resolution,[status(thm)],[c_851,c_436])).

tff(c_878,plain,(
    ! [A_92,B_2] : r2_hidden('#skF_3'(A_92,A_92,'#skF_4'),B_2) ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_858])).

tff(c_885,plain,(
    ! [A_94,B_95] : r2_hidden('#skF_3'(A_94,A_94,'#skF_4'),B_95) ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_858])).

tff(c_43,plain,(
    ! [A_14,B_15] : k4_xboole_0(k4_xboole_0(A_14,B_15),A_14) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_30,c_36])).

tff(c_164,plain,(
    ! [D_30,B_31,A_32] :
      ( ~ r2_hidden(D_30,B_31)
      | ~ r2_hidden(D_30,k4_xboole_0(A_32,B_31)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_179,plain,(
    ! [D_30,A_14] :
      ( ~ r2_hidden(D_30,A_14)
      | ~ r2_hidden(D_30,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_43,c_164])).

tff(c_439,plain,(
    ! [D_63] :
      ( ~ r2_hidden(D_63,k1_xboole_0)
      | ~ r2_hidden(D_63,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_420,c_179])).

tff(c_889,plain,(
    ! [A_94] : ~ r2_hidden('#skF_3'(A_94,A_94,'#skF_4'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_885,c_439])).

tff(c_911,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_878,c_889])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n008.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 11:28:30 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.46/1.35  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.46/1.35  
% 2.46/1.35  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.46/1.35  %$ r2_hidden > r1_tarski > k4_xboole_0 > #nlpp > k1_xboole_0 > #skF_5 > #skF_2 > #skF_4 > #skF_3 > #skF_1
% 2.46/1.35  
% 2.46/1.35  %Foreground sorts:
% 2.46/1.35  
% 2.46/1.35  
% 2.46/1.35  %Background operators:
% 2.46/1.35  
% 2.46/1.35  
% 2.46/1.35  %Foreground operators:
% 2.46/1.35  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.46/1.35  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.46/1.35  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.46/1.35  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.46/1.35  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.46/1.35  tff('#skF_5', type, '#skF_5': $i).
% 2.46/1.35  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.46/1.35  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.46/1.35  tff('#skF_4', type, '#skF_4': $i).
% 2.46/1.35  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 2.46/1.35  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.46/1.35  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.46/1.35  
% 2.66/1.37  tff(f_53, negated_conjecture, ~(![A, B]: (r1_tarski(A, k4_xboole_0(B, A)) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_xboole_1)).
% 2.66/1.37  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 2.66/1.37  tff(f_46, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 2.66/1.37  tff(f_42, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_xboole_0)).
% 2.66/1.37  tff(f_48, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 2.66/1.37  tff(c_32, plain, (k1_xboole_0!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.66/1.37  tff(c_181, plain, (![A_35, B_36]: (r2_hidden('#skF_1'(A_35, B_36), A_35) | r1_tarski(A_35, B_36))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.66/1.37  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.66/1.37  tff(c_196, plain, (![A_37]: (r1_tarski(A_37, A_37))), inference(resolution, [status(thm)], [c_181, c_4])).
% 2.66/1.37  tff(c_28, plain, (![A_12, B_13]: (k4_xboole_0(A_12, B_13)=k1_xboole_0 | ~r1_tarski(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.66/1.37  tff(c_200, plain, (![A_37]: (k4_xboole_0(A_37, A_37)=k1_xboole_0)), inference(resolution, [status(thm)], [c_196, c_28])).
% 2.66/1.37  tff(c_788, plain, (![A_89, B_90, C_91]: (r2_hidden('#skF_2'(A_89, B_90, C_91), A_89) | r2_hidden('#skF_3'(A_89, B_90, C_91), C_91) | k4_xboole_0(A_89, B_90)=C_91)), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.66/1.37  tff(c_22, plain, (![A_6, B_7, C_8]: (~r2_hidden('#skF_2'(A_6, B_7, C_8), B_7) | r2_hidden('#skF_3'(A_6, B_7, C_8), C_8) | k4_xboole_0(A_6, B_7)=C_8)), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.66/1.37  tff(c_795, plain, (![A_89, C_91]: (r2_hidden('#skF_3'(A_89, A_89, C_91), C_91) | k4_xboole_0(A_89, A_89)=C_91)), inference(resolution, [status(thm)], [c_788, c_22])).
% 2.66/1.37  tff(c_851, plain, (![A_92, C_93]: (r2_hidden('#skF_3'(A_92, A_92, C_93), C_93) | k1_xboole_0=C_93)), inference(demodulation, [status(thm), theory('equality')], [c_200, c_795])).
% 2.66/1.37  tff(c_202, plain, (![A_38]: (k4_xboole_0(A_38, A_38)=k1_xboole_0)), inference(resolution, [status(thm)], [c_196, c_28])).
% 2.66/1.37  tff(c_30, plain, (![A_14, B_15]: (r1_tarski(k4_xboole_0(A_14, B_15), A_14))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.66/1.37  tff(c_217, plain, (![A_38]: (r1_tarski(k1_xboole_0, A_38))), inference(superposition, [status(thm), theory('equality')], [c_202, c_30])).
% 2.66/1.37  tff(c_34, plain, (r1_tarski('#skF_4', k4_xboole_0('#skF_5', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.66/1.37  tff(c_36, plain, (![A_18, B_19]: (k4_xboole_0(A_18, B_19)=k1_xboole_0 | ~r1_tarski(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.66/1.37  tff(c_44, plain, (k4_xboole_0('#skF_4', k4_xboole_0('#skF_5', '#skF_4'))=k1_xboole_0), inference(resolution, [status(thm)], [c_34, c_36])).
% 2.66/1.37  tff(c_308, plain, (![D_52, A_53, B_54]: (r2_hidden(D_52, k4_xboole_0(A_53, B_54)) | r2_hidden(D_52, B_54) | ~r2_hidden(D_52, A_53))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.66/1.37  tff(c_400, plain, (![D_62]: (r2_hidden(D_62, k1_xboole_0) | r2_hidden(D_62, k4_xboole_0('#skF_5', '#skF_4')) | ~r2_hidden(D_62, '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_44, c_308])).
% 2.66/1.37  tff(c_10, plain, (![D_11, B_7, A_6]: (~r2_hidden(D_11, B_7) | ~r2_hidden(D_11, k4_xboole_0(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.66/1.37  tff(c_420, plain, (![D_63]: (r2_hidden(D_63, k1_xboole_0) | ~r2_hidden(D_63, '#skF_4'))), inference(resolution, [status(thm)], [c_400, c_10])).
% 2.66/1.37  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.66/1.37  tff(c_422, plain, (![D_63, B_2]: (r2_hidden(D_63, B_2) | ~r1_tarski(k1_xboole_0, B_2) | ~r2_hidden(D_63, '#skF_4'))), inference(resolution, [status(thm)], [c_420, c_2])).
% 2.66/1.37  tff(c_436, plain, (![D_63, B_2]: (r2_hidden(D_63, B_2) | ~r2_hidden(D_63, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_217, c_422])).
% 2.66/1.37  tff(c_858, plain, (![A_92, B_2]: (r2_hidden('#skF_3'(A_92, A_92, '#skF_4'), B_2) | k1_xboole_0='#skF_4')), inference(resolution, [status(thm)], [c_851, c_436])).
% 2.66/1.37  tff(c_878, plain, (![A_92, B_2]: (r2_hidden('#skF_3'(A_92, A_92, '#skF_4'), B_2))), inference(negUnitSimplification, [status(thm)], [c_32, c_858])).
% 2.66/1.37  tff(c_885, plain, (![A_94, B_95]: (r2_hidden('#skF_3'(A_94, A_94, '#skF_4'), B_95))), inference(negUnitSimplification, [status(thm)], [c_32, c_858])).
% 2.66/1.37  tff(c_43, plain, (![A_14, B_15]: (k4_xboole_0(k4_xboole_0(A_14, B_15), A_14)=k1_xboole_0)), inference(resolution, [status(thm)], [c_30, c_36])).
% 2.66/1.37  tff(c_164, plain, (![D_30, B_31, A_32]: (~r2_hidden(D_30, B_31) | ~r2_hidden(D_30, k4_xboole_0(A_32, B_31)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.66/1.37  tff(c_179, plain, (![D_30, A_14]: (~r2_hidden(D_30, A_14) | ~r2_hidden(D_30, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_43, c_164])).
% 2.66/1.37  tff(c_439, plain, (![D_63]: (~r2_hidden(D_63, k1_xboole_0) | ~r2_hidden(D_63, '#skF_4'))), inference(resolution, [status(thm)], [c_420, c_179])).
% 2.66/1.37  tff(c_889, plain, (![A_94]: (~r2_hidden('#skF_3'(A_94, A_94, '#skF_4'), '#skF_4'))), inference(resolution, [status(thm)], [c_885, c_439])).
% 2.66/1.37  tff(c_911, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_878, c_889])).
% 2.66/1.37  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.66/1.37  
% 2.66/1.37  Inference rules
% 2.66/1.37  ----------------------
% 2.66/1.37  #Ref     : 0
% 2.66/1.37  #Sup     : 204
% 2.66/1.37  #Fact    : 0
% 2.66/1.37  #Define  : 0
% 2.66/1.37  #Split   : 0
% 2.66/1.37  #Chain   : 0
% 2.66/1.37  #Close   : 0
% 2.66/1.37  
% 2.66/1.37  Ordering : KBO
% 2.66/1.37  
% 2.66/1.37  Simplification rules
% 2.66/1.37  ----------------------
% 2.66/1.37  #Subsume      : 38
% 2.66/1.37  #Demod        : 87
% 2.66/1.37  #Tautology    : 109
% 2.66/1.37  #SimpNegUnit  : 1
% 2.66/1.37  #BackRed      : 0
% 2.66/1.37  
% 2.66/1.37  #Partial instantiations: 0
% 2.66/1.37  #Strategies tried      : 1
% 2.66/1.37  
% 2.66/1.37  Timing (in seconds)
% 2.66/1.37  ----------------------
% 2.66/1.37  Preprocessing        : 0.27
% 2.66/1.37  Parsing              : 0.14
% 2.66/1.37  CNF conversion       : 0.02
% 2.66/1.37  Main loop            : 0.31
% 2.66/1.37  Inferencing          : 0.12
% 2.66/1.37  Reduction            : 0.09
% 2.66/1.37  Demodulation         : 0.07
% 2.66/1.37  BG Simplification    : 0.02
% 2.66/1.37  Subsumption          : 0.06
% 2.66/1.37  Abstraction          : 0.01
% 2.66/1.37  MUC search           : 0.00
% 2.66/1.37  Cooper               : 0.00
% 2.66/1.37  Total                : 0.61
% 2.66/1.37  Index Insertion      : 0.00
% 2.66/1.37  Index Deletion       : 0.00
% 2.66/1.37  Index Matching       : 0.00
% 2.66/1.37  BG Taut test         : 0.00
%------------------------------------------------------------------------------
