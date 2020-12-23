%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:57:11 EST 2020

% Result     : Theorem 2.21s
% Output     : CNFRefutation 2.21s
% Verified   : 
% Statistics : Number of formulae       :   50 (  68 expanded)
%              Number of leaves         :   24 (  35 expanded)
%              Depth                    :    8
%              Number of atoms          :   64 ( 110 expanded)
%              Number of equality atoms :   12 (  19 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k3_xboole_0 > #nlpp > k1_setfam_1 > k1_xboole_0 > #skF_6 > #skF_4 > #skF_9 > #skF_8 > #skF_3 > #skF_2 > #skF_7 > #skF_1 > #skF_5

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_3',type,(
    '#skF_3': $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_80,negated_conjecture,(
    ~ ! [A,B] :
        ( r2_hidden(A,B)
       => r1_tarski(k1_setfam_1(B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_setfam_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_75,axiom,(
    ! [A,B] :
      ( ( A != k1_xboole_0
       => ( B = k1_setfam_1(A)
        <=> ! [C] :
              ( r2_hidden(C,B)
            <=> ! [D] :
                  ( r2_hidden(D,A)
                 => r2_hidden(C,D) ) ) ) )
      & ( A = k1_xboole_0
       => ( B = k1_setfam_1(A)
        <=> B = k1_xboole_0 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_setfam_1)).

tff(f_56,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_54,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_46,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(c_38,plain,(
    ~ r1_tarski(k1_setfam_1('#skF_9'),'#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_77,plain,(
    ! [A_43,B_44] :
      ( ~ r2_hidden('#skF_1'(A_43,B_44),B_44)
      | r1_tarski(A_43,B_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_82,plain,(
    ! [A_1] : r1_tarski(A_1,A_1) ),
    inference(resolution,[status(thm)],[c_6,c_77])).

tff(c_40,plain,(
    r2_hidden('#skF_8','#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_244,plain,(
    ! [C_72,D_73,A_74] :
      ( r2_hidden(C_72,D_73)
      | ~ r2_hidden(D_73,A_74)
      | ~ r2_hidden(C_72,k1_setfam_1(A_74))
      | k1_xboole_0 = A_74 ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_265,plain,(
    ! [C_72] :
      ( r2_hidden(C_72,'#skF_8')
      | ~ r2_hidden(C_72,k1_setfam_1('#skF_9'))
      | k1_xboole_0 = '#skF_9' ) ),
    inference(resolution,[status(thm)],[c_40,c_244])).

tff(c_266,plain,(
    k1_xboole_0 = '#skF_9' ),
    inference(splitLeft,[status(thm)],[c_265])).

tff(c_103,plain,(
    ! [C_51,B_52,A_53] :
      ( r2_hidden(C_51,B_52)
      | ~ r2_hidden(C_51,A_53)
      | ~ r1_tarski(A_53,B_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_126,plain,(
    ! [B_56] :
      ( r2_hidden('#skF_8',B_56)
      | ~ r1_tarski('#skF_9',B_56) ) ),
    inference(resolution,[status(thm)],[c_40,c_103])).

tff(c_14,plain,(
    ! [A_13] : r1_xboole_0(A_13,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_12,plain,(
    ! [A_11] :
      ( r2_hidden('#skF_3'(A_11),A_11)
      | k1_xboole_0 = A_11 ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_49,plain,(
    ! [A_37,B_38,C_39] :
      ( ~ r1_xboole_0(A_37,B_38)
      | ~ r2_hidden(C_39,k3_xboole_0(A_37,B_38)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_60,plain,(
    ! [A_40,B_41] :
      ( ~ r1_xboole_0(A_40,B_41)
      | k3_xboole_0(A_40,B_41) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_12,c_49])).

tff(c_65,plain,(
    ! [A_42] : k3_xboole_0(A_42,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_14,c_60])).

tff(c_10,plain,(
    ! [A_6,B_7,C_10] :
      ( ~ r1_xboole_0(A_6,B_7)
      | ~ r2_hidden(C_10,k3_xboole_0(A_6,B_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_70,plain,(
    ! [A_42,C_10] :
      ( ~ r1_xboole_0(A_42,k1_xboole_0)
      | ~ r2_hidden(C_10,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_65,c_10])).

tff(c_75,plain,(
    ! [C_10] : ~ r2_hidden(C_10,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_70])).

tff(c_138,plain,(
    ~ r1_tarski('#skF_9',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_126,c_75])).

tff(c_272,plain,(
    ~ r1_tarski('#skF_9','#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_266,c_138])).

tff(c_282,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_272])).

tff(c_285,plain,(
    ! [C_75] :
      ( r2_hidden(C_75,'#skF_8')
      | ~ r2_hidden(C_75,k1_setfam_1('#skF_9')) ) ),
    inference(splitRight,[status(thm)],[c_265])).

tff(c_466,plain,(
    ! [B_87] :
      ( r2_hidden('#skF_1'(k1_setfam_1('#skF_9'),B_87),'#skF_8')
      | r1_tarski(k1_setfam_1('#skF_9'),B_87) ) ),
    inference(resolution,[status(thm)],[c_6,c_285])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_474,plain,(
    r1_tarski(k1_setfam_1('#skF_9'),'#skF_8') ),
    inference(resolution,[status(thm)],[c_466,c_4])).

tff(c_480,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_38,c_474])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n007.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 20:00:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.21/1.28  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.21/1.28  
% 2.21/1.28  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.21/1.29  %$ r2_hidden > r1_xboole_0 > r1_tarski > k3_xboole_0 > #nlpp > k1_setfam_1 > k1_xboole_0 > #skF_6 > #skF_4 > #skF_9 > #skF_8 > #skF_3 > #skF_2 > #skF_7 > #skF_1 > #skF_5
% 2.21/1.29  
% 2.21/1.29  %Foreground sorts:
% 2.21/1.29  
% 2.21/1.29  
% 2.21/1.29  %Background operators:
% 2.21/1.29  
% 2.21/1.29  
% 2.21/1.29  %Foreground operators:
% 2.21/1.29  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 2.21/1.29  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.21/1.29  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.21/1.29  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.21/1.29  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 2.21/1.29  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.21/1.29  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.21/1.29  tff('#skF_9', type, '#skF_9': $i).
% 2.21/1.29  tff('#skF_8', type, '#skF_8': $i).
% 2.21/1.29  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.21/1.29  tff('#skF_3', type, '#skF_3': $i > $i).
% 2.21/1.29  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.21/1.29  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.21/1.29  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.21/1.29  tff('#skF_7', type, '#skF_7': ($i * $i) > $i).
% 2.21/1.29  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.21/1.29  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 2.21/1.29  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.21/1.29  
% 2.21/1.30  tff(f_80, negated_conjecture, ~(![A, B]: (r2_hidden(A, B) => r1_tarski(k1_setfam_1(B), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_setfam_1)).
% 2.21/1.30  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 2.21/1.30  tff(f_75, axiom, (![A, B]: ((~(A = k1_xboole_0) => ((B = k1_setfam_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (![D]: (r2_hidden(D, A) => r2_hidden(C, D))))))) & ((A = k1_xboole_0) => ((B = k1_setfam_1(A)) <=> (B = k1_xboole_0))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_setfam_1)).
% 2.21/1.30  tff(f_56, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 2.21/1.30  tff(f_54, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 2.21/1.30  tff(f_46, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 2.21/1.30  tff(c_38, plain, (~r1_tarski(k1_setfam_1('#skF_9'), '#skF_8')), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.21/1.30  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.21/1.30  tff(c_77, plain, (![A_43, B_44]: (~r2_hidden('#skF_1'(A_43, B_44), B_44) | r1_tarski(A_43, B_44))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.21/1.30  tff(c_82, plain, (![A_1]: (r1_tarski(A_1, A_1))), inference(resolution, [status(thm)], [c_6, c_77])).
% 2.21/1.30  tff(c_40, plain, (r2_hidden('#skF_8', '#skF_9')), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.21/1.30  tff(c_244, plain, (![C_72, D_73, A_74]: (r2_hidden(C_72, D_73) | ~r2_hidden(D_73, A_74) | ~r2_hidden(C_72, k1_setfam_1(A_74)) | k1_xboole_0=A_74)), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.21/1.30  tff(c_265, plain, (![C_72]: (r2_hidden(C_72, '#skF_8') | ~r2_hidden(C_72, k1_setfam_1('#skF_9')) | k1_xboole_0='#skF_9')), inference(resolution, [status(thm)], [c_40, c_244])).
% 2.21/1.30  tff(c_266, plain, (k1_xboole_0='#skF_9'), inference(splitLeft, [status(thm)], [c_265])).
% 2.21/1.30  tff(c_103, plain, (![C_51, B_52, A_53]: (r2_hidden(C_51, B_52) | ~r2_hidden(C_51, A_53) | ~r1_tarski(A_53, B_52))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.21/1.30  tff(c_126, plain, (![B_56]: (r2_hidden('#skF_8', B_56) | ~r1_tarski('#skF_9', B_56))), inference(resolution, [status(thm)], [c_40, c_103])).
% 2.21/1.30  tff(c_14, plain, (![A_13]: (r1_xboole_0(A_13, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.21/1.30  tff(c_12, plain, (![A_11]: (r2_hidden('#skF_3'(A_11), A_11) | k1_xboole_0=A_11)), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.21/1.30  tff(c_49, plain, (![A_37, B_38, C_39]: (~r1_xboole_0(A_37, B_38) | ~r2_hidden(C_39, k3_xboole_0(A_37, B_38)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.21/1.30  tff(c_60, plain, (![A_40, B_41]: (~r1_xboole_0(A_40, B_41) | k3_xboole_0(A_40, B_41)=k1_xboole_0)), inference(resolution, [status(thm)], [c_12, c_49])).
% 2.21/1.30  tff(c_65, plain, (![A_42]: (k3_xboole_0(A_42, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_14, c_60])).
% 2.21/1.30  tff(c_10, plain, (![A_6, B_7, C_10]: (~r1_xboole_0(A_6, B_7) | ~r2_hidden(C_10, k3_xboole_0(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.21/1.30  tff(c_70, plain, (![A_42, C_10]: (~r1_xboole_0(A_42, k1_xboole_0) | ~r2_hidden(C_10, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_65, c_10])).
% 2.21/1.30  tff(c_75, plain, (![C_10]: (~r2_hidden(C_10, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_70])).
% 2.21/1.30  tff(c_138, plain, (~r1_tarski('#skF_9', k1_xboole_0)), inference(resolution, [status(thm)], [c_126, c_75])).
% 2.21/1.30  tff(c_272, plain, (~r1_tarski('#skF_9', '#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_266, c_138])).
% 2.21/1.30  tff(c_282, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_82, c_272])).
% 2.21/1.30  tff(c_285, plain, (![C_75]: (r2_hidden(C_75, '#skF_8') | ~r2_hidden(C_75, k1_setfam_1('#skF_9')))), inference(splitRight, [status(thm)], [c_265])).
% 2.21/1.30  tff(c_466, plain, (![B_87]: (r2_hidden('#skF_1'(k1_setfam_1('#skF_9'), B_87), '#skF_8') | r1_tarski(k1_setfam_1('#skF_9'), B_87))), inference(resolution, [status(thm)], [c_6, c_285])).
% 2.21/1.30  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.21/1.30  tff(c_474, plain, (r1_tarski(k1_setfam_1('#skF_9'), '#skF_8')), inference(resolution, [status(thm)], [c_466, c_4])).
% 2.21/1.30  tff(c_480, plain, $false, inference(negUnitSimplification, [status(thm)], [c_38, c_38, c_474])).
% 2.21/1.30  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.21/1.30  
% 2.21/1.30  Inference rules
% 2.21/1.30  ----------------------
% 2.21/1.30  #Ref     : 0
% 2.21/1.30  #Sup     : 88
% 2.21/1.30  #Fact    : 0
% 2.21/1.30  #Define  : 0
% 2.21/1.30  #Split   : 3
% 2.21/1.30  #Chain   : 0
% 2.21/1.30  #Close   : 0
% 2.21/1.30  
% 2.21/1.30  Ordering : KBO
% 2.21/1.30  
% 2.21/1.30  Simplification rules
% 2.21/1.30  ----------------------
% 2.21/1.30  #Subsume      : 14
% 2.21/1.30  #Demod        : 34
% 2.21/1.30  #Tautology    : 18
% 2.21/1.30  #SimpNegUnit  : 3
% 2.21/1.30  #BackRed      : 16
% 2.21/1.30  
% 2.21/1.30  #Partial instantiations: 0
% 2.21/1.30  #Strategies tried      : 1
% 2.21/1.30  
% 2.21/1.30  Timing (in seconds)
% 2.21/1.30  ----------------------
% 2.21/1.30  Preprocessing        : 0.27
% 2.21/1.30  Parsing              : 0.14
% 2.21/1.30  CNF conversion       : 0.02
% 2.21/1.30  Main loop            : 0.26
% 2.21/1.30  Inferencing          : 0.09
% 2.21/1.30  Reduction            : 0.07
% 2.21/1.30  Demodulation         : 0.05
% 2.21/1.30  BG Simplification    : 0.02
% 2.21/1.30  Subsumption          : 0.07
% 2.21/1.30  Abstraction          : 0.01
% 2.21/1.30  MUC search           : 0.00
% 2.21/1.30  Cooper               : 0.00
% 2.21/1.30  Total                : 0.56
% 2.21/1.30  Index Insertion      : 0.00
% 2.21/1.30  Index Deletion       : 0.00
% 2.21/1.30  Index Matching       : 0.00
% 2.21/1.30  BG Taut test         : 0.00
%------------------------------------------------------------------------------
