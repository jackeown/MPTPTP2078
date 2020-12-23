%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:00:15 EST 2020

% Result     : Theorem 6.62s
% Output     : CNFRefutation 6.62s
% Verified   : 
% Statistics : Number of formulae       :   48 (  61 expanded)
%              Number of leaves         :   26 (  34 expanded)
%              Depth                    :   11
%              Number of atoms          :   56 (  96 expanded)
%              Number of equality atoms :   20 (  31 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_relat_1 > k2_enumset1 > k1_enumset1 > k8_relat_1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_setfam_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k8_relat_1,type,(
    k8_relat_1: ( $i * $i ) > $i )).

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

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_65,negated_conjecture,(
    ~ ! [A,B,C] :
        ( v1_relat_1(C)
       => ( r1_tarski(A,B)
         => k8_relat_1(A,k8_relat_1(B,C)) = k8_relat_1(A,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t130_relat_1)).

tff(f_46,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_42,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_48,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_58,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k8_relat_1(A,k8_relat_1(B,C)) = k8_relat_1(k3_xboole_0(A,B),C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t127_relat_1)).

tff(c_44,plain,(
    v1_relat_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_28,plain,(
    ! [A_13] : k4_xboole_0(A_13,k1_xboole_0) = A_13 ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_42,plain,(
    r1_tarski('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_543,plain,(
    ! [A_92,B_93,C_94] :
      ( r2_hidden('#skF_2'(A_92,B_93,C_94),A_92)
      | r2_hidden('#skF_3'(A_92,B_93,C_94),C_94)
      | k4_xboole_0(A_92,B_93) = C_94 ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_3024,plain,(
    ! [A_237,B_238,C_239,B_240] :
      ( r2_hidden('#skF_2'(A_237,B_238,C_239),B_240)
      | ~ r1_tarski(A_237,B_240)
      | r2_hidden('#skF_3'(A_237,B_238,C_239),C_239)
      | k4_xboole_0(A_237,B_238) = C_239 ) ),
    inference(resolution,[status(thm)],[c_543,c_2])).

tff(c_22,plain,(
    ! [A_6,B_7,C_8] :
      ( ~ r2_hidden('#skF_2'(A_6,B_7,C_8),B_7)
      | r2_hidden('#skF_3'(A_6,B_7,C_8),C_8)
      | k4_xboole_0(A_6,B_7) = C_8 ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_3105,plain,(
    ! [A_237,B_240,C_239] :
      ( ~ r1_tarski(A_237,B_240)
      | r2_hidden('#skF_3'(A_237,B_240,C_239),C_239)
      | k4_xboole_0(A_237,B_240) = C_239 ) ),
    inference(resolution,[status(thm)],[c_3024,c_22])).

tff(c_3212,plain,(
    ! [A_247,B_248,C_249] :
      ( ~ r1_tarski(A_247,B_248)
      | r2_hidden('#skF_3'(A_247,B_248,C_249),C_249)
      | k4_xboole_0(A_247,B_248) = C_249 ) ),
    inference(resolution,[status(thm)],[c_3024,c_22])).

tff(c_78,plain,(
    ! [D_37,B_38,A_39] :
      ( ~ r2_hidden(D_37,B_38)
      | ~ r2_hidden(D_37,k4_xboole_0(A_39,B_38)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_81,plain,(
    ! [D_37,A_13] :
      ( ~ r2_hidden(D_37,k1_xboole_0)
      | ~ r2_hidden(D_37,A_13) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_78])).

tff(c_3796,plain,(
    ! [A_285,B_286,A_287] :
      ( ~ r2_hidden('#skF_3'(A_285,B_286,k1_xboole_0),A_287)
      | ~ r1_tarski(A_285,B_286)
      | k4_xboole_0(A_285,B_286) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_3212,c_81])).

tff(c_3882,plain,(
    ! [A_288,B_289] :
      ( ~ r1_tarski(A_288,B_289)
      | k4_xboole_0(A_288,B_289) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_3105,c_3796])).

tff(c_3917,plain,(
    k4_xboole_0('#skF_4','#skF_5') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_42,c_3882])).

tff(c_30,plain,(
    ! [A_14,B_15] : k4_xboole_0(A_14,k4_xboole_0(A_14,B_15)) = k3_xboole_0(A_14,B_15) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_4002,plain,(
    k4_xboole_0('#skF_4',k1_xboole_0) = k3_xboole_0('#skF_4','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_3917,c_30])).

tff(c_4036,plain,(
    k3_xboole_0('#skF_4','#skF_5') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_4002])).

tff(c_38,plain,(
    ! [A_23,B_24,C_25] :
      ( k8_relat_1(k3_xboole_0(A_23,B_24),C_25) = k8_relat_1(A_23,k8_relat_1(B_24,C_25))
      | ~ v1_relat_1(C_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_8170,plain,(
    ! [C_386] :
      ( k8_relat_1('#skF_4',k8_relat_1('#skF_5',C_386)) = k8_relat_1('#skF_4',C_386)
      | ~ v1_relat_1(C_386) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4036,c_38])).

tff(c_40,plain,(
    k8_relat_1('#skF_4',k8_relat_1('#skF_5','#skF_6')) != k8_relat_1('#skF_4','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_8179,plain,(
    ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_8170,c_40])).

tff(c_8191,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_8179])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n016.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 20:20:34 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.62/2.33  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.62/2.33  
% 6.62/2.33  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.62/2.33  %$ r2_hidden > r1_tarski > v1_relat_1 > k2_enumset1 > k1_enumset1 > k8_relat_1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_setfam_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3 > #skF_1
% 6.62/2.33  
% 6.62/2.33  %Foreground sorts:
% 6.62/2.33  
% 6.62/2.33  
% 6.62/2.33  %Background operators:
% 6.62/2.33  
% 6.62/2.33  
% 6.62/2.33  %Foreground operators:
% 6.62/2.33  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 6.62/2.33  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.62/2.33  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 6.62/2.33  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 6.62/2.33  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 6.62/2.33  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.62/2.33  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 6.62/2.33  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 6.62/2.33  tff('#skF_5', type, '#skF_5': $i).
% 6.62/2.33  tff('#skF_6', type, '#skF_6': $i).
% 6.62/2.33  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 6.62/2.33  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 6.62/2.33  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.62/2.33  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 6.62/2.33  tff('#skF_4', type, '#skF_4': $i).
% 6.62/2.33  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 6.62/2.33  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.62/2.33  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 6.62/2.33  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 6.62/2.33  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 6.62/2.33  
% 6.62/2.34  tff(f_65, negated_conjecture, ~(![A, B, C]: (v1_relat_1(C) => (r1_tarski(A, B) => (k8_relat_1(A, k8_relat_1(B, C)) = k8_relat_1(A, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t130_relat_1)).
% 6.62/2.34  tff(f_46, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 6.62/2.34  tff(f_42, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 6.62/2.34  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 6.62/2.34  tff(f_48, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 6.62/2.34  tff(f_58, axiom, (![A, B, C]: (v1_relat_1(C) => (k8_relat_1(A, k8_relat_1(B, C)) = k8_relat_1(k3_xboole_0(A, B), C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t127_relat_1)).
% 6.62/2.34  tff(c_44, plain, (v1_relat_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_65])).
% 6.62/2.34  tff(c_28, plain, (![A_13]: (k4_xboole_0(A_13, k1_xboole_0)=A_13)), inference(cnfTransformation, [status(thm)], [f_46])).
% 6.62/2.34  tff(c_42, plain, (r1_tarski('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_65])).
% 6.62/2.34  tff(c_543, plain, (![A_92, B_93, C_94]: (r2_hidden('#skF_2'(A_92, B_93, C_94), A_92) | r2_hidden('#skF_3'(A_92, B_93, C_94), C_94) | k4_xboole_0(A_92, B_93)=C_94)), inference(cnfTransformation, [status(thm)], [f_42])).
% 6.62/2.34  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 6.62/2.34  tff(c_3024, plain, (![A_237, B_238, C_239, B_240]: (r2_hidden('#skF_2'(A_237, B_238, C_239), B_240) | ~r1_tarski(A_237, B_240) | r2_hidden('#skF_3'(A_237, B_238, C_239), C_239) | k4_xboole_0(A_237, B_238)=C_239)), inference(resolution, [status(thm)], [c_543, c_2])).
% 6.62/2.34  tff(c_22, plain, (![A_6, B_7, C_8]: (~r2_hidden('#skF_2'(A_6, B_7, C_8), B_7) | r2_hidden('#skF_3'(A_6, B_7, C_8), C_8) | k4_xboole_0(A_6, B_7)=C_8)), inference(cnfTransformation, [status(thm)], [f_42])).
% 6.62/2.34  tff(c_3105, plain, (![A_237, B_240, C_239]: (~r1_tarski(A_237, B_240) | r2_hidden('#skF_3'(A_237, B_240, C_239), C_239) | k4_xboole_0(A_237, B_240)=C_239)), inference(resolution, [status(thm)], [c_3024, c_22])).
% 6.62/2.34  tff(c_3212, plain, (![A_247, B_248, C_249]: (~r1_tarski(A_247, B_248) | r2_hidden('#skF_3'(A_247, B_248, C_249), C_249) | k4_xboole_0(A_247, B_248)=C_249)), inference(resolution, [status(thm)], [c_3024, c_22])).
% 6.62/2.34  tff(c_78, plain, (![D_37, B_38, A_39]: (~r2_hidden(D_37, B_38) | ~r2_hidden(D_37, k4_xboole_0(A_39, B_38)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 6.62/2.34  tff(c_81, plain, (![D_37, A_13]: (~r2_hidden(D_37, k1_xboole_0) | ~r2_hidden(D_37, A_13))), inference(superposition, [status(thm), theory('equality')], [c_28, c_78])).
% 6.62/2.34  tff(c_3796, plain, (![A_285, B_286, A_287]: (~r2_hidden('#skF_3'(A_285, B_286, k1_xboole_0), A_287) | ~r1_tarski(A_285, B_286) | k4_xboole_0(A_285, B_286)=k1_xboole_0)), inference(resolution, [status(thm)], [c_3212, c_81])).
% 6.62/2.34  tff(c_3882, plain, (![A_288, B_289]: (~r1_tarski(A_288, B_289) | k4_xboole_0(A_288, B_289)=k1_xboole_0)), inference(resolution, [status(thm)], [c_3105, c_3796])).
% 6.62/2.34  tff(c_3917, plain, (k4_xboole_0('#skF_4', '#skF_5')=k1_xboole_0), inference(resolution, [status(thm)], [c_42, c_3882])).
% 6.62/2.34  tff(c_30, plain, (![A_14, B_15]: (k4_xboole_0(A_14, k4_xboole_0(A_14, B_15))=k3_xboole_0(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_48])).
% 6.62/2.34  tff(c_4002, plain, (k4_xboole_0('#skF_4', k1_xboole_0)=k3_xboole_0('#skF_4', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_3917, c_30])).
% 6.62/2.34  tff(c_4036, plain, (k3_xboole_0('#skF_4', '#skF_5')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_28, c_4002])).
% 6.62/2.34  tff(c_38, plain, (![A_23, B_24, C_25]: (k8_relat_1(k3_xboole_0(A_23, B_24), C_25)=k8_relat_1(A_23, k8_relat_1(B_24, C_25)) | ~v1_relat_1(C_25))), inference(cnfTransformation, [status(thm)], [f_58])).
% 6.62/2.34  tff(c_8170, plain, (![C_386]: (k8_relat_1('#skF_4', k8_relat_1('#skF_5', C_386))=k8_relat_1('#skF_4', C_386) | ~v1_relat_1(C_386))), inference(superposition, [status(thm), theory('equality')], [c_4036, c_38])).
% 6.62/2.34  tff(c_40, plain, (k8_relat_1('#skF_4', k8_relat_1('#skF_5', '#skF_6'))!=k8_relat_1('#skF_4', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_65])).
% 6.62/2.34  tff(c_8179, plain, (~v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_8170, c_40])).
% 6.62/2.34  tff(c_8191, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_44, c_8179])).
% 6.62/2.34  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.62/2.34  
% 6.62/2.34  Inference rules
% 6.62/2.34  ----------------------
% 6.62/2.34  #Ref     : 0
% 6.62/2.34  #Sup     : 1945
% 6.62/2.34  #Fact    : 0
% 6.62/2.34  #Define  : 0
% 6.62/2.34  #Split   : 1
% 6.62/2.34  #Chain   : 0
% 6.62/2.34  #Close   : 0
% 6.62/2.34  
% 6.62/2.34  Ordering : KBO
% 6.62/2.34  
% 6.62/2.34  Simplification rules
% 6.62/2.34  ----------------------
% 6.62/2.34  #Subsume      : 464
% 6.62/2.34  #Demod        : 2095
% 6.62/2.34  #Tautology    : 720
% 6.62/2.34  #SimpNegUnit  : 0
% 6.62/2.34  #BackRed      : 36
% 6.62/2.34  
% 6.62/2.34  #Partial instantiations: 0
% 6.62/2.34  #Strategies tried      : 1
% 6.62/2.34  
% 6.62/2.34  Timing (in seconds)
% 6.62/2.34  ----------------------
% 6.62/2.34  Preprocessing        : 0.30
% 6.62/2.34  Parsing              : 0.15
% 6.62/2.34  CNF conversion       : 0.02
% 6.62/2.34  Main loop            : 1.30
% 6.62/2.34  Inferencing          : 0.42
% 6.62/2.35  Reduction            : 0.42
% 6.62/2.35  Demodulation         : 0.33
% 6.62/2.35  BG Simplification    : 0.05
% 6.62/2.35  Subsumption          : 0.31
% 6.62/2.35  Abstraction          : 0.07
% 6.62/2.35  MUC search           : 0.00
% 6.62/2.35  Cooper               : 0.00
% 6.62/2.35  Total                : 1.62
% 6.62/2.35  Index Insertion      : 0.00
% 6.62/2.35  Index Deletion       : 0.00
% 6.62/2.35  Index Matching       : 0.00
% 6.62/2.35  BG Taut test         : 0.00
%------------------------------------------------------------------------------
