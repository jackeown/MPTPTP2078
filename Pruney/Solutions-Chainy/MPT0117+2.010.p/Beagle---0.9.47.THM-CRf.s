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
% DateTime   : Thu Dec  3 09:45:30 EST 2020

% Result     : Theorem 10.59s
% Output     : CNFRefutation 10.77s
% Verified   : 
% Statistics : Number of formulae       :   65 ( 142 expanded)
%              Number of leaves         :   27 (  58 expanded)
%              Depth                    :    9
%              Number of atoms          :   60 ( 152 expanded)
%              Number of equality atoms :   31 (  96 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_5 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_92,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( r1_tarski(A,B)
          & r1_tarski(C,B) )
       => r1_tarski(k5_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t110_xboole_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_85,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k5_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

tff(f_71,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

tff(f_75,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_73,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_53,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_69,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_63,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k3_xboole_0(B,C))
     => r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_xboole_1)).

tff(f_83,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(k4_xboole_0(A,B),C)
        & r1_tarski(k4_xboole_0(B,A),C) )
     => r1_tarski(k5_xboole_0(A,B),C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t97_xboole_1)).

tff(c_38,plain,(
    r1_tarski('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_166,plain,(
    ! [A_46,B_47] :
      ( k2_xboole_0(A_46,B_47) = B_47
      | ~ r1_tarski(A_46,B_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_177,plain,(
    k2_xboole_0('#skF_5','#skF_4') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_38,c_166])).

tff(c_34,plain,(
    ! [A_36,B_37] : k5_xboole_0(A_36,k4_xboole_0(B_37,A_36)) = k2_xboole_0(A_36,B_37) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_68,plain,(
    ! [B_42,A_43] : k5_xboole_0(B_42,A_43) = k5_xboole_0(A_43,B_42) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_24,plain,(
    ! [A_26] : k5_xboole_0(A_26,k1_xboole_0) = A_26 ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_84,plain,(
    ! [A_43] : k5_xboole_0(k1_xboole_0,A_43) = A_43 ),
    inference(superposition,[status(thm),theory(equality)],[c_68,c_24])).

tff(c_28,plain,(
    ! [A_30] : k5_xboole_0(A_30,A_30) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_671,plain,(
    ! [A_72,B_73,C_74] : k5_xboole_0(k5_xboole_0(A_72,B_73),C_74) = k5_xboole_0(A_72,k5_xboole_0(B_73,C_74)) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_742,plain,(
    ! [A_30,C_74] : k5_xboole_0(A_30,k5_xboole_0(A_30,C_74)) = k5_xboole_0(k1_xboole_0,C_74) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_671])).

tff(c_804,plain,(
    ! [A_75,C_76] : k5_xboole_0(A_75,k5_xboole_0(A_75,C_76)) = C_76 ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_742])).

tff(c_19440,plain,(
    ! [A_381,B_382] : k5_xboole_0(A_381,k2_xboole_0(A_381,B_382)) = k4_xboole_0(B_382,A_381) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_804])).

tff(c_19587,plain,(
    k5_xboole_0('#skF_5','#skF_4') = k4_xboole_0('#skF_4','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_177,c_19440])).

tff(c_2,plain,(
    ! [B_2,A_1] : k5_xboole_0(B_2,A_1) = k5_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_856,plain,(
    ! [B_2,A_1] : k5_xboole_0(B_2,k5_xboole_0(A_1,B_2)) = A_1 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_804])).

tff(c_19943,plain,(
    k5_xboole_0('#skF_4',k4_xboole_0('#skF_4','#skF_5')) = '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_19587,c_856])).

tff(c_12,plain,(
    ! [A_12,B_13] : k5_xboole_0(A_12,k3_xboole_0(A_12,B_13)) = k4_xboole_0(A_12,B_13) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_843,plain,(
    ! [A_12,B_13] : k5_xboole_0(A_12,k4_xboole_0(A_12,B_13)) = k3_xboole_0(A_12,B_13) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_804])).

tff(c_20929,plain,(
    k3_xboole_0('#skF_4','#skF_5') = '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_19943,c_843])).

tff(c_22,plain,(
    ! [A_24,B_25] : r1_tarski(k4_xboole_0(A_24,B_25),A_24) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_464,plain,(
    ! [A_65,B_66,C_67] :
      ( r1_tarski(A_65,B_66)
      | ~ r1_tarski(A_65,k3_xboole_0(B_66,C_67)) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_481,plain,(
    ! [B_66,C_67,B_25] : r1_tarski(k4_xboole_0(k3_xboole_0(B_66,C_67),B_25),B_66) ),
    inference(resolution,[status(thm)],[c_22,c_464])).

tff(c_21063,plain,(
    ! [B_25] : r1_tarski(k4_xboole_0('#skF_5',B_25),'#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_20929,c_481])).

tff(c_13493,plain,(
    ! [A_283,B_284] : k5_xboole_0(A_283,k4_xboole_0(A_283,B_284)) = k3_xboole_0(A_283,B_284) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_804])).

tff(c_40,plain,(
    r1_tarski('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_178,plain,(
    k2_xboole_0('#skF_3','#skF_4') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_40,c_166])).

tff(c_7866,plain,(
    ! [A_214,B_215] : k5_xboole_0(A_214,k2_xboole_0(A_214,B_215)) = k4_xboole_0(B_215,A_214) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_804])).

tff(c_8018,plain,(
    k5_xboole_0('#skF_3','#skF_4') = k4_xboole_0('#skF_4','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_178,c_7866])).

tff(c_8092,plain,(
    k5_xboole_0('#skF_4',k4_xboole_0('#skF_4','#skF_3')) = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_8018,c_856])).

tff(c_13519,plain,(
    k3_xboole_0('#skF_4','#skF_3') = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_13493,c_8092])).

tff(c_13886,plain,(
    ! [B_25] : r1_tarski(k4_xboole_0('#skF_3',B_25),'#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_13519,c_481])).

tff(c_1476,plain,(
    ! [A_93,B_94,C_95] :
      ( r1_tarski(k5_xboole_0(A_93,B_94),C_95)
      | ~ r1_tarski(k4_xboole_0(B_94,A_93),C_95)
      | ~ r1_tarski(k4_xboole_0(A_93,B_94),C_95) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_36,plain,(
    ~ r1_tarski(k5_xboole_0('#skF_3','#skF_5'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_1529,plain,
    ( ~ r1_tarski(k4_xboole_0('#skF_5','#skF_3'),'#skF_4')
    | ~ r1_tarski(k4_xboole_0('#skF_3','#skF_5'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_1476,c_36])).

tff(c_1533,plain,(
    ~ r1_tarski(k4_xboole_0('#skF_3','#skF_5'),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_1529])).

tff(c_14270,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_13886,c_1533])).

tff(c_14271,plain,(
    ~ r1_tarski(k4_xboole_0('#skF_5','#skF_3'),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_1529])).

tff(c_21244,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_21063,c_14271])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:20:15 EST 2020
% 0.19/0.34  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 10.59/4.06  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.59/4.07  
% 10.59/4.07  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.59/4.07  %$ r2_hidden > r1_xboole_0 > r1_tarski > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_5 > #skF_3 > #skF_4 > #skF_1
% 10.59/4.07  
% 10.59/4.07  %Foreground sorts:
% 10.59/4.07  
% 10.59/4.07  
% 10.59/4.07  %Background operators:
% 10.59/4.07  
% 10.59/4.07  
% 10.59/4.07  %Foreground operators:
% 10.59/4.07  tff('#skF_2', type, '#skF_2': $i > $i).
% 10.59/4.07  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 10.59/4.07  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 10.59/4.07  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 10.59/4.07  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 10.59/4.07  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 10.59/4.07  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 10.59/4.07  tff('#skF_5', type, '#skF_5': $i).
% 10.59/4.07  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 10.59/4.07  tff('#skF_3', type, '#skF_3': $i).
% 10.59/4.07  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 10.59/4.07  tff('#skF_4', type, '#skF_4': $i).
% 10.59/4.07  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 10.59/4.07  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 10.59/4.07  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 10.59/4.07  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 10.59/4.07  
% 10.77/4.08  tff(f_92, negated_conjecture, ~(![A, B, C]: ((r1_tarski(A, B) & r1_tarski(C, B)) => r1_tarski(k5_xboole_0(A, C), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t110_xboole_1)).
% 10.77/4.08  tff(f_57, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 10.77/4.08  tff(f_85, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_xboole_1)).
% 10.77/4.08  tff(f_27, axiom, (![A, B]: (k5_xboole_0(A, B) = k5_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 10.77/4.08  tff(f_71, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 10.77/4.08  tff(f_75, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t92_xboole_1)).
% 10.77/4.08  tff(f_73, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_xboole_1)).
% 10.77/4.08  tff(f_53, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 10.77/4.08  tff(f_69, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 10.77/4.08  tff(f_63, axiom, (![A, B, C]: (r1_tarski(A, k3_xboole_0(B, C)) => r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t18_xboole_1)).
% 10.77/4.08  tff(f_83, axiom, (![A, B, C]: ((r1_tarski(k4_xboole_0(A, B), C) & r1_tarski(k4_xboole_0(B, A), C)) => r1_tarski(k5_xboole_0(A, B), C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t97_xboole_1)).
% 10.77/4.08  tff(c_38, plain, (r1_tarski('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_92])).
% 10.77/4.08  tff(c_166, plain, (![A_46, B_47]: (k2_xboole_0(A_46, B_47)=B_47 | ~r1_tarski(A_46, B_47))), inference(cnfTransformation, [status(thm)], [f_57])).
% 10.77/4.08  tff(c_177, plain, (k2_xboole_0('#skF_5', '#skF_4')='#skF_4'), inference(resolution, [status(thm)], [c_38, c_166])).
% 10.77/4.08  tff(c_34, plain, (![A_36, B_37]: (k5_xboole_0(A_36, k4_xboole_0(B_37, A_36))=k2_xboole_0(A_36, B_37))), inference(cnfTransformation, [status(thm)], [f_85])).
% 10.77/4.08  tff(c_68, plain, (![B_42, A_43]: (k5_xboole_0(B_42, A_43)=k5_xboole_0(A_43, B_42))), inference(cnfTransformation, [status(thm)], [f_27])).
% 10.77/4.08  tff(c_24, plain, (![A_26]: (k5_xboole_0(A_26, k1_xboole_0)=A_26)), inference(cnfTransformation, [status(thm)], [f_71])).
% 10.77/4.08  tff(c_84, plain, (![A_43]: (k5_xboole_0(k1_xboole_0, A_43)=A_43)), inference(superposition, [status(thm), theory('equality')], [c_68, c_24])).
% 10.77/4.08  tff(c_28, plain, (![A_30]: (k5_xboole_0(A_30, A_30)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_75])).
% 10.77/4.08  tff(c_671, plain, (![A_72, B_73, C_74]: (k5_xboole_0(k5_xboole_0(A_72, B_73), C_74)=k5_xboole_0(A_72, k5_xboole_0(B_73, C_74)))), inference(cnfTransformation, [status(thm)], [f_73])).
% 10.77/4.08  tff(c_742, plain, (![A_30, C_74]: (k5_xboole_0(A_30, k5_xboole_0(A_30, C_74))=k5_xboole_0(k1_xboole_0, C_74))), inference(superposition, [status(thm), theory('equality')], [c_28, c_671])).
% 10.77/4.08  tff(c_804, plain, (![A_75, C_76]: (k5_xboole_0(A_75, k5_xboole_0(A_75, C_76))=C_76)), inference(demodulation, [status(thm), theory('equality')], [c_84, c_742])).
% 10.77/4.08  tff(c_19440, plain, (![A_381, B_382]: (k5_xboole_0(A_381, k2_xboole_0(A_381, B_382))=k4_xboole_0(B_382, A_381))), inference(superposition, [status(thm), theory('equality')], [c_34, c_804])).
% 10.77/4.08  tff(c_19587, plain, (k5_xboole_0('#skF_5', '#skF_4')=k4_xboole_0('#skF_4', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_177, c_19440])).
% 10.77/4.08  tff(c_2, plain, (![B_2, A_1]: (k5_xboole_0(B_2, A_1)=k5_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 10.77/4.08  tff(c_856, plain, (![B_2, A_1]: (k5_xboole_0(B_2, k5_xboole_0(A_1, B_2))=A_1)), inference(superposition, [status(thm), theory('equality')], [c_2, c_804])).
% 10.77/4.08  tff(c_19943, plain, (k5_xboole_0('#skF_4', k4_xboole_0('#skF_4', '#skF_5'))='#skF_5'), inference(superposition, [status(thm), theory('equality')], [c_19587, c_856])).
% 10.77/4.08  tff(c_12, plain, (![A_12, B_13]: (k5_xboole_0(A_12, k3_xboole_0(A_12, B_13))=k4_xboole_0(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_53])).
% 10.77/4.08  tff(c_843, plain, (![A_12, B_13]: (k5_xboole_0(A_12, k4_xboole_0(A_12, B_13))=k3_xboole_0(A_12, B_13))), inference(superposition, [status(thm), theory('equality')], [c_12, c_804])).
% 10.77/4.08  tff(c_20929, plain, (k3_xboole_0('#skF_4', '#skF_5')='#skF_5'), inference(superposition, [status(thm), theory('equality')], [c_19943, c_843])).
% 10.77/4.08  tff(c_22, plain, (![A_24, B_25]: (r1_tarski(k4_xboole_0(A_24, B_25), A_24))), inference(cnfTransformation, [status(thm)], [f_69])).
% 10.77/4.08  tff(c_464, plain, (![A_65, B_66, C_67]: (r1_tarski(A_65, B_66) | ~r1_tarski(A_65, k3_xboole_0(B_66, C_67)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 10.77/4.08  tff(c_481, plain, (![B_66, C_67, B_25]: (r1_tarski(k4_xboole_0(k3_xboole_0(B_66, C_67), B_25), B_66))), inference(resolution, [status(thm)], [c_22, c_464])).
% 10.77/4.08  tff(c_21063, plain, (![B_25]: (r1_tarski(k4_xboole_0('#skF_5', B_25), '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_20929, c_481])).
% 10.77/4.08  tff(c_13493, plain, (![A_283, B_284]: (k5_xboole_0(A_283, k4_xboole_0(A_283, B_284))=k3_xboole_0(A_283, B_284))), inference(superposition, [status(thm), theory('equality')], [c_12, c_804])).
% 10.77/4.08  tff(c_40, plain, (r1_tarski('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_92])).
% 10.77/4.08  tff(c_178, plain, (k2_xboole_0('#skF_3', '#skF_4')='#skF_4'), inference(resolution, [status(thm)], [c_40, c_166])).
% 10.77/4.08  tff(c_7866, plain, (![A_214, B_215]: (k5_xboole_0(A_214, k2_xboole_0(A_214, B_215))=k4_xboole_0(B_215, A_214))), inference(superposition, [status(thm), theory('equality')], [c_34, c_804])).
% 10.77/4.08  tff(c_8018, plain, (k5_xboole_0('#skF_3', '#skF_4')=k4_xboole_0('#skF_4', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_178, c_7866])).
% 10.77/4.08  tff(c_8092, plain, (k5_xboole_0('#skF_4', k4_xboole_0('#skF_4', '#skF_3'))='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_8018, c_856])).
% 10.77/4.08  tff(c_13519, plain, (k3_xboole_0('#skF_4', '#skF_3')='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_13493, c_8092])).
% 10.77/4.08  tff(c_13886, plain, (![B_25]: (r1_tarski(k4_xboole_0('#skF_3', B_25), '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_13519, c_481])).
% 10.77/4.08  tff(c_1476, plain, (![A_93, B_94, C_95]: (r1_tarski(k5_xboole_0(A_93, B_94), C_95) | ~r1_tarski(k4_xboole_0(B_94, A_93), C_95) | ~r1_tarski(k4_xboole_0(A_93, B_94), C_95))), inference(cnfTransformation, [status(thm)], [f_83])).
% 10.77/4.08  tff(c_36, plain, (~r1_tarski(k5_xboole_0('#skF_3', '#skF_5'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_92])).
% 10.77/4.08  tff(c_1529, plain, (~r1_tarski(k4_xboole_0('#skF_5', '#skF_3'), '#skF_4') | ~r1_tarski(k4_xboole_0('#skF_3', '#skF_5'), '#skF_4')), inference(resolution, [status(thm)], [c_1476, c_36])).
% 10.77/4.08  tff(c_1533, plain, (~r1_tarski(k4_xboole_0('#skF_3', '#skF_5'), '#skF_4')), inference(splitLeft, [status(thm)], [c_1529])).
% 10.77/4.08  tff(c_14270, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_13886, c_1533])).
% 10.77/4.08  tff(c_14271, plain, (~r1_tarski(k4_xboole_0('#skF_5', '#skF_3'), '#skF_4')), inference(splitRight, [status(thm)], [c_1529])).
% 10.77/4.08  tff(c_21244, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_21063, c_14271])).
% 10.77/4.08  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.77/4.08  
% 10.77/4.08  Inference rules
% 10.77/4.08  ----------------------
% 10.77/4.08  #Ref     : 0
% 10.77/4.08  #Sup     : 5397
% 10.77/4.08  #Fact    : 0
% 10.77/4.08  #Define  : 0
% 10.77/4.08  #Split   : 5
% 10.77/4.08  #Chain   : 0
% 10.77/4.08  #Close   : 0
% 10.77/4.08  
% 10.77/4.08  Ordering : KBO
% 10.77/4.08  
% 10.77/4.08  Simplification rules
% 10.77/4.08  ----------------------
% 10.77/4.08  #Subsume      : 236
% 10.77/4.08  #Demod        : 6166
% 10.77/4.08  #Tautology    : 3142
% 10.77/4.08  #SimpNegUnit  : 76
% 10.77/4.08  #BackRed      : 76
% 10.77/4.08  
% 10.77/4.08  #Partial instantiations: 0
% 10.77/4.08  #Strategies tried      : 1
% 10.77/4.08  
% 10.77/4.08  Timing (in seconds)
% 10.77/4.08  ----------------------
% 10.83/4.09  Preprocessing        : 0.29
% 10.83/4.09  Parsing              : 0.16
% 10.83/4.09  CNF conversion       : 0.02
% 10.83/4.09  Main loop            : 2.96
% 10.83/4.09  Inferencing          : 0.67
% 10.83/4.09  Reduction            : 1.57
% 10.83/4.09  Demodulation         : 1.32
% 10.83/4.09  BG Simplification    : 0.08
% 10.83/4.09  Subsumption          : 0.46
% 10.83/4.09  Abstraction          : 0.10
% 10.83/4.09  MUC search           : 0.00
% 10.83/4.09  Cooper               : 0.00
% 10.83/4.09  Total                : 3.28
% 10.83/4.09  Index Insertion      : 0.00
% 10.83/4.09  Index Deletion       : 0.00
% 10.83/4.09  Index Matching       : 0.00
% 10.83/4.09  BG Taut test         : 0.00
%------------------------------------------------------------------------------
