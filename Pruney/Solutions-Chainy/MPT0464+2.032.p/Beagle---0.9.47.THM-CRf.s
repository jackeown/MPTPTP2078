%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:58:47 EST 2020

% Result     : Theorem 2.52s
% Output     : CNFRefutation 2.52s
% Verified   : 
% Statistics : Number of formulae       :   57 (  94 expanded)
%              Number of leaves         :   22 (  40 expanded)
%              Depth                    :    8
%              Number of atoms          :   76 ( 176 expanded)
%              Number of equality atoms :    8 (  12 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k5_relat_1 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_45,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k2_xboole_0(B,C))
     => r1_tarski(k4_xboole_0(A,B),C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_xboole_1)).

tff(f_72,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ! [B] :
            ( v1_relat_1(B)
           => ! [C] :
                ( v1_relat_1(C)
               => r1_tarski(k5_relat_1(A,k3_xboole_0(B,C)),k3_xboole_0(k5_relat_1(A,B),k5_relat_1(A,C))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_relat_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k4_xboole_0(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_relat_1)).

tff(f_61,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ! [C] :
              ( v1_relat_1(C)
             => ( r1_tarski(A,B)
               => r1_tarski(k5_relat_1(C,A),k5_relat_1(C,B)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_relat_1)).

tff(f_29,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(A,C) )
     => r1_tarski(A,k3_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_xboole_1)).

tff(c_29,plain,(
    ! [B_34,A_35] : k2_xboole_0(B_34,A_35) = k2_xboole_0(A_35,B_34) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_14,plain,(
    ! [A_15,B_16] : r1_tarski(A_15,k2_xboole_0(A_15,B_16)) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_44,plain,(
    ! [A_35,B_34] : r1_tarski(A_35,k2_xboole_0(B_34,A_35)) ),
    inference(superposition,[status(thm),theory(equality)],[c_29,c_14])).

tff(c_8,plain,(
    ! [A_8,B_9] : k2_xboole_0(A_8,k4_xboole_0(B_9,A_8)) = k2_xboole_0(A_8,B_9) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_12,plain,(
    ! [A_13,B_14] : k4_xboole_0(A_13,k4_xboole_0(A_13,B_14)) = k3_xboole_0(A_13,B_14) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_147,plain,(
    ! [A_50,B_51,C_52] :
      ( r1_tarski(k4_xboole_0(A_50,B_51),C_52)
      | ~ r1_tarski(A_50,k2_xboole_0(B_51,C_52)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_468,plain,(
    ! [A_84,B_85,C_86] :
      ( r1_tarski(k3_xboole_0(A_84,B_85),C_86)
      | ~ r1_tarski(A_84,k2_xboole_0(k4_xboole_0(A_84,B_85),C_86)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_147])).

tff(c_562,plain,(
    ! [A_91,B_92,A_93] :
      ( r1_tarski(k3_xboole_0(A_91,B_92),A_93)
      | ~ r1_tarski(A_91,k2_xboole_0(A_93,k4_xboole_0(A_91,B_92))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_468])).

tff(c_575,plain,(
    ! [B_9,A_8] :
      ( r1_tarski(k3_xboole_0(B_9,A_8),A_8)
      | ~ r1_tarski(B_9,k2_xboole_0(A_8,B_9)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_562])).

tff(c_595,plain,(
    ! [B_9,A_8] : r1_tarski(k3_xboole_0(B_9,A_8),A_8) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_575])).

tff(c_24,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_79,plain,(
    ! [A_40,B_41] : k4_xboole_0(A_40,k4_xboole_0(A_40,B_41)) = k3_xboole_0(A_40,B_41) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_16,plain,(
    ! [A_17,B_18] :
      ( v1_relat_1(k4_xboole_0(A_17,B_18))
      | ~ v1_relat_1(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_88,plain,(
    ! [A_40,B_41] :
      ( v1_relat_1(k3_xboole_0(A_40,B_41))
      | ~ v1_relat_1(A_40) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_79,c_16])).

tff(c_22,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_26,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_18,plain,(
    ! [C_25,A_19,B_23] :
      ( r1_tarski(k5_relat_1(C_25,A_19),k5_relat_1(C_25,B_23))
      | ~ r1_tarski(A_19,B_23)
      | ~ v1_relat_1(C_25)
      | ~ v1_relat_1(B_23)
      | ~ v1_relat_1(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_4,plain,(
    ! [A_3,B_4] : r1_tarski(k3_xboole_0(A_3,B_4),A_3) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_174,plain,(
    ! [A_57,B_58,C_59] :
      ( r1_tarski(A_57,k3_xboole_0(B_58,C_59))
      | ~ r1_tarski(A_57,C_59)
      | ~ r1_tarski(A_57,B_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_20,plain,(
    ~ r1_tarski(k5_relat_1('#skF_1',k3_xboole_0('#skF_2','#skF_3')),k3_xboole_0(k5_relat_1('#skF_1','#skF_2'),k5_relat_1('#skF_1','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_178,plain,
    ( ~ r1_tarski(k5_relat_1('#skF_1',k3_xboole_0('#skF_2','#skF_3')),k5_relat_1('#skF_1','#skF_3'))
    | ~ r1_tarski(k5_relat_1('#skF_1',k3_xboole_0('#skF_2','#skF_3')),k5_relat_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_174,c_20])).

tff(c_284,plain,(
    ~ r1_tarski(k5_relat_1('#skF_1',k3_xboole_0('#skF_2','#skF_3')),k5_relat_1('#skF_1','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_178])).

tff(c_287,plain,
    ( ~ r1_tarski(k3_xboole_0('#skF_2','#skF_3'),'#skF_2')
    | ~ v1_relat_1('#skF_1')
    | ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1(k3_xboole_0('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_18,c_284])).

tff(c_290,plain,(
    ~ v1_relat_1(k3_xboole_0('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_26,c_4,c_287])).

tff(c_293,plain,(
    ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_88,c_290])).

tff(c_297,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_293])).

tff(c_298,plain,(
    ~ r1_tarski(k5_relat_1('#skF_1',k3_xboole_0('#skF_2','#skF_3')),k5_relat_1('#skF_1','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_178])).

tff(c_302,plain,
    ( ~ r1_tarski(k3_xboole_0('#skF_2','#skF_3'),'#skF_3')
    | ~ v1_relat_1('#skF_1')
    | ~ v1_relat_1('#skF_3')
    | ~ v1_relat_1(k3_xboole_0('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_18,c_298])).

tff(c_305,plain,
    ( ~ r1_tarski(k3_xboole_0('#skF_2','#skF_3'),'#skF_3')
    | ~ v1_relat_1(k3_xboole_0('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_26,c_302])).

tff(c_306,plain,(
    ~ v1_relat_1(k3_xboole_0('#skF_2','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_305])).

tff(c_310,plain,(
    ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_88,c_306])).

tff(c_314,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_310])).

tff(c_315,plain,(
    ~ r1_tarski(k3_xboole_0('#skF_2','#skF_3'),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_305])).

tff(c_600,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_595,c_315])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.09/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.09/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n005.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 10:04:17 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.52/1.33  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.52/1.33  
% 2.52/1.33  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.52/1.33  %$ r1_tarski > v1_relat_1 > k5_relat_1 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > #skF_2 > #skF_3 > #skF_1
% 2.52/1.33  
% 2.52/1.33  %Foreground sorts:
% 2.52/1.33  
% 2.52/1.33  
% 2.52/1.33  %Background operators:
% 2.52/1.33  
% 2.52/1.33  
% 2.52/1.33  %Foreground operators:
% 2.52/1.33  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.52/1.33  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.52/1.33  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.52/1.33  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.52/1.33  tff('#skF_2', type, '#skF_2': $i).
% 2.52/1.33  tff('#skF_3', type, '#skF_3': $i).
% 2.52/1.33  tff('#skF_1', type, '#skF_1': $i).
% 2.52/1.33  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.52/1.33  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.52/1.33  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.52/1.33  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.52/1.33  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.52/1.33  
% 2.52/1.35  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 2.52/1.35  tff(f_45, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 2.52/1.35  tff(f_37, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 2.52/1.35  tff(f_43, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 2.52/1.35  tff(f_41, axiom, (![A, B, C]: (r1_tarski(A, k2_xboole_0(B, C)) => r1_tarski(k4_xboole_0(A, B), C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_xboole_1)).
% 2.52/1.35  tff(f_72, negated_conjecture, ~(![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => r1_tarski(k5_relat_1(A, k3_xboole_0(B, C)), k3_xboole_0(k5_relat_1(A, B), k5_relat_1(A, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_relat_1)).
% 2.52/1.35  tff(f_49, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k4_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_relat_1)).
% 2.52/1.35  tff(f_61, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (r1_tarski(A, B) => r1_tarski(k5_relat_1(C, A), k5_relat_1(C, B))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_relat_1)).
% 2.52/1.35  tff(f_29, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 2.52/1.35  tff(f_35, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(A, C)) => r1_tarski(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t19_xboole_1)).
% 2.52/1.35  tff(c_29, plain, (![B_34, A_35]: (k2_xboole_0(B_34, A_35)=k2_xboole_0(A_35, B_34))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.52/1.35  tff(c_14, plain, (![A_15, B_16]: (r1_tarski(A_15, k2_xboole_0(A_15, B_16)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.52/1.35  tff(c_44, plain, (![A_35, B_34]: (r1_tarski(A_35, k2_xboole_0(B_34, A_35)))), inference(superposition, [status(thm), theory('equality')], [c_29, c_14])).
% 2.52/1.35  tff(c_8, plain, (![A_8, B_9]: (k2_xboole_0(A_8, k4_xboole_0(B_9, A_8))=k2_xboole_0(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.52/1.35  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.52/1.35  tff(c_12, plain, (![A_13, B_14]: (k4_xboole_0(A_13, k4_xboole_0(A_13, B_14))=k3_xboole_0(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.52/1.35  tff(c_147, plain, (![A_50, B_51, C_52]: (r1_tarski(k4_xboole_0(A_50, B_51), C_52) | ~r1_tarski(A_50, k2_xboole_0(B_51, C_52)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.52/1.35  tff(c_468, plain, (![A_84, B_85, C_86]: (r1_tarski(k3_xboole_0(A_84, B_85), C_86) | ~r1_tarski(A_84, k2_xboole_0(k4_xboole_0(A_84, B_85), C_86)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_147])).
% 2.52/1.35  tff(c_562, plain, (![A_91, B_92, A_93]: (r1_tarski(k3_xboole_0(A_91, B_92), A_93) | ~r1_tarski(A_91, k2_xboole_0(A_93, k4_xboole_0(A_91, B_92))))), inference(superposition, [status(thm), theory('equality')], [c_2, c_468])).
% 2.52/1.35  tff(c_575, plain, (![B_9, A_8]: (r1_tarski(k3_xboole_0(B_9, A_8), A_8) | ~r1_tarski(B_9, k2_xboole_0(A_8, B_9)))), inference(superposition, [status(thm), theory('equality')], [c_8, c_562])).
% 2.52/1.35  tff(c_595, plain, (![B_9, A_8]: (r1_tarski(k3_xboole_0(B_9, A_8), A_8))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_575])).
% 2.52/1.35  tff(c_24, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.52/1.35  tff(c_79, plain, (![A_40, B_41]: (k4_xboole_0(A_40, k4_xboole_0(A_40, B_41))=k3_xboole_0(A_40, B_41))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.52/1.35  tff(c_16, plain, (![A_17, B_18]: (v1_relat_1(k4_xboole_0(A_17, B_18)) | ~v1_relat_1(A_17))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.52/1.35  tff(c_88, plain, (![A_40, B_41]: (v1_relat_1(k3_xboole_0(A_40, B_41)) | ~v1_relat_1(A_40))), inference(superposition, [status(thm), theory('equality')], [c_79, c_16])).
% 2.52/1.35  tff(c_22, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.52/1.35  tff(c_26, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.52/1.35  tff(c_18, plain, (![C_25, A_19, B_23]: (r1_tarski(k5_relat_1(C_25, A_19), k5_relat_1(C_25, B_23)) | ~r1_tarski(A_19, B_23) | ~v1_relat_1(C_25) | ~v1_relat_1(B_23) | ~v1_relat_1(A_19))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.52/1.35  tff(c_4, plain, (![A_3, B_4]: (r1_tarski(k3_xboole_0(A_3, B_4), A_3))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.52/1.35  tff(c_174, plain, (![A_57, B_58, C_59]: (r1_tarski(A_57, k3_xboole_0(B_58, C_59)) | ~r1_tarski(A_57, C_59) | ~r1_tarski(A_57, B_58))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.52/1.35  tff(c_20, plain, (~r1_tarski(k5_relat_1('#skF_1', k3_xboole_0('#skF_2', '#skF_3')), k3_xboole_0(k5_relat_1('#skF_1', '#skF_2'), k5_relat_1('#skF_1', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.52/1.35  tff(c_178, plain, (~r1_tarski(k5_relat_1('#skF_1', k3_xboole_0('#skF_2', '#skF_3')), k5_relat_1('#skF_1', '#skF_3')) | ~r1_tarski(k5_relat_1('#skF_1', k3_xboole_0('#skF_2', '#skF_3')), k5_relat_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_174, c_20])).
% 2.52/1.35  tff(c_284, plain, (~r1_tarski(k5_relat_1('#skF_1', k3_xboole_0('#skF_2', '#skF_3')), k5_relat_1('#skF_1', '#skF_2'))), inference(splitLeft, [status(thm)], [c_178])).
% 2.52/1.35  tff(c_287, plain, (~r1_tarski(k3_xboole_0('#skF_2', '#skF_3'), '#skF_2') | ~v1_relat_1('#skF_1') | ~v1_relat_1('#skF_2') | ~v1_relat_1(k3_xboole_0('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_18, c_284])).
% 2.52/1.35  tff(c_290, plain, (~v1_relat_1(k3_xboole_0('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_26, c_4, c_287])).
% 2.52/1.35  tff(c_293, plain, (~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_88, c_290])).
% 2.52/1.35  tff(c_297, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_24, c_293])).
% 2.52/1.35  tff(c_298, plain, (~r1_tarski(k5_relat_1('#skF_1', k3_xboole_0('#skF_2', '#skF_3')), k5_relat_1('#skF_1', '#skF_3'))), inference(splitRight, [status(thm)], [c_178])).
% 2.52/1.35  tff(c_302, plain, (~r1_tarski(k3_xboole_0('#skF_2', '#skF_3'), '#skF_3') | ~v1_relat_1('#skF_1') | ~v1_relat_1('#skF_3') | ~v1_relat_1(k3_xboole_0('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_18, c_298])).
% 2.52/1.35  tff(c_305, plain, (~r1_tarski(k3_xboole_0('#skF_2', '#skF_3'), '#skF_3') | ~v1_relat_1(k3_xboole_0('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_26, c_302])).
% 2.52/1.35  tff(c_306, plain, (~v1_relat_1(k3_xboole_0('#skF_2', '#skF_3'))), inference(splitLeft, [status(thm)], [c_305])).
% 2.52/1.35  tff(c_310, plain, (~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_88, c_306])).
% 2.52/1.35  tff(c_314, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_24, c_310])).
% 2.52/1.35  tff(c_315, plain, (~r1_tarski(k3_xboole_0('#skF_2', '#skF_3'), '#skF_3')), inference(splitRight, [status(thm)], [c_305])).
% 2.52/1.35  tff(c_600, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_595, c_315])).
% 2.52/1.35  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.52/1.35  
% 2.52/1.35  Inference rules
% 2.52/1.35  ----------------------
% 2.52/1.35  #Ref     : 0
% 2.52/1.35  #Sup     : 143
% 2.52/1.35  #Fact    : 0
% 2.52/1.35  #Define  : 0
% 2.52/1.35  #Split   : 2
% 2.52/1.35  #Chain   : 0
% 2.52/1.35  #Close   : 0
% 2.52/1.35  
% 2.52/1.35  Ordering : KBO
% 2.52/1.35  
% 2.52/1.35  Simplification rules
% 2.52/1.35  ----------------------
% 2.52/1.35  #Subsume      : 3
% 2.52/1.35  #Demod        : 63
% 2.52/1.35  #Tautology    : 54
% 2.52/1.35  #SimpNegUnit  : 0
% 2.52/1.35  #BackRed      : 1
% 2.52/1.35  
% 2.52/1.35  #Partial instantiations: 0
% 2.52/1.35  #Strategies tried      : 1
% 2.52/1.35  
% 2.52/1.35  Timing (in seconds)
% 2.52/1.35  ----------------------
% 2.52/1.35  Preprocessing        : 0.28
% 2.52/1.35  Parsing              : 0.15
% 2.52/1.35  CNF conversion       : 0.02
% 2.52/1.35  Main loop            : 0.33
% 2.52/1.35  Inferencing          : 0.11
% 2.52/1.35  Reduction            : 0.12
% 2.52/1.35  Demodulation         : 0.10
% 2.52/1.35  BG Simplification    : 0.01
% 2.52/1.35  Subsumption          : 0.06
% 2.52/1.35  Abstraction          : 0.01
% 2.52/1.35  MUC search           : 0.00
% 2.52/1.35  Cooper               : 0.00
% 2.52/1.35  Total                : 0.64
% 2.52/1.35  Index Insertion      : 0.00
% 2.52/1.35  Index Deletion       : 0.00
% 2.52/1.35  Index Matching       : 0.00
% 2.52/1.35  BG Taut test         : 0.00
%------------------------------------------------------------------------------
