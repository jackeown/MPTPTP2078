%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:00:19 EST 2020

% Result     : Theorem 6.98s
% Output     : CNFRefutation 6.98s
% Verified   : 
% Statistics : Number of formulae       :   52 (  76 expanded)
%              Number of leaves         :   18 (  33 expanded)
%              Depth                    :   13
%              Number of atoms          :  105 ( 178 expanded)
%              Number of equality atoms :    7 (   9 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k8_relat_1 > #nlpp > k2_relat_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k8_relat_1,type,(
    k8_relat_1: ( $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

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

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(f_70,negated_conjecture,(
    ~ ! [A,B,C] :
        ( v1_relat_1(C)
       => ! [D] :
            ( v1_relat_1(D)
           => ( ( r1_tarski(C,D)
                & r1_tarski(A,B) )
             => r1_tarski(k8_relat_1(A,C),k8_relat_1(B,D)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t133_relat_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => v1_relat_1(k8_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k8_relat_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k2_relat_1(k8_relat_1(A,B)),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t116_relat_1)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k2_relat_1(B),A)
       => k8_relat_1(A,B) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t125_relat_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k8_relat_1(A,B),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t117_relat_1)).

tff(f_58,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ! [C] :
          ( v1_relat_1(C)
         => ( r1_tarski(B,C)
           => r1_tarski(k8_relat_1(A,B),k8_relat_1(A,C)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t132_relat_1)).

tff(c_22,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_4,plain,(
    ! [A_4,B_5] :
      ( v1_relat_1(k8_relat_1(A_4,B_5))
      | ~ v1_relat_1(B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_14,plain,(
    ~ r1_tarski(k8_relat_1('#skF_1','#skF_3'),k8_relat_1('#skF_2','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_6,plain,(
    ! [A_6,B_7] :
      ( r1_tarski(k2_relat_1(k8_relat_1(A_6,B_7)),A_6)
      | ~ v1_relat_1(B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_16,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_26,plain,(
    ! [A_23,C_24,B_25] :
      ( r1_tarski(A_23,C_24)
      | ~ r1_tarski(B_25,C_24)
      | ~ r1_tarski(A_23,B_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_38,plain,(
    ! [A_23] :
      ( r1_tarski(A_23,'#skF_2')
      | ~ r1_tarski(A_23,'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_16,c_26])).

tff(c_98,plain,(
    ! [A_34,B_35] :
      ( k8_relat_1(A_34,B_35) = B_35
      | ~ r1_tarski(k2_relat_1(B_35),A_34)
      | ~ v1_relat_1(B_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_113,plain,(
    ! [B_36] :
      ( k8_relat_1('#skF_2',B_36) = B_36
      | ~ v1_relat_1(B_36)
      | ~ r1_tarski(k2_relat_1(B_36),'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_38,c_98])).

tff(c_369,plain,(
    ! [B_68] :
      ( k8_relat_1('#skF_2',k8_relat_1('#skF_1',B_68)) = k8_relat_1('#skF_1',B_68)
      | ~ v1_relat_1(k8_relat_1('#skF_1',B_68))
      | ~ v1_relat_1(B_68) ) ),
    inference(resolution,[status(thm)],[c_6,c_113])).

tff(c_374,plain,(
    ! [B_5] :
      ( k8_relat_1('#skF_2',k8_relat_1('#skF_1',B_5)) = k8_relat_1('#skF_1',B_5)
      | ~ v1_relat_1(B_5) ) ),
    inference(resolution,[status(thm)],[c_4,c_369])).

tff(c_541,plain,(
    ! [A_79,B_80] :
      ( k8_relat_1(A_79,k8_relat_1(A_79,B_80)) = k8_relat_1(A_79,B_80)
      | ~ v1_relat_1(k8_relat_1(A_79,B_80))
      | ~ v1_relat_1(B_80) ) ),
    inference(resolution,[status(thm)],[c_6,c_98])).

tff(c_853,plain,(
    ! [A_92,B_93] :
      ( k8_relat_1(A_92,k8_relat_1(A_92,B_93)) = k8_relat_1(A_92,B_93)
      | ~ v1_relat_1(B_93) ) ),
    inference(resolution,[status(thm)],[c_4,c_541])).

tff(c_8,plain,(
    ! [A_8,B_9] :
      ( r1_tarski(k8_relat_1(A_8,B_9),B_9)
      | ~ v1_relat_1(B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_958,plain,(
    ! [A_92,B_93] :
      ( r1_tarski(k8_relat_1(A_92,B_93),k8_relat_1(A_92,B_93))
      | ~ v1_relat_1(k8_relat_1(A_92,B_93))
      | ~ v1_relat_1(B_93) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_853,c_8])).

tff(c_20,plain,(
    v1_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_18,plain,(
    r1_tarski('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_39,plain,(
    ! [A_26] :
      ( r1_tarski(A_26,'#skF_4')
      | ~ r1_tarski(A_26,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_18,c_26])).

tff(c_47,plain,(
    ! [A_8] :
      ( r1_tarski(k8_relat_1(A_8,'#skF_3'),'#skF_4')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_8,c_39])).

tff(c_51,plain,(
    ! [A_8] : r1_tarski(k8_relat_1(A_8,'#skF_3'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_47])).

tff(c_12,plain,(
    ! [A_12,B_13,C_15] :
      ( r1_tarski(k8_relat_1(A_12,B_13),k8_relat_1(A_12,C_15))
      | ~ r1_tarski(B_13,C_15)
      | ~ v1_relat_1(C_15)
      | ~ v1_relat_1(B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_170,plain,(
    ! [A_49,B_50,C_51] :
      ( r1_tarski(k8_relat_1(A_49,B_50),k8_relat_1(A_49,C_51))
      | ~ r1_tarski(B_50,C_51)
      | ~ v1_relat_1(C_51)
      | ~ v1_relat_1(B_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_2,plain,(
    ! [A_1,C_3,B_2] :
      ( r1_tarski(A_1,C_3)
      | ~ r1_tarski(B_2,C_3)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_786,plain,(
    ! [A_87,A_88,C_89,B_90] :
      ( r1_tarski(A_87,k8_relat_1(A_88,C_89))
      | ~ r1_tarski(A_87,k8_relat_1(A_88,B_90))
      | ~ r1_tarski(B_90,C_89)
      | ~ v1_relat_1(C_89)
      | ~ v1_relat_1(B_90) ) ),
    inference(resolution,[status(thm)],[c_170,c_2])).

tff(c_1758,plain,(
    ! [A_125,B_126,C_127,C_128] :
      ( r1_tarski(k8_relat_1(A_125,B_126),k8_relat_1(A_125,C_127))
      | ~ r1_tarski(C_128,C_127)
      | ~ v1_relat_1(C_127)
      | ~ r1_tarski(B_126,C_128)
      | ~ v1_relat_1(C_128)
      | ~ v1_relat_1(B_126) ) ),
    inference(resolution,[status(thm)],[c_12,c_786])).

tff(c_1820,plain,(
    ! [A_125,B_126,A_8] :
      ( r1_tarski(k8_relat_1(A_125,B_126),k8_relat_1(A_125,'#skF_4'))
      | ~ v1_relat_1('#skF_4')
      | ~ r1_tarski(B_126,k8_relat_1(A_8,'#skF_3'))
      | ~ v1_relat_1(k8_relat_1(A_8,'#skF_3'))
      | ~ v1_relat_1(B_126) ) ),
    inference(resolution,[status(thm)],[c_51,c_1758])).

tff(c_8184,plain,(
    ! [A_301,B_302,A_303] :
      ( r1_tarski(k8_relat_1(A_301,B_302),k8_relat_1(A_301,'#skF_4'))
      | ~ r1_tarski(B_302,k8_relat_1(A_303,'#skF_3'))
      | ~ v1_relat_1(k8_relat_1(A_303,'#skF_3'))
      | ~ v1_relat_1(B_302) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_1820])).

tff(c_8223,plain,(
    ! [A_301,A_92] :
      ( r1_tarski(k8_relat_1(A_301,k8_relat_1(A_92,'#skF_3')),k8_relat_1(A_301,'#skF_4'))
      | ~ v1_relat_1(k8_relat_1(A_92,'#skF_3'))
      | ~ v1_relat_1('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_958,c_8184])).

tff(c_8551,plain,(
    ! [A_310,A_311] :
      ( r1_tarski(k8_relat_1(A_310,k8_relat_1(A_311,'#skF_3')),k8_relat_1(A_310,'#skF_4'))
      | ~ v1_relat_1(k8_relat_1(A_311,'#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_8223])).

tff(c_8612,plain,
    ( r1_tarski(k8_relat_1('#skF_1','#skF_3'),k8_relat_1('#skF_2','#skF_4'))
    | ~ v1_relat_1(k8_relat_1('#skF_1','#skF_3'))
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_374,c_8551])).

tff(c_8657,plain,
    ( r1_tarski(k8_relat_1('#skF_1','#skF_3'),k8_relat_1('#skF_2','#skF_4'))
    | ~ v1_relat_1(k8_relat_1('#skF_1','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_8612])).

tff(c_8658,plain,(
    ~ v1_relat_1(k8_relat_1('#skF_1','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_14,c_8657])).

tff(c_8663,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_4,c_8658])).

tff(c_8667,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_8663])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n005.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 10:44:47 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.98/2.55  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.98/2.55  
% 6.98/2.55  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.98/2.55  %$ r1_tarski > v1_relat_1 > k8_relat_1 > #nlpp > k2_relat_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 6.98/2.55  
% 6.98/2.55  %Foreground sorts:
% 6.98/2.55  
% 6.98/2.55  
% 6.98/2.55  %Background operators:
% 6.98/2.55  
% 6.98/2.55  
% 6.98/2.55  %Foreground operators:
% 6.98/2.55  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 6.98/2.55  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.98/2.55  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.98/2.55  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 6.98/2.55  tff('#skF_2', type, '#skF_2': $i).
% 6.98/2.55  tff('#skF_3', type, '#skF_3': $i).
% 6.98/2.55  tff('#skF_1', type, '#skF_1': $i).
% 6.98/2.55  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.98/2.55  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 6.98/2.55  tff('#skF_4', type, '#skF_4': $i).
% 6.98/2.55  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.98/2.55  
% 6.98/2.57  tff(f_70, negated_conjecture, ~(![A, B, C]: (v1_relat_1(C) => (![D]: (v1_relat_1(D) => ((r1_tarski(C, D) & r1_tarski(A, B)) => r1_tarski(k8_relat_1(A, C), k8_relat_1(B, D))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t133_relat_1)).
% 6.98/2.57  tff(f_35, axiom, (![A, B]: (v1_relat_1(B) => v1_relat_1(k8_relat_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k8_relat_1)).
% 6.98/2.57  tff(f_39, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k2_relat_1(k8_relat_1(A, B)), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t116_relat_1)).
% 6.98/2.57  tff(f_31, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 6.98/2.57  tff(f_49, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(B), A) => (k8_relat_1(A, B) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t125_relat_1)).
% 6.98/2.57  tff(f_43, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k8_relat_1(A, B), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t117_relat_1)).
% 6.98/2.57  tff(f_58, axiom, (![A, B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (r1_tarski(B, C) => r1_tarski(k8_relat_1(A, B), k8_relat_1(A, C))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t132_relat_1)).
% 6.98/2.57  tff(c_22, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_70])).
% 6.98/2.57  tff(c_4, plain, (![A_4, B_5]: (v1_relat_1(k8_relat_1(A_4, B_5)) | ~v1_relat_1(B_5))), inference(cnfTransformation, [status(thm)], [f_35])).
% 6.98/2.57  tff(c_14, plain, (~r1_tarski(k8_relat_1('#skF_1', '#skF_3'), k8_relat_1('#skF_2', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_70])).
% 6.98/2.57  tff(c_6, plain, (![A_6, B_7]: (r1_tarski(k2_relat_1(k8_relat_1(A_6, B_7)), A_6) | ~v1_relat_1(B_7))), inference(cnfTransformation, [status(thm)], [f_39])).
% 6.98/2.57  tff(c_16, plain, (r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_70])).
% 6.98/2.57  tff(c_26, plain, (![A_23, C_24, B_25]: (r1_tarski(A_23, C_24) | ~r1_tarski(B_25, C_24) | ~r1_tarski(A_23, B_25))), inference(cnfTransformation, [status(thm)], [f_31])).
% 6.98/2.57  tff(c_38, plain, (![A_23]: (r1_tarski(A_23, '#skF_2') | ~r1_tarski(A_23, '#skF_1'))), inference(resolution, [status(thm)], [c_16, c_26])).
% 6.98/2.57  tff(c_98, plain, (![A_34, B_35]: (k8_relat_1(A_34, B_35)=B_35 | ~r1_tarski(k2_relat_1(B_35), A_34) | ~v1_relat_1(B_35))), inference(cnfTransformation, [status(thm)], [f_49])).
% 6.98/2.57  tff(c_113, plain, (![B_36]: (k8_relat_1('#skF_2', B_36)=B_36 | ~v1_relat_1(B_36) | ~r1_tarski(k2_relat_1(B_36), '#skF_1'))), inference(resolution, [status(thm)], [c_38, c_98])).
% 6.98/2.57  tff(c_369, plain, (![B_68]: (k8_relat_1('#skF_2', k8_relat_1('#skF_1', B_68))=k8_relat_1('#skF_1', B_68) | ~v1_relat_1(k8_relat_1('#skF_1', B_68)) | ~v1_relat_1(B_68))), inference(resolution, [status(thm)], [c_6, c_113])).
% 6.98/2.57  tff(c_374, plain, (![B_5]: (k8_relat_1('#skF_2', k8_relat_1('#skF_1', B_5))=k8_relat_1('#skF_1', B_5) | ~v1_relat_1(B_5))), inference(resolution, [status(thm)], [c_4, c_369])).
% 6.98/2.57  tff(c_541, plain, (![A_79, B_80]: (k8_relat_1(A_79, k8_relat_1(A_79, B_80))=k8_relat_1(A_79, B_80) | ~v1_relat_1(k8_relat_1(A_79, B_80)) | ~v1_relat_1(B_80))), inference(resolution, [status(thm)], [c_6, c_98])).
% 6.98/2.57  tff(c_853, plain, (![A_92, B_93]: (k8_relat_1(A_92, k8_relat_1(A_92, B_93))=k8_relat_1(A_92, B_93) | ~v1_relat_1(B_93))), inference(resolution, [status(thm)], [c_4, c_541])).
% 6.98/2.57  tff(c_8, plain, (![A_8, B_9]: (r1_tarski(k8_relat_1(A_8, B_9), B_9) | ~v1_relat_1(B_9))), inference(cnfTransformation, [status(thm)], [f_43])).
% 6.98/2.57  tff(c_958, plain, (![A_92, B_93]: (r1_tarski(k8_relat_1(A_92, B_93), k8_relat_1(A_92, B_93)) | ~v1_relat_1(k8_relat_1(A_92, B_93)) | ~v1_relat_1(B_93))), inference(superposition, [status(thm), theory('equality')], [c_853, c_8])).
% 6.98/2.57  tff(c_20, plain, (v1_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_70])).
% 6.98/2.57  tff(c_18, plain, (r1_tarski('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_70])).
% 6.98/2.57  tff(c_39, plain, (![A_26]: (r1_tarski(A_26, '#skF_4') | ~r1_tarski(A_26, '#skF_3'))), inference(resolution, [status(thm)], [c_18, c_26])).
% 6.98/2.57  tff(c_47, plain, (![A_8]: (r1_tarski(k8_relat_1(A_8, '#skF_3'), '#skF_4') | ~v1_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_8, c_39])).
% 6.98/2.57  tff(c_51, plain, (![A_8]: (r1_tarski(k8_relat_1(A_8, '#skF_3'), '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_47])).
% 6.98/2.57  tff(c_12, plain, (![A_12, B_13, C_15]: (r1_tarski(k8_relat_1(A_12, B_13), k8_relat_1(A_12, C_15)) | ~r1_tarski(B_13, C_15) | ~v1_relat_1(C_15) | ~v1_relat_1(B_13))), inference(cnfTransformation, [status(thm)], [f_58])).
% 6.98/2.57  tff(c_170, plain, (![A_49, B_50, C_51]: (r1_tarski(k8_relat_1(A_49, B_50), k8_relat_1(A_49, C_51)) | ~r1_tarski(B_50, C_51) | ~v1_relat_1(C_51) | ~v1_relat_1(B_50))), inference(cnfTransformation, [status(thm)], [f_58])).
% 6.98/2.57  tff(c_2, plain, (![A_1, C_3, B_2]: (r1_tarski(A_1, C_3) | ~r1_tarski(B_2, C_3) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 6.98/2.57  tff(c_786, plain, (![A_87, A_88, C_89, B_90]: (r1_tarski(A_87, k8_relat_1(A_88, C_89)) | ~r1_tarski(A_87, k8_relat_1(A_88, B_90)) | ~r1_tarski(B_90, C_89) | ~v1_relat_1(C_89) | ~v1_relat_1(B_90))), inference(resolution, [status(thm)], [c_170, c_2])).
% 6.98/2.57  tff(c_1758, plain, (![A_125, B_126, C_127, C_128]: (r1_tarski(k8_relat_1(A_125, B_126), k8_relat_1(A_125, C_127)) | ~r1_tarski(C_128, C_127) | ~v1_relat_1(C_127) | ~r1_tarski(B_126, C_128) | ~v1_relat_1(C_128) | ~v1_relat_1(B_126))), inference(resolution, [status(thm)], [c_12, c_786])).
% 6.98/2.57  tff(c_1820, plain, (![A_125, B_126, A_8]: (r1_tarski(k8_relat_1(A_125, B_126), k8_relat_1(A_125, '#skF_4')) | ~v1_relat_1('#skF_4') | ~r1_tarski(B_126, k8_relat_1(A_8, '#skF_3')) | ~v1_relat_1(k8_relat_1(A_8, '#skF_3')) | ~v1_relat_1(B_126))), inference(resolution, [status(thm)], [c_51, c_1758])).
% 6.98/2.57  tff(c_8184, plain, (![A_301, B_302, A_303]: (r1_tarski(k8_relat_1(A_301, B_302), k8_relat_1(A_301, '#skF_4')) | ~r1_tarski(B_302, k8_relat_1(A_303, '#skF_3')) | ~v1_relat_1(k8_relat_1(A_303, '#skF_3')) | ~v1_relat_1(B_302))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_1820])).
% 6.98/2.57  tff(c_8223, plain, (![A_301, A_92]: (r1_tarski(k8_relat_1(A_301, k8_relat_1(A_92, '#skF_3')), k8_relat_1(A_301, '#skF_4')) | ~v1_relat_1(k8_relat_1(A_92, '#skF_3')) | ~v1_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_958, c_8184])).
% 6.98/2.57  tff(c_8551, plain, (![A_310, A_311]: (r1_tarski(k8_relat_1(A_310, k8_relat_1(A_311, '#skF_3')), k8_relat_1(A_310, '#skF_4')) | ~v1_relat_1(k8_relat_1(A_311, '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_8223])).
% 6.98/2.57  tff(c_8612, plain, (r1_tarski(k8_relat_1('#skF_1', '#skF_3'), k8_relat_1('#skF_2', '#skF_4')) | ~v1_relat_1(k8_relat_1('#skF_1', '#skF_3')) | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_374, c_8551])).
% 6.98/2.57  tff(c_8657, plain, (r1_tarski(k8_relat_1('#skF_1', '#skF_3'), k8_relat_1('#skF_2', '#skF_4')) | ~v1_relat_1(k8_relat_1('#skF_1', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_8612])).
% 6.98/2.57  tff(c_8658, plain, (~v1_relat_1(k8_relat_1('#skF_1', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_14, c_8657])).
% 6.98/2.57  tff(c_8663, plain, (~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_4, c_8658])).
% 6.98/2.57  tff(c_8667, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_22, c_8663])).
% 6.98/2.57  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.98/2.57  
% 6.98/2.57  Inference rules
% 6.98/2.57  ----------------------
% 6.98/2.57  #Ref     : 0
% 6.98/2.57  #Sup     : 1938
% 6.98/2.57  #Fact    : 0
% 6.98/2.57  #Define  : 0
% 6.98/2.57  #Split   : 12
% 6.98/2.57  #Chain   : 0
% 6.98/2.57  #Close   : 0
% 6.98/2.57  
% 6.98/2.57  Ordering : KBO
% 6.98/2.57  
% 6.98/2.57  Simplification rules
% 6.98/2.57  ----------------------
% 6.98/2.57  #Subsume      : 692
% 6.98/2.57  #Demod        : 826
% 6.98/2.57  #Tautology    : 240
% 6.98/2.57  #SimpNegUnit  : 1
% 6.98/2.57  #BackRed      : 0
% 6.98/2.57  
% 6.98/2.57  #Partial instantiations: 0
% 6.98/2.57  #Strategies tried      : 1
% 6.98/2.57  
% 6.98/2.57  Timing (in seconds)
% 6.98/2.57  ----------------------
% 6.98/2.57  Preprocessing        : 0.29
% 6.98/2.57  Parsing              : 0.16
% 6.98/2.57  CNF conversion       : 0.02
% 6.98/2.57  Main loop            : 1.49
% 6.98/2.57  Inferencing          : 0.43
% 6.98/2.57  Reduction            : 0.41
% 6.98/2.57  Demodulation         : 0.28
% 6.98/2.57  BG Simplification    : 0.04
% 6.98/2.57  Subsumption          : 0.51
% 6.98/2.57  Abstraction          : 0.06
% 6.98/2.57  MUC search           : 0.00
% 6.98/2.57  Cooper               : 0.00
% 6.98/2.57  Total                : 1.80
% 6.98/2.57  Index Insertion      : 0.00
% 6.98/2.57  Index Deletion       : 0.00
% 6.98/2.57  Index Matching       : 0.00
% 6.98/2.57  BG Taut test         : 0.00
%------------------------------------------------------------------------------
