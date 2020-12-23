%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:04:56 EST 2020

% Result     : Theorem 6.76s
% Output     : CNFRefutation 6.76s
% Verified   : 
% Statistics : Number of formulae       :   51 (  67 expanded)
%              Number of leaves         :   27 (  36 expanded)
%              Depth                    :    6
%              Number of atoms          :   64 (  95 expanded)
%              Number of equality atoms :    6 (   9 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > v1_funct_1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k3_xboole_0 > k2_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k1_setfam_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_72,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_relat_1(C)
          & v1_funct_1(C) )
       => r1_tarski(k9_relat_1(C,k3_xboole_0(A,k10_relat_1(C,B))),k3_xboole_0(k9_relat_1(C,A),B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t149_funct_1)).

tff(f_37,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_59,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r1_tarski(A,B)
       => r1_tarski(k9_relat_1(C,A),k9_relat_1(C,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t156_relat_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_65,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => r1_tarski(k9_relat_1(B,k10_relat_1(B,A)),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t145_funct_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_xboole_0(A,B),C)
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_xboole_1)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(A,C) )
     => r1_tarski(A,k3_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_xboole_1)).

tff(c_30,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_8,plain,(
    ! [A_8,B_9] : r1_tarski(k3_xboole_0(A_8,B_9),A_8) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_7318,plain,(
    ! [C_451,A_452,B_453] :
      ( r1_tarski(k9_relat_1(C_451,A_452),k9_relat_1(C_451,B_453))
      | ~ r1_tarski(A_452,B_453)
      | ~ v1_relat_1(C_451) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_28,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_33,plain,(
    ! [B_36,A_37] : k3_xboole_0(B_36,A_37) = k3_xboole_0(A_37,B_36) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_48,plain,(
    ! [B_36,A_37] : r1_tarski(k3_xboole_0(B_36,A_37),A_37) ),
    inference(superposition,[status(thm),theory(equality)],[c_33,c_8])).

tff(c_24,plain,(
    ! [B_33,A_32] :
      ( r1_tarski(k9_relat_1(B_33,k10_relat_1(B_33,A_32)),A_32)
      | ~ v1_funct_1(B_33)
      | ~ v1_relat_1(B_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_460,plain,(
    ! [C_97,A_98,B_99] :
      ( r1_tarski(k9_relat_1(C_97,A_98),k9_relat_1(C_97,B_99))
      | ~ r1_tarski(A_98,B_99)
      | ~ v1_relat_1(C_97) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_6,plain,(
    ! [A_6,B_7] :
      ( k2_xboole_0(A_6,B_7) = B_7
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_898,plain,(
    ! [C_138,A_139,B_140] :
      ( k2_xboole_0(k9_relat_1(C_138,A_139),k9_relat_1(C_138,B_140)) = k9_relat_1(C_138,B_140)
      | ~ r1_tarski(A_139,B_140)
      | ~ v1_relat_1(C_138) ) ),
    inference(resolution,[status(thm)],[c_460,c_6])).

tff(c_4,plain,(
    ! [A_3,C_5,B_4] :
      ( r1_tarski(A_3,C_5)
      | ~ r1_tarski(k2_xboole_0(A_3,B_4),C_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_3094,plain,(
    ! [C_264,A_265,C_266,B_267] :
      ( r1_tarski(k9_relat_1(C_264,A_265),C_266)
      | ~ r1_tarski(k9_relat_1(C_264,B_267),C_266)
      | ~ r1_tarski(A_265,B_267)
      | ~ v1_relat_1(C_264) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_898,c_4])).

tff(c_7012,plain,(
    ! [B_424,A_425,A_426] :
      ( r1_tarski(k9_relat_1(B_424,A_425),A_426)
      | ~ r1_tarski(A_425,k10_relat_1(B_424,A_426))
      | ~ v1_funct_1(B_424)
      | ~ v1_relat_1(B_424) ) ),
    inference(resolution,[status(thm)],[c_24,c_3094])).

tff(c_191,plain,(
    ! [A_62,B_63,C_64] :
      ( r1_tarski(A_62,k3_xboole_0(B_63,C_64))
      | ~ r1_tarski(A_62,C_64)
      | ~ r1_tarski(A_62,B_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_26,plain,(
    ~ r1_tarski(k9_relat_1('#skF_3',k3_xboole_0('#skF_1',k10_relat_1('#skF_3','#skF_2'))),k3_xboole_0(k9_relat_1('#skF_3','#skF_1'),'#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_31,plain,(
    ~ r1_tarski(k9_relat_1('#skF_3',k3_xboole_0('#skF_1',k10_relat_1('#skF_3','#skF_2'))),k3_xboole_0('#skF_2',k9_relat_1('#skF_3','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_26])).

tff(c_209,plain,
    ( ~ r1_tarski(k9_relat_1('#skF_3',k3_xboole_0('#skF_1',k10_relat_1('#skF_3','#skF_2'))),k9_relat_1('#skF_3','#skF_1'))
    | ~ r1_tarski(k9_relat_1('#skF_3',k3_xboole_0('#skF_1',k10_relat_1('#skF_3','#skF_2'))),'#skF_2') ),
    inference(resolution,[status(thm)],[c_191,c_31])).

tff(c_352,plain,(
    ~ r1_tarski(k9_relat_1('#skF_3',k3_xboole_0('#skF_1',k10_relat_1('#skF_3','#skF_2'))),'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_209])).

tff(c_7058,plain,
    ( ~ r1_tarski(k3_xboole_0('#skF_1',k10_relat_1('#skF_3','#skF_2')),k10_relat_1('#skF_3','#skF_2'))
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_7012,c_352])).

tff(c_7089,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_48,c_7058])).

tff(c_7090,plain,(
    ~ r1_tarski(k9_relat_1('#skF_3',k3_xboole_0('#skF_1',k10_relat_1('#skF_3','#skF_2'))),k9_relat_1('#skF_3','#skF_1')) ),
    inference(splitRight,[status(thm)],[c_209])).

tff(c_7321,plain,
    ( ~ r1_tarski(k3_xboole_0('#skF_1',k10_relat_1('#skF_3','#skF_2')),'#skF_1')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_7318,c_7090])).

tff(c_7330,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_8,c_7321])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:12:25 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.76/2.89  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.76/2.90  
% 6.76/2.90  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.76/2.90  %$ r1_tarski > v1_relat_1 > v1_funct_1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k3_xboole_0 > k2_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k1_setfam_1 > #skF_2 > #skF_3 > #skF_1
% 6.76/2.90  
% 6.76/2.90  %Foreground sorts:
% 6.76/2.90  
% 6.76/2.90  
% 6.76/2.90  %Background operators:
% 6.76/2.90  
% 6.76/2.90  
% 6.76/2.90  %Foreground operators:
% 6.76/2.90  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 6.76/2.90  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.76/2.90  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 6.76/2.90  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.76/2.90  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 6.76/2.90  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 6.76/2.90  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 6.76/2.90  tff('#skF_2', type, '#skF_2': $i).
% 6.76/2.90  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 6.76/2.90  tff('#skF_3', type, '#skF_3': $i).
% 6.76/2.90  tff('#skF_1', type, '#skF_1': $i).
% 6.76/2.90  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 6.76/2.90  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.76/2.90  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 6.76/2.90  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 6.76/2.90  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.76/2.90  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 6.76/2.90  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 6.76/2.90  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 6.76/2.90  
% 6.76/2.91  tff(f_72, negated_conjecture, ~(![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => r1_tarski(k9_relat_1(C, k3_xboole_0(A, k10_relat_1(C, B))), k3_xboole_0(k9_relat_1(C, A), B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t149_funct_1)).
% 6.76/2.91  tff(f_37, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 6.76/2.91  tff(f_59, axiom, (![A, B, C]: (v1_relat_1(C) => (r1_tarski(A, B) => r1_tarski(k9_relat_1(C, A), k9_relat_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t156_relat_1)).
% 6.76/2.91  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 6.76/2.91  tff(f_65, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => r1_tarski(k9_relat_1(B, k10_relat_1(B, A)), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t145_funct_1)).
% 6.76/2.91  tff(f_35, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 6.76/2.91  tff(f_31, axiom, (![A, B, C]: (r1_tarski(k2_xboole_0(A, B), C) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_xboole_1)).
% 6.76/2.91  tff(f_43, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(A, C)) => r1_tarski(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t19_xboole_1)).
% 6.76/2.91  tff(c_30, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_72])).
% 6.76/2.91  tff(c_8, plain, (![A_8, B_9]: (r1_tarski(k3_xboole_0(A_8, B_9), A_8))), inference(cnfTransformation, [status(thm)], [f_37])).
% 6.76/2.91  tff(c_7318, plain, (![C_451, A_452, B_453]: (r1_tarski(k9_relat_1(C_451, A_452), k9_relat_1(C_451, B_453)) | ~r1_tarski(A_452, B_453) | ~v1_relat_1(C_451))), inference(cnfTransformation, [status(thm)], [f_59])).
% 6.76/2.91  tff(c_28, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_72])).
% 6.76/2.91  tff(c_33, plain, (![B_36, A_37]: (k3_xboole_0(B_36, A_37)=k3_xboole_0(A_37, B_36))), inference(cnfTransformation, [status(thm)], [f_27])).
% 6.76/2.91  tff(c_48, plain, (![B_36, A_37]: (r1_tarski(k3_xboole_0(B_36, A_37), A_37))), inference(superposition, [status(thm), theory('equality')], [c_33, c_8])).
% 6.76/2.91  tff(c_24, plain, (![B_33, A_32]: (r1_tarski(k9_relat_1(B_33, k10_relat_1(B_33, A_32)), A_32) | ~v1_funct_1(B_33) | ~v1_relat_1(B_33))), inference(cnfTransformation, [status(thm)], [f_65])).
% 6.76/2.91  tff(c_460, plain, (![C_97, A_98, B_99]: (r1_tarski(k9_relat_1(C_97, A_98), k9_relat_1(C_97, B_99)) | ~r1_tarski(A_98, B_99) | ~v1_relat_1(C_97))), inference(cnfTransformation, [status(thm)], [f_59])).
% 6.76/2.91  tff(c_6, plain, (![A_6, B_7]: (k2_xboole_0(A_6, B_7)=B_7 | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_35])).
% 6.76/2.91  tff(c_898, plain, (![C_138, A_139, B_140]: (k2_xboole_0(k9_relat_1(C_138, A_139), k9_relat_1(C_138, B_140))=k9_relat_1(C_138, B_140) | ~r1_tarski(A_139, B_140) | ~v1_relat_1(C_138))), inference(resolution, [status(thm)], [c_460, c_6])).
% 6.76/2.91  tff(c_4, plain, (![A_3, C_5, B_4]: (r1_tarski(A_3, C_5) | ~r1_tarski(k2_xboole_0(A_3, B_4), C_5))), inference(cnfTransformation, [status(thm)], [f_31])).
% 6.76/2.91  tff(c_3094, plain, (![C_264, A_265, C_266, B_267]: (r1_tarski(k9_relat_1(C_264, A_265), C_266) | ~r1_tarski(k9_relat_1(C_264, B_267), C_266) | ~r1_tarski(A_265, B_267) | ~v1_relat_1(C_264))), inference(superposition, [status(thm), theory('equality')], [c_898, c_4])).
% 6.76/2.91  tff(c_7012, plain, (![B_424, A_425, A_426]: (r1_tarski(k9_relat_1(B_424, A_425), A_426) | ~r1_tarski(A_425, k10_relat_1(B_424, A_426)) | ~v1_funct_1(B_424) | ~v1_relat_1(B_424))), inference(resolution, [status(thm)], [c_24, c_3094])).
% 6.76/2.91  tff(c_191, plain, (![A_62, B_63, C_64]: (r1_tarski(A_62, k3_xboole_0(B_63, C_64)) | ~r1_tarski(A_62, C_64) | ~r1_tarski(A_62, B_63))), inference(cnfTransformation, [status(thm)], [f_43])).
% 6.76/2.91  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 6.76/2.91  tff(c_26, plain, (~r1_tarski(k9_relat_1('#skF_3', k3_xboole_0('#skF_1', k10_relat_1('#skF_3', '#skF_2'))), k3_xboole_0(k9_relat_1('#skF_3', '#skF_1'), '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_72])).
% 6.76/2.91  tff(c_31, plain, (~r1_tarski(k9_relat_1('#skF_3', k3_xboole_0('#skF_1', k10_relat_1('#skF_3', '#skF_2'))), k3_xboole_0('#skF_2', k9_relat_1('#skF_3', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_26])).
% 6.76/2.91  tff(c_209, plain, (~r1_tarski(k9_relat_1('#skF_3', k3_xboole_0('#skF_1', k10_relat_1('#skF_3', '#skF_2'))), k9_relat_1('#skF_3', '#skF_1')) | ~r1_tarski(k9_relat_1('#skF_3', k3_xboole_0('#skF_1', k10_relat_1('#skF_3', '#skF_2'))), '#skF_2')), inference(resolution, [status(thm)], [c_191, c_31])).
% 6.76/2.91  tff(c_352, plain, (~r1_tarski(k9_relat_1('#skF_3', k3_xboole_0('#skF_1', k10_relat_1('#skF_3', '#skF_2'))), '#skF_2')), inference(splitLeft, [status(thm)], [c_209])).
% 6.76/2.91  tff(c_7058, plain, (~r1_tarski(k3_xboole_0('#skF_1', k10_relat_1('#skF_3', '#skF_2')), k10_relat_1('#skF_3', '#skF_2')) | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_7012, c_352])).
% 6.76/2.91  tff(c_7089, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_48, c_7058])).
% 6.76/2.91  tff(c_7090, plain, (~r1_tarski(k9_relat_1('#skF_3', k3_xboole_0('#skF_1', k10_relat_1('#skF_3', '#skF_2'))), k9_relat_1('#skF_3', '#skF_1'))), inference(splitRight, [status(thm)], [c_209])).
% 6.76/2.91  tff(c_7321, plain, (~r1_tarski(k3_xboole_0('#skF_1', k10_relat_1('#skF_3', '#skF_2')), '#skF_1') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_7318, c_7090])).
% 6.76/2.91  tff(c_7330, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_30, c_8, c_7321])).
% 6.76/2.91  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.76/2.91  
% 6.76/2.91  Inference rules
% 6.76/2.91  ----------------------
% 6.76/2.91  #Ref     : 0
% 6.76/2.91  #Sup     : 1779
% 6.76/2.91  #Fact    : 0
% 6.76/2.91  #Define  : 0
% 6.76/2.91  #Split   : 1
% 6.76/2.91  #Chain   : 0
% 6.76/2.91  #Close   : 0
% 6.76/2.91  
% 6.76/2.91  Ordering : KBO
% 6.76/2.91  
% 6.76/2.91  Simplification rules
% 6.76/2.91  ----------------------
% 6.76/2.91  #Subsume      : 118
% 6.76/2.91  #Demod        : 351
% 6.76/2.91  #Tautology    : 719
% 6.76/2.91  #SimpNegUnit  : 0
% 6.76/2.91  #BackRed      : 0
% 6.76/2.91  
% 6.76/2.91  #Partial instantiations: 0
% 6.76/2.91  #Strategies tried      : 1
% 6.76/2.91  
% 6.76/2.91  Timing (in seconds)
% 6.76/2.91  ----------------------
% 6.76/2.91  Preprocessing        : 0.49
% 6.76/2.91  Parsing              : 0.27
% 6.76/2.91  CNF conversion       : 0.03
% 6.76/2.91  Main loop            : 1.50
% 6.76/2.91  Inferencing          : 0.40
% 6.76/2.91  Reduction            : 0.60
% 6.76/2.91  Demodulation         : 0.52
% 6.76/2.91  BG Simplification    : 0.05
% 6.76/2.91  Subsumption          : 0.34
% 6.76/2.91  Abstraction          : 0.06
% 6.76/2.91  MUC search           : 0.00
% 6.76/2.91  Cooper               : 0.00
% 6.76/2.91  Total                : 2.01
% 6.76/2.91  Index Insertion      : 0.00
% 6.76/2.91  Index Deletion       : 0.00
% 6.76/2.91  Index Matching       : 0.00
% 6.76/2.91  BG Taut test         : 0.00
%------------------------------------------------------------------------------
