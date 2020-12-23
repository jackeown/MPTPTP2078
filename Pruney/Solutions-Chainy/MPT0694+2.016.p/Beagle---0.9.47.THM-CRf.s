%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:04:55 EST 2020

% Result     : Theorem 32.69s
% Output     : CNFRefutation 32.69s
% Verified   : 
% Statistics : Number of formulae       :   54 (  75 expanded)
%              Number of leaves         :   28 (  39 expanded)
%              Depth                    :    6
%              Number of atoms          :   80 ( 120 expanded)
%              Number of equality atoms :    5 (  12 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > v1_funct_1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k2_relat_1 > k1_setfam_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

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

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_95,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_relat_1(C)
          & v1_funct_1(C) )
       => r1_tarski(k9_relat_1(C,k3_xboole_0(A,k10_relat_1(C,B))),k3_xboole_0(k9_relat_1(C,A),B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t149_funct_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_49,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_47,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_78,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ! [D] :
          ( v1_relat_1(D)
         => ( ( r1_tarski(C,D)
              & r1_tarski(A,B) )
           => r1_tarski(k9_relat_1(C,A),k9_relat_1(D,B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t158_relat_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_88,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => r1_tarski(k9_relat_1(B,k10_relat_1(B,A)),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t145_funct_1)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(A,C) )
     => r1_tarski(A,k3_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_xboole_1)).

tff(c_40,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_8,plain,(
    ! [B_4] : r1_tarski(B_4,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_107,plain,(
    ! [A_52,B_53] : k4_xboole_0(A_52,k4_xboole_0(A_52,B_53)) = k3_xboole_0(A_52,B_53) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_14,plain,(
    ! [A_11,B_12] : r1_tarski(k4_xboole_0(A_11,B_12),A_11) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_116,plain,(
    ! [A_52,B_53] : r1_tarski(k3_xboole_0(A_52,B_53),A_52) ),
    inference(superposition,[status(thm),theory(equality)],[c_107,c_14])).

tff(c_108578,plain,(
    ! [C_1403,A_1404,D_1405,B_1406] :
      ( r1_tarski(k9_relat_1(C_1403,A_1404),k9_relat_1(D_1405,B_1406))
      | ~ r1_tarski(A_1404,B_1406)
      | ~ r1_tarski(C_1403,D_1405)
      | ~ v1_relat_1(D_1405)
      | ~ v1_relat_1(C_1403) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_38,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_125,plain,(
    ! [A_54,B_55] : r1_tarski(k3_xboole_0(A_54,B_55),A_54) ),
    inference(superposition,[status(thm),theory(equality)],[c_107,c_14])).

tff(c_130,plain,(
    ! [B_2,A_1] : r1_tarski(k3_xboole_0(B_2,A_1),A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_125])).

tff(c_30,plain,(
    ! [C_31,A_29,D_33,B_30] :
      ( r1_tarski(k9_relat_1(C_31,A_29),k9_relat_1(D_33,B_30))
      | ~ r1_tarski(A_29,B_30)
      | ~ r1_tarski(C_31,D_33)
      | ~ v1_relat_1(D_33)
      | ~ v1_relat_1(C_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_626,plain,(
    ! [B_108,A_109] :
      ( r1_tarski(k9_relat_1(B_108,k10_relat_1(B_108,A_109)),A_109)
      | ~ v1_funct_1(B_108)
      | ~ v1_relat_1(B_108) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_12,plain,(
    ! [A_8,C_10,B_9] :
      ( r1_tarski(A_8,C_10)
      | ~ r1_tarski(B_9,C_10)
      | ~ r1_tarski(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_2689,plain,(
    ! [A_154,A_155,B_156] :
      ( r1_tarski(A_154,A_155)
      | ~ r1_tarski(A_154,k9_relat_1(B_156,k10_relat_1(B_156,A_155)))
      | ~ v1_funct_1(B_156)
      | ~ v1_relat_1(B_156) ) ),
    inference(resolution,[status(thm)],[c_626,c_12])).

tff(c_19313,plain,(
    ! [C_504,A_505,A_506,D_507] :
      ( r1_tarski(k9_relat_1(C_504,A_505),A_506)
      | ~ v1_funct_1(D_507)
      | ~ r1_tarski(A_505,k10_relat_1(D_507,A_506))
      | ~ r1_tarski(C_504,D_507)
      | ~ v1_relat_1(D_507)
      | ~ v1_relat_1(C_504) ) ),
    inference(resolution,[status(thm)],[c_30,c_2689])).

tff(c_106539,plain,(
    ! [C_1356,B_1357,D_1358,A_1359] :
      ( r1_tarski(k9_relat_1(C_1356,k3_xboole_0(B_1357,k10_relat_1(D_1358,A_1359))),A_1359)
      | ~ v1_funct_1(D_1358)
      | ~ r1_tarski(C_1356,D_1358)
      | ~ v1_relat_1(D_1358)
      | ~ v1_relat_1(C_1356) ) ),
    inference(resolution,[status(thm)],[c_130,c_19313])).

tff(c_323,plain,(
    ! [A_84,B_85,C_86] :
      ( r1_tarski(A_84,k3_xboole_0(B_85,C_86))
      | ~ r1_tarski(A_84,C_86)
      | ~ r1_tarski(A_84,B_85) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_36,plain,(
    ~ r1_tarski(k9_relat_1('#skF_3',k3_xboole_0('#skF_1',k10_relat_1('#skF_3','#skF_2'))),k3_xboole_0(k9_relat_1('#skF_3','#skF_1'),'#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_42,plain,(
    ~ r1_tarski(k9_relat_1('#skF_3',k3_xboole_0('#skF_1',k10_relat_1('#skF_3','#skF_2'))),k3_xboole_0('#skF_2',k9_relat_1('#skF_3','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_36])).

tff(c_338,plain,
    ( ~ r1_tarski(k9_relat_1('#skF_3',k3_xboole_0('#skF_1',k10_relat_1('#skF_3','#skF_2'))),k9_relat_1('#skF_3','#skF_1'))
    | ~ r1_tarski(k9_relat_1('#skF_3',k3_xboole_0('#skF_1',k10_relat_1('#skF_3','#skF_2'))),'#skF_2') ),
    inference(resolution,[status(thm)],[c_323,c_42])).

tff(c_420,plain,(
    ~ r1_tarski(k9_relat_1('#skF_3',k3_xboole_0('#skF_1',k10_relat_1('#skF_3','#skF_2'))),'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_338])).

tff(c_106708,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ r1_tarski('#skF_3','#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_106539,c_420])).

tff(c_106840,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_8,c_38,c_106708])).

tff(c_106841,plain,(
    ~ r1_tarski(k9_relat_1('#skF_3',k3_xboole_0('#skF_1',k10_relat_1('#skF_3','#skF_2'))),k9_relat_1('#skF_3','#skF_1')) ),
    inference(splitRight,[status(thm)],[c_338])).

tff(c_108588,plain,
    ( ~ r1_tarski(k3_xboole_0('#skF_1',k10_relat_1('#skF_3','#skF_2')),'#skF_1')
    | ~ r1_tarski('#skF_3','#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_108578,c_106841])).

tff(c_108600,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_8,c_116,c_108588])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n018.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 17:44:42 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 32.69/22.85  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 32.69/22.85  
% 32.69/22.85  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 32.69/22.85  %$ r1_tarski > v1_relat_1 > v1_funct_1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k2_relat_1 > k1_setfam_1 > #skF_2 > #skF_3 > #skF_1
% 32.69/22.85  
% 32.69/22.85  %Foreground sorts:
% 32.69/22.85  
% 32.69/22.85  
% 32.69/22.85  %Background operators:
% 32.69/22.85  
% 32.69/22.85  
% 32.69/22.85  %Foreground operators:
% 32.69/22.85  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 32.69/22.85  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 32.69/22.85  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 32.69/22.85  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 32.69/22.85  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 32.69/22.85  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 32.69/22.85  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 32.69/22.85  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 32.69/22.85  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 32.69/22.85  tff('#skF_2', type, '#skF_2': $i).
% 32.69/22.85  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 32.69/22.85  tff('#skF_3', type, '#skF_3': $i).
% 32.69/22.85  tff('#skF_1', type, '#skF_1': $i).
% 32.69/22.85  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 32.69/22.85  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 32.69/22.85  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 32.69/22.85  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 32.69/22.85  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 32.69/22.85  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 32.69/22.85  
% 32.69/22.86  tff(f_95, negated_conjecture, ~(![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => r1_tarski(k9_relat_1(C, k3_xboole_0(A, k10_relat_1(C, B))), k3_xboole_0(k9_relat_1(C, A), B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t149_funct_1)).
% 32.69/22.86  tff(f_33, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 32.69/22.86  tff(f_49, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 32.69/22.86  tff(f_47, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 32.69/22.86  tff(f_78, axiom, (![A, B, C]: (v1_relat_1(C) => (![D]: (v1_relat_1(D) => ((r1_tarski(C, D) & r1_tarski(A, B)) => r1_tarski(k9_relat_1(C, A), k9_relat_1(D, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t158_relat_1)).
% 32.69/22.86  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 32.69/22.86  tff(f_88, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => r1_tarski(k9_relat_1(B, k10_relat_1(B, A)), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t145_funct_1)).
% 32.69/22.86  tff(f_45, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 32.69/22.86  tff(f_39, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(A, C)) => r1_tarski(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t19_xboole_1)).
% 32.69/22.86  tff(c_40, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_95])).
% 32.69/22.86  tff(c_8, plain, (![B_4]: (r1_tarski(B_4, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 32.69/22.86  tff(c_107, plain, (![A_52, B_53]: (k4_xboole_0(A_52, k4_xboole_0(A_52, B_53))=k3_xboole_0(A_52, B_53))), inference(cnfTransformation, [status(thm)], [f_49])).
% 32.69/22.86  tff(c_14, plain, (![A_11, B_12]: (r1_tarski(k4_xboole_0(A_11, B_12), A_11))), inference(cnfTransformation, [status(thm)], [f_47])).
% 32.69/22.86  tff(c_116, plain, (![A_52, B_53]: (r1_tarski(k3_xboole_0(A_52, B_53), A_52))), inference(superposition, [status(thm), theory('equality')], [c_107, c_14])).
% 32.69/22.86  tff(c_108578, plain, (![C_1403, A_1404, D_1405, B_1406]: (r1_tarski(k9_relat_1(C_1403, A_1404), k9_relat_1(D_1405, B_1406)) | ~r1_tarski(A_1404, B_1406) | ~r1_tarski(C_1403, D_1405) | ~v1_relat_1(D_1405) | ~v1_relat_1(C_1403))), inference(cnfTransformation, [status(thm)], [f_78])).
% 32.69/22.86  tff(c_38, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_95])).
% 32.69/22.86  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 32.69/22.86  tff(c_125, plain, (![A_54, B_55]: (r1_tarski(k3_xboole_0(A_54, B_55), A_54))), inference(superposition, [status(thm), theory('equality')], [c_107, c_14])).
% 32.69/22.86  tff(c_130, plain, (![B_2, A_1]: (r1_tarski(k3_xboole_0(B_2, A_1), A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_125])).
% 32.69/22.87  tff(c_30, plain, (![C_31, A_29, D_33, B_30]: (r1_tarski(k9_relat_1(C_31, A_29), k9_relat_1(D_33, B_30)) | ~r1_tarski(A_29, B_30) | ~r1_tarski(C_31, D_33) | ~v1_relat_1(D_33) | ~v1_relat_1(C_31))), inference(cnfTransformation, [status(thm)], [f_78])).
% 32.69/22.87  tff(c_626, plain, (![B_108, A_109]: (r1_tarski(k9_relat_1(B_108, k10_relat_1(B_108, A_109)), A_109) | ~v1_funct_1(B_108) | ~v1_relat_1(B_108))), inference(cnfTransformation, [status(thm)], [f_88])).
% 32.69/22.87  tff(c_12, plain, (![A_8, C_10, B_9]: (r1_tarski(A_8, C_10) | ~r1_tarski(B_9, C_10) | ~r1_tarski(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_45])).
% 32.69/22.87  tff(c_2689, plain, (![A_154, A_155, B_156]: (r1_tarski(A_154, A_155) | ~r1_tarski(A_154, k9_relat_1(B_156, k10_relat_1(B_156, A_155))) | ~v1_funct_1(B_156) | ~v1_relat_1(B_156))), inference(resolution, [status(thm)], [c_626, c_12])).
% 32.69/22.87  tff(c_19313, plain, (![C_504, A_505, A_506, D_507]: (r1_tarski(k9_relat_1(C_504, A_505), A_506) | ~v1_funct_1(D_507) | ~r1_tarski(A_505, k10_relat_1(D_507, A_506)) | ~r1_tarski(C_504, D_507) | ~v1_relat_1(D_507) | ~v1_relat_1(C_504))), inference(resolution, [status(thm)], [c_30, c_2689])).
% 32.69/22.87  tff(c_106539, plain, (![C_1356, B_1357, D_1358, A_1359]: (r1_tarski(k9_relat_1(C_1356, k3_xboole_0(B_1357, k10_relat_1(D_1358, A_1359))), A_1359) | ~v1_funct_1(D_1358) | ~r1_tarski(C_1356, D_1358) | ~v1_relat_1(D_1358) | ~v1_relat_1(C_1356))), inference(resolution, [status(thm)], [c_130, c_19313])).
% 32.69/22.87  tff(c_323, plain, (![A_84, B_85, C_86]: (r1_tarski(A_84, k3_xboole_0(B_85, C_86)) | ~r1_tarski(A_84, C_86) | ~r1_tarski(A_84, B_85))), inference(cnfTransformation, [status(thm)], [f_39])).
% 32.69/22.87  tff(c_36, plain, (~r1_tarski(k9_relat_1('#skF_3', k3_xboole_0('#skF_1', k10_relat_1('#skF_3', '#skF_2'))), k3_xboole_0(k9_relat_1('#skF_3', '#skF_1'), '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_95])).
% 32.69/22.87  tff(c_42, plain, (~r1_tarski(k9_relat_1('#skF_3', k3_xboole_0('#skF_1', k10_relat_1('#skF_3', '#skF_2'))), k3_xboole_0('#skF_2', k9_relat_1('#skF_3', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_36])).
% 32.69/22.87  tff(c_338, plain, (~r1_tarski(k9_relat_1('#skF_3', k3_xboole_0('#skF_1', k10_relat_1('#skF_3', '#skF_2'))), k9_relat_1('#skF_3', '#skF_1')) | ~r1_tarski(k9_relat_1('#skF_3', k3_xboole_0('#skF_1', k10_relat_1('#skF_3', '#skF_2'))), '#skF_2')), inference(resolution, [status(thm)], [c_323, c_42])).
% 32.69/22.87  tff(c_420, plain, (~r1_tarski(k9_relat_1('#skF_3', k3_xboole_0('#skF_1', k10_relat_1('#skF_3', '#skF_2'))), '#skF_2')), inference(splitLeft, [status(thm)], [c_338])).
% 32.69/22.87  tff(c_106708, plain, (~v1_funct_1('#skF_3') | ~r1_tarski('#skF_3', '#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_106539, c_420])).
% 32.69/22.87  tff(c_106840, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_40, c_8, c_38, c_106708])).
% 32.69/22.87  tff(c_106841, plain, (~r1_tarski(k9_relat_1('#skF_3', k3_xboole_0('#skF_1', k10_relat_1('#skF_3', '#skF_2'))), k9_relat_1('#skF_3', '#skF_1'))), inference(splitRight, [status(thm)], [c_338])).
% 32.69/22.87  tff(c_108588, plain, (~r1_tarski(k3_xboole_0('#skF_1', k10_relat_1('#skF_3', '#skF_2')), '#skF_1') | ~r1_tarski('#skF_3', '#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_108578, c_106841])).
% 32.69/22.87  tff(c_108600, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_40, c_8, c_116, c_108588])).
% 32.69/22.87  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 32.69/22.87  
% 32.69/22.87  Inference rules
% 32.69/22.87  ----------------------
% 32.69/22.87  #Ref     : 0
% 32.69/22.87  #Sup     : 27051
% 32.69/22.87  #Fact    : 0
% 32.69/22.87  #Define  : 0
% 32.69/22.87  #Split   : 1
% 32.69/22.87  #Chain   : 0
% 32.69/22.87  #Close   : 0
% 32.69/22.87  
% 32.69/22.87  Ordering : KBO
% 32.69/22.87  
% 32.69/22.87  Simplification rules
% 32.69/22.87  ----------------------
% 32.69/22.87  #Subsume      : 2102
% 32.69/22.87  #Demod        : 10198
% 32.69/22.87  #Tautology    : 8511
% 32.69/22.87  #SimpNegUnit  : 0
% 32.69/22.87  #BackRed      : 0
% 32.69/22.87  
% 32.69/22.87  #Partial instantiations: 0
% 32.69/22.87  #Strategies tried      : 1
% 32.69/22.87  
% 32.69/22.87  Timing (in seconds)
% 32.69/22.87  ----------------------
% 32.69/22.87  Preprocessing        : 0.35
% 32.69/22.87  Parsing              : 0.18
% 32.69/22.87  CNF conversion       : 0.02
% 32.69/22.87  Main loop            : 21.72
% 32.69/22.87  Inferencing          : 2.16
% 32.69/22.87  Reduction            : 10.14
% 32.69/22.87  Demodulation         : 9.33
% 33.05/22.87  BG Simplification    : 0.37
% 33.05/22.87  Subsumption          : 7.83
% 33.05/22.87  Abstraction          : 0.45
% 33.05/22.87  MUC search           : 0.00
% 33.05/22.87  Cooper               : 0.00
% 33.05/22.87  Total                : 22.10
% 33.05/22.87  Index Insertion      : 0.00
% 33.05/22.87  Index Deletion       : 0.00
% 33.05/22.87  Index Matching       : 0.00
% 33.05/22.87  BG Taut test         : 0.00
%------------------------------------------------------------------------------
