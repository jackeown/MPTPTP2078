%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:06:45 EST 2020

% Result     : Theorem 3.17s
% Output     : CNFRefutation 3.19s
% Verified   : 
% Statistics : Number of formulae       :   50 (  53 expanded)
%              Number of leaves         :   29 (  32 expanded)
%              Depth                    :    8
%              Number of atoms          :   61 (  68 expanded)
%              Number of equality atoms :   16 (  18 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_relat_1 > k2_enumset1 > k1_enumset1 > k8_relat_1 > k7_relat_1 > k2_xboole_0 > k2_wellord1 > k2_tarski > #nlpp > k3_tarski > k3_relat_1 > k2_relat_1 > k1_relat_1 > #skF_2 > #skF_4 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k8_relat_1,type,(
    k8_relat_1: ( $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k3_relat_1,type,(
    k3_relat_1: $i > $i )).

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
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k2_wellord1,type,(
    k2_wellord1: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_74,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => k2_wellord1(A,k3_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_wellord1)).

tff(f_53,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k3_relat_1(A) = k2_xboole_0(k1_relat_1(A),k2_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_relat_1)).

tff(f_43,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_65,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k1_relat_1(B),A)
       => k7_relat_1(B,A) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t97_relat_1)).

tff(f_69,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_wellord1(B,A) = k8_relat_1(A,k7_relat_1(B,A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_wellord1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( C = k2_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            | r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_xboole_0)).

tff(f_59,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k2_relat_1(B),A)
       => k8_relat_1(A,B) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t125_relat_1)).

tff(c_44,plain,(
    v1_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_103,plain,(
    ! [A_51] :
      ( k2_xboole_0(k1_relat_1(A_51),k2_relat_1(A_51)) = k3_relat_1(A_51)
      | ~ v1_relat_1(A_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_26,plain,(
    ! [A_12,B_13] : r1_tarski(A_12,k2_xboole_0(A_12,B_13)) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_115,plain,(
    ! [A_51] :
      ( r1_tarski(k1_relat_1(A_51),k3_relat_1(A_51))
      | ~ v1_relat_1(A_51) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_103,c_26])).

tff(c_160,plain,(
    ! [B_60,A_61] :
      ( k7_relat_1(B_60,A_61) = B_60
      | ~ r1_tarski(k1_relat_1(B_60),A_61)
      | ~ v1_relat_1(B_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_192,plain,(
    ! [A_65] :
      ( k7_relat_1(A_65,k3_relat_1(A_65)) = A_65
      | ~ v1_relat_1(A_65) ) ),
    inference(resolution,[status(thm)],[c_115,c_160])).

tff(c_40,plain,(
    ! [A_26,B_27] :
      ( k8_relat_1(A_26,k7_relat_1(B_27,A_26)) = k2_wellord1(B_27,A_26)
      | ~ v1_relat_1(B_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_1143,plain,(
    ! [A_162] :
      ( k8_relat_1(k3_relat_1(A_162),A_162) = k2_wellord1(A_162,k3_relat_1(A_162))
      | ~ v1_relat_1(A_162)
      | ~ v1_relat_1(A_162) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_192,c_40])).

tff(c_34,plain,(
    ! [A_21] :
      ( k2_xboole_0(k1_relat_1(A_21),k2_relat_1(A_21)) = k3_relat_1(A_21)
      | ~ v1_relat_1(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_71,plain,(
    ! [D_39,B_40,A_41] :
      ( ~ r2_hidden(D_39,B_40)
      | r2_hidden(D_39,k2_xboole_0(A_41,B_40)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_484,plain,(
    ! [A_109,A_110,B_111] :
      ( r1_tarski(A_109,k2_xboole_0(A_110,B_111))
      | ~ r2_hidden('#skF_1'(A_109,k2_xboole_0(A_110,B_111)),B_111) ) ),
    inference(resolution,[status(thm)],[c_71,c_4])).

tff(c_528,plain,(
    ! [A_112,A_113] : r1_tarski(A_112,k2_xboole_0(A_113,A_112)) ),
    inference(resolution,[status(thm)],[c_6,c_484])).

tff(c_550,plain,(
    ! [A_114] :
      ( r1_tarski(k2_relat_1(A_114),k3_relat_1(A_114))
      | ~ v1_relat_1(A_114) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_528])).

tff(c_36,plain,(
    ! [A_22,B_23] :
      ( k8_relat_1(A_22,B_23) = B_23
      | ~ r1_tarski(k2_relat_1(B_23),A_22)
      | ~ v1_relat_1(B_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_554,plain,(
    ! [A_114] :
      ( k8_relat_1(k3_relat_1(A_114),A_114) = A_114
      | ~ v1_relat_1(A_114) ) ),
    inference(resolution,[status(thm)],[c_550,c_36])).

tff(c_1158,plain,(
    ! [A_163] :
      ( k2_wellord1(A_163,k3_relat_1(A_163)) = A_163
      | ~ v1_relat_1(A_163)
      | ~ v1_relat_1(A_163)
      | ~ v1_relat_1(A_163) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1143,c_554])).

tff(c_42,plain,(
    k2_wellord1('#skF_4',k3_relat_1('#skF_4')) != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_1164,plain,(
    ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1158,c_42])).

tff(c_1172,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_1164])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n017.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 10:50:31 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.17/1.47  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.19/1.48  
% 3.19/1.48  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.19/1.48  %$ r2_hidden > r1_tarski > v1_relat_1 > k2_enumset1 > k1_enumset1 > k8_relat_1 > k7_relat_1 > k2_xboole_0 > k2_wellord1 > k2_tarski > #nlpp > k3_tarski > k3_relat_1 > k2_relat_1 > k1_relat_1 > #skF_2 > #skF_4 > #skF_3 > #skF_1
% 3.19/1.48  
% 3.19/1.48  %Foreground sorts:
% 3.19/1.48  
% 3.19/1.48  
% 3.19/1.48  %Background operators:
% 3.19/1.48  
% 3.19/1.48  
% 3.19/1.48  %Foreground operators:
% 3.19/1.48  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 3.19/1.48  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.19/1.48  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.19/1.48  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 3.19/1.48  tff(k3_relat_1, type, k3_relat_1: $i > $i).
% 3.19/1.48  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.19/1.48  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.19/1.48  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.19/1.48  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.19/1.48  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.19/1.48  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 3.19/1.48  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.19/1.48  tff(k3_tarski, type, k3_tarski: $i > $i).
% 3.19/1.48  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.19/1.48  tff('#skF_4', type, '#skF_4': $i).
% 3.19/1.48  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 3.19/1.48  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.19/1.48  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.19/1.48  tff(k2_wellord1, type, k2_wellord1: ($i * $i) > $i).
% 3.19/1.48  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.19/1.48  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.19/1.48  
% 3.19/1.49  tff(f_74, negated_conjecture, ~(![A]: (v1_relat_1(A) => (k2_wellord1(A, k3_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t30_wellord1)).
% 3.19/1.49  tff(f_53, axiom, (![A]: (v1_relat_1(A) => (k3_relat_1(A) = k2_xboole_0(k1_relat_1(A), k2_relat_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d6_relat_1)).
% 3.19/1.49  tff(f_43, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 3.19/1.49  tff(f_65, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(B), A) => (k7_relat_1(B, A) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t97_relat_1)).
% 3.19/1.49  tff(f_69, axiom, (![A, B]: (v1_relat_1(B) => (k2_wellord1(B, A) = k8_relat_1(A, k7_relat_1(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t18_wellord1)).
% 3.19/1.49  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 3.19/1.49  tff(f_41, axiom, (![A, B, C]: ((C = k2_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) | r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_xboole_0)).
% 3.19/1.49  tff(f_59, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(B), A) => (k8_relat_1(A, B) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t125_relat_1)).
% 3.19/1.49  tff(c_44, plain, (v1_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.19/1.49  tff(c_103, plain, (![A_51]: (k2_xboole_0(k1_relat_1(A_51), k2_relat_1(A_51))=k3_relat_1(A_51) | ~v1_relat_1(A_51))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.19/1.49  tff(c_26, plain, (![A_12, B_13]: (r1_tarski(A_12, k2_xboole_0(A_12, B_13)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.19/1.49  tff(c_115, plain, (![A_51]: (r1_tarski(k1_relat_1(A_51), k3_relat_1(A_51)) | ~v1_relat_1(A_51))), inference(superposition, [status(thm), theory('equality')], [c_103, c_26])).
% 3.19/1.49  tff(c_160, plain, (![B_60, A_61]: (k7_relat_1(B_60, A_61)=B_60 | ~r1_tarski(k1_relat_1(B_60), A_61) | ~v1_relat_1(B_60))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.19/1.49  tff(c_192, plain, (![A_65]: (k7_relat_1(A_65, k3_relat_1(A_65))=A_65 | ~v1_relat_1(A_65))), inference(resolution, [status(thm)], [c_115, c_160])).
% 3.19/1.49  tff(c_40, plain, (![A_26, B_27]: (k8_relat_1(A_26, k7_relat_1(B_27, A_26))=k2_wellord1(B_27, A_26) | ~v1_relat_1(B_27))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.19/1.49  tff(c_1143, plain, (![A_162]: (k8_relat_1(k3_relat_1(A_162), A_162)=k2_wellord1(A_162, k3_relat_1(A_162)) | ~v1_relat_1(A_162) | ~v1_relat_1(A_162))), inference(superposition, [status(thm), theory('equality')], [c_192, c_40])).
% 3.19/1.49  tff(c_34, plain, (![A_21]: (k2_xboole_0(k1_relat_1(A_21), k2_relat_1(A_21))=k3_relat_1(A_21) | ~v1_relat_1(A_21))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.19/1.49  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.19/1.49  tff(c_71, plain, (![D_39, B_40, A_41]: (~r2_hidden(D_39, B_40) | r2_hidden(D_39, k2_xboole_0(A_41, B_40)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.19/1.49  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.19/1.49  tff(c_484, plain, (![A_109, A_110, B_111]: (r1_tarski(A_109, k2_xboole_0(A_110, B_111)) | ~r2_hidden('#skF_1'(A_109, k2_xboole_0(A_110, B_111)), B_111))), inference(resolution, [status(thm)], [c_71, c_4])).
% 3.19/1.49  tff(c_528, plain, (![A_112, A_113]: (r1_tarski(A_112, k2_xboole_0(A_113, A_112)))), inference(resolution, [status(thm)], [c_6, c_484])).
% 3.19/1.49  tff(c_550, plain, (![A_114]: (r1_tarski(k2_relat_1(A_114), k3_relat_1(A_114)) | ~v1_relat_1(A_114))), inference(superposition, [status(thm), theory('equality')], [c_34, c_528])).
% 3.19/1.49  tff(c_36, plain, (![A_22, B_23]: (k8_relat_1(A_22, B_23)=B_23 | ~r1_tarski(k2_relat_1(B_23), A_22) | ~v1_relat_1(B_23))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.19/1.49  tff(c_554, plain, (![A_114]: (k8_relat_1(k3_relat_1(A_114), A_114)=A_114 | ~v1_relat_1(A_114))), inference(resolution, [status(thm)], [c_550, c_36])).
% 3.19/1.49  tff(c_1158, plain, (![A_163]: (k2_wellord1(A_163, k3_relat_1(A_163))=A_163 | ~v1_relat_1(A_163) | ~v1_relat_1(A_163) | ~v1_relat_1(A_163))), inference(superposition, [status(thm), theory('equality')], [c_1143, c_554])).
% 3.19/1.49  tff(c_42, plain, (k2_wellord1('#skF_4', k3_relat_1('#skF_4'))!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.19/1.49  tff(c_1164, plain, (~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1158, c_42])).
% 3.19/1.49  tff(c_1172, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_44, c_1164])).
% 3.19/1.49  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.19/1.49  
% 3.19/1.49  Inference rules
% 3.19/1.49  ----------------------
% 3.19/1.49  #Ref     : 0
% 3.19/1.49  #Sup     : 244
% 3.19/1.49  #Fact    : 6
% 3.19/1.49  #Define  : 0
% 3.19/1.49  #Split   : 0
% 3.19/1.49  #Chain   : 0
% 3.19/1.49  #Close   : 0
% 3.19/1.49  
% 3.19/1.49  Ordering : KBO
% 3.19/1.49  
% 3.19/1.49  Simplification rules
% 3.19/1.49  ----------------------
% 3.19/1.49  #Subsume      : 12
% 3.19/1.49  #Demod        : 2
% 3.19/1.49  #Tautology    : 59
% 3.19/1.49  #SimpNegUnit  : 0
% 3.19/1.49  #BackRed      : 0
% 3.19/1.49  
% 3.19/1.49  #Partial instantiations: 0
% 3.19/1.49  #Strategies tried      : 1
% 3.19/1.49  
% 3.19/1.49  Timing (in seconds)
% 3.19/1.49  ----------------------
% 3.19/1.49  Preprocessing        : 0.30
% 3.19/1.49  Parsing              : 0.15
% 3.19/1.49  CNF conversion       : 0.02
% 3.19/1.49  Main loop            : 0.41
% 3.19/1.49  Inferencing          : 0.16
% 3.19/1.49  Reduction            : 0.09
% 3.19/1.49  Demodulation         : 0.06
% 3.19/1.49  BG Simplification    : 0.02
% 3.19/1.49  Subsumption          : 0.10
% 3.19/1.49  Abstraction          : 0.03
% 3.19/1.49  MUC search           : 0.00
% 3.19/1.49  Cooper               : 0.00
% 3.19/1.49  Total                : 0.73
% 3.19/1.49  Index Insertion      : 0.00
% 3.19/1.49  Index Deletion       : 0.00
% 3.19/1.49  Index Matching       : 0.00
% 3.19/1.49  BG Taut test         : 0.00
%------------------------------------------------------------------------------
