%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:06:45 EST 2020

% Result     : Theorem 3.91s
% Output     : CNFRefutation 3.91s
% Verified   : 
% Statistics : Number of formulae       :   50 (  59 expanded)
%              Number of leaves         :   28 (  34 expanded)
%              Depth                    :    9
%              Number of atoms          :   62 (  85 expanded)
%              Number of equality atoms :   15 (  19 expanded)
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

tff(f_72,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => k2_wellord1(A,k3_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_wellord1)).

tff(f_51,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k3_relat_1(A) = k2_xboole_0(k1_relat_1(A),k2_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_relat_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( C = k2_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            | r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).

tff(f_57,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k2_relat_1(B),A)
       => k8_relat_1(A,B) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t125_relat_1)).

tff(f_67,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_wellord1(B,A) = k7_relat_1(k8_relat_1(A,B),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_wellord1)).

tff(f_63,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k1_relat_1(B),A)
       => k7_relat_1(B,A) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t97_relat_1)).

tff(c_42,plain,(
    v1_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_32,plain,(
    ! [A_19] :
      ( k2_xboole_0(k1_relat_1(A_19),k2_relat_1(A_19)) = k3_relat_1(A_19)
      | ~ v1_relat_1(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_10,plain,(
    ! [D_11,B_7,A_6] :
      ( ~ r2_hidden(D_11,B_7)
      | r2_hidden(D_11,k2_xboole_0(A_6,B_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_63,plain,(
    ! [A_36,B_37] :
      ( ~ r2_hidden('#skF_1'(A_36,B_37),B_37)
      | r1_tarski(A_36,B_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_478,plain,(
    ! [A_107,A_108,B_109] :
      ( r1_tarski(A_107,k2_xboole_0(A_108,B_109))
      | ~ r2_hidden('#skF_1'(A_107,k2_xboole_0(A_108,B_109)),B_109) ) ),
    inference(resolution,[status(thm)],[c_10,c_63])).

tff(c_522,plain,(
    ! [A_110,A_111] : r1_tarski(A_110,k2_xboole_0(A_111,A_110)) ),
    inference(resolution,[status(thm)],[c_6,c_478])).

tff(c_544,plain,(
    ! [A_112] :
      ( r1_tarski(k2_relat_1(A_112),k3_relat_1(A_112))
      | ~ v1_relat_1(A_112) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_522])).

tff(c_34,plain,(
    ! [A_20,B_21] :
      ( k8_relat_1(A_20,B_21) = B_21
      | ~ r1_tarski(k2_relat_1(B_21),A_20)
      | ~ v1_relat_1(B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_606,plain,(
    ! [A_116] :
      ( k8_relat_1(k3_relat_1(A_116),A_116) = A_116
      | ~ v1_relat_1(A_116) ) ),
    inference(resolution,[status(thm)],[c_544,c_34])).

tff(c_38,plain,(
    ! [A_24,B_25] :
      ( k7_relat_1(k8_relat_1(A_24,B_25),A_24) = k2_wellord1(B_25,A_24)
      | ~ v1_relat_1(B_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_1806,plain,(
    ! [A_202] :
      ( k7_relat_1(A_202,k3_relat_1(A_202)) = k2_wellord1(A_202,k3_relat_1(A_202))
      | ~ v1_relat_1(A_202)
      | ~ v1_relat_1(A_202) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_606,c_38])).

tff(c_12,plain,(
    ! [D_11,A_6,B_7] :
      ( ~ r2_hidden(D_11,A_6)
      | r2_hidden(D_11,k2_xboole_0(A_6,B_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_220,plain,(
    ! [A_74,A_75,B_76] :
      ( r1_tarski(A_74,k2_xboole_0(A_75,B_76))
      | ~ r2_hidden('#skF_1'(A_74,k2_xboole_0(A_75,B_76)),A_75) ) ),
    inference(resolution,[status(thm)],[c_12,c_63])).

tff(c_254,plain,(
    ! [A_77,B_78] : r1_tarski(A_77,k2_xboole_0(A_77,B_78)) ),
    inference(resolution,[status(thm)],[c_6,c_220])).

tff(c_293,plain,(
    ! [A_82] :
      ( r1_tarski(k1_relat_1(A_82),k3_relat_1(A_82))
      | ~ v1_relat_1(A_82) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_254])).

tff(c_36,plain,(
    ! [B_23,A_22] :
      ( k7_relat_1(B_23,A_22) = B_23
      | ~ r1_tarski(k1_relat_1(B_23),A_22)
      | ~ v1_relat_1(B_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_297,plain,(
    ! [A_82] :
      ( k7_relat_1(A_82,k3_relat_1(A_82)) = A_82
      | ~ v1_relat_1(A_82) ) ),
    inference(resolution,[status(thm)],[c_293,c_36])).

tff(c_2068,plain,(
    ! [A_207] :
      ( k2_wellord1(A_207,k3_relat_1(A_207)) = A_207
      | ~ v1_relat_1(A_207)
      | ~ v1_relat_1(A_207)
      | ~ v1_relat_1(A_207) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1806,c_297])).

tff(c_40,plain,(
    k2_wellord1('#skF_4',k3_relat_1('#skF_4')) != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_2074,plain,(
    ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_2068,c_40])).

tff(c_2082,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_2074])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:17:52 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.91/1.69  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.91/1.69  
% 3.91/1.69  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.91/1.69  %$ r2_hidden > r1_tarski > v1_relat_1 > k2_enumset1 > k1_enumset1 > k8_relat_1 > k7_relat_1 > k2_xboole_0 > k2_wellord1 > k2_tarski > #nlpp > k3_tarski > k3_relat_1 > k2_relat_1 > k1_relat_1 > #skF_2 > #skF_4 > #skF_3 > #skF_1
% 3.91/1.69  
% 3.91/1.69  %Foreground sorts:
% 3.91/1.69  
% 3.91/1.69  
% 3.91/1.69  %Background operators:
% 3.91/1.69  
% 3.91/1.69  
% 3.91/1.69  %Foreground operators:
% 3.91/1.69  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 3.91/1.69  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.91/1.69  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.91/1.69  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 3.91/1.69  tff(k3_relat_1, type, k3_relat_1: $i > $i).
% 3.91/1.69  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.91/1.69  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.91/1.69  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.91/1.69  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.91/1.69  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.91/1.69  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 3.91/1.69  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.91/1.69  tff(k3_tarski, type, k3_tarski: $i > $i).
% 3.91/1.69  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.91/1.69  tff('#skF_4', type, '#skF_4': $i).
% 3.91/1.69  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 3.91/1.69  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.91/1.69  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.91/1.69  tff(k2_wellord1, type, k2_wellord1: ($i * $i) > $i).
% 3.91/1.69  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.91/1.69  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.91/1.69  
% 3.91/1.70  tff(f_72, negated_conjecture, ~(![A]: (v1_relat_1(A) => (k2_wellord1(A, k3_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t30_wellord1)).
% 3.91/1.70  tff(f_51, axiom, (![A]: (v1_relat_1(A) => (k3_relat_1(A) = k2_xboole_0(k1_relat_1(A), k2_relat_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d6_relat_1)).
% 3.91/1.70  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 3.91/1.70  tff(f_41, axiom, (![A, B, C]: ((C = k2_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) | r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_xboole_0)).
% 3.91/1.70  tff(f_57, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(B), A) => (k8_relat_1(A, B) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t125_relat_1)).
% 3.91/1.70  tff(f_67, axiom, (![A, B]: (v1_relat_1(B) => (k2_wellord1(B, A) = k7_relat_1(k8_relat_1(A, B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_wellord1)).
% 3.91/1.70  tff(f_63, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(B), A) => (k7_relat_1(B, A) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t97_relat_1)).
% 3.91/1.70  tff(c_42, plain, (v1_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.91/1.70  tff(c_32, plain, (![A_19]: (k2_xboole_0(k1_relat_1(A_19), k2_relat_1(A_19))=k3_relat_1(A_19) | ~v1_relat_1(A_19))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.91/1.70  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.91/1.70  tff(c_10, plain, (![D_11, B_7, A_6]: (~r2_hidden(D_11, B_7) | r2_hidden(D_11, k2_xboole_0(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.91/1.70  tff(c_63, plain, (![A_36, B_37]: (~r2_hidden('#skF_1'(A_36, B_37), B_37) | r1_tarski(A_36, B_37))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.91/1.70  tff(c_478, plain, (![A_107, A_108, B_109]: (r1_tarski(A_107, k2_xboole_0(A_108, B_109)) | ~r2_hidden('#skF_1'(A_107, k2_xboole_0(A_108, B_109)), B_109))), inference(resolution, [status(thm)], [c_10, c_63])).
% 3.91/1.70  tff(c_522, plain, (![A_110, A_111]: (r1_tarski(A_110, k2_xboole_0(A_111, A_110)))), inference(resolution, [status(thm)], [c_6, c_478])).
% 3.91/1.70  tff(c_544, plain, (![A_112]: (r1_tarski(k2_relat_1(A_112), k3_relat_1(A_112)) | ~v1_relat_1(A_112))), inference(superposition, [status(thm), theory('equality')], [c_32, c_522])).
% 3.91/1.70  tff(c_34, plain, (![A_20, B_21]: (k8_relat_1(A_20, B_21)=B_21 | ~r1_tarski(k2_relat_1(B_21), A_20) | ~v1_relat_1(B_21))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.91/1.70  tff(c_606, plain, (![A_116]: (k8_relat_1(k3_relat_1(A_116), A_116)=A_116 | ~v1_relat_1(A_116))), inference(resolution, [status(thm)], [c_544, c_34])).
% 3.91/1.70  tff(c_38, plain, (![A_24, B_25]: (k7_relat_1(k8_relat_1(A_24, B_25), A_24)=k2_wellord1(B_25, A_24) | ~v1_relat_1(B_25))), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.91/1.70  tff(c_1806, plain, (![A_202]: (k7_relat_1(A_202, k3_relat_1(A_202))=k2_wellord1(A_202, k3_relat_1(A_202)) | ~v1_relat_1(A_202) | ~v1_relat_1(A_202))), inference(superposition, [status(thm), theory('equality')], [c_606, c_38])).
% 3.91/1.70  tff(c_12, plain, (![D_11, A_6, B_7]: (~r2_hidden(D_11, A_6) | r2_hidden(D_11, k2_xboole_0(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.91/1.70  tff(c_220, plain, (![A_74, A_75, B_76]: (r1_tarski(A_74, k2_xboole_0(A_75, B_76)) | ~r2_hidden('#skF_1'(A_74, k2_xboole_0(A_75, B_76)), A_75))), inference(resolution, [status(thm)], [c_12, c_63])).
% 3.91/1.70  tff(c_254, plain, (![A_77, B_78]: (r1_tarski(A_77, k2_xboole_0(A_77, B_78)))), inference(resolution, [status(thm)], [c_6, c_220])).
% 3.91/1.70  tff(c_293, plain, (![A_82]: (r1_tarski(k1_relat_1(A_82), k3_relat_1(A_82)) | ~v1_relat_1(A_82))), inference(superposition, [status(thm), theory('equality')], [c_32, c_254])).
% 3.91/1.70  tff(c_36, plain, (![B_23, A_22]: (k7_relat_1(B_23, A_22)=B_23 | ~r1_tarski(k1_relat_1(B_23), A_22) | ~v1_relat_1(B_23))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.91/1.70  tff(c_297, plain, (![A_82]: (k7_relat_1(A_82, k3_relat_1(A_82))=A_82 | ~v1_relat_1(A_82))), inference(resolution, [status(thm)], [c_293, c_36])).
% 3.91/1.70  tff(c_2068, plain, (![A_207]: (k2_wellord1(A_207, k3_relat_1(A_207))=A_207 | ~v1_relat_1(A_207) | ~v1_relat_1(A_207) | ~v1_relat_1(A_207))), inference(superposition, [status(thm), theory('equality')], [c_1806, c_297])).
% 3.91/1.70  tff(c_40, plain, (k2_wellord1('#skF_4', k3_relat_1('#skF_4'))!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.91/1.70  tff(c_2074, plain, (~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_2068, c_40])).
% 3.91/1.70  tff(c_2082, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_42, c_2074])).
% 3.91/1.70  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.91/1.70  
% 3.91/1.70  Inference rules
% 3.91/1.70  ----------------------
% 3.91/1.70  #Ref     : 0
% 3.91/1.70  #Sup     : 451
% 3.91/1.70  #Fact    : 6
% 3.91/1.70  #Define  : 0
% 3.91/1.70  #Split   : 0
% 3.91/1.70  #Chain   : 0
% 3.91/1.70  #Close   : 0
% 3.91/1.70  
% 3.91/1.70  Ordering : KBO
% 3.91/1.70  
% 3.91/1.70  Simplification rules
% 3.91/1.70  ----------------------
% 3.91/1.70  #Subsume      : 63
% 3.91/1.70  #Demod        : 8
% 3.91/1.70  #Tautology    : 148
% 3.91/1.70  #SimpNegUnit  : 0
% 3.91/1.70  #BackRed      : 1
% 3.91/1.70  
% 3.91/1.71  #Partial instantiations: 0
% 3.91/1.71  #Strategies tried      : 1
% 3.91/1.71  
% 3.91/1.71  Timing (in seconds)
% 3.91/1.71  ----------------------
% 3.91/1.71  Preprocessing        : 0.33
% 3.91/1.71  Parsing              : 0.17
% 3.91/1.71  CNF conversion       : 0.02
% 3.91/1.71  Main loop            : 0.56
% 3.91/1.71  Inferencing          : 0.23
% 3.91/1.71  Reduction            : 0.12
% 3.91/1.71  Demodulation         : 0.08
% 3.91/1.71  BG Simplification    : 0.03
% 3.91/1.71  Subsumption          : 0.13
% 3.91/1.71  Abstraction          : 0.04
% 3.91/1.71  MUC search           : 0.00
% 3.91/1.71  Cooper               : 0.00
% 3.91/1.71  Total                : 0.91
% 3.91/1.71  Index Insertion      : 0.00
% 3.91/1.71  Index Deletion       : 0.00
% 3.91/1.71  Index Matching       : 0.00
% 3.91/1.71  BG Taut test         : 0.00
%------------------------------------------------------------------------------
