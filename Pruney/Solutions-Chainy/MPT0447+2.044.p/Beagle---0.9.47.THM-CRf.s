%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:58:33 EST 2020

% Result     : Theorem 3.36s
% Output     : CNFRefutation 3.36s
% Verified   : 
% Statistics : Number of formulae       :   54 (  91 expanded)
%              Number of leaves         :   21 (  41 expanded)
%              Depth                    :   10
%              Number of atoms          :   88 ( 185 expanded)
%              Number of equality atoms :    9 (  15 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k3_relat_1 > k2_relat_1 > k1_relat_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k3_relat_1,type,(
    k3_relat_1: $i > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_72,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ! [B] :
            ( v1_relat_1(B)
           => ( r1_tarski(A,B)
             => r1_tarski(k3_relat_1(A),k3_relat_1(B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_relat_1)).

tff(f_62,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(A,B)
           => ( r1_tarski(k1_relat_1(A),k1_relat_1(B))
              & r1_tarski(k2_relat_1(A),k2_relat_1(B)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_relat_1)).

tff(f_51,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k3_relat_1(A) = k2_xboole_0(k1_relat_1(A),k2_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_relat_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(A,k2_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(C,B) )
     => r1_tarski(k2_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_xboole_1)).

tff(c_30,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_28,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_26,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_20,plain,(
    ! [A_16,B_18] :
      ( r1_tarski(k2_relat_1(A_16),k2_relat_1(B_18))
      | ~ r1_tarski(A_16,B_18)
      | ~ v1_relat_1(B_18)
      | ~ v1_relat_1(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_70,plain,(
    ! [A_32] :
      ( k2_xboole_0(k1_relat_1(A_32),k2_relat_1(A_32)) = k3_relat_1(A_32)
      | ~ v1_relat_1(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_8,plain,(
    ! [A_3,C_5,B_4] :
      ( r1_tarski(A_3,k2_xboole_0(C_5,B_4))
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_76,plain,(
    ! [A_3,A_32] :
      ( r1_tarski(A_3,k3_relat_1(A_32))
      | ~ r1_tarski(A_3,k2_relat_1(A_32))
      | ~ v1_relat_1(A_32) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_70,c_8])).

tff(c_22,plain,(
    ! [A_16,B_18] :
      ( r1_tarski(k1_relat_1(A_16),k1_relat_1(B_18))
      | ~ r1_tarski(A_16,B_18)
      | ~ v1_relat_1(B_18)
      | ~ v1_relat_1(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_10,plain,(
    ! [A_6,B_7] : r1_tarski(A_6,k2_xboole_0(A_6,B_7)) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_79,plain,(
    ! [A_32] :
      ( r1_tarski(k1_relat_1(A_32),k3_relat_1(A_32))
      | ~ v1_relat_1(A_32) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_70,c_10])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_98,plain,(
    ! [A_36,C_37,B_38] :
      ( r1_tarski(k2_xboole_0(A_36,C_37),B_38)
      | ~ r1_tarski(C_37,B_38)
      | ~ r1_tarski(A_36,B_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_52,plain,(
    ! [B_27,A_28] :
      ( B_27 = A_28
      | ~ r1_tarski(B_27,A_28)
      | ~ r1_tarski(A_28,B_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_59,plain,(
    ! [A_6,B_7] :
      ( k2_xboole_0(A_6,B_7) = A_6
      | ~ r1_tarski(k2_xboole_0(A_6,B_7),A_6) ) ),
    inference(resolution,[status(thm)],[c_10,c_52])).

tff(c_102,plain,(
    ! [B_38,C_37] :
      ( k2_xboole_0(B_38,C_37) = B_38
      | ~ r1_tarski(C_37,B_38)
      | ~ r1_tarski(B_38,B_38) ) ),
    inference(resolution,[status(thm)],[c_98,c_59])).

tff(c_112,plain,(
    ! [B_39,C_40] :
      ( k2_xboole_0(B_39,C_40) = B_39
      | ~ r1_tarski(C_40,B_39) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_102])).

tff(c_294,plain,(
    ! [A_50] :
      ( k2_xboole_0(k3_relat_1(A_50),k1_relat_1(A_50)) = k3_relat_1(A_50)
      | ~ v1_relat_1(A_50) ) ),
    inference(resolution,[status(thm)],[c_79,c_112])).

tff(c_312,plain,(
    ! [A_3,A_50] :
      ( r1_tarski(A_3,k3_relat_1(A_50))
      | ~ r1_tarski(A_3,k1_relat_1(A_50))
      | ~ v1_relat_1(A_50) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_294,c_8])).

tff(c_18,plain,(
    ! [A_15] :
      ( k2_xboole_0(k1_relat_1(A_15),k2_relat_1(A_15)) = k3_relat_1(A_15)
      | ~ v1_relat_1(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_1144,plain,(
    ! [A_98,B_99] :
      ( r1_tarski(k3_relat_1(A_98),B_99)
      | ~ r1_tarski(k2_relat_1(A_98),B_99)
      | ~ r1_tarski(k1_relat_1(A_98),B_99)
      | ~ v1_relat_1(A_98) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_98])).

tff(c_24,plain,(
    ~ r1_tarski(k3_relat_1('#skF_1'),k3_relat_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_1168,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_1'),k3_relat_1('#skF_2'))
    | ~ r1_tarski(k1_relat_1('#skF_1'),k3_relat_1('#skF_2'))
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_1144,c_24])).

tff(c_1184,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_1'),k3_relat_1('#skF_2'))
    | ~ r1_tarski(k1_relat_1('#skF_1'),k3_relat_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_1168])).

tff(c_1234,plain,(
    ~ r1_tarski(k1_relat_1('#skF_1'),k3_relat_1('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_1184])).

tff(c_1237,plain,
    ( ~ r1_tarski(k1_relat_1('#skF_1'),k1_relat_1('#skF_2'))
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_312,c_1234])).

tff(c_1243,plain,(
    ~ r1_tarski(k1_relat_1('#skF_1'),k1_relat_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_1237])).

tff(c_1249,plain,
    ( ~ r1_tarski('#skF_1','#skF_2')
    | ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_22,c_1243])).

tff(c_1253,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_26,c_1249])).

tff(c_1254,plain,(
    ~ r1_tarski(k2_relat_1('#skF_1'),k3_relat_1('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_1184])).

tff(c_1261,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_1'),k2_relat_1('#skF_2'))
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_76,c_1254])).

tff(c_1267,plain,(
    ~ r1_tarski(k2_relat_1('#skF_1'),k2_relat_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_1261])).

tff(c_1380,plain,
    ( ~ r1_tarski('#skF_1','#skF_2')
    | ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_20,c_1267])).

tff(c_1384,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_26,c_1380])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:43:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.36/1.55  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.36/1.56  
% 3.36/1.56  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.36/1.56  %$ r1_tarski > v1_relat_1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k3_relat_1 > k2_relat_1 > k1_relat_1 > #skF_2 > #skF_1
% 3.36/1.56  
% 3.36/1.56  %Foreground sorts:
% 3.36/1.56  
% 3.36/1.56  
% 3.36/1.56  %Background operators:
% 3.36/1.56  
% 3.36/1.56  
% 3.36/1.56  %Foreground operators:
% 3.36/1.56  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.36/1.56  tff(k3_relat_1, type, k3_relat_1: $i > $i).
% 3.36/1.56  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.36/1.56  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.36/1.56  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.36/1.56  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.36/1.56  tff('#skF_2', type, '#skF_2': $i).
% 3.36/1.56  tff('#skF_1', type, '#skF_1': $i).
% 3.36/1.56  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.36/1.56  tff(k3_tarski, type, k3_tarski: $i > $i).
% 3.36/1.56  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.36/1.56  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.36/1.56  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.36/1.56  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.36/1.56  
% 3.36/1.57  tff(f_72, negated_conjecture, ~(![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(A, B) => r1_tarski(k3_relat_1(A), k3_relat_1(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_relat_1)).
% 3.36/1.57  tff(f_62, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(A, B) => (r1_tarski(k1_relat_1(A), k1_relat_1(B)) & r1_tarski(k2_relat_1(A), k2_relat_1(B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t25_relat_1)).
% 3.36/1.57  tff(f_51, axiom, (![A]: (v1_relat_1(A) => (k3_relat_1(A) = k2_xboole_0(k1_relat_1(A), k2_relat_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d6_relat_1)).
% 3.36/1.57  tff(f_35, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(A, k2_xboole_0(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_xboole_1)).
% 3.36/1.57  tff(f_37, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 3.36/1.57  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.36/1.57  tff(f_43, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(C, B)) => r1_tarski(k2_xboole_0(A, C), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_xboole_1)).
% 3.36/1.57  tff(c_30, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.36/1.57  tff(c_28, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.36/1.57  tff(c_26, plain, (r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.36/1.57  tff(c_20, plain, (![A_16, B_18]: (r1_tarski(k2_relat_1(A_16), k2_relat_1(B_18)) | ~r1_tarski(A_16, B_18) | ~v1_relat_1(B_18) | ~v1_relat_1(A_16))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.36/1.57  tff(c_70, plain, (![A_32]: (k2_xboole_0(k1_relat_1(A_32), k2_relat_1(A_32))=k3_relat_1(A_32) | ~v1_relat_1(A_32))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.36/1.57  tff(c_8, plain, (![A_3, C_5, B_4]: (r1_tarski(A_3, k2_xboole_0(C_5, B_4)) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.36/1.57  tff(c_76, plain, (![A_3, A_32]: (r1_tarski(A_3, k3_relat_1(A_32)) | ~r1_tarski(A_3, k2_relat_1(A_32)) | ~v1_relat_1(A_32))), inference(superposition, [status(thm), theory('equality')], [c_70, c_8])).
% 3.36/1.57  tff(c_22, plain, (![A_16, B_18]: (r1_tarski(k1_relat_1(A_16), k1_relat_1(B_18)) | ~r1_tarski(A_16, B_18) | ~v1_relat_1(B_18) | ~v1_relat_1(A_16))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.36/1.57  tff(c_10, plain, (![A_6, B_7]: (r1_tarski(A_6, k2_xboole_0(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.36/1.57  tff(c_79, plain, (![A_32]: (r1_tarski(k1_relat_1(A_32), k3_relat_1(A_32)) | ~v1_relat_1(A_32))), inference(superposition, [status(thm), theory('equality')], [c_70, c_10])).
% 3.36/1.57  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.36/1.57  tff(c_98, plain, (![A_36, C_37, B_38]: (r1_tarski(k2_xboole_0(A_36, C_37), B_38) | ~r1_tarski(C_37, B_38) | ~r1_tarski(A_36, B_38))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.36/1.57  tff(c_52, plain, (![B_27, A_28]: (B_27=A_28 | ~r1_tarski(B_27, A_28) | ~r1_tarski(A_28, B_27))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.36/1.57  tff(c_59, plain, (![A_6, B_7]: (k2_xboole_0(A_6, B_7)=A_6 | ~r1_tarski(k2_xboole_0(A_6, B_7), A_6))), inference(resolution, [status(thm)], [c_10, c_52])).
% 3.36/1.57  tff(c_102, plain, (![B_38, C_37]: (k2_xboole_0(B_38, C_37)=B_38 | ~r1_tarski(C_37, B_38) | ~r1_tarski(B_38, B_38))), inference(resolution, [status(thm)], [c_98, c_59])).
% 3.36/1.57  tff(c_112, plain, (![B_39, C_40]: (k2_xboole_0(B_39, C_40)=B_39 | ~r1_tarski(C_40, B_39))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_102])).
% 3.36/1.57  tff(c_294, plain, (![A_50]: (k2_xboole_0(k3_relat_1(A_50), k1_relat_1(A_50))=k3_relat_1(A_50) | ~v1_relat_1(A_50))), inference(resolution, [status(thm)], [c_79, c_112])).
% 3.36/1.57  tff(c_312, plain, (![A_3, A_50]: (r1_tarski(A_3, k3_relat_1(A_50)) | ~r1_tarski(A_3, k1_relat_1(A_50)) | ~v1_relat_1(A_50))), inference(superposition, [status(thm), theory('equality')], [c_294, c_8])).
% 3.36/1.57  tff(c_18, plain, (![A_15]: (k2_xboole_0(k1_relat_1(A_15), k2_relat_1(A_15))=k3_relat_1(A_15) | ~v1_relat_1(A_15))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.36/1.57  tff(c_1144, plain, (![A_98, B_99]: (r1_tarski(k3_relat_1(A_98), B_99) | ~r1_tarski(k2_relat_1(A_98), B_99) | ~r1_tarski(k1_relat_1(A_98), B_99) | ~v1_relat_1(A_98))), inference(superposition, [status(thm), theory('equality')], [c_18, c_98])).
% 3.36/1.57  tff(c_24, plain, (~r1_tarski(k3_relat_1('#skF_1'), k3_relat_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.36/1.57  tff(c_1168, plain, (~r1_tarski(k2_relat_1('#skF_1'), k3_relat_1('#skF_2')) | ~r1_tarski(k1_relat_1('#skF_1'), k3_relat_1('#skF_2')) | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_1144, c_24])).
% 3.36/1.57  tff(c_1184, plain, (~r1_tarski(k2_relat_1('#skF_1'), k3_relat_1('#skF_2')) | ~r1_tarski(k1_relat_1('#skF_1'), k3_relat_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_1168])).
% 3.36/1.57  tff(c_1234, plain, (~r1_tarski(k1_relat_1('#skF_1'), k3_relat_1('#skF_2'))), inference(splitLeft, [status(thm)], [c_1184])).
% 3.36/1.57  tff(c_1237, plain, (~r1_tarski(k1_relat_1('#skF_1'), k1_relat_1('#skF_2')) | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_312, c_1234])).
% 3.36/1.57  tff(c_1243, plain, (~r1_tarski(k1_relat_1('#skF_1'), k1_relat_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_1237])).
% 3.36/1.57  tff(c_1249, plain, (~r1_tarski('#skF_1', '#skF_2') | ~v1_relat_1('#skF_2') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_22, c_1243])).
% 3.36/1.57  tff(c_1253, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_26, c_1249])).
% 3.36/1.57  tff(c_1254, plain, (~r1_tarski(k2_relat_1('#skF_1'), k3_relat_1('#skF_2'))), inference(splitRight, [status(thm)], [c_1184])).
% 3.36/1.57  tff(c_1261, plain, (~r1_tarski(k2_relat_1('#skF_1'), k2_relat_1('#skF_2')) | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_76, c_1254])).
% 3.36/1.57  tff(c_1267, plain, (~r1_tarski(k2_relat_1('#skF_1'), k2_relat_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_1261])).
% 3.36/1.57  tff(c_1380, plain, (~r1_tarski('#skF_1', '#skF_2') | ~v1_relat_1('#skF_2') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_20, c_1267])).
% 3.36/1.57  tff(c_1384, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_26, c_1380])).
% 3.36/1.57  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.36/1.57  
% 3.36/1.57  Inference rules
% 3.36/1.57  ----------------------
% 3.36/1.57  #Ref     : 0
% 3.36/1.57  #Sup     : 331
% 3.36/1.57  #Fact    : 0
% 3.36/1.57  #Define  : 0
% 3.36/1.57  #Split   : 2
% 3.36/1.57  #Chain   : 0
% 3.36/1.57  #Close   : 0
% 3.36/1.57  
% 3.36/1.57  Ordering : KBO
% 3.36/1.57  
% 3.36/1.57  Simplification rules
% 3.36/1.57  ----------------------
% 3.36/1.57  #Subsume      : 51
% 3.36/1.57  #Demod        : 114
% 3.36/1.57  #Tautology    : 95
% 3.36/1.57  #SimpNegUnit  : 0
% 3.36/1.57  #BackRed      : 0
% 3.36/1.57  
% 3.36/1.57  #Partial instantiations: 0
% 3.36/1.57  #Strategies tried      : 1
% 3.36/1.57  
% 3.36/1.57  Timing (in seconds)
% 3.36/1.57  ----------------------
% 3.36/1.57  Preprocessing        : 0.31
% 3.36/1.57  Parsing              : 0.16
% 3.36/1.57  CNF conversion       : 0.02
% 3.36/1.57  Main loop            : 0.49
% 3.36/1.57  Inferencing          : 0.18
% 3.36/1.57  Reduction            : 0.15
% 3.36/1.57  Demodulation         : 0.11
% 3.36/1.57  BG Simplification    : 0.02
% 3.36/1.57  Subsumption          : 0.11
% 3.36/1.57  Abstraction          : 0.03
% 3.36/1.57  MUC search           : 0.00
% 3.36/1.57  Cooper               : 0.00
% 3.36/1.57  Total                : 0.83
% 3.36/1.57  Index Insertion      : 0.00
% 3.36/1.57  Index Deletion       : 0.00
% 3.36/1.57  Index Matching       : 0.00
% 3.36/1.57  BG Taut test         : 0.00
%------------------------------------------------------------------------------
