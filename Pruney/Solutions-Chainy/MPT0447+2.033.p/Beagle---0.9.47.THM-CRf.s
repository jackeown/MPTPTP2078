%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:58:32 EST 2020

% Result     : Theorem 2.00s
% Output     : CNFRefutation 2.00s
% Verified   : 
% Statistics : Number of formulae       :   53 (  85 expanded)
%              Number of leaves         :   21 (  39 expanded)
%              Depth                    :    9
%              Number of atoms          :   79 ( 164 expanded)
%              Number of equality atoms :   10 (  16 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   2 average)

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

tff(f_66,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ! [B] :
            ( v1_relat_1(B)
           => ( r1_tarski(A,B)
             => r1_tarski(k3_relat_1(A),k3_relat_1(B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_relat_1)).

tff(f_56,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(A,B)
           => ( r1_tarski(k1_relat_1(A),k1_relat_1(B))
              & r1_tarski(k2_relat_1(A),k2_relat_1(B)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_relat_1)).

tff(f_45,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k3_relat_1(A) = k2_xboole_0(k1_relat_1(A),k2_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_relat_1)).

tff(f_29,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(A,k2_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_41,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(C,B) )
     => r1_tarski(k2_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_xboole_1)).

tff(c_24,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_22,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_20,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_14,plain,(
    ! [A_14,B_16] :
      ( r1_tarski(k2_relat_1(A_14),k2_relat_1(B_16))
      | ~ r1_tarski(A_14,B_16)
      | ~ v1_relat_1(B_16)
      | ~ v1_relat_1(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_153,plain,(
    ! [A_34] :
      ( k2_xboole_0(k1_relat_1(A_34),k2_relat_1(A_34)) = k3_relat_1(A_34)
      | ~ v1_relat_1(A_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_2,plain,(
    ! [A_1,C_3,B_2] :
      ( r1_tarski(A_1,k2_xboole_0(C_3,B_2))
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_162,plain,(
    ! [A_1,A_34] :
      ( r1_tarski(A_1,k3_relat_1(A_34))
      | ~ r1_tarski(A_1,k2_relat_1(A_34))
      | ~ v1_relat_1(A_34) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_153,c_2])).

tff(c_16,plain,(
    ! [A_14,B_16] :
      ( r1_tarski(k1_relat_1(A_14),k1_relat_1(B_16))
      | ~ r1_tarski(A_14,B_16)
      | ~ v1_relat_1(B_16)
      | ~ v1_relat_1(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_6,plain,(
    ! [B_8,A_7] : k2_tarski(B_8,A_7) = k2_tarski(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_67,plain,(
    ! [A_22,B_23] : k3_tarski(k2_tarski(A_22,B_23)) = k2_xboole_0(A_22,B_23) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_82,plain,(
    ! [B_24,A_25] : k3_tarski(k2_tarski(B_24,A_25)) = k2_xboole_0(A_25,B_24) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_67])).

tff(c_10,plain,(
    ! [A_11,B_12] : k3_tarski(k2_tarski(A_11,B_12)) = k2_xboole_0(A_11,B_12) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_88,plain,(
    ! [B_24,A_25] : k2_xboole_0(B_24,A_25) = k2_xboole_0(A_25,B_24) ),
    inference(superposition,[status(thm),theory(equality)],[c_82,c_10])).

tff(c_138,plain,(
    ! [A_28,C_29,B_30] :
      ( r1_tarski(A_28,k2_xboole_0(C_29,B_30))
      | ~ r1_tarski(A_28,B_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_144,plain,(
    ! [A_28,A_25,B_24] :
      ( r1_tarski(A_28,k2_xboole_0(A_25,B_24))
      | ~ r1_tarski(A_28,A_25) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_88,c_138])).

tff(c_159,plain,(
    ! [A_28,A_34] :
      ( r1_tarski(A_28,k3_relat_1(A_34))
      | ~ r1_tarski(A_28,k1_relat_1(A_34))
      | ~ v1_relat_1(A_34) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_153,c_144])).

tff(c_12,plain,(
    ! [A_13] :
      ( k2_xboole_0(k1_relat_1(A_13),k2_relat_1(A_13)) = k3_relat_1(A_13)
      | ~ v1_relat_1(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_168,plain,(
    ! [A_35,C_36,B_37] :
      ( r1_tarski(k2_xboole_0(A_35,C_36),B_37)
      | ~ r1_tarski(C_36,B_37)
      | ~ r1_tarski(A_35,B_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_194,plain,(
    ! [A_46,B_47] :
      ( r1_tarski(k3_relat_1(A_46),B_47)
      | ~ r1_tarski(k2_relat_1(A_46),B_47)
      | ~ r1_tarski(k1_relat_1(A_46),B_47)
      | ~ v1_relat_1(A_46) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_168])).

tff(c_18,plain,(
    ~ r1_tarski(k3_relat_1('#skF_1'),k3_relat_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_203,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_1'),k3_relat_1('#skF_2'))
    | ~ r1_tarski(k1_relat_1('#skF_1'),k3_relat_1('#skF_2'))
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_194,c_18])).

tff(c_212,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_1'),k3_relat_1('#skF_2'))
    | ~ r1_tarski(k1_relat_1('#skF_1'),k3_relat_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_203])).

tff(c_213,plain,(
    ~ r1_tarski(k1_relat_1('#skF_1'),k3_relat_1('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_212])).

tff(c_216,plain,
    ( ~ r1_tarski(k1_relat_1('#skF_1'),k1_relat_1('#skF_2'))
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_159,c_213])).

tff(c_222,plain,(
    ~ r1_tarski(k1_relat_1('#skF_1'),k1_relat_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_216])).

tff(c_228,plain,
    ( ~ r1_tarski('#skF_1','#skF_2')
    | ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_16,c_222])).

tff(c_232,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_22,c_20,c_228])).

tff(c_233,plain,(
    ~ r1_tarski(k2_relat_1('#skF_1'),k3_relat_1('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_212])).

tff(c_240,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_1'),k2_relat_1('#skF_2'))
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_162,c_233])).

tff(c_246,plain,(
    ~ r1_tarski(k2_relat_1('#skF_1'),k2_relat_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_240])).

tff(c_250,plain,
    ( ~ r1_tarski('#skF_1','#skF_2')
    | ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_14,c_246])).

tff(c_254,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_22,c_20,c_250])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:24:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.00/1.28  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.00/1.29  
% 2.00/1.29  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.00/1.29  %$ r1_tarski > v1_relat_1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k3_relat_1 > k2_relat_1 > k1_relat_1 > #skF_2 > #skF_1
% 2.00/1.29  
% 2.00/1.29  %Foreground sorts:
% 2.00/1.29  
% 2.00/1.29  
% 2.00/1.29  %Background operators:
% 2.00/1.29  
% 2.00/1.29  
% 2.00/1.29  %Foreground operators:
% 2.00/1.29  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.00/1.29  tff(k3_relat_1, type, k3_relat_1: $i > $i).
% 2.00/1.29  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.00/1.29  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.00/1.29  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.00/1.29  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.00/1.29  tff('#skF_2', type, '#skF_2': $i).
% 2.00/1.29  tff('#skF_1', type, '#skF_1': $i).
% 2.00/1.29  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.00/1.29  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.00/1.29  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.00/1.29  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.00/1.29  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.00/1.29  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.00/1.29  
% 2.00/1.30  tff(f_66, negated_conjecture, ~(![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(A, B) => r1_tarski(k3_relat_1(A), k3_relat_1(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_relat_1)).
% 2.00/1.30  tff(f_56, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(A, B) => (r1_tarski(k1_relat_1(A), k1_relat_1(B)) & r1_tarski(k2_relat_1(A), k2_relat_1(B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t25_relat_1)).
% 2.00/1.30  tff(f_45, axiom, (![A]: (v1_relat_1(A) => (k3_relat_1(A) = k2_xboole_0(k1_relat_1(A), k2_relat_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d6_relat_1)).
% 2.00/1.30  tff(f_29, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(A, k2_xboole_0(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_xboole_1)).
% 2.00/1.30  tff(f_37, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 2.00/1.30  tff(f_41, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 2.00/1.30  tff(f_35, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(C, B)) => r1_tarski(k2_xboole_0(A, C), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_xboole_1)).
% 2.00/1.30  tff(c_24, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.00/1.30  tff(c_22, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.00/1.30  tff(c_20, plain, (r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.00/1.30  tff(c_14, plain, (![A_14, B_16]: (r1_tarski(k2_relat_1(A_14), k2_relat_1(B_16)) | ~r1_tarski(A_14, B_16) | ~v1_relat_1(B_16) | ~v1_relat_1(A_14))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.00/1.30  tff(c_153, plain, (![A_34]: (k2_xboole_0(k1_relat_1(A_34), k2_relat_1(A_34))=k3_relat_1(A_34) | ~v1_relat_1(A_34))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.00/1.30  tff(c_2, plain, (![A_1, C_3, B_2]: (r1_tarski(A_1, k2_xboole_0(C_3, B_2)) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.00/1.30  tff(c_162, plain, (![A_1, A_34]: (r1_tarski(A_1, k3_relat_1(A_34)) | ~r1_tarski(A_1, k2_relat_1(A_34)) | ~v1_relat_1(A_34))), inference(superposition, [status(thm), theory('equality')], [c_153, c_2])).
% 2.00/1.30  tff(c_16, plain, (![A_14, B_16]: (r1_tarski(k1_relat_1(A_14), k1_relat_1(B_16)) | ~r1_tarski(A_14, B_16) | ~v1_relat_1(B_16) | ~v1_relat_1(A_14))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.00/1.30  tff(c_6, plain, (![B_8, A_7]: (k2_tarski(B_8, A_7)=k2_tarski(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.00/1.30  tff(c_67, plain, (![A_22, B_23]: (k3_tarski(k2_tarski(A_22, B_23))=k2_xboole_0(A_22, B_23))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.00/1.30  tff(c_82, plain, (![B_24, A_25]: (k3_tarski(k2_tarski(B_24, A_25))=k2_xboole_0(A_25, B_24))), inference(superposition, [status(thm), theory('equality')], [c_6, c_67])).
% 2.00/1.30  tff(c_10, plain, (![A_11, B_12]: (k3_tarski(k2_tarski(A_11, B_12))=k2_xboole_0(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.00/1.30  tff(c_88, plain, (![B_24, A_25]: (k2_xboole_0(B_24, A_25)=k2_xboole_0(A_25, B_24))), inference(superposition, [status(thm), theory('equality')], [c_82, c_10])).
% 2.00/1.30  tff(c_138, plain, (![A_28, C_29, B_30]: (r1_tarski(A_28, k2_xboole_0(C_29, B_30)) | ~r1_tarski(A_28, B_30))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.00/1.30  tff(c_144, plain, (![A_28, A_25, B_24]: (r1_tarski(A_28, k2_xboole_0(A_25, B_24)) | ~r1_tarski(A_28, A_25))), inference(superposition, [status(thm), theory('equality')], [c_88, c_138])).
% 2.00/1.30  tff(c_159, plain, (![A_28, A_34]: (r1_tarski(A_28, k3_relat_1(A_34)) | ~r1_tarski(A_28, k1_relat_1(A_34)) | ~v1_relat_1(A_34))), inference(superposition, [status(thm), theory('equality')], [c_153, c_144])).
% 2.00/1.30  tff(c_12, plain, (![A_13]: (k2_xboole_0(k1_relat_1(A_13), k2_relat_1(A_13))=k3_relat_1(A_13) | ~v1_relat_1(A_13))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.00/1.30  tff(c_168, plain, (![A_35, C_36, B_37]: (r1_tarski(k2_xboole_0(A_35, C_36), B_37) | ~r1_tarski(C_36, B_37) | ~r1_tarski(A_35, B_37))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.00/1.30  tff(c_194, plain, (![A_46, B_47]: (r1_tarski(k3_relat_1(A_46), B_47) | ~r1_tarski(k2_relat_1(A_46), B_47) | ~r1_tarski(k1_relat_1(A_46), B_47) | ~v1_relat_1(A_46))), inference(superposition, [status(thm), theory('equality')], [c_12, c_168])).
% 2.00/1.30  tff(c_18, plain, (~r1_tarski(k3_relat_1('#skF_1'), k3_relat_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.00/1.30  tff(c_203, plain, (~r1_tarski(k2_relat_1('#skF_1'), k3_relat_1('#skF_2')) | ~r1_tarski(k1_relat_1('#skF_1'), k3_relat_1('#skF_2')) | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_194, c_18])).
% 2.00/1.30  tff(c_212, plain, (~r1_tarski(k2_relat_1('#skF_1'), k3_relat_1('#skF_2')) | ~r1_tarski(k1_relat_1('#skF_1'), k3_relat_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_203])).
% 2.00/1.30  tff(c_213, plain, (~r1_tarski(k1_relat_1('#skF_1'), k3_relat_1('#skF_2'))), inference(splitLeft, [status(thm)], [c_212])).
% 2.00/1.30  tff(c_216, plain, (~r1_tarski(k1_relat_1('#skF_1'), k1_relat_1('#skF_2')) | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_159, c_213])).
% 2.00/1.30  tff(c_222, plain, (~r1_tarski(k1_relat_1('#skF_1'), k1_relat_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_216])).
% 2.00/1.30  tff(c_228, plain, (~r1_tarski('#skF_1', '#skF_2') | ~v1_relat_1('#skF_2') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_16, c_222])).
% 2.00/1.30  tff(c_232, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_24, c_22, c_20, c_228])).
% 2.00/1.30  tff(c_233, plain, (~r1_tarski(k2_relat_1('#skF_1'), k3_relat_1('#skF_2'))), inference(splitRight, [status(thm)], [c_212])).
% 2.00/1.30  tff(c_240, plain, (~r1_tarski(k2_relat_1('#skF_1'), k2_relat_1('#skF_2')) | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_162, c_233])).
% 2.00/1.30  tff(c_246, plain, (~r1_tarski(k2_relat_1('#skF_1'), k2_relat_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_240])).
% 2.00/1.30  tff(c_250, plain, (~r1_tarski('#skF_1', '#skF_2') | ~v1_relat_1('#skF_2') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_14, c_246])).
% 2.00/1.30  tff(c_254, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_24, c_22, c_20, c_250])).
% 2.00/1.30  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.00/1.30  
% 2.00/1.30  Inference rules
% 2.00/1.30  ----------------------
% 2.00/1.30  #Ref     : 0
% 2.00/1.30  #Sup     : 50
% 2.00/1.30  #Fact    : 0
% 2.00/1.30  #Define  : 0
% 2.00/1.30  #Split   : 2
% 2.00/1.30  #Chain   : 0
% 2.00/1.30  #Close   : 0
% 2.00/1.30  
% 2.00/1.30  Ordering : KBO
% 2.00/1.30  
% 2.00/1.30  Simplification rules
% 2.00/1.30  ----------------------
% 2.00/1.30  #Subsume      : 6
% 2.00/1.30  #Demod        : 18
% 2.00/1.30  #Tautology    : 27
% 2.00/1.30  #SimpNegUnit  : 0
% 2.00/1.30  #BackRed      : 0
% 2.00/1.30  
% 2.00/1.30  #Partial instantiations: 0
% 2.00/1.30  #Strategies tried      : 1
% 2.00/1.30  
% 2.00/1.30  Timing (in seconds)
% 2.00/1.30  ----------------------
% 2.00/1.30  Preprocessing        : 0.29
% 2.00/1.30  Parsing              : 0.16
% 2.00/1.30  CNF conversion       : 0.02
% 2.00/1.30  Main loop            : 0.17
% 2.00/1.30  Inferencing          : 0.07
% 2.00/1.30  Reduction            : 0.05
% 2.00/1.30  Demodulation         : 0.04
% 2.00/1.30  BG Simplification    : 0.01
% 2.00/1.30  Subsumption          : 0.03
% 2.00/1.30  Abstraction          : 0.01
% 2.00/1.30  MUC search           : 0.00
% 2.00/1.30  Cooper               : 0.00
% 2.00/1.30  Total                : 0.49
% 2.00/1.30  Index Insertion      : 0.00
% 2.00/1.30  Index Deletion       : 0.00
% 2.00/1.30  Index Matching       : 0.00
% 2.00/1.30  BG Taut test         : 0.00
%------------------------------------------------------------------------------
