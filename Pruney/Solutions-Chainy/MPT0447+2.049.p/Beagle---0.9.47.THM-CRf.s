%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:58:34 EST 2020

% Result     : Theorem 2.70s
% Output     : CNFRefutation 2.70s
% Verified   : 
% Statistics : Number of formulae       :   54 (  87 expanded)
%              Number of leaves         :   21 (  39 expanded)
%              Depth                    :    8
%              Number of atoms          :   98 ( 184 expanded)
%              Number of equality atoms :   15 (  27 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k4_xboole_0 > k2_xboole_0 > #nlpp > k3_relat_1 > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_relat_1,type,(
    k3_relat_1: $i > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_70,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ! [B] :
            ( v1_relat_1(B)
           => ( r1_tarski(A,B)
             => r1_tarski(k3_relat_1(A),k3_relat_1(B)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_relat_1)).

tff(f_60,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(A,B)
           => ( r1_tarski(k1_relat_1(A),k1_relat_1(B))
              & r1_tarski(k2_relat_1(A),k2_relat_1(B)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_relat_1)).

tff(f_49,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k3_relat_1(A) = k2_xboole_0(k1_relat_1(A),k2_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_relat_1)).

tff(f_33,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(A,k2_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_35,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k4_xboole_0(A,B),C)
     => r1_tarski(A,k2_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_xboole_1)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(C,B) )
     => r1_tarski(k2_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_xboole_1)).

tff(c_26,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_24,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_22,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_16,plain,(
    ! [A_14,B_16] :
      ( r1_tarski(k2_relat_1(A_14),k2_relat_1(B_16))
      | ~ r1_tarski(A_14,B_16)
      | ~ v1_relat_1(B_16)
      | ~ v1_relat_1(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_14,plain,(
    ! [A_13] :
      ( k2_xboole_0(k1_relat_1(A_13),k2_relat_1(A_13)) = k3_relat_1(A_13)
      | ~ v1_relat_1(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_50,plain,(
    ! [A_23,C_24,B_25] :
      ( r1_tarski(A_23,k2_xboole_0(C_24,B_25))
      | ~ r1_tarski(A_23,B_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( k4_xboole_0(A_1,B_2) = k1_xboole_0
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_74,plain,(
    ! [A_28,C_29,B_30] :
      ( k4_xboole_0(A_28,k2_xboole_0(C_29,B_30)) = k1_xboole_0
      | ~ r1_tarski(A_28,B_30) ) ),
    inference(resolution,[status(thm)],[c_50,c_4])).

tff(c_263,plain,(
    ! [A_60,A_61] :
      ( k4_xboole_0(A_60,k3_relat_1(A_61)) = k1_xboole_0
      | ~ r1_tarski(A_60,k2_relat_1(A_61))
      | ~ v1_relat_1(A_61) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_74])).

tff(c_279,plain,(
    ! [A_14,B_16] :
      ( k4_xboole_0(k2_relat_1(A_14),k3_relat_1(B_16)) = k1_xboole_0
      | ~ r1_tarski(A_14,B_16)
      | ~ v1_relat_1(B_16)
      | ~ v1_relat_1(A_14) ) ),
    inference(resolution,[status(thm)],[c_16,c_263])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( r1_tarski(A_1,B_2)
      | k4_xboole_0(A_1,B_2) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_8,plain,(
    ! [A_6] : r1_tarski(k1_xboole_0,A_6) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_33,plain,(
    ! [A_21,B_22] :
      ( k4_xboole_0(A_21,B_22) = k1_xboole_0
      | ~ r1_tarski(A_21,B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_45,plain,(
    ! [A_6] : k4_xboole_0(k1_xboole_0,A_6) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_8,c_33])).

tff(c_347,plain,(
    ! [A_70,B_71] :
      ( r1_tarski(k1_relat_1(A_70),k1_relat_1(B_71))
      | ~ r1_tarski(A_70,B_71)
      | ~ v1_relat_1(B_71)
      | ~ v1_relat_1(A_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_351,plain,(
    ! [A_70,B_71] :
      ( k4_xboole_0(k1_relat_1(A_70),k1_relat_1(B_71)) = k1_xboole_0
      | ~ r1_tarski(A_70,B_71)
      | ~ v1_relat_1(B_71)
      | ~ v1_relat_1(A_70) ) ),
    inference(resolution,[status(thm)],[c_347,c_4])).

tff(c_100,plain,(
    ! [A_31,B_32,C_33] :
      ( r1_tarski(A_31,k2_xboole_0(B_32,C_33))
      | ~ r1_tarski(k4_xboole_0(A_31,B_32),C_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_250,plain,(
    ! [A_57,B_58,B_59] :
      ( r1_tarski(A_57,k2_xboole_0(B_58,B_59))
      | k4_xboole_0(k4_xboole_0(A_57,B_58),B_59) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_2,c_100])).

tff(c_909,plain,(
    ! [A_117,A_118] :
      ( r1_tarski(A_117,k3_relat_1(A_118))
      | k4_xboole_0(k4_xboole_0(A_117,k1_relat_1(A_118)),k2_relat_1(A_118)) != k1_xboole_0
      | ~ v1_relat_1(A_118) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_250])).

tff(c_912,plain,(
    ! [A_70,B_71] :
      ( r1_tarski(k1_relat_1(A_70),k3_relat_1(B_71))
      | k4_xboole_0(k1_xboole_0,k2_relat_1(B_71)) != k1_xboole_0
      | ~ v1_relat_1(B_71)
      | ~ r1_tarski(A_70,B_71)
      | ~ v1_relat_1(B_71)
      | ~ v1_relat_1(A_70) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_351,c_909])).

tff(c_927,plain,(
    ! [A_119,B_120] :
      ( r1_tarski(k1_relat_1(A_119),k3_relat_1(B_120))
      | ~ r1_tarski(A_119,B_120)
      | ~ v1_relat_1(B_120)
      | ~ v1_relat_1(A_119) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_45,c_912])).

tff(c_131,plain,(
    ! [A_35,C_36,B_37] :
      ( r1_tarski(k2_xboole_0(A_35,C_36),B_37)
      | ~ r1_tarski(C_36,B_37)
      | ~ r1_tarski(A_35,B_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_769,plain,(
    ! [A_110,B_111] :
      ( r1_tarski(k3_relat_1(A_110),B_111)
      | ~ r1_tarski(k2_relat_1(A_110),B_111)
      | ~ r1_tarski(k1_relat_1(A_110),B_111)
      | ~ v1_relat_1(A_110) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_131])).

tff(c_20,plain,(
    ~ r1_tarski(k3_relat_1('#skF_1'),k3_relat_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_782,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_1'),k3_relat_1('#skF_2'))
    | ~ r1_tarski(k1_relat_1('#skF_1'),k3_relat_1('#skF_2'))
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_769,c_20])).

tff(c_790,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_1'),k3_relat_1('#skF_2'))
    | ~ r1_tarski(k1_relat_1('#skF_1'),k3_relat_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_782])).

tff(c_791,plain,(
    ~ r1_tarski(k1_relat_1('#skF_1'),k3_relat_1('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_790])).

tff(c_930,plain,
    ( ~ r1_tarski('#skF_1','#skF_2')
    | ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_927,c_791])).

tff(c_937,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_24,c_22,c_930])).

tff(c_938,plain,(
    ~ r1_tarski(k2_relat_1('#skF_1'),k3_relat_1('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_790])).

tff(c_949,plain,(
    k4_xboole_0(k2_relat_1('#skF_1'),k3_relat_1('#skF_2')) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2,c_938])).

tff(c_956,plain,
    ( ~ r1_tarski('#skF_1','#skF_2')
    | ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_279,c_949])).

tff(c_963,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_24,c_22,c_956])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n018.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 17:41:57 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.70/1.42  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.70/1.43  
% 2.70/1.43  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.70/1.43  %$ r1_tarski > v1_relat_1 > k4_xboole_0 > k2_xboole_0 > #nlpp > k3_relat_1 > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1
% 2.70/1.43  
% 2.70/1.43  %Foreground sorts:
% 2.70/1.43  
% 2.70/1.43  
% 2.70/1.43  %Background operators:
% 2.70/1.43  
% 2.70/1.43  
% 2.70/1.43  %Foreground operators:
% 2.70/1.43  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.70/1.43  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.70/1.43  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.70/1.43  tff(k3_relat_1, type, k3_relat_1: $i > $i).
% 2.70/1.43  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.70/1.43  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.70/1.43  tff('#skF_2', type, '#skF_2': $i).
% 2.70/1.43  tff('#skF_1', type, '#skF_1': $i).
% 2.70/1.43  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.70/1.43  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.70/1.43  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.70/1.43  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.70/1.43  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.70/1.43  
% 2.70/1.44  tff(f_70, negated_conjecture, ~(![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(A, B) => r1_tarski(k3_relat_1(A), k3_relat_1(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_relat_1)).
% 2.70/1.44  tff(f_60, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(A, B) => (r1_tarski(k1_relat_1(A), k1_relat_1(B)) & r1_tarski(k2_relat_1(A), k2_relat_1(B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t25_relat_1)).
% 2.70/1.44  tff(f_49, axiom, (![A]: (v1_relat_1(A) => (k3_relat_1(A) = k2_xboole_0(k1_relat_1(A), k2_relat_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d6_relat_1)).
% 2.70/1.44  tff(f_33, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(A, k2_xboole_0(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_xboole_1)).
% 2.70/1.44  tff(f_29, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 2.70/1.44  tff(f_35, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.70/1.44  tff(f_39, axiom, (![A, B, C]: (r1_tarski(k4_xboole_0(A, B), C) => r1_tarski(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_xboole_1)).
% 2.70/1.44  tff(f_45, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(C, B)) => r1_tarski(k2_xboole_0(A, C), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_xboole_1)).
% 2.70/1.44  tff(c_26, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.70/1.44  tff(c_24, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.70/1.44  tff(c_22, plain, (r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.70/1.44  tff(c_16, plain, (![A_14, B_16]: (r1_tarski(k2_relat_1(A_14), k2_relat_1(B_16)) | ~r1_tarski(A_14, B_16) | ~v1_relat_1(B_16) | ~v1_relat_1(A_14))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.70/1.44  tff(c_14, plain, (![A_13]: (k2_xboole_0(k1_relat_1(A_13), k2_relat_1(A_13))=k3_relat_1(A_13) | ~v1_relat_1(A_13))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.70/1.44  tff(c_50, plain, (![A_23, C_24, B_25]: (r1_tarski(A_23, k2_xboole_0(C_24, B_25)) | ~r1_tarski(A_23, B_25))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.70/1.44  tff(c_4, plain, (![A_1, B_2]: (k4_xboole_0(A_1, B_2)=k1_xboole_0 | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.70/1.44  tff(c_74, plain, (![A_28, C_29, B_30]: (k4_xboole_0(A_28, k2_xboole_0(C_29, B_30))=k1_xboole_0 | ~r1_tarski(A_28, B_30))), inference(resolution, [status(thm)], [c_50, c_4])).
% 2.70/1.44  tff(c_263, plain, (![A_60, A_61]: (k4_xboole_0(A_60, k3_relat_1(A_61))=k1_xboole_0 | ~r1_tarski(A_60, k2_relat_1(A_61)) | ~v1_relat_1(A_61))), inference(superposition, [status(thm), theory('equality')], [c_14, c_74])).
% 2.70/1.44  tff(c_279, plain, (![A_14, B_16]: (k4_xboole_0(k2_relat_1(A_14), k3_relat_1(B_16))=k1_xboole_0 | ~r1_tarski(A_14, B_16) | ~v1_relat_1(B_16) | ~v1_relat_1(A_14))), inference(resolution, [status(thm)], [c_16, c_263])).
% 2.70/1.44  tff(c_2, plain, (![A_1, B_2]: (r1_tarski(A_1, B_2) | k4_xboole_0(A_1, B_2)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.70/1.44  tff(c_8, plain, (![A_6]: (r1_tarski(k1_xboole_0, A_6))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.70/1.44  tff(c_33, plain, (![A_21, B_22]: (k4_xboole_0(A_21, B_22)=k1_xboole_0 | ~r1_tarski(A_21, B_22))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.70/1.44  tff(c_45, plain, (![A_6]: (k4_xboole_0(k1_xboole_0, A_6)=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_33])).
% 2.70/1.44  tff(c_347, plain, (![A_70, B_71]: (r1_tarski(k1_relat_1(A_70), k1_relat_1(B_71)) | ~r1_tarski(A_70, B_71) | ~v1_relat_1(B_71) | ~v1_relat_1(A_70))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.70/1.44  tff(c_351, plain, (![A_70, B_71]: (k4_xboole_0(k1_relat_1(A_70), k1_relat_1(B_71))=k1_xboole_0 | ~r1_tarski(A_70, B_71) | ~v1_relat_1(B_71) | ~v1_relat_1(A_70))), inference(resolution, [status(thm)], [c_347, c_4])).
% 2.70/1.44  tff(c_100, plain, (![A_31, B_32, C_33]: (r1_tarski(A_31, k2_xboole_0(B_32, C_33)) | ~r1_tarski(k4_xboole_0(A_31, B_32), C_33))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.70/1.44  tff(c_250, plain, (![A_57, B_58, B_59]: (r1_tarski(A_57, k2_xboole_0(B_58, B_59)) | k4_xboole_0(k4_xboole_0(A_57, B_58), B_59)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_100])).
% 2.70/1.44  tff(c_909, plain, (![A_117, A_118]: (r1_tarski(A_117, k3_relat_1(A_118)) | k4_xboole_0(k4_xboole_0(A_117, k1_relat_1(A_118)), k2_relat_1(A_118))!=k1_xboole_0 | ~v1_relat_1(A_118))), inference(superposition, [status(thm), theory('equality')], [c_14, c_250])).
% 2.70/1.44  tff(c_912, plain, (![A_70, B_71]: (r1_tarski(k1_relat_1(A_70), k3_relat_1(B_71)) | k4_xboole_0(k1_xboole_0, k2_relat_1(B_71))!=k1_xboole_0 | ~v1_relat_1(B_71) | ~r1_tarski(A_70, B_71) | ~v1_relat_1(B_71) | ~v1_relat_1(A_70))), inference(superposition, [status(thm), theory('equality')], [c_351, c_909])).
% 2.70/1.44  tff(c_927, plain, (![A_119, B_120]: (r1_tarski(k1_relat_1(A_119), k3_relat_1(B_120)) | ~r1_tarski(A_119, B_120) | ~v1_relat_1(B_120) | ~v1_relat_1(A_119))), inference(demodulation, [status(thm), theory('equality')], [c_45, c_912])).
% 2.70/1.44  tff(c_131, plain, (![A_35, C_36, B_37]: (r1_tarski(k2_xboole_0(A_35, C_36), B_37) | ~r1_tarski(C_36, B_37) | ~r1_tarski(A_35, B_37))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.70/1.44  tff(c_769, plain, (![A_110, B_111]: (r1_tarski(k3_relat_1(A_110), B_111) | ~r1_tarski(k2_relat_1(A_110), B_111) | ~r1_tarski(k1_relat_1(A_110), B_111) | ~v1_relat_1(A_110))), inference(superposition, [status(thm), theory('equality')], [c_14, c_131])).
% 2.70/1.44  tff(c_20, plain, (~r1_tarski(k3_relat_1('#skF_1'), k3_relat_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.70/1.44  tff(c_782, plain, (~r1_tarski(k2_relat_1('#skF_1'), k3_relat_1('#skF_2')) | ~r1_tarski(k1_relat_1('#skF_1'), k3_relat_1('#skF_2')) | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_769, c_20])).
% 2.70/1.44  tff(c_790, plain, (~r1_tarski(k2_relat_1('#skF_1'), k3_relat_1('#skF_2')) | ~r1_tarski(k1_relat_1('#skF_1'), k3_relat_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_782])).
% 2.70/1.44  tff(c_791, plain, (~r1_tarski(k1_relat_1('#skF_1'), k3_relat_1('#skF_2'))), inference(splitLeft, [status(thm)], [c_790])).
% 2.70/1.44  tff(c_930, plain, (~r1_tarski('#skF_1', '#skF_2') | ~v1_relat_1('#skF_2') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_927, c_791])).
% 2.70/1.44  tff(c_937, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_26, c_24, c_22, c_930])).
% 2.70/1.44  tff(c_938, plain, (~r1_tarski(k2_relat_1('#skF_1'), k3_relat_1('#skF_2'))), inference(splitRight, [status(thm)], [c_790])).
% 2.70/1.44  tff(c_949, plain, (k4_xboole_0(k2_relat_1('#skF_1'), k3_relat_1('#skF_2'))!=k1_xboole_0), inference(resolution, [status(thm)], [c_2, c_938])).
% 2.70/1.44  tff(c_956, plain, (~r1_tarski('#skF_1', '#skF_2') | ~v1_relat_1('#skF_2') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_279, c_949])).
% 2.70/1.44  tff(c_963, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_26, c_24, c_22, c_956])).
% 2.70/1.44  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.70/1.44  
% 2.70/1.44  Inference rules
% 2.70/1.44  ----------------------
% 2.70/1.44  #Ref     : 0
% 2.70/1.44  #Sup     : 192
% 2.70/1.44  #Fact    : 0
% 2.70/1.44  #Define  : 0
% 2.70/1.44  #Split   : 1
% 2.70/1.44  #Chain   : 0
% 2.70/1.44  #Close   : 0
% 2.70/1.44  
% 2.70/1.44  Ordering : KBO
% 2.70/1.44  
% 2.70/1.44  Simplification rules
% 2.70/1.44  ----------------------
% 2.70/1.44  #Subsume      : 6
% 2.70/1.44  #Demod        : 82
% 2.70/1.44  #Tautology    : 101
% 2.70/1.44  #SimpNegUnit  : 0
% 2.70/1.44  #BackRed      : 0
% 2.70/1.44  
% 2.70/1.44  #Partial instantiations: 0
% 2.70/1.44  #Strategies tried      : 1
% 2.70/1.44  
% 2.70/1.44  Timing (in seconds)
% 2.70/1.44  ----------------------
% 2.70/1.45  Preprocessing        : 0.28
% 2.70/1.45  Parsing              : 0.16
% 2.70/1.45  CNF conversion       : 0.02
% 2.70/1.45  Main loop            : 0.40
% 2.70/1.45  Inferencing          : 0.17
% 2.70/1.45  Reduction            : 0.11
% 2.70/1.45  Demodulation         : 0.08
% 2.70/1.45  BG Simplification    : 0.02
% 2.70/1.45  Subsumption          : 0.08
% 2.70/1.45  Abstraction          : 0.01
% 2.70/1.45  MUC search           : 0.00
% 2.70/1.45  Cooper               : 0.00
% 2.70/1.45  Total                : 0.71
% 2.70/1.45  Index Insertion      : 0.00
% 2.70/1.45  Index Deletion       : 0.00
% 2.70/1.45  Index Matching       : 0.00
% 2.70/1.45  BG Taut test         : 0.00
%------------------------------------------------------------------------------
