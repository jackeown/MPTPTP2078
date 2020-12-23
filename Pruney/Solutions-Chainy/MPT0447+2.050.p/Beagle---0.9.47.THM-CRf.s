%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:58:34 EST 2020

% Result     : Theorem 7.82s
% Output     : CNFRefutation 7.88s
% Verified   : 
% Statistics : Number of formulae       :   48 (  76 expanded)
%              Number of leaves         :   19 (  34 expanded)
%              Depth                    :    9
%              Number of atoms          :   87 ( 164 expanded)
%              Number of equality atoms :    6 (  11 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k2_xboole_0 > #nlpp > k3_relat_1 > k2_relat_1 > k1_relat_1 > #skF_2 > #skF_1

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

tff(f_29,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(A,k2_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_33,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_xboole_0(A,B),C)
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(C,B) )
     => r1_tarski(k2_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_xboole_1)).

tff(c_24,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_22,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_20,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_14,plain,(
    ! [A_15,B_17] :
      ( r1_tarski(k2_relat_1(A_15),k2_relat_1(B_17))
      | ~ r1_tarski(A_15,B_17)
      | ~ v1_relat_1(B_17)
      | ~ v1_relat_1(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_172,plain,(
    ! [A_40] :
      ( k2_xboole_0(k1_relat_1(A_40),k2_relat_1(A_40)) = k3_relat_1(A_40)
      | ~ v1_relat_1(A_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_2,plain,(
    ! [A_1,C_3,B_2] :
      ( r1_tarski(A_1,k2_xboole_0(C_3,B_2))
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_190,plain,(
    ! [A_1,A_40] :
      ( r1_tarski(A_1,k3_relat_1(A_40))
      | ~ r1_tarski(A_1,k2_relat_1(A_40))
      | ~ v1_relat_1(A_40) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_172,c_2])).

tff(c_8,plain,(
    ! [A_9,B_10] : r1_tarski(A_9,k2_xboole_0(A_9,B_10)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_193,plain,(
    ! [A_40] :
      ( r1_tarski(k1_relat_1(A_40),k3_relat_1(A_40))
      | ~ v1_relat_1(A_40) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_172,c_8])).

tff(c_961,plain,(
    ! [A_94,B_95] :
      ( r1_tarski(k1_relat_1(A_94),k1_relat_1(B_95))
      | ~ r1_tarski(A_94,B_95)
      | ~ v1_relat_1(B_95)
      | ~ v1_relat_1(A_94) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_6,plain,(
    ! [A_7,B_8] :
      ( k2_xboole_0(A_7,B_8) = B_8
      | ~ r1_tarski(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_2523,plain,(
    ! [A_149,B_150] :
      ( k2_xboole_0(k1_relat_1(A_149),k1_relat_1(B_150)) = k1_relat_1(B_150)
      | ~ r1_tarski(A_149,B_150)
      | ~ v1_relat_1(B_150)
      | ~ v1_relat_1(A_149) ) ),
    inference(resolution,[status(thm)],[c_961,c_6])).

tff(c_4,plain,(
    ! [A_4,C_6,B_5] :
      ( r1_tarski(A_4,C_6)
      | ~ r1_tarski(k2_xboole_0(A_4,B_5),C_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_10003,plain,(
    ! [A_387,C_388,B_389] :
      ( r1_tarski(k1_relat_1(A_387),C_388)
      | ~ r1_tarski(k1_relat_1(B_389),C_388)
      | ~ r1_tarski(A_387,B_389)
      | ~ v1_relat_1(B_389)
      | ~ v1_relat_1(A_387) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2523,c_4])).

tff(c_10120,plain,(
    ! [A_390,A_391] :
      ( r1_tarski(k1_relat_1(A_390),k3_relat_1(A_391))
      | ~ r1_tarski(A_390,A_391)
      | ~ v1_relat_1(A_390)
      | ~ v1_relat_1(A_391) ) ),
    inference(resolution,[status(thm)],[c_193,c_10003])).

tff(c_12,plain,(
    ! [A_14] :
      ( k2_xboole_0(k1_relat_1(A_14),k2_relat_1(A_14)) = k3_relat_1(A_14)
      | ~ v1_relat_1(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_367,plain,(
    ! [A_56,C_57,B_58] :
      ( r1_tarski(k2_xboole_0(A_56,C_57),B_58)
      | ~ r1_tarski(C_57,B_58)
      | ~ r1_tarski(A_56,B_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_3020,plain,(
    ! [A_168,B_169] :
      ( r1_tarski(k3_relat_1(A_168),B_169)
      | ~ r1_tarski(k2_relat_1(A_168),B_169)
      | ~ r1_tarski(k1_relat_1(A_168),B_169)
      | ~ v1_relat_1(A_168) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_367])).

tff(c_18,plain,(
    ~ r1_tarski(k3_relat_1('#skF_1'),k3_relat_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_3036,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_1'),k3_relat_1('#skF_2'))
    | ~ r1_tarski(k1_relat_1('#skF_1'),k3_relat_1('#skF_2'))
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_3020,c_18])).

tff(c_3046,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_1'),k3_relat_1('#skF_2'))
    | ~ r1_tarski(k1_relat_1('#skF_1'),k3_relat_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_3036])).

tff(c_3047,plain,(
    ~ r1_tarski(k1_relat_1('#skF_1'),k3_relat_1('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_3046])).

tff(c_10131,plain,
    ( ~ r1_tarski('#skF_1','#skF_2')
    | ~ v1_relat_1('#skF_1')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_10120,c_3047])).

tff(c_10146,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_24,c_20,c_10131])).

tff(c_10147,plain,(
    ~ r1_tarski(k2_relat_1('#skF_1'),k3_relat_1('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_3046])).

tff(c_10151,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_1'),k2_relat_1('#skF_2'))
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_190,c_10147])).

tff(c_10154,plain,(
    ~ r1_tarski(k2_relat_1('#skF_1'),k2_relat_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_10151])).

tff(c_10276,plain,
    ( ~ r1_tarski('#skF_1','#skF_2')
    | ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_14,c_10154])).

tff(c_10280,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_22,c_20,c_10276])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.02/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.02/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:51:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.82/2.66  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.82/2.67  
% 7.82/2.67  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.82/2.67  %$ r1_tarski > v1_relat_1 > k2_xboole_0 > #nlpp > k3_relat_1 > k2_relat_1 > k1_relat_1 > #skF_2 > #skF_1
% 7.82/2.67  
% 7.82/2.67  %Foreground sorts:
% 7.82/2.67  
% 7.82/2.67  
% 7.82/2.67  %Background operators:
% 7.82/2.67  
% 7.82/2.67  
% 7.82/2.67  %Foreground operators:
% 7.82/2.67  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.82/2.67  tff(k3_relat_1, type, k3_relat_1: $i > $i).
% 7.82/2.67  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.82/2.67  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 7.82/2.67  tff('#skF_2', type, '#skF_2': $i).
% 7.82/2.67  tff('#skF_1', type, '#skF_1': $i).
% 7.82/2.67  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.82/2.67  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 7.82/2.67  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.82/2.67  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 7.82/2.67  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 7.82/2.67  
% 7.88/2.68  tff(f_70, negated_conjecture, ~(![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(A, B) => r1_tarski(k3_relat_1(A), k3_relat_1(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_relat_1)).
% 7.88/2.68  tff(f_60, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(A, B) => (r1_tarski(k1_relat_1(A), k1_relat_1(B)) & r1_tarski(k2_relat_1(A), k2_relat_1(B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t25_relat_1)).
% 7.88/2.68  tff(f_49, axiom, (![A]: (v1_relat_1(A) => (k3_relat_1(A) = k2_xboole_0(k1_relat_1(A), k2_relat_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d6_relat_1)).
% 7.88/2.68  tff(f_29, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(A, k2_xboole_0(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_xboole_1)).
% 7.88/2.68  tff(f_39, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 7.88/2.68  tff(f_37, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 7.88/2.68  tff(f_33, axiom, (![A, B, C]: (r1_tarski(k2_xboole_0(A, B), C) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_xboole_1)).
% 7.88/2.68  tff(f_45, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(C, B)) => r1_tarski(k2_xboole_0(A, C), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_xboole_1)).
% 7.88/2.68  tff(c_24, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_70])).
% 7.88/2.68  tff(c_22, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_70])).
% 7.88/2.68  tff(c_20, plain, (r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_70])).
% 7.88/2.68  tff(c_14, plain, (![A_15, B_17]: (r1_tarski(k2_relat_1(A_15), k2_relat_1(B_17)) | ~r1_tarski(A_15, B_17) | ~v1_relat_1(B_17) | ~v1_relat_1(A_15))), inference(cnfTransformation, [status(thm)], [f_60])).
% 7.88/2.68  tff(c_172, plain, (![A_40]: (k2_xboole_0(k1_relat_1(A_40), k2_relat_1(A_40))=k3_relat_1(A_40) | ~v1_relat_1(A_40))), inference(cnfTransformation, [status(thm)], [f_49])).
% 7.88/2.68  tff(c_2, plain, (![A_1, C_3, B_2]: (r1_tarski(A_1, k2_xboole_0(C_3, B_2)) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 7.88/2.68  tff(c_190, plain, (![A_1, A_40]: (r1_tarski(A_1, k3_relat_1(A_40)) | ~r1_tarski(A_1, k2_relat_1(A_40)) | ~v1_relat_1(A_40))), inference(superposition, [status(thm), theory('equality')], [c_172, c_2])).
% 7.88/2.68  tff(c_8, plain, (![A_9, B_10]: (r1_tarski(A_9, k2_xboole_0(A_9, B_10)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 7.88/2.68  tff(c_193, plain, (![A_40]: (r1_tarski(k1_relat_1(A_40), k3_relat_1(A_40)) | ~v1_relat_1(A_40))), inference(superposition, [status(thm), theory('equality')], [c_172, c_8])).
% 7.88/2.68  tff(c_961, plain, (![A_94, B_95]: (r1_tarski(k1_relat_1(A_94), k1_relat_1(B_95)) | ~r1_tarski(A_94, B_95) | ~v1_relat_1(B_95) | ~v1_relat_1(A_94))), inference(cnfTransformation, [status(thm)], [f_60])).
% 7.88/2.68  tff(c_6, plain, (![A_7, B_8]: (k2_xboole_0(A_7, B_8)=B_8 | ~r1_tarski(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_37])).
% 7.88/2.68  tff(c_2523, plain, (![A_149, B_150]: (k2_xboole_0(k1_relat_1(A_149), k1_relat_1(B_150))=k1_relat_1(B_150) | ~r1_tarski(A_149, B_150) | ~v1_relat_1(B_150) | ~v1_relat_1(A_149))), inference(resolution, [status(thm)], [c_961, c_6])).
% 7.88/2.68  tff(c_4, plain, (![A_4, C_6, B_5]: (r1_tarski(A_4, C_6) | ~r1_tarski(k2_xboole_0(A_4, B_5), C_6))), inference(cnfTransformation, [status(thm)], [f_33])).
% 7.88/2.68  tff(c_10003, plain, (![A_387, C_388, B_389]: (r1_tarski(k1_relat_1(A_387), C_388) | ~r1_tarski(k1_relat_1(B_389), C_388) | ~r1_tarski(A_387, B_389) | ~v1_relat_1(B_389) | ~v1_relat_1(A_387))), inference(superposition, [status(thm), theory('equality')], [c_2523, c_4])).
% 7.88/2.68  tff(c_10120, plain, (![A_390, A_391]: (r1_tarski(k1_relat_1(A_390), k3_relat_1(A_391)) | ~r1_tarski(A_390, A_391) | ~v1_relat_1(A_390) | ~v1_relat_1(A_391))), inference(resolution, [status(thm)], [c_193, c_10003])).
% 7.88/2.68  tff(c_12, plain, (![A_14]: (k2_xboole_0(k1_relat_1(A_14), k2_relat_1(A_14))=k3_relat_1(A_14) | ~v1_relat_1(A_14))), inference(cnfTransformation, [status(thm)], [f_49])).
% 7.88/2.68  tff(c_367, plain, (![A_56, C_57, B_58]: (r1_tarski(k2_xboole_0(A_56, C_57), B_58) | ~r1_tarski(C_57, B_58) | ~r1_tarski(A_56, B_58))), inference(cnfTransformation, [status(thm)], [f_45])).
% 7.88/2.68  tff(c_3020, plain, (![A_168, B_169]: (r1_tarski(k3_relat_1(A_168), B_169) | ~r1_tarski(k2_relat_1(A_168), B_169) | ~r1_tarski(k1_relat_1(A_168), B_169) | ~v1_relat_1(A_168))), inference(superposition, [status(thm), theory('equality')], [c_12, c_367])).
% 7.88/2.68  tff(c_18, plain, (~r1_tarski(k3_relat_1('#skF_1'), k3_relat_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_70])).
% 7.88/2.68  tff(c_3036, plain, (~r1_tarski(k2_relat_1('#skF_1'), k3_relat_1('#skF_2')) | ~r1_tarski(k1_relat_1('#skF_1'), k3_relat_1('#skF_2')) | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_3020, c_18])).
% 7.88/2.68  tff(c_3046, plain, (~r1_tarski(k2_relat_1('#skF_1'), k3_relat_1('#skF_2')) | ~r1_tarski(k1_relat_1('#skF_1'), k3_relat_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_3036])).
% 7.88/2.68  tff(c_3047, plain, (~r1_tarski(k1_relat_1('#skF_1'), k3_relat_1('#skF_2'))), inference(splitLeft, [status(thm)], [c_3046])).
% 7.88/2.68  tff(c_10131, plain, (~r1_tarski('#skF_1', '#skF_2') | ~v1_relat_1('#skF_1') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_10120, c_3047])).
% 7.88/2.68  tff(c_10146, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_22, c_24, c_20, c_10131])).
% 7.88/2.68  tff(c_10147, plain, (~r1_tarski(k2_relat_1('#skF_1'), k3_relat_1('#skF_2'))), inference(splitRight, [status(thm)], [c_3046])).
% 7.88/2.68  tff(c_10151, plain, (~r1_tarski(k2_relat_1('#skF_1'), k2_relat_1('#skF_2')) | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_190, c_10147])).
% 7.88/2.68  tff(c_10154, plain, (~r1_tarski(k2_relat_1('#skF_1'), k2_relat_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_10151])).
% 7.88/2.68  tff(c_10276, plain, (~r1_tarski('#skF_1', '#skF_2') | ~v1_relat_1('#skF_2') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_14, c_10154])).
% 7.88/2.68  tff(c_10280, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_24, c_22, c_20, c_10276])).
% 7.88/2.68  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.88/2.68  
% 7.88/2.68  Inference rules
% 7.88/2.68  ----------------------
% 7.88/2.68  #Ref     : 0
% 7.88/2.68  #Sup     : 2645
% 7.88/2.68  #Fact    : 0
% 7.88/2.68  #Define  : 0
% 7.88/2.68  #Split   : 3
% 7.88/2.68  #Chain   : 0
% 7.88/2.68  #Close   : 0
% 7.88/2.68  
% 7.88/2.68  Ordering : KBO
% 7.88/2.68  
% 7.88/2.68  Simplification rules
% 7.88/2.68  ----------------------
% 7.88/2.68  #Subsume      : 583
% 7.88/2.68  #Demod        : 607
% 7.88/2.68  #Tautology    : 560
% 7.88/2.68  #SimpNegUnit  : 0
% 7.88/2.68  #BackRed      : 0
% 7.88/2.68  
% 7.88/2.68  #Partial instantiations: 0
% 7.88/2.68  #Strategies tried      : 1
% 7.88/2.68  
% 7.88/2.68  Timing (in seconds)
% 7.88/2.68  ----------------------
% 7.88/2.68  Preprocessing        : 0.26
% 7.88/2.69  Parsing              : 0.15
% 7.88/2.69  CNF conversion       : 0.02
% 7.88/2.69  Main loop            : 1.66
% 7.88/2.69  Inferencing          : 0.46
% 7.88/2.69  Reduction            : 0.54
% 7.88/2.69  Demodulation         : 0.42
% 7.88/2.69  BG Simplification    : 0.05
% 7.88/2.69  Subsumption          : 0.51
% 7.88/2.69  Abstraction          : 0.06
% 7.88/2.69  MUC search           : 0.00
% 7.88/2.69  Cooper               : 0.00
% 7.88/2.69  Total                : 1.95
% 7.88/2.69  Index Insertion      : 0.00
% 7.88/2.69  Index Deletion       : 0.00
% 7.88/2.69  Index Matching       : 0.00
% 7.88/2.69  BG Taut test         : 0.00
%------------------------------------------------------------------------------
