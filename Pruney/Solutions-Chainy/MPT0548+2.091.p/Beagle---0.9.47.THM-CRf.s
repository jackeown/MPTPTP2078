%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:00:47 EST 2020

% Result     : Theorem 2.00s
% Output     : CNFRefutation 2.00s
% Verified   : 
% Statistics : Number of formulae       :   44 (  55 expanded)
%              Number of leaves         :   24 (  29 expanded)
%              Depth                    :    7
%              Number of atoms          :   44 (  60 expanded)
%              Number of equality atoms :   27 (  37 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > v1_relat_1 > k9_relat_1 > k7_relat_1 > k4_xboole_0 > k3_xboole_0 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_37,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_39,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_50,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_31,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_56,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( k7_relat_1(B,A) = k1_xboole_0
      <=> r1_xboole_0(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_relat_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_27,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_29,axiom,(
    ! [A] : k4_xboole_0(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).

tff(f_43,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k9_relat_1(B,A) = k9_relat_1(B,k3_xboole_0(k1_relat_1(B),A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t145_relat_1)).

tff(f_59,negated_conjecture,(
    ~ ! [A] : k9_relat_1(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t150_relat_1)).

tff(c_39,plain,(
    ! [B_18] : k2_zfmisc_1(k1_xboole_0,B_18) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_14,plain,(
    ! [A_7,B_8] : v1_relat_1(k2_zfmisc_1(A_7,B_8)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_43,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_39,c_14])).

tff(c_20,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_6,plain,(
    ! [A_4] : r1_xboole_0(A_4,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_129,plain,(
    ! [B_28,A_29] :
      ( k7_relat_1(B_28,A_29) = k1_xboole_0
      | ~ r1_xboole_0(k1_relat_1(B_28),A_29)
      | ~ v1_relat_1(B_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_140,plain,(
    ! [B_30] :
      ( k7_relat_1(B_30,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(B_30) ) ),
    inference(resolution,[status(thm)],[c_6,c_129])).

tff(c_147,plain,(
    k7_relat_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_43,c_140])).

tff(c_18,plain,(
    ! [B_12,A_11] :
      ( k2_relat_1(k7_relat_1(B_12,A_11)) = k9_relat_1(B_12,A_11)
      | ~ v1_relat_1(B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_152,plain,
    ( k9_relat_1(k1_xboole_0,k1_xboole_0) = k2_relat_1(k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_147,c_18])).

tff(c_156,plain,(
    k9_relat_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_43,c_20,c_152])).

tff(c_84,plain,(
    ! [A_23,B_24] : k4_xboole_0(A_23,k4_xboole_0(A_23,B_24)) = k3_xboole_0(A_23,B_24) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_4,plain,(
    ! [A_3] : k4_xboole_0(k1_xboole_0,A_3) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_94,plain,(
    ! [B_24] : k3_xboole_0(k1_xboole_0,B_24) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_84,c_4])).

tff(c_22,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_241,plain,(
    ! [B_41,A_42] :
      ( k9_relat_1(B_41,k3_xboole_0(k1_relat_1(B_41),A_42)) = k9_relat_1(B_41,A_42)
      | ~ v1_relat_1(B_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_250,plain,(
    ! [A_42] :
      ( k9_relat_1(k1_xboole_0,k3_xboole_0(k1_xboole_0,A_42)) = k9_relat_1(k1_xboole_0,A_42)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_241])).

tff(c_254,plain,(
    ! [A_42] : k9_relat_1(k1_xboole_0,A_42) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_43,c_156,c_94,c_250])).

tff(c_28,plain,(
    k9_relat_1(k1_xboole_0,'#skF_1') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_258,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_254,c_28])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n003.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 19:57:27 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.00/1.24  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.00/1.25  
% 2.00/1.25  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.00/1.25  %$ r1_xboole_0 > v1_relat_1 > k9_relat_1 > k7_relat_1 > k4_xboole_0 > k3_xboole_0 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_1
% 2.00/1.25  
% 2.00/1.25  %Foreground sorts:
% 2.00/1.25  
% 2.00/1.25  
% 2.00/1.25  %Background operators:
% 2.00/1.25  
% 2.00/1.25  
% 2.00/1.25  %Foreground operators:
% 2.00/1.25  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.00/1.25  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.00/1.25  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.00/1.25  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.00/1.25  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.00/1.25  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.00/1.25  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.00/1.25  tff('#skF_1', type, '#skF_1': $i).
% 2.00/1.25  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.00/1.25  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.00/1.25  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.00/1.25  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.00/1.25  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.00/1.25  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.00/1.25  
% 2.00/1.26  tff(f_37, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 2.00/1.26  tff(f_39, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 2.00/1.26  tff(f_50, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 2.00/1.26  tff(f_31, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 2.00/1.26  tff(f_56, axiom, (![A, B]: (v1_relat_1(B) => ((k7_relat_1(B, A) = k1_xboole_0) <=> r1_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t95_relat_1)).
% 2.00/1.26  tff(f_47, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_relat_1)).
% 2.00/1.26  tff(f_27, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 2.00/1.26  tff(f_29, axiom, (![A]: (k4_xboole_0(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_boole)).
% 2.00/1.26  tff(f_43, axiom, (![A, B]: (v1_relat_1(B) => (k9_relat_1(B, A) = k9_relat_1(B, k3_xboole_0(k1_relat_1(B), A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t145_relat_1)).
% 2.00/1.26  tff(f_59, negated_conjecture, ~(![A]: (k9_relat_1(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t150_relat_1)).
% 2.00/1.26  tff(c_39, plain, (![B_18]: (k2_zfmisc_1(k1_xboole_0, B_18)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.00/1.26  tff(c_14, plain, (![A_7, B_8]: (v1_relat_1(k2_zfmisc_1(A_7, B_8)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.00/1.26  tff(c_43, plain, (v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_39, c_14])).
% 2.00/1.26  tff(c_20, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.00/1.26  tff(c_6, plain, (![A_4]: (r1_xboole_0(A_4, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.00/1.26  tff(c_129, plain, (![B_28, A_29]: (k7_relat_1(B_28, A_29)=k1_xboole_0 | ~r1_xboole_0(k1_relat_1(B_28), A_29) | ~v1_relat_1(B_28))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.00/1.26  tff(c_140, plain, (![B_30]: (k7_relat_1(B_30, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(B_30))), inference(resolution, [status(thm)], [c_6, c_129])).
% 2.00/1.26  tff(c_147, plain, (k7_relat_1(k1_xboole_0, k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_43, c_140])).
% 2.00/1.26  tff(c_18, plain, (![B_12, A_11]: (k2_relat_1(k7_relat_1(B_12, A_11))=k9_relat_1(B_12, A_11) | ~v1_relat_1(B_12))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.00/1.26  tff(c_152, plain, (k9_relat_1(k1_xboole_0, k1_xboole_0)=k2_relat_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_147, c_18])).
% 2.00/1.26  tff(c_156, plain, (k9_relat_1(k1_xboole_0, k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_43, c_20, c_152])).
% 2.00/1.26  tff(c_84, plain, (![A_23, B_24]: (k4_xboole_0(A_23, k4_xboole_0(A_23, B_24))=k3_xboole_0(A_23, B_24))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.00/1.26  tff(c_4, plain, (![A_3]: (k4_xboole_0(k1_xboole_0, A_3)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.00/1.26  tff(c_94, plain, (![B_24]: (k3_xboole_0(k1_xboole_0, B_24)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_84, c_4])).
% 2.00/1.26  tff(c_22, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.00/1.26  tff(c_241, plain, (![B_41, A_42]: (k9_relat_1(B_41, k3_xboole_0(k1_relat_1(B_41), A_42))=k9_relat_1(B_41, A_42) | ~v1_relat_1(B_41))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.00/1.26  tff(c_250, plain, (![A_42]: (k9_relat_1(k1_xboole_0, k3_xboole_0(k1_xboole_0, A_42))=k9_relat_1(k1_xboole_0, A_42) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_22, c_241])).
% 2.00/1.26  tff(c_254, plain, (![A_42]: (k9_relat_1(k1_xboole_0, A_42)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_43, c_156, c_94, c_250])).
% 2.00/1.26  tff(c_28, plain, (k9_relat_1(k1_xboole_0, '#skF_1')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.00/1.26  tff(c_258, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_254, c_28])).
% 2.00/1.26  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.00/1.26  
% 2.00/1.26  Inference rules
% 2.00/1.26  ----------------------
% 2.00/1.26  #Ref     : 0
% 2.00/1.26  #Sup     : 58
% 2.00/1.26  #Fact    : 0
% 2.00/1.26  #Define  : 0
% 2.00/1.26  #Split   : 0
% 2.00/1.26  #Chain   : 0
% 2.00/1.26  #Close   : 0
% 2.00/1.26  
% 2.00/1.26  Ordering : KBO
% 2.00/1.26  
% 2.00/1.26  Simplification rules
% 2.00/1.26  ----------------------
% 2.00/1.26  #Subsume      : 0
% 2.00/1.26  #Demod        : 27
% 2.00/1.26  #Tautology    : 46
% 2.00/1.26  #SimpNegUnit  : 0
% 2.00/1.26  #BackRed      : 1
% 2.00/1.26  
% 2.00/1.26  #Partial instantiations: 0
% 2.00/1.26  #Strategies tried      : 1
% 2.00/1.26  
% 2.00/1.26  Timing (in seconds)
% 2.00/1.26  ----------------------
% 2.00/1.26  Preprocessing        : 0.30
% 2.00/1.26  Parsing              : 0.17
% 2.00/1.26  CNF conversion       : 0.02
% 2.00/1.26  Main loop            : 0.16
% 2.00/1.26  Inferencing          : 0.07
% 2.00/1.26  Reduction            : 0.05
% 2.00/1.26  Demodulation         : 0.03
% 2.00/1.26  BG Simplification    : 0.01
% 2.00/1.26  Subsumption          : 0.02
% 2.00/1.26  Abstraction          : 0.01
% 2.00/1.26  MUC search           : 0.00
% 2.00/1.26  Cooper               : 0.00
% 2.00/1.26  Total                : 0.49
% 2.00/1.26  Index Insertion      : 0.00
% 2.00/1.26  Index Deletion       : 0.00
% 2.00/1.26  Index Matching       : 0.00
% 2.00/1.26  BG Taut test         : 0.00
%------------------------------------------------------------------------------
