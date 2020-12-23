%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:59:32 EST 2020

% Result     : Theorem 1.70s
% Output     : CNFRefutation 1.70s
% Verified   : 
% Statistics : Number of formulae       :   31 (  34 expanded)
%              Number of leaves         :   19 (  21 expanded)
%              Depth                    :    6
%              Number of atoms          :   36 (  41 expanded)
%              Number of equality atoms :    7 (   9 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k5_relat_1 > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_55,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => k5_relat_1(k6_relat_1(k1_relat_1(A)),A) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t78_relat_1)).

tff(f_33,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k3_xboole_0(A,k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A))) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_relat_1)).

tff(f_27,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_44,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(A,B)
           => ( r1_tarski(k1_relat_1(A),k1_relat_1(B))
              & r1_tarski(k2_relat_1(A),k2_relat_1(B)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_relat_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k1_relat_1(B),A)
       => k5_relat_1(k6_relat_1(A),B) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_relat_1)).

tff(c_16,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_27,plain,(
    ! [A_15] :
      ( k3_xboole_0(A_15,k2_zfmisc_1(k1_relat_1(A_15),k2_relat_1(A_15))) = A_15
      | ~ v1_relat_1(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_2,plain,(
    ! [A_1,B_2] : r1_tarski(k3_xboole_0(A_1,B_2),A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_33,plain,(
    ! [A_15] :
      ( r1_tarski(A_15,A_15)
      | ~ v1_relat_1(A_15) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_27,c_2])).

tff(c_62,plain,(
    ! [A_22,B_23] :
      ( r1_tarski(k1_relat_1(A_22),k1_relat_1(B_23))
      | ~ r1_tarski(A_22,B_23)
      | ~ v1_relat_1(B_23)
      | ~ v1_relat_1(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_12,plain,(
    ! [A_9,B_10] :
      ( k5_relat_1(k6_relat_1(A_9),B_10) = B_10
      | ~ r1_tarski(k1_relat_1(B_10),A_9)
      | ~ v1_relat_1(B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_67,plain,(
    ! [B_24,A_25] :
      ( k5_relat_1(k6_relat_1(k1_relat_1(B_24)),A_25) = A_25
      | ~ r1_tarski(A_25,B_24)
      | ~ v1_relat_1(B_24)
      | ~ v1_relat_1(A_25) ) ),
    inference(resolution,[status(thm)],[c_62,c_12])).

tff(c_14,plain,(
    k5_relat_1(k6_relat_1(k1_relat_1('#skF_1')),'#skF_1') != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_77,plain,
    ( ~ r1_tarski('#skF_1','#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_67,c_14])).

tff(c_88,plain,(
    ~ r1_tarski('#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_77])).

tff(c_93,plain,(
    ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_33,c_88])).

tff(c_97,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_93])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:18:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.70/1.10  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.70/1.10  
% 1.70/1.10  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.70/1.11  %$ r1_tarski > v1_relat_1 > k5_relat_1 > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_1
% 1.70/1.11  
% 1.70/1.11  %Foreground sorts:
% 1.70/1.11  
% 1.70/1.11  
% 1.70/1.11  %Background operators:
% 1.70/1.11  
% 1.70/1.11  
% 1.70/1.11  %Foreground operators:
% 1.70/1.11  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.70/1.11  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 1.70/1.11  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.70/1.11  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.70/1.11  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.70/1.11  tff('#skF_1', type, '#skF_1': $i).
% 1.70/1.11  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.70/1.11  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.70/1.11  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.70/1.11  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 1.70/1.11  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.70/1.11  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.70/1.11  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.70/1.11  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 1.70/1.11  
% 1.70/1.11  tff(f_55, negated_conjecture, ~(![A]: (v1_relat_1(A) => (k5_relat_1(k6_relat_1(k1_relat_1(A)), A) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t78_relat_1)).
% 1.70/1.11  tff(f_33, axiom, (![A]: (v1_relat_1(A) => (k3_xboole_0(A, k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_relat_1)).
% 1.70/1.11  tff(f_27, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 1.70/1.11  tff(f_44, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(A, B) => (r1_tarski(k1_relat_1(A), k1_relat_1(B)) & r1_tarski(k2_relat_1(A), k2_relat_1(B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t25_relat_1)).
% 1.70/1.11  tff(f_50, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(B), A) => (k5_relat_1(k6_relat_1(A), B) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t77_relat_1)).
% 1.70/1.11  tff(c_16, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_55])).
% 1.70/1.11  tff(c_27, plain, (![A_15]: (k3_xboole_0(A_15, k2_zfmisc_1(k1_relat_1(A_15), k2_relat_1(A_15)))=A_15 | ~v1_relat_1(A_15))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.70/1.11  tff(c_2, plain, (![A_1, B_2]: (r1_tarski(k3_xboole_0(A_1, B_2), A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.70/1.11  tff(c_33, plain, (![A_15]: (r1_tarski(A_15, A_15) | ~v1_relat_1(A_15))), inference(superposition, [status(thm), theory('equality')], [c_27, c_2])).
% 1.70/1.11  tff(c_62, plain, (![A_22, B_23]: (r1_tarski(k1_relat_1(A_22), k1_relat_1(B_23)) | ~r1_tarski(A_22, B_23) | ~v1_relat_1(B_23) | ~v1_relat_1(A_22))), inference(cnfTransformation, [status(thm)], [f_44])).
% 1.70/1.11  tff(c_12, plain, (![A_9, B_10]: (k5_relat_1(k6_relat_1(A_9), B_10)=B_10 | ~r1_tarski(k1_relat_1(B_10), A_9) | ~v1_relat_1(B_10))), inference(cnfTransformation, [status(thm)], [f_50])).
% 1.70/1.11  tff(c_67, plain, (![B_24, A_25]: (k5_relat_1(k6_relat_1(k1_relat_1(B_24)), A_25)=A_25 | ~r1_tarski(A_25, B_24) | ~v1_relat_1(B_24) | ~v1_relat_1(A_25))), inference(resolution, [status(thm)], [c_62, c_12])).
% 1.70/1.11  tff(c_14, plain, (k5_relat_1(k6_relat_1(k1_relat_1('#skF_1')), '#skF_1')!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_55])).
% 1.70/1.11  tff(c_77, plain, (~r1_tarski('#skF_1', '#skF_1') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_67, c_14])).
% 1.70/1.11  tff(c_88, plain, (~r1_tarski('#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_16, c_77])).
% 1.70/1.11  tff(c_93, plain, (~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_33, c_88])).
% 1.70/1.11  tff(c_97, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_16, c_93])).
% 1.70/1.11  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.70/1.11  
% 1.70/1.11  Inference rules
% 1.70/1.11  ----------------------
% 1.70/1.11  #Ref     : 0
% 1.70/1.11  #Sup     : 16
% 1.70/1.11  #Fact    : 0
% 1.70/1.11  #Define  : 0
% 1.70/1.11  #Split   : 0
% 1.70/1.11  #Chain   : 0
% 1.70/1.11  #Close   : 0
% 1.70/1.11  
% 1.70/1.11  Ordering : KBO
% 1.70/1.11  
% 1.70/1.11  Simplification rules
% 1.70/1.11  ----------------------
% 1.70/1.11  #Subsume      : 0
% 1.70/1.11  #Demod        : 3
% 1.70/1.11  #Tautology    : 10
% 1.70/1.11  #SimpNegUnit  : 0
% 1.70/1.11  #BackRed      : 0
% 1.70/1.11  
% 1.70/1.11  #Partial instantiations: 0
% 1.70/1.11  #Strategies tried      : 1
% 1.70/1.12  
% 1.70/1.12  Timing (in seconds)
% 1.70/1.12  ----------------------
% 1.70/1.12  Preprocessing        : 0.26
% 1.70/1.12  Parsing              : 0.15
% 1.70/1.12  CNF conversion       : 0.01
% 1.70/1.12  Main loop            : 0.11
% 1.70/1.12  Inferencing          : 0.06
% 1.70/1.12  Reduction            : 0.03
% 1.70/1.12  Demodulation         : 0.02
% 1.70/1.12  BG Simplification    : 0.01
% 1.70/1.12  Subsumption          : 0.01
% 1.70/1.12  Abstraction          : 0.00
% 1.70/1.12  MUC search           : 0.00
% 1.70/1.12  Cooper               : 0.00
% 1.70/1.12  Total                : 0.39
% 1.70/1.12  Index Insertion      : 0.00
% 1.70/1.12  Index Deletion       : 0.00
% 1.70/1.12  Index Matching       : 0.00
% 1.70/1.12  BG Taut test         : 0.00
%------------------------------------------------------------------------------
