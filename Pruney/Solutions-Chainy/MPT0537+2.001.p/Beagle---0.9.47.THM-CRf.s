%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:00:20 EST 2020

% Result     : Theorem 1.94s
% Output     : CNFRefutation 1.94s
% Verified   : 
% Statistics : Number of formulae       :   35 (  41 expanded)
%              Number of leaves         :   21 (  24 expanded)
%              Depth                    :    7
%              Number of atoms          :   40 (  49 expanded)
%              Number of equality atoms :   12 (  17 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v1_xboole_0 > v1_relat_1 > k8_relat_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_1 > #skF_4 > #skF_5 > #skF_2 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k8_relat_1,type,(
    k8_relat_1: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(f_58,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => k8_relat_1(k1_xboole_0,A) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t137_relat_1)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_39,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relat_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ! [C] :
          ( v1_relat_1(C)
         => ( C = k8_relat_1(A,B)
          <=> ! [D,E] :
                ( r2_hidden(k4_tarski(D,E),C)
              <=> ( r2_hidden(E,A)
                  & r2_hidden(k4_tarski(D,E),B) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d12_relat_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_35,axiom,(
    ! [A,B] : ~ r2_hidden(A,k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_zfmisc_1)).

tff(c_32,plain,(
    k8_relat_1(k1_xboole_0,'#skF_5') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_34,plain,(
    v1_relat_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_42,plain,(
    ! [A_25] :
      ( v1_relat_1(A_25)
      | ~ v1_xboole_0(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_46,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_2,c_42])).

tff(c_92,plain,(
    ! [A_44,B_45,C_46] :
      ( r2_hidden('#skF_2'(A_44,B_45,C_46),A_44)
      | r2_hidden(k4_tarski('#skF_3'(A_44,B_45,C_46),'#skF_4'(A_44,B_45,C_46)),C_46)
      | k8_relat_1(A_44,B_45) = C_46
      | ~ v1_relat_1(C_46)
      | ~ v1_relat_1(B_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_6,plain,(
    ! [A_1] : k2_zfmisc_1(A_1,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_62,plain,(
    ! [A_27,B_28] : ~ r2_hidden(A_27,k2_zfmisc_1(A_27,B_28)) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_68,plain,(
    ! [A_1] : ~ r2_hidden(A_1,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_62])).

tff(c_104,plain,(
    ! [A_44,B_45] :
      ( r2_hidden('#skF_2'(A_44,B_45,k1_xboole_0),A_44)
      | k8_relat_1(A_44,B_45) = k1_xboole_0
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(B_45) ) ),
    inference(resolution,[status(thm)],[c_92,c_68])).

tff(c_116,plain,(
    ! [A_50,B_51] :
      ( r2_hidden('#skF_2'(A_50,B_51,k1_xboole_0),A_50)
      | k8_relat_1(A_50,B_51) = k1_xboole_0
      | ~ v1_relat_1(B_51) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_104])).

tff(c_122,plain,(
    ! [B_52] :
      ( k8_relat_1(k1_xboole_0,B_52) = k1_xboole_0
      | ~ v1_relat_1(B_52) ) ),
    inference(resolution,[status(thm)],[c_116,c_68])).

tff(c_128,plain,(
    k8_relat_1(k1_xboole_0,'#skF_5') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_34,c_122])).

tff(c_133,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_128])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 16:46:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.94/1.28  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.94/1.28  
% 1.94/1.28  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.94/1.29  %$ r2_hidden > v1_xboole_0 > v1_relat_1 > k8_relat_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_1 > #skF_4 > #skF_5 > #skF_2 > #skF_3
% 1.94/1.29  
% 1.94/1.29  %Foreground sorts:
% 1.94/1.29  
% 1.94/1.29  
% 1.94/1.29  %Background operators:
% 1.94/1.29  
% 1.94/1.29  
% 1.94/1.29  %Foreground operators:
% 1.94/1.29  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 1.94/1.29  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 1.94/1.29  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.94/1.29  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.94/1.29  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 1.94/1.29  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.94/1.29  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 1.94/1.29  tff('#skF_5', type, '#skF_5': $i).
% 1.94/1.29  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 1.94/1.29  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.94/1.29  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.94/1.29  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.94/1.29  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 1.94/1.29  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.94/1.29  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.94/1.29  
% 1.94/1.30  tff(f_58, negated_conjecture, ~(![A]: (v1_relat_1(A) => (k8_relat_1(k1_xboole_0, A) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t137_relat_1)).
% 1.94/1.30  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 1.94/1.30  tff(f_39, axiom, (![A]: (v1_xboole_0(A) => v1_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relat_1)).
% 1.94/1.30  tff(f_53, axiom, (![A, B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => ((C = k8_relat_1(A, B)) <=> (![D, E]: (r2_hidden(k4_tarski(D, E), C) <=> (r2_hidden(E, A) & r2_hidden(k4_tarski(D, E), B))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d12_relat_1)).
% 1.94/1.30  tff(f_32, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 1.94/1.30  tff(f_35, axiom, (![A, B]: ~r2_hidden(A, k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t152_zfmisc_1)).
% 1.94/1.30  tff(c_32, plain, (k8_relat_1(k1_xboole_0, '#skF_5')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_58])).
% 1.94/1.30  tff(c_34, plain, (v1_relat_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_58])).
% 1.94/1.30  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 1.94/1.30  tff(c_42, plain, (![A_25]: (v1_relat_1(A_25) | ~v1_xboole_0(A_25))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.94/1.30  tff(c_46, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_42])).
% 1.94/1.30  tff(c_92, plain, (![A_44, B_45, C_46]: (r2_hidden('#skF_2'(A_44, B_45, C_46), A_44) | r2_hidden(k4_tarski('#skF_3'(A_44, B_45, C_46), '#skF_4'(A_44, B_45, C_46)), C_46) | k8_relat_1(A_44, B_45)=C_46 | ~v1_relat_1(C_46) | ~v1_relat_1(B_45))), inference(cnfTransformation, [status(thm)], [f_53])).
% 1.94/1.30  tff(c_6, plain, (![A_1]: (k2_zfmisc_1(A_1, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.94/1.30  tff(c_62, plain, (![A_27, B_28]: (~r2_hidden(A_27, k2_zfmisc_1(A_27, B_28)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.94/1.30  tff(c_68, plain, (![A_1]: (~r2_hidden(A_1, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_6, c_62])).
% 1.94/1.30  tff(c_104, plain, (![A_44, B_45]: (r2_hidden('#skF_2'(A_44, B_45, k1_xboole_0), A_44) | k8_relat_1(A_44, B_45)=k1_xboole_0 | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(B_45))), inference(resolution, [status(thm)], [c_92, c_68])).
% 1.94/1.30  tff(c_116, plain, (![A_50, B_51]: (r2_hidden('#skF_2'(A_50, B_51, k1_xboole_0), A_50) | k8_relat_1(A_50, B_51)=k1_xboole_0 | ~v1_relat_1(B_51))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_104])).
% 1.94/1.30  tff(c_122, plain, (![B_52]: (k8_relat_1(k1_xboole_0, B_52)=k1_xboole_0 | ~v1_relat_1(B_52))), inference(resolution, [status(thm)], [c_116, c_68])).
% 1.94/1.30  tff(c_128, plain, (k8_relat_1(k1_xboole_0, '#skF_5')=k1_xboole_0), inference(resolution, [status(thm)], [c_34, c_122])).
% 1.94/1.30  tff(c_133, plain, $false, inference(negUnitSimplification, [status(thm)], [c_32, c_128])).
% 1.94/1.30  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.94/1.30  
% 1.94/1.30  Inference rules
% 1.94/1.30  ----------------------
% 1.94/1.30  #Ref     : 0
% 1.94/1.30  #Sup     : 20
% 1.94/1.30  #Fact    : 0
% 1.94/1.30  #Define  : 0
% 1.94/1.30  #Split   : 0
% 1.94/1.30  #Chain   : 0
% 1.94/1.30  #Close   : 0
% 1.94/1.30  
% 1.94/1.30  Ordering : KBO
% 1.94/1.30  
% 1.94/1.30  Simplification rules
% 1.94/1.30  ----------------------
% 1.94/1.30  #Subsume      : 1
% 1.94/1.30  #Demod        : 1
% 1.94/1.30  #Tautology    : 10
% 1.94/1.30  #SimpNegUnit  : 1
% 1.94/1.30  #BackRed      : 0
% 1.94/1.30  
% 1.94/1.30  #Partial instantiations: 0
% 1.94/1.30  #Strategies tried      : 1
% 1.94/1.30  
% 1.94/1.30  Timing (in seconds)
% 1.94/1.30  ----------------------
% 2.07/1.30  Preprocessing        : 0.26
% 2.07/1.30  Parsing              : 0.13
% 2.07/1.30  CNF conversion       : 0.02
% 2.07/1.30  Main loop            : 0.20
% 2.07/1.30  Inferencing          : 0.09
% 2.07/1.30  Reduction            : 0.04
% 2.07/1.30  Demodulation         : 0.03
% 2.07/1.30  BG Simplification    : 0.01
% 2.07/1.30  Subsumption          : 0.04
% 2.07/1.30  Abstraction          : 0.01
% 2.07/1.30  MUC search           : 0.00
% 2.07/1.30  Cooper               : 0.00
% 2.07/1.30  Total                : 0.49
% 2.07/1.30  Index Insertion      : 0.00
% 2.07/1.30  Index Deletion       : 0.00
% 2.07/1.30  Index Matching       : 0.00
% 2.07/1.30  BG Taut test         : 0.00
%------------------------------------------------------------------------------
