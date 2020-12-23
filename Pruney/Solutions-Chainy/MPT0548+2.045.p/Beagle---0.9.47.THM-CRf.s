%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:00:41 EST 2020

% Result     : Theorem 1.65s
% Output     : CNFRefutation 1.65s
% Verified   : 
% Statistics : Number of formulae       :   44 (  55 expanded)
%              Number of leaves         :   26 (  31 expanded)
%              Depth                    :    6
%              Number of atoms          :   39 (  57 expanded)
%              Number of equality atoms :   24 (  34 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v1_relat_1 > k9_relat_1 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_48,axiom,(
    ! [A] :
      ( v1_relat_1(A)
    <=> ! [B] :
          ~ ( r2_hidden(B,A)
            & ! [C,D] : B != k4_tarski(C,D) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_relat_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_38,axiom,(
    ! [A,B] : ~ r2_hidden(A,k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_zfmisc_1)).

tff(f_59,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_56,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k9_relat_1(A,k1_relat_1(A)) = k2_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_relat_1)).

tff(f_27,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_29,axiom,(
    ! [A] : k4_xboole_0(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).

tff(f_52,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k9_relat_1(B,A) = k9_relat_1(B,k3_xboole_0(k1_relat_1(B),A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t145_relat_1)).

tff(f_62,negated_conjecture,(
    ~ ! [A] : k9_relat_1(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t150_relat_1)).

tff(c_74,plain,(
    ! [A_35] :
      ( r2_hidden('#skF_1'(A_35),A_35)
      | v1_relat_1(A_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_8,plain,(
    ! [A_4] : k2_zfmisc_1(A_4,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_66,plain,(
    ! [A_32,B_33] : ~ r2_hidden(A_32,k2_zfmisc_1(A_32,B_33)) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_69,plain,(
    ! [A_4] : ~ r2_hidden(A_4,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_66])).

tff(c_79,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_74,c_69])).

tff(c_24,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_26,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_81,plain,(
    ! [A_39] :
      ( k9_relat_1(A_39,k1_relat_1(A_39)) = k2_relat_1(A_39)
      | ~ v1_relat_1(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_90,plain,
    ( k9_relat_1(k1_xboole_0,k1_xboole_0) = k2_relat_1(k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_81])).

tff(c_94,plain,(
    k9_relat_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_79,c_24,c_90])).

tff(c_110,plain,(
    ! [A_42,B_43] : k4_xboole_0(A_42,k4_xboole_0(A_42,B_43)) = k3_xboole_0(A_42,B_43) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_4,plain,(
    ! [A_3] : k4_xboole_0(k1_xboole_0,A_3) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_120,plain,(
    ! [B_43] : k3_xboole_0(k1_xboole_0,B_43) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_110,c_4])).

tff(c_146,plain,(
    ! [B_45,A_46] :
      ( k9_relat_1(B_45,k3_xboole_0(k1_relat_1(B_45),A_46)) = k9_relat_1(B_45,A_46)
      | ~ v1_relat_1(B_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_155,plain,(
    ! [A_46] :
      ( k9_relat_1(k1_xboole_0,k3_xboole_0(k1_xboole_0,A_46)) = k9_relat_1(k1_xboole_0,A_46)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_146])).

tff(c_159,plain,(
    ! [A_46] : k9_relat_1(k1_xboole_0,A_46) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_79,c_94,c_120,c_155])).

tff(c_28,plain,(
    k9_relat_1(k1_xboole_0,'#skF_4') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_163,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_159,c_28])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n006.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 16:58:52 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.65/1.13  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.65/1.14  
% 1.65/1.14  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.65/1.14  %$ r2_hidden > v1_relat_1 > k9_relat_1 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2
% 1.65/1.14  
% 1.65/1.14  %Foreground sorts:
% 1.65/1.14  
% 1.65/1.14  
% 1.65/1.14  %Background operators:
% 1.65/1.14  
% 1.65/1.14  
% 1.65/1.14  %Foreground operators:
% 1.65/1.14  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.65/1.14  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.65/1.14  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.65/1.14  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 1.65/1.14  tff('#skF_1', type, '#skF_1': $i > $i).
% 1.65/1.14  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.65/1.14  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 1.65/1.14  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.65/1.14  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 1.65/1.14  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.65/1.14  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.65/1.14  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.65/1.14  tff('#skF_4', type, '#skF_4': $i).
% 1.65/1.14  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.65/1.14  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 1.65/1.14  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.65/1.14  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.65/1.14  
% 1.65/1.15  tff(f_48, axiom, (![A]: (v1_relat_1(A) <=> (![B]: ~(r2_hidden(B, A) & (![C, D]: ~(B = k4_tarski(C, D))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_relat_1)).
% 1.65/1.15  tff(f_35, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 1.65/1.15  tff(f_38, axiom, (![A, B]: ~r2_hidden(A, k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t152_zfmisc_1)).
% 1.65/1.15  tff(f_59, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 1.65/1.15  tff(f_56, axiom, (![A]: (v1_relat_1(A) => (k9_relat_1(A, k1_relat_1(A)) = k2_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t146_relat_1)).
% 1.65/1.15  tff(f_27, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 1.65/1.15  tff(f_29, axiom, (![A]: (k4_xboole_0(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_boole)).
% 1.65/1.15  tff(f_52, axiom, (![A, B]: (v1_relat_1(B) => (k9_relat_1(B, A) = k9_relat_1(B, k3_xboole_0(k1_relat_1(B), A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t145_relat_1)).
% 1.65/1.15  tff(f_62, negated_conjecture, ~(![A]: (k9_relat_1(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t150_relat_1)).
% 1.65/1.15  tff(c_74, plain, (![A_35]: (r2_hidden('#skF_1'(A_35), A_35) | v1_relat_1(A_35))), inference(cnfTransformation, [status(thm)], [f_48])).
% 1.65/1.15  tff(c_8, plain, (![A_4]: (k2_zfmisc_1(A_4, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.65/1.15  tff(c_66, plain, (![A_32, B_33]: (~r2_hidden(A_32, k2_zfmisc_1(A_32, B_33)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 1.65/1.15  tff(c_69, plain, (![A_4]: (~r2_hidden(A_4, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_8, c_66])).
% 1.65/1.15  tff(c_79, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_74, c_69])).
% 1.65/1.15  tff(c_24, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_59])).
% 1.65/1.15  tff(c_26, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_59])).
% 1.65/1.15  tff(c_81, plain, (![A_39]: (k9_relat_1(A_39, k1_relat_1(A_39))=k2_relat_1(A_39) | ~v1_relat_1(A_39))), inference(cnfTransformation, [status(thm)], [f_56])).
% 1.65/1.15  tff(c_90, plain, (k9_relat_1(k1_xboole_0, k1_xboole_0)=k2_relat_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_26, c_81])).
% 1.65/1.15  tff(c_94, plain, (k9_relat_1(k1_xboole_0, k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_79, c_24, c_90])).
% 1.65/1.15  tff(c_110, plain, (![A_42, B_43]: (k4_xboole_0(A_42, k4_xboole_0(A_42, B_43))=k3_xboole_0(A_42, B_43))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.65/1.15  tff(c_4, plain, (![A_3]: (k4_xboole_0(k1_xboole_0, A_3)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.65/1.15  tff(c_120, plain, (![B_43]: (k3_xboole_0(k1_xboole_0, B_43)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_110, c_4])).
% 1.65/1.15  tff(c_146, plain, (![B_45, A_46]: (k9_relat_1(B_45, k3_xboole_0(k1_relat_1(B_45), A_46))=k9_relat_1(B_45, A_46) | ~v1_relat_1(B_45))), inference(cnfTransformation, [status(thm)], [f_52])).
% 1.65/1.15  tff(c_155, plain, (![A_46]: (k9_relat_1(k1_xboole_0, k3_xboole_0(k1_xboole_0, A_46))=k9_relat_1(k1_xboole_0, A_46) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_26, c_146])).
% 1.65/1.15  tff(c_159, plain, (![A_46]: (k9_relat_1(k1_xboole_0, A_46)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_79, c_94, c_120, c_155])).
% 1.65/1.15  tff(c_28, plain, (k9_relat_1(k1_xboole_0, '#skF_4')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_62])).
% 1.65/1.15  tff(c_163, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_159, c_28])).
% 1.65/1.15  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.65/1.15  
% 1.65/1.15  Inference rules
% 1.65/1.15  ----------------------
% 1.65/1.15  #Ref     : 0
% 1.65/1.15  #Sup     : 34
% 1.65/1.15  #Fact    : 0
% 1.65/1.15  #Define  : 0
% 1.65/1.15  #Split   : 0
% 1.65/1.15  #Chain   : 0
% 1.65/1.15  #Close   : 0
% 1.65/1.15  
% 1.65/1.15  Ordering : KBO
% 1.65/1.15  
% 1.65/1.15  Simplification rules
% 1.65/1.15  ----------------------
% 1.65/1.15  #Subsume      : 1
% 1.65/1.15  #Demod        : 10
% 1.65/1.15  #Tautology    : 27
% 1.65/1.15  #SimpNegUnit  : 0
% 1.65/1.15  #BackRed      : 1
% 1.65/1.15  
% 1.65/1.15  #Partial instantiations: 0
% 1.65/1.15  #Strategies tried      : 1
% 1.65/1.15  
% 1.65/1.15  Timing (in seconds)
% 1.65/1.15  ----------------------
% 1.65/1.15  Preprocessing        : 0.26
% 1.65/1.15  Parsing              : 0.14
% 1.65/1.15  CNF conversion       : 0.02
% 1.65/1.15  Main loop            : 0.12
% 1.65/1.15  Inferencing          : 0.05
% 1.65/1.15  Reduction            : 0.04
% 1.65/1.15  Demodulation         : 0.03
% 1.65/1.15  BG Simplification    : 0.01
% 1.65/1.15  Subsumption          : 0.02
% 1.65/1.15  Abstraction          : 0.01
% 1.65/1.15  MUC search           : 0.00
% 1.65/1.15  Cooper               : 0.00
% 1.65/1.15  Total                : 0.41
% 1.65/1.15  Index Insertion      : 0.00
% 1.65/1.15  Index Deletion       : 0.00
% 1.65/1.15  Index Matching       : 0.00
% 1.65/1.15  BG Taut test         : 0.00
%------------------------------------------------------------------------------
