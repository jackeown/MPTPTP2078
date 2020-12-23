%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:00:03 EST 2020

% Result     : Theorem 2.03s
% Output     : CNFRefutation 2.03s
% Verified   : 
% Statistics : Number of formulae       :   52 (  52 expanded)
%              Number of leaves         :   37 (  37 expanded)
%              Depth                    :    7
%              Number of atoms          :   40 (  40 expanded)
%              Number of equality atoms :   22 (  22 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k7_relat_1 > k5_xboole_0 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k2_relat_1 > k1_tarski > k1_setfam_1 > k1_relat_1 > o_0_0_xboole_0 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(o_0_0_xboole_0,type,(
    o_0_0_xboole_0: $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_30,axiom,(
    ! [A] : k4_xboole_0(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).

tff(f_34,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_67,axiom,(
    ! [A] :
      ( v1_relat_1(A)
    <=> ! [B] :
          ~ ( r2_hidden(B,A)
            & ! [C,D] : B != k4_tarski(C,D) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_relat_1)).

tff(f_52,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => k2_xboole_0(k1_tarski(A),B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_zfmisc_1)).

tff(f_55,axiom,(
    ! [A,B] : k2_xboole_0(k1_tarski(A),B) != k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_zfmisc_1)).

tff(f_70,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_76,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( k7_relat_1(B,A) = k1_xboole_0
      <=> r1_xboole_0(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_relat_1)).

tff(f_79,negated_conjecture,(
    ~ ! [A] : k7_relat_1(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t111_relat_1)).

tff(c_6,plain,(
    ! [A_3] : k4_xboole_0(k1_xboole_0,A_3) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_10,plain,(
    ! [A_4,B_5] :
      ( r1_xboole_0(A_4,B_5)
      | k4_xboole_0(A_4,B_5) != A_4 ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_36,plain,(
    ! [A_40] :
      ( r2_hidden('#skF_1'(A_40),A_40)
      | v1_relat_1(A_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_122,plain,(
    ! [A_77,B_78] :
      ( k2_xboole_0(k1_tarski(A_77),B_78) = B_78
      | ~ r2_hidden(A_77,B_78) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_28,plain,(
    ! [A_36,B_37] : k2_xboole_0(k1_tarski(A_36),B_37) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_146,plain,(
    ! [B_81,A_82] :
      ( k1_xboole_0 != B_81
      | ~ r2_hidden(A_82,B_81) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_122,c_28])).

tff(c_151,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_36,c_146])).

tff(c_40,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_191,plain,(
    ! [B_91,A_92] :
      ( k7_relat_1(B_91,A_92) = k1_xboole_0
      | ~ r1_xboole_0(k1_relat_1(B_91),A_92)
      | ~ v1_relat_1(B_91) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_201,plain,(
    ! [A_92] :
      ( k7_relat_1(k1_xboole_0,A_92) = k1_xboole_0
      | ~ r1_xboole_0(k1_xboole_0,A_92)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_191])).

tff(c_206,plain,(
    ! [A_93] :
      ( k7_relat_1(k1_xboole_0,A_93) = k1_xboole_0
      | ~ r1_xboole_0(k1_xboole_0,A_93) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_151,c_201])).

tff(c_213,plain,(
    ! [B_5] :
      ( k7_relat_1(k1_xboole_0,B_5) = k1_xboole_0
      | k4_xboole_0(k1_xboole_0,B_5) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_10,c_206])).

tff(c_217,plain,(
    ! [B_5] : k7_relat_1(k1_xboole_0,B_5) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_213])).

tff(c_46,plain,(
    k7_relat_1(k1_xboole_0,'#skF_4') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_223,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_217,c_46])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:31:06 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.03/1.21  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.03/1.21  
% 2.03/1.21  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.03/1.21  %$ r2_hidden > r1_xboole_0 > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k7_relat_1 > k5_xboole_0 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k2_relat_1 > k1_tarski > k1_setfam_1 > k1_relat_1 > o_0_0_xboole_0 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2
% 2.03/1.21  
% 2.03/1.21  %Foreground sorts:
% 2.03/1.21  
% 2.03/1.21  
% 2.03/1.21  %Background operators:
% 2.03/1.21  
% 2.03/1.21  
% 2.03/1.21  %Foreground operators:
% 2.03/1.21  tff(o_0_0_xboole_0, type, o_0_0_xboole_0: $i).
% 2.03/1.21  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.03/1.21  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.03/1.21  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.03/1.21  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.03/1.21  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.03/1.21  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.03/1.21  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.03/1.21  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.03/1.21  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.03/1.21  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.03/1.21  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.03/1.21  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.03/1.21  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.03/1.21  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.03/1.21  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.03/1.21  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.03/1.21  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.03/1.21  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.03/1.21  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.03/1.21  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.03/1.21  tff('#skF_4', type, '#skF_4': $i).
% 2.03/1.21  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.03/1.21  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.03/1.21  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.03/1.21  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.03/1.21  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.03/1.21  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.03/1.21  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.03/1.21  
% 2.03/1.22  tff(f_30, axiom, (![A]: (k4_xboole_0(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_boole)).
% 2.03/1.22  tff(f_34, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_xboole_1)).
% 2.03/1.22  tff(f_67, axiom, (![A]: (v1_relat_1(A) <=> (![B]: ~(r2_hidden(B, A) & (![C, D]: ~(B = k4_tarski(C, D))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_relat_1)).
% 2.03/1.22  tff(f_52, axiom, (![A, B]: (r2_hidden(A, B) => (k2_xboole_0(k1_tarski(A), B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_zfmisc_1)).
% 2.03/1.22  tff(f_55, axiom, (![A, B]: ~(k2_xboole_0(k1_tarski(A), B) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_zfmisc_1)).
% 2.03/1.22  tff(f_70, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 2.03/1.22  tff(f_76, axiom, (![A, B]: (v1_relat_1(B) => ((k7_relat_1(B, A) = k1_xboole_0) <=> r1_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t95_relat_1)).
% 2.03/1.22  tff(f_79, negated_conjecture, ~(![A]: (k7_relat_1(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t111_relat_1)).
% 2.03/1.22  tff(c_6, plain, (![A_3]: (k4_xboole_0(k1_xboole_0, A_3)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_30])).
% 2.03/1.22  tff(c_10, plain, (![A_4, B_5]: (r1_xboole_0(A_4, B_5) | k4_xboole_0(A_4, B_5)!=A_4)), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.03/1.22  tff(c_36, plain, (![A_40]: (r2_hidden('#skF_1'(A_40), A_40) | v1_relat_1(A_40))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.03/1.22  tff(c_122, plain, (![A_77, B_78]: (k2_xboole_0(k1_tarski(A_77), B_78)=B_78 | ~r2_hidden(A_77, B_78))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.03/1.22  tff(c_28, plain, (![A_36, B_37]: (k2_xboole_0(k1_tarski(A_36), B_37)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.03/1.22  tff(c_146, plain, (![B_81, A_82]: (k1_xboole_0!=B_81 | ~r2_hidden(A_82, B_81))), inference(superposition, [status(thm), theory('equality')], [c_122, c_28])).
% 2.03/1.22  tff(c_151, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_36, c_146])).
% 2.03/1.22  tff(c_40, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.03/1.22  tff(c_191, plain, (![B_91, A_92]: (k7_relat_1(B_91, A_92)=k1_xboole_0 | ~r1_xboole_0(k1_relat_1(B_91), A_92) | ~v1_relat_1(B_91))), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.03/1.22  tff(c_201, plain, (![A_92]: (k7_relat_1(k1_xboole_0, A_92)=k1_xboole_0 | ~r1_xboole_0(k1_xboole_0, A_92) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_40, c_191])).
% 2.03/1.22  tff(c_206, plain, (![A_93]: (k7_relat_1(k1_xboole_0, A_93)=k1_xboole_0 | ~r1_xboole_0(k1_xboole_0, A_93))), inference(demodulation, [status(thm), theory('equality')], [c_151, c_201])).
% 2.03/1.22  tff(c_213, plain, (![B_5]: (k7_relat_1(k1_xboole_0, B_5)=k1_xboole_0 | k4_xboole_0(k1_xboole_0, B_5)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_10, c_206])).
% 2.03/1.22  tff(c_217, plain, (![B_5]: (k7_relat_1(k1_xboole_0, B_5)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_213])).
% 2.03/1.22  tff(c_46, plain, (k7_relat_1(k1_xboole_0, '#skF_4')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.03/1.22  tff(c_223, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_217, c_46])).
% 2.03/1.22  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.03/1.22  
% 2.03/1.22  Inference rules
% 2.03/1.22  ----------------------
% 2.03/1.22  #Ref     : 0
% 2.03/1.22  #Sup     : 40
% 2.03/1.22  #Fact    : 0
% 2.03/1.23  #Define  : 0
% 2.03/1.23  #Split   : 0
% 2.03/1.23  #Chain   : 0
% 2.03/1.23  #Close   : 0
% 2.03/1.23  
% 2.03/1.23  Ordering : KBO
% 2.03/1.23  
% 2.03/1.23  Simplification rules
% 2.03/1.23  ----------------------
% 2.03/1.23  #Subsume      : 0
% 2.03/1.23  #Demod        : 8
% 2.03/1.23  #Tautology    : 32
% 2.03/1.23  #SimpNegUnit  : 0
% 2.03/1.23  #BackRed      : 2
% 2.03/1.23  
% 2.03/1.23  #Partial instantiations: 0
% 2.03/1.23  #Strategies tried      : 1
% 2.03/1.23  
% 2.03/1.23  Timing (in seconds)
% 2.03/1.23  ----------------------
% 2.03/1.23  Preprocessing        : 0.32
% 2.03/1.23  Parsing              : 0.18
% 2.03/1.23  CNF conversion       : 0.02
% 2.03/1.23  Main loop            : 0.14
% 2.03/1.23  Inferencing          : 0.06
% 2.03/1.23  Reduction            : 0.04
% 2.03/1.23  Demodulation         : 0.03
% 2.03/1.23  BG Simplification    : 0.01
% 2.03/1.23  Subsumption          : 0.02
% 2.03/1.23  Abstraction          : 0.01
% 2.03/1.23  MUC search           : 0.00
% 2.03/1.23  Cooper               : 0.00
% 2.03/1.23  Total                : 0.49
% 2.03/1.23  Index Insertion      : 0.00
% 2.03/1.23  Index Deletion       : 0.00
% 2.03/1.23  Index Matching       : 0.00
% 2.03/1.23  BG Taut test         : 0.00
%------------------------------------------------------------------------------
