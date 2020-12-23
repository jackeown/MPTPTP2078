%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:00:44 EST 2020

% Result     : Theorem 2.17s
% Output     : CNFRefutation 2.17s
% Verified   : 
% Statistics : Number of formulae       :   42 (  48 expanded)
%              Number of leaves         :   24 (  27 expanded)
%              Depth                    :    7
%              Number of atoms          :   45 (  52 expanded)
%              Number of equality atoms :   20 (  24 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > v1_relat_1 > k9_relat_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_62,axiom,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_relat_1)).

tff(f_54,axiom,(
    ! [A] : v1_relat_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).

tff(f_61,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & r2_hidden(C,B) ) )
      & ~ ( ? [C] :
              ( r2_hidden(C,A)
              & r2_hidden(C,B) )
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

tff(f_49,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_52,axiom,(
    ! [A,B] : ~ r2_hidden(A,k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_zfmisc_1)).

tff(f_68,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( k7_relat_1(B,A) = k1_xboole_0
      <=> r1_xboole_0(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_relat_1)).

tff(f_58,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_71,negated_conjecture,(
    ~ ! [A] : k9_relat_1(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t150_relat_1)).

tff(c_24,plain,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_39,plain,(
    ! [A_15] : v1_relat_1(k6_relat_1(A_15)) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_41,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_39])).

tff(c_20,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_10,plain,(
    ! [A_6] : k2_zfmisc_1(A_6,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_68,plain,(
    ! [A_18,B_19] : ~ r2_hidden(A_18,k2_zfmisc_1(A_18,B_19)) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_76,plain,(
    ! [A_22] : ~ r2_hidden(A_22,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_68])).

tff(c_81,plain,(
    ! [B_2] : r1_xboole_0(k1_xboole_0,B_2) ),
    inference(resolution,[status(thm)],[c_6,c_76])).

tff(c_22,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_117,plain,(
    ! [B_34,A_35] :
      ( k7_relat_1(B_34,A_35) = k1_xboole_0
      | ~ r1_xboole_0(k1_relat_1(B_34),A_35)
      | ~ v1_relat_1(B_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_124,plain,(
    ! [A_35] :
      ( k7_relat_1(k1_xboole_0,A_35) = k1_xboole_0
      | ~ r1_xboole_0(k1_xboole_0,A_35)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_117])).

tff(c_141,plain,(
    ! [A_38] : k7_relat_1(k1_xboole_0,A_38) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_41,c_81,c_124])).

tff(c_18,plain,(
    ! [B_12,A_11] :
      ( k2_relat_1(k7_relat_1(B_12,A_11)) = k9_relat_1(B_12,A_11)
      | ~ v1_relat_1(B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_146,plain,(
    ! [A_38] :
      ( k9_relat_1(k1_xboole_0,A_38) = k2_relat_1(k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_141,c_18])).

tff(c_151,plain,(
    ! [A_38] : k9_relat_1(k1_xboole_0,A_38) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_41,c_20,c_146])).

tff(c_30,plain,(
    k9_relat_1(k1_xboole_0,'#skF_2') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_155,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_151,c_30])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n020.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 11:30:37 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.17/1.30  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.17/1.30  
% 2.17/1.30  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.17/1.30  %$ r2_hidden > r1_xboole_0 > v1_relat_1 > k9_relat_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1
% 2.17/1.30  
% 2.17/1.30  %Foreground sorts:
% 2.17/1.30  
% 2.17/1.30  
% 2.17/1.30  %Background operators:
% 2.17/1.30  
% 2.17/1.30  
% 2.17/1.30  %Foreground operators:
% 2.17/1.30  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.17/1.30  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.17/1.30  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.17/1.30  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.17/1.30  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.17/1.30  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.17/1.30  tff('#skF_2', type, '#skF_2': $i).
% 2.17/1.30  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.17/1.30  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.17/1.30  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.17/1.30  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.17/1.30  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 2.17/1.30  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.17/1.30  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.17/1.30  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.17/1.30  
% 2.17/1.31  tff(f_62, axiom, (k6_relat_1(k1_xboole_0) = k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t81_relat_1)).
% 2.17/1.31  tff(f_54, axiom, (![A]: v1_relat_1(k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 2.17/1.31  tff(f_61, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 2.17/1.31  tff(f_43, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 2.17/1.31  tff(f_49, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 2.17/1.31  tff(f_52, axiom, (![A, B]: ~r2_hidden(A, k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t152_zfmisc_1)).
% 2.17/1.31  tff(f_68, axiom, (![A, B]: (v1_relat_1(B) => ((k7_relat_1(B, A) = k1_xboole_0) <=> r1_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t95_relat_1)).
% 2.17/1.31  tff(f_58, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_relat_1)).
% 2.17/1.31  tff(f_71, negated_conjecture, ~(![A]: (k9_relat_1(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t150_relat_1)).
% 2.17/1.31  tff(c_24, plain, (k6_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.17/1.31  tff(c_39, plain, (![A_15]: (v1_relat_1(k6_relat_1(A_15)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.17/1.31  tff(c_41, plain, (v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_24, c_39])).
% 2.17/1.31  tff(c_20, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.17/1.31  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.17/1.31  tff(c_10, plain, (![A_6]: (k2_zfmisc_1(A_6, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.17/1.31  tff(c_68, plain, (![A_18, B_19]: (~r2_hidden(A_18, k2_zfmisc_1(A_18, B_19)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.17/1.31  tff(c_76, plain, (![A_22]: (~r2_hidden(A_22, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_10, c_68])).
% 2.17/1.31  tff(c_81, plain, (![B_2]: (r1_xboole_0(k1_xboole_0, B_2))), inference(resolution, [status(thm)], [c_6, c_76])).
% 2.17/1.31  tff(c_22, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.17/1.31  tff(c_117, plain, (![B_34, A_35]: (k7_relat_1(B_34, A_35)=k1_xboole_0 | ~r1_xboole_0(k1_relat_1(B_34), A_35) | ~v1_relat_1(B_34))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.17/1.31  tff(c_124, plain, (![A_35]: (k7_relat_1(k1_xboole_0, A_35)=k1_xboole_0 | ~r1_xboole_0(k1_xboole_0, A_35) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_22, c_117])).
% 2.17/1.31  tff(c_141, plain, (![A_38]: (k7_relat_1(k1_xboole_0, A_38)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_41, c_81, c_124])).
% 2.17/1.31  tff(c_18, plain, (![B_12, A_11]: (k2_relat_1(k7_relat_1(B_12, A_11))=k9_relat_1(B_12, A_11) | ~v1_relat_1(B_12))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.17/1.31  tff(c_146, plain, (![A_38]: (k9_relat_1(k1_xboole_0, A_38)=k2_relat_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_141, c_18])).
% 2.17/1.31  tff(c_151, plain, (![A_38]: (k9_relat_1(k1_xboole_0, A_38)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_41, c_20, c_146])).
% 2.17/1.31  tff(c_30, plain, (k9_relat_1(k1_xboole_0, '#skF_2')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.17/1.31  tff(c_155, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_151, c_30])).
% 2.17/1.31  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.17/1.31  
% 2.17/1.31  Inference rules
% 2.17/1.31  ----------------------
% 2.17/1.31  #Ref     : 0
% 2.17/1.31  #Sup     : 31
% 2.17/1.32  #Fact    : 0
% 2.17/1.32  #Define  : 0
% 2.17/1.32  #Split   : 0
% 2.17/1.32  #Chain   : 0
% 2.17/1.32  #Close   : 0
% 2.17/1.32  
% 2.17/1.32  Ordering : KBO
% 2.17/1.32  
% 2.17/1.32  Simplification rules
% 2.17/1.32  ----------------------
% 2.17/1.32  #Subsume      : 3
% 2.17/1.32  #Demod        : 7
% 2.17/1.32  #Tautology    : 20
% 2.17/1.32  #SimpNegUnit  : 0
% 2.17/1.32  #BackRed      : 1
% 2.17/1.32  
% 2.17/1.32  #Partial instantiations: 0
% 2.17/1.32  #Strategies tried      : 1
% 2.17/1.32  
% 2.17/1.32  Timing (in seconds)
% 2.17/1.32  ----------------------
% 2.17/1.32  Preprocessing        : 0.34
% 2.17/1.32  Parsing              : 0.20
% 2.17/1.32  CNF conversion       : 0.02
% 2.17/1.32  Main loop            : 0.16
% 2.17/1.32  Inferencing          : 0.07
% 2.17/1.32  Reduction            : 0.04
% 2.17/1.32  Demodulation         : 0.03
% 2.17/1.32  BG Simplification    : 0.01
% 2.17/1.32  Subsumption          : 0.03
% 2.17/1.32  Abstraction          : 0.01
% 2.17/1.32  MUC search           : 0.00
% 2.17/1.32  Cooper               : 0.00
% 2.17/1.32  Total                : 0.53
% 2.17/1.32  Index Insertion      : 0.00
% 2.17/1.32  Index Deletion       : 0.00
% 2.17/1.32  Index Matching       : 0.00
% 2.17/1.32  BG Taut test         : 0.00
%------------------------------------------------------------------------------
