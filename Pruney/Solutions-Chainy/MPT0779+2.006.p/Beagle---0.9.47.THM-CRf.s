%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:06:39 EST 2020

% Result     : Theorem 1.83s
% Output     : CNFRefutation 1.83s
% Verified   : 
% Statistics : Number of formulae       :   36 (  44 expanded)
%              Number of leaves         :   20 (  25 expanded)
%              Depth                    :    6
%              Number of atoms          :   35 (  60 expanded)
%              Number of equality atoms :   19 (  30 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v1_relat_1 > v1_funct_1 > k7_relat_1 > k3_xboole_0 > k2_wellord1 > k1_funct_1 > #nlpp > o_1_0_funct_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(o_1_0_funct_1,type,(
    o_1_0_funct_1: $i > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_wellord1,type,(
    k2_wellord1: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_45,axiom,(
    ! [A,B] :
    ? [C] :
      ( v1_relat_1(C)
      & v1_funct_1(C)
      & k1_relat_1(C) = B
      & ! [D] :
          ( r2_hidden(D,B)
         => k1_funct_1(C,D) = o_1_0_funct_1(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',s3_funct_1__e1_27_1__funct_1)).

tff(f_33,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k7_relat_1(A,k1_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_relat_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k1_relat_1(k7_relat_1(B,A)) = k3_xboole_0(k1_relat_1(B),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t90_relat_1)).

tff(f_54,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => k2_wellord1(k2_wellord1(B,A),A) = k2_wellord1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_wellord1)).

tff(f_49,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k2_wellord1(k2_wellord1(C,A),B) = k2_wellord1(C,k3_xboole_0(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_wellord1)).

tff(c_8,plain,(
    ! [A_4,B_5] : k1_relat_1('#skF_1'(A_4,B_5)) = B_5 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_12,plain,(
    ! [A_4,B_5] : v1_relat_1('#skF_1'(A_4,B_5)) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_30,plain,(
    ! [A_20] :
      ( k7_relat_1(A_20,k1_relat_1(A_20)) = A_20
      | ~ v1_relat_1(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_39,plain,(
    ! [A_4,B_5] :
      ( k7_relat_1('#skF_1'(A_4,B_5),B_5) = '#skF_1'(A_4,B_5)
      | ~ v1_relat_1('#skF_1'(A_4,B_5)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_30])).

tff(c_43,plain,(
    ! [A_4,B_5] : k7_relat_1('#skF_1'(A_4,B_5),B_5) = '#skF_1'(A_4,B_5) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_39])).

tff(c_62,plain,(
    ! [B_26,A_27] :
      ( k3_xboole_0(k1_relat_1(B_26),A_27) = k1_relat_1(k7_relat_1(B_26,A_27))
      | ~ v1_relat_1(B_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_71,plain,(
    ! [A_4,B_5,A_27] :
      ( k1_relat_1(k7_relat_1('#skF_1'(A_4,B_5),A_27)) = k3_xboole_0(B_5,A_27)
      | ~ v1_relat_1('#skF_1'(A_4,B_5)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_62])).

tff(c_96,plain,(
    ! [A_31,B_32,A_33] : k1_relat_1(k7_relat_1('#skF_1'(A_31,B_32),A_33)) = k3_xboole_0(B_32,A_33) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_71])).

tff(c_111,plain,(
    ! [B_5,A_4] : k3_xboole_0(B_5,B_5) = k1_relat_1('#skF_1'(A_4,B_5)) ),
    inference(superposition,[status(thm),theory(equality)],[c_43,c_96])).

tff(c_118,plain,(
    ! [B_5] : k3_xboole_0(B_5,B_5) = B_5 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_111])).

tff(c_18,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_76,plain,(
    ! [C_28,A_29,B_30] :
      ( k2_wellord1(k2_wellord1(C_28,A_29),B_30) = k2_wellord1(C_28,k3_xboole_0(A_29,B_30))
      | ~ v1_relat_1(C_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_16,plain,(
    k2_wellord1(k2_wellord1('#skF_3','#skF_2'),'#skF_2') != k2_wellord1('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_85,plain,
    ( k2_wellord1('#skF_3',k3_xboole_0('#skF_2','#skF_2')) != k2_wellord1('#skF_3','#skF_2')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_76,c_16])).

tff(c_94,plain,(
    k2_wellord1('#skF_3',k3_xboole_0('#skF_2','#skF_2')) != k2_wellord1('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_85])).

tff(c_123,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_118,c_94])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n014.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 20:15:22 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.83/1.16  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.83/1.17  
% 1.83/1.17  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.83/1.17  %$ r2_hidden > v1_relat_1 > v1_funct_1 > k7_relat_1 > k3_xboole_0 > k2_wellord1 > k1_funct_1 > #nlpp > o_1_0_funct_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 1.83/1.17  
% 1.83/1.17  %Foreground sorts:
% 1.83/1.17  
% 1.83/1.17  
% 1.83/1.17  %Background operators:
% 1.83/1.17  
% 1.83/1.17  
% 1.83/1.17  %Foreground operators:
% 1.83/1.17  tff(o_1_0_funct_1, type, o_1_0_funct_1: $i > $i).
% 1.83/1.17  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 1.83/1.17  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.83/1.17  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.83/1.17  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 1.83/1.17  tff('#skF_2', type, '#skF_2': $i).
% 1.83/1.17  tff('#skF_3', type, '#skF_3': $i).
% 1.83/1.17  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 1.83/1.17  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.83/1.17  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.83/1.17  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.83/1.17  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.83/1.17  tff(k2_wellord1, type, k2_wellord1: ($i * $i) > $i).
% 1.83/1.17  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.83/1.17  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.83/1.17  
% 1.83/1.18  tff(f_45, axiom, (![A, B]: (?[C]: (((v1_relat_1(C) & v1_funct_1(C)) & (k1_relat_1(C) = B)) & (![D]: (r2_hidden(D, B) => (k1_funct_1(C, D) = o_1_0_funct_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', s3_funct_1__e1_27_1__funct_1)).
% 1.83/1.18  tff(f_33, axiom, (![A]: (v1_relat_1(A) => (k7_relat_1(A, k1_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_relat_1)).
% 1.83/1.18  tff(f_29, axiom, (![A, B]: (v1_relat_1(B) => (k1_relat_1(k7_relat_1(B, A)) = k3_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t90_relat_1)).
% 1.83/1.18  tff(f_54, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => (k2_wellord1(k2_wellord1(B, A), A) = k2_wellord1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_wellord1)).
% 1.83/1.18  tff(f_49, axiom, (![A, B, C]: (v1_relat_1(C) => (k2_wellord1(k2_wellord1(C, A), B) = k2_wellord1(C, k3_xboole_0(A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t26_wellord1)).
% 1.83/1.18  tff(c_8, plain, (![A_4, B_5]: (k1_relat_1('#skF_1'(A_4, B_5))=B_5)), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.83/1.18  tff(c_12, plain, (![A_4, B_5]: (v1_relat_1('#skF_1'(A_4, B_5)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.83/1.18  tff(c_30, plain, (![A_20]: (k7_relat_1(A_20, k1_relat_1(A_20))=A_20 | ~v1_relat_1(A_20))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.83/1.18  tff(c_39, plain, (![A_4, B_5]: (k7_relat_1('#skF_1'(A_4, B_5), B_5)='#skF_1'(A_4, B_5) | ~v1_relat_1('#skF_1'(A_4, B_5)))), inference(superposition, [status(thm), theory('equality')], [c_8, c_30])).
% 1.83/1.18  tff(c_43, plain, (![A_4, B_5]: (k7_relat_1('#skF_1'(A_4, B_5), B_5)='#skF_1'(A_4, B_5))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_39])).
% 1.83/1.18  tff(c_62, plain, (![B_26, A_27]: (k3_xboole_0(k1_relat_1(B_26), A_27)=k1_relat_1(k7_relat_1(B_26, A_27)) | ~v1_relat_1(B_26))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.83/1.18  tff(c_71, plain, (![A_4, B_5, A_27]: (k1_relat_1(k7_relat_1('#skF_1'(A_4, B_5), A_27))=k3_xboole_0(B_5, A_27) | ~v1_relat_1('#skF_1'(A_4, B_5)))), inference(superposition, [status(thm), theory('equality')], [c_8, c_62])).
% 1.83/1.18  tff(c_96, plain, (![A_31, B_32, A_33]: (k1_relat_1(k7_relat_1('#skF_1'(A_31, B_32), A_33))=k3_xboole_0(B_32, A_33))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_71])).
% 1.83/1.18  tff(c_111, plain, (![B_5, A_4]: (k3_xboole_0(B_5, B_5)=k1_relat_1('#skF_1'(A_4, B_5)))), inference(superposition, [status(thm), theory('equality')], [c_43, c_96])).
% 1.83/1.18  tff(c_118, plain, (![B_5]: (k3_xboole_0(B_5, B_5)=B_5)), inference(demodulation, [status(thm), theory('equality')], [c_8, c_111])).
% 1.83/1.18  tff(c_18, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_54])).
% 1.83/1.18  tff(c_76, plain, (![C_28, A_29, B_30]: (k2_wellord1(k2_wellord1(C_28, A_29), B_30)=k2_wellord1(C_28, k3_xboole_0(A_29, B_30)) | ~v1_relat_1(C_28))), inference(cnfTransformation, [status(thm)], [f_49])).
% 1.83/1.18  tff(c_16, plain, (k2_wellord1(k2_wellord1('#skF_3', '#skF_2'), '#skF_2')!=k2_wellord1('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_54])).
% 1.83/1.18  tff(c_85, plain, (k2_wellord1('#skF_3', k3_xboole_0('#skF_2', '#skF_2'))!=k2_wellord1('#skF_3', '#skF_2') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_76, c_16])).
% 1.83/1.18  tff(c_94, plain, (k2_wellord1('#skF_3', k3_xboole_0('#skF_2', '#skF_2'))!=k2_wellord1('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_18, c_85])).
% 1.83/1.18  tff(c_123, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_118, c_94])).
% 1.83/1.18  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.83/1.18  
% 1.83/1.18  Inference rules
% 1.83/1.18  ----------------------
% 1.83/1.18  #Ref     : 0
% 1.83/1.18  #Sup     : 23
% 1.83/1.18  #Fact    : 0
% 1.83/1.18  #Define  : 0
% 1.83/1.18  #Split   : 0
% 1.83/1.18  #Chain   : 0
% 1.83/1.18  #Close   : 0
% 1.83/1.18  
% 1.83/1.18  Ordering : KBO
% 1.83/1.18  
% 1.83/1.18  Simplification rules
% 1.83/1.18  ----------------------
% 1.83/1.18  #Subsume      : 0
% 1.83/1.18  #Demod        : 8
% 1.83/1.18  #Tautology    : 14
% 1.83/1.18  #SimpNegUnit  : 0
% 1.83/1.18  #BackRed      : 1
% 1.83/1.18  
% 1.83/1.18  #Partial instantiations: 0
% 1.83/1.18  #Strategies tried      : 1
% 1.83/1.18  
% 1.83/1.18  Timing (in seconds)
% 1.83/1.18  ----------------------
% 1.83/1.18  Preprocessing        : 0.30
% 1.83/1.18  Parsing              : 0.15
% 1.83/1.18  CNF conversion       : 0.02
% 1.83/1.18  Main loop            : 0.11
% 1.83/1.18  Inferencing          : 0.05
% 1.83/1.18  Reduction            : 0.03
% 1.83/1.18  Demodulation         : 0.02
% 1.83/1.18  BG Simplification    : 0.01
% 1.83/1.18  Subsumption          : 0.01
% 1.83/1.18  Abstraction          : 0.01
% 1.83/1.18  MUC search           : 0.00
% 1.83/1.18  Cooper               : 0.00
% 1.83/1.18  Total                : 0.43
% 1.83/1.18  Index Insertion      : 0.00
% 1.83/1.18  Index Deletion       : 0.00
% 1.83/1.18  Index Matching       : 0.00
% 1.83/1.18  BG Taut test         : 0.00
%------------------------------------------------------------------------------
