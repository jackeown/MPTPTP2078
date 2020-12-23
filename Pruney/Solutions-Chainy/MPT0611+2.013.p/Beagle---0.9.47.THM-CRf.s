%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:02:41 EST 2020

% Result     : Theorem 1.88s
% Output     : CNFRefutation 1.88s
% Verified   : 
% Statistics : Number of formulae       :   35 (  44 expanded)
%              Number of leaves         :   17 (  23 expanded)
%              Depth                    :   11
%              Number of atoms          :   43 (  67 expanded)
%              Number of equality atoms :    4 (   6 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > v1_relat_1 > k4_xboole_0 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_relat_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_53,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ! [B] :
            ( v1_relat_1(B)
           => ( r1_xboole_0(k2_relat_1(A),k2_relat_1(B))
             => r1_xboole_0(A,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t215_relat_1)).

tff(f_43,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => r1_tarski(A,k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_relat_1)).

tff(f_39,axiom,(
    ! [A,B,C,D] :
      ( ( r1_xboole_0(A,B)
        | r1_xboole_0(C,D) )
     => r1_xboole_0(k2_zfmisc_1(A,C),k2_zfmisc_1(B,D)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t127_zfmisc_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_33,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_xboole_0(A,k4_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t85_xboole_1)).

tff(c_14,plain,(
    ~ r1_xboole_0('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_20,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_12,plain,(
    ! [A_10] :
      ( r1_tarski(A_10,k2_zfmisc_1(k1_relat_1(A_10),k2_relat_1(A_10)))
      | ~ v1_relat_1(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_18,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_16,plain,(
    r1_xboole_0(k2_relat_1('#skF_1'),k2_relat_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_75,plain,(
    ! [C_25,D_26,A_27,B_28] :
      ( ~ r1_xboole_0(C_25,D_26)
      | r1_xboole_0(k2_zfmisc_1(A_27,C_25),k2_zfmisc_1(B_28,D_26)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( k4_xboole_0(A_1,B_2) = A_1
      | ~ r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_116,plain,(
    ! [A_49,C_50,B_51,D_52] :
      ( k4_xboole_0(k2_zfmisc_1(A_49,C_50),k2_zfmisc_1(B_51,D_52)) = k2_zfmisc_1(A_49,C_50)
      | ~ r1_xboole_0(C_50,D_52) ) ),
    inference(resolution,[status(thm)],[c_75,c_2])).

tff(c_6,plain,(
    ! [A_3,C_5,B_4] :
      ( r1_xboole_0(A_3,k4_xboole_0(C_5,B_4))
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_152,plain,(
    ! [B_63,C_61,A_62,D_65,A_64] :
      ( r1_xboole_0(A_62,k2_zfmisc_1(A_64,C_61))
      | ~ r1_tarski(A_62,k2_zfmisc_1(B_63,D_65))
      | ~ r1_xboole_0(C_61,D_65) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_116,c_6])).

tff(c_156,plain,(
    ! [A_66,A_67,C_68] :
      ( r1_xboole_0(A_66,k2_zfmisc_1(A_67,C_68))
      | ~ r1_xboole_0(C_68,k2_relat_1(A_66))
      | ~ v1_relat_1(A_66) ) ),
    inference(resolution,[status(thm)],[c_12,c_152])).

tff(c_163,plain,(
    ! [A_67] :
      ( r1_xboole_0('#skF_2',k2_zfmisc_1(A_67,k2_relat_1('#skF_1')))
      | ~ v1_relat_1('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_16,c_156])).

tff(c_171,plain,(
    ! [A_69] : r1_xboole_0('#skF_2',k2_zfmisc_1(A_69,k2_relat_1('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_163])).

tff(c_176,plain,(
    ! [A_70] : k4_xboole_0('#skF_2',k2_zfmisc_1(A_70,k2_relat_1('#skF_1'))) = '#skF_2' ),
    inference(resolution,[status(thm)],[c_171,c_2])).

tff(c_198,plain,(
    ! [A_73,A_74] :
      ( r1_xboole_0(A_73,'#skF_2')
      | ~ r1_tarski(A_73,k2_zfmisc_1(A_74,k2_relat_1('#skF_1'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_176,c_6])).

tff(c_202,plain,
    ( r1_xboole_0('#skF_1','#skF_2')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_12,c_198])).

tff(c_205,plain,(
    r1_xboole_0('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_202])).

tff(c_207,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_14,c_205])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n022.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 14:52:40 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.88/1.30  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.88/1.30  
% 1.88/1.30  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.88/1.30  %$ r1_xboole_0 > r1_tarski > v1_relat_1 > k4_xboole_0 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_relat_1 > #skF_2 > #skF_1
% 1.88/1.30  
% 1.88/1.30  %Foreground sorts:
% 1.88/1.30  
% 1.88/1.30  
% 1.88/1.30  %Background operators:
% 1.88/1.30  
% 1.88/1.30  
% 1.88/1.30  %Foreground operators:
% 1.88/1.30  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.88/1.30  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.88/1.30  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.88/1.30  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.88/1.30  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.88/1.30  tff('#skF_2', type, '#skF_2': $i).
% 1.88/1.30  tff('#skF_1', type, '#skF_1': $i).
% 1.88/1.30  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.88/1.30  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.88/1.30  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.88/1.30  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.88/1.30  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.88/1.30  
% 1.88/1.31  tff(f_53, negated_conjecture, ~(![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_xboole_0(k2_relat_1(A), k2_relat_1(B)) => r1_xboole_0(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t215_relat_1)).
% 1.88/1.31  tff(f_43, axiom, (![A]: (v1_relat_1(A) => r1_tarski(A, k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t21_relat_1)).
% 1.88/1.31  tff(f_39, axiom, (![A, B, C, D]: ((r1_xboole_0(A, B) | r1_xboole_0(C, D)) => r1_xboole_0(k2_zfmisc_1(A, C), k2_zfmisc_1(B, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t127_zfmisc_1)).
% 1.88/1.31  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 1.88/1.31  tff(f_33, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_xboole_0(A, k4_xboole_0(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t85_xboole_1)).
% 1.88/1.31  tff(c_14, plain, (~r1_xboole_0('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_53])).
% 1.88/1.31  tff(c_20, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_53])).
% 1.88/1.31  tff(c_12, plain, (![A_10]: (r1_tarski(A_10, k2_zfmisc_1(k1_relat_1(A_10), k2_relat_1(A_10))) | ~v1_relat_1(A_10))), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.88/1.31  tff(c_18, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_53])).
% 1.88/1.31  tff(c_16, plain, (r1_xboole_0(k2_relat_1('#skF_1'), k2_relat_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_53])).
% 1.88/1.31  tff(c_75, plain, (![C_25, D_26, A_27, B_28]: (~r1_xboole_0(C_25, D_26) | r1_xboole_0(k2_zfmisc_1(A_27, C_25), k2_zfmisc_1(B_28, D_26)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.88/1.31  tff(c_2, plain, (![A_1, B_2]: (k4_xboole_0(A_1, B_2)=A_1 | ~r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.88/1.31  tff(c_116, plain, (![A_49, C_50, B_51, D_52]: (k4_xboole_0(k2_zfmisc_1(A_49, C_50), k2_zfmisc_1(B_51, D_52))=k2_zfmisc_1(A_49, C_50) | ~r1_xboole_0(C_50, D_52))), inference(resolution, [status(thm)], [c_75, c_2])).
% 1.88/1.31  tff(c_6, plain, (![A_3, C_5, B_4]: (r1_xboole_0(A_3, k4_xboole_0(C_5, B_4)) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.88/1.31  tff(c_152, plain, (![B_63, C_61, A_62, D_65, A_64]: (r1_xboole_0(A_62, k2_zfmisc_1(A_64, C_61)) | ~r1_tarski(A_62, k2_zfmisc_1(B_63, D_65)) | ~r1_xboole_0(C_61, D_65))), inference(superposition, [status(thm), theory('equality')], [c_116, c_6])).
% 1.88/1.31  tff(c_156, plain, (![A_66, A_67, C_68]: (r1_xboole_0(A_66, k2_zfmisc_1(A_67, C_68)) | ~r1_xboole_0(C_68, k2_relat_1(A_66)) | ~v1_relat_1(A_66))), inference(resolution, [status(thm)], [c_12, c_152])).
% 1.88/1.31  tff(c_163, plain, (![A_67]: (r1_xboole_0('#skF_2', k2_zfmisc_1(A_67, k2_relat_1('#skF_1'))) | ~v1_relat_1('#skF_2'))), inference(resolution, [status(thm)], [c_16, c_156])).
% 1.88/1.31  tff(c_171, plain, (![A_69]: (r1_xboole_0('#skF_2', k2_zfmisc_1(A_69, k2_relat_1('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_163])).
% 1.88/1.31  tff(c_176, plain, (![A_70]: (k4_xboole_0('#skF_2', k2_zfmisc_1(A_70, k2_relat_1('#skF_1')))='#skF_2')), inference(resolution, [status(thm)], [c_171, c_2])).
% 1.88/1.31  tff(c_198, plain, (![A_73, A_74]: (r1_xboole_0(A_73, '#skF_2') | ~r1_tarski(A_73, k2_zfmisc_1(A_74, k2_relat_1('#skF_1'))))), inference(superposition, [status(thm), theory('equality')], [c_176, c_6])).
% 1.88/1.31  tff(c_202, plain, (r1_xboole_0('#skF_1', '#skF_2') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_12, c_198])).
% 1.88/1.31  tff(c_205, plain, (r1_xboole_0('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_20, c_202])).
% 1.88/1.31  tff(c_207, plain, $false, inference(negUnitSimplification, [status(thm)], [c_14, c_205])).
% 1.88/1.31  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.88/1.31  
% 1.88/1.31  Inference rules
% 1.88/1.31  ----------------------
% 1.88/1.31  #Ref     : 0
% 1.88/1.31  #Sup     : 49
% 1.88/1.31  #Fact    : 0
% 1.88/1.31  #Define  : 0
% 1.88/1.31  #Split   : 0
% 1.88/1.31  #Chain   : 0
% 1.88/1.31  #Close   : 0
% 1.88/1.31  
% 1.88/1.31  Ordering : KBO
% 1.88/1.31  
% 1.88/1.31  Simplification rules
% 1.88/1.31  ----------------------
% 1.88/1.31  #Subsume      : 2
% 1.88/1.31  #Demod        : 3
% 1.88/1.31  #Tautology    : 13
% 1.88/1.31  #SimpNegUnit  : 1
% 1.88/1.31  #BackRed      : 0
% 1.88/1.31  
% 1.88/1.31  #Partial instantiations: 0
% 1.88/1.31  #Strategies tried      : 1
% 1.88/1.31  
% 1.88/1.31  Timing (in seconds)
% 1.88/1.31  ----------------------
% 2.12/1.32  Preprocessing        : 0.28
% 2.12/1.32  Parsing              : 0.16
% 2.12/1.32  CNF conversion       : 0.02
% 2.12/1.32  Main loop            : 0.21
% 2.12/1.32  Inferencing          : 0.09
% 2.12/1.32  Reduction            : 0.05
% 2.12/1.32  Demodulation         : 0.03
% 2.12/1.32  BG Simplification    : 0.01
% 2.12/1.32  Subsumption          : 0.04
% 2.12/1.32  Abstraction          : 0.01
% 2.12/1.32  MUC search           : 0.00
% 2.12/1.32  Cooper               : 0.00
% 2.12/1.32  Total                : 0.52
% 2.12/1.32  Index Insertion      : 0.00
% 2.12/1.32  Index Deletion       : 0.00
% 2.12/1.32  Index Matching       : 0.00
% 2.12/1.32  BG Taut test         : 0.00
%------------------------------------------------------------------------------
