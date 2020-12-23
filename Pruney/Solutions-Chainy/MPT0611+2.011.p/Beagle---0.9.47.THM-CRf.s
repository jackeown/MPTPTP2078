%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:02:41 EST 2020

% Result     : Theorem 1.93s
% Output     : CNFRefutation 1.93s
% Verified   : 
% Statistics : Number of formulae       :   37 (  41 expanded)
%              Number of leaves         :   18 (  22 expanded)
%              Depth                    :    8
%              Number of atoms          :   55 (  69 expanded)
%              Number of equality atoms :    3 (   3 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > v1_relat_1 > k2_zfmisc_1 > k2_xboole_0 > #nlpp > k2_relat_1 > k1_relat_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_71,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ! [B] :
            ( v1_relat_1(B)
           => ( r1_xboole_0(k2_relat_1(A),k2_relat_1(B))
             => r1_xboole_0(A,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t215_relat_1)).

tff(f_61,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => r1_tarski(A,k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_relat_1)).

tff(f_57,axiom,(
    ! [A,B,C,D] :
      ( ( r1_xboole_0(A,B)
        | r1_xboole_0(C,D) )
     => r1_xboole_0(k2_zfmisc_1(A,C),k2_zfmisc_1(B,D)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t127_zfmisc_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_xboole_0(B,C) )
     => r1_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ( ~ ( ~ r1_xboole_0(A,k2_xboole_0(B,C))
          & r1_xboole_0(A,B)
          & r1_xboole_0(A,C) )
      & ~ ( ~ ( r1_xboole_0(A,B)
              & r1_xboole_0(A,C) )
          & r1_xboole_0(A,k2_xboole_0(B,C)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_xboole_1)).

tff(c_18,plain,(
    ~ r1_xboole_0('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_22,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_24,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_20,plain,(
    r1_xboole_0(k2_relat_1('#skF_1'),k2_relat_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_16,plain,(
    ! [A_13] :
      ( r1_tarski(A_13,k2_zfmisc_1(k1_relat_1(A_13),k2_relat_1(A_13)))
      | ~ v1_relat_1(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_41,plain,(
    ! [C_28,D_29,A_30,B_31] :
      ( ~ r1_xboole_0(C_28,D_29)
      | r1_xboole_0(k2_zfmisc_1(A_30,C_28),k2_zfmisc_1(B_31,D_29)) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_4,plain,(
    ! [A_3,C_5,B_4] :
      ( r1_xboole_0(A_3,C_5)
      | ~ r1_xboole_0(B_4,C_5)
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_69,plain,(
    ! [B_47,A_48,C_50,D_46,A_49] :
      ( r1_xboole_0(A_49,k2_zfmisc_1(B_47,D_46))
      | ~ r1_tarski(A_49,k2_zfmisc_1(A_48,C_50))
      | ~ r1_xboole_0(C_50,D_46) ) ),
    inference(resolution,[status(thm)],[c_41,c_4])).

tff(c_82,plain,(
    ! [A_54,B_55,D_56] :
      ( r1_xboole_0(A_54,k2_zfmisc_1(B_55,D_56))
      | ~ r1_xboole_0(k2_relat_1(A_54),D_56)
      | ~ v1_relat_1(A_54) ) ),
    inference(resolution,[status(thm)],[c_16,c_69])).

tff(c_90,plain,(
    ! [B_55] :
      ( r1_xboole_0('#skF_1',k2_zfmisc_1(B_55,k2_relat_1('#skF_2')))
      | ~ v1_relat_1('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_20,c_82])).

tff(c_95,plain,(
    ! [B_55] : r1_xboole_0('#skF_1',k2_zfmisc_1(B_55,k2_relat_1('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_90])).

tff(c_28,plain,(
    ! [A_23] :
      ( r1_tarski(A_23,k2_zfmisc_1(k1_relat_1(A_23),k2_relat_1(A_23)))
      | ~ v1_relat_1(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( k2_xboole_0(A_1,B_2) = B_2
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_144,plain,(
    ! [A_71] :
      ( k2_xboole_0(A_71,k2_zfmisc_1(k1_relat_1(A_71),k2_relat_1(A_71))) = k2_zfmisc_1(k1_relat_1(A_71),k2_relat_1(A_71))
      | ~ v1_relat_1(A_71) ) ),
    inference(resolution,[status(thm)],[c_28,c_2])).

tff(c_10,plain,(
    ! [A_6,B_7,C_8] :
      ( r1_xboole_0(A_6,B_7)
      | ~ r1_xboole_0(A_6,k2_xboole_0(B_7,C_8)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_162,plain,(
    ! [A_72,A_73] :
      ( r1_xboole_0(A_72,A_73)
      | ~ r1_xboole_0(A_72,k2_zfmisc_1(k1_relat_1(A_73),k2_relat_1(A_73)))
      | ~ v1_relat_1(A_73) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_144,c_10])).

tff(c_174,plain,
    ( r1_xboole_0('#skF_1','#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_95,c_162])).

tff(c_191,plain,(
    r1_xboole_0('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_174])).

tff(c_193,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_18,c_191])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.11/0.32  % Computer   : n009.cluster.edu
% 0.11/0.32  % Model      : x86_64 x86_64
% 0.11/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.32  % Memory     : 8042.1875MB
% 0.11/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.32  % CPULimit   : 60
% 0.11/0.32  % DateTime   : Tue Dec  1 14:21:11 EST 2020
% 0.11/0.33  % CPUTime    : 
% 0.11/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.93/1.19  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.93/1.20  
% 1.93/1.20  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.93/1.20  %$ r1_xboole_0 > r1_tarski > v1_relat_1 > k2_zfmisc_1 > k2_xboole_0 > #nlpp > k2_relat_1 > k1_relat_1 > #skF_2 > #skF_1
% 1.93/1.20  
% 1.93/1.20  %Foreground sorts:
% 1.93/1.20  
% 1.93/1.20  
% 1.93/1.20  %Background operators:
% 1.93/1.20  
% 1.93/1.20  
% 1.93/1.20  %Foreground operators:
% 1.93/1.20  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.93/1.20  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.93/1.20  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.93/1.20  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.93/1.20  tff('#skF_2', type, '#skF_2': $i).
% 1.93/1.20  tff('#skF_1', type, '#skF_1': $i).
% 1.93/1.20  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.93/1.20  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.93/1.20  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.93/1.20  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.93/1.20  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.93/1.20  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.93/1.20  
% 1.93/1.21  tff(f_71, negated_conjecture, ~(![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_xboole_0(k2_relat_1(A), k2_relat_1(B)) => r1_xboole_0(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t215_relat_1)).
% 1.93/1.21  tff(f_61, axiom, (![A]: (v1_relat_1(A) => r1_tarski(A, k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t21_relat_1)).
% 1.93/1.21  tff(f_57, axiom, (![A, B, C, D]: ((r1_xboole_0(A, B) | r1_xboole_0(C, D)) => r1_xboole_0(k2_zfmisc_1(A, C), k2_zfmisc_1(B, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t127_zfmisc_1)).
% 1.93/1.21  tff(f_35, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_xboole_0(B, C)) => r1_xboole_0(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t63_xboole_1)).
% 1.93/1.21  tff(f_29, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 1.93/1.21  tff(f_51, axiom, (![A, B, C]: (~((~r1_xboole_0(A, k2_xboole_0(B, C)) & r1_xboole_0(A, B)) & r1_xboole_0(A, C)) & ~(~(r1_xboole_0(A, B) & r1_xboole_0(A, C)) & r1_xboole_0(A, k2_xboole_0(B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_xboole_1)).
% 1.93/1.21  tff(c_18, plain, (~r1_xboole_0('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_71])).
% 1.93/1.21  tff(c_22, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_71])).
% 1.93/1.21  tff(c_24, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_71])).
% 1.93/1.21  tff(c_20, plain, (r1_xboole_0(k2_relat_1('#skF_1'), k2_relat_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_71])).
% 1.93/1.21  tff(c_16, plain, (![A_13]: (r1_tarski(A_13, k2_zfmisc_1(k1_relat_1(A_13), k2_relat_1(A_13))) | ~v1_relat_1(A_13))), inference(cnfTransformation, [status(thm)], [f_61])).
% 1.93/1.21  tff(c_41, plain, (![C_28, D_29, A_30, B_31]: (~r1_xboole_0(C_28, D_29) | r1_xboole_0(k2_zfmisc_1(A_30, C_28), k2_zfmisc_1(B_31, D_29)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 1.93/1.21  tff(c_4, plain, (![A_3, C_5, B_4]: (r1_xboole_0(A_3, C_5) | ~r1_xboole_0(B_4, C_5) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.93/1.21  tff(c_69, plain, (![B_47, A_48, C_50, D_46, A_49]: (r1_xboole_0(A_49, k2_zfmisc_1(B_47, D_46)) | ~r1_tarski(A_49, k2_zfmisc_1(A_48, C_50)) | ~r1_xboole_0(C_50, D_46))), inference(resolution, [status(thm)], [c_41, c_4])).
% 1.93/1.21  tff(c_82, plain, (![A_54, B_55, D_56]: (r1_xboole_0(A_54, k2_zfmisc_1(B_55, D_56)) | ~r1_xboole_0(k2_relat_1(A_54), D_56) | ~v1_relat_1(A_54))), inference(resolution, [status(thm)], [c_16, c_69])).
% 1.93/1.21  tff(c_90, plain, (![B_55]: (r1_xboole_0('#skF_1', k2_zfmisc_1(B_55, k2_relat_1('#skF_2'))) | ~v1_relat_1('#skF_1'))), inference(resolution, [status(thm)], [c_20, c_82])).
% 1.93/1.21  tff(c_95, plain, (![B_55]: (r1_xboole_0('#skF_1', k2_zfmisc_1(B_55, k2_relat_1('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_90])).
% 1.93/1.21  tff(c_28, plain, (![A_23]: (r1_tarski(A_23, k2_zfmisc_1(k1_relat_1(A_23), k2_relat_1(A_23))) | ~v1_relat_1(A_23))), inference(cnfTransformation, [status(thm)], [f_61])).
% 1.93/1.21  tff(c_2, plain, (![A_1, B_2]: (k2_xboole_0(A_1, B_2)=B_2 | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.93/1.21  tff(c_144, plain, (![A_71]: (k2_xboole_0(A_71, k2_zfmisc_1(k1_relat_1(A_71), k2_relat_1(A_71)))=k2_zfmisc_1(k1_relat_1(A_71), k2_relat_1(A_71)) | ~v1_relat_1(A_71))), inference(resolution, [status(thm)], [c_28, c_2])).
% 1.93/1.21  tff(c_10, plain, (![A_6, B_7, C_8]: (r1_xboole_0(A_6, B_7) | ~r1_xboole_0(A_6, k2_xboole_0(B_7, C_8)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 1.93/1.21  tff(c_162, plain, (![A_72, A_73]: (r1_xboole_0(A_72, A_73) | ~r1_xboole_0(A_72, k2_zfmisc_1(k1_relat_1(A_73), k2_relat_1(A_73))) | ~v1_relat_1(A_73))), inference(superposition, [status(thm), theory('equality')], [c_144, c_10])).
% 1.93/1.21  tff(c_174, plain, (r1_xboole_0('#skF_1', '#skF_2') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_95, c_162])).
% 1.93/1.21  tff(c_191, plain, (r1_xboole_0('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_22, c_174])).
% 1.93/1.21  tff(c_193, plain, $false, inference(negUnitSimplification, [status(thm)], [c_18, c_191])).
% 1.93/1.21  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.93/1.21  
% 1.93/1.21  Inference rules
% 1.93/1.21  ----------------------
% 1.93/1.21  #Ref     : 0
% 1.93/1.21  #Sup     : 38
% 1.93/1.21  #Fact    : 0
% 1.93/1.21  #Define  : 0
% 1.93/1.21  #Split   : 0
% 1.93/1.21  #Chain   : 0
% 1.93/1.21  #Close   : 0
% 1.93/1.21  
% 1.93/1.21  Ordering : KBO
% 1.93/1.21  
% 1.93/1.21  Simplification rules
% 1.93/1.21  ----------------------
% 1.93/1.21  #Subsume      : 0
% 1.93/1.21  #Demod        : 4
% 1.93/1.21  #Tautology    : 6
% 1.93/1.21  #SimpNegUnit  : 1
% 1.93/1.21  #BackRed      : 0
% 1.93/1.21  
% 1.93/1.21  #Partial instantiations: 0
% 1.93/1.21  #Strategies tried      : 1
% 1.93/1.21  
% 1.93/1.21  Timing (in seconds)
% 1.93/1.21  ----------------------
% 1.93/1.21  Preprocessing        : 0.27
% 1.93/1.21  Parsing              : 0.15
% 1.93/1.21  CNF conversion       : 0.02
% 1.93/1.21  Main loop            : 0.20
% 1.93/1.21  Inferencing          : 0.08
% 1.93/1.21  Reduction            : 0.04
% 1.93/1.21  Demodulation         : 0.03
% 1.93/1.21  BG Simplification    : 0.01
% 1.93/1.21  Subsumption          : 0.05
% 1.93/1.21  Abstraction          : 0.01
% 1.93/1.21  MUC search           : 0.00
% 1.93/1.21  Cooper               : 0.00
% 1.93/1.21  Total                : 0.49
% 1.93/1.21  Index Insertion      : 0.00
% 1.93/1.21  Index Deletion       : 0.00
% 1.93/1.21  Index Matching       : 0.00
% 1.93/1.21  BG Taut test         : 0.00
%------------------------------------------------------------------------------
