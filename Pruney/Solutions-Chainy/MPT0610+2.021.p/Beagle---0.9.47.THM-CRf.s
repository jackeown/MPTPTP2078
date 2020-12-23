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
% DateTime   : Thu Dec  3 10:02:39 EST 2020

% Result     : Theorem 2.00s
% Output     : CNFRefutation 2.00s
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
           => ( r1_xboole_0(k1_relat_1(A),k1_relat_1(B))
             => r1_xboole_0(A,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t214_relat_1)).

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
    r1_xboole_0(k1_relat_1('#skF_1'),k1_relat_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_16,plain,(
    ! [A_13] :
      ( r1_tarski(A_13,k2_zfmisc_1(k1_relat_1(A_13),k2_relat_1(A_13)))
      | ~ v1_relat_1(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_45,plain,(
    ! [A_32,B_33,C_34,D_35] :
      ( ~ r1_xboole_0(A_32,B_33)
      | r1_xboole_0(k2_zfmisc_1(A_32,C_34),k2_zfmisc_1(B_33,D_35)) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_4,plain,(
    ! [A_3,C_5,B_4] :
      ( r1_xboole_0(A_3,C_5)
      | ~ r1_xboole_0(B_4,C_5)
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_65,plain,(
    ! [C_42,D_45,A_44,A_43,B_41] :
      ( r1_xboole_0(A_44,k2_zfmisc_1(B_41,D_45))
      | ~ r1_tarski(A_44,k2_zfmisc_1(A_43,C_42))
      | ~ r1_xboole_0(A_43,B_41) ) ),
    inference(resolution,[status(thm)],[c_45,c_4])).

tff(c_73,plain,(
    ! [A_51,B_52,D_53] :
      ( r1_xboole_0(A_51,k2_zfmisc_1(B_52,D_53))
      | ~ r1_xboole_0(k1_relat_1(A_51),B_52)
      | ~ v1_relat_1(A_51) ) ),
    inference(resolution,[status(thm)],[c_16,c_65])).

tff(c_81,plain,(
    ! [D_53] :
      ( r1_xboole_0('#skF_1',k2_zfmisc_1(k1_relat_1('#skF_2'),D_53))
      | ~ v1_relat_1('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_20,c_73])).

tff(c_86,plain,(
    ! [D_53] : r1_xboole_0('#skF_1',k2_zfmisc_1(k1_relat_1('#skF_2'),D_53)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_81])).

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
    inference(resolution,[status(thm)],[c_86,c_162])).

tff(c_191,plain,(
    r1_xboole_0('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_174])).

tff(c_193,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_18,c_191])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n003.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 16:45:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.00/1.20  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.00/1.20  
% 2.00/1.20  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.00/1.20  %$ r1_xboole_0 > r1_tarski > v1_relat_1 > k2_zfmisc_1 > k2_xboole_0 > #nlpp > k2_relat_1 > k1_relat_1 > #skF_2 > #skF_1
% 2.00/1.20  
% 2.00/1.20  %Foreground sorts:
% 2.00/1.20  
% 2.00/1.20  
% 2.00/1.20  %Background operators:
% 2.00/1.20  
% 2.00/1.20  
% 2.00/1.20  %Foreground operators:
% 2.00/1.20  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.00/1.20  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.00/1.20  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.00/1.20  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.00/1.20  tff('#skF_2', type, '#skF_2': $i).
% 2.00/1.20  tff('#skF_1', type, '#skF_1': $i).
% 2.00/1.20  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.00/1.20  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.00/1.20  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.00/1.20  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.00/1.20  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.00/1.20  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.00/1.20  
% 2.00/1.21  tff(f_71, negated_conjecture, ~(![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_xboole_0(k1_relat_1(A), k1_relat_1(B)) => r1_xboole_0(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t214_relat_1)).
% 2.00/1.21  tff(f_61, axiom, (![A]: (v1_relat_1(A) => r1_tarski(A, k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t21_relat_1)).
% 2.00/1.21  tff(f_57, axiom, (![A, B, C, D]: ((r1_xboole_0(A, B) | r1_xboole_0(C, D)) => r1_xboole_0(k2_zfmisc_1(A, C), k2_zfmisc_1(B, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t127_zfmisc_1)).
% 2.00/1.21  tff(f_35, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_xboole_0(B, C)) => r1_xboole_0(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t63_xboole_1)).
% 2.00/1.21  tff(f_29, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 2.00/1.21  tff(f_51, axiom, (![A, B, C]: (~((~r1_xboole_0(A, k2_xboole_0(B, C)) & r1_xboole_0(A, B)) & r1_xboole_0(A, C)) & ~(~(r1_xboole_0(A, B) & r1_xboole_0(A, C)) & r1_xboole_0(A, k2_xboole_0(B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_xboole_1)).
% 2.00/1.21  tff(c_18, plain, (~r1_xboole_0('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.00/1.21  tff(c_22, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.00/1.21  tff(c_24, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.00/1.21  tff(c_20, plain, (r1_xboole_0(k1_relat_1('#skF_1'), k1_relat_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.00/1.21  tff(c_16, plain, (![A_13]: (r1_tarski(A_13, k2_zfmisc_1(k1_relat_1(A_13), k2_relat_1(A_13))) | ~v1_relat_1(A_13))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.00/1.21  tff(c_45, plain, (![A_32, B_33, C_34, D_35]: (~r1_xboole_0(A_32, B_33) | r1_xboole_0(k2_zfmisc_1(A_32, C_34), k2_zfmisc_1(B_33, D_35)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.00/1.21  tff(c_4, plain, (![A_3, C_5, B_4]: (r1_xboole_0(A_3, C_5) | ~r1_xboole_0(B_4, C_5) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.00/1.21  tff(c_65, plain, (![C_42, D_45, A_44, A_43, B_41]: (r1_xboole_0(A_44, k2_zfmisc_1(B_41, D_45)) | ~r1_tarski(A_44, k2_zfmisc_1(A_43, C_42)) | ~r1_xboole_0(A_43, B_41))), inference(resolution, [status(thm)], [c_45, c_4])).
% 2.00/1.21  tff(c_73, plain, (![A_51, B_52, D_53]: (r1_xboole_0(A_51, k2_zfmisc_1(B_52, D_53)) | ~r1_xboole_0(k1_relat_1(A_51), B_52) | ~v1_relat_1(A_51))), inference(resolution, [status(thm)], [c_16, c_65])).
% 2.00/1.21  tff(c_81, plain, (![D_53]: (r1_xboole_0('#skF_1', k2_zfmisc_1(k1_relat_1('#skF_2'), D_53)) | ~v1_relat_1('#skF_1'))), inference(resolution, [status(thm)], [c_20, c_73])).
% 2.00/1.21  tff(c_86, plain, (![D_53]: (r1_xboole_0('#skF_1', k2_zfmisc_1(k1_relat_1('#skF_2'), D_53)))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_81])).
% 2.00/1.21  tff(c_28, plain, (![A_23]: (r1_tarski(A_23, k2_zfmisc_1(k1_relat_1(A_23), k2_relat_1(A_23))) | ~v1_relat_1(A_23))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.00/1.21  tff(c_2, plain, (![A_1, B_2]: (k2_xboole_0(A_1, B_2)=B_2 | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.00/1.21  tff(c_144, plain, (![A_71]: (k2_xboole_0(A_71, k2_zfmisc_1(k1_relat_1(A_71), k2_relat_1(A_71)))=k2_zfmisc_1(k1_relat_1(A_71), k2_relat_1(A_71)) | ~v1_relat_1(A_71))), inference(resolution, [status(thm)], [c_28, c_2])).
% 2.00/1.21  tff(c_10, plain, (![A_6, B_7, C_8]: (r1_xboole_0(A_6, B_7) | ~r1_xboole_0(A_6, k2_xboole_0(B_7, C_8)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.00/1.21  tff(c_162, plain, (![A_72, A_73]: (r1_xboole_0(A_72, A_73) | ~r1_xboole_0(A_72, k2_zfmisc_1(k1_relat_1(A_73), k2_relat_1(A_73))) | ~v1_relat_1(A_73))), inference(superposition, [status(thm), theory('equality')], [c_144, c_10])).
% 2.00/1.21  tff(c_174, plain, (r1_xboole_0('#skF_1', '#skF_2') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_86, c_162])).
% 2.00/1.21  tff(c_191, plain, (r1_xboole_0('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_22, c_174])).
% 2.00/1.21  tff(c_193, plain, $false, inference(negUnitSimplification, [status(thm)], [c_18, c_191])).
% 2.00/1.21  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.00/1.21  
% 2.00/1.21  Inference rules
% 2.00/1.21  ----------------------
% 2.00/1.21  #Ref     : 0
% 2.00/1.21  #Sup     : 38
% 2.00/1.21  #Fact    : 0
% 2.00/1.21  #Define  : 0
% 2.00/1.21  #Split   : 0
% 2.00/1.21  #Chain   : 0
% 2.00/1.21  #Close   : 0
% 2.00/1.21  
% 2.00/1.21  Ordering : KBO
% 2.00/1.21  
% 2.00/1.21  Simplification rules
% 2.00/1.21  ----------------------
% 2.00/1.21  #Subsume      : 0
% 2.00/1.21  #Demod        : 4
% 2.00/1.21  #Tautology    : 6
% 2.00/1.21  #SimpNegUnit  : 1
% 2.00/1.21  #BackRed      : 0
% 2.00/1.21  
% 2.00/1.21  #Partial instantiations: 0
% 2.00/1.21  #Strategies tried      : 1
% 2.00/1.21  
% 2.00/1.21  Timing (in seconds)
% 2.00/1.21  ----------------------
% 2.00/1.22  Preprocessing        : 0.26
% 2.00/1.22  Parsing              : 0.15
% 2.00/1.22  CNF conversion       : 0.02
% 2.00/1.22  Main loop            : 0.20
% 2.00/1.22  Inferencing          : 0.08
% 2.00/1.22  Reduction            : 0.05
% 2.00/1.22  Demodulation         : 0.03
% 2.00/1.22  BG Simplification    : 0.01
% 2.00/1.22  Subsumption          : 0.05
% 2.00/1.22  Abstraction          : 0.01
% 2.00/1.22  MUC search           : 0.00
% 2.00/1.22  Cooper               : 0.00
% 2.00/1.22  Total                : 0.49
% 2.00/1.22  Index Insertion      : 0.00
% 2.12/1.22  Index Deletion       : 0.00
% 2.12/1.22  Index Matching       : 0.00
% 2.12/1.22  BG Taut test         : 0.00
%------------------------------------------------------------------------------
