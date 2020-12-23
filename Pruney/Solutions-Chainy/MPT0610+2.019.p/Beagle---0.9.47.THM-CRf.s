%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:02:39 EST 2020

% Result     : Theorem 2.54s
% Output     : CNFRefutation 2.54s
% Verified   : 
% Statistics : Number of formulae       :   34 (  43 expanded)
%              Number of leaves         :   16 (  22 expanded)
%              Depth                    :   11
%              Number of atoms          :   44 (  70 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > v1_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_relat_1 > #skF_2 > #skF_1

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_55,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ! [B] :
            ( v1_relat_1(B)
           => ( r1_xboole_0(k1_relat_1(A),k1_relat_1(B))
             => r1_xboole_0(A,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t214_relat_1)).

tff(f_45,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => r1_tarski(A,k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_relat_1)).

tff(f_41,axiom,(
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
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(c_12,plain,(
    ~ r1_xboole_0('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_16,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_10,plain,(
    ! [A_10] :
      ( r1_tarski(A_10,k2_zfmisc_1(k1_relat_1(A_10),k2_relat_1(A_10)))
      | ~ v1_relat_1(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_18,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_14,plain,(
    r1_xboole_0(k1_relat_1('#skF_1'),k1_relat_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_63,plain,(
    ! [A_22,B_23,C_24,D_25] :
      ( ~ r1_xboole_0(A_22,B_23)
      | r1_xboole_0(k2_zfmisc_1(A_22,C_24),k2_zfmisc_1(B_23,D_25)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_4,plain,(
    ! [A_3,C_5,B_4] :
      ( r1_xboole_0(A_3,C_5)
      | ~ r1_xboole_0(B_4,C_5)
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_115,plain,(
    ! [A_57,B_59,C_56,A_55,D_58] :
      ( r1_xboole_0(A_57,k2_zfmisc_1(B_59,D_58))
      | ~ r1_tarski(A_57,k2_zfmisc_1(A_55,C_56))
      | ~ r1_xboole_0(A_55,B_59) ) ),
    inference(resolution,[status(thm)],[c_63,c_4])).

tff(c_119,plain,(
    ! [A_60,B_61,D_62] :
      ( r1_xboole_0(A_60,k2_zfmisc_1(B_61,D_62))
      | ~ r1_xboole_0(k1_relat_1(A_60),B_61)
      | ~ v1_relat_1(A_60) ) ),
    inference(resolution,[status(thm)],[c_10,c_115])).

tff(c_133,plain,(
    ! [D_62] :
      ( r1_xboole_0('#skF_1',k2_zfmisc_1(k1_relat_1('#skF_2'),D_62))
      | ~ v1_relat_1('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_14,c_119])).

tff(c_159,plain,(
    ! [D_69] : r1_xboole_0('#skF_1',k2_zfmisc_1(k1_relat_1('#skF_2'),D_69)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_133])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( r1_xboole_0(B_2,A_1)
      | ~ r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_189,plain,(
    ! [D_73] : r1_xboole_0(k2_zfmisc_1(k1_relat_1('#skF_2'),D_73),'#skF_1') ),
    inference(resolution,[status(thm)],[c_159,c_2])).

tff(c_281,plain,(
    ! [A_95,D_96] :
      ( r1_xboole_0(A_95,'#skF_1')
      | ~ r1_tarski(A_95,k2_zfmisc_1(k1_relat_1('#skF_2'),D_96)) ) ),
    inference(resolution,[status(thm)],[c_189,c_4])).

tff(c_285,plain,
    ( r1_xboole_0('#skF_2','#skF_1')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_10,c_281])).

tff(c_288,plain,(
    r1_xboole_0('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_285])).

tff(c_292,plain,(
    r1_xboole_0('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_288,c_2])).

tff(c_297,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_12,c_292])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n005.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 17:05:32 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.54/1.40  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.54/1.40  
% 2.54/1.40  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.54/1.40  %$ r1_xboole_0 > r1_tarski > v1_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_relat_1 > #skF_2 > #skF_1
% 2.54/1.40  
% 2.54/1.40  %Foreground sorts:
% 2.54/1.40  
% 2.54/1.40  
% 2.54/1.40  %Background operators:
% 2.54/1.40  
% 2.54/1.40  
% 2.54/1.40  %Foreground operators:
% 2.54/1.40  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.54/1.40  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.54/1.40  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.54/1.40  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.54/1.40  tff('#skF_2', type, '#skF_2': $i).
% 2.54/1.40  tff('#skF_1', type, '#skF_1': $i).
% 2.54/1.40  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.54/1.40  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.54/1.40  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.54/1.40  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.54/1.40  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.54/1.40  
% 2.54/1.41  tff(f_55, negated_conjecture, ~(![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_xboole_0(k1_relat_1(A), k1_relat_1(B)) => r1_xboole_0(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t214_relat_1)).
% 2.54/1.41  tff(f_45, axiom, (![A]: (v1_relat_1(A) => r1_tarski(A, k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t21_relat_1)).
% 2.54/1.41  tff(f_41, axiom, (![A, B, C, D]: ((r1_xboole_0(A, B) | r1_xboole_0(C, D)) => r1_xboole_0(k2_zfmisc_1(A, C), k2_zfmisc_1(B, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t127_zfmisc_1)).
% 2.54/1.41  tff(f_35, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_xboole_0(B, C)) => r1_xboole_0(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t63_xboole_1)).
% 2.54/1.41  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 2.54/1.41  tff(c_12, plain, (~r1_xboole_0('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.54/1.41  tff(c_16, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.54/1.41  tff(c_10, plain, (![A_10]: (r1_tarski(A_10, k2_zfmisc_1(k1_relat_1(A_10), k2_relat_1(A_10))) | ~v1_relat_1(A_10))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.54/1.41  tff(c_18, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.54/1.41  tff(c_14, plain, (r1_xboole_0(k1_relat_1('#skF_1'), k1_relat_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.54/1.41  tff(c_63, plain, (![A_22, B_23, C_24, D_25]: (~r1_xboole_0(A_22, B_23) | r1_xboole_0(k2_zfmisc_1(A_22, C_24), k2_zfmisc_1(B_23, D_25)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.54/1.41  tff(c_4, plain, (![A_3, C_5, B_4]: (r1_xboole_0(A_3, C_5) | ~r1_xboole_0(B_4, C_5) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.54/1.41  tff(c_115, plain, (![A_57, B_59, C_56, A_55, D_58]: (r1_xboole_0(A_57, k2_zfmisc_1(B_59, D_58)) | ~r1_tarski(A_57, k2_zfmisc_1(A_55, C_56)) | ~r1_xboole_0(A_55, B_59))), inference(resolution, [status(thm)], [c_63, c_4])).
% 2.54/1.41  tff(c_119, plain, (![A_60, B_61, D_62]: (r1_xboole_0(A_60, k2_zfmisc_1(B_61, D_62)) | ~r1_xboole_0(k1_relat_1(A_60), B_61) | ~v1_relat_1(A_60))), inference(resolution, [status(thm)], [c_10, c_115])).
% 2.54/1.41  tff(c_133, plain, (![D_62]: (r1_xboole_0('#skF_1', k2_zfmisc_1(k1_relat_1('#skF_2'), D_62)) | ~v1_relat_1('#skF_1'))), inference(resolution, [status(thm)], [c_14, c_119])).
% 2.54/1.41  tff(c_159, plain, (![D_69]: (r1_xboole_0('#skF_1', k2_zfmisc_1(k1_relat_1('#skF_2'), D_69)))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_133])).
% 2.54/1.41  tff(c_2, plain, (![B_2, A_1]: (r1_xboole_0(B_2, A_1) | ~r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.54/1.41  tff(c_189, plain, (![D_73]: (r1_xboole_0(k2_zfmisc_1(k1_relat_1('#skF_2'), D_73), '#skF_1'))), inference(resolution, [status(thm)], [c_159, c_2])).
% 2.54/1.41  tff(c_281, plain, (![A_95, D_96]: (r1_xboole_0(A_95, '#skF_1') | ~r1_tarski(A_95, k2_zfmisc_1(k1_relat_1('#skF_2'), D_96)))), inference(resolution, [status(thm)], [c_189, c_4])).
% 2.54/1.42  tff(c_285, plain, (r1_xboole_0('#skF_2', '#skF_1') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_10, c_281])).
% 2.54/1.42  tff(c_288, plain, (r1_xboole_0('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_16, c_285])).
% 2.54/1.42  tff(c_292, plain, (r1_xboole_0('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_288, c_2])).
% 2.54/1.42  tff(c_297, plain, $false, inference(negUnitSimplification, [status(thm)], [c_12, c_292])).
% 2.54/1.42  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.54/1.42  
% 2.54/1.42  Inference rules
% 2.54/1.42  ----------------------
% 2.54/1.42  #Ref     : 0
% 2.54/1.42  #Sup     : 71
% 2.54/1.42  #Fact    : 0
% 2.54/1.42  #Define  : 0
% 2.54/1.42  #Split   : 0
% 2.54/1.42  #Chain   : 0
% 2.54/1.42  #Close   : 0
% 2.54/1.42  
% 2.54/1.42  Ordering : KBO
% 2.54/1.42  
% 2.54/1.42  Simplification rules
% 2.54/1.42  ----------------------
% 2.54/1.42  #Subsume      : 7
% 2.54/1.42  #Demod        : 8
% 2.54/1.42  #Tautology    : 3
% 2.54/1.42  #SimpNegUnit  : 1
% 2.54/1.42  #BackRed      : 0
% 2.54/1.42  
% 2.54/1.42  #Partial instantiations: 0
% 2.54/1.42  #Strategies tried      : 1
% 2.54/1.42  
% 2.54/1.42  Timing (in seconds)
% 2.54/1.42  ----------------------
% 2.54/1.42  Preprocessing        : 0.35
% 2.54/1.42  Parsing              : 0.22
% 2.54/1.42  CNF conversion       : 0.02
% 2.54/1.42  Main loop            : 0.31
% 2.54/1.42  Inferencing          : 0.12
% 2.54/1.42  Reduction            : 0.07
% 2.54/1.42  Demodulation         : 0.05
% 2.54/1.42  BG Simplification    : 0.01
% 2.54/1.42  Subsumption          : 0.09
% 2.54/1.42  Abstraction          : 0.01
% 2.54/1.42  MUC search           : 0.00
% 2.54/1.42  Cooper               : 0.00
% 2.54/1.42  Total                : 0.69
% 2.54/1.42  Index Insertion      : 0.00
% 2.54/1.42  Index Deletion       : 0.00
% 2.54/1.42  Index Matching       : 0.00
% 2.54/1.42  BG Taut test         : 0.00
%------------------------------------------------------------------------------
