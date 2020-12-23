%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:08:47 EST 2020

% Result     : Theorem 1.86s
% Output     : CNFRefutation 2.01s
% Verified   : 
% Statistics : Number of formulae       :   38 (  45 expanded)
%              Number of leaves         :   19 (  24 expanded)
%              Depth                    :    7
%              Number of atoms          :   53 (  79 expanded)
%              Number of equality atoms :    7 (   9 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > m1_subset_1 > #nlpp > k2_subset_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_3 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_58,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_60,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

tff(f_56,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & ! [C] :
            ~ ( r2_hidden(C,B)
              & ! [D] :
                  ~ ( r2_hidden(D,B)
                    & r2_hidden(D,C) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_tarski)).

tff(f_83,negated_conjecture,(
    ~ ! [A] :
        ~ ( A != k1_xboole_0
          & ! [B] :
              ~ ( r2_hidden(B,A)
                & r1_xboole_0(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_mcart_1)).

tff(f_72,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ~ ( B != k1_xboole_0
          & ! [C] :
              ( m1_subset_1(C,A)
             => ~ r2_hidden(C,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_subset_1)).

tff(c_12,plain,(
    ! [A_13] : k2_subset_1(A_13) = A_13 ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_14,plain,(
    ! [A_14] : m1_subset_1(k2_subset_1(A_14),k1_zfmisc_1(A_14)) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_23,plain,(
    ! [A_14] : m1_subset_1(A_14,k1_zfmisc_1(A_14)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_14])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_67,plain,(
    ! [D_40,A_41,B_42] :
      ( ~ r2_hidden(D_40,'#skF_2'(A_41,B_42))
      | ~ r2_hidden(D_40,B_42)
      | ~ r2_hidden(A_41,B_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_99,plain,(
    ! [A_51,B_52,B_53] :
      ( ~ r2_hidden('#skF_1'('#skF_2'(A_51,B_52),B_53),B_52)
      | ~ r2_hidden(A_51,B_52)
      | r1_xboole_0('#skF_2'(A_51,B_52),B_53) ) ),
    inference(resolution,[status(thm)],[c_6,c_67])).

tff(c_105,plain,(
    ! [A_54,B_55] :
      ( ~ r2_hidden(A_54,B_55)
      | r1_xboole_0('#skF_2'(A_54,B_55),B_55) ) ),
    inference(resolution,[status(thm)],[c_4,c_99])).

tff(c_47,plain,(
    ! [A_27,B_28] :
      ( r2_hidden('#skF_2'(A_27,B_28),B_28)
      | ~ r2_hidden(A_27,B_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_20,plain,(
    ! [B_19] :
      ( ~ r1_xboole_0(B_19,'#skF_4')
      | ~ r2_hidden(B_19,'#skF_4') ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_52,plain,(
    ! [A_27] :
      ( ~ r1_xboole_0('#skF_2'(A_27,'#skF_4'),'#skF_4')
      | ~ r2_hidden(A_27,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_47,c_20])).

tff(c_114,plain,(
    ! [A_56] : ~ r2_hidden(A_56,'#skF_4') ),
    inference(resolution,[status(thm)],[c_105,c_52])).

tff(c_135,plain,(
    ! [A_1] : r1_xboole_0(A_1,'#skF_4') ),
    inference(resolution,[status(thm)],[c_4,c_114])).

tff(c_22,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_58,plain,(
    ! [A_37,B_38] :
      ( r2_hidden('#skF_3'(A_37,B_38),B_38)
      | k1_xboole_0 = B_38
      | ~ m1_subset_1(B_38,k1_zfmisc_1(A_37)) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_62,plain,(
    ! [A_37] :
      ( ~ r1_xboole_0('#skF_3'(A_37,'#skF_4'),'#skF_4')
      | k1_xboole_0 = '#skF_4'
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_37)) ) ),
    inference(resolution,[status(thm)],[c_58,c_20])).

tff(c_65,plain,(
    ! [A_37] :
      ( ~ r1_xboole_0('#skF_3'(A_37,'#skF_4'),'#skF_4')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_37)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_22,c_62])).

tff(c_152,plain,(
    ! [A_59] : ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_59)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_135,c_65])).

tff(c_157,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_23,c_152])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:24:40 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.86/1.22  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.86/1.23  
% 1.86/1.23  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.98/1.23  %$ r2_hidden > r1_xboole_0 > m1_subset_1 > #nlpp > k2_subset_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 1.98/1.23  
% 1.98/1.23  %Foreground sorts:
% 1.98/1.23  
% 1.98/1.23  
% 1.98/1.23  %Background operators:
% 1.98/1.23  
% 1.98/1.23  
% 1.98/1.23  %Foreground operators:
% 1.98/1.23  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.98/1.23  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.98/1.23  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.98/1.23  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 1.98/1.23  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.98/1.23  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.98/1.23  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.98/1.23  tff('#skF_4', type, '#skF_4': $i).
% 1.98/1.23  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.98/1.23  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 1.98/1.23  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.98/1.23  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 1.98/1.23  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.98/1.23  
% 2.01/1.24  tff(f_58, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 2.01/1.24  tff(f_60, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 2.01/1.24  tff(f_43, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 2.01/1.24  tff(f_56, axiom, (![A, B]: ~(r2_hidden(A, B) & (![C]: ~(r2_hidden(C, B) & (![D]: ~(r2_hidden(D, B) & r2_hidden(D, C))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_tarski)).
% 2.01/1.24  tff(f_83, negated_conjecture, ~(![A]: ~(~(A = k1_xboole_0) & (![B]: ~(r2_hidden(B, A) & r1_xboole_0(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_mcart_1)).
% 2.01/1.24  tff(f_72, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => ~(~(B = k1_xboole_0) & (![C]: (m1_subset_1(C, A) => ~r2_hidden(C, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_subset_1)).
% 2.01/1.24  tff(c_12, plain, (![A_13]: (k2_subset_1(A_13)=A_13)), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.01/1.24  tff(c_14, plain, (![A_14]: (m1_subset_1(k2_subset_1(A_14), k1_zfmisc_1(A_14)))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.01/1.24  tff(c_23, plain, (![A_14]: (m1_subset_1(A_14, k1_zfmisc_1(A_14)))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_14])).
% 2.01/1.24  tff(c_4, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.01/1.24  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.01/1.24  tff(c_67, plain, (![D_40, A_41, B_42]: (~r2_hidden(D_40, '#skF_2'(A_41, B_42)) | ~r2_hidden(D_40, B_42) | ~r2_hidden(A_41, B_42))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.01/1.24  tff(c_99, plain, (![A_51, B_52, B_53]: (~r2_hidden('#skF_1'('#skF_2'(A_51, B_52), B_53), B_52) | ~r2_hidden(A_51, B_52) | r1_xboole_0('#skF_2'(A_51, B_52), B_53))), inference(resolution, [status(thm)], [c_6, c_67])).
% 2.01/1.24  tff(c_105, plain, (![A_54, B_55]: (~r2_hidden(A_54, B_55) | r1_xboole_0('#skF_2'(A_54, B_55), B_55))), inference(resolution, [status(thm)], [c_4, c_99])).
% 2.01/1.24  tff(c_47, plain, (![A_27, B_28]: (r2_hidden('#skF_2'(A_27, B_28), B_28) | ~r2_hidden(A_27, B_28))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.01/1.24  tff(c_20, plain, (![B_19]: (~r1_xboole_0(B_19, '#skF_4') | ~r2_hidden(B_19, '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.01/1.24  tff(c_52, plain, (![A_27]: (~r1_xboole_0('#skF_2'(A_27, '#skF_4'), '#skF_4') | ~r2_hidden(A_27, '#skF_4'))), inference(resolution, [status(thm)], [c_47, c_20])).
% 2.01/1.24  tff(c_114, plain, (![A_56]: (~r2_hidden(A_56, '#skF_4'))), inference(resolution, [status(thm)], [c_105, c_52])).
% 2.01/1.24  tff(c_135, plain, (![A_1]: (r1_xboole_0(A_1, '#skF_4'))), inference(resolution, [status(thm)], [c_4, c_114])).
% 2.01/1.24  tff(c_22, plain, (k1_xboole_0!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.01/1.24  tff(c_58, plain, (![A_37, B_38]: (r2_hidden('#skF_3'(A_37, B_38), B_38) | k1_xboole_0=B_38 | ~m1_subset_1(B_38, k1_zfmisc_1(A_37)))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.01/1.24  tff(c_62, plain, (![A_37]: (~r1_xboole_0('#skF_3'(A_37, '#skF_4'), '#skF_4') | k1_xboole_0='#skF_4' | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_37)))), inference(resolution, [status(thm)], [c_58, c_20])).
% 2.01/1.24  tff(c_65, plain, (![A_37]: (~r1_xboole_0('#skF_3'(A_37, '#skF_4'), '#skF_4') | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_37)))), inference(negUnitSimplification, [status(thm)], [c_22, c_62])).
% 2.01/1.24  tff(c_152, plain, (![A_59]: (~m1_subset_1('#skF_4', k1_zfmisc_1(A_59)))), inference(demodulation, [status(thm), theory('equality')], [c_135, c_65])).
% 2.01/1.24  tff(c_157, plain, $false, inference(resolution, [status(thm)], [c_23, c_152])).
% 2.01/1.24  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.01/1.24  
% 2.01/1.24  Inference rules
% 2.01/1.24  ----------------------
% 2.01/1.24  #Ref     : 0
% 2.01/1.24  #Sup     : 22
% 2.01/1.24  #Fact    : 0
% 2.01/1.24  #Define  : 0
% 2.01/1.24  #Split   : 0
% 2.01/1.24  #Chain   : 0
% 2.01/1.24  #Close   : 0
% 2.01/1.24  
% 2.01/1.24  Ordering : KBO
% 2.01/1.24  
% 2.01/1.24  Simplification rules
% 2.01/1.24  ----------------------
% 2.01/1.24  #Subsume      : 7
% 2.01/1.24  #Demod        : 6
% 2.01/1.24  #Tautology    : 4
% 2.01/1.24  #SimpNegUnit  : 2
% 2.01/1.24  #BackRed      : 2
% 2.01/1.24  
% 2.01/1.24  #Partial instantiations: 0
% 2.01/1.24  #Strategies tried      : 1
% 2.01/1.24  
% 2.01/1.24  Timing (in seconds)
% 2.01/1.24  ----------------------
% 2.01/1.24  Preprocessing        : 0.29
% 2.01/1.24  Parsing              : 0.16
% 2.01/1.24  CNF conversion       : 0.02
% 2.01/1.24  Main loop            : 0.14
% 2.01/1.24  Inferencing          : 0.06
% 2.01/1.24  Reduction            : 0.03
% 2.01/1.24  Demodulation         : 0.02
% 2.01/1.24  BG Simplification    : 0.01
% 2.01/1.24  Subsumption          : 0.03
% 2.01/1.24  Abstraction          : 0.01
% 2.01/1.24  MUC search           : 0.00
% 2.01/1.24  Cooper               : 0.00
% 2.01/1.24  Total                : 0.46
% 2.01/1.24  Index Insertion      : 0.00
% 2.01/1.24  Index Deletion       : 0.00
% 2.01/1.24  Index Matching       : 0.00
% 2.01/1.24  BG Taut test         : 0.00
%------------------------------------------------------------------------------
