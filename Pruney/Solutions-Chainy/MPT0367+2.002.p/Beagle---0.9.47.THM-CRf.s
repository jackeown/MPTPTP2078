%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:56:47 EST 2020

% Result     : Theorem 2.10s
% Output     : CNFRefutation 2.10s
% Verified   : 
% Statistics : Number of formulae       :   35 (  49 expanded)
%              Number of leaves         :   17 (  26 expanded)
%              Depth                    :    8
%              Number of atoms          :   64 ( 119 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > #nlpp > k1_zfmisc_1 > #skF_1 > #skF_5 > #skF_3 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_71,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => ! [C] :
            ( m1_subset_1(C,k1_zfmisc_1(A))
           => ( ! [D] :
                  ( m1_subset_1(D,B)
                 => r2_hidden(D,C) )
             => r1_tarski(B,C) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_subset_1)).

tff(f_58,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(A))
         => ( ! [D] :
                ( m1_subset_1(D,A)
               => ( r2_hidden(D,B)
                 => r2_hidden(D,C) ) )
           => r1_tarski(B,C) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_subset_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_44,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

tff(c_26,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_24,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_20,plain,(
    ~ r1_tarski('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_96,plain,(
    ! [A_36,B_37,C_38] :
      ( r2_hidden('#skF_2'(A_36,B_37,C_38),B_37)
      | r1_tarski(B_37,C_38)
      | ~ m1_subset_1(C_38,k1_zfmisc_1(A_36))
      | ~ m1_subset_1(B_37,k1_zfmisc_1(A_36)) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_129,plain,(
    ! [B_43,C_44,A_45] :
      ( ~ v1_xboole_0(B_43)
      | r1_tarski(B_43,C_44)
      | ~ m1_subset_1(C_44,k1_zfmisc_1(A_45))
      | ~ m1_subset_1(B_43,k1_zfmisc_1(A_45)) ) ),
    inference(resolution,[status(thm)],[c_96,c_2])).

tff(c_159,plain,(
    ! [B_49] :
      ( ~ v1_xboole_0(B_49)
      | r1_tarski(B_49,'#skF_5')
      | ~ m1_subset_1(B_49,k1_zfmisc_1('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_24,c_129])).

tff(c_177,plain,
    ( ~ v1_xboole_0('#skF_4')
    | r1_tarski('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_26,c_159])).

tff(c_187,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_20,c_177])).

tff(c_6,plain,(
    ! [B_6,A_5] :
      ( m1_subset_1(B_6,A_5)
      | ~ r2_hidden(B_6,A_5)
      | v1_xboole_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_255,plain,(
    ! [A_60,B_61,C_62] :
      ( m1_subset_1('#skF_2'(A_60,B_61,C_62),B_61)
      | v1_xboole_0(B_61)
      | r1_tarski(B_61,C_62)
      | ~ m1_subset_1(C_62,k1_zfmisc_1(A_60))
      | ~ m1_subset_1(B_61,k1_zfmisc_1(A_60)) ) ),
    inference(resolution,[status(thm)],[c_96,c_6])).

tff(c_22,plain,(
    ! [D_18] :
      ( r2_hidden(D_18,'#skF_5')
      | ~ m1_subset_1(D_18,'#skF_4') ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_80,plain,(
    ! [A_32,B_33,C_34] :
      ( ~ r2_hidden('#skF_2'(A_32,B_33,C_34),C_34)
      | r1_tarski(B_33,C_34)
      | ~ m1_subset_1(C_34,k1_zfmisc_1(A_32))
      | ~ m1_subset_1(B_33,k1_zfmisc_1(A_32)) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_90,plain,(
    ! [B_33,A_32] :
      ( r1_tarski(B_33,'#skF_5')
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_32))
      | ~ m1_subset_1(B_33,k1_zfmisc_1(A_32))
      | ~ m1_subset_1('#skF_2'(A_32,B_33,'#skF_5'),'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_22,c_80])).

tff(c_262,plain,(
    ! [A_60] :
      ( v1_xboole_0('#skF_4')
      | r1_tarski('#skF_4','#skF_5')
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_60))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_60)) ) ),
    inference(resolution,[status(thm)],[c_255,c_90])).

tff(c_299,plain,(
    ! [A_63] :
      ( ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_63))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_63)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_20,c_187,c_20,c_262])).

tff(c_305,plain,(
    ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_24,c_299])).

tff(c_310,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_305])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:44:34 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.10/1.25  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.10/1.25  
% 2.10/1.25  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.10/1.25  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > #nlpp > k1_zfmisc_1 > #skF_1 > #skF_5 > #skF_3 > #skF_2 > #skF_4
% 2.10/1.25  
% 2.10/1.25  %Foreground sorts:
% 2.10/1.25  
% 2.10/1.25  
% 2.10/1.25  %Background operators:
% 2.10/1.25  
% 2.10/1.25  
% 2.10/1.25  %Foreground operators:
% 2.10/1.25  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.10/1.25  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.10/1.25  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.10/1.25  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.10/1.25  tff('#skF_5', type, '#skF_5': $i).
% 2.10/1.25  tff('#skF_3', type, '#skF_3': $i).
% 2.10/1.25  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.10/1.25  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.10/1.25  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.10/1.25  tff('#skF_4', type, '#skF_4': $i).
% 2.10/1.25  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.10/1.25  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.10/1.25  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.10/1.25  
% 2.10/1.27  tff(f_71, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => ((![D]: (m1_subset_1(D, B) => r2_hidden(D, C))) => r1_tarski(B, C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_subset_1)).
% 2.10/1.27  tff(f_58, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => ((![D]: (m1_subset_1(D, A) => (r2_hidden(D, B) => r2_hidden(D, C)))) => r1_tarski(B, C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_subset_1)).
% 2.10/1.27  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 2.10/1.27  tff(f_44, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 2.10/1.27  tff(c_26, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.10/1.27  tff(c_24, plain, (m1_subset_1('#skF_5', k1_zfmisc_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.10/1.27  tff(c_20, plain, (~r1_tarski('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.10/1.27  tff(c_96, plain, (![A_36, B_37, C_38]: (r2_hidden('#skF_2'(A_36, B_37, C_38), B_37) | r1_tarski(B_37, C_38) | ~m1_subset_1(C_38, k1_zfmisc_1(A_36)) | ~m1_subset_1(B_37, k1_zfmisc_1(A_36)))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.10/1.27  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.10/1.27  tff(c_129, plain, (![B_43, C_44, A_45]: (~v1_xboole_0(B_43) | r1_tarski(B_43, C_44) | ~m1_subset_1(C_44, k1_zfmisc_1(A_45)) | ~m1_subset_1(B_43, k1_zfmisc_1(A_45)))), inference(resolution, [status(thm)], [c_96, c_2])).
% 2.10/1.27  tff(c_159, plain, (![B_49]: (~v1_xboole_0(B_49) | r1_tarski(B_49, '#skF_5') | ~m1_subset_1(B_49, k1_zfmisc_1('#skF_3')))), inference(resolution, [status(thm)], [c_24, c_129])).
% 2.10/1.27  tff(c_177, plain, (~v1_xboole_0('#skF_4') | r1_tarski('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_26, c_159])).
% 2.10/1.27  tff(c_187, plain, (~v1_xboole_0('#skF_4')), inference(negUnitSimplification, [status(thm)], [c_20, c_177])).
% 2.10/1.27  tff(c_6, plain, (![B_6, A_5]: (m1_subset_1(B_6, A_5) | ~r2_hidden(B_6, A_5) | v1_xboole_0(A_5))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.10/1.27  tff(c_255, plain, (![A_60, B_61, C_62]: (m1_subset_1('#skF_2'(A_60, B_61, C_62), B_61) | v1_xboole_0(B_61) | r1_tarski(B_61, C_62) | ~m1_subset_1(C_62, k1_zfmisc_1(A_60)) | ~m1_subset_1(B_61, k1_zfmisc_1(A_60)))), inference(resolution, [status(thm)], [c_96, c_6])).
% 2.10/1.27  tff(c_22, plain, (![D_18]: (r2_hidden(D_18, '#skF_5') | ~m1_subset_1(D_18, '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.10/1.27  tff(c_80, plain, (![A_32, B_33, C_34]: (~r2_hidden('#skF_2'(A_32, B_33, C_34), C_34) | r1_tarski(B_33, C_34) | ~m1_subset_1(C_34, k1_zfmisc_1(A_32)) | ~m1_subset_1(B_33, k1_zfmisc_1(A_32)))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.10/1.27  tff(c_90, plain, (![B_33, A_32]: (r1_tarski(B_33, '#skF_5') | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_32)) | ~m1_subset_1(B_33, k1_zfmisc_1(A_32)) | ~m1_subset_1('#skF_2'(A_32, B_33, '#skF_5'), '#skF_4'))), inference(resolution, [status(thm)], [c_22, c_80])).
% 2.10/1.27  tff(c_262, plain, (![A_60]: (v1_xboole_0('#skF_4') | r1_tarski('#skF_4', '#skF_5') | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_60)) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_60)))), inference(resolution, [status(thm)], [c_255, c_90])).
% 2.10/1.27  tff(c_299, plain, (![A_63]: (~m1_subset_1('#skF_5', k1_zfmisc_1(A_63)) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_63)))), inference(negUnitSimplification, [status(thm)], [c_20, c_187, c_20, c_262])).
% 2.10/1.27  tff(c_305, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_3'))), inference(resolution, [status(thm)], [c_24, c_299])).
% 2.10/1.27  tff(c_310, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_26, c_305])).
% 2.10/1.27  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.10/1.27  
% 2.10/1.27  Inference rules
% 2.10/1.27  ----------------------
% 2.10/1.27  #Ref     : 0
% 2.10/1.27  #Sup     : 54
% 2.10/1.27  #Fact    : 0
% 2.10/1.27  #Define  : 0
% 2.10/1.27  #Split   : 5
% 2.10/1.27  #Chain   : 0
% 2.10/1.27  #Close   : 0
% 2.10/1.27  
% 2.10/1.27  Ordering : KBO
% 2.10/1.27  
% 2.10/1.27  Simplification rules
% 2.10/1.27  ----------------------
% 2.10/1.27  #Subsume      : 16
% 2.10/1.27  #Demod        : 3
% 2.10/1.27  #Tautology    : 5
% 2.10/1.27  #SimpNegUnit  : 14
% 2.10/1.27  #BackRed      : 0
% 2.10/1.27  
% 2.10/1.27  #Partial instantiations: 0
% 2.10/1.27  #Strategies tried      : 1
% 2.10/1.27  
% 2.10/1.27  Timing (in seconds)
% 2.10/1.27  ----------------------
% 2.10/1.27  Preprocessing        : 0.27
% 2.10/1.27  Parsing              : 0.15
% 2.10/1.27  CNF conversion       : 0.02
% 2.10/1.27  Main loop            : 0.25
% 2.10/1.27  Inferencing          : 0.10
% 2.10/1.27  Reduction            : 0.06
% 2.10/1.27  Demodulation         : 0.03
% 2.10/1.27  BG Simplification    : 0.01
% 2.10/1.27  Subsumption          : 0.05
% 2.10/1.27  Abstraction          : 0.01
% 2.10/1.27  MUC search           : 0.00
% 2.10/1.27  Cooper               : 0.00
% 2.10/1.27  Total                : 0.54
% 2.10/1.27  Index Insertion      : 0.00
% 2.10/1.27  Index Deletion       : 0.00
% 2.10/1.27  Index Matching       : 0.00
% 2.10/1.27  BG Taut test         : 0.00
%------------------------------------------------------------------------------
