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
% DateTime   : Thu Dec  3 09:56:38 EST 2020

% Result     : Theorem 3.19s
% Output     : CNFRefutation 3.19s
% Verified   : 
% Statistics : Number of formulae       :   50 (  64 expanded)
%              Number of leaves         :   21 (  30 expanded)
%              Depth                    :    7
%              Number of atoms          :   65 ( 106 expanded)
%              Number of equality atoms :    8 (   9 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > k4_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_67,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => ! [C] :
            ( m1_subset_1(C,k1_zfmisc_1(A))
           => ( r1_xboole_0(B,C)
            <=> r1_tarski(B,k3_subset_1(A,C)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_subset_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_38,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k4_xboole_0(B,C))
     => ( r1_tarski(A,B)
        & r1_xboole_0(A,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_xboole_1)).

tff(f_46,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_42,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(k4_xboole_0(A,C),k4_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t33_xboole_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_57,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

tff(c_26,plain,
    ( ~ r1_tarski('#skF_3',k3_subset_1('#skF_2','#skF_4'))
    | ~ r1_xboole_0('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_58,plain,(
    ~ r1_xboole_0('#skF_3','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_26])).

tff(c_32,plain,
    ( r1_xboole_0('#skF_3','#skF_4')
    | r1_tarski('#skF_3',k3_subset_1('#skF_2','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_91,plain,(
    r1_tarski('#skF_3',k3_subset_1('#skF_2','#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_32])).

tff(c_22,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_220,plain,(
    ! [A_65,B_66] :
      ( k4_xboole_0(A_65,B_66) = k3_subset_1(A_65,B_66)
      | ~ m1_subset_1(B_66,k1_zfmisc_1(A_65)) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_227,plain,(
    k4_xboole_0('#skF_2','#skF_4') = k3_subset_1('#skF_2','#skF_4') ),
    inference(resolution,[status(thm)],[c_22,c_220])).

tff(c_8,plain,(
    ! [A_6,C_8,B_7] :
      ( r1_xboole_0(A_6,C_8)
      | ~ r1_tarski(A_6,k4_xboole_0(B_7,C_8)) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_430,plain,(
    ! [A_80] :
      ( r1_xboole_0(A_80,'#skF_4')
      | ~ r1_tarski(A_80,k3_subset_1('#skF_2','#skF_4')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_227,c_8])).

tff(c_445,plain,(
    r1_xboole_0('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_91,c_430])).

tff(c_464,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_445])).

tff(c_465,plain,(
    ~ r1_tarski('#skF_3',k3_subset_1('#skF_2','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_26])).

tff(c_937,plain,(
    ! [A_121,B_122] :
      ( k4_xboole_0(A_121,B_122) = k3_subset_1(A_121,B_122)
      | ~ m1_subset_1(B_122,k1_zfmisc_1(A_121)) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_944,plain,(
    k4_xboole_0('#skF_2','#skF_4') = k3_subset_1('#skF_2','#skF_4') ),
    inference(resolution,[status(thm)],[c_22,c_937])).

tff(c_466,plain,(
    r1_xboole_0('#skF_3','#skF_4') ),
    inference(splitRight,[status(thm)],[c_26])).

tff(c_14,plain,(
    ! [A_12,B_13] :
      ( k4_xboole_0(A_12,B_13) = A_12
      | ~ r1_xboole_0(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_470,plain,(
    k4_xboole_0('#skF_3','#skF_4') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_466,c_14])).

tff(c_898,plain,(
    ! [A_118,C_119,B_120] :
      ( r1_tarski(k4_xboole_0(A_118,C_119),k4_xboole_0(B_120,C_119))
      | ~ r1_tarski(A_118,B_120) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_1246,plain,(
    ! [B_138] :
      ( r1_tarski('#skF_3',k4_xboole_0(B_138,'#skF_4'))
      | ~ r1_tarski('#skF_3',B_138) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_470,c_898])).

tff(c_1259,plain,
    ( r1_tarski('#skF_3',k3_subset_1('#skF_2','#skF_4'))
    | ~ r1_tarski('#skF_3','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_944,c_1246])).

tff(c_1279,plain,(
    ~ r1_tarski('#skF_3','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_465,c_1259])).

tff(c_24,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_1037,plain,(
    ! [C_126,A_127,B_128] :
      ( r2_hidden(C_126,A_127)
      | ~ r2_hidden(C_126,B_128)
      | ~ m1_subset_1(B_128,k1_zfmisc_1(A_127)) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_1495,plain,(
    ! [A_147,B_148,A_149] :
      ( r2_hidden('#skF_1'(A_147,B_148),A_149)
      | ~ m1_subset_1(A_147,k1_zfmisc_1(A_149))
      | r1_tarski(A_147,B_148) ) ),
    inference(resolution,[status(thm)],[c_6,c_1037])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_1507,plain,(
    ! [A_150,A_151] :
      ( ~ m1_subset_1(A_150,k1_zfmisc_1(A_151))
      | r1_tarski(A_150,A_151) ) ),
    inference(resolution,[status(thm)],[c_1495,c_4])).

tff(c_1513,plain,(
    r1_tarski('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_24,c_1507])).

tff(c_1518,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1279,c_1513])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n023.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 13:26:20 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.19/1.55  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.19/1.55  
% 3.19/1.55  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.19/1.55  %$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > k4_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 3.19/1.55  
% 3.19/1.55  %Foreground sorts:
% 3.19/1.55  
% 3.19/1.55  
% 3.19/1.55  %Background operators:
% 3.19/1.55  
% 3.19/1.55  
% 3.19/1.55  %Foreground operators:
% 3.19/1.55  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.19/1.55  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.19/1.55  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.19/1.55  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.19/1.55  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 3.19/1.55  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.19/1.55  tff('#skF_2', type, '#skF_2': $i).
% 3.19/1.55  tff('#skF_3', type, '#skF_3': $i).
% 3.19/1.55  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.19/1.55  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.19/1.55  tff('#skF_4', type, '#skF_4': $i).
% 3.19/1.55  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.19/1.55  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.19/1.55  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.19/1.55  
% 3.19/1.57  tff(f_67, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (r1_xboole_0(B, C) <=> r1_tarski(B, k3_subset_1(A, C))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_subset_1)).
% 3.19/1.57  tff(f_50, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 3.19/1.57  tff(f_38, axiom, (![A, B, C]: (r1_tarski(A, k4_xboole_0(B, C)) => (r1_tarski(A, B) & r1_xboole_0(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t106_xboole_1)).
% 3.19/1.57  tff(f_46, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_xboole_1)).
% 3.19/1.57  tff(f_42, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(k4_xboole_0(A, C), k4_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t33_xboole_1)).
% 3.19/1.57  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 3.19/1.57  tff(f_57, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_subset_1)).
% 3.19/1.57  tff(c_26, plain, (~r1_tarski('#skF_3', k3_subset_1('#skF_2', '#skF_4')) | ~r1_xboole_0('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.19/1.57  tff(c_58, plain, (~r1_xboole_0('#skF_3', '#skF_4')), inference(splitLeft, [status(thm)], [c_26])).
% 3.19/1.57  tff(c_32, plain, (r1_xboole_0('#skF_3', '#skF_4') | r1_tarski('#skF_3', k3_subset_1('#skF_2', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.19/1.57  tff(c_91, plain, (r1_tarski('#skF_3', k3_subset_1('#skF_2', '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_58, c_32])).
% 3.19/1.57  tff(c_22, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.19/1.57  tff(c_220, plain, (![A_65, B_66]: (k4_xboole_0(A_65, B_66)=k3_subset_1(A_65, B_66) | ~m1_subset_1(B_66, k1_zfmisc_1(A_65)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.19/1.57  tff(c_227, plain, (k4_xboole_0('#skF_2', '#skF_4')=k3_subset_1('#skF_2', '#skF_4')), inference(resolution, [status(thm)], [c_22, c_220])).
% 3.19/1.57  tff(c_8, plain, (![A_6, C_8, B_7]: (r1_xboole_0(A_6, C_8) | ~r1_tarski(A_6, k4_xboole_0(B_7, C_8)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.19/1.57  tff(c_430, plain, (![A_80]: (r1_xboole_0(A_80, '#skF_4') | ~r1_tarski(A_80, k3_subset_1('#skF_2', '#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_227, c_8])).
% 3.19/1.57  tff(c_445, plain, (r1_xboole_0('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_91, c_430])).
% 3.19/1.57  tff(c_464, plain, $false, inference(negUnitSimplification, [status(thm)], [c_58, c_445])).
% 3.19/1.57  tff(c_465, plain, (~r1_tarski('#skF_3', k3_subset_1('#skF_2', '#skF_4'))), inference(splitRight, [status(thm)], [c_26])).
% 3.19/1.57  tff(c_937, plain, (![A_121, B_122]: (k4_xboole_0(A_121, B_122)=k3_subset_1(A_121, B_122) | ~m1_subset_1(B_122, k1_zfmisc_1(A_121)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.19/1.57  tff(c_944, plain, (k4_xboole_0('#skF_2', '#skF_4')=k3_subset_1('#skF_2', '#skF_4')), inference(resolution, [status(thm)], [c_22, c_937])).
% 3.19/1.57  tff(c_466, plain, (r1_xboole_0('#skF_3', '#skF_4')), inference(splitRight, [status(thm)], [c_26])).
% 3.19/1.57  tff(c_14, plain, (![A_12, B_13]: (k4_xboole_0(A_12, B_13)=A_12 | ~r1_xboole_0(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.19/1.57  tff(c_470, plain, (k4_xboole_0('#skF_3', '#skF_4')='#skF_3'), inference(resolution, [status(thm)], [c_466, c_14])).
% 3.19/1.57  tff(c_898, plain, (![A_118, C_119, B_120]: (r1_tarski(k4_xboole_0(A_118, C_119), k4_xboole_0(B_120, C_119)) | ~r1_tarski(A_118, B_120))), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.19/1.57  tff(c_1246, plain, (![B_138]: (r1_tarski('#skF_3', k4_xboole_0(B_138, '#skF_4')) | ~r1_tarski('#skF_3', B_138))), inference(superposition, [status(thm), theory('equality')], [c_470, c_898])).
% 3.19/1.57  tff(c_1259, plain, (r1_tarski('#skF_3', k3_subset_1('#skF_2', '#skF_4')) | ~r1_tarski('#skF_3', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_944, c_1246])).
% 3.19/1.57  tff(c_1279, plain, (~r1_tarski('#skF_3', '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_465, c_1259])).
% 3.19/1.57  tff(c_24, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.19/1.57  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.19/1.57  tff(c_1037, plain, (![C_126, A_127, B_128]: (r2_hidden(C_126, A_127) | ~r2_hidden(C_126, B_128) | ~m1_subset_1(B_128, k1_zfmisc_1(A_127)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.19/1.57  tff(c_1495, plain, (![A_147, B_148, A_149]: (r2_hidden('#skF_1'(A_147, B_148), A_149) | ~m1_subset_1(A_147, k1_zfmisc_1(A_149)) | r1_tarski(A_147, B_148))), inference(resolution, [status(thm)], [c_6, c_1037])).
% 3.19/1.57  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.19/1.57  tff(c_1507, plain, (![A_150, A_151]: (~m1_subset_1(A_150, k1_zfmisc_1(A_151)) | r1_tarski(A_150, A_151))), inference(resolution, [status(thm)], [c_1495, c_4])).
% 3.19/1.57  tff(c_1513, plain, (r1_tarski('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_24, c_1507])).
% 3.19/1.57  tff(c_1518, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1279, c_1513])).
% 3.19/1.57  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.19/1.57  
% 3.19/1.57  Inference rules
% 3.19/1.57  ----------------------
% 3.19/1.57  #Ref     : 0
% 3.19/1.57  #Sup     : 353
% 3.19/1.57  #Fact    : 0
% 3.19/1.57  #Define  : 0
% 3.19/1.57  #Split   : 2
% 3.19/1.57  #Chain   : 0
% 3.19/1.57  #Close   : 0
% 3.19/1.57  
% 3.19/1.57  Ordering : KBO
% 3.19/1.57  
% 3.19/1.57  Simplification rules
% 3.19/1.57  ----------------------
% 3.19/1.57  #Subsume      : 11
% 3.19/1.57  #Demod        : 155
% 3.19/1.57  #Tautology    : 174
% 3.19/1.57  #SimpNegUnit  : 6
% 3.19/1.57  #BackRed      : 0
% 3.19/1.57  
% 3.19/1.57  #Partial instantiations: 0
% 3.19/1.57  #Strategies tried      : 1
% 3.19/1.57  
% 3.19/1.57  Timing (in seconds)
% 3.19/1.57  ----------------------
% 3.19/1.57  Preprocessing        : 0.30
% 3.19/1.57  Parsing              : 0.17
% 3.19/1.57  CNF conversion       : 0.02
% 3.19/1.57  Main loop            : 0.45
% 3.19/1.57  Inferencing          : 0.17
% 3.19/1.57  Reduction            : 0.15
% 3.19/1.57  Demodulation         : 0.10
% 3.19/1.57  BG Simplification    : 0.02
% 3.19/1.57  Subsumption          : 0.08
% 3.19/1.57  Abstraction          : 0.02
% 3.19/1.57  MUC search           : 0.00
% 3.19/1.57  Cooper               : 0.00
% 3.19/1.57  Total                : 0.79
% 3.19/1.57  Index Insertion      : 0.00
% 3.19/1.57  Index Deletion       : 0.00
% 3.19/1.57  Index Matching       : 0.00
% 3.19/1.57  BG Taut test         : 0.00
%------------------------------------------------------------------------------
