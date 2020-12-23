%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:56:57 EST 2020

% Result     : Theorem 1.94s
% Output     : CNFRefutation 1.96s
% Verified   : 
% Statistics : Number of formulae       :   56 (  85 expanded)
%              Number of leaves         :   23 (  39 expanded)
%              Depth                    :    8
%              Number of atoms          :   72 ( 159 expanded)
%              Number of equality atoms :    6 (  14 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k2_enumset1 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_1 > #skF_3 > #skF_5 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_71,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,A)
       => ( A != k1_xboole_0
         => m1_subset_1(k1_tarski(B),k1_zfmisc_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_subset_1)).

tff(f_63,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_50,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_46,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_35,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(c_38,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_40,plain,(
    m1_subset_1('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_64,plain,(
    ! [B_29,A_30] :
      ( v1_xboole_0(B_29)
      | ~ m1_subset_1(B_29,A_30)
      | ~ v1_xboole_0(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_68,plain,
    ( v1_xboole_0('#skF_5')
    | ~ v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_40,c_64])).

tff(c_69,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_68])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_26,plain,(
    ! [A_14,B_15] :
      ( r1_tarski(k1_tarski(A_14),B_15)
      | ~ r2_hidden(A_14,B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_30,plain,(
    ! [B_17,A_16] :
      ( r2_hidden(B_17,A_16)
      | ~ m1_subset_1(B_17,A_16)
      | v1_xboole_0(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_80,plain,(
    ! [B_33,A_34] :
      ( m1_subset_1(B_33,A_34)
      | ~ v1_xboole_0(B_33)
      | ~ v1_xboole_0(A_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_36,plain,(
    ~ m1_subset_1(k1_tarski('#skF_5'),k1_zfmisc_1('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_88,plain,
    ( ~ v1_xboole_0(k1_tarski('#skF_5'))
    | ~ v1_xboole_0(k1_zfmisc_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_80,c_36])).

tff(c_94,plain,(
    ~ v1_xboole_0(k1_zfmisc_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_88])).

tff(c_14,plain,(
    ! [C_13,A_9] :
      ( r2_hidden(C_13,k1_zfmisc_1(A_9))
      | ~ r1_tarski(C_13,A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_114,plain,(
    ! [B_41,A_42] :
      ( m1_subset_1(B_41,A_42)
      | ~ r2_hidden(B_41,A_42)
      | v1_xboole_0(A_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_133,plain,(
    ! [C_45,A_46] :
      ( m1_subset_1(C_45,k1_zfmisc_1(A_46))
      | v1_xboole_0(k1_zfmisc_1(A_46))
      | ~ r1_tarski(C_45,A_46) ) ),
    inference(resolution,[status(thm)],[c_14,c_114])).

tff(c_139,plain,
    ( v1_xboole_0(k1_zfmisc_1('#skF_4'))
    | ~ r1_tarski(k1_tarski('#skF_5'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_133,c_36])).

tff(c_143,plain,(
    ~ r1_tarski(k1_tarski('#skF_5'),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_94,c_139])).

tff(c_147,plain,(
    ~ r2_hidden('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_26,c_143])).

tff(c_159,plain,
    ( ~ m1_subset_1('#skF_5','#skF_4')
    | v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_30,c_147])).

tff(c_162,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_159])).

tff(c_164,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_69,c_162])).

tff(c_166,plain,(
    v1_xboole_0(k1_zfmisc_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_88])).

tff(c_57,plain,(
    ! [C_23,A_24] :
      ( r2_hidden(C_23,k1_zfmisc_1(A_24))
      | ~ r1_tarski(C_23,A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_61,plain,(
    ! [A_24,C_23] :
      ( ~ v1_xboole_0(k1_zfmisc_1(A_24))
      | ~ r1_tarski(C_23,A_24) ) ),
    inference(resolution,[status(thm)],[c_57,c_2])).

tff(c_174,plain,(
    ! [C_49] : ~ r1_tarski(C_49,'#skF_4') ),
    inference(resolution,[status(thm)],[c_166,c_61])).

tff(c_200,plain,(
    ! [A_50] : ~ r2_hidden(A_50,'#skF_4') ),
    inference(resolution,[status(thm)],[c_26,c_174])).

tff(c_204,plain,(
    v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_4,c_200])).

tff(c_208,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_69,c_204])).

tff(c_210,plain,(
    v1_xboole_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_68])).

tff(c_6,plain,(
    ! [A_5] :
      ( k1_xboole_0 = A_5
      | ~ v1_xboole_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_217,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_210,c_6])).

tff(c_221,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_217])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:51:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.94/1.18  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.96/1.19  
% 1.96/1.19  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.96/1.19  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k2_enumset1 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_1 > #skF_3 > #skF_5 > #skF_4 > #skF_2
% 1.96/1.19  
% 1.96/1.19  %Foreground sorts:
% 1.96/1.19  
% 1.96/1.19  
% 1.96/1.19  %Background operators:
% 1.96/1.19  
% 1.96/1.19  
% 1.96/1.19  %Foreground operators:
% 1.96/1.19  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.96/1.19  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.96/1.19  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.96/1.19  tff('#skF_1', type, '#skF_1': $i > $i).
% 1.96/1.19  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.96/1.19  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 1.96/1.19  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.96/1.19  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.96/1.19  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.96/1.19  tff('#skF_5', type, '#skF_5': $i).
% 1.96/1.19  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.96/1.19  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.96/1.19  tff('#skF_4', type, '#skF_4': $i).
% 1.96/1.19  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.96/1.19  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 1.96/1.19  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.96/1.19  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.96/1.19  
% 1.96/1.20  tff(f_71, negated_conjecture, ~(![A, B]: (m1_subset_1(B, A) => (~(A = k1_xboole_0) => m1_subset_1(k1_tarski(B), k1_zfmisc_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_subset_1)).
% 1.96/1.20  tff(f_63, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 1.96/1.20  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 1.96/1.20  tff(f_50, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 1.96/1.20  tff(f_46, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 1.96/1.20  tff(f_35, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 1.96/1.20  tff(c_38, plain, (k1_xboole_0!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_71])).
% 1.96/1.20  tff(c_40, plain, (m1_subset_1('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_71])).
% 1.96/1.20  tff(c_64, plain, (![B_29, A_30]: (v1_xboole_0(B_29) | ~m1_subset_1(B_29, A_30) | ~v1_xboole_0(A_30))), inference(cnfTransformation, [status(thm)], [f_63])).
% 1.96/1.20  tff(c_68, plain, (v1_xboole_0('#skF_5') | ~v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_40, c_64])).
% 1.96/1.20  tff(c_69, plain, (~v1_xboole_0('#skF_4')), inference(splitLeft, [status(thm)], [c_68])).
% 1.96/1.20  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.96/1.20  tff(c_26, plain, (![A_14, B_15]: (r1_tarski(k1_tarski(A_14), B_15) | ~r2_hidden(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_50])).
% 1.96/1.20  tff(c_30, plain, (![B_17, A_16]: (r2_hidden(B_17, A_16) | ~m1_subset_1(B_17, A_16) | v1_xboole_0(A_16))), inference(cnfTransformation, [status(thm)], [f_63])).
% 1.96/1.20  tff(c_80, plain, (![B_33, A_34]: (m1_subset_1(B_33, A_34) | ~v1_xboole_0(B_33) | ~v1_xboole_0(A_34))), inference(cnfTransformation, [status(thm)], [f_63])).
% 1.96/1.20  tff(c_36, plain, (~m1_subset_1(k1_tarski('#skF_5'), k1_zfmisc_1('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_71])).
% 1.96/1.20  tff(c_88, plain, (~v1_xboole_0(k1_tarski('#skF_5')) | ~v1_xboole_0(k1_zfmisc_1('#skF_4'))), inference(resolution, [status(thm)], [c_80, c_36])).
% 1.96/1.20  tff(c_94, plain, (~v1_xboole_0(k1_zfmisc_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_88])).
% 1.96/1.20  tff(c_14, plain, (![C_13, A_9]: (r2_hidden(C_13, k1_zfmisc_1(A_9)) | ~r1_tarski(C_13, A_9))), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.96/1.20  tff(c_114, plain, (![B_41, A_42]: (m1_subset_1(B_41, A_42) | ~r2_hidden(B_41, A_42) | v1_xboole_0(A_42))), inference(cnfTransformation, [status(thm)], [f_63])).
% 1.96/1.20  tff(c_133, plain, (![C_45, A_46]: (m1_subset_1(C_45, k1_zfmisc_1(A_46)) | v1_xboole_0(k1_zfmisc_1(A_46)) | ~r1_tarski(C_45, A_46))), inference(resolution, [status(thm)], [c_14, c_114])).
% 1.96/1.20  tff(c_139, plain, (v1_xboole_0(k1_zfmisc_1('#skF_4')) | ~r1_tarski(k1_tarski('#skF_5'), '#skF_4')), inference(resolution, [status(thm)], [c_133, c_36])).
% 1.96/1.20  tff(c_143, plain, (~r1_tarski(k1_tarski('#skF_5'), '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_94, c_139])).
% 1.96/1.20  tff(c_147, plain, (~r2_hidden('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_26, c_143])).
% 1.96/1.20  tff(c_159, plain, (~m1_subset_1('#skF_5', '#skF_4') | v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_30, c_147])).
% 1.96/1.20  tff(c_162, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_159])).
% 1.96/1.20  tff(c_164, plain, $false, inference(negUnitSimplification, [status(thm)], [c_69, c_162])).
% 1.96/1.20  tff(c_166, plain, (v1_xboole_0(k1_zfmisc_1('#skF_4'))), inference(splitRight, [status(thm)], [c_88])).
% 1.96/1.20  tff(c_57, plain, (![C_23, A_24]: (r2_hidden(C_23, k1_zfmisc_1(A_24)) | ~r1_tarski(C_23, A_24))), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.96/1.20  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.96/1.20  tff(c_61, plain, (![A_24, C_23]: (~v1_xboole_0(k1_zfmisc_1(A_24)) | ~r1_tarski(C_23, A_24))), inference(resolution, [status(thm)], [c_57, c_2])).
% 1.96/1.20  tff(c_174, plain, (![C_49]: (~r1_tarski(C_49, '#skF_4'))), inference(resolution, [status(thm)], [c_166, c_61])).
% 1.96/1.20  tff(c_200, plain, (![A_50]: (~r2_hidden(A_50, '#skF_4'))), inference(resolution, [status(thm)], [c_26, c_174])).
% 1.96/1.20  tff(c_204, plain, (v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_4, c_200])).
% 1.96/1.20  tff(c_208, plain, $false, inference(negUnitSimplification, [status(thm)], [c_69, c_204])).
% 1.96/1.20  tff(c_210, plain, (v1_xboole_0('#skF_4')), inference(splitRight, [status(thm)], [c_68])).
% 1.96/1.20  tff(c_6, plain, (![A_5]: (k1_xboole_0=A_5 | ~v1_xboole_0(A_5))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.96/1.20  tff(c_217, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_210, c_6])).
% 1.96/1.20  tff(c_221, plain, $false, inference(negUnitSimplification, [status(thm)], [c_38, c_217])).
% 1.96/1.20  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.96/1.20  
% 1.96/1.20  Inference rules
% 1.96/1.20  ----------------------
% 1.96/1.20  #Ref     : 0
% 1.96/1.20  #Sup     : 36
% 1.96/1.20  #Fact    : 0
% 1.96/1.20  #Define  : 0
% 1.96/1.20  #Split   : 2
% 1.96/1.20  #Chain   : 0
% 1.96/1.20  #Close   : 0
% 1.96/1.20  
% 1.96/1.20  Ordering : KBO
% 1.96/1.20  
% 1.96/1.20  Simplification rules
% 1.96/1.20  ----------------------
% 1.96/1.20  #Subsume      : 3
% 1.96/1.20  #Demod        : 3
% 1.96/1.20  #Tautology    : 14
% 1.96/1.20  #SimpNegUnit  : 5
% 1.96/1.20  #BackRed      : 2
% 1.96/1.20  
% 1.96/1.20  #Partial instantiations: 0
% 1.96/1.20  #Strategies tried      : 1
% 1.96/1.20  
% 1.96/1.20  Timing (in seconds)
% 1.96/1.20  ----------------------
% 1.96/1.21  Preprocessing        : 0.29
% 1.96/1.21  Parsing              : 0.15
% 1.96/1.21  CNF conversion       : 0.02
% 1.96/1.21  Main loop            : 0.15
% 1.96/1.21  Inferencing          : 0.06
% 1.96/1.21  Reduction            : 0.04
% 1.96/1.21  Demodulation         : 0.02
% 1.96/1.21  BG Simplification    : 0.01
% 1.96/1.21  Subsumption          : 0.03
% 1.96/1.21  Abstraction          : 0.01
% 1.96/1.21  MUC search           : 0.00
% 1.96/1.21  Cooper               : 0.00
% 1.96/1.21  Total                : 0.47
% 1.96/1.21  Index Insertion      : 0.00
% 1.96/1.21  Index Deletion       : 0.00
% 1.96/1.21  Index Matching       : 0.00
% 1.96/1.21  BG Taut test         : 0.00
%------------------------------------------------------------------------------
