%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:50:03 EST 2020

% Result     : Theorem 3.21s
% Output     : CNFRefutation 3.23s
% Verified   : 
% Statistics : Number of formulae       :   53 (  70 expanded)
%              Number of leaves         :   24 (  35 expanded)
%              Depth                    :   11
%              Number of atoms          :   85 ( 135 expanded)
%              Number of equality atoms :   28 (  49 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_xboole_0 > r2_hidden > r1_xboole_0 > r1_tarski > k2_enumset1 > k1_enumset1 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_5 > #skF_4 > #skF_3 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff(r2_xboole_0,type,(
    r2_xboole_0: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_98,negated_conjecture,(
    ~ ! [A,B] :
        ~ ( A != k1_tarski(B)
          & A != k1_xboole_0
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & C != B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_zfmisc_1)).

tff(f_68,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_78,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_50,axiom,(
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

tff(f_83,axiom,(
    ! [A,B] :
      ~ ( r1_xboole_0(k1_tarski(A),B)
        & r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l24_zfmisc_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r2_xboole_0(A,B)
    <=> ( r1_tarski(A,B)
        & A != B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_xboole_0)).

tff(f_60,axiom,(
    ! [A,B] :
      ~ ( r2_xboole_0(A,B)
        & ! [C] :
            ~ ( r2_hidden(C,B)
              & ~ r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_xboole_0)).

tff(c_36,plain,(
    k1_tarski('#skF_5') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_34,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_49,plain,(
    ! [A_30] :
      ( r2_hidden('#skF_3'(A_30),A_30)
      | k1_xboole_0 = A_30 ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_32,plain,(
    ! [C_24] :
      ( C_24 = '#skF_5'
      | ~ r2_hidden(C_24,'#skF_4') ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_53,plain,
    ( '#skF_3'('#skF_4') = '#skF_5'
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_49,c_32])).

tff(c_56,plain,(
    '#skF_3'('#skF_4') = '#skF_5' ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_53])).

tff(c_18,plain,(
    ! [A_11] :
      ( r2_hidden('#skF_3'(A_11),A_11)
      | k1_xboole_0 = A_11 ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_60,plain,
    ( r2_hidden('#skF_5','#skF_4')
    | k1_xboole_0 = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_56,c_18])).

tff(c_63,plain,(
    r2_hidden('#skF_5','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_60])).

tff(c_28,plain,(
    ! [A_19,B_20] :
      ( r1_tarski(k1_tarski(A_19),B_20)
      | ~ r2_hidden(A_19,B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_86,plain,(
    ! [A_39,B_40] :
      ( r2_hidden('#skF_1'(A_39,B_40),B_40)
      | r1_xboole_0(A_39,B_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_92,plain,(
    ! [A_41] :
      ( '#skF_1'(A_41,'#skF_4') = '#skF_5'
      | r1_xboole_0(A_41,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_86,c_32])).

tff(c_30,plain,(
    ! [A_21,B_22] :
      ( ~ r2_hidden(A_21,B_22)
      | ~ r1_xboole_0(k1_tarski(A_21),B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_97,plain,(
    ! [A_21] :
      ( ~ r2_hidden(A_21,'#skF_4')
      | '#skF_1'(k1_tarski(A_21),'#skF_4') = '#skF_5' ) ),
    inference(resolution,[status(thm)],[c_92,c_30])).

tff(c_140,plain,(
    ! [A_50,B_51] :
      ( r2_hidden('#skF_1'(A_50,B_51),A_50)
      | r1_xboole_0(A_50,B_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_147,plain,(
    ! [A_21] :
      ( r2_hidden('#skF_5',k1_tarski(A_21))
      | r1_xboole_0(k1_tarski(A_21),'#skF_4')
      | ~ r2_hidden(A_21,'#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_97,c_140])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( r2_xboole_0(A_1,B_2)
      | B_2 = A_1
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_110,plain,(
    ! [A_46,B_47] :
      ( r2_hidden('#skF_2'(A_46,B_47),B_47)
      | ~ r2_xboole_0(A_46,B_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_121,plain,(
    ! [A_48] :
      ( '#skF_2'(A_48,'#skF_4') = '#skF_5'
      | ~ r2_xboole_0(A_48,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_110,c_32])).

tff(c_166,plain,(
    ! [A_59] :
      ( '#skF_2'(A_59,'#skF_4') = '#skF_5'
      | A_59 = '#skF_4'
      | ~ r1_tarski(A_59,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_2,c_121])).

tff(c_244,plain,(
    ! [A_66] :
      ( '#skF_2'(k1_tarski(A_66),'#skF_4') = '#skF_5'
      | k1_tarski(A_66) = '#skF_4'
      | ~ r2_hidden(A_66,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_28,c_166])).

tff(c_14,plain,(
    ! [A_8,B_9] :
      ( ~ r2_hidden('#skF_2'(A_8,B_9),A_8)
      | ~ r2_xboole_0(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_462,plain,(
    ! [A_89] :
      ( ~ r2_hidden('#skF_5',k1_tarski(A_89))
      | ~ r2_xboole_0(k1_tarski(A_89),'#skF_4')
      | k1_tarski(A_89) = '#skF_4'
      | ~ r2_hidden(A_89,'#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_244,c_14])).

tff(c_503,plain,(
    ! [A_94] :
      ( ~ r2_hidden('#skF_5',k1_tarski(A_94))
      | ~ r2_hidden(A_94,'#skF_4')
      | k1_tarski(A_94) = '#skF_4'
      | ~ r1_tarski(k1_tarski(A_94),'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_2,c_462])).

tff(c_512,plain,(
    ! [A_95] :
      ( k1_tarski(A_95) = '#skF_4'
      | ~ r1_tarski(k1_tarski(A_95),'#skF_4')
      | r1_xboole_0(k1_tarski(A_95),'#skF_4')
      | ~ r2_hidden(A_95,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_147,c_503])).

tff(c_520,plain,(
    ! [A_96] :
      ( k1_tarski(A_96) = '#skF_4'
      | ~ r1_tarski(k1_tarski(A_96),'#skF_4')
      | ~ r2_hidden(A_96,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_512,c_30])).

tff(c_526,plain,(
    ! [A_97] :
      ( k1_tarski(A_97) = '#skF_4'
      | ~ r2_hidden(A_97,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_28,c_520])).

tff(c_541,plain,(
    k1_tarski('#skF_5') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_63,c_526])).

tff(c_552,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_541])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:32:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.21/2.08  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.21/2.09  
% 3.21/2.09  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.23/2.09  %$ r2_xboole_0 > r2_hidden > r1_xboole_0 > r1_tarski > k2_enumset1 > k1_enumset1 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_5 > #skF_4 > #skF_3 > #skF_2 > #skF_1
% 3.23/2.09  
% 3.23/2.09  %Foreground sorts:
% 3.23/2.09  
% 3.23/2.09  
% 3.23/2.09  %Background operators:
% 3.23/2.09  
% 3.23/2.09  
% 3.23/2.09  %Foreground operators:
% 3.23/2.09  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.23/2.09  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.23/2.09  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.23/2.09  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.23/2.09  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.23/2.09  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.23/2.09  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.23/2.09  tff('#skF_5', type, '#skF_5': $i).
% 3.23/2.09  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.23/2.09  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.23/2.09  tff(r2_xboole_0, type, r2_xboole_0: ($i * $i) > $o).
% 3.23/2.09  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.23/2.09  tff('#skF_4', type, '#skF_4': $i).
% 3.23/2.09  tff('#skF_3', type, '#skF_3': $i > $i).
% 3.23/2.09  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.23/2.09  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.23/2.09  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.23/2.09  
% 3.23/2.11  tff(f_98, negated_conjecture, ~(![A, B]: ~((~(A = k1_tarski(B)) & ~(A = k1_xboole_0)) & (![C]: ~(r2_hidden(C, A) & ~(C = B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_zfmisc_1)).
% 3.23/2.11  tff(f_68, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 3.23/2.11  tff(f_78, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 3.23/2.11  tff(f_50, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 3.23/2.11  tff(f_83, axiom, (![A, B]: ~(r1_xboole_0(k1_tarski(A), B) & r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l24_zfmisc_1)).
% 3.23/2.11  tff(f_32, axiom, (![A, B]: (r2_xboole_0(A, B) <=> (r1_tarski(A, B) & ~(A = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_xboole_0)).
% 3.23/2.11  tff(f_60, axiom, (![A, B]: ~(r2_xboole_0(A, B) & (![C]: ~(r2_hidden(C, B) & ~r2_hidden(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_xboole_0)).
% 3.23/2.11  tff(c_36, plain, (k1_tarski('#skF_5')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_98])).
% 3.23/2.11  tff(c_34, plain, (k1_xboole_0!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_98])).
% 3.23/2.11  tff(c_49, plain, (![A_30]: (r2_hidden('#skF_3'(A_30), A_30) | k1_xboole_0=A_30)), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.23/2.11  tff(c_32, plain, (![C_24]: (C_24='#skF_5' | ~r2_hidden(C_24, '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_98])).
% 3.23/2.11  tff(c_53, plain, ('#skF_3'('#skF_4')='#skF_5' | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_49, c_32])).
% 3.23/2.11  tff(c_56, plain, ('#skF_3'('#skF_4')='#skF_5'), inference(negUnitSimplification, [status(thm)], [c_34, c_53])).
% 3.23/2.11  tff(c_18, plain, (![A_11]: (r2_hidden('#skF_3'(A_11), A_11) | k1_xboole_0=A_11)), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.23/2.11  tff(c_60, plain, (r2_hidden('#skF_5', '#skF_4') | k1_xboole_0='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_56, c_18])).
% 3.23/2.11  tff(c_63, plain, (r2_hidden('#skF_5', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_34, c_60])).
% 3.23/2.11  tff(c_28, plain, (![A_19, B_20]: (r1_tarski(k1_tarski(A_19), B_20) | ~r2_hidden(A_19, B_20))), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.23/2.11  tff(c_86, plain, (![A_39, B_40]: (r2_hidden('#skF_1'(A_39, B_40), B_40) | r1_xboole_0(A_39, B_40))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.23/2.11  tff(c_92, plain, (![A_41]: ('#skF_1'(A_41, '#skF_4')='#skF_5' | r1_xboole_0(A_41, '#skF_4'))), inference(resolution, [status(thm)], [c_86, c_32])).
% 3.23/2.11  tff(c_30, plain, (![A_21, B_22]: (~r2_hidden(A_21, B_22) | ~r1_xboole_0(k1_tarski(A_21), B_22))), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.23/2.11  tff(c_97, plain, (![A_21]: (~r2_hidden(A_21, '#skF_4') | '#skF_1'(k1_tarski(A_21), '#skF_4')='#skF_5')), inference(resolution, [status(thm)], [c_92, c_30])).
% 3.23/2.11  tff(c_140, plain, (![A_50, B_51]: (r2_hidden('#skF_1'(A_50, B_51), A_50) | r1_xboole_0(A_50, B_51))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.23/2.11  tff(c_147, plain, (![A_21]: (r2_hidden('#skF_5', k1_tarski(A_21)) | r1_xboole_0(k1_tarski(A_21), '#skF_4') | ~r2_hidden(A_21, '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_97, c_140])).
% 3.23/2.11  tff(c_2, plain, (![A_1, B_2]: (r2_xboole_0(A_1, B_2) | B_2=A_1 | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.23/2.11  tff(c_110, plain, (![A_46, B_47]: (r2_hidden('#skF_2'(A_46, B_47), B_47) | ~r2_xboole_0(A_46, B_47))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.23/2.11  tff(c_121, plain, (![A_48]: ('#skF_2'(A_48, '#skF_4')='#skF_5' | ~r2_xboole_0(A_48, '#skF_4'))), inference(resolution, [status(thm)], [c_110, c_32])).
% 3.23/2.11  tff(c_166, plain, (![A_59]: ('#skF_2'(A_59, '#skF_4')='#skF_5' | A_59='#skF_4' | ~r1_tarski(A_59, '#skF_4'))), inference(resolution, [status(thm)], [c_2, c_121])).
% 3.23/2.11  tff(c_244, plain, (![A_66]: ('#skF_2'(k1_tarski(A_66), '#skF_4')='#skF_5' | k1_tarski(A_66)='#skF_4' | ~r2_hidden(A_66, '#skF_4'))), inference(resolution, [status(thm)], [c_28, c_166])).
% 3.23/2.11  tff(c_14, plain, (![A_8, B_9]: (~r2_hidden('#skF_2'(A_8, B_9), A_8) | ~r2_xboole_0(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.23/2.11  tff(c_462, plain, (![A_89]: (~r2_hidden('#skF_5', k1_tarski(A_89)) | ~r2_xboole_0(k1_tarski(A_89), '#skF_4') | k1_tarski(A_89)='#skF_4' | ~r2_hidden(A_89, '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_244, c_14])).
% 3.23/2.11  tff(c_503, plain, (![A_94]: (~r2_hidden('#skF_5', k1_tarski(A_94)) | ~r2_hidden(A_94, '#skF_4') | k1_tarski(A_94)='#skF_4' | ~r1_tarski(k1_tarski(A_94), '#skF_4'))), inference(resolution, [status(thm)], [c_2, c_462])).
% 3.23/2.11  tff(c_512, plain, (![A_95]: (k1_tarski(A_95)='#skF_4' | ~r1_tarski(k1_tarski(A_95), '#skF_4') | r1_xboole_0(k1_tarski(A_95), '#skF_4') | ~r2_hidden(A_95, '#skF_4'))), inference(resolution, [status(thm)], [c_147, c_503])).
% 3.23/2.11  tff(c_520, plain, (![A_96]: (k1_tarski(A_96)='#skF_4' | ~r1_tarski(k1_tarski(A_96), '#skF_4') | ~r2_hidden(A_96, '#skF_4'))), inference(resolution, [status(thm)], [c_512, c_30])).
% 3.23/2.11  tff(c_526, plain, (![A_97]: (k1_tarski(A_97)='#skF_4' | ~r2_hidden(A_97, '#skF_4'))), inference(resolution, [status(thm)], [c_28, c_520])).
% 3.23/2.11  tff(c_541, plain, (k1_tarski('#skF_5')='#skF_4'), inference(resolution, [status(thm)], [c_63, c_526])).
% 3.23/2.11  tff(c_552, plain, $false, inference(negUnitSimplification, [status(thm)], [c_36, c_541])).
% 3.23/2.11  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.23/2.11  
% 3.23/2.11  Inference rules
% 3.23/2.11  ----------------------
% 3.23/2.11  #Ref     : 0
% 3.23/2.11  #Sup     : 109
% 3.23/2.11  #Fact    : 0
% 3.23/2.11  #Define  : 0
% 3.23/2.11  #Split   : 0
% 3.23/2.11  #Chain   : 0
% 3.23/2.11  #Close   : 0
% 3.23/2.11  
% 3.23/2.11  Ordering : KBO
% 3.23/2.11  
% 3.23/2.11  Simplification rules
% 3.23/2.11  ----------------------
% 3.23/2.11  #Subsume      : 32
% 3.23/2.11  #Demod        : 35
% 3.23/2.11  #Tautology    : 43
% 3.23/2.11  #SimpNegUnit  : 7
% 3.27/2.11  #BackRed      : 0
% 3.27/2.11  
% 3.27/2.11  #Partial instantiations: 0
% 3.27/2.11  #Strategies tried      : 1
% 3.27/2.11  
% 3.27/2.11  Timing (in seconds)
% 3.27/2.11  ----------------------
% 3.28/2.12  Preprocessing        : 0.53
% 3.28/2.12  Parsing              : 0.29
% 3.28/2.12  CNF conversion       : 0.03
% 3.28/2.12  Main loop            : 0.63
% 3.28/2.12  Inferencing          : 0.25
% 3.28/2.12  Reduction            : 0.14
% 3.28/2.12  Demodulation         : 0.09
% 3.28/2.12  BG Simplification    : 0.03
% 3.28/2.12  Subsumption          : 0.18
% 3.28/2.12  Abstraction          : 0.02
% 3.28/2.12  MUC search           : 0.00
% 3.28/2.12  Cooper               : 0.00
% 3.28/2.12  Total                : 1.21
% 3.28/2.12  Index Insertion      : 0.00
% 3.28/2.12  Index Deletion       : 0.00
% 3.28/2.12  Index Matching       : 0.00
% 3.28/2.12  BG Taut test         : 0.00
%------------------------------------------------------------------------------
