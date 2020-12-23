%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:56:07 EST 2020

% Result     : Theorem 3.12s
% Output     : CNFRefutation 3.12s
% Verified   : 
% Statistics : Number of formulae       :   62 (  87 expanded)
%              Number of leaves         :   30 (  43 expanded)
%              Depth                    :    9
%              Number of atoms          :   71 ( 121 expanded)
%              Number of equality atoms :   23 (  45 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > k1_subset_1 > k1_xboole_0 > #skF_6 > #skF_4 > #skF_7 > #skF_2 > #skF_8 > #skF_3 > #skF_1 > #skF_5

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_subset_1,type,(
    k1_subset_1: $i > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_67,axiom,(
    ! [A] : k1_subset_1(A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_subset_1)).

tff(f_78,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => ( r1_tarski(B,k3_subset_1(A,B))
        <=> B = k1_subset_1(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_subset_1)).

tff(f_54,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_58,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_42,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_50,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_71,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_170,plain,(
    ! [A_53,B_54] :
      ( r2_hidden('#skF_1'(A_53,B_54),A_53)
      | r1_tarski(A_53,B_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_48,plain,(
    ! [A_24] : k1_subset_1(A_24) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_54,plain,
    ( k1_subset_1('#skF_7') != '#skF_8'
    | ~ r1_tarski('#skF_8',k3_subset_1('#skF_7','#skF_8')) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_61,plain,
    ( k1_xboole_0 != '#skF_8'
    | ~ r1_tarski('#skF_8',k3_subset_1('#skF_7','#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_54])).

tff(c_72,plain,(
    ~ r1_tarski('#skF_8',k3_subset_1('#skF_7','#skF_8')) ),
    inference(splitLeft,[status(thm)],[c_61])).

tff(c_60,plain,
    ( r1_tarski('#skF_8',k3_subset_1('#skF_7','#skF_8'))
    | k1_subset_1('#skF_7') = '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_62,plain,
    ( r1_tarski('#skF_8',k3_subset_1('#skF_7','#skF_8'))
    | k1_xboole_0 = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_60])).

tff(c_93,plain,(
    k1_xboole_0 = '#skF_8' ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_62])).

tff(c_30,plain,(
    ! [A_16] : r1_xboole_0(A_16,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_73,plain,(
    ! [A_30,B_31] :
      ( k4_xboole_0(A_30,B_31) = A_30
      | ~ r1_xboole_0(A_30,B_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_77,plain,(
    ! [A_16] : k4_xboole_0(A_16,k1_xboole_0) = A_16 ),
    inference(resolution,[status(thm)],[c_30,c_73])).

tff(c_94,plain,(
    ! [A_16] : k4_xboole_0(A_16,'#skF_8') = A_16 ),
    inference(demodulation,[status(thm),theory(equality)],[c_93,c_77])).

tff(c_155,plain,(
    ! [D_48,B_49,A_50] :
      ( ~ r2_hidden(D_48,B_49)
      | ~ r2_hidden(D_48,k4_xboole_0(A_50,B_49)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_162,plain,(
    ! [D_48,A_16] :
      ( ~ r2_hidden(D_48,'#skF_8')
      | ~ r2_hidden(D_48,A_16) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_94,c_155])).

tff(c_217,plain,(
    ! [B_62,A_63] :
      ( ~ r2_hidden('#skF_1'('#skF_8',B_62),A_63)
      | r1_tarski('#skF_8',B_62) ) ),
    inference(resolution,[status(thm)],[c_170,c_162])).

tff(c_226,plain,(
    ! [B_2] : r1_tarski('#skF_8',B_2) ),
    inference(resolution,[status(thm)],[c_6,c_217])).

tff(c_231,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_226,c_72])).

tff(c_232,plain,(
    k1_xboole_0 != '#skF_8' ),
    inference(splitRight,[status(thm)],[c_61])).

tff(c_233,plain,(
    r1_tarski('#skF_8',k3_subset_1('#skF_7','#skF_8')) ),
    inference(splitRight,[status(thm)],[c_61])).

tff(c_26,plain,(
    ! [A_12] :
      ( r2_hidden('#skF_4'(A_12),A_12)
      | k1_xboole_0 = A_12 ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_335,plain,(
    ! [C_89,B_90,A_91] :
      ( r2_hidden(C_89,B_90)
      | ~ r2_hidden(C_89,A_91)
      | ~ r1_tarski(A_91,B_90) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_344,plain,(
    ! [A_12,B_90] :
      ( r2_hidden('#skF_4'(A_12),B_90)
      | ~ r1_tarski(A_12,B_90)
      | k1_xboole_0 = A_12 ) ),
    inference(resolution,[status(thm)],[c_26,c_335])).

tff(c_52,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1('#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_396,plain,(
    ! [A_99,B_100] :
      ( k4_xboole_0(A_99,B_100) = k3_subset_1(A_99,B_100)
      | ~ m1_subset_1(B_100,k1_zfmisc_1(A_99)) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_400,plain,(
    k4_xboole_0('#skF_7','#skF_8') = k3_subset_1('#skF_7','#skF_8') ),
    inference(resolution,[status(thm)],[c_52,c_396])).

tff(c_10,plain,(
    ! [D_11,B_7,A_6] :
      ( ~ r2_hidden(D_11,B_7)
      | ~ r2_hidden(D_11,k4_xboole_0(A_6,B_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_618,plain,(
    ! [D_113] :
      ( ~ r2_hidden(D_113,'#skF_8')
      | ~ r2_hidden(D_113,k3_subset_1('#skF_7','#skF_8')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_400,c_10])).

tff(c_1429,plain,(
    ! [A_164] :
      ( ~ r2_hidden('#skF_4'(A_164),'#skF_8')
      | ~ r1_tarski(A_164,k3_subset_1('#skF_7','#skF_8'))
      | k1_xboole_0 = A_164 ) ),
    inference(resolution,[status(thm)],[c_344,c_618])).

tff(c_1448,plain,
    ( ~ r1_tarski('#skF_8',k3_subset_1('#skF_7','#skF_8'))
    | k1_xboole_0 = '#skF_8' ),
    inference(resolution,[status(thm)],[c_26,c_1429])).

tff(c_1458,plain,(
    k1_xboole_0 = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_233,c_1448])).

tff(c_1460,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_232,c_1458])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n019.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 16:43:22 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.12/1.47  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.12/1.48  
% 3.12/1.48  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.12/1.48  %$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > k1_subset_1 > k1_xboole_0 > #skF_6 > #skF_4 > #skF_7 > #skF_2 > #skF_8 > #skF_3 > #skF_1 > #skF_5
% 3.12/1.48  
% 3.12/1.48  %Foreground sorts:
% 3.12/1.48  
% 3.12/1.48  
% 3.12/1.48  %Background operators:
% 3.12/1.48  
% 3.12/1.48  
% 3.12/1.48  %Foreground operators:
% 3.12/1.48  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 3.12/1.48  tff('#skF_4', type, '#skF_4': $i > $i).
% 3.12/1.48  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.12/1.48  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.12/1.48  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.12/1.48  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.12/1.48  tff('#skF_7', type, '#skF_7': $i).
% 3.12/1.48  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.12/1.48  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.12/1.48  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 3.12/1.48  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.12/1.48  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 3.12/1.48  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.12/1.48  tff('#skF_8', type, '#skF_8': $i).
% 3.12/1.48  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.12/1.48  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 3.12/1.48  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.12/1.48  tff(k1_subset_1, type, k1_subset_1: $i > $i).
% 3.12/1.48  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.12/1.48  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.12/1.48  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 3.12/1.48  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.12/1.48  
% 3.12/1.49  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 3.12/1.49  tff(f_67, axiom, (![A]: (k1_subset_1(A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_subset_1)).
% 3.12/1.49  tff(f_78, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (r1_tarski(B, k3_subset_1(A, B)) <=> (B = k1_subset_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_subset_1)).
% 3.12/1.49  tff(f_54, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 3.12/1.49  tff(f_58, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_xboole_1)).
% 3.12/1.49  tff(f_42, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 3.12/1.49  tff(f_50, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 3.12/1.49  tff(f_71, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 3.12/1.49  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.12/1.49  tff(c_170, plain, (![A_53, B_54]: (r2_hidden('#skF_1'(A_53, B_54), A_53) | r1_tarski(A_53, B_54))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.12/1.49  tff(c_48, plain, (![A_24]: (k1_subset_1(A_24)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.12/1.49  tff(c_54, plain, (k1_subset_1('#skF_7')!='#skF_8' | ~r1_tarski('#skF_8', k3_subset_1('#skF_7', '#skF_8'))), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.12/1.49  tff(c_61, plain, (k1_xboole_0!='#skF_8' | ~r1_tarski('#skF_8', k3_subset_1('#skF_7', '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_54])).
% 3.12/1.49  tff(c_72, plain, (~r1_tarski('#skF_8', k3_subset_1('#skF_7', '#skF_8'))), inference(splitLeft, [status(thm)], [c_61])).
% 3.12/1.49  tff(c_60, plain, (r1_tarski('#skF_8', k3_subset_1('#skF_7', '#skF_8')) | k1_subset_1('#skF_7')='#skF_8'), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.12/1.49  tff(c_62, plain, (r1_tarski('#skF_8', k3_subset_1('#skF_7', '#skF_8')) | k1_xboole_0='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_48, c_60])).
% 3.12/1.49  tff(c_93, plain, (k1_xboole_0='#skF_8'), inference(negUnitSimplification, [status(thm)], [c_72, c_62])).
% 3.12/1.49  tff(c_30, plain, (![A_16]: (r1_xboole_0(A_16, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.12/1.49  tff(c_73, plain, (![A_30, B_31]: (k4_xboole_0(A_30, B_31)=A_30 | ~r1_xboole_0(A_30, B_31))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.12/1.49  tff(c_77, plain, (![A_16]: (k4_xboole_0(A_16, k1_xboole_0)=A_16)), inference(resolution, [status(thm)], [c_30, c_73])).
% 3.12/1.49  tff(c_94, plain, (![A_16]: (k4_xboole_0(A_16, '#skF_8')=A_16)), inference(demodulation, [status(thm), theory('equality')], [c_93, c_77])).
% 3.12/1.49  tff(c_155, plain, (![D_48, B_49, A_50]: (~r2_hidden(D_48, B_49) | ~r2_hidden(D_48, k4_xboole_0(A_50, B_49)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.12/1.49  tff(c_162, plain, (![D_48, A_16]: (~r2_hidden(D_48, '#skF_8') | ~r2_hidden(D_48, A_16))), inference(superposition, [status(thm), theory('equality')], [c_94, c_155])).
% 3.12/1.49  tff(c_217, plain, (![B_62, A_63]: (~r2_hidden('#skF_1'('#skF_8', B_62), A_63) | r1_tarski('#skF_8', B_62))), inference(resolution, [status(thm)], [c_170, c_162])).
% 3.12/1.49  tff(c_226, plain, (![B_2]: (r1_tarski('#skF_8', B_2))), inference(resolution, [status(thm)], [c_6, c_217])).
% 3.12/1.49  tff(c_231, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_226, c_72])).
% 3.12/1.49  tff(c_232, plain, (k1_xboole_0!='#skF_8'), inference(splitRight, [status(thm)], [c_61])).
% 3.12/1.49  tff(c_233, plain, (r1_tarski('#skF_8', k3_subset_1('#skF_7', '#skF_8'))), inference(splitRight, [status(thm)], [c_61])).
% 3.12/1.49  tff(c_26, plain, (![A_12]: (r2_hidden('#skF_4'(A_12), A_12) | k1_xboole_0=A_12)), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.12/1.49  tff(c_335, plain, (![C_89, B_90, A_91]: (r2_hidden(C_89, B_90) | ~r2_hidden(C_89, A_91) | ~r1_tarski(A_91, B_90))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.12/1.49  tff(c_344, plain, (![A_12, B_90]: (r2_hidden('#skF_4'(A_12), B_90) | ~r1_tarski(A_12, B_90) | k1_xboole_0=A_12)), inference(resolution, [status(thm)], [c_26, c_335])).
% 3.12/1.49  tff(c_52, plain, (m1_subset_1('#skF_8', k1_zfmisc_1('#skF_7'))), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.12/1.49  tff(c_396, plain, (![A_99, B_100]: (k4_xboole_0(A_99, B_100)=k3_subset_1(A_99, B_100) | ~m1_subset_1(B_100, k1_zfmisc_1(A_99)))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.12/1.49  tff(c_400, plain, (k4_xboole_0('#skF_7', '#skF_8')=k3_subset_1('#skF_7', '#skF_8')), inference(resolution, [status(thm)], [c_52, c_396])).
% 3.12/1.49  tff(c_10, plain, (![D_11, B_7, A_6]: (~r2_hidden(D_11, B_7) | ~r2_hidden(D_11, k4_xboole_0(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.12/1.49  tff(c_618, plain, (![D_113]: (~r2_hidden(D_113, '#skF_8') | ~r2_hidden(D_113, k3_subset_1('#skF_7', '#skF_8')))), inference(superposition, [status(thm), theory('equality')], [c_400, c_10])).
% 3.12/1.49  tff(c_1429, plain, (![A_164]: (~r2_hidden('#skF_4'(A_164), '#skF_8') | ~r1_tarski(A_164, k3_subset_1('#skF_7', '#skF_8')) | k1_xboole_0=A_164)), inference(resolution, [status(thm)], [c_344, c_618])).
% 3.12/1.49  tff(c_1448, plain, (~r1_tarski('#skF_8', k3_subset_1('#skF_7', '#skF_8')) | k1_xboole_0='#skF_8'), inference(resolution, [status(thm)], [c_26, c_1429])).
% 3.12/1.49  tff(c_1458, plain, (k1_xboole_0='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_233, c_1448])).
% 3.12/1.49  tff(c_1460, plain, $false, inference(negUnitSimplification, [status(thm)], [c_232, c_1458])).
% 3.12/1.49  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.12/1.49  
% 3.12/1.49  Inference rules
% 3.12/1.49  ----------------------
% 3.12/1.49  #Ref     : 0
% 3.12/1.49  #Sup     : 295
% 3.12/1.49  #Fact    : 0
% 3.12/1.49  #Define  : 0
% 3.12/1.49  #Split   : 9
% 3.12/1.49  #Chain   : 0
% 3.12/1.49  #Close   : 0
% 3.12/1.49  
% 3.12/1.49  Ordering : KBO
% 3.12/1.49  
% 3.12/1.49  Simplification rules
% 3.12/1.49  ----------------------
% 3.12/1.49  #Subsume      : 34
% 3.12/1.49  #Demod        : 67
% 3.12/1.49  #Tautology    : 108
% 3.12/1.49  #SimpNegUnit  : 24
% 3.12/1.49  #BackRed      : 13
% 3.12/1.49  
% 3.12/1.49  #Partial instantiations: 0
% 3.12/1.49  #Strategies tried      : 1
% 3.12/1.49  
% 3.12/1.49  Timing (in seconds)
% 3.12/1.49  ----------------------
% 3.12/1.49  Preprocessing        : 0.31
% 3.12/1.50  Parsing              : 0.16
% 3.12/1.50  CNF conversion       : 0.02
% 3.12/1.50  Main loop            : 0.43
% 3.12/1.50  Inferencing          : 0.15
% 3.12/1.50  Reduction            : 0.12
% 3.12/1.50  Demodulation         : 0.08
% 3.12/1.50  BG Simplification    : 0.02
% 3.12/1.50  Subsumption          : 0.09
% 3.12/1.50  Abstraction          : 0.02
% 3.12/1.50  MUC search           : 0.00
% 3.12/1.50  Cooper               : 0.00
% 3.12/1.50  Total                : 0.76
% 3.12/1.50  Index Insertion      : 0.00
% 3.12/1.50  Index Deletion       : 0.00
% 3.12/1.50  Index Matching       : 0.00
% 3.12/1.50  BG Taut test         : 0.00
%------------------------------------------------------------------------------
