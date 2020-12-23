%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:56:08 EST 2020

% Result     : Theorem 1.90s
% Output     : CNFRefutation 1.90s
% Verified   : 
% Statistics : Number of formulae       :   54 (  75 expanded)
%              Number of leaves         :   27 (  37 expanded)
%              Depth                    :    9
%              Number of atoms          :   60 (  98 expanded)
%              Number of equality atoms :   16 (  35 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_subset_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_4 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_subset_1,type,(
    k1_subset_1: $i > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_59,axiom,(
    ! [A] : k1_subset_1(A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_subset_1)).

tff(f_70,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => ( r1_tarski(B,k3_subset_1(A,B))
        <=> B = k1_subset_1(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_subset_1)).

tff(f_53,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_43,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_57,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_63,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

tff(c_32,plain,(
    ! [A_17] : k1_subset_1(A_17) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_38,plain,
    ( k1_subset_1('#skF_4') != '#skF_5'
    | ~ r1_tarski('#skF_5',k3_subset_1('#skF_4','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_45,plain,
    ( k1_xboole_0 != '#skF_5'
    | ~ r1_tarski('#skF_5',k3_subset_1('#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_38])).

tff(c_56,plain,(
    ~ r1_tarski('#skF_5',k3_subset_1('#skF_4','#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_45])).

tff(c_44,plain,
    ( r1_tarski('#skF_5',k3_subset_1('#skF_4','#skF_5'))
    | k1_subset_1('#skF_4') = '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_46,plain,
    ( r1_tarski('#skF_5',k3_subset_1('#skF_4','#skF_5'))
    | k1_xboole_0 = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_44])).

tff(c_63,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_46])).

tff(c_26,plain,(
    ! [A_14] : r1_tarski(k1_xboole_0,A_14) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_65,plain,(
    ! [A_14] : r1_tarski('#skF_5',A_14) ),
    inference(demodulation,[status(thm),theory(equality)],[c_63,c_26])).

tff(c_74,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_65,c_56])).

tff(c_75,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(splitRight,[status(thm)],[c_45])).

tff(c_20,plain,(
    ! [A_7] :
      ( r2_hidden('#skF_3'(A_7),A_7)
      | k1_xboole_0 = A_7 ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_30,plain,(
    ! [A_15,B_16] :
      ( r1_tarski(k1_tarski(A_15),B_16)
      | ~ r2_hidden(A_15,B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_76,plain,(
    r1_tarski('#skF_5',k3_subset_1('#skF_4','#skF_5')) ),
    inference(splitRight,[status(thm)],[c_45])).

tff(c_106,plain,(
    ! [A_42,C_43,B_44] :
      ( r1_tarski(A_42,C_43)
      | ~ r1_tarski(B_44,C_43)
      | ~ r1_tarski(A_42,B_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_144,plain,(
    ! [A_51] :
      ( r1_tarski(A_51,k3_subset_1('#skF_4','#skF_5'))
      | ~ r1_tarski(A_51,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_76,c_106])).

tff(c_28,plain,(
    ! [A_15,B_16] :
      ( r2_hidden(A_15,B_16)
      | ~ r1_tarski(k1_tarski(A_15),B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_152,plain,(
    ! [A_15] :
      ( r2_hidden(A_15,k3_subset_1('#skF_4','#skF_5'))
      | ~ r1_tarski(k1_tarski(A_15),'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_144,c_28])).

tff(c_36,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_154,plain,(
    ! [A_53,B_54] :
      ( k4_xboole_0(A_53,B_54) = k3_subset_1(A_53,B_54)
      | ~ m1_subset_1(B_54,k1_zfmisc_1(A_53)) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_158,plain,(
    k4_xboole_0('#skF_4','#skF_5') = k3_subset_1('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_36,c_154])).

tff(c_4,plain,(
    ! [D_6,B_2,A_1] :
      ( ~ r2_hidden(D_6,B_2)
      | ~ r2_hidden(D_6,k4_xboole_0(A_1,B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_190,plain,(
    ! [D_57] :
      ( ~ r2_hidden(D_57,'#skF_5')
      | ~ r2_hidden(D_57,k3_subset_1('#skF_4','#skF_5')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_158,c_4])).

tff(c_208,plain,(
    ! [A_59] :
      ( ~ r2_hidden(A_59,'#skF_5')
      | ~ r1_tarski(k1_tarski(A_59),'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_152,c_190])).

tff(c_219,plain,(
    ! [A_60] : ~ r2_hidden(A_60,'#skF_5') ),
    inference(resolution,[status(thm)],[c_30,c_208])).

tff(c_223,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_20,c_219])).

tff(c_227,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_75,c_223])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:29:34 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.90/1.19  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.90/1.20  
% 1.90/1.20  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.90/1.20  %$ r2_hidden > r1_tarski > m1_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_subset_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_4 > #skF_3
% 1.90/1.20  
% 1.90/1.20  %Foreground sorts:
% 1.90/1.20  
% 1.90/1.20  
% 1.90/1.20  %Background operators:
% 1.90/1.20  
% 1.90/1.20  
% 1.90/1.20  %Foreground operators:
% 1.90/1.20  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 1.90/1.20  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.90/1.20  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.90/1.20  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.90/1.20  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.90/1.20  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.90/1.20  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 1.90/1.20  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.90/1.20  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 1.90/1.20  tff('#skF_5', type, '#skF_5': $i).
% 1.90/1.20  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 1.90/1.20  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.90/1.20  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.90/1.20  tff('#skF_4', type, '#skF_4': $i).
% 1.90/1.20  tff('#skF_3', type, '#skF_3': $i > $i).
% 1.90/1.20  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.90/1.20  tff(k1_subset_1, type, k1_subset_1: $i > $i).
% 1.90/1.20  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.90/1.20  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.90/1.20  
% 1.90/1.21  tff(f_59, axiom, (![A]: (k1_subset_1(A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_subset_1)).
% 1.90/1.21  tff(f_70, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (r1_tarski(B, k3_subset_1(A, B)) <=> (B = k1_subset_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_subset_1)).
% 1.90/1.21  tff(f_53, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 1.90/1.21  tff(f_43, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 1.90/1.21  tff(f_57, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 1.90/1.21  tff(f_51, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 1.90/1.21  tff(f_63, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 1.90/1.21  tff(f_35, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 1.90/1.21  tff(c_32, plain, (![A_17]: (k1_subset_1(A_17)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_59])).
% 1.90/1.21  tff(c_38, plain, (k1_subset_1('#skF_4')!='#skF_5' | ~r1_tarski('#skF_5', k3_subset_1('#skF_4', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_70])).
% 1.90/1.21  tff(c_45, plain, (k1_xboole_0!='#skF_5' | ~r1_tarski('#skF_5', k3_subset_1('#skF_4', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_38])).
% 1.90/1.21  tff(c_56, plain, (~r1_tarski('#skF_5', k3_subset_1('#skF_4', '#skF_5'))), inference(splitLeft, [status(thm)], [c_45])).
% 1.90/1.21  tff(c_44, plain, (r1_tarski('#skF_5', k3_subset_1('#skF_4', '#skF_5')) | k1_subset_1('#skF_4')='#skF_5'), inference(cnfTransformation, [status(thm)], [f_70])).
% 1.90/1.21  tff(c_46, plain, (r1_tarski('#skF_5', k3_subset_1('#skF_4', '#skF_5')) | k1_xboole_0='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_32, c_44])).
% 1.90/1.21  tff(c_63, plain, (k1_xboole_0='#skF_5'), inference(negUnitSimplification, [status(thm)], [c_56, c_46])).
% 1.90/1.21  tff(c_26, plain, (![A_14]: (r1_tarski(k1_xboole_0, A_14))), inference(cnfTransformation, [status(thm)], [f_53])).
% 1.90/1.21  tff(c_65, plain, (![A_14]: (r1_tarski('#skF_5', A_14))), inference(demodulation, [status(thm), theory('equality')], [c_63, c_26])).
% 1.90/1.21  tff(c_74, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_65, c_56])).
% 1.90/1.21  tff(c_75, plain, (k1_xboole_0!='#skF_5'), inference(splitRight, [status(thm)], [c_45])).
% 1.90/1.21  tff(c_20, plain, (![A_7]: (r2_hidden('#skF_3'(A_7), A_7) | k1_xboole_0=A_7)), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.90/1.21  tff(c_30, plain, (![A_15, B_16]: (r1_tarski(k1_tarski(A_15), B_16) | ~r2_hidden(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_57])).
% 1.90/1.21  tff(c_76, plain, (r1_tarski('#skF_5', k3_subset_1('#skF_4', '#skF_5'))), inference(splitRight, [status(thm)], [c_45])).
% 1.90/1.21  tff(c_106, plain, (![A_42, C_43, B_44]: (r1_tarski(A_42, C_43) | ~r1_tarski(B_44, C_43) | ~r1_tarski(A_42, B_44))), inference(cnfTransformation, [status(thm)], [f_51])).
% 1.90/1.21  tff(c_144, plain, (![A_51]: (r1_tarski(A_51, k3_subset_1('#skF_4', '#skF_5')) | ~r1_tarski(A_51, '#skF_5'))), inference(resolution, [status(thm)], [c_76, c_106])).
% 1.90/1.21  tff(c_28, plain, (![A_15, B_16]: (r2_hidden(A_15, B_16) | ~r1_tarski(k1_tarski(A_15), B_16))), inference(cnfTransformation, [status(thm)], [f_57])).
% 1.90/1.21  tff(c_152, plain, (![A_15]: (r2_hidden(A_15, k3_subset_1('#skF_4', '#skF_5')) | ~r1_tarski(k1_tarski(A_15), '#skF_5'))), inference(resolution, [status(thm)], [c_144, c_28])).
% 1.90/1.21  tff(c_36, plain, (m1_subset_1('#skF_5', k1_zfmisc_1('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_70])).
% 1.90/1.21  tff(c_154, plain, (![A_53, B_54]: (k4_xboole_0(A_53, B_54)=k3_subset_1(A_53, B_54) | ~m1_subset_1(B_54, k1_zfmisc_1(A_53)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 1.90/1.21  tff(c_158, plain, (k4_xboole_0('#skF_4', '#skF_5')=k3_subset_1('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_36, c_154])).
% 1.90/1.21  tff(c_4, plain, (![D_6, B_2, A_1]: (~r2_hidden(D_6, B_2) | ~r2_hidden(D_6, k4_xboole_0(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.90/1.21  tff(c_190, plain, (![D_57]: (~r2_hidden(D_57, '#skF_5') | ~r2_hidden(D_57, k3_subset_1('#skF_4', '#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_158, c_4])).
% 1.90/1.21  tff(c_208, plain, (![A_59]: (~r2_hidden(A_59, '#skF_5') | ~r1_tarski(k1_tarski(A_59), '#skF_5'))), inference(resolution, [status(thm)], [c_152, c_190])).
% 1.90/1.21  tff(c_219, plain, (![A_60]: (~r2_hidden(A_60, '#skF_5'))), inference(resolution, [status(thm)], [c_30, c_208])).
% 1.90/1.21  tff(c_223, plain, (k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_20, c_219])).
% 1.90/1.21  tff(c_227, plain, $false, inference(negUnitSimplification, [status(thm)], [c_75, c_223])).
% 1.90/1.21  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.90/1.21  
% 1.90/1.21  Inference rules
% 1.90/1.21  ----------------------
% 1.90/1.21  #Ref     : 0
% 1.90/1.21  #Sup     : 36
% 1.90/1.21  #Fact    : 0
% 1.90/1.21  #Define  : 0
% 1.90/1.21  #Split   : 1
% 1.90/1.21  #Chain   : 0
% 1.90/1.21  #Close   : 0
% 1.90/1.21  
% 1.90/1.21  Ordering : KBO
% 1.90/1.21  
% 1.90/1.21  Simplification rules
% 1.90/1.21  ----------------------
% 1.90/1.21  #Subsume      : 5
% 1.90/1.21  #Demod        : 8
% 1.90/1.21  #Tautology    : 15
% 1.90/1.21  #SimpNegUnit  : 4
% 1.90/1.21  #BackRed      : 4
% 1.90/1.21  
% 1.90/1.21  #Partial instantiations: 0
% 1.90/1.21  #Strategies tried      : 1
% 1.90/1.21  
% 1.90/1.21  Timing (in seconds)
% 1.90/1.21  ----------------------
% 1.90/1.21  Preprocessing        : 0.29
% 1.90/1.21  Parsing              : 0.15
% 1.90/1.21  CNF conversion       : 0.02
% 1.90/1.21  Main loop            : 0.16
% 1.90/1.21  Inferencing          : 0.06
% 1.90/1.21  Reduction            : 0.05
% 1.90/1.21  Demodulation         : 0.03
% 1.90/1.21  BG Simplification    : 0.01
% 1.90/1.21  Subsumption          : 0.03
% 1.90/1.21  Abstraction          : 0.01
% 1.90/1.21  MUC search           : 0.00
% 1.90/1.21  Cooper               : 0.00
% 1.90/1.21  Total                : 0.48
% 1.90/1.21  Index Insertion      : 0.00
% 1.90/1.21  Index Deletion       : 0.00
% 1.90/1.21  Index Matching       : 0.00
% 1.90/1.21  BG Taut test         : 0.00
%------------------------------------------------------------------------------
