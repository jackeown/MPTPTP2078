%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:56:27 EST 2020

% Result     : Theorem 2.22s
% Output     : CNFRefutation 2.42s
% Verified   : 
% Statistics : Number of formulae       :   52 (  61 expanded)
%              Number of leaves         :   27 (  33 expanded)
%              Depth                    :    8
%              Number of atoms          :   53 (  77 expanded)
%              Number of equality atoms :   22 (  29 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_5 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

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

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_76,negated_conjecture,(
    ~ ! [A,B,C] :
        ( m1_subset_1(C,k1_zfmisc_1(A))
       => ( ( r1_tarski(B,C)
            & r1_tarski(B,k3_subset_1(A,C)) )
         => B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_subset_1)).

tff(f_61,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_63,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_47,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_39,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_53,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_67,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_59,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k4_xboole_0(B,C))
     => ( r1_tarski(A,B)
        & r1_xboole_0(A,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_xboole_1)).

tff(c_24,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_18,plain,(
    ! [A_15] : k4_xboole_0(A_15,k1_xboole_0) = A_15 ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_20,plain,(
    ! [A_16] : r1_xboole_0(A_16,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_6,plain,(
    ! [A_6] :
      ( r2_hidden('#skF_2'(A_6),A_6)
      | k1_xboole_0 = A_6 ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_105,plain,(
    ! [A_35,B_36,C_37] :
      ( ~ r1_xboole_0(A_35,B_36)
      | ~ r2_hidden(C_37,k3_xboole_0(A_35,B_36)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_141,plain,(
    ! [A_42,B_43] :
      ( ~ r1_xboole_0(A_42,B_43)
      | k3_xboole_0(A_42,B_43) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_6,c_105])).

tff(c_154,plain,(
    ! [A_44] : k3_xboole_0(A_44,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_20,c_141])).

tff(c_12,plain,(
    ! [A_10,B_11] : k5_xboole_0(A_10,k3_xboole_0(A_10,B_11)) = k4_xboole_0(A_10,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_162,plain,(
    ! [A_44] : k5_xboole_0(A_44,k1_xboole_0) = k4_xboole_0(A_44,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_154,c_12])).

tff(c_168,plain,(
    ! [A_44] : k5_xboole_0(A_44,k1_xboole_0) = A_44 ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_162])).

tff(c_28,plain,(
    r1_tarski('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_43,plain,(
    ! [A_24,B_25] :
      ( k4_xboole_0(A_24,B_25) = k1_xboole_0
      | ~ r1_tarski(A_24,B_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_55,plain,(
    k4_xboole_0('#skF_4','#skF_5') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_28,c_43])).

tff(c_26,plain,(
    r1_tarski('#skF_4',k3_subset_1('#skF_3','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_30,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_186,plain,(
    ! [A_47,B_48] :
      ( k4_xboole_0(A_47,B_48) = k3_subset_1(A_47,B_48)
      | ~ m1_subset_1(B_48,k1_zfmisc_1(A_47)) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_190,plain,(
    k4_xboole_0('#skF_3','#skF_5') = k3_subset_1('#skF_3','#skF_5') ),
    inference(resolution,[status(thm)],[c_30,c_186])).

tff(c_14,plain,(
    ! [A_12,C_14,B_13] :
      ( r1_xboole_0(A_12,C_14)
      | ~ r1_tarski(A_12,k4_xboole_0(B_13,C_14)) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_305,plain,(
    ! [A_57] :
      ( r1_xboole_0(A_57,'#skF_5')
      | ~ r1_tarski(A_57,k3_subset_1('#skF_3','#skF_5')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_190,c_14])).

tff(c_314,plain,(
    r1_xboole_0('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_26,c_305])).

tff(c_110,plain,(
    ! [A_35,B_36] :
      ( ~ r1_xboole_0(A_35,B_36)
      | k3_xboole_0(A_35,B_36) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_6,c_105])).

tff(c_318,plain,(
    k3_xboole_0('#skF_4','#skF_5') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_314,c_110])).

tff(c_331,plain,(
    k5_xboole_0('#skF_4',k1_xboole_0) = k4_xboole_0('#skF_4','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_318,c_12])).

tff(c_341,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_168,c_55,c_331])).

tff(c_343,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_341])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:48:29 EST 2020
% 0.19/0.34  % CPUTime    : 
% 0.19/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.22/1.37  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.22/1.38  
% 2.22/1.38  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.22/1.38  %$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_5 > #skF_3 > #skF_4 > #skF_1
% 2.22/1.38  
% 2.22/1.38  %Foreground sorts:
% 2.22/1.38  
% 2.22/1.38  
% 2.22/1.38  %Background operators:
% 2.22/1.38  
% 2.22/1.38  
% 2.22/1.38  %Foreground operators:
% 2.22/1.38  tff('#skF_2', type, '#skF_2': $i > $i).
% 2.22/1.38  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.22/1.38  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.22/1.38  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.22/1.38  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.22/1.38  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.22/1.38  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.22/1.38  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 2.22/1.38  tff('#skF_5', type, '#skF_5': $i).
% 2.22/1.38  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.22/1.38  tff('#skF_3', type, '#skF_3': $i).
% 2.22/1.38  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.22/1.38  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.22/1.38  tff('#skF_4', type, '#skF_4': $i).
% 2.22/1.38  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.22/1.38  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.22/1.38  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.22/1.38  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.22/1.38  
% 2.42/1.40  tff(f_76, negated_conjecture, ~(![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => ((r1_tarski(B, C) & r1_tarski(B, k3_subset_1(A, C))) => (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t40_subset_1)).
% 2.42/1.40  tff(f_61, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 2.42/1.40  tff(f_63, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 2.42/1.40  tff(f_47, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 2.42/1.40  tff(f_39, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 2.42/1.40  tff(f_53, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 2.42/1.40  tff(f_51, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 2.42/1.40  tff(f_67, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_subset_1)).
% 2.42/1.40  tff(f_59, axiom, (![A, B, C]: (r1_tarski(A, k4_xboole_0(B, C)) => (r1_tarski(A, B) & r1_xboole_0(A, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t106_xboole_1)).
% 2.42/1.40  tff(c_24, plain, (k1_xboole_0!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.42/1.40  tff(c_18, plain, (![A_15]: (k4_xboole_0(A_15, k1_xboole_0)=A_15)), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.42/1.40  tff(c_20, plain, (![A_16]: (r1_xboole_0(A_16, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.42/1.40  tff(c_6, plain, (![A_6]: (r2_hidden('#skF_2'(A_6), A_6) | k1_xboole_0=A_6)), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.42/1.40  tff(c_105, plain, (![A_35, B_36, C_37]: (~r1_xboole_0(A_35, B_36) | ~r2_hidden(C_37, k3_xboole_0(A_35, B_36)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.42/1.40  tff(c_141, plain, (![A_42, B_43]: (~r1_xboole_0(A_42, B_43) | k3_xboole_0(A_42, B_43)=k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_105])).
% 2.42/1.40  tff(c_154, plain, (![A_44]: (k3_xboole_0(A_44, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_20, c_141])).
% 2.42/1.40  tff(c_12, plain, (![A_10, B_11]: (k5_xboole_0(A_10, k3_xboole_0(A_10, B_11))=k4_xboole_0(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.42/1.40  tff(c_162, plain, (![A_44]: (k5_xboole_0(A_44, k1_xboole_0)=k4_xboole_0(A_44, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_154, c_12])).
% 2.42/1.40  tff(c_168, plain, (![A_44]: (k5_xboole_0(A_44, k1_xboole_0)=A_44)), inference(demodulation, [status(thm), theory('equality')], [c_18, c_162])).
% 2.42/1.40  tff(c_28, plain, (r1_tarski('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.42/1.40  tff(c_43, plain, (![A_24, B_25]: (k4_xboole_0(A_24, B_25)=k1_xboole_0 | ~r1_tarski(A_24, B_25))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.42/1.40  tff(c_55, plain, (k4_xboole_0('#skF_4', '#skF_5')=k1_xboole_0), inference(resolution, [status(thm)], [c_28, c_43])).
% 2.42/1.40  tff(c_26, plain, (r1_tarski('#skF_4', k3_subset_1('#skF_3', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.42/1.40  tff(c_30, plain, (m1_subset_1('#skF_5', k1_zfmisc_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.42/1.40  tff(c_186, plain, (![A_47, B_48]: (k4_xboole_0(A_47, B_48)=k3_subset_1(A_47, B_48) | ~m1_subset_1(B_48, k1_zfmisc_1(A_47)))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.42/1.40  tff(c_190, plain, (k4_xboole_0('#skF_3', '#skF_5')=k3_subset_1('#skF_3', '#skF_5')), inference(resolution, [status(thm)], [c_30, c_186])).
% 2.42/1.40  tff(c_14, plain, (![A_12, C_14, B_13]: (r1_xboole_0(A_12, C_14) | ~r1_tarski(A_12, k4_xboole_0(B_13, C_14)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.42/1.40  tff(c_305, plain, (![A_57]: (r1_xboole_0(A_57, '#skF_5') | ~r1_tarski(A_57, k3_subset_1('#skF_3', '#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_190, c_14])).
% 2.42/1.40  tff(c_314, plain, (r1_xboole_0('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_26, c_305])).
% 2.42/1.40  tff(c_110, plain, (![A_35, B_36]: (~r1_xboole_0(A_35, B_36) | k3_xboole_0(A_35, B_36)=k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_105])).
% 2.42/1.40  tff(c_318, plain, (k3_xboole_0('#skF_4', '#skF_5')=k1_xboole_0), inference(resolution, [status(thm)], [c_314, c_110])).
% 2.42/1.40  tff(c_331, plain, (k5_xboole_0('#skF_4', k1_xboole_0)=k4_xboole_0('#skF_4', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_318, c_12])).
% 2.42/1.40  tff(c_341, plain, (k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_168, c_55, c_331])).
% 2.42/1.40  tff(c_343, plain, $false, inference(negUnitSimplification, [status(thm)], [c_24, c_341])).
% 2.42/1.40  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.42/1.40  
% 2.42/1.40  Inference rules
% 2.42/1.40  ----------------------
% 2.42/1.40  #Ref     : 0
% 2.42/1.40  #Sup     : 76
% 2.42/1.40  #Fact    : 0
% 2.42/1.40  #Define  : 0
% 2.42/1.40  #Split   : 1
% 2.42/1.40  #Chain   : 0
% 2.42/1.40  #Close   : 0
% 2.42/1.40  
% 2.42/1.40  Ordering : KBO
% 2.42/1.40  
% 2.42/1.40  Simplification rules
% 2.42/1.40  ----------------------
% 2.42/1.40  #Subsume      : 9
% 2.42/1.40  #Demod        : 11
% 2.42/1.40  #Tautology    : 31
% 2.42/1.40  #SimpNegUnit  : 6
% 2.42/1.40  #BackRed      : 0
% 2.42/1.40  
% 2.42/1.40  #Partial instantiations: 0
% 2.42/1.40  #Strategies tried      : 1
% 2.42/1.40  
% 2.42/1.40  Timing (in seconds)
% 2.42/1.40  ----------------------
% 2.42/1.40  Preprocessing        : 0.39
% 2.42/1.40  Parsing              : 0.22
% 2.42/1.40  CNF conversion       : 0.02
% 2.42/1.40  Main loop            : 0.25
% 2.42/1.40  Inferencing          : 0.10
% 2.42/1.40  Reduction            : 0.08
% 2.42/1.40  Demodulation         : 0.05
% 2.42/1.40  BG Simplification    : 0.01
% 2.42/1.40  Subsumption          : 0.04
% 2.42/1.40  Abstraction          : 0.01
% 2.42/1.40  MUC search           : 0.00
% 2.42/1.40  Cooper               : 0.00
% 2.42/1.40  Total                : 0.67
% 2.42/1.40  Index Insertion      : 0.00
% 2.42/1.40  Index Deletion       : 0.00
% 2.42/1.40  Index Matching       : 0.00
% 2.42/1.40  BG Taut test         : 0.00
%------------------------------------------------------------------------------
