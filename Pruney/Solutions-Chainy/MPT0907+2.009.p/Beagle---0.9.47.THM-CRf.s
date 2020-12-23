%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:09:56 EST 2020

% Result     : Theorem 1.98s
% Output     : CNFRefutation 1.98s
% Verified   : 
% Statistics : Number of formulae       :   46 (  62 expanded)
%              Number of leaves         :   20 (  30 expanded)
%              Depth                    :    7
%              Number of atoms          :   57 (  90 expanded)
%              Number of equality atoms :   19 (  34 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > m1_subset_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_mcart_1 > k1_zfmisc_1 > k1_mcart_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_mcart_1,type,(
    k2_mcart_1: $i > $i )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_mcart_1,type,(
    k1_mcart_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_43,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_74,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r2_hidden(A,k2_zfmisc_1(B,C))
       => ( A != k1_mcart_1(A)
          & A != k2_mcart_1(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_mcart_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

tff(f_65,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) != k1_xboole_0
     => ! [C] :
          ( m1_subset_1(C,k2_zfmisc_1(A,B))
         => ( C != k1_mcart_1(C)
            & C != k2_mcart_1(C) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_mcart_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

tff(f_34,axiom,(
    ! [A,B] : ~ r2_hidden(A,k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_zfmisc_1)).

tff(c_12,plain,(
    ! [A_11] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_11)) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_22,plain,
    ( k2_mcart_1('#skF_1') = '#skF_1'
    | k1_mcart_1('#skF_1') = '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_27,plain,(
    k1_mcart_1('#skF_1') = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_22])).

tff(c_24,plain,(
    r2_hidden('#skF_1',k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_32,plain,(
    ! [A_24,B_25] :
      ( m1_subset_1(A_24,B_25)
      | ~ r2_hidden(A_24,B_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_36,plain,(
    m1_subset_1('#skF_1',k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_24,c_32])).

tff(c_49,plain,(
    ! [C_43,A_44,B_45] :
      ( k1_mcart_1(C_43) != C_43
      | ~ m1_subset_1(C_43,k2_zfmisc_1(A_44,B_45))
      | k2_zfmisc_1(A_44,B_45) = k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_52,plain,
    ( k1_mcart_1('#skF_1') != '#skF_1'
    | k2_zfmisc_1('#skF_2','#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_36,c_49])).

tff(c_55,plain,(
    k2_zfmisc_1('#skF_2','#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_27,c_52])).

tff(c_38,plain,(
    ! [C_30,A_31,B_32] :
      ( r2_hidden(C_30,A_31)
      | ~ r2_hidden(C_30,B_32)
      | ~ m1_subset_1(B_32,k1_zfmisc_1(A_31)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_41,plain,(
    ! [A_31] :
      ( r2_hidden('#skF_1',A_31)
      | ~ m1_subset_1(k2_zfmisc_1('#skF_2','#skF_3'),k1_zfmisc_1(A_31)) ) ),
    inference(resolution,[status(thm)],[c_24,c_38])).

tff(c_56,plain,(
    ! [A_31] :
      ( r2_hidden('#skF_1',A_31)
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_31)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_55,c_41])).

tff(c_83,plain,(
    ! [A_49] : r2_hidden('#skF_1',A_49) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_56])).

tff(c_8,plain,(
    ! [A_5,B_6] : ~ r2_hidden(A_5,k2_zfmisc_1(A_5,B_6)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_100,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_83,c_8])).

tff(c_101,plain,(
    k2_mcart_1('#skF_1') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_22])).

tff(c_107,plain,(
    ! [A_50,B_51] :
      ( m1_subset_1(A_50,B_51)
      | ~ r2_hidden(A_50,B_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_111,plain,(
    m1_subset_1('#skF_1',k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_24,c_107])).

tff(c_129,plain,(
    ! [C_72,A_73,B_74] :
      ( k2_mcart_1(C_72) != C_72
      | ~ m1_subset_1(C_72,k2_zfmisc_1(A_73,B_74))
      | k2_zfmisc_1(A_73,B_74) = k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_132,plain,
    ( k2_mcart_1('#skF_1') != '#skF_1'
    | k2_zfmisc_1('#skF_2','#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_111,c_129])).

tff(c_135,plain,(
    k2_zfmisc_1('#skF_2','#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_101,c_132])).

tff(c_113,plain,(
    ! [C_56,A_57,B_58] :
      ( r2_hidden(C_56,A_57)
      | ~ r2_hidden(C_56,B_58)
      | ~ m1_subset_1(B_58,k1_zfmisc_1(A_57)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_116,plain,(
    ! [A_57] :
      ( r2_hidden('#skF_1',A_57)
      | ~ m1_subset_1(k2_zfmisc_1('#skF_2','#skF_3'),k1_zfmisc_1(A_57)) ) ),
    inference(resolution,[status(thm)],[c_24,c_113])).

tff(c_136,plain,(
    ! [A_57] :
      ( r2_hidden('#skF_1',A_57)
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_57)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_135,c_116])).

tff(c_162,plain,(
    ! [A_75] : r2_hidden('#skF_1',A_75) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_136])).

tff(c_179,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_162,c_8])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n025.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 13:16:50 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.98/1.23  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.98/1.24  
% 1.98/1.24  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.98/1.24  %$ r2_hidden > m1_subset_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_mcart_1 > k1_zfmisc_1 > k1_mcart_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 1.98/1.24  
% 1.98/1.24  %Foreground sorts:
% 1.98/1.24  
% 1.98/1.24  
% 1.98/1.24  %Background operators:
% 1.98/1.24  
% 1.98/1.24  
% 1.98/1.24  %Foreground operators:
% 1.98/1.24  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.98/1.24  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.98/1.24  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 1.98/1.24  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.98/1.24  tff('#skF_2', type, '#skF_2': $i).
% 1.98/1.24  tff('#skF_3', type, '#skF_3': $i).
% 1.98/1.24  tff('#skF_1', type, '#skF_1': $i).
% 1.98/1.24  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.98/1.24  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.98/1.24  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 1.98/1.24  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.98/1.24  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.98/1.24  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 1.98/1.24  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.98/1.24  
% 1.98/1.25  tff(f_43, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 1.98/1.25  tff(f_74, negated_conjecture, ~(![A, B, C]: (r2_hidden(A, k2_zfmisc_1(B, C)) => (~(A = k1_mcart_1(A)) & ~(A = k2_mcart_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t67_mcart_1)).
% 1.98/1.25  tff(f_47, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_subset)).
% 1.98/1.25  tff(f_65, axiom, (![A, B]: (~(k2_zfmisc_1(A, B) = k1_xboole_0) => (![C]: (m1_subset_1(C, k2_zfmisc_1(A, B)) => (~(C = k1_mcart_1(C)) & ~(C = k2_mcart_1(C))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t66_mcart_1)).
% 1.98/1.25  tff(f_41, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_subset_1)).
% 1.98/1.25  tff(f_34, axiom, (![A, B]: ~r2_hidden(A, k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t152_zfmisc_1)).
% 1.98/1.25  tff(c_12, plain, (![A_11]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_11)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.98/1.25  tff(c_22, plain, (k2_mcart_1('#skF_1')='#skF_1' | k1_mcart_1('#skF_1')='#skF_1'), inference(cnfTransformation, [status(thm)], [f_74])).
% 1.98/1.25  tff(c_27, plain, (k1_mcart_1('#skF_1')='#skF_1'), inference(splitLeft, [status(thm)], [c_22])).
% 1.98/1.25  tff(c_24, plain, (r2_hidden('#skF_1', k2_zfmisc_1('#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_74])).
% 1.98/1.25  tff(c_32, plain, (![A_24, B_25]: (m1_subset_1(A_24, B_25) | ~r2_hidden(A_24, B_25))), inference(cnfTransformation, [status(thm)], [f_47])).
% 1.98/1.25  tff(c_36, plain, (m1_subset_1('#skF_1', k2_zfmisc_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_24, c_32])).
% 1.98/1.25  tff(c_49, plain, (![C_43, A_44, B_45]: (k1_mcart_1(C_43)!=C_43 | ~m1_subset_1(C_43, k2_zfmisc_1(A_44, B_45)) | k2_zfmisc_1(A_44, B_45)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_65])).
% 1.98/1.25  tff(c_52, plain, (k1_mcart_1('#skF_1')!='#skF_1' | k2_zfmisc_1('#skF_2', '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_36, c_49])).
% 1.98/1.25  tff(c_55, plain, (k2_zfmisc_1('#skF_2', '#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_27, c_52])).
% 1.98/1.25  tff(c_38, plain, (![C_30, A_31, B_32]: (r2_hidden(C_30, A_31) | ~r2_hidden(C_30, B_32) | ~m1_subset_1(B_32, k1_zfmisc_1(A_31)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.98/1.25  tff(c_41, plain, (![A_31]: (r2_hidden('#skF_1', A_31) | ~m1_subset_1(k2_zfmisc_1('#skF_2', '#skF_3'), k1_zfmisc_1(A_31)))), inference(resolution, [status(thm)], [c_24, c_38])).
% 1.98/1.25  tff(c_56, plain, (![A_31]: (r2_hidden('#skF_1', A_31) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_31)))), inference(demodulation, [status(thm), theory('equality')], [c_55, c_41])).
% 1.98/1.25  tff(c_83, plain, (![A_49]: (r2_hidden('#skF_1', A_49))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_56])).
% 1.98/1.25  tff(c_8, plain, (![A_5, B_6]: (~r2_hidden(A_5, k2_zfmisc_1(A_5, B_6)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 1.98/1.25  tff(c_100, plain, $false, inference(resolution, [status(thm)], [c_83, c_8])).
% 1.98/1.25  tff(c_101, plain, (k2_mcart_1('#skF_1')='#skF_1'), inference(splitRight, [status(thm)], [c_22])).
% 1.98/1.25  tff(c_107, plain, (![A_50, B_51]: (m1_subset_1(A_50, B_51) | ~r2_hidden(A_50, B_51))), inference(cnfTransformation, [status(thm)], [f_47])).
% 1.98/1.25  tff(c_111, plain, (m1_subset_1('#skF_1', k2_zfmisc_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_24, c_107])).
% 1.98/1.25  tff(c_129, plain, (![C_72, A_73, B_74]: (k2_mcart_1(C_72)!=C_72 | ~m1_subset_1(C_72, k2_zfmisc_1(A_73, B_74)) | k2_zfmisc_1(A_73, B_74)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_65])).
% 1.98/1.25  tff(c_132, plain, (k2_mcart_1('#skF_1')!='#skF_1' | k2_zfmisc_1('#skF_2', '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_111, c_129])).
% 1.98/1.25  tff(c_135, plain, (k2_zfmisc_1('#skF_2', '#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_101, c_132])).
% 1.98/1.25  tff(c_113, plain, (![C_56, A_57, B_58]: (r2_hidden(C_56, A_57) | ~r2_hidden(C_56, B_58) | ~m1_subset_1(B_58, k1_zfmisc_1(A_57)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.98/1.25  tff(c_116, plain, (![A_57]: (r2_hidden('#skF_1', A_57) | ~m1_subset_1(k2_zfmisc_1('#skF_2', '#skF_3'), k1_zfmisc_1(A_57)))), inference(resolution, [status(thm)], [c_24, c_113])).
% 1.98/1.25  tff(c_136, plain, (![A_57]: (r2_hidden('#skF_1', A_57) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_57)))), inference(demodulation, [status(thm), theory('equality')], [c_135, c_116])).
% 1.98/1.25  tff(c_162, plain, (![A_75]: (r2_hidden('#skF_1', A_75))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_136])).
% 1.98/1.25  tff(c_179, plain, $false, inference(resolution, [status(thm)], [c_162, c_8])).
% 1.98/1.25  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.98/1.25  
% 1.98/1.25  Inference rules
% 1.98/1.25  ----------------------
% 1.98/1.25  #Ref     : 0
% 1.98/1.25  #Sup     : 35
% 1.98/1.25  #Fact    : 0
% 1.98/1.25  #Define  : 0
% 1.98/1.25  #Split   : 1
% 1.98/1.25  #Chain   : 0
% 1.98/1.25  #Close   : 0
% 1.98/1.25  
% 1.98/1.25  Ordering : KBO
% 1.98/1.25  
% 1.98/1.25  Simplification rules
% 1.98/1.25  ----------------------
% 1.98/1.25  #Subsume      : 1
% 1.98/1.25  #Demod        : 16
% 1.98/1.25  #Tautology    : 14
% 1.98/1.25  #SimpNegUnit  : 0
% 1.98/1.25  #BackRed      : 6
% 1.98/1.25  
% 1.98/1.25  #Partial instantiations: 0
% 1.98/1.25  #Strategies tried      : 1
% 1.98/1.25  
% 1.98/1.25  Timing (in seconds)
% 1.98/1.25  ----------------------
% 1.98/1.25  Preprocessing        : 0.29
% 1.98/1.25  Parsing              : 0.17
% 1.98/1.25  CNF conversion       : 0.02
% 1.98/1.25  Main loop            : 0.16
% 1.98/1.25  Inferencing          : 0.06
% 1.98/1.25  Reduction            : 0.05
% 1.98/1.25  Demodulation         : 0.03
% 1.98/1.25  BG Simplification    : 0.01
% 1.98/1.25  Subsumption          : 0.03
% 1.98/1.25  Abstraction          : 0.01
% 1.98/1.25  MUC search           : 0.00
% 1.98/1.25  Cooper               : 0.00
% 1.98/1.25  Total                : 0.48
% 1.98/1.25  Index Insertion      : 0.00
% 1.98/1.25  Index Deletion       : 0.00
% 1.98/1.26  Index Matching       : 0.00
% 1.98/1.26  BG Taut test         : 0.00
%------------------------------------------------------------------------------
