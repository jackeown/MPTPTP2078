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
% DateTime   : Thu Dec  3 10:09:55 EST 2020

% Result     : Theorem 1.88s
% Output     : CNFRefutation 1.97s
% Verified   : 
% Statistics : Number of formulae       :   47 (  63 expanded)
%              Number of leaves         :   21 (  31 expanded)
%              Depth                    :    7
%              Number of atoms          :   57 (  90 expanded)
%              Number of equality atoms :   19 (  34 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_mcart_1 > k1_mcart_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1

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

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_mcart_1,type,(
    k2_mcart_1: $i > $i )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_mcart_1,type,(
    k1_mcart_1: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_34,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_68,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r2_hidden(A,k2_zfmisc_1(B,C))
       => ( A != k1_mcart_1(A)
          & A != k2_mcart_1(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_mcart_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

tff(f_59,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) != k1_xboole_0
     => ! [C] :
          ( m1_subset_1(C,k2_zfmisc_1(A,B))
         => ( C != k1_mcart_1(C)
            & C != k2_mcart_1(C) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_mcart_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_43,axiom,(
    ! [A,B] : ~ r2_hidden(A,k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_zfmisc_1)).

tff(c_8,plain,(
    ! [A_6] : r1_tarski(k1_xboole_0,A_6) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_24,plain,
    ( k2_mcart_1('#skF_2') = '#skF_2'
    | k1_mcart_1('#skF_2') = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_29,plain,(
    k1_mcart_1('#skF_2') = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_24])).

tff(c_26,plain,(
    r2_hidden('#skF_2',k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_34,plain,(
    ! [A_22,B_23] :
      ( m1_subset_1(A_22,B_23)
      | ~ r2_hidden(A_22,B_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_38,plain,(
    m1_subset_1('#skF_2',k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_26,c_34])).

tff(c_68,plain,(
    ! [C_43,A_44,B_45] :
      ( k1_mcart_1(C_43) != C_43
      | ~ m1_subset_1(C_43,k2_zfmisc_1(A_44,B_45))
      | k2_zfmisc_1(A_44,B_45) = k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_75,plain,
    ( k1_mcart_1('#skF_2') != '#skF_2'
    | k2_zfmisc_1('#skF_3','#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_38,c_68])).

tff(c_79,plain,(
    k2_zfmisc_1('#skF_3','#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_29,c_75])).

tff(c_50,plain,(
    ! [C_28,B_29,A_30] :
      ( r2_hidden(C_28,B_29)
      | ~ r2_hidden(C_28,A_30)
      | ~ r1_tarski(A_30,B_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_56,plain,(
    ! [B_29] :
      ( r2_hidden('#skF_2',B_29)
      | ~ r1_tarski(k2_zfmisc_1('#skF_3','#skF_4'),B_29) ) ),
    inference(resolution,[status(thm)],[c_26,c_50])).

tff(c_80,plain,(
    ! [B_29] :
      ( r2_hidden('#skF_2',B_29)
      | ~ r1_tarski(k1_xboole_0,B_29) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_79,c_56])).

tff(c_102,plain,(
    ! [B_46] : r2_hidden('#skF_2',B_46) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_80])).

tff(c_16,plain,(
    ! [A_11,B_12] : ~ r2_hidden(A_11,k2_zfmisc_1(A_11,B_12)) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_115,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_102,c_16])).

tff(c_116,plain,(
    k2_mcart_1('#skF_2') = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_24])).

tff(c_122,plain,(
    ! [A_47,B_48] :
      ( m1_subset_1(A_47,B_48)
      | ~ r2_hidden(A_47,B_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_126,plain,(
    m1_subset_1('#skF_2',k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_26,c_122])).

tff(c_182,plain,(
    ! [C_77,A_78,B_79] :
      ( k2_mcart_1(C_77) != C_77
      | ~ m1_subset_1(C_77,k2_zfmisc_1(A_78,B_79))
      | k2_zfmisc_1(A_78,B_79) = k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_193,plain,
    ( k2_mcart_1('#skF_2') != '#skF_2'
    | k2_zfmisc_1('#skF_3','#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_126,c_182])).

tff(c_198,plain,(
    k2_zfmisc_1('#skF_3','#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_116,c_193])).

tff(c_139,plain,(
    ! [C_54,B_55,A_56] :
      ( r2_hidden(C_54,B_55)
      | ~ r2_hidden(C_54,A_56)
      | ~ r1_tarski(A_56,B_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_145,plain,(
    ! [B_55] :
      ( r2_hidden('#skF_2',B_55)
      | ~ r1_tarski(k2_zfmisc_1('#skF_3','#skF_4'),B_55) ) ),
    inference(resolution,[status(thm)],[c_26,c_139])).

tff(c_199,plain,(
    ! [B_55] :
      ( r2_hidden('#skF_2',B_55)
      | ~ r1_tarski(k1_xboole_0,B_55) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_198,c_145])).

tff(c_236,plain,(
    ! [B_83] : r2_hidden('#skF_2',B_83) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_199])).

tff(c_249,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_236,c_16])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:25:40 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.88/1.20  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.97/1.21  
% 1.97/1.21  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.97/1.21  %$ r2_hidden > r1_tarski > m1_subset_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_mcart_1 > k1_mcart_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 1.97/1.21  
% 1.97/1.21  %Foreground sorts:
% 1.97/1.21  
% 1.97/1.21  
% 1.97/1.21  %Background operators:
% 1.97/1.21  
% 1.97/1.21  
% 1.97/1.21  %Foreground operators:
% 1.97/1.21  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.97/1.21  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.97/1.21  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 1.97/1.21  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.97/1.21  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.97/1.21  tff('#skF_2', type, '#skF_2': $i).
% 1.97/1.21  tff('#skF_3', type, '#skF_3': $i).
% 1.97/1.21  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.97/1.21  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 1.97/1.21  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.97/1.21  tff('#skF_4', type, '#skF_4': $i).
% 1.97/1.21  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.97/1.21  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 1.97/1.21  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.97/1.21  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.97/1.21  
% 1.97/1.22  tff(f_34, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 1.97/1.22  tff(f_68, negated_conjecture, ~(![A, B, C]: (r2_hidden(A, k2_zfmisc_1(B, C)) => (~(A = k1_mcart_1(A)) & ~(A = k2_mcart_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t67_mcart_1)).
% 1.97/1.22  tff(f_47, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_subset)).
% 1.97/1.22  tff(f_59, axiom, (![A, B]: (~(k2_zfmisc_1(A, B) = k1_xboole_0) => (![C]: (m1_subset_1(C, k2_zfmisc_1(A, B)) => (~(C = k1_mcart_1(C)) & ~(C = k2_mcart_1(C))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t66_mcart_1)).
% 1.97/1.22  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 1.97/1.22  tff(f_43, axiom, (![A, B]: ~r2_hidden(A, k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t152_zfmisc_1)).
% 1.97/1.22  tff(c_8, plain, (![A_6]: (r1_tarski(k1_xboole_0, A_6))), inference(cnfTransformation, [status(thm)], [f_34])).
% 1.97/1.22  tff(c_24, plain, (k2_mcart_1('#skF_2')='#skF_2' | k1_mcart_1('#skF_2')='#skF_2'), inference(cnfTransformation, [status(thm)], [f_68])).
% 1.97/1.22  tff(c_29, plain, (k1_mcart_1('#skF_2')='#skF_2'), inference(splitLeft, [status(thm)], [c_24])).
% 1.97/1.22  tff(c_26, plain, (r2_hidden('#skF_2', k2_zfmisc_1('#skF_3', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_68])).
% 1.97/1.22  tff(c_34, plain, (![A_22, B_23]: (m1_subset_1(A_22, B_23) | ~r2_hidden(A_22, B_23))), inference(cnfTransformation, [status(thm)], [f_47])).
% 1.97/1.22  tff(c_38, plain, (m1_subset_1('#skF_2', k2_zfmisc_1('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_26, c_34])).
% 1.97/1.22  tff(c_68, plain, (![C_43, A_44, B_45]: (k1_mcart_1(C_43)!=C_43 | ~m1_subset_1(C_43, k2_zfmisc_1(A_44, B_45)) | k2_zfmisc_1(A_44, B_45)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_59])).
% 1.97/1.22  tff(c_75, plain, (k1_mcart_1('#skF_2')!='#skF_2' | k2_zfmisc_1('#skF_3', '#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_38, c_68])).
% 1.97/1.22  tff(c_79, plain, (k2_zfmisc_1('#skF_3', '#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_29, c_75])).
% 1.97/1.22  tff(c_50, plain, (![C_28, B_29, A_30]: (r2_hidden(C_28, B_29) | ~r2_hidden(C_28, A_30) | ~r1_tarski(A_30, B_29))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.97/1.22  tff(c_56, plain, (![B_29]: (r2_hidden('#skF_2', B_29) | ~r1_tarski(k2_zfmisc_1('#skF_3', '#skF_4'), B_29))), inference(resolution, [status(thm)], [c_26, c_50])).
% 1.97/1.22  tff(c_80, plain, (![B_29]: (r2_hidden('#skF_2', B_29) | ~r1_tarski(k1_xboole_0, B_29))), inference(demodulation, [status(thm), theory('equality')], [c_79, c_56])).
% 1.97/1.22  tff(c_102, plain, (![B_46]: (r2_hidden('#skF_2', B_46))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_80])).
% 1.97/1.22  tff(c_16, plain, (![A_11, B_12]: (~r2_hidden(A_11, k2_zfmisc_1(A_11, B_12)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.97/1.22  tff(c_115, plain, $false, inference(resolution, [status(thm)], [c_102, c_16])).
% 1.97/1.22  tff(c_116, plain, (k2_mcart_1('#skF_2')='#skF_2'), inference(splitRight, [status(thm)], [c_24])).
% 1.97/1.22  tff(c_122, plain, (![A_47, B_48]: (m1_subset_1(A_47, B_48) | ~r2_hidden(A_47, B_48))), inference(cnfTransformation, [status(thm)], [f_47])).
% 1.97/1.22  tff(c_126, plain, (m1_subset_1('#skF_2', k2_zfmisc_1('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_26, c_122])).
% 1.97/1.22  tff(c_182, plain, (![C_77, A_78, B_79]: (k2_mcart_1(C_77)!=C_77 | ~m1_subset_1(C_77, k2_zfmisc_1(A_78, B_79)) | k2_zfmisc_1(A_78, B_79)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_59])).
% 1.97/1.22  tff(c_193, plain, (k2_mcart_1('#skF_2')!='#skF_2' | k2_zfmisc_1('#skF_3', '#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_126, c_182])).
% 1.97/1.22  tff(c_198, plain, (k2_zfmisc_1('#skF_3', '#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_116, c_193])).
% 1.97/1.22  tff(c_139, plain, (![C_54, B_55, A_56]: (r2_hidden(C_54, B_55) | ~r2_hidden(C_54, A_56) | ~r1_tarski(A_56, B_55))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.97/1.22  tff(c_145, plain, (![B_55]: (r2_hidden('#skF_2', B_55) | ~r1_tarski(k2_zfmisc_1('#skF_3', '#skF_4'), B_55))), inference(resolution, [status(thm)], [c_26, c_139])).
% 1.97/1.22  tff(c_199, plain, (![B_55]: (r2_hidden('#skF_2', B_55) | ~r1_tarski(k1_xboole_0, B_55))), inference(demodulation, [status(thm), theory('equality')], [c_198, c_145])).
% 1.97/1.22  tff(c_236, plain, (![B_83]: (r2_hidden('#skF_2', B_83))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_199])).
% 1.97/1.22  tff(c_249, plain, $false, inference(resolution, [status(thm)], [c_236, c_16])).
% 1.97/1.22  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.97/1.22  
% 1.97/1.22  Inference rules
% 1.97/1.22  ----------------------
% 1.97/1.22  #Ref     : 0
% 1.97/1.22  #Sup     : 47
% 1.97/1.22  #Fact    : 0
% 1.97/1.22  #Define  : 0
% 1.97/1.22  #Split   : 1
% 1.97/1.22  #Chain   : 0
% 1.97/1.22  #Close   : 0
% 1.97/1.22  
% 1.97/1.22  Ordering : KBO
% 1.97/1.22  
% 1.97/1.22  Simplification rules
% 1.97/1.22  ----------------------
% 1.97/1.22  #Subsume      : 0
% 1.97/1.22  #Demod        : 18
% 1.97/1.22  #Tautology    : 17
% 1.97/1.22  #SimpNegUnit  : 0
% 1.97/1.22  #BackRed      : 6
% 1.97/1.22  
% 1.97/1.22  #Partial instantiations: 0
% 1.97/1.22  #Strategies tried      : 1
% 1.97/1.22  
% 1.97/1.22  Timing (in seconds)
% 1.97/1.22  ----------------------
% 1.97/1.23  Preprocessing        : 0.27
% 1.97/1.23  Parsing              : 0.15
% 1.97/1.23  CNF conversion       : 0.02
% 1.97/1.23  Main loop            : 0.19
% 1.97/1.23  Inferencing          : 0.08
% 1.97/1.23  Reduction            : 0.05
% 1.97/1.23  Demodulation         : 0.03
% 1.97/1.23  BG Simplification    : 0.01
% 1.97/1.23  Subsumption          : 0.03
% 1.97/1.23  Abstraction          : 0.01
% 1.97/1.23  MUC search           : 0.00
% 1.97/1.23  Cooper               : 0.00
% 1.97/1.23  Total                : 0.49
% 1.97/1.23  Index Insertion      : 0.00
% 1.97/1.23  Index Deletion       : 0.00
% 1.97/1.23  Index Matching       : 0.00
% 1.97/1.23  BG Taut test         : 0.00
%------------------------------------------------------------------------------
