%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:09:21 EST 2020

% Result     : Theorem 1.94s
% Output     : CNFRefutation 1.96s
% Verified   : 
% Statistics : Number of formulae       :   47 ( 110 expanded)
%              Number of leaves         :   21 (  46 expanded)
%              Depth                    :    7
%              Number of atoms          :   64 ( 233 expanded)
%              Number of equality atoms :   29 (  79 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_mcart_1 > k1_mcart_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_mcart_1,type,(
    k2_mcart_1: $i > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_mcart_1,type,(
    k1_mcart_1: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_70,negated_conjecture,(
    ~ ! [A,B] :
        ~ ( A != k1_xboole_0
          & B != k1_xboole_0
          & ~ ! [C] :
                ( m1_subset_1(C,k2_zfmisc_1(A,B))
               => C = k4_tarski(k1_mcart_1(C),k2_mcart_1(C)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_mcart_1)).

tff(f_48,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_50,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_56,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r2_hidden(A,B)
       => A = k4_tarski(k1_mcart_1(A),k2_mcart_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_mcart_1)).

tff(f_29,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_35,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(c_24,plain,(
    m1_subset_1('#skF_3',k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_59,plain,(
    ! [B_18,A_19] :
      ( v1_xboole_0(B_18)
      | ~ m1_subset_1(B_18,A_19)
      | ~ v1_xboole_0(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_67,plain,
    ( v1_xboole_0('#skF_3')
    | ~ v1_xboole_0(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_24,c_59])).

tff(c_68,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_67])).

tff(c_22,plain,(
    k4_tarski(k1_mcart_1('#skF_3'),k2_mcart_1('#skF_3')) != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_18,plain,(
    ! [A_6,B_7] : v1_relat_1(k2_zfmisc_1(A_6,B_7)) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_12,plain,(
    ! [B_5,A_4] :
      ( r2_hidden(B_5,A_4)
      | ~ m1_subset_1(B_5,A_4)
      | v1_xboole_0(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_86,plain,(
    ! [A_26,B_27] :
      ( k4_tarski(k1_mcart_1(A_26),k2_mcart_1(A_26)) = A_26
      | ~ r2_hidden(A_26,B_27)
      | ~ v1_relat_1(B_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_90,plain,(
    ! [B_28,A_29] :
      ( k4_tarski(k1_mcart_1(B_28),k2_mcart_1(B_28)) = B_28
      | ~ v1_relat_1(A_29)
      | ~ m1_subset_1(B_28,A_29)
      | v1_xboole_0(A_29) ) ),
    inference(resolution,[status(thm)],[c_12,c_86])).

tff(c_94,plain,
    ( k4_tarski(k1_mcart_1('#skF_3'),k2_mcart_1('#skF_3')) = '#skF_3'
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2'))
    | v1_xboole_0(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_24,c_90])).

tff(c_98,plain,
    ( k4_tarski(k1_mcart_1('#skF_3'),k2_mcart_1('#skF_3')) = '#skF_3'
    | v1_xboole_0(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_94])).

tff(c_100,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_22,c_98])).

tff(c_101,plain,(
    v1_xboole_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_67])).

tff(c_2,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_106,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_101,c_2])).

tff(c_28,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_116,plain,(
    '#skF_3' != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_106,c_28])).

tff(c_26,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_115,plain,(
    '#skF_2' != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_106,c_26])).

tff(c_102,plain,(
    v1_xboole_0(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_67])).

tff(c_110,plain,(
    k2_zfmisc_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_102,c_2])).

tff(c_132,plain,(
    k2_zfmisc_1('#skF_1','#skF_2') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_106,c_110])).

tff(c_4,plain,(
    ! [B_3,A_2] :
      ( k1_xboole_0 = B_3
      | k1_xboole_0 = A_2
      | k2_zfmisc_1(A_2,B_3) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_179,plain,(
    ! [B_37,A_38] :
      ( B_37 = '#skF_3'
      | A_38 = '#skF_3'
      | k2_zfmisc_1(A_38,B_37) != '#skF_3' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_106,c_106,c_106,c_4])).

tff(c_185,plain,
    ( '#skF_2' = '#skF_3'
    | '#skF_3' = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_132,c_179])).

tff(c_194,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_116,c_115,c_185])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:36:08 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.94/1.23  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.96/1.24  
% 1.96/1.24  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.96/1.24  %$ r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_mcart_1 > k1_mcart_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 1.96/1.24  
% 1.96/1.24  %Foreground sorts:
% 1.96/1.24  
% 1.96/1.24  
% 1.96/1.24  %Background operators:
% 1.96/1.24  
% 1.96/1.24  
% 1.96/1.24  %Foreground operators:
% 1.96/1.24  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.96/1.24  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.96/1.24  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 1.96/1.24  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.96/1.24  tff('#skF_2', type, '#skF_2': $i).
% 1.96/1.24  tff('#skF_3', type, '#skF_3': $i).
% 1.96/1.24  tff('#skF_1', type, '#skF_1': $i).
% 1.96/1.24  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.96/1.24  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 1.96/1.24  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.96/1.24  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.96/1.24  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.96/1.24  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 1.96/1.24  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.96/1.24  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.96/1.24  
% 1.96/1.25  tff(f_70, negated_conjecture, ~(![A, B]: ~((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(![C]: (m1_subset_1(C, k2_zfmisc_1(A, B)) => (C = k4_tarski(k1_mcart_1(C), k2_mcart_1(C))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t24_mcart_1)).
% 1.96/1.25  tff(f_48, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 1.96/1.25  tff(f_50, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 1.96/1.25  tff(f_56, axiom, (![A, B]: (v1_relat_1(B) => (r2_hidden(A, B) => (A = k4_tarski(k1_mcart_1(A), k2_mcart_1(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t23_mcart_1)).
% 1.96/1.25  tff(f_29, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 1.96/1.25  tff(f_35, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 1.96/1.25  tff(c_24, plain, (m1_subset_1('#skF_3', k2_zfmisc_1('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_70])).
% 1.96/1.25  tff(c_59, plain, (![B_18, A_19]: (v1_xboole_0(B_18) | ~m1_subset_1(B_18, A_19) | ~v1_xboole_0(A_19))), inference(cnfTransformation, [status(thm)], [f_48])).
% 1.96/1.25  tff(c_67, plain, (v1_xboole_0('#skF_3') | ~v1_xboole_0(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_24, c_59])).
% 1.96/1.25  tff(c_68, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(splitLeft, [status(thm)], [c_67])).
% 1.96/1.25  tff(c_22, plain, (k4_tarski(k1_mcart_1('#skF_3'), k2_mcart_1('#skF_3'))!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_70])).
% 1.96/1.25  tff(c_18, plain, (![A_6, B_7]: (v1_relat_1(k2_zfmisc_1(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 1.96/1.25  tff(c_12, plain, (![B_5, A_4]: (r2_hidden(B_5, A_4) | ~m1_subset_1(B_5, A_4) | v1_xboole_0(A_4))), inference(cnfTransformation, [status(thm)], [f_48])).
% 1.96/1.25  tff(c_86, plain, (![A_26, B_27]: (k4_tarski(k1_mcart_1(A_26), k2_mcart_1(A_26))=A_26 | ~r2_hidden(A_26, B_27) | ~v1_relat_1(B_27))), inference(cnfTransformation, [status(thm)], [f_56])).
% 1.96/1.25  tff(c_90, plain, (![B_28, A_29]: (k4_tarski(k1_mcart_1(B_28), k2_mcart_1(B_28))=B_28 | ~v1_relat_1(A_29) | ~m1_subset_1(B_28, A_29) | v1_xboole_0(A_29))), inference(resolution, [status(thm)], [c_12, c_86])).
% 1.96/1.25  tff(c_94, plain, (k4_tarski(k1_mcart_1('#skF_3'), k2_mcart_1('#skF_3'))='#skF_3' | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2')) | v1_xboole_0(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_24, c_90])).
% 1.96/1.25  tff(c_98, plain, (k4_tarski(k1_mcart_1('#skF_3'), k2_mcart_1('#skF_3'))='#skF_3' | v1_xboole_0(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_94])).
% 1.96/1.25  tff(c_100, plain, $false, inference(negUnitSimplification, [status(thm)], [c_68, c_22, c_98])).
% 1.96/1.25  tff(c_101, plain, (v1_xboole_0('#skF_3')), inference(splitRight, [status(thm)], [c_67])).
% 1.96/1.25  tff(c_2, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.96/1.25  tff(c_106, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_101, c_2])).
% 1.96/1.25  tff(c_28, plain, (k1_xboole_0!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_70])).
% 1.96/1.25  tff(c_116, plain, ('#skF_3'!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_106, c_28])).
% 1.96/1.25  tff(c_26, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_70])).
% 1.96/1.25  tff(c_115, plain, ('#skF_2'!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_106, c_26])).
% 1.96/1.25  tff(c_102, plain, (v1_xboole_0(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(splitRight, [status(thm)], [c_67])).
% 1.96/1.25  tff(c_110, plain, (k2_zfmisc_1('#skF_1', '#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_102, c_2])).
% 1.96/1.25  tff(c_132, plain, (k2_zfmisc_1('#skF_1', '#skF_2')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_106, c_110])).
% 1.96/1.25  tff(c_4, plain, (![B_3, A_2]: (k1_xboole_0=B_3 | k1_xboole_0=A_2 | k2_zfmisc_1(A_2, B_3)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.96/1.25  tff(c_179, plain, (![B_37, A_38]: (B_37='#skF_3' | A_38='#skF_3' | k2_zfmisc_1(A_38, B_37)!='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_106, c_106, c_106, c_4])).
% 1.96/1.25  tff(c_185, plain, ('#skF_2'='#skF_3' | '#skF_3'='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_132, c_179])).
% 1.96/1.25  tff(c_194, plain, $false, inference(negUnitSimplification, [status(thm)], [c_116, c_115, c_185])).
% 1.96/1.25  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.96/1.25  
% 1.96/1.25  Inference rules
% 1.96/1.25  ----------------------
% 1.96/1.25  #Ref     : 0
% 1.96/1.25  #Sup     : 37
% 1.96/1.25  #Fact    : 0
% 1.96/1.25  #Define  : 0
% 1.96/1.25  #Split   : 1
% 1.96/1.25  #Chain   : 0
% 1.96/1.25  #Close   : 0
% 1.96/1.25  
% 1.96/1.25  Ordering : KBO
% 1.96/1.25  
% 1.96/1.25  Simplification rules
% 1.96/1.25  ----------------------
% 1.96/1.25  #Subsume      : 0
% 1.96/1.25  #Demod        : 22
% 1.96/1.25  #Tautology    : 30
% 1.96/1.25  #SimpNegUnit  : 2
% 1.96/1.25  #BackRed      : 8
% 1.96/1.25  
% 1.96/1.25  #Partial instantiations: 0
% 1.96/1.25  #Strategies tried      : 1
% 1.96/1.25  
% 1.96/1.25  Timing (in seconds)
% 1.96/1.25  ----------------------
% 1.96/1.26  Preprocessing        : 0.30
% 1.96/1.26  Parsing              : 0.16
% 1.96/1.26  CNF conversion       : 0.02
% 1.96/1.26  Main loop            : 0.15
% 1.96/1.26  Inferencing          : 0.05
% 1.96/1.26  Reduction            : 0.04
% 1.96/1.26  Demodulation         : 0.03
% 1.96/1.26  BG Simplification    : 0.01
% 1.96/1.26  Subsumption          : 0.02
% 1.96/1.26  Abstraction          : 0.01
% 1.96/1.26  MUC search           : 0.00
% 1.96/1.26  Cooper               : 0.00
% 1.96/1.26  Total                : 0.48
% 1.96/1.26  Index Insertion      : 0.00
% 1.96/1.26  Index Deletion       : 0.00
% 1.96/1.26  Index Matching       : 0.00
% 1.96/1.26  BG Taut test         : 0.00
%------------------------------------------------------------------------------
