%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:09:21 EST 2020

% Result     : Theorem 2.00s
% Output     : CNFRefutation 2.00s
% Verified   : 
% Statistics : Number of formulae       :   53 ( 137 expanded)
%              Number of leaves         :   24 (  56 expanded)
%              Depth                    :    8
%              Number of atoms          :   73 ( 292 expanded)
%              Number of equality atoms :   38 ( 105 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_relat_1 > k2_mcart_1 > k1_relat_1 > k1_mcart_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_79,negated_conjecture,(
    ~ ! [A,B] :
        ~ ( A != k1_xboole_0
          & B != k1_xboole_0
          & ~ ! [C] :
                ( m1_subset_1(C,k2_zfmisc_1(A,B))
               => C = k4_tarski(k1_mcart_1(C),k2_mcart_1(C)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_mcart_1)).

tff(f_42,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_44,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_65,axiom,(
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

tff(f_59,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_56,axiom,(
    ! [A,B] :
      ~ ( A != k1_xboole_0
        & B != k1_xboole_0
        & ~ ( k1_relat_1(k2_zfmisc_1(A,B)) = A
            & k2_relat_1(k2_zfmisc_1(A,B)) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t195_relat_1)).

tff(c_26,plain,(
    m1_subset_1('#skF_3',k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_42,plain,(
    ! [B_16,A_17] :
      ( v1_xboole_0(B_16)
      | ~ m1_subset_1(B_16,A_17)
      | ~ v1_xboole_0(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_50,plain,
    ( v1_xboole_0('#skF_3')
    | ~ v1_xboole_0(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_26,c_42])).

tff(c_51,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_50])).

tff(c_24,plain,(
    k4_tarski(k1_mcart_1('#skF_3'),k2_mcart_1('#skF_3')) != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_12,plain,(
    ! [A_4,B_5] : v1_relat_1(k2_zfmisc_1(A_4,B_5)) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_6,plain,(
    ! [B_3,A_2] :
      ( r2_hidden(B_3,A_2)
      | ~ m1_subset_1(B_3,A_2)
      | v1_xboole_0(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_82,plain,(
    ! [A_26,B_27] :
      ( k4_tarski(k1_mcart_1(A_26),k2_mcart_1(A_26)) = A_26
      | ~ r2_hidden(A_26,B_27)
      | ~ v1_relat_1(B_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_86,plain,(
    ! [B_28,A_29] :
      ( k4_tarski(k1_mcart_1(B_28),k2_mcart_1(B_28)) = B_28
      | ~ v1_relat_1(A_29)
      | ~ m1_subset_1(B_28,A_29)
      | v1_xboole_0(A_29) ) ),
    inference(resolution,[status(thm)],[c_6,c_82])).

tff(c_90,plain,
    ( k4_tarski(k1_mcart_1('#skF_3'),k2_mcart_1('#skF_3')) = '#skF_3'
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2'))
    | v1_xboole_0(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_26,c_86])).

tff(c_94,plain,
    ( k4_tarski(k1_mcart_1('#skF_3'),k2_mcart_1('#skF_3')) = '#skF_3'
    | v1_xboole_0(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_90])).

tff(c_96,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_51,c_24,c_94])).

tff(c_97,plain,(
    v1_xboole_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_2,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_102,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_97,c_2])).

tff(c_30,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_111,plain,(
    '#skF_3' != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_30])).

tff(c_28,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_110,plain,(
    '#skF_2' != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_28])).

tff(c_20,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_109,plain,(
    k1_relat_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_102,c_20])).

tff(c_98,plain,(
    v1_xboole_0(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_106,plain,(
    k2_zfmisc_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_98,c_2])).

tff(c_125,plain,(
    k2_zfmisc_1('#skF_1','#skF_2') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_106])).

tff(c_16,plain,(
    ! [A_6,B_7] :
      ( k1_relat_1(k2_zfmisc_1(A_6,B_7)) = A_6
      | k1_xboole_0 = B_7
      | k1_xboole_0 = A_6 ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_156,plain,(
    ! [A_35,B_36] :
      ( k1_relat_1(k2_zfmisc_1(A_35,B_36)) = A_35
      | B_36 = '#skF_3'
      | A_35 = '#skF_3' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_102,c_16])).

tff(c_165,plain,
    ( k1_relat_1('#skF_3') = '#skF_1'
    | '#skF_2' = '#skF_3'
    | '#skF_3' = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_125,c_156])).

tff(c_168,plain,
    ( '#skF_3' = '#skF_1'
    | '#skF_2' = '#skF_3'
    | '#skF_3' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_109,c_165])).

tff(c_170,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_111,c_110,c_111,c_168])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n006.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 09:26:22 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.00/1.18  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.00/1.19  
% 2.00/1.19  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.00/1.19  %$ r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_relat_1 > k2_mcart_1 > k1_relat_1 > k1_mcart_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.00/1.19  
% 2.00/1.19  %Foreground sorts:
% 2.00/1.19  
% 2.00/1.19  
% 2.00/1.19  %Background operators:
% 2.00/1.19  
% 2.00/1.19  
% 2.00/1.19  %Foreground operators:
% 2.00/1.19  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.00/1.19  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.00/1.19  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.00/1.19  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.00/1.19  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.00/1.19  tff('#skF_2', type, '#skF_2': $i).
% 2.00/1.19  tff('#skF_3', type, '#skF_3': $i).
% 2.00/1.19  tff('#skF_1', type, '#skF_1': $i).
% 2.00/1.19  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.00/1.19  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 2.00/1.19  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.00/1.19  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.00/1.19  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.00/1.19  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 2.00/1.19  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.00/1.19  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.00/1.19  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.00/1.19  
% 2.00/1.20  tff(f_79, negated_conjecture, ~(![A, B]: ~((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(![C]: (m1_subset_1(C, k2_zfmisc_1(A, B)) => (C = k4_tarski(k1_mcart_1(C), k2_mcart_1(C))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t24_mcart_1)).
% 2.00/1.20  tff(f_42, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 2.00/1.20  tff(f_44, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 2.00/1.20  tff(f_65, axiom, (![A, B]: (v1_relat_1(B) => (r2_hidden(A, B) => (A = k4_tarski(k1_mcart_1(A), k2_mcart_1(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t23_mcart_1)).
% 2.00/1.20  tff(f_29, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 2.00/1.20  tff(f_59, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 2.00/1.20  tff(f_56, axiom, (![A, B]: ~((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~((k1_relat_1(k2_zfmisc_1(A, B)) = A) & (k2_relat_1(k2_zfmisc_1(A, B)) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t195_relat_1)).
% 2.00/1.20  tff(c_26, plain, (m1_subset_1('#skF_3', k2_zfmisc_1('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.00/1.20  tff(c_42, plain, (![B_16, A_17]: (v1_xboole_0(B_16) | ~m1_subset_1(B_16, A_17) | ~v1_xboole_0(A_17))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.00/1.20  tff(c_50, plain, (v1_xboole_0('#skF_3') | ~v1_xboole_0(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_26, c_42])).
% 2.00/1.20  tff(c_51, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(splitLeft, [status(thm)], [c_50])).
% 2.00/1.20  tff(c_24, plain, (k4_tarski(k1_mcart_1('#skF_3'), k2_mcart_1('#skF_3'))!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.00/1.20  tff(c_12, plain, (![A_4, B_5]: (v1_relat_1(k2_zfmisc_1(A_4, B_5)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.00/1.20  tff(c_6, plain, (![B_3, A_2]: (r2_hidden(B_3, A_2) | ~m1_subset_1(B_3, A_2) | v1_xboole_0(A_2))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.00/1.20  tff(c_82, plain, (![A_26, B_27]: (k4_tarski(k1_mcart_1(A_26), k2_mcart_1(A_26))=A_26 | ~r2_hidden(A_26, B_27) | ~v1_relat_1(B_27))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.00/1.20  tff(c_86, plain, (![B_28, A_29]: (k4_tarski(k1_mcart_1(B_28), k2_mcart_1(B_28))=B_28 | ~v1_relat_1(A_29) | ~m1_subset_1(B_28, A_29) | v1_xboole_0(A_29))), inference(resolution, [status(thm)], [c_6, c_82])).
% 2.00/1.20  tff(c_90, plain, (k4_tarski(k1_mcart_1('#skF_3'), k2_mcart_1('#skF_3'))='#skF_3' | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2')) | v1_xboole_0(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_26, c_86])).
% 2.00/1.20  tff(c_94, plain, (k4_tarski(k1_mcart_1('#skF_3'), k2_mcart_1('#skF_3'))='#skF_3' | v1_xboole_0(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_90])).
% 2.00/1.20  tff(c_96, plain, $false, inference(negUnitSimplification, [status(thm)], [c_51, c_24, c_94])).
% 2.00/1.20  tff(c_97, plain, (v1_xboole_0('#skF_3')), inference(splitRight, [status(thm)], [c_50])).
% 2.00/1.20  tff(c_2, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.00/1.20  tff(c_102, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_97, c_2])).
% 2.00/1.20  tff(c_30, plain, (k1_xboole_0!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.00/1.20  tff(c_111, plain, ('#skF_3'!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_102, c_30])).
% 2.00/1.20  tff(c_28, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.00/1.20  tff(c_110, plain, ('#skF_2'!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_102, c_28])).
% 2.00/1.20  tff(c_20, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.00/1.20  tff(c_109, plain, (k1_relat_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_102, c_102, c_20])).
% 2.00/1.20  tff(c_98, plain, (v1_xboole_0(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(splitRight, [status(thm)], [c_50])).
% 2.00/1.20  tff(c_106, plain, (k2_zfmisc_1('#skF_1', '#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_98, c_2])).
% 2.00/1.20  tff(c_125, plain, (k2_zfmisc_1('#skF_1', '#skF_2')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_102, c_106])).
% 2.00/1.20  tff(c_16, plain, (![A_6, B_7]: (k1_relat_1(k2_zfmisc_1(A_6, B_7))=A_6 | k1_xboole_0=B_7 | k1_xboole_0=A_6)), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.00/1.20  tff(c_156, plain, (![A_35, B_36]: (k1_relat_1(k2_zfmisc_1(A_35, B_36))=A_35 | B_36='#skF_3' | A_35='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_102, c_102, c_16])).
% 2.00/1.20  tff(c_165, plain, (k1_relat_1('#skF_3')='#skF_1' | '#skF_2'='#skF_3' | '#skF_3'='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_125, c_156])).
% 2.00/1.20  tff(c_168, plain, ('#skF_3'='#skF_1' | '#skF_2'='#skF_3' | '#skF_3'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_109, c_165])).
% 2.00/1.20  tff(c_170, plain, $false, inference(negUnitSimplification, [status(thm)], [c_111, c_110, c_111, c_168])).
% 2.00/1.20  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.00/1.20  
% 2.00/1.20  Inference rules
% 2.00/1.20  ----------------------
% 2.00/1.20  #Ref     : 0
% 2.00/1.20  #Sup     : 31
% 2.00/1.20  #Fact    : 0
% 2.00/1.20  #Define  : 0
% 2.00/1.20  #Split   : 1
% 2.00/1.20  #Chain   : 0
% 2.00/1.20  #Close   : 0
% 2.00/1.20  
% 2.00/1.20  Ordering : KBO
% 2.00/1.20  
% 2.00/1.20  Simplification rules
% 2.00/1.20  ----------------------
% 2.00/1.20  #Subsume      : 0
% 2.00/1.20  #Demod        : 17
% 2.00/1.20  #Tautology    : 25
% 2.00/1.20  #SimpNegUnit  : 2
% 2.00/1.20  #BackRed      : 7
% 2.00/1.20  
% 2.00/1.20  #Partial instantiations: 0
% 2.00/1.20  #Strategies tried      : 1
% 2.00/1.20  
% 2.00/1.20  Timing (in seconds)
% 2.00/1.20  ----------------------
% 2.00/1.21  Preprocessing        : 0.29
% 2.00/1.21  Parsing              : 0.16
% 2.00/1.21  CNF conversion       : 0.02
% 2.00/1.21  Main loop            : 0.15
% 2.00/1.21  Inferencing          : 0.06
% 2.00/1.21  Reduction            : 0.04
% 2.00/1.21  Demodulation         : 0.03
% 2.00/1.21  BG Simplification    : 0.01
% 2.00/1.21  Subsumption          : 0.02
% 2.00/1.21  Abstraction          : 0.01
% 2.00/1.21  MUC search           : 0.00
% 2.00/1.21  Cooper               : 0.00
% 2.00/1.21  Total                : 0.47
% 2.00/1.21  Index Insertion      : 0.00
% 2.00/1.21  Index Deletion       : 0.00
% 2.00/1.21  Index Matching       : 0.00
% 2.00/1.21  BG Taut test         : 0.00
%------------------------------------------------------------------------------
