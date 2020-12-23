%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:09:23 EST 2020

% Result     : Theorem 2.10s
% Output     : CNFRefutation 2.10s
% Verified   : 
% Statistics : Number of formulae       :   51 (  63 expanded)
%              Number of leaves         :   27 (  34 expanded)
%              Depth                    :    9
%              Number of atoms          :   69 (  95 expanded)
%              Number of equality atoms :   39 (  55 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_relat_1 > k2_mcart_1 > k1_relat_1 > k1_mcart_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(f_83,negated_conjecture,(
    ~ ! [A,B] :
        ~ ( A != k1_xboole_0
          & B != k1_xboole_0
          & ~ ! [C] :
                ( m1_subset_1(C,k2_zfmisc_1(A,B))
               => C = k4_tarski(k1_mcart_1(C),k2_mcart_1(C)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_mcart_1)).

tff(f_43,axiom,(
    ! [A,B] : r1_tarski(k2_relat_1(k2_zfmisc_1(A,B)),B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t194_relat_1)).

tff(f_33,axiom,(
    ! [A] :
      ( r1_tarski(A,k1_xboole_0)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).

tff(f_41,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_63,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ( k1_relat_1(A) = k1_xboole_0
          | k2_relat_1(A) = k1_xboole_0 )
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(f_69,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r2_hidden(A,B)
       => A = k4_tarski(k1_mcart_1(A),k2_mcart_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_mcart_1)).

tff(f_29,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_55,axiom,(
    ! [A,B] :
      ~ ( A != k1_xboole_0
        & B != k1_xboole_0
        & ~ ( k1_relat_1(k2_zfmisc_1(A,B)) = A
            & k2_relat_1(k2_zfmisc_1(A,B)) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t195_relat_1)).

tff(c_28,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_26,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_32,plain,(
    ! [A_19,B_20] : r1_tarski(k2_relat_1(k2_zfmisc_1(A_19,B_20)),B_20) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_4,plain,(
    ! [A_2] :
      ( k1_xboole_0 = A_2
      | ~ r1_tarski(A_2,k1_xboole_0) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_37,plain,(
    ! [A_19] : k2_relat_1(k2_zfmisc_1(A_19,k1_xboole_0)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_32,c_4])).

tff(c_8,plain,(
    ! [A_5,B_6] : v1_relat_1(k2_zfmisc_1(A_5,B_6)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_53,plain,(
    ! [A_22] :
      ( k2_relat_1(A_22) != k1_xboole_0
      | k1_xboole_0 = A_22
      | ~ v1_relat_1(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_194,plain,(
    ! [A_251,B_252] :
      ( k2_relat_1(k2_zfmisc_1(A_251,B_252)) != k1_xboole_0
      | k2_zfmisc_1(A_251,B_252) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_8,c_53])).

tff(c_201,plain,(
    ! [A_19] : k2_zfmisc_1(A_19,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_37,c_194])).

tff(c_202,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_201,c_37])).

tff(c_22,plain,(
    k4_tarski(k1_mcart_1('#skF_3'),k2_mcart_1('#skF_3')) != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_24,plain,(
    m1_subset_1('#skF_3',k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_6,plain,(
    ! [A_3,B_4] :
      ( r2_hidden(A_3,B_4)
      | v1_xboole_0(B_4)
      | ~ m1_subset_1(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_100,plain,(
    ! [A_30,B_31] :
      ( k4_tarski(k1_mcart_1(A_30),k2_mcart_1(A_30)) = A_30
      | ~ r2_hidden(A_30,B_31)
      | ~ v1_relat_1(B_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_257,plain,(
    ! [A_257,B_258] :
      ( k4_tarski(k1_mcart_1(A_257),k2_mcart_1(A_257)) = A_257
      | ~ v1_relat_1(B_258)
      | v1_xboole_0(B_258)
      | ~ m1_subset_1(A_257,B_258) ) ),
    inference(resolution,[status(thm)],[c_6,c_100])).

tff(c_259,plain,
    ( k4_tarski(k1_mcart_1('#skF_3'),k2_mcart_1('#skF_3')) = '#skF_3'
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2'))
    | v1_xboole_0(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_24,c_257])).

tff(c_262,plain,
    ( k4_tarski(k1_mcart_1('#skF_3'),k2_mcart_1('#skF_3')) = '#skF_3'
    | v1_xboole_0(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_259])).

tff(c_263,plain,(
    v1_xboole_0(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_22,c_262])).

tff(c_2,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_267,plain,(
    k2_zfmisc_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_263,c_2])).

tff(c_12,plain,(
    ! [A_9,B_10] :
      ( k2_relat_1(k2_zfmisc_1(A_9,B_10)) = B_10
      | k1_xboole_0 = B_10
      | k1_xboole_0 = A_9 ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_279,plain,
    ( k2_relat_1(k1_xboole_0) = '#skF_2'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_267,c_12])).

tff(c_293,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_202,c_279])).

tff(c_295,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_26,c_26,c_293])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:54:24 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.10/1.20  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.10/1.20  
% 2.10/1.20  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.10/1.20  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_relat_1 > k2_mcart_1 > k1_relat_1 > k1_mcart_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.10/1.20  
% 2.10/1.20  %Foreground sorts:
% 2.10/1.20  
% 2.10/1.20  
% 2.10/1.20  %Background operators:
% 2.10/1.20  
% 2.10/1.20  
% 2.10/1.20  %Foreground operators:
% 2.10/1.20  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.10/1.20  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.10/1.20  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.10/1.20  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.10/1.20  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.10/1.20  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.10/1.20  tff('#skF_2', type, '#skF_2': $i).
% 2.10/1.20  tff('#skF_3', type, '#skF_3': $i).
% 2.10/1.20  tff('#skF_1', type, '#skF_1': $i).
% 2.10/1.20  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.10/1.20  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 2.10/1.20  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.10/1.20  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.10/1.20  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.10/1.20  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 2.10/1.20  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.10/1.20  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.10/1.20  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.10/1.20  
% 2.10/1.21  tff(f_83, negated_conjecture, ~(![A, B]: ~((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(![C]: (m1_subset_1(C, k2_zfmisc_1(A, B)) => (C = k4_tarski(k1_mcart_1(C), k2_mcart_1(C))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t24_mcart_1)).
% 2.10/1.21  tff(f_43, axiom, (![A, B]: r1_tarski(k2_relat_1(k2_zfmisc_1(A, B)), B)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t194_relat_1)).
% 2.10/1.21  tff(f_33, axiom, (![A]: (r1_tarski(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_1)).
% 2.10/1.21  tff(f_41, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 2.10/1.21  tff(f_63, axiom, (![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_relat_1)).
% 2.10/1.21  tff(f_39, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 2.10/1.21  tff(f_69, axiom, (![A, B]: (v1_relat_1(B) => (r2_hidden(A, B) => (A = k4_tarski(k1_mcart_1(A), k2_mcart_1(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t23_mcart_1)).
% 2.10/1.21  tff(f_29, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 2.10/1.21  tff(f_55, axiom, (![A, B]: ~((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~((k1_relat_1(k2_zfmisc_1(A, B)) = A) & (k2_relat_1(k2_zfmisc_1(A, B)) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t195_relat_1)).
% 2.10/1.21  tff(c_28, plain, (k1_xboole_0!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.10/1.21  tff(c_26, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.10/1.21  tff(c_32, plain, (![A_19, B_20]: (r1_tarski(k2_relat_1(k2_zfmisc_1(A_19, B_20)), B_20))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.10/1.21  tff(c_4, plain, (![A_2]: (k1_xboole_0=A_2 | ~r1_tarski(A_2, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.10/1.21  tff(c_37, plain, (![A_19]: (k2_relat_1(k2_zfmisc_1(A_19, k1_xboole_0))=k1_xboole_0)), inference(resolution, [status(thm)], [c_32, c_4])).
% 2.10/1.21  tff(c_8, plain, (![A_5, B_6]: (v1_relat_1(k2_zfmisc_1(A_5, B_6)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.10/1.21  tff(c_53, plain, (![A_22]: (k2_relat_1(A_22)!=k1_xboole_0 | k1_xboole_0=A_22 | ~v1_relat_1(A_22))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.10/1.21  tff(c_194, plain, (![A_251, B_252]: (k2_relat_1(k2_zfmisc_1(A_251, B_252))!=k1_xboole_0 | k2_zfmisc_1(A_251, B_252)=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_53])).
% 2.10/1.21  tff(c_201, plain, (![A_19]: (k2_zfmisc_1(A_19, k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_37, c_194])).
% 2.10/1.21  tff(c_202, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_201, c_37])).
% 2.10/1.21  tff(c_22, plain, (k4_tarski(k1_mcart_1('#skF_3'), k2_mcart_1('#skF_3'))!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.10/1.21  tff(c_24, plain, (m1_subset_1('#skF_3', k2_zfmisc_1('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.10/1.21  tff(c_6, plain, (![A_3, B_4]: (r2_hidden(A_3, B_4) | v1_xboole_0(B_4) | ~m1_subset_1(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.10/1.21  tff(c_100, plain, (![A_30, B_31]: (k4_tarski(k1_mcart_1(A_30), k2_mcart_1(A_30))=A_30 | ~r2_hidden(A_30, B_31) | ~v1_relat_1(B_31))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.10/1.21  tff(c_257, plain, (![A_257, B_258]: (k4_tarski(k1_mcart_1(A_257), k2_mcart_1(A_257))=A_257 | ~v1_relat_1(B_258) | v1_xboole_0(B_258) | ~m1_subset_1(A_257, B_258))), inference(resolution, [status(thm)], [c_6, c_100])).
% 2.10/1.21  tff(c_259, plain, (k4_tarski(k1_mcart_1('#skF_3'), k2_mcart_1('#skF_3'))='#skF_3' | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2')) | v1_xboole_0(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_24, c_257])).
% 2.10/1.21  tff(c_262, plain, (k4_tarski(k1_mcart_1('#skF_3'), k2_mcart_1('#skF_3'))='#skF_3' | v1_xboole_0(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_259])).
% 2.10/1.21  tff(c_263, plain, (v1_xboole_0(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_22, c_262])).
% 2.10/1.21  tff(c_2, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.10/1.21  tff(c_267, plain, (k2_zfmisc_1('#skF_1', '#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_263, c_2])).
% 2.10/1.21  tff(c_12, plain, (![A_9, B_10]: (k2_relat_1(k2_zfmisc_1(A_9, B_10))=B_10 | k1_xboole_0=B_10 | k1_xboole_0=A_9)), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.10/1.21  tff(c_279, plain, (k2_relat_1(k1_xboole_0)='#skF_2' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_267, c_12])).
% 2.10/1.21  tff(c_293, plain, (k1_xboole_0='#skF_2' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_202, c_279])).
% 2.10/1.21  tff(c_295, plain, $false, inference(negUnitSimplification, [status(thm)], [c_28, c_26, c_26, c_293])).
% 2.10/1.21  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.10/1.21  
% 2.10/1.21  Inference rules
% 2.10/1.21  ----------------------
% 2.10/1.21  #Ref     : 0
% 2.10/1.21  #Sup     : 78
% 2.10/1.21  #Fact    : 0
% 2.10/1.21  #Define  : 0
% 2.10/1.21  #Split   : 1
% 2.10/1.21  #Chain   : 0
% 2.10/1.21  #Close   : 0
% 2.10/1.21  
% 2.10/1.21  Ordering : KBO
% 2.10/1.21  
% 2.10/1.21  Simplification rules
% 2.10/1.21  ----------------------
% 2.10/1.21  #Subsume      : 8
% 2.10/1.21  #Demod        : 12
% 2.10/1.21  #Tautology    : 26
% 2.10/1.21  #SimpNegUnit  : 2
% 2.10/1.21  #BackRed      : 3
% 2.10/1.21  
% 2.10/1.21  #Partial instantiations: 36
% 2.10/1.21  #Strategies tried      : 1
% 2.10/1.21  
% 2.10/1.21  Timing (in seconds)
% 2.10/1.21  ----------------------
% 2.10/1.22  Preprocessing        : 0.28
% 2.10/1.22  Parsing              : 0.15
% 2.10/1.22  CNF conversion       : 0.02
% 2.10/1.22  Main loop            : 0.18
% 2.10/1.22  Inferencing          : 0.08
% 2.10/1.22  Reduction            : 0.05
% 2.10/1.22  Demodulation         : 0.04
% 2.10/1.22  BG Simplification    : 0.01
% 2.10/1.22  Subsumption          : 0.02
% 2.10/1.22  Abstraction          : 0.01
% 2.10/1.22  MUC search           : 0.00
% 2.10/1.22  Cooper               : 0.00
% 2.10/1.22  Total                : 0.49
% 2.10/1.22  Index Insertion      : 0.00
% 2.10/1.22  Index Deletion       : 0.00
% 2.10/1.22  Index Matching       : 0.00
% 2.10/1.22  BG Taut test         : 0.00
%------------------------------------------------------------------------------
