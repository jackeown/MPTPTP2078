%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:56:42 EST 2020

% Result     : Theorem 1.91s
% Output     : CNFRefutation 2.23s
% Verified   : 
% Statistics : Number of formulae       :   53 ( 125 expanded)
%              Number of leaves         :   17 (  50 expanded)
%              Depth                    :   11
%              Number of atoms          :   85 ( 281 expanded)
%              Number of equality atoms :   11 (  47 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > m1_subset_1 > k3_subset_1 > #nlpp > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

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

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_64,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => ! [C] :
            ( m1_subset_1(C,k1_zfmisc_1(A))
           => ( ( r1_xboole_0(B,C)
                & r1_xboole_0(k3_subset_1(A,B),k3_subset_1(A,C)) )
             => B = k3_subset_1(A,C) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_subset_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k3_subset_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,k3_subset_1(A,B)) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_52,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(A))
         => ( r1_xboole_0(B,C)
          <=> r1_tarski(B,k3_subset_1(A,C)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_subset_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(c_18,plain,(
    k3_subset_1('#skF_1','#skF_3') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_26,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_24,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_22,plain,(
    r1_xboole_0('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_10,plain,(
    ! [A_5,B_6] :
      ( m1_subset_1(k3_subset_1(A_5,B_6),k1_zfmisc_1(A_5))
      | ~ m1_subset_1(B_6,k1_zfmisc_1(A_5)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_52,plain,(
    ! [A_21,B_22] :
      ( k3_subset_1(A_21,k3_subset_1(A_21,B_22)) = B_22
      | ~ m1_subset_1(B_22,k1_zfmisc_1(A_21)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_61,plain,(
    k3_subset_1('#skF_1',k3_subset_1('#skF_1','#skF_3')) = '#skF_3' ),
    inference(resolution,[status(thm)],[c_24,c_52])).

tff(c_8,plain,(
    ! [B_4] : r1_tarski(B_4,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_139,plain,(
    ! [B_28,C_29,A_30] :
      ( r1_xboole_0(B_28,C_29)
      | ~ r1_tarski(B_28,k3_subset_1(A_30,C_29))
      | ~ m1_subset_1(C_29,k1_zfmisc_1(A_30))
      | ~ m1_subset_1(B_28,k1_zfmisc_1(A_30)) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_158,plain,(
    ! [A_31,C_32] :
      ( r1_xboole_0(k3_subset_1(A_31,C_32),C_32)
      | ~ m1_subset_1(C_32,k1_zfmisc_1(A_31))
      | ~ m1_subset_1(k3_subset_1(A_31,C_32),k1_zfmisc_1(A_31)) ) ),
    inference(resolution,[status(thm)],[c_8,c_139])).

tff(c_172,plain,(
    ! [A_33,B_34] :
      ( r1_xboole_0(k3_subset_1(A_33,B_34),B_34)
      | ~ m1_subset_1(B_34,k1_zfmisc_1(A_33)) ) ),
    inference(resolution,[status(thm)],[c_10,c_158])).

tff(c_180,plain,
    ( r1_xboole_0('#skF_3',k3_subset_1('#skF_1','#skF_3'))
    | ~ m1_subset_1(k3_subset_1('#skF_1','#skF_3'),k1_zfmisc_1('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_61,c_172])).

tff(c_185,plain,(
    ~ m1_subset_1(k3_subset_1('#skF_1','#skF_3'),k1_zfmisc_1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_180])).

tff(c_188,plain,(
    ~ m1_subset_1('#skF_3',k1_zfmisc_1('#skF_1')) ),
    inference(resolution,[status(thm)],[c_10,c_185])).

tff(c_192,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_188])).

tff(c_194,plain,(
    m1_subset_1(k3_subset_1('#skF_1','#skF_3'),k1_zfmisc_1('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_180])).

tff(c_20,plain,(
    r1_xboole_0(k3_subset_1('#skF_1','#skF_2'),k3_subset_1('#skF_1','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( r1_xboole_0(B_2,A_1)
      | ~ r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_39,plain,(
    r1_xboole_0(k3_subset_1('#skF_1','#skF_3'),k3_subset_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_20,c_2])).

tff(c_60,plain,(
    k3_subset_1('#skF_1',k3_subset_1('#skF_1','#skF_2')) = '#skF_2' ),
    inference(resolution,[status(thm)],[c_26,c_52])).

tff(c_164,plain,
    ( r1_xboole_0(k3_subset_1('#skF_1',k3_subset_1('#skF_1','#skF_2')),k3_subset_1('#skF_1','#skF_2'))
    | ~ m1_subset_1(k3_subset_1('#skF_1','#skF_2'),k1_zfmisc_1('#skF_1'))
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_60,c_158])).

tff(c_170,plain,
    ( r1_xboole_0('#skF_2',k3_subset_1('#skF_1','#skF_2'))
    | ~ m1_subset_1(k3_subset_1('#skF_1','#skF_2'),k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_60,c_164])).

tff(c_245,plain,(
    ~ m1_subset_1(k3_subset_1('#skF_1','#skF_2'),k1_zfmisc_1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_170])).

tff(c_248,plain,(
    ~ m1_subset_1('#skF_2',k1_zfmisc_1('#skF_1')) ),
    inference(resolution,[status(thm)],[c_10,c_245])).

tff(c_252,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_248])).

tff(c_254,plain,(
    m1_subset_1(k3_subset_1('#skF_1','#skF_2'),k1_zfmisc_1('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_170])).

tff(c_126,plain,(
    ! [B_25,A_26,C_27] :
      ( r1_tarski(B_25,k3_subset_1(A_26,C_27))
      | ~ r1_xboole_0(B_25,C_27)
      | ~ m1_subset_1(C_27,k1_zfmisc_1(A_26))
      | ~ m1_subset_1(B_25,k1_zfmisc_1(A_26)) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_137,plain,(
    ! [B_25] :
      ( r1_tarski(B_25,'#skF_2')
      | ~ r1_xboole_0(B_25,k3_subset_1('#skF_1','#skF_2'))
      | ~ m1_subset_1(k3_subset_1('#skF_1','#skF_2'),k1_zfmisc_1('#skF_1'))
      | ~ m1_subset_1(B_25,k1_zfmisc_1('#skF_1')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_60,c_126])).

tff(c_300,plain,(
    ! [B_41] :
      ( r1_tarski(B_41,'#skF_2')
      | ~ r1_xboole_0(B_41,k3_subset_1('#skF_1','#skF_2'))
      | ~ m1_subset_1(B_41,k1_zfmisc_1('#skF_1')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_254,c_137])).

tff(c_314,plain,
    ( r1_tarski(k3_subset_1('#skF_1','#skF_3'),'#skF_2')
    | ~ m1_subset_1(k3_subset_1('#skF_1','#skF_3'),k1_zfmisc_1('#skF_1')) ),
    inference(resolution,[status(thm)],[c_39,c_300])).

tff(c_324,plain,(
    r1_tarski(k3_subset_1('#skF_1','#skF_3'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_194,c_314])).

tff(c_4,plain,(
    ! [B_4,A_3] :
      ( B_4 = A_3
      | ~ r1_tarski(B_4,A_3)
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_138,plain,(
    ! [A_26,C_27,B_25] :
      ( k3_subset_1(A_26,C_27) = B_25
      | ~ r1_tarski(k3_subset_1(A_26,C_27),B_25)
      | ~ r1_xboole_0(B_25,C_27)
      | ~ m1_subset_1(C_27,k1_zfmisc_1(A_26))
      | ~ m1_subset_1(B_25,k1_zfmisc_1(A_26)) ) ),
    inference(resolution,[status(thm)],[c_126,c_4])).

tff(c_327,plain,
    ( k3_subset_1('#skF_1','#skF_3') = '#skF_2'
    | ~ r1_xboole_0('#skF_2','#skF_3')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1('#skF_1'))
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1('#skF_1')) ),
    inference(resolution,[status(thm)],[c_324,c_138])).

tff(c_332,plain,(
    k3_subset_1('#skF_1','#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_24,c_22,c_327])).

tff(c_334,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_18,c_332])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n016.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 19:35:34 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.91/1.31  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.91/1.31  
% 1.91/1.31  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.91/1.31  %$ r1_xboole_0 > r1_tarski > m1_subset_1 > k3_subset_1 > #nlpp > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1
% 1.91/1.31  
% 1.91/1.31  %Foreground sorts:
% 1.91/1.31  
% 1.91/1.31  
% 1.91/1.31  %Background operators:
% 1.91/1.31  
% 1.91/1.31  
% 1.91/1.31  %Foreground operators:
% 1.91/1.31  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.91/1.31  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.91/1.31  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 1.91/1.31  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.91/1.31  tff('#skF_2', type, '#skF_2': $i).
% 1.91/1.31  tff('#skF_3', type, '#skF_3': $i).
% 1.91/1.31  tff('#skF_1', type, '#skF_1': $i).
% 1.91/1.31  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.91/1.31  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.91/1.31  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.91/1.31  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.91/1.31  
% 2.23/1.33  tff(f_64, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => ((r1_xboole_0(B, C) & r1_xboole_0(k3_subset_1(A, B), k3_subset_1(A, C))) => (B = k3_subset_1(A, C))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_subset_1)).
% 2.23/1.33  tff(f_39, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k3_subset_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 2.23/1.33  tff(f_43, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, k3_subset_1(A, B)) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 2.23/1.33  tff(f_35, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.23/1.33  tff(f_52, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (r1_xboole_0(B, C) <=> r1_tarski(B, k3_subset_1(A, C))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_subset_1)).
% 2.23/1.33  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 2.23/1.33  tff(c_18, plain, (k3_subset_1('#skF_1', '#skF_3')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.23/1.33  tff(c_26, plain, (m1_subset_1('#skF_2', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.23/1.33  tff(c_24, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.23/1.33  tff(c_22, plain, (r1_xboole_0('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.23/1.33  tff(c_10, plain, (![A_5, B_6]: (m1_subset_1(k3_subset_1(A_5, B_6), k1_zfmisc_1(A_5)) | ~m1_subset_1(B_6, k1_zfmisc_1(A_5)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.23/1.33  tff(c_52, plain, (![A_21, B_22]: (k3_subset_1(A_21, k3_subset_1(A_21, B_22))=B_22 | ~m1_subset_1(B_22, k1_zfmisc_1(A_21)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.23/1.33  tff(c_61, plain, (k3_subset_1('#skF_1', k3_subset_1('#skF_1', '#skF_3'))='#skF_3'), inference(resolution, [status(thm)], [c_24, c_52])).
% 2.23/1.33  tff(c_8, plain, (![B_4]: (r1_tarski(B_4, B_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.23/1.33  tff(c_139, plain, (![B_28, C_29, A_30]: (r1_xboole_0(B_28, C_29) | ~r1_tarski(B_28, k3_subset_1(A_30, C_29)) | ~m1_subset_1(C_29, k1_zfmisc_1(A_30)) | ~m1_subset_1(B_28, k1_zfmisc_1(A_30)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.23/1.33  tff(c_158, plain, (![A_31, C_32]: (r1_xboole_0(k3_subset_1(A_31, C_32), C_32) | ~m1_subset_1(C_32, k1_zfmisc_1(A_31)) | ~m1_subset_1(k3_subset_1(A_31, C_32), k1_zfmisc_1(A_31)))), inference(resolution, [status(thm)], [c_8, c_139])).
% 2.23/1.33  tff(c_172, plain, (![A_33, B_34]: (r1_xboole_0(k3_subset_1(A_33, B_34), B_34) | ~m1_subset_1(B_34, k1_zfmisc_1(A_33)))), inference(resolution, [status(thm)], [c_10, c_158])).
% 2.23/1.33  tff(c_180, plain, (r1_xboole_0('#skF_3', k3_subset_1('#skF_1', '#skF_3')) | ~m1_subset_1(k3_subset_1('#skF_1', '#skF_3'), k1_zfmisc_1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_61, c_172])).
% 2.23/1.33  tff(c_185, plain, (~m1_subset_1(k3_subset_1('#skF_1', '#skF_3'), k1_zfmisc_1('#skF_1'))), inference(splitLeft, [status(thm)], [c_180])).
% 2.23/1.33  tff(c_188, plain, (~m1_subset_1('#skF_3', k1_zfmisc_1('#skF_1'))), inference(resolution, [status(thm)], [c_10, c_185])).
% 2.23/1.33  tff(c_192, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_24, c_188])).
% 2.23/1.33  tff(c_194, plain, (m1_subset_1(k3_subset_1('#skF_1', '#skF_3'), k1_zfmisc_1('#skF_1'))), inference(splitRight, [status(thm)], [c_180])).
% 2.23/1.33  tff(c_20, plain, (r1_xboole_0(k3_subset_1('#skF_1', '#skF_2'), k3_subset_1('#skF_1', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.23/1.33  tff(c_2, plain, (![B_2, A_1]: (r1_xboole_0(B_2, A_1) | ~r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.23/1.33  tff(c_39, plain, (r1_xboole_0(k3_subset_1('#skF_1', '#skF_3'), k3_subset_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_20, c_2])).
% 2.23/1.33  tff(c_60, plain, (k3_subset_1('#skF_1', k3_subset_1('#skF_1', '#skF_2'))='#skF_2'), inference(resolution, [status(thm)], [c_26, c_52])).
% 2.23/1.33  tff(c_164, plain, (r1_xboole_0(k3_subset_1('#skF_1', k3_subset_1('#skF_1', '#skF_2')), k3_subset_1('#skF_1', '#skF_2')) | ~m1_subset_1(k3_subset_1('#skF_1', '#skF_2'), k1_zfmisc_1('#skF_1')) | ~m1_subset_1('#skF_2', k1_zfmisc_1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_60, c_158])).
% 2.23/1.33  tff(c_170, plain, (r1_xboole_0('#skF_2', k3_subset_1('#skF_1', '#skF_2')) | ~m1_subset_1(k3_subset_1('#skF_1', '#skF_2'), k1_zfmisc_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_60, c_164])).
% 2.23/1.33  tff(c_245, plain, (~m1_subset_1(k3_subset_1('#skF_1', '#skF_2'), k1_zfmisc_1('#skF_1'))), inference(splitLeft, [status(thm)], [c_170])).
% 2.23/1.33  tff(c_248, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1('#skF_1'))), inference(resolution, [status(thm)], [c_10, c_245])).
% 2.23/1.33  tff(c_252, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_26, c_248])).
% 2.23/1.33  tff(c_254, plain, (m1_subset_1(k3_subset_1('#skF_1', '#skF_2'), k1_zfmisc_1('#skF_1'))), inference(splitRight, [status(thm)], [c_170])).
% 2.23/1.33  tff(c_126, plain, (![B_25, A_26, C_27]: (r1_tarski(B_25, k3_subset_1(A_26, C_27)) | ~r1_xboole_0(B_25, C_27) | ~m1_subset_1(C_27, k1_zfmisc_1(A_26)) | ~m1_subset_1(B_25, k1_zfmisc_1(A_26)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.23/1.33  tff(c_137, plain, (![B_25]: (r1_tarski(B_25, '#skF_2') | ~r1_xboole_0(B_25, k3_subset_1('#skF_1', '#skF_2')) | ~m1_subset_1(k3_subset_1('#skF_1', '#skF_2'), k1_zfmisc_1('#skF_1')) | ~m1_subset_1(B_25, k1_zfmisc_1('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_60, c_126])).
% 2.23/1.33  tff(c_300, plain, (![B_41]: (r1_tarski(B_41, '#skF_2') | ~r1_xboole_0(B_41, k3_subset_1('#skF_1', '#skF_2')) | ~m1_subset_1(B_41, k1_zfmisc_1('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_254, c_137])).
% 2.23/1.33  tff(c_314, plain, (r1_tarski(k3_subset_1('#skF_1', '#skF_3'), '#skF_2') | ~m1_subset_1(k3_subset_1('#skF_1', '#skF_3'), k1_zfmisc_1('#skF_1'))), inference(resolution, [status(thm)], [c_39, c_300])).
% 2.23/1.33  tff(c_324, plain, (r1_tarski(k3_subset_1('#skF_1', '#skF_3'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_194, c_314])).
% 2.23/1.33  tff(c_4, plain, (![B_4, A_3]: (B_4=A_3 | ~r1_tarski(B_4, A_3) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.23/1.33  tff(c_138, plain, (![A_26, C_27, B_25]: (k3_subset_1(A_26, C_27)=B_25 | ~r1_tarski(k3_subset_1(A_26, C_27), B_25) | ~r1_xboole_0(B_25, C_27) | ~m1_subset_1(C_27, k1_zfmisc_1(A_26)) | ~m1_subset_1(B_25, k1_zfmisc_1(A_26)))), inference(resolution, [status(thm)], [c_126, c_4])).
% 2.23/1.33  tff(c_327, plain, (k3_subset_1('#skF_1', '#skF_3')='#skF_2' | ~r1_xboole_0('#skF_2', '#skF_3') | ~m1_subset_1('#skF_3', k1_zfmisc_1('#skF_1')) | ~m1_subset_1('#skF_2', k1_zfmisc_1('#skF_1'))), inference(resolution, [status(thm)], [c_324, c_138])).
% 2.23/1.33  tff(c_332, plain, (k3_subset_1('#skF_1', '#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_26, c_24, c_22, c_327])).
% 2.23/1.33  tff(c_334, plain, $false, inference(negUnitSimplification, [status(thm)], [c_18, c_332])).
% 2.23/1.33  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.23/1.33  
% 2.23/1.33  Inference rules
% 2.23/1.33  ----------------------
% 2.23/1.33  #Ref     : 0
% 2.23/1.33  #Sup     : 69
% 2.23/1.33  #Fact    : 0
% 2.23/1.33  #Define  : 0
% 2.23/1.33  #Split   : 2
% 2.23/1.33  #Chain   : 0
% 2.23/1.33  #Close   : 0
% 2.23/1.33  
% 2.23/1.33  Ordering : KBO
% 2.23/1.33  
% 2.23/1.33  Simplification rules
% 2.23/1.33  ----------------------
% 2.23/1.33  #Subsume      : 3
% 2.23/1.33  #Demod        : 46
% 2.23/1.33  #Tautology    : 34
% 2.23/1.33  #SimpNegUnit  : 1
% 2.23/1.33  #BackRed      : 0
% 2.23/1.33  
% 2.23/1.33  #Partial instantiations: 0
% 2.23/1.33  #Strategies tried      : 1
% 2.23/1.33  
% 2.23/1.33  Timing (in seconds)
% 2.23/1.33  ----------------------
% 2.23/1.33  Preprocessing        : 0.28
% 2.23/1.33  Parsing              : 0.16
% 2.23/1.33  CNF conversion       : 0.02
% 2.23/1.33  Main loop            : 0.23
% 2.23/1.33  Inferencing          : 0.09
% 2.23/1.33  Reduction            : 0.06
% 2.23/1.33  Demodulation         : 0.05
% 2.23/1.33  BG Simplification    : 0.01
% 2.23/1.33  Subsumption          : 0.05
% 2.23/1.33  Abstraction          : 0.01
% 2.23/1.33  MUC search           : 0.00
% 2.23/1.33  Cooper               : 0.00
% 2.23/1.33  Total                : 0.54
% 2.23/1.33  Index Insertion      : 0.00
% 2.23/1.33  Index Deletion       : 0.00
% 2.23/1.33  Index Matching       : 0.00
% 2.23/1.33  BG Taut test         : 0.00
%------------------------------------------------------------------------------
