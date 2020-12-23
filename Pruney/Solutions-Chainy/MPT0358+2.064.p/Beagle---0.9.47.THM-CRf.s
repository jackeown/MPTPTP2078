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
% DateTime   : Thu Dec  3 09:56:08 EST 2020

% Result     : Theorem 2.02s
% Output     : CNFRefutation 2.02s
% Verified   : 
% Statistics : Number of formulae       :   51 (  81 expanded)
%              Number of leaves         :   20 (  35 expanded)
%              Depth                    :    6
%              Number of atoms          :   56 ( 109 expanded)
%              Number of equality atoms :   28 (  52 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > m1_subset_1 > k4_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > k1_subset_1 > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_subset_1,type,(
    k1_subset_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_41,axiom,(
    ! [A] : k1_subset_1(A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_subset_1)).

tff(f_52,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => ( r1_tarski(B,k3_subset_1(A,B))
        <=> B = k1_subset_1(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_subset_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_35,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_39,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

tff(c_14,plain,(
    ! [A_9] : k1_subset_1(A_9) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_26,plain,
    ( r1_tarski('#skF_2',k3_subset_1('#skF_1','#skF_2'))
    | k1_subset_1('#skF_1') = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_28,plain,
    ( r1_tarski('#skF_2',k3_subset_1('#skF_1','#skF_2'))
    | k1_xboole_0 = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_26])).

tff(c_47,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_28])).

tff(c_4,plain,(
    ! [A_3,B_4] :
      ( r1_tarski(A_3,B_4)
      | k4_xboole_0(A_3,B_4) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_96,plain,(
    ! [A_26,B_27] :
      ( r1_tarski(A_26,B_27)
      | k4_xboole_0(A_26,B_27) != '#skF_2' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_47,c_4])).

tff(c_20,plain,
    ( k1_subset_1('#skF_1') != '#skF_2'
    | ~ r1_tarski('#skF_2',k3_subset_1('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_27,plain,
    ( k1_xboole_0 != '#skF_2'
    | ~ r1_tarski('#skF_2',k3_subset_1('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_20])).

tff(c_62,plain,(
    ~ r1_tarski('#skF_2',k3_subset_1('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_47,c_27])).

tff(c_100,plain,(
    k4_xboole_0('#skF_2',k3_subset_1('#skF_1','#skF_2')) != '#skF_2' ),
    inference(resolution,[status(thm)],[c_96,c_62])).

tff(c_18,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_164,plain,(
    ! [A_38,B_39] :
      ( k4_xboole_0(A_38,B_39) = k3_subset_1(A_38,B_39)
      | ~ m1_subset_1(B_39,k1_zfmisc_1(A_38)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_168,plain,(
    k4_xboole_0('#skF_1','#skF_2') = k3_subset_1('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_18,c_164])).

tff(c_8,plain,(
    ! [A_5,B_6] : r1_xboole_0(k4_xboole_0(A_5,B_6),B_6) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_37,plain,(
    ! [B_15,A_16] :
      ( r1_xboole_0(B_15,A_16)
      | ~ r1_xboole_0(A_16,B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_40,plain,(
    ! [B_6,A_5] : r1_xboole_0(B_6,k4_xboole_0(A_5,B_6)) ),
    inference(resolution,[status(thm)],[c_8,c_37])).

tff(c_63,plain,(
    ! [A_22,B_23] :
      ( k4_xboole_0(A_22,B_23) = A_22
      | ~ r1_xboole_0(A_22,B_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_70,plain,(
    ! [B_6,A_5] : k4_xboole_0(B_6,k4_xboole_0(A_5,B_6)) = B_6 ),
    inference(resolution,[status(thm)],[c_40,c_63])).

tff(c_177,plain,(
    k4_xboole_0('#skF_2',k3_subset_1('#skF_1','#skF_2')) = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_168,c_70])).

tff(c_188,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_100,c_177])).

tff(c_190,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(splitRight,[status(thm)],[c_28])).

tff(c_335,plain,(
    ! [A_52,B_53] :
      ( k4_xboole_0(A_52,B_53) = k3_subset_1(A_52,B_53)
      | ~ m1_subset_1(B_53,k1_zfmisc_1(A_52)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_339,plain,(
    k4_xboole_0('#skF_1','#skF_2') = k3_subset_1('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_18,c_335])).

tff(c_219,plain,(
    ! [A_42,B_43] :
      ( k4_xboole_0(A_42,B_43) = A_42
      | ~ r1_xboole_0(A_42,B_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_238,plain,(
    ! [B_6,A_5] : k4_xboole_0(B_6,k4_xboole_0(A_5,B_6)) = B_6 ),
    inference(resolution,[status(thm)],[c_40,c_219])).

tff(c_346,plain,(
    k4_xboole_0('#skF_2',k3_subset_1('#skF_1','#skF_2')) = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_339,c_238])).

tff(c_189,plain,(
    r1_tarski('#skF_2',k3_subset_1('#skF_1','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_28])).

tff(c_6,plain,(
    ! [A_3,B_4] :
      ( k4_xboole_0(A_3,B_4) = k1_xboole_0
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_194,plain,(
    k4_xboole_0('#skF_2',k3_subset_1('#skF_1','#skF_2')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_189,c_6])).

tff(c_372,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_346,c_194])).

tff(c_374,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_190,c_372])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n013.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 19:53:54 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.02/1.23  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.02/1.24  
% 2.02/1.24  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.02/1.24  %$ r1_xboole_0 > r1_tarski > m1_subset_1 > k4_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > k1_subset_1 > k1_xboole_0 > #skF_2 > #skF_1
% 2.02/1.24  
% 2.02/1.24  %Foreground sorts:
% 2.02/1.24  
% 2.02/1.24  
% 2.02/1.24  %Background operators:
% 2.02/1.24  
% 2.02/1.24  
% 2.02/1.24  %Foreground operators:
% 2.02/1.24  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.02/1.24  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.02/1.24  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.02/1.24  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.02/1.24  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 2.02/1.24  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.02/1.24  tff('#skF_2', type, '#skF_2': $i).
% 2.02/1.24  tff('#skF_1', type, '#skF_1': $i).
% 2.02/1.24  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.02/1.24  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.02/1.24  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.02/1.24  tff(k1_subset_1, type, k1_subset_1: $i > $i).
% 2.02/1.24  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.02/1.24  
% 2.02/1.25  tff(f_41, axiom, (![A]: (k1_subset_1(A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_subset_1)).
% 2.02/1.25  tff(f_52, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (r1_tarski(B, k3_subset_1(A, B)) <=> (B = k1_subset_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_subset_1)).
% 2.02/1.25  tff(f_33, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 2.02/1.25  tff(f_45, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 2.02/1.25  tff(f_35, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_xboole_1)).
% 2.02/1.25  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 2.02/1.25  tff(f_39, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_xboole_1)).
% 2.02/1.25  tff(c_14, plain, (![A_9]: (k1_subset_1(A_9)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.02/1.25  tff(c_26, plain, (r1_tarski('#skF_2', k3_subset_1('#skF_1', '#skF_2')) | k1_subset_1('#skF_1')='#skF_2'), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.02/1.25  tff(c_28, plain, (r1_tarski('#skF_2', k3_subset_1('#skF_1', '#skF_2')) | k1_xboole_0='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_14, c_26])).
% 2.02/1.25  tff(c_47, plain, (k1_xboole_0='#skF_2'), inference(splitLeft, [status(thm)], [c_28])).
% 2.02/1.25  tff(c_4, plain, (![A_3, B_4]: (r1_tarski(A_3, B_4) | k4_xboole_0(A_3, B_4)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.02/1.25  tff(c_96, plain, (![A_26, B_27]: (r1_tarski(A_26, B_27) | k4_xboole_0(A_26, B_27)!='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_47, c_4])).
% 2.02/1.25  tff(c_20, plain, (k1_subset_1('#skF_1')!='#skF_2' | ~r1_tarski('#skF_2', k3_subset_1('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.02/1.25  tff(c_27, plain, (k1_xboole_0!='#skF_2' | ~r1_tarski('#skF_2', k3_subset_1('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_20])).
% 2.02/1.25  tff(c_62, plain, (~r1_tarski('#skF_2', k3_subset_1('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_47, c_27])).
% 2.02/1.25  tff(c_100, plain, (k4_xboole_0('#skF_2', k3_subset_1('#skF_1', '#skF_2'))!='#skF_2'), inference(resolution, [status(thm)], [c_96, c_62])).
% 2.02/1.25  tff(c_18, plain, (m1_subset_1('#skF_2', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.02/1.25  tff(c_164, plain, (![A_38, B_39]: (k4_xboole_0(A_38, B_39)=k3_subset_1(A_38, B_39) | ~m1_subset_1(B_39, k1_zfmisc_1(A_38)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.02/1.25  tff(c_168, plain, (k4_xboole_0('#skF_1', '#skF_2')=k3_subset_1('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_18, c_164])).
% 2.02/1.25  tff(c_8, plain, (![A_5, B_6]: (r1_xboole_0(k4_xboole_0(A_5, B_6), B_6))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.02/1.25  tff(c_37, plain, (![B_15, A_16]: (r1_xboole_0(B_15, A_16) | ~r1_xboole_0(A_16, B_15))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.02/1.25  tff(c_40, plain, (![B_6, A_5]: (r1_xboole_0(B_6, k4_xboole_0(A_5, B_6)))), inference(resolution, [status(thm)], [c_8, c_37])).
% 2.02/1.25  tff(c_63, plain, (![A_22, B_23]: (k4_xboole_0(A_22, B_23)=A_22 | ~r1_xboole_0(A_22, B_23))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.02/1.25  tff(c_70, plain, (![B_6, A_5]: (k4_xboole_0(B_6, k4_xboole_0(A_5, B_6))=B_6)), inference(resolution, [status(thm)], [c_40, c_63])).
% 2.02/1.25  tff(c_177, plain, (k4_xboole_0('#skF_2', k3_subset_1('#skF_1', '#skF_2'))='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_168, c_70])).
% 2.02/1.25  tff(c_188, plain, $false, inference(negUnitSimplification, [status(thm)], [c_100, c_177])).
% 2.02/1.25  tff(c_190, plain, (k1_xboole_0!='#skF_2'), inference(splitRight, [status(thm)], [c_28])).
% 2.02/1.25  tff(c_335, plain, (![A_52, B_53]: (k4_xboole_0(A_52, B_53)=k3_subset_1(A_52, B_53) | ~m1_subset_1(B_53, k1_zfmisc_1(A_52)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.02/1.25  tff(c_339, plain, (k4_xboole_0('#skF_1', '#skF_2')=k3_subset_1('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_18, c_335])).
% 2.02/1.25  tff(c_219, plain, (![A_42, B_43]: (k4_xboole_0(A_42, B_43)=A_42 | ~r1_xboole_0(A_42, B_43))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.02/1.25  tff(c_238, plain, (![B_6, A_5]: (k4_xboole_0(B_6, k4_xboole_0(A_5, B_6))=B_6)), inference(resolution, [status(thm)], [c_40, c_219])).
% 2.02/1.25  tff(c_346, plain, (k4_xboole_0('#skF_2', k3_subset_1('#skF_1', '#skF_2'))='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_339, c_238])).
% 2.02/1.25  tff(c_189, plain, (r1_tarski('#skF_2', k3_subset_1('#skF_1', '#skF_2'))), inference(splitRight, [status(thm)], [c_28])).
% 2.02/1.25  tff(c_6, plain, (![A_3, B_4]: (k4_xboole_0(A_3, B_4)=k1_xboole_0 | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.02/1.25  tff(c_194, plain, (k4_xboole_0('#skF_2', k3_subset_1('#skF_1', '#skF_2'))=k1_xboole_0), inference(resolution, [status(thm)], [c_189, c_6])).
% 2.02/1.25  tff(c_372, plain, (k1_xboole_0='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_346, c_194])).
% 2.02/1.25  tff(c_374, plain, $false, inference(negUnitSimplification, [status(thm)], [c_190, c_372])).
% 2.02/1.25  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.02/1.25  
% 2.02/1.25  Inference rules
% 2.02/1.25  ----------------------
% 2.02/1.25  #Ref     : 0
% 2.02/1.25  #Sup     : 89
% 2.02/1.25  #Fact    : 0
% 2.02/1.25  #Define  : 0
% 2.02/1.25  #Split   : 1
% 2.02/1.25  #Chain   : 0
% 2.02/1.25  #Close   : 0
% 2.02/1.25  
% 2.02/1.25  Ordering : KBO
% 2.02/1.25  
% 2.02/1.25  Simplification rules
% 2.02/1.25  ----------------------
% 2.02/1.25  #Subsume      : 3
% 2.02/1.25  #Demod        : 44
% 2.02/1.25  #Tautology    : 53
% 2.02/1.25  #SimpNegUnit  : 2
% 2.02/1.25  #BackRed      : 3
% 2.02/1.25  
% 2.02/1.25  #Partial instantiations: 0
% 2.02/1.25  #Strategies tried      : 1
% 2.02/1.25  
% 2.02/1.25  Timing (in seconds)
% 2.02/1.25  ----------------------
% 2.02/1.25  Preprocessing        : 0.29
% 2.02/1.25  Parsing              : 0.15
% 2.02/1.25  CNF conversion       : 0.02
% 2.02/1.25  Main loop            : 0.21
% 2.02/1.26  Inferencing          : 0.08
% 2.02/1.26  Reduction            : 0.07
% 2.02/1.26  Demodulation         : 0.05
% 2.02/1.26  BG Simplification    : 0.01
% 2.02/1.26  Subsumption          : 0.03
% 2.02/1.26  Abstraction          : 0.01
% 2.02/1.26  MUC search           : 0.00
% 2.02/1.26  Cooper               : 0.00
% 2.02/1.26  Total                : 0.52
% 2.02/1.26  Index Insertion      : 0.00
% 2.02/1.26  Index Deletion       : 0.00
% 2.02/1.26  Index Matching       : 0.00
% 2.02/1.26  BG Taut test         : 0.00
%------------------------------------------------------------------------------
