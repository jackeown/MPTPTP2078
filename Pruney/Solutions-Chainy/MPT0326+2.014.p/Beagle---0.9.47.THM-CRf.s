%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:54:30 EST 2020

% Result     : Theorem 2.61s
% Output     : CNFRefutation 2.61s
% Verified   : 
% Statistics : Number of formulae       :   58 ( 136 expanded)
%              Number of leaves         :   18 (  50 expanded)
%              Depth                    :   10
%              Number of atoms          :   85 ( 273 expanded)
%              Number of equality atoms :   18 (  49 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > v1_xboole_0 > k2_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(f_79,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B,C,D] :
            ( ( r1_tarski(k2_zfmisc_1(A,B),k2_zfmisc_1(C,D))
              | r1_tarski(k2_zfmisc_1(B,A),k2_zfmisc_1(D,C)) )
           => r1_tarski(B,D) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t139_zfmisc_1)).

tff(f_37,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_68,axiom,(
    ! [A,B,C,D] :
      ( r1_tarski(k2_zfmisc_1(A,B),k2_zfmisc_1(C,D))
     => ( k2_zfmisc_1(A,B) = k1_xboole_0
        | ( r1_tarski(A,C)
          & r1_tarski(B,D) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t138_zfmisc_1)).

tff(f_60,axiom,(
    ! [A,B,C] :
      ~ ( A != k1_xboole_0
        & ( r1_tarski(k2_zfmisc_1(B,A),k2_zfmisc_1(C,A))
          | r1_tarski(k2_zfmisc_1(A,B),k2_zfmisc_1(A,C)) )
        & ~ r1_tarski(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t117_zfmisc_1)).

tff(f_39,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_49,axiom,(
    ! [A,B,C] :
      ( ~ v1_xboole_0(C)
     => ~ ( r1_tarski(C,A)
          & r1_tarski(C,B)
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t68_xboole_1)).

tff(c_24,plain,(
    ~ v1_xboole_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_6,plain,(
    ! [A_6] : r1_tarski(k1_xboole_0,A_6) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_20,plain,(
    ~ r1_tarski('#skF_2','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_22,plain,
    ( r1_tarski(k2_zfmisc_1('#skF_2','#skF_1'),k2_zfmisc_1('#skF_4','#skF_3'))
    | r1_tarski(k2_zfmisc_1('#skF_1','#skF_2'),k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_53,plain,(
    r1_tarski(k2_zfmisc_1('#skF_1','#skF_2'),k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_22])).

tff(c_553,plain,(
    ! [B_127,D_128,A_129,C_130] :
      ( r1_tarski(B_127,D_128)
      | k2_zfmisc_1(A_129,B_127) = k1_xboole_0
      | ~ r1_tarski(k2_zfmisc_1(A_129,B_127),k2_zfmisc_1(C_130,D_128)) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_560,plain,
    ( r1_tarski('#skF_2','#skF_4')
    | k2_zfmisc_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_53,c_553])).

tff(c_564,plain,(
    k2_zfmisc_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_20,c_560])).

tff(c_12,plain,(
    ! [A_11,B_12,C_13] :
      ( ~ r1_tarski(k2_zfmisc_1(A_11,B_12),k2_zfmisc_1(A_11,C_13))
      | r1_tarski(B_12,C_13)
      | k1_xboole_0 = A_11 ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_578,plain,(
    ! [C_13] :
      ( ~ r1_tarski(k1_xboole_0,k2_zfmisc_1('#skF_1',C_13))
      | r1_tarski('#skF_2',C_13)
      | k1_xboole_0 = '#skF_1' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_564,c_12])).

tff(c_593,plain,(
    ! [C_13] :
      ( r1_tarski('#skF_2',C_13)
      | k1_xboole_0 = '#skF_1' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_578])).

tff(c_597,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_593])).

tff(c_8,plain,(
    ! [A_7] : r1_xboole_0(A_7,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_46,plain,(
    ! [A_31,B_32,C_33] :
      ( ~ r1_xboole_0(A_31,B_32)
      | ~ r1_tarski(C_33,B_32)
      | ~ r1_tarski(C_33,A_31)
      | v1_xboole_0(C_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_57,plain,(
    ! [C_34,A_35] :
      ( ~ r1_tarski(C_34,k1_xboole_0)
      | ~ r1_tarski(C_34,A_35)
      | v1_xboole_0(C_34) ) ),
    inference(resolution,[status(thm)],[c_8,c_46])).

tff(c_60,plain,(
    ! [A_35] :
      ( ~ r1_tarski(k1_xboole_0,A_35)
      | v1_xboole_0(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_6,c_57])).

tff(c_63,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_60])).

tff(c_605,plain,(
    v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_597,c_63])).

tff(c_612,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_605])).

tff(c_613,plain,(
    ! [C_13] : r1_tarski('#skF_2',C_13) ),
    inference(splitRight,[status(thm)],[c_593])).

tff(c_617,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_613,c_20])).

tff(c_618,plain,(
    r1_tarski(k2_zfmisc_1('#skF_2','#skF_1'),k2_zfmisc_1('#skF_4','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_22])).

tff(c_639,plain,(
    ! [B_140,D_141,A_142,C_143] :
      ( r1_tarski(B_140,D_141)
      | k2_zfmisc_1(A_142,B_140) = k1_xboole_0
      | ~ r1_tarski(k2_zfmisc_1(A_142,B_140),k2_zfmisc_1(C_143,D_141)) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_643,plain,
    ( r1_tarski('#skF_1','#skF_3')
    | k2_zfmisc_1('#skF_2','#skF_1') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_618,c_639])).

tff(c_644,plain,(
    k2_zfmisc_1('#skF_2','#skF_1') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_643])).

tff(c_657,plain,(
    ! [C_13] :
      ( ~ r1_tarski(k1_xboole_0,k2_zfmisc_1('#skF_2',C_13))
      | r1_tarski('#skF_1',C_13)
      | k1_xboole_0 = '#skF_2' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_644,c_12])).

tff(c_672,plain,(
    ! [C_13] :
      ( r1_tarski('#skF_1',C_13)
      | k1_xboole_0 = '#skF_2' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_657])).

tff(c_676,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_672])).

tff(c_695,plain,(
    ! [A_6] : r1_tarski('#skF_2',A_6) ),
    inference(demodulation,[status(thm),theory(equality)],[c_676,c_6])).

tff(c_714,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_695,c_20])).

tff(c_715,plain,(
    ! [C_13] : r1_tarski('#skF_1',C_13) ),
    inference(splitRight,[status(thm)],[c_672])).

tff(c_717,plain,(
    ! [C_149] : r1_tarski('#skF_1',C_149) ),
    inference(splitRight,[status(thm)],[c_672])).

tff(c_52,plain,(
    ! [C_33,A_7] :
      ( ~ r1_tarski(C_33,k1_xboole_0)
      | ~ r1_tarski(C_33,A_7)
      | v1_xboole_0(C_33) ) ),
    inference(resolution,[status(thm)],[c_8,c_46])).

tff(c_720,plain,(
    ! [A_7] :
      ( ~ r1_tarski('#skF_1',A_7)
      | v1_xboole_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_717,c_52])).

tff(c_728,plain,(
    v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_715,c_720])).

tff(c_730,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_728])).

tff(c_732,plain,(
    k2_zfmisc_1('#skF_2','#skF_1') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_643])).

tff(c_736,plain,(
    ! [A_150,C_151,B_152,D_153] :
      ( r1_tarski(A_150,C_151)
      | k2_zfmisc_1(A_150,B_152) = k1_xboole_0
      | ~ r1_tarski(k2_zfmisc_1(A_150,B_152),k2_zfmisc_1(C_151,D_153)) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_739,plain,
    ( r1_tarski('#skF_2','#skF_4')
    | k2_zfmisc_1('#skF_2','#skF_1') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_618,c_736])).

tff(c_743,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_732,c_20,c_739])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:00:02 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.61/1.34  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.61/1.34  
% 2.61/1.34  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.61/1.34  %$ r1_xboole_0 > r1_tarski > v1_xboole_0 > k2_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.61/1.34  
% 2.61/1.34  %Foreground sorts:
% 2.61/1.34  
% 2.61/1.34  
% 2.61/1.34  %Background operators:
% 2.61/1.34  
% 2.61/1.34  
% 2.61/1.34  %Foreground operators:
% 2.61/1.34  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.61/1.34  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.61/1.34  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.61/1.34  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.61/1.34  tff('#skF_2', type, '#skF_2': $i).
% 2.61/1.34  tff('#skF_3', type, '#skF_3': $i).
% 2.61/1.34  tff('#skF_1', type, '#skF_1': $i).
% 2.61/1.34  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.61/1.34  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.61/1.34  tff('#skF_4', type, '#skF_4': $i).
% 2.61/1.34  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.61/1.34  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.61/1.34  
% 2.61/1.36  tff(f_79, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B, C, D]: ((r1_tarski(k2_zfmisc_1(A, B), k2_zfmisc_1(C, D)) | r1_tarski(k2_zfmisc_1(B, A), k2_zfmisc_1(D, C))) => r1_tarski(B, D))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t139_zfmisc_1)).
% 2.61/1.36  tff(f_37, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.61/1.36  tff(f_68, axiom, (![A, B, C, D]: (r1_tarski(k2_zfmisc_1(A, B), k2_zfmisc_1(C, D)) => ((k2_zfmisc_1(A, B) = k1_xboole_0) | (r1_tarski(A, C) & r1_tarski(B, D))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t138_zfmisc_1)).
% 2.61/1.36  tff(f_60, axiom, (![A, B, C]: ~((~(A = k1_xboole_0) & (r1_tarski(k2_zfmisc_1(B, A), k2_zfmisc_1(C, A)) | r1_tarski(k2_zfmisc_1(A, B), k2_zfmisc_1(A, C)))) & ~r1_tarski(B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t117_zfmisc_1)).
% 2.61/1.36  tff(f_39, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 2.61/1.36  tff(f_49, axiom, (![A, B, C]: (~v1_xboole_0(C) => ~((r1_tarski(C, A) & r1_tarski(C, B)) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t68_xboole_1)).
% 2.61/1.36  tff(c_24, plain, (~v1_xboole_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.61/1.36  tff(c_6, plain, (![A_6]: (r1_tarski(k1_xboole_0, A_6))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.61/1.36  tff(c_20, plain, (~r1_tarski('#skF_2', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.61/1.36  tff(c_22, plain, (r1_tarski(k2_zfmisc_1('#skF_2', '#skF_1'), k2_zfmisc_1('#skF_4', '#skF_3')) | r1_tarski(k2_zfmisc_1('#skF_1', '#skF_2'), k2_zfmisc_1('#skF_3', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.61/1.36  tff(c_53, plain, (r1_tarski(k2_zfmisc_1('#skF_1', '#skF_2'), k2_zfmisc_1('#skF_3', '#skF_4'))), inference(splitLeft, [status(thm)], [c_22])).
% 2.61/1.36  tff(c_553, plain, (![B_127, D_128, A_129, C_130]: (r1_tarski(B_127, D_128) | k2_zfmisc_1(A_129, B_127)=k1_xboole_0 | ~r1_tarski(k2_zfmisc_1(A_129, B_127), k2_zfmisc_1(C_130, D_128)))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.61/1.36  tff(c_560, plain, (r1_tarski('#skF_2', '#skF_4') | k2_zfmisc_1('#skF_1', '#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_53, c_553])).
% 2.61/1.36  tff(c_564, plain, (k2_zfmisc_1('#skF_1', '#skF_2')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_20, c_560])).
% 2.61/1.36  tff(c_12, plain, (![A_11, B_12, C_13]: (~r1_tarski(k2_zfmisc_1(A_11, B_12), k2_zfmisc_1(A_11, C_13)) | r1_tarski(B_12, C_13) | k1_xboole_0=A_11)), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.61/1.36  tff(c_578, plain, (![C_13]: (~r1_tarski(k1_xboole_0, k2_zfmisc_1('#skF_1', C_13)) | r1_tarski('#skF_2', C_13) | k1_xboole_0='#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_564, c_12])).
% 2.61/1.36  tff(c_593, plain, (![C_13]: (r1_tarski('#skF_2', C_13) | k1_xboole_0='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_6, c_578])).
% 2.61/1.36  tff(c_597, plain, (k1_xboole_0='#skF_1'), inference(splitLeft, [status(thm)], [c_593])).
% 2.61/1.36  tff(c_8, plain, (![A_7]: (r1_xboole_0(A_7, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.61/1.36  tff(c_46, plain, (![A_31, B_32, C_33]: (~r1_xboole_0(A_31, B_32) | ~r1_tarski(C_33, B_32) | ~r1_tarski(C_33, A_31) | v1_xboole_0(C_33))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.61/1.36  tff(c_57, plain, (![C_34, A_35]: (~r1_tarski(C_34, k1_xboole_0) | ~r1_tarski(C_34, A_35) | v1_xboole_0(C_34))), inference(resolution, [status(thm)], [c_8, c_46])).
% 2.61/1.36  tff(c_60, plain, (![A_35]: (~r1_tarski(k1_xboole_0, A_35) | v1_xboole_0(k1_xboole_0))), inference(resolution, [status(thm)], [c_6, c_57])).
% 2.61/1.36  tff(c_63, plain, (v1_xboole_0(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_60])).
% 2.61/1.36  tff(c_605, plain, (v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_597, c_63])).
% 2.61/1.36  tff(c_612, plain, $false, inference(negUnitSimplification, [status(thm)], [c_24, c_605])).
% 2.61/1.36  tff(c_613, plain, (![C_13]: (r1_tarski('#skF_2', C_13))), inference(splitRight, [status(thm)], [c_593])).
% 2.61/1.36  tff(c_617, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_613, c_20])).
% 2.61/1.36  tff(c_618, plain, (r1_tarski(k2_zfmisc_1('#skF_2', '#skF_1'), k2_zfmisc_1('#skF_4', '#skF_3'))), inference(splitRight, [status(thm)], [c_22])).
% 2.61/1.36  tff(c_639, plain, (![B_140, D_141, A_142, C_143]: (r1_tarski(B_140, D_141) | k2_zfmisc_1(A_142, B_140)=k1_xboole_0 | ~r1_tarski(k2_zfmisc_1(A_142, B_140), k2_zfmisc_1(C_143, D_141)))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.61/1.36  tff(c_643, plain, (r1_tarski('#skF_1', '#skF_3') | k2_zfmisc_1('#skF_2', '#skF_1')=k1_xboole_0), inference(resolution, [status(thm)], [c_618, c_639])).
% 2.61/1.36  tff(c_644, plain, (k2_zfmisc_1('#skF_2', '#skF_1')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_643])).
% 2.61/1.36  tff(c_657, plain, (![C_13]: (~r1_tarski(k1_xboole_0, k2_zfmisc_1('#skF_2', C_13)) | r1_tarski('#skF_1', C_13) | k1_xboole_0='#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_644, c_12])).
% 2.61/1.36  tff(c_672, plain, (![C_13]: (r1_tarski('#skF_1', C_13) | k1_xboole_0='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_6, c_657])).
% 2.61/1.36  tff(c_676, plain, (k1_xboole_0='#skF_2'), inference(splitLeft, [status(thm)], [c_672])).
% 2.61/1.36  tff(c_695, plain, (![A_6]: (r1_tarski('#skF_2', A_6))), inference(demodulation, [status(thm), theory('equality')], [c_676, c_6])).
% 2.61/1.36  tff(c_714, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_695, c_20])).
% 2.61/1.36  tff(c_715, plain, (![C_13]: (r1_tarski('#skF_1', C_13))), inference(splitRight, [status(thm)], [c_672])).
% 2.61/1.36  tff(c_717, plain, (![C_149]: (r1_tarski('#skF_1', C_149))), inference(splitRight, [status(thm)], [c_672])).
% 2.61/1.36  tff(c_52, plain, (![C_33, A_7]: (~r1_tarski(C_33, k1_xboole_0) | ~r1_tarski(C_33, A_7) | v1_xboole_0(C_33))), inference(resolution, [status(thm)], [c_8, c_46])).
% 2.61/1.36  tff(c_720, plain, (![A_7]: (~r1_tarski('#skF_1', A_7) | v1_xboole_0('#skF_1'))), inference(resolution, [status(thm)], [c_717, c_52])).
% 2.61/1.36  tff(c_728, plain, (v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_715, c_720])).
% 2.61/1.36  tff(c_730, plain, $false, inference(negUnitSimplification, [status(thm)], [c_24, c_728])).
% 2.61/1.36  tff(c_732, plain, (k2_zfmisc_1('#skF_2', '#skF_1')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_643])).
% 2.61/1.36  tff(c_736, plain, (![A_150, C_151, B_152, D_153]: (r1_tarski(A_150, C_151) | k2_zfmisc_1(A_150, B_152)=k1_xboole_0 | ~r1_tarski(k2_zfmisc_1(A_150, B_152), k2_zfmisc_1(C_151, D_153)))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.61/1.36  tff(c_739, plain, (r1_tarski('#skF_2', '#skF_4') | k2_zfmisc_1('#skF_2', '#skF_1')=k1_xboole_0), inference(resolution, [status(thm)], [c_618, c_736])).
% 2.61/1.36  tff(c_743, plain, $false, inference(negUnitSimplification, [status(thm)], [c_732, c_20, c_739])).
% 2.61/1.36  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.61/1.36  
% 2.61/1.36  Inference rules
% 2.61/1.36  ----------------------
% 2.61/1.36  #Ref     : 0
% 2.61/1.36  #Sup     : 133
% 2.61/1.36  #Fact    : 0
% 2.61/1.36  #Define  : 0
% 2.61/1.36  #Split   : 13
% 2.61/1.36  #Chain   : 0
% 2.61/1.36  #Close   : 0
% 2.61/1.36  
% 2.61/1.36  Ordering : KBO
% 2.61/1.36  
% 2.61/1.36  Simplification rules
% 2.61/1.36  ----------------------
% 2.61/1.36  #Subsume      : 19
% 2.61/1.36  #Demod        : 170
% 2.61/1.36  #Tautology    : 64
% 2.61/1.36  #SimpNegUnit  : 11
% 2.61/1.36  #BackRed      : 78
% 2.61/1.36  
% 2.61/1.36  #Partial instantiations: 0
% 2.61/1.36  #Strategies tried      : 1
% 2.61/1.36  
% 2.61/1.36  Timing (in seconds)
% 2.61/1.36  ----------------------
% 2.61/1.36  Preprocessing        : 0.26
% 2.61/1.36  Parsing              : 0.15
% 2.61/1.36  CNF conversion       : 0.02
% 2.61/1.36  Main loop            : 0.34
% 2.61/1.36  Inferencing          : 0.12
% 2.61/1.36  Reduction            : 0.10
% 2.61/1.36  Demodulation         : 0.07
% 2.61/1.36  BG Simplification    : 0.02
% 2.61/1.36  Subsumption          : 0.07
% 2.61/1.36  Abstraction          : 0.01
% 2.61/1.36  MUC search           : 0.00
% 2.61/1.36  Cooper               : 0.00
% 2.61/1.36  Total                : 0.63
% 2.61/1.36  Index Insertion      : 0.00
% 2.61/1.36  Index Deletion       : 0.00
% 2.61/1.36  Index Matching       : 0.00
% 2.61/1.36  BG Taut test         : 0.00
%------------------------------------------------------------------------------
