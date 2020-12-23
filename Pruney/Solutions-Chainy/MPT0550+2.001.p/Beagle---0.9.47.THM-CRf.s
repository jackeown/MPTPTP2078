%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:00:52 EST 2020

% Result     : Theorem 2.61s
% Output     : CNFRefutation 2.61s
% Verified   : 
% Statistics : Number of formulae       :   60 ( 116 expanded)
%              Number of leaves         :   26 (  50 expanded)
%              Depth                    :   11
%              Number of atoms          :   71 ( 179 expanded)
%              Number of equality atoms :   30 (  74 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_xboole_0 > v1_relat_1 > k9_relat_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_31,axiom,(
    ? [A] : v1_xboole_0(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc1_xboole_0)).

tff(f_29,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_92,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ~ ( A != k1_xboole_0
            & r1_tarski(A,k1_relat_1(B))
            & k9_relat_1(B,A) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_relat_1)).

tff(f_75,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k7_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).

tff(f_81,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(A,k1_relat_1(B))
       => k1_relat_1(k7_relat_1(B,A)) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_relat_1)).

tff(f_61,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => r1_tarski(A,k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_relat_1)).

tff(f_39,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(c_4,plain,(
    v1_xboole_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_87,plain,(
    ! [A_23] :
      ( k1_xboole_0 = A_23
      | ~ v1_xboole_0(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_91,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_4,c_87])).

tff(c_42,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_99,plain,(
    '#skF_2' != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_91,c_42])).

tff(c_34,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_97,plain,(
    k1_relat_1('#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_91,c_91,c_34])).

tff(c_44,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_16,plain,(
    ! [A_5] : k2_zfmisc_1(A_5,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_95,plain,(
    ! [A_5] : k2_zfmisc_1(A_5,'#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_91,c_91,c_16])).

tff(c_38,plain,(
    k9_relat_1('#skF_3','#skF_2') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_94,plain,(
    k9_relat_1('#skF_3','#skF_2') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_91,c_38])).

tff(c_24,plain,(
    ! [B_11,A_10] :
      ( k2_relat_1(k7_relat_1(B_11,A_10)) = k9_relat_1(B_11,A_10)
      | ~ v1_relat_1(B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_22,plain,(
    ! [A_8,B_9] :
      ( v1_relat_1(k7_relat_1(A_8,B_9))
      | ~ v1_relat_1(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_40,plain,(
    r1_tarski('#skF_2',k1_relat_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_211,plain,(
    ! [B_38,A_39] :
      ( k1_relat_1(k7_relat_1(B_38,A_39)) = A_39
      | ~ r1_tarski(A_39,k1_relat_1(B_38))
      | ~ v1_relat_1(B_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_221,plain,
    ( k1_relat_1(k7_relat_1('#skF_3','#skF_2')) = '#skF_2'
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_40,c_211])).

tff(c_231,plain,(
    k1_relat_1(k7_relat_1('#skF_3','#skF_2')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_221])).

tff(c_26,plain,(
    ! [A_12] :
      ( r1_tarski(A_12,k2_zfmisc_1(k1_relat_1(A_12),k2_relat_1(A_12)))
      | ~ v1_relat_1(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_239,plain,
    ( r1_tarski(k7_relat_1('#skF_3','#skF_2'),k2_zfmisc_1('#skF_2',k2_relat_1(k7_relat_1('#skF_3','#skF_2'))))
    | ~ v1_relat_1(k7_relat_1('#skF_3','#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_231,c_26])).

tff(c_413,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_3','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_239])).

tff(c_416,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_22,c_413])).

tff(c_420,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_416])).

tff(c_421,plain,(
    r1_tarski(k7_relat_1('#skF_3','#skF_2'),k2_zfmisc_1('#skF_2',k2_relat_1(k7_relat_1('#skF_3','#skF_2')))) ),
    inference(splitRight,[status(thm)],[c_239])).

tff(c_607,plain,
    ( r1_tarski(k7_relat_1('#skF_3','#skF_2'),k2_zfmisc_1('#skF_2',k9_relat_1('#skF_3','#skF_2')))
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_421])).

tff(c_610,plain,(
    r1_tarski(k7_relat_1('#skF_3','#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_95,c_94,c_607])).

tff(c_12,plain,(
    ! [A_4] : r1_tarski(k1_xboole_0,A_4) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_98,plain,(
    ! [A_4] : r1_tarski('#skF_1',A_4) ),
    inference(demodulation,[status(thm),theory(equality)],[c_91,c_12])).

tff(c_158,plain,(
    ! [B_32,A_33] :
      ( B_32 = A_33
      | ~ r1_tarski(B_32,A_33)
      | ~ r1_tarski(A_33,B_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_165,plain,(
    ! [A_4] :
      ( A_4 = '#skF_1'
      | ~ r1_tarski(A_4,'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_98,c_158])).

tff(c_675,plain,(
    k7_relat_1('#skF_3','#skF_2') = '#skF_1' ),
    inference(resolution,[status(thm)],[c_610,c_165])).

tff(c_683,plain,(
    k1_relat_1('#skF_1') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_675,c_231])).

tff(c_687,plain,(
    '#skF_2' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_97,c_683])).

tff(c_689,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_99,c_687])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n007.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 09:32:51 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.61/1.38  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.61/1.38  
% 2.61/1.38  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.61/1.39  %$ r1_tarski > v1_xboole_0 > v1_relat_1 > k9_relat_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.61/1.39  
% 2.61/1.39  %Foreground sorts:
% 2.61/1.39  
% 2.61/1.39  
% 2.61/1.39  %Background operators:
% 2.61/1.39  
% 2.61/1.39  
% 2.61/1.39  %Foreground operators:
% 2.61/1.39  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.61/1.39  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.61/1.39  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.61/1.39  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.61/1.39  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.61/1.39  tff('#skF_2', type, '#skF_2': $i).
% 2.61/1.39  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.61/1.39  tff('#skF_3', type, '#skF_3': $i).
% 2.61/1.39  tff('#skF_1', type, '#skF_1': $i).
% 2.61/1.39  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.61/1.39  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.61/1.39  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.61/1.39  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.61/1.39  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.61/1.39  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.61/1.39  
% 2.61/1.40  tff(f_31, axiom, (?[A]: v1_xboole_0(A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', rc1_xboole_0)).
% 2.61/1.40  tff(f_29, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 2.61/1.40  tff(f_92, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => ~((~(A = k1_xboole_0) & r1_tarski(A, k1_relat_1(B))) & (k9_relat_1(B, A) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t152_relat_1)).
% 2.61/1.40  tff(f_75, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 2.61/1.40  tff(f_45, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 2.61/1.40  tff(f_57, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_relat_1)).
% 2.61/1.40  tff(f_53, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k7_relat_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 2.61/1.40  tff(f_81, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(A, k1_relat_1(B)) => (k1_relat_1(k7_relat_1(B, A)) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_relat_1)).
% 2.61/1.40  tff(f_61, axiom, (![A]: (v1_relat_1(A) => r1_tarski(A, k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t21_relat_1)).
% 2.61/1.40  tff(f_39, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.61/1.40  tff(f_37, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.61/1.40  tff(c_4, plain, (v1_xboole_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.61/1.40  tff(c_87, plain, (![A_23]: (k1_xboole_0=A_23 | ~v1_xboole_0(A_23))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.61/1.40  tff(c_91, plain, (k1_xboole_0='#skF_1'), inference(resolution, [status(thm)], [c_4, c_87])).
% 2.61/1.40  tff(c_42, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.61/1.40  tff(c_99, plain, ('#skF_2'!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_91, c_42])).
% 2.61/1.40  tff(c_34, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.61/1.40  tff(c_97, plain, (k1_relat_1('#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_91, c_91, c_34])).
% 2.61/1.40  tff(c_44, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.61/1.40  tff(c_16, plain, (![A_5]: (k2_zfmisc_1(A_5, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.61/1.40  tff(c_95, plain, (![A_5]: (k2_zfmisc_1(A_5, '#skF_1')='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_91, c_91, c_16])).
% 2.61/1.40  tff(c_38, plain, (k9_relat_1('#skF_3', '#skF_2')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.61/1.40  tff(c_94, plain, (k9_relat_1('#skF_3', '#skF_2')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_91, c_38])).
% 2.61/1.40  tff(c_24, plain, (![B_11, A_10]: (k2_relat_1(k7_relat_1(B_11, A_10))=k9_relat_1(B_11, A_10) | ~v1_relat_1(B_11))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.61/1.40  tff(c_22, plain, (![A_8, B_9]: (v1_relat_1(k7_relat_1(A_8, B_9)) | ~v1_relat_1(A_8))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.61/1.40  tff(c_40, plain, (r1_tarski('#skF_2', k1_relat_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.61/1.40  tff(c_211, plain, (![B_38, A_39]: (k1_relat_1(k7_relat_1(B_38, A_39))=A_39 | ~r1_tarski(A_39, k1_relat_1(B_38)) | ~v1_relat_1(B_38))), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.61/1.40  tff(c_221, plain, (k1_relat_1(k7_relat_1('#skF_3', '#skF_2'))='#skF_2' | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_40, c_211])).
% 2.61/1.40  tff(c_231, plain, (k1_relat_1(k7_relat_1('#skF_3', '#skF_2'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_44, c_221])).
% 2.61/1.40  tff(c_26, plain, (![A_12]: (r1_tarski(A_12, k2_zfmisc_1(k1_relat_1(A_12), k2_relat_1(A_12))) | ~v1_relat_1(A_12))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.61/1.40  tff(c_239, plain, (r1_tarski(k7_relat_1('#skF_3', '#skF_2'), k2_zfmisc_1('#skF_2', k2_relat_1(k7_relat_1('#skF_3', '#skF_2')))) | ~v1_relat_1(k7_relat_1('#skF_3', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_231, c_26])).
% 2.61/1.40  tff(c_413, plain, (~v1_relat_1(k7_relat_1('#skF_3', '#skF_2'))), inference(splitLeft, [status(thm)], [c_239])).
% 2.61/1.40  tff(c_416, plain, (~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_22, c_413])).
% 2.61/1.40  tff(c_420, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_44, c_416])).
% 2.61/1.40  tff(c_421, plain, (r1_tarski(k7_relat_1('#skF_3', '#skF_2'), k2_zfmisc_1('#skF_2', k2_relat_1(k7_relat_1('#skF_3', '#skF_2'))))), inference(splitRight, [status(thm)], [c_239])).
% 2.61/1.40  tff(c_607, plain, (r1_tarski(k7_relat_1('#skF_3', '#skF_2'), k2_zfmisc_1('#skF_2', k9_relat_1('#skF_3', '#skF_2'))) | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_24, c_421])).
% 2.61/1.40  tff(c_610, plain, (r1_tarski(k7_relat_1('#skF_3', '#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_95, c_94, c_607])).
% 2.61/1.40  tff(c_12, plain, (![A_4]: (r1_tarski(k1_xboole_0, A_4))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.61/1.40  tff(c_98, plain, (![A_4]: (r1_tarski('#skF_1', A_4))), inference(demodulation, [status(thm), theory('equality')], [c_91, c_12])).
% 2.61/1.40  tff(c_158, plain, (![B_32, A_33]: (B_32=A_33 | ~r1_tarski(B_32, A_33) | ~r1_tarski(A_33, B_32))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.61/1.40  tff(c_165, plain, (![A_4]: (A_4='#skF_1' | ~r1_tarski(A_4, '#skF_1'))), inference(resolution, [status(thm)], [c_98, c_158])).
% 2.61/1.40  tff(c_675, plain, (k7_relat_1('#skF_3', '#skF_2')='#skF_1'), inference(resolution, [status(thm)], [c_610, c_165])).
% 2.61/1.40  tff(c_683, plain, (k1_relat_1('#skF_1')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_675, c_231])).
% 2.61/1.40  tff(c_687, plain, ('#skF_2'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_97, c_683])).
% 2.61/1.40  tff(c_689, plain, $false, inference(negUnitSimplification, [status(thm)], [c_99, c_687])).
% 2.61/1.40  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.61/1.40  
% 2.61/1.40  Inference rules
% 2.61/1.40  ----------------------
% 2.61/1.40  #Ref     : 0
% 2.61/1.40  #Sup     : 148
% 2.61/1.40  #Fact    : 0
% 2.61/1.40  #Define  : 0
% 2.61/1.40  #Split   : 3
% 2.61/1.40  #Chain   : 0
% 2.61/1.40  #Close   : 0
% 2.61/1.40  
% 2.61/1.40  Ordering : KBO
% 2.61/1.40  
% 2.61/1.40  Simplification rules
% 2.61/1.40  ----------------------
% 2.61/1.40  #Subsume      : 2
% 2.61/1.40  #Demod        : 126
% 2.61/1.40  #Tautology    : 85
% 2.61/1.40  #SimpNegUnit  : 1
% 2.61/1.40  #BackRed      : 16
% 2.61/1.40  
% 2.61/1.40  #Partial instantiations: 0
% 2.61/1.40  #Strategies tried      : 1
% 2.61/1.40  
% 2.61/1.40  Timing (in seconds)
% 2.61/1.40  ----------------------
% 2.61/1.40  Preprocessing        : 0.30
% 2.61/1.40  Parsing              : 0.17
% 2.61/1.40  CNF conversion       : 0.02
% 2.61/1.40  Main loop            : 0.31
% 2.61/1.40  Inferencing          : 0.10
% 2.61/1.40  Reduction            : 0.10
% 2.61/1.40  Demodulation         : 0.08
% 2.61/1.40  BG Simplification    : 0.02
% 2.61/1.40  Subsumption          : 0.06
% 2.61/1.40  Abstraction          : 0.01
% 2.61/1.40  MUC search           : 0.00
% 2.61/1.40  Cooper               : 0.00
% 2.61/1.40  Total                : 0.64
% 2.61/1.40  Index Insertion      : 0.00
% 2.61/1.40  Index Deletion       : 0.00
% 2.61/1.40  Index Matching       : 0.00
% 2.61/1.40  BG Taut test         : 0.00
%------------------------------------------------------------------------------
