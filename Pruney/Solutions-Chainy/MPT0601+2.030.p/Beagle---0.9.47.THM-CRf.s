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
% DateTime   : Thu Dec  3 10:02:18 EST 2020

% Result     : Theorem 2.75s
% Output     : CNFRefutation 2.88s
% Verified   : 
% Statistics : Number of formulae       :   54 (  76 expanded)
%              Number of leaves         :   23 (  35 expanded)
%              Depth                    :    8
%              Number of atoms          :   75 ( 122 expanded)
%              Number of equality atoms :   30 (  47 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > v1_relat_1 > k9_relat_1 > k4_xboole_0 > k2_tarski > k11_relat_1 > #nlpp > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k11_relat_1,type,(
    k11_relat_1: ( $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_69,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ( r2_hidden(A,k1_relat_1(B))
        <=> k11_relat_1(B,A) != k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t205_relat_1)).

tff(f_42,axiom,(
    ! [A,B] :
      ( ~ r2_hidden(A,B)
     => r1_xboole_0(k1_tarski(A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l27_zfmisc_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_61,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( k9_relat_1(B,A) = k1_xboole_0
      <=> r1_xboole_0(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t151_relat_1)).

tff(f_55,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] : k11_relat_1(A,B) = k9_relat_1(A,k1_tarski(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d16_relat_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_37,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_50,axiom,(
    ! [A,B,C] :
      ( k4_xboole_0(k2_tarski(A,B),C) = k2_tarski(A,B)
    <=> ( ~ r2_hidden(A,C)
        & ~ r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_zfmisc_1)).

tff(c_26,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_34,plain,
    ( r2_hidden('#skF_1',k1_relat_1('#skF_2'))
    | k11_relat_1('#skF_2','#skF_1') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_102,plain,(
    k11_relat_1('#skF_2','#skF_1') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_34])).

tff(c_54,plain,(
    ! [A_25,B_26] :
      ( r1_xboole_0(k1_tarski(A_25),B_26)
      | r2_hidden(A_25,B_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( r1_xboole_0(B_2,A_1)
      | ~ r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_57,plain,(
    ! [B_26,A_25] :
      ( r1_xboole_0(B_26,k1_tarski(A_25))
      | r2_hidden(A_25,B_26) ) ),
    inference(resolution,[status(thm)],[c_54,c_2])).

tff(c_207,plain,(
    ! [B_45,A_46] :
      ( k9_relat_1(B_45,A_46) = k1_xboole_0
      | ~ r1_xboole_0(k1_relat_1(B_45),A_46)
      | ~ v1_relat_1(B_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_575,plain,(
    ! [B_90,A_91] :
      ( k9_relat_1(B_90,k1_tarski(A_91)) = k1_xboole_0
      | ~ v1_relat_1(B_90)
      | r2_hidden(A_91,k1_relat_1(B_90)) ) ),
    inference(resolution,[status(thm)],[c_57,c_207])).

tff(c_28,plain,
    ( k11_relat_1('#skF_2','#skF_1') = k1_xboole_0
    | ~ r2_hidden('#skF_1',k1_relat_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_119,plain,(
    ~ r2_hidden('#skF_1',k1_relat_1('#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_102,c_28])).

tff(c_578,plain,
    ( k9_relat_1('#skF_2',k1_tarski('#skF_1')) = k1_xboole_0
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_575,c_119])).

tff(c_581,plain,(
    k9_relat_1('#skF_2',k1_tarski('#skF_1')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_578])).

tff(c_20,plain,(
    ! [A_13,B_15] :
      ( k9_relat_1(A_13,k1_tarski(B_15)) = k11_relat_1(A_13,B_15)
      | ~ v1_relat_1(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_585,plain,
    ( k11_relat_1('#skF_2','#skF_1') = k1_xboole_0
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_581,c_20])).

tff(c_592,plain,(
    k11_relat_1('#skF_2','#skF_1') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_585])).

tff(c_594,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_102,c_592])).

tff(c_596,plain,(
    k11_relat_1('#skF_2','#skF_1') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_34])).

tff(c_595,plain,(
    r2_hidden('#skF_1',k1_relat_1('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_34])).

tff(c_790,plain,(
    ! [B_110,A_111] :
      ( r1_xboole_0(k1_relat_1(B_110),A_111)
      | k9_relat_1(B_110,A_111) != k1_xboole_0
      | ~ v1_relat_1(B_110) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_802,plain,(
    ! [A_112,B_113] :
      ( r1_xboole_0(A_112,k1_relat_1(B_113))
      | k9_relat_1(B_113,A_112) != k1_xboole_0
      | ~ v1_relat_1(B_113) ) ),
    inference(resolution,[status(thm)],[c_790,c_2])).

tff(c_6,plain,(
    ! [A_5,B_6] :
      ( k4_xboole_0(A_5,B_6) = A_5
      | ~ r1_xboole_0(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_1001,plain,(
    ! [A_147,B_148] :
      ( k4_xboole_0(A_147,k1_relat_1(B_148)) = A_147
      | k9_relat_1(B_148,A_147) != k1_xboole_0
      | ~ v1_relat_1(B_148) ) ),
    inference(resolution,[status(thm)],[c_802,c_6])).

tff(c_10,plain,(
    ! [A_7] : k2_tarski(A_7,A_7) = k1_tarski(A_7) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_815,plain,(
    ! [A_114,C_115,B_116] :
      ( ~ r2_hidden(A_114,C_115)
      | k4_xboole_0(k2_tarski(A_114,B_116),C_115) != k2_tarski(A_114,B_116) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_826,plain,(
    ! [A_7,C_115] :
      ( ~ r2_hidden(A_7,C_115)
      | k4_xboole_0(k1_tarski(A_7),C_115) != k2_tarski(A_7,A_7) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_815])).

tff(c_829,plain,(
    ! [A_7,C_115] :
      ( ~ r2_hidden(A_7,C_115)
      | k4_xboole_0(k1_tarski(A_7),C_115) != k1_tarski(A_7) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_826])).

tff(c_1095,plain,(
    ! [A_153,B_154] :
      ( ~ r2_hidden(A_153,k1_relat_1(B_154))
      | k9_relat_1(B_154,k1_tarski(A_153)) != k1_xboole_0
      | ~ v1_relat_1(B_154) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1001,c_829])).

tff(c_1101,plain,
    ( k9_relat_1('#skF_2',k1_tarski('#skF_1')) != k1_xboole_0
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_595,c_1095])).

tff(c_1105,plain,(
    k9_relat_1('#skF_2',k1_tarski('#skF_1')) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_1101])).

tff(c_1108,plain,
    ( k11_relat_1('#skF_2','#skF_1') != k1_xboole_0
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_1105])).

tff(c_1111,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_596,c_1108])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n010.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 13:39:29 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.75/1.40  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.75/1.40  
% 2.75/1.40  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.75/1.40  %$ r2_hidden > r1_xboole_0 > v1_relat_1 > k9_relat_1 > k4_xboole_0 > k2_tarski > k11_relat_1 > #nlpp > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1
% 2.75/1.40  
% 2.75/1.40  %Foreground sorts:
% 2.75/1.40  
% 2.75/1.40  
% 2.75/1.40  %Background operators:
% 2.75/1.40  
% 2.75/1.40  
% 2.75/1.40  %Foreground operators:
% 2.75/1.40  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.75/1.40  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.75/1.40  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.75/1.40  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.75/1.40  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.75/1.40  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.75/1.40  tff(k11_relat_1, type, k11_relat_1: ($i * $i) > $i).
% 2.75/1.40  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.75/1.40  tff('#skF_2', type, '#skF_2': $i).
% 2.75/1.40  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.75/1.40  tff('#skF_1', type, '#skF_1': $i).
% 2.75/1.40  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.75/1.40  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.75/1.40  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.75/1.40  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.75/1.40  
% 2.88/1.41  tff(f_69, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => (r2_hidden(A, k1_relat_1(B)) <=> ~(k11_relat_1(B, A) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t205_relat_1)).
% 2.88/1.41  tff(f_42, axiom, (![A, B]: (~r2_hidden(A, B) => r1_xboole_0(k1_tarski(A), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 2.88/1.41  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 2.88/1.41  tff(f_61, axiom, (![A, B]: (v1_relat_1(B) => ((k9_relat_1(B, A) = k1_xboole_0) <=> r1_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t151_relat_1)).
% 2.88/1.41  tff(f_55, axiom, (![A]: (v1_relat_1(A) => (![B]: (k11_relat_1(A, B) = k9_relat_1(A, k1_tarski(B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d16_relat_1)).
% 2.88/1.41  tff(f_35, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 2.88/1.41  tff(f_37, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 2.88/1.41  tff(f_50, axiom, (![A, B, C]: ((k4_xboole_0(k2_tarski(A, B), C) = k2_tarski(A, B)) <=> (~r2_hidden(A, C) & ~r2_hidden(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_zfmisc_1)).
% 2.88/1.41  tff(c_26, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.88/1.41  tff(c_34, plain, (r2_hidden('#skF_1', k1_relat_1('#skF_2')) | k11_relat_1('#skF_2', '#skF_1')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.88/1.41  tff(c_102, plain, (k11_relat_1('#skF_2', '#skF_1')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_34])).
% 2.88/1.41  tff(c_54, plain, (![A_25, B_26]: (r1_xboole_0(k1_tarski(A_25), B_26) | r2_hidden(A_25, B_26))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.88/1.41  tff(c_2, plain, (![B_2, A_1]: (r1_xboole_0(B_2, A_1) | ~r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.88/1.41  tff(c_57, plain, (![B_26, A_25]: (r1_xboole_0(B_26, k1_tarski(A_25)) | r2_hidden(A_25, B_26))), inference(resolution, [status(thm)], [c_54, c_2])).
% 2.88/1.41  tff(c_207, plain, (![B_45, A_46]: (k9_relat_1(B_45, A_46)=k1_xboole_0 | ~r1_xboole_0(k1_relat_1(B_45), A_46) | ~v1_relat_1(B_45))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.88/1.41  tff(c_575, plain, (![B_90, A_91]: (k9_relat_1(B_90, k1_tarski(A_91))=k1_xboole_0 | ~v1_relat_1(B_90) | r2_hidden(A_91, k1_relat_1(B_90)))), inference(resolution, [status(thm)], [c_57, c_207])).
% 2.88/1.41  tff(c_28, plain, (k11_relat_1('#skF_2', '#skF_1')=k1_xboole_0 | ~r2_hidden('#skF_1', k1_relat_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.88/1.41  tff(c_119, plain, (~r2_hidden('#skF_1', k1_relat_1('#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_102, c_28])).
% 2.88/1.41  tff(c_578, plain, (k9_relat_1('#skF_2', k1_tarski('#skF_1'))=k1_xboole_0 | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_575, c_119])).
% 2.88/1.41  tff(c_581, plain, (k9_relat_1('#skF_2', k1_tarski('#skF_1'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_26, c_578])).
% 2.88/1.41  tff(c_20, plain, (![A_13, B_15]: (k9_relat_1(A_13, k1_tarski(B_15))=k11_relat_1(A_13, B_15) | ~v1_relat_1(A_13))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.88/1.41  tff(c_585, plain, (k11_relat_1('#skF_2', '#skF_1')=k1_xboole_0 | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_581, c_20])).
% 2.88/1.41  tff(c_592, plain, (k11_relat_1('#skF_2', '#skF_1')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_26, c_585])).
% 2.88/1.41  tff(c_594, plain, $false, inference(negUnitSimplification, [status(thm)], [c_102, c_592])).
% 2.88/1.41  tff(c_596, plain, (k11_relat_1('#skF_2', '#skF_1')=k1_xboole_0), inference(splitRight, [status(thm)], [c_34])).
% 2.88/1.41  tff(c_595, plain, (r2_hidden('#skF_1', k1_relat_1('#skF_2'))), inference(splitRight, [status(thm)], [c_34])).
% 2.88/1.41  tff(c_790, plain, (![B_110, A_111]: (r1_xboole_0(k1_relat_1(B_110), A_111) | k9_relat_1(B_110, A_111)!=k1_xboole_0 | ~v1_relat_1(B_110))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.88/1.41  tff(c_802, plain, (![A_112, B_113]: (r1_xboole_0(A_112, k1_relat_1(B_113)) | k9_relat_1(B_113, A_112)!=k1_xboole_0 | ~v1_relat_1(B_113))), inference(resolution, [status(thm)], [c_790, c_2])).
% 2.88/1.41  tff(c_6, plain, (![A_5, B_6]: (k4_xboole_0(A_5, B_6)=A_5 | ~r1_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.88/1.41  tff(c_1001, plain, (![A_147, B_148]: (k4_xboole_0(A_147, k1_relat_1(B_148))=A_147 | k9_relat_1(B_148, A_147)!=k1_xboole_0 | ~v1_relat_1(B_148))), inference(resolution, [status(thm)], [c_802, c_6])).
% 2.88/1.41  tff(c_10, plain, (![A_7]: (k2_tarski(A_7, A_7)=k1_tarski(A_7))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.88/1.41  tff(c_815, plain, (![A_114, C_115, B_116]: (~r2_hidden(A_114, C_115) | k4_xboole_0(k2_tarski(A_114, B_116), C_115)!=k2_tarski(A_114, B_116))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.88/1.41  tff(c_826, plain, (![A_7, C_115]: (~r2_hidden(A_7, C_115) | k4_xboole_0(k1_tarski(A_7), C_115)!=k2_tarski(A_7, A_7))), inference(superposition, [status(thm), theory('equality')], [c_10, c_815])).
% 2.88/1.41  tff(c_829, plain, (![A_7, C_115]: (~r2_hidden(A_7, C_115) | k4_xboole_0(k1_tarski(A_7), C_115)!=k1_tarski(A_7))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_826])).
% 2.88/1.41  tff(c_1095, plain, (![A_153, B_154]: (~r2_hidden(A_153, k1_relat_1(B_154)) | k9_relat_1(B_154, k1_tarski(A_153))!=k1_xboole_0 | ~v1_relat_1(B_154))), inference(superposition, [status(thm), theory('equality')], [c_1001, c_829])).
% 2.88/1.41  tff(c_1101, plain, (k9_relat_1('#skF_2', k1_tarski('#skF_1'))!=k1_xboole_0 | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_595, c_1095])).
% 2.88/1.41  tff(c_1105, plain, (k9_relat_1('#skF_2', k1_tarski('#skF_1'))!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_26, c_1101])).
% 2.88/1.41  tff(c_1108, plain, (k11_relat_1('#skF_2', '#skF_1')!=k1_xboole_0 | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_20, c_1105])).
% 2.88/1.41  tff(c_1111, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_26, c_596, c_1108])).
% 2.88/1.41  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.88/1.41  
% 2.88/1.41  Inference rules
% 2.88/1.41  ----------------------
% 2.88/1.41  #Ref     : 0
% 2.88/1.41  #Sup     : 250
% 2.88/1.41  #Fact    : 0
% 2.88/1.41  #Define  : 0
% 2.88/1.41  #Split   : 1
% 2.88/1.41  #Chain   : 0
% 2.88/1.41  #Close   : 0
% 2.88/1.41  
% 2.88/1.41  Ordering : KBO
% 2.88/1.41  
% 2.88/1.41  Simplification rules
% 2.88/1.41  ----------------------
% 2.88/1.41  #Subsume      : 59
% 2.88/1.41  #Demod        : 42
% 2.88/1.41  #Tautology    : 116
% 2.88/1.41  #SimpNegUnit  : 6
% 2.88/1.41  #BackRed      : 0
% 2.88/1.41  
% 2.88/1.41  #Partial instantiations: 0
% 2.88/1.41  #Strategies tried      : 1
% 2.88/1.41  
% 2.88/1.41  Timing (in seconds)
% 2.88/1.41  ----------------------
% 2.88/1.42  Preprocessing        : 0.29
% 2.88/1.42  Parsing              : 0.16
% 2.88/1.42  CNF conversion       : 0.02
% 2.88/1.42  Main loop            : 0.35
% 2.88/1.42  Inferencing          : 0.15
% 2.88/1.42  Reduction            : 0.09
% 2.88/1.42  Demodulation         : 0.06
% 2.88/1.42  BG Simplification    : 0.02
% 2.88/1.42  Subsumption          : 0.06
% 2.88/1.42  Abstraction          : 0.02
% 2.88/1.42  MUC search           : 0.00
% 2.88/1.42  Cooper               : 0.00
% 2.88/1.42  Total                : 0.67
% 2.88/1.42  Index Insertion      : 0.00
% 2.88/1.42  Index Deletion       : 0.00
% 2.88/1.42  Index Matching       : 0.00
% 2.88/1.42  BG Taut test         : 0.00
%------------------------------------------------------------------------------
