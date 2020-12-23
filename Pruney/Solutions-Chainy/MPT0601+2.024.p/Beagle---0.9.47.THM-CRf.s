%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:02:17 EST 2020

% Result     : Theorem 1.97s
% Output     : CNFRefutation 2.10s
% Verified   : 
% Statistics : Number of formulae       :   60 (  79 expanded)
%              Number of leaves         :   29 (  39 expanded)
%              Depth                    :   10
%              Number of atoms          :   76 ( 118 expanded)
%              Number of equality atoms :   36 (  51 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > v1_relat_1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k2_xboole_0 > k2_tarski > k11_relat_1 > #nlpp > k2_relat_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k11_relat_1,type,(
    k11_relat_1: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_80,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ( r2_hidden(A,k1_relat_1(B))
        <=> k11_relat_1(B,A) != k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t205_relat_1)).

tff(f_72,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_40,axiom,(
    ! [A,B] :
      ( ~ r2_hidden(A,B)
     => r1_xboole_0(k1_tarski(A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l27_zfmisc_1)).

tff(f_69,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( r1_xboole_0(B,k1_relat_1(A))
         => k7_relat_1(A,B) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t187_relat_1)).

tff(f_52,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_48,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] : k11_relat_1(A,B) = k9_relat_1(A,k1_tarski(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d16_relat_1)).

tff(f_27,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

tff(f_43,axiom,(
    ! [A,B] : k2_xboole_0(k1_tarski(A),B) != k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_zfmisc_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_62,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ~ ( A != k1_xboole_0
          & r1_tarski(A,k1_relat_1(B))
          & k9_relat_1(B,A) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_relat_1)).

tff(c_28,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_36,plain,
    ( r2_hidden('#skF_1',k1_relat_1('#skF_2'))
    | k11_relat_1('#skF_2','#skF_1') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_79,plain,(
    k11_relat_1('#skF_2','#skF_1') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_36])).

tff(c_24,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_12,plain,(
    ! [A_7,B_8] :
      ( r1_xboole_0(k1_tarski(A_7),B_8)
      | r2_hidden(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_105,plain,(
    ! [A_38,B_39] :
      ( k7_relat_1(A_38,B_39) = k1_xboole_0
      | ~ r1_xboole_0(B_39,k1_relat_1(A_38))
      | ~ v1_relat_1(A_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_126,plain,(
    ! [A_42,A_43] :
      ( k7_relat_1(A_42,k1_tarski(A_43)) = k1_xboole_0
      | ~ v1_relat_1(A_42)
      | r2_hidden(A_43,k1_relat_1(A_42)) ) ),
    inference(resolution,[status(thm)],[c_12,c_105])).

tff(c_30,plain,
    ( k11_relat_1('#skF_2','#skF_1') = k1_xboole_0
    | ~ r2_hidden('#skF_1',k1_relat_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_86,plain,(
    ~ r2_hidden('#skF_1',k1_relat_1('#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_79,c_30])).

tff(c_129,plain,
    ( k7_relat_1('#skF_2',k1_tarski('#skF_1')) = k1_xboole_0
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_126,c_86])).

tff(c_135,plain,(
    k7_relat_1('#skF_2',k1_tarski('#skF_1')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_129])).

tff(c_18,plain,(
    ! [B_15,A_14] :
      ( k2_relat_1(k7_relat_1(B_15,A_14)) = k9_relat_1(B_15,A_14)
      | ~ v1_relat_1(B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_139,plain,
    ( k9_relat_1('#skF_2',k1_tarski('#skF_1')) = k2_relat_1(k1_xboole_0)
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_135,c_18])).

tff(c_143,plain,(
    k9_relat_1('#skF_2',k1_tarski('#skF_1')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_24,c_139])).

tff(c_16,plain,(
    ! [A_11,B_13] :
      ( k9_relat_1(A_11,k1_tarski(B_13)) = k11_relat_1(A_11,B_13)
      | ~ v1_relat_1(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_148,plain,
    ( k11_relat_1('#skF_2','#skF_1') = k1_xboole_0
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_143,c_16])).

tff(c_155,plain,(
    k11_relat_1('#skF_2','#skF_1') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_148])).

tff(c_157,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_79,c_155])).

tff(c_159,plain,(
    k11_relat_1('#skF_2','#skF_1') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_36])).

tff(c_158,plain,(
    r2_hidden('#skF_1',k1_relat_1('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_36])).

tff(c_2,plain,(
    ! [A_1] : k2_xboole_0(A_1,k1_xboole_0) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_54,plain,(
    ! [A_22,B_23] : k2_xboole_0(k1_tarski(A_22),B_23) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_58,plain,(
    ! [A_22] : k1_tarski(A_22) != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_54])).

tff(c_10,plain,(
    ! [A_5,B_6] :
      ( r1_tarski(k1_tarski(A_5),B_6)
      | ~ r2_hidden(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_204,plain,(
    ! [B_56,A_57] :
      ( k9_relat_1(B_56,A_57) != k1_xboole_0
      | ~ r1_tarski(A_57,k1_relat_1(B_56))
      | k1_xboole_0 = A_57
      | ~ v1_relat_1(B_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_208,plain,(
    ! [B_56,A_5] :
      ( k9_relat_1(B_56,k1_tarski(A_5)) != k1_xboole_0
      | k1_tarski(A_5) = k1_xboole_0
      | ~ v1_relat_1(B_56)
      | ~ r2_hidden(A_5,k1_relat_1(B_56)) ) ),
    inference(resolution,[status(thm)],[c_10,c_204])).

tff(c_215,plain,(
    ! [B_58,A_59] :
      ( k9_relat_1(B_58,k1_tarski(A_59)) != k1_xboole_0
      | ~ v1_relat_1(B_58)
      | ~ r2_hidden(A_59,k1_relat_1(B_58)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_208])).

tff(c_221,plain,
    ( k9_relat_1('#skF_2',k1_tarski('#skF_1')) != k1_xboole_0
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_158,c_215])).

tff(c_228,plain,(
    k9_relat_1('#skF_2',k1_tarski('#skF_1')) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_221])).

tff(c_231,plain,
    ( k11_relat_1('#skF_2','#skF_1') != k1_xboole_0
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_228])).

tff(c_234,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_159,c_231])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:32:20 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.97/1.22  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.97/1.23  
% 1.97/1.23  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.97/1.23  %$ r2_hidden > r1_xboole_0 > r1_tarski > v1_relat_1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k2_xboole_0 > k2_tarski > k11_relat_1 > #nlpp > k2_relat_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1
% 1.97/1.23  
% 1.97/1.23  %Foreground sorts:
% 1.97/1.23  
% 1.97/1.23  
% 1.97/1.23  %Background operators:
% 1.97/1.23  
% 1.97/1.23  
% 1.97/1.23  %Foreground operators:
% 1.97/1.23  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.97/1.23  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.97/1.23  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.97/1.23  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 1.97/1.23  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.97/1.23  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.97/1.23  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.97/1.23  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.97/1.23  tff(k11_relat_1, type, k11_relat_1: ($i * $i) > $i).
% 1.97/1.23  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.97/1.23  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.97/1.23  tff('#skF_2', type, '#skF_2': $i).
% 1.97/1.23  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 1.97/1.23  tff('#skF_1', type, '#skF_1': $i).
% 1.97/1.23  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.97/1.23  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.97/1.23  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.97/1.23  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.97/1.23  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.97/1.23  
% 2.10/1.24  tff(f_80, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => (r2_hidden(A, k1_relat_1(B)) <=> ~(k11_relat_1(B, A) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t205_relat_1)).
% 2.10/1.24  tff(f_72, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 2.10/1.24  tff(f_40, axiom, (![A, B]: (~r2_hidden(A, B) => r1_xboole_0(k1_tarski(A), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 2.10/1.24  tff(f_69, axiom, (![A]: (v1_relat_1(A) => (![B]: (r1_xboole_0(B, k1_relat_1(A)) => (k7_relat_1(A, B) = k1_xboole_0))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t187_relat_1)).
% 2.10/1.24  tff(f_52, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_relat_1)).
% 2.10/1.24  tff(f_48, axiom, (![A]: (v1_relat_1(A) => (![B]: (k11_relat_1(A, B) = k9_relat_1(A, k1_tarski(B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d16_relat_1)).
% 2.10/1.24  tff(f_27, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 2.10/1.24  tff(f_43, axiom, (![A, B]: ~(k2_xboole_0(k1_tarski(A), B) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_zfmisc_1)).
% 2.10/1.24  tff(f_35, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 2.10/1.24  tff(f_62, axiom, (![A, B]: (v1_relat_1(B) => ~((~(A = k1_xboole_0) & r1_tarski(A, k1_relat_1(B))) & (k9_relat_1(B, A) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t152_relat_1)).
% 2.10/1.24  tff(c_28, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.10/1.24  tff(c_36, plain, (r2_hidden('#skF_1', k1_relat_1('#skF_2')) | k11_relat_1('#skF_2', '#skF_1')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.10/1.24  tff(c_79, plain, (k11_relat_1('#skF_2', '#skF_1')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_36])).
% 2.10/1.24  tff(c_24, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.10/1.24  tff(c_12, plain, (![A_7, B_8]: (r1_xboole_0(k1_tarski(A_7), B_8) | r2_hidden(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.10/1.24  tff(c_105, plain, (![A_38, B_39]: (k7_relat_1(A_38, B_39)=k1_xboole_0 | ~r1_xboole_0(B_39, k1_relat_1(A_38)) | ~v1_relat_1(A_38))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.10/1.24  tff(c_126, plain, (![A_42, A_43]: (k7_relat_1(A_42, k1_tarski(A_43))=k1_xboole_0 | ~v1_relat_1(A_42) | r2_hidden(A_43, k1_relat_1(A_42)))), inference(resolution, [status(thm)], [c_12, c_105])).
% 2.10/1.24  tff(c_30, plain, (k11_relat_1('#skF_2', '#skF_1')=k1_xboole_0 | ~r2_hidden('#skF_1', k1_relat_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.10/1.24  tff(c_86, plain, (~r2_hidden('#skF_1', k1_relat_1('#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_79, c_30])).
% 2.10/1.24  tff(c_129, plain, (k7_relat_1('#skF_2', k1_tarski('#skF_1'))=k1_xboole_0 | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_126, c_86])).
% 2.10/1.24  tff(c_135, plain, (k7_relat_1('#skF_2', k1_tarski('#skF_1'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_28, c_129])).
% 2.10/1.24  tff(c_18, plain, (![B_15, A_14]: (k2_relat_1(k7_relat_1(B_15, A_14))=k9_relat_1(B_15, A_14) | ~v1_relat_1(B_15))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.10/1.24  tff(c_139, plain, (k9_relat_1('#skF_2', k1_tarski('#skF_1'))=k2_relat_1(k1_xboole_0) | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_135, c_18])).
% 2.10/1.24  tff(c_143, plain, (k9_relat_1('#skF_2', k1_tarski('#skF_1'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_28, c_24, c_139])).
% 2.10/1.24  tff(c_16, plain, (![A_11, B_13]: (k9_relat_1(A_11, k1_tarski(B_13))=k11_relat_1(A_11, B_13) | ~v1_relat_1(A_11))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.10/1.24  tff(c_148, plain, (k11_relat_1('#skF_2', '#skF_1')=k1_xboole_0 | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_143, c_16])).
% 2.10/1.24  tff(c_155, plain, (k11_relat_1('#skF_2', '#skF_1')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_28, c_148])).
% 2.10/1.24  tff(c_157, plain, $false, inference(negUnitSimplification, [status(thm)], [c_79, c_155])).
% 2.10/1.24  tff(c_159, plain, (k11_relat_1('#skF_2', '#skF_1')=k1_xboole_0), inference(splitRight, [status(thm)], [c_36])).
% 2.10/1.24  tff(c_158, plain, (r2_hidden('#skF_1', k1_relat_1('#skF_2'))), inference(splitRight, [status(thm)], [c_36])).
% 2.10/1.24  tff(c_2, plain, (![A_1]: (k2_xboole_0(A_1, k1_xboole_0)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.10/1.24  tff(c_54, plain, (![A_22, B_23]: (k2_xboole_0(k1_tarski(A_22), B_23)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.10/1.24  tff(c_58, plain, (![A_22]: (k1_tarski(A_22)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2, c_54])).
% 2.10/1.24  tff(c_10, plain, (![A_5, B_6]: (r1_tarski(k1_tarski(A_5), B_6) | ~r2_hidden(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.10/1.24  tff(c_204, plain, (![B_56, A_57]: (k9_relat_1(B_56, A_57)!=k1_xboole_0 | ~r1_tarski(A_57, k1_relat_1(B_56)) | k1_xboole_0=A_57 | ~v1_relat_1(B_56))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.10/1.24  tff(c_208, plain, (![B_56, A_5]: (k9_relat_1(B_56, k1_tarski(A_5))!=k1_xboole_0 | k1_tarski(A_5)=k1_xboole_0 | ~v1_relat_1(B_56) | ~r2_hidden(A_5, k1_relat_1(B_56)))), inference(resolution, [status(thm)], [c_10, c_204])).
% 2.10/1.24  tff(c_215, plain, (![B_58, A_59]: (k9_relat_1(B_58, k1_tarski(A_59))!=k1_xboole_0 | ~v1_relat_1(B_58) | ~r2_hidden(A_59, k1_relat_1(B_58)))), inference(negUnitSimplification, [status(thm)], [c_58, c_208])).
% 2.10/1.24  tff(c_221, plain, (k9_relat_1('#skF_2', k1_tarski('#skF_1'))!=k1_xboole_0 | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_158, c_215])).
% 2.10/1.24  tff(c_228, plain, (k9_relat_1('#skF_2', k1_tarski('#skF_1'))!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_28, c_221])).
% 2.10/1.24  tff(c_231, plain, (k11_relat_1('#skF_2', '#skF_1')!=k1_xboole_0 | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_16, c_228])).
% 2.10/1.24  tff(c_234, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_28, c_159, c_231])).
% 2.10/1.24  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.10/1.24  
% 2.10/1.24  Inference rules
% 2.10/1.24  ----------------------
% 2.10/1.24  #Ref     : 0
% 2.10/1.24  #Sup     : 45
% 2.10/1.24  #Fact    : 0
% 2.10/1.24  #Define  : 0
% 2.10/1.24  #Split   : 3
% 2.10/1.24  #Chain   : 0
% 2.10/1.24  #Close   : 0
% 2.10/1.24  
% 2.10/1.24  Ordering : KBO
% 2.10/1.24  
% 2.10/1.24  Simplification rules
% 2.10/1.24  ----------------------
% 2.10/1.24  #Subsume      : 5
% 2.10/1.24  #Demod        : 9
% 2.10/1.24  #Tautology    : 28
% 2.10/1.24  #SimpNegUnit  : 4
% 2.10/1.24  #BackRed      : 0
% 2.10/1.24  
% 2.10/1.24  #Partial instantiations: 0
% 2.10/1.24  #Strategies tried      : 1
% 2.10/1.24  
% 2.10/1.24  Timing (in seconds)
% 2.10/1.24  ----------------------
% 2.10/1.25  Preprocessing        : 0.31
% 2.10/1.25  Parsing              : 0.17
% 2.10/1.25  CNF conversion       : 0.02
% 2.10/1.25  Main loop            : 0.17
% 2.10/1.25  Inferencing          : 0.07
% 2.10/1.25  Reduction            : 0.05
% 2.10/1.25  Demodulation         : 0.03
% 2.10/1.25  BG Simplification    : 0.01
% 2.10/1.25  Subsumption          : 0.03
% 2.10/1.25  Abstraction          : 0.01
% 2.10/1.25  MUC search           : 0.00
% 2.10/1.25  Cooper               : 0.00
% 2.10/1.25  Total                : 0.50
% 2.10/1.25  Index Insertion      : 0.00
% 2.10/1.25  Index Deletion       : 0.00
% 2.10/1.25  Index Matching       : 0.00
% 2.10/1.25  BG Taut test         : 0.00
%------------------------------------------------------------------------------
