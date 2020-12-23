%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:05:34 EST 2020

% Result     : Theorem 2.02s
% Output     : CNFRefutation 2.02s
% Verified   : 
% Statistics : Number of formulae       :   51 ( 100 expanded)
%              Number of leaves         :   28 (  50 expanded)
%              Depth                    :    8
%              Number of atoms          :   62 ( 181 expanded)
%              Number of equality atoms :   18 (  48 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > v1_relat_1 > v1_funct_1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k2_tarski > k1_funct_1 > k11_relat_1 > #nlpp > k2_relat_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

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

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_74,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_relat_1(B)
          & v1_funct_1(B) )
       => r1_tarski(k2_relat_1(k7_relat_1(B,k1_tarski(A))),k1_tarski(k1_funct_1(B,A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t167_funct_1)).

tff(f_40,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k1_tarski(B))
    <=> ( A = k1_xboole_0
        | A = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_zfmisc_1)).

tff(f_59,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_34,axiom,(
    ! [A,B] :
      ( ~ r2_hidden(A,B)
     => r1_xboole_0(k1_tarski(A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l27_zfmisc_1)).

tff(f_56,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( r1_xboole_0(B,k1_relat_1(A))
         => k7_relat_1(A,B) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t187_relat_1)).

tff(f_67,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r2_hidden(A,k1_relat_1(B))
       => k11_relat_1(B,A) = k1_tarski(k1_funct_1(B,A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t117_funct_1)).

tff(f_45,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] : k11_relat_1(A,B) = k9_relat_1(A,k1_tarski(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d16_relat_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

tff(c_30,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_28,plain,(
    v1_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_12,plain,(
    ! [B_7] : r1_tarski(k1_xboole_0,k1_tarski(B_7)) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_20,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_6,plain,(
    ! [A_4,B_5] :
      ( r1_xboole_0(k1_tarski(A_4),B_5)
      | r2_hidden(A_4,B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_99,plain,(
    ! [A_31,B_32] :
      ( k7_relat_1(A_31,B_32) = k1_xboole_0
      | ~ r1_xboole_0(B_32,k1_relat_1(A_31))
      | ~ v1_relat_1(A_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_107,plain,(
    ! [A_31,A_4] :
      ( k7_relat_1(A_31,k1_tarski(A_4)) = k1_xboole_0
      | ~ v1_relat_1(A_31)
      | r2_hidden(A_4,k1_relat_1(A_31)) ) ),
    inference(resolution,[status(thm)],[c_6,c_99])).

tff(c_113,plain,(
    ! [B_35,A_36] :
      ( k1_tarski(k1_funct_1(B_35,A_36)) = k11_relat_1(B_35,A_36)
      | ~ r2_hidden(A_36,k1_relat_1(B_35))
      | ~ v1_funct_1(B_35)
      | ~ v1_relat_1(B_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_121,plain,(
    ! [A_37,A_38] :
      ( k1_tarski(k1_funct_1(A_37,A_38)) = k11_relat_1(A_37,A_38)
      | ~ v1_funct_1(A_37)
      | k7_relat_1(A_37,k1_tarski(A_38)) = k1_xboole_0
      | ~ v1_relat_1(A_37) ) ),
    inference(resolution,[status(thm)],[c_107,c_113])).

tff(c_26,plain,(
    ~ r1_tarski(k2_relat_1(k7_relat_1('#skF_2',k1_tarski('#skF_1'))),k1_tarski(k1_funct_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_130,plain,
    ( ~ r1_tarski(k2_relat_1(k1_xboole_0),k1_tarski(k1_funct_1('#skF_2','#skF_1')))
    | k1_tarski(k1_funct_1('#skF_2','#skF_1')) = k11_relat_1('#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_121,c_26])).

tff(c_137,plain,(
    k1_tarski(k1_funct_1('#skF_2','#skF_1')) = k11_relat_1('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_12,c_20,c_130])).

tff(c_14,plain,(
    ! [A_8,B_10] :
      ( k9_relat_1(A_8,k1_tarski(B_10)) = k11_relat_1(A_8,B_10)
      | ~ v1_relat_1(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_69,plain,(
    ! [B_27,A_28] :
      ( k2_relat_1(k7_relat_1(B_27,A_28)) = k9_relat_1(B_27,A_28)
      | ~ v1_relat_1(B_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_75,plain,
    ( ~ r1_tarski(k9_relat_1('#skF_2',k1_tarski('#skF_1')),k1_tarski(k1_funct_1('#skF_2','#skF_1')))
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_69,c_26])).

tff(c_81,plain,(
    ~ r1_tarski(k9_relat_1('#skF_2',k1_tarski('#skF_1')),k1_tarski(k1_funct_1('#skF_2','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_75])).

tff(c_96,plain,
    ( ~ r1_tarski(k11_relat_1('#skF_2','#skF_1'),k1_tarski(k1_funct_1('#skF_2','#skF_1')))
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_81])).

tff(c_98,plain,(
    ~ r1_tarski(k11_relat_1('#skF_2','#skF_1'),k1_tarski(k1_funct_1('#skF_2','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_96])).

tff(c_139,plain,(
    ~ r1_tarski(k11_relat_1('#skF_2','#skF_1'),k11_relat_1('#skF_2','#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_137,c_98])).

tff(c_10,plain,(
    ! [B_7] : r1_tarski(k1_tarski(B_7),k1_tarski(B_7)) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_160,plain,(
    r1_tarski(k1_tarski(k1_funct_1('#skF_2','#skF_1')),k11_relat_1('#skF_2','#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_137,c_10])).

tff(c_167,plain,(
    r1_tarski(k11_relat_1('#skF_2','#skF_1'),k11_relat_1('#skF_2','#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_137,c_160])).

tff(c_169,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_139,c_167])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 21:07:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.02/1.33  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.02/1.33  
% 2.02/1.33  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.02/1.33  %$ r2_hidden > r1_xboole_0 > r1_tarski > v1_relat_1 > v1_funct_1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k2_tarski > k1_funct_1 > k11_relat_1 > #nlpp > k2_relat_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1
% 2.02/1.33  
% 2.02/1.33  %Foreground sorts:
% 2.02/1.33  
% 2.02/1.33  
% 2.02/1.33  %Background operators:
% 2.02/1.33  
% 2.02/1.33  
% 2.02/1.33  %Foreground operators:
% 2.02/1.33  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.02/1.33  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.02/1.33  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.02/1.33  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.02/1.33  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.02/1.33  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.02/1.33  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.02/1.33  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.02/1.33  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.02/1.33  tff(k11_relat_1, type, k11_relat_1: ($i * $i) > $i).
% 2.02/1.33  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.02/1.33  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.02/1.33  tff('#skF_2', type, '#skF_2': $i).
% 2.02/1.33  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.02/1.33  tff('#skF_1', type, '#skF_1': $i).
% 2.02/1.33  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.02/1.33  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.02/1.33  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.02/1.33  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.02/1.33  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.02/1.33  
% 2.02/1.34  tff(f_74, negated_conjecture, ~(![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => r1_tarski(k2_relat_1(k7_relat_1(B, k1_tarski(A))), k1_tarski(k1_funct_1(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t167_funct_1)).
% 2.02/1.34  tff(f_40, axiom, (![A, B]: (r1_tarski(A, k1_tarski(B)) <=> ((A = k1_xboole_0) | (A = k1_tarski(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_zfmisc_1)).
% 2.02/1.34  tff(f_59, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 2.02/1.34  tff(f_34, axiom, (![A, B]: (~r2_hidden(A, B) => r1_xboole_0(k1_tarski(A), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 2.02/1.34  tff(f_56, axiom, (![A]: (v1_relat_1(A) => (![B]: (r1_xboole_0(B, k1_relat_1(A)) => (k7_relat_1(A, B) = k1_xboole_0))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t187_relat_1)).
% 2.02/1.34  tff(f_67, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r2_hidden(A, k1_relat_1(B)) => (k11_relat_1(B, A) = k1_tarski(k1_funct_1(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t117_funct_1)).
% 2.02/1.34  tff(f_45, axiom, (![A]: (v1_relat_1(A) => (![B]: (k11_relat_1(A, B) = k9_relat_1(A, k1_tarski(B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d16_relat_1)).
% 2.02/1.34  tff(f_49, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_relat_1)).
% 2.02/1.34  tff(c_30, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.02/1.34  tff(c_28, plain, (v1_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.02/1.34  tff(c_12, plain, (![B_7]: (r1_tarski(k1_xboole_0, k1_tarski(B_7)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.02/1.34  tff(c_20, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.02/1.34  tff(c_6, plain, (![A_4, B_5]: (r1_xboole_0(k1_tarski(A_4), B_5) | r2_hidden(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.02/1.34  tff(c_99, plain, (![A_31, B_32]: (k7_relat_1(A_31, B_32)=k1_xboole_0 | ~r1_xboole_0(B_32, k1_relat_1(A_31)) | ~v1_relat_1(A_31))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.02/1.34  tff(c_107, plain, (![A_31, A_4]: (k7_relat_1(A_31, k1_tarski(A_4))=k1_xboole_0 | ~v1_relat_1(A_31) | r2_hidden(A_4, k1_relat_1(A_31)))), inference(resolution, [status(thm)], [c_6, c_99])).
% 2.02/1.34  tff(c_113, plain, (![B_35, A_36]: (k1_tarski(k1_funct_1(B_35, A_36))=k11_relat_1(B_35, A_36) | ~r2_hidden(A_36, k1_relat_1(B_35)) | ~v1_funct_1(B_35) | ~v1_relat_1(B_35))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.02/1.34  tff(c_121, plain, (![A_37, A_38]: (k1_tarski(k1_funct_1(A_37, A_38))=k11_relat_1(A_37, A_38) | ~v1_funct_1(A_37) | k7_relat_1(A_37, k1_tarski(A_38))=k1_xboole_0 | ~v1_relat_1(A_37))), inference(resolution, [status(thm)], [c_107, c_113])).
% 2.02/1.34  tff(c_26, plain, (~r1_tarski(k2_relat_1(k7_relat_1('#skF_2', k1_tarski('#skF_1'))), k1_tarski(k1_funct_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.02/1.34  tff(c_130, plain, (~r1_tarski(k2_relat_1(k1_xboole_0), k1_tarski(k1_funct_1('#skF_2', '#skF_1'))) | k1_tarski(k1_funct_1('#skF_2', '#skF_1'))=k11_relat_1('#skF_2', '#skF_1') | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_121, c_26])).
% 2.02/1.34  tff(c_137, plain, (k1_tarski(k1_funct_1('#skF_2', '#skF_1'))=k11_relat_1('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_12, c_20, c_130])).
% 2.02/1.34  tff(c_14, plain, (![A_8, B_10]: (k9_relat_1(A_8, k1_tarski(B_10))=k11_relat_1(A_8, B_10) | ~v1_relat_1(A_8))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.02/1.34  tff(c_69, plain, (![B_27, A_28]: (k2_relat_1(k7_relat_1(B_27, A_28))=k9_relat_1(B_27, A_28) | ~v1_relat_1(B_27))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.02/1.34  tff(c_75, plain, (~r1_tarski(k9_relat_1('#skF_2', k1_tarski('#skF_1')), k1_tarski(k1_funct_1('#skF_2', '#skF_1'))) | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_69, c_26])).
% 2.02/1.34  tff(c_81, plain, (~r1_tarski(k9_relat_1('#skF_2', k1_tarski('#skF_1')), k1_tarski(k1_funct_1('#skF_2', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_75])).
% 2.02/1.34  tff(c_96, plain, (~r1_tarski(k11_relat_1('#skF_2', '#skF_1'), k1_tarski(k1_funct_1('#skF_2', '#skF_1'))) | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_14, c_81])).
% 2.02/1.34  tff(c_98, plain, (~r1_tarski(k11_relat_1('#skF_2', '#skF_1'), k1_tarski(k1_funct_1('#skF_2', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_96])).
% 2.02/1.34  tff(c_139, plain, (~r1_tarski(k11_relat_1('#skF_2', '#skF_1'), k11_relat_1('#skF_2', '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_137, c_98])).
% 2.02/1.34  tff(c_10, plain, (![B_7]: (r1_tarski(k1_tarski(B_7), k1_tarski(B_7)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.02/1.34  tff(c_160, plain, (r1_tarski(k1_tarski(k1_funct_1('#skF_2', '#skF_1')), k11_relat_1('#skF_2', '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_137, c_10])).
% 2.02/1.34  tff(c_167, plain, (r1_tarski(k11_relat_1('#skF_2', '#skF_1'), k11_relat_1('#skF_2', '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_137, c_160])).
% 2.02/1.34  tff(c_169, plain, $false, inference(negUnitSimplification, [status(thm)], [c_139, c_167])).
% 2.02/1.34  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.02/1.34  
% 2.02/1.34  Inference rules
% 2.02/1.34  ----------------------
% 2.02/1.34  #Ref     : 0
% 2.02/1.34  #Sup     : 34
% 2.02/1.35  #Fact    : 0
% 2.02/1.35  #Define  : 0
% 2.02/1.35  #Split   : 1
% 2.02/1.35  #Chain   : 0
% 2.02/1.35  #Close   : 0
% 2.02/1.35  
% 2.02/1.35  Ordering : KBO
% 2.02/1.35  
% 2.02/1.35  Simplification rules
% 2.02/1.35  ----------------------
% 2.02/1.35  #Subsume      : 2
% 2.02/1.35  #Demod        : 13
% 2.02/1.35  #Tautology    : 18
% 2.02/1.35  #SimpNegUnit  : 1
% 2.02/1.35  #BackRed      : 3
% 2.02/1.35  
% 2.02/1.35  #Partial instantiations: 0
% 2.02/1.35  #Strategies tried      : 1
% 2.02/1.35  
% 2.02/1.35  Timing (in seconds)
% 2.02/1.35  ----------------------
% 2.02/1.35  Preprocessing        : 0.32
% 2.02/1.35  Parsing              : 0.17
% 2.02/1.35  CNF conversion       : 0.02
% 2.02/1.35  Main loop            : 0.14
% 2.02/1.35  Inferencing          : 0.05
% 2.02/1.35  Reduction            : 0.05
% 2.02/1.35  Demodulation         : 0.03
% 2.02/1.35  BG Simplification    : 0.01
% 2.02/1.35  Subsumption          : 0.02
% 2.02/1.35  Abstraction          : 0.01
% 2.02/1.35  MUC search           : 0.00
% 2.02/1.35  Cooper               : 0.00
% 2.02/1.35  Total                : 0.49
% 2.02/1.35  Index Insertion      : 0.00
% 2.02/1.35  Index Deletion       : 0.00
% 2.02/1.35  Index Matching       : 0.00
% 2.02/1.35  BG Taut test         : 0.00
%------------------------------------------------------------------------------
