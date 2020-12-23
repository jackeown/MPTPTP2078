%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:05:31 EST 2020

% Result     : Theorem 1.71s
% Output     : CNFRefutation 1.71s
% Verified   : 
% Statistics : Number of formulae       :   49 (  57 expanded)
%              Number of leaves         :   28 (  33 expanded)
%              Depth                    :    7
%              Number of atoms          :   63 (  81 expanded)
%              Number of equality atoms :   19 (  19 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > v1_relat_1 > v1_funct_1 > k9_relat_1 > k7_relat_1 > k2_tarski > k1_funct_1 > k11_relat_1 > #nlpp > k2_relat_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1

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

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_78,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_relat_1(B)
          & v1_funct_1(B) )
       => r1_tarski(k2_relat_1(k7_relat_1(B,k1_tarski(A))),k1_tarski(k1_funct_1(B,A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t167_funct_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k1_tarski(B))
    <=> ( A = k1_xboole_0
        | A = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).

tff(f_63,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( ~ r2_hidden(A,B)
     => r1_xboole_0(k1_tarski(A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l27_zfmisc_1)).

tff(f_60,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( r1_xboole_0(B,k1_relat_1(A))
         => k7_relat_1(A,B) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t187_relat_1)).

tff(f_71,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r2_hidden(A,k1_relat_1(B))
       => k11_relat_1(B,A) = k1_tarski(k1_funct_1(B,A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t117_funct_1)).

tff(f_49,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] : k11_relat_1(A,B) = k9_relat_1(A,k1_tarski(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d16_relat_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_34,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_32,plain,(
    v1_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_16,plain,(
    ! [B_7] : r1_tarski(k1_xboole_0,k1_tarski(B_7)) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_24,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_10,plain,(
    ! [A_4,B_5] :
      ( r1_xboole_0(k1_tarski(A_4),B_5)
      | r2_hidden(A_4,B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_108,plain,(
    ! [A_32,B_33] :
      ( k7_relat_1(A_32,B_33) = k1_xboole_0
      | ~ r1_xboole_0(B_33,k1_relat_1(A_32))
      | ~ v1_relat_1(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_122,plain,(
    ! [A_36,A_37] :
      ( k7_relat_1(A_36,k1_tarski(A_37)) = k1_xboole_0
      | ~ v1_relat_1(A_36)
      | r2_hidden(A_37,k1_relat_1(A_36)) ) ),
    inference(resolution,[status(thm)],[c_10,c_108])).

tff(c_28,plain,(
    ! [B_17,A_16] :
      ( k1_tarski(k1_funct_1(B_17,A_16)) = k11_relat_1(B_17,A_16)
      | ~ r2_hidden(A_16,k1_relat_1(B_17))
      | ~ v1_funct_1(B_17)
      | ~ v1_relat_1(B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_130,plain,(
    ! [A_38,A_39] :
      ( k1_tarski(k1_funct_1(A_38,A_39)) = k11_relat_1(A_38,A_39)
      | ~ v1_funct_1(A_38)
      | k7_relat_1(A_38,k1_tarski(A_39)) = k1_xboole_0
      | ~ v1_relat_1(A_38) ) ),
    inference(resolution,[status(thm)],[c_122,c_28])).

tff(c_30,plain,(
    ~ r1_tarski(k2_relat_1(k7_relat_1('#skF_2',k1_tarski('#skF_1'))),k1_tarski(k1_funct_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_139,plain,
    ( ~ r1_tarski(k2_relat_1(k1_xboole_0),k1_tarski(k1_funct_1('#skF_2','#skF_1')))
    | k1_tarski(k1_funct_1('#skF_2','#skF_1')) = k11_relat_1('#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_130,c_30])).

tff(c_146,plain,(
    k1_tarski(k1_funct_1('#skF_2','#skF_1')) = k11_relat_1('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_16,c_24,c_139])).

tff(c_18,plain,(
    ! [A_8,B_10] :
      ( k9_relat_1(A_8,k1_tarski(B_10)) = k11_relat_1(A_8,B_10)
      | ~ v1_relat_1(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_68,plain,(
    ! [B_26,A_27] :
      ( k2_relat_1(k7_relat_1(B_26,A_27)) = k9_relat_1(B_26,A_27)
      | ~ v1_relat_1(B_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_74,plain,
    ( ~ r1_tarski(k9_relat_1('#skF_2',k1_tarski('#skF_1')),k1_tarski(k1_funct_1('#skF_2','#skF_1')))
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_68,c_30])).

tff(c_80,plain,(
    ~ r1_tarski(k9_relat_1('#skF_2',k1_tarski('#skF_1')),k1_tarski(k1_funct_1('#skF_2','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_74])).

tff(c_105,plain,
    ( ~ r1_tarski(k11_relat_1('#skF_2','#skF_1'),k1_tarski(k1_funct_1('#skF_2','#skF_1')))
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_80])).

tff(c_107,plain,(
    ~ r1_tarski(k11_relat_1('#skF_2','#skF_1'),k1_tarski(k1_funct_1('#skF_2','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_105])).

tff(c_148,plain,(
    ~ r1_tarski(k11_relat_1('#skF_2','#skF_1'),k11_relat_1('#skF_2','#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_146,c_107])).

tff(c_153,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_148])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:06:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.71/1.16  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.71/1.16  
% 1.71/1.16  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.71/1.17  %$ r2_hidden > r1_xboole_0 > r1_tarski > v1_relat_1 > v1_funct_1 > k9_relat_1 > k7_relat_1 > k2_tarski > k1_funct_1 > k11_relat_1 > #nlpp > k2_relat_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1
% 1.71/1.17  
% 1.71/1.17  %Foreground sorts:
% 1.71/1.17  
% 1.71/1.17  
% 1.71/1.17  %Background operators:
% 1.71/1.17  
% 1.71/1.17  
% 1.71/1.17  %Foreground operators:
% 1.71/1.17  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 1.71/1.17  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.71/1.17  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.71/1.17  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.71/1.17  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 1.71/1.17  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.71/1.17  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.71/1.17  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.71/1.17  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.71/1.17  tff(k11_relat_1, type, k11_relat_1: ($i * $i) > $i).
% 1.71/1.17  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.71/1.17  tff('#skF_2', type, '#skF_2': $i).
% 1.71/1.17  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 1.71/1.17  tff('#skF_1', type, '#skF_1': $i).
% 1.71/1.17  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 1.71/1.17  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.71/1.17  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.71/1.17  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.71/1.17  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.71/1.17  
% 1.71/1.18  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 1.71/1.18  tff(f_78, negated_conjecture, ~(![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => r1_tarski(k2_relat_1(k7_relat_1(B, k1_tarski(A))), k1_tarski(k1_funct_1(B, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t167_funct_1)).
% 1.71/1.18  tff(f_44, axiom, (![A, B]: (r1_tarski(A, k1_tarski(B)) <=> ((A = k1_xboole_0) | (A = k1_tarski(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_zfmisc_1)).
% 1.71/1.18  tff(f_63, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 1.71/1.18  tff(f_38, axiom, (![A, B]: (~r2_hidden(A, B) => r1_xboole_0(k1_tarski(A), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 1.71/1.18  tff(f_60, axiom, (![A]: (v1_relat_1(A) => (![B]: (r1_xboole_0(B, k1_relat_1(A)) => (k7_relat_1(A, B) = k1_xboole_0))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t187_relat_1)).
% 1.71/1.18  tff(f_71, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r2_hidden(A, k1_relat_1(B)) => (k11_relat_1(B, A) = k1_tarski(k1_funct_1(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t117_funct_1)).
% 1.71/1.18  tff(f_49, axiom, (![A]: (v1_relat_1(A) => (![B]: (k11_relat_1(A, B) = k9_relat_1(A, k1_tarski(B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d16_relat_1)).
% 1.71/1.18  tff(f_53, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_relat_1)).
% 1.71/1.18  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.71/1.18  tff(c_34, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_78])).
% 1.71/1.18  tff(c_32, plain, (v1_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_78])).
% 1.71/1.18  tff(c_16, plain, (![B_7]: (r1_tarski(k1_xboole_0, k1_tarski(B_7)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 1.71/1.18  tff(c_24, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_63])).
% 1.71/1.18  tff(c_10, plain, (![A_4, B_5]: (r1_xboole_0(k1_tarski(A_4), B_5) | r2_hidden(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_38])).
% 1.71/1.18  tff(c_108, plain, (![A_32, B_33]: (k7_relat_1(A_32, B_33)=k1_xboole_0 | ~r1_xboole_0(B_33, k1_relat_1(A_32)) | ~v1_relat_1(A_32))), inference(cnfTransformation, [status(thm)], [f_60])).
% 1.71/1.18  tff(c_122, plain, (![A_36, A_37]: (k7_relat_1(A_36, k1_tarski(A_37))=k1_xboole_0 | ~v1_relat_1(A_36) | r2_hidden(A_37, k1_relat_1(A_36)))), inference(resolution, [status(thm)], [c_10, c_108])).
% 1.71/1.18  tff(c_28, plain, (![B_17, A_16]: (k1_tarski(k1_funct_1(B_17, A_16))=k11_relat_1(B_17, A_16) | ~r2_hidden(A_16, k1_relat_1(B_17)) | ~v1_funct_1(B_17) | ~v1_relat_1(B_17))), inference(cnfTransformation, [status(thm)], [f_71])).
% 1.71/1.18  tff(c_130, plain, (![A_38, A_39]: (k1_tarski(k1_funct_1(A_38, A_39))=k11_relat_1(A_38, A_39) | ~v1_funct_1(A_38) | k7_relat_1(A_38, k1_tarski(A_39))=k1_xboole_0 | ~v1_relat_1(A_38))), inference(resolution, [status(thm)], [c_122, c_28])).
% 1.71/1.18  tff(c_30, plain, (~r1_tarski(k2_relat_1(k7_relat_1('#skF_2', k1_tarski('#skF_1'))), k1_tarski(k1_funct_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_78])).
% 1.71/1.18  tff(c_139, plain, (~r1_tarski(k2_relat_1(k1_xboole_0), k1_tarski(k1_funct_1('#skF_2', '#skF_1'))) | k1_tarski(k1_funct_1('#skF_2', '#skF_1'))=k11_relat_1('#skF_2', '#skF_1') | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_130, c_30])).
% 1.71/1.18  tff(c_146, plain, (k1_tarski(k1_funct_1('#skF_2', '#skF_1'))=k11_relat_1('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_16, c_24, c_139])).
% 1.71/1.18  tff(c_18, plain, (![A_8, B_10]: (k9_relat_1(A_8, k1_tarski(B_10))=k11_relat_1(A_8, B_10) | ~v1_relat_1(A_8))), inference(cnfTransformation, [status(thm)], [f_49])).
% 1.71/1.18  tff(c_68, plain, (![B_26, A_27]: (k2_relat_1(k7_relat_1(B_26, A_27))=k9_relat_1(B_26, A_27) | ~v1_relat_1(B_26))), inference(cnfTransformation, [status(thm)], [f_53])).
% 1.71/1.18  tff(c_74, plain, (~r1_tarski(k9_relat_1('#skF_2', k1_tarski('#skF_1')), k1_tarski(k1_funct_1('#skF_2', '#skF_1'))) | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_68, c_30])).
% 1.71/1.18  tff(c_80, plain, (~r1_tarski(k9_relat_1('#skF_2', k1_tarski('#skF_1')), k1_tarski(k1_funct_1('#skF_2', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_74])).
% 1.71/1.18  tff(c_105, plain, (~r1_tarski(k11_relat_1('#skF_2', '#skF_1'), k1_tarski(k1_funct_1('#skF_2', '#skF_1'))) | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_18, c_80])).
% 1.71/1.18  tff(c_107, plain, (~r1_tarski(k11_relat_1('#skF_2', '#skF_1'), k1_tarski(k1_funct_1('#skF_2', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_105])).
% 1.71/1.18  tff(c_148, plain, (~r1_tarski(k11_relat_1('#skF_2', '#skF_1'), k11_relat_1('#skF_2', '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_146, c_107])).
% 1.71/1.18  tff(c_153, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_148])).
% 1.71/1.18  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.71/1.18  
% 1.71/1.18  Inference rules
% 1.71/1.18  ----------------------
% 1.71/1.18  #Ref     : 0
% 1.71/1.18  #Sup     : 25
% 1.71/1.18  #Fact    : 0
% 1.71/1.18  #Define  : 0
% 1.71/1.18  #Split   : 1
% 1.71/1.18  #Chain   : 0
% 1.71/1.18  #Close   : 0
% 1.71/1.18  
% 1.71/1.18  Ordering : KBO
% 1.71/1.18  
% 1.71/1.18  Simplification rules
% 1.71/1.18  ----------------------
% 1.71/1.18  #Subsume      : 2
% 1.71/1.18  #Demod        : 14
% 1.71/1.18  #Tautology    : 17
% 1.71/1.18  #SimpNegUnit  : 0
% 1.71/1.18  #BackRed      : 3
% 1.71/1.18  
% 1.71/1.18  #Partial instantiations: 0
% 1.71/1.18  #Strategies tried      : 1
% 1.71/1.18  
% 1.71/1.18  Timing (in seconds)
% 1.71/1.18  ----------------------
% 1.96/1.18  Preprocessing        : 0.29
% 1.96/1.18  Parsing              : 0.16
% 1.96/1.18  CNF conversion       : 0.02
% 1.96/1.18  Main loop            : 0.13
% 1.96/1.18  Inferencing          : 0.05
% 1.96/1.18  Reduction            : 0.04
% 1.96/1.18  Demodulation         : 0.03
% 1.96/1.18  BG Simplification    : 0.01
% 1.96/1.18  Subsumption          : 0.02
% 1.96/1.18  Abstraction          : 0.01
% 1.96/1.18  MUC search           : 0.00
% 1.96/1.18  Cooper               : 0.00
% 1.96/1.18  Total                : 0.45
% 1.96/1.18  Index Insertion      : 0.00
% 1.96/1.18  Index Deletion       : 0.00
% 1.96/1.18  Index Matching       : 0.00
% 1.96/1.18  BG Taut test         : 0.00
%------------------------------------------------------------------------------
