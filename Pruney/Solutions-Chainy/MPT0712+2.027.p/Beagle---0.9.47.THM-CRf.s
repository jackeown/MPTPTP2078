%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:05:34 EST 2020

% Result     : Theorem 2.56s
% Output     : CNFRefutation 2.56s
% Verified   : 
% Statistics : Number of formulae       :   49 (  71 expanded)
%              Number of leaves         :   26 (  37 expanded)
%              Depth                    :    9
%              Number of atoms          :   60 ( 106 expanded)
%              Number of equality atoms :   20 (  29 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_relat_1 > v1_funct_1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k2_tarski > k1_funct_1 > k11_relat_1 > #nlpp > k2_relat_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1

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

tff(f_27,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_44,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k2_tarski(B,C))
    <=> ~ ( A != k1_xboole_0
          & A != k1_tarski(B)
          & A != k1_tarski(C)
          & A != k2_tarski(B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l45_zfmisc_1)).

tff(f_75,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_relat_1(B)
          & v1_funct_1(B) )
       => r1_tarski(k2_relat_1(k7_relat_1(B,k1_tarski(A))),k1_tarski(k1_funct_1(B,A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t167_funct_1)).

tff(f_60,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r2_hidden(A,k1_relat_1(B))
      <=> k11_relat_1(B,A) != k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t205_relat_1)).

tff(f_68,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r2_hidden(A,k1_relat_1(B))
       => k11_relat_1(B,A) = k1_tarski(k1_funct_1(B,A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t117_funct_1)).

tff(f_49,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] : k11_relat_1(A,B) = k9_relat_1(A,k1_tarski(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d16_relat_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

tff(c_32,plain,(
    ! [A_18] : k2_tarski(A_18,A_18) = k1_tarski(A_18) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_14,plain,(
    ! [B_5,C_6] : r1_tarski(k1_xboole_0,k2_tarski(B_5,C_6)) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_37,plain,(
    ! [A_18] : r1_tarski(k1_xboole_0,k1_tarski(A_18)) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_14])).

tff(c_30,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_28,plain,(
    v1_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_20,plain,(
    ! [A_12,B_13] :
      ( r2_hidden(A_12,k1_relat_1(B_13))
      | k11_relat_1(B_13,A_12) = k1_xboole_0
      | ~ v1_relat_1(B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_106,plain,(
    ! [B_37,A_38] :
      ( k1_tarski(k1_funct_1(B_37,A_38)) = k11_relat_1(B_37,A_38)
      | ~ r2_hidden(A_38,k1_relat_1(B_37))
      | ~ v1_funct_1(B_37)
      | ~ v1_relat_1(B_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_111,plain,(
    ! [B_39,A_40] :
      ( k1_tarski(k1_funct_1(B_39,A_40)) = k11_relat_1(B_39,A_40)
      | ~ v1_funct_1(B_39)
      | k11_relat_1(B_39,A_40) = k1_xboole_0
      | ~ v1_relat_1(B_39) ) ),
    inference(resolution,[status(thm)],[c_20,c_106])).

tff(c_2,plain,(
    ! [A_1] : k2_tarski(A_1,A_1) = k1_tarski(A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_44,plain,(
    ! [C_20,B_21] : r1_tarski(k1_tarski(C_20),k2_tarski(B_21,C_20)) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_47,plain,(
    ! [A_1] : r1_tarski(k1_tarski(A_1),k1_tarski(A_1)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_44])).

tff(c_203,plain,(
    ! [B_48,A_49] :
      ( r1_tarski(k11_relat_1(B_48,A_49),k1_tarski(k1_funct_1(B_48,A_49)))
      | ~ v1_funct_1(B_48)
      | k11_relat_1(B_48,A_49) = k1_xboole_0
      | ~ v1_relat_1(B_48) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_111,c_47])).

tff(c_16,plain,(
    ! [A_7,B_9] :
      ( k9_relat_1(A_7,k1_tarski(B_9)) = k11_relat_1(A_7,B_9)
      | ~ v1_relat_1(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_81,plain,(
    ! [B_31,A_32] :
      ( k2_relat_1(k7_relat_1(B_31,A_32)) = k9_relat_1(B_31,A_32)
      | ~ v1_relat_1(B_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_26,plain,(
    ~ r1_tarski(k2_relat_1(k7_relat_1('#skF_2',k1_tarski('#skF_1'))),k1_tarski(k1_funct_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_87,plain,
    ( ~ r1_tarski(k9_relat_1('#skF_2',k1_tarski('#skF_1')),k1_tarski(k1_funct_1('#skF_2','#skF_1')))
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_81,c_26])).

tff(c_93,plain,(
    ~ r1_tarski(k9_relat_1('#skF_2',k1_tarski('#skF_1')),k1_tarski(k1_funct_1('#skF_2','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_87])).

tff(c_97,plain,
    ( ~ r1_tarski(k11_relat_1('#skF_2','#skF_1'),k1_tarski(k1_funct_1('#skF_2','#skF_1')))
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_93])).

tff(c_99,plain,(
    ~ r1_tarski(k11_relat_1('#skF_2','#skF_1'),k1_tarski(k1_funct_1('#skF_2','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_97])).

tff(c_209,plain,
    ( ~ v1_funct_1('#skF_2')
    | k11_relat_1('#skF_2','#skF_1') = k1_xboole_0
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_203,c_99])).

tff(c_216,plain,(
    k11_relat_1('#skF_2','#skF_1') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_209])).

tff(c_220,plain,(
    ~ r1_tarski(k1_xboole_0,k1_tarski(k1_funct_1('#skF_2','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_216,c_99])).

tff(c_223,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_37,c_220])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:14:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.56/1.67  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.56/1.68  
% 2.56/1.68  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.56/1.68  %$ r2_hidden > r1_tarski > v1_relat_1 > v1_funct_1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k2_tarski > k1_funct_1 > k11_relat_1 > #nlpp > k2_relat_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1
% 2.56/1.68  
% 2.56/1.68  %Foreground sorts:
% 2.56/1.68  
% 2.56/1.68  
% 2.56/1.68  %Background operators:
% 2.56/1.68  
% 2.56/1.68  
% 2.56/1.68  %Foreground operators:
% 2.56/1.68  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.56/1.68  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.56/1.68  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.56/1.68  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.56/1.68  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.56/1.68  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.56/1.68  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.56/1.68  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.56/1.68  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.56/1.68  tff(k11_relat_1, type, k11_relat_1: ($i * $i) > $i).
% 2.56/1.68  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.56/1.68  tff('#skF_2', type, '#skF_2': $i).
% 2.56/1.68  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.56/1.68  tff('#skF_1', type, '#skF_1': $i).
% 2.56/1.68  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.56/1.68  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.56/1.68  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.56/1.68  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.56/1.68  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.56/1.68  
% 2.56/1.70  tff(f_27, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 2.56/1.70  tff(f_44, axiom, (![A, B, C]: (r1_tarski(A, k2_tarski(B, C)) <=> ~(((~(A = k1_xboole_0) & ~(A = k1_tarski(B))) & ~(A = k1_tarski(C))) & ~(A = k2_tarski(B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l45_zfmisc_1)).
% 2.56/1.70  tff(f_75, negated_conjecture, ~(![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => r1_tarski(k2_relat_1(k7_relat_1(B, k1_tarski(A))), k1_tarski(k1_funct_1(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t167_funct_1)).
% 2.56/1.70  tff(f_60, axiom, (![A, B]: (v1_relat_1(B) => (r2_hidden(A, k1_relat_1(B)) <=> ~(k11_relat_1(B, A) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t205_relat_1)).
% 2.56/1.70  tff(f_68, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r2_hidden(A, k1_relat_1(B)) => (k11_relat_1(B, A) = k1_tarski(k1_funct_1(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t117_funct_1)).
% 2.56/1.70  tff(f_49, axiom, (![A]: (v1_relat_1(A) => (![B]: (k11_relat_1(A, B) = k9_relat_1(A, k1_tarski(B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d16_relat_1)).
% 2.56/1.70  tff(f_53, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_relat_1)).
% 2.56/1.70  tff(c_32, plain, (![A_18]: (k2_tarski(A_18, A_18)=k1_tarski(A_18))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.56/1.70  tff(c_14, plain, (![B_5, C_6]: (r1_tarski(k1_xboole_0, k2_tarski(B_5, C_6)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.56/1.70  tff(c_37, plain, (![A_18]: (r1_tarski(k1_xboole_0, k1_tarski(A_18)))), inference(superposition, [status(thm), theory('equality')], [c_32, c_14])).
% 2.56/1.70  tff(c_30, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.56/1.70  tff(c_28, plain, (v1_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.56/1.70  tff(c_20, plain, (![A_12, B_13]: (r2_hidden(A_12, k1_relat_1(B_13)) | k11_relat_1(B_13, A_12)=k1_xboole_0 | ~v1_relat_1(B_13))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.56/1.70  tff(c_106, plain, (![B_37, A_38]: (k1_tarski(k1_funct_1(B_37, A_38))=k11_relat_1(B_37, A_38) | ~r2_hidden(A_38, k1_relat_1(B_37)) | ~v1_funct_1(B_37) | ~v1_relat_1(B_37))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.56/1.70  tff(c_111, plain, (![B_39, A_40]: (k1_tarski(k1_funct_1(B_39, A_40))=k11_relat_1(B_39, A_40) | ~v1_funct_1(B_39) | k11_relat_1(B_39, A_40)=k1_xboole_0 | ~v1_relat_1(B_39))), inference(resolution, [status(thm)], [c_20, c_106])).
% 2.56/1.70  tff(c_2, plain, (![A_1]: (k2_tarski(A_1, A_1)=k1_tarski(A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.56/1.70  tff(c_44, plain, (![C_20, B_21]: (r1_tarski(k1_tarski(C_20), k2_tarski(B_21, C_20)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.56/1.70  tff(c_47, plain, (![A_1]: (r1_tarski(k1_tarski(A_1), k1_tarski(A_1)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_44])).
% 2.56/1.70  tff(c_203, plain, (![B_48, A_49]: (r1_tarski(k11_relat_1(B_48, A_49), k1_tarski(k1_funct_1(B_48, A_49))) | ~v1_funct_1(B_48) | k11_relat_1(B_48, A_49)=k1_xboole_0 | ~v1_relat_1(B_48))), inference(superposition, [status(thm), theory('equality')], [c_111, c_47])).
% 2.56/1.70  tff(c_16, plain, (![A_7, B_9]: (k9_relat_1(A_7, k1_tarski(B_9))=k11_relat_1(A_7, B_9) | ~v1_relat_1(A_7))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.56/1.70  tff(c_81, plain, (![B_31, A_32]: (k2_relat_1(k7_relat_1(B_31, A_32))=k9_relat_1(B_31, A_32) | ~v1_relat_1(B_31))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.56/1.70  tff(c_26, plain, (~r1_tarski(k2_relat_1(k7_relat_1('#skF_2', k1_tarski('#skF_1'))), k1_tarski(k1_funct_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.56/1.70  tff(c_87, plain, (~r1_tarski(k9_relat_1('#skF_2', k1_tarski('#skF_1')), k1_tarski(k1_funct_1('#skF_2', '#skF_1'))) | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_81, c_26])).
% 2.56/1.70  tff(c_93, plain, (~r1_tarski(k9_relat_1('#skF_2', k1_tarski('#skF_1')), k1_tarski(k1_funct_1('#skF_2', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_87])).
% 2.56/1.70  tff(c_97, plain, (~r1_tarski(k11_relat_1('#skF_2', '#skF_1'), k1_tarski(k1_funct_1('#skF_2', '#skF_1'))) | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_16, c_93])).
% 2.56/1.70  tff(c_99, plain, (~r1_tarski(k11_relat_1('#skF_2', '#skF_1'), k1_tarski(k1_funct_1('#skF_2', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_97])).
% 2.56/1.70  tff(c_209, plain, (~v1_funct_1('#skF_2') | k11_relat_1('#skF_2', '#skF_1')=k1_xboole_0 | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_203, c_99])).
% 2.56/1.70  tff(c_216, plain, (k11_relat_1('#skF_2', '#skF_1')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_209])).
% 2.56/1.70  tff(c_220, plain, (~r1_tarski(k1_xboole_0, k1_tarski(k1_funct_1('#skF_2', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_216, c_99])).
% 2.56/1.70  tff(c_223, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_37, c_220])).
% 2.56/1.70  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.56/1.70  
% 2.56/1.70  Inference rules
% 2.56/1.70  ----------------------
% 2.56/1.70  #Ref     : 0
% 2.56/1.70  #Sup     : 41
% 2.56/1.70  #Fact    : 0
% 2.56/1.70  #Define  : 0
% 2.56/1.70  #Split   : 1
% 2.56/1.70  #Chain   : 0
% 2.56/1.70  #Close   : 0
% 2.56/1.70  
% 2.56/1.70  Ordering : KBO
% 2.56/1.70  
% 2.56/1.70  Simplification rules
% 2.56/1.70  ----------------------
% 2.56/1.70  #Subsume      : 3
% 2.56/1.70  #Demod        : 24
% 2.56/1.70  #Tautology    : 20
% 2.56/1.70  #SimpNegUnit  : 0
% 2.56/1.70  #BackRed      : 4
% 2.56/1.70  
% 2.56/1.70  #Partial instantiations: 0
% 2.56/1.70  #Strategies tried      : 1
% 2.56/1.70  
% 2.56/1.70  Timing (in seconds)
% 2.56/1.70  ----------------------
% 2.56/1.70  Preprocessing        : 0.48
% 2.56/1.71  Parsing              : 0.25
% 2.56/1.71  CNF conversion       : 0.03
% 2.56/1.71  Main loop            : 0.30
% 2.56/1.71  Inferencing          : 0.11
% 2.56/1.71  Reduction            : 0.10
% 2.56/1.71  Demodulation         : 0.07
% 2.56/1.71  BG Simplification    : 0.02
% 2.56/1.71  Subsumption          : 0.05
% 2.56/1.71  Abstraction          : 0.02
% 2.56/1.71  MUC search           : 0.00
% 2.56/1.71  Cooper               : 0.00
% 2.56/1.71  Total                : 0.83
% 2.56/1.71  Index Insertion      : 0.00
% 2.56/1.71  Index Deletion       : 0.00
% 2.56/1.71  Index Matching       : 0.00
% 2.56/1.71  BG Taut test         : 0.00
%------------------------------------------------------------------------------
