%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:05:31 EST 2020

% Result     : Theorem 1.88s
% Output     : CNFRefutation 1.99s
% Verified   : 
% Statistics : Number of formulae       :   50 (  58 expanded)
%              Number of leaves         :   29 (  34 expanded)
%              Depth                    :    7
%              Number of atoms          :   61 (  79 expanded)
%              Number of equality atoms :   17 (  17 expanded)
%              Maximal formula depth    :    7 (   4 average)
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

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_76,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_relat_1(B)
          & v1_funct_1(B) )
       => r1_tarski(k2_relat_1(k7_relat_1(B,k1_tarski(A))),k1_tarski(k1_funct_1(B,A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t167_funct_1)).

tff(f_33,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_61,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_42,axiom,(
    ! [A,B] :
      ( ~ r2_hidden(A,B)
     => r1_xboole_0(k1_tarski(A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l27_zfmisc_1)).

tff(f_58,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( r1_xboole_0(B,k1_relat_1(A))
         => k7_relat_1(A,B) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t187_relat_1)).

tff(f_69,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r2_hidden(A,k1_relat_1(B))
       => k11_relat_1(B,A) = k1_tarski(k1_funct_1(B,A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t117_funct_1)).

tff(f_47,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] : k11_relat_1(A,B) = k9_relat_1(A,k1_tarski(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d16_relat_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_32,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_30,plain,(
    v1_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_8,plain,(
    ! [A_3] : r1_tarski(k1_xboole_0,A_3) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_22,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_14,plain,(
    ! [A_7,B_8] :
      ( r1_xboole_0(k1_tarski(A_7),B_8)
      | r2_hidden(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_114,plain,(
    ! [A_33,B_34] :
      ( k7_relat_1(A_33,B_34) = k1_xboole_0
      | ~ r1_xboole_0(B_34,k1_relat_1(A_33))
      | ~ v1_relat_1(A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_128,plain,(
    ! [A_37,A_38] :
      ( k7_relat_1(A_37,k1_tarski(A_38)) = k1_xboole_0
      | ~ v1_relat_1(A_37)
      | r2_hidden(A_38,k1_relat_1(A_37)) ) ),
    inference(resolution,[status(thm)],[c_14,c_114])).

tff(c_26,plain,(
    ! [B_18,A_17] :
      ( k1_tarski(k1_funct_1(B_18,A_17)) = k11_relat_1(B_18,A_17)
      | ~ r2_hidden(A_17,k1_relat_1(B_18))
      | ~ v1_funct_1(B_18)
      | ~ v1_relat_1(B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_136,plain,(
    ! [A_39,A_40] :
      ( k1_tarski(k1_funct_1(A_39,A_40)) = k11_relat_1(A_39,A_40)
      | ~ v1_funct_1(A_39)
      | k7_relat_1(A_39,k1_tarski(A_40)) = k1_xboole_0
      | ~ v1_relat_1(A_39) ) ),
    inference(resolution,[status(thm)],[c_128,c_26])).

tff(c_28,plain,(
    ~ r1_tarski(k2_relat_1(k7_relat_1('#skF_2',k1_tarski('#skF_1'))),k1_tarski(k1_funct_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_145,plain,
    ( ~ r1_tarski(k2_relat_1(k1_xboole_0),k1_tarski(k1_funct_1('#skF_2','#skF_1')))
    | k1_tarski(k1_funct_1('#skF_2','#skF_1')) = k11_relat_1('#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_136,c_28])).

tff(c_152,plain,(
    k1_tarski(k1_funct_1('#skF_2','#skF_1')) = k11_relat_1('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_8,c_22,c_145])).

tff(c_16,plain,(
    ! [A_9,B_11] :
      ( k9_relat_1(A_9,k1_tarski(B_11)) = k11_relat_1(A_9,B_11)
      | ~ v1_relat_1(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_95,plain,(
    ! [B_31,A_32] :
      ( k2_relat_1(k7_relat_1(B_31,A_32)) = k9_relat_1(B_31,A_32)
      | ~ v1_relat_1(B_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_101,plain,
    ( ~ r1_tarski(k9_relat_1('#skF_2',k1_tarski('#skF_1')),k1_tarski(k1_funct_1('#skF_2','#skF_1')))
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_95,c_28])).

tff(c_107,plain,(
    ~ r1_tarski(k9_relat_1('#skF_2',k1_tarski('#skF_1')),k1_tarski(k1_funct_1('#skF_2','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_101])).

tff(c_111,plain,
    ( ~ r1_tarski(k11_relat_1('#skF_2','#skF_1'),k1_tarski(k1_funct_1('#skF_2','#skF_1')))
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_107])).

tff(c_113,plain,(
    ~ r1_tarski(k11_relat_1('#skF_2','#skF_1'),k1_tarski(k1_funct_1('#skF_2','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_111])).

tff(c_154,plain,(
    ~ r1_tarski(k11_relat_1('#skF_2','#skF_1'),k11_relat_1('#skF_2','#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_152,c_113])).

tff(c_159,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_154])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n021.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 13:47:34 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.88/1.17  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.88/1.18  
% 1.88/1.18  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.88/1.18  %$ r2_hidden > r1_xboole_0 > r1_tarski > v1_relat_1 > v1_funct_1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k2_tarski > k1_funct_1 > k11_relat_1 > #nlpp > k2_relat_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1
% 1.88/1.18  
% 1.88/1.18  %Foreground sorts:
% 1.88/1.18  
% 1.88/1.18  
% 1.88/1.18  %Background operators:
% 1.88/1.18  
% 1.88/1.18  
% 1.88/1.18  %Foreground operators:
% 1.88/1.18  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 1.88/1.18  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.88/1.18  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.88/1.18  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.88/1.18  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 1.88/1.18  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.88/1.18  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.88/1.18  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.88/1.18  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.88/1.18  tff(k11_relat_1, type, k11_relat_1: ($i * $i) > $i).
% 1.88/1.18  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.88/1.18  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.88/1.18  tff('#skF_2', type, '#skF_2': $i).
% 1.88/1.18  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 1.88/1.18  tff('#skF_1', type, '#skF_1': $i).
% 1.88/1.18  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 1.88/1.18  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.88/1.18  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.88/1.18  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.88/1.18  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.88/1.18  
% 1.99/1.19  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 1.99/1.19  tff(f_76, negated_conjecture, ~(![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => r1_tarski(k2_relat_1(k7_relat_1(B, k1_tarski(A))), k1_tarski(k1_funct_1(B, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t167_funct_1)).
% 1.99/1.19  tff(f_33, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 1.99/1.19  tff(f_61, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 1.99/1.19  tff(f_42, axiom, (![A, B]: (~r2_hidden(A, B) => r1_xboole_0(k1_tarski(A), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 1.99/1.19  tff(f_58, axiom, (![A]: (v1_relat_1(A) => (![B]: (r1_xboole_0(B, k1_relat_1(A)) => (k7_relat_1(A, B) = k1_xboole_0))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t187_relat_1)).
% 1.99/1.19  tff(f_69, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r2_hidden(A, k1_relat_1(B)) => (k11_relat_1(B, A) = k1_tarski(k1_funct_1(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t117_funct_1)).
% 1.99/1.19  tff(f_47, axiom, (![A]: (v1_relat_1(A) => (![B]: (k11_relat_1(A, B) = k9_relat_1(A, k1_tarski(B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d16_relat_1)).
% 1.99/1.19  tff(f_51, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_relat_1)).
% 1.99/1.19  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.99/1.19  tff(c_32, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_76])).
% 1.99/1.19  tff(c_30, plain, (v1_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_76])).
% 1.99/1.19  tff(c_8, plain, (![A_3]: (r1_tarski(k1_xboole_0, A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.99/1.19  tff(c_22, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_61])).
% 1.99/1.19  tff(c_14, plain, (![A_7, B_8]: (r1_xboole_0(k1_tarski(A_7), B_8) | r2_hidden(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.99/1.19  tff(c_114, plain, (![A_33, B_34]: (k7_relat_1(A_33, B_34)=k1_xboole_0 | ~r1_xboole_0(B_34, k1_relat_1(A_33)) | ~v1_relat_1(A_33))), inference(cnfTransformation, [status(thm)], [f_58])).
% 1.99/1.19  tff(c_128, plain, (![A_37, A_38]: (k7_relat_1(A_37, k1_tarski(A_38))=k1_xboole_0 | ~v1_relat_1(A_37) | r2_hidden(A_38, k1_relat_1(A_37)))), inference(resolution, [status(thm)], [c_14, c_114])).
% 1.99/1.19  tff(c_26, plain, (![B_18, A_17]: (k1_tarski(k1_funct_1(B_18, A_17))=k11_relat_1(B_18, A_17) | ~r2_hidden(A_17, k1_relat_1(B_18)) | ~v1_funct_1(B_18) | ~v1_relat_1(B_18))), inference(cnfTransformation, [status(thm)], [f_69])).
% 1.99/1.19  tff(c_136, plain, (![A_39, A_40]: (k1_tarski(k1_funct_1(A_39, A_40))=k11_relat_1(A_39, A_40) | ~v1_funct_1(A_39) | k7_relat_1(A_39, k1_tarski(A_40))=k1_xboole_0 | ~v1_relat_1(A_39))), inference(resolution, [status(thm)], [c_128, c_26])).
% 1.99/1.19  tff(c_28, plain, (~r1_tarski(k2_relat_1(k7_relat_1('#skF_2', k1_tarski('#skF_1'))), k1_tarski(k1_funct_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_76])).
% 1.99/1.19  tff(c_145, plain, (~r1_tarski(k2_relat_1(k1_xboole_0), k1_tarski(k1_funct_1('#skF_2', '#skF_1'))) | k1_tarski(k1_funct_1('#skF_2', '#skF_1'))=k11_relat_1('#skF_2', '#skF_1') | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_136, c_28])).
% 1.99/1.19  tff(c_152, plain, (k1_tarski(k1_funct_1('#skF_2', '#skF_1'))=k11_relat_1('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_8, c_22, c_145])).
% 1.99/1.19  tff(c_16, plain, (![A_9, B_11]: (k9_relat_1(A_9, k1_tarski(B_11))=k11_relat_1(A_9, B_11) | ~v1_relat_1(A_9))), inference(cnfTransformation, [status(thm)], [f_47])).
% 1.99/1.19  tff(c_95, plain, (![B_31, A_32]: (k2_relat_1(k7_relat_1(B_31, A_32))=k9_relat_1(B_31, A_32) | ~v1_relat_1(B_31))), inference(cnfTransformation, [status(thm)], [f_51])).
% 1.99/1.19  tff(c_101, plain, (~r1_tarski(k9_relat_1('#skF_2', k1_tarski('#skF_1')), k1_tarski(k1_funct_1('#skF_2', '#skF_1'))) | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_95, c_28])).
% 1.99/1.19  tff(c_107, plain, (~r1_tarski(k9_relat_1('#skF_2', k1_tarski('#skF_1')), k1_tarski(k1_funct_1('#skF_2', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_101])).
% 1.99/1.19  tff(c_111, plain, (~r1_tarski(k11_relat_1('#skF_2', '#skF_1'), k1_tarski(k1_funct_1('#skF_2', '#skF_1'))) | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_16, c_107])).
% 1.99/1.19  tff(c_113, plain, (~r1_tarski(k11_relat_1('#skF_2', '#skF_1'), k1_tarski(k1_funct_1('#skF_2', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_111])).
% 1.99/1.19  tff(c_154, plain, (~r1_tarski(k11_relat_1('#skF_2', '#skF_1'), k11_relat_1('#skF_2', '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_152, c_113])).
% 1.99/1.19  tff(c_159, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_154])).
% 1.99/1.19  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.99/1.19  
% 1.99/1.19  Inference rules
% 1.99/1.19  ----------------------
% 1.99/1.19  #Ref     : 0
% 1.99/1.19  #Sup     : 27
% 1.99/1.19  #Fact    : 0
% 1.99/1.19  #Define  : 0
% 1.99/1.19  #Split   : 1
% 1.99/1.19  #Chain   : 0
% 1.99/1.19  #Close   : 0
% 1.99/1.19  
% 1.99/1.19  Ordering : KBO
% 1.99/1.19  
% 1.99/1.19  Simplification rules
% 1.99/1.19  ----------------------
% 1.99/1.19  #Subsume      : 2
% 1.99/1.19  #Demod        : 13
% 1.99/1.19  #Tautology    : 18
% 1.99/1.19  #SimpNegUnit  : 0
% 1.99/1.19  #BackRed      : 3
% 1.99/1.19  
% 1.99/1.19  #Partial instantiations: 0
% 1.99/1.19  #Strategies tried      : 1
% 1.99/1.19  
% 1.99/1.19  Timing (in seconds)
% 1.99/1.19  ----------------------
% 1.99/1.19  Preprocessing        : 0.30
% 1.99/1.19  Parsing              : 0.16
% 1.99/1.19  CNF conversion       : 0.02
% 1.99/1.19  Main loop            : 0.15
% 1.99/1.19  Inferencing          : 0.05
% 1.99/1.19  Reduction            : 0.05
% 1.99/1.19  Demodulation         : 0.03
% 1.99/1.20  BG Simplification    : 0.01
% 1.99/1.20  Subsumption          : 0.02
% 1.99/1.20  Abstraction          : 0.01
% 1.99/1.20  MUC search           : 0.00
% 1.99/1.20  Cooper               : 0.00
% 1.99/1.20  Total                : 0.47
% 1.99/1.20  Index Insertion      : 0.00
% 1.99/1.20  Index Deletion       : 0.00
% 1.99/1.20  Index Matching       : 0.00
% 1.99/1.20  BG Taut test         : 0.00
%------------------------------------------------------------------------------
