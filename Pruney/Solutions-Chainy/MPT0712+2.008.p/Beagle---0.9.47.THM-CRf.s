%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:05:32 EST 2020

% Result     : Theorem 1.80s
% Output     : CNFRefutation 1.80s
% Verified   : 
% Statistics : Number of formulae       :   51 (  69 expanded)
%              Number of leaves         :   29 (  38 expanded)
%              Depth                    :    9
%              Number of atoms          :   70 ( 107 expanded)
%              Number of equality atoms :   19 (  25 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_relat_1 > v1_funct_1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k2_tarski > k1_funct_1 > k11_relat_1 > #nlpp > k2_relat_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1

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

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

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

tff(f_33,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_74,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_relat_1(B)
          & v1_funct_1(B) )
       => r1_tarski(k2_relat_1(k7_relat_1(B,k1_tarski(A))),k1_tarski(k1_funct_1(B,A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t167_funct_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_57,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r2_hidden(A,k1_relat_1(B))
      <=> k11_relat_1(B,A) != k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t205_relat_1)).

tff(f_35,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_67,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( ( r2_hidden(A,k1_relat_1(C))
          & r2_hidden(B,k1_relat_1(C)) )
       => k9_relat_1(C,k2_tarski(A,B)) = k2_tarski(k1_funct_1(C,A),k1_funct_1(C,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t118_funct_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_46,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] : k11_relat_1(A,B) = k9_relat_1(A,k1_tarski(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d16_relat_1)).

tff(c_8,plain,(
    ! [A_3] : r1_tarski(k1_xboole_0,A_3) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_32,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_30,plain,(
    v1_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_22,plain,(
    ! [A_19,B_20] :
      ( r2_hidden(A_19,k1_relat_1(B_20))
      | k11_relat_1(B_20,A_19) = k1_xboole_0
      | ~ v1_relat_1(B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_10,plain,(
    ! [A_4] : k2_tarski(A_4,A_4) = k1_tarski(A_4) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_129,plain,(
    ! [C_47,A_48,B_49] :
      ( k2_tarski(k1_funct_1(C_47,A_48),k1_funct_1(C_47,B_49)) = k9_relat_1(C_47,k2_tarski(A_48,B_49))
      | ~ r2_hidden(B_49,k1_relat_1(C_47))
      | ~ r2_hidden(A_48,k1_relat_1(C_47))
      | ~ v1_funct_1(C_47)
      | ~ v1_relat_1(C_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_136,plain,(
    ! [C_47,B_49] :
      ( k9_relat_1(C_47,k2_tarski(B_49,B_49)) = k1_tarski(k1_funct_1(C_47,B_49))
      | ~ r2_hidden(B_49,k1_relat_1(C_47))
      | ~ r2_hidden(B_49,k1_relat_1(C_47))
      | ~ v1_funct_1(C_47)
      | ~ v1_relat_1(C_47) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_129,c_10])).

tff(c_148,plain,(
    ! [C_50,B_51] :
      ( k9_relat_1(C_50,k1_tarski(B_51)) = k1_tarski(k1_funct_1(C_50,B_51))
      | ~ r2_hidden(B_51,k1_relat_1(C_50))
      | ~ r2_hidden(B_51,k1_relat_1(C_50))
      | ~ v1_funct_1(C_50)
      | ~ v1_relat_1(C_50) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_136])).

tff(c_152,plain,(
    ! [B_52,A_53] :
      ( k9_relat_1(B_52,k1_tarski(A_53)) = k1_tarski(k1_funct_1(B_52,A_53))
      | ~ r2_hidden(A_53,k1_relat_1(B_52))
      | ~ v1_funct_1(B_52)
      | k11_relat_1(B_52,A_53) = k1_xboole_0
      | ~ v1_relat_1(B_52) ) ),
    inference(resolution,[status(thm)],[c_22,c_148])).

tff(c_157,plain,(
    ! [B_54,A_55] :
      ( k9_relat_1(B_54,k1_tarski(A_55)) = k1_tarski(k1_funct_1(B_54,A_55))
      | ~ v1_funct_1(B_54)
      | k11_relat_1(B_54,A_55) = k1_xboole_0
      | ~ v1_relat_1(B_54) ) ),
    inference(resolution,[status(thm)],[c_22,c_152])).

tff(c_20,plain,(
    ! [B_18,A_17] :
      ( k2_relat_1(k7_relat_1(B_18,A_17)) = k9_relat_1(B_18,A_17)
      | ~ v1_relat_1(B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_28,plain,(
    ~ r1_tarski(k2_relat_1(k7_relat_1('#skF_2',k1_tarski('#skF_1'))),k1_tarski(k1_funct_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_88,plain,
    ( ~ r1_tarski(k9_relat_1('#skF_2',k1_tarski('#skF_1')),k1_tarski(k1_funct_1('#skF_2','#skF_1')))
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_28])).

tff(c_90,plain,(
    ~ r1_tarski(k9_relat_1('#skF_2',k1_tarski('#skF_1')),k1_tarski(k1_funct_1('#skF_2','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_88])).

tff(c_163,plain,
    ( ~ r1_tarski(k1_tarski(k1_funct_1('#skF_2','#skF_1')),k1_tarski(k1_funct_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_2')
    | k11_relat_1('#skF_2','#skF_1') = k1_xboole_0
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_157,c_90])).

tff(c_175,plain,(
    k11_relat_1('#skF_2','#skF_1') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_6,c_163])).

tff(c_18,plain,(
    ! [A_14,B_16] :
      ( k9_relat_1(A_14,k1_tarski(B_16)) = k11_relat_1(A_14,B_16)
      | ~ v1_relat_1(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_111,plain,
    ( ~ r1_tarski(k11_relat_1('#skF_2','#skF_1'),k1_tarski(k1_funct_1('#skF_2','#skF_1')))
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_90])).

tff(c_113,plain,(
    ~ r1_tarski(k11_relat_1('#skF_2','#skF_1'),k1_tarski(k1_funct_1('#skF_2','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_111])).

tff(c_177,plain,(
    ~ r1_tarski(k1_xboole_0,k1_tarski(k1_funct_1('#skF_2','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_175,c_113])).

tff(c_180,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_177])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n015.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 14:31:53 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.80/1.27  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.80/1.27  
% 1.80/1.27  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.80/1.27  %$ r2_hidden > r1_tarski > v1_relat_1 > v1_funct_1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k2_tarski > k1_funct_1 > k11_relat_1 > #nlpp > k2_relat_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1
% 1.80/1.27  
% 1.80/1.27  %Foreground sorts:
% 1.80/1.27  
% 1.80/1.27  
% 1.80/1.27  %Background operators:
% 1.80/1.27  
% 1.80/1.27  
% 1.80/1.27  %Foreground operators:
% 1.80/1.27  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 1.80/1.27  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.80/1.27  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.80/1.27  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.80/1.27  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 1.80/1.27  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.80/1.27  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 1.80/1.27  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.80/1.27  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.80/1.27  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.80/1.27  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.80/1.27  tff(k11_relat_1, type, k11_relat_1: ($i * $i) > $i).
% 1.80/1.27  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.80/1.27  tff('#skF_2', type, '#skF_2': $i).
% 1.80/1.27  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 1.80/1.27  tff('#skF_1', type, '#skF_1': $i).
% 1.80/1.27  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 1.80/1.27  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.80/1.27  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.80/1.27  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.80/1.27  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.80/1.27  
% 1.80/1.29  tff(f_33, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 1.80/1.29  tff(f_74, negated_conjecture, ~(![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => r1_tarski(k2_relat_1(k7_relat_1(B, k1_tarski(A))), k1_tarski(k1_funct_1(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t167_funct_1)).
% 1.80/1.29  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 1.80/1.29  tff(f_57, axiom, (![A, B]: (v1_relat_1(B) => (r2_hidden(A, k1_relat_1(B)) <=> ~(k11_relat_1(B, A) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t205_relat_1)).
% 1.80/1.29  tff(f_35, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 1.80/1.29  tff(f_67, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => ((r2_hidden(A, k1_relat_1(C)) & r2_hidden(B, k1_relat_1(C))) => (k9_relat_1(C, k2_tarski(A, B)) = k2_tarski(k1_funct_1(C, A), k1_funct_1(C, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t118_funct_1)).
% 1.80/1.29  tff(f_50, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_relat_1)).
% 1.80/1.29  tff(f_46, axiom, (![A]: (v1_relat_1(A) => (![B]: (k11_relat_1(A, B) = k9_relat_1(A, k1_tarski(B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d16_relat_1)).
% 1.80/1.29  tff(c_8, plain, (![A_3]: (r1_tarski(k1_xboole_0, A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.80/1.29  tff(c_32, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_74])).
% 1.80/1.29  tff(c_30, plain, (v1_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_74])).
% 1.80/1.29  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.80/1.29  tff(c_22, plain, (![A_19, B_20]: (r2_hidden(A_19, k1_relat_1(B_20)) | k11_relat_1(B_20, A_19)=k1_xboole_0 | ~v1_relat_1(B_20))), inference(cnfTransformation, [status(thm)], [f_57])).
% 1.80/1.29  tff(c_10, plain, (![A_4]: (k2_tarski(A_4, A_4)=k1_tarski(A_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.80/1.29  tff(c_129, plain, (![C_47, A_48, B_49]: (k2_tarski(k1_funct_1(C_47, A_48), k1_funct_1(C_47, B_49))=k9_relat_1(C_47, k2_tarski(A_48, B_49)) | ~r2_hidden(B_49, k1_relat_1(C_47)) | ~r2_hidden(A_48, k1_relat_1(C_47)) | ~v1_funct_1(C_47) | ~v1_relat_1(C_47))), inference(cnfTransformation, [status(thm)], [f_67])).
% 1.80/1.29  tff(c_136, plain, (![C_47, B_49]: (k9_relat_1(C_47, k2_tarski(B_49, B_49))=k1_tarski(k1_funct_1(C_47, B_49)) | ~r2_hidden(B_49, k1_relat_1(C_47)) | ~r2_hidden(B_49, k1_relat_1(C_47)) | ~v1_funct_1(C_47) | ~v1_relat_1(C_47))), inference(superposition, [status(thm), theory('equality')], [c_129, c_10])).
% 1.80/1.29  tff(c_148, plain, (![C_50, B_51]: (k9_relat_1(C_50, k1_tarski(B_51))=k1_tarski(k1_funct_1(C_50, B_51)) | ~r2_hidden(B_51, k1_relat_1(C_50)) | ~r2_hidden(B_51, k1_relat_1(C_50)) | ~v1_funct_1(C_50) | ~v1_relat_1(C_50))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_136])).
% 1.80/1.29  tff(c_152, plain, (![B_52, A_53]: (k9_relat_1(B_52, k1_tarski(A_53))=k1_tarski(k1_funct_1(B_52, A_53)) | ~r2_hidden(A_53, k1_relat_1(B_52)) | ~v1_funct_1(B_52) | k11_relat_1(B_52, A_53)=k1_xboole_0 | ~v1_relat_1(B_52))), inference(resolution, [status(thm)], [c_22, c_148])).
% 1.80/1.29  tff(c_157, plain, (![B_54, A_55]: (k9_relat_1(B_54, k1_tarski(A_55))=k1_tarski(k1_funct_1(B_54, A_55)) | ~v1_funct_1(B_54) | k11_relat_1(B_54, A_55)=k1_xboole_0 | ~v1_relat_1(B_54))), inference(resolution, [status(thm)], [c_22, c_152])).
% 1.80/1.29  tff(c_20, plain, (![B_18, A_17]: (k2_relat_1(k7_relat_1(B_18, A_17))=k9_relat_1(B_18, A_17) | ~v1_relat_1(B_18))), inference(cnfTransformation, [status(thm)], [f_50])).
% 1.80/1.29  tff(c_28, plain, (~r1_tarski(k2_relat_1(k7_relat_1('#skF_2', k1_tarski('#skF_1'))), k1_tarski(k1_funct_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_74])).
% 1.80/1.29  tff(c_88, plain, (~r1_tarski(k9_relat_1('#skF_2', k1_tarski('#skF_1')), k1_tarski(k1_funct_1('#skF_2', '#skF_1'))) | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_20, c_28])).
% 1.80/1.29  tff(c_90, plain, (~r1_tarski(k9_relat_1('#skF_2', k1_tarski('#skF_1')), k1_tarski(k1_funct_1('#skF_2', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_88])).
% 1.80/1.29  tff(c_163, plain, (~r1_tarski(k1_tarski(k1_funct_1('#skF_2', '#skF_1')), k1_tarski(k1_funct_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_2') | k11_relat_1('#skF_2', '#skF_1')=k1_xboole_0 | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_157, c_90])).
% 1.80/1.29  tff(c_175, plain, (k11_relat_1('#skF_2', '#skF_1')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_6, c_163])).
% 1.80/1.29  tff(c_18, plain, (![A_14, B_16]: (k9_relat_1(A_14, k1_tarski(B_16))=k11_relat_1(A_14, B_16) | ~v1_relat_1(A_14))), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.80/1.29  tff(c_111, plain, (~r1_tarski(k11_relat_1('#skF_2', '#skF_1'), k1_tarski(k1_funct_1('#skF_2', '#skF_1'))) | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_18, c_90])).
% 1.80/1.29  tff(c_113, plain, (~r1_tarski(k11_relat_1('#skF_2', '#skF_1'), k1_tarski(k1_funct_1('#skF_2', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_111])).
% 1.80/1.29  tff(c_177, plain, (~r1_tarski(k1_xboole_0, k1_tarski(k1_funct_1('#skF_2', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_175, c_113])).
% 1.80/1.29  tff(c_180, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_8, c_177])).
% 1.80/1.29  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.80/1.29  
% 1.80/1.29  Inference rules
% 1.80/1.29  ----------------------
% 1.80/1.29  #Ref     : 0
% 1.80/1.29  #Sup     : 30
% 1.80/1.29  #Fact    : 0
% 1.80/1.29  #Define  : 0
% 1.80/1.29  #Split   : 0
% 1.80/1.29  #Chain   : 0
% 1.80/1.29  #Close   : 0
% 1.80/1.29  
% 1.80/1.29  Ordering : KBO
% 1.80/1.29  
% 1.80/1.29  Simplification rules
% 1.80/1.29  ----------------------
% 1.80/1.29  #Subsume      : 1
% 1.80/1.29  #Demod        : 11
% 1.80/1.29  #Tautology    : 21
% 1.80/1.29  #SimpNegUnit  : 0
% 1.80/1.29  #BackRed      : 1
% 1.80/1.29  
% 1.80/1.29  #Partial instantiations: 0
% 1.80/1.29  #Strategies tried      : 1
% 1.80/1.29  
% 1.80/1.29  Timing (in seconds)
% 1.80/1.29  ----------------------
% 1.80/1.29  Preprocessing        : 0.27
% 1.80/1.29  Parsing              : 0.14
% 1.80/1.29  CNF conversion       : 0.02
% 1.80/1.29  Main loop            : 0.14
% 1.80/1.29  Inferencing          : 0.06
% 1.80/1.29  Reduction            : 0.04
% 1.80/1.29  Demodulation         : 0.03
% 1.80/1.29  BG Simplification    : 0.01
% 1.80/1.29  Subsumption          : 0.02
% 1.80/1.29  Abstraction          : 0.01
% 1.80/1.29  MUC search           : 0.00
% 1.80/1.29  Cooper               : 0.00
% 1.80/1.29  Total                : 0.44
% 1.80/1.29  Index Insertion      : 0.00
% 1.80/1.29  Index Deletion       : 0.00
% 1.80/1.29  Index Matching       : 0.00
% 1.80/1.29  BG Taut test         : 0.00
%------------------------------------------------------------------------------
