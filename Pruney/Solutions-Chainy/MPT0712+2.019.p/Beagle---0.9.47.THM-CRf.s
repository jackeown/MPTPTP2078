%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:05:33 EST 2020

% Result     : Theorem 2.09s
% Output     : CNFRefutation 2.38s
% Verified   : 
% Statistics : Number of formulae       :   52 (  70 expanded)
%              Number of leaves         :   29 (  38 expanded)
%              Depth                    :    9
%              Number of atoms          :   78 ( 116 expanded)
%              Number of equality atoms :   21 (  30 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > v1_relat_1 > v1_funct_1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1

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

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

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

tff(f_33,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_63,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_80,negated_conjecture,(
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

tff(f_35,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_49,axiom,(
    ! [A,B,C] :
      ~ ( ~ r2_hidden(A,B)
        & ~ r2_hidden(C,B)
        & ~ r1_xboole_0(k2_tarski(A,C),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t57_zfmisc_1)).

tff(f_60,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( r1_xboole_0(B,k1_relat_1(A))
         => k7_relat_1(A,B) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t187_relat_1)).

tff(f_73,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( ( r2_hidden(A,k1_relat_1(C))
          & r2_hidden(B,k1_relat_1(C)) )
       => k9_relat_1(C,k2_tarski(A,B)) = k2_tarski(k1_funct_1(C,A),k1_funct_1(C,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t118_funct_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

tff(c_8,plain,(
    ! [A_3] : r1_tarski(k1_xboole_0,A_3) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_22,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_32,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_30,plain,(
    v1_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_10,plain,(
    ! [A_4] : k2_tarski(A_4,A_4) = k1_tarski(A_4) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_112,plain,(
    ! [A_36,C_37,B_38] :
      ( r1_xboole_0(k2_tarski(A_36,C_37),B_38)
      | r2_hidden(C_37,B_38)
      | r2_hidden(A_36,B_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_122,plain,(
    ! [A_39,B_40] :
      ( r1_xboole_0(k1_tarski(A_39),B_40)
      | r2_hidden(A_39,B_40)
      | r2_hidden(A_39,B_40) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_112])).

tff(c_20,plain,(
    ! [A_15,B_17] :
      ( k7_relat_1(A_15,B_17) = k1_xboole_0
      | ~ r1_xboole_0(B_17,k1_relat_1(A_15))
      | ~ v1_relat_1(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_127,plain,(
    ! [A_15,A_39] :
      ( k7_relat_1(A_15,k1_tarski(A_39)) = k1_xboole_0
      | ~ v1_relat_1(A_15)
      | r2_hidden(A_39,k1_relat_1(A_15)) ) ),
    inference(resolution,[status(thm)],[c_122,c_20])).

tff(c_128,plain,(
    ! [C_41,A_42,B_43] :
      ( k2_tarski(k1_funct_1(C_41,A_42),k1_funct_1(C_41,B_43)) = k9_relat_1(C_41,k2_tarski(A_42,B_43))
      | ~ r2_hidden(B_43,k1_relat_1(C_41))
      | ~ r2_hidden(A_42,k1_relat_1(C_41))
      | ~ v1_funct_1(C_41)
      | ~ v1_relat_1(C_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_138,plain,(
    ! [C_41,B_43] :
      ( k9_relat_1(C_41,k2_tarski(B_43,B_43)) = k1_tarski(k1_funct_1(C_41,B_43))
      | ~ r2_hidden(B_43,k1_relat_1(C_41))
      | ~ r2_hidden(B_43,k1_relat_1(C_41))
      | ~ v1_funct_1(C_41)
      | ~ v1_relat_1(C_41) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_128,c_10])).

tff(c_240,plain,(
    ! [C_54,B_55] :
      ( k9_relat_1(C_54,k1_tarski(B_55)) = k1_tarski(k1_funct_1(C_54,B_55))
      | ~ r2_hidden(B_55,k1_relat_1(C_54))
      | ~ r2_hidden(B_55,k1_relat_1(C_54))
      | ~ v1_funct_1(C_54)
      | ~ v1_relat_1(C_54) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_138])).

tff(c_262,plain,(
    ! [A_56,A_57] :
      ( k9_relat_1(A_56,k1_tarski(A_57)) = k1_tarski(k1_funct_1(A_56,A_57))
      | ~ r2_hidden(A_57,k1_relat_1(A_56))
      | ~ v1_funct_1(A_56)
      | k7_relat_1(A_56,k1_tarski(A_57)) = k1_xboole_0
      | ~ v1_relat_1(A_56) ) ),
    inference(resolution,[status(thm)],[c_127,c_240])).

tff(c_305,plain,(
    ! [A_62,A_63] :
      ( k9_relat_1(A_62,k1_tarski(A_63)) = k1_tarski(k1_funct_1(A_62,A_63))
      | ~ v1_funct_1(A_62)
      | k7_relat_1(A_62,k1_tarski(A_63)) = k1_xboole_0
      | ~ v1_relat_1(A_62) ) ),
    inference(resolution,[status(thm)],[c_127,c_262])).

tff(c_85,plain,(
    ! [B_29,A_30] :
      ( k2_relat_1(k7_relat_1(B_29,A_30)) = k9_relat_1(B_29,A_30)
      | ~ v1_relat_1(B_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_28,plain,(
    ~ r1_tarski(k2_relat_1(k7_relat_1('#skF_2',k1_tarski('#skF_1'))),k1_tarski(k1_funct_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_91,plain,
    ( ~ r1_tarski(k9_relat_1('#skF_2',k1_tarski('#skF_1')),k1_tarski(k1_funct_1('#skF_2','#skF_1')))
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_85,c_28])).

tff(c_97,plain,(
    ~ r1_tarski(k9_relat_1('#skF_2',k1_tarski('#skF_1')),k1_tarski(k1_funct_1('#skF_2','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_91])).

tff(c_311,plain,
    ( ~ r1_tarski(k1_tarski(k1_funct_1('#skF_2','#skF_1')),k1_tarski(k1_funct_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_2')
    | k7_relat_1('#skF_2',k1_tarski('#skF_1')) = k1_xboole_0
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_305,c_97])).

tff(c_317,plain,(
    k7_relat_1('#skF_2',k1_tarski('#skF_1')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_6,c_311])).

tff(c_319,plain,(
    ~ r1_tarski(k2_relat_1(k1_xboole_0),k1_tarski(k1_funct_1('#skF_2','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_317,c_28])).

tff(c_322,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_22,c_319])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:27:59 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.09/1.63  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.09/1.63  
% 2.09/1.63  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.09/1.63  %$ r2_hidden > r1_xboole_0 > r1_tarski > v1_relat_1 > v1_funct_1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1
% 2.09/1.63  
% 2.09/1.63  %Foreground sorts:
% 2.09/1.63  
% 2.09/1.63  
% 2.09/1.63  %Background operators:
% 2.09/1.63  
% 2.09/1.63  
% 2.09/1.63  %Foreground operators:
% 2.09/1.63  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.09/1.63  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.09/1.63  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.09/1.63  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.09/1.63  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.09/1.63  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.09/1.63  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.09/1.63  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.09/1.63  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.09/1.63  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.09/1.63  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.09/1.63  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.09/1.63  tff('#skF_2', type, '#skF_2': $i).
% 2.09/1.63  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.09/1.63  tff('#skF_1', type, '#skF_1': $i).
% 2.09/1.63  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.09/1.63  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.09/1.63  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.09/1.63  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.09/1.63  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.09/1.63  
% 2.38/1.65  tff(f_33, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.38/1.65  tff(f_63, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 2.38/1.65  tff(f_80, negated_conjecture, ~(![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => r1_tarski(k2_relat_1(k7_relat_1(B, k1_tarski(A))), k1_tarski(k1_funct_1(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t167_funct_1)).
% 2.38/1.65  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.38/1.65  tff(f_35, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 2.38/1.65  tff(f_49, axiom, (![A, B, C]: ~((~r2_hidden(A, B) & ~r2_hidden(C, B)) & ~r1_xboole_0(k2_tarski(A, C), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t57_zfmisc_1)).
% 2.38/1.65  tff(f_60, axiom, (![A]: (v1_relat_1(A) => (![B]: (r1_xboole_0(B, k1_relat_1(A)) => (k7_relat_1(A, B) = k1_xboole_0))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t187_relat_1)).
% 2.38/1.65  tff(f_73, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => ((r2_hidden(A, k1_relat_1(C)) & r2_hidden(B, k1_relat_1(C))) => (k9_relat_1(C, k2_tarski(A, B)) = k2_tarski(k1_funct_1(C, A), k1_funct_1(C, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t118_funct_1)).
% 2.38/1.65  tff(f_53, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_relat_1)).
% 2.38/1.65  tff(c_8, plain, (![A_3]: (r1_tarski(k1_xboole_0, A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.38/1.65  tff(c_22, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.38/1.65  tff(c_32, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.38/1.65  tff(c_30, plain, (v1_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.38/1.65  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.38/1.65  tff(c_10, plain, (![A_4]: (k2_tarski(A_4, A_4)=k1_tarski(A_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.38/1.65  tff(c_112, plain, (![A_36, C_37, B_38]: (r1_xboole_0(k2_tarski(A_36, C_37), B_38) | r2_hidden(C_37, B_38) | r2_hidden(A_36, B_38))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.38/1.65  tff(c_122, plain, (![A_39, B_40]: (r1_xboole_0(k1_tarski(A_39), B_40) | r2_hidden(A_39, B_40) | r2_hidden(A_39, B_40))), inference(superposition, [status(thm), theory('equality')], [c_10, c_112])).
% 2.38/1.65  tff(c_20, plain, (![A_15, B_17]: (k7_relat_1(A_15, B_17)=k1_xboole_0 | ~r1_xboole_0(B_17, k1_relat_1(A_15)) | ~v1_relat_1(A_15))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.38/1.65  tff(c_127, plain, (![A_15, A_39]: (k7_relat_1(A_15, k1_tarski(A_39))=k1_xboole_0 | ~v1_relat_1(A_15) | r2_hidden(A_39, k1_relat_1(A_15)))), inference(resolution, [status(thm)], [c_122, c_20])).
% 2.38/1.65  tff(c_128, plain, (![C_41, A_42, B_43]: (k2_tarski(k1_funct_1(C_41, A_42), k1_funct_1(C_41, B_43))=k9_relat_1(C_41, k2_tarski(A_42, B_43)) | ~r2_hidden(B_43, k1_relat_1(C_41)) | ~r2_hidden(A_42, k1_relat_1(C_41)) | ~v1_funct_1(C_41) | ~v1_relat_1(C_41))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.38/1.65  tff(c_138, plain, (![C_41, B_43]: (k9_relat_1(C_41, k2_tarski(B_43, B_43))=k1_tarski(k1_funct_1(C_41, B_43)) | ~r2_hidden(B_43, k1_relat_1(C_41)) | ~r2_hidden(B_43, k1_relat_1(C_41)) | ~v1_funct_1(C_41) | ~v1_relat_1(C_41))), inference(superposition, [status(thm), theory('equality')], [c_128, c_10])).
% 2.38/1.65  tff(c_240, plain, (![C_54, B_55]: (k9_relat_1(C_54, k1_tarski(B_55))=k1_tarski(k1_funct_1(C_54, B_55)) | ~r2_hidden(B_55, k1_relat_1(C_54)) | ~r2_hidden(B_55, k1_relat_1(C_54)) | ~v1_funct_1(C_54) | ~v1_relat_1(C_54))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_138])).
% 2.38/1.65  tff(c_262, plain, (![A_56, A_57]: (k9_relat_1(A_56, k1_tarski(A_57))=k1_tarski(k1_funct_1(A_56, A_57)) | ~r2_hidden(A_57, k1_relat_1(A_56)) | ~v1_funct_1(A_56) | k7_relat_1(A_56, k1_tarski(A_57))=k1_xboole_0 | ~v1_relat_1(A_56))), inference(resolution, [status(thm)], [c_127, c_240])).
% 2.38/1.65  tff(c_305, plain, (![A_62, A_63]: (k9_relat_1(A_62, k1_tarski(A_63))=k1_tarski(k1_funct_1(A_62, A_63)) | ~v1_funct_1(A_62) | k7_relat_1(A_62, k1_tarski(A_63))=k1_xboole_0 | ~v1_relat_1(A_62))), inference(resolution, [status(thm)], [c_127, c_262])).
% 2.38/1.65  tff(c_85, plain, (![B_29, A_30]: (k2_relat_1(k7_relat_1(B_29, A_30))=k9_relat_1(B_29, A_30) | ~v1_relat_1(B_29))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.38/1.65  tff(c_28, plain, (~r1_tarski(k2_relat_1(k7_relat_1('#skF_2', k1_tarski('#skF_1'))), k1_tarski(k1_funct_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.38/1.65  tff(c_91, plain, (~r1_tarski(k9_relat_1('#skF_2', k1_tarski('#skF_1')), k1_tarski(k1_funct_1('#skF_2', '#skF_1'))) | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_85, c_28])).
% 2.38/1.65  tff(c_97, plain, (~r1_tarski(k9_relat_1('#skF_2', k1_tarski('#skF_1')), k1_tarski(k1_funct_1('#skF_2', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_91])).
% 2.38/1.65  tff(c_311, plain, (~r1_tarski(k1_tarski(k1_funct_1('#skF_2', '#skF_1')), k1_tarski(k1_funct_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_2') | k7_relat_1('#skF_2', k1_tarski('#skF_1'))=k1_xboole_0 | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_305, c_97])).
% 2.38/1.65  tff(c_317, plain, (k7_relat_1('#skF_2', k1_tarski('#skF_1'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_6, c_311])).
% 2.38/1.65  tff(c_319, plain, (~r1_tarski(k2_relat_1(k1_xboole_0), k1_tarski(k1_funct_1('#skF_2', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_317, c_28])).
% 2.38/1.65  tff(c_322, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_8, c_22, c_319])).
% 2.38/1.65  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.38/1.65  
% 2.38/1.65  Inference rules
% 2.38/1.65  ----------------------
% 2.38/1.65  #Ref     : 0
% 2.38/1.65  #Sup     : 62
% 2.38/1.65  #Fact    : 4
% 2.38/1.65  #Define  : 0
% 2.38/1.65  #Split   : 1
% 2.38/1.65  #Chain   : 0
% 2.38/1.65  #Close   : 0
% 2.38/1.65  
% 2.38/1.65  Ordering : KBO
% 2.38/1.65  
% 2.38/1.65  Simplification rules
% 2.38/1.65  ----------------------
% 2.38/1.65  #Subsume      : 15
% 2.38/1.65  #Demod        : 21
% 2.38/1.65  #Tautology    : 25
% 2.38/1.65  #SimpNegUnit  : 0
% 2.38/1.65  #BackRed      : 1
% 2.38/1.65  
% 2.38/1.65  #Partial instantiations: 0
% 2.38/1.65  #Strategies tried      : 1
% 2.38/1.65  
% 2.38/1.65  Timing (in seconds)
% 2.38/1.65  ----------------------
% 2.38/1.65  Preprocessing        : 0.49
% 2.38/1.65  Parsing              : 0.34
% 2.38/1.65  CNF conversion       : 0.02
% 2.38/1.65  Main loop            : 0.22
% 2.38/1.65  Inferencing          : 0.08
% 2.38/1.65  Reduction            : 0.06
% 2.38/1.65  Demodulation         : 0.04
% 2.38/1.65  BG Simplification    : 0.01
% 2.38/1.65  Subsumption          : 0.04
% 2.38/1.65  Abstraction          : 0.01
% 2.38/1.65  MUC search           : 0.00
% 2.38/1.65  Cooper               : 0.00
% 2.38/1.65  Total                : 0.74
% 2.38/1.65  Index Insertion      : 0.00
% 2.38/1.65  Index Deletion       : 0.00
% 2.38/1.65  Index Matching       : 0.00
% 2.38/1.65  BG Taut test         : 0.00
%------------------------------------------------------------------------------
