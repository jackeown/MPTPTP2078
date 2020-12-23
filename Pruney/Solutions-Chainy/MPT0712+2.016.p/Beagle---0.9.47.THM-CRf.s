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

% Result     : Theorem 1.82s
% Output     : CNFRefutation 1.82s
% Verified   : 
% Statistics : Number of formulae       :   50 (  63 expanded)
%              Number of leaves         :   28 (  35 expanded)
%              Depth                    :    9
%              Number of atoms          :   73 ( 102 expanded)
%              Number of equality atoms :   21 (  26 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > v1_relat_1 > v1_funct_1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1

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

tff(f_56,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_73,negated_conjecture,(
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

tff(f_42,axiom,(
    ! [A,B] :
      ( ~ r2_hidden(A,B)
     => r1_xboole_0(k1_tarski(A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l27_zfmisc_1)).

tff(f_53,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( r1_xboole_0(B,k1_relat_1(A))
         => k7_relat_1(A,B) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t187_relat_1)).

tff(f_35,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_66,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( ( r2_hidden(A,k1_relat_1(C))
          & r2_hidden(B,k1_relat_1(C)) )
       => k9_relat_1(C,k2_tarski(A,B)) = k2_tarski(k1_funct_1(C,A),k1_funct_1(C,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t118_funct_1)).

tff(f_46,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

tff(c_8,plain,(
    ! [A_3] : r1_tarski(k1_xboole_0,A_3) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_20,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_30,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_28,plain,(
    v1_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_14,plain,(
    ! [A_7,B_8] :
      ( r1_xboole_0(k1_tarski(A_7),B_8)
      | r2_hidden(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_98,plain,(
    ! [A_29,B_30] :
      ( k7_relat_1(A_29,B_30) = k1_xboole_0
      | ~ r1_xboole_0(B_30,k1_relat_1(A_29))
      | ~ v1_relat_1(A_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_106,plain,(
    ! [A_29,A_7] :
      ( k7_relat_1(A_29,k1_tarski(A_7)) = k1_xboole_0
      | ~ v1_relat_1(A_29)
      | r2_hidden(A_7,k1_relat_1(A_29)) ) ),
    inference(resolution,[status(thm)],[c_14,c_98])).

tff(c_10,plain,(
    ! [A_4] : k2_tarski(A_4,A_4) = k1_tarski(A_4) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_107,plain,(
    ! [C_31,A_32,B_33] :
      ( k2_tarski(k1_funct_1(C_31,A_32),k1_funct_1(C_31,B_33)) = k9_relat_1(C_31,k2_tarski(A_32,B_33))
      | ~ r2_hidden(B_33,k1_relat_1(C_31))
      | ~ r2_hidden(A_32,k1_relat_1(C_31))
      | ~ v1_funct_1(C_31)
      | ~ v1_relat_1(C_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_114,plain,(
    ! [C_31,B_33] :
      ( k9_relat_1(C_31,k2_tarski(B_33,B_33)) = k1_tarski(k1_funct_1(C_31,B_33))
      | ~ r2_hidden(B_33,k1_relat_1(C_31))
      | ~ r2_hidden(B_33,k1_relat_1(C_31))
      | ~ v1_funct_1(C_31)
      | ~ v1_relat_1(C_31) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_107,c_10])).

tff(c_131,plain,(
    ! [C_36,B_37] :
      ( k9_relat_1(C_36,k1_tarski(B_37)) = k1_tarski(k1_funct_1(C_36,B_37))
      | ~ r2_hidden(B_37,k1_relat_1(C_36))
      | ~ r2_hidden(B_37,k1_relat_1(C_36))
      | ~ v1_funct_1(C_36)
      | ~ v1_relat_1(C_36) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_114])).

tff(c_138,plain,(
    ! [A_38,A_39] :
      ( k9_relat_1(A_38,k1_tarski(A_39)) = k1_tarski(k1_funct_1(A_38,A_39))
      | ~ r2_hidden(A_39,k1_relat_1(A_38))
      | ~ v1_funct_1(A_38)
      | k7_relat_1(A_38,k1_tarski(A_39)) = k1_xboole_0
      | ~ v1_relat_1(A_38) ) ),
    inference(resolution,[status(thm)],[c_106,c_131])).

tff(c_146,plain,(
    ! [A_40,A_41] :
      ( k9_relat_1(A_40,k1_tarski(A_41)) = k1_tarski(k1_funct_1(A_40,A_41))
      | ~ v1_funct_1(A_40)
      | k7_relat_1(A_40,k1_tarski(A_41)) = k1_xboole_0
      | ~ v1_relat_1(A_40) ) ),
    inference(resolution,[status(thm)],[c_106,c_138])).

tff(c_84,plain,(
    ! [B_27,A_28] :
      ( k2_relat_1(k7_relat_1(B_27,A_28)) = k9_relat_1(B_27,A_28)
      | ~ v1_relat_1(B_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_26,plain,(
    ~ r1_tarski(k2_relat_1(k7_relat_1('#skF_2',k1_tarski('#skF_1'))),k1_tarski(k1_funct_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_90,plain,
    ( ~ r1_tarski(k9_relat_1('#skF_2',k1_tarski('#skF_1')),k1_tarski(k1_funct_1('#skF_2','#skF_1')))
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_84,c_26])).

tff(c_96,plain,(
    ~ r1_tarski(k9_relat_1('#skF_2',k1_tarski('#skF_1')),k1_tarski(k1_funct_1('#skF_2','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_90])).

tff(c_152,plain,
    ( ~ r1_tarski(k1_tarski(k1_funct_1('#skF_2','#skF_1')),k1_tarski(k1_funct_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_2')
    | k7_relat_1('#skF_2',k1_tarski('#skF_1')) = k1_xboole_0
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_146,c_96])).

tff(c_158,plain,(
    k7_relat_1('#skF_2',k1_tarski('#skF_1')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_6,c_152])).

tff(c_160,plain,(
    ~ r1_tarski(k2_relat_1(k1_xboole_0),k1_tarski(k1_funct_1('#skF_2','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_158,c_26])).

tff(c_163,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_20,c_160])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n010.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 14:44:29 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.82/1.18  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.82/1.19  
% 1.82/1.19  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.82/1.19  %$ r2_hidden > r1_xboole_0 > r1_tarski > v1_relat_1 > v1_funct_1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1
% 1.82/1.19  
% 1.82/1.19  %Foreground sorts:
% 1.82/1.19  
% 1.82/1.19  
% 1.82/1.19  %Background operators:
% 1.82/1.19  
% 1.82/1.19  
% 1.82/1.19  %Foreground operators:
% 1.82/1.19  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 1.82/1.19  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.82/1.19  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.82/1.19  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.82/1.19  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 1.82/1.19  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.82/1.19  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.82/1.19  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.82/1.19  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.82/1.19  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.82/1.19  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.82/1.19  tff('#skF_2', type, '#skF_2': $i).
% 1.82/1.19  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 1.82/1.19  tff('#skF_1', type, '#skF_1': $i).
% 1.82/1.19  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 1.82/1.19  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.82/1.19  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.82/1.19  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.82/1.19  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.82/1.19  
% 1.82/1.20  tff(f_33, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 1.82/1.20  tff(f_56, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 1.82/1.20  tff(f_73, negated_conjecture, ~(![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => r1_tarski(k2_relat_1(k7_relat_1(B, k1_tarski(A))), k1_tarski(k1_funct_1(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t167_funct_1)).
% 1.82/1.20  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 1.82/1.20  tff(f_42, axiom, (![A, B]: (~r2_hidden(A, B) => r1_xboole_0(k1_tarski(A), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 1.82/1.20  tff(f_53, axiom, (![A]: (v1_relat_1(A) => (![B]: (r1_xboole_0(B, k1_relat_1(A)) => (k7_relat_1(A, B) = k1_xboole_0))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t187_relat_1)).
% 1.82/1.20  tff(f_35, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 1.82/1.20  tff(f_66, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => ((r2_hidden(A, k1_relat_1(C)) & r2_hidden(B, k1_relat_1(C))) => (k9_relat_1(C, k2_tarski(A, B)) = k2_tarski(k1_funct_1(C, A), k1_funct_1(C, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t118_funct_1)).
% 1.82/1.20  tff(f_46, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_relat_1)).
% 1.82/1.20  tff(c_8, plain, (![A_3]: (r1_tarski(k1_xboole_0, A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.82/1.20  tff(c_20, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_56])).
% 1.82/1.20  tff(c_30, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_73])).
% 1.82/1.20  tff(c_28, plain, (v1_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_73])).
% 1.82/1.20  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.82/1.20  tff(c_14, plain, (![A_7, B_8]: (r1_xboole_0(k1_tarski(A_7), B_8) | r2_hidden(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.82/1.20  tff(c_98, plain, (![A_29, B_30]: (k7_relat_1(A_29, B_30)=k1_xboole_0 | ~r1_xboole_0(B_30, k1_relat_1(A_29)) | ~v1_relat_1(A_29))), inference(cnfTransformation, [status(thm)], [f_53])).
% 1.82/1.20  tff(c_106, plain, (![A_29, A_7]: (k7_relat_1(A_29, k1_tarski(A_7))=k1_xboole_0 | ~v1_relat_1(A_29) | r2_hidden(A_7, k1_relat_1(A_29)))), inference(resolution, [status(thm)], [c_14, c_98])).
% 1.82/1.20  tff(c_10, plain, (![A_4]: (k2_tarski(A_4, A_4)=k1_tarski(A_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.82/1.20  tff(c_107, plain, (![C_31, A_32, B_33]: (k2_tarski(k1_funct_1(C_31, A_32), k1_funct_1(C_31, B_33))=k9_relat_1(C_31, k2_tarski(A_32, B_33)) | ~r2_hidden(B_33, k1_relat_1(C_31)) | ~r2_hidden(A_32, k1_relat_1(C_31)) | ~v1_funct_1(C_31) | ~v1_relat_1(C_31))), inference(cnfTransformation, [status(thm)], [f_66])).
% 1.82/1.20  tff(c_114, plain, (![C_31, B_33]: (k9_relat_1(C_31, k2_tarski(B_33, B_33))=k1_tarski(k1_funct_1(C_31, B_33)) | ~r2_hidden(B_33, k1_relat_1(C_31)) | ~r2_hidden(B_33, k1_relat_1(C_31)) | ~v1_funct_1(C_31) | ~v1_relat_1(C_31))), inference(superposition, [status(thm), theory('equality')], [c_107, c_10])).
% 1.82/1.20  tff(c_131, plain, (![C_36, B_37]: (k9_relat_1(C_36, k1_tarski(B_37))=k1_tarski(k1_funct_1(C_36, B_37)) | ~r2_hidden(B_37, k1_relat_1(C_36)) | ~r2_hidden(B_37, k1_relat_1(C_36)) | ~v1_funct_1(C_36) | ~v1_relat_1(C_36))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_114])).
% 1.82/1.20  tff(c_138, plain, (![A_38, A_39]: (k9_relat_1(A_38, k1_tarski(A_39))=k1_tarski(k1_funct_1(A_38, A_39)) | ~r2_hidden(A_39, k1_relat_1(A_38)) | ~v1_funct_1(A_38) | k7_relat_1(A_38, k1_tarski(A_39))=k1_xboole_0 | ~v1_relat_1(A_38))), inference(resolution, [status(thm)], [c_106, c_131])).
% 1.82/1.20  tff(c_146, plain, (![A_40, A_41]: (k9_relat_1(A_40, k1_tarski(A_41))=k1_tarski(k1_funct_1(A_40, A_41)) | ~v1_funct_1(A_40) | k7_relat_1(A_40, k1_tarski(A_41))=k1_xboole_0 | ~v1_relat_1(A_40))), inference(resolution, [status(thm)], [c_106, c_138])).
% 1.82/1.20  tff(c_84, plain, (![B_27, A_28]: (k2_relat_1(k7_relat_1(B_27, A_28))=k9_relat_1(B_27, A_28) | ~v1_relat_1(B_27))), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.82/1.20  tff(c_26, plain, (~r1_tarski(k2_relat_1(k7_relat_1('#skF_2', k1_tarski('#skF_1'))), k1_tarski(k1_funct_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_73])).
% 1.82/1.20  tff(c_90, plain, (~r1_tarski(k9_relat_1('#skF_2', k1_tarski('#skF_1')), k1_tarski(k1_funct_1('#skF_2', '#skF_1'))) | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_84, c_26])).
% 1.82/1.20  tff(c_96, plain, (~r1_tarski(k9_relat_1('#skF_2', k1_tarski('#skF_1')), k1_tarski(k1_funct_1('#skF_2', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_90])).
% 1.82/1.20  tff(c_152, plain, (~r1_tarski(k1_tarski(k1_funct_1('#skF_2', '#skF_1')), k1_tarski(k1_funct_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_2') | k7_relat_1('#skF_2', k1_tarski('#skF_1'))=k1_xboole_0 | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_146, c_96])).
% 1.82/1.20  tff(c_158, plain, (k7_relat_1('#skF_2', k1_tarski('#skF_1'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_6, c_152])).
% 1.82/1.20  tff(c_160, plain, (~r1_tarski(k2_relat_1(k1_xboole_0), k1_tarski(k1_funct_1('#skF_2', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_158, c_26])).
% 1.82/1.20  tff(c_163, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_8, c_20, c_160])).
% 1.82/1.20  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.82/1.20  
% 1.82/1.20  Inference rules
% 1.82/1.20  ----------------------
% 1.82/1.20  #Ref     : 0
% 1.82/1.20  #Sup     : 29
% 1.82/1.20  #Fact    : 0
% 1.82/1.20  #Define  : 0
% 1.82/1.20  #Split   : 1
% 1.82/1.20  #Chain   : 0
% 1.82/1.20  #Close   : 0
% 1.82/1.20  
% 1.82/1.20  Ordering : KBO
% 1.82/1.20  
% 1.82/1.20  Simplification rules
% 1.82/1.20  ----------------------
% 1.82/1.20  #Subsume      : 5
% 1.82/1.20  #Demod        : 12
% 1.82/1.20  #Tautology    : 18
% 1.82/1.20  #SimpNegUnit  : 0
% 1.82/1.20  #BackRed      : 1
% 1.82/1.20  
% 1.82/1.20  #Partial instantiations: 0
% 1.82/1.20  #Strategies tried      : 1
% 1.82/1.20  
% 1.82/1.20  Timing (in seconds)
% 1.82/1.20  ----------------------
% 1.82/1.21  Preprocessing        : 0.28
% 1.82/1.21  Parsing              : 0.15
% 1.82/1.21  CNF conversion       : 0.02
% 1.82/1.21  Main loop            : 0.14
% 1.82/1.21  Inferencing          : 0.06
% 1.82/1.21  Reduction            : 0.04
% 1.82/1.21  Demodulation         : 0.03
% 1.82/1.21  BG Simplification    : 0.01
% 1.82/1.21  Subsumption          : 0.02
% 1.82/1.21  Abstraction          : 0.01
% 1.82/1.21  MUC search           : 0.00
% 1.82/1.21  Cooper               : 0.00
% 1.82/1.21  Total                : 0.46
% 1.82/1.21  Index Insertion      : 0.00
% 1.82/1.21  Index Deletion       : 0.00
% 1.82/1.21  Index Matching       : 0.00
% 1.82/1.21  BG Taut test         : 0.00
%------------------------------------------------------------------------------
