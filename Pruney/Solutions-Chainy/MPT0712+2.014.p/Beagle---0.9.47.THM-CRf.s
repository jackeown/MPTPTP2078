%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:05:33 EST 2020

% Result     : Theorem 2.13s
% Output     : CNFRefutation 2.13s
% Verified   : 
% Statistics : Number of formulae       :   51 (  65 expanded)
%              Number of leaves         :   27 (  35 expanded)
%              Depth                    :    9
%              Number of atoms          :   79 ( 109 expanded)
%              Number of equality atoms :   26 (  32 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > v1_relat_1 > v1_funct_1 > k9_relat_1 > k7_relat_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1

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
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_53,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k2_tarski(B,C))
    <=> ~ ( A != k1_xboole_0
          & A != k1_tarski(B)
          & A != k1_tarski(C)
          & A != k2_tarski(B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l45_zfmisc_1)).

tff(f_67,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_84,negated_conjecture,(
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

tff(f_38,axiom,(
    ! [A,B] :
      ( ~ r2_hidden(A,B)
     => r1_xboole_0(k1_tarski(A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l27_zfmisc_1)).

tff(f_64,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( r1_xboole_0(B,k1_relat_1(A))
         => k7_relat_1(A,B) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t187_relat_1)).

tff(f_77,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( ( r2_hidden(A,k1_relat_1(C))
          & r2_hidden(B,k1_relat_1(C)) )
       => k9_relat_1(C,k2_tarski(A,B)) = k2_tarski(k1_funct_1(C,A),k1_funct_1(C,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t118_funct_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

tff(c_49,plain,(
    ! [A_20] : k2_tarski(A_20,A_20) = k1_tarski(A_20) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_20,plain,(
    ! [B_7,C_8] : r1_tarski(k1_xboole_0,k2_tarski(B_7,C_8)) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_54,plain,(
    ! [A_20] : r1_tarski(k1_xboole_0,k1_tarski(A_20)) ),
    inference(superposition,[status(thm),theory(equality)],[c_49,c_20])).

tff(c_26,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_36,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_34,plain,(
    v1_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_10,plain,(
    ! [A_4,B_5] :
      ( r1_xboole_0(k1_tarski(A_4),B_5)
      | r2_hidden(A_4,B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_106,plain,(
    ! [A_33,B_34] :
      ( k7_relat_1(A_33,B_34) = k1_xboole_0
      | ~ r1_xboole_0(B_34,k1_relat_1(A_33))
      | ~ v1_relat_1(A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_114,plain,(
    ! [A_33,A_4] :
      ( k7_relat_1(A_33,k1_tarski(A_4)) = k1_xboole_0
      | ~ v1_relat_1(A_33)
      | r2_hidden(A_4,k1_relat_1(A_33)) ) ),
    inference(resolution,[status(thm)],[c_10,c_106])).

tff(c_8,plain,(
    ! [A_3] : k2_tarski(A_3,A_3) = k1_tarski(A_3) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_175,plain,(
    ! [C_48,A_49,B_50] :
      ( k2_tarski(k1_funct_1(C_48,A_49),k1_funct_1(C_48,B_50)) = k9_relat_1(C_48,k2_tarski(A_49,B_50))
      | ~ r2_hidden(B_50,k1_relat_1(C_48))
      | ~ r2_hidden(A_49,k1_relat_1(C_48))
      | ~ v1_funct_1(C_48)
      | ~ v1_relat_1(C_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_200,plain,(
    ! [C_48,B_50] :
      ( k9_relat_1(C_48,k2_tarski(B_50,B_50)) = k1_tarski(k1_funct_1(C_48,B_50))
      | ~ r2_hidden(B_50,k1_relat_1(C_48))
      | ~ r2_hidden(B_50,k1_relat_1(C_48))
      | ~ v1_funct_1(C_48)
      | ~ v1_relat_1(C_48) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_175,c_8])).

tff(c_239,plain,(
    ! [C_61,B_62] :
      ( k9_relat_1(C_61,k1_tarski(B_62)) = k1_tarski(k1_funct_1(C_61,B_62))
      | ~ r2_hidden(B_62,k1_relat_1(C_61))
      | ~ r2_hidden(B_62,k1_relat_1(C_61))
      | ~ v1_funct_1(C_61)
      | ~ v1_relat_1(C_61) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_200])).

tff(c_250,plain,(
    ! [A_65,A_66] :
      ( k9_relat_1(A_65,k1_tarski(A_66)) = k1_tarski(k1_funct_1(A_65,A_66))
      | ~ r2_hidden(A_66,k1_relat_1(A_65))
      | ~ v1_funct_1(A_65)
      | k7_relat_1(A_65,k1_tarski(A_66)) = k1_xboole_0
      | ~ v1_relat_1(A_65) ) ),
    inference(resolution,[status(thm)],[c_114,c_239])).

tff(c_258,plain,(
    ! [A_67,A_68] :
      ( k9_relat_1(A_67,k1_tarski(A_68)) = k1_tarski(k1_funct_1(A_67,A_68))
      | ~ v1_funct_1(A_67)
      | k7_relat_1(A_67,k1_tarski(A_68)) = k1_xboole_0
      | ~ v1_relat_1(A_67) ) ),
    inference(resolution,[status(thm)],[c_114,c_250])).

tff(c_92,plain,(
    ! [B_31,A_32] :
      ( k2_relat_1(k7_relat_1(B_31,A_32)) = k9_relat_1(B_31,A_32)
      | ~ v1_relat_1(B_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_32,plain,(
    ~ r1_tarski(k2_relat_1(k7_relat_1('#skF_2',k1_tarski('#skF_1'))),k1_tarski(k1_funct_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_98,plain,
    ( ~ r1_tarski(k9_relat_1('#skF_2',k1_tarski('#skF_1')),k1_tarski(k1_funct_1('#skF_2','#skF_1')))
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_92,c_32])).

tff(c_104,plain,(
    ~ r1_tarski(k9_relat_1('#skF_2',k1_tarski('#skF_1')),k1_tarski(k1_funct_1('#skF_2','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_98])).

tff(c_273,plain,
    ( ~ r1_tarski(k1_tarski(k1_funct_1('#skF_2','#skF_1')),k1_tarski(k1_funct_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_2')
    | k7_relat_1('#skF_2',k1_tarski('#skF_1')) = k1_xboole_0
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_258,c_104])).

tff(c_281,plain,(
    k7_relat_1('#skF_2',k1_tarski('#skF_1')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_6,c_273])).

tff(c_293,plain,(
    ~ r1_tarski(k2_relat_1(k1_xboole_0),k1_tarski(k1_funct_1('#skF_2','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_281,c_32])).

tff(c_296,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_26,c_293])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n021.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 13:55:49 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.13/1.28  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.13/1.28  
% 2.13/1.28  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.13/1.28  %$ r2_hidden > r1_xboole_0 > r1_tarski > v1_relat_1 > v1_funct_1 > k9_relat_1 > k7_relat_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1
% 2.13/1.28  
% 2.13/1.28  %Foreground sorts:
% 2.13/1.28  
% 2.13/1.28  
% 2.13/1.28  %Background operators:
% 2.13/1.28  
% 2.13/1.28  
% 2.13/1.28  %Foreground operators:
% 2.13/1.28  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.13/1.28  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.13/1.28  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.13/1.28  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.13/1.28  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.13/1.28  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.13/1.28  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.13/1.28  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.13/1.28  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.13/1.28  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.13/1.28  tff('#skF_2', type, '#skF_2': $i).
% 2.13/1.28  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.13/1.28  tff('#skF_1', type, '#skF_1': $i).
% 2.13/1.28  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.13/1.28  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.13/1.28  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.13/1.28  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.13/1.28  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.13/1.28  
% 2.13/1.30  tff(f_33, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 2.13/1.30  tff(f_53, axiom, (![A, B, C]: (r1_tarski(A, k2_tarski(B, C)) <=> ~(((~(A = k1_xboole_0) & ~(A = k1_tarski(B))) & ~(A = k1_tarski(C))) & ~(A = k2_tarski(B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l45_zfmisc_1)).
% 2.13/1.30  tff(f_67, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 2.13/1.30  tff(f_84, negated_conjecture, ~(![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => r1_tarski(k2_relat_1(k7_relat_1(B, k1_tarski(A))), k1_tarski(k1_funct_1(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t167_funct_1)).
% 2.13/1.30  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.13/1.30  tff(f_38, axiom, (![A, B]: (~r2_hidden(A, B) => r1_xboole_0(k1_tarski(A), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 2.13/1.30  tff(f_64, axiom, (![A]: (v1_relat_1(A) => (![B]: (r1_xboole_0(B, k1_relat_1(A)) => (k7_relat_1(A, B) = k1_xboole_0))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t187_relat_1)).
% 2.13/1.30  tff(f_77, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => ((r2_hidden(A, k1_relat_1(C)) & r2_hidden(B, k1_relat_1(C))) => (k9_relat_1(C, k2_tarski(A, B)) = k2_tarski(k1_funct_1(C, A), k1_funct_1(C, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t118_funct_1)).
% 2.13/1.30  tff(f_57, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_relat_1)).
% 2.13/1.30  tff(c_49, plain, (![A_20]: (k2_tarski(A_20, A_20)=k1_tarski(A_20))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.13/1.30  tff(c_20, plain, (![B_7, C_8]: (r1_tarski(k1_xboole_0, k2_tarski(B_7, C_8)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.13/1.30  tff(c_54, plain, (![A_20]: (r1_tarski(k1_xboole_0, k1_tarski(A_20)))), inference(superposition, [status(thm), theory('equality')], [c_49, c_20])).
% 2.13/1.30  tff(c_26, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.13/1.30  tff(c_36, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.13/1.30  tff(c_34, plain, (v1_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.13/1.30  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.13/1.30  tff(c_10, plain, (![A_4, B_5]: (r1_xboole_0(k1_tarski(A_4), B_5) | r2_hidden(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.13/1.30  tff(c_106, plain, (![A_33, B_34]: (k7_relat_1(A_33, B_34)=k1_xboole_0 | ~r1_xboole_0(B_34, k1_relat_1(A_33)) | ~v1_relat_1(A_33))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.13/1.30  tff(c_114, plain, (![A_33, A_4]: (k7_relat_1(A_33, k1_tarski(A_4))=k1_xboole_0 | ~v1_relat_1(A_33) | r2_hidden(A_4, k1_relat_1(A_33)))), inference(resolution, [status(thm)], [c_10, c_106])).
% 2.13/1.30  tff(c_8, plain, (![A_3]: (k2_tarski(A_3, A_3)=k1_tarski(A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.13/1.30  tff(c_175, plain, (![C_48, A_49, B_50]: (k2_tarski(k1_funct_1(C_48, A_49), k1_funct_1(C_48, B_50))=k9_relat_1(C_48, k2_tarski(A_49, B_50)) | ~r2_hidden(B_50, k1_relat_1(C_48)) | ~r2_hidden(A_49, k1_relat_1(C_48)) | ~v1_funct_1(C_48) | ~v1_relat_1(C_48))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.13/1.30  tff(c_200, plain, (![C_48, B_50]: (k9_relat_1(C_48, k2_tarski(B_50, B_50))=k1_tarski(k1_funct_1(C_48, B_50)) | ~r2_hidden(B_50, k1_relat_1(C_48)) | ~r2_hidden(B_50, k1_relat_1(C_48)) | ~v1_funct_1(C_48) | ~v1_relat_1(C_48))), inference(superposition, [status(thm), theory('equality')], [c_175, c_8])).
% 2.13/1.30  tff(c_239, plain, (![C_61, B_62]: (k9_relat_1(C_61, k1_tarski(B_62))=k1_tarski(k1_funct_1(C_61, B_62)) | ~r2_hidden(B_62, k1_relat_1(C_61)) | ~r2_hidden(B_62, k1_relat_1(C_61)) | ~v1_funct_1(C_61) | ~v1_relat_1(C_61))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_200])).
% 2.13/1.30  tff(c_250, plain, (![A_65, A_66]: (k9_relat_1(A_65, k1_tarski(A_66))=k1_tarski(k1_funct_1(A_65, A_66)) | ~r2_hidden(A_66, k1_relat_1(A_65)) | ~v1_funct_1(A_65) | k7_relat_1(A_65, k1_tarski(A_66))=k1_xboole_0 | ~v1_relat_1(A_65))), inference(resolution, [status(thm)], [c_114, c_239])).
% 2.13/1.30  tff(c_258, plain, (![A_67, A_68]: (k9_relat_1(A_67, k1_tarski(A_68))=k1_tarski(k1_funct_1(A_67, A_68)) | ~v1_funct_1(A_67) | k7_relat_1(A_67, k1_tarski(A_68))=k1_xboole_0 | ~v1_relat_1(A_67))), inference(resolution, [status(thm)], [c_114, c_250])).
% 2.13/1.30  tff(c_92, plain, (![B_31, A_32]: (k2_relat_1(k7_relat_1(B_31, A_32))=k9_relat_1(B_31, A_32) | ~v1_relat_1(B_31))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.13/1.30  tff(c_32, plain, (~r1_tarski(k2_relat_1(k7_relat_1('#skF_2', k1_tarski('#skF_1'))), k1_tarski(k1_funct_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.13/1.30  tff(c_98, plain, (~r1_tarski(k9_relat_1('#skF_2', k1_tarski('#skF_1')), k1_tarski(k1_funct_1('#skF_2', '#skF_1'))) | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_92, c_32])).
% 2.13/1.30  tff(c_104, plain, (~r1_tarski(k9_relat_1('#skF_2', k1_tarski('#skF_1')), k1_tarski(k1_funct_1('#skF_2', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_98])).
% 2.13/1.30  tff(c_273, plain, (~r1_tarski(k1_tarski(k1_funct_1('#skF_2', '#skF_1')), k1_tarski(k1_funct_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_2') | k7_relat_1('#skF_2', k1_tarski('#skF_1'))=k1_xboole_0 | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_258, c_104])).
% 2.13/1.30  tff(c_281, plain, (k7_relat_1('#skF_2', k1_tarski('#skF_1'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_6, c_273])).
% 2.13/1.30  tff(c_293, plain, (~r1_tarski(k2_relat_1(k1_xboole_0), k1_tarski(k1_funct_1('#skF_2', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_281, c_32])).
% 2.13/1.30  tff(c_296, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_54, c_26, c_293])).
% 2.13/1.30  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.13/1.30  
% 2.13/1.30  Inference rules
% 2.13/1.30  ----------------------
% 2.13/1.30  #Ref     : 0
% 2.13/1.30  #Sup     : 62
% 2.13/1.30  #Fact    : 0
% 2.13/1.30  #Define  : 0
% 2.13/1.30  #Split   : 1
% 2.13/1.30  #Chain   : 0
% 2.13/1.30  #Close   : 0
% 2.13/1.30  
% 2.13/1.30  Ordering : KBO
% 2.13/1.30  
% 2.13/1.30  Simplification rules
% 2.13/1.30  ----------------------
% 2.13/1.30  #Subsume      : 8
% 2.13/1.30  #Demod        : 23
% 2.13/1.30  #Tautology    : 27
% 2.13/1.30  #SimpNegUnit  : 0
% 2.13/1.30  #BackRed      : 1
% 2.13/1.30  
% 2.13/1.30  #Partial instantiations: 0
% 2.13/1.30  #Strategies tried      : 1
% 2.13/1.30  
% 2.13/1.30  Timing (in seconds)
% 2.13/1.30  ----------------------
% 2.13/1.30  Preprocessing        : 0.31
% 2.13/1.30  Parsing              : 0.16
% 2.13/1.30  CNF conversion       : 0.02
% 2.13/1.30  Main loop            : 0.24
% 2.13/1.30  Inferencing          : 0.09
% 2.13/1.30  Reduction            : 0.07
% 2.13/1.30  Demodulation         : 0.05
% 2.13/1.30  BG Simplification    : 0.01
% 2.13/1.30  Subsumption          : 0.05
% 2.13/1.30  Abstraction          : 0.02
% 2.13/1.30  MUC search           : 0.00
% 2.13/1.30  Cooper               : 0.00
% 2.13/1.30  Total                : 0.58
% 2.13/1.30  Index Insertion      : 0.00
% 2.13/1.30  Index Deletion       : 0.00
% 2.13/1.30  Index Matching       : 0.00
% 2.13/1.30  BG Taut test         : 0.00
%------------------------------------------------------------------------------
