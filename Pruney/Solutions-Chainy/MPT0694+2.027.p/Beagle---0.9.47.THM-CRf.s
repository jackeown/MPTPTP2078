%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:04:56 EST 2020

% Result     : Theorem 2.20s
% Output     : CNFRefutation 2.47s
% Verified   : 
% Statistics : Number of formulae       :   44 (  62 expanded)
%              Number of leaves         :   21 (  31 expanded)
%              Depth                    :    6
%              Number of atoms          :   55 (  90 expanded)
%              Number of equality atoms :    4 (   8 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > v1_funct_1 > k9_relat_1 > k3_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_56,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_relat_1(C)
          & v1_funct_1(C) )
       => r1_tarski(k9_relat_1(C,k3_xboole_0(A,k10_relat_1(C,B))),k3_xboole_0(k9_relat_1(C,A),B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t149_funct_1)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => r1_tarski(k9_relat_1(C,k3_xboole_0(A,B)),k3_xboole_0(k9_relat_1(C,A),k9_relat_1(C,B))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t154_relat_1)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k3_xboole_0(B,C))
     => r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_49,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => k9_relat_1(B,k10_relat_1(B,A)) = k3_xboole_0(A,k9_relat_1(B,k1_relat_1(B))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_funct_1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(A,C) )
     => r1_tarski(A,k3_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_xboole_1)).

tff(c_18,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_370,plain,(
    ! [C_56,A_57,B_58] :
      ( r1_tarski(k9_relat_1(C_56,k3_xboole_0(A_57,B_58)),k3_xboole_0(k9_relat_1(C_56,A_57),k9_relat_1(C_56,B_58)))
      | ~ v1_relat_1(C_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_4,plain,(
    ! [A_3,B_4,C_5] :
      ( r1_tarski(A_3,B_4)
      | ~ r1_tarski(A_3,k3_xboole_0(B_4,C_5)) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_398,plain,(
    ! [C_59,A_60,B_61] :
      ( r1_tarski(k9_relat_1(C_59,k3_xboole_0(A_60,B_61)),k9_relat_1(C_59,A_60))
      | ~ v1_relat_1(C_59) ) ),
    inference(resolution,[status(thm)],[c_370,c_4])).

tff(c_16,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_129,plain,(
    ! [C_34,A_35,B_36] :
      ( r1_tarski(k9_relat_1(C_34,k3_xboole_0(A_35,B_36)),k3_xboole_0(k9_relat_1(C_34,A_35),k9_relat_1(C_34,B_36)))
      | ~ v1_relat_1(C_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_62,plain,(
    ! [A_20,B_21,C_22] :
      ( r1_tarski(A_20,B_21)
      | ~ r1_tarski(A_20,k3_xboole_0(B_21,C_22)) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_65,plain,(
    ! [A_20,A_1,B_2] :
      ( r1_tarski(A_20,A_1)
      | ~ r1_tarski(A_20,k3_xboole_0(B_2,A_1)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_62])).

tff(c_222,plain,(
    ! [C_42,A_43,B_44] :
      ( r1_tarski(k9_relat_1(C_42,k3_xboole_0(A_43,B_44)),k9_relat_1(C_42,B_44))
      | ~ v1_relat_1(C_42) ) ),
    inference(resolution,[status(thm)],[c_129,c_65])).

tff(c_96,plain,(
    ! [A_29,B_30] :
      ( k3_xboole_0(A_29,k9_relat_1(B_30,k1_relat_1(B_30))) = k9_relat_1(B_30,k10_relat_1(B_30,A_29))
      | ~ v1_funct_1(B_30)
      | ~ v1_relat_1(B_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_108,plain,(
    ! [A_3,A_29,B_30] :
      ( r1_tarski(A_3,A_29)
      | ~ r1_tarski(A_3,k9_relat_1(B_30,k10_relat_1(B_30,A_29)))
      | ~ v1_funct_1(B_30)
      | ~ v1_relat_1(B_30) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_96,c_4])).

tff(c_303,plain,(
    ! [C_51,A_52,A_53] :
      ( r1_tarski(k9_relat_1(C_51,k3_xboole_0(A_52,k10_relat_1(C_51,A_53))),A_53)
      | ~ v1_funct_1(C_51)
      | ~ v1_relat_1(C_51) ) ),
    inference(resolution,[status(thm)],[c_222,c_108])).

tff(c_6,plain,(
    ! [A_6,B_7,C_8] :
      ( r1_tarski(A_6,k3_xboole_0(B_7,C_8))
      | ~ r1_tarski(A_6,C_8)
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_14,plain,(
    ~ r1_tarski(k9_relat_1('#skF_3',k3_xboole_0('#skF_1',k10_relat_1('#skF_3','#skF_2'))),k3_xboole_0(k9_relat_1('#skF_3','#skF_1'),'#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_19,plain,(
    ~ r1_tarski(k9_relat_1('#skF_3',k3_xboole_0('#skF_1',k10_relat_1('#skF_3','#skF_2'))),k3_xboole_0('#skF_2',k9_relat_1('#skF_3','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_14])).

tff(c_94,plain,
    ( ~ r1_tarski(k9_relat_1('#skF_3',k3_xboole_0('#skF_1',k10_relat_1('#skF_3','#skF_2'))),k9_relat_1('#skF_3','#skF_1'))
    | ~ r1_tarski(k9_relat_1('#skF_3',k3_xboole_0('#skF_1',k10_relat_1('#skF_3','#skF_2'))),'#skF_2') ),
    inference(resolution,[status(thm)],[c_6,c_19])).

tff(c_95,plain,(
    ~ r1_tarski(k9_relat_1('#skF_3',k3_xboole_0('#skF_1',k10_relat_1('#skF_3','#skF_2'))),'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_94])).

tff(c_310,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_303,c_95])).

tff(c_335,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_16,c_310])).

tff(c_336,plain,(
    ~ r1_tarski(k9_relat_1('#skF_3',k3_xboole_0('#skF_1',k10_relat_1('#skF_3','#skF_2'))),k9_relat_1('#skF_3','#skF_1')) ),
    inference(splitRight,[status(thm)],[c_94])).

tff(c_401,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_398,c_336])).

tff(c_414,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_401])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:52:07 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.20/1.43  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.20/1.43  
% 2.20/1.43  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.47/1.44  %$ r1_tarski > v1_relat_1 > v1_funct_1 > k9_relat_1 > k3_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 2.47/1.44  
% 2.47/1.44  %Foreground sorts:
% 2.47/1.44  
% 2.47/1.44  
% 2.47/1.44  %Background operators:
% 2.47/1.44  
% 2.47/1.44  
% 2.47/1.44  %Foreground operators:
% 2.47/1.44  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.47/1.44  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.47/1.44  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.47/1.44  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.47/1.44  tff('#skF_2', type, '#skF_2': $i).
% 2.47/1.44  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.47/1.44  tff('#skF_3', type, '#skF_3': $i).
% 2.47/1.44  tff('#skF_1', type, '#skF_1': $i).
% 2.47/1.44  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.47/1.44  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 2.47/1.44  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.47/1.44  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.47/1.44  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.47/1.44  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.47/1.44  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.47/1.44  
% 2.47/1.45  tff(f_56, negated_conjecture, ~(![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => r1_tarski(k9_relat_1(C, k3_xboole_0(A, k10_relat_1(C, B))), k3_xboole_0(k9_relat_1(C, A), B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t149_funct_1)).
% 2.47/1.45  tff(f_43, axiom, (![A, B, C]: (v1_relat_1(C) => r1_tarski(k9_relat_1(C, k3_xboole_0(A, B)), k3_xboole_0(k9_relat_1(C, A), k9_relat_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t154_relat_1)).
% 2.47/1.45  tff(f_31, axiom, (![A, B, C]: (r1_tarski(A, k3_xboole_0(B, C)) => r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t18_xboole_1)).
% 2.47/1.45  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 2.47/1.45  tff(f_49, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (k9_relat_1(B, k10_relat_1(B, A)) = k3_xboole_0(A, k9_relat_1(B, k1_relat_1(B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_funct_1)).
% 2.47/1.45  tff(f_37, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(A, C)) => r1_tarski(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t19_xboole_1)).
% 2.47/1.45  tff(c_18, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.47/1.45  tff(c_370, plain, (![C_56, A_57, B_58]: (r1_tarski(k9_relat_1(C_56, k3_xboole_0(A_57, B_58)), k3_xboole_0(k9_relat_1(C_56, A_57), k9_relat_1(C_56, B_58))) | ~v1_relat_1(C_56))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.47/1.45  tff(c_4, plain, (![A_3, B_4, C_5]: (r1_tarski(A_3, B_4) | ~r1_tarski(A_3, k3_xboole_0(B_4, C_5)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.47/1.45  tff(c_398, plain, (![C_59, A_60, B_61]: (r1_tarski(k9_relat_1(C_59, k3_xboole_0(A_60, B_61)), k9_relat_1(C_59, A_60)) | ~v1_relat_1(C_59))), inference(resolution, [status(thm)], [c_370, c_4])).
% 2.47/1.45  tff(c_16, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.47/1.45  tff(c_129, plain, (![C_34, A_35, B_36]: (r1_tarski(k9_relat_1(C_34, k3_xboole_0(A_35, B_36)), k3_xboole_0(k9_relat_1(C_34, A_35), k9_relat_1(C_34, B_36))) | ~v1_relat_1(C_34))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.47/1.45  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.47/1.45  tff(c_62, plain, (![A_20, B_21, C_22]: (r1_tarski(A_20, B_21) | ~r1_tarski(A_20, k3_xboole_0(B_21, C_22)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.47/1.45  tff(c_65, plain, (![A_20, A_1, B_2]: (r1_tarski(A_20, A_1) | ~r1_tarski(A_20, k3_xboole_0(B_2, A_1)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_62])).
% 2.47/1.45  tff(c_222, plain, (![C_42, A_43, B_44]: (r1_tarski(k9_relat_1(C_42, k3_xboole_0(A_43, B_44)), k9_relat_1(C_42, B_44)) | ~v1_relat_1(C_42))), inference(resolution, [status(thm)], [c_129, c_65])).
% 2.47/1.45  tff(c_96, plain, (![A_29, B_30]: (k3_xboole_0(A_29, k9_relat_1(B_30, k1_relat_1(B_30)))=k9_relat_1(B_30, k10_relat_1(B_30, A_29)) | ~v1_funct_1(B_30) | ~v1_relat_1(B_30))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.47/1.45  tff(c_108, plain, (![A_3, A_29, B_30]: (r1_tarski(A_3, A_29) | ~r1_tarski(A_3, k9_relat_1(B_30, k10_relat_1(B_30, A_29))) | ~v1_funct_1(B_30) | ~v1_relat_1(B_30))), inference(superposition, [status(thm), theory('equality')], [c_96, c_4])).
% 2.47/1.45  tff(c_303, plain, (![C_51, A_52, A_53]: (r1_tarski(k9_relat_1(C_51, k3_xboole_0(A_52, k10_relat_1(C_51, A_53))), A_53) | ~v1_funct_1(C_51) | ~v1_relat_1(C_51))), inference(resolution, [status(thm)], [c_222, c_108])).
% 2.47/1.45  tff(c_6, plain, (![A_6, B_7, C_8]: (r1_tarski(A_6, k3_xboole_0(B_7, C_8)) | ~r1_tarski(A_6, C_8) | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.47/1.45  tff(c_14, plain, (~r1_tarski(k9_relat_1('#skF_3', k3_xboole_0('#skF_1', k10_relat_1('#skF_3', '#skF_2'))), k3_xboole_0(k9_relat_1('#skF_3', '#skF_1'), '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.47/1.45  tff(c_19, plain, (~r1_tarski(k9_relat_1('#skF_3', k3_xboole_0('#skF_1', k10_relat_1('#skF_3', '#skF_2'))), k3_xboole_0('#skF_2', k9_relat_1('#skF_3', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_14])).
% 2.47/1.45  tff(c_94, plain, (~r1_tarski(k9_relat_1('#skF_3', k3_xboole_0('#skF_1', k10_relat_1('#skF_3', '#skF_2'))), k9_relat_1('#skF_3', '#skF_1')) | ~r1_tarski(k9_relat_1('#skF_3', k3_xboole_0('#skF_1', k10_relat_1('#skF_3', '#skF_2'))), '#skF_2')), inference(resolution, [status(thm)], [c_6, c_19])).
% 2.47/1.45  tff(c_95, plain, (~r1_tarski(k9_relat_1('#skF_3', k3_xboole_0('#skF_1', k10_relat_1('#skF_3', '#skF_2'))), '#skF_2')), inference(splitLeft, [status(thm)], [c_94])).
% 2.47/1.45  tff(c_310, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_303, c_95])).
% 2.47/1.45  tff(c_335, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_18, c_16, c_310])).
% 2.47/1.45  tff(c_336, plain, (~r1_tarski(k9_relat_1('#skF_3', k3_xboole_0('#skF_1', k10_relat_1('#skF_3', '#skF_2'))), k9_relat_1('#skF_3', '#skF_1'))), inference(splitRight, [status(thm)], [c_94])).
% 2.47/1.45  tff(c_401, plain, (~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_398, c_336])).
% 2.47/1.45  tff(c_414, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_18, c_401])).
% 2.47/1.45  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.47/1.45  
% 2.47/1.45  Inference rules
% 2.47/1.45  ----------------------
% 2.47/1.45  #Ref     : 0
% 2.47/1.45  #Sup     : 103
% 2.47/1.45  #Fact    : 0
% 2.47/1.45  #Define  : 0
% 2.47/1.45  #Split   : 1
% 2.47/1.45  #Chain   : 0
% 2.47/1.45  #Close   : 0
% 2.47/1.45  
% 2.47/1.45  Ordering : KBO
% 2.47/1.45  
% 2.47/1.45  Simplification rules
% 2.47/1.45  ----------------------
% 2.47/1.45  #Subsume      : 20
% 2.47/1.45  #Demod        : 4
% 2.47/1.45  #Tautology    : 18
% 2.47/1.45  #SimpNegUnit  : 0
% 2.47/1.45  #BackRed      : 0
% 2.47/1.45  
% 2.47/1.45  #Partial instantiations: 0
% 2.47/1.45  #Strategies tried      : 1
% 2.47/1.45  
% 2.47/1.45  Timing (in seconds)
% 2.47/1.45  ----------------------
% 2.47/1.45  Preprocessing        : 0.32
% 2.47/1.45  Parsing              : 0.17
% 2.47/1.45  CNF conversion       : 0.02
% 2.47/1.45  Main loop            : 0.25
% 2.47/1.45  Inferencing          : 0.09
% 2.47/1.45  Reduction            : 0.08
% 2.47/1.45  Demodulation         : 0.06
% 2.47/1.45  BG Simplification    : 0.02
% 2.47/1.45  Subsumption          : 0.06
% 2.47/1.45  Abstraction          : 0.01
% 2.47/1.45  MUC search           : 0.00
% 2.47/1.45  Cooper               : 0.00
% 2.47/1.45  Total                : 0.60
% 2.47/1.45  Index Insertion      : 0.00
% 2.47/1.45  Index Deletion       : 0.00
% 2.47/1.45  Index Matching       : 0.00
% 2.47/1.45  BG Taut test         : 0.00
%------------------------------------------------------------------------------
