%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:04:08 EST 2020

% Result     : Theorem 1.96s
% Output     : CNFRefutation 1.96s
% Verified   : 
% Statistics : Number of formulae       :   43 (  55 expanded)
%              Number of leaves         :   23 (  30 expanded)
%              Depth                    :   10
%              Number of atoms          :   73 (  91 expanded)
%              Number of equality atoms :   23 (  25 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v2_funct_1 > v1_relat_1 > v1_funct_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k2_relat_1 > k2_funct_1 > k1_relat_1 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff(k2_funct_1,type,(
    k2_funct_1: $i > $i )).

tff(v2_funct_1,type,(
    v2_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_59,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v1_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).

tff(f_55,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).

tff(f_61,axiom,(
    ! [A] : v2_funct_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_funct_1)).

tff(f_41,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_71,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k2_relat_1(A) = k1_relat_1(k2_funct_1(A))
          & k1_relat_1(A) = k2_relat_1(k2_funct_1(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_47,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k1_relat_1(B),A)
       => k5_relat_1(k6_relat_1(A),B) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_relat_1)).

tff(f_81,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k5_relat_1(A,k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))
          & k5_relat_1(k2_funct_1(A),A) = k6_relat_1(k2_relat_1(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_1)).

tff(f_84,negated_conjecture,(
    ~ ! [A] : k2_funct_1(k6_relat_1(A)) = k6_relat_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_funct_1)).

tff(c_22,plain,(
    ! [A_10] : v1_relat_1(k6_relat_1(A_10)) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_24,plain,(
    ! [A_10] : v1_funct_1(k6_relat_1(A_10)) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_20,plain,(
    ! [A_9] :
      ( v1_relat_1(k2_funct_1(A_9))
      | ~ v1_funct_1(A_9)
      | ~ v1_relat_1(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_26,plain,(
    ! [A_11] : v2_funct_1(k6_relat_1(A_11)) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_12,plain,(
    ! [A_6] : k1_relat_1(k6_relat_1(A_6)) = A_6 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_14,plain,(
    ! [A_6] : k2_relat_1(k6_relat_1(A_6)) = A_6 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_30,plain,(
    ! [A_12] :
      ( k1_relat_1(k2_funct_1(A_12)) = k2_relat_1(A_12)
      | ~ v2_funct_1(A_12)
      | ~ v1_funct_1(A_12)
      | ~ v1_relat_1(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_93,plain,(
    ! [A_28,B_29] :
      ( k5_relat_1(k6_relat_1(A_28),B_29) = B_29
      | ~ r1_tarski(k1_relat_1(B_29),A_28)
      | ~ v1_relat_1(B_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_107,plain,(
    ! [B_30] :
      ( k5_relat_1(k6_relat_1(k1_relat_1(B_30)),B_30) = B_30
      | ~ v1_relat_1(B_30) ) ),
    inference(resolution,[status(thm)],[c_6,c_93])).

tff(c_187,plain,(
    ! [A_36] :
      ( k5_relat_1(k6_relat_1(k2_relat_1(A_36)),k2_funct_1(A_36)) = k2_funct_1(A_36)
      | ~ v1_relat_1(k2_funct_1(A_36))
      | ~ v2_funct_1(A_36)
      | ~ v1_funct_1(A_36)
      | ~ v1_relat_1(A_36) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_107])).

tff(c_199,plain,(
    ! [A_6] :
      ( k5_relat_1(k6_relat_1(A_6),k2_funct_1(k6_relat_1(A_6))) = k2_funct_1(k6_relat_1(A_6))
      | ~ v1_relat_1(k2_funct_1(k6_relat_1(A_6)))
      | ~ v2_funct_1(k6_relat_1(A_6))
      | ~ v1_funct_1(k6_relat_1(A_6))
      | ~ v1_relat_1(k6_relat_1(A_6)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_187])).

tff(c_204,plain,(
    ! [A_37] :
      ( k5_relat_1(k6_relat_1(A_37),k2_funct_1(k6_relat_1(A_37))) = k2_funct_1(k6_relat_1(A_37))
      | ~ v1_relat_1(k2_funct_1(k6_relat_1(A_37))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_24,c_26,c_199])).

tff(c_34,plain,(
    ! [A_13] :
      ( k5_relat_1(A_13,k2_funct_1(A_13)) = k6_relat_1(k1_relat_1(A_13))
      | ~ v2_funct_1(A_13)
      | ~ v1_funct_1(A_13)
      | ~ v1_relat_1(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_210,plain,(
    ! [A_37] :
      ( k6_relat_1(k1_relat_1(k6_relat_1(A_37))) = k2_funct_1(k6_relat_1(A_37))
      | ~ v2_funct_1(k6_relat_1(A_37))
      | ~ v1_funct_1(k6_relat_1(A_37))
      | ~ v1_relat_1(k6_relat_1(A_37))
      | ~ v1_relat_1(k2_funct_1(k6_relat_1(A_37))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_204,c_34])).

tff(c_223,plain,(
    ! [A_38] :
      ( k2_funct_1(k6_relat_1(A_38)) = k6_relat_1(A_38)
      | ~ v1_relat_1(k2_funct_1(k6_relat_1(A_38))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_24,c_26,c_12,c_210])).

tff(c_226,plain,(
    ! [A_38] :
      ( k2_funct_1(k6_relat_1(A_38)) = k6_relat_1(A_38)
      | ~ v1_funct_1(k6_relat_1(A_38))
      | ~ v1_relat_1(k6_relat_1(A_38)) ) ),
    inference(resolution,[status(thm)],[c_20,c_223])).

tff(c_229,plain,(
    ! [A_38] : k2_funct_1(k6_relat_1(A_38)) = k6_relat_1(A_38) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_24,c_226])).

tff(c_36,plain,(
    k2_funct_1(k6_relat_1('#skF_1')) != k6_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_236,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_229,c_36])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n011.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 20:01:27 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.96/1.18  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.96/1.18  
% 1.96/1.18  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.96/1.18  %$ r1_tarski > v2_funct_1 > v1_relat_1 > v1_funct_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k2_relat_1 > k2_funct_1 > k1_relat_1 > #skF_1
% 1.96/1.18  
% 1.96/1.18  %Foreground sorts:
% 1.96/1.18  
% 1.96/1.18  
% 1.96/1.18  %Background operators:
% 1.96/1.18  
% 1.96/1.18  
% 1.96/1.18  %Foreground operators:
% 1.96/1.18  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 1.96/1.18  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 1.96/1.18  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 1.96/1.18  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.96/1.18  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 1.96/1.18  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.96/1.18  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.96/1.18  tff('#skF_1', type, '#skF_1': $i).
% 1.96/1.18  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.96/1.18  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.96/1.18  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.96/1.18  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 1.96/1.18  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.96/1.18  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.96/1.18  
% 1.96/1.20  tff(f_59, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v1_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc3_funct_1)).
% 1.96/1.20  tff(f_55, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 1.96/1.20  tff(f_61, axiom, (![A]: v2_funct_1(k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_funct_1)).
% 1.96/1.20  tff(f_41, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 1.96/1.20  tff(f_71, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k2_relat_1(A) = k1_relat_1(k2_funct_1(A))) & (k1_relat_1(A) = k2_relat_1(k2_funct_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_funct_1)).
% 1.96/1.20  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 1.96/1.20  tff(f_47, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(B), A) => (k5_relat_1(k6_relat_1(A), B) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t77_relat_1)).
% 1.96/1.20  tff(f_81, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k5_relat_1(A, k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))) & (k5_relat_1(k2_funct_1(A), A) = k6_relat_1(k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t61_funct_1)).
% 1.96/1.20  tff(f_84, negated_conjecture, ~(![A]: (k2_funct_1(k6_relat_1(A)) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t67_funct_1)).
% 1.96/1.20  tff(c_22, plain, (![A_10]: (v1_relat_1(k6_relat_1(A_10)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 1.96/1.20  tff(c_24, plain, (![A_10]: (v1_funct_1(k6_relat_1(A_10)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 1.96/1.20  tff(c_20, plain, (![A_9]: (v1_relat_1(k2_funct_1(A_9)) | ~v1_funct_1(A_9) | ~v1_relat_1(A_9))), inference(cnfTransformation, [status(thm)], [f_55])).
% 1.96/1.20  tff(c_26, plain, (![A_11]: (v2_funct_1(k6_relat_1(A_11)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 1.96/1.20  tff(c_12, plain, (![A_6]: (k1_relat_1(k6_relat_1(A_6))=A_6)), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.96/1.20  tff(c_14, plain, (![A_6]: (k2_relat_1(k6_relat_1(A_6))=A_6)), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.96/1.20  tff(c_30, plain, (![A_12]: (k1_relat_1(k2_funct_1(A_12))=k2_relat_1(A_12) | ~v2_funct_1(A_12) | ~v1_funct_1(A_12) | ~v1_relat_1(A_12))), inference(cnfTransformation, [status(thm)], [f_71])).
% 1.96/1.20  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.96/1.20  tff(c_93, plain, (![A_28, B_29]: (k5_relat_1(k6_relat_1(A_28), B_29)=B_29 | ~r1_tarski(k1_relat_1(B_29), A_28) | ~v1_relat_1(B_29))), inference(cnfTransformation, [status(thm)], [f_47])).
% 1.96/1.20  tff(c_107, plain, (![B_30]: (k5_relat_1(k6_relat_1(k1_relat_1(B_30)), B_30)=B_30 | ~v1_relat_1(B_30))), inference(resolution, [status(thm)], [c_6, c_93])).
% 1.96/1.20  tff(c_187, plain, (![A_36]: (k5_relat_1(k6_relat_1(k2_relat_1(A_36)), k2_funct_1(A_36))=k2_funct_1(A_36) | ~v1_relat_1(k2_funct_1(A_36)) | ~v2_funct_1(A_36) | ~v1_funct_1(A_36) | ~v1_relat_1(A_36))), inference(superposition, [status(thm), theory('equality')], [c_30, c_107])).
% 1.96/1.20  tff(c_199, plain, (![A_6]: (k5_relat_1(k6_relat_1(A_6), k2_funct_1(k6_relat_1(A_6)))=k2_funct_1(k6_relat_1(A_6)) | ~v1_relat_1(k2_funct_1(k6_relat_1(A_6))) | ~v2_funct_1(k6_relat_1(A_6)) | ~v1_funct_1(k6_relat_1(A_6)) | ~v1_relat_1(k6_relat_1(A_6)))), inference(superposition, [status(thm), theory('equality')], [c_14, c_187])).
% 1.96/1.20  tff(c_204, plain, (![A_37]: (k5_relat_1(k6_relat_1(A_37), k2_funct_1(k6_relat_1(A_37)))=k2_funct_1(k6_relat_1(A_37)) | ~v1_relat_1(k2_funct_1(k6_relat_1(A_37))))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_24, c_26, c_199])).
% 1.96/1.20  tff(c_34, plain, (![A_13]: (k5_relat_1(A_13, k2_funct_1(A_13))=k6_relat_1(k1_relat_1(A_13)) | ~v2_funct_1(A_13) | ~v1_funct_1(A_13) | ~v1_relat_1(A_13))), inference(cnfTransformation, [status(thm)], [f_81])).
% 1.96/1.20  tff(c_210, plain, (![A_37]: (k6_relat_1(k1_relat_1(k6_relat_1(A_37)))=k2_funct_1(k6_relat_1(A_37)) | ~v2_funct_1(k6_relat_1(A_37)) | ~v1_funct_1(k6_relat_1(A_37)) | ~v1_relat_1(k6_relat_1(A_37)) | ~v1_relat_1(k2_funct_1(k6_relat_1(A_37))))), inference(superposition, [status(thm), theory('equality')], [c_204, c_34])).
% 1.96/1.20  tff(c_223, plain, (![A_38]: (k2_funct_1(k6_relat_1(A_38))=k6_relat_1(A_38) | ~v1_relat_1(k2_funct_1(k6_relat_1(A_38))))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_24, c_26, c_12, c_210])).
% 1.96/1.20  tff(c_226, plain, (![A_38]: (k2_funct_1(k6_relat_1(A_38))=k6_relat_1(A_38) | ~v1_funct_1(k6_relat_1(A_38)) | ~v1_relat_1(k6_relat_1(A_38)))), inference(resolution, [status(thm)], [c_20, c_223])).
% 1.96/1.20  tff(c_229, plain, (![A_38]: (k2_funct_1(k6_relat_1(A_38))=k6_relat_1(A_38))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_24, c_226])).
% 1.96/1.20  tff(c_36, plain, (k2_funct_1(k6_relat_1('#skF_1'))!=k6_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_84])).
% 1.96/1.20  tff(c_236, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_229, c_36])).
% 1.96/1.20  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.96/1.20  
% 1.96/1.20  Inference rules
% 1.96/1.20  ----------------------
% 1.96/1.20  #Ref     : 1
% 1.96/1.20  #Sup     : 37
% 1.96/1.20  #Fact    : 0
% 1.96/1.20  #Define  : 0
% 1.96/1.20  #Split   : 0
% 1.96/1.20  #Chain   : 0
% 1.96/1.20  #Close   : 0
% 1.96/1.20  
% 1.96/1.20  Ordering : KBO
% 1.96/1.20  
% 1.96/1.20  Simplification rules
% 1.96/1.20  ----------------------
% 1.96/1.20  #Subsume      : 0
% 1.96/1.20  #Demod        : 34
% 1.96/1.20  #Tautology    : 32
% 1.96/1.20  #SimpNegUnit  : 0
% 1.96/1.20  #BackRed      : 2
% 1.96/1.20  
% 1.96/1.20  #Partial instantiations: 0
% 1.96/1.20  #Strategies tried      : 1
% 1.96/1.20  
% 1.96/1.20  Timing (in seconds)
% 1.96/1.20  ----------------------
% 1.96/1.20  Preprocessing        : 0.29
% 1.96/1.20  Parsing              : 0.16
% 1.96/1.20  CNF conversion       : 0.02
% 1.96/1.20  Main loop            : 0.16
% 1.96/1.20  Inferencing          : 0.06
% 1.96/1.20  Reduction            : 0.05
% 1.96/1.20  Demodulation         : 0.04
% 1.96/1.20  BG Simplification    : 0.01
% 1.96/1.20  Subsumption          : 0.03
% 1.96/1.20  Abstraction          : 0.01
% 1.96/1.20  MUC search           : 0.00
% 1.96/1.20  Cooper               : 0.00
% 1.96/1.20  Total                : 0.48
% 1.96/1.20  Index Insertion      : 0.00
% 1.96/1.20  Index Deletion       : 0.00
% 1.96/1.20  Index Matching       : 0.00
% 1.96/1.20  BG Taut test         : 0.00
%------------------------------------------------------------------------------
