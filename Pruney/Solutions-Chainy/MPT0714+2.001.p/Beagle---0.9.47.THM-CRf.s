%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:05:36 EST 2020

% Result     : Theorem 11.13s
% Output     : CNFRefutation 11.41s
% Verified   : 
% Statistics : Number of formulae       :   47 (  84 expanded)
%              Number of leaves         :   23 (  39 expanded)
%              Depth                    :   11
%              Number of atoms          :   80 ( 193 expanded)
%              Number of equality atoms :   21 (  48 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > v1_funct_1 > k9_relat_1 > k7_relat_1 > k5_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

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

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(f_83,negated_conjecture,(
    ~ ! [A] :
        ( ( v1_relat_1(A)
          & v1_funct_1(A) )
       => ! [B] :
            ( ( v1_relat_1(B)
              & v1_funct_1(B) )
           => ! [C] : k5_relat_1(k7_relat_1(A,C),k7_relat_1(B,k9_relat_1(A,C))) = k7_relat_1(k5_relat_1(A,B),C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t169_funct_1)).

tff(f_42,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ! [C] :
          ( v1_relat_1(C)
         => k7_relat_1(k5_relat_1(B,C),A) = k5_relat_1(k7_relat_1(B,A),C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t112_relat_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k7_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).

tff(f_46,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_66,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k7_relat_1(B,A) = k5_relat_1(k6_relat_1(A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).

tff(f_70,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v1_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_62,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k2_relat_1(B),A)
       => k5_relat_1(B,k6_relat_1(A)) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_relat_1)).

tff(f_56,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ! [C] :
              ( v1_relat_1(C)
             => k5_relat_1(k5_relat_1(A,B),C) = k5_relat_1(A,k5_relat_1(B,C)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_relat_1)).

tff(c_32,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_28,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_10,plain,(
    ! [B_6,C_8,A_5] :
      ( k7_relat_1(k5_relat_1(B_6,C_8),A_5) = k5_relat_1(k7_relat_1(B_6,A_5),C_8)
      | ~ v1_relat_1(C_8)
      | ~ v1_relat_1(B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( v1_relat_1(k7_relat_1(A_3,B_4))
      | ~ v1_relat_1(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_12,plain,(
    ! [B_10,A_9] :
      ( k2_relat_1(k7_relat_1(B_10,A_9)) = k9_relat_1(B_10,A_9)
      | ~ v1_relat_1(B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_18,plain,(
    ! [A_20,B_21] :
      ( k5_relat_1(k6_relat_1(A_20),B_21) = k7_relat_1(B_21,A_20)
      | ~ v1_relat_1(B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_20,plain,(
    ! [A_22] : v1_relat_1(k6_relat_1(A_22)) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_63,plain,(
    ! [B_38,A_39] :
      ( k5_relat_1(B_38,k6_relat_1(A_39)) = B_38
      | ~ r1_tarski(k2_relat_1(B_38),A_39)
      | ~ v1_relat_1(B_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_71,plain,(
    ! [B_38] :
      ( k5_relat_1(B_38,k6_relat_1(k2_relat_1(B_38))) = B_38
      | ~ v1_relat_1(B_38) ) ),
    inference(resolution,[status(thm)],[c_6,c_63])).

tff(c_175,plain,(
    ! [A_48,B_49,C_50] :
      ( k5_relat_1(k5_relat_1(A_48,B_49),C_50) = k5_relat_1(A_48,k5_relat_1(B_49,C_50))
      | ~ v1_relat_1(C_50)
      | ~ v1_relat_1(B_49)
      | ~ v1_relat_1(A_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_200,plain,(
    ! [B_38,C_50] :
      ( k5_relat_1(B_38,k5_relat_1(k6_relat_1(k2_relat_1(B_38)),C_50)) = k5_relat_1(B_38,C_50)
      | ~ v1_relat_1(C_50)
      | ~ v1_relat_1(k6_relat_1(k2_relat_1(B_38)))
      | ~ v1_relat_1(B_38)
      | ~ v1_relat_1(B_38) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_71,c_175])).

tff(c_2580,plain,(
    ! [B_133,C_134] :
      ( k5_relat_1(B_133,k5_relat_1(k6_relat_1(k2_relat_1(B_133)),C_134)) = k5_relat_1(B_133,C_134)
      | ~ v1_relat_1(C_134)
      | ~ v1_relat_1(B_133) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_200])).

tff(c_3151,plain,(
    ! [B_143,B_144] :
      ( k5_relat_1(B_143,k7_relat_1(B_144,k2_relat_1(B_143))) = k5_relat_1(B_143,B_144)
      | ~ v1_relat_1(B_144)
      | ~ v1_relat_1(B_143)
      | ~ v1_relat_1(B_144) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_2580])).

tff(c_16698,plain,(
    ! [B_312,A_313,B_314] :
      ( k5_relat_1(k7_relat_1(B_312,A_313),k7_relat_1(B_314,k9_relat_1(B_312,A_313))) = k5_relat_1(k7_relat_1(B_312,A_313),B_314)
      | ~ v1_relat_1(B_314)
      | ~ v1_relat_1(k7_relat_1(B_312,A_313))
      | ~ v1_relat_1(B_314)
      | ~ v1_relat_1(B_312) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_3151])).

tff(c_24,plain,(
    k5_relat_1(k7_relat_1('#skF_1','#skF_3'),k7_relat_1('#skF_2',k9_relat_1('#skF_1','#skF_3'))) != k7_relat_1(k5_relat_1('#skF_1','#skF_2'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_16791,plain,
    ( k7_relat_1(k5_relat_1('#skF_1','#skF_2'),'#skF_3') != k5_relat_1(k7_relat_1('#skF_1','#skF_3'),'#skF_2')
    | ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1(k7_relat_1('#skF_1','#skF_3'))
    | ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_16698,c_24])).

tff(c_17073,plain,
    ( k7_relat_1(k5_relat_1('#skF_1','#skF_2'),'#skF_3') != k5_relat_1(k7_relat_1('#skF_1','#skF_3'),'#skF_2')
    | ~ v1_relat_1(k7_relat_1('#skF_1','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_28,c_28,c_16791])).

tff(c_17192,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_1','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_17073])).

tff(c_17195,plain,(
    ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_8,c_17192])).

tff(c_17199,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_17195])).

tff(c_17200,plain,(
    k7_relat_1(k5_relat_1('#skF_1','#skF_2'),'#skF_3') != k5_relat_1(k7_relat_1('#skF_1','#skF_3'),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_17073])).

tff(c_17204,plain,
    ( ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_17200])).

tff(c_17208,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_28,c_17204])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n017.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 11:08:16 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.20/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 11.13/4.03  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.13/4.04  
% 11.13/4.04  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.13/4.04  %$ r1_tarski > v1_relat_1 > v1_funct_1 > k9_relat_1 > k7_relat_1 > k5_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > #skF_2 > #skF_3 > #skF_1
% 11.13/4.04  
% 11.13/4.04  %Foreground sorts:
% 11.13/4.04  
% 11.13/4.04  
% 11.13/4.04  %Background operators:
% 11.13/4.04  
% 11.13/4.04  
% 11.13/4.04  %Foreground operators:
% 11.13/4.04  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 11.13/4.04  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 11.13/4.04  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 11.13/4.04  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 11.13/4.04  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 11.13/4.04  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 11.13/4.04  tff('#skF_2', type, '#skF_2': $i).
% 11.13/4.04  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 11.13/4.04  tff('#skF_3', type, '#skF_3': $i).
% 11.13/4.04  tff('#skF_1', type, '#skF_1': $i).
% 11.13/4.04  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 11.13/4.04  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 11.13/4.04  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 11.13/4.04  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 11.13/4.04  
% 11.41/4.05  tff(f_83, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (![C]: (k5_relat_1(k7_relat_1(A, C), k7_relat_1(B, k9_relat_1(A, C))) = k7_relat_1(k5_relat_1(A, B), C))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t169_funct_1)).
% 11.41/4.05  tff(f_42, axiom, (![A, B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (k7_relat_1(k5_relat_1(B, C), A) = k5_relat_1(k7_relat_1(B, A), C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t112_relat_1)).
% 11.41/4.05  tff(f_35, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k7_relat_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 11.41/4.05  tff(f_46, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_relat_1)).
% 11.41/4.05  tff(f_66, axiom, (![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k5_relat_1(k6_relat_1(A), B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t94_relat_1)).
% 11.41/4.05  tff(f_70, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v1_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc3_funct_1)).
% 11.41/4.05  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 11.41/4.05  tff(f_62, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(B), A) => (k5_relat_1(B, k6_relat_1(A)) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_relat_1)).
% 11.41/4.05  tff(f_56, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (k5_relat_1(k5_relat_1(A, B), C) = k5_relat_1(A, k5_relat_1(B, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_relat_1)).
% 11.41/4.05  tff(c_32, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_83])).
% 11.41/4.05  tff(c_28, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_83])).
% 11.41/4.05  tff(c_10, plain, (![B_6, C_8, A_5]: (k7_relat_1(k5_relat_1(B_6, C_8), A_5)=k5_relat_1(k7_relat_1(B_6, A_5), C_8) | ~v1_relat_1(C_8) | ~v1_relat_1(B_6))), inference(cnfTransformation, [status(thm)], [f_42])).
% 11.41/4.05  tff(c_8, plain, (![A_3, B_4]: (v1_relat_1(k7_relat_1(A_3, B_4)) | ~v1_relat_1(A_3))), inference(cnfTransformation, [status(thm)], [f_35])).
% 11.41/4.05  tff(c_12, plain, (![B_10, A_9]: (k2_relat_1(k7_relat_1(B_10, A_9))=k9_relat_1(B_10, A_9) | ~v1_relat_1(B_10))), inference(cnfTransformation, [status(thm)], [f_46])).
% 11.41/4.05  tff(c_18, plain, (![A_20, B_21]: (k5_relat_1(k6_relat_1(A_20), B_21)=k7_relat_1(B_21, A_20) | ~v1_relat_1(B_21))), inference(cnfTransformation, [status(thm)], [f_66])).
% 11.41/4.05  tff(c_20, plain, (![A_22]: (v1_relat_1(k6_relat_1(A_22)))), inference(cnfTransformation, [status(thm)], [f_70])).
% 11.41/4.05  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 11.41/4.05  tff(c_63, plain, (![B_38, A_39]: (k5_relat_1(B_38, k6_relat_1(A_39))=B_38 | ~r1_tarski(k2_relat_1(B_38), A_39) | ~v1_relat_1(B_38))), inference(cnfTransformation, [status(thm)], [f_62])).
% 11.41/4.05  tff(c_71, plain, (![B_38]: (k5_relat_1(B_38, k6_relat_1(k2_relat_1(B_38)))=B_38 | ~v1_relat_1(B_38))), inference(resolution, [status(thm)], [c_6, c_63])).
% 11.41/4.05  tff(c_175, plain, (![A_48, B_49, C_50]: (k5_relat_1(k5_relat_1(A_48, B_49), C_50)=k5_relat_1(A_48, k5_relat_1(B_49, C_50)) | ~v1_relat_1(C_50) | ~v1_relat_1(B_49) | ~v1_relat_1(A_48))), inference(cnfTransformation, [status(thm)], [f_56])).
% 11.41/4.05  tff(c_200, plain, (![B_38, C_50]: (k5_relat_1(B_38, k5_relat_1(k6_relat_1(k2_relat_1(B_38)), C_50))=k5_relat_1(B_38, C_50) | ~v1_relat_1(C_50) | ~v1_relat_1(k6_relat_1(k2_relat_1(B_38))) | ~v1_relat_1(B_38) | ~v1_relat_1(B_38))), inference(superposition, [status(thm), theory('equality')], [c_71, c_175])).
% 11.41/4.05  tff(c_2580, plain, (![B_133, C_134]: (k5_relat_1(B_133, k5_relat_1(k6_relat_1(k2_relat_1(B_133)), C_134))=k5_relat_1(B_133, C_134) | ~v1_relat_1(C_134) | ~v1_relat_1(B_133))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_200])).
% 11.41/4.05  tff(c_3151, plain, (![B_143, B_144]: (k5_relat_1(B_143, k7_relat_1(B_144, k2_relat_1(B_143)))=k5_relat_1(B_143, B_144) | ~v1_relat_1(B_144) | ~v1_relat_1(B_143) | ~v1_relat_1(B_144))), inference(superposition, [status(thm), theory('equality')], [c_18, c_2580])).
% 11.41/4.05  tff(c_16698, plain, (![B_312, A_313, B_314]: (k5_relat_1(k7_relat_1(B_312, A_313), k7_relat_1(B_314, k9_relat_1(B_312, A_313)))=k5_relat_1(k7_relat_1(B_312, A_313), B_314) | ~v1_relat_1(B_314) | ~v1_relat_1(k7_relat_1(B_312, A_313)) | ~v1_relat_1(B_314) | ~v1_relat_1(B_312))), inference(superposition, [status(thm), theory('equality')], [c_12, c_3151])).
% 11.41/4.05  tff(c_24, plain, (k5_relat_1(k7_relat_1('#skF_1', '#skF_3'), k7_relat_1('#skF_2', k9_relat_1('#skF_1', '#skF_3')))!=k7_relat_1(k5_relat_1('#skF_1', '#skF_2'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_83])).
% 11.41/4.05  tff(c_16791, plain, (k7_relat_1(k5_relat_1('#skF_1', '#skF_2'), '#skF_3')!=k5_relat_1(k7_relat_1('#skF_1', '#skF_3'), '#skF_2') | ~v1_relat_1('#skF_2') | ~v1_relat_1(k7_relat_1('#skF_1', '#skF_3')) | ~v1_relat_1('#skF_2') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_16698, c_24])).
% 11.41/4.05  tff(c_17073, plain, (k7_relat_1(k5_relat_1('#skF_1', '#skF_2'), '#skF_3')!=k5_relat_1(k7_relat_1('#skF_1', '#skF_3'), '#skF_2') | ~v1_relat_1(k7_relat_1('#skF_1', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_28, c_28, c_16791])).
% 11.41/4.05  tff(c_17192, plain, (~v1_relat_1(k7_relat_1('#skF_1', '#skF_3'))), inference(splitLeft, [status(thm)], [c_17073])).
% 11.41/4.05  tff(c_17195, plain, (~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_8, c_17192])).
% 11.41/4.05  tff(c_17199, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_32, c_17195])).
% 11.41/4.05  tff(c_17200, plain, (k7_relat_1(k5_relat_1('#skF_1', '#skF_2'), '#skF_3')!=k5_relat_1(k7_relat_1('#skF_1', '#skF_3'), '#skF_2')), inference(splitRight, [status(thm)], [c_17073])).
% 11.41/4.05  tff(c_17204, plain, (~v1_relat_1('#skF_2') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_10, c_17200])).
% 11.41/4.05  tff(c_17208, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_32, c_28, c_17204])).
% 11.41/4.05  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.41/4.05  
% 11.41/4.05  Inference rules
% 11.41/4.05  ----------------------
% 11.41/4.05  #Ref     : 0
% 11.41/4.05  #Sup     : 3597
% 11.41/4.05  #Fact    : 0
% 11.41/4.05  #Define  : 0
% 11.41/4.05  #Split   : 1
% 11.41/4.05  #Chain   : 0
% 11.41/4.05  #Close   : 0
% 11.41/4.05  
% 11.41/4.05  Ordering : KBO
% 11.41/4.05  
% 11.41/4.05  Simplification rules
% 11.41/4.05  ----------------------
% 11.41/4.05  #Subsume      : 203
% 11.41/4.05  #Demod        : 6966
% 11.41/4.05  #Tautology    : 1071
% 11.41/4.05  #SimpNegUnit  : 0
% 11.41/4.05  #BackRed      : 1
% 11.41/4.05  
% 11.41/4.05  #Partial instantiations: 0
% 11.41/4.05  #Strategies tried      : 1
% 11.41/4.05  
% 11.41/4.05  Timing (in seconds)
% 11.41/4.05  ----------------------
% 11.41/4.05  Preprocessing        : 0.29
% 11.41/4.05  Parsing              : 0.15
% 11.41/4.05  CNF conversion       : 0.02
% 11.41/4.05  Main loop            : 3.01
% 11.41/4.05  Inferencing          : 0.84
% 11.41/4.05  Reduction            : 1.39
% 11.41/4.05  Demodulation         : 1.16
% 11.41/4.05  BG Simplification    : 0.13
% 11.41/4.05  Subsumption          : 0.53
% 11.41/4.05  Abstraction          : 0.25
% 11.41/4.05  MUC search           : 0.00
% 11.41/4.05  Cooper               : 0.00
% 11.41/4.06  Total                : 3.33
% 11.41/4.06  Index Insertion      : 0.00
% 11.41/4.06  Index Deletion       : 0.00
% 11.41/4.06  Index Matching       : 0.00
% 11.41/4.06  BG Taut test         : 0.00
%------------------------------------------------------------------------------
