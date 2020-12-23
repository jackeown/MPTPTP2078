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
% DateTime   : Thu Dec  3 10:01:56 EST 2020

% Result     : Theorem 4.40s
% Output     : CNFRefutation 4.40s
% Verified   : 
% Statistics : Number of formulae       :   37 (  45 expanded)
%              Number of leaves         :   18 (  23 expanded)
%              Depth                    :    8
%              Number of atoms          :   76 (  96 expanded)
%              Number of equality atoms :   12 (  18 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k5_relat_1 > k10_relat_1 > #nlpp > k2_relat_1 > k1_relat_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_66,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ! [B] :
            ( v1_relat_1(B)
           => k1_relat_1(k5_relat_1(A,B)) = k10_relat_1(A,k1_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t182_relat_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(A)
        & v1_relat_1(B) )
     => v1_relat_1(k5_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_relat_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k10_relat_1(B,A),k1_relat_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t167_relat_1)).

tff(f_58,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ! [C] :
          ( v1_relat_1(C)
         => k10_relat_1(k5_relat_1(B,C),A) = k10_relat_1(B,k10_relat_1(C,A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t181_relat_1)).

tff(f_45,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k10_relat_1(A,k2_relat_1(A)) = k1_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_relat_1)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r1_tarski(A,B)
       => r1_tarski(k10_relat_1(C,A),k10_relat_1(C,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t178_relat_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(c_22,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_20,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( v1_relat_1(k5_relat_1(A_3,B_4))
      | ~ v1_relat_1(B_4)
      | ~ v1_relat_1(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_10,plain,(
    ! [B_6,A_5] :
      ( r1_tarski(k10_relat_1(B_6,A_5),k1_relat_1(B_6))
      | ~ v1_relat_1(B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_60,plain,(
    ! [B_27,C_28,A_29] :
      ( k10_relat_1(k5_relat_1(B_27,C_28),A_29) = k10_relat_1(B_27,k10_relat_1(C_28,A_29))
      | ~ v1_relat_1(C_28)
      | ~ v1_relat_1(B_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_12,plain,(
    ! [A_7] :
      ( k10_relat_1(A_7,k2_relat_1(A_7)) = k1_relat_1(A_7)
      | ~ v1_relat_1(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_196,plain,(
    ! [B_50,C_51] :
      ( k10_relat_1(B_50,k10_relat_1(C_51,k2_relat_1(k5_relat_1(B_50,C_51)))) = k1_relat_1(k5_relat_1(B_50,C_51))
      | ~ v1_relat_1(k5_relat_1(B_50,C_51))
      | ~ v1_relat_1(C_51)
      | ~ v1_relat_1(B_50) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_60,c_12])).

tff(c_14,plain,(
    ! [C_10,A_8,B_9] :
      ( r1_tarski(k10_relat_1(C_10,A_8),k10_relat_1(C_10,B_9))
      | ~ r1_tarski(A_8,B_9)
      | ~ v1_relat_1(C_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_1430,plain,(
    ! [B_143,C_144,B_145] :
      ( r1_tarski(k1_relat_1(k5_relat_1(B_143,C_144)),k10_relat_1(B_143,B_145))
      | ~ r1_tarski(k10_relat_1(C_144,k2_relat_1(k5_relat_1(B_143,C_144))),B_145)
      | ~ v1_relat_1(B_143)
      | ~ v1_relat_1(k5_relat_1(B_143,C_144))
      | ~ v1_relat_1(C_144)
      | ~ v1_relat_1(B_143) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_196,c_14])).

tff(c_1454,plain,(
    ! [B_146,B_147] :
      ( r1_tarski(k1_relat_1(k5_relat_1(B_146,B_147)),k10_relat_1(B_146,k1_relat_1(B_147)))
      | ~ v1_relat_1(k5_relat_1(B_146,B_147))
      | ~ v1_relat_1(B_146)
      | ~ v1_relat_1(B_147) ) ),
    inference(resolution,[status(thm)],[c_10,c_1430])).

tff(c_142,plain,(
    ! [B_39,C_40,A_41] :
      ( r1_tarski(k10_relat_1(B_39,k10_relat_1(C_40,A_41)),k1_relat_1(k5_relat_1(B_39,C_40)))
      | ~ v1_relat_1(k5_relat_1(B_39,C_40))
      | ~ v1_relat_1(C_40)
      | ~ v1_relat_1(B_39) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_60,c_10])).

tff(c_175,plain,(
    ! [B_45,A_46] :
      ( r1_tarski(k10_relat_1(B_45,k1_relat_1(A_46)),k1_relat_1(k5_relat_1(B_45,A_46)))
      | ~ v1_relat_1(k5_relat_1(B_45,A_46))
      | ~ v1_relat_1(A_46)
      | ~ v1_relat_1(B_45)
      | ~ v1_relat_1(A_46) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_142])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_185,plain,(
    ! [B_45,A_46] :
      ( k10_relat_1(B_45,k1_relat_1(A_46)) = k1_relat_1(k5_relat_1(B_45,A_46))
      | ~ r1_tarski(k1_relat_1(k5_relat_1(B_45,A_46)),k10_relat_1(B_45,k1_relat_1(A_46)))
      | ~ v1_relat_1(k5_relat_1(B_45,A_46))
      | ~ v1_relat_1(B_45)
      | ~ v1_relat_1(A_46) ) ),
    inference(resolution,[status(thm)],[c_175,c_2])).

tff(c_1472,plain,(
    ! [B_148,B_149] :
      ( k10_relat_1(B_148,k1_relat_1(B_149)) = k1_relat_1(k5_relat_1(B_148,B_149))
      | ~ v1_relat_1(k5_relat_1(B_148,B_149))
      | ~ v1_relat_1(B_148)
      | ~ v1_relat_1(B_149) ) ),
    inference(resolution,[status(thm)],[c_1454,c_185])).

tff(c_1477,plain,(
    ! [A_150,B_151] :
      ( k10_relat_1(A_150,k1_relat_1(B_151)) = k1_relat_1(k5_relat_1(A_150,B_151))
      | ~ v1_relat_1(B_151)
      | ~ v1_relat_1(A_150) ) ),
    inference(resolution,[status(thm)],[c_8,c_1472])).

tff(c_18,plain,(
    k10_relat_1('#skF_1',k1_relat_1('#skF_2')) != k1_relat_1(k5_relat_1('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_1600,plain,
    ( ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_1477,c_18])).

tff(c_1617,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_20,c_1600])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n003.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 18:46:57 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.40/1.89  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.40/1.89  
% 4.40/1.89  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.40/1.89  %$ r1_tarski > v1_relat_1 > k5_relat_1 > k10_relat_1 > #nlpp > k2_relat_1 > k1_relat_1 > #skF_2 > #skF_1
% 4.40/1.89  
% 4.40/1.89  %Foreground sorts:
% 4.40/1.89  
% 4.40/1.89  
% 4.40/1.89  %Background operators:
% 4.40/1.89  
% 4.40/1.89  
% 4.40/1.89  %Foreground operators:
% 4.40/1.89  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.40/1.89  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 4.40/1.89  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.40/1.89  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 4.40/1.89  tff('#skF_2', type, '#skF_2': $i).
% 4.40/1.89  tff('#skF_1', type, '#skF_1': $i).
% 4.40/1.89  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.40/1.89  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 4.40/1.89  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.40/1.89  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.40/1.89  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.40/1.89  
% 4.40/1.90  tff(f_66, negated_conjecture, ~(![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k1_relat_1(k5_relat_1(A, B)) = k10_relat_1(A, k1_relat_1(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t182_relat_1)).
% 4.40/1.90  tff(f_37, axiom, (![A, B]: ((v1_relat_1(A) & v1_relat_1(B)) => v1_relat_1(k5_relat_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k5_relat_1)).
% 4.40/1.90  tff(f_41, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k10_relat_1(B, A), k1_relat_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t167_relat_1)).
% 4.40/1.90  tff(f_58, axiom, (![A, B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (k10_relat_1(k5_relat_1(B, C), A) = k10_relat_1(B, k10_relat_1(C, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t181_relat_1)).
% 4.40/1.90  tff(f_45, axiom, (![A]: (v1_relat_1(A) => (k10_relat_1(A, k2_relat_1(A)) = k1_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t169_relat_1)).
% 4.40/1.90  tff(f_51, axiom, (![A, B, C]: (v1_relat_1(C) => (r1_tarski(A, B) => r1_tarski(k10_relat_1(C, A), k10_relat_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t178_relat_1)).
% 4.40/1.90  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 4.40/1.90  tff(c_22, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_66])).
% 4.40/1.90  tff(c_20, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_66])).
% 4.40/1.90  tff(c_8, plain, (![A_3, B_4]: (v1_relat_1(k5_relat_1(A_3, B_4)) | ~v1_relat_1(B_4) | ~v1_relat_1(A_3))), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.40/1.90  tff(c_10, plain, (![B_6, A_5]: (r1_tarski(k10_relat_1(B_6, A_5), k1_relat_1(B_6)) | ~v1_relat_1(B_6))), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.40/1.90  tff(c_60, plain, (![B_27, C_28, A_29]: (k10_relat_1(k5_relat_1(B_27, C_28), A_29)=k10_relat_1(B_27, k10_relat_1(C_28, A_29)) | ~v1_relat_1(C_28) | ~v1_relat_1(B_27))), inference(cnfTransformation, [status(thm)], [f_58])).
% 4.40/1.90  tff(c_12, plain, (![A_7]: (k10_relat_1(A_7, k2_relat_1(A_7))=k1_relat_1(A_7) | ~v1_relat_1(A_7))), inference(cnfTransformation, [status(thm)], [f_45])).
% 4.40/1.90  tff(c_196, plain, (![B_50, C_51]: (k10_relat_1(B_50, k10_relat_1(C_51, k2_relat_1(k5_relat_1(B_50, C_51))))=k1_relat_1(k5_relat_1(B_50, C_51)) | ~v1_relat_1(k5_relat_1(B_50, C_51)) | ~v1_relat_1(C_51) | ~v1_relat_1(B_50))), inference(superposition, [status(thm), theory('equality')], [c_60, c_12])).
% 4.40/1.90  tff(c_14, plain, (![C_10, A_8, B_9]: (r1_tarski(k10_relat_1(C_10, A_8), k10_relat_1(C_10, B_9)) | ~r1_tarski(A_8, B_9) | ~v1_relat_1(C_10))), inference(cnfTransformation, [status(thm)], [f_51])).
% 4.40/1.90  tff(c_1430, plain, (![B_143, C_144, B_145]: (r1_tarski(k1_relat_1(k5_relat_1(B_143, C_144)), k10_relat_1(B_143, B_145)) | ~r1_tarski(k10_relat_1(C_144, k2_relat_1(k5_relat_1(B_143, C_144))), B_145) | ~v1_relat_1(B_143) | ~v1_relat_1(k5_relat_1(B_143, C_144)) | ~v1_relat_1(C_144) | ~v1_relat_1(B_143))), inference(superposition, [status(thm), theory('equality')], [c_196, c_14])).
% 4.40/1.90  tff(c_1454, plain, (![B_146, B_147]: (r1_tarski(k1_relat_1(k5_relat_1(B_146, B_147)), k10_relat_1(B_146, k1_relat_1(B_147))) | ~v1_relat_1(k5_relat_1(B_146, B_147)) | ~v1_relat_1(B_146) | ~v1_relat_1(B_147))), inference(resolution, [status(thm)], [c_10, c_1430])).
% 4.40/1.90  tff(c_142, plain, (![B_39, C_40, A_41]: (r1_tarski(k10_relat_1(B_39, k10_relat_1(C_40, A_41)), k1_relat_1(k5_relat_1(B_39, C_40))) | ~v1_relat_1(k5_relat_1(B_39, C_40)) | ~v1_relat_1(C_40) | ~v1_relat_1(B_39))), inference(superposition, [status(thm), theory('equality')], [c_60, c_10])).
% 4.40/1.90  tff(c_175, plain, (![B_45, A_46]: (r1_tarski(k10_relat_1(B_45, k1_relat_1(A_46)), k1_relat_1(k5_relat_1(B_45, A_46))) | ~v1_relat_1(k5_relat_1(B_45, A_46)) | ~v1_relat_1(A_46) | ~v1_relat_1(B_45) | ~v1_relat_1(A_46))), inference(superposition, [status(thm), theory('equality')], [c_12, c_142])).
% 4.40/1.90  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.40/1.90  tff(c_185, plain, (![B_45, A_46]: (k10_relat_1(B_45, k1_relat_1(A_46))=k1_relat_1(k5_relat_1(B_45, A_46)) | ~r1_tarski(k1_relat_1(k5_relat_1(B_45, A_46)), k10_relat_1(B_45, k1_relat_1(A_46))) | ~v1_relat_1(k5_relat_1(B_45, A_46)) | ~v1_relat_1(B_45) | ~v1_relat_1(A_46))), inference(resolution, [status(thm)], [c_175, c_2])).
% 4.40/1.90  tff(c_1472, plain, (![B_148, B_149]: (k10_relat_1(B_148, k1_relat_1(B_149))=k1_relat_1(k5_relat_1(B_148, B_149)) | ~v1_relat_1(k5_relat_1(B_148, B_149)) | ~v1_relat_1(B_148) | ~v1_relat_1(B_149))), inference(resolution, [status(thm)], [c_1454, c_185])).
% 4.40/1.90  tff(c_1477, plain, (![A_150, B_151]: (k10_relat_1(A_150, k1_relat_1(B_151))=k1_relat_1(k5_relat_1(A_150, B_151)) | ~v1_relat_1(B_151) | ~v1_relat_1(A_150))), inference(resolution, [status(thm)], [c_8, c_1472])).
% 4.40/1.90  tff(c_18, plain, (k10_relat_1('#skF_1', k1_relat_1('#skF_2'))!=k1_relat_1(k5_relat_1('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_66])).
% 4.40/1.90  tff(c_1600, plain, (~v1_relat_1('#skF_2') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_1477, c_18])).
% 4.40/1.90  tff(c_1617, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_22, c_20, c_1600])).
% 4.40/1.90  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.40/1.90  
% 4.40/1.90  Inference rules
% 4.40/1.90  ----------------------
% 4.40/1.90  #Ref     : 0
% 4.40/1.90  #Sup     : 455
% 4.40/1.90  #Fact    : 0
% 4.40/1.90  #Define  : 0
% 4.40/1.90  #Split   : 0
% 4.40/1.90  #Chain   : 0
% 4.40/1.90  #Close   : 0
% 4.40/1.90  
% 4.40/1.90  Ordering : KBO
% 4.40/1.90  
% 4.40/1.90  Simplification rules
% 4.40/1.90  ----------------------
% 4.40/1.90  #Subsume      : 59
% 4.40/1.90  #Demod        : 45
% 4.40/1.90  #Tautology    : 48
% 4.40/1.90  #SimpNegUnit  : 0
% 4.40/1.90  #BackRed      : 0
% 4.40/1.90  
% 4.40/1.90  #Partial instantiations: 0
% 4.40/1.90  #Strategies tried      : 1
% 4.40/1.90  
% 4.40/1.90  Timing (in seconds)
% 4.40/1.90  ----------------------
% 4.40/1.90  Preprocessing        : 0.39
% 4.40/1.90  Parsing              : 0.22
% 4.40/1.90  CNF conversion       : 0.03
% 4.40/1.91  Main loop            : 0.74
% 4.40/1.91  Inferencing          : 0.26
% 4.40/1.91  Reduction            : 0.16
% 4.40/1.91  Demodulation         : 0.11
% 4.40/1.91  BG Simplification    : 0.05
% 4.40/1.91  Subsumption          : 0.23
% 4.40/1.91  Abstraction          : 0.05
% 4.40/1.91  MUC search           : 0.00
% 4.40/1.91  Cooper               : 0.00
% 4.40/1.91  Total                : 1.17
% 4.40/1.91  Index Insertion      : 0.00
% 4.40/1.91  Index Deletion       : 0.00
% 4.40/1.91  Index Matching       : 0.00
% 4.40/1.91  BG Taut test         : 0.00
%------------------------------------------------------------------------------
