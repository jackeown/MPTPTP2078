%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:01:09 EST 2020

% Result     : Theorem 3.47s
% Output     : CNFRefutation 3.52s
% Verified   : 
% Statistics : Number of formulae       :   40 (  44 expanded)
%              Number of leaves         :   21 (  24 expanded)
%              Depth                    :   10
%              Number of atoms          :   84 (  96 expanded)
%              Number of equality atoms :   19 (  21 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k9_relat_1 > k7_relat_1 > k5_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_relat_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_71,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ! [B] :
            ( v1_relat_1(B)
           => k2_relat_1(k5_relat_1(A,B)) = k9_relat_1(B,k2_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t160_relat_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(A)
        & v1_relat_1(B) )
     => v1_relat_1(k5_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_relat_1)).

tff(f_35,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k9_relat_1(A,k1_relat_1(A)) = k2_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_relat_1)).

tff(f_46,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ! [C] :
          ( v1_relat_1(C)
         => k9_relat_1(k5_relat_1(B,C),A) = k9_relat_1(C,k9_relat_1(B,A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t159_relat_1)).

tff(f_63,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k7_relat_1(B,A) = k5_relat_1(k6_relat_1(A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).

tff(f_53,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => r1_tarski(k1_relat_1(k5_relat_1(A,B)),k1_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_relat_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k1_relat_1(B),A)
       => k5_relat_1(k6_relat_1(A),B) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_relat_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

tff(c_20,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_18,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( v1_relat_1(k5_relat_1(A_1,B_2))
      | ~ v1_relat_1(B_2)
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_4,plain,(
    ! [A_3] :
      ( k9_relat_1(A_3,k1_relat_1(A_3)) = k2_relat_1(A_3)
      | ~ v1_relat_1(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_8,plain,(
    ! [B_7,C_9,A_6] :
      ( k9_relat_1(k5_relat_1(B_7,C_9),A_6) = k9_relat_1(C_9,k9_relat_1(B_7,A_6))
      | ~ v1_relat_1(C_9)
      | ~ v1_relat_1(B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_14,plain,(
    ! [A_15,B_16] :
      ( k5_relat_1(k6_relat_1(A_15),B_16) = k7_relat_1(B_16,A_15)
      | ~ v1_relat_1(B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_10,plain,(
    ! [A_10,B_12] :
      ( r1_tarski(k1_relat_1(k5_relat_1(A_10,B_12)),k1_relat_1(A_10))
      | ~ v1_relat_1(B_12)
      | ~ v1_relat_1(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_56,plain,(
    ! [A_27,B_28] :
      ( k5_relat_1(k6_relat_1(A_27),B_28) = B_28
      | ~ r1_tarski(k1_relat_1(B_28),A_27)
      | ~ v1_relat_1(B_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_116,plain,(
    ! [A_39,B_40] :
      ( k5_relat_1(k6_relat_1(k1_relat_1(A_39)),k5_relat_1(A_39,B_40)) = k5_relat_1(A_39,B_40)
      | ~ v1_relat_1(k5_relat_1(A_39,B_40))
      | ~ v1_relat_1(B_40)
      | ~ v1_relat_1(A_39) ) ),
    inference(resolution,[status(thm)],[c_10,c_56])).

tff(c_218,plain,(
    ! [A_45,B_46] :
      ( k7_relat_1(k5_relat_1(A_45,B_46),k1_relat_1(A_45)) = k5_relat_1(A_45,B_46)
      | ~ v1_relat_1(k5_relat_1(A_45,B_46))
      | ~ v1_relat_1(B_46)
      | ~ v1_relat_1(A_45)
      | ~ v1_relat_1(k5_relat_1(A_45,B_46)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_116])).

tff(c_6,plain,(
    ! [B_5,A_4] :
      ( k2_relat_1(k7_relat_1(B_5,A_4)) = k9_relat_1(B_5,A_4)
      | ~ v1_relat_1(B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_443,plain,(
    ! [A_59,B_60] :
      ( k9_relat_1(k5_relat_1(A_59,B_60),k1_relat_1(A_59)) = k2_relat_1(k5_relat_1(A_59,B_60))
      | ~ v1_relat_1(k5_relat_1(A_59,B_60))
      | ~ v1_relat_1(k5_relat_1(A_59,B_60))
      | ~ v1_relat_1(B_60)
      | ~ v1_relat_1(A_59)
      | ~ v1_relat_1(k5_relat_1(A_59,B_60)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_218,c_6])).

tff(c_917,plain,(
    ! [C_80,B_81] :
      ( k9_relat_1(C_80,k9_relat_1(B_81,k1_relat_1(B_81))) = k2_relat_1(k5_relat_1(B_81,C_80))
      | ~ v1_relat_1(k5_relat_1(B_81,C_80))
      | ~ v1_relat_1(k5_relat_1(B_81,C_80))
      | ~ v1_relat_1(C_80)
      | ~ v1_relat_1(B_81)
      | ~ v1_relat_1(k5_relat_1(B_81,C_80))
      | ~ v1_relat_1(C_80)
      | ~ v1_relat_1(B_81) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_443])).

tff(c_1042,plain,(
    ! [C_84,A_85] :
      ( k9_relat_1(C_84,k2_relat_1(A_85)) = k2_relat_1(k5_relat_1(A_85,C_84))
      | ~ v1_relat_1(k5_relat_1(A_85,C_84))
      | ~ v1_relat_1(k5_relat_1(A_85,C_84))
      | ~ v1_relat_1(C_84)
      | ~ v1_relat_1(A_85)
      | ~ v1_relat_1(k5_relat_1(A_85,C_84))
      | ~ v1_relat_1(C_84)
      | ~ v1_relat_1(A_85)
      | ~ v1_relat_1(A_85) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_917])).

tff(c_1058,plain,(
    ! [B_86,A_87] :
      ( k9_relat_1(B_86,k2_relat_1(A_87)) = k2_relat_1(k5_relat_1(A_87,B_86))
      | ~ v1_relat_1(k5_relat_1(A_87,B_86))
      | ~ v1_relat_1(B_86)
      | ~ v1_relat_1(A_87) ) ),
    inference(resolution,[status(thm)],[c_2,c_1042])).

tff(c_1081,plain,(
    ! [B_88,A_89] :
      ( k9_relat_1(B_88,k2_relat_1(A_89)) = k2_relat_1(k5_relat_1(A_89,B_88))
      | ~ v1_relat_1(B_88)
      | ~ v1_relat_1(A_89) ) ),
    inference(resolution,[status(thm)],[c_2,c_1058])).

tff(c_16,plain,(
    k9_relat_1('#skF_2',k2_relat_1('#skF_1')) != k2_relat_1(k5_relat_1('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_1103,plain,
    ( ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_1081,c_16])).

tff(c_1118,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_18,c_1103])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:00:59 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.47/1.55  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.47/1.55  
% 3.47/1.55  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.52/1.56  %$ r1_tarski > v1_relat_1 > k9_relat_1 > k7_relat_1 > k5_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_relat_1 > #skF_2 > #skF_1
% 3.52/1.56  
% 3.52/1.56  %Foreground sorts:
% 3.52/1.56  
% 3.52/1.56  
% 3.52/1.56  %Background operators:
% 3.52/1.56  
% 3.52/1.56  
% 3.52/1.56  %Foreground operators:
% 3.52/1.56  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.52/1.56  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 3.52/1.56  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 3.52/1.56  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.52/1.56  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.52/1.56  tff('#skF_2', type, '#skF_2': $i).
% 3.52/1.56  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 3.52/1.56  tff('#skF_1', type, '#skF_1': $i).
% 3.52/1.56  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.52/1.56  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.52/1.56  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 3.52/1.56  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.52/1.56  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.52/1.56  
% 3.52/1.57  tff(f_71, negated_conjecture, ~(![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k2_relat_1(k5_relat_1(A, B)) = k9_relat_1(B, k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t160_relat_1)).
% 3.52/1.57  tff(f_31, axiom, (![A, B]: ((v1_relat_1(A) & v1_relat_1(B)) => v1_relat_1(k5_relat_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k5_relat_1)).
% 3.52/1.57  tff(f_35, axiom, (![A]: (v1_relat_1(A) => (k9_relat_1(A, k1_relat_1(A)) = k2_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t146_relat_1)).
% 3.52/1.57  tff(f_46, axiom, (![A, B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (k9_relat_1(k5_relat_1(B, C), A) = k9_relat_1(C, k9_relat_1(B, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t159_relat_1)).
% 3.52/1.57  tff(f_63, axiom, (![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k5_relat_1(k6_relat_1(A), B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t94_relat_1)).
% 3.52/1.57  tff(f_53, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k5_relat_1(A, B)), k1_relat_1(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_relat_1)).
% 3.52/1.57  tff(f_59, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(B), A) => (k5_relat_1(k6_relat_1(A), B) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t77_relat_1)).
% 3.52/1.57  tff(f_39, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_relat_1)).
% 3.52/1.57  tff(c_20, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.52/1.57  tff(c_18, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.52/1.57  tff(c_2, plain, (![A_1, B_2]: (v1_relat_1(k5_relat_1(A_1, B_2)) | ~v1_relat_1(B_2) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.52/1.57  tff(c_4, plain, (![A_3]: (k9_relat_1(A_3, k1_relat_1(A_3))=k2_relat_1(A_3) | ~v1_relat_1(A_3))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.52/1.57  tff(c_8, plain, (![B_7, C_9, A_6]: (k9_relat_1(k5_relat_1(B_7, C_9), A_6)=k9_relat_1(C_9, k9_relat_1(B_7, A_6)) | ~v1_relat_1(C_9) | ~v1_relat_1(B_7))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.52/1.57  tff(c_14, plain, (![A_15, B_16]: (k5_relat_1(k6_relat_1(A_15), B_16)=k7_relat_1(B_16, A_15) | ~v1_relat_1(B_16))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.52/1.57  tff(c_10, plain, (![A_10, B_12]: (r1_tarski(k1_relat_1(k5_relat_1(A_10, B_12)), k1_relat_1(A_10)) | ~v1_relat_1(B_12) | ~v1_relat_1(A_10))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.52/1.57  tff(c_56, plain, (![A_27, B_28]: (k5_relat_1(k6_relat_1(A_27), B_28)=B_28 | ~r1_tarski(k1_relat_1(B_28), A_27) | ~v1_relat_1(B_28))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.52/1.57  tff(c_116, plain, (![A_39, B_40]: (k5_relat_1(k6_relat_1(k1_relat_1(A_39)), k5_relat_1(A_39, B_40))=k5_relat_1(A_39, B_40) | ~v1_relat_1(k5_relat_1(A_39, B_40)) | ~v1_relat_1(B_40) | ~v1_relat_1(A_39))), inference(resolution, [status(thm)], [c_10, c_56])).
% 3.52/1.57  tff(c_218, plain, (![A_45, B_46]: (k7_relat_1(k5_relat_1(A_45, B_46), k1_relat_1(A_45))=k5_relat_1(A_45, B_46) | ~v1_relat_1(k5_relat_1(A_45, B_46)) | ~v1_relat_1(B_46) | ~v1_relat_1(A_45) | ~v1_relat_1(k5_relat_1(A_45, B_46)))), inference(superposition, [status(thm), theory('equality')], [c_14, c_116])).
% 3.52/1.57  tff(c_6, plain, (![B_5, A_4]: (k2_relat_1(k7_relat_1(B_5, A_4))=k9_relat_1(B_5, A_4) | ~v1_relat_1(B_5))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.52/1.57  tff(c_443, plain, (![A_59, B_60]: (k9_relat_1(k5_relat_1(A_59, B_60), k1_relat_1(A_59))=k2_relat_1(k5_relat_1(A_59, B_60)) | ~v1_relat_1(k5_relat_1(A_59, B_60)) | ~v1_relat_1(k5_relat_1(A_59, B_60)) | ~v1_relat_1(B_60) | ~v1_relat_1(A_59) | ~v1_relat_1(k5_relat_1(A_59, B_60)))), inference(superposition, [status(thm), theory('equality')], [c_218, c_6])).
% 3.52/1.57  tff(c_917, plain, (![C_80, B_81]: (k9_relat_1(C_80, k9_relat_1(B_81, k1_relat_1(B_81)))=k2_relat_1(k5_relat_1(B_81, C_80)) | ~v1_relat_1(k5_relat_1(B_81, C_80)) | ~v1_relat_1(k5_relat_1(B_81, C_80)) | ~v1_relat_1(C_80) | ~v1_relat_1(B_81) | ~v1_relat_1(k5_relat_1(B_81, C_80)) | ~v1_relat_1(C_80) | ~v1_relat_1(B_81))), inference(superposition, [status(thm), theory('equality')], [c_8, c_443])).
% 3.52/1.57  tff(c_1042, plain, (![C_84, A_85]: (k9_relat_1(C_84, k2_relat_1(A_85))=k2_relat_1(k5_relat_1(A_85, C_84)) | ~v1_relat_1(k5_relat_1(A_85, C_84)) | ~v1_relat_1(k5_relat_1(A_85, C_84)) | ~v1_relat_1(C_84) | ~v1_relat_1(A_85) | ~v1_relat_1(k5_relat_1(A_85, C_84)) | ~v1_relat_1(C_84) | ~v1_relat_1(A_85) | ~v1_relat_1(A_85))), inference(superposition, [status(thm), theory('equality')], [c_4, c_917])).
% 3.52/1.57  tff(c_1058, plain, (![B_86, A_87]: (k9_relat_1(B_86, k2_relat_1(A_87))=k2_relat_1(k5_relat_1(A_87, B_86)) | ~v1_relat_1(k5_relat_1(A_87, B_86)) | ~v1_relat_1(B_86) | ~v1_relat_1(A_87))), inference(resolution, [status(thm)], [c_2, c_1042])).
% 3.52/1.57  tff(c_1081, plain, (![B_88, A_89]: (k9_relat_1(B_88, k2_relat_1(A_89))=k2_relat_1(k5_relat_1(A_89, B_88)) | ~v1_relat_1(B_88) | ~v1_relat_1(A_89))), inference(resolution, [status(thm)], [c_2, c_1058])).
% 3.52/1.57  tff(c_16, plain, (k9_relat_1('#skF_2', k2_relat_1('#skF_1'))!=k2_relat_1(k5_relat_1('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.52/1.57  tff(c_1103, plain, (~v1_relat_1('#skF_2') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_1081, c_16])).
% 3.52/1.57  tff(c_1118, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_20, c_18, c_1103])).
% 3.52/1.57  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.52/1.57  
% 3.52/1.57  Inference rules
% 3.52/1.57  ----------------------
% 3.52/1.57  #Ref     : 0
% 3.52/1.57  #Sup     : 316
% 3.52/1.57  #Fact    : 0
% 3.52/1.57  #Define  : 0
% 3.52/1.57  #Split   : 0
% 3.52/1.57  #Chain   : 0
% 3.52/1.57  #Close   : 0
% 3.52/1.57  
% 3.52/1.57  Ordering : KBO
% 3.52/1.57  
% 3.52/1.57  Simplification rules
% 3.52/1.57  ----------------------
% 3.52/1.57  #Subsume      : 24
% 3.52/1.57  #Demod        : 2
% 3.52/1.57  #Tautology    : 55
% 3.52/1.57  #SimpNegUnit  : 0
% 3.52/1.57  #BackRed      : 0
% 3.52/1.57  
% 3.52/1.57  #Partial instantiations: 0
% 3.52/1.57  #Strategies tried      : 1
% 3.52/1.57  
% 3.52/1.57  Timing (in seconds)
% 3.52/1.57  ----------------------
% 3.52/1.57  Preprocessing        : 0.27
% 3.52/1.57  Parsing              : 0.15
% 3.52/1.57  CNF conversion       : 0.02
% 3.52/1.57  Main loop            : 0.50
% 3.52/1.57  Inferencing          : 0.21
% 3.52/1.57  Reduction            : 0.13
% 3.52/1.57  Demodulation         : 0.09
% 3.52/1.57  BG Simplification    : 0.04
% 3.52/1.57  Subsumption          : 0.10
% 3.52/1.57  Abstraction          : 0.03
% 3.52/1.57  MUC search           : 0.00
% 3.52/1.57  Cooper               : 0.00
% 3.52/1.57  Total                : 0.80
% 3.52/1.57  Index Insertion      : 0.00
% 3.52/1.57  Index Deletion       : 0.00
% 3.52/1.57  Index Matching       : 0.00
% 3.52/1.57  BG Taut test         : 0.00
%------------------------------------------------------------------------------
