%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:01:05 EST 2020

% Result     : Theorem 1.95s
% Output     : CNFRefutation 1.95s
% Verified   : 
% Statistics : Number of formulae       :   46 (  93 expanded)
%              Number of leaves         :   21 (  40 expanded)
%              Depth                    :    9
%              Number of atoms          :   73 ( 201 expanded)
%              Number of equality atoms :    4 (  16 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k9_relat_1 > k7_relat_1 > k5_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_65,negated_conjecture,(
    ~ ! [A,B,C] :
        ( v1_relat_1(C)
       => ( r1_tarski(A,B)
         => r1_tarski(k9_relat_1(C,A),k9_relat_1(C,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t156_relat_1)).

tff(f_33,axiom,(
    ! [A] : v1_relat_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).

tff(f_58,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k7_relat_1(B,A) = k5_relat_1(k6_relat_1(A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(A)
        & v1_relat_1(B) )
     => v1_relat_1(k5_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_relat_1)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r1_tarski(A,B)
       => r1_tarski(k7_relat_1(C,A),k7_relat_1(C,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t104_relat_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_54,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(A,B)
           => ( r1_tarski(k1_relat_1(A),k1_relat_1(B))
              & r1_tarski(k2_relat_1(A),k2_relat_1(B)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_relat_1)).

tff(c_20,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_4,plain,(
    ! [A_3] : v1_relat_1(k6_relat_1(A_3)) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_23,plain,(
    ! [A_17,B_18] :
      ( k5_relat_1(k6_relat_1(A_17),B_18) = k7_relat_1(B_18,A_17)
      | ~ v1_relat_1(B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( v1_relat_1(k5_relat_1(A_1,B_2))
      | ~ v1_relat_1(B_2)
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_29,plain,(
    ! [B_18,A_17] :
      ( v1_relat_1(k7_relat_1(B_18,A_17))
      | ~ v1_relat_1(B_18)
      | ~ v1_relat_1(k6_relat_1(A_17))
      | ~ v1_relat_1(B_18) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_23,c_2])).

tff(c_35,plain,(
    ! [B_18,A_17] :
      ( v1_relat_1(k7_relat_1(B_18,A_17))
      | ~ v1_relat_1(B_18) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_29])).

tff(c_18,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_6,plain,(
    ! [C_6,A_4,B_5] :
      ( r1_tarski(k7_relat_1(C_6,A_4),k7_relat_1(C_6,B_5))
      | ~ r1_tarski(A_4,B_5)
      | ~ v1_relat_1(C_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_8,plain,(
    ! [B_8,A_7] :
      ( k2_relat_1(k7_relat_1(B_8,A_7)) = k9_relat_1(B_8,A_7)
      | ~ v1_relat_1(B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_49,plain,(
    ! [A_28,B_29] :
      ( r1_tarski(k2_relat_1(A_28),k2_relat_1(B_29))
      | ~ r1_tarski(A_28,B_29)
      | ~ v1_relat_1(B_29)
      | ~ v1_relat_1(A_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_56,plain,(
    ! [B_30,A_31,B_32] :
      ( r1_tarski(k9_relat_1(B_30,A_31),k2_relat_1(B_32))
      | ~ r1_tarski(k7_relat_1(B_30,A_31),B_32)
      | ~ v1_relat_1(B_32)
      | ~ v1_relat_1(k7_relat_1(B_30,A_31))
      | ~ v1_relat_1(B_30) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_49])).

tff(c_64,plain,(
    ! [B_36,A_37,B_38,A_39] :
      ( r1_tarski(k9_relat_1(B_36,A_37),k9_relat_1(B_38,A_39))
      | ~ r1_tarski(k7_relat_1(B_36,A_37),k7_relat_1(B_38,A_39))
      | ~ v1_relat_1(k7_relat_1(B_38,A_39))
      | ~ v1_relat_1(k7_relat_1(B_36,A_37))
      | ~ v1_relat_1(B_36)
      | ~ v1_relat_1(B_38) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_56])).

tff(c_16,plain,(
    ~ r1_tarski(k9_relat_1('#skF_3','#skF_1'),k9_relat_1('#skF_3','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_67,plain,
    ( ~ r1_tarski(k7_relat_1('#skF_3','#skF_1'),k7_relat_1('#skF_3','#skF_2'))
    | ~ v1_relat_1(k7_relat_1('#skF_3','#skF_2'))
    | ~ v1_relat_1(k7_relat_1('#skF_3','#skF_1'))
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_64,c_16])).

tff(c_70,plain,
    ( ~ r1_tarski(k7_relat_1('#skF_3','#skF_1'),k7_relat_1('#skF_3','#skF_2'))
    | ~ v1_relat_1(k7_relat_1('#skF_3','#skF_2'))
    | ~ v1_relat_1(k7_relat_1('#skF_3','#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_67])).

tff(c_71,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_3','#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_70])).

tff(c_74,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_35,c_71])).

tff(c_78,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_74])).

tff(c_79,plain,
    ( ~ v1_relat_1(k7_relat_1('#skF_3','#skF_2'))
    | ~ r1_tarski(k7_relat_1('#skF_3','#skF_1'),k7_relat_1('#skF_3','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_70])).

tff(c_81,plain,(
    ~ r1_tarski(k7_relat_1('#skF_3','#skF_1'),k7_relat_1('#skF_3','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_79])).

tff(c_84,plain,
    ( ~ r1_tarski('#skF_1','#skF_2')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_6,c_81])).

tff(c_88,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_18,c_84])).

tff(c_89,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_3','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_79])).

tff(c_93,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_35,c_89])).

tff(c_97,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_93])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n019.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 13:01:52 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.95/1.35  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.95/1.35  
% 1.95/1.35  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.95/1.35  %$ r1_tarski > v1_relat_1 > k9_relat_1 > k7_relat_1 > k5_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 1.95/1.35  
% 1.95/1.35  %Foreground sorts:
% 1.95/1.35  
% 1.95/1.35  
% 1.95/1.35  %Background operators:
% 1.95/1.35  
% 1.95/1.35  
% 1.95/1.35  %Foreground operators:
% 1.95/1.35  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.95/1.35  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 1.95/1.35  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 1.95/1.35  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.95/1.35  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.95/1.35  tff('#skF_2', type, '#skF_2': $i).
% 1.95/1.35  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 1.95/1.35  tff('#skF_3', type, '#skF_3': $i).
% 1.95/1.35  tff('#skF_1', type, '#skF_1': $i).
% 1.95/1.35  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.95/1.35  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.95/1.35  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 1.95/1.35  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.95/1.35  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.95/1.35  
% 1.95/1.36  tff(f_65, negated_conjecture, ~(![A, B, C]: (v1_relat_1(C) => (r1_tarski(A, B) => r1_tarski(k9_relat_1(C, A), k9_relat_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t156_relat_1)).
% 1.95/1.36  tff(f_33, axiom, (![A]: v1_relat_1(k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 1.95/1.36  tff(f_58, axiom, (![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k5_relat_1(k6_relat_1(A), B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t94_relat_1)).
% 1.95/1.36  tff(f_31, axiom, (![A, B]: ((v1_relat_1(A) & v1_relat_1(B)) => v1_relat_1(k5_relat_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k5_relat_1)).
% 1.95/1.36  tff(f_39, axiom, (![A, B, C]: (v1_relat_1(C) => (r1_tarski(A, B) => r1_tarski(k7_relat_1(C, A), k7_relat_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t104_relat_1)).
% 1.95/1.36  tff(f_43, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_relat_1)).
% 1.95/1.36  tff(f_54, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(A, B) => (r1_tarski(k1_relat_1(A), k1_relat_1(B)) & r1_tarski(k2_relat_1(A), k2_relat_1(B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t25_relat_1)).
% 1.95/1.36  tff(c_20, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_65])).
% 1.95/1.36  tff(c_4, plain, (![A_3]: (v1_relat_1(k6_relat_1(A_3)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.95/1.36  tff(c_23, plain, (![A_17, B_18]: (k5_relat_1(k6_relat_1(A_17), B_18)=k7_relat_1(B_18, A_17) | ~v1_relat_1(B_18))), inference(cnfTransformation, [status(thm)], [f_58])).
% 1.95/1.36  tff(c_2, plain, (![A_1, B_2]: (v1_relat_1(k5_relat_1(A_1, B_2)) | ~v1_relat_1(B_2) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.95/1.36  tff(c_29, plain, (![B_18, A_17]: (v1_relat_1(k7_relat_1(B_18, A_17)) | ~v1_relat_1(B_18) | ~v1_relat_1(k6_relat_1(A_17)) | ~v1_relat_1(B_18))), inference(superposition, [status(thm), theory('equality')], [c_23, c_2])).
% 1.95/1.36  tff(c_35, plain, (![B_18, A_17]: (v1_relat_1(k7_relat_1(B_18, A_17)) | ~v1_relat_1(B_18))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_29])).
% 1.95/1.36  tff(c_18, plain, (r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_65])).
% 1.95/1.36  tff(c_6, plain, (![C_6, A_4, B_5]: (r1_tarski(k7_relat_1(C_6, A_4), k7_relat_1(C_6, B_5)) | ~r1_tarski(A_4, B_5) | ~v1_relat_1(C_6))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.95/1.36  tff(c_8, plain, (![B_8, A_7]: (k2_relat_1(k7_relat_1(B_8, A_7))=k9_relat_1(B_8, A_7) | ~v1_relat_1(B_8))), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.95/1.36  tff(c_49, plain, (![A_28, B_29]: (r1_tarski(k2_relat_1(A_28), k2_relat_1(B_29)) | ~r1_tarski(A_28, B_29) | ~v1_relat_1(B_29) | ~v1_relat_1(A_28))), inference(cnfTransformation, [status(thm)], [f_54])).
% 1.95/1.36  tff(c_56, plain, (![B_30, A_31, B_32]: (r1_tarski(k9_relat_1(B_30, A_31), k2_relat_1(B_32)) | ~r1_tarski(k7_relat_1(B_30, A_31), B_32) | ~v1_relat_1(B_32) | ~v1_relat_1(k7_relat_1(B_30, A_31)) | ~v1_relat_1(B_30))), inference(superposition, [status(thm), theory('equality')], [c_8, c_49])).
% 1.95/1.36  tff(c_64, plain, (![B_36, A_37, B_38, A_39]: (r1_tarski(k9_relat_1(B_36, A_37), k9_relat_1(B_38, A_39)) | ~r1_tarski(k7_relat_1(B_36, A_37), k7_relat_1(B_38, A_39)) | ~v1_relat_1(k7_relat_1(B_38, A_39)) | ~v1_relat_1(k7_relat_1(B_36, A_37)) | ~v1_relat_1(B_36) | ~v1_relat_1(B_38))), inference(superposition, [status(thm), theory('equality')], [c_8, c_56])).
% 1.95/1.36  tff(c_16, plain, (~r1_tarski(k9_relat_1('#skF_3', '#skF_1'), k9_relat_1('#skF_3', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_65])).
% 1.95/1.36  tff(c_67, plain, (~r1_tarski(k7_relat_1('#skF_3', '#skF_1'), k7_relat_1('#skF_3', '#skF_2')) | ~v1_relat_1(k7_relat_1('#skF_3', '#skF_2')) | ~v1_relat_1(k7_relat_1('#skF_3', '#skF_1')) | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_64, c_16])).
% 1.95/1.36  tff(c_70, plain, (~r1_tarski(k7_relat_1('#skF_3', '#skF_1'), k7_relat_1('#skF_3', '#skF_2')) | ~v1_relat_1(k7_relat_1('#skF_3', '#skF_2')) | ~v1_relat_1(k7_relat_1('#skF_3', '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_67])).
% 1.95/1.36  tff(c_71, plain, (~v1_relat_1(k7_relat_1('#skF_3', '#skF_1'))), inference(splitLeft, [status(thm)], [c_70])).
% 1.95/1.36  tff(c_74, plain, (~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_35, c_71])).
% 1.95/1.36  tff(c_78, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_20, c_74])).
% 1.95/1.36  tff(c_79, plain, (~v1_relat_1(k7_relat_1('#skF_3', '#skF_2')) | ~r1_tarski(k7_relat_1('#skF_3', '#skF_1'), k7_relat_1('#skF_3', '#skF_2'))), inference(splitRight, [status(thm)], [c_70])).
% 1.95/1.36  tff(c_81, plain, (~r1_tarski(k7_relat_1('#skF_3', '#skF_1'), k7_relat_1('#skF_3', '#skF_2'))), inference(splitLeft, [status(thm)], [c_79])).
% 1.95/1.36  tff(c_84, plain, (~r1_tarski('#skF_1', '#skF_2') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_6, c_81])).
% 1.95/1.36  tff(c_88, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_20, c_18, c_84])).
% 1.95/1.36  tff(c_89, plain, (~v1_relat_1(k7_relat_1('#skF_3', '#skF_2'))), inference(splitRight, [status(thm)], [c_79])).
% 1.95/1.36  tff(c_93, plain, (~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_35, c_89])).
% 1.95/1.36  tff(c_97, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_20, c_93])).
% 1.95/1.36  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.95/1.36  
% 1.95/1.36  Inference rules
% 1.95/1.36  ----------------------
% 1.95/1.36  #Ref     : 0
% 1.95/1.36  #Sup     : 13
% 1.95/1.36  #Fact    : 0
% 1.95/1.36  #Define  : 0
% 1.95/1.36  #Split   : 2
% 1.95/1.36  #Chain   : 0
% 1.95/1.36  #Close   : 0
% 1.95/1.36  
% 1.95/1.36  Ordering : KBO
% 1.95/1.36  
% 1.95/1.36  Simplification rules
% 1.95/1.36  ----------------------
% 1.95/1.36  #Subsume      : 1
% 1.95/1.36  #Demod        : 6
% 1.95/1.36  #Tautology    : 4
% 1.95/1.36  #SimpNegUnit  : 0
% 1.95/1.36  #BackRed      : 0
% 1.95/1.36  
% 1.95/1.36  #Partial instantiations: 0
% 1.95/1.36  #Strategies tried      : 1
% 1.95/1.36  
% 1.95/1.36  Timing (in seconds)
% 1.95/1.36  ----------------------
% 1.95/1.37  Preprocessing        : 0.32
% 1.95/1.37  Parsing              : 0.18
% 1.95/1.37  CNF conversion       : 0.02
% 1.95/1.37  Main loop            : 0.15
% 1.95/1.37  Inferencing          : 0.07
% 1.95/1.37  Reduction            : 0.04
% 1.95/1.37  Demodulation         : 0.03
% 1.95/1.37  BG Simplification    : 0.01
% 1.95/1.37  Subsumption          : 0.02
% 1.95/1.37  Abstraction          : 0.01
% 1.95/1.37  MUC search           : 0.00
% 1.95/1.37  Cooper               : 0.00
% 1.95/1.37  Total                : 0.50
% 1.95/1.37  Index Insertion      : 0.00
% 1.95/1.37  Index Deletion       : 0.00
% 1.95/1.37  Index Matching       : 0.00
% 1.95/1.37  BG Taut test         : 0.00
%------------------------------------------------------------------------------
