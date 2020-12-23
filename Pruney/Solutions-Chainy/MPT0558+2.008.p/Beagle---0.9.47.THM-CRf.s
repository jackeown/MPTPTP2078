%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:01:08 EST 2020

% Result     : Theorem 17.99s
% Output     : CNFRefutation 17.99s
% Verified   : 
% Statistics : Number of formulae       :   46 (  50 expanded)
%              Number of leaves         :   23 (  26 expanded)
%              Depth                    :   12
%              Number of atoms          :   94 ( 106 expanded)
%              Number of equality atoms :   24 (  26 expanded)
%              Maximal formula depth    :   11 (   5 average)
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

tff(f_80,negated_conjecture,(
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

tff(f_37,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k9_relat_1(A,k1_relat_1(A)) = k2_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_relat_1)).

tff(f_48,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ! [C] :
          ( v1_relat_1(C)
         => k9_relat_1(k5_relat_1(B,C),A) = k9_relat_1(C,k9_relat_1(B,A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t159_relat_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_55,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => r1_tarski(k1_relat_1(k5_relat_1(A,B)),k1_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_relat_1)).

tff(f_72,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k7_relat_1(B,A) = k5_relat_1(k6_relat_1(A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).

tff(f_33,axiom,(
    ! [A] : v1_relat_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).

tff(f_68,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_64,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(k1_relat_1(A),k2_relat_1(B))
           => k2_relat_1(k5_relat_1(B,A)) = k2_relat_1(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_relat_1)).

tff(c_26,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_24,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( v1_relat_1(k5_relat_1(A_1,B_2))
      | ~ v1_relat_1(B_2)
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_6,plain,(
    ! [A_4] :
      ( k9_relat_1(A_4,k1_relat_1(A_4)) = k2_relat_1(A_4)
      | ~ v1_relat_1(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_10,plain,(
    ! [B_8,C_10,A_7] :
      ( k9_relat_1(k5_relat_1(B_8,C_10),A_7) = k9_relat_1(C_10,k9_relat_1(B_8,A_7))
      | ~ v1_relat_1(C_10)
      | ~ v1_relat_1(B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_8,plain,(
    ! [B_6,A_5] :
      ( k2_relat_1(k7_relat_1(B_6,A_5)) = k9_relat_1(B_6,A_5)
      | ~ v1_relat_1(B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_12,plain,(
    ! [A_11,B_13] :
      ( r1_tarski(k1_relat_1(k5_relat_1(A_11,B_13)),k1_relat_1(A_11))
      | ~ v1_relat_1(B_13)
      | ~ v1_relat_1(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_20,plain,(
    ! [A_18,B_19] :
      ( k5_relat_1(k6_relat_1(A_18),B_19) = k7_relat_1(B_19,A_18)
      | ~ v1_relat_1(B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_4,plain,(
    ! [A_3] : v1_relat_1(k6_relat_1(A_3)) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_18,plain,(
    ! [A_17] : k2_relat_1(k6_relat_1(A_17)) = A_17 ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_199,plain,(
    ! [B_48,A_49] :
      ( k2_relat_1(k5_relat_1(B_48,A_49)) = k2_relat_1(A_49)
      | ~ r1_tarski(k1_relat_1(A_49),k2_relat_1(B_48))
      | ~ v1_relat_1(B_48)
      | ~ v1_relat_1(A_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_216,plain,(
    ! [A_17,A_49] :
      ( k2_relat_1(k5_relat_1(k6_relat_1(A_17),A_49)) = k2_relat_1(A_49)
      | ~ r1_tarski(k1_relat_1(A_49),A_17)
      | ~ v1_relat_1(k6_relat_1(A_17))
      | ~ v1_relat_1(A_49) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_199])).

tff(c_309,plain,(
    ! [A_56,A_57] :
      ( k2_relat_1(k5_relat_1(k6_relat_1(A_56),A_57)) = k2_relat_1(A_57)
      | ~ r1_tarski(k1_relat_1(A_57),A_56)
      | ~ v1_relat_1(A_57) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_216])).

tff(c_481,plain,(
    ! [B_63,A_64] :
      ( k2_relat_1(k7_relat_1(B_63,A_64)) = k2_relat_1(B_63)
      | ~ r1_tarski(k1_relat_1(B_63),A_64)
      | ~ v1_relat_1(B_63)
      | ~ v1_relat_1(B_63) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_309])).

tff(c_834,plain,(
    ! [A_78,B_79] :
      ( k2_relat_1(k7_relat_1(k5_relat_1(A_78,B_79),k1_relat_1(A_78))) = k2_relat_1(k5_relat_1(A_78,B_79))
      | ~ v1_relat_1(k5_relat_1(A_78,B_79))
      | ~ v1_relat_1(B_79)
      | ~ v1_relat_1(A_78) ) ),
    inference(resolution,[status(thm)],[c_12,c_481])).

tff(c_4411,plain,(
    ! [A_173,B_174] :
      ( k9_relat_1(k5_relat_1(A_173,B_174),k1_relat_1(A_173)) = k2_relat_1(k5_relat_1(A_173,B_174))
      | ~ v1_relat_1(k5_relat_1(A_173,B_174))
      | ~ v1_relat_1(B_174)
      | ~ v1_relat_1(A_173)
      | ~ v1_relat_1(k5_relat_1(A_173,B_174)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_834])).

tff(c_48295,plain,(
    ! [C_579,B_580] :
      ( k9_relat_1(C_579,k9_relat_1(B_580,k1_relat_1(B_580))) = k2_relat_1(k5_relat_1(B_580,C_579))
      | ~ v1_relat_1(k5_relat_1(B_580,C_579))
      | ~ v1_relat_1(C_579)
      | ~ v1_relat_1(B_580)
      | ~ v1_relat_1(k5_relat_1(B_580,C_579))
      | ~ v1_relat_1(C_579)
      | ~ v1_relat_1(B_580) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_4411])).

tff(c_51141,plain,(
    ! [C_598,A_599] :
      ( k9_relat_1(C_598,k2_relat_1(A_599)) = k2_relat_1(k5_relat_1(A_599,C_598))
      | ~ v1_relat_1(k5_relat_1(A_599,C_598))
      | ~ v1_relat_1(C_598)
      | ~ v1_relat_1(A_599)
      | ~ v1_relat_1(k5_relat_1(A_599,C_598))
      | ~ v1_relat_1(C_598)
      | ~ v1_relat_1(A_599)
      | ~ v1_relat_1(A_599) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_48295])).

tff(c_51149,plain,(
    ! [B_600,A_601] :
      ( k9_relat_1(B_600,k2_relat_1(A_601)) = k2_relat_1(k5_relat_1(A_601,B_600))
      | ~ v1_relat_1(k5_relat_1(A_601,B_600))
      | ~ v1_relat_1(B_600)
      | ~ v1_relat_1(A_601) ) ),
    inference(resolution,[status(thm)],[c_2,c_51141])).

tff(c_51159,plain,(
    ! [B_602,A_603] :
      ( k9_relat_1(B_602,k2_relat_1(A_603)) = k2_relat_1(k5_relat_1(A_603,B_602))
      | ~ v1_relat_1(B_602)
      | ~ v1_relat_1(A_603) ) ),
    inference(resolution,[status(thm)],[c_2,c_51149])).

tff(c_22,plain,(
    k9_relat_1('#skF_2',k2_relat_1('#skF_1')) != k2_relat_1(k5_relat_1('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_51684,plain,
    ( ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_51159,c_22])).

tff(c_52182,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_24,c_51684])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:08:02 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 17.99/8.94  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 17.99/8.94  
% 17.99/8.94  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 17.99/8.94  %$ r1_tarski > v1_relat_1 > k9_relat_1 > k7_relat_1 > k5_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_relat_1 > #skF_2 > #skF_1
% 17.99/8.94  
% 17.99/8.94  %Foreground sorts:
% 17.99/8.94  
% 17.99/8.94  
% 17.99/8.94  %Background operators:
% 17.99/8.94  
% 17.99/8.94  
% 17.99/8.94  %Foreground operators:
% 17.99/8.94  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 17.99/8.94  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 17.99/8.94  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 17.99/8.94  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 17.99/8.94  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 17.99/8.94  tff('#skF_2', type, '#skF_2': $i).
% 17.99/8.94  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 17.99/8.94  tff('#skF_1', type, '#skF_1': $i).
% 17.99/8.94  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 17.99/8.94  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 17.99/8.94  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 17.99/8.94  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 17.99/8.94  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 17.99/8.94  
% 17.99/8.96  tff(f_80, negated_conjecture, ~(![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k2_relat_1(k5_relat_1(A, B)) = k9_relat_1(B, k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t160_relat_1)).
% 17.99/8.96  tff(f_31, axiom, (![A, B]: ((v1_relat_1(A) & v1_relat_1(B)) => v1_relat_1(k5_relat_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k5_relat_1)).
% 17.99/8.96  tff(f_37, axiom, (![A]: (v1_relat_1(A) => (k9_relat_1(A, k1_relat_1(A)) = k2_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t146_relat_1)).
% 17.99/8.96  tff(f_48, axiom, (![A, B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (k9_relat_1(k5_relat_1(B, C), A) = k9_relat_1(C, k9_relat_1(B, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t159_relat_1)).
% 17.99/8.96  tff(f_41, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_relat_1)).
% 17.99/8.96  tff(f_55, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k5_relat_1(A, B)), k1_relat_1(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_relat_1)).
% 17.99/8.96  tff(f_72, axiom, (![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k5_relat_1(k6_relat_1(A), B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t94_relat_1)).
% 17.99/8.96  tff(f_33, axiom, (![A]: v1_relat_1(k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 17.99/8.96  tff(f_68, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 17.99/8.96  tff(f_64, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(A), k2_relat_1(B)) => (k2_relat_1(k5_relat_1(B, A)) = k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_relat_1)).
% 17.99/8.96  tff(c_26, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_80])).
% 17.99/8.96  tff(c_24, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_80])).
% 17.99/8.96  tff(c_2, plain, (![A_1, B_2]: (v1_relat_1(k5_relat_1(A_1, B_2)) | ~v1_relat_1(B_2) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 17.99/8.96  tff(c_6, plain, (![A_4]: (k9_relat_1(A_4, k1_relat_1(A_4))=k2_relat_1(A_4) | ~v1_relat_1(A_4))), inference(cnfTransformation, [status(thm)], [f_37])).
% 17.99/8.96  tff(c_10, plain, (![B_8, C_10, A_7]: (k9_relat_1(k5_relat_1(B_8, C_10), A_7)=k9_relat_1(C_10, k9_relat_1(B_8, A_7)) | ~v1_relat_1(C_10) | ~v1_relat_1(B_8))), inference(cnfTransformation, [status(thm)], [f_48])).
% 17.99/8.96  tff(c_8, plain, (![B_6, A_5]: (k2_relat_1(k7_relat_1(B_6, A_5))=k9_relat_1(B_6, A_5) | ~v1_relat_1(B_6))), inference(cnfTransformation, [status(thm)], [f_41])).
% 17.99/8.96  tff(c_12, plain, (![A_11, B_13]: (r1_tarski(k1_relat_1(k5_relat_1(A_11, B_13)), k1_relat_1(A_11)) | ~v1_relat_1(B_13) | ~v1_relat_1(A_11))), inference(cnfTransformation, [status(thm)], [f_55])).
% 17.99/8.96  tff(c_20, plain, (![A_18, B_19]: (k5_relat_1(k6_relat_1(A_18), B_19)=k7_relat_1(B_19, A_18) | ~v1_relat_1(B_19))), inference(cnfTransformation, [status(thm)], [f_72])).
% 17.99/8.96  tff(c_4, plain, (![A_3]: (v1_relat_1(k6_relat_1(A_3)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 17.99/8.96  tff(c_18, plain, (![A_17]: (k2_relat_1(k6_relat_1(A_17))=A_17)), inference(cnfTransformation, [status(thm)], [f_68])).
% 17.99/8.96  tff(c_199, plain, (![B_48, A_49]: (k2_relat_1(k5_relat_1(B_48, A_49))=k2_relat_1(A_49) | ~r1_tarski(k1_relat_1(A_49), k2_relat_1(B_48)) | ~v1_relat_1(B_48) | ~v1_relat_1(A_49))), inference(cnfTransformation, [status(thm)], [f_64])).
% 17.99/8.96  tff(c_216, plain, (![A_17, A_49]: (k2_relat_1(k5_relat_1(k6_relat_1(A_17), A_49))=k2_relat_1(A_49) | ~r1_tarski(k1_relat_1(A_49), A_17) | ~v1_relat_1(k6_relat_1(A_17)) | ~v1_relat_1(A_49))), inference(superposition, [status(thm), theory('equality')], [c_18, c_199])).
% 17.99/8.96  tff(c_309, plain, (![A_56, A_57]: (k2_relat_1(k5_relat_1(k6_relat_1(A_56), A_57))=k2_relat_1(A_57) | ~r1_tarski(k1_relat_1(A_57), A_56) | ~v1_relat_1(A_57))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_216])).
% 17.99/8.96  tff(c_481, plain, (![B_63, A_64]: (k2_relat_1(k7_relat_1(B_63, A_64))=k2_relat_1(B_63) | ~r1_tarski(k1_relat_1(B_63), A_64) | ~v1_relat_1(B_63) | ~v1_relat_1(B_63))), inference(superposition, [status(thm), theory('equality')], [c_20, c_309])).
% 17.99/8.96  tff(c_834, plain, (![A_78, B_79]: (k2_relat_1(k7_relat_1(k5_relat_1(A_78, B_79), k1_relat_1(A_78)))=k2_relat_1(k5_relat_1(A_78, B_79)) | ~v1_relat_1(k5_relat_1(A_78, B_79)) | ~v1_relat_1(B_79) | ~v1_relat_1(A_78))), inference(resolution, [status(thm)], [c_12, c_481])).
% 17.99/8.96  tff(c_4411, plain, (![A_173, B_174]: (k9_relat_1(k5_relat_1(A_173, B_174), k1_relat_1(A_173))=k2_relat_1(k5_relat_1(A_173, B_174)) | ~v1_relat_1(k5_relat_1(A_173, B_174)) | ~v1_relat_1(B_174) | ~v1_relat_1(A_173) | ~v1_relat_1(k5_relat_1(A_173, B_174)))), inference(superposition, [status(thm), theory('equality')], [c_8, c_834])).
% 17.99/8.96  tff(c_48295, plain, (![C_579, B_580]: (k9_relat_1(C_579, k9_relat_1(B_580, k1_relat_1(B_580)))=k2_relat_1(k5_relat_1(B_580, C_579)) | ~v1_relat_1(k5_relat_1(B_580, C_579)) | ~v1_relat_1(C_579) | ~v1_relat_1(B_580) | ~v1_relat_1(k5_relat_1(B_580, C_579)) | ~v1_relat_1(C_579) | ~v1_relat_1(B_580))), inference(superposition, [status(thm), theory('equality')], [c_10, c_4411])).
% 17.99/8.96  tff(c_51141, plain, (![C_598, A_599]: (k9_relat_1(C_598, k2_relat_1(A_599))=k2_relat_1(k5_relat_1(A_599, C_598)) | ~v1_relat_1(k5_relat_1(A_599, C_598)) | ~v1_relat_1(C_598) | ~v1_relat_1(A_599) | ~v1_relat_1(k5_relat_1(A_599, C_598)) | ~v1_relat_1(C_598) | ~v1_relat_1(A_599) | ~v1_relat_1(A_599))), inference(superposition, [status(thm), theory('equality')], [c_6, c_48295])).
% 17.99/8.96  tff(c_51149, plain, (![B_600, A_601]: (k9_relat_1(B_600, k2_relat_1(A_601))=k2_relat_1(k5_relat_1(A_601, B_600)) | ~v1_relat_1(k5_relat_1(A_601, B_600)) | ~v1_relat_1(B_600) | ~v1_relat_1(A_601))), inference(resolution, [status(thm)], [c_2, c_51141])).
% 17.99/8.96  tff(c_51159, plain, (![B_602, A_603]: (k9_relat_1(B_602, k2_relat_1(A_603))=k2_relat_1(k5_relat_1(A_603, B_602)) | ~v1_relat_1(B_602) | ~v1_relat_1(A_603))), inference(resolution, [status(thm)], [c_2, c_51149])).
% 17.99/8.96  tff(c_22, plain, (k9_relat_1('#skF_2', k2_relat_1('#skF_1'))!=k2_relat_1(k5_relat_1('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_80])).
% 17.99/8.96  tff(c_51684, plain, (~v1_relat_1('#skF_2') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_51159, c_22])).
% 17.99/8.96  tff(c_52182, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_26, c_24, c_51684])).
% 17.99/8.96  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 17.99/8.96  
% 17.99/8.96  Inference rules
% 17.99/8.96  ----------------------
% 17.99/8.96  #Ref     : 0
% 17.99/8.96  #Sup     : 11906
% 17.99/8.96  #Fact    : 0
% 17.99/8.96  #Define  : 0
% 17.99/8.96  #Split   : 0
% 17.99/8.96  #Chain   : 0
% 17.99/8.96  #Close   : 0
% 17.99/8.96  
% 17.99/8.96  Ordering : KBO
% 17.99/8.96  
% 17.99/8.96  Simplification rules
% 17.99/8.96  ----------------------
% 17.99/8.96  #Subsume      : 2238
% 17.99/8.96  #Demod        : 9204
% 17.99/8.96  #Tautology    : 1730
% 17.99/8.96  #SimpNegUnit  : 0
% 17.99/8.96  #BackRed      : 21
% 17.99/8.96  
% 17.99/8.96  #Partial instantiations: 0
% 17.99/8.96  #Strategies tried      : 1
% 17.99/8.96  
% 17.99/8.96  Timing (in seconds)
% 17.99/8.96  ----------------------
% 17.99/8.96  Preprocessing        : 0.28
% 17.99/8.96  Parsing              : 0.15
% 17.99/8.96  CNF conversion       : 0.02
% 17.99/8.96  Main loop            : 7.88
% 17.99/8.96  Inferencing          : 2.09
% 17.99/8.96  Reduction            : 2.31
% 17.99/8.96  Demodulation         : 1.78
% 17.99/8.96  BG Simplification    : 0.38
% 17.99/8.96  Subsumption          : 2.75
% 17.99/8.96  Abstraction          : 0.59
% 17.99/8.96  MUC search           : 0.00
% 17.99/8.96  Cooper               : 0.00
% 17.99/8.96  Total                : 8.19
% 17.99/8.96  Index Insertion      : 0.00
% 17.99/8.96  Index Deletion       : 0.00
% 17.99/8.96  Index Matching       : 0.00
% 17.99/8.96  BG Taut test         : 0.00
%------------------------------------------------------------------------------
