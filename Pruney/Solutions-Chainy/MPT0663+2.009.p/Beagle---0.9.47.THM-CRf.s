%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:04:12 EST 2020

% Result     : Theorem 3.37s
% Output     : CNFRefutation 3.37s
% Verified   : 
% Statistics : Number of formulae       :   45 (  54 expanded)
%              Number of leaves         :   24 (  30 expanded)
%              Depth                    :   10
%              Number of atoms          :   71 (  91 expanded)
%              Number of equality atoms :   30 (  38 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v1_relat_1 > v1_funct_1 > k7_relat_1 > k5_relat_1 > k3_xboole_0 > k1_funct_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_70,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_relat_1(C)
          & v1_funct_1(C) )
       => ( r2_hidden(A,k3_xboole_0(k1_relat_1(C),B))
         => k1_funct_1(k7_relat_1(C,B),A) = k1_funct_1(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_funct_1)).

tff(f_51,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v1_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).

tff(f_43,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_53,axiom,(
    ! [A,B] : k5_relat_1(k6_relat_1(B),k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_funct_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k7_relat_1(B,A) = k5_relat_1(k6_relat_1(A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).

tff(f_39,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ! [C] :
              ( v1_relat_1(C)
             => ( k1_relat_1(A) = k1_relat_1(B)
               => k1_relat_1(k5_relat_1(C,A)) = k1_relat_1(k5_relat_1(C,B)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t198_relat_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_61,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( r2_hidden(A,k1_relat_1(k7_relat_1(C,B)))
       => k1_funct_1(k7_relat_1(C,B),A) = k1_funct_1(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_funct_1)).

tff(c_26,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_24,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_12,plain,(
    ! [A_13] : v1_relat_1(k6_relat_1(A_13)) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_6,plain,(
    ! [A_10] : k1_relat_1(k6_relat_1(A_10)) = A_10 ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_16,plain,(
    ! [B_15,A_14] : k5_relat_1(k6_relat_1(B_15),k6_relat_1(A_14)) = k6_relat_1(k3_xboole_0(A_14,B_15)) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_10,plain,(
    ! [A_11,B_12] :
      ( k5_relat_1(k6_relat_1(A_11),B_12) = k7_relat_1(B_12,A_11)
      | ~ v1_relat_1(B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_120,plain,(
    ! [C_31,B_32,A_33] :
      ( k1_relat_1(k5_relat_1(C_31,B_32)) = k1_relat_1(k5_relat_1(C_31,A_33))
      | k1_relat_1(B_32) != k1_relat_1(A_33)
      | ~ v1_relat_1(C_31)
      | ~ v1_relat_1(B_32)
      | ~ v1_relat_1(A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_147,plain,(
    ! [B_12,A_11,A_33] :
      ( k1_relat_1(k7_relat_1(B_12,A_11)) = k1_relat_1(k5_relat_1(k6_relat_1(A_11),A_33))
      | k1_relat_1(B_12) != k1_relat_1(A_33)
      | ~ v1_relat_1(k6_relat_1(A_11))
      | ~ v1_relat_1(B_12)
      | ~ v1_relat_1(A_33)
      | ~ v1_relat_1(B_12) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_120])).

tff(c_404,plain,(
    ! [B_49,A_50,A_51] :
      ( k1_relat_1(k7_relat_1(B_49,A_50)) = k1_relat_1(k5_relat_1(k6_relat_1(A_50),A_51))
      | k1_relat_1(B_49) != k1_relat_1(A_51)
      | ~ v1_relat_1(A_51)
      | ~ v1_relat_1(B_49) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_147])).

tff(c_466,plain,(
    ! [B_49,B_15,A_14] :
      ( k1_relat_1(k7_relat_1(B_49,B_15)) = k1_relat_1(k6_relat_1(k3_xboole_0(A_14,B_15)))
      | k1_relat_1(k6_relat_1(A_14)) != k1_relat_1(B_49)
      | ~ v1_relat_1(k6_relat_1(A_14))
      | ~ v1_relat_1(B_49) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_404])).

tff(c_480,plain,(
    ! [A_52,B_53,B_54] :
      ( k3_xboole_0(A_52,B_53) = k1_relat_1(k7_relat_1(B_54,B_53))
      | k1_relat_1(B_54) != A_52
      | ~ v1_relat_1(B_54) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_6,c_6,c_466])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_545,plain,(
    ! [B_55,A_56,B_57] :
      ( k3_xboole_0(B_55,A_56) = k1_relat_1(k7_relat_1(B_57,B_55))
      | k1_relat_1(B_57) != A_56
      | ~ v1_relat_1(B_57) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_480,c_2])).

tff(c_22,plain,(
    r2_hidden('#skF_1',k3_xboole_0(k1_relat_1('#skF_3'),'#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_27,plain,(
    r2_hidden('#skF_1',k3_xboole_0('#skF_2',k1_relat_1('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_22])).

tff(c_611,plain,(
    ! [B_58] :
      ( r2_hidden('#skF_1',k1_relat_1(k7_relat_1(B_58,'#skF_2')))
      | k1_relat_1(B_58) != k1_relat_1('#skF_3')
      | ~ v1_relat_1(B_58) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_545,c_27])).

tff(c_18,plain,(
    ! [C_18,B_17,A_16] :
      ( k1_funct_1(k7_relat_1(C_18,B_17),A_16) = k1_funct_1(C_18,A_16)
      | ~ r2_hidden(A_16,k1_relat_1(k7_relat_1(C_18,B_17)))
      | ~ v1_funct_1(C_18)
      | ~ v1_relat_1(C_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_1421,plain,(
    ! [B_93] :
      ( k1_funct_1(k7_relat_1(B_93,'#skF_2'),'#skF_1') = k1_funct_1(B_93,'#skF_1')
      | ~ v1_funct_1(B_93)
      | k1_relat_1(B_93) != k1_relat_1('#skF_3')
      | ~ v1_relat_1(B_93) ) ),
    inference(resolution,[status(thm)],[c_611,c_18])).

tff(c_20,plain,(
    k1_funct_1(k7_relat_1('#skF_3','#skF_2'),'#skF_1') != k1_funct_1('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_1427,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1421,c_20])).

tff(c_1439,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_24,c_1427])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:19:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.37/1.62  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.37/1.63  
% 3.37/1.63  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.37/1.63  %$ r2_hidden > v1_relat_1 > v1_funct_1 > k7_relat_1 > k5_relat_1 > k3_xboole_0 > k1_funct_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 3.37/1.63  
% 3.37/1.63  %Foreground sorts:
% 3.37/1.63  
% 3.37/1.63  
% 3.37/1.63  %Background operators:
% 3.37/1.63  
% 3.37/1.63  
% 3.37/1.63  %Foreground operators:
% 3.37/1.63  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.37/1.63  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.37/1.63  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.37/1.63  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 3.37/1.63  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 3.37/1.63  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.37/1.63  tff('#skF_2', type, '#skF_2': $i).
% 3.37/1.63  tff('#skF_3', type, '#skF_3': $i).
% 3.37/1.63  tff('#skF_1', type, '#skF_1': $i).
% 3.37/1.63  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.37/1.63  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.37/1.63  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.37/1.63  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 3.37/1.63  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.37/1.63  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.37/1.63  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.37/1.63  
% 3.37/1.64  tff(f_70, negated_conjecture, ~(![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(A, k3_xboole_0(k1_relat_1(C), B)) => (k1_funct_1(k7_relat_1(C, B), A) = k1_funct_1(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_funct_1)).
% 3.37/1.64  tff(f_51, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v1_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc3_funct_1)).
% 3.37/1.64  tff(f_43, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 3.37/1.64  tff(f_53, axiom, (![A, B]: (k5_relat_1(k6_relat_1(B), k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_funct_1)).
% 3.37/1.64  tff(f_47, axiom, (![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k5_relat_1(k6_relat_1(A), B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t94_relat_1)).
% 3.37/1.64  tff(f_39, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => ((k1_relat_1(A) = k1_relat_1(B)) => (k1_relat_1(k5_relat_1(C, A)) = k1_relat_1(k5_relat_1(C, B)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t198_relat_1)).
% 3.37/1.64  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 3.37/1.64  tff(f_61, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(A, k1_relat_1(k7_relat_1(C, B))) => (k1_funct_1(k7_relat_1(C, B), A) = k1_funct_1(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_funct_1)).
% 3.37/1.64  tff(c_26, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.37/1.64  tff(c_24, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.37/1.64  tff(c_12, plain, (![A_13]: (v1_relat_1(k6_relat_1(A_13)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.37/1.64  tff(c_6, plain, (![A_10]: (k1_relat_1(k6_relat_1(A_10))=A_10)), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.37/1.64  tff(c_16, plain, (![B_15, A_14]: (k5_relat_1(k6_relat_1(B_15), k6_relat_1(A_14))=k6_relat_1(k3_xboole_0(A_14, B_15)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.37/1.64  tff(c_10, plain, (![A_11, B_12]: (k5_relat_1(k6_relat_1(A_11), B_12)=k7_relat_1(B_12, A_11) | ~v1_relat_1(B_12))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.37/1.64  tff(c_120, plain, (![C_31, B_32, A_33]: (k1_relat_1(k5_relat_1(C_31, B_32))=k1_relat_1(k5_relat_1(C_31, A_33)) | k1_relat_1(B_32)!=k1_relat_1(A_33) | ~v1_relat_1(C_31) | ~v1_relat_1(B_32) | ~v1_relat_1(A_33))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.37/1.64  tff(c_147, plain, (![B_12, A_11, A_33]: (k1_relat_1(k7_relat_1(B_12, A_11))=k1_relat_1(k5_relat_1(k6_relat_1(A_11), A_33)) | k1_relat_1(B_12)!=k1_relat_1(A_33) | ~v1_relat_1(k6_relat_1(A_11)) | ~v1_relat_1(B_12) | ~v1_relat_1(A_33) | ~v1_relat_1(B_12))), inference(superposition, [status(thm), theory('equality')], [c_10, c_120])).
% 3.37/1.64  tff(c_404, plain, (![B_49, A_50, A_51]: (k1_relat_1(k7_relat_1(B_49, A_50))=k1_relat_1(k5_relat_1(k6_relat_1(A_50), A_51)) | k1_relat_1(B_49)!=k1_relat_1(A_51) | ~v1_relat_1(A_51) | ~v1_relat_1(B_49))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_147])).
% 3.37/1.64  tff(c_466, plain, (![B_49, B_15, A_14]: (k1_relat_1(k7_relat_1(B_49, B_15))=k1_relat_1(k6_relat_1(k3_xboole_0(A_14, B_15))) | k1_relat_1(k6_relat_1(A_14))!=k1_relat_1(B_49) | ~v1_relat_1(k6_relat_1(A_14)) | ~v1_relat_1(B_49))), inference(superposition, [status(thm), theory('equality')], [c_16, c_404])).
% 3.37/1.64  tff(c_480, plain, (![A_52, B_53, B_54]: (k3_xboole_0(A_52, B_53)=k1_relat_1(k7_relat_1(B_54, B_53)) | k1_relat_1(B_54)!=A_52 | ~v1_relat_1(B_54))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_6, c_6, c_466])).
% 3.37/1.64  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.37/1.64  tff(c_545, plain, (![B_55, A_56, B_57]: (k3_xboole_0(B_55, A_56)=k1_relat_1(k7_relat_1(B_57, B_55)) | k1_relat_1(B_57)!=A_56 | ~v1_relat_1(B_57))), inference(superposition, [status(thm), theory('equality')], [c_480, c_2])).
% 3.37/1.64  tff(c_22, plain, (r2_hidden('#skF_1', k3_xboole_0(k1_relat_1('#skF_3'), '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.37/1.64  tff(c_27, plain, (r2_hidden('#skF_1', k3_xboole_0('#skF_2', k1_relat_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_22])).
% 3.37/1.64  tff(c_611, plain, (![B_58]: (r2_hidden('#skF_1', k1_relat_1(k7_relat_1(B_58, '#skF_2'))) | k1_relat_1(B_58)!=k1_relat_1('#skF_3') | ~v1_relat_1(B_58))), inference(superposition, [status(thm), theory('equality')], [c_545, c_27])).
% 3.37/1.64  tff(c_18, plain, (![C_18, B_17, A_16]: (k1_funct_1(k7_relat_1(C_18, B_17), A_16)=k1_funct_1(C_18, A_16) | ~r2_hidden(A_16, k1_relat_1(k7_relat_1(C_18, B_17))) | ~v1_funct_1(C_18) | ~v1_relat_1(C_18))), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.37/1.64  tff(c_1421, plain, (![B_93]: (k1_funct_1(k7_relat_1(B_93, '#skF_2'), '#skF_1')=k1_funct_1(B_93, '#skF_1') | ~v1_funct_1(B_93) | k1_relat_1(B_93)!=k1_relat_1('#skF_3') | ~v1_relat_1(B_93))), inference(resolution, [status(thm)], [c_611, c_18])).
% 3.37/1.64  tff(c_20, plain, (k1_funct_1(k7_relat_1('#skF_3', '#skF_2'), '#skF_1')!=k1_funct_1('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.37/1.64  tff(c_1427, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1421, c_20])).
% 3.37/1.64  tff(c_1439, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_26, c_24, c_1427])).
% 3.37/1.64  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.37/1.64  
% 3.37/1.64  Inference rules
% 3.37/1.64  ----------------------
% 3.37/1.64  #Ref     : 4
% 3.37/1.64  #Sup     : 397
% 3.37/1.64  #Fact    : 0
% 3.37/1.64  #Define  : 0
% 3.37/1.64  #Split   : 0
% 3.37/1.64  #Chain   : 0
% 3.37/1.64  #Close   : 0
% 3.37/1.64  
% 3.37/1.64  Ordering : KBO
% 3.37/1.64  
% 3.37/1.64  Simplification rules
% 3.37/1.64  ----------------------
% 3.37/1.64  #Subsume      : 79
% 3.37/1.64  #Demod        : 92
% 3.37/1.64  #Tautology    : 30
% 3.37/1.64  #SimpNegUnit  : 0
% 3.37/1.64  #BackRed      : 0
% 3.37/1.64  
% 3.37/1.64  #Partial instantiations: 0
% 3.37/1.64  #Strategies tried      : 1
% 3.37/1.64  
% 3.37/1.64  Timing (in seconds)
% 3.37/1.64  ----------------------
% 3.37/1.64  Preprocessing        : 0.28
% 3.37/1.64  Parsing              : 0.16
% 3.37/1.64  CNF conversion       : 0.02
% 3.37/1.64  Main loop            : 0.51
% 3.37/1.64  Inferencing          : 0.19
% 3.37/1.64  Reduction            : 0.17
% 3.37/1.64  Demodulation         : 0.13
% 3.37/1.64  BG Simplification    : 0.03
% 3.37/1.64  Subsumption          : 0.10
% 3.37/1.64  Abstraction          : 0.03
% 3.37/1.64  MUC search           : 0.00
% 3.37/1.64  Cooper               : 0.00
% 3.37/1.64  Total                : 0.82
% 3.37/1.64  Index Insertion      : 0.00
% 3.37/1.64  Index Deletion       : 0.00
% 3.37/1.64  Index Matching       : 0.00
% 3.37/1.64  BG Taut test         : 0.00
%------------------------------------------------------------------------------
