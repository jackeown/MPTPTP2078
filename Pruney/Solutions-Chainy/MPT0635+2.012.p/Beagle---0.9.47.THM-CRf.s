%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:03:22 EST 2020

% Result     : Theorem 3.23s
% Output     : CNFRefutation 3.23s
% Verified   : 
% Statistics : Number of formulae       :   57 ( 107 expanded)
%              Number of leaves         :   30 (  53 expanded)
%              Depth                    :    9
%              Number of atoms          :   92 ( 207 expanded)
%              Number of equality atoms :   20 (  47 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v1_relat_1 > v1_funct_1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k7_relat_1 > k5_relat_1 > k3_xboole_0 > k2_tarski > k1_funct_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

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

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

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

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_92,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_relat_1(C)
          & v1_funct_1(C) )
       => ( r2_hidden(A,k3_xboole_0(k1_relat_1(C),B))
         => k1_funct_1(C,A) = k1_funct_1(k5_relat_1(k6_relat_1(B),C),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_funct_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k1_relat_1(k7_relat_1(B,A)) = k3_xboole_0(k1_relat_1(B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t90_relat_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_51,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v1_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).

tff(f_39,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k7_relat_1(B,A) = k5_relat_1(k6_relat_1(A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).

tff(f_66,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ! [C] :
          ( ( v1_relat_1(C)
            & v1_funct_1(C) )
         => ( r2_hidden(A,k1_relat_1(k5_relat_1(C,B)))
          <=> ( r2_hidden(A,k1_relat_1(C))
              & r2_hidden(k1_funct_1(C,A),k1_relat_1(B)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_funct_1)).

tff(f_83,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => k1_funct_1(k6_relat_1(B),A) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_funct_1)).

tff(f_79,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ! [C] :
          ( ( v1_relat_1(C)
            & v1_funct_1(C) )
         => ( r2_hidden(A,k1_relat_1(B))
           => k1_funct_1(k5_relat_1(B,C),A) = k1_funct_1(C,k1_funct_1(B,A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_funct_1)).

tff(c_40,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_38,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_145,plain,(
    ! [B_47,A_48] :
      ( k3_xboole_0(k1_relat_1(B_47),A_48) = k1_relat_1(k7_relat_1(B_47,A_48))
      | ~ v1_relat_1(B_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_185,plain,(
    ! [A_51,B_52] :
      ( k3_xboole_0(A_51,k1_relat_1(B_52)) = k1_relat_1(k7_relat_1(B_52,A_51))
      | ~ v1_relat_1(B_52) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_145,c_2])).

tff(c_36,plain,(
    r2_hidden('#skF_1',k3_xboole_0(k1_relat_1('#skF_3'),'#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_41,plain,(
    r2_hidden('#skF_1',k3_xboole_0('#skF_2',k1_relat_1('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_36])).

tff(c_201,plain,
    ( r2_hidden('#skF_1',k1_relat_1(k7_relat_1('#skF_3','#skF_2')))
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_185,c_41])).

tff(c_225,plain,(
    r2_hidden('#skF_1',k1_relat_1(k7_relat_1('#skF_3','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_201])).

tff(c_20,plain,(
    ! [A_19] : v1_relat_1(k6_relat_1(A_19)) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_22,plain,(
    ! [A_19] : v1_funct_1(k6_relat_1(A_19)) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_12,plain,(
    ! [A_14] : k1_relat_1(k6_relat_1(A_14)) = A_14 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_18,plain,(
    ! [A_17,B_18] :
      ( k5_relat_1(k6_relat_1(A_17),B_18) = k7_relat_1(B_18,A_17)
      | ~ v1_relat_1(B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_347,plain,(
    ! [A_59,C_60,B_61] :
      ( r2_hidden(A_59,k1_relat_1(C_60))
      | ~ r2_hidden(A_59,k1_relat_1(k5_relat_1(C_60,B_61)))
      | ~ v1_funct_1(C_60)
      | ~ v1_relat_1(C_60)
      | ~ v1_funct_1(B_61)
      | ~ v1_relat_1(B_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_350,plain,(
    ! [A_59,A_17,B_18] :
      ( r2_hidden(A_59,k1_relat_1(k6_relat_1(A_17)))
      | ~ r2_hidden(A_59,k1_relat_1(k7_relat_1(B_18,A_17)))
      | ~ v1_funct_1(k6_relat_1(A_17))
      | ~ v1_relat_1(k6_relat_1(A_17))
      | ~ v1_funct_1(B_18)
      | ~ v1_relat_1(B_18)
      | ~ v1_relat_1(B_18) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_347])).

tff(c_353,plain,(
    ! [A_62,A_63,B_64] :
      ( r2_hidden(A_62,A_63)
      | ~ r2_hidden(A_62,k1_relat_1(k7_relat_1(B_64,A_63)))
      | ~ v1_funct_1(B_64)
      | ~ v1_relat_1(B_64) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_22,c_12,c_350])).

tff(c_362,plain,
    ( r2_hidden('#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_225,c_353])).

tff(c_368,plain,(
    r2_hidden('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_362])).

tff(c_32,plain,(
    ! [B_29,A_28] :
      ( k1_funct_1(k6_relat_1(B_29),A_28) = A_28
      | ~ r2_hidden(A_28,B_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_523,plain,(
    ! [B_86,C_87,A_88] :
      ( k1_funct_1(k5_relat_1(B_86,C_87),A_88) = k1_funct_1(C_87,k1_funct_1(B_86,A_88))
      | ~ r2_hidden(A_88,k1_relat_1(B_86))
      | ~ v1_funct_1(C_87)
      | ~ v1_relat_1(C_87)
      | ~ v1_funct_1(B_86)
      | ~ v1_relat_1(B_86) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_540,plain,(
    ! [A_14,C_87,A_88] :
      ( k1_funct_1(k5_relat_1(k6_relat_1(A_14),C_87),A_88) = k1_funct_1(C_87,k1_funct_1(k6_relat_1(A_14),A_88))
      | ~ r2_hidden(A_88,A_14)
      | ~ v1_funct_1(C_87)
      | ~ v1_relat_1(C_87)
      | ~ v1_funct_1(k6_relat_1(A_14))
      | ~ v1_relat_1(k6_relat_1(A_14)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_523])).

tff(c_1261,plain,(
    ! [A_141,C_142,A_143] :
      ( k1_funct_1(k5_relat_1(k6_relat_1(A_141),C_142),A_143) = k1_funct_1(C_142,k1_funct_1(k6_relat_1(A_141),A_143))
      | ~ r2_hidden(A_143,A_141)
      | ~ v1_funct_1(C_142)
      | ~ v1_relat_1(C_142) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_22,c_540])).

tff(c_34,plain,(
    k1_funct_1(k5_relat_1(k6_relat_1('#skF_2'),'#skF_3'),'#skF_1') != k1_funct_1('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_1273,plain,
    ( k1_funct_1('#skF_3',k1_funct_1(k6_relat_1('#skF_2'),'#skF_1')) != k1_funct_1('#skF_3','#skF_1')
    | ~ r2_hidden('#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1261,c_34])).

tff(c_1282,plain,(
    k1_funct_1('#skF_3',k1_funct_1(k6_relat_1('#skF_2'),'#skF_1')) != k1_funct_1('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_368,c_1273])).

tff(c_1286,plain,(
    ~ r2_hidden('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_1282])).

tff(c_1290,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_368,c_1286])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 10:39:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.23/1.61  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.23/1.62  
% 3.23/1.62  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.23/1.62  %$ r2_hidden > v1_relat_1 > v1_funct_1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k7_relat_1 > k5_relat_1 > k3_xboole_0 > k2_tarski > k1_funct_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 3.23/1.62  
% 3.23/1.62  %Foreground sorts:
% 3.23/1.62  
% 3.23/1.62  
% 3.23/1.62  %Background operators:
% 3.23/1.62  
% 3.23/1.62  
% 3.23/1.62  %Foreground operators:
% 3.23/1.62  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.23/1.62  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.23/1.62  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.23/1.62  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 3.23/1.62  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 3.23/1.62  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.23/1.62  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.23/1.62  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.23/1.62  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.23/1.62  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.23/1.62  tff('#skF_2', type, '#skF_2': $i).
% 3.23/1.62  tff('#skF_3', type, '#skF_3': $i).
% 3.23/1.62  tff('#skF_1', type, '#skF_1': $i).
% 3.23/1.62  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.23/1.62  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.23/1.62  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.23/1.62  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 3.23/1.62  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.23/1.62  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.23/1.62  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.23/1.62  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 3.23/1.62  
% 3.23/1.63  tff(f_92, negated_conjecture, ~(![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(A, k3_xboole_0(k1_relat_1(C), B)) => (k1_funct_1(C, A) = k1_funct_1(k5_relat_1(k6_relat_1(B), C), A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_funct_1)).
% 3.23/1.63  tff(f_43, axiom, (![A, B]: (v1_relat_1(B) => (k1_relat_1(k7_relat_1(B, A)) = k3_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t90_relat_1)).
% 3.23/1.63  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 3.23/1.63  tff(f_51, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v1_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc3_funct_1)).
% 3.23/1.63  tff(f_39, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 3.23/1.63  tff(f_47, axiom, (![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k5_relat_1(k6_relat_1(A), B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t94_relat_1)).
% 3.23/1.63  tff(f_66, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (![C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(A, k1_relat_1(k5_relat_1(C, B))) <=> (r2_hidden(A, k1_relat_1(C)) & r2_hidden(k1_funct_1(C, A), k1_relat_1(B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t21_funct_1)).
% 3.23/1.63  tff(f_83, axiom, (![A, B]: (r2_hidden(A, B) => (k1_funct_1(k6_relat_1(B), A) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t35_funct_1)).
% 3.23/1.63  tff(f_79, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (![C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(A, k1_relat_1(B)) => (k1_funct_1(k5_relat_1(B, C), A) = k1_funct_1(C, k1_funct_1(B, A)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t23_funct_1)).
% 3.23/1.63  tff(c_40, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_92])).
% 3.23/1.63  tff(c_38, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_92])).
% 3.23/1.63  tff(c_145, plain, (![B_47, A_48]: (k3_xboole_0(k1_relat_1(B_47), A_48)=k1_relat_1(k7_relat_1(B_47, A_48)) | ~v1_relat_1(B_47))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.23/1.63  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.23/1.63  tff(c_185, plain, (![A_51, B_52]: (k3_xboole_0(A_51, k1_relat_1(B_52))=k1_relat_1(k7_relat_1(B_52, A_51)) | ~v1_relat_1(B_52))), inference(superposition, [status(thm), theory('equality')], [c_145, c_2])).
% 3.23/1.63  tff(c_36, plain, (r2_hidden('#skF_1', k3_xboole_0(k1_relat_1('#skF_3'), '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_92])).
% 3.23/1.63  tff(c_41, plain, (r2_hidden('#skF_1', k3_xboole_0('#skF_2', k1_relat_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_36])).
% 3.23/1.63  tff(c_201, plain, (r2_hidden('#skF_1', k1_relat_1(k7_relat_1('#skF_3', '#skF_2'))) | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_185, c_41])).
% 3.23/1.63  tff(c_225, plain, (r2_hidden('#skF_1', k1_relat_1(k7_relat_1('#skF_3', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_201])).
% 3.23/1.63  tff(c_20, plain, (![A_19]: (v1_relat_1(k6_relat_1(A_19)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.23/1.63  tff(c_22, plain, (![A_19]: (v1_funct_1(k6_relat_1(A_19)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.23/1.63  tff(c_12, plain, (![A_14]: (k1_relat_1(k6_relat_1(A_14))=A_14)), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.23/1.63  tff(c_18, plain, (![A_17, B_18]: (k5_relat_1(k6_relat_1(A_17), B_18)=k7_relat_1(B_18, A_17) | ~v1_relat_1(B_18))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.23/1.63  tff(c_347, plain, (![A_59, C_60, B_61]: (r2_hidden(A_59, k1_relat_1(C_60)) | ~r2_hidden(A_59, k1_relat_1(k5_relat_1(C_60, B_61))) | ~v1_funct_1(C_60) | ~v1_relat_1(C_60) | ~v1_funct_1(B_61) | ~v1_relat_1(B_61))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.23/1.63  tff(c_350, plain, (![A_59, A_17, B_18]: (r2_hidden(A_59, k1_relat_1(k6_relat_1(A_17))) | ~r2_hidden(A_59, k1_relat_1(k7_relat_1(B_18, A_17))) | ~v1_funct_1(k6_relat_1(A_17)) | ~v1_relat_1(k6_relat_1(A_17)) | ~v1_funct_1(B_18) | ~v1_relat_1(B_18) | ~v1_relat_1(B_18))), inference(superposition, [status(thm), theory('equality')], [c_18, c_347])).
% 3.23/1.63  tff(c_353, plain, (![A_62, A_63, B_64]: (r2_hidden(A_62, A_63) | ~r2_hidden(A_62, k1_relat_1(k7_relat_1(B_64, A_63))) | ~v1_funct_1(B_64) | ~v1_relat_1(B_64))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_22, c_12, c_350])).
% 3.23/1.63  tff(c_362, plain, (r2_hidden('#skF_1', '#skF_2') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_225, c_353])).
% 3.23/1.63  tff(c_368, plain, (r2_hidden('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_362])).
% 3.23/1.63  tff(c_32, plain, (![B_29, A_28]: (k1_funct_1(k6_relat_1(B_29), A_28)=A_28 | ~r2_hidden(A_28, B_29))), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.23/1.63  tff(c_523, plain, (![B_86, C_87, A_88]: (k1_funct_1(k5_relat_1(B_86, C_87), A_88)=k1_funct_1(C_87, k1_funct_1(B_86, A_88)) | ~r2_hidden(A_88, k1_relat_1(B_86)) | ~v1_funct_1(C_87) | ~v1_relat_1(C_87) | ~v1_funct_1(B_86) | ~v1_relat_1(B_86))), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.23/1.63  tff(c_540, plain, (![A_14, C_87, A_88]: (k1_funct_1(k5_relat_1(k6_relat_1(A_14), C_87), A_88)=k1_funct_1(C_87, k1_funct_1(k6_relat_1(A_14), A_88)) | ~r2_hidden(A_88, A_14) | ~v1_funct_1(C_87) | ~v1_relat_1(C_87) | ~v1_funct_1(k6_relat_1(A_14)) | ~v1_relat_1(k6_relat_1(A_14)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_523])).
% 3.23/1.63  tff(c_1261, plain, (![A_141, C_142, A_143]: (k1_funct_1(k5_relat_1(k6_relat_1(A_141), C_142), A_143)=k1_funct_1(C_142, k1_funct_1(k6_relat_1(A_141), A_143)) | ~r2_hidden(A_143, A_141) | ~v1_funct_1(C_142) | ~v1_relat_1(C_142))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_22, c_540])).
% 3.23/1.63  tff(c_34, plain, (k1_funct_1(k5_relat_1(k6_relat_1('#skF_2'), '#skF_3'), '#skF_1')!=k1_funct_1('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_92])).
% 3.23/1.63  tff(c_1273, plain, (k1_funct_1('#skF_3', k1_funct_1(k6_relat_1('#skF_2'), '#skF_1'))!=k1_funct_1('#skF_3', '#skF_1') | ~r2_hidden('#skF_1', '#skF_2') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1261, c_34])).
% 3.23/1.63  tff(c_1282, plain, (k1_funct_1('#skF_3', k1_funct_1(k6_relat_1('#skF_2'), '#skF_1'))!=k1_funct_1('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_368, c_1273])).
% 3.23/1.63  tff(c_1286, plain, (~r2_hidden('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_32, c_1282])).
% 3.23/1.63  tff(c_1290, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_368, c_1286])).
% 3.23/1.63  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.23/1.63  
% 3.23/1.63  Inference rules
% 3.23/1.63  ----------------------
% 3.23/1.63  #Ref     : 0
% 3.23/1.63  #Sup     : 298
% 3.23/1.63  #Fact    : 0
% 3.23/1.63  #Define  : 0
% 3.23/1.63  #Split   : 1
% 3.23/1.63  #Chain   : 0
% 3.23/1.63  #Close   : 0
% 3.23/1.63  
% 3.23/1.63  Ordering : KBO
% 3.23/1.63  
% 3.23/1.63  Simplification rules
% 3.23/1.63  ----------------------
% 3.23/1.63  #Subsume      : 68
% 3.23/1.63  #Demod        : 133
% 3.23/1.63  #Tautology    : 69
% 3.23/1.63  #SimpNegUnit  : 9
% 3.23/1.63  #BackRed      : 4
% 3.23/1.63  
% 3.23/1.63  #Partial instantiations: 0
% 3.23/1.63  #Strategies tried      : 1
% 3.23/1.63  
% 3.63/1.63  Timing (in seconds)
% 3.63/1.63  ----------------------
% 3.63/1.63  Preprocessing        : 0.34
% 3.63/1.63  Parsing              : 0.18
% 3.63/1.63  CNF conversion       : 0.02
% 3.63/1.63  Main loop            : 0.47
% 3.63/1.63  Inferencing          : 0.17
% 3.63/1.63  Reduction            : 0.16
% 3.63/1.63  Demodulation         : 0.12
% 3.63/1.63  BG Simplification    : 0.03
% 3.63/1.63  Subsumption          : 0.09
% 3.63/1.63  Abstraction          : 0.03
% 3.63/1.63  MUC search           : 0.00
% 3.63/1.63  Cooper               : 0.00
% 3.63/1.64  Total                : 0.84
% 3.63/1.64  Index Insertion      : 0.00
% 3.63/1.64  Index Deletion       : 0.00
% 3.63/1.64  Index Matching       : 0.00
% 3.63/1.64  BG Taut test         : 0.00
%------------------------------------------------------------------------------
