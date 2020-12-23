%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:05:41 EST 2020

% Result     : Theorem 3.49s
% Output     : CNFRefutation 3.49s
% Verified   : 
% Statistics : Number of formulae       :   52 (  62 expanded)
%              Number of leaves         :   26 (  34 expanded)
%              Depth                    :   11
%              Number of atoms          :  103 ( 137 expanded)
%              Number of equality atoms :   12 (  15 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > v4_relat_1 > r2_hidden > v1_relat_1 > v1_funct_1 > k9_relat_1 > k7_relat_1 > k5_relat_1 > k1_funct_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

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

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

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

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_81,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_relat_1(B)
          & v5_relat_1(B,A)
          & v1_funct_1(B) )
       => ! [C] :
            ( r2_hidden(C,k1_relat_1(B))
           => r2_hidden(k1_funct_1(B,C),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t172_funct_1)).

tff(f_29,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k9_relat_1(A,k1_relat_1(A)) = k2_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_relat_1)).

tff(f_59,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v4_relat_1(k6_relat_1(A),A)
      & v5_relat_1(k6_relat_1(A),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc24_relat_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k7_relat_1(B,A) = k5_relat_1(k6_relat_1(A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).

tff(f_49,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_36,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k2_relat_1(k5_relat_1(A,B)) = k9_relat_1(B,k2_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t160_relat_1)).

tff(f_69,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( ( r2_hidden(A,k1_relat_1(C))
          & r2_hidden(A,B) )
       => r2_hidden(k1_funct_1(C,A),k2_relat_1(k7_relat_1(C,B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_funct_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A) )
     => ! [C] :
          ( r2_hidden(C,k2_relat_1(B))
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t202_relat_1)).

tff(c_30,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_26,plain,(
    v1_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_24,plain,(
    r2_hidden('#skF_3',k1_relat_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_28,plain,(
    v5_relat_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_2,plain,(
    ! [A_1] :
      ( k9_relat_1(A_1,k1_relat_1(A_1)) = k2_relat_1(A_1)
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_18,plain,(
    ! [A_12] : v5_relat_1(k6_relat_1(A_12),A_12) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_12,plain,(
    ! [A_10,B_11] :
      ( k5_relat_1(k6_relat_1(A_10),B_11) = k7_relat_1(B_11,A_10)
      | ~ v1_relat_1(B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_14,plain,(
    ! [A_12] : v1_relat_1(k6_relat_1(A_12)) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_10,plain,(
    ! [A_9] : k2_relat_1(k6_relat_1(A_9)) = A_9 ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_84,plain,(
    ! [B_26,A_27] :
      ( k9_relat_1(B_26,k2_relat_1(A_27)) = k2_relat_1(k5_relat_1(A_27,B_26))
      | ~ v1_relat_1(B_26)
      | ~ v1_relat_1(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_101,plain,(
    ! [A_9,B_26] :
      ( k2_relat_1(k5_relat_1(k6_relat_1(A_9),B_26)) = k9_relat_1(B_26,A_9)
      | ~ v1_relat_1(B_26)
      | ~ v1_relat_1(k6_relat_1(A_9)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_84])).

tff(c_110,plain,(
    ! [A_28,B_29] :
      ( k2_relat_1(k5_relat_1(k6_relat_1(A_28),B_29)) = k9_relat_1(B_29,A_28)
      | ~ v1_relat_1(B_29) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_101])).

tff(c_254,plain,(
    ! [B_43,A_44] :
      ( k2_relat_1(k7_relat_1(B_43,A_44)) = k9_relat_1(B_43,A_44)
      | ~ v1_relat_1(B_43)
      | ~ v1_relat_1(B_43) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_110])).

tff(c_20,plain,(
    ! [C_15,A_13,B_14] :
      ( r2_hidden(k1_funct_1(C_15,A_13),k2_relat_1(k7_relat_1(C_15,B_14)))
      | ~ r2_hidden(A_13,B_14)
      | ~ r2_hidden(A_13,k1_relat_1(C_15))
      | ~ v1_funct_1(C_15)
      | ~ v1_relat_1(C_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_1066,plain,(
    ! [B_110,A_111,A_112] :
      ( r2_hidden(k1_funct_1(B_110,A_111),k9_relat_1(B_110,A_112))
      | ~ r2_hidden(A_111,A_112)
      | ~ r2_hidden(A_111,k1_relat_1(B_110))
      | ~ v1_funct_1(B_110)
      | ~ v1_relat_1(B_110)
      | ~ v1_relat_1(B_110)
      | ~ v1_relat_1(B_110) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_254,c_20])).

tff(c_125,plain,(
    ! [C_30,A_31,B_32] :
      ( r2_hidden(C_30,A_31)
      | ~ r2_hidden(C_30,k2_relat_1(B_32))
      | ~ v5_relat_1(B_32,A_31)
      | ~ v1_relat_1(B_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_129,plain,(
    ! [C_30,A_31,A_9] :
      ( r2_hidden(C_30,A_31)
      | ~ r2_hidden(C_30,A_9)
      | ~ v5_relat_1(k6_relat_1(A_9),A_31)
      | ~ v1_relat_1(k6_relat_1(A_9)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_125])).

tff(c_131,plain,(
    ! [C_30,A_31,A_9] :
      ( r2_hidden(C_30,A_31)
      | ~ r2_hidden(C_30,A_9)
      | ~ v5_relat_1(k6_relat_1(A_9),A_31) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_129])).

tff(c_1204,plain,(
    ! [B_121,A_122,A_123,A_124] :
      ( r2_hidden(k1_funct_1(B_121,A_122),A_123)
      | ~ v5_relat_1(k6_relat_1(k9_relat_1(B_121,A_124)),A_123)
      | ~ r2_hidden(A_122,A_124)
      | ~ r2_hidden(A_122,k1_relat_1(B_121))
      | ~ v1_funct_1(B_121)
      | ~ v1_relat_1(B_121) ) ),
    inference(resolution,[status(thm)],[c_1066,c_131])).

tff(c_1225,plain,(
    ! [B_125,A_126,A_127] :
      ( r2_hidden(k1_funct_1(B_125,A_126),k9_relat_1(B_125,A_127))
      | ~ r2_hidden(A_126,A_127)
      | ~ r2_hidden(A_126,k1_relat_1(B_125))
      | ~ v1_funct_1(B_125)
      | ~ v1_relat_1(B_125) ) ),
    inference(resolution,[status(thm)],[c_18,c_1204])).

tff(c_1312,plain,(
    ! [A_131,A_132] :
      ( r2_hidden(k1_funct_1(A_131,A_132),k2_relat_1(A_131))
      | ~ r2_hidden(A_132,k1_relat_1(A_131))
      | ~ r2_hidden(A_132,k1_relat_1(A_131))
      | ~ v1_funct_1(A_131)
      | ~ v1_relat_1(A_131)
      | ~ v1_relat_1(A_131) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_1225])).

tff(c_6,plain,(
    ! [C_8,A_5,B_6] :
      ( r2_hidden(C_8,A_5)
      | ~ r2_hidden(C_8,k2_relat_1(B_6))
      | ~ v5_relat_1(B_6,A_5)
      | ~ v1_relat_1(B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_1381,plain,(
    ! [A_133,A_134,A_135] :
      ( r2_hidden(k1_funct_1(A_133,A_134),A_135)
      | ~ v5_relat_1(A_133,A_135)
      | ~ r2_hidden(A_134,k1_relat_1(A_133))
      | ~ v1_funct_1(A_133)
      | ~ v1_relat_1(A_133) ) ),
    inference(resolution,[status(thm)],[c_1312,c_6])).

tff(c_22,plain,(
    ~ r2_hidden(k1_funct_1('#skF_2','#skF_3'),'#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_1405,plain,
    ( ~ v5_relat_1('#skF_2','#skF_1')
    | ~ r2_hidden('#skF_3',k1_relat_1('#skF_2'))
    | ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_1381,c_22])).

tff(c_1417,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_26,c_24,c_28,c_1405])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:51:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.49/1.56  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.49/1.57  
% 3.49/1.57  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.49/1.57  %$ v5_relat_1 > v4_relat_1 > r2_hidden > v1_relat_1 > v1_funct_1 > k9_relat_1 > k7_relat_1 > k5_relat_1 > k1_funct_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 3.49/1.57  
% 3.49/1.57  %Foreground sorts:
% 3.49/1.57  
% 3.49/1.57  
% 3.49/1.57  %Background operators:
% 3.49/1.57  
% 3.49/1.57  
% 3.49/1.57  %Foreground operators:
% 3.49/1.57  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.49/1.57  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.49/1.57  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.49/1.57  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 3.49/1.57  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 3.49/1.57  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.49/1.57  tff('#skF_2', type, '#skF_2': $i).
% 3.49/1.57  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 3.49/1.57  tff('#skF_3', type, '#skF_3': $i).
% 3.49/1.57  tff('#skF_1', type, '#skF_1': $i).
% 3.49/1.57  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.49/1.57  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.49/1.57  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.49/1.57  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.49/1.57  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 3.49/1.57  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.49/1.57  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.49/1.57  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.49/1.57  
% 3.49/1.58  tff(f_81, negated_conjecture, ~(![A, B]: (((v1_relat_1(B) & v5_relat_1(B, A)) & v1_funct_1(B)) => (![C]: (r2_hidden(C, k1_relat_1(B)) => r2_hidden(k1_funct_1(B, C), A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t172_funct_1)).
% 3.49/1.58  tff(f_29, axiom, (![A]: (v1_relat_1(A) => (k9_relat_1(A, k1_relat_1(A)) = k2_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t146_relat_1)).
% 3.49/1.58  tff(f_59, axiom, (![A]: ((v1_relat_1(k6_relat_1(A)) & v4_relat_1(k6_relat_1(A), A)) & v5_relat_1(k6_relat_1(A), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc24_relat_1)).
% 3.49/1.58  tff(f_53, axiom, (![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k5_relat_1(k6_relat_1(A), B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t94_relat_1)).
% 3.49/1.58  tff(f_49, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 3.49/1.58  tff(f_36, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k2_relat_1(k5_relat_1(A, B)) = k9_relat_1(B, k2_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t160_relat_1)).
% 3.49/1.58  tff(f_69, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => ((r2_hidden(A, k1_relat_1(C)) & r2_hidden(A, B)) => r2_hidden(k1_funct_1(C, A), k2_relat_1(k7_relat_1(C, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_funct_1)).
% 3.49/1.58  tff(f_45, axiom, (![A, B]: ((v1_relat_1(B) & v5_relat_1(B, A)) => (![C]: (r2_hidden(C, k2_relat_1(B)) => r2_hidden(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t202_relat_1)).
% 3.49/1.58  tff(c_30, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.49/1.58  tff(c_26, plain, (v1_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.49/1.58  tff(c_24, plain, (r2_hidden('#skF_3', k1_relat_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.49/1.58  tff(c_28, plain, (v5_relat_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.49/1.58  tff(c_2, plain, (![A_1]: (k9_relat_1(A_1, k1_relat_1(A_1))=k2_relat_1(A_1) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.49/1.58  tff(c_18, plain, (![A_12]: (v5_relat_1(k6_relat_1(A_12), A_12))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.49/1.58  tff(c_12, plain, (![A_10, B_11]: (k5_relat_1(k6_relat_1(A_10), B_11)=k7_relat_1(B_11, A_10) | ~v1_relat_1(B_11))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.49/1.58  tff(c_14, plain, (![A_12]: (v1_relat_1(k6_relat_1(A_12)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.49/1.58  tff(c_10, plain, (![A_9]: (k2_relat_1(k6_relat_1(A_9))=A_9)), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.49/1.58  tff(c_84, plain, (![B_26, A_27]: (k9_relat_1(B_26, k2_relat_1(A_27))=k2_relat_1(k5_relat_1(A_27, B_26)) | ~v1_relat_1(B_26) | ~v1_relat_1(A_27))), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.49/1.58  tff(c_101, plain, (![A_9, B_26]: (k2_relat_1(k5_relat_1(k6_relat_1(A_9), B_26))=k9_relat_1(B_26, A_9) | ~v1_relat_1(B_26) | ~v1_relat_1(k6_relat_1(A_9)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_84])).
% 3.49/1.58  tff(c_110, plain, (![A_28, B_29]: (k2_relat_1(k5_relat_1(k6_relat_1(A_28), B_29))=k9_relat_1(B_29, A_28) | ~v1_relat_1(B_29))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_101])).
% 3.49/1.58  tff(c_254, plain, (![B_43, A_44]: (k2_relat_1(k7_relat_1(B_43, A_44))=k9_relat_1(B_43, A_44) | ~v1_relat_1(B_43) | ~v1_relat_1(B_43))), inference(superposition, [status(thm), theory('equality')], [c_12, c_110])).
% 3.49/1.58  tff(c_20, plain, (![C_15, A_13, B_14]: (r2_hidden(k1_funct_1(C_15, A_13), k2_relat_1(k7_relat_1(C_15, B_14))) | ~r2_hidden(A_13, B_14) | ~r2_hidden(A_13, k1_relat_1(C_15)) | ~v1_funct_1(C_15) | ~v1_relat_1(C_15))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.49/1.58  tff(c_1066, plain, (![B_110, A_111, A_112]: (r2_hidden(k1_funct_1(B_110, A_111), k9_relat_1(B_110, A_112)) | ~r2_hidden(A_111, A_112) | ~r2_hidden(A_111, k1_relat_1(B_110)) | ~v1_funct_1(B_110) | ~v1_relat_1(B_110) | ~v1_relat_1(B_110) | ~v1_relat_1(B_110))), inference(superposition, [status(thm), theory('equality')], [c_254, c_20])).
% 3.49/1.58  tff(c_125, plain, (![C_30, A_31, B_32]: (r2_hidden(C_30, A_31) | ~r2_hidden(C_30, k2_relat_1(B_32)) | ~v5_relat_1(B_32, A_31) | ~v1_relat_1(B_32))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.49/1.58  tff(c_129, plain, (![C_30, A_31, A_9]: (r2_hidden(C_30, A_31) | ~r2_hidden(C_30, A_9) | ~v5_relat_1(k6_relat_1(A_9), A_31) | ~v1_relat_1(k6_relat_1(A_9)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_125])).
% 3.49/1.58  tff(c_131, plain, (![C_30, A_31, A_9]: (r2_hidden(C_30, A_31) | ~r2_hidden(C_30, A_9) | ~v5_relat_1(k6_relat_1(A_9), A_31))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_129])).
% 3.49/1.58  tff(c_1204, plain, (![B_121, A_122, A_123, A_124]: (r2_hidden(k1_funct_1(B_121, A_122), A_123) | ~v5_relat_1(k6_relat_1(k9_relat_1(B_121, A_124)), A_123) | ~r2_hidden(A_122, A_124) | ~r2_hidden(A_122, k1_relat_1(B_121)) | ~v1_funct_1(B_121) | ~v1_relat_1(B_121))), inference(resolution, [status(thm)], [c_1066, c_131])).
% 3.49/1.58  tff(c_1225, plain, (![B_125, A_126, A_127]: (r2_hidden(k1_funct_1(B_125, A_126), k9_relat_1(B_125, A_127)) | ~r2_hidden(A_126, A_127) | ~r2_hidden(A_126, k1_relat_1(B_125)) | ~v1_funct_1(B_125) | ~v1_relat_1(B_125))), inference(resolution, [status(thm)], [c_18, c_1204])).
% 3.49/1.58  tff(c_1312, plain, (![A_131, A_132]: (r2_hidden(k1_funct_1(A_131, A_132), k2_relat_1(A_131)) | ~r2_hidden(A_132, k1_relat_1(A_131)) | ~r2_hidden(A_132, k1_relat_1(A_131)) | ~v1_funct_1(A_131) | ~v1_relat_1(A_131) | ~v1_relat_1(A_131))), inference(superposition, [status(thm), theory('equality')], [c_2, c_1225])).
% 3.49/1.58  tff(c_6, plain, (![C_8, A_5, B_6]: (r2_hidden(C_8, A_5) | ~r2_hidden(C_8, k2_relat_1(B_6)) | ~v5_relat_1(B_6, A_5) | ~v1_relat_1(B_6))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.49/1.58  tff(c_1381, plain, (![A_133, A_134, A_135]: (r2_hidden(k1_funct_1(A_133, A_134), A_135) | ~v5_relat_1(A_133, A_135) | ~r2_hidden(A_134, k1_relat_1(A_133)) | ~v1_funct_1(A_133) | ~v1_relat_1(A_133))), inference(resolution, [status(thm)], [c_1312, c_6])).
% 3.49/1.58  tff(c_22, plain, (~r2_hidden(k1_funct_1('#skF_2', '#skF_3'), '#skF_1')), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.49/1.58  tff(c_1405, plain, (~v5_relat_1('#skF_2', '#skF_1') | ~r2_hidden('#skF_3', k1_relat_1('#skF_2')) | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_1381, c_22])).
% 3.49/1.58  tff(c_1417, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_30, c_26, c_24, c_28, c_1405])).
% 3.49/1.58  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.49/1.58  
% 3.49/1.58  Inference rules
% 3.49/1.58  ----------------------
% 3.49/1.58  #Ref     : 0
% 3.49/1.58  #Sup     : 358
% 3.49/1.58  #Fact    : 0
% 3.49/1.58  #Define  : 0
% 3.49/1.58  #Split   : 3
% 3.49/1.58  #Chain   : 0
% 3.49/1.58  #Close   : 0
% 3.49/1.58  
% 3.49/1.58  Ordering : KBO
% 3.49/1.58  
% 3.49/1.58  Simplification rules
% 3.49/1.58  ----------------------
% 3.49/1.58  #Subsume      : 38
% 3.49/1.58  #Demod        : 301
% 3.49/1.58  #Tautology    : 89
% 3.49/1.58  #SimpNegUnit  : 0
% 3.49/1.58  #BackRed      : 0
% 3.49/1.58  
% 3.49/1.58  #Partial instantiations: 0
% 3.49/1.58  #Strategies tried      : 1
% 3.49/1.58  
% 3.49/1.58  Timing (in seconds)
% 3.49/1.58  ----------------------
% 3.49/1.58  Preprocessing        : 0.28
% 3.49/1.58  Parsing              : 0.15
% 3.49/1.58  CNF conversion       : 0.02
% 3.49/1.58  Main loop            : 0.54
% 3.49/1.58  Inferencing          : 0.19
% 3.49/1.58  Reduction            : 0.18
% 3.49/1.58  Demodulation         : 0.13
% 3.49/1.58  BG Simplification    : 0.03
% 3.49/1.58  Subsumption          : 0.11
% 3.49/1.59  Abstraction          : 0.04
% 3.49/1.59  MUC search           : 0.00
% 3.49/1.59  Cooper               : 0.00
% 3.49/1.59  Total                : 0.84
% 3.49/1.59  Index Insertion      : 0.00
% 3.49/1.59  Index Deletion       : 0.00
% 3.49/1.59  Index Matching       : 0.00
% 3.49/1.59  BG Taut test         : 0.00
%------------------------------------------------------------------------------
