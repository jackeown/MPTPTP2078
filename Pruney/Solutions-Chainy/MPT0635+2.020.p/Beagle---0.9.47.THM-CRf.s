%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:03:23 EST 2020

% Result     : Theorem 3.16s
% Output     : CNFRefutation 3.16s
% Verified   : 
% Statistics : Number of formulae       :   53 (  69 expanded)
%              Number of leaves         :   31 (  41 expanded)
%              Depth                    :    8
%              Number of atoms          :   85 ( 126 expanded)
%              Number of equality atoms :   16 (  24 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v1_relat_1 > v1_funct_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_relat_1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > k1_funct_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

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

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

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

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_96,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_relat_1(C)
          & v1_funct_1(C) )
       => ( r2_hidden(A,k3_xboole_0(k1_relat_1(C),B))
         => k1_funct_1(C,A) = k1_funct_1(k5_relat_1(k6_relat_1(B),C),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_funct_1)).

tff(f_49,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v1_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).

tff(f_45,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_87,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => k1_relat_1(k5_relat_1(k6_relat_1(A),B)) = k3_xboole_0(k1_relat_1(B),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_funct_1)).

tff(f_64,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ! [C] :
          ( ( v1_relat_1(C)
            & v1_funct_1(C) )
         => ( r2_hidden(A,k1_relat_1(k5_relat_1(C,B)))
          <=> ( r2_hidden(A,k1_relat_1(C))
              & r2_hidden(k1_funct_1(C,A),k1_relat_1(B)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_funct_1)).

tff(f_81,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => k1_funct_1(k6_relat_1(B),A) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_funct_1)).

tff(f_77,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ! [C] :
          ( ( v1_relat_1(C)
            & v1_funct_1(C) )
         => ( r2_hidden(A,k1_relat_1(k5_relat_1(C,B)))
           => k1_funct_1(k5_relat_1(C,B),A) = k1_funct_1(B,k1_funct_1(C,A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_funct_1)).

tff(c_44,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_42,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_40,plain,(
    r2_hidden('#skF_1',k3_xboole_0(k1_relat_1('#skF_3'),'#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_22,plain,(
    ! [A_33] : v1_relat_1(k6_relat_1(A_33)) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_24,plain,(
    ! [A_33] : v1_funct_1(k6_relat_1(A_33)) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_18,plain,(
    ! [A_32] : k1_relat_1(k6_relat_1(A_32)) = A_32 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_36,plain,(
    ! [A_44,B_45] :
      ( k1_relat_1(k5_relat_1(k6_relat_1(A_44),B_45)) = k3_xboole_0(k1_relat_1(B_45),A_44)
      | ~ v1_funct_1(B_45)
      | ~ v1_relat_1(B_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_284,plain,(
    ! [A_93,C_94,B_95] :
      ( r2_hidden(A_93,k1_relat_1(C_94))
      | ~ r2_hidden(A_93,k1_relat_1(k5_relat_1(C_94,B_95)))
      | ~ v1_funct_1(C_94)
      | ~ v1_relat_1(C_94)
      | ~ v1_funct_1(B_95)
      | ~ v1_relat_1(B_95) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_287,plain,(
    ! [A_93,A_44,B_45] :
      ( r2_hidden(A_93,k1_relat_1(k6_relat_1(A_44)))
      | ~ r2_hidden(A_93,k3_xboole_0(k1_relat_1(B_45),A_44))
      | ~ v1_funct_1(k6_relat_1(A_44))
      | ~ v1_relat_1(k6_relat_1(A_44))
      | ~ v1_funct_1(B_45)
      | ~ v1_relat_1(B_45)
      | ~ v1_funct_1(B_45)
      | ~ v1_relat_1(B_45) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_284])).

tff(c_290,plain,(
    ! [A_96,A_97,B_98] :
      ( r2_hidden(A_96,A_97)
      | ~ r2_hidden(A_96,k3_xboole_0(k1_relat_1(B_98),A_97))
      | ~ v1_funct_1(B_98)
      | ~ v1_relat_1(B_98) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_24,c_18,c_287])).

tff(c_296,plain,
    ( r2_hidden('#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_40,c_290])).

tff(c_302,plain,(
    r2_hidden('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_296])).

tff(c_34,plain,(
    ! [B_43,A_42] :
      ( k1_funct_1(k6_relat_1(B_43),A_42) = A_42
      | ~ r2_hidden(A_42,B_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_483,plain,(
    ! [C_130,B_131,A_132] :
      ( k1_funct_1(k5_relat_1(C_130,B_131),A_132) = k1_funct_1(B_131,k1_funct_1(C_130,A_132))
      | ~ r2_hidden(A_132,k1_relat_1(k5_relat_1(C_130,B_131)))
      | ~ v1_funct_1(C_130)
      | ~ v1_relat_1(C_130)
      | ~ v1_funct_1(B_131)
      | ~ v1_relat_1(B_131) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_501,plain,(
    ! [A_44,B_45,A_132] :
      ( k1_funct_1(k5_relat_1(k6_relat_1(A_44),B_45),A_132) = k1_funct_1(B_45,k1_funct_1(k6_relat_1(A_44),A_132))
      | ~ r2_hidden(A_132,k3_xboole_0(k1_relat_1(B_45),A_44))
      | ~ v1_funct_1(k6_relat_1(A_44))
      | ~ v1_relat_1(k6_relat_1(A_44))
      | ~ v1_funct_1(B_45)
      | ~ v1_relat_1(B_45)
      | ~ v1_funct_1(B_45)
      | ~ v1_relat_1(B_45) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_483])).

tff(c_842,plain,(
    ! [A_167,B_168,A_169] :
      ( k1_funct_1(k5_relat_1(k6_relat_1(A_167),B_168),A_169) = k1_funct_1(B_168,k1_funct_1(k6_relat_1(A_167),A_169))
      | ~ r2_hidden(A_169,k3_xboole_0(k1_relat_1(B_168),A_167))
      | ~ v1_funct_1(B_168)
      | ~ v1_relat_1(B_168) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_24,c_501])).

tff(c_864,plain,
    ( k1_funct_1(k5_relat_1(k6_relat_1('#skF_2'),'#skF_3'),'#skF_1') = k1_funct_1('#skF_3',k1_funct_1(k6_relat_1('#skF_2'),'#skF_1'))
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_40,c_842])).

tff(c_874,plain,(
    k1_funct_1(k5_relat_1(k6_relat_1('#skF_2'),'#skF_3'),'#skF_1') = k1_funct_1('#skF_3',k1_funct_1(k6_relat_1('#skF_2'),'#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_864])).

tff(c_38,plain,(
    k1_funct_1(k5_relat_1(k6_relat_1('#skF_2'),'#skF_3'),'#skF_1') != k1_funct_1('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_877,plain,(
    k1_funct_1('#skF_3',k1_funct_1(k6_relat_1('#skF_2'),'#skF_1')) != k1_funct_1('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_874,c_38])).

tff(c_890,plain,(
    ~ r2_hidden('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_877])).

tff(c_894,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_302,c_890])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n012.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 12:29:07 EST 2020
% 0.12/0.35  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.16/1.58  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.16/1.58  
% 3.16/1.58  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.16/1.59  %$ r2_hidden > v1_relat_1 > v1_funct_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_relat_1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > k1_funct_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 3.16/1.59  
% 3.16/1.59  %Foreground sorts:
% 3.16/1.59  
% 3.16/1.59  
% 3.16/1.59  %Background operators:
% 3.16/1.59  
% 3.16/1.59  
% 3.16/1.59  %Foreground operators:
% 3.16/1.59  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.16/1.59  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.16/1.59  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.16/1.59  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.16/1.59  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 3.16/1.59  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.16/1.59  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.16/1.59  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.16/1.59  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.16/1.59  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.16/1.59  tff('#skF_2', type, '#skF_2': $i).
% 3.16/1.59  tff('#skF_3', type, '#skF_3': $i).
% 3.16/1.59  tff('#skF_1', type, '#skF_1': $i).
% 3.16/1.59  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.16/1.59  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.16/1.59  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.16/1.59  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.16/1.59  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.16/1.59  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 3.16/1.59  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.16/1.59  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.16/1.59  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.16/1.59  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.16/1.59  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 3.16/1.59  
% 3.16/1.60  tff(f_96, negated_conjecture, ~(![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(A, k3_xboole_0(k1_relat_1(C), B)) => (k1_funct_1(C, A) = k1_funct_1(k5_relat_1(k6_relat_1(B), C), A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_funct_1)).
% 3.16/1.60  tff(f_49, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v1_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc3_funct_1)).
% 3.16/1.60  tff(f_45, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 3.16/1.60  tff(f_87, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (k1_relat_1(k5_relat_1(k6_relat_1(A), B)) = k3_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t37_funct_1)).
% 3.16/1.60  tff(f_64, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (![C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(A, k1_relat_1(k5_relat_1(C, B))) <=> (r2_hidden(A, k1_relat_1(C)) & r2_hidden(k1_funct_1(C, A), k1_relat_1(B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t21_funct_1)).
% 3.16/1.60  tff(f_81, axiom, (![A, B]: (r2_hidden(A, B) => (k1_funct_1(k6_relat_1(B), A) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t35_funct_1)).
% 3.16/1.60  tff(f_77, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (![C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(A, k1_relat_1(k5_relat_1(C, B))) => (k1_funct_1(k5_relat_1(C, B), A) = k1_funct_1(B, k1_funct_1(C, A)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t22_funct_1)).
% 3.16/1.60  tff(c_44, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_96])).
% 3.16/1.60  tff(c_42, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_96])).
% 3.16/1.60  tff(c_40, plain, (r2_hidden('#skF_1', k3_xboole_0(k1_relat_1('#skF_3'), '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_96])).
% 3.16/1.60  tff(c_22, plain, (![A_33]: (v1_relat_1(k6_relat_1(A_33)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.16/1.60  tff(c_24, plain, (![A_33]: (v1_funct_1(k6_relat_1(A_33)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.16/1.60  tff(c_18, plain, (![A_32]: (k1_relat_1(k6_relat_1(A_32))=A_32)), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.16/1.60  tff(c_36, plain, (![A_44, B_45]: (k1_relat_1(k5_relat_1(k6_relat_1(A_44), B_45))=k3_xboole_0(k1_relat_1(B_45), A_44) | ~v1_funct_1(B_45) | ~v1_relat_1(B_45))), inference(cnfTransformation, [status(thm)], [f_87])).
% 3.16/1.60  tff(c_284, plain, (![A_93, C_94, B_95]: (r2_hidden(A_93, k1_relat_1(C_94)) | ~r2_hidden(A_93, k1_relat_1(k5_relat_1(C_94, B_95))) | ~v1_funct_1(C_94) | ~v1_relat_1(C_94) | ~v1_funct_1(B_95) | ~v1_relat_1(B_95))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.16/1.60  tff(c_287, plain, (![A_93, A_44, B_45]: (r2_hidden(A_93, k1_relat_1(k6_relat_1(A_44))) | ~r2_hidden(A_93, k3_xboole_0(k1_relat_1(B_45), A_44)) | ~v1_funct_1(k6_relat_1(A_44)) | ~v1_relat_1(k6_relat_1(A_44)) | ~v1_funct_1(B_45) | ~v1_relat_1(B_45) | ~v1_funct_1(B_45) | ~v1_relat_1(B_45))), inference(superposition, [status(thm), theory('equality')], [c_36, c_284])).
% 3.16/1.60  tff(c_290, plain, (![A_96, A_97, B_98]: (r2_hidden(A_96, A_97) | ~r2_hidden(A_96, k3_xboole_0(k1_relat_1(B_98), A_97)) | ~v1_funct_1(B_98) | ~v1_relat_1(B_98))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_24, c_18, c_287])).
% 3.16/1.60  tff(c_296, plain, (r2_hidden('#skF_1', '#skF_2') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_40, c_290])).
% 3.16/1.60  tff(c_302, plain, (r2_hidden('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_296])).
% 3.16/1.60  tff(c_34, plain, (![B_43, A_42]: (k1_funct_1(k6_relat_1(B_43), A_42)=A_42 | ~r2_hidden(A_42, B_43))), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.16/1.60  tff(c_483, plain, (![C_130, B_131, A_132]: (k1_funct_1(k5_relat_1(C_130, B_131), A_132)=k1_funct_1(B_131, k1_funct_1(C_130, A_132)) | ~r2_hidden(A_132, k1_relat_1(k5_relat_1(C_130, B_131))) | ~v1_funct_1(C_130) | ~v1_relat_1(C_130) | ~v1_funct_1(B_131) | ~v1_relat_1(B_131))), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.16/1.60  tff(c_501, plain, (![A_44, B_45, A_132]: (k1_funct_1(k5_relat_1(k6_relat_1(A_44), B_45), A_132)=k1_funct_1(B_45, k1_funct_1(k6_relat_1(A_44), A_132)) | ~r2_hidden(A_132, k3_xboole_0(k1_relat_1(B_45), A_44)) | ~v1_funct_1(k6_relat_1(A_44)) | ~v1_relat_1(k6_relat_1(A_44)) | ~v1_funct_1(B_45) | ~v1_relat_1(B_45) | ~v1_funct_1(B_45) | ~v1_relat_1(B_45))), inference(superposition, [status(thm), theory('equality')], [c_36, c_483])).
% 3.16/1.60  tff(c_842, plain, (![A_167, B_168, A_169]: (k1_funct_1(k5_relat_1(k6_relat_1(A_167), B_168), A_169)=k1_funct_1(B_168, k1_funct_1(k6_relat_1(A_167), A_169)) | ~r2_hidden(A_169, k3_xboole_0(k1_relat_1(B_168), A_167)) | ~v1_funct_1(B_168) | ~v1_relat_1(B_168))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_24, c_501])).
% 3.16/1.60  tff(c_864, plain, (k1_funct_1(k5_relat_1(k6_relat_1('#skF_2'), '#skF_3'), '#skF_1')=k1_funct_1('#skF_3', k1_funct_1(k6_relat_1('#skF_2'), '#skF_1')) | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_40, c_842])).
% 3.16/1.60  tff(c_874, plain, (k1_funct_1(k5_relat_1(k6_relat_1('#skF_2'), '#skF_3'), '#skF_1')=k1_funct_1('#skF_3', k1_funct_1(k6_relat_1('#skF_2'), '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_864])).
% 3.16/1.60  tff(c_38, plain, (k1_funct_1(k5_relat_1(k6_relat_1('#skF_2'), '#skF_3'), '#skF_1')!=k1_funct_1('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_96])).
% 3.16/1.60  tff(c_877, plain, (k1_funct_1('#skF_3', k1_funct_1(k6_relat_1('#skF_2'), '#skF_1'))!=k1_funct_1('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_874, c_38])).
% 3.16/1.60  tff(c_890, plain, (~r2_hidden('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_34, c_877])).
% 3.16/1.60  tff(c_894, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_302, c_890])).
% 3.16/1.60  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.16/1.60  
% 3.16/1.60  Inference rules
% 3.16/1.60  ----------------------
% 3.16/1.60  #Ref     : 0
% 3.16/1.60  #Sup     : 187
% 3.16/1.60  #Fact    : 0
% 3.16/1.60  #Define  : 0
% 3.16/1.60  #Split   : 0
% 3.16/1.60  #Chain   : 0
% 3.16/1.60  #Close   : 0
% 3.16/1.60  
% 3.16/1.60  Ordering : KBO
% 3.16/1.60  
% 3.16/1.60  Simplification rules
% 3.16/1.60  ----------------------
% 3.16/1.60  #Subsume      : 11
% 3.16/1.60  #Demod        : 97
% 3.16/1.60  #Tautology    : 72
% 3.16/1.60  #SimpNegUnit  : 0
% 3.16/1.60  #BackRed      : 1
% 3.16/1.60  
% 3.16/1.60  #Partial instantiations: 0
% 3.16/1.60  #Strategies tried      : 1
% 3.16/1.60  
% 3.16/1.60  Timing (in seconds)
% 3.16/1.60  ----------------------
% 3.16/1.60  Preprocessing        : 0.35
% 3.16/1.60  Parsing              : 0.19
% 3.16/1.60  CNF conversion       : 0.02
% 3.16/1.60  Main loop            : 0.42
% 3.16/1.60  Inferencing          : 0.16
% 3.16/1.60  Reduction            : 0.13
% 3.16/1.60  Demodulation         : 0.10
% 3.16/1.60  BG Simplification    : 0.03
% 3.16/1.60  Subsumption          : 0.08
% 3.16/1.60  Abstraction          : 0.03
% 3.16/1.60  MUC search           : 0.00
% 3.16/1.60  Cooper               : 0.00
% 3.16/1.60  Total                : 0.80
% 3.16/1.60  Index Insertion      : 0.00
% 3.16/1.60  Index Deletion       : 0.00
% 3.16/1.60  Index Matching       : 0.00
% 3.16/1.60  BG Taut test         : 0.00
%------------------------------------------------------------------------------
