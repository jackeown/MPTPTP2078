%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:03:23 EST 2020

% Result     : Theorem 2.62s
% Output     : CNFRefutation 2.98s
% Verified   : 
% Statistics : Number of formulae       :   53 (  75 expanded)
%              Number of leaves         :   32 (  43 expanded)
%              Depth                    :    8
%              Number of atoms          :   65 ( 121 expanded)
%              Number of equality atoms :   15 (  25 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v1_relat_1 > v1_funct_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k7_relat_1 > k5_relat_1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > k1_funct_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

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

tff(f_87,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_relat_1(C)
          & v1_funct_1(C) )
       => ( r2_hidden(A,k3_xboole_0(k1_relat_1(C),B))
         => k1_funct_1(C,A) = k1_funct_1(k5_relat_1(k6_relat_1(B),C),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_funct_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k1_relat_1(k7_relat_1(B,A)) = k3_xboole_0(k1_relat_1(B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t90_relat_1)).

tff(f_53,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k1_relat_1(k7_relat_1(C,B)))
      <=> ( r2_hidden(A,B)
          & r2_hidden(A,k1_relat_1(C)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t86_relat_1)).

tff(f_78,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => k1_funct_1(k6_relat_1(B),A) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_funct_1)).

tff(f_61,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v1_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).

tff(f_45,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_74,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ! [C] :
          ( ( v1_relat_1(C)
            & v1_funct_1(C) )
         => ( r2_hidden(A,k1_relat_1(B))
           => k1_funct_1(k5_relat_1(B,C),A) = k1_funct_1(C,k1_funct_1(B,A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_funct_1)).

tff(c_44,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_116,plain,(
    ! [B_60,A_61] :
      ( k3_xboole_0(k1_relat_1(B_60),A_61) = k1_relat_1(k7_relat_1(B_60,A_61))
      | ~ v1_relat_1(B_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_40,plain,(
    r2_hidden('#skF_1',k3_xboole_0(k1_relat_1('#skF_3'),'#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_122,plain,
    ( r2_hidden('#skF_1',k1_relat_1(k7_relat_1('#skF_3','#skF_2')))
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_116,c_40])).

tff(c_131,plain,(
    r2_hidden('#skF_1',k1_relat_1(k7_relat_1('#skF_3','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_122])).

tff(c_172,plain,(
    ! [A_70,B_71,C_72] :
      ( r2_hidden(A_70,B_71)
      | ~ r2_hidden(A_70,k1_relat_1(k7_relat_1(C_72,B_71)))
      | ~ v1_relat_1(C_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_178,plain,
    ( r2_hidden('#skF_1','#skF_2')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_131,c_172])).

tff(c_183,plain,(
    r2_hidden('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_178])).

tff(c_36,plain,(
    ! [B_44,A_43] :
      ( k1_funct_1(k6_relat_1(B_44),A_43) = A_43
      | ~ r2_hidden(A_43,B_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_42,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_30,plain,(
    ! [A_38] : v1_relat_1(k6_relat_1(A_38)) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_32,plain,(
    ! [A_38] : v1_funct_1(k6_relat_1(A_38)) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_18,plain,(
    ! [A_32] : k1_relat_1(k6_relat_1(A_32)) = A_32 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_570,plain,(
    ! [B_122,C_123,A_124] :
      ( k1_funct_1(k5_relat_1(B_122,C_123),A_124) = k1_funct_1(C_123,k1_funct_1(B_122,A_124))
      | ~ r2_hidden(A_124,k1_relat_1(B_122))
      | ~ v1_funct_1(C_123)
      | ~ v1_relat_1(C_123)
      | ~ v1_funct_1(B_122)
      | ~ v1_relat_1(B_122) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_582,plain,(
    ! [A_32,C_123,A_124] :
      ( k1_funct_1(k5_relat_1(k6_relat_1(A_32),C_123),A_124) = k1_funct_1(C_123,k1_funct_1(k6_relat_1(A_32),A_124))
      | ~ r2_hidden(A_124,A_32)
      | ~ v1_funct_1(C_123)
      | ~ v1_relat_1(C_123)
      | ~ v1_funct_1(k6_relat_1(A_32))
      | ~ v1_relat_1(k6_relat_1(A_32)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_570])).

tff(c_725,plain,(
    ! [A_130,C_131,A_132] :
      ( k1_funct_1(k5_relat_1(k6_relat_1(A_130),C_131),A_132) = k1_funct_1(C_131,k1_funct_1(k6_relat_1(A_130),A_132))
      | ~ r2_hidden(A_132,A_130)
      | ~ v1_funct_1(C_131)
      | ~ v1_relat_1(C_131) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_32,c_582])).

tff(c_38,plain,(
    k1_funct_1(k5_relat_1(k6_relat_1('#skF_2'),'#skF_3'),'#skF_1') != k1_funct_1('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_731,plain,
    ( k1_funct_1('#skF_3',k1_funct_1(k6_relat_1('#skF_2'),'#skF_1')) != k1_funct_1('#skF_3','#skF_1')
    | ~ r2_hidden('#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_725,c_38])).

tff(c_737,plain,(
    k1_funct_1('#skF_3',k1_funct_1(k6_relat_1('#skF_2'),'#skF_1')) != k1_funct_1('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_183,c_731])).

tff(c_741,plain,(
    ~ r2_hidden('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_737])).

tff(c_745,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_183,c_741])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:27:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.62/1.47  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.98/1.47  
% 2.98/1.47  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.98/1.47  %$ r2_hidden > v1_relat_1 > v1_funct_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k7_relat_1 > k5_relat_1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > k1_funct_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 2.98/1.47  
% 2.98/1.47  %Foreground sorts:
% 2.98/1.47  
% 2.98/1.47  
% 2.98/1.47  %Background operators:
% 2.98/1.47  
% 2.98/1.47  
% 2.98/1.47  %Foreground operators:
% 2.98/1.47  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.98/1.47  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.98/1.47  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.98/1.47  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.98/1.47  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.98/1.47  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.98/1.47  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.98/1.47  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.98/1.47  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.98/1.47  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.98/1.47  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.98/1.47  tff('#skF_2', type, '#skF_2': $i).
% 2.98/1.47  tff('#skF_3', type, '#skF_3': $i).
% 2.98/1.47  tff('#skF_1', type, '#skF_1': $i).
% 2.98/1.47  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.98/1.47  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.98/1.47  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.98/1.47  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.98/1.47  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.98/1.47  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 2.98/1.47  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.98/1.47  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.98/1.47  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.98/1.47  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.98/1.47  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.98/1.47  
% 2.98/1.49  tff(f_87, negated_conjecture, ~(![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(A, k3_xboole_0(k1_relat_1(C), B)) => (k1_funct_1(C, A) = k1_funct_1(k5_relat_1(k6_relat_1(B), C), A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_funct_1)).
% 2.98/1.49  tff(f_57, axiom, (![A, B]: (v1_relat_1(B) => (k1_relat_1(k7_relat_1(B, A)) = k3_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t90_relat_1)).
% 2.98/1.49  tff(f_53, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k1_relat_1(k7_relat_1(C, B))) <=> (r2_hidden(A, B) & r2_hidden(A, k1_relat_1(C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t86_relat_1)).
% 2.98/1.49  tff(f_78, axiom, (![A, B]: (r2_hidden(A, B) => (k1_funct_1(k6_relat_1(B), A) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t35_funct_1)).
% 2.98/1.49  tff(f_61, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v1_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc3_funct_1)).
% 2.98/1.49  tff(f_45, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 2.98/1.49  tff(f_74, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (![C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(A, k1_relat_1(B)) => (k1_funct_1(k5_relat_1(B, C), A) = k1_funct_1(C, k1_funct_1(B, A)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t23_funct_1)).
% 2.98/1.49  tff(c_44, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.98/1.49  tff(c_116, plain, (![B_60, A_61]: (k3_xboole_0(k1_relat_1(B_60), A_61)=k1_relat_1(k7_relat_1(B_60, A_61)) | ~v1_relat_1(B_60))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.98/1.49  tff(c_40, plain, (r2_hidden('#skF_1', k3_xboole_0(k1_relat_1('#skF_3'), '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.98/1.49  tff(c_122, plain, (r2_hidden('#skF_1', k1_relat_1(k7_relat_1('#skF_3', '#skF_2'))) | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_116, c_40])).
% 2.98/1.49  tff(c_131, plain, (r2_hidden('#skF_1', k1_relat_1(k7_relat_1('#skF_3', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_122])).
% 2.98/1.49  tff(c_172, plain, (![A_70, B_71, C_72]: (r2_hidden(A_70, B_71) | ~r2_hidden(A_70, k1_relat_1(k7_relat_1(C_72, B_71))) | ~v1_relat_1(C_72))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.98/1.49  tff(c_178, plain, (r2_hidden('#skF_1', '#skF_2') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_131, c_172])).
% 2.98/1.49  tff(c_183, plain, (r2_hidden('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_178])).
% 2.98/1.49  tff(c_36, plain, (![B_44, A_43]: (k1_funct_1(k6_relat_1(B_44), A_43)=A_43 | ~r2_hidden(A_43, B_44))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.98/1.49  tff(c_42, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.98/1.49  tff(c_30, plain, (![A_38]: (v1_relat_1(k6_relat_1(A_38)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.98/1.49  tff(c_32, plain, (![A_38]: (v1_funct_1(k6_relat_1(A_38)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.98/1.49  tff(c_18, plain, (![A_32]: (k1_relat_1(k6_relat_1(A_32))=A_32)), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.98/1.49  tff(c_570, plain, (![B_122, C_123, A_124]: (k1_funct_1(k5_relat_1(B_122, C_123), A_124)=k1_funct_1(C_123, k1_funct_1(B_122, A_124)) | ~r2_hidden(A_124, k1_relat_1(B_122)) | ~v1_funct_1(C_123) | ~v1_relat_1(C_123) | ~v1_funct_1(B_122) | ~v1_relat_1(B_122))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.98/1.49  tff(c_582, plain, (![A_32, C_123, A_124]: (k1_funct_1(k5_relat_1(k6_relat_1(A_32), C_123), A_124)=k1_funct_1(C_123, k1_funct_1(k6_relat_1(A_32), A_124)) | ~r2_hidden(A_124, A_32) | ~v1_funct_1(C_123) | ~v1_relat_1(C_123) | ~v1_funct_1(k6_relat_1(A_32)) | ~v1_relat_1(k6_relat_1(A_32)))), inference(superposition, [status(thm), theory('equality')], [c_18, c_570])).
% 2.98/1.49  tff(c_725, plain, (![A_130, C_131, A_132]: (k1_funct_1(k5_relat_1(k6_relat_1(A_130), C_131), A_132)=k1_funct_1(C_131, k1_funct_1(k6_relat_1(A_130), A_132)) | ~r2_hidden(A_132, A_130) | ~v1_funct_1(C_131) | ~v1_relat_1(C_131))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_32, c_582])).
% 2.98/1.49  tff(c_38, plain, (k1_funct_1(k5_relat_1(k6_relat_1('#skF_2'), '#skF_3'), '#skF_1')!=k1_funct_1('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.98/1.49  tff(c_731, plain, (k1_funct_1('#skF_3', k1_funct_1(k6_relat_1('#skF_2'), '#skF_1'))!=k1_funct_1('#skF_3', '#skF_1') | ~r2_hidden('#skF_1', '#skF_2') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_725, c_38])).
% 2.98/1.49  tff(c_737, plain, (k1_funct_1('#skF_3', k1_funct_1(k6_relat_1('#skF_2'), '#skF_1'))!=k1_funct_1('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_183, c_731])).
% 2.98/1.49  tff(c_741, plain, (~r2_hidden('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_36, c_737])).
% 2.98/1.49  tff(c_745, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_183, c_741])).
% 2.98/1.49  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.98/1.49  
% 2.98/1.49  Inference rules
% 2.98/1.49  ----------------------
% 2.98/1.49  #Ref     : 0
% 2.98/1.49  #Sup     : 170
% 2.98/1.49  #Fact    : 0
% 2.98/1.49  #Define  : 0
% 2.98/1.49  #Split   : 0
% 2.98/1.49  #Chain   : 0
% 2.98/1.49  #Close   : 0
% 2.98/1.49  
% 2.98/1.49  Ordering : KBO
% 2.98/1.49  
% 2.98/1.49  Simplification rules
% 2.98/1.49  ----------------------
% 2.98/1.49  #Subsume      : 14
% 2.98/1.49  #Demod        : 122
% 2.98/1.49  #Tautology    : 78
% 2.98/1.49  #SimpNegUnit  : 0
% 2.98/1.49  #BackRed      : 0
% 2.98/1.49  
% 2.98/1.49  #Partial instantiations: 0
% 2.98/1.49  #Strategies tried      : 1
% 2.98/1.49  
% 2.98/1.49  Timing (in seconds)
% 3.02/1.49  ----------------------
% 3.02/1.49  Preprocessing        : 0.31
% 3.02/1.49  Parsing              : 0.17
% 3.02/1.49  CNF conversion       : 0.02
% 3.02/1.49  Main loop            : 0.40
% 3.02/1.49  Inferencing          : 0.16
% 3.02/1.49  Reduction            : 0.14
% 3.02/1.49  Demodulation         : 0.11
% 3.02/1.49  BG Simplification    : 0.03
% 3.02/1.49  Subsumption          : 0.05
% 3.02/1.49  Abstraction          : 0.03
% 3.02/1.49  MUC search           : 0.00
% 3.02/1.49  Cooper               : 0.00
% 3.02/1.49  Total                : 0.74
% 3.02/1.49  Index Insertion      : 0.00
% 3.02/1.49  Index Deletion       : 0.00
% 3.02/1.49  Index Matching       : 0.00
% 3.02/1.49  BG Taut test         : 0.00
%------------------------------------------------------------------------------
