%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:05:32 EST 2020

% Result     : Theorem 6.51s
% Output     : CNFRefutation 6.59s
% Verified   : 
% Statistics : Number of formulae       :   69 ( 111 expanded)
%              Number of leaves         :   35 (  54 expanded)
%              Depth                    :    9
%              Number of atoms          :   97 ( 187 expanded)
%              Number of equality atoms :   25 (  42 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > v1_relat_1 > v1_funct_1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k4_xboole_0 > k2_xboole_0 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_33,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_98,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_relat_1(B)
          & v1_funct_1(B) )
       => r1_tarski(k2_relat_1(k7_relat_1(B,k1_tarski(A))),k1_tarski(k1_funct_1(B,A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t167_funct_1)).

tff(f_35,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).

tff(f_81,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( r1_xboole_0(B,k1_relat_1(A))
         => k7_relat_1(A,B) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t187_relat_1)).

tff(f_62,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k7_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).

tff(f_72,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_74,axiom,(
    ! [A] : k9_relat_1(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t150_relat_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_58,axiom,(
    ! [A,B] :
      ( ~ r2_hidden(A,B)
     => r1_xboole_0(k1_tarski(A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l27_zfmisc_1)).

tff(f_45,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_91,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( ( r2_hidden(A,k1_relat_1(C))
          & r2_hidden(B,k1_relat_1(C)) )
       => k9_relat_1(C,k2_tarski(A,B)) = k2_tarski(k1_funct_1(C,A),k1_funct_1(C,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t118_funct_1)).

tff(c_8,plain,(
    ! [A_3] : r1_tarski(k1_xboole_0,A_3) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_44,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_10,plain,(
    ! [A_4,B_5] : r1_xboole_0(k4_xboole_0(A_4,B_5),B_5) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_127,plain,(
    ! [A_66,B_67] :
      ( k7_relat_1(A_66,B_67) = k1_xboole_0
      | ~ r1_xboole_0(B_67,k1_relat_1(A_66))
      | ~ v1_relat_1(A_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_147,plain,(
    ! [A_72,A_73] :
      ( k7_relat_1(A_72,k4_xboole_0(A_73,k1_relat_1(A_72))) = k1_xboole_0
      | ~ v1_relat_1(A_72) ) ),
    inference(resolution,[status(thm)],[c_10,c_127])).

tff(c_28,plain,(
    ! [A_28,B_29] :
      ( v1_relat_1(k7_relat_1(A_28,B_29))
      | ~ v1_relat_1(A_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_156,plain,(
    ! [A_72] :
      ( v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(A_72)
      | ~ v1_relat_1(A_72) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_147,c_28])).

tff(c_163,plain,(
    ! [A_74] :
      ( ~ v1_relat_1(A_74)
      | ~ v1_relat_1(A_74) ) ),
    inference(splitLeft,[status(thm)],[c_156])).

tff(c_167,plain,(
    ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_44,c_163])).

tff(c_172,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_167])).

tff(c_173,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_156])).

tff(c_32,plain,(
    ! [B_34,A_33] :
      ( k2_relat_1(k7_relat_1(B_34,A_33)) = k9_relat_1(B_34,A_33)
      | ~ v1_relat_1(B_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_216,plain,(
    ! [A_83,A_84] :
      ( k9_relat_1(A_83,k4_xboole_0(A_84,k1_relat_1(A_83))) = k2_relat_1(k1_xboole_0)
      | ~ v1_relat_1(A_83)
      | ~ v1_relat_1(A_83) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_147,c_32])).

tff(c_34,plain,(
    ! [A_35] : k9_relat_1(k1_xboole_0,A_35) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_223,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0
    | ~ v1_relat_1(k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_216,c_34])).

tff(c_233,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_173,c_173,c_223])).

tff(c_42,plain,(
    v1_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_26,plain,(
    ! [A_26,B_27] :
      ( r1_xboole_0(k1_tarski(A_26),B_27)
      | r2_hidden(A_26,B_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_136,plain,(
    ! [A_66,A_26] :
      ( k7_relat_1(A_66,k1_tarski(A_26)) = k1_xboole_0
      | ~ v1_relat_1(A_66)
      | r2_hidden(A_26,k1_relat_1(A_66)) ) ),
    inference(resolution,[status(thm)],[c_26,c_127])).

tff(c_16,plain,(
    ! [A_11] : k2_tarski(A_11,A_11) = k1_tarski(A_11) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_324,plain,(
    ! [C_99,A_100,B_101] :
      ( k2_tarski(k1_funct_1(C_99,A_100),k1_funct_1(C_99,B_101)) = k9_relat_1(C_99,k2_tarski(A_100,B_101))
      | ~ r2_hidden(B_101,k1_relat_1(C_99))
      | ~ r2_hidden(A_100,k1_relat_1(C_99))
      | ~ v1_funct_1(C_99)
      | ~ v1_relat_1(C_99) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_331,plain,(
    ! [C_99,B_101] :
      ( k9_relat_1(C_99,k2_tarski(B_101,B_101)) = k1_tarski(k1_funct_1(C_99,B_101))
      | ~ r2_hidden(B_101,k1_relat_1(C_99))
      | ~ r2_hidden(B_101,k1_relat_1(C_99))
      | ~ v1_funct_1(C_99)
      | ~ v1_relat_1(C_99) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_324,c_16])).

tff(c_789,plain,(
    ! [C_115,B_116] :
      ( k9_relat_1(C_115,k1_tarski(B_116)) = k1_tarski(k1_funct_1(C_115,B_116))
      | ~ r2_hidden(B_116,k1_relat_1(C_115))
      | ~ r2_hidden(B_116,k1_relat_1(C_115))
      | ~ v1_funct_1(C_115)
      | ~ v1_relat_1(C_115) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_331])).

tff(c_2596,plain,(
    ! [A_179,A_180] :
      ( k9_relat_1(A_179,k1_tarski(A_180)) = k1_tarski(k1_funct_1(A_179,A_180))
      | ~ r2_hidden(A_180,k1_relat_1(A_179))
      | ~ v1_funct_1(A_179)
      | k7_relat_1(A_179,k1_tarski(A_180)) = k1_xboole_0
      | ~ v1_relat_1(A_179) ) ),
    inference(resolution,[status(thm)],[c_136,c_789])).

tff(c_8235,plain,(
    ! [A_295,A_296] :
      ( k9_relat_1(A_295,k1_tarski(A_296)) = k1_tarski(k1_funct_1(A_295,A_296))
      | ~ v1_funct_1(A_295)
      | k7_relat_1(A_295,k1_tarski(A_296)) = k1_xboole_0
      | ~ v1_relat_1(A_295) ) ),
    inference(resolution,[status(thm)],[c_136,c_2596])).

tff(c_112,plain,(
    ! [B_62,A_63] :
      ( k2_relat_1(k7_relat_1(B_62,A_63)) = k9_relat_1(B_62,A_63)
      | ~ v1_relat_1(B_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_40,plain,(
    ~ r1_tarski(k2_relat_1(k7_relat_1('#skF_2',k1_tarski('#skF_1'))),k1_tarski(k1_funct_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_118,plain,
    ( ~ r1_tarski(k9_relat_1('#skF_2',k1_tarski('#skF_1')),k1_tarski(k1_funct_1('#skF_2','#skF_1')))
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_112,c_40])).

tff(c_124,plain,(
    ~ r1_tarski(k9_relat_1('#skF_2',k1_tarski('#skF_1')),k1_tarski(k1_funct_1('#skF_2','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_118])).

tff(c_8281,plain,
    ( ~ r1_tarski(k1_tarski(k1_funct_1('#skF_2','#skF_1')),k1_tarski(k1_funct_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_2')
    | k7_relat_1('#skF_2',k1_tarski('#skF_1')) = k1_xboole_0
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_8235,c_124])).

tff(c_8339,plain,(
    k7_relat_1('#skF_2',k1_tarski('#skF_1')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_6,c_8281])).

tff(c_8349,plain,(
    ~ r1_tarski(k2_relat_1(k1_xboole_0),k1_tarski(k1_funct_1('#skF_2','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8339,c_40])).

tff(c_8352,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_233,c_8349])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:28:54 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.51/2.29  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.51/2.29  
% 6.51/2.29  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.59/2.29  %$ r2_hidden > r1_xboole_0 > r1_tarski > v1_relat_1 > v1_funct_1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k4_xboole_0 > k2_xboole_0 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1
% 6.59/2.29  
% 6.59/2.29  %Foreground sorts:
% 6.59/2.29  
% 6.59/2.29  
% 6.59/2.29  %Background operators:
% 6.59/2.29  
% 6.59/2.29  
% 6.59/2.29  %Foreground operators:
% 6.59/2.29  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 6.59/2.29  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.59/2.29  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 6.59/2.29  tff(k1_tarski, type, k1_tarski: $i > $i).
% 6.59/2.29  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 6.59/2.29  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 6.59/2.29  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 6.59/2.29  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 6.59/2.29  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.59/2.29  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 6.59/2.29  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 6.59/2.29  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 6.59/2.29  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 6.59/2.29  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 6.59/2.29  tff('#skF_2', type, '#skF_2': $i).
% 6.59/2.29  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 6.59/2.29  tff('#skF_1', type, '#skF_1': $i).
% 6.59/2.29  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 6.59/2.29  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 6.59/2.29  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.59/2.29  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 6.59/2.29  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.59/2.29  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 6.59/2.29  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 6.59/2.29  
% 6.59/2.30  tff(f_33, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 6.59/2.30  tff(f_98, negated_conjecture, ~(![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => r1_tarski(k2_relat_1(k7_relat_1(B, k1_tarski(A))), k1_tarski(k1_funct_1(B, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t167_funct_1)).
% 6.59/2.30  tff(f_35, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_xboole_1)).
% 6.59/2.30  tff(f_81, axiom, (![A]: (v1_relat_1(A) => (![B]: (r1_xboole_0(B, k1_relat_1(A)) => (k7_relat_1(A, B) = k1_xboole_0))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t187_relat_1)).
% 6.59/2.30  tff(f_62, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k7_relat_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 6.59/2.30  tff(f_72, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_relat_1)).
% 6.59/2.30  tff(f_74, axiom, (![A]: (k9_relat_1(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t150_relat_1)).
% 6.59/2.30  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 6.59/2.30  tff(f_58, axiom, (![A, B]: (~r2_hidden(A, B) => r1_xboole_0(k1_tarski(A), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 6.59/2.30  tff(f_45, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 6.59/2.30  tff(f_91, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => ((r2_hidden(A, k1_relat_1(C)) & r2_hidden(B, k1_relat_1(C))) => (k9_relat_1(C, k2_tarski(A, B)) = k2_tarski(k1_funct_1(C, A), k1_funct_1(C, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t118_funct_1)).
% 6.59/2.30  tff(c_8, plain, (![A_3]: (r1_tarski(k1_xboole_0, A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 6.59/2.30  tff(c_44, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_98])).
% 6.59/2.30  tff(c_10, plain, (![A_4, B_5]: (r1_xboole_0(k4_xboole_0(A_4, B_5), B_5))), inference(cnfTransformation, [status(thm)], [f_35])).
% 6.59/2.30  tff(c_127, plain, (![A_66, B_67]: (k7_relat_1(A_66, B_67)=k1_xboole_0 | ~r1_xboole_0(B_67, k1_relat_1(A_66)) | ~v1_relat_1(A_66))), inference(cnfTransformation, [status(thm)], [f_81])).
% 6.59/2.30  tff(c_147, plain, (![A_72, A_73]: (k7_relat_1(A_72, k4_xboole_0(A_73, k1_relat_1(A_72)))=k1_xboole_0 | ~v1_relat_1(A_72))), inference(resolution, [status(thm)], [c_10, c_127])).
% 6.59/2.30  tff(c_28, plain, (![A_28, B_29]: (v1_relat_1(k7_relat_1(A_28, B_29)) | ~v1_relat_1(A_28))), inference(cnfTransformation, [status(thm)], [f_62])).
% 6.59/2.30  tff(c_156, plain, (![A_72]: (v1_relat_1(k1_xboole_0) | ~v1_relat_1(A_72) | ~v1_relat_1(A_72))), inference(superposition, [status(thm), theory('equality')], [c_147, c_28])).
% 6.59/2.30  tff(c_163, plain, (![A_74]: (~v1_relat_1(A_74) | ~v1_relat_1(A_74))), inference(splitLeft, [status(thm)], [c_156])).
% 6.59/2.30  tff(c_167, plain, (~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_44, c_163])).
% 6.59/2.30  tff(c_172, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_44, c_167])).
% 6.59/2.30  tff(c_173, plain, (v1_relat_1(k1_xboole_0)), inference(splitRight, [status(thm)], [c_156])).
% 6.59/2.30  tff(c_32, plain, (![B_34, A_33]: (k2_relat_1(k7_relat_1(B_34, A_33))=k9_relat_1(B_34, A_33) | ~v1_relat_1(B_34))), inference(cnfTransformation, [status(thm)], [f_72])).
% 6.59/2.30  tff(c_216, plain, (![A_83, A_84]: (k9_relat_1(A_83, k4_xboole_0(A_84, k1_relat_1(A_83)))=k2_relat_1(k1_xboole_0) | ~v1_relat_1(A_83) | ~v1_relat_1(A_83))), inference(superposition, [status(thm), theory('equality')], [c_147, c_32])).
% 6.59/2.30  tff(c_34, plain, (![A_35]: (k9_relat_1(k1_xboole_0, A_35)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_74])).
% 6.59/2.30  tff(c_223, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_216, c_34])).
% 6.59/2.30  tff(c_233, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_173, c_173, c_223])).
% 6.59/2.30  tff(c_42, plain, (v1_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_98])).
% 6.59/2.30  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 6.59/2.30  tff(c_26, plain, (![A_26, B_27]: (r1_xboole_0(k1_tarski(A_26), B_27) | r2_hidden(A_26, B_27))), inference(cnfTransformation, [status(thm)], [f_58])).
% 6.59/2.30  tff(c_136, plain, (![A_66, A_26]: (k7_relat_1(A_66, k1_tarski(A_26))=k1_xboole_0 | ~v1_relat_1(A_66) | r2_hidden(A_26, k1_relat_1(A_66)))), inference(resolution, [status(thm)], [c_26, c_127])).
% 6.59/2.30  tff(c_16, plain, (![A_11]: (k2_tarski(A_11, A_11)=k1_tarski(A_11))), inference(cnfTransformation, [status(thm)], [f_45])).
% 6.59/2.30  tff(c_324, plain, (![C_99, A_100, B_101]: (k2_tarski(k1_funct_1(C_99, A_100), k1_funct_1(C_99, B_101))=k9_relat_1(C_99, k2_tarski(A_100, B_101)) | ~r2_hidden(B_101, k1_relat_1(C_99)) | ~r2_hidden(A_100, k1_relat_1(C_99)) | ~v1_funct_1(C_99) | ~v1_relat_1(C_99))), inference(cnfTransformation, [status(thm)], [f_91])).
% 6.59/2.30  tff(c_331, plain, (![C_99, B_101]: (k9_relat_1(C_99, k2_tarski(B_101, B_101))=k1_tarski(k1_funct_1(C_99, B_101)) | ~r2_hidden(B_101, k1_relat_1(C_99)) | ~r2_hidden(B_101, k1_relat_1(C_99)) | ~v1_funct_1(C_99) | ~v1_relat_1(C_99))), inference(superposition, [status(thm), theory('equality')], [c_324, c_16])).
% 6.59/2.30  tff(c_789, plain, (![C_115, B_116]: (k9_relat_1(C_115, k1_tarski(B_116))=k1_tarski(k1_funct_1(C_115, B_116)) | ~r2_hidden(B_116, k1_relat_1(C_115)) | ~r2_hidden(B_116, k1_relat_1(C_115)) | ~v1_funct_1(C_115) | ~v1_relat_1(C_115))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_331])).
% 6.59/2.30  tff(c_2596, plain, (![A_179, A_180]: (k9_relat_1(A_179, k1_tarski(A_180))=k1_tarski(k1_funct_1(A_179, A_180)) | ~r2_hidden(A_180, k1_relat_1(A_179)) | ~v1_funct_1(A_179) | k7_relat_1(A_179, k1_tarski(A_180))=k1_xboole_0 | ~v1_relat_1(A_179))), inference(resolution, [status(thm)], [c_136, c_789])).
% 6.59/2.30  tff(c_8235, plain, (![A_295, A_296]: (k9_relat_1(A_295, k1_tarski(A_296))=k1_tarski(k1_funct_1(A_295, A_296)) | ~v1_funct_1(A_295) | k7_relat_1(A_295, k1_tarski(A_296))=k1_xboole_0 | ~v1_relat_1(A_295))), inference(resolution, [status(thm)], [c_136, c_2596])).
% 6.59/2.30  tff(c_112, plain, (![B_62, A_63]: (k2_relat_1(k7_relat_1(B_62, A_63))=k9_relat_1(B_62, A_63) | ~v1_relat_1(B_62))), inference(cnfTransformation, [status(thm)], [f_72])).
% 6.59/2.30  tff(c_40, plain, (~r1_tarski(k2_relat_1(k7_relat_1('#skF_2', k1_tarski('#skF_1'))), k1_tarski(k1_funct_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_98])).
% 6.59/2.30  tff(c_118, plain, (~r1_tarski(k9_relat_1('#skF_2', k1_tarski('#skF_1')), k1_tarski(k1_funct_1('#skF_2', '#skF_1'))) | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_112, c_40])).
% 6.59/2.30  tff(c_124, plain, (~r1_tarski(k9_relat_1('#skF_2', k1_tarski('#skF_1')), k1_tarski(k1_funct_1('#skF_2', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_118])).
% 6.59/2.30  tff(c_8281, plain, (~r1_tarski(k1_tarski(k1_funct_1('#skF_2', '#skF_1')), k1_tarski(k1_funct_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_2') | k7_relat_1('#skF_2', k1_tarski('#skF_1'))=k1_xboole_0 | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_8235, c_124])).
% 6.59/2.30  tff(c_8339, plain, (k7_relat_1('#skF_2', k1_tarski('#skF_1'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_6, c_8281])).
% 6.59/2.30  tff(c_8349, plain, (~r1_tarski(k2_relat_1(k1_xboole_0), k1_tarski(k1_funct_1('#skF_2', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_8339, c_40])).
% 6.59/2.30  tff(c_8352, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_8, c_233, c_8349])).
% 6.59/2.30  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.59/2.30  
% 6.59/2.30  Inference rules
% 6.59/2.30  ----------------------
% 6.59/2.30  #Ref     : 0
% 6.59/2.30  #Sup     : 1749
% 6.59/2.30  #Fact    : 0
% 6.59/2.30  #Define  : 0
% 6.59/2.30  #Split   : 1
% 6.59/2.30  #Chain   : 0
% 6.59/2.30  #Close   : 0
% 6.59/2.30  
% 6.59/2.30  Ordering : KBO
% 6.59/2.30  
% 6.59/2.30  Simplification rules
% 6.59/2.30  ----------------------
% 6.59/2.30  #Subsume      : 431
% 6.59/2.30  #Demod        : 2026
% 6.59/2.30  #Tautology    : 875
% 6.59/2.30  #SimpNegUnit  : 0
% 6.59/2.30  #BackRed      : 3
% 6.59/2.31  
% 6.59/2.31  #Partial instantiations: 0
% 6.59/2.31  #Strategies tried      : 1
% 6.59/2.31  
% 6.59/2.31  Timing (in seconds)
% 6.59/2.31  ----------------------
% 6.59/2.31  Preprocessing        : 0.33
% 6.59/2.31  Parsing              : 0.18
% 6.59/2.31  CNF conversion       : 0.02
% 6.59/2.31  Main loop            : 1.21
% 6.59/2.31  Inferencing          : 0.42
% 6.59/2.31  Reduction            : 0.42
% 6.59/2.31  Demodulation         : 0.31
% 6.59/2.31  BG Simplification    : 0.05
% 6.59/2.31  Subsumption          : 0.25
% 6.59/2.31  Abstraction          : 0.07
% 6.59/2.31  MUC search           : 0.00
% 6.59/2.31  Cooper               : 0.00
% 6.59/2.31  Total                : 1.57
% 6.59/2.31  Index Insertion      : 0.00
% 6.59/2.31  Index Deletion       : 0.00
% 6.59/2.31  Index Matching       : 0.00
% 6.59/2.31  BG Taut test         : 0.00
%------------------------------------------------------------------------------
