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
% DateTime   : Thu Dec  3 10:00:21 EST 2020

% Result     : Theorem 2.53s
% Output     : CNFRefutation 2.53s
% Verified   : 
% Statistics : Number of formulae       :   68 (  74 expanded)
%              Number of leaves         :   38 (  41 expanded)
%              Depth                    :   13
%              Number of atoms          :   82 (  89 expanded)
%              Number of equality atoms :   38 (  44 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_xboole_0 > v1_relat_1 > k5_enumset1 > k4_enumset1 > k2_enumset1 > k8_relat_1 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k2_relat_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_4 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k8_relat_1,type,(
    k8_relat_1: ( $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i ) > $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_100,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => k8_relat_1(k1_xboole_0,A) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t137_relat_1)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_87,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k2_relat_1(k8_relat_1(A,B)),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t116_relat_1)).

tff(f_34,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_63,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_57,axiom,(
    ! [A,B,C,D] :
      ~ ( r1_tarski(A,k2_zfmisc_1(B,C))
        & r2_hidden(D,A)
        & ! [E,F] :
            ~ ( r2_hidden(E,B)
              & r2_hidden(F,C)
              & D = k4_tarski(E,F) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t103_zfmisc_1)).

tff(f_65,axiom,(
    ! [A,B] : k3_xboole_0(k1_tarski(A),k2_tarski(A,B)) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_zfmisc_1)).

tff(f_67,axiom,(
    ! [A,B] : k4_xboole_0(k1_tarski(A),k2_tarski(A,B)) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_zfmisc_1)).

tff(f_36,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_40,axiom,(
    ! [A,B] : k2_enumset1(A,A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_enumset1)).

tff(f_44,axiom,(
    ! [A] : k2_enumset1(A,A,A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t82_enumset1)).

tff(f_75,axiom,(
    ! [A,B,C] :
      ( k4_xboole_0(k2_tarski(A,B),C) = k2_tarski(A,B)
    <=> ( ~ r2_hidden(A,C)
        & ~ r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_zfmisc_1)).

tff(f_83,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(A)
        & v1_xboole_0(B) )
     => ( v1_xboole_0(k8_relat_1(B,A))
        & v1_relat_1(k8_relat_1(B,A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc18_relat_1)).

tff(f_95,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ( k1_relat_1(A) = k1_xboole_0
          | k2_relat_1(A) = k1_xboole_0 )
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).

tff(c_48,plain,(
    k8_relat_1(k1_xboole_0,'#skF_4') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_50,plain,(
    v1_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_42,plain,(
    ! [A_35,B_36] :
      ( r1_tarski(k2_relat_1(k8_relat_1(A_35,B_36)),A_35)
      | ~ v1_relat_1(B_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_4,plain,(
    ! [A_1] :
      ( r2_hidden('#skF_1'(A_1),A_1)
      | k1_xboole_0 = A_1 ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_26,plain,(
    ! [B_25] : k2_zfmisc_1(k1_xboole_0,B_25) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_597,plain,(
    ! [A_106,B_107,C_108,D_109] :
      ( r2_hidden('#skF_2'(A_106,B_107,C_108,D_109),B_107)
      | ~ r2_hidden(D_109,A_106)
      | ~ r1_tarski(A_106,k2_zfmisc_1(B_107,C_108)) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_28,plain,(
    ! [A_26,B_27] : k3_xboole_0(k1_tarski(A_26),k2_tarski(A_26,B_27)) = k1_tarski(A_26) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_30,plain,(
    ! [A_28,B_29] : k4_xboole_0(k1_tarski(A_28),k2_tarski(A_28,B_29)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_123,plain,(
    ! [A_52,B_53] : k4_xboole_0(A_52,k4_xboole_0(A_52,B_53)) = k3_xboole_0(A_52,B_53) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_138,plain,(
    ! [A_28,B_29] : k3_xboole_0(k1_tarski(A_28),k2_tarski(A_28,B_29)) = k4_xboole_0(k1_tarski(A_28),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_123])).

tff(c_141,plain,(
    ! [A_28] : k4_xboole_0(k1_tarski(A_28),k1_xboole_0) = k1_tarski(A_28) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_138])).

tff(c_155,plain,(
    ! [A_57,B_58] : k2_enumset1(A_57,A_57,A_57,B_58) = k2_tarski(A_57,B_58) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_14,plain,(
    ! [A_17] : k2_enumset1(A_17,A_17,A_17,A_17) = k1_tarski(A_17) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_162,plain,(
    ! [B_58] : k2_tarski(B_58,B_58) = k1_tarski(B_58) ),
    inference(superposition,[status(thm),theory(equality)],[c_155,c_14])).

tff(c_249,plain,(
    ! [A_67,C_68,B_69] :
      ( ~ r2_hidden(A_67,C_68)
      | k4_xboole_0(k2_tarski(A_67,B_69),C_68) != k2_tarski(A_67,B_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_256,plain,(
    ! [B_58,C_68] :
      ( ~ r2_hidden(B_58,C_68)
      | k4_xboole_0(k1_tarski(B_58),C_68) != k2_tarski(B_58,B_58) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_162,c_249])).

tff(c_262,plain,(
    ! [B_70,C_71] :
      ( ~ r2_hidden(B_70,C_71)
      | k4_xboole_0(k1_tarski(B_70),C_71) != k1_tarski(B_70) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_162,c_256])).

tff(c_280,plain,(
    ! [A_28] : ~ r2_hidden(A_28,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_141,c_262])).

tff(c_601,plain,(
    ! [D_109,A_106,C_108] :
      ( ~ r2_hidden(D_109,A_106)
      | ~ r1_tarski(A_106,k2_zfmisc_1(k1_xboole_0,C_108)) ) ),
    inference(resolution,[status(thm)],[c_597,c_280])).

tff(c_604,plain,(
    ! [D_110,A_111] :
      ( ~ r2_hidden(D_110,A_111)
      | ~ r1_tarski(A_111,k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_601])).

tff(c_617,plain,(
    ! [A_112] :
      ( ~ r1_tarski(A_112,k1_xboole_0)
      | k1_xboole_0 = A_112 ) ),
    inference(resolution,[status(thm)],[c_4,c_604])).

tff(c_623,plain,(
    ! [B_113] :
      ( k2_relat_1(k8_relat_1(k1_xboole_0,B_113)) = k1_xboole_0
      | ~ v1_relat_1(B_113) ) ),
    inference(resolution,[status(thm)],[c_42,c_617])).

tff(c_207,plain,(
    ! [B_62,A_63] :
      ( v1_relat_1(k8_relat_1(B_62,A_63))
      | ~ v1_xboole_0(B_62)
      | ~ v1_relat_1(A_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_44,plain,(
    ! [A_37] :
      ( k2_relat_1(A_37) != k1_xboole_0
      | k1_xboole_0 = A_37
      | ~ v1_relat_1(A_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_214,plain,(
    ! [B_62,A_63] :
      ( k2_relat_1(k8_relat_1(B_62,A_63)) != k1_xboole_0
      | k8_relat_1(B_62,A_63) = k1_xboole_0
      | ~ v1_xboole_0(B_62)
      | ~ v1_relat_1(A_63) ) ),
    inference(resolution,[status(thm)],[c_207,c_44])).

tff(c_629,plain,(
    ! [B_113] :
      ( k8_relat_1(k1_xboole_0,B_113) = k1_xboole_0
      | ~ v1_xboole_0(k1_xboole_0)
      | ~ v1_relat_1(B_113) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_623,c_214])).

tff(c_641,plain,(
    ! [B_114] :
      ( k8_relat_1(k1_xboole_0,B_114) = k1_xboole_0
      | ~ v1_relat_1(B_114) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_629])).

tff(c_647,plain,(
    k8_relat_1(k1_xboole_0,'#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_50,c_641])).

tff(c_652,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_647])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:14:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.53/1.29  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.53/1.29  
% 2.53/1.29  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.53/1.30  %$ r2_hidden > r1_tarski > v1_xboole_0 > v1_relat_1 > k5_enumset1 > k4_enumset1 > k2_enumset1 > k8_relat_1 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k2_relat_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_4 > #skF_3
% 2.53/1.30  
% 2.53/1.30  %Foreground sorts:
% 2.53/1.30  
% 2.53/1.30  
% 2.53/1.30  %Background operators:
% 2.53/1.30  
% 2.53/1.30  
% 2.53/1.30  %Foreground operators:
% 2.53/1.30  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 2.53/1.30  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.53/1.30  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.53/1.30  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.53/1.30  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.53/1.30  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.53/1.30  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.53/1.30  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.53/1.30  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.53/1.30  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.53/1.30  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.53/1.30  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.53/1.30  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 2.53/1.30  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.53/1.30  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.53/1.30  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.53/1.30  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.53/1.30  tff('#skF_4', type, '#skF_4': $i).
% 2.53/1.30  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.53/1.30  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.53/1.30  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 2.53/1.30  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.53/1.30  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.53/1.30  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.53/1.30  
% 2.53/1.31  tff(f_100, negated_conjecture, ~(![A]: (v1_relat_1(A) => (k8_relat_1(k1_xboole_0, A) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t137_relat_1)).
% 2.53/1.31  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.53/1.31  tff(f_87, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k2_relat_1(k8_relat_1(A, B)), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t116_relat_1)).
% 2.53/1.31  tff(f_34, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 2.53/1.31  tff(f_63, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 2.53/1.31  tff(f_57, axiom, (![A, B, C, D]: ~((r1_tarski(A, k2_zfmisc_1(B, C)) & r2_hidden(D, A)) & (![E, F]: ~((r2_hidden(E, B) & r2_hidden(F, C)) & (D = k4_tarski(E, F)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t103_zfmisc_1)).
% 2.53/1.31  tff(f_65, axiom, (![A, B]: (k3_xboole_0(k1_tarski(A), k2_tarski(A, B)) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t19_zfmisc_1)).
% 2.53/1.31  tff(f_67, axiom, (![A, B]: (k4_xboole_0(k1_tarski(A), k2_tarski(A, B)) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t22_zfmisc_1)).
% 2.53/1.31  tff(f_36, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 2.53/1.31  tff(f_40, axiom, (![A, B]: (k2_enumset1(A, A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t77_enumset1)).
% 2.53/1.31  tff(f_44, axiom, (![A]: (k2_enumset1(A, A, A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t82_enumset1)).
% 2.53/1.31  tff(f_75, axiom, (![A, B, C]: ((k4_xboole_0(k2_tarski(A, B), C) = k2_tarski(A, B)) <=> (~r2_hidden(A, C) & ~r2_hidden(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_zfmisc_1)).
% 2.53/1.31  tff(f_83, axiom, (![A, B]: ((v1_relat_1(A) & v1_xboole_0(B)) => (v1_xboole_0(k8_relat_1(B, A)) & v1_relat_1(k8_relat_1(B, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc18_relat_1)).
% 2.53/1.31  tff(f_95, axiom, (![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_relat_1)).
% 2.53/1.31  tff(c_48, plain, (k8_relat_1(k1_xboole_0, '#skF_4')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_100])).
% 2.53/1.31  tff(c_50, plain, (v1_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_100])).
% 2.53/1.31  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 2.53/1.31  tff(c_42, plain, (![A_35, B_36]: (r1_tarski(k2_relat_1(k8_relat_1(A_35, B_36)), A_35) | ~v1_relat_1(B_36))), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.53/1.31  tff(c_4, plain, (![A_1]: (r2_hidden('#skF_1'(A_1), A_1) | k1_xboole_0=A_1)), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.53/1.31  tff(c_26, plain, (![B_25]: (k2_zfmisc_1(k1_xboole_0, B_25)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.53/1.31  tff(c_597, plain, (![A_106, B_107, C_108, D_109]: (r2_hidden('#skF_2'(A_106, B_107, C_108, D_109), B_107) | ~r2_hidden(D_109, A_106) | ~r1_tarski(A_106, k2_zfmisc_1(B_107, C_108)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.53/1.31  tff(c_28, plain, (![A_26, B_27]: (k3_xboole_0(k1_tarski(A_26), k2_tarski(A_26, B_27))=k1_tarski(A_26))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.53/1.31  tff(c_30, plain, (![A_28, B_29]: (k4_xboole_0(k1_tarski(A_28), k2_tarski(A_28, B_29))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.53/1.31  tff(c_123, plain, (![A_52, B_53]: (k4_xboole_0(A_52, k4_xboole_0(A_52, B_53))=k3_xboole_0(A_52, B_53))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.53/1.31  tff(c_138, plain, (![A_28, B_29]: (k3_xboole_0(k1_tarski(A_28), k2_tarski(A_28, B_29))=k4_xboole_0(k1_tarski(A_28), k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_30, c_123])).
% 2.53/1.31  tff(c_141, plain, (![A_28]: (k4_xboole_0(k1_tarski(A_28), k1_xboole_0)=k1_tarski(A_28))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_138])).
% 2.53/1.31  tff(c_155, plain, (![A_57, B_58]: (k2_enumset1(A_57, A_57, A_57, B_58)=k2_tarski(A_57, B_58))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.53/1.31  tff(c_14, plain, (![A_17]: (k2_enumset1(A_17, A_17, A_17, A_17)=k1_tarski(A_17))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.53/1.31  tff(c_162, plain, (![B_58]: (k2_tarski(B_58, B_58)=k1_tarski(B_58))), inference(superposition, [status(thm), theory('equality')], [c_155, c_14])).
% 2.53/1.31  tff(c_249, plain, (![A_67, C_68, B_69]: (~r2_hidden(A_67, C_68) | k4_xboole_0(k2_tarski(A_67, B_69), C_68)!=k2_tarski(A_67, B_69))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.53/1.31  tff(c_256, plain, (![B_58, C_68]: (~r2_hidden(B_58, C_68) | k4_xboole_0(k1_tarski(B_58), C_68)!=k2_tarski(B_58, B_58))), inference(superposition, [status(thm), theory('equality')], [c_162, c_249])).
% 2.53/1.31  tff(c_262, plain, (![B_70, C_71]: (~r2_hidden(B_70, C_71) | k4_xboole_0(k1_tarski(B_70), C_71)!=k1_tarski(B_70))), inference(demodulation, [status(thm), theory('equality')], [c_162, c_256])).
% 2.53/1.31  tff(c_280, plain, (![A_28]: (~r2_hidden(A_28, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_141, c_262])).
% 2.53/1.31  tff(c_601, plain, (![D_109, A_106, C_108]: (~r2_hidden(D_109, A_106) | ~r1_tarski(A_106, k2_zfmisc_1(k1_xboole_0, C_108)))), inference(resolution, [status(thm)], [c_597, c_280])).
% 2.53/1.31  tff(c_604, plain, (![D_110, A_111]: (~r2_hidden(D_110, A_111) | ~r1_tarski(A_111, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_601])).
% 2.53/1.31  tff(c_617, plain, (![A_112]: (~r1_tarski(A_112, k1_xboole_0) | k1_xboole_0=A_112)), inference(resolution, [status(thm)], [c_4, c_604])).
% 2.53/1.31  tff(c_623, plain, (![B_113]: (k2_relat_1(k8_relat_1(k1_xboole_0, B_113))=k1_xboole_0 | ~v1_relat_1(B_113))), inference(resolution, [status(thm)], [c_42, c_617])).
% 2.53/1.31  tff(c_207, plain, (![B_62, A_63]: (v1_relat_1(k8_relat_1(B_62, A_63)) | ~v1_xboole_0(B_62) | ~v1_relat_1(A_63))), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.53/1.31  tff(c_44, plain, (![A_37]: (k2_relat_1(A_37)!=k1_xboole_0 | k1_xboole_0=A_37 | ~v1_relat_1(A_37))), inference(cnfTransformation, [status(thm)], [f_95])).
% 2.53/1.31  tff(c_214, plain, (![B_62, A_63]: (k2_relat_1(k8_relat_1(B_62, A_63))!=k1_xboole_0 | k8_relat_1(B_62, A_63)=k1_xboole_0 | ~v1_xboole_0(B_62) | ~v1_relat_1(A_63))), inference(resolution, [status(thm)], [c_207, c_44])).
% 2.53/1.31  tff(c_629, plain, (![B_113]: (k8_relat_1(k1_xboole_0, B_113)=k1_xboole_0 | ~v1_xboole_0(k1_xboole_0) | ~v1_relat_1(B_113))), inference(superposition, [status(thm), theory('equality')], [c_623, c_214])).
% 2.53/1.31  tff(c_641, plain, (![B_114]: (k8_relat_1(k1_xboole_0, B_114)=k1_xboole_0 | ~v1_relat_1(B_114))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_629])).
% 2.53/1.31  tff(c_647, plain, (k8_relat_1(k1_xboole_0, '#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_50, c_641])).
% 2.53/1.31  tff(c_652, plain, $false, inference(negUnitSimplification, [status(thm)], [c_48, c_647])).
% 2.53/1.31  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.53/1.31  
% 2.53/1.31  Inference rules
% 2.53/1.31  ----------------------
% 2.53/1.31  #Ref     : 0
% 2.53/1.31  #Sup     : 138
% 2.53/1.31  #Fact    : 2
% 2.53/1.31  #Define  : 0
% 2.53/1.31  #Split   : 2
% 2.53/1.31  #Chain   : 0
% 2.53/1.31  #Close   : 0
% 2.53/1.31  
% 2.53/1.31  Ordering : KBO
% 2.53/1.31  
% 2.53/1.31  Simplification rules
% 2.53/1.31  ----------------------
% 2.53/1.31  #Subsume      : 11
% 2.53/1.31  #Demod        : 43
% 2.53/1.31  #Tautology    : 64
% 2.53/1.31  #SimpNegUnit  : 5
% 2.53/1.31  #BackRed      : 0
% 2.53/1.31  
% 2.53/1.31  #Partial instantiations: 0
% 2.53/1.31  #Strategies tried      : 1
% 2.53/1.31  
% 2.53/1.31  Timing (in seconds)
% 2.53/1.31  ----------------------
% 2.84/1.31  Preprocessing        : 0.33
% 2.84/1.31  Parsing              : 0.18
% 2.84/1.31  CNF conversion       : 0.02
% 2.84/1.31  Main loop            : 0.29
% 2.84/1.31  Inferencing          : 0.11
% 2.84/1.31  Reduction            : 0.09
% 2.84/1.31  Demodulation         : 0.07
% 2.84/1.31  BG Simplification    : 0.02
% 2.84/1.31  Subsumption          : 0.04
% 2.84/1.31  Abstraction          : 0.02
% 2.84/1.31  MUC search           : 0.00
% 2.84/1.31  Cooper               : 0.00
% 2.84/1.31  Total                : 0.65
% 2.84/1.31  Index Insertion      : 0.00
% 2.84/1.31  Index Deletion       : 0.00
% 2.84/1.31  Index Matching       : 0.00
% 2.84/1.31  BG Taut test         : 0.00
%------------------------------------------------------------------------------
