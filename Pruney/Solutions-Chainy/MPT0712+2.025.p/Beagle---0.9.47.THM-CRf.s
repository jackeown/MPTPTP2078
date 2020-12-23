%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:05:34 EST 2020

% Result     : Theorem 2.45s
% Output     : CNFRefutation 2.45s
% Verified   : 
% Statistics : Number of formulae       :   59 ( 124 expanded)
%              Number of leaves         :   30 (  58 expanded)
%              Depth                    :    8
%              Number of atoms          :   76 ( 229 expanded)
%              Number of equality atoms :   28 (  88 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > v1_relat_1 > v1_funct_1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k2_tarski > k1_funct_1 > k11_relat_1 > #nlpp > k2_relat_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1

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

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k11_relat_1,type,(
    k11_relat_1: ( $i * $i ) > $i )).

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

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_95,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_relat_1(B)
          & v1_funct_1(B) )
       => r1_tarski(k2_relat_1(k7_relat_1(B,k1_tarski(A))),k1_tarski(k1_funct_1(B,A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t167_funct_1)).

tff(f_27,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_29,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_61,axiom,(
    ! [A,B,C,D] :
      ( r1_tarski(D,k1_enumset1(A,B,C))
    <=> ~ ( D != k1_xboole_0
          & D != k1_tarski(A)
          & D != k1_tarski(B)
          & D != k1_tarski(C)
          & D != k2_tarski(A,B)
          & D != k2_tarski(B,C)
          & D != k2_tarski(A,C)
          & D != k1_enumset1(A,B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t142_zfmisc_1)).

tff(f_80,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_34,axiom,(
    ! [A,B] :
      ( ~ r2_hidden(A,B)
     => r1_xboole_0(k1_tarski(A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l27_zfmisc_1)).

tff(f_77,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( r1_xboole_0(B,k1_relat_1(A))
         => k7_relat_1(A,B) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t187_relat_1)).

tff(f_88,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r2_hidden(A,k1_relat_1(B))
       => k11_relat_1(B,A) = k1_tarski(k1_funct_1(B,A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t117_funct_1)).

tff(f_66,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] : k11_relat_1(A,B) = k9_relat_1(A,k1_tarski(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d16_relat_1)).

tff(f_70,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

tff(c_42,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_40,plain,(
    v1_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_2,plain,(
    ! [A_1] : k2_tarski(A_1,A_1) = k1_tarski(A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_65,plain,(
    ! [A_35,B_36] : k1_enumset1(A_35,A_35,B_36) = k2_tarski(A_35,B_36) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_24,plain,(
    ! [A_6,B_7,C_8] : r1_tarski(k1_xboole_0,k1_enumset1(A_6,B_7,C_8)) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_85,plain,(
    ! [A_37,B_38] : r1_tarski(k1_xboole_0,k2_tarski(A_37,B_38)) ),
    inference(superposition,[status(thm),theory(equality)],[c_65,c_24])).

tff(c_87,plain,(
    ! [A_1] : r1_tarski(k1_xboole_0,k1_tarski(A_1)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_85])).

tff(c_32,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_6,plain,(
    ! [A_4,B_5] :
      ( r1_xboole_0(k1_tarski(A_4),B_5)
      | r2_hidden(A_4,B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_172,plain,(
    ! [A_63,B_64] :
      ( k7_relat_1(A_63,B_64) = k1_xboole_0
      | ~ r1_xboole_0(B_64,k1_relat_1(A_63))
      | ~ v1_relat_1(A_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_186,plain,(
    ! [A_67,A_68] :
      ( k7_relat_1(A_67,k1_tarski(A_68)) = k1_xboole_0
      | ~ v1_relat_1(A_67)
      | r2_hidden(A_68,k1_relat_1(A_67)) ) ),
    inference(resolution,[status(thm)],[c_6,c_172])).

tff(c_36,plain,(
    ! [B_19,A_18] :
      ( k1_tarski(k1_funct_1(B_19,A_18)) = k11_relat_1(B_19,A_18)
      | ~ r2_hidden(A_18,k1_relat_1(B_19))
      | ~ v1_funct_1(B_19)
      | ~ v1_relat_1(B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_194,plain,(
    ! [A_69,A_70] :
      ( k1_tarski(k1_funct_1(A_69,A_70)) = k11_relat_1(A_69,A_70)
      | ~ v1_funct_1(A_69)
      | k7_relat_1(A_69,k1_tarski(A_70)) = k1_xboole_0
      | ~ v1_relat_1(A_69) ) ),
    inference(resolution,[status(thm)],[c_186,c_36])).

tff(c_38,plain,(
    ~ r1_tarski(k2_relat_1(k7_relat_1('#skF_2',k1_tarski('#skF_1'))),k1_tarski(k1_funct_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_203,plain,
    ( ~ r1_tarski(k2_relat_1(k1_xboole_0),k1_tarski(k1_funct_1('#skF_2','#skF_1')))
    | k1_tarski(k1_funct_1('#skF_2','#skF_1')) = k11_relat_1('#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_194,c_38])).

tff(c_210,plain,(
    k1_tarski(k1_funct_1('#skF_2','#skF_1')) = k11_relat_1('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_87,c_32,c_203])).

tff(c_26,plain,(
    ! [A_10,B_12] :
      ( k9_relat_1(A_10,k1_tarski(B_12)) = k11_relat_1(A_10,B_12)
      | ~ v1_relat_1(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_135,plain,(
    ! [B_56,A_57] :
      ( k2_relat_1(k7_relat_1(B_56,A_57)) = k9_relat_1(B_56,A_57)
      | ~ v1_relat_1(B_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_141,plain,
    ( ~ r1_tarski(k9_relat_1('#skF_2',k1_tarski('#skF_1')),k1_tarski(k1_funct_1('#skF_2','#skF_1')))
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_135,c_38])).

tff(c_147,plain,(
    ~ r1_tarski(k9_relat_1('#skF_2',k1_tarski('#skF_1')),k1_tarski(k1_funct_1('#skF_2','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_141])).

tff(c_169,plain,
    ( ~ r1_tarski(k11_relat_1('#skF_2','#skF_1'),k1_tarski(k1_funct_1('#skF_2','#skF_1')))
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_147])).

tff(c_171,plain,(
    ~ r1_tarski(k11_relat_1('#skF_2','#skF_1'),k1_tarski(k1_funct_1('#skF_2','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_169])).

tff(c_257,plain,(
    ~ r1_tarski(k11_relat_1('#skF_2','#skF_1'),k11_relat_1('#skF_2','#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_210,c_171])).

tff(c_18,plain,(
    ! [C_8,A_6,B_7] : r1_tarski(k1_tarski(C_8),k1_enumset1(A_6,B_7,C_8)) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_89,plain,(
    ! [B_40,A_41] : r1_tarski(k1_tarski(B_40),k2_tarski(A_41,B_40)) ),
    inference(superposition,[status(thm),theory(equality)],[c_65,c_18])).

tff(c_92,plain,(
    ! [A_1] : r1_tarski(k1_tarski(A_1),k1_tarski(A_1)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_89])).

tff(c_272,plain,(
    r1_tarski(k11_relat_1('#skF_2','#skF_1'),k1_tarski(k1_funct_1('#skF_2','#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_210,c_92])).

tff(c_295,plain,(
    r1_tarski(k11_relat_1('#skF_2','#skF_1'),k11_relat_1('#skF_2','#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_210,c_272])).

tff(c_308,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_257,c_295])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:09:23 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.45/1.35  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.45/1.35  
% 2.45/1.35  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.45/1.35  %$ r2_hidden > r1_xboole_0 > r1_tarski > v1_relat_1 > v1_funct_1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k2_tarski > k1_funct_1 > k11_relat_1 > #nlpp > k2_relat_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1
% 2.45/1.35  
% 2.45/1.35  %Foreground sorts:
% 2.45/1.35  
% 2.45/1.35  
% 2.45/1.35  %Background operators:
% 2.45/1.35  
% 2.45/1.35  
% 2.45/1.35  %Foreground operators:
% 2.45/1.35  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.45/1.35  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.45/1.35  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.45/1.35  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.45/1.35  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.45/1.35  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.45/1.35  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.45/1.35  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.45/1.35  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.45/1.35  tff(k11_relat_1, type, k11_relat_1: ($i * $i) > $i).
% 2.45/1.35  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.45/1.35  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.45/1.35  tff('#skF_2', type, '#skF_2': $i).
% 2.45/1.35  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.45/1.35  tff('#skF_1', type, '#skF_1': $i).
% 2.45/1.35  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.45/1.35  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.45/1.35  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.45/1.35  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.45/1.35  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.45/1.35  
% 2.45/1.37  tff(f_95, negated_conjecture, ~(![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => r1_tarski(k2_relat_1(k7_relat_1(B, k1_tarski(A))), k1_tarski(k1_funct_1(B, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t167_funct_1)).
% 2.45/1.37  tff(f_27, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 2.45/1.37  tff(f_29, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 2.45/1.37  tff(f_61, axiom, (![A, B, C, D]: (r1_tarski(D, k1_enumset1(A, B, C)) <=> ~(((((((~(D = k1_xboole_0) & ~(D = k1_tarski(A))) & ~(D = k1_tarski(B))) & ~(D = k1_tarski(C))) & ~(D = k2_tarski(A, B))) & ~(D = k2_tarski(B, C))) & ~(D = k2_tarski(A, C))) & ~(D = k1_enumset1(A, B, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t142_zfmisc_1)).
% 2.45/1.37  tff(f_80, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 2.45/1.37  tff(f_34, axiom, (![A, B]: (~r2_hidden(A, B) => r1_xboole_0(k1_tarski(A), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 2.45/1.37  tff(f_77, axiom, (![A]: (v1_relat_1(A) => (![B]: (r1_xboole_0(B, k1_relat_1(A)) => (k7_relat_1(A, B) = k1_xboole_0))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t187_relat_1)).
% 2.45/1.37  tff(f_88, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r2_hidden(A, k1_relat_1(B)) => (k11_relat_1(B, A) = k1_tarski(k1_funct_1(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t117_funct_1)).
% 2.45/1.37  tff(f_66, axiom, (![A]: (v1_relat_1(A) => (![B]: (k11_relat_1(A, B) = k9_relat_1(A, k1_tarski(B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d16_relat_1)).
% 2.45/1.37  tff(f_70, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_relat_1)).
% 2.45/1.37  tff(c_42, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_95])).
% 2.45/1.37  tff(c_40, plain, (v1_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_95])).
% 2.45/1.37  tff(c_2, plain, (![A_1]: (k2_tarski(A_1, A_1)=k1_tarski(A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.45/1.37  tff(c_65, plain, (![A_35, B_36]: (k1_enumset1(A_35, A_35, B_36)=k2_tarski(A_35, B_36))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.45/1.37  tff(c_24, plain, (![A_6, B_7, C_8]: (r1_tarski(k1_xboole_0, k1_enumset1(A_6, B_7, C_8)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.45/1.37  tff(c_85, plain, (![A_37, B_38]: (r1_tarski(k1_xboole_0, k2_tarski(A_37, B_38)))), inference(superposition, [status(thm), theory('equality')], [c_65, c_24])).
% 2.45/1.37  tff(c_87, plain, (![A_1]: (r1_tarski(k1_xboole_0, k1_tarski(A_1)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_85])).
% 2.45/1.37  tff(c_32, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.45/1.37  tff(c_6, plain, (![A_4, B_5]: (r1_xboole_0(k1_tarski(A_4), B_5) | r2_hidden(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.45/1.37  tff(c_172, plain, (![A_63, B_64]: (k7_relat_1(A_63, B_64)=k1_xboole_0 | ~r1_xboole_0(B_64, k1_relat_1(A_63)) | ~v1_relat_1(A_63))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.45/1.37  tff(c_186, plain, (![A_67, A_68]: (k7_relat_1(A_67, k1_tarski(A_68))=k1_xboole_0 | ~v1_relat_1(A_67) | r2_hidden(A_68, k1_relat_1(A_67)))), inference(resolution, [status(thm)], [c_6, c_172])).
% 2.45/1.37  tff(c_36, plain, (![B_19, A_18]: (k1_tarski(k1_funct_1(B_19, A_18))=k11_relat_1(B_19, A_18) | ~r2_hidden(A_18, k1_relat_1(B_19)) | ~v1_funct_1(B_19) | ~v1_relat_1(B_19))), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.45/1.37  tff(c_194, plain, (![A_69, A_70]: (k1_tarski(k1_funct_1(A_69, A_70))=k11_relat_1(A_69, A_70) | ~v1_funct_1(A_69) | k7_relat_1(A_69, k1_tarski(A_70))=k1_xboole_0 | ~v1_relat_1(A_69))), inference(resolution, [status(thm)], [c_186, c_36])).
% 2.45/1.37  tff(c_38, plain, (~r1_tarski(k2_relat_1(k7_relat_1('#skF_2', k1_tarski('#skF_1'))), k1_tarski(k1_funct_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_95])).
% 2.45/1.37  tff(c_203, plain, (~r1_tarski(k2_relat_1(k1_xboole_0), k1_tarski(k1_funct_1('#skF_2', '#skF_1'))) | k1_tarski(k1_funct_1('#skF_2', '#skF_1'))=k11_relat_1('#skF_2', '#skF_1') | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_194, c_38])).
% 2.45/1.37  tff(c_210, plain, (k1_tarski(k1_funct_1('#skF_2', '#skF_1'))=k11_relat_1('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_87, c_32, c_203])).
% 2.45/1.37  tff(c_26, plain, (![A_10, B_12]: (k9_relat_1(A_10, k1_tarski(B_12))=k11_relat_1(A_10, B_12) | ~v1_relat_1(A_10))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.45/1.37  tff(c_135, plain, (![B_56, A_57]: (k2_relat_1(k7_relat_1(B_56, A_57))=k9_relat_1(B_56, A_57) | ~v1_relat_1(B_56))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.45/1.37  tff(c_141, plain, (~r1_tarski(k9_relat_1('#skF_2', k1_tarski('#skF_1')), k1_tarski(k1_funct_1('#skF_2', '#skF_1'))) | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_135, c_38])).
% 2.45/1.37  tff(c_147, plain, (~r1_tarski(k9_relat_1('#skF_2', k1_tarski('#skF_1')), k1_tarski(k1_funct_1('#skF_2', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_141])).
% 2.45/1.37  tff(c_169, plain, (~r1_tarski(k11_relat_1('#skF_2', '#skF_1'), k1_tarski(k1_funct_1('#skF_2', '#skF_1'))) | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_26, c_147])).
% 2.45/1.37  tff(c_171, plain, (~r1_tarski(k11_relat_1('#skF_2', '#skF_1'), k1_tarski(k1_funct_1('#skF_2', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_169])).
% 2.45/1.37  tff(c_257, plain, (~r1_tarski(k11_relat_1('#skF_2', '#skF_1'), k11_relat_1('#skF_2', '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_210, c_171])).
% 2.45/1.37  tff(c_18, plain, (![C_8, A_6, B_7]: (r1_tarski(k1_tarski(C_8), k1_enumset1(A_6, B_7, C_8)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.45/1.37  tff(c_89, plain, (![B_40, A_41]: (r1_tarski(k1_tarski(B_40), k2_tarski(A_41, B_40)))), inference(superposition, [status(thm), theory('equality')], [c_65, c_18])).
% 2.45/1.37  tff(c_92, plain, (![A_1]: (r1_tarski(k1_tarski(A_1), k1_tarski(A_1)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_89])).
% 2.45/1.37  tff(c_272, plain, (r1_tarski(k11_relat_1('#skF_2', '#skF_1'), k1_tarski(k1_funct_1('#skF_2', '#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_210, c_92])).
% 2.45/1.37  tff(c_295, plain, (r1_tarski(k11_relat_1('#skF_2', '#skF_1'), k11_relat_1('#skF_2', '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_210, c_272])).
% 2.45/1.37  tff(c_308, plain, $false, inference(negUnitSimplification, [status(thm)], [c_257, c_295])).
% 2.45/1.37  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.45/1.37  
% 2.45/1.37  Inference rules
% 2.45/1.37  ----------------------
% 2.45/1.37  #Ref     : 0
% 2.45/1.37  #Sup     : 64
% 2.45/1.37  #Fact    : 0
% 2.45/1.37  #Define  : 0
% 2.45/1.37  #Split   : 1
% 2.45/1.37  #Chain   : 0
% 2.45/1.37  #Close   : 0
% 2.45/1.37  
% 2.45/1.37  Ordering : KBO
% 2.45/1.37  
% 2.45/1.37  Simplification rules
% 2.45/1.37  ----------------------
% 2.45/1.37  #Subsume      : 2
% 2.45/1.37  #Demod        : 36
% 2.45/1.37  #Tautology    : 36
% 2.45/1.37  #SimpNegUnit  : 1
% 2.45/1.37  #BackRed      : 3
% 2.45/1.37  
% 2.45/1.37  #Partial instantiations: 0
% 2.45/1.37  #Strategies tried      : 1
% 2.45/1.37  
% 2.45/1.37  Timing (in seconds)
% 2.45/1.37  ----------------------
% 2.45/1.37  Preprocessing        : 0.32
% 2.45/1.37  Parsing              : 0.17
% 2.45/1.37  CNF conversion       : 0.02
% 2.45/1.37  Main loop            : 0.23
% 2.45/1.37  Inferencing          : 0.08
% 2.45/1.37  Reduction            : 0.08
% 2.45/1.37  Demodulation         : 0.06
% 2.45/1.37  BG Simplification    : 0.02
% 2.45/1.37  Subsumption          : 0.04
% 2.45/1.37  Abstraction          : 0.02
% 2.75/1.37  MUC search           : 0.00
% 2.75/1.37  Cooper               : 0.00
% 2.75/1.37  Total                : 0.58
% 2.75/1.37  Index Insertion      : 0.00
% 2.75/1.37  Index Deletion       : 0.00
% 2.75/1.37  Index Matching       : 0.00
% 2.75/1.37  BG Taut test         : 0.00
%------------------------------------------------------------------------------
