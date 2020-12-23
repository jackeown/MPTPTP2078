%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:03:00 EST 2020

% Result     : Theorem 3.93s
% Output     : CNFRefutation 3.93s
% Verified   : 
% Statistics : Number of formulae       :   62 ( 101 expanded)
%              Number of leaves         :   31 (  52 expanded)
%              Depth                    :   13
%              Number of atoms          :  113 ( 267 expanded)
%              Number of equality atoms :   56 ( 125 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_enumset1 > k4_tarski > k2_tarski > k1_funct_1 > #nlpp > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_7 > #skF_6 > #skF_4 > #skF_11 > #skF_1 > #skF_8 > #skF_3 > #skF_10 > #skF_2 > #skF_9 > #skF_5

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_7',type,(
    '#skF_7': $i > $i )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_11',type,(
    '#skF_11': $i )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_8',type,(
    '#skF_8': $i > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_10',type,(
    '#skF_10': $i > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_9',type,(
    '#skF_9': ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_53,axiom,(
    ! [A] :
      ( v1_relat_1(A)
    <=> ! [B] :
          ~ ( r2_hidden(B,A)
            & ! [C,D] : B != k4_tarski(C,D) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_relat_1)).

tff(f_104,negated_conjecture,(
    ~ ! [A] :
        ( ! [B] :
            ( ( v1_relat_1(B)
              & v1_funct_1(B) )
           => ! [C] :
                ( ( v1_relat_1(C)
                  & v1_funct_1(C) )
               => ( ( k1_relat_1(B) = A
                    & k1_relat_1(C) = A )
                 => B = C ) ) )
       => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_funct_1)).

tff(f_73,axiom,(
    ! [A,B] :
    ? [C] :
      ( v1_relat_1(C)
      & v1_funct_1(C)
      & k1_relat_1(C) = A
      & ! [D] :
          ( r2_hidden(D,A)
         => k1_funct_1(C,D) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',s3_funct_1__e2_24__funct_1)).

tff(f_85,axiom,(
    ! [A] :
    ? [B] :
      ( v1_relat_1(B)
      & v1_funct_1(B)
      & k1_relat_1(B) = A
      & ! [C] :
          ( r2_hidden(C,A)
         => k1_funct_1(B,C) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',s3_funct_1__e2_25__funct_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_61,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ! [B,C] : ~ r2_hidden(k4_tarski(B,C),A)
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_relat_1)).

tff(c_28,plain,(
    ! [A_13] :
      ( r2_hidden('#skF_4'(A_13),A_13)
      | v1_relat_1(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_48,plain,(
    k1_xboole_0 != '#skF_11' ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_36,plain,(
    ! [A_34,B_35] : v1_funct_1('#skF_9'(A_34,B_35)) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_34,plain,(
    ! [A_34,B_35] : k1_relat_1('#skF_9'(A_34,B_35)) = A_34 ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_38,plain,(
    ! [A_34,B_35] : v1_relat_1('#skF_9'(A_34,B_35)) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_44,plain,(
    ! [A_41] : v1_funct_1('#skF_10'(A_41)) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_42,plain,(
    ! [A_41] : k1_relat_1('#skF_10'(A_41)) = A_41 ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_46,plain,(
    ! [A_41] : v1_relat_1('#skF_10'(A_41)) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_74,plain,(
    ! [C_62,B_63] :
      ( C_62 = B_63
      | k1_relat_1(C_62) != '#skF_11'
      | k1_relat_1(B_63) != '#skF_11'
      | ~ v1_funct_1(C_62)
      | ~ v1_relat_1(C_62)
      | ~ v1_funct_1(B_63)
      | ~ v1_relat_1(B_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_78,plain,(
    ! [B_63,A_41] :
      ( B_63 = '#skF_10'(A_41)
      | k1_relat_1('#skF_10'(A_41)) != '#skF_11'
      | k1_relat_1(B_63) != '#skF_11'
      | ~ v1_funct_1('#skF_10'(A_41))
      | ~ v1_funct_1(B_63)
      | ~ v1_relat_1(B_63) ) ),
    inference(resolution,[status(thm)],[c_46,c_74])).

tff(c_291,plain,(
    ! [B_101,A_102] :
      ( B_101 = '#skF_10'(A_102)
      | A_102 != '#skF_11'
      | k1_relat_1(B_101) != '#skF_11'
      | ~ v1_funct_1(B_101)
      | ~ v1_relat_1(B_101) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_78])).

tff(c_297,plain,(
    ! [A_34,B_35,A_102] :
      ( '#skF_9'(A_34,B_35) = '#skF_10'(A_102)
      | A_102 != '#skF_11'
      | k1_relat_1('#skF_9'(A_34,B_35)) != '#skF_11'
      | ~ v1_funct_1('#skF_9'(A_34,B_35)) ) ),
    inference(resolution,[status(thm)],[c_38,c_291])).

tff(c_366,plain,(
    ! [A_107,B_108,A_109] :
      ( '#skF_9'(A_107,B_108) = '#skF_10'(A_109)
      | A_109 != '#skF_11'
      | A_107 != '#skF_11' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_297])).

tff(c_32,plain,(
    ! [A_34,B_35,D_40] :
      ( k1_funct_1('#skF_9'(A_34,B_35),D_40) = B_35
      | ~ r2_hidden(D_40,A_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_606,plain,(
    ! [A_131,D_132,B_133,A_134] :
      ( k1_funct_1('#skF_10'(A_131),D_132) = B_133
      | ~ r2_hidden(D_132,A_134)
      | A_131 != '#skF_11'
      | A_134 != '#skF_11' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_366,c_32])).

tff(c_1406,plain,(
    ! [A_1488,A_1489] :
      ( k1_funct_1('#skF_10'(A_1488),'#skF_4'(A_1489)) = '#skF_11'
      | A_1488 != '#skF_11'
      | A_1489 != '#skF_11'
      | v1_relat_1(A_1489) ) ),
    inference(resolution,[status(thm)],[c_28,c_606])).

tff(c_40,plain,(
    ! [A_41,C_46] :
      ( k1_funct_1('#skF_10'(A_41),C_46) = k1_xboole_0
      | ~ r2_hidden(C_46,A_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_1409,plain,(
    ! [A_1489,A_1488] :
      ( k1_xboole_0 = '#skF_11'
      | ~ r2_hidden('#skF_4'(A_1489),A_1488)
      | A_1488 != '#skF_11'
      | A_1489 != '#skF_11'
      | v1_relat_1(A_1489) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1406,c_40])).

tff(c_1596,plain,(
    ! [A_2869,A_2870] :
      ( ~ r2_hidden('#skF_4'(A_2869),A_2870)
      | A_2870 != '#skF_11'
      | A_2869 != '#skF_11'
      | v1_relat_1(A_2869) ) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_1409])).

tff(c_1609,plain,(
    ! [A_13] :
      ( A_13 != '#skF_11'
      | v1_relat_1(A_13) ) ),
    inference(resolution,[status(thm)],[c_28,c_1596])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_1946,plain,(
    ! [A_2928,A_2929] :
      ( k1_funct_1('#skF_10'(A_2928),'#skF_1'(A_2929)) = '#skF_11'
      | A_2928 != '#skF_11'
      | A_2929 != '#skF_11'
      | v1_xboole_0(A_2929) ) ),
    inference(resolution,[status(thm)],[c_4,c_606])).

tff(c_1949,plain,(
    ! [A_2929,A_2928] :
      ( k1_xboole_0 = '#skF_11'
      | ~ r2_hidden('#skF_1'(A_2929),A_2928)
      | A_2928 != '#skF_11'
      | A_2929 != '#skF_11'
      | v1_xboole_0(A_2929) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1946,c_40])).

tff(c_2127,plain,(
    ! [A_4361,A_4362] :
      ( ~ r2_hidden('#skF_1'(A_4361),A_4362)
      | A_4362 != '#skF_11'
      | A_4361 != '#skF_11'
      | v1_xboole_0(A_4361) ) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_1949])).

tff(c_2144,plain,(
    ! [A_4389] :
      ( A_4389 != '#skF_11'
      | v1_xboole_0(A_4389) ) ),
    inference(resolution,[status(thm)],[c_4,c_2127])).

tff(c_184,plain,(
    ! [A_88] :
      ( k1_xboole_0 = A_88
      | r2_hidden(k4_tarski('#skF_7'(A_88),'#skF_8'(A_88)),A_88)
      | ~ v1_relat_1(A_88) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_193,plain,(
    ! [A_88] :
      ( ~ v1_xboole_0(A_88)
      | k1_xboole_0 = A_88
      | ~ v1_relat_1(A_88) ) ),
    inference(resolution,[status(thm)],[c_184,c_2])).

tff(c_2161,plain,(
    ! [A_4390] :
      ( k1_xboole_0 = A_4390
      | ~ v1_relat_1(A_4390)
      | A_4390 != '#skF_11' ) ),
    inference(resolution,[status(thm)],[c_2144,c_193])).

tff(c_2182,plain,(
    k1_xboole_0 = '#skF_11' ),
    inference(resolution,[status(thm)],[c_1609,c_2161])).

tff(c_2201,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2182,c_48])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n008.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 10:31:00 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.93/1.66  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.93/1.66  
% 3.93/1.66  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.93/1.66  %$ r2_hidden > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_enumset1 > k4_tarski > k2_tarski > k1_funct_1 > #nlpp > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_7 > #skF_6 > #skF_4 > #skF_11 > #skF_1 > #skF_8 > #skF_3 > #skF_10 > #skF_2 > #skF_9 > #skF_5
% 3.93/1.66  
% 3.93/1.66  %Foreground sorts:
% 3.93/1.66  
% 3.93/1.66  
% 3.93/1.66  %Background operators:
% 3.93/1.66  
% 3.93/1.66  
% 3.93/1.66  %Foreground operators:
% 3.93/1.66  tff('#skF_7', type, '#skF_7': $i > $i).
% 3.93/1.66  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 3.93/1.66  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.93/1.66  tff('#skF_4', type, '#skF_4': $i > $i).
% 3.93/1.66  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.93/1.66  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.93/1.66  tff('#skF_11', type, '#skF_11': $i).
% 3.93/1.66  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.93/1.66  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 3.93/1.66  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.93/1.66  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.93/1.66  tff('#skF_8', type, '#skF_8': $i > $i).
% 3.93/1.66  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 3.93/1.66  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.93/1.66  tff('#skF_10', type, '#skF_10': $i > $i).
% 3.93/1.66  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.93/1.66  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.93/1.66  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.93/1.66  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.93/1.66  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.93/1.66  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.93/1.66  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.93/1.66  tff('#skF_9', type, '#skF_9': ($i * $i) > $i).
% 3.93/1.66  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 3.93/1.66  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.93/1.66  
% 3.93/1.67  tff(f_53, axiom, (![A]: (v1_relat_1(A) <=> (![B]: ~(r2_hidden(B, A) & (![C, D]: ~(B = k4_tarski(C, D))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_relat_1)).
% 3.93/1.67  tff(f_104, negated_conjecture, ~(![A]: ((![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (![C]: ((v1_relat_1(C) & v1_funct_1(C)) => (((k1_relat_1(B) = A) & (k1_relat_1(C) = A)) => (B = C)))))) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t16_funct_1)).
% 3.93/1.67  tff(f_73, axiom, (![A, B]: (?[C]: (((v1_relat_1(C) & v1_funct_1(C)) & (k1_relat_1(C) = A)) & (![D]: (r2_hidden(D, A) => (k1_funct_1(C, D) = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', s3_funct_1__e2_24__funct_1)).
% 3.93/1.67  tff(f_85, axiom, (![A]: (?[B]: (((v1_relat_1(B) & v1_funct_1(B)) & (k1_relat_1(B) = A)) & (![C]: (r2_hidden(C, A) => (k1_funct_1(B, C) = k1_xboole_0)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', s3_funct_1__e2_25__funct_1)).
% 3.93/1.67  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 3.93/1.67  tff(f_61, axiom, (![A]: (v1_relat_1(A) => ((![B, C]: ~r2_hidden(k4_tarski(B, C), A)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t56_relat_1)).
% 3.93/1.67  tff(c_28, plain, (![A_13]: (r2_hidden('#skF_4'(A_13), A_13) | v1_relat_1(A_13))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.93/1.67  tff(c_48, plain, (k1_xboole_0!='#skF_11'), inference(cnfTransformation, [status(thm)], [f_104])).
% 3.93/1.67  tff(c_36, plain, (![A_34, B_35]: (v1_funct_1('#skF_9'(A_34, B_35)))), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.93/1.67  tff(c_34, plain, (![A_34, B_35]: (k1_relat_1('#skF_9'(A_34, B_35))=A_34)), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.93/1.67  tff(c_38, plain, (![A_34, B_35]: (v1_relat_1('#skF_9'(A_34, B_35)))), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.93/1.67  tff(c_44, plain, (![A_41]: (v1_funct_1('#skF_10'(A_41)))), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.93/1.67  tff(c_42, plain, (![A_41]: (k1_relat_1('#skF_10'(A_41))=A_41)), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.93/1.67  tff(c_46, plain, (![A_41]: (v1_relat_1('#skF_10'(A_41)))), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.93/1.67  tff(c_74, plain, (![C_62, B_63]: (C_62=B_63 | k1_relat_1(C_62)!='#skF_11' | k1_relat_1(B_63)!='#skF_11' | ~v1_funct_1(C_62) | ~v1_relat_1(C_62) | ~v1_funct_1(B_63) | ~v1_relat_1(B_63))), inference(cnfTransformation, [status(thm)], [f_104])).
% 3.93/1.67  tff(c_78, plain, (![B_63, A_41]: (B_63='#skF_10'(A_41) | k1_relat_1('#skF_10'(A_41))!='#skF_11' | k1_relat_1(B_63)!='#skF_11' | ~v1_funct_1('#skF_10'(A_41)) | ~v1_funct_1(B_63) | ~v1_relat_1(B_63))), inference(resolution, [status(thm)], [c_46, c_74])).
% 3.93/1.67  tff(c_291, plain, (![B_101, A_102]: (B_101='#skF_10'(A_102) | A_102!='#skF_11' | k1_relat_1(B_101)!='#skF_11' | ~v1_funct_1(B_101) | ~v1_relat_1(B_101))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_78])).
% 3.93/1.67  tff(c_297, plain, (![A_34, B_35, A_102]: ('#skF_9'(A_34, B_35)='#skF_10'(A_102) | A_102!='#skF_11' | k1_relat_1('#skF_9'(A_34, B_35))!='#skF_11' | ~v1_funct_1('#skF_9'(A_34, B_35)))), inference(resolution, [status(thm)], [c_38, c_291])).
% 3.93/1.67  tff(c_366, plain, (![A_107, B_108, A_109]: ('#skF_9'(A_107, B_108)='#skF_10'(A_109) | A_109!='#skF_11' | A_107!='#skF_11')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_297])).
% 3.93/1.67  tff(c_32, plain, (![A_34, B_35, D_40]: (k1_funct_1('#skF_9'(A_34, B_35), D_40)=B_35 | ~r2_hidden(D_40, A_34))), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.93/1.67  tff(c_606, plain, (![A_131, D_132, B_133, A_134]: (k1_funct_1('#skF_10'(A_131), D_132)=B_133 | ~r2_hidden(D_132, A_134) | A_131!='#skF_11' | A_134!='#skF_11')), inference(superposition, [status(thm), theory('equality')], [c_366, c_32])).
% 3.93/1.67  tff(c_1406, plain, (![A_1488, A_1489]: (k1_funct_1('#skF_10'(A_1488), '#skF_4'(A_1489))='#skF_11' | A_1488!='#skF_11' | A_1489!='#skF_11' | v1_relat_1(A_1489))), inference(resolution, [status(thm)], [c_28, c_606])).
% 3.93/1.67  tff(c_40, plain, (![A_41, C_46]: (k1_funct_1('#skF_10'(A_41), C_46)=k1_xboole_0 | ~r2_hidden(C_46, A_41))), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.93/1.67  tff(c_1409, plain, (![A_1489, A_1488]: (k1_xboole_0='#skF_11' | ~r2_hidden('#skF_4'(A_1489), A_1488) | A_1488!='#skF_11' | A_1489!='#skF_11' | v1_relat_1(A_1489))), inference(superposition, [status(thm), theory('equality')], [c_1406, c_40])).
% 3.93/1.67  tff(c_1596, plain, (![A_2869, A_2870]: (~r2_hidden('#skF_4'(A_2869), A_2870) | A_2870!='#skF_11' | A_2869!='#skF_11' | v1_relat_1(A_2869))), inference(negUnitSimplification, [status(thm)], [c_48, c_1409])).
% 3.93/1.67  tff(c_1609, plain, (![A_13]: (A_13!='#skF_11' | v1_relat_1(A_13))), inference(resolution, [status(thm)], [c_28, c_1596])).
% 3.93/1.67  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.93/1.67  tff(c_1946, plain, (![A_2928, A_2929]: (k1_funct_1('#skF_10'(A_2928), '#skF_1'(A_2929))='#skF_11' | A_2928!='#skF_11' | A_2929!='#skF_11' | v1_xboole_0(A_2929))), inference(resolution, [status(thm)], [c_4, c_606])).
% 3.93/1.67  tff(c_1949, plain, (![A_2929, A_2928]: (k1_xboole_0='#skF_11' | ~r2_hidden('#skF_1'(A_2929), A_2928) | A_2928!='#skF_11' | A_2929!='#skF_11' | v1_xboole_0(A_2929))), inference(superposition, [status(thm), theory('equality')], [c_1946, c_40])).
% 3.93/1.67  tff(c_2127, plain, (![A_4361, A_4362]: (~r2_hidden('#skF_1'(A_4361), A_4362) | A_4362!='#skF_11' | A_4361!='#skF_11' | v1_xboole_0(A_4361))), inference(negUnitSimplification, [status(thm)], [c_48, c_1949])).
% 3.93/1.67  tff(c_2144, plain, (![A_4389]: (A_4389!='#skF_11' | v1_xboole_0(A_4389))), inference(resolution, [status(thm)], [c_4, c_2127])).
% 3.93/1.67  tff(c_184, plain, (![A_88]: (k1_xboole_0=A_88 | r2_hidden(k4_tarski('#skF_7'(A_88), '#skF_8'(A_88)), A_88) | ~v1_relat_1(A_88))), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.93/1.67  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.93/1.67  tff(c_193, plain, (![A_88]: (~v1_xboole_0(A_88) | k1_xboole_0=A_88 | ~v1_relat_1(A_88))), inference(resolution, [status(thm)], [c_184, c_2])).
% 3.93/1.67  tff(c_2161, plain, (![A_4390]: (k1_xboole_0=A_4390 | ~v1_relat_1(A_4390) | A_4390!='#skF_11')), inference(resolution, [status(thm)], [c_2144, c_193])).
% 3.93/1.67  tff(c_2182, plain, (k1_xboole_0='#skF_11'), inference(resolution, [status(thm)], [c_1609, c_2161])).
% 3.93/1.67  tff(c_2201, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2182, c_48])).
% 3.93/1.67  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.93/1.67  
% 3.93/1.67  Inference rules
% 3.93/1.67  ----------------------
% 3.93/1.67  #Ref     : 3
% 3.93/1.67  #Sup     : 551
% 3.93/1.67  #Fact    : 0
% 3.93/1.67  #Define  : 0
% 3.93/1.67  #Split   : 1
% 3.93/1.67  #Chain   : 0
% 3.93/1.67  #Close   : 0
% 3.93/1.67  
% 3.93/1.67  Ordering : KBO
% 3.93/1.67  
% 3.93/1.67  Simplification rules
% 3.93/1.67  ----------------------
% 3.93/1.67  #Subsume      : 153
% 3.93/1.67  #Demod        : 63
% 3.93/1.67  #Tautology    : 74
% 3.93/1.67  #SimpNegUnit  : 11
% 3.93/1.67  #BackRed      : 11
% 3.93/1.67  
% 3.93/1.67  #Partial instantiations: 2898
% 3.93/1.67  #Strategies tried      : 1
% 3.93/1.67  
% 3.93/1.67  Timing (in seconds)
% 3.93/1.67  ----------------------
% 4.07/1.68  Preprocessing        : 0.31
% 4.07/1.68  Parsing              : 0.16
% 4.07/1.68  CNF conversion       : 0.03
% 4.07/1.68  Main loop            : 0.56
% 4.07/1.68  Inferencing          : 0.22
% 4.07/1.68  Reduction            : 0.15
% 4.07/1.68  Demodulation         : 0.11
% 4.07/1.68  BG Simplification    : 0.03
% 4.07/1.68  Subsumption          : 0.12
% 4.07/1.68  Abstraction          : 0.03
% 4.07/1.68  MUC search           : 0.00
% 4.07/1.68  Cooper               : 0.00
% 4.07/1.68  Total                : 0.90
% 4.07/1.68  Index Insertion      : 0.00
% 4.07/1.68  Index Deletion       : 0.00
% 4.07/1.68  Index Matching       : 0.00
% 4.07/1.68  BG Taut test         : 0.00
%------------------------------------------------------------------------------
