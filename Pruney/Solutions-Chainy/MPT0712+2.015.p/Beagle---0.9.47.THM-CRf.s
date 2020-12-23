%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:05:33 EST 2020

% Result     : Theorem 2.27s
% Output     : CNFRefutation 2.67s
% Verified   : 
% Statistics : Number of formulae       :   55 (  70 expanded)
%              Number of leaves         :   30 (  38 expanded)
%              Depth                    :    9
%              Number of atoms          :   85 ( 116 expanded)
%              Number of equality atoms :   31 (  38 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > v1_relat_1 > v1_funct_1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1

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

tff(f_33,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_35,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_69,axiom,(
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

tff(f_83,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_100,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_relat_1(B)
          & v1_funct_1(B) )
       => r1_tarski(k2_relat_1(k7_relat_1(B,k1_tarski(A))),k1_tarski(k1_funct_1(B,A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t167_funct_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_42,axiom,(
    ! [A,B] :
      ( ~ r2_hidden(A,B)
     => r1_xboole_0(k1_tarski(A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l27_zfmisc_1)).

tff(f_80,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( r1_xboole_0(B,k1_relat_1(A))
         => k7_relat_1(A,B) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t187_relat_1)).

tff(f_93,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( ( r2_hidden(A,k1_relat_1(C))
          & r2_hidden(B,k1_relat_1(C)) )
       => k9_relat_1(C,k2_tarski(A,B)) = k2_tarski(k1_funct_1(C,A),k1_funct_1(C,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t118_funct_1)).

tff(f_73,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

tff(c_8,plain,(
    ! [A_3] : k2_tarski(A_3,A_3) = k1_tarski(A_3) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_73,plain,(
    ! [A_36,B_37] : k1_enumset1(A_36,A_36,B_37) = k2_tarski(A_36,B_37) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_32,plain,(
    ! [A_11,B_12,C_13] : r1_tarski(k1_xboole_0,k1_enumset1(A_11,B_12,C_13)) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_90,plain,(
    ! [A_38,B_39] : r1_tarski(k1_xboole_0,k2_tarski(A_38,B_39)) ),
    inference(superposition,[status(thm),theory(equality)],[c_73,c_32])).

tff(c_92,plain,(
    ! [A_3] : r1_tarski(k1_xboole_0,k1_tarski(A_3)) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_90])).

tff(c_38,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_48,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_46,plain,(
    v1_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_14,plain,(
    ! [A_9,B_10] :
      ( r1_xboole_0(k1_tarski(A_9),B_10)
      | r2_hidden(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_200,plain,(
    ! [A_65,B_66] :
      ( k7_relat_1(A_65,B_66) = k1_xboole_0
      | ~ r1_xboole_0(B_66,k1_relat_1(A_65))
      | ~ v1_relat_1(A_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_208,plain,(
    ! [A_65,A_9] :
      ( k7_relat_1(A_65,k1_tarski(A_9)) = k1_xboole_0
      | ~ v1_relat_1(A_65)
      | r2_hidden(A_9,k1_relat_1(A_65)) ) ),
    inference(resolution,[status(thm)],[c_14,c_200])).

tff(c_215,plain,(
    ! [C_69,A_70,B_71] :
      ( k2_tarski(k1_funct_1(C_69,A_70),k1_funct_1(C_69,B_71)) = k9_relat_1(C_69,k2_tarski(A_70,B_71))
      | ~ r2_hidden(B_71,k1_relat_1(C_69))
      | ~ r2_hidden(A_70,k1_relat_1(C_69))
      | ~ v1_funct_1(C_69)
      | ~ v1_relat_1(C_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_249,plain,(
    ! [C_69,A_70] :
      ( k9_relat_1(C_69,k2_tarski(A_70,A_70)) = k1_tarski(k1_funct_1(C_69,A_70))
      | ~ r2_hidden(A_70,k1_relat_1(C_69))
      | ~ r2_hidden(A_70,k1_relat_1(C_69))
      | ~ v1_funct_1(C_69)
      | ~ v1_relat_1(C_69) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_215])).

tff(c_395,plain,(
    ! [C_110,A_111] :
      ( k9_relat_1(C_110,k1_tarski(A_111)) = k1_tarski(k1_funct_1(C_110,A_111))
      | ~ r2_hidden(A_111,k1_relat_1(C_110))
      | ~ r2_hidden(A_111,k1_relat_1(C_110))
      | ~ v1_funct_1(C_110)
      | ~ v1_relat_1(C_110) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_249])).

tff(c_402,plain,(
    ! [A_112,A_113] :
      ( k9_relat_1(A_112,k1_tarski(A_113)) = k1_tarski(k1_funct_1(A_112,A_113))
      | ~ r2_hidden(A_113,k1_relat_1(A_112))
      | ~ v1_funct_1(A_112)
      | k7_relat_1(A_112,k1_tarski(A_113)) = k1_xboole_0
      | ~ v1_relat_1(A_112) ) ),
    inference(resolution,[status(thm)],[c_208,c_395])).

tff(c_410,plain,(
    ! [A_114,A_115] :
      ( k9_relat_1(A_114,k1_tarski(A_115)) = k1_tarski(k1_funct_1(A_114,A_115))
      | ~ v1_funct_1(A_114)
      | k7_relat_1(A_114,k1_tarski(A_115)) = k1_xboole_0
      | ~ v1_relat_1(A_114) ) ),
    inference(resolution,[status(thm)],[c_208,c_402])).

tff(c_177,plain,(
    ! [B_60,A_61] :
      ( k2_relat_1(k7_relat_1(B_60,A_61)) = k9_relat_1(B_60,A_61)
      | ~ v1_relat_1(B_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_44,plain,(
    ~ r1_tarski(k2_relat_1(k7_relat_1('#skF_2',k1_tarski('#skF_1'))),k1_tarski(k1_funct_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_183,plain,
    ( ~ r1_tarski(k9_relat_1('#skF_2',k1_tarski('#skF_1')),k1_tarski(k1_funct_1('#skF_2','#skF_1')))
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_177,c_44])).

tff(c_189,plain,(
    ~ r1_tarski(k9_relat_1('#skF_2',k1_tarski('#skF_1')),k1_tarski(k1_funct_1('#skF_2','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_183])).

tff(c_422,plain,
    ( ~ r1_tarski(k1_tarski(k1_funct_1('#skF_2','#skF_1')),k1_tarski(k1_funct_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_2')
    | k7_relat_1('#skF_2',k1_tarski('#skF_1')) = k1_xboole_0
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_410,c_189])).

tff(c_429,plain,(
    k7_relat_1('#skF_2',k1_tarski('#skF_1')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_6,c_422])).

tff(c_431,plain,(
    ~ r1_tarski(k2_relat_1(k1_xboole_0),k1_tarski(k1_funct_1('#skF_2','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_429,c_44])).

tff(c_434,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_38,c_431])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n008.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 11:56:15 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.27/1.34  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.67/1.34  
% 2.67/1.34  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.67/1.35  %$ r2_hidden > r1_xboole_0 > r1_tarski > v1_relat_1 > v1_funct_1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1
% 2.67/1.35  
% 2.67/1.35  %Foreground sorts:
% 2.67/1.35  
% 2.67/1.35  
% 2.67/1.35  %Background operators:
% 2.67/1.35  
% 2.67/1.35  
% 2.67/1.35  %Foreground operators:
% 2.67/1.35  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.67/1.35  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.67/1.35  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.67/1.35  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.67/1.35  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.67/1.35  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.67/1.35  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.67/1.35  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.67/1.35  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.67/1.35  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.67/1.35  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.67/1.35  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.67/1.35  tff('#skF_2', type, '#skF_2': $i).
% 2.67/1.35  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.67/1.35  tff('#skF_1', type, '#skF_1': $i).
% 2.67/1.35  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.67/1.35  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.67/1.35  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.67/1.35  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.67/1.35  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.67/1.35  
% 2.67/1.36  tff(f_33, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 2.67/1.36  tff(f_35, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 2.67/1.36  tff(f_69, axiom, (![A, B, C, D]: (r1_tarski(D, k1_enumset1(A, B, C)) <=> ~(((((((~(D = k1_xboole_0) & ~(D = k1_tarski(A))) & ~(D = k1_tarski(B))) & ~(D = k1_tarski(C))) & ~(D = k2_tarski(A, B))) & ~(D = k2_tarski(B, C))) & ~(D = k2_tarski(A, C))) & ~(D = k1_enumset1(A, B, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t142_zfmisc_1)).
% 2.67/1.36  tff(f_83, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 2.67/1.36  tff(f_100, negated_conjecture, ~(![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => r1_tarski(k2_relat_1(k7_relat_1(B, k1_tarski(A))), k1_tarski(k1_funct_1(B, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t167_funct_1)).
% 2.67/1.36  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.67/1.36  tff(f_42, axiom, (![A, B]: (~r2_hidden(A, B) => r1_xboole_0(k1_tarski(A), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 2.67/1.36  tff(f_80, axiom, (![A]: (v1_relat_1(A) => (![B]: (r1_xboole_0(B, k1_relat_1(A)) => (k7_relat_1(A, B) = k1_xboole_0))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t187_relat_1)).
% 2.67/1.36  tff(f_93, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => ((r2_hidden(A, k1_relat_1(C)) & r2_hidden(B, k1_relat_1(C))) => (k9_relat_1(C, k2_tarski(A, B)) = k2_tarski(k1_funct_1(C, A), k1_funct_1(C, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t118_funct_1)).
% 2.67/1.36  tff(f_73, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_relat_1)).
% 2.67/1.36  tff(c_8, plain, (![A_3]: (k2_tarski(A_3, A_3)=k1_tarski(A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.67/1.36  tff(c_73, plain, (![A_36, B_37]: (k1_enumset1(A_36, A_36, B_37)=k2_tarski(A_36, B_37))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.67/1.36  tff(c_32, plain, (![A_11, B_12, C_13]: (r1_tarski(k1_xboole_0, k1_enumset1(A_11, B_12, C_13)))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.67/1.36  tff(c_90, plain, (![A_38, B_39]: (r1_tarski(k1_xboole_0, k2_tarski(A_38, B_39)))), inference(superposition, [status(thm), theory('equality')], [c_73, c_32])).
% 2.67/1.36  tff(c_92, plain, (![A_3]: (r1_tarski(k1_xboole_0, k1_tarski(A_3)))), inference(superposition, [status(thm), theory('equality')], [c_8, c_90])).
% 2.67/1.36  tff(c_38, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.67/1.36  tff(c_48, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_100])).
% 2.67/1.36  tff(c_46, plain, (v1_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_100])).
% 2.67/1.36  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.67/1.36  tff(c_14, plain, (![A_9, B_10]: (r1_xboole_0(k1_tarski(A_9), B_10) | r2_hidden(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.67/1.36  tff(c_200, plain, (![A_65, B_66]: (k7_relat_1(A_65, B_66)=k1_xboole_0 | ~r1_xboole_0(B_66, k1_relat_1(A_65)) | ~v1_relat_1(A_65))), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.67/1.36  tff(c_208, plain, (![A_65, A_9]: (k7_relat_1(A_65, k1_tarski(A_9))=k1_xboole_0 | ~v1_relat_1(A_65) | r2_hidden(A_9, k1_relat_1(A_65)))), inference(resolution, [status(thm)], [c_14, c_200])).
% 2.67/1.36  tff(c_215, plain, (![C_69, A_70, B_71]: (k2_tarski(k1_funct_1(C_69, A_70), k1_funct_1(C_69, B_71))=k9_relat_1(C_69, k2_tarski(A_70, B_71)) | ~r2_hidden(B_71, k1_relat_1(C_69)) | ~r2_hidden(A_70, k1_relat_1(C_69)) | ~v1_funct_1(C_69) | ~v1_relat_1(C_69))), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.67/1.36  tff(c_249, plain, (![C_69, A_70]: (k9_relat_1(C_69, k2_tarski(A_70, A_70))=k1_tarski(k1_funct_1(C_69, A_70)) | ~r2_hidden(A_70, k1_relat_1(C_69)) | ~r2_hidden(A_70, k1_relat_1(C_69)) | ~v1_funct_1(C_69) | ~v1_relat_1(C_69))), inference(superposition, [status(thm), theory('equality')], [c_8, c_215])).
% 2.67/1.36  tff(c_395, plain, (![C_110, A_111]: (k9_relat_1(C_110, k1_tarski(A_111))=k1_tarski(k1_funct_1(C_110, A_111)) | ~r2_hidden(A_111, k1_relat_1(C_110)) | ~r2_hidden(A_111, k1_relat_1(C_110)) | ~v1_funct_1(C_110) | ~v1_relat_1(C_110))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_249])).
% 2.67/1.36  tff(c_402, plain, (![A_112, A_113]: (k9_relat_1(A_112, k1_tarski(A_113))=k1_tarski(k1_funct_1(A_112, A_113)) | ~r2_hidden(A_113, k1_relat_1(A_112)) | ~v1_funct_1(A_112) | k7_relat_1(A_112, k1_tarski(A_113))=k1_xboole_0 | ~v1_relat_1(A_112))), inference(resolution, [status(thm)], [c_208, c_395])).
% 2.67/1.36  tff(c_410, plain, (![A_114, A_115]: (k9_relat_1(A_114, k1_tarski(A_115))=k1_tarski(k1_funct_1(A_114, A_115)) | ~v1_funct_1(A_114) | k7_relat_1(A_114, k1_tarski(A_115))=k1_xboole_0 | ~v1_relat_1(A_114))), inference(resolution, [status(thm)], [c_208, c_402])).
% 2.67/1.36  tff(c_177, plain, (![B_60, A_61]: (k2_relat_1(k7_relat_1(B_60, A_61))=k9_relat_1(B_60, A_61) | ~v1_relat_1(B_60))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.67/1.36  tff(c_44, plain, (~r1_tarski(k2_relat_1(k7_relat_1('#skF_2', k1_tarski('#skF_1'))), k1_tarski(k1_funct_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_100])).
% 2.67/1.36  tff(c_183, plain, (~r1_tarski(k9_relat_1('#skF_2', k1_tarski('#skF_1')), k1_tarski(k1_funct_1('#skF_2', '#skF_1'))) | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_177, c_44])).
% 2.67/1.36  tff(c_189, plain, (~r1_tarski(k9_relat_1('#skF_2', k1_tarski('#skF_1')), k1_tarski(k1_funct_1('#skF_2', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_183])).
% 2.67/1.36  tff(c_422, plain, (~r1_tarski(k1_tarski(k1_funct_1('#skF_2', '#skF_1')), k1_tarski(k1_funct_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_2') | k7_relat_1('#skF_2', k1_tarski('#skF_1'))=k1_xboole_0 | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_410, c_189])).
% 2.67/1.36  tff(c_429, plain, (k7_relat_1('#skF_2', k1_tarski('#skF_1'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_6, c_422])).
% 2.67/1.36  tff(c_431, plain, (~r1_tarski(k2_relat_1(k1_xboole_0), k1_tarski(k1_funct_1('#skF_2', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_429, c_44])).
% 2.67/1.36  tff(c_434, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_92, c_38, c_431])).
% 2.67/1.36  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.67/1.36  
% 2.67/1.36  Inference rules
% 2.67/1.36  ----------------------
% 2.67/1.36  #Ref     : 0
% 2.67/1.36  #Sup     : 92
% 2.67/1.36  #Fact    : 0
% 2.67/1.36  #Define  : 0
% 2.67/1.36  #Split   : 1
% 2.67/1.36  #Chain   : 0
% 2.67/1.36  #Close   : 0
% 2.67/1.36  
% 2.67/1.36  Ordering : KBO
% 2.67/1.36  
% 2.67/1.36  Simplification rules
% 2.67/1.36  ----------------------
% 2.67/1.36  #Subsume      : 14
% 2.67/1.36  #Demod        : 47
% 2.67/1.36  #Tautology    : 41
% 2.67/1.36  #SimpNegUnit  : 0
% 2.67/1.36  #BackRed      : 1
% 2.67/1.36  
% 2.67/1.36  #Partial instantiations: 0
% 2.67/1.36  #Strategies tried      : 1
% 2.67/1.36  
% 2.67/1.36  Timing (in seconds)
% 2.67/1.36  ----------------------
% 2.67/1.36  Preprocessing        : 0.31
% 2.67/1.36  Parsing              : 0.16
% 2.67/1.36  CNF conversion       : 0.02
% 2.67/1.36  Main loop            : 0.29
% 2.67/1.36  Inferencing          : 0.11
% 2.67/1.36  Reduction            : 0.09
% 2.67/1.36  Demodulation         : 0.07
% 2.67/1.36  BG Simplification    : 0.02
% 2.67/1.36  Subsumption          : 0.05
% 2.67/1.36  Abstraction          : 0.02
% 2.67/1.36  MUC search           : 0.00
% 2.67/1.36  Cooper               : 0.00
% 2.67/1.36  Total                : 0.62
% 2.67/1.36  Index Insertion      : 0.00
% 2.67/1.36  Index Deletion       : 0.00
% 2.67/1.36  Index Matching       : 0.00
% 2.67/1.36  BG Taut test         : 0.00
%------------------------------------------------------------------------------
