%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:02:52 EST 2020

% Result     : Theorem 2.25s
% Output     : CNFRefutation 2.51s
% Verified   : 
% Statistics : Number of formulae       :   58 ( 110 expanded)
%              Number of leaves         :   30 (  53 expanded)
%              Depth                    :   11
%              Number of atoms          :   87 ( 210 expanded)
%              Number of equality atoms :   39 (  95 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_relat_1 > v1_funct_1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k4_tarski > k2_tarski > k1_funct_1 > k11_relat_1 > #nlpp > k2_relat_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

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

tff(k11_relat_1,type,(
    k11_relat_1: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_96,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_relat_1(B)
          & v1_funct_1(B) )
       => ( k1_relat_1(B) = k1_tarski(A)
         => k2_relat_1(B) = k1_tarski(k1_funct_1(B,A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_funct_1)).

tff(f_60,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] : k11_relat_1(A,B) = k9_relat_1(A,k1_tarski(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d16_relat_1)).

tff(f_64,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k9_relat_1(A,k1_relat_1(A)) = k2_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_relat_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_41,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_77,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r2_hidden(A,k1_relat_1(B))
      <=> k11_relat_1(B,A) != k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t205_relat_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ~ ( A != k1_tarski(B)
        & A != k1_xboole_0
        & ! [C] :
            ~ ( r2_hidden(C,A)
              & C != B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_zfmisc_1)).

tff(f_70,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(k4_tarski(A,B),C)
      <=> r2_hidden(B,k11_relat_1(C,A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t204_relat_1)).

tff(f_87,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( r2_hidden(k4_tarski(A,B),C)
      <=> ( r2_hidden(A,k1_relat_1(C))
          & B = k1_funct_1(C,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_funct_1)).

tff(c_46,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_42,plain,(
    k1_tarski('#skF_2') = k1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_136,plain,(
    ! [A_45,B_46] :
      ( k9_relat_1(A_45,k1_tarski(B_46)) = k11_relat_1(A_45,B_46)
      | ~ v1_relat_1(A_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_148,plain,(
    ! [A_47] :
      ( k9_relat_1(A_47,k1_relat_1('#skF_3')) = k11_relat_1(A_47,'#skF_2')
      | ~ v1_relat_1(A_47) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_136])).

tff(c_24,plain,(
    ! [A_17] :
      ( k9_relat_1(A_17,k1_relat_1(A_17)) = k2_relat_1(A_17)
      | ~ v1_relat_1(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_155,plain,
    ( k11_relat_1('#skF_3','#skF_2') = k2_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_148,c_24])).

tff(c_165,plain,(
    k11_relat_1('#skF_3','#skF_2') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_46,c_155])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_75,plain,(
    ! [A_32,B_33] :
      ( r2_hidden(A_32,B_33)
      | ~ r1_tarski(k1_tarski(A_32),B_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_89,plain,(
    ! [A_35] : r2_hidden(A_35,k1_tarski(A_35)) ),
    inference(resolution,[status(thm)],[c_6,c_75])).

tff(c_92,plain,(
    r2_hidden('#skF_2',k1_relat_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_89])).

tff(c_198,plain,(
    ! [B_53,A_54] :
      ( k11_relat_1(B_53,A_54) != k1_xboole_0
      | ~ r2_hidden(A_54,k1_relat_1(B_53))
      | ~ v1_relat_1(B_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_208,plain,
    ( k11_relat_1('#skF_3','#skF_2') != k1_xboole_0
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_92,c_198])).

tff(c_213,plain,(
    k2_relat_1('#skF_3') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_165,c_208])).

tff(c_20,plain,(
    ! [A_11,B_12] :
      ( r2_hidden('#skF_1'(A_11,B_12),A_11)
      | k1_xboole_0 = A_11
      | k1_tarski(B_12) = A_11 ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_44,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_26,plain,(
    ! [A_18,B_19,C_20] :
      ( r2_hidden(k4_tarski(A_18,B_19),C_20)
      | ~ r2_hidden(B_19,k11_relat_1(C_20,A_18))
      | ~ v1_relat_1(C_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_325,plain,(
    ! [C_70,A_71,B_72] :
      ( k1_funct_1(C_70,A_71) = B_72
      | ~ r2_hidden(k4_tarski(A_71,B_72),C_70)
      | ~ v1_funct_1(C_70)
      | ~ v1_relat_1(C_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_384,plain,(
    ! [C_78,A_79,B_80] :
      ( k1_funct_1(C_78,A_79) = B_80
      | ~ v1_funct_1(C_78)
      | ~ r2_hidden(B_80,k11_relat_1(C_78,A_79))
      | ~ v1_relat_1(C_78) ) ),
    inference(resolution,[status(thm)],[c_26,c_325])).

tff(c_399,plain,(
    ! [B_80] :
      ( k1_funct_1('#skF_3','#skF_2') = B_80
      | ~ v1_funct_1('#skF_3')
      | ~ r2_hidden(B_80,k2_relat_1('#skF_3'))
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_165,c_384])).

tff(c_405,plain,(
    ! [B_81] :
      ( k1_funct_1('#skF_3','#skF_2') = B_81
      | ~ r2_hidden(B_81,k2_relat_1('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_399])).

tff(c_417,plain,(
    ! [B_12] :
      ( '#skF_1'(k2_relat_1('#skF_3'),B_12) = k1_funct_1('#skF_3','#skF_2')
      | k2_relat_1('#skF_3') = k1_xboole_0
      | k2_relat_1('#skF_3') = k1_tarski(B_12) ) ),
    inference(resolution,[status(thm)],[c_20,c_405])).

tff(c_424,plain,(
    ! [B_82] :
      ( '#skF_1'(k2_relat_1('#skF_3'),B_82) = k1_funct_1('#skF_3','#skF_2')
      | k2_relat_1('#skF_3') = k1_tarski(B_82) ) ),
    inference(negUnitSimplification,[status(thm)],[c_213,c_417])).

tff(c_18,plain,(
    ! [A_11,B_12] :
      ( '#skF_1'(A_11,B_12) != B_12
      | k1_xboole_0 = A_11
      | k1_tarski(B_12) = A_11 ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_432,plain,(
    ! [B_82] :
      ( k1_funct_1('#skF_3','#skF_2') != B_82
      | k2_relat_1('#skF_3') = k1_xboole_0
      | k2_relat_1('#skF_3') = k1_tarski(B_82)
      | k2_relat_1('#skF_3') = k1_tarski(B_82) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_424,c_18])).

tff(c_440,plain,(
    k1_tarski(k1_funct_1('#skF_3','#skF_2')) = k2_relat_1('#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_213,c_432])).

tff(c_40,plain,(
    k1_tarski(k1_funct_1('#skF_3','#skF_2')) != k2_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_443,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_440,c_40])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n010.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 16:08:14 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.25/1.32  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.51/1.33  
% 2.51/1.33  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.51/1.33  %$ r2_hidden > r1_tarski > v1_relat_1 > v1_funct_1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k4_tarski > k2_tarski > k1_funct_1 > k11_relat_1 > #nlpp > k2_relat_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.51/1.33  
% 2.51/1.33  %Foreground sorts:
% 2.51/1.33  
% 2.51/1.33  
% 2.51/1.33  %Background operators:
% 2.51/1.33  
% 2.51/1.33  
% 2.51/1.33  %Foreground operators:
% 2.51/1.33  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.51/1.33  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.51/1.33  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.51/1.33  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.51/1.33  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.51/1.33  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.51/1.33  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.51/1.33  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.51/1.33  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.51/1.33  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.51/1.33  tff(k11_relat_1, type, k11_relat_1: ($i * $i) > $i).
% 2.51/1.33  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.51/1.33  tff('#skF_2', type, '#skF_2': $i).
% 2.51/1.33  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.51/1.33  tff('#skF_3', type, '#skF_3': $i).
% 2.51/1.33  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.51/1.33  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.51/1.33  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.51/1.33  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.51/1.33  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.51/1.33  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.51/1.33  
% 2.51/1.34  tff(f_96, negated_conjecture, ~(![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((k1_relat_1(B) = k1_tarski(A)) => (k2_relat_1(B) = k1_tarski(k1_funct_1(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t14_funct_1)).
% 2.51/1.34  tff(f_60, axiom, (![A]: (v1_relat_1(A) => (![B]: (k11_relat_1(A, B) = k9_relat_1(A, k1_tarski(B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d16_relat_1)).
% 2.51/1.34  tff(f_64, axiom, (![A]: (v1_relat_1(A) => (k9_relat_1(A, k1_relat_1(A)) = k2_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t146_relat_1)).
% 2.51/1.34  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.51/1.34  tff(f_41, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 2.51/1.34  tff(f_77, axiom, (![A, B]: (v1_relat_1(B) => (r2_hidden(A, k1_relat_1(B)) <=> ~(k11_relat_1(B, A) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t205_relat_1)).
% 2.51/1.34  tff(f_55, axiom, (![A, B]: ~((~(A = k1_tarski(B)) & ~(A = k1_xboole_0)) & (![C]: ~(r2_hidden(C, A) & ~(C = B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_zfmisc_1)).
% 2.51/1.34  tff(f_70, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(k4_tarski(A, B), C) <=> r2_hidden(B, k11_relat_1(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t204_relat_1)).
% 2.51/1.34  tff(f_87, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(k4_tarski(A, B), C) <=> (r2_hidden(A, k1_relat_1(C)) & (B = k1_funct_1(C, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_funct_1)).
% 2.51/1.34  tff(c_46, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_96])).
% 2.51/1.34  tff(c_42, plain, (k1_tarski('#skF_2')=k1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_96])).
% 2.51/1.34  tff(c_136, plain, (![A_45, B_46]: (k9_relat_1(A_45, k1_tarski(B_46))=k11_relat_1(A_45, B_46) | ~v1_relat_1(A_45))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.51/1.34  tff(c_148, plain, (![A_47]: (k9_relat_1(A_47, k1_relat_1('#skF_3'))=k11_relat_1(A_47, '#skF_2') | ~v1_relat_1(A_47))), inference(superposition, [status(thm), theory('equality')], [c_42, c_136])).
% 2.51/1.34  tff(c_24, plain, (![A_17]: (k9_relat_1(A_17, k1_relat_1(A_17))=k2_relat_1(A_17) | ~v1_relat_1(A_17))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.51/1.34  tff(c_155, plain, (k11_relat_1('#skF_3', '#skF_2')=k2_relat_1('#skF_3') | ~v1_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_148, c_24])).
% 2.51/1.34  tff(c_165, plain, (k11_relat_1('#skF_3', '#skF_2')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_46, c_155])).
% 2.51/1.34  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.51/1.34  tff(c_75, plain, (![A_32, B_33]: (r2_hidden(A_32, B_33) | ~r1_tarski(k1_tarski(A_32), B_33))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.51/1.34  tff(c_89, plain, (![A_35]: (r2_hidden(A_35, k1_tarski(A_35)))), inference(resolution, [status(thm)], [c_6, c_75])).
% 2.51/1.34  tff(c_92, plain, (r2_hidden('#skF_2', k1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_42, c_89])).
% 2.51/1.34  tff(c_198, plain, (![B_53, A_54]: (k11_relat_1(B_53, A_54)!=k1_xboole_0 | ~r2_hidden(A_54, k1_relat_1(B_53)) | ~v1_relat_1(B_53))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.51/1.34  tff(c_208, plain, (k11_relat_1('#skF_3', '#skF_2')!=k1_xboole_0 | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_92, c_198])).
% 2.51/1.34  tff(c_213, plain, (k2_relat_1('#skF_3')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_46, c_165, c_208])).
% 2.51/1.34  tff(c_20, plain, (![A_11, B_12]: (r2_hidden('#skF_1'(A_11, B_12), A_11) | k1_xboole_0=A_11 | k1_tarski(B_12)=A_11)), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.51/1.34  tff(c_44, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_96])).
% 2.51/1.34  tff(c_26, plain, (![A_18, B_19, C_20]: (r2_hidden(k4_tarski(A_18, B_19), C_20) | ~r2_hidden(B_19, k11_relat_1(C_20, A_18)) | ~v1_relat_1(C_20))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.51/1.34  tff(c_325, plain, (![C_70, A_71, B_72]: (k1_funct_1(C_70, A_71)=B_72 | ~r2_hidden(k4_tarski(A_71, B_72), C_70) | ~v1_funct_1(C_70) | ~v1_relat_1(C_70))), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.51/1.34  tff(c_384, plain, (![C_78, A_79, B_80]: (k1_funct_1(C_78, A_79)=B_80 | ~v1_funct_1(C_78) | ~r2_hidden(B_80, k11_relat_1(C_78, A_79)) | ~v1_relat_1(C_78))), inference(resolution, [status(thm)], [c_26, c_325])).
% 2.51/1.34  tff(c_399, plain, (![B_80]: (k1_funct_1('#skF_3', '#skF_2')=B_80 | ~v1_funct_1('#skF_3') | ~r2_hidden(B_80, k2_relat_1('#skF_3')) | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_165, c_384])).
% 2.51/1.34  tff(c_405, plain, (![B_81]: (k1_funct_1('#skF_3', '#skF_2')=B_81 | ~r2_hidden(B_81, k2_relat_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_399])).
% 2.51/1.34  tff(c_417, plain, (![B_12]: ('#skF_1'(k2_relat_1('#skF_3'), B_12)=k1_funct_1('#skF_3', '#skF_2') | k2_relat_1('#skF_3')=k1_xboole_0 | k2_relat_1('#skF_3')=k1_tarski(B_12))), inference(resolution, [status(thm)], [c_20, c_405])).
% 2.51/1.34  tff(c_424, plain, (![B_82]: ('#skF_1'(k2_relat_1('#skF_3'), B_82)=k1_funct_1('#skF_3', '#skF_2') | k2_relat_1('#skF_3')=k1_tarski(B_82))), inference(negUnitSimplification, [status(thm)], [c_213, c_417])).
% 2.51/1.34  tff(c_18, plain, (![A_11, B_12]: ('#skF_1'(A_11, B_12)!=B_12 | k1_xboole_0=A_11 | k1_tarski(B_12)=A_11)), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.51/1.34  tff(c_432, plain, (![B_82]: (k1_funct_1('#skF_3', '#skF_2')!=B_82 | k2_relat_1('#skF_3')=k1_xboole_0 | k2_relat_1('#skF_3')=k1_tarski(B_82) | k2_relat_1('#skF_3')=k1_tarski(B_82))), inference(superposition, [status(thm), theory('equality')], [c_424, c_18])).
% 2.51/1.34  tff(c_440, plain, (k1_tarski(k1_funct_1('#skF_3', '#skF_2'))=k2_relat_1('#skF_3')), inference(negUnitSimplification, [status(thm)], [c_213, c_432])).
% 2.51/1.34  tff(c_40, plain, (k1_tarski(k1_funct_1('#skF_3', '#skF_2'))!=k2_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_96])).
% 2.51/1.34  tff(c_443, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_440, c_40])).
% 2.51/1.34  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.51/1.34  
% 2.51/1.34  Inference rules
% 2.51/1.34  ----------------------
% 2.51/1.34  #Ref     : 0
% 2.51/1.34  #Sup     : 80
% 2.51/1.34  #Fact    : 0
% 2.51/1.34  #Define  : 0
% 2.51/1.34  #Split   : 1
% 2.51/1.34  #Chain   : 0
% 2.51/1.34  #Close   : 0
% 2.51/1.34  
% 2.51/1.34  Ordering : KBO
% 2.51/1.34  
% 2.51/1.34  Simplification rules
% 2.51/1.34  ----------------------
% 2.51/1.34  #Subsume      : 4
% 2.51/1.34  #Demod        : 31
% 2.51/1.34  #Tautology    : 36
% 2.51/1.34  #SimpNegUnit  : 5
% 2.51/1.34  #BackRed      : 1
% 2.51/1.34  
% 2.51/1.34  #Partial instantiations: 0
% 2.51/1.34  #Strategies tried      : 1
% 2.51/1.34  
% 2.51/1.34  Timing (in seconds)
% 2.51/1.34  ----------------------
% 2.51/1.34  Preprocessing        : 0.32
% 2.51/1.34  Parsing              : 0.17
% 2.51/1.34  CNF conversion       : 0.02
% 2.51/1.34  Main loop            : 0.25
% 2.51/1.34  Inferencing          : 0.09
% 2.51/1.34  Reduction            : 0.07
% 2.51/1.34  Demodulation         : 0.05
% 2.51/1.35  BG Simplification    : 0.02
% 2.51/1.35  Subsumption          : 0.05
% 2.51/1.35  Abstraction          : 0.01
% 2.51/1.35  MUC search           : 0.00
% 2.51/1.35  Cooper               : 0.00
% 2.51/1.35  Total                : 0.59
% 2.51/1.35  Index Insertion      : 0.00
% 2.51/1.35  Index Deletion       : 0.00
% 2.51/1.35  Index Matching       : 0.00
% 2.51/1.35  BG Taut test         : 0.00
%------------------------------------------------------------------------------
