%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:59:40 EST 2020

% Result     : Theorem 3.20s
% Output     : CNFRefutation 3.20s
% Verified   : 
% Statistics : Number of formulae       :   76 (  92 expanded)
%              Number of leaves         :   39 (  48 expanded)
%              Depth                    :    9
%              Number of atoms          :   96 ( 132 expanded)
%              Number of equality atoms :   21 (  32 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > v1_xboole_0 > v1_relat_1 > k2_enumset1 > k1_enumset1 > k7_relat_1 > k5_relat_1 > k4_tarski > k3_xboole_0 > k2_tarski > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_6 > #skF_1 > #skF_7 > #skF_3 > #skF_8 > #skF_2 > #skF_5 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i ) > $i )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

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

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_32,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_74,axiom,(
    ! [A,B] :
      ( B = k1_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(C,D),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_1)).

tff(f_104,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ( k7_relat_1(B,A) = k1_xboole_0
        <=> r1_xboole_0(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_relat_1)).

tff(f_36,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_76,axiom,(
    ! [A] : v1_relat_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).

tff(f_89,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_85,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_xboole_0(k2_relat_1(A),k1_relat_1(B))
           => k5_relat_1(A,B) = k1_xboole_0 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_relat_1)).

tff(f_97,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k7_relat_1(B,A) = k5_relat_1(k6_relat_1(A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).

tff(f_93,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k1_relat_1(k7_relat_1(B,A)) = k3_xboole_0(k1_relat_1(B),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t90_relat_1)).

tff(f_54,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & r2_hidden(C,B) ) )
      & ~ ( ? [C] :
              ( r2_hidden(C,A)
              & r2_hidden(C,B) )
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

tff(f_60,axiom,(
    ! [A,B] :
      ~ ( ~ r1_xboole_0(A,B)
        & r1_xboole_0(k3_xboole_0(A,B),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_xboole_1)).

tff(c_6,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_1277,plain,(
    ! [C_214,A_215] :
      ( r2_hidden(k4_tarski(C_214,'#skF_6'(A_215,k1_relat_1(A_215),C_214)),A_215)
      | ~ r2_hidden(C_214,k1_relat_1(A_215)) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_1294,plain,(
    ! [A_216,C_217] :
      ( ~ v1_xboole_0(A_216)
      | ~ r2_hidden(C_217,k1_relat_1(A_216)) ) ),
    inference(resolution,[status(thm)],[c_1277,c_2])).

tff(c_1321,plain,(
    ! [A_218] :
      ( ~ v1_xboole_0(A_218)
      | v1_xboole_0(k1_relat_1(A_218)) ) ),
    inference(resolution,[status(thm)],[c_4,c_1294])).

tff(c_50,plain,
    ( ~ r1_xboole_0(k1_relat_1('#skF_8'),'#skF_7')
    | k7_relat_1('#skF_8','#skF_7') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_92,plain,(
    k7_relat_1('#skF_8','#skF_7') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_50])).

tff(c_48,plain,(
    v1_relat_1('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_56,plain,
    ( k7_relat_1('#skF_8','#skF_7') = k1_xboole_0
    | r1_xboole_0(k1_relat_1('#skF_8'),'#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_115,plain,(
    r1_xboole_0(k1_relat_1('#skF_8'),'#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_92,c_56])).

tff(c_8,plain,(
    ! [B_6,A_5] :
      ( r1_xboole_0(B_6,A_5)
      | ~ r1_xboole_0(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_118,plain,(
    r1_xboole_0('#skF_7',k1_relat_1('#skF_8')) ),
    inference(resolution,[status(thm)],[c_115,c_8])).

tff(c_36,plain,(
    ! [A_40] : v1_relat_1(k6_relat_1(A_40)) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_42,plain,(
    ! [A_44] : k2_relat_1(k6_relat_1(A_44)) = A_44 ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_258,plain,(
    ! [A_97,B_98] :
      ( k5_relat_1(A_97,B_98) = k1_xboole_0
      | ~ r1_xboole_0(k2_relat_1(A_97),k1_relat_1(B_98))
      | ~ v1_relat_1(B_98)
      | ~ v1_relat_1(A_97) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_273,plain,(
    ! [A_44,B_98] :
      ( k5_relat_1(k6_relat_1(A_44),B_98) = k1_xboole_0
      | ~ r1_xboole_0(A_44,k1_relat_1(B_98))
      | ~ v1_relat_1(B_98)
      | ~ v1_relat_1(k6_relat_1(A_44)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_258])).

tff(c_951,plain,(
    ! [A_167,B_168] :
      ( k5_relat_1(k6_relat_1(A_167),B_168) = k1_xboole_0
      | ~ r1_xboole_0(A_167,k1_relat_1(B_168))
      | ~ v1_relat_1(B_168) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_273])).

tff(c_988,plain,
    ( k5_relat_1(k6_relat_1('#skF_7'),'#skF_8') = k1_xboole_0
    | ~ v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_118,c_951])).

tff(c_1012,plain,(
    k5_relat_1(k6_relat_1('#skF_7'),'#skF_8') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_988])).

tff(c_46,plain,(
    ! [A_47,B_48] :
      ( k5_relat_1(k6_relat_1(A_47),B_48) = k7_relat_1(B_48,A_47)
      | ~ v1_relat_1(B_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_1022,plain,
    ( k7_relat_1('#skF_8','#skF_7') = k1_xboole_0
    | ~ v1_relat_1('#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_1012,c_46])).

tff(c_1029,plain,(
    k7_relat_1('#skF_8','#skF_7') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_1022])).

tff(c_1031,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_92,c_1029])).

tff(c_1032,plain,(
    ~ r1_xboole_0(k1_relat_1('#skF_8'),'#skF_7') ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_1033,plain,(
    k7_relat_1('#skF_8','#skF_7') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_1113,plain,(
    ! [B_194,A_195] :
      ( k3_xboole_0(k1_relat_1(B_194),A_195) = k1_relat_1(k7_relat_1(B_194,A_195))
      | ~ v1_relat_1(B_194) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_1047,plain,(
    ! [A_171,B_172] :
      ( r2_hidden('#skF_2'(A_171,B_172),A_171)
      | r1_xboole_0(A_171,B_172) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_1051,plain,(
    ! [A_171,B_172] :
      ( ~ v1_xboole_0(A_171)
      | r1_xboole_0(A_171,B_172) ) ),
    inference(resolution,[status(thm)],[c_1047,c_2])).

tff(c_1075,plain,(
    ! [A_179,B_180] :
      ( ~ r1_xboole_0(k3_xboole_0(A_179,B_180),B_180)
      | r1_xboole_0(A_179,B_180) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_1085,plain,(
    ! [A_179,B_172] :
      ( r1_xboole_0(A_179,B_172)
      | ~ v1_xboole_0(k3_xboole_0(A_179,B_172)) ) ),
    inference(resolution,[status(thm)],[c_1051,c_1075])).

tff(c_1145,plain,(
    ! [B_198,A_199] :
      ( r1_xboole_0(k1_relat_1(B_198),A_199)
      | ~ v1_xboole_0(k1_relat_1(k7_relat_1(B_198,A_199)))
      | ~ v1_relat_1(B_198) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1113,c_1085])).

tff(c_1151,plain,
    ( r1_xboole_0(k1_relat_1('#skF_8'),'#skF_7')
    | ~ v1_xboole_0(k1_relat_1(k1_xboole_0))
    | ~ v1_relat_1('#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_1033,c_1145])).

tff(c_1155,plain,
    ( r1_xboole_0(k1_relat_1('#skF_8'),'#skF_7')
    | ~ v1_xboole_0(k1_relat_1(k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_1151])).

tff(c_1156,plain,(
    ~ v1_xboole_0(k1_relat_1(k1_xboole_0)) ),
    inference(negUnitSimplification,[status(thm)],[c_1032,c_1155])).

tff(c_1324,plain,(
    ~ v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_1321,c_1156])).

tff(c_1340,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_1324])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:54:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.20/1.46  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.20/1.47  
% 3.20/1.47  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.20/1.47  %$ r2_hidden > r1_xboole_0 > v1_xboole_0 > v1_relat_1 > k2_enumset1 > k1_enumset1 > k7_relat_1 > k5_relat_1 > k4_tarski > k3_xboole_0 > k2_tarski > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_6 > #skF_1 > #skF_7 > #skF_3 > #skF_8 > #skF_2 > #skF_5 > #skF_4
% 3.20/1.47  
% 3.20/1.47  %Foreground sorts:
% 3.20/1.47  
% 3.20/1.47  
% 3.20/1.47  %Background operators:
% 3.20/1.47  
% 3.20/1.47  
% 3.20/1.47  %Foreground operators:
% 3.20/1.47  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.20/1.47  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.20/1.47  tff('#skF_6', type, '#skF_6': ($i * $i * $i) > $i).
% 3.20/1.47  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 3.20/1.47  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 3.20/1.47  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.20/1.47  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.20/1.47  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 3.20/1.47  tff('#skF_7', type, '#skF_7': $i).
% 3.20/1.47  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 3.20/1.47  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.20/1.47  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.20/1.47  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.20/1.47  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.20/1.47  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.20/1.47  tff('#skF_8', type, '#skF_8': $i).
% 3.20/1.47  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.20/1.47  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.20/1.47  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 3.20/1.47  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.20/1.47  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.20/1.47  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.20/1.47  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.20/1.47  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 3.20/1.47  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.20/1.47  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 3.20/1.47  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 3.20/1.47  
% 3.20/1.48  tff(f_32, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 3.20/1.48  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 3.20/1.48  tff(f_74, axiom, (![A, B]: ((B = k1_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(C, D), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_relat_1)).
% 3.20/1.48  tff(f_104, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => ((k7_relat_1(B, A) = k1_xboole_0) <=> r1_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t95_relat_1)).
% 3.20/1.48  tff(f_36, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 3.20/1.48  tff(f_76, axiom, (![A]: v1_relat_1(k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 3.20/1.48  tff(f_89, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 3.20/1.48  tff(f_85, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_xboole_0(k2_relat_1(A), k1_relat_1(B)) => (k5_relat_1(A, B) = k1_xboole_0)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t67_relat_1)).
% 3.20/1.48  tff(f_97, axiom, (![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k5_relat_1(k6_relat_1(A), B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t94_relat_1)).
% 3.20/1.48  tff(f_93, axiom, (![A, B]: (v1_relat_1(B) => (k1_relat_1(k7_relat_1(B, A)) = k3_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t90_relat_1)).
% 3.20/1.48  tff(f_54, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 3.20/1.48  tff(f_60, axiom, (![A, B]: ~(~r1_xboole_0(A, B) & r1_xboole_0(k3_xboole_0(A, B), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t75_xboole_1)).
% 3.20/1.48  tff(c_6, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.20/1.48  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.20/1.48  tff(c_1277, plain, (![C_214, A_215]: (r2_hidden(k4_tarski(C_214, '#skF_6'(A_215, k1_relat_1(A_215), C_214)), A_215) | ~r2_hidden(C_214, k1_relat_1(A_215)))), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.20/1.48  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.20/1.48  tff(c_1294, plain, (![A_216, C_217]: (~v1_xboole_0(A_216) | ~r2_hidden(C_217, k1_relat_1(A_216)))), inference(resolution, [status(thm)], [c_1277, c_2])).
% 3.20/1.48  tff(c_1321, plain, (![A_218]: (~v1_xboole_0(A_218) | v1_xboole_0(k1_relat_1(A_218)))), inference(resolution, [status(thm)], [c_4, c_1294])).
% 3.20/1.48  tff(c_50, plain, (~r1_xboole_0(k1_relat_1('#skF_8'), '#skF_7') | k7_relat_1('#skF_8', '#skF_7')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_104])).
% 3.20/1.48  tff(c_92, plain, (k7_relat_1('#skF_8', '#skF_7')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_50])).
% 3.20/1.48  tff(c_48, plain, (v1_relat_1('#skF_8')), inference(cnfTransformation, [status(thm)], [f_104])).
% 3.20/1.48  tff(c_56, plain, (k7_relat_1('#skF_8', '#skF_7')=k1_xboole_0 | r1_xboole_0(k1_relat_1('#skF_8'), '#skF_7')), inference(cnfTransformation, [status(thm)], [f_104])).
% 3.20/1.48  tff(c_115, plain, (r1_xboole_0(k1_relat_1('#skF_8'), '#skF_7')), inference(negUnitSimplification, [status(thm)], [c_92, c_56])).
% 3.20/1.48  tff(c_8, plain, (![B_6, A_5]: (r1_xboole_0(B_6, A_5) | ~r1_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.20/1.48  tff(c_118, plain, (r1_xboole_0('#skF_7', k1_relat_1('#skF_8'))), inference(resolution, [status(thm)], [c_115, c_8])).
% 3.20/1.48  tff(c_36, plain, (![A_40]: (v1_relat_1(k6_relat_1(A_40)))), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.20/1.48  tff(c_42, plain, (![A_44]: (k2_relat_1(k6_relat_1(A_44))=A_44)), inference(cnfTransformation, [status(thm)], [f_89])).
% 3.20/1.48  tff(c_258, plain, (![A_97, B_98]: (k5_relat_1(A_97, B_98)=k1_xboole_0 | ~r1_xboole_0(k2_relat_1(A_97), k1_relat_1(B_98)) | ~v1_relat_1(B_98) | ~v1_relat_1(A_97))), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.20/1.48  tff(c_273, plain, (![A_44, B_98]: (k5_relat_1(k6_relat_1(A_44), B_98)=k1_xboole_0 | ~r1_xboole_0(A_44, k1_relat_1(B_98)) | ~v1_relat_1(B_98) | ~v1_relat_1(k6_relat_1(A_44)))), inference(superposition, [status(thm), theory('equality')], [c_42, c_258])).
% 3.20/1.48  tff(c_951, plain, (![A_167, B_168]: (k5_relat_1(k6_relat_1(A_167), B_168)=k1_xboole_0 | ~r1_xboole_0(A_167, k1_relat_1(B_168)) | ~v1_relat_1(B_168))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_273])).
% 3.20/1.48  tff(c_988, plain, (k5_relat_1(k6_relat_1('#skF_7'), '#skF_8')=k1_xboole_0 | ~v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_118, c_951])).
% 3.20/1.48  tff(c_1012, plain, (k5_relat_1(k6_relat_1('#skF_7'), '#skF_8')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_48, c_988])).
% 3.20/1.48  tff(c_46, plain, (![A_47, B_48]: (k5_relat_1(k6_relat_1(A_47), B_48)=k7_relat_1(B_48, A_47) | ~v1_relat_1(B_48))), inference(cnfTransformation, [status(thm)], [f_97])).
% 3.20/1.48  tff(c_1022, plain, (k7_relat_1('#skF_8', '#skF_7')=k1_xboole_0 | ~v1_relat_1('#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_1012, c_46])).
% 3.20/1.48  tff(c_1029, plain, (k7_relat_1('#skF_8', '#skF_7')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_48, c_1022])).
% 3.20/1.48  tff(c_1031, plain, $false, inference(negUnitSimplification, [status(thm)], [c_92, c_1029])).
% 3.20/1.48  tff(c_1032, plain, (~r1_xboole_0(k1_relat_1('#skF_8'), '#skF_7')), inference(splitRight, [status(thm)], [c_50])).
% 3.20/1.48  tff(c_1033, plain, (k7_relat_1('#skF_8', '#skF_7')=k1_xboole_0), inference(splitRight, [status(thm)], [c_50])).
% 3.20/1.48  tff(c_1113, plain, (![B_194, A_195]: (k3_xboole_0(k1_relat_1(B_194), A_195)=k1_relat_1(k7_relat_1(B_194, A_195)) | ~v1_relat_1(B_194))), inference(cnfTransformation, [status(thm)], [f_93])).
% 3.20/1.48  tff(c_1047, plain, (![A_171, B_172]: (r2_hidden('#skF_2'(A_171, B_172), A_171) | r1_xboole_0(A_171, B_172))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.20/1.48  tff(c_1051, plain, (![A_171, B_172]: (~v1_xboole_0(A_171) | r1_xboole_0(A_171, B_172))), inference(resolution, [status(thm)], [c_1047, c_2])).
% 3.20/1.48  tff(c_1075, plain, (![A_179, B_180]: (~r1_xboole_0(k3_xboole_0(A_179, B_180), B_180) | r1_xboole_0(A_179, B_180))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.20/1.48  tff(c_1085, plain, (![A_179, B_172]: (r1_xboole_0(A_179, B_172) | ~v1_xboole_0(k3_xboole_0(A_179, B_172)))), inference(resolution, [status(thm)], [c_1051, c_1075])).
% 3.20/1.48  tff(c_1145, plain, (![B_198, A_199]: (r1_xboole_0(k1_relat_1(B_198), A_199) | ~v1_xboole_0(k1_relat_1(k7_relat_1(B_198, A_199))) | ~v1_relat_1(B_198))), inference(superposition, [status(thm), theory('equality')], [c_1113, c_1085])).
% 3.20/1.48  tff(c_1151, plain, (r1_xboole_0(k1_relat_1('#skF_8'), '#skF_7') | ~v1_xboole_0(k1_relat_1(k1_xboole_0)) | ~v1_relat_1('#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_1033, c_1145])).
% 3.20/1.48  tff(c_1155, plain, (r1_xboole_0(k1_relat_1('#skF_8'), '#skF_7') | ~v1_xboole_0(k1_relat_1(k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_1151])).
% 3.20/1.48  tff(c_1156, plain, (~v1_xboole_0(k1_relat_1(k1_xboole_0))), inference(negUnitSimplification, [status(thm)], [c_1032, c_1155])).
% 3.20/1.48  tff(c_1324, plain, (~v1_xboole_0(k1_xboole_0)), inference(resolution, [status(thm)], [c_1321, c_1156])).
% 3.20/1.48  tff(c_1340, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_1324])).
% 3.20/1.48  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.20/1.48  
% 3.20/1.48  Inference rules
% 3.20/1.48  ----------------------
% 3.20/1.48  #Ref     : 0
% 3.20/1.48  #Sup     : 286
% 3.20/1.48  #Fact    : 0
% 3.20/1.48  #Define  : 0
% 3.20/1.48  #Split   : 2
% 3.20/1.48  #Chain   : 0
% 3.20/1.48  #Close   : 0
% 3.20/1.48  
% 3.20/1.48  Ordering : KBO
% 3.20/1.48  
% 3.20/1.48  Simplification rules
% 3.20/1.48  ----------------------
% 3.20/1.48  #Subsume      : 59
% 3.20/1.48  #Demod        : 81
% 3.20/1.48  #Tautology    : 61
% 3.20/1.48  #SimpNegUnit  : 5
% 3.20/1.48  #BackRed      : 0
% 3.20/1.48  
% 3.20/1.48  #Partial instantiations: 0
% 3.20/1.48  #Strategies tried      : 1
% 3.20/1.48  
% 3.20/1.48  Timing (in seconds)
% 3.20/1.48  ----------------------
% 3.29/1.49  Preprocessing        : 0.32
% 3.29/1.49  Parsing              : 0.16
% 3.29/1.49  CNF conversion       : 0.02
% 3.29/1.49  Main loop            : 0.40
% 3.29/1.49  Inferencing          : 0.16
% 3.29/1.49  Reduction            : 0.11
% 3.29/1.49  Demodulation         : 0.07
% 3.29/1.49  BG Simplification    : 0.02
% 3.29/1.49  Subsumption          : 0.08
% 3.29/1.49  Abstraction          : 0.02
% 3.29/1.49  MUC search           : 0.00
% 3.29/1.49  Cooper               : 0.00
% 3.29/1.49  Total                : 0.75
% 3.29/1.49  Index Insertion      : 0.00
% 3.29/1.49  Index Deletion       : 0.00
% 3.29/1.49  Index Matching       : 0.00
% 3.29/1.49  BG Taut test         : 0.00
%------------------------------------------------------------------------------
