%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:01:18 EST 2020

% Result     : Theorem 3.09s
% Output     : CNFRefutation 3.42s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 768 expanded)
%              Number of leaves         :   33 ( 269 expanded)
%              Depth                    :   14
%              Number of atoms          :   96 (1641 expanded)
%              Number of equality atoms :   39 ( 291 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_tarski > k3_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k2_relat_1 > k1_tarski > k1_setfam_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_6 > #skF_5 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

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

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_103,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => k10_relat_1(A,k1_xboole_0) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t171_relat_1)).

tff(f_52,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & r2_hidden(C,B) ) )
      & ~ ( ? [C] :
              ( r2_hidden(C,A)
              & r2_hidden(C,B) )
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

tff(f_34,axiom,(
    ! [A,B,C] :
      ( C = k3_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

tff(f_54,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_71,axiom,(
    ! [A,B] :
      ~ ( r1_xboole_0(k1_tarski(A),B)
        & r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l24_zfmisc_1)).

tff(f_85,axiom,(
    ! [A,B] :
      ~ ( A != k1_tarski(B)
        & A != k1_xboole_0
        & ! [C] :
            ~ ( r2_hidden(C,A)
              & C != B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_zfmisc_1)).

tff(f_98,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k10_relat_1(C,B))
      <=> ? [D] :
            ( r2_hidden(D,k2_relat_1(C))
            & r2_hidden(k4_tarski(A,D),C)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t166_relat_1)).

tff(c_56,plain,(
    k10_relat_1('#skF_6',k1_xboole_0) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_58,plain,(
    v1_relat_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_24,plain,(
    ! [A_7,B_8] :
      ( r2_hidden('#skF_3'(A_7,B_8),A_7)
      | r1_xboole_0(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_86,plain,(
    ! [A_64,B_65] :
      ( r2_hidden('#skF_3'(A_64,B_65),B_65)
      | r1_xboole_0(A_64,B_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_6,plain,(
    ! [D_6,A_1,B_2] :
      ( r2_hidden(D_6,A_1)
      | ~ r2_hidden(D_6,k3_xboole_0(A_1,B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_173,plain,(
    ! [A_89,A_90,B_91] :
      ( r2_hidden('#skF_3'(A_89,k3_xboole_0(A_90,B_91)),A_90)
      | r1_xboole_0(A_89,k3_xboole_0(A_90,B_91)) ) ),
    inference(resolution,[status(thm)],[c_86,c_6])).

tff(c_26,plain,(
    ! [A_12] : r1_xboole_0(A_12,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_69,plain,(
    ! [A_56,B_57] :
      ( ~ r2_hidden(A_56,B_57)
      | ~ r1_xboole_0(k1_tarski(A_56),B_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_74,plain,(
    ! [A_56] : ~ r2_hidden(A_56,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_26,c_69])).

tff(c_198,plain,(
    ! [A_97,B_98] : r1_xboole_0(A_97,k3_xboole_0(k1_xboole_0,B_98)) ),
    inference(resolution,[status(thm)],[c_173,c_74])).

tff(c_40,plain,(
    ! [A_40,B_41] :
      ( ~ r2_hidden(A_40,B_41)
      | ~ r1_xboole_0(k1_tarski(A_40),B_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_207,plain,(
    ! [A_99,B_100] : ~ r2_hidden(A_99,k3_xboole_0(k1_xboole_0,B_100)) ),
    inference(resolution,[status(thm)],[c_198,c_40])).

tff(c_231,plain,(
    ! [B_100,B_8] : r1_xboole_0(k3_xboole_0(k1_xboole_0,B_100),B_8) ),
    inference(resolution,[status(thm)],[c_24,c_207])).

tff(c_44,plain,(
    ! [A_42,B_43] :
      ( r2_hidden('#skF_4'(A_42,B_43),A_42)
      | k1_xboole_0 = A_42
      | k1_tarski(B_43) = A_42 ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_357,plain,(
    ! [B_127,B_128] :
      ( k3_xboole_0(k1_xboole_0,B_127) = k1_xboole_0
      | k3_xboole_0(k1_xboole_0,B_127) = k1_tarski(B_128) ) ),
    inference(resolution,[status(thm)],[c_44,c_207])).

tff(c_389,plain,(
    ! [B_128,B_41,B_127] :
      ( ~ r2_hidden(B_128,B_41)
      | ~ r1_xboole_0(k3_xboole_0(k1_xboole_0,B_127),B_41)
      | k3_xboole_0(k1_xboole_0,B_127) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_357,c_40])).

tff(c_399,plain,(
    ! [B_128,B_41,B_127] :
      ( ~ r2_hidden(B_128,B_41)
      | k3_xboole_0(k1_xboole_0,B_127) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_231,c_389])).

tff(c_413,plain,(
    ! [B_128,B_41] : ~ r2_hidden(B_128,B_41) ),
    inference(splitLeft,[status(thm)],[c_399])).

tff(c_16,plain,(
    ! [A_1,B_2,C_3] :
      ( r2_hidden('#skF_1'(A_1,B_2,C_3),B_2)
      | r2_hidden('#skF_2'(A_1,B_2,C_3),C_3)
      | k3_xboole_0(A_1,B_2) = C_3 ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_710,plain,(
    ! [A_954,B_955] : k3_xboole_0(A_954,B_955) = '#skF_6' ),
    inference(negUnitSimplification,[status(thm)],[c_413,c_413,c_16])).

tff(c_654,plain,(
    ! [A_1,B_2,C_3] : k3_xboole_0(A_1,B_2) = C_3 ),
    inference(negUnitSimplification,[status(thm)],[c_413,c_413,c_16])).

tff(c_712,plain,(
    ! [C_3] : C_3 = '#skF_6' ),
    inference(superposition,[status(thm),theory(equality)],[c_710,c_654])).

tff(c_458,plain,(
    ! [B_141] :
      ( k1_xboole_0 = '#skF_6'
      | k1_tarski(B_141) = '#skF_6' ) ),
    inference(negUnitSimplification,[status(thm)],[c_413,c_44])).

tff(c_418,plain,(
    ! [A_42,B_43] :
      ( k1_xboole_0 = A_42
      | k1_tarski(B_43) = A_42 ) ),
    inference(negUnitSimplification,[status(thm)],[c_413,c_44])).

tff(c_460,plain,(
    ! [A_42] :
      ( k1_xboole_0 = A_42
      | A_42 = '#skF_6'
      | k1_xboole_0 = '#skF_6' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_458,c_418])).

tff(c_653,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_460])).

tff(c_839,plain,(
    k10_relat_1('#skF_6','#skF_6') != '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_653,c_653,c_56])).

tff(c_885,plain,(
    $false ),
    inference(superposition,[status(thm),theory(equality)],[c_712,c_839])).

tff(c_887,plain,(
    k1_xboole_0 != '#skF_6' ),
    inference(splitRight,[status(thm)],[c_460])).

tff(c_985,plain,(
    ! [A_4552,B_4553] : k3_xboole_0(A_4552,B_4553) = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_413,c_413,c_16])).

tff(c_973,plain,(
    ! [A_1,B_2,C_3] : k3_xboole_0(A_1,B_2) = C_3 ),
    inference(negUnitSimplification,[status(thm)],[c_413,c_413,c_16])).

tff(c_1154,plain,(
    ! [C_5410] : k1_xboole_0 = C_5410 ),
    inference(superposition,[status(thm),theory(equality)],[c_985,c_973])).

tff(c_894,plain,(
    ! [A_3524] :
      ( k1_xboole_0 = A_3524
      | A_3524 = '#skF_6' ) ),
    inference(splitRight,[status(thm)],[c_460])).

tff(c_942,plain,(
    k10_relat_1('#skF_6',k1_xboole_0) = '#skF_6' ),
    inference(superposition,[status(thm),theory(equality)],[c_894,c_56])).

tff(c_1161,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(superposition,[status(thm),theory(equality)],[c_1154,c_942])).

tff(c_1182,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_887,c_1161])).

tff(c_1183,plain,(
    ! [B_127] : k3_xboole_0(k1_xboole_0,B_127) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_399])).

tff(c_1244,plain,(
    ! [A_6270,B_6271,C_6272] :
      ( r2_hidden('#skF_1'(A_6270,B_6271,C_6272),A_6270)
      | r2_hidden('#skF_2'(A_6270,B_6271,C_6272),C_6272)
      | k3_xboole_0(A_6270,B_6271) = C_6272 ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_1260,plain,(
    ! [B_6271,C_6272] :
      ( r2_hidden('#skF_2'(k1_xboole_0,B_6271,C_6272),C_6272)
      | k3_xboole_0(k1_xboole_0,B_6271) = C_6272 ) ),
    inference(resolution,[status(thm)],[c_1244,c_74])).

tff(c_1283,plain,(
    ! [B_6273,C_6274] :
      ( r2_hidden('#skF_2'(k1_xboole_0,B_6273,C_6274),C_6274)
      | k1_xboole_0 = C_6274 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1183,c_1260])).

tff(c_274,plain,(
    ! [A_109,B_110,C_111] :
      ( r2_hidden('#skF_5'(A_109,B_110,C_111),B_110)
      | ~ r2_hidden(A_109,k10_relat_1(C_111,B_110))
      | ~ v1_relat_1(C_111) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_299,plain,(
    ! [A_109,C_111] :
      ( ~ r2_hidden(A_109,k10_relat_1(C_111,k1_xboole_0))
      | ~ v1_relat_1(C_111) ) ),
    inference(resolution,[status(thm)],[c_274,c_74])).

tff(c_1305,plain,(
    ! [C_6275] :
      ( ~ v1_relat_1(C_6275)
      | k10_relat_1(C_6275,k1_xboole_0) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_1283,c_299])).

tff(c_1308,plain,(
    k10_relat_1('#skF_6',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_58,c_1305])).

tff(c_1312,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_1308])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:53:30 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.09/1.54  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.42/1.55  
% 3.42/1.55  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.42/1.55  %$ r2_hidden > r1_xboole_0 > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_tarski > k3_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k2_relat_1 > k1_tarski > k1_setfam_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_6 > #skF_5 > #skF_2 > #skF_4
% 3.42/1.55  
% 3.42/1.55  %Foreground sorts:
% 3.42/1.55  
% 3.42/1.55  
% 3.42/1.55  %Background operators:
% 3.42/1.55  
% 3.42/1.55  
% 3.42/1.55  %Foreground operators:
% 3.42/1.55  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 3.42/1.55  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.42/1.55  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.42/1.55  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.42/1.55  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 3.42/1.55  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.42/1.55  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.42/1.55  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 3.42/1.55  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.42/1.55  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.42/1.55  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.42/1.55  tff('#skF_6', type, '#skF_6': $i).
% 3.42/1.55  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 3.42/1.55  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.42/1.55  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.42/1.55  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 3.42/1.55  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.42/1.55  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.42/1.55  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.42/1.55  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 3.42/1.55  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.42/1.55  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.42/1.55  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.42/1.55  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.42/1.55  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 3.42/1.55  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 3.42/1.55  
% 3.42/1.56  tff(f_103, negated_conjecture, ~(![A]: (v1_relat_1(A) => (k10_relat_1(A, k1_xboole_0) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t171_relat_1)).
% 3.42/1.56  tff(f_52, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 3.42/1.56  tff(f_34, axiom, (![A, B, C]: ((C = k3_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_xboole_0)).
% 3.42/1.56  tff(f_54, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 3.42/1.56  tff(f_71, axiom, (![A, B]: ~(r1_xboole_0(k1_tarski(A), B) & r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l24_zfmisc_1)).
% 3.42/1.56  tff(f_85, axiom, (![A, B]: ~((~(A = k1_tarski(B)) & ~(A = k1_xboole_0)) & (![C]: ~(r2_hidden(C, A) & ~(C = B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_zfmisc_1)).
% 3.42/1.56  tff(f_98, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k10_relat_1(C, B)) <=> (?[D]: ((r2_hidden(D, k2_relat_1(C)) & r2_hidden(k4_tarski(A, D), C)) & r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t166_relat_1)).
% 3.42/1.56  tff(c_56, plain, (k10_relat_1('#skF_6', k1_xboole_0)!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_103])).
% 3.42/1.56  tff(c_58, plain, (v1_relat_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_103])).
% 3.42/1.56  tff(c_24, plain, (![A_7, B_8]: (r2_hidden('#skF_3'(A_7, B_8), A_7) | r1_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.42/1.56  tff(c_86, plain, (![A_64, B_65]: (r2_hidden('#skF_3'(A_64, B_65), B_65) | r1_xboole_0(A_64, B_65))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.42/1.56  tff(c_6, plain, (![D_6, A_1, B_2]: (r2_hidden(D_6, A_1) | ~r2_hidden(D_6, k3_xboole_0(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.42/1.56  tff(c_173, plain, (![A_89, A_90, B_91]: (r2_hidden('#skF_3'(A_89, k3_xboole_0(A_90, B_91)), A_90) | r1_xboole_0(A_89, k3_xboole_0(A_90, B_91)))), inference(resolution, [status(thm)], [c_86, c_6])).
% 3.42/1.56  tff(c_26, plain, (![A_12]: (r1_xboole_0(A_12, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.42/1.56  tff(c_69, plain, (![A_56, B_57]: (~r2_hidden(A_56, B_57) | ~r1_xboole_0(k1_tarski(A_56), B_57))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.42/1.56  tff(c_74, plain, (![A_56]: (~r2_hidden(A_56, k1_xboole_0))), inference(resolution, [status(thm)], [c_26, c_69])).
% 3.42/1.56  tff(c_198, plain, (![A_97, B_98]: (r1_xboole_0(A_97, k3_xboole_0(k1_xboole_0, B_98)))), inference(resolution, [status(thm)], [c_173, c_74])).
% 3.42/1.56  tff(c_40, plain, (![A_40, B_41]: (~r2_hidden(A_40, B_41) | ~r1_xboole_0(k1_tarski(A_40), B_41))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.42/1.56  tff(c_207, plain, (![A_99, B_100]: (~r2_hidden(A_99, k3_xboole_0(k1_xboole_0, B_100)))), inference(resolution, [status(thm)], [c_198, c_40])).
% 3.42/1.56  tff(c_231, plain, (![B_100, B_8]: (r1_xboole_0(k3_xboole_0(k1_xboole_0, B_100), B_8))), inference(resolution, [status(thm)], [c_24, c_207])).
% 3.42/1.56  tff(c_44, plain, (![A_42, B_43]: (r2_hidden('#skF_4'(A_42, B_43), A_42) | k1_xboole_0=A_42 | k1_tarski(B_43)=A_42)), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.42/1.56  tff(c_357, plain, (![B_127, B_128]: (k3_xboole_0(k1_xboole_0, B_127)=k1_xboole_0 | k3_xboole_0(k1_xboole_0, B_127)=k1_tarski(B_128))), inference(resolution, [status(thm)], [c_44, c_207])).
% 3.42/1.56  tff(c_389, plain, (![B_128, B_41, B_127]: (~r2_hidden(B_128, B_41) | ~r1_xboole_0(k3_xboole_0(k1_xboole_0, B_127), B_41) | k3_xboole_0(k1_xboole_0, B_127)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_357, c_40])).
% 3.42/1.56  tff(c_399, plain, (![B_128, B_41, B_127]: (~r2_hidden(B_128, B_41) | k3_xboole_0(k1_xboole_0, B_127)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_231, c_389])).
% 3.42/1.56  tff(c_413, plain, (![B_128, B_41]: (~r2_hidden(B_128, B_41))), inference(splitLeft, [status(thm)], [c_399])).
% 3.42/1.56  tff(c_16, plain, (![A_1, B_2, C_3]: (r2_hidden('#skF_1'(A_1, B_2, C_3), B_2) | r2_hidden('#skF_2'(A_1, B_2, C_3), C_3) | k3_xboole_0(A_1, B_2)=C_3)), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.42/1.56  tff(c_710, plain, (![A_954, B_955]: (k3_xboole_0(A_954, B_955)='#skF_6')), inference(negUnitSimplification, [status(thm)], [c_413, c_413, c_16])).
% 3.42/1.56  tff(c_654, plain, (![A_1, B_2, C_3]: (k3_xboole_0(A_1, B_2)=C_3)), inference(negUnitSimplification, [status(thm)], [c_413, c_413, c_16])).
% 3.42/1.56  tff(c_712, plain, (![C_3]: (C_3='#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_710, c_654])).
% 3.42/1.56  tff(c_458, plain, (![B_141]: (k1_xboole_0='#skF_6' | k1_tarski(B_141)='#skF_6')), inference(negUnitSimplification, [status(thm)], [c_413, c_44])).
% 3.42/1.56  tff(c_418, plain, (![A_42, B_43]: (k1_xboole_0=A_42 | k1_tarski(B_43)=A_42)), inference(negUnitSimplification, [status(thm)], [c_413, c_44])).
% 3.42/1.56  tff(c_460, plain, (![A_42]: (k1_xboole_0=A_42 | A_42='#skF_6' | k1_xboole_0='#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_458, c_418])).
% 3.42/1.56  tff(c_653, plain, (k1_xboole_0='#skF_6'), inference(splitLeft, [status(thm)], [c_460])).
% 3.42/1.56  tff(c_839, plain, (k10_relat_1('#skF_6', '#skF_6')!='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_653, c_653, c_56])).
% 3.42/1.56  tff(c_885, plain, $false, inference(superposition, [status(thm), theory('equality')], [c_712, c_839])).
% 3.42/1.56  tff(c_887, plain, (k1_xboole_0!='#skF_6'), inference(splitRight, [status(thm)], [c_460])).
% 3.42/1.56  tff(c_985, plain, (![A_4552, B_4553]: (k3_xboole_0(A_4552, B_4553)=k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_413, c_413, c_16])).
% 3.42/1.56  tff(c_973, plain, (![A_1, B_2, C_3]: (k3_xboole_0(A_1, B_2)=C_3)), inference(negUnitSimplification, [status(thm)], [c_413, c_413, c_16])).
% 3.42/1.56  tff(c_1154, plain, (![C_5410]: (k1_xboole_0=C_5410)), inference(superposition, [status(thm), theory('equality')], [c_985, c_973])).
% 3.42/1.56  tff(c_894, plain, (![A_3524]: (k1_xboole_0=A_3524 | A_3524='#skF_6')), inference(splitRight, [status(thm)], [c_460])).
% 3.42/1.56  tff(c_942, plain, (k10_relat_1('#skF_6', k1_xboole_0)='#skF_6'), inference(superposition, [status(thm), theory('equality')], [c_894, c_56])).
% 3.42/1.56  tff(c_1161, plain, (k1_xboole_0='#skF_6'), inference(superposition, [status(thm), theory('equality')], [c_1154, c_942])).
% 3.42/1.56  tff(c_1182, plain, $false, inference(negUnitSimplification, [status(thm)], [c_887, c_1161])).
% 3.42/1.56  tff(c_1183, plain, (![B_127]: (k3_xboole_0(k1_xboole_0, B_127)=k1_xboole_0)), inference(splitRight, [status(thm)], [c_399])).
% 3.42/1.56  tff(c_1244, plain, (![A_6270, B_6271, C_6272]: (r2_hidden('#skF_1'(A_6270, B_6271, C_6272), A_6270) | r2_hidden('#skF_2'(A_6270, B_6271, C_6272), C_6272) | k3_xboole_0(A_6270, B_6271)=C_6272)), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.42/1.56  tff(c_1260, plain, (![B_6271, C_6272]: (r2_hidden('#skF_2'(k1_xboole_0, B_6271, C_6272), C_6272) | k3_xboole_0(k1_xboole_0, B_6271)=C_6272)), inference(resolution, [status(thm)], [c_1244, c_74])).
% 3.42/1.56  tff(c_1283, plain, (![B_6273, C_6274]: (r2_hidden('#skF_2'(k1_xboole_0, B_6273, C_6274), C_6274) | k1_xboole_0=C_6274)), inference(demodulation, [status(thm), theory('equality')], [c_1183, c_1260])).
% 3.42/1.56  tff(c_274, plain, (![A_109, B_110, C_111]: (r2_hidden('#skF_5'(A_109, B_110, C_111), B_110) | ~r2_hidden(A_109, k10_relat_1(C_111, B_110)) | ~v1_relat_1(C_111))), inference(cnfTransformation, [status(thm)], [f_98])).
% 3.42/1.56  tff(c_299, plain, (![A_109, C_111]: (~r2_hidden(A_109, k10_relat_1(C_111, k1_xboole_0)) | ~v1_relat_1(C_111))), inference(resolution, [status(thm)], [c_274, c_74])).
% 3.42/1.56  tff(c_1305, plain, (![C_6275]: (~v1_relat_1(C_6275) | k10_relat_1(C_6275, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_1283, c_299])).
% 3.42/1.56  tff(c_1308, plain, (k10_relat_1('#skF_6', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_58, c_1305])).
% 3.42/1.56  tff(c_1312, plain, $false, inference(negUnitSimplification, [status(thm)], [c_56, c_1308])).
% 3.42/1.56  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.42/1.56  
% 3.42/1.56  Inference rules
% 3.42/1.56  ----------------------
% 3.42/1.56  #Ref     : 0
% 3.42/1.56  #Sup     : 303
% 3.42/1.56  #Fact    : 3
% 3.42/1.56  #Define  : 0
% 3.42/1.56  #Split   : 4
% 3.42/1.56  #Chain   : 0
% 3.42/1.56  #Close   : 0
% 3.42/1.56  
% 3.42/1.56  Ordering : KBO
% 3.42/1.56  
% 3.42/1.56  Simplification rules
% 3.42/1.56  ----------------------
% 3.42/1.56  #Subsume      : 94
% 3.42/1.56  #Demod        : 59
% 3.42/1.56  #Tautology    : 59
% 3.42/1.56  #SimpNegUnit  : 28
% 3.42/1.56  #BackRed      : 16
% 3.42/1.56  
% 3.42/1.56  #Partial instantiations: 1005
% 3.42/1.56  #Strategies tried      : 1
% 3.42/1.56  
% 3.42/1.56  Timing (in seconds)
% 3.42/1.56  ----------------------
% 3.42/1.57  Preprocessing        : 0.35
% 3.42/1.57  Parsing              : 0.17
% 3.42/1.57  CNF conversion       : 0.03
% 3.42/1.57  Main loop            : 0.45
% 3.42/1.57  Inferencing          : 0.22
% 3.42/1.57  Reduction            : 0.10
% 3.42/1.57  Demodulation         : 0.07
% 3.42/1.57  BG Simplification    : 0.03
% 3.42/1.57  Subsumption          : 0.07
% 3.42/1.57  Abstraction          : 0.03
% 3.42/1.57  MUC search           : 0.00
% 3.42/1.57  Cooper               : 0.00
% 3.42/1.57  Total                : 0.83
% 3.42/1.57  Index Insertion      : 0.00
% 3.42/1.57  Index Deletion       : 0.00
% 3.42/1.57  Index Matching       : 0.00
% 3.42/1.57  BG Taut test         : 0.00
%------------------------------------------------------------------------------
