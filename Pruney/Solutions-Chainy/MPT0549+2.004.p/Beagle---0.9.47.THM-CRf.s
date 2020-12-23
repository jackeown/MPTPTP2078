%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:00:48 EST 2020

% Result     : Theorem 3.69s
% Output     : CNFRefutation 3.69s
% Verified   : 
% Statistics : Number of formulae       :   93 ( 154 expanded)
%              Number of leaves         :   40 (  68 expanded)
%              Depth                    :    8
%              Number of atoms          :  120 ( 248 expanded)
%              Number of equality atoms :   32 (  64 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k2_zfmisc_1 > k2_tarski > #nlpp > k3_tarski > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

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

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_117,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ( k9_relat_1(B,A) = k1_xboole_0
        <=> r1_xboole_0(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t151_relat_1)).

tff(f_110,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( k7_relat_1(B,A) = k1_xboole_0
      <=> r1_xboole_0(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_relat_1)).

tff(f_96,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_xboole_0(k2_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc11_relat_1)).

tff(f_35,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_45,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_81,axiom,(
    ! [A,B,C] :
      ~ ( r1_xboole_0(k2_tarski(A,B),C)
        & r2_hidden(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_zfmisc_1)).

tff(f_100,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_92,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k7_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).

tff(f_75,axiom,(
    ! [A,B,C,D] :
      ( ( r1_xboole_0(A,B)
        | r1_xboole_0(C,D) )
     => r1_xboole_0(k2_zfmisc_1(A,C),k2_zfmisc_1(B,D)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t127_zfmisc_1)).

tff(f_57,axiom,(
    ! [A] :
      ( ~ ( ~ r1_xboole_0(A,A)
          & A = k1_xboole_0 )
      & ~ ( A != k1_xboole_0
          & r1_xboole_0(A,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_xboole_1)).

tff(f_104,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => r1_tarski(A,k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_relat_1)).

tff(f_43,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(c_58,plain,(
    v1_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_844,plain,(
    ! [B_171,A_172] :
      ( r1_xboole_0(k1_relat_1(B_171),A_172)
      | k7_relat_1(B_171,A_172) != k1_xboole_0
      | ~ v1_relat_1(B_171) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_60,plain,
    ( ~ r1_xboole_0(k1_relat_1('#skF_4'),'#skF_3')
    | k9_relat_1('#skF_4','#skF_3') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_90,plain,(
    k9_relat_1('#skF_4','#skF_3') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_60])).

tff(c_48,plain,(
    ! [A_50] :
      ( v1_xboole_0(k2_relat_1(A_50))
      | ~ v1_xboole_0(A_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_85,plain,(
    ! [A_63] :
      ( v1_xboole_0(k2_relat_1(A_63))
      | ~ v1_xboole_0(A_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_6,plain,(
    ! [A_5] :
      ( k1_xboole_0 = A_5
      | ~ v1_xboole_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_91,plain,(
    ! [A_64] :
      ( k2_relat_1(A_64) = k1_xboole_0
      | ~ v1_xboole_0(A_64) ) ),
    inference(resolution,[status(thm)],[c_85,c_6])).

tff(c_102,plain,(
    ! [A_68] :
      ( k2_relat_1(k2_relat_1(A_68)) = k1_xboole_0
      | ~ v1_xboole_0(A_68) ) ),
    inference(resolution,[status(thm)],[c_48,c_91])).

tff(c_111,plain,(
    ! [A_68] :
      ( v1_xboole_0(k1_xboole_0)
      | ~ v1_xboole_0(k2_relat_1(A_68))
      | ~ v1_xboole_0(A_68) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_102,c_48])).

tff(c_130,plain,(
    ! [A_71] :
      ( ~ v1_xboole_0(k2_relat_1(A_71))
      | ~ v1_xboole_0(A_71) ) ),
    inference(splitLeft,[status(thm)],[c_111])).

tff(c_137,plain,(
    ! [A_50] : ~ v1_xboole_0(A_50) ),
    inference(resolution,[status(thm)],[c_48,c_130])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_138,plain,(
    ! [A_1] : r2_hidden('#skF_1'(A_1),A_1) ),
    inference(negUnitSimplification,[status(thm)],[c_137,c_4])).

tff(c_16,plain,(
    ! [A_9] : r1_xboole_0(A_9,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_166,plain,(
    ! [A_77,C_78,B_79] :
      ( ~ r2_hidden(A_77,C_78)
      | ~ r1_xboole_0(k2_tarski(A_77,B_79),C_78) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_172,plain,(
    ! [A_80] : ~ r2_hidden(A_80,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_16,c_166])).

tff(c_177,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_138,c_172])).

tff(c_178,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_111])).

tff(c_89,plain,(
    ! [A_63] :
      ( k2_relat_1(A_63) = k1_xboole_0
      | ~ v1_xboole_0(A_63) ) ),
    inference(resolution,[status(thm)],[c_85,c_6])).

tff(c_186,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_178,c_89])).

tff(c_66,plain,
    ( k9_relat_1('#skF_4','#skF_3') = k1_xboole_0
    | r1_xboole_0(k1_relat_1('#skF_4'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_179,plain,(
    r1_xboole_0(k1_relat_1('#skF_4'),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_90,c_66])).

tff(c_429,plain,(
    ! [B_116,A_117] :
      ( k7_relat_1(B_116,A_117) = k1_xboole_0
      | ~ r1_xboole_0(k1_relat_1(B_116),A_117)
      | ~ v1_relat_1(B_116) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_432,plain,
    ( k7_relat_1('#skF_4','#skF_3') = k1_xboole_0
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_179,c_429])).

tff(c_439,plain,(
    k7_relat_1('#skF_4','#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_432])).

tff(c_50,plain,(
    ! [B_52,A_51] :
      ( k2_relat_1(k7_relat_1(B_52,A_51)) = k9_relat_1(B_52,A_51)
      | ~ v1_relat_1(B_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_444,plain,
    ( k9_relat_1('#skF_4','#skF_3') = k2_relat_1(k1_xboole_0)
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_439,c_50])).

tff(c_451,plain,(
    k9_relat_1('#skF_4','#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_186,c_444])).

tff(c_453,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_90,c_451])).

tff(c_454,plain,(
    ~ r1_xboole_0(k1_relat_1('#skF_4'),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_60])).

tff(c_856,plain,
    ( k7_relat_1('#skF_4','#skF_3') != k1_xboole_0
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_844,c_454])).

tff(c_866,plain,(
    k7_relat_1('#skF_4','#skF_3') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_856])).

tff(c_46,plain,(
    ! [A_48,B_49] :
      ( v1_relat_1(k7_relat_1(A_48,B_49))
      | ~ v1_relat_1(A_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_720,plain,(
    ! [C_160,D_161,A_162,B_163] :
      ( ~ r1_xboole_0(C_160,D_161)
      | r1_xboole_0(k2_zfmisc_1(A_162,C_160),k2_zfmisc_1(B_163,D_161)) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_20,plain,(
    ! [A_10] :
      ( ~ r1_xboole_0(A_10,A_10)
      | k1_xboole_0 = A_10 ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_756,plain,(
    ! [B_165,D_166] :
      ( k2_zfmisc_1(B_165,D_166) = k1_xboole_0
      | ~ r1_xboole_0(D_166,D_166) ) ),
    inference(resolution,[status(thm)],[c_720,c_20])).

tff(c_776,plain,(
    ! [B_165] : k2_zfmisc_1(B_165,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_16,c_756])).

tff(c_455,plain,(
    k9_relat_1('#skF_4','#skF_3') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_60])).

tff(c_633,plain,(
    ! [B_148,A_149] :
      ( k2_relat_1(k7_relat_1(B_148,A_149)) = k9_relat_1(B_148,A_149)
      | ~ v1_relat_1(B_148) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_52,plain,(
    ! [A_53] :
      ( r1_tarski(A_53,k2_zfmisc_1(k1_relat_1(A_53),k2_relat_1(A_53)))
      | ~ v1_relat_1(A_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_2456,plain,(
    ! [B_283,A_284] :
      ( r1_tarski(k7_relat_1(B_283,A_284),k2_zfmisc_1(k1_relat_1(k7_relat_1(B_283,A_284)),k9_relat_1(B_283,A_284)))
      | ~ v1_relat_1(k7_relat_1(B_283,A_284))
      | ~ v1_relat_1(B_283) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_633,c_52])).

tff(c_2485,plain,
    ( r1_tarski(k7_relat_1('#skF_4','#skF_3'),k2_zfmisc_1(k1_relat_1(k7_relat_1('#skF_4','#skF_3')),k1_xboole_0))
    | ~ v1_relat_1(k7_relat_1('#skF_4','#skF_3'))
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_455,c_2456])).

tff(c_2501,plain,
    ( r1_tarski(k7_relat_1('#skF_4','#skF_3'),k1_xboole_0)
    | ~ v1_relat_1(k7_relat_1('#skF_4','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_776,c_2485])).

tff(c_2502,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_4','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_2501])).

tff(c_2505,plain,(
    ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_46,c_2502])).

tff(c_2509,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_2505])).

tff(c_2510,plain,(
    r1_tarski(k7_relat_1('#skF_4','#skF_3'),k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_2501])).

tff(c_14,plain,(
    ! [A_8] : r1_tarski(k1_xboole_0,A_8) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_557,plain,(
    ! [B_135,A_136] :
      ( B_135 = A_136
      | ~ r1_tarski(B_135,A_136)
      | ~ r1_tarski(A_136,B_135) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_566,plain,(
    ! [A_8] :
      ( k1_xboole_0 = A_8
      | ~ r1_tarski(A_8,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_14,c_557])).

tff(c_2518,plain,(
    k7_relat_1('#skF_4','#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2510,c_566])).

tff(c_2524,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_866,c_2518])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.11  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.10/0.30  % Computer   : n003.cluster.edu
% 0.10/0.30  % Model      : x86_64 x86_64
% 0.10/0.30  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.10/0.30  % Memory     : 8042.1875MB
% 0.10/0.30  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.10/0.30  % CPULimit   : 60
% 0.10/0.30  % DateTime   : Tue Dec  1 14:12:12 EST 2020
% 0.10/0.30  % CPUTime    : 
% 0.10/0.31  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.69/1.58  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.69/1.59  
% 3.69/1.59  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.69/1.59  %$ r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k2_zfmisc_1 > k2_tarski > #nlpp > k3_tarski > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2
% 3.69/1.59  
% 3.69/1.59  %Foreground sorts:
% 3.69/1.59  
% 3.69/1.59  
% 3.69/1.59  %Background operators:
% 3.69/1.59  
% 3.69/1.59  
% 3.69/1.59  %Foreground operators:
% 3.69/1.59  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.69/1.59  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.69/1.59  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 3.69/1.59  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.69/1.59  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.69/1.59  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.69/1.59  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.69/1.59  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.69/1.59  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.69/1.59  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.69/1.59  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.69/1.59  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.69/1.59  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 3.69/1.59  tff('#skF_3', type, '#skF_3': $i).
% 3.69/1.59  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.69/1.59  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.69/1.59  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.69/1.59  tff(k3_tarski, type, k3_tarski: $i > $i).
% 3.69/1.59  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.69/1.59  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.69/1.59  tff('#skF_4', type, '#skF_4': $i).
% 3.69/1.59  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.69/1.59  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.69/1.59  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.69/1.59  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.69/1.59  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.69/1.59  
% 3.69/1.60  tff(f_117, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => ((k9_relat_1(B, A) = k1_xboole_0) <=> r1_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t151_relat_1)).
% 3.69/1.60  tff(f_110, axiom, (![A, B]: (v1_relat_1(B) => ((k7_relat_1(B, A) = k1_xboole_0) <=> r1_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t95_relat_1)).
% 3.69/1.60  tff(f_96, axiom, (![A]: (v1_xboole_0(A) => v1_xboole_0(k2_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc11_relat_1)).
% 3.69/1.60  tff(f_35, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 3.69/1.60  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 3.69/1.60  tff(f_45, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 3.69/1.60  tff(f_81, axiom, (![A, B, C]: ~(r1_xboole_0(k2_tarski(A, B), C) & r2_hidden(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_zfmisc_1)).
% 3.69/1.60  tff(f_100, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_relat_1)).
% 3.69/1.60  tff(f_92, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k7_relat_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 3.69/1.60  tff(f_75, axiom, (![A, B, C, D]: ((r1_xboole_0(A, B) | r1_xboole_0(C, D)) => r1_xboole_0(k2_zfmisc_1(A, C), k2_zfmisc_1(B, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t127_zfmisc_1)).
% 3.69/1.60  tff(f_57, axiom, (![A]: (~(~r1_xboole_0(A, A) & (A = k1_xboole_0)) & ~(~(A = k1_xboole_0) & r1_xboole_0(A, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t66_xboole_1)).
% 3.69/1.60  tff(f_104, axiom, (![A]: (v1_relat_1(A) => r1_tarski(A, k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t21_relat_1)).
% 3.69/1.60  tff(f_43, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 3.69/1.60  tff(f_41, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.69/1.60  tff(c_58, plain, (v1_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_117])).
% 3.69/1.60  tff(c_844, plain, (![B_171, A_172]: (r1_xboole_0(k1_relat_1(B_171), A_172) | k7_relat_1(B_171, A_172)!=k1_xboole_0 | ~v1_relat_1(B_171))), inference(cnfTransformation, [status(thm)], [f_110])).
% 3.69/1.60  tff(c_60, plain, (~r1_xboole_0(k1_relat_1('#skF_4'), '#skF_3') | k9_relat_1('#skF_4', '#skF_3')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_117])).
% 3.69/1.60  tff(c_90, plain, (k9_relat_1('#skF_4', '#skF_3')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_60])).
% 3.69/1.60  tff(c_48, plain, (![A_50]: (v1_xboole_0(k2_relat_1(A_50)) | ~v1_xboole_0(A_50))), inference(cnfTransformation, [status(thm)], [f_96])).
% 3.69/1.60  tff(c_85, plain, (![A_63]: (v1_xboole_0(k2_relat_1(A_63)) | ~v1_xboole_0(A_63))), inference(cnfTransformation, [status(thm)], [f_96])).
% 3.69/1.60  tff(c_6, plain, (![A_5]: (k1_xboole_0=A_5 | ~v1_xboole_0(A_5))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.69/1.60  tff(c_91, plain, (![A_64]: (k2_relat_1(A_64)=k1_xboole_0 | ~v1_xboole_0(A_64))), inference(resolution, [status(thm)], [c_85, c_6])).
% 3.69/1.60  tff(c_102, plain, (![A_68]: (k2_relat_1(k2_relat_1(A_68))=k1_xboole_0 | ~v1_xboole_0(A_68))), inference(resolution, [status(thm)], [c_48, c_91])).
% 3.69/1.60  tff(c_111, plain, (![A_68]: (v1_xboole_0(k1_xboole_0) | ~v1_xboole_0(k2_relat_1(A_68)) | ~v1_xboole_0(A_68))), inference(superposition, [status(thm), theory('equality')], [c_102, c_48])).
% 3.69/1.60  tff(c_130, plain, (![A_71]: (~v1_xboole_0(k2_relat_1(A_71)) | ~v1_xboole_0(A_71))), inference(splitLeft, [status(thm)], [c_111])).
% 3.69/1.60  tff(c_137, plain, (![A_50]: (~v1_xboole_0(A_50))), inference(resolution, [status(thm)], [c_48, c_130])).
% 3.69/1.60  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.69/1.60  tff(c_138, plain, (![A_1]: (r2_hidden('#skF_1'(A_1), A_1))), inference(negUnitSimplification, [status(thm)], [c_137, c_4])).
% 3.69/1.60  tff(c_16, plain, (![A_9]: (r1_xboole_0(A_9, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.69/1.60  tff(c_166, plain, (![A_77, C_78, B_79]: (~r2_hidden(A_77, C_78) | ~r1_xboole_0(k2_tarski(A_77, B_79), C_78))), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.69/1.60  tff(c_172, plain, (![A_80]: (~r2_hidden(A_80, k1_xboole_0))), inference(resolution, [status(thm)], [c_16, c_166])).
% 3.69/1.60  tff(c_177, plain, $false, inference(resolution, [status(thm)], [c_138, c_172])).
% 3.69/1.60  tff(c_178, plain, (v1_xboole_0(k1_xboole_0)), inference(splitRight, [status(thm)], [c_111])).
% 3.69/1.60  tff(c_89, plain, (![A_63]: (k2_relat_1(A_63)=k1_xboole_0 | ~v1_xboole_0(A_63))), inference(resolution, [status(thm)], [c_85, c_6])).
% 3.69/1.60  tff(c_186, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_178, c_89])).
% 3.69/1.60  tff(c_66, plain, (k9_relat_1('#skF_4', '#skF_3')=k1_xboole_0 | r1_xboole_0(k1_relat_1('#skF_4'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_117])).
% 3.69/1.60  tff(c_179, plain, (r1_xboole_0(k1_relat_1('#skF_4'), '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_90, c_66])).
% 3.69/1.60  tff(c_429, plain, (![B_116, A_117]: (k7_relat_1(B_116, A_117)=k1_xboole_0 | ~r1_xboole_0(k1_relat_1(B_116), A_117) | ~v1_relat_1(B_116))), inference(cnfTransformation, [status(thm)], [f_110])).
% 3.69/1.60  tff(c_432, plain, (k7_relat_1('#skF_4', '#skF_3')=k1_xboole_0 | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_179, c_429])).
% 3.69/1.60  tff(c_439, plain, (k7_relat_1('#skF_4', '#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_58, c_432])).
% 3.69/1.60  tff(c_50, plain, (![B_52, A_51]: (k2_relat_1(k7_relat_1(B_52, A_51))=k9_relat_1(B_52, A_51) | ~v1_relat_1(B_52))), inference(cnfTransformation, [status(thm)], [f_100])).
% 3.69/1.60  tff(c_444, plain, (k9_relat_1('#skF_4', '#skF_3')=k2_relat_1(k1_xboole_0) | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_439, c_50])).
% 3.69/1.60  tff(c_451, plain, (k9_relat_1('#skF_4', '#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_58, c_186, c_444])).
% 3.69/1.60  tff(c_453, plain, $false, inference(negUnitSimplification, [status(thm)], [c_90, c_451])).
% 3.69/1.60  tff(c_454, plain, (~r1_xboole_0(k1_relat_1('#skF_4'), '#skF_3')), inference(splitRight, [status(thm)], [c_60])).
% 3.69/1.60  tff(c_856, plain, (k7_relat_1('#skF_4', '#skF_3')!=k1_xboole_0 | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_844, c_454])).
% 3.69/1.60  tff(c_866, plain, (k7_relat_1('#skF_4', '#skF_3')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_58, c_856])).
% 3.69/1.60  tff(c_46, plain, (![A_48, B_49]: (v1_relat_1(k7_relat_1(A_48, B_49)) | ~v1_relat_1(A_48))), inference(cnfTransformation, [status(thm)], [f_92])).
% 3.69/1.60  tff(c_720, plain, (![C_160, D_161, A_162, B_163]: (~r1_xboole_0(C_160, D_161) | r1_xboole_0(k2_zfmisc_1(A_162, C_160), k2_zfmisc_1(B_163, D_161)))), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.69/1.60  tff(c_20, plain, (![A_10]: (~r1_xboole_0(A_10, A_10) | k1_xboole_0=A_10)), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.69/1.60  tff(c_756, plain, (![B_165, D_166]: (k2_zfmisc_1(B_165, D_166)=k1_xboole_0 | ~r1_xboole_0(D_166, D_166))), inference(resolution, [status(thm)], [c_720, c_20])).
% 3.69/1.60  tff(c_776, plain, (![B_165]: (k2_zfmisc_1(B_165, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_16, c_756])).
% 3.69/1.60  tff(c_455, plain, (k9_relat_1('#skF_4', '#skF_3')=k1_xboole_0), inference(splitRight, [status(thm)], [c_60])).
% 3.69/1.60  tff(c_633, plain, (![B_148, A_149]: (k2_relat_1(k7_relat_1(B_148, A_149))=k9_relat_1(B_148, A_149) | ~v1_relat_1(B_148))), inference(cnfTransformation, [status(thm)], [f_100])).
% 3.69/1.60  tff(c_52, plain, (![A_53]: (r1_tarski(A_53, k2_zfmisc_1(k1_relat_1(A_53), k2_relat_1(A_53))) | ~v1_relat_1(A_53))), inference(cnfTransformation, [status(thm)], [f_104])).
% 3.69/1.60  tff(c_2456, plain, (![B_283, A_284]: (r1_tarski(k7_relat_1(B_283, A_284), k2_zfmisc_1(k1_relat_1(k7_relat_1(B_283, A_284)), k9_relat_1(B_283, A_284))) | ~v1_relat_1(k7_relat_1(B_283, A_284)) | ~v1_relat_1(B_283))), inference(superposition, [status(thm), theory('equality')], [c_633, c_52])).
% 3.69/1.60  tff(c_2485, plain, (r1_tarski(k7_relat_1('#skF_4', '#skF_3'), k2_zfmisc_1(k1_relat_1(k7_relat_1('#skF_4', '#skF_3')), k1_xboole_0)) | ~v1_relat_1(k7_relat_1('#skF_4', '#skF_3')) | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_455, c_2456])).
% 3.69/1.60  tff(c_2501, plain, (r1_tarski(k7_relat_1('#skF_4', '#skF_3'), k1_xboole_0) | ~v1_relat_1(k7_relat_1('#skF_4', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_776, c_2485])).
% 3.69/1.60  tff(c_2502, plain, (~v1_relat_1(k7_relat_1('#skF_4', '#skF_3'))), inference(splitLeft, [status(thm)], [c_2501])).
% 3.69/1.60  tff(c_2505, plain, (~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_46, c_2502])).
% 3.69/1.60  tff(c_2509, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_58, c_2505])).
% 3.69/1.60  tff(c_2510, plain, (r1_tarski(k7_relat_1('#skF_4', '#skF_3'), k1_xboole_0)), inference(splitRight, [status(thm)], [c_2501])).
% 3.69/1.60  tff(c_14, plain, (![A_8]: (r1_tarski(k1_xboole_0, A_8))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.69/1.60  tff(c_557, plain, (![B_135, A_136]: (B_135=A_136 | ~r1_tarski(B_135, A_136) | ~r1_tarski(A_136, B_135))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.69/1.60  tff(c_566, plain, (![A_8]: (k1_xboole_0=A_8 | ~r1_tarski(A_8, k1_xboole_0))), inference(resolution, [status(thm)], [c_14, c_557])).
% 3.69/1.60  tff(c_2518, plain, (k7_relat_1('#skF_4', '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_2510, c_566])).
% 3.69/1.60  tff(c_2524, plain, $false, inference(negUnitSimplification, [status(thm)], [c_866, c_2518])).
% 3.69/1.60  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.69/1.60  
% 3.69/1.60  Inference rules
% 3.69/1.60  ----------------------
% 3.69/1.60  #Ref     : 0
% 3.69/1.60  #Sup     : 564
% 3.69/1.60  #Fact    : 0
% 3.69/1.60  #Define  : 0
% 3.69/1.60  #Split   : 4
% 3.69/1.60  #Chain   : 0
% 3.69/1.60  #Close   : 0
% 3.69/1.60  
% 3.69/1.60  Ordering : KBO
% 3.69/1.60  
% 3.69/1.60  Simplification rules
% 3.69/1.60  ----------------------
% 3.69/1.60  #Subsume      : 16
% 3.69/1.60  #Demod        : 446
% 3.69/1.60  #Tautology    : 429
% 3.69/1.60  #SimpNegUnit  : 10
% 3.69/1.60  #BackRed      : 2
% 3.69/1.60  
% 3.69/1.60  #Partial instantiations: 0
% 3.69/1.60  #Strategies tried      : 1
% 3.69/1.60  
% 3.69/1.60  Timing (in seconds)
% 3.69/1.60  ----------------------
% 3.69/1.61  Preprocessing        : 0.35
% 3.69/1.61  Parsing              : 0.18
% 3.69/1.61  CNF conversion       : 0.02
% 3.69/1.61  Main loop            : 0.53
% 3.69/1.61  Inferencing          : 0.19
% 3.69/1.61  Reduction            : 0.16
% 3.69/1.61  Demodulation         : 0.12
% 3.69/1.61  BG Simplification    : 0.03
% 3.69/1.61  Subsumption          : 0.10
% 3.69/1.61  Abstraction          : 0.03
% 3.69/1.61  MUC search           : 0.00
% 3.69/1.61  Cooper               : 0.00
% 3.69/1.61  Total                : 0.92
% 3.69/1.61  Index Insertion      : 0.00
% 3.69/1.61  Index Deletion       : 0.00
% 3.69/1.61  Index Matching       : 0.00
% 3.69/1.61  BG Taut test         : 0.00
%------------------------------------------------------------------------------
