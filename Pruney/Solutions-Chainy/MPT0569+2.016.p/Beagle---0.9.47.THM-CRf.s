%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:01:38 EST 2020

% Result     : Theorem 14.51s
% Output     : CNFRefutation 14.51s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 102 expanded)
%              Number of leaves         :   41 (  54 expanded)
%              Depth                    :    9
%              Number of atoms          :  109 ( 168 expanded)
%              Number of equality atoms :   23 (  38 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_tarski > k3_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k2_relat_1 > k1_xboole_0 > #skF_2 > #skF_4 > #skF_13 > #skF_5 > #skF_6 > #skF_8 > #skF_11 > #skF_3 > #skF_7 > #skF_1 > #skF_9 > #skF_12 > #skF_10

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_13',type,(
    '#skF_13': $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': ( $i * $i ) > $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_11',type,(
    '#skF_11': ( $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': ( $i * $i ) > $i )).

tff('#skF_12',type,(
    '#skF_12': $i )).

tff('#skF_10',type,(
    '#skF_10': ( $i * $i * $i ) > $i )).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_33,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_131,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ( k10_relat_1(B,A) = k1_xboole_0
        <=> r1_xboole_0(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t173_relat_1)).

tff(f_59,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_124,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k10_relat_1(B,A) = k10_relat_1(B,k3_xboole_0(k2_relat_1(B),A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t168_relat_1)).

tff(f_120,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k10_relat_1(C,B))
      <=> ? [D] :
            ( r2_hidden(D,k2_relat_1(C))
            & r2_hidden(k4_tarski(A,D),C)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t166_relat_1)).

tff(f_71,axiom,(
    ! [A] :
      ( ~ ( ~ r1_xboole_0(A,A)
          & A = k1_xboole_0 )
      & ~ ( A != k1_xboole_0
          & r1_xboole_0(A,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_xboole_1)).

tff(f_51,axiom,(
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

tff(f_109,axiom,(
    ! [A,B] :
      ( B = k2_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(D,C),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_relat_1)).

tff(f_101,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B,C] :
          ( C = k10_relat_1(A,B)
        <=> ! [D] :
              ( r2_hidden(D,C)
            <=> ? [E] :
                  ( r2_hidden(k4_tarski(D,E),A)
                  & r2_hidden(E,B) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d14_relat_1)).

tff(c_95,plain,(
    ! [A_116,B_117] :
      ( r1_xboole_0(A_116,B_117)
      | k3_xboole_0(A_116,B_117) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_6,plain,(
    ! [B_4,A_3] :
      ( r1_xboole_0(B_4,A_3)
      | ~ r1_xboole_0(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_656,plain,(
    ! [B_205,A_206] :
      ( r1_xboole_0(B_205,A_206)
      | k3_xboole_0(A_206,B_205) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_95,c_6])).

tff(c_82,plain,
    ( k10_relat_1('#skF_13','#skF_12') = k1_xboole_0
    | r1_xboole_0(k2_relat_1('#skF_13'),'#skF_12') ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_123,plain,(
    r1_xboole_0(k2_relat_1('#skF_13'),'#skF_12') ),
    inference(splitLeft,[status(thm)],[c_82])).

tff(c_76,plain,
    ( ~ r1_xboole_0(k2_relat_1('#skF_13'),'#skF_12')
    | k10_relat_1('#skF_13','#skF_12') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_183,plain,(
    k10_relat_1('#skF_13','#skF_12') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_123,c_76])).

tff(c_14,plain,(
    ! [A_10] :
      ( r2_hidden('#skF_2'(A_10),A_10)
      | k1_xboole_0 = A_10 ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_74,plain,(
    v1_relat_1('#skF_13') ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( k3_xboole_0(A_1,B_2) = k1_xboole_0
      | ~ r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_129,plain,(
    k3_xboole_0(k2_relat_1('#skF_13'),'#skF_12') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_123,c_2])).

tff(c_342,plain,(
    ! [B_149,A_150] :
      ( k10_relat_1(B_149,k3_xboole_0(k2_relat_1(B_149),A_150)) = k10_relat_1(B_149,A_150)
      | ~ v1_relat_1(B_149) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_355,plain,
    ( k10_relat_1('#skF_13',k1_xboole_0) = k10_relat_1('#skF_13','#skF_12')
    | ~ v1_relat_1('#skF_13') ),
    inference(superposition,[status(thm),theory(equality)],[c_129,c_342])).

tff(c_360,plain,(
    k10_relat_1('#skF_13',k1_xboole_0) = k10_relat_1('#skF_13','#skF_12') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_355])).

tff(c_531,plain,(
    ! [A_194,B_195,C_196] :
      ( r2_hidden('#skF_11'(A_194,B_195,C_196),B_195)
      | ~ r2_hidden(A_194,k10_relat_1(C_196,B_195))
      | ~ v1_relat_1(C_196) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_16,plain,(
    r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_197,plain,(
    ! [A_134,B_135,C_136] :
      ( ~ r1_xboole_0(A_134,B_135)
      | ~ r2_hidden(C_136,B_135)
      | ~ r2_hidden(C_136,A_134) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_212,plain,(
    ! [C_136] : ~ r2_hidden(C_136,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_16,c_197])).

tff(c_571,plain,(
    ! [A_199,C_200] :
      ( ~ r2_hidden(A_199,k10_relat_1(C_200,k1_xboole_0))
      | ~ v1_relat_1(C_200) ) ),
    inference(resolution,[status(thm)],[c_531,c_212])).

tff(c_582,plain,(
    ! [A_199] :
      ( ~ r2_hidden(A_199,k10_relat_1('#skF_13','#skF_12'))
      | ~ v1_relat_1('#skF_13') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_360,c_571])).

tff(c_602,plain,(
    ! [A_201] : ~ r2_hidden(A_201,k10_relat_1('#skF_13','#skF_12')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_582])).

tff(c_622,plain,(
    k10_relat_1('#skF_13','#skF_12') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_14,c_602])).

tff(c_630,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_183,c_622])).

tff(c_632,plain,(
    ~ r1_xboole_0(k2_relat_1('#skF_13'),'#skF_12') ),
    inference(splitRight,[status(thm)],[c_82])).

tff(c_674,plain,(
    k3_xboole_0('#skF_12',k2_relat_1('#skF_13')) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_656,c_632])).

tff(c_10,plain,(
    ! [A_5,B_6] :
      ( r2_hidden('#skF_1'(A_5,B_6),B_6)
      | r1_xboole_0(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_697,plain,(
    ! [A_219,B_220,C_221] :
      ( ~ r1_xboole_0(A_219,B_220)
      | ~ r2_hidden(C_221,B_220)
      | ~ r2_hidden(C_221,A_219) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_706,plain,(
    ! [C_221] : ~ r2_hidden(C_221,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_16,c_697])).

tff(c_631,plain,(
    k10_relat_1('#skF_13','#skF_12') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_82])).

tff(c_52,plain,(
    ! [A_85,C_100] :
      ( r2_hidden(k4_tarski('#skF_10'(A_85,k2_relat_1(A_85),C_100),C_100),A_85)
      | ~ r2_hidden(C_100,k2_relat_1(A_85)) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_12,plain,(
    ! [A_5,B_6] :
      ( r2_hidden('#skF_1'(A_5,B_6),A_5)
      | r1_xboole_0(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_1240,plain,(
    ! [D_279,A_280,B_281,E_282] :
      ( r2_hidden(D_279,k10_relat_1(A_280,B_281))
      | ~ r2_hidden(E_282,B_281)
      | ~ r2_hidden(k4_tarski(D_279,E_282),A_280)
      | ~ v1_relat_1(A_280) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_4926,plain,(
    ! [D_489,A_490,A_491,B_492] :
      ( r2_hidden(D_489,k10_relat_1(A_490,A_491))
      | ~ r2_hidden(k4_tarski(D_489,'#skF_1'(A_491,B_492)),A_490)
      | ~ v1_relat_1(A_490)
      | r1_xboole_0(A_491,B_492) ) ),
    inference(resolution,[status(thm)],[c_12,c_1240])).

tff(c_33374,plain,(
    ! [A_1124,A_1125,B_1126] :
      ( r2_hidden('#skF_10'(A_1124,k2_relat_1(A_1124),'#skF_1'(A_1125,B_1126)),k10_relat_1(A_1124,A_1125))
      | ~ v1_relat_1(A_1124)
      | r1_xboole_0(A_1125,B_1126)
      | ~ r2_hidden('#skF_1'(A_1125,B_1126),k2_relat_1(A_1124)) ) ),
    inference(resolution,[status(thm)],[c_52,c_4926])).

tff(c_33569,plain,(
    ! [B_1126] :
      ( r2_hidden('#skF_10'('#skF_13',k2_relat_1('#skF_13'),'#skF_1'('#skF_12',B_1126)),k1_xboole_0)
      | ~ v1_relat_1('#skF_13')
      | r1_xboole_0('#skF_12',B_1126)
      | ~ r2_hidden('#skF_1'('#skF_12',B_1126),k2_relat_1('#skF_13')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_631,c_33374])).

tff(c_33600,plain,(
    ! [B_1126] :
      ( r2_hidden('#skF_10'('#skF_13',k2_relat_1('#skF_13'),'#skF_1'('#skF_12',B_1126)),k1_xboole_0)
      | r1_xboole_0('#skF_12',B_1126)
      | ~ r2_hidden('#skF_1'('#skF_12',B_1126),k2_relat_1('#skF_13')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_33569])).

tff(c_33602,plain,(
    ! [B_1127] :
      ( r1_xboole_0('#skF_12',B_1127)
      | ~ r2_hidden('#skF_1'('#skF_12',B_1127),k2_relat_1('#skF_13')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_706,c_33600])).

tff(c_33607,plain,(
    r1_xboole_0('#skF_12',k2_relat_1('#skF_13')) ),
    inference(resolution,[status(thm)],[c_10,c_33602])).

tff(c_33612,plain,(
    k3_xboole_0('#skF_12',k2_relat_1('#skF_13')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_33607,c_2])).

tff(c_33619,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_674,c_33612])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n018.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 17:48:12 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 14.51/6.76  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 14.51/6.77  
% 14.51/6.77  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 14.51/6.77  %$ r2_hidden > r1_xboole_0 > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_tarski > k3_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k2_relat_1 > k1_xboole_0 > #skF_2 > #skF_4 > #skF_13 > #skF_5 > #skF_6 > #skF_8 > #skF_11 > #skF_3 > #skF_7 > #skF_1 > #skF_9 > #skF_12 > #skF_10
% 14.51/6.77  
% 14.51/6.77  %Foreground sorts:
% 14.51/6.77  
% 14.51/6.77  
% 14.51/6.77  %Background operators:
% 14.51/6.77  
% 14.51/6.77  
% 14.51/6.77  %Foreground operators:
% 14.51/6.77  tff('#skF_2', type, '#skF_2': $i > $i).
% 14.51/6.77  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 14.51/6.77  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 14.51/6.77  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 14.51/6.77  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 14.51/6.77  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 14.51/6.77  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 14.51/6.77  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 14.51/6.77  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 14.51/6.77  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 14.51/6.77  tff('#skF_13', type, '#skF_13': $i).
% 14.51/6.77  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 14.51/6.77  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 14.51/6.77  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 14.51/6.77  tff('#skF_6', type, '#skF_6': ($i * $i * $i * $i) > $i).
% 14.51/6.77  tff('#skF_8', type, '#skF_8': ($i * $i) > $i).
% 14.51/6.77  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 14.51/6.77  tff('#skF_11', type, '#skF_11': ($i * $i * $i) > $i).
% 14.51/6.77  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 14.51/6.77  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 14.51/6.77  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 14.51/6.77  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 14.51/6.77  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 14.51/6.77  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 14.51/6.77  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 14.51/6.77  tff('#skF_7', type, '#skF_7': ($i * $i) > $i).
% 14.51/6.77  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 14.51/6.77  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 14.51/6.77  tff('#skF_9', type, '#skF_9': ($i * $i) > $i).
% 14.51/6.77  tff('#skF_12', type, '#skF_12': $i).
% 14.51/6.77  tff('#skF_10', type, '#skF_10': ($i * $i * $i) > $i).
% 14.51/6.77  
% 14.51/6.79  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 14.51/6.79  tff(f_33, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 14.51/6.79  tff(f_131, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => ((k10_relat_1(B, A) = k1_xboole_0) <=> r1_xboole_0(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t173_relat_1)).
% 14.51/6.79  tff(f_59, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 14.51/6.79  tff(f_124, axiom, (![A, B]: (v1_relat_1(B) => (k10_relat_1(B, A) = k10_relat_1(B, k3_xboole_0(k2_relat_1(B), A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t168_relat_1)).
% 14.51/6.79  tff(f_120, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k10_relat_1(C, B)) <=> (?[D]: ((r2_hidden(D, k2_relat_1(C)) & r2_hidden(k4_tarski(A, D), C)) & r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t166_relat_1)).
% 14.51/6.79  tff(f_71, axiom, (![A]: (~(~r1_xboole_0(A, A) & (A = k1_xboole_0)) & ~(~(A = k1_xboole_0) & r1_xboole_0(A, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t66_xboole_1)).
% 14.51/6.79  tff(f_51, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 14.51/6.79  tff(f_109, axiom, (![A, B]: ((B = k2_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(D, C), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_relat_1)).
% 14.51/6.79  tff(f_101, axiom, (![A]: (v1_relat_1(A) => (![B, C]: ((C = k10_relat_1(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (?[E]: (r2_hidden(k4_tarski(D, E), A) & r2_hidden(E, B))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d14_relat_1)).
% 14.51/6.79  tff(c_95, plain, (![A_116, B_117]: (r1_xboole_0(A_116, B_117) | k3_xboole_0(A_116, B_117)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 14.51/6.79  tff(c_6, plain, (![B_4, A_3]: (r1_xboole_0(B_4, A_3) | ~r1_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 14.51/6.79  tff(c_656, plain, (![B_205, A_206]: (r1_xboole_0(B_205, A_206) | k3_xboole_0(A_206, B_205)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_95, c_6])).
% 14.51/6.79  tff(c_82, plain, (k10_relat_1('#skF_13', '#skF_12')=k1_xboole_0 | r1_xboole_0(k2_relat_1('#skF_13'), '#skF_12')), inference(cnfTransformation, [status(thm)], [f_131])).
% 14.51/6.79  tff(c_123, plain, (r1_xboole_0(k2_relat_1('#skF_13'), '#skF_12')), inference(splitLeft, [status(thm)], [c_82])).
% 14.51/6.79  tff(c_76, plain, (~r1_xboole_0(k2_relat_1('#skF_13'), '#skF_12') | k10_relat_1('#skF_13', '#skF_12')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_131])).
% 14.51/6.79  tff(c_183, plain, (k10_relat_1('#skF_13', '#skF_12')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_123, c_76])).
% 14.51/6.79  tff(c_14, plain, (![A_10]: (r2_hidden('#skF_2'(A_10), A_10) | k1_xboole_0=A_10)), inference(cnfTransformation, [status(thm)], [f_59])).
% 14.51/6.79  tff(c_74, plain, (v1_relat_1('#skF_13')), inference(cnfTransformation, [status(thm)], [f_131])).
% 14.51/6.79  tff(c_2, plain, (![A_1, B_2]: (k3_xboole_0(A_1, B_2)=k1_xboole_0 | ~r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 14.51/6.79  tff(c_129, plain, (k3_xboole_0(k2_relat_1('#skF_13'), '#skF_12')=k1_xboole_0), inference(resolution, [status(thm)], [c_123, c_2])).
% 14.51/6.79  tff(c_342, plain, (![B_149, A_150]: (k10_relat_1(B_149, k3_xboole_0(k2_relat_1(B_149), A_150))=k10_relat_1(B_149, A_150) | ~v1_relat_1(B_149))), inference(cnfTransformation, [status(thm)], [f_124])).
% 14.51/6.79  tff(c_355, plain, (k10_relat_1('#skF_13', k1_xboole_0)=k10_relat_1('#skF_13', '#skF_12') | ~v1_relat_1('#skF_13')), inference(superposition, [status(thm), theory('equality')], [c_129, c_342])).
% 14.51/6.79  tff(c_360, plain, (k10_relat_1('#skF_13', k1_xboole_0)=k10_relat_1('#skF_13', '#skF_12')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_355])).
% 14.51/6.79  tff(c_531, plain, (![A_194, B_195, C_196]: (r2_hidden('#skF_11'(A_194, B_195, C_196), B_195) | ~r2_hidden(A_194, k10_relat_1(C_196, B_195)) | ~v1_relat_1(C_196))), inference(cnfTransformation, [status(thm)], [f_120])).
% 14.51/6.79  tff(c_16, plain, (r1_xboole_0(k1_xboole_0, k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_71])).
% 14.51/6.79  tff(c_197, plain, (![A_134, B_135, C_136]: (~r1_xboole_0(A_134, B_135) | ~r2_hidden(C_136, B_135) | ~r2_hidden(C_136, A_134))), inference(cnfTransformation, [status(thm)], [f_51])).
% 14.51/6.79  tff(c_212, plain, (![C_136]: (~r2_hidden(C_136, k1_xboole_0))), inference(resolution, [status(thm)], [c_16, c_197])).
% 14.51/6.79  tff(c_571, plain, (![A_199, C_200]: (~r2_hidden(A_199, k10_relat_1(C_200, k1_xboole_0)) | ~v1_relat_1(C_200))), inference(resolution, [status(thm)], [c_531, c_212])).
% 14.51/6.79  tff(c_582, plain, (![A_199]: (~r2_hidden(A_199, k10_relat_1('#skF_13', '#skF_12')) | ~v1_relat_1('#skF_13'))), inference(superposition, [status(thm), theory('equality')], [c_360, c_571])).
% 14.51/6.79  tff(c_602, plain, (![A_201]: (~r2_hidden(A_201, k10_relat_1('#skF_13', '#skF_12')))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_582])).
% 14.51/6.79  tff(c_622, plain, (k10_relat_1('#skF_13', '#skF_12')=k1_xboole_0), inference(resolution, [status(thm)], [c_14, c_602])).
% 14.51/6.79  tff(c_630, plain, $false, inference(negUnitSimplification, [status(thm)], [c_183, c_622])).
% 14.51/6.79  tff(c_632, plain, (~r1_xboole_0(k2_relat_1('#skF_13'), '#skF_12')), inference(splitRight, [status(thm)], [c_82])).
% 14.51/6.79  tff(c_674, plain, (k3_xboole_0('#skF_12', k2_relat_1('#skF_13'))!=k1_xboole_0), inference(resolution, [status(thm)], [c_656, c_632])).
% 14.51/6.79  tff(c_10, plain, (![A_5, B_6]: (r2_hidden('#skF_1'(A_5, B_6), B_6) | r1_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_51])).
% 14.51/6.79  tff(c_697, plain, (![A_219, B_220, C_221]: (~r1_xboole_0(A_219, B_220) | ~r2_hidden(C_221, B_220) | ~r2_hidden(C_221, A_219))), inference(cnfTransformation, [status(thm)], [f_51])).
% 14.51/6.79  tff(c_706, plain, (![C_221]: (~r2_hidden(C_221, k1_xboole_0))), inference(resolution, [status(thm)], [c_16, c_697])).
% 14.51/6.79  tff(c_631, plain, (k10_relat_1('#skF_13', '#skF_12')=k1_xboole_0), inference(splitRight, [status(thm)], [c_82])).
% 14.51/6.79  tff(c_52, plain, (![A_85, C_100]: (r2_hidden(k4_tarski('#skF_10'(A_85, k2_relat_1(A_85), C_100), C_100), A_85) | ~r2_hidden(C_100, k2_relat_1(A_85)))), inference(cnfTransformation, [status(thm)], [f_109])).
% 14.51/6.79  tff(c_12, plain, (![A_5, B_6]: (r2_hidden('#skF_1'(A_5, B_6), A_5) | r1_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_51])).
% 14.51/6.79  tff(c_1240, plain, (![D_279, A_280, B_281, E_282]: (r2_hidden(D_279, k10_relat_1(A_280, B_281)) | ~r2_hidden(E_282, B_281) | ~r2_hidden(k4_tarski(D_279, E_282), A_280) | ~v1_relat_1(A_280))), inference(cnfTransformation, [status(thm)], [f_101])).
% 14.51/6.79  tff(c_4926, plain, (![D_489, A_490, A_491, B_492]: (r2_hidden(D_489, k10_relat_1(A_490, A_491)) | ~r2_hidden(k4_tarski(D_489, '#skF_1'(A_491, B_492)), A_490) | ~v1_relat_1(A_490) | r1_xboole_0(A_491, B_492))), inference(resolution, [status(thm)], [c_12, c_1240])).
% 14.51/6.79  tff(c_33374, plain, (![A_1124, A_1125, B_1126]: (r2_hidden('#skF_10'(A_1124, k2_relat_1(A_1124), '#skF_1'(A_1125, B_1126)), k10_relat_1(A_1124, A_1125)) | ~v1_relat_1(A_1124) | r1_xboole_0(A_1125, B_1126) | ~r2_hidden('#skF_1'(A_1125, B_1126), k2_relat_1(A_1124)))), inference(resolution, [status(thm)], [c_52, c_4926])).
% 14.51/6.79  tff(c_33569, plain, (![B_1126]: (r2_hidden('#skF_10'('#skF_13', k2_relat_1('#skF_13'), '#skF_1'('#skF_12', B_1126)), k1_xboole_0) | ~v1_relat_1('#skF_13') | r1_xboole_0('#skF_12', B_1126) | ~r2_hidden('#skF_1'('#skF_12', B_1126), k2_relat_1('#skF_13')))), inference(superposition, [status(thm), theory('equality')], [c_631, c_33374])).
% 14.51/6.79  tff(c_33600, plain, (![B_1126]: (r2_hidden('#skF_10'('#skF_13', k2_relat_1('#skF_13'), '#skF_1'('#skF_12', B_1126)), k1_xboole_0) | r1_xboole_0('#skF_12', B_1126) | ~r2_hidden('#skF_1'('#skF_12', B_1126), k2_relat_1('#skF_13')))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_33569])).
% 14.51/6.79  tff(c_33602, plain, (![B_1127]: (r1_xboole_0('#skF_12', B_1127) | ~r2_hidden('#skF_1'('#skF_12', B_1127), k2_relat_1('#skF_13')))), inference(negUnitSimplification, [status(thm)], [c_706, c_33600])).
% 14.51/6.79  tff(c_33607, plain, (r1_xboole_0('#skF_12', k2_relat_1('#skF_13'))), inference(resolution, [status(thm)], [c_10, c_33602])).
% 14.51/6.79  tff(c_33612, plain, (k3_xboole_0('#skF_12', k2_relat_1('#skF_13'))=k1_xboole_0), inference(resolution, [status(thm)], [c_33607, c_2])).
% 14.51/6.79  tff(c_33619, plain, $false, inference(negUnitSimplification, [status(thm)], [c_674, c_33612])).
% 14.51/6.79  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 14.51/6.79  
% 14.51/6.79  Inference rules
% 14.51/6.79  ----------------------
% 14.51/6.79  #Ref     : 0
% 14.51/6.79  #Sup     : 8214
% 14.51/6.79  #Fact    : 0
% 14.51/6.79  #Define  : 0
% 14.51/6.79  #Split   : 20
% 14.51/6.79  #Chain   : 0
% 14.51/6.79  #Close   : 0
% 14.51/6.79  
% 14.51/6.79  Ordering : KBO
% 14.51/6.79  
% 14.51/6.79  Simplification rules
% 14.51/6.79  ----------------------
% 14.51/6.79  #Subsume      : 3523
% 14.51/6.79  #Demod        : 3903
% 14.51/6.79  #Tautology    : 1963
% 14.51/6.79  #SimpNegUnit  : 368
% 14.51/6.79  #BackRed      : 2
% 14.51/6.79  
% 14.51/6.79  #Partial instantiations: 0
% 14.51/6.79  #Strategies tried      : 1
% 14.51/6.79  
% 14.51/6.79  Timing (in seconds)
% 14.51/6.79  ----------------------
% 14.51/6.79  Preprocessing        : 0.35
% 14.51/6.79  Parsing              : 0.18
% 14.51/6.79  CNF conversion       : 0.03
% 14.51/6.79  Main loop            : 5.69
% 14.51/6.79  Inferencing          : 1.07
% 14.51/6.79  Reduction            : 1.01
% 14.51/6.79  Demodulation         : 0.67
% 14.51/6.79  BG Simplification    : 0.11
% 14.51/6.79  Subsumption          : 3.26
% 14.51/6.79  Abstraction          : 0.16
% 14.51/6.79  MUC search           : 0.00
% 14.51/6.79  Cooper               : 0.00
% 14.51/6.79  Total                : 6.08
% 14.51/6.79  Index Insertion      : 0.00
% 14.51/6.79  Index Deletion       : 0.00
% 14.51/6.79  Index Matching       : 0.00
% 14.51/6.79  BG Taut test         : 0.00
%------------------------------------------------------------------------------
