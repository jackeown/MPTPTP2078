%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:01:38 EST 2020

% Result     : Theorem 49.56s
% Output     : CNFRefutation 49.56s
% Verified   : 
% Statistics : Number of formulae       :   71 (  96 expanded)
%              Number of leaves         :   36 (  50 expanded)
%              Depth                    :    9
%              Number of atoms          :   98 ( 161 expanded)
%              Number of equality atoms :   14 (  27 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > v1_relat_1 > k4_tarski > k3_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k2_relat_1 > k1_tarski > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_4 > #skF_13 > #skF_5 > #skF_6 > #skF_8 > #skF_11 > #skF_3 > #skF_2 > #skF_7 > #skF_1 > #skF_9 > #skF_12 > #skF_10

%Foreground sorts:

%Background operators:

%Foreground operators:
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

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_13',type,(
    '#skF_13': $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': ( $i * $i ) > $i )).

tff('#skF_11',type,(
    '#skF_11': ( $i * $i * $i ) > $i )).

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_12',type,(
    '#skF_12': $i )).

tff('#skF_10',type,(
    '#skF_10': ( $i * $i * $i ) > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_112,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ( k10_relat_1(B,A) = k1_xboole_0
        <=> r1_xboole_0(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t173_relat_1)).

tff(f_105,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_87,axiom,(
    ! [A,B] :
      ( B = k2_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(D,C),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_relat_1)).

tff(f_59,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_64,axiom,(
    ! [A,B] :
      ~ ( r1_xboole_0(k1_tarski(A),B)
        & r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l24_zfmisc_1)).

tff(f_98,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k10_relat_1(C,B))
      <=> ? [D] :
            ( r2_hidden(D,k2_relat_1(C))
            & r2_hidden(k4_tarski(A,D),C)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t166_relat_1)).

tff(f_43,axiom,(
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

tff(f_79,axiom,(
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

tff(c_70,plain,
    ( k10_relat_1('#skF_13','#skF_12') = k1_xboole_0
    | r1_xboole_0(k2_relat_1('#skF_13'),'#skF_12') ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_109,plain,(
    r1_xboole_0(k2_relat_1('#skF_13'),'#skF_12') ),
    inference(splitLeft,[status(thm)],[c_70])).

tff(c_64,plain,
    ( ~ r1_xboole_0(k2_relat_1('#skF_13'),'#skF_12')
    | k10_relat_1('#skF_13','#skF_12') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_111,plain,(
    k10_relat_1('#skF_13','#skF_12') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_109,c_64])).

tff(c_58,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_1170,plain,(
    ! [A_247,B_248] :
      ( r2_hidden(k4_tarski('#skF_8'(A_247,B_248),'#skF_7'(A_247,B_248)),A_247)
      | r2_hidden('#skF_9'(A_247,B_248),B_248)
      | k2_relat_1(A_247) = B_248 ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_12,plain,(
    ! [A_11] : r1_xboole_0(A_11,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_89,plain,(
    ! [A_88,B_89] :
      ( ~ r2_hidden(A_88,B_89)
      | ~ r1_xboole_0(k1_tarski(A_88),B_89) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_94,plain,(
    ! [A_88] : ~ r2_hidden(A_88,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_12,c_89])).

tff(c_1259,plain,(
    ! [B_248] :
      ( r2_hidden('#skF_9'(k1_xboole_0,B_248),B_248)
      | k2_relat_1(k1_xboole_0) = B_248 ) ),
    inference(resolution,[status(thm)],[c_1170,c_94])).

tff(c_1284,plain,(
    ! [B_249] :
      ( r2_hidden('#skF_9'(k1_xboole_0,B_249),B_249)
      | k1_xboole_0 = B_249 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_1259])).

tff(c_62,plain,(
    v1_relat_1('#skF_13') ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_50,plain,(
    ! [A_77,B_78,C_79] :
      ( r2_hidden('#skF_11'(A_77,B_78,C_79),B_78)
      | ~ r2_hidden(A_77,k10_relat_1(C_79,B_78))
      | ~ v1_relat_1(C_79) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_419,plain,(
    ! [A_166,B_167,C_168] :
      ( r2_hidden('#skF_11'(A_166,B_167,C_168),k2_relat_1(C_168))
      | ~ r2_hidden(A_166,k10_relat_1(C_168,B_167))
      | ~ v1_relat_1(C_168) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_125,plain,(
    ! [A_102,B_103,C_104] :
      ( ~ r1_xboole_0(A_102,B_103)
      | ~ r2_hidden(C_104,B_103)
      | ~ r2_hidden(C_104,A_102) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_136,plain,(
    ! [C_104] :
      ( ~ r2_hidden(C_104,'#skF_12')
      | ~ r2_hidden(C_104,k2_relat_1('#skF_13')) ) ),
    inference(resolution,[status(thm)],[c_109,c_125])).

tff(c_443,plain,(
    ! [A_166,B_167] :
      ( ~ r2_hidden('#skF_11'(A_166,B_167,'#skF_13'),'#skF_12')
      | ~ r2_hidden(A_166,k10_relat_1('#skF_13',B_167))
      | ~ v1_relat_1('#skF_13') ) ),
    inference(resolution,[status(thm)],[c_419,c_136])).

tff(c_544,plain,(
    ! [A_185,B_186] :
      ( ~ r2_hidden('#skF_11'(A_185,B_186,'#skF_13'),'#skF_12')
      | ~ r2_hidden(A_185,k10_relat_1('#skF_13',B_186)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_443])).

tff(c_548,plain,(
    ! [A_77] :
      ( ~ r2_hidden(A_77,k10_relat_1('#skF_13','#skF_12'))
      | ~ v1_relat_1('#skF_13') ) ),
    inference(resolution,[status(thm)],[c_50,c_544])).

tff(c_551,plain,(
    ! [A_77] : ~ r2_hidden(A_77,k10_relat_1('#skF_13','#skF_12')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_548])).

tff(c_1326,plain,(
    k10_relat_1('#skF_13','#skF_12') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1284,c_551])).

tff(c_1384,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_111,c_1326])).

tff(c_1386,plain,(
    ~ r1_xboole_0(k2_relat_1('#skF_13'),'#skF_12') ),
    inference(splitRight,[status(thm)],[c_70])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_1385,plain,(
    k10_relat_1('#skF_13','#skF_12') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_70])).

tff(c_36,plain,(
    ! [A_58,C_73] :
      ( r2_hidden(k4_tarski('#skF_10'(A_58,k2_relat_1(A_58),C_73),C_73),A_58)
      | ~ r2_hidden(C_73,k2_relat_1(A_58)) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_1831,plain,(
    ! [D_342,A_343,B_344,E_345] :
      ( r2_hidden(D_342,k10_relat_1(A_343,B_344))
      | ~ r2_hidden(E_345,B_344)
      | ~ r2_hidden(k4_tarski(D_342,E_345),A_343)
      | ~ v1_relat_1(A_343) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_10995,plain,(
    ! [D_600,A_601,B_602,A_603] :
      ( r2_hidden(D_600,k10_relat_1(A_601,B_602))
      | ~ r2_hidden(k4_tarski(D_600,'#skF_1'(A_603,B_602)),A_601)
      | ~ v1_relat_1(A_601)
      | r1_xboole_0(A_603,B_602) ) ),
    inference(resolution,[status(thm)],[c_4,c_1831])).

tff(c_176216,plain,(
    ! [A_1906,A_1907,B_1908] :
      ( r2_hidden('#skF_10'(A_1906,k2_relat_1(A_1906),'#skF_1'(A_1907,B_1908)),k10_relat_1(A_1906,B_1908))
      | ~ v1_relat_1(A_1906)
      | r1_xboole_0(A_1907,B_1908)
      | ~ r2_hidden('#skF_1'(A_1907,B_1908),k2_relat_1(A_1906)) ) ),
    inference(resolution,[status(thm)],[c_36,c_10995])).

tff(c_176623,plain,(
    ! [A_1907] :
      ( r2_hidden('#skF_10'('#skF_13',k2_relat_1('#skF_13'),'#skF_1'(A_1907,'#skF_12')),k1_xboole_0)
      | ~ v1_relat_1('#skF_13')
      | r1_xboole_0(A_1907,'#skF_12')
      | ~ r2_hidden('#skF_1'(A_1907,'#skF_12'),k2_relat_1('#skF_13')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1385,c_176216])).

tff(c_176676,plain,(
    ! [A_1907] :
      ( r2_hidden('#skF_10'('#skF_13',k2_relat_1('#skF_13'),'#skF_1'(A_1907,'#skF_12')),k1_xboole_0)
      | r1_xboole_0(A_1907,'#skF_12')
      | ~ r2_hidden('#skF_1'(A_1907,'#skF_12'),k2_relat_1('#skF_13')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_176623])).

tff(c_176679,plain,(
    ! [A_1909] :
      ( r1_xboole_0(A_1909,'#skF_12')
      | ~ r2_hidden('#skF_1'(A_1909,'#skF_12'),k2_relat_1('#skF_13')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_94,c_176676])).

tff(c_176683,plain,(
    r1_xboole_0(k2_relat_1('#skF_13'),'#skF_12') ),
    inference(resolution,[status(thm)],[c_6,c_176679])).

tff(c_176687,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1386,c_1386,c_176683])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.32  % Computer   : n004.cluster.edu
% 0.13/0.32  % Model      : x86_64 x86_64
% 0.13/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.32  % Memory     : 8042.1875MB
% 0.13/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.32  % CPULimit   : 60
% 0.13/0.32  % DateTime   : Tue Dec  1 16:38:08 EST 2020
% 0.13/0.32  % CPUTime    : 
% 0.13/0.33  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 49.56/39.13  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 49.56/39.13  
% 49.56/39.13  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 49.56/39.13  %$ r2_hidden > r1_xboole_0 > v1_relat_1 > k4_tarski > k3_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k2_relat_1 > k1_tarski > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_4 > #skF_13 > #skF_5 > #skF_6 > #skF_8 > #skF_11 > #skF_3 > #skF_2 > #skF_7 > #skF_1 > #skF_9 > #skF_12 > #skF_10
% 49.56/39.13  
% 49.56/39.13  %Foreground sorts:
% 49.56/39.13  
% 49.56/39.13  
% 49.56/39.13  %Background operators:
% 49.56/39.13  
% 49.56/39.13  
% 49.56/39.13  %Foreground operators:
% 49.56/39.13  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 49.56/39.13  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 49.56/39.13  tff(k1_tarski, type, k1_tarski: $i > $i).
% 49.56/39.13  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 49.56/39.13  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 49.56/39.13  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 49.56/39.13  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 49.56/39.13  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 49.56/39.13  tff('#skF_13', type, '#skF_13': $i).
% 49.56/39.13  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 49.56/39.13  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 49.56/39.13  tff('#skF_6', type, '#skF_6': ($i * $i * $i * $i) > $i).
% 49.56/39.13  tff('#skF_8', type, '#skF_8': ($i * $i) > $i).
% 49.56/39.13  tff('#skF_11', type, '#skF_11': ($i * $i * $i) > $i).
% 49.56/39.13  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 49.56/39.13  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 49.56/39.13  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 49.56/39.13  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 49.56/39.13  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 49.56/39.13  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 49.56/39.13  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 49.56/39.13  tff('#skF_7', type, '#skF_7': ($i * $i) > $i).
% 49.56/39.13  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 49.56/39.13  tff('#skF_9', type, '#skF_9': ($i * $i) > $i).
% 49.56/39.13  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 49.56/39.13  tff('#skF_12', type, '#skF_12': $i).
% 49.56/39.13  tff('#skF_10', type, '#skF_10': ($i * $i * $i) > $i).
% 49.56/39.13  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 49.56/39.13  
% 49.56/39.15  tff(f_112, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => ((k10_relat_1(B, A) = k1_xboole_0) <=> r1_xboole_0(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t173_relat_1)).
% 49.56/39.15  tff(f_105, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 49.56/39.15  tff(f_87, axiom, (![A, B]: ((B = k2_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(D, C), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_relat_1)).
% 49.56/39.15  tff(f_59, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 49.56/39.15  tff(f_64, axiom, (![A, B]: ~(r1_xboole_0(k1_tarski(A), B) & r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l24_zfmisc_1)).
% 49.56/39.15  tff(f_98, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k10_relat_1(C, B)) <=> (?[D]: ((r2_hidden(D, k2_relat_1(C)) & r2_hidden(k4_tarski(A, D), C)) & r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t166_relat_1)).
% 49.56/39.15  tff(f_43, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 49.56/39.15  tff(f_79, axiom, (![A]: (v1_relat_1(A) => (![B, C]: ((C = k10_relat_1(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (?[E]: (r2_hidden(k4_tarski(D, E), A) & r2_hidden(E, B))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d14_relat_1)).
% 49.56/39.15  tff(c_70, plain, (k10_relat_1('#skF_13', '#skF_12')=k1_xboole_0 | r1_xboole_0(k2_relat_1('#skF_13'), '#skF_12')), inference(cnfTransformation, [status(thm)], [f_112])).
% 49.56/39.15  tff(c_109, plain, (r1_xboole_0(k2_relat_1('#skF_13'), '#skF_12')), inference(splitLeft, [status(thm)], [c_70])).
% 49.56/39.15  tff(c_64, plain, (~r1_xboole_0(k2_relat_1('#skF_13'), '#skF_12') | k10_relat_1('#skF_13', '#skF_12')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_112])).
% 49.56/39.15  tff(c_111, plain, (k10_relat_1('#skF_13', '#skF_12')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_109, c_64])).
% 49.56/39.15  tff(c_58, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_105])).
% 49.56/39.15  tff(c_1170, plain, (![A_247, B_248]: (r2_hidden(k4_tarski('#skF_8'(A_247, B_248), '#skF_7'(A_247, B_248)), A_247) | r2_hidden('#skF_9'(A_247, B_248), B_248) | k2_relat_1(A_247)=B_248)), inference(cnfTransformation, [status(thm)], [f_87])).
% 49.56/39.15  tff(c_12, plain, (![A_11]: (r1_xboole_0(A_11, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_59])).
% 49.56/39.15  tff(c_89, plain, (![A_88, B_89]: (~r2_hidden(A_88, B_89) | ~r1_xboole_0(k1_tarski(A_88), B_89))), inference(cnfTransformation, [status(thm)], [f_64])).
% 49.56/39.15  tff(c_94, plain, (![A_88]: (~r2_hidden(A_88, k1_xboole_0))), inference(resolution, [status(thm)], [c_12, c_89])).
% 49.56/39.15  tff(c_1259, plain, (![B_248]: (r2_hidden('#skF_9'(k1_xboole_0, B_248), B_248) | k2_relat_1(k1_xboole_0)=B_248)), inference(resolution, [status(thm)], [c_1170, c_94])).
% 49.56/39.15  tff(c_1284, plain, (![B_249]: (r2_hidden('#skF_9'(k1_xboole_0, B_249), B_249) | k1_xboole_0=B_249)), inference(demodulation, [status(thm), theory('equality')], [c_58, c_1259])).
% 49.56/39.15  tff(c_62, plain, (v1_relat_1('#skF_13')), inference(cnfTransformation, [status(thm)], [f_112])).
% 49.56/39.15  tff(c_50, plain, (![A_77, B_78, C_79]: (r2_hidden('#skF_11'(A_77, B_78, C_79), B_78) | ~r2_hidden(A_77, k10_relat_1(C_79, B_78)) | ~v1_relat_1(C_79))), inference(cnfTransformation, [status(thm)], [f_98])).
% 49.56/39.15  tff(c_419, plain, (![A_166, B_167, C_168]: (r2_hidden('#skF_11'(A_166, B_167, C_168), k2_relat_1(C_168)) | ~r2_hidden(A_166, k10_relat_1(C_168, B_167)) | ~v1_relat_1(C_168))), inference(cnfTransformation, [status(thm)], [f_98])).
% 49.56/39.15  tff(c_125, plain, (![A_102, B_103, C_104]: (~r1_xboole_0(A_102, B_103) | ~r2_hidden(C_104, B_103) | ~r2_hidden(C_104, A_102))), inference(cnfTransformation, [status(thm)], [f_43])).
% 49.56/39.15  tff(c_136, plain, (![C_104]: (~r2_hidden(C_104, '#skF_12') | ~r2_hidden(C_104, k2_relat_1('#skF_13')))), inference(resolution, [status(thm)], [c_109, c_125])).
% 49.56/39.15  tff(c_443, plain, (![A_166, B_167]: (~r2_hidden('#skF_11'(A_166, B_167, '#skF_13'), '#skF_12') | ~r2_hidden(A_166, k10_relat_1('#skF_13', B_167)) | ~v1_relat_1('#skF_13'))), inference(resolution, [status(thm)], [c_419, c_136])).
% 49.56/39.15  tff(c_544, plain, (![A_185, B_186]: (~r2_hidden('#skF_11'(A_185, B_186, '#skF_13'), '#skF_12') | ~r2_hidden(A_185, k10_relat_1('#skF_13', B_186)))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_443])).
% 49.56/39.15  tff(c_548, plain, (![A_77]: (~r2_hidden(A_77, k10_relat_1('#skF_13', '#skF_12')) | ~v1_relat_1('#skF_13'))), inference(resolution, [status(thm)], [c_50, c_544])).
% 49.56/39.15  tff(c_551, plain, (![A_77]: (~r2_hidden(A_77, k10_relat_1('#skF_13', '#skF_12')))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_548])).
% 49.56/39.15  tff(c_1326, plain, (k10_relat_1('#skF_13', '#skF_12')=k1_xboole_0), inference(resolution, [status(thm)], [c_1284, c_551])).
% 49.56/39.15  tff(c_1384, plain, $false, inference(negUnitSimplification, [status(thm)], [c_111, c_1326])).
% 49.56/39.15  tff(c_1386, plain, (~r1_xboole_0(k2_relat_1('#skF_13'), '#skF_12')), inference(splitRight, [status(thm)], [c_70])).
% 49.56/39.15  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_43])).
% 49.56/39.15  tff(c_1385, plain, (k10_relat_1('#skF_13', '#skF_12')=k1_xboole_0), inference(splitRight, [status(thm)], [c_70])).
% 49.56/39.15  tff(c_36, plain, (![A_58, C_73]: (r2_hidden(k4_tarski('#skF_10'(A_58, k2_relat_1(A_58), C_73), C_73), A_58) | ~r2_hidden(C_73, k2_relat_1(A_58)))), inference(cnfTransformation, [status(thm)], [f_87])).
% 49.56/39.15  tff(c_4, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_43])).
% 49.56/39.15  tff(c_1831, plain, (![D_342, A_343, B_344, E_345]: (r2_hidden(D_342, k10_relat_1(A_343, B_344)) | ~r2_hidden(E_345, B_344) | ~r2_hidden(k4_tarski(D_342, E_345), A_343) | ~v1_relat_1(A_343))), inference(cnfTransformation, [status(thm)], [f_79])).
% 49.56/39.15  tff(c_10995, plain, (![D_600, A_601, B_602, A_603]: (r2_hidden(D_600, k10_relat_1(A_601, B_602)) | ~r2_hidden(k4_tarski(D_600, '#skF_1'(A_603, B_602)), A_601) | ~v1_relat_1(A_601) | r1_xboole_0(A_603, B_602))), inference(resolution, [status(thm)], [c_4, c_1831])).
% 49.56/39.15  tff(c_176216, plain, (![A_1906, A_1907, B_1908]: (r2_hidden('#skF_10'(A_1906, k2_relat_1(A_1906), '#skF_1'(A_1907, B_1908)), k10_relat_1(A_1906, B_1908)) | ~v1_relat_1(A_1906) | r1_xboole_0(A_1907, B_1908) | ~r2_hidden('#skF_1'(A_1907, B_1908), k2_relat_1(A_1906)))), inference(resolution, [status(thm)], [c_36, c_10995])).
% 49.56/39.15  tff(c_176623, plain, (![A_1907]: (r2_hidden('#skF_10'('#skF_13', k2_relat_1('#skF_13'), '#skF_1'(A_1907, '#skF_12')), k1_xboole_0) | ~v1_relat_1('#skF_13') | r1_xboole_0(A_1907, '#skF_12') | ~r2_hidden('#skF_1'(A_1907, '#skF_12'), k2_relat_1('#skF_13')))), inference(superposition, [status(thm), theory('equality')], [c_1385, c_176216])).
% 49.56/39.15  tff(c_176676, plain, (![A_1907]: (r2_hidden('#skF_10'('#skF_13', k2_relat_1('#skF_13'), '#skF_1'(A_1907, '#skF_12')), k1_xboole_0) | r1_xboole_0(A_1907, '#skF_12') | ~r2_hidden('#skF_1'(A_1907, '#skF_12'), k2_relat_1('#skF_13')))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_176623])).
% 49.56/39.15  tff(c_176679, plain, (![A_1909]: (r1_xboole_0(A_1909, '#skF_12') | ~r2_hidden('#skF_1'(A_1909, '#skF_12'), k2_relat_1('#skF_13')))), inference(negUnitSimplification, [status(thm)], [c_94, c_176676])).
% 49.56/39.15  tff(c_176683, plain, (r1_xboole_0(k2_relat_1('#skF_13'), '#skF_12')), inference(resolution, [status(thm)], [c_6, c_176679])).
% 49.56/39.15  tff(c_176687, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1386, c_1386, c_176683])).
% 49.56/39.15  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 49.56/39.15  
% 49.56/39.15  Inference rules
% 49.56/39.15  ----------------------
% 49.56/39.15  #Ref     : 0
% 49.56/39.15  #Sup     : 46493
% 49.56/39.15  #Fact    : 0
% 49.56/39.15  #Define  : 0
% 49.56/39.15  #Split   : 18
% 49.56/39.15  #Chain   : 0
% 49.56/39.15  #Close   : 0
% 49.56/39.15  
% 49.56/39.15  Ordering : KBO
% 49.56/39.15  
% 49.56/39.15  Simplification rules
% 49.56/39.15  ----------------------
% 49.56/39.15  #Subsume      : 20321
% 49.56/39.15  #Demod        : 46062
% 49.56/39.15  #Tautology    : 16955
% 49.56/39.15  #SimpNegUnit  : 873
% 49.56/39.15  #BackRed      : 32
% 49.56/39.15  
% 49.56/39.15  #Partial instantiations: 0
% 49.56/39.15  #Strategies tried      : 1
% 49.56/39.15  
% 49.56/39.15  Timing (in seconds)
% 49.56/39.15  ----------------------
% 49.73/39.15  Preprocessing        : 0.30
% 49.73/39.15  Parsing              : 0.15
% 49.73/39.15  CNF conversion       : 0.03
% 49.73/39.15  Main loop            : 38.11
% 49.73/39.15  Inferencing          : 3.52
% 49.73/39.15  Reduction            : 4.60
% 49.73/39.15  Demodulation         : 3.18
% 49.73/39.15  BG Simplification    : 0.33
% 49.73/39.15  Subsumption          : 28.56
% 49.73/39.15  Abstraction          : 0.63
% 49.73/39.15  MUC search           : 0.00
% 49.73/39.15  Cooper               : 0.00
% 49.73/39.15  Total                : 38.45
% 49.73/39.15  Index Insertion      : 0.00
% 49.73/39.15  Index Deletion       : 0.00
% 49.73/39.15  Index Matching       : 0.00
% 49.73/39.15  BG Taut test         : 0.00
%------------------------------------------------------------------------------
