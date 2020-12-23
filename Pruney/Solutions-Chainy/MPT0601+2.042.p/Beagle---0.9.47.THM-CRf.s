%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:02:19 EST 2020

% Result     : Theorem 6.59s
% Output     : CNFRefutation 6.59s
% Verified   : 
% Statistics : Number of formulae       :   76 ( 156 expanded)
%              Number of leaves         :   26 (  63 expanded)
%              Depth                    :    9
%              Number of atoms          :  109 ( 288 expanded)
%              Number of equality atoms :   13 (  38 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > v1_xboole_0 > v1_relat_1 > k4_tarski > k11_relat_1 > #nlpp > k1_relat_1 > k1_xboole_0 > #skF_6 > #skF_1 > #skF_7 > #skF_3 > #skF_8 > #skF_2 > #skF_5 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(k11_relat_1,type,(
    k11_relat_1: ( $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_8',type,(
    '#skF_8': $i )).

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

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_55,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_53,axiom,(
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

tff(f_63,axiom,(
    ! [A,B] :
      ( B = k1_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(C,D),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_1)).

tff(f_35,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_77,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ( r2_hidden(A,k1_relat_1(B))
        <=> k11_relat_1(B,A) != k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t205_relat_1)).

tff(f_69,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(k4_tarski(A,B),C)
      <=> r2_hidden(B,k11_relat_1(C,A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t204_relat_1)).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_14,plain,(
    ! [A_11] : r1_xboole_0(A_11,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_1987,plain,(
    ! [A_153,B_154,C_155] :
      ( ~ r1_xboole_0(A_153,B_154)
      | ~ r2_hidden(C_155,B_154)
      | ~ r2_hidden(C_155,A_153) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_1998,plain,(
    ! [C_158,A_159] :
      ( ~ r2_hidden(C_158,k1_xboole_0)
      | ~ r2_hidden(C_158,A_159) ) ),
    inference(resolution,[status(thm)],[c_14,c_1987])).

tff(c_2011,plain,(
    ! [A_159] :
      ( ~ r2_hidden('#skF_1'(k1_xboole_0),A_159)
      | v1_xboole_0(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_4,c_1998])).

tff(c_2013,plain,(
    ! [A_160] : ~ r2_hidden('#skF_1'(k1_xboole_0),A_160) ),
    inference(splitLeft,[status(thm)],[c_2011])).

tff(c_2018,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_4,c_2013])).

tff(c_2106,plain,(
    ! [C_182,A_183] :
      ( r2_hidden(k4_tarski(C_182,'#skF_6'(A_183,k1_relat_1(A_183),C_182)),A_183)
      | ~ r2_hidden(C_182,k1_relat_1(A_183)) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_2128,plain,(
    ! [A_184,C_185] :
      ( ~ v1_xboole_0(A_184)
      | ~ r2_hidden(C_185,k1_relat_1(A_184)) ) ),
    inference(resolution,[status(thm)],[c_2106,c_2])).

tff(c_2158,plain,(
    ! [A_186] :
      ( ~ v1_xboole_0(A_186)
      | v1_xboole_0(k1_relat_1(A_186)) ) ),
    inference(resolution,[status(thm)],[c_4,c_2128])).

tff(c_6,plain,(
    ! [A_5] :
      ( k1_xboole_0 = A_5
      | ~ v1_xboole_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_2170,plain,(
    ! [A_187] :
      ( k1_relat_1(A_187) = k1_xboole_0
      | ~ v1_xboole_0(A_187) ) ),
    inference(resolution,[status(thm)],[c_2158,c_6])).

tff(c_2182,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2018,c_2170])).

tff(c_2127,plain,(
    ! [A_183,C_182] :
      ( ~ v1_xboole_0(A_183)
      | ~ r2_hidden(C_182,k1_relat_1(A_183)) ) ),
    inference(resolution,[status(thm)],[c_2106,c_2])).

tff(c_2189,plain,(
    ! [C_182] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | ~ r2_hidden(C_182,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2182,c_2127])).

tff(c_2198,plain,(
    ! [C_182] : ~ r2_hidden(C_182,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2018,c_2189])).

tff(c_34,plain,
    ( k11_relat_1('#skF_8','#skF_7') = k1_xboole_0
    | ~ r2_hidden('#skF_7',k1_relat_1('#skF_8')) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_49,plain,(
    ~ r2_hidden('#skF_7',k1_relat_1('#skF_8')) ),
    inference(splitLeft,[status(thm)],[c_34])).

tff(c_40,plain,
    ( r2_hidden('#skF_7',k1_relat_1('#skF_8'))
    | k11_relat_1('#skF_8','#skF_7') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_56,plain,(
    k11_relat_1('#skF_8','#skF_7') != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_49,c_40])).

tff(c_32,plain,(
    v1_relat_1('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_111,plain,(
    ! [A_58,B_59,C_60] :
      ( r2_hidden(k4_tarski(A_58,B_59),C_60)
      | ~ r2_hidden(B_59,k11_relat_1(C_60,A_58))
      | ~ v1_relat_1(C_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_18,plain,(
    ! [C_27,A_12,D_30] :
      ( r2_hidden(C_27,k1_relat_1(A_12))
      | ~ r2_hidden(k4_tarski(C_27,D_30),A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_1380,plain,(
    ! [A_134,C_135,B_136] :
      ( r2_hidden(A_134,k1_relat_1(C_135))
      | ~ r2_hidden(B_136,k11_relat_1(C_135,A_134))
      | ~ v1_relat_1(C_135) ) ),
    inference(resolution,[status(thm)],[c_111,c_18])).

tff(c_1851,plain,(
    ! [A_145,C_146] :
      ( r2_hidden(A_145,k1_relat_1(C_146))
      | ~ v1_relat_1(C_146)
      | v1_xboole_0(k11_relat_1(C_146,A_145)) ) ),
    inference(resolution,[status(thm)],[c_4,c_1380])).

tff(c_1895,plain,
    ( ~ v1_relat_1('#skF_8')
    | v1_xboole_0(k11_relat_1('#skF_8','#skF_7')) ),
    inference(resolution,[status(thm)],[c_1851,c_49])).

tff(c_1930,plain,(
    v1_xboole_0(k11_relat_1('#skF_8','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_1895])).

tff(c_1953,plain,(
    k11_relat_1('#skF_8','#skF_7') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1930,c_6])).

tff(c_1963,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_1953])).

tff(c_1965,plain,(
    r2_hidden('#skF_7',k1_relat_1('#skF_8')) ),
    inference(splitRight,[status(thm)],[c_34])).

tff(c_1964,plain,(
    k11_relat_1('#skF_8','#skF_7') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_34])).

tff(c_30,plain,(
    ! [B_32,C_33,A_31] :
      ( r2_hidden(B_32,k11_relat_1(C_33,A_31))
      | ~ r2_hidden(k4_tarski(A_31,B_32),C_33)
      | ~ v1_relat_1(C_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_5230,plain,(
    ! [A_281,C_282] :
      ( r2_hidden('#skF_6'(A_281,k1_relat_1(A_281),C_282),k11_relat_1(A_281,C_282))
      | ~ v1_relat_1(A_281)
      | ~ r2_hidden(C_282,k1_relat_1(A_281)) ) ),
    inference(resolution,[status(thm)],[c_2106,c_30])).

tff(c_5271,plain,
    ( r2_hidden('#skF_6'('#skF_8',k1_relat_1('#skF_8'),'#skF_7'),k1_xboole_0)
    | ~ v1_relat_1('#skF_8')
    | ~ r2_hidden('#skF_7',k1_relat_1('#skF_8')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1964,c_5230])).

tff(c_5278,plain,(
    r2_hidden('#skF_6'('#skF_8',k1_relat_1('#skF_8'),'#skF_7'),k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1965,c_32,c_5271])).

tff(c_5280,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2198,c_5278])).

tff(c_5281,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_2011])).

tff(c_5368,plain,(
    ! [C_304,A_305] :
      ( r2_hidden(k4_tarski(C_304,'#skF_6'(A_305,k1_relat_1(A_305),C_304)),A_305)
      | ~ r2_hidden(C_304,k1_relat_1(A_305)) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_5390,plain,(
    ! [A_306,C_307] :
      ( ~ v1_xboole_0(A_306)
      | ~ r2_hidden(C_307,k1_relat_1(A_306)) ) ),
    inference(resolution,[status(thm)],[c_5368,c_2])).

tff(c_5420,plain,(
    ! [A_308] :
      ( ~ v1_xboole_0(A_308)
      | v1_xboole_0(k1_relat_1(A_308)) ) ),
    inference(resolution,[status(thm)],[c_4,c_5390])).

tff(c_5432,plain,(
    ! [A_309] :
      ( k1_relat_1(A_309) = k1_xboole_0
      | ~ v1_xboole_0(A_309) ) ),
    inference(resolution,[status(thm)],[c_5420,c_6])).

tff(c_5444,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_5281,c_5432])).

tff(c_5389,plain,(
    ! [A_305,C_304] :
      ( ~ v1_xboole_0(A_305)
      | ~ r2_hidden(C_304,k1_relat_1(A_305)) ) ),
    inference(resolution,[status(thm)],[c_5368,c_2])).

tff(c_5451,plain,(
    ! [C_304] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | ~ r2_hidden(C_304,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5444,c_5389])).

tff(c_5460,plain,(
    ! [C_304] : ~ r2_hidden(C_304,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5281,c_5451])).

tff(c_8249,plain,(
    ! [A_400,C_401] :
      ( r2_hidden('#skF_6'(A_400,k1_relat_1(A_400),C_401),k11_relat_1(A_400,C_401))
      | ~ v1_relat_1(A_400)
      | ~ r2_hidden(C_401,k1_relat_1(A_400)) ) ),
    inference(resolution,[status(thm)],[c_5368,c_30])).

tff(c_8284,plain,
    ( r2_hidden('#skF_6'('#skF_8',k1_relat_1('#skF_8'),'#skF_7'),k1_xboole_0)
    | ~ v1_relat_1('#skF_8')
    | ~ r2_hidden('#skF_7',k1_relat_1('#skF_8')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1964,c_8249])).

tff(c_8290,plain,(
    r2_hidden('#skF_6'('#skF_8',k1_relat_1('#skF_8'),'#skF_7'),k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1965,c_32,c_8284])).

tff(c_8292,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_5460,c_8290])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n018.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 13:15:56 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.59/2.41  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.59/2.42  
% 6.59/2.42  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.59/2.42  %$ r2_hidden > r1_xboole_0 > v1_xboole_0 > v1_relat_1 > k4_tarski > k11_relat_1 > #nlpp > k1_relat_1 > k1_xboole_0 > #skF_6 > #skF_1 > #skF_7 > #skF_3 > #skF_8 > #skF_2 > #skF_5 > #skF_4
% 6.59/2.42  
% 6.59/2.42  %Foreground sorts:
% 6.59/2.42  
% 6.59/2.42  
% 6.59/2.42  %Background operators:
% 6.59/2.42  
% 6.59/2.42  
% 6.59/2.42  %Foreground operators:
% 6.59/2.42  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.59/2.42  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 6.59/2.42  tff('#skF_6', type, '#skF_6': ($i * $i * $i) > $i).
% 6.59/2.42  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 6.59/2.42  tff('#skF_1', type, '#skF_1': $i > $i).
% 6.59/2.42  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 6.59/2.42  tff('#skF_7', type, '#skF_7': $i).
% 6.59/2.42  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 6.59/2.42  tff(k11_relat_1, type, k11_relat_1: ($i * $i) > $i).
% 6.59/2.42  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 6.59/2.42  tff('#skF_8', type, '#skF_8': $i).
% 6.59/2.42  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.59/2.42  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 6.59/2.42  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.59/2.42  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 6.59/2.42  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 6.59/2.42  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 6.59/2.42  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 6.59/2.42  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 6.59/2.42  
% 6.59/2.43  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 6.59/2.43  tff(f_55, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 6.59/2.43  tff(f_53, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 6.59/2.43  tff(f_63, axiom, (![A, B]: ((B = k1_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(C, D), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_relat_1)).
% 6.59/2.43  tff(f_35, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 6.59/2.43  tff(f_77, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => (r2_hidden(A, k1_relat_1(B)) <=> ~(k11_relat_1(B, A) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t205_relat_1)).
% 6.59/2.43  tff(f_69, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(k4_tarski(A, B), C) <=> r2_hidden(B, k11_relat_1(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t204_relat_1)).
% 6.59/2.43  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 6.59/2.43  tff(c_14, plain, (![A_11]: (r1_xboole_0(A_11, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_55])).
% 6.59/2.43  tff(c_1987, plain, (![A_153, B_154, C_155]: (~r1_xboole_0(A_153, B_154) | ~r2_hidden(C_155, B_154) | ~r2_hidden(C_155, A_153))), inference(cnfTransformation, [status(thm)], [f_53])).
% 6.59/2.43  tff(c_1998, plain, (![C_158, A_159]: (~r2_hidden(C_158, k1_xboole_0) | ~r2_hidden(C_158, A_159))), inference(resolution, [status(thm)], [c_14, c_1987])).
% 6.59/2.43  tff(c_2011, plain, (![A_159]: (~r2_hidden('#skF_1'(k1_xboole_0), A_159) | v1_xboole_0(k1_xboole_0))), inference(resolution, [status(thm)], [c_4, c_1998])).
% 6.59/2.43  tff(c_2013, plain, (![A_160]: (~r2_hidden('#skF_1'(k1_xboole_0), A_160))), inference(splitLeft, [status(thm)], [c_2011])).
% 6.59/2.43  tff(c_2018, plain, (v1_xboole_0(k1_xboole_0)), inference(resolution, [status(thm)], [c_4, c_2013])).
% 6.59/2.43  tff(c_2106, plain, (![C_182, A_183]: (r2_hidden(k4_tarski(C_182, '#skF_6'(A_183, k1_relat_1(A_183), C_182)), A_183) | ~r2_hidden(C_182, k1_relat_1(A_183)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 6.59/2.43  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 6.59/2.43  tff(c_2128, plain, (![A_184, C_185]: (~v1_xboole_0(A_184) | ~r2_hidden(C_185, k1_relat_1(A_184)))), inference(resolution, [status(thm)], [c_2106, c_2])).
% 6.59/2.43  tff(c_2158, plain, (![A_186]: (~v1_xboole_0(A_186) | v1_xboole_0(k1_relat_1(A_186)))), inference(resolution, [status(thm)], [c_4, c_2128])).
% 6.59/2.43  tff(c_6, plain, (![A_5]: (k1_xboole_0=A_5 | ~v1_xboole_0(A_5))), inference(cnfTransformation, [status(thm)], [f_35])).
% 6.59/2.43  tff(c_2170, plain, (![A_187]: (k1_relat_1(A_187)=k1_xboole_0 | ~v1_xboole_0(A_187))), inference(resolution, [status(thm)], [c_2158, c_6])).
% 6.59/2.43  tff(c_2182, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_2018, c_2170])).
% 6.59/2.43  tff(c_2127, plain, (![A_183, C_182]: (~v1_xboole_0(A_183) | ~r2_hidden(C_182, k1_relat_1(A_183)))), inference(resolution, [status(thm)], [c_2106, c_2])).
% 6.59/2.43  tff(c_2189, plain, (![C_182]: (~v1_xboole_0(k1_xboole_0) | ~r2_hidden(C_182, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_2182, c_2127])).
% 6.59/2.43  tff(c_2198, plain, (![C_182]: (~r2_hidden(C_182, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_2018, c_2189])).
% 6.59/2.43  tff(c_34, plain, (k11_relat_1('#skF_8', '#skF_7')=k1_xboole_0 | ~r2_hidden('#skF_7', k1_relat_1('#skF_8'))), inference(cnfTransformation, [status(thm)], [f_77])).
% 6.59/2.43  tff(c_49, plain, (~r2_hidden('#skF_7', k1_relat_1('#skF_8'))), inference(splitLeft, [status(thm)], [c_34])).
% 6.59/2.43  tff(c_40, plain, (r2_hidden('#skF_7', k1_relat_1('#skF_8')) | k11_relat_1('#skF_8', '#skF_7')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_77])).
% 6.59/2.43  tff(c_56, plain, (k11_relat_1('#skF_8', '#skF_7')!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_49, c_40])).
% 6.59/2.43  tff(c_32, plain, (v1_relat_1('#skF_8')), inference(cnfTransformation, [status(thm)], [f_77])).
% 6.59/2.43  tff(c_111, plain, (![A_58, B_59, C_60]: (r2_hidden(k4_tarski(A_58, B_59), C_60) | ~r2_hidden(B_59, k11_relat_1(C_60, A_58)) | ~v1_relat_1(C_60))), inference(cnfTransformation, [status(thm)], [f_69])).
% 6.59/2.43  tff(c_18, plain, (![C_27, A_12, D_30]: (r2_hidden(C_27, k1_relat_1(A_12)) | ~r2_hidden(k4_tarski(C_27, D_30), A_12))), inference(cnfTransformation, [status(thm)], [f_63])).
% 6.59/2.43  tff(c_1380, plain, (![A_134, C_135, B_136]: (r2_hidden(A_134, k1_relat_1(C_135)) | ~r2_hidden(B_136, k11_relat_1(C_135, A_134)) | ~v1_relat_1(C_135))), inference(resolution, [status(thm)], [c_111, c_18])).
% 6.59/2.43  tff(c_1851, plain, (![A_145, C_146]: (r2_hidden(A_145, k1_relat_1(C_146)) | ~v1_relat_1(C_146) | v1_xboole_0(k11_relat_1(C_146, A_145)))), inference(resolution, [status(thm)], [c_4, c_1380])).
% 6.59/2.43  tff(c_1895, plain, (~v1_relat_1('#skF_8') | v1_xboole_0(k11_relat_1('#skF_8', '#skF_7'))), inference(resolution, [status(thm)], [c_1851, c_49])).
% 6.59/2.43  tff(c_1930, plain, (v1_xboole_0(k11_relat_1('#skF_8', '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_1895])).
% 6.59/2.43  tff(c_1953, plain, (k11_relat_1('#skF_8', '#skF_7')=k1_xboole_0), inference(resolution, [status(thm)], [c_1930, c_6])).
% 6.59/2.43  tff(c_1963, plain, $false, inference(negUnitSimplification, [status(thm)], [c_56, c_1953])).
% 6.59/2.43  tff(c_1965, plain, (r2_hidden('#skF_7', k1_relat_1('#skF_8'))), inference(splitRight, [status(thm)], [c_34])).
% 6.59/2.43  tff(c_1964, plain, (k11_relat_1('#skF_8', '#skF_7')=k1_xboole_0), inference(splitRight, [status(thm)], [c_34])).
% 6.59/2.43  tff(c_30, plain, (![B_32, C_33, A_31]: (r2_hidden(B_32, k11_relat_1(C_33, A_31)) | ~r2_hidden(k4_tarski(A_31, B_32), C_33) | ~v1_relat_1(C_33))), inference(cnfTransformation, [status(thm)], [f_69])).
% 6.59/2.43  tff(c_5230, plain, (![A_281, C_282]: (r2_hidden('#skF_6'(A_281, k1_relat_1(A_281), C_282), k11_relat_1(A_281, C_282)) | ~v1_relat_1(A_281) | ~r2_hidden(C_282, k1_relat_1(A_281)))), inference(resolution, [status(thm)], [c_2106, c_30])).
% 6.59/2.43  tff(c_5271, plain, (r2_hidden('#skF_6'('#skF_8', k1_relat_1('#skF_8'), '#skF_7'), k1_xboole_0) | ~v1_relat_1('#skF_8') | ~r2_hidden('#skF_7', k1_relat_1('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_1964, c_5230])).
% 6.59/2.43  tff(c_5278, plain, (r2_hidden('#skF_6'('#skF_8', k1_relat_1('#skF_8'), '#skF_7'), k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_1965, c_32, c_5271])).
% 6.59/2.43  tff(c_5280, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2198, c_5278])).
% 6.59/2.43  tff(c_5281, plain, (v1_xboole_0(k1_xboole_0)), inference(splitRight, [status(thm)], [c_2011])).
% 6.59/2.43  tff(c_5368, plain, (![C_304, A_305]: (r2_hidden(k4_tarski(C_304, '#skF_6'(A_305, k1_relat_1(A_305), C_304)), A_305) | ~r2_hidden(C_304, k1_relat_1(A_305)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 6.59/2.43  tff(c_5390, plain, (![A_306, C_307]: (~v1_xboole_0(A_306) | ~r2_hidden(C_307, k1_relat_1(A_306)))), inference(resolution, [status(thm)], [c_5368, c_2])).
% 6.59/2.43  tff(c_5420, plain, (![A_308]: (~v1_xboole_0(A_308) | v1_xboole_0(k1_relat_1(A_308)))), inference(resolution, [status(thm)], [c_4, c_5390])).
% 6.59/2.43  tff(c_5432, plain, (![A_309]: (k1_relat_1(A_309)=k1_xboole_0 | ~v1_xboole_0(A_309))), inference(resolution, [status(thm)], [c_5420, c_6])).
% 6.59/2.43  tff(c_5444, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_5281, c_5432])).
% 6.59/2.43  tff(c_5389, plain, (![A_305, C_304]: (~v1_xboole_0(A_305) | ~r2_hidden(C_304, k1_relat_1(A_305)))), inference(resolution, [status(thm)], [c_5368, c_2])).
% 6.59/2.43  tff(c_5451, plain, (![C_304]: (~v1_xboole_0(k1_xboole_0) | ~r2_hidden(C_304, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_5444, c_5389])).
% 6.59/2.43  tff(c_5460, plain, (![C_304]: (~r2_hidden(C_304, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_5281, c_5451])).
% 6.59/2.43  tff(c_8249, plain, (![A_400, C_401]: (r2_hidden('#skF_6'(A_400, k1_relat_1(A_400), C_401), k11_relat_1(A_400, C_401)) | ~v1_relat_1(A_400) | ~r2_hidden(C_401, k1_relat_1(A_400)))), inference(resolution, [status(thm)], [c_5368, c_30])).
% 6.59/2.43  tff(c_8284, plain, (r2_hidden('#skF_6'('#skF_8', k1_relat_1('#skF_8'), '#skF_7'), k1_xboole_0) | ~v1_relat_1('#skF_8') | ~r2_hidden('#skF_7', k1_relat_1('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_1964, c_8249])).
% 6.59/2.43  tff(c_8290, plain, (r2_hidden('#skF_6'('#skF_8', k1_relat_1('#skF_8'), '#skF_7'), k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_1965, c_32, c_8284])).
% 6.59/2.43  tff(c_8292, plain, $false, inference(negUnitSimplification, [status(thm)], [c_5460, c_8290])).
% 6.59/2.43  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.59/2.43  
% 6.59/2.43  Inference rules
% 6.59/2.43  ----------------------
% 6.59/2.43  #Ref     : 0
% 6.59/2.43  #Sup     : 2090
% 6.59/2.43  #Fact    : 0
% 6.59/2.43  #Define  : 0
% 6.59/2.43  #Split   : 8
% 6.59/2.43  #Chain   : 0
% 6.59/2.43  #Close   : 0
% 6.59/2.43  
% 6.59/2.43  Ordering : KBO
% 6.59/2.43  
% 6.59/2.43  Simplification rules
% 6.59/2.43  ----------------------
% 6.59/2.43  #Subsume      : 683
% 6.59/2.43  #Demod        : 1943
% 6.59/2.43  #Tautology    : 805
% 6.59/2.43  #SimpNegUnit  : 38
% 6.59/2.43  #BackRed      : 0
% 6.59/2.43  
% 6.59/2.43  #Partial instantiations: 0
% 6.59/2.43  #Strategies tried      : 1
% 6.59/2.43  
% 6.59/2.43  Timing (in seconds)
% 6.59/2.43  ----------------------
% 6.59/2.44  Preprocessing        : 0.31
% 6.59/2.44  Parsing              : 0.17
% 6.59/2.44  CNF conversion       : 0.03
% 6.59/2.44  Main loop            : 1.29
% 6.59/2.44  Inferencing          : 0.44
% 6.59/2.44  Reduction            : 0.36
% 6.59/2.44  Demodulation         : 0.24
% 6.59/2.44  BG Simplification    : 0.05
% 6.59/2.44  Subsumption          : 0.35
% 6.59/2.44  Abstraction          : 0.07
% 6.59/2.44  MUC search           : 0.00
% 6.59/2.44  Cooper               : 0.00
% 6.59/2.44  Total                : 1.64
% 6.59/2.44  Index Insertion      : 0.00
% 6.59/2.44  Index Deletion       : 0.00
% 6.59/2.44  Index Matching       : 0.00
% 6.59/2.44  BG Taut test         : 0.00
%------------------------------------------------------------------------------
