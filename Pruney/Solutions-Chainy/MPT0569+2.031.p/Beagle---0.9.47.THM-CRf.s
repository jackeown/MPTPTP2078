%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:01:39 EST 2020

% Result     : Theorem 18.36s
% Output     : CNFRefutation 18.36s
% Verified   : 
% Statistics : Number of formulae       :   71 (  91 expanded)
%              Number of leaves         :   39 (  51 expanded)
%              Depth                    :    9
%              Number of atoms          :   89 ( 147 expanded)
%              Number of equality atoms :   12 (  24 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k2_relat_1 > k1_tarski > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_6 > #skF_3 > #skF_9 > #skF_7 > #skF_8 > #skF_1 > #skF_5 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i ) > $i )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

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

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_112,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ( k10_relat_1(B,A) = k1_xboole_0
        <=> r1_xboole_0(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t173_relat_1)).

tff(f_51,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_97,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k10_relat_1(C,B))
      <=> ? [D] :
            ( r2_hidden(D,k2_relat_1(C))
            & r2_hidden(k4_tarski(A,D),C)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t166_relat_1)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

tff(f_55,axiom,(
    ! [A] : k4_xboole_0(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).

tff(f_76,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k4_xboole_0(B,k1_tarski(C)))
    <=> ( r2_hidden(A,B)
        & A != C ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_zfmisc_1)).

tff(f_86,axiom,(
    ! [A,B] :
      ( B = k2_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(D,C),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_relat_1)).

tff(c_68,plain,
    ( k10_relat_1('#skF_9','#skF_8') = k1_xboole_0
    | r1_xboole_0(k2_relat_1('#skF_9'),'#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_135,plain,(
    r1_xboole_0(k2_relat_1('#skF_9'),'#skF_8') ),
    inference(splitLeft,[status(thm)],[c_68])).

tff(c_62,plain,
    ( ~ r1_xboole_0(k2_relat_1('#skF_9'),'#skF_8')
    | k10_relat_1('#skF_9','#skF_8') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_162,plain,(
    k10_relat_1('#skF_9','#skF_8') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_135,c_62])).

tff(c_8,plain,(
    ! [A_6] :
      ( r2_hidden('#skF_2'(A_6),A_6)
      | k1_xboole_0 = A_6 ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_60,plain,(
    v1_relat_1('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_50,plain,(
    ! [A_63,B_64,C_65] :
      ( r2_hidden('#skF_7'(A_63,B_64,C_65),B_64)
      | ~ r2_hidden(A_63,k10_relat_1(C_65,B_64))
      | ~ v1_relat_1(C_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_447,plain,(
    ! [A_136,B_137,C_138] :
      ( r2_hidden('#skF_7'(A_136,B_137,C_138),k2_relat_1(C_138))
      | ~ r2_hidden(A_136,k10_relat_1(C_138,B_137))
      | ~ v1_relat_1(C_138) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_177,plain,(
    ! [A_92,B_93,C_94] :
      ( ~ r1_xboole_0(A_92,B_93)
      | ~ r2_hidden(C_94,B_93)
      | ~ r2_hidden(C_94,A_92) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_186,plain,(
    ! [C_94] :
      ( ~ r2_hidden(C_94,'#skF_8')
      | ~ r2_hidden(C_94,k2_relat_1('#skF_9')) ) ),
    inference(resolution,[status(thm)],[c_135,c_177])).

tff(c_451,plain,(
    ! [A_136,B_137] :
      ( ~ r2_hidden('#skF_7'(A_136,B_137,'#skF_9'),'#skF_8')
      | ~ r2_hidden(A_136,k10_relat_1('#skF_9',B_137))
      | ~ v1_relat_1('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_447,c_186])).

tff(c_964,plain,(
    ! [A_183,B_184] :
      ( ~ r2_hidden('#skF_7'(A_183,B_184,'#skF_9'),'#skF_8')
      | ~ r2_hidden(A_183,k10_relat_1('#skF_9',B_184)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_451])).

tff(c_968,plain,(
    ! [A_63] :
      ( ~ r2_hidden(A_63,k10_relat_1('#skF_9','#skF_8'))
      | ~ v1_relat_1('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_50,c_964])).

tff(c_972,plain,(
    ! [A_185] : ~ r2_hidden(A_185,k10_relat_1('#skF_9','#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_968])).

tff(c_1000,plain,(
    k10_relat_1('#skF_9','#skF_8') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_8,c_972])).

tff(c_1010,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_162,c_1000])).

tff(c_1012,plain,(
    ~ r1_xboole_0(k2_relat_1('#skF_9'),'#skF_8') ),
    inference(splitRight,[status(thm)],[c_68])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_12,plain,(
    ! [A_10] : k4_xboole_0(k1_xboole_0,A_10) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_85,plain,(
    ! [C_74,B_75] : ~ r2_hidden(C_74,k4_xboole_0(B_75,k1_tarski(C_74))) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_88,plain,(
    ! [C_74] : ~ r2_hidden(C_74,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_85])).

tff(c_1011,plain,(
    k10_relat_1('#skF_9','#skF_8') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_68])).

tff(c_36,plain,(
    ! [A_44,C_59] :
      ( r2_hidden(k4_tarski('#skF_6'(A_44,k2_relat_1(A_44),C_59),C_59),A_44)
      | ~ r2_hidden(C_59,k2_relat_1(A_44)) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_1950,plain,(
    ! [A_297,C_298,B_299,D_300] :
      ( r2_hidden(A_297,k10_relat_1(C_298,B_299))
      | ~ r2_hidden(D_300,B_299)
      | ~ r2_hidden(k4_tarski(A_297,D_300),C_298)
      | ~ r2_hidden(D_300,k2_relat_1(C_298))
      | ~ v1_relat_1(C_298) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_7775,plain,(
    ! [A_588,C_589,B_590,A_591] :
      ( r2_hidden(A_588,k10_relat_1(C_589,B_590))
      | ~ r2_hidden(k4_tarski(A_588,'#skF_1'(A_591,B_590)),C_589)
      | ~ r2_hidden('#skF_1'(A_591,B_590),k2_relat_1(C_589))
      | ~ v1_relat_1(C_589)
      | r1_xboole_0(A_591,B_590) ) ),
    inference(resolution,[status(thm)],[c_4,c_1950])).

tff(c_31411,plain,(
    ! [A_23900,A_23901,B_23902] :
      ( r2_hidden('#skF_6'(A_23900,k2_relat_1(A_23900),'#skF_1'(A_23901,B_23902)),k10_relat_1(A_23900,B_23902))
      | ~ v1_relat_1(A_23900)
      | r1_xboole_0(A_23901,B_23902)
      | ~ r2_hidden('#skF_1'(A_23901,B_23902),k2_relat_1(A_23900)) ) ),
    inference(resolution,[status(thm)],[c_36,c_7775])).

tff(c_31656,plain,(
    ! [A_23901] :
      ( r2_hidden('#skF_6'('#skF_9',k2_relat_1('#skF_9'),'#skF_1'(A_23901,'#skF_8')),k1_xboole_0)
      | ~ v1_relat_1('#skF_9')
      | r1_xboole_0(A_23901,'#skF_8')
      | ~ r2_hidden('#skF_1'(A_23901,'#skF_8'),k2_relat_1('#skF_9')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1011,c_31411])).

tff(c_31685,plain,(
    ! [A_23901] :
      ( r2_hidden('#skF_6'('#skF_9',k2_relat_1('#skF_9'),'#skF_1'(A_23901,'#skF_8')),k1_xboole_0)
      | r1_xboole_0(A_23901,'#skF_8')
      | ~ r2_hidden('#skF_1'(A_23901,'#skF_8'),k2_relat_1('#skF_9')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_31656])).

tff(c_31687,plain,(
    ! [A_23967] :
      ( r1_xboole_0(A_23967,'#skF_8')
      | ~ r2_hidden('#skF_1'(A_23967,'#skF_8'),k2_relat_1('#skF_9')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_88,c_31685])).

tff(c_31702,plain,(
    r1_xboole_0(k2_relat_1('#skF_9'),'#skF_8') ),
    inference(resolution,[status(thm)],[c_6,c_31687])).

tff(c_31708,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1012,c_1012,c_31702])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 15:01:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 18.36/8.66  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 18.36/8.67  
% 18.36/8.67  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 18.36/8.67  %$ r2_hidden > r1_xboole_0 > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k2_relat_1 > k1_tarski > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_6 > #skF_3 > #skF_9 > #skF_7 > #skF_8 > #skF_1 > #skF_5 > #skF_4
% 18.36/8.67  
% 18.36/8.67  %Foreground sorts:
% 18.36/8.67  
% 18.36/8.67  
% 18.36/8.67  %Background operators:
% 18.36/8.67  
% 18.36/8.67  
% 18.36/8.67  %Foreground operators:
% 18.36/8.67  tff('#skF_2', type, '#skF_2': $i > $i).
% 18.36/8.67  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 18.36/8.67  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 18.36/8.67  tff('#skF_6', type, '#skF_6': ($i * $i * $i) > $i).
% 18.36/8.67  tff(k1_tarski, type, k1_tarski: $i > $i).
% 18.36/8.67  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 18.36/8.67  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 18.36/8.67  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 18.36/8.67  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 18.36/8.67  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 18.36/8.67  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 18.36/8.67  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 18.36/8.67  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 18.36/8.67  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 18.36/8.67  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 18.36/8.67  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 18.36/8.67  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 18.36/8.67  tff('#skF_9', type, '#skF_9': $i).
% 18.36/8.67  tff('#skF_7', type, '#skF_7': ($i * $i * $i) > $i).
% 18.36/8.67  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 18.36/8.67  tff('#skF_8', type, '#skF_8': $i).
% 18.36/8.67  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 18.36/8.67  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 18.36/8.67  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 18.36/8.67  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 18.36/8.67  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 18.36/8.67  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 18.36/8.67  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 18.36/8.67  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 18.36/8.67  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 18.36/8.67  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 18.36/8.67  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 18.36/8.67  
% 18.36/8.68  tff(f_112, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => ((k10_relat_1(B, A) = k1_xboole_0) <=> r1_xboole_0(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t173_relat_1)).
% 18.36/8.68  tff(f_51, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 18.36/8.68  tff(f_97, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k10_relat_1(C, B)) <=> (?[D]: ((r2_hidden(D, k2_relat_1(C)) & r2_hidden(k4_tarski(A, D), C)) & r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t166_relat_1)).
% 18.36/8.68  tff(f_43, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 18.36/8.68  tff(f_55, axiom, (![A]: (k4_xboole_0(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_boole)).
% 18.36/8.68  tff(f_76, axiom, (![A, B, C]: (r2_hidden(A, k4_xboole_0(B, k1_tarski(C))) <=> (r2_hidden(A, B) & ~(A = C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_zfmisc_1)).
% 18.36/8.68  tff(f_86, axiom, (![A, B]: ((B = k2_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(D, C), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_relat_1)).
% 18.36/8.68  tff(c_68, plain, (k10_relat_1('#skF_9', '#skF_8')=k1_xboole_0 | r1_xboole_0(k2_relat_1('#skF_9'), '#skF_8')), inference(cnfTransformation, [status(thm)], [f_112])).
% 18.36/8.68  tff(c_135, plain, (r1_xboole_0(k2_relat_1('#skF_9'), '#skF_8')), inference(splitLeft, [status(thm)], [c_68])).
% 18.36/8.68  tff(c_62, plain, (~r1_xboole_0(k2_relat_1('#skF_9'), '#skF_8') | k10_relat_1('#skF_9', '#skF_8')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_112])).
% 18.36/8.68  tff(c_162, plain, (k10_relat_1('#skF_9', '#skF_8')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_135, c_62])).
% 18.36/8.68  tff(c_8, plain, (![A_6]: (r2_hidden('#skF_2'(A_6), A_6) | k1_xboole_0=A_6)), inference(cnfTransformation, [status(thm)], [f_51])).
% 18.36/8.68  tff(c_60, plain, (v1_relat_1('#skF_9')), inference(cnfTransformation, [status(thm)], [f_112])).
% 18.36/8.68  tff(c_50, plain, (![A_63, B_64, C_65]: (r2_hidden('#skF_7'(A_63, B_64, C_65), B_64) | ~r2_hidden(A_63, k10_relat_1(C_65, B_64)) | ~v1_relat_1(C_65))), inference(cnfTransformation, [status(thm)], [f_97])).
% 18.36/8.68  tff(c_447, plain, (![A_136, B_137, C_138]: (r2_hidden('#skF_7'(A_136, B_137, C_138), k2_relat_1(C_138)) | ~r2_hidden(A_136, k10_relat_1(C_138, B_137)) | ~v1_relat_1(C_138))), inference(cnfTransformation, [status(thm)], [f_97])).
% 18.36/8.68  tff(c_177, plain, (![A_92, B_93, C_94]: (~r1_xboole_0(A_92, B_93) | ~r2_hidden(C_94, B_93) | ~r2_hidden(C_94, A_92))), inference(cnfTransformation, [status(thm)], [f_43])).
% 18.36/8.68  tff(c_186, plain, (![C_94]: (~r2_hidden(C_94, '#skF_8') | ~r2_hidden(C_94, k2_relat_1('#skF_9')))), inference(resolution, [status(thm)], [c_135, c_177])).
% 18.36/8.68  tff(c_451, plain, (![A_136, B_137]: (~r2_hidden('#skF_7'(A_136, B_137, '#skF_9'), '#skF_8') | ~r2_hidden(A_136, k10_relat_1('#skF_9', B_137)) | ~v1_relat_1('#skF_9'))), inference(resolution, [status(thm)], [c_447, c_186])).
% 18.36/8.68  tff(c_964, plain, (![A_183, B_184]: (~r2_hidden('#skF_7'(A_183, B_184, '#skF_9'), '#skF_8') | ~r2_hidden(A_183, k10_relat_1('#skF_9', B_184)))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_451])).
% 18.36/8.68  tff(c_968, plain, (![A_63]: (~r2_hidden(A_63, k10_relat_1('#skF_9', '#skF_8')) | ~v1_relat_1('#skF_9'))), inference(resolution, [status(thm)], [c_50, c_964])).
% 18.36/8.68  tff(c_972, plain, (![A_185]: (~r2_hidden(A_185, k10_relat_1('#skF_9', '#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_968])).
% 18.36/8.68  tff(c_1000, plain, (k10_relat_1('#skF_9', '#skF_8')=k1_xboole_0), inference(resolution, [status(thm)], [c_8, c_972])).
% 18.36/8.68  tff(c_1010, plain, $false, inference(negUnitSimplification, [status(thm)], [c_162, c_1000])).
% 18.36/8.68  tff(c_1012, plain, (~r1_xboole_0(k2_relat_1('#skF_9'), '#skF_8')), inference(splitRight, [status(thm)], [c_68])).
% 18.36/8.68  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_43])).
% 18.36/8.68  tff(c_12, plain, (![A_10]: (k4_xboole_0(k1_xboole_0, A_10)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_55])).
% 18.36/8.68  tff(c_85, plain, (![C_74, B_75]: (~r2_hidden(C_74, k4_xboole_0(B_75, k1_tarski(C_74))))), inference(cnfTransformation, [status(thm)], [f_76])).
% 18.36/8.68  tff(c_88, plain, (![C_74]: (~r2_hidden(C_74, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_12, c_85])).
% 18.36/8.68  tff(c_1011, plain, (k10_relat_1('#skF_9', '#skF_8')=k1_xboole_0), inference(splitRight, [status(thm)], [c_68])).
% 18.36/8.68  tff(c_36, plain, (![A_44, C_59]: (r2_hidden(k4_tarski('#skF_6'(A_44, k2_relat_1(A_44), C_59), C_59), A_44) | ~r2_hidden(C_59, k2_relat_1(A_44)))), inference(cnfTransformation, [status(thm)], [f_86])).
% 18.36/8.68  tff(c_4, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_43])).
% 18.36/8.68  tff(c_1950, plain, (![A_297, C_298, B_299, D_300]: (r2_hidden(A_297, k10_relat_1(C_298, B_299)) | ~r2_hidden(D_300, B_299) | ~r2_hidden(k4_tarski(A_297, D_300), C_298) | ~r2_hidden(D_300, k2_relat_1(C_298)) | ~v1_relat_1(C_298))), inference(cnfTransformation, [status(thm)], [f_97])).
% 18.36/8.68  tff(c_7775, plain, (![A_588, C_589, B_590, A_591]: (r2_hidden(A_588, k10_relat_1(C_589, B_590)) | ~r2_hidden(k4_tarski(A_588, '#skF_1'(A_591, B_590)), C_589) | ~r2_hidden('#skF_1'(A_591, B_590), k2_relat_1(C_589)) | ~v1_relat_1(C_589) | r1_xboole_0(A_591, B_590))), inference(resolution, [status(thm)], [c_4, c_1950])).
% 18.36/8.68  tff(c_31411, plain, (![A_23900, A_23901, B_23902]: (r2_hidden('#skF_6'(A_23900, k2_relat_1(A_23900), '#skF_1'(A_23901, B_23902)), k10_relat_1(A_23900, B_23902)) | ~v1_relat_1(A_23900) | r1_xboole_0(A_23901, B_23902) | ~r2_hidden('#skF_1'(A_23901, B_23902), k2_relat_1(A_23900)))), inference(resolution, [status(thm)], [c_36, c_7775])).
% 18.36/8.68  tff(c_31656, plain, (![A_23901]: (r2_hidden('#skF_6'('#skF_9', k2_relat_1('#skF_9'), '#skF_1'(A_23901, '#skF_8')), k1_xboole_0) | ~v1_relat_1('#skF_9') | r1_xboole_0(A_23901, '#skF_8') | ~r2_hidden('#skF_1'(A_23901, '#skF_8'), k2_relat_1('#skF_9')))), inference(superposition, [status(thm), theory('equality')], [c_1011, c_31411])).
% 18.36/8.68  tff(c_31685, plain, (![A_23901]: (r2_hidden('#skF_6'('#skF_9', k2_relat_1('#skF_9'), '#skF_1'(A_23901, '#skF_8')), k1_xboole_0) | r1_xboole_0(A_23901, '#skF_8') | ~r2_hidden('#skF_1'(A_23901, '#skF_8'), k2_relat_1('#skF_9')))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_31656])).
% 18.36/8.68  tff(c_31687, plain, (![A_23967]: (r1_xboole_0(A_23967, '#skF_8') | ~r2_hidden('#skF_1'(A_23967, '#skF_8'), k2_relat_1('#skF_9')))), inference(negUnitSimplification, [status(thm)], [c_88, c_31685])).
% 18.36/8.68  tff(c_31702, plain, (r1_xboole_0(k2_relat_1('#skF_9'), '#skF_8')), inference(resolution, [status(thm)], [c_6, c_31687])).
% 18.36/8.68  tff(c_31708, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1012, c_1012, c_31702])).
% 18.36/8.68  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 18.36/8.68  
% 18.36/8.68  Inference rules
% 18.36/8.68  ----------------------
% 18.36/8.68  #Ref     : 0
% 18.36/8.68  #Sup     : 8171
% 18.36/8.68  #Fact    : 0
% 18.36/8.68  #Define  : 0
% 18.36/8.68  #Split   : 14
% 18.36/8.68  #Chain   : 0
% 18.36/8.68  #Close   : 0
% 18.36/8.68  
% 18.36/8.68  Ordering : KBO
% 18.36/8.68  
% 18.36/8.68  Simplification rules
% 18.36/8.68  ----------------------
% 18.36/8.68  #Subsume      : 2673
% 18.36/8.68  #Demod        : 3491
% 18.36/8.68  #Tautology    : 1143
% 18.36/8.68  #SimpNegUnit  : 495
% 18.36/8.68  #BackRed      : 2
% 18.36/8.68  
% 18.36/8.68  #Partial instantiations: 9256
% 18.36/8.68  #Strategies tried      : 1
% 18.36/8.68  
% 18.36/8.68  Timing (in seconds)
% 18.36/8.68  ----------------------
% 18.36/8.68  Preprocessing        : 0.37
% 18.36/8.68  Parsing              : 0.19
% 18.36/8.69  CNF conversion       : 0.03
% 18.36/8.69  Main loop            : 7.51
% 18.36/8.69  Inferencing          : 1.34
% 18.36/8.69  Reduction            : 1.26
% 18.36/8.69  Demodulation         : 0.81
% 18.36/8.69  BG Simplification    : 0.12
% 18.36/8.69  Subsumption          : 4.51
% 18.36/8.69  Abstraction          : 0.19
% 18.36/8.69  MUC search           : 0.00
% 18.36/8.69  Cooper               : 0.00
% 18.36/8.69  Total                : 7.90
% 18.36/8.69  Index Insertion      : 0.00
% 18.36/8.69  Index Deletion       : 0.00
% 18.36/8.69  Index Matching       : 0.00
% 18.36/8.69  BG Taut test         : 0.00
%------------------------------------------------------------------------------
