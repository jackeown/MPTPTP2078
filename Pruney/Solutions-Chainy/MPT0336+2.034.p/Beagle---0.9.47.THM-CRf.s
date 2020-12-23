%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:55:05 EST 2020

% Result     : Theorem 8.42s
% Output     : CNFRefutation 8.42s
% Verified   : 
% Statistics : Number of formulae       :   85 ( 197 expanded)
%              Number of leaves         :   32 (  81 expanded)
%              Depth                    :   14
%              Number of atoms          :  130 ( 453 expanded)
%              Number of equality atoms :   10 (  23 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_6 > #skF_11 > #skF_10 > #skF_2 > #skF_9 > #skF_8 > #skF_3 > #skF_7 > #skF_1 > #skF_5 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_11',type,(
    '#skF_11': $i )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_117,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( r1_tarski(k3_xboole_0(A,B),k1_tarski(D))
          & r2_hidden(D,C)
          & r1_xboole_0(C,B) )
       => r1_xboole_0(k2_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t149_zfmisc_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_95,axiom,(
    ! [A,B,C] :
      ( ~ ( ~ r1_xboole_0(A,k2_xboole_0(B,C))
          & r1_xboole_0(A,B)
          & r1_xboole_0(A,C) )
      & ~ ( ~ ( r1_xboole_0(A,B)
              & r1_xboole_0(A,C) )
          & r1_xboole_0(A,k2_xboole_0(B,C)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_xboole_1)).

tff(f_34,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_65,axiom,(
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

tff(f_102,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

tff(f_79,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( C = k3_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

tff(c_66,plain,(
    r1_xboole_0('#skF_10','#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_87,plain,(
    ! [B_44,A_45] :
      ( r1_xboole_0(B_44,A_45)
      | ~ r1_xboole_0(A_45,B_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_90,plain,(
    r1_xboole_0('#skF_9','#skF_10') ),
    inference(resolution,[status(thm)],[c_66,c_87])).

tff(c_723,plain,(
    ! [A_147,C_148,B_149] :
      ( ~ r1_xboole_0(A_147,C_148)
      | ~ r1_xboole_0(A_147,B_149)
      | r1_xboole_0(A_147,k2_xboole_0(B_149,C_148)) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_28,plain,(
    ! [B_15,A_14] :
      ( r1_xboole_0(B_15,A_14)
      | ~ r1_xboole_0(A_14,B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_1705,plain,(
    ! [B_2187,C_2188,A_2189] :
      ( r1_xboole_0(k2_xboole_0(B_2187,C_2188),A_2189)
      | ~ r1_xboole_0(A_2189,C_2188)
      | ~ r1_xboole_0(A_2189,B_2187) ) ),
    inference(resolution,[status(thm)],[c_723,c_28])).

tff(c_64,plain,(
    ~ r1_xboole_0(k2_xboole_0('#skF_8','#skF_10'),'#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_1720,plain,
    ( ~ r1_xboole_0('#skF_9','#skF_10')
    | ~ r1_xboole_0('#skF_9','#skF_8') ),
    inference(resolution,[status(thm)],[c_1705,c_64])).

tff(c_1728,plain,(
    ~ r1_xboole_0('#skF_9','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_1720])).

tff(c_182,plain,(
    ! [A_69,B_70] :
      ( r2_hidden('#skF_1'(A_69,B_70),A_69)
      | r1_tarski(A_69,B_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_6,plain,(
    ! [A_3,B_4] :
      ( ~ r2_hidden('#skF_1'(A_3,B_4),B_4)
      | r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_206,plain,(
    ! [A_69] : r1_tarski(A_69,A_69) ),
    inference(resolution,[status(thm)],[c_182,c_6])).

tff(c_68,plain,(
    r2_hidden('#skF_11','#skF_10') ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_269,plain,(
    ! [C_83,B_84,A_85] :
      ( r2_hidden(C_83,B_84)
      | ~ r2_hidden(C_83,A_85)
      | ~ r1_tarski(A_85,B_84) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_284,plain,(
    ! [B_84] :
      ( r2_hidden('#skF_11',B_84)
      | ~ r1_tarski('#skF_10',B_84) ) ),
    inference(resolution,[status(thm)],[c_68,c_269])).

tff(c_416,plain,(
    ! [A_113,B_114,C_115] :
      ( ~ r1_xboole_0(A_113,B_114)
      | ~ r2_hidden(C_115,B_114)
      | ~ r2_hidden(C_115,A_113) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_435,plain,(
    ! [C_116] :
      ( ~ r2_hidden(C_116,'#skF_9')
      | ~ r2_hidden(C_116,'#skF_10') ) ),
    inference(resolution,[status(thm)],[c_66,c_416])).

tff(c_439,plain,
    ( ~ r2_hidden('#skF_11','#skF_9')
    | ~ r1_tarski('#skF_10','#skF_10') ),
    inference(resolution,[status(thm)],[c_284,c_435])).

tff(c_457,plain,(
    ~ r2_hidden('#skF_11','#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_206,c_439])).

tff(c_70,plain,(
    r1_tarski(k3_xboole_0('#skF_8','#skF_9'),k1_tarski('#skF_11')) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( r2_hidden('#skF_1'(A_3,B_4),A_3)
      | r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_2160,plain,(
    ! [A_2814,B_2815,B_2816] :
      ( r2_hidden('#skF_1'(A_2814,B_2815),B_2816)
      | ~ r1_tarski(A_2814,B_2816)
      | r1_tarski(A_2814,B_2815) ) ),
    inference(resolution,[status(thm)],[c_8,c_269])).

tff(c_46,plain,(
    ! [C_33,A_29] :
      ( C_33 = A_29
      | ~ r2_hidden(C_33,k1_tarski(A_29)) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_4012,plain,(
    ! [A_4391,A_4392,B_4393] :
      ( A_4391 = '#skF_1'(A_4392,B_4393)
      | ~ r1_tarski(A_4392,k1_tarski(A_4391))
      | r1_tarski(A_4392,B_4393) ) ),
    inference(resolution,[status(thm)],[c_2160,c_46])).

tff(c_4034,plain,(
    ! [B_4393] :
      ( '#skF_1'(k3_xboole_0('#skF_8','#skF_9'),B_4393) = '#skF_11'
      | r1_tarski(k3_xboole_0('#skF_8','#skF_9'),B_4393) ) ),
    inference(resolution,[status(thm)],[c_70,c_4012])).

tff(c_474,plain,(
    ! [A_119,B_120] :
      ( r2_hidden('#skF_5'(A_119,B_120),k3_xboole_0(A_119,B_120))
      | r1_xboole_0(A_119,B_120) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_4,plain,(
    ! [C_7,B_4,A_3] :
      ( r2_hidden(C_7,B_4)
      | ~ r2_hidden(C_7,A_3)
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_6840,plain,(
    ! [A_6041,B_6042,B_6043] :
      ( r2_hidden('#skF_5'(A_6041,B_6042),B_6043)
      | ~ r1_tarski(k3_xboole_0(A_6041,B_6042),B_6043)
      | r1_xboole_0(A_6041,B_6042) ) ),
    inference(resolution,[status(thm)],[c_474,c_4])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_494,plain,(
    ! [B_2,A_1] :
      ( r2_hidden('#skF_5'(B_2,A_1),k3_xboole_0(A_1,B_2))
      | r1_xboole_0(B_2,A_1) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_474])).

tff(c_34,plain,(
    ! [A_16,B_17] :
      ( r2_hidden('#skF_4'(A_16,B_17),A_16)
      | r1_xboole_0(A_16,B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_169,plain,(
    ! [D_63,A_64,B_65] :
      ( r2_hidden(D_63,A_64)
      | ~ r2_hidden(D_63,k3_xboole_0(A_64,B_65)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_4453,plain,(
    ! [A_4682,B_4683,B_4684] :
      ( r2_hidden('#skF_4'(k3_xboole_0(A_4682,B_4683),B_4684),A_4682)
      | r1_xboole_0(k3_xboole_0(A_4682,B_4683),B_4684) ) ),
    inference(resolution,[status(thm)],[c_34,c_169])).

tff(c_32,plain,(
    ! [A_16,B_17] :
      ( r2_hidden('#skF_4'(A_16,B_17),B_17)
      | r1_xboole_0(A_16,B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_458,plain,(
    ! [A_16] :
      ( ~ r2_hidden('#skF_4'(A_16,'#skF_10'),'#skF_9')
      | r1_xboole_0(A_16,'#skF_10') ) ),
    inference(resolution,[status(thm)],[c_32,c_435])).

tff(c_4538,plain,(
    ! [B_4715] : r1_xboole_0(k3_xboole_0('#skF_9',B_4715),'#skF_10') ),
    inference(resolution,[status(thm)],[c_4453,c_458])).

tff(c_30,plain,(
    ! [A_16,B_17,C_20] :
      ( ~ r1_xboole_0(A_16,B_17)
      | ~ r2_hidden(C_20,B_17)
      | ~ r2_hidden(C_20,A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_4795,plain,(
    ! [C_4967,B_4968] :
      ( ~ r2_hidden(C_4967,'#skF_10')
      | ~ r2_hidden(C_4967,k3_xboole_0('#skF_9',B_4968)) ) ),
    inference(resolution,[status(thm)],[c_4538,c_30])).

tff(c_4920,plain,(
    ! [B_2] :
      ( ~ r2_hidden('#skF_5'(B_2,'#skF_9'),'#skF_10')
      | r1_xboole_0(B_2,'#skF_9') ) ),
    inference(resolution,[status(thm)],[c_494,c_4795])).

tff(c_10180,plain,(
    ! [A_7634] :
      ( ~ r1_tarski(k3_xboole_0(A_7634,'#skF_9'),'#skF_10')
      | r1_xboole_0(A_7634,'#skF_9') ) ),
    inference(resolution,[status(thm)],[c_6840,c_4920])).

tff(c_10232,plain,
    ( r1_xboole_0('#skF_8','#skF_9')
    | '#skF_1'(k3_xboole_0('#skF_8','#skF_9'),'#skF_10') = '#skF_11' ),
    inference(resolution,[status(thm)],[c_4034,c_10180])).

tff(c_10235,plain,(
    '#skF_1'(k3_xboole_0('#skF_8','#skF_9'),'#skF_10') = '#skF_11' ),
    inference(splitLeft,[status(thm)],[c_10232])).

tff(c_12,plain,(
    ! [D_13,B_9,A_8] :
      ( r2_hidden(D_13,B_9)
      | ~ r2_hidden(D_13,k3_xboole_0(A_8,B_9)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_204,plain,(
    ! [A_8,B_9,B_70] :
      ( r2_hidden('#skF_1'(k3_xboole_0(A_8,B_9),B_70),B_9)
      | r1_tarski(k3_xboole_0(A_8,B_9),B_70) ) ),
    inference(resolution,[status(thm)],[c_182,c_12])).

tff(c_10242,plain,
    ( r2_hidden('#skF_11','#skF_9')
    | r1_tarski(k3_xboole_0('#skF_8','#skF_9'),'#skF_10') ),
    inference(superposition,[status(thm),theory(equality)],[c_10235,c_204])).

tff(c_10259,plain,(
    r1_tarski(k3_xboole_0('#skF_8','#skF_9'),'#skF_10') ),
    inference(negUnitSimplification,[status(thm)],[c_457,c_10242])).

tff(c_6913,plain,(
    ! [A_6041] :
      ( ~ r1_tarski(k3_xboole_0(A_6041,'#skF_9'),'#skF_10')
      | r1_xboole_0(A_6041,'#skF_9') ) ),
    inference(resolution,[status(thm)],[c_6840,c_4920])).

tff(c_10273,plain,(
    r1_xboole_0('#skF_8','#skF_9') ),
    inference(resolution,[status(thm)],[c_10259,c_6913])).

tff(c_10283,plain,(
    r1_xboole_0('#skF_9','#skF_8') ),
    inference(resolution,[status(thm)],[c_10273,c_28])).

tff(c_10288,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1728,c_10283])).

tff(c_10289,plain,(
    r1_xboole_0('#skF_8','#skF_9') ),
    inference(splitRight,[status(thm)],[c_10232])).

tff(c_10294,plain,(
    r1_xboole_0('#skF_9','#skF_8') ),
    inference(resolution,[status(thm)],[c_10289,c_28])).

tff(c_10299,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1728,c_10294])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n021.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 11:04:19 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.42/3.08  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.42/3.08  
% 8.42/3.08  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.42/3.08  %$ r2_hidden > r1_xboole_0 > r1_tarski > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_6 > #skF_11 > #skF_10 > #skF_2 > #skF_9 > #skF_8 > #skF_3 > #skF_7 > #skF_1 > #skF_5 > #skF_4
% 8.42/3.08  
% 8.42/3.08  %Foreground sorts:
% 8.42/3.08  
% 8.42/3.08  
% 8.42/3.08  %Background operators:
% 8.42/3.08  
% 8.42/3.08  
% 8.42/3.08  %Foreground operators:
% 8.42/3.08  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 8.42/3.08  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.42/3.08  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 8.42/3.08  tff('#skF_11', type, '#skF_11': $i).
% 8.42/3.08  tff(k1_tarski, type, k1_tarski: $i > $i).
% 8.42/3.08  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 8.42/3.08  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 8.42/3.08  tff('#skF_10', type, '#skF_10': $i).
% 8.42/3.08  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 8.42/3.08  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 8.42/3.08  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 8.42/3.08  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 8.42/3.08  tff('#skF_9', type, '#skF_9': $i).
% 8.42/3.08  tff('#skF_8', type, '#skF_8': $i).
% 8.42/3.08  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.42/3.08  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 8.42/3.08  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.42/3.08  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 8.42/3.08  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 8.42/3.08  tff('#skF_7', type, '#skF_7': ($i * $i) > $i).
% 8.42/3.08  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 8.42/3.08  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 8.42/3.08  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 8.42/3.08  
% 8.42/3.10  tff(f_117, negated_conjecture, ~(![A, B, C, D]: (((r1_tarski(k3_xboole_0(A, B), k1_tarski(D)) & r2_hidden(D, C)) & r1_xboole_0(C, B)) => r1_xboole_0(k2_xboole_0(A, C), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t149_zfmisc_1)).
% 8.42/3.10  tff(f_47, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 8.42/3.10  tff(f_95, axiom, (![A, B, C]: (~((~r1_xboole_0(A, k2_xboole_0(B, C)) & r1_xboole_0(A, B)) & r1_xboole_0(A, C)) & ~(~(r1_xboole_0(A, B) & r1_xboole_0(A, C)) & r1_xboole_0(A, k2_xboole_0(B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_xboole_1)).
% 8.42/3.10  tff(f_34, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 8.42/3.10  tff(f_65, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 8.42/3.10  tff(f_102, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 8.42/3.10  tff(f_79, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 8.42/3.10  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 8.42/3.10  tff(f_43, axiom, (![A, B, C]: ((C = k3_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_xboole_0)).
% 8.42/3.10  tff(c_66, plain, (r1_xboole_0('#skF_10', '#skF_9')), inference(cnfTransformation, [status(thm)], [f_117])).
% 8.42/3.10  tff(c_87, plain, (![B_44, A_45]: (r1_xboole_0(B_44, A_45) | ~r1_xboole_0(A_45, B_44))), inference(cnfTransformation, [status(thm)], [f_47])).
% 8.42/3.10  tff(c_90, plain, (r1_xboole_0('#skF_9', '#skF_10')), inference(resolution, [status(thm)], [c_66, c_87])).
% 8.42/3.10  tff(c_723, plain, (![A_147, C_148, B_149]: (~r1_xboole_0(A_147, C_148) | ~r1_xboole_0(A_147, B_149) | r1_xboole_0(A_147, k2_xboole_0(B_149, C_148)))), inference(cnfTransformation, [status(thm)], [f_95])).
% 8.42/3.10  tff(c_28, plain, (![B_15, A_14]: (r1_xboole_0(B_15, A_14) | ~r1_xboole_0(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_47])).
% 8.42/3.10  tff(c_1705, plain, (![B_2187, C_2188, A_2189]: (r1_xboole_0(k2_xboole_0(B_2187, C_2188), A_2189) | ~r1_xboole_0(A_2189, C_2188) | ~r1_xboole_0(A_2189, B_2187))), inference(resolution, [status(thm)], [c_723, c_28])).
% 8.42/3.10  tff(c_64, plain, (~r1_xboole_0(k2_xboole_0('#skF_8', '#skF_10'), '#skF_9')), inference(cnfTransformation, [status(thm)], [f_117])).
% 8.42/3.10  tff(c_1720, plain, (~r1_xboole_0('#skF_9', '#skF_10') | ~r1_xboole_0('#skF_9', '#skF_8')), inference(resolution, [status(thm)], [c_1705, c_64])).
% 8.42/3.10  tff(c_1728, plain, (~r1_xboole_0('#skF_9', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_90, c_1720])).
% 8.42/3.10  tff(c_182, plain, (![A_69, B_70]: (r2_hidden('#skF_1'(A_69, B_70), A_69) | r1_tarski(A_69, B_70))), inference(cnfTransformation, [status(thm)], [f_34])).
% 8.42/3.10  tff(c_6, plain, (![A_3, B_4]: (~r2_hidden('#skF_1'(A_3, B_4), B_4) | r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_34])).
% 8.42/3.10  tff(c_206, plain, (![A_69]: (r1_tarski(A_69, A_69))), inference(resolution, [status(thm)], [c_182, c_6])).
% 8.42/3.10  tff(c_68, plain, (r2_hidden('#skF_11', '#skF_10')), inference(cnfTransformation, [status(thm)], [f_117])).
% 8.42/3.10  tff(c_269, plain, (![C_83, B_84, A_85]: (r2_hidden(C_83, B_84) | ~r2_hidden(C_83, A_85) | ~r1_tarski(A_85, B_84))), inference(cnfTransformation, [status(thm)], [f_34])).
% 8.42/3.10  tff(c_284, plain, (![B_84]: (r2_hidden('#skF_11', B_84) | ~r1_tarski('#skF_10', B_84))), inference(resolution, [status(thm)], [c_68, c_269])).
% 8.42/3.10  tff(c_416, plain, (![A_113, B_114, C_115]: (~r1_xboole_0(A_113, B_114) | ~r2_hidden(C_115, B_114) | ~r2_hidden(C_115, A_113))), inference(cnfTransformation, [status(thm)], [f_65])).
% 8.42/3.10  tff(c_435, plain, (![C_116]: (~r2_hidden(C_116, '#skF_9') | ~r2_hidden(C_116, '#skF_10'))), inference(resolution, [status(thm)], [c_66, c_416])).
% 8.42/3.10  tff(c_439, plain, (~r2_hidden('#skF_11', '#skF_9') | ~r1_tarski('#skF_10', '#skF_10')), inference(resolution, [status(thm)], [c_284, c_435])).
% 8.42/3.10  tff(c_457, plain, (~r2_hidden('#skF_11', '#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_206, c_439])).
% 8.42/3.10  tff(c_70, plain, (r1_tarski(k3_xboole_0('#skF_8', '#skF_9'), k1_tarski('#skF_11'))), inference(cnfTransformation, [status(thm)], [f_117])).
% 8.42/3.10  tff(c_8, plain, (![A_3, B_4]: (r2_hidden('#skF_1'(A_3, B_4), A_3) | r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_34])).
% 8.42/3.10  tff(c_2160, plain, (![A_2814, B_2815, B_2816]: (r2_hidden('#skF_1'(A_2814, B_2815), B_2816) | ~r1_tarski(A_2814, B_2816) | r1_tarski(A_2814, B_2815))), inference(resolution, [status(thm)], [c_8, c_269])).
% 8.42/3.10  tff(c_46, plain, (![C_33, A_29]: (C_33=A_29 | ~r2_hidden(C_33, k1_tarski(A_29)))), inference(cnfTransformation, [status(thm)], [f_102])).
% 8.42/3.10  tff(c_4012, plain, (![A_4391, A_4392, B_4393]: (A_4391='#skF_1'(A_4392, B_4393) | ~r1_tarski(A_4392, k1_tarski(A_4391)) | r1_tarski(A_4392, B_4393))), inference(resolution, [status(thm)], [c_2160, c_46])).
% 8.42/3.10  tff(c_4034, plain, (![B_4393]: ('#skF_1'(k3_xboole_0('#skF_8', '#skF_9'), B_4393)='#skF_11' | r1_tarski(k3_xboole_0('#skF_8', '#skF_9'), B_4393))), inference(resolution, [status(thm)], [c_70, c_4012])).
% 8.42/3.10  tff(c_474, plain, (![A_119, B_120]: (r2_hidden('#skF_5'(A_119, B_120), k3_xboole_0(A_119, B_120)) | r1_xboole_0(A_119, B_120))), inference(cnfTransformation, [status(thm)], [f_79])).
% 8.42/3.10  tff(c_4, plain, (![C_7, B_4, A_3]: (r2_hidden(C_7, B_4) | ~r2_hidden(C_7, A_3) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_34])).
% 8.42/3.10  tff(c_6840, plain, (![A_6041, B_6042, B_6043]: (r2_hidden('#skF_5'(A_6041, B_6042), B_6043) | ~r1_tarski(k3_xboole_0(A_6041, B_6042), B_6043) | r1_xboole_0(A_6041, B_6042))), inference(resolution, [status(thm)], [c_474, c_4])).
% 8.42/3.10  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 8.42/3.10  tff(c_494, plain, (![B_2, A_1]: (r2_hidden('#skF_5'(B_2, A_1), k3_xboole_0(A_1, B_2)) | r1_xboole_0(B_2, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_474])).
% 8.42/3.10  tff(c_34, plain, (![A_16, B_17]: (r2_hidden('#skF_4'(A_16, B_17), A_16) | r1_xboole_0(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_65])).
% 8.42/3.10  tff(c_169, plain, (![D_63, A_64, B_65]: (r2_hidden(D_63, A_64) | ~r2_hidden(D_63, k3_xboole_0(A_64, B_65)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 8.42/3.10  tff(c_4453, plain, (![A_4682, B_4683, B_4684]: (r2_hidden('#skF_4'(k3_xboole_0(A_4682, B_4683), B_4684), A_4682) | r1_xboole_0(k3_xboole_0(A_4682, B_4683), B_4684))), inference(resolution, [status(thm)], [c_34, c_169])).
% 8.42/3.10  tff(c_32, plain, (![A_16, B_17]: (r2_hidden('#skF_4'(A_16, B_17), B_17) | r1_xboole_0(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_65])).
% 8.42/3.10  tff(c_458, plain, (![A_16]: (~r2_hidden('#skF_4'(A_16, '#skF_10'), '#skF_9') | r1_xboole_0(A_16, '#skF_10'))), inference(resolution, [status(thm)], [c_32, c_435])).
% 8.42/3.10  tff(c_4538, plain, (![B_4715]: (r1_xboole_0(k3_xboole_0('#skF_9', B_4715), '#skF_10'))), inference(resolution, [status(thm)], [c_4453, c_458])).
% 8.42/3.10  tff(c_30, plain, (![A_16, B_17, C_20]: (~r1_xboole_0(A_16, B_17) | ~r2_hidden(C_20, B_17) | ~r2_hidden(C_20, A_16))), inference(cnfTransformation, [status(thm)], [f_65])).
% 8.42/3.10  tff(c_4795, plain, (![C_4967, B_4968]: (~r2_hidden(C_4967, '#skF_10') | ~r2_hidden(C_4967, k3_xboole_0('#skF_9', B_4968)))), inference(resolution, [status(thm)], [c_4538, c_30])).
% 8.42/3.10  tff(c_4920, plain, (![B_2]: (~r2_hidden('#skF_5'(B_2, '#skF_9'), '#skF_10') | r1_xboole_0(B_2, '#skF_9'))), inference(resolution, [status(thm)], [c_494, c_4795])).
% 8.42/3.10  tff(c_10180, plain, (![A_7634]: (~r1_tarski(k3_xboole_0(A_7634, '#skF_9'), '#skF_10') | r1_xboole_0(A_7634, '#skF_9'))), inference(resolution, [status(thm)], [c_6840, c_4920])).
% 8.42/3.10  tff(c_10232, plain, (r1_xboole_0('#skF_8', '#skF_9') | '#skF_1'(k3_xboole_0('#skF_8', '#skF_9'), '#skF_10')='#skF_11'), inference(resolution, [status(thm)], [c_4034, c_10180])).
% 8.42/3.10  tff(c_10235, plain, ('#skF_1'(k3_xboole_0('#skF_8', '#skF_9'), '#skF_10')='#skF_11'), inference(splitLeft, [status(thm)], [c_10232])).
% 8.42/3.10  tff(c_12, plain, (![D_13, B_9, A_8]: (r2_hidden(D_13, B_9) | ~r2_hidden(D_13, k3_xboole_0(A_8, B_9)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 8.42/3.10  tff(c_204, plain, (![A_8, B_9, B_70]: (r2_hidden('#skF_1'(k3_xboole_0(A_8, B_9), B_70), B_9) | r1_tarski(k3_xboole_0(A_8, B_9), B_70))), inference(resolution, [status(thm)], [c_182, c_12])).
% 8.42/3.10  tff(c_10242, plain, (r2_hidden('#skF_11', '#skF_9') | r1_tarski(k3_xboole_0('#skF_8', '#skF_9'), '#skF_10')), inference(superposition, [status(thm), theory('equality')], [c_10235, c_204])).
% 8.42/3.10  tff(c_10259, plain, (r1_tarski(k3_xboole_0('#skF_8', '#skF_9'), '#skF_10')), inference(negUnitSimplification, [status(thm)], [c_457, c_10242])).
% 8.42/3.10  tff(c_6913, plain, (![A_6041]: (~r1_tarski(k3_xboole_0(A_6041, '#skF_9'), '#skF_10') | r1_xboole_0(A_6041, '#skF_9'))), inference(resolution, [status(thm)], [c_6840, c_4920])).
% 8.42/3.10  tff(c_10273, plain, (r1_xboole_0('#skF_8', '#skF_9')), inference(resolution, [status(thm)], [c_10259, c_6913])).
% 8.42/3.10  tff(c_10283, plain, (r1_xboole_0('#skF_9', '#skF_8')), inference(resolution, [status(thm)], [c_10273, c_28])).
% 8.42/3.10  tff(c_10288, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1728, c_10283])).
% 8.42/3.10  tff(c_10289, plain, (r1_xboole_0('#skF_8', '#skF_9')), inference(splitRight, [status(thm)], [c_10232])).
% 8.42/3.10  tff(c_10294, plain, (r1_xboole_0('#skF_9', '#skF_8')), inference(resolution, [status(thm)], [c_10289, c_28])).
% 8.42/3.10  tff(c_10299, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1728, c_10294])).
% 8.42/3.10  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.42/3.10  
% 8.42/3.10  Inference rules
% 8.42/3.10  ----------------------
% 8.42/3.10  #Ref     : 0
% 8.42/3.10  #Sup     : 2183
% 8.42/3.10  #Fact    : 0
% 8.42/3.10  #Define  : 0
% 8.42/3.10  #Split   : 7
% 8.42/3.10  #Chain   : 0
% 8.42/3.10  #Close   : 0
% 8.42/3.10  
% 8.42/3.10  Ordering : KBO
% 8.42/3.10  
% 8.42/3.10  Simplification rules
% 8.42/3.10  ----------------------
% 8.42/3.10  #Subsume      : 805
% 8.42/3.10  #Demod        : 216
% 8.42/3.10  #Tautology    : 242
% 8.42/3.10  #SimpNegUnit  : 96
% 8.42/3.10  #BackRed      : 66
% 8.42/3.10  
% 8.42/3.10  #Partial instantiations: 4097
% 8.42/3.10  #Strategies tried      : 1
% 8.42/3.10  
% 8.42/3.10  Timing (in seconds)
% 8.42/3.10  ----------------------
% 8.42/3.10  Preprocessing        : 0.46
% 8.42/3.10  Parsing              : 0.25
% 8.42/3.10  CNF conversion       : 0.03
% 8.42/3.10  Main loop            : 1.73
% 8.42/3.10  Inferencing          : 0.62
% 8.42/3.10  Reduction            : 0.47
% 8.42/3.10  Demodulation         : 0.33
% 8.42/3.10  BG Simplification    : 0.06
% 8.42/3.10  Subsumption          : 0.46
% 8.42/3.10  Abstraction          : 0.07
% 8.42/3.10  MUC search           : 0.00
% 8.42/3.10  Cooper               : 0.00
% 8.42/3.10  Total                : 2.23
% 8.42/3.10  Index Insertion      : 0.00
% 8.42/3.10  Index Deletion       : 0.00
% 8.42/3.10  Index Matching       : 0.00
% 8.42/3.10  BG Taut test         : 0.00
%------------------------------------------------------------------------------
