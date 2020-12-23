%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:15:28 EST 2020

% Result     : Theorem 14.38s
% Output     : CNFRefutation 14.57s
% Verified   : 
% Statistics : Number of formulae       :  215 (1726 expanded)
%              Number of leaves         :   53 ( 590 expanded)
%              Depth                    :   22
%              Number of atoms          :  330 (3699 expanded)
%              Number of equality atoms :   99 ( 878 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_funct_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k4_zfmisc_1 > k2_enumset1 > k3_zfmisc_1 > k1_enumset1 > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_mcart_1 > k1_zfmisc_1 > k1_tarski > k1_mcart_1 > k1_xboole_0 > #skF_6 > #skF_11 > #skF_9 > #skF_1 > #skF_4 > #skF_10 > #skF_13 > #skF_5 > #skF_2 > #skF_3 > #skF_7 > #skF_8 > #skF_12

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_11',type,(
    '#skF_11': $i )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff('#skF_9',type,(
    '#skF_9': ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k4_zfmisc_1,type,(
    k4_zfmisc_1: ( $i * $i * $i * $i ) > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_13',type,(
    '#skF_13': $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k3_zfmisc_1,type,(
    k3_zfmisc_1: ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_mcart_1,type,(
    k2_mcart_1: $i > $i )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_mcart_1,type,(
    k1_mcart_1: $i > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_12',type,(
    '#skF_12': $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_158,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,k1_tarski(B))
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,k1_tarski(B)))) )
       => ( r2_hidden(C,A)
         => k1_funct_1(D,C) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_funct_2)).

tff(f_133,axiom,(
    ! [A,B,C] :
      ( ( A != k1_xboole_0
        & B != k1_xboole_0
        & C != k1_xboole_0 )
    <=> k3_zfmisc_1(A,B,C) != k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_mcart_1)).

tff(f_135,axiom,(
    ! [A,B,C,D] : k3_zfmisc_1(k2_zfmisc_1(A,B),C,D) = k4_zfmisc_1(A,B,C,D) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t54_mcart_1)).

tff(f_109,axiom,(
    ! [A,B,C,D] : k4_zfmisc_1(A,B,C,D) = k2_zfmisc_1(k3_zfmisc_1(A,B,C),D) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_zfmisc_1)).

tff(f_115,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k2_zfmisc_1(B,C))
     => ( r2_hidden(k1_mcart_1(A),B)
        & r2_hidden(k2_mcart_1(A),C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_mcart_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_40,axiom,(
    ! [A,B,C] :
      ( C = k3_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

tff(f_147,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_hidden(C,A)
       => ( B = k1_xboole_0
          | r2_hidden(k1_funct_1(D,C),B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_funct_2)).

tff(f_101,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_107,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(f_74,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_55,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_53,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).

tff(c_138,plain,(
    k1_funct_1('#skF_13','#skF_12') != '#skF_11' ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_146,plain,(
    v1_funct_1('#skF_13') ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_130,plain,(
    ! [A_75,C_77] : k3_zfmisc_1(A_75,k1_xboole_0,C_77) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_11354,plain,(
    ! [A_33445,B_33446,C_33447,D_33448] : k3_zfmisc_1(k2_zfmisc_1(A_33445,B_33446),C_33447,D_33448) = k4_zfmisc_1(A_33445,B_33446,C_33447,D_33448) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_11375,plain,(
    ! [A_33445,B_33446,C_77] : k4_zfmisc_1(A_33445,B_33446,k1_xboole_0,C_77) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_130,c_11354])).

tff(c_128,plain,(
    ! [A_75,B_76] : k3_zfmisc_1(A_75,B_76,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_23012,plain,(
    ! [A_70845,B_70846,C_70847,D_70848] : k2_zfmisc_1(k3_zfmisc_1(A_70845,B_70846,C_70847),D_70848) = k4_zfmisc_1(A_70845,B_70846,C_70847,D_70848) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_23034,plain,(
    ! [A_75,B_76,D_70848] : k4_zfmisc_1(A_75,B_76,k1_xboole_0,D_70848) = k2_zfmisc_1(k1_xboole_0,D_70848) ),
    inference(superposition,[status(thm),theory(equality)],[c_128,c_23012])).

tff(c_23041,plain,(
    ! [D_70849] : k2_zfmisc_1(k1_xboole_0,D_70849) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_11375,c_23034])).

tff(c_118,plain,(
    ! [A_69,C_71,B_70] :
      ( r2_hidden(k2_mcart_1(A_69),C_71)
      | ~ r2_hidden(A_69,k2_zfmisc_1(B_70,C_71)) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_23091,plain,(
    ! [A_70853,D_70854] :
      ( r2_hidden(k2_mcart_1(A_70853),D_70854)
      | ~ r2_hidden(A_70853,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_23041,c_118])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_23155,plain,(
    ! [D_70854,A_70853] :
      ( ~ v1_xboole_0(D_70854)
      | ~ r2_hidden(A_70853,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_23091,c_2])).

tff(c_23156,plain,(
    ! [A_70853] : ~ r2_hidden(A_70853,k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_23155])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_372,plain,(
    ! [A_143,C_144,B_145] :
      ( r2_hidden(k2_mcart_1(A_143),C_144)
      | ~ r2_hidden(A_143,k2_zfmisc_1(B_145,C_144)) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_23408,plain,(
    ! [B_70879,C_70880] :
      ( r2_hidden(k2_mcart_1('#skF_1'(k2_zfmisc_1(B_70879,C_70880))),C_70880)
      | v1_xboole_0(k2_zfmisc_1(B_70879,C_70880)) ) ),
    inference(resolution,[status(thm)],[c_4,c_372])).

tff(c_23464,plain,(
    ! [B_70879] : v1_xboole_0(k2_zfmisc_1(B_70879,k1_xboole_0)) ),
    inference(resolution,[status(thm)],[c_23408,c_23156])).

tff(c_24175,plain,(
    ! [A_71008,B_71009,C_71010] :
      ( r2_hidden('#skF_2'(A_71008,B_71009,C_71010),A_71008)
      | r2_hidden('#skF_3'(A_71008,B_71009,C_71010),C_71010)
      | k3_xboole_0(A_71008,B_71009) = C_71010 ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_24302,plain,(
    ! [B_71011,C_71012] :
      ( r2_hidden('#skF_3'(k1_xboole_0,B_71011,C_71012),C_71012)
      | k3_xboole_0(k1_xboole_0,B_71011) = C_71012 ) ),
    inference(resolution,[status(thm)],[c_24175,c_23156])).

tff(c_24357,plain,(
    ! [B_71011] : k3_xboole_0(k1_xboole_0,B_71011) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_24302,c_23156])).

tff(c_24368,plain,(
    ! [C_71012,B_71011] :
      ( ~ v1_xboole_0(C_71012)
      | k3_xboole_0(k1_xboole_0,B_71011) = C_71012 ) ),
    inference(resolution,[status(thm)],[c_24302,c_2])).

tff(c_24441,plain,(
    ! [C_71014] :
      ( ~ v1_xboole_0(C_71014)
      | k1_xboole_0 = C_71014 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24357,c_24368])).

tff(c_24498,plain,(
    ! [B_70879] : k2_zfmisc_1(B_70879,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_23464,c_24441])).

tff(c_144,plain,(
    v1_funct_2('#skF_13','#skF_10',k1_tarski('#skF_11')) ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_142,plain,(
    m1_subset_1('#skF_13',k1_zfmisc_1(k2_zfmisc_1('#skF_10',k1_tarski('#skF_11')))) ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_140,plain,(
    r2_hidden('#skF_12','#skF_10') ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_32866,plain,(
    ! [D_108211,C_108212,B_108213,A_108214] :
      ( r2_hidden(k1_funct_1(D_108211,C_108212),B_108213)
      | k1_xboole_0 = B_108213
      | ~ r2_hidden(C_108212,A_108214)
      | ~ m1_subset_1(D_108211,k1_zfmisc_1(k2_zfmisc_1(A_108214,B_108213)))
      | ~ v1_funct_2(D_108211,A_108214,B_108213)
      | ~ v1_funct_1(D_108211) ) ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_33742,plain,(
    ! [D_108888,B_108889] :
      ( r2_hidden(k1_funct_1(D_108888,'#skF_12'),B_108889)
      | k1_xboole_0 = B_108889
      | ~ m1_subset_1(D_108888,k1_zfmisc_1(k2_zfmisc_1('#skF_10',B_108889)))
      | ~ v1_funct_2(D_108888,'#skF_10',B_108889)
      | ~ v1_funct_1(D_108888) ) ),
    inference(resolution,[status(thm)],[c_140,c_32866])).

tff(c_33773,plain,
    ( r2_hidden(k1_funct_1('#skF_13','#skF_12'),k1_tarski('#skF_11'))
    | k1_tarski('#skF_11') = k1_xboole_0
    | ~ v1_funct_2('#skF_13','#skF_10',k1_tarski('#skF_11'))
    | ~ v1_funct_1('#skF_13') ),
    inference(resolution,[status(thm)],[c_142,c_33742])).

tff(c_33778,plain,
    ( r2_hidden(k1_funct_1('#skF_13','#skF_12'),k1_tarski('#skF_11'))
    | k1_tarski('#skF_11') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_146,c_144,c_33773])).

tff(c_33779,plain,(
    k1_tarski('#skF_11') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_33778])).

tff(c_112,plain,(
    ! [A_62] : ~ v1_xboole_0(k1_zfmisc_1(A_62)) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_270,plain,(
    ! [A_114,B_115] :
      ( r2_hidden(A_114,B_115)
      | v1_xboole_0(B_115)
      | ~ m1_subset_1(A_114,B_115) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_58,plain,(
    ! [C_51,A_47] :
      ( r1_tarski(C_51,A_47)
      | ~ r2_hidden(C_51,k1_zfmisc_1(A_47)) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_274,plain,(
    ! [A_114,A_47] :
      ( r1_tarski(A_114,A_47)
      | v1_xboole_0(k1_zfmisc_1(A_47))
      | ~ m1_subset_1(A_114,k1_zfmisc_1(A_47)) ) ),
    inference(resolution,[status(thm)],[c_270,c_58])).

tff(c_282,plain,(
    ! [A_116,A_117] :
      ( r1_tarski(A_116,A_117)
      | ~ m1_subset_1(A_116,k1_zfmisc_1(A_117)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_112,c_274])).

tff(c_286,plain,(
    r1_tarski('#skF_13',k2_zfmisc_1('#skF_10',k1_tarski('#skF_11'))) ),
    inference(resolution,[status(thm)],[c_142,c_282])).

tff(c_24,plain,(
    ! [A_11,B_12] :
      ( k3_xboole_0(A_11,B_12) = A_11
      | ~ r1_tarski(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_301,plain,(
    k3_xboole_0('#skF_13',k2_zfmisc_1('#skF_10',k1_tarski('#skF_11'))) = '#skF_13' ),
    inference(resolution,[status(thm)],[c_286,c_24])).

tff(c_309,plain,(
    ! [D_121,B_122,A_123] :
      ( r2_hidden(D_121,B_122)
      | ~ r2_hidden(D_121,k3_xboole_0(A_123,B_122)) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_312,plain,(
    ! [D_121] :
      ( r2_hidden(D_121,k2_zfmisc_1('#skF_10',k1_tarski('#skF_11')))
      | ~ r2_hidden(D_121,'#skF_13') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_301,c_309])).

tff(c_381,plain,(
    ! [D_121] :
      ( r2_hidden(k2_mcart_1(D_121),k1_tarski('#skF_11'))
      | ~ r2_hidden(D_121,'#skF_13') ) ),
    inference(resolution,[status(thm)],[c_312,c_372])).

tff(c_44,plain,(
    ! [A_19] : k2_tarski(A_19,A_19) = k1_tarski(A_19) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_440,plain,(
    ! [D_184,B_185,A_186] :
      ( D_184 = B_185
      | D_184 = A_186
      | ~ r2_hidden(D_184,k2_tarski(A_186,B_185)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_468,plain,(
    ! [D_187,A_188] :
      ( D_187 = A_188
      | D_187 = A_188
      | ~ r2_hidden(D_187,k1_tarski(A_188)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_440])).

tff(c_492,plain,(
    ! [D_189] :
      ( k2_mcart_1(D_189) = '#skF_11'
      | ~ r2_hidden(D_189,'#skF_13') ) ),
    inference(resolution,[status(thm)],[c_381,c_468])).

tff(c_502,plain,
    ( k2_mcart_1('#skF_1'('#skF_13')) = '#skF_11'
    | v1_xboole_0('#skF_13') ),
    inference(resolution,[status(thm)],[c_4,c_492])).

tff(c_518,plain,(
    v1_xboole_0('#skF_13') ),
    inference(splitLeft,[status(thm)],[c_502])).

tff(c_247,plain,(
    ! [C_107,A_108] :
      ( r1_tarski(C_107,A_108)
      | ~ r2_hidden(C_107,k1_zfmisc_1(A_108)) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_251,plain,(
    ! [A_108] :
      ( r1_tarski('#skF_1'(k1_zfmisc_1(A_108)),A_108)
      | v1_xboole_0(k1_zfmisc_1(A_108)) ) ),
    inference(resolution,[status(thm)],[c_4,c_247])).

tff(c_254,plain,(
    ! [A_108] : r1_tarski('#skF_1'(k1_zfmisc_1(A_108)),A_108) ),
    inference(negUnitSimplification,[status(thm)],[c_112,c_251])).

tff(c_256,plain,(
    ! [A_110,B_111] :
      ( k3_xboole_0(A_110,B_111) = A_110
      | ~ r1_tarski(A_110,B_111) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_260,plain,(
    ! [A_108] : k3_xboole_0('#skF_1'(k1_zfmisc_1(A_108)),A_108) = '#skF_1'(k1_zfmisc_1(A_108)) ),
    inference(resolution,[status(thm)],[c_254,c_256])).

tff(c_533,plain,(
    ! [A_200,B_201] :
      ( r2_hidden('#skF_1'(k3_xboole_0(A_200,B_201)),B_201)
      | v1_xboole_0(k3_xboole_0(A_200,B_201)) ) ),
    inference(resolution,[status(thm)],[c_4,c_309])).

tff(c_594,plain,(
    ! [B_202,A_203] :
      ( ~ v1_xboole_0(B_202)
      | v1_xboole_0(k3_xboole_0(A_203,B_202)) ) ),
    inference(resolution,[status(thm)],[c_533,c_2])).

tff(c_597,plain,(
    ! [A_108] :
      ( ~ v1_xboole_0(A_108)
      | v1_xboole_0('#skF_1'(k1_zfmisc_1(A_108))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_260,c_594])).

tff(c_1516,plain,(
    ! [B_338,C_339] :
      ( r2_hidden(k2_mcart_1('#skF_1'(k2_zfmisc_1(B_338,C_339))),C_339)
      | v1_xboole_0(k2_zfmisc_1(B_338,C_339)) ) ),
    inference(resolution,[status(thm)],[c_4,c_372])).

tff(c_955,plain,(
    ! [D_233,A_234,B_235] :
      ( r2_hidden(D_233,k3_xboole_0(A_234,B_235))
      | ~ r2_hidden(D_233,B_235)
      | ~ r2_hidden(D_233,A_234) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_1139,plain,(
    ! [A_250,B_251,D_252] :
      ( ~ v1_xboole_0(k3_xboole_0(A_250,B_251))
      | ~ r2_hidden(D_252,B_251)
      | ~ r2_hidden(D_252,A_250) ) ),
    inference(resolution,[status(thm)],[c_955,c_2])).

tff(c_1151,plain,(
    ! [D_252] :
      ( ~ v1_xboole_0('#skF_13')
      | ~ r2_hidden(D_252,k2_zfmisc_1('#skF_10',k1_tarski('#skF_11')))
      | ~ r2_hidden(D_252,'#skF_13') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_301,c_1139])).

tff(c_1158,plain,(
    ! [D_253] :
      ( ~ r2_hidden(D_253,k2_zfmisc_1('#skF_10',k1_tarski('#skF_11')))
      | ~ r2_hidden(D_253,'#skF_13') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_518,c_1151])).

tff(c_1185,plain,(
    ! [D_121] : ~ r2_hidden(D_121,'#skF_13') ),
    inference(resolution,[status(thm)],[c_312,c_1158])).

tff(c_1572,plain,(
    ! [B_338] : v1_xboole_0(k2_zfmisc_1(B_338,'#skF_13')) ),
    inference(resolution,[status(thm)],[c_1516,c_1185])).

tff(c_2383,plain,(
    ! [A_423,B_424,C_425] :
      ( r2_hidden('#skF_2'(A_423,B_424,C_425),A_423)
      | r2_hidden('#skF_3'(A_423,B_424,C_425),C_425)
      | k3_xboole_0(A_423,B_424) = C_425 ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_18,plain,(
    ! [A_5,B_6,C_7] :
      ( ~ r2_hidden('#skF_2'(A_5,B_6,C_7),C_7)
      | r2_hidden('#skF_3'(A_5,B_6,C_7),C_7)
      | k3_xboole_0(A_5,B_6) = C_7 ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_2525,plain,(
    ! [A_426,B_427] :
      ( r2_hidden('#skF_3'(A_426,B_427,A_426),A_426)
      | k3_xboole_0(A_426,B_427) = A_426 ) ),
    inference(resolution,[status(thm)],[c_2383,c_18])).

tff(c_2585,plain,(
    ! [B_427] : k3_xboole_0('#skF_13',B_427) = '#skF_13' ),
    inference(resolution,[status(thm)],[c_2525,c_1185])).

tff(c_2500,plain,(
    ! [B_424,C_425] :
      ( r2_hidden('#skF_3'('#skF_13',B_424,C_425),C_425)
      | k3_xboole_0('#skF_13',B_424) = C_425 ) ),
    inference(resolution,[status(thm)],[c_2383,c_1185])).

tff(c_2737,plain,(
    ! [B_430,C_431] :
      ( r2_hidden('#skF_3'('#skF_13',B_430,C_431),C_431)
      | C_431 = '#skF_13' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2585,c_2500])).

tff(c_2848,plain,(
    ! [C_432] :
      ( ~ v1_xboole_0(C_432)
      | C_432 = '#skF_13' ) ),
    inference(resolution,[status(thm)],[c_2737,c_2])).

tff(c_2920,plain,(
    ! [B_338] : k2_zfmisc_1(B_338,'#skF_13') = '#skF_13' ),
    inference(resolution,[status(thm)],[c_1572,c_2848])).

tff(c_805,plain,(
    ! [A_213,B_214,C_215,D_216] : k3_zfmisc_1(k2_zfmisc_1(A_213,B_214),C_215,D_216) = k4_zfmisc_1(A_213,B_214,C_215,D_216) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_812,plain,(
    ! [A_213,B_214,D_216] : k4_zfmisc_1(A_213,B_214,k1_xboole_0,D_216) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_805,c_130])).

tff(c_883,plain,(
    ! [A_224,B_225,C_226,D_227] : k2_zfmisc_1(k3_zfmisc_1(A_224,B_225,C_226),D_227) = k4_zfmisc_1(A_224,B_225,C_226,D_227) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_905,plain,(
    ! [A_75,B_76,D_227] : k4_zfmisc_1(A_75,B_76,k1_xboole_0,D_227) = k2_zfmisc_1(k1_xboole_0,D_227) ),
    inference(superposition,[status(thm),theory(equality)],[c_128,c_883])).

tff(c_912,plain,(
    ! [D_228] : k2_zfmisc_1(k1_xboole_0,D_228) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_812,c_905])).

tff(c_974,plain,(
    ! [A_236,D_237] :
      ( r2_hidden(k2_mcart_1(A_236),D_237)
      | ~ r2_hidden(A_236,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_912,c_118])).

tff(c_1032,plain,(
    ! [D_237,A_236] :
      ( ~ v1_xboole_0(D_237)
      | ~ r2_hidden(A_236,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_974,c_2])).

tff(c_1033,plain,(
    ! [A_236] : ~ r2_hidden(A_236,k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_1032])).

tff(c_2799,plain,(
    k1_xboole_0 = '#skF_13' ),
    inference(resolution,[status(thm)],[c_2737,c_1033])).

tff(c_136,plain,(
    ! [D_85,C_84,B_83,A_82] :
      ( r2_hidden(k1_funct_1(D_85,C_84),B_83)
      | k1_xboole_0 = B_83
      | ~ r2_hidden(C_84,A_82)
      | ~ m1_subset_1(D_85,k1_zfmisc_1(k2_zfmisc_1(A_82,B_83)))
      | ~ v1_funct_2(D_85,A_82,B_83)
      | ~ v1_funct_1(D_85) ) ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_10831,plain,(
    ! [D_32249,C_32250,B_32251,A_32252] :
      ( r2_hidden(k1_funct_1(D_32249,C_32250),B_32251)
      | B_32251 = '#skF_13'
      | ~ r2_hidden(C_32250,A_32252)
      | ~ m1_subset_1(D_32249,k1_zfmisc_1(k2_zfmisc_1(A_32252,B_32251)))
      | ~ v1_funct_2(D_32249,A_32252,B_32251)
      | ~ v1_funct_1(D_32249) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2799,c_136])).

tff(c_11130,plain,(
    ! [D_32756,B_32757] :
      ( r2_hidden(k1_funct_1(D_32756,'#skF_12'),B_32757)
      | B_32757 = '#skF_13'
      | ~ m1_subset_1(D_32756,k1_zfmisc_1(k2_zfmisc_1('#skF_10',B_32757)))
      | ~ v1_funct_2(D_32756,'#skF_10',B_32757)
      | ~ v1_funct_1(D_32756) ) ),
    inference(resolution,[status(thm)],[c_140,c_10831])).

tff(c_11161,plain,
    ( r2_hidden(k1_funct_1('#skF_13','#skF_12'),k1_tarski('#skF_11'))
    | k1_tarski('#skF_11') = '#skF_13'
    | ~ v1_funct_2('#skF_13','#skF_10',k1_tarski('#skF_11'))
    | ~ v1_funct_1('#skF_13') ),
    inference(resolution,[status(thm)],[c_142,c_11130])).

tff(c_11166,plain,
    ( r2_hidden(k1_funct_1('#skF_13','#skF_12'),k1_tarski('#skF_11'))
    | k1_tarski('#skF_11') = '#skF_13' ),
    inference(demodulation,[status(thm),theory(equality)],[c_146,c_144,c_11161])).

tff(c_11185,plain,(
    k1_tarski('#skF_11') = '#skF_13' ),
    inference(splitLeft,[status(thm)],[c_11166])).

tff(c_323,plain,(
    ! [D_124] :
      ( r2_hidden(D_124,k2_zfmisc_1('#skF_10',k1_tarski('#skF_11')))
      | ~ r2_hidden(D_124,'#skF_13') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_301,c_309])).

tff(c_327,plain,(
    ! [D_124] :
      ( ~ v1_xboole_0(k2_zfmisc_1('#skF_10',k1_tarski('#skF_11')))
      | ~ r2_hidden(D_124,'#skF_13') ) ),
    inference(resolution,[status(thm)],[c_323,c_2])).

tff(c_354,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_10',k1_tarski('#skF_11'))) ),
    inference(splitLeft,[status(thm)],[c_327])).

tff(c_11186,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_10','#skF_13')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_11185,c_354])).

tff(c_11192,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_518,c_2920,c_11186])).

tff(c_11193,plain,(
    r2_hidden(k1_funct_1('#skF_13','#skF_12'),k1_tarski('#skF_11')) ),
    inference(splitRight,[status(thm)],[c_11166])).

tff(c_454,plain,(
    ! [D_184,A_19] :
      ( D_184 = A_19
      | D_184 = A_19
      | ~ r2_hidden(D_184,k1_tarski(A_19)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_440])).

tff(c_11199,plain,(
    k1_funct_1('#skF_13','#skF_12') = '#skF_11' ),
    inference(resolution,[status(thm)],[c_11193,c_454])).

tff(c_11207,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_138,c_138,c_11199])).

tff(c_11208,plain,(
    ! [D_237] : ~ v1_xboole_0(D_237) ),
    inference(splitRight,[status(thm)],[c_1032])).

tff(c_577,plain,(
    ! [A_108] :
      ( r2_hidden('#skF_1'('#skF_1'(k1_zfmisc_1(A_108))),A_108)
      | v1_xboole_0(k3_xboole_0('#skF_1'(k1_zfmisc_1(A_108)),A_108)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_260,c_533])).

tff(c_752,plain,(
    ! [A_212] :
      ( r2_hidden('#skF_1'('#skF_1'(k1_zfmisc_1(A_212))),A_212)
      | v1_xboole_0('#skF_1'(k1_zfmisc_1(A_212))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_260,c_577])).

tff(c_483,plain,(
    ! [D_121] :
      ( k2_mcart_1(D_121) = '#skF_11'
      | ~ r2_hidden(D_121,'#skF_13') ) ),
    inference(resolution,[status(thm)],[c_381,c_468])).

tff(c_794,plain,
    ( k2_mcart_1('#skF_1'('#skF_1'(k1_zfmisc_1('#skF_13')))) = '#skF_11'
    | v1_xboole_0('#skF_1'(k1_zfmisc_1('#skF_13'))) ),
    inference(resolution,[status(thm)],[c_752,c_483])).

tff(c_881,plain,(
    v1_xboole_0('#skF_1'(k1_zfmisc_1('#skF_13'))) ),
    inference(splitLeft,[status(thm)],[c_794])).

tff(c_11221,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_11208,c_881])).

tff(c_11223,plain,(
    ~ v1_xboole_0('#skF_1'(k1_zfmisc_1('#skF_13'))) ),
    inference(splitRight,[status(thm)],[c_794])).

tff(c_11226,plain,(
    ~ v1_xboole_0('#skF_13') ),
    inference(resolution,[status(thm)],[c_597,c_11223])).

tff(c_11230,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_518,c_11226])).

tff(c_11232,plain,(
    ~ v1_xboole_0('#skF_13') ),
    inference(splitRight,[status(thm)],[c_502])).

tff(c_11272,plain,(
    ! [A_33440,B_33441] :
      ( r2_hidden('#skF_1'(k3_xboole_0(A_33440,B_33441)),B_33441)
      | v1_xboole_0(k3_xboole_0(A_33440,B_33441)) ) ),
    inference(resolution,[status(thm)],[c_4,c_309])).

tff(c_11319,plain,
    ( r2_hidden('#skF_1'('#skF_13'),k2_zfmisc_1('#skF_10',k1_tarski('#skF_11')))
    | v1_xboole_0(k3_xboole_0('#skF_13',k2_zfmisc_1('#skF_10',k1_tarski('#skF_11')))) ),
    inference(superposition,[status(thm),theory(equality)],[c_301,c_11272])).

tff(c_11332,plain,
    ( r2_hidden('#skF_1'('#skF_13'),k2_zfmisc_1('#skF_10',k1_tarski('#skF_11')))
    | v1_xboole_0('#skF_13') ),
    inference(demodulation,[status(thm),theory(equality)],[c_301,c_11319])).

tff(c_11333,plain,(
    r2_hidden('#skF_1'('#skF_13'),k2_zfmisc_1('#skF_10',k1_tarski('#skF_11'))) ),
    inference(negUnitSimplification,[status(thm)],[c_11232,c_11332])).

tff(c_33797,plain,(
    r2_hidden('#skF_1'('#skF_13'),k2_zfmisc_1('#skF_10',k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_33779,c_11333])).

tff(c_33829,plain,(
    r2_hidden('#skF_1'('#skF_13'),k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24498,c_33797])).

tff(c_33831,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_23156,c_33829])).

tff(c_33832,plain,(
    r2_hidden(k1_funct_1('#skF_13','#skF_12'),k1_tarski('#skF_11')) ),
    inference(splitRight,[status(thm)],[c_33778])).

tff(c_33838,plain,(
    k1_funct_1('#skF_13','#skF_12') = '#skF_11' ),
    inference(resolution,[status(thm)],[c_33832,c_454])).

tff(c_33846,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_138,c_138,c_33838])).

tff(c_33847,plain,(
    ! [D_70854] : ~ v1_xboole_0(D_70854) ),
    inference(splitRight,[status(thm)],[c_23155])).

tff(c_287,plain,(
    ! [D_118,A_119,B_120] :
      ( r2_hidden(D_118,A_119)
      | ~ r2_hidden(D_118,k3_xboole_0(A_119,B_120)) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_297,plain,(
    ! [A_119,B_120] :
      ( r2_hidden('#skF_1'(k3_xboole_0(A_119,B_120)),A_119)
      | v1_xboole_0(k3_xboole_0(A_119,B_120)) ) ),
    inference(resolution,[status(thm)],[c_4,c_287])).

tff(c_34029,plain,(
    ! [A_109394,B_109395] : r2_hidden('#skF_1'(k3_xboole_0(A_109394,B_109395)),A_109394) ),
    inference(negUnitSimplification,[status(thm)],[c_33847,c_297])).

tff(c_34108,plain,(
    ! [A_109397,B_109398] : '#skF_1'(k3_xboole_0(k1_tarski(A_109397),B_109398)) = A_109397 ),
    inference(resolution,[status(thm)],[c_34029,c_454])).

tff(c_322,plain,(
    ! [A_123,B_122] :
      ( r2_hidden('#skF_1'(k3_xboole_0(A_123,B_122)),B_122)
      | v1_xboole_0(k3_xboole_0(A_123,B_122)) ) ),
    inference(resolution,[status(thm)],[c_4,c_309])).

tff(c_33855,plain,(
    ! [A_123,B_122] : r2_hidden('#skF_1'(k3_xboole_0(A_123,B_122)),B_122) ),
    inference(negUnitSimplification,[status(thm)],[c_33847,c_322])).

tff(c_34120,plain,(
    ! [A_109397,B_109398] : r2_hidden(A_109397,B_109398) ),
    inference(superposition,[status(thm),theory(equality)],[c_34108,c_33855])).

tff(c_34178,plain,(
    ! [D_109401,A_109402] : D_109401 = A_109402 ),
    inference(demodulation,[status(thm),theory(equality)],[c_34120,c_454])).

tff(c_36504,plain,(
    ! [D_109401] : D_109401 != '#skF_11' ),
    inference(superposition,[status(thm),theory(equality)],[c_34178,c_138])).

tff(c_36582,plain,(
    $false ),
    inference(reflexivity,[status(thm),theory(equality)],[c_36504])).

tff(c_36584,plain,(
    v1_xboole_0(k2_zfmisc_1('#skF_10',k1_tarski('#skF_11'))) ),
    inference(splitRight,[status(thm)],[c_327])).

tff(c_38543,plain,(
    ! [A_111520,B_111521,C_111522] :
      ( r2_hidden('#skF_2'(A_111520,B_111521,C_111522),B_111521)
      | r2_hidden('#skF_3'(A_111520,B_111521,C_111522),C_111522)
      | k3_xboole_0(A_111520,B_111521) = C_111522 ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_36583,plain,(
    ! [D_124] : ~ r2_hidden(D_124,'#skF_13') ),
    inference(splitRight,[status(thm)],[c_327])).

tff(c_38680,plain,(
    ! [A_111523,C_111524] :
      ( r2_hidden('#skF_3'(A_111523,'#skF_13',C_111524),C_111524)
      | k3_xboole_0(A_111523,'#skF_13') = C_111524 ) ),
    inference(resolution,[status(thm)],[c_38543,c_36583])).

tff(c_38746,plain,(
    ! [A_111523] : k3_xboole_0(A_111523,'#skF_13') = '#skF_13' ),
    inference(resolution,[status(thm)],[c_38680,c_36583])).

tff(c_38751,plain,(
    ! [C_111524,A_111523] :
      ( ~ v1_xboole_0(C_111524)
      | k3_xboole_0(A_111523,'#skF_13') = C_111524 ) ),
    inference(resolution,[status(thm)],[c_38680,c_2])).

tff(c_39158,plain,(
    ! [C_111531] :
      ( ~ v1_xboole_0(C_111531)
      | C_111531 = '#skF_13' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38746,c_38751])).

tff(c_39221,plain,(
    k2_zfmisc_1('#skF_10',k1_tarski('#skF_11')) = '#skF_13' ),
    inference(resolution,[status(thm)],[c_36584,c_39158])).

tff(c_39487,plain,(
    m1_subset_1('#skF_13',k1_zfmisc_1('#skF_13')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_39221,c_142])).

tff(c_37142,plain,(
    ! [A_111335,B_111336,C_111337,D_111338] : k3_zfmisc_1(k2_zfmisc_1(A_111335,B_111336),C_111337,D_111338) = k4_zfmisc_1(A_111335,B_111336,C_111337,D_111338) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_37155,plain,(
    ! [A_111335,B_111336,D_111338] : k4_zfmisc_1(A_111335,B_111336,k1_xboole_0,D_111338) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_37142,c_130])).

tff(c_37038,plain,(
    ! [A_111315,B_111316,C_111317,D_111318] : k2_zfmisc_1(k3_zfmisc_1(A_111315,B_111316,C_111317),D_111318) = k4_zfmisc_1(A_111315,B_111316,C_111317,D_111318) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_37054,plain,(
    ! [A_75,B_76,D_111318] : k4_zfmisc_1(A_75,B_76,k1_xboole_0,D_111318) = k2_zfmisc_1(k1_xboole_0,D_111318) ),
    inference(superposition,[status(thm),theory(equality)],[c_128,c_37038])).

tff(c_37200,plain,(
    ! [D_111342] : k2_zfmisc_1(k1_xboole_0,D_111342) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_37155,c_37054])).

tff(c_37369,plain,(
    ! [A_111357,D_111358] :
      ( r2_hidden(k2_mcart_1(A_111357),D_111358)
      | ~ r2_hidden(A_111357,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_37200,c_118])).

tff(c_37415,plain,(
    ! [A_111357] : ~ r2_hidden(A_111357,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_37369,c_36583])).

tff(c_38740,plain,(
    ! [A_111523] : k3_xboole_0(A_111523,'#skF_13') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_38680,c_37415])).

tff(c_38850,plain,(
    k1_xboole_0 = '#skF_13' ),
    inference(demodulation,[status(thm),theory(equality)],[c_38746,c_38740])).

tff(c_43421,plain,(
    ! [D_137187,C_137188,B_137189,A_137190] :
      ( r2_hidden(k1_funct_1(D_137187,C_137188),B_137189)
      | B_137189 = '#skF_13'
      | ~ r2_hidden(C_137188,A_137190)
      | ~ m1_subset_1(D_137187,k1_zfmisc_1(k2_zfmisc_1(A_137190,B_137189)))
      | ~ v1_funct_2(D_137187,A_137190,B_137189)
      | ~ v1_funct_1(D_137187) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38850,c_136])).

tff(c_43551,plain,(
    ! [D_137357,B_137358] :
      ( r2_hidden(k1_funct_1(D_137357,'#skF_12'),B_137358)
      | B_137358 = '#skF_13'
      | ~ m1_subset_1(D_137357,k1_zfmisc_1(k2_zfmisc_1('#skF_10',B_137358)))
      | ~ v1_funct_2(D_137357,'#skF_10',B_137358)
      | ~ v1_funct_1(D_137357) ) ),
    inference(resolution,[status(thm)],[c_140,c_43421])).

tff(c_43562,plain,(
    ! [D_137357] :
      ( r2_hidden(k1_funct_1(D_137357,'#skF_12'),k1_tarski('#skF_11'))
      | k1_tarski('#skF_11') = '#skF_13'
      | ~ m1_subset_1(D_137357,k1_zfmisc_1('#skF_13'))
      | ~ v1_funct_2(D_137357,'#skF_10',k1_tarski('#skF_11'))
      | ~ v1_funct_1(D_137357) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_39221,c_43551])).

tff(c_43694,plain,(
    k1_tarski('#skF_11') = '#skF_13' ),
    inference(splitLeft,[status(thm)],[c_43562])).

tff(c_181,plain,(
    ! [A_97] : k2_tarski(A_97,A_97) = k1_tarski(A_97) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_28,plain,(
    ! [D_18,A_13] : r2_hidden(D_18,k2_tarski(A_13,D_18)) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_189,plain,(
    ! [A_97] : r2_hidden(A_97,k1_tarski(A_97)) ),
    inference(superposition,[status(thm),theory(equality)],[c_181,c_28])).

tff(c_43728,plain,(
    r2_hidden('#skF_11','#skF_13') ),
    inference(superposition,[status(thm),theory(equality)],[c_43694,c_189])).

tff(c_43740,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_36583,c_43728])).

tff(c_44356,plain,(
    ! [D_139208] :
      ( r2_hidden(k1_funct_1(D_139208,'#skF_12'),k1_tarski('#skF_11'))
      | ~ m1_subset_1(D_139208,k1_zfmisc_1('#skF_13'))
      | ~ v1_funct_2(D_139208,'#skF_10',k1_tarski('#skF_11'))
      | ~ v1_funct_1(D_139208) ) ),
    inference(splitRight,[status(thm)],[c_43562])).

tff(c_36652,plain,(
    ! [D_111275,B_111276,A_111277] :
      ( D_111275 = B_111276
      | D_111275 = A_111277
      | ~ r2_hidden(D_111275,k2_tarski(A_111277,B_111276)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_36666,plain,(
    ! [D_111275,A_19] :
      ( D_111275 = A_19
      | D_111275 = A_19
      | ~ r2_hidden(D_111275,k1_tarski(A_19)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_36652])).

tff(c_45640,plain,(
    ! [D_140894] :
      ( k1_funct_1(D_140894,'#skF_12') = '#skF_11'
      | ~ m1_subset_1(D_140894,k1_zfmisc_1('#skF_13'))
      | ~ v1_funct_2(D_140894,'#skF_10',k1_tarski('#skF_11'))
      | ~ v1_funct_1(D_140894) ) ),
    inference(resolution,[status(thm)],[c_44356,c_36666])).

tff(c_45643,plain,
    ( k1_funct_1('#skF_13','#skF_12') = '#skF_11'
    | ~ m1_subset_1('#skF_13',k1_zfmisc_1('#skF_13'))
    | ~ v1_funct_1('#skF_13') ),
    inference(resolution,[status(thm)],[c_144,c_45640])).

tff(c_45646,plain,(
    k1_funct_1('#skF_13','#skF_12') = '#skF_11' ),
    inference(demodulation,[status(thm),theory(equality)],[c_146,c_39487,c_45643])).

tff(c_45648,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_138,c_45646])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n015.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 09:53:08 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 14.38/6.04  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 14.38/6.06  
% 14.38/6.06  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 14.38/6.06  %$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_funct_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k4_zfmisc_1 > k2_enumset1 > k3_zfmisc_1 > k1_enumset1 > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_mcart_1 > k1_zfmisc_1 > k1_tarski > k1_mcart_1 > k1_xboole_0 > #skF_6 > #skF_11 > #skF_9 > #skF_1 > #skF_4 > #skF_10 > #skF_13 > #skF_5 > #skF_2 > #skF_3 > #skF_7 > #skF_8 > #skF_12
% 14.38/6.06  
% 14.38/6.06  %Foreground sorts:
% 14.38/6.06  
% 14.38/6.06  
% 14.38/6.06  %Background operators:
% 14.38/6.06  
% 14.38/6.06  
% 14.38/6.06  %Foreground operators:
% 14.38/6.06  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 14.38/6.06  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 14.38/6.06  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 14.38/6.06  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 14.38/6.06  tff('#skF_11', type, '#skF_11': $i).
% 14.38/6.06  tff(k1_tarski, type, k1_tarski: $i > $i).
% 14.38/6.06  tff('#skF_9', type, '#skF_9': ($i * $i * $i * $i * $i * $i * $i) > $i).
% 14.38/6.06  tff('#skF_1', type, '#skF_1': $i > $i).
% 14.38/6.06  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 14.38/6.06  tff(k4_zfmisc_1, type, k4_zfmisc_1: ($i * $i * $i * $i) > $i).
% 14.38/6.06  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 14.38/6.06  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 14.38/6.06  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 14.38/6.06  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 14.38/6.06  tff('#skF_10', type, '#skF_10': $i).
% 14.38/6.06  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 14.38/6.06  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 14.38/6.06  tff('#skF_13', type, '#skF_13': $i).
% 14.38/6.06  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 14.38/6.06  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 14.38/6.06  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 14.38/6.06  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 14.38/6.06  tff(k3_zfmisc_1, type, k3_zfmisc_1: ($i * $i * $i) > $i).
% 14.38/6.06  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 14.38/6.06  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 14.38/6.06  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 14.38/6.06  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 14.38/6.06  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 14.38/6.06  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 14.38/6.06  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 14.38/6.06  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 14.38/6.06  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 14.38/6.06  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 14.38/6.06  tff('#skF_7', type, '#skF_7': ($i * $i) > $i).
% 14.38/6.06  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 14.38/6.06  tff('#skF_8', type, '#skF_8': ($i * $i * $i * $i * $i * $i * $i) > $i).
% 14.38/6.06  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 14.38/6.06  tff('#skF_12', type, '#skF_12': $i).
% 14.38/6.06  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 14.38/6.06  
% 14.57/6.09  tff(f_158, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, k1_tarski(B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, k1_tarski(B))))) => (r2_hidden(C, A) => (k1_funct_1(D, C) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_funct_2)).
% 14.57/6.09  tff(f_133, axiom, (![A, B, C]: (((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0)) <=> ~(k3_zfmisc_1(A, B, C) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t35_mcart_1)).
% 14.57/6.09  tff(f_135, axiom, (![A, B, C, D]: (k3_zfmisc_1(k2_zfmisc_1(A, B), C, D) = k4_zfmisc_1(A, B, C, D))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t54_mcart_1)).
% 14.57/6.09  tff(f_109, axiom, (![A, B, C, D]: (k4_zfmisc_1(A, B, C, D) = k2_zfmisc_1(k3_zfmisc_1(A, B, C), D))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_zfmisc_1)).
% 14.57/6.09  tff(f_115, axiom, (![A, B, C]: (r2_hidden(A, k2_zfmisc_1(B, C)) => (r2_hidden(k1_mcart_1(A), B) & r2_hidden(k2_mcart_1(A), C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_mcart_1)).
% 14.57/6.09  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 14.57/6.09  tff(f_40, axiom, (![A, B, C]: ((C = k3_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_xboole_0)).
% 14.57/6.09  tff(f_147, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_hidden(C, A) => ((B = k1_xboole_0) | r2_hidden(k1_funct_1(D, C), B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_funct_2)).
% 14.57/6.09  tff(f_101, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_subset_1)).
% 14.57/6.09  tff(f_107, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 14.57/6.09  tff(f_74, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 14.57/6.09  tff(f_44, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 14.57/6.09  tff(f_55, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 14.57/6.09  tff(f_53, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_tarski)).
% 14.57/6.09  tff(c_138, plain, (k1_funct_1('#skF_13', '#skF_12')!='#skF_11'), inference(cnfTransformation, [status(thm)], [f_158])).
% 14.57/6.09  tff(c_146, plain, (v1_funct_1('#skF_13')), inference(cnfTransformation, [status(thm)], [f_158])).
% 14.57/6.09  tff(c_130, plain, (![A_75, C_77]: (k3_zfmisc_1(A_75, k1_xboole_0, C_77)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_133])).
% 14.57/6.09  tff(c_11354, plain, (![A_33445, B_33446, C_33447, D_33448]: (k3_zfmisc_1(k2_zfmisc_1(A_33445, B_33446), C_33447, D_33448)=k4_zfmisc_1(A_33445, B_33446, C_33447, D_33448))), inference(cnfTransformation, [status(thm)], [f_135])).
% 14.57/6.09  tff(c_11375, plain, (![A_33445, B_33446, C_77]: (k4_zfmisc_1(A_33445, B_33446, k1_xboole_0, C_77)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_130, c_11354])).
% 14.57/6.09  tff(c_128, plain, (![A_75, B_76]: (k3_zfmisc_1(A_75, B_76, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_133])).
% 14.57/6.09  tff(c_23012, plain, (![A_70845, B_70846, C_70847, D_70848]: (k2_zfmisc_1(k3_zfmisc_1(A_70845, B_70846, C_70847), D_70848)=k4_zfmisc_1(A_70845, B_70846, C_70847, D_70848))), inference(cnfTransformation, [status(thm)], [f_109])).
% 14.57/6.09  tff(c_23034, plain, (![A_75, B_76, D_70848]: (k4_zfmisc_1(A_75, B_76, k1_xboole_0, D_70848)=k2_zfmisc_1(k1_xboole_0, D_70848))), inference(superposition, [status(thm), theory('equality')], [c_128, c_23012])).
% 14.57/6.09  tff(c_23041, plain, (![D_70849]: (k2_zfmisc_1(k1_xboole_0, D_70849)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_11375, c_23034])).
% 14.57/6.09  tff(c_118, plain, (![A_69, C_71, B_70]: (r2_hidden(k2_mcart_1(A_69), C_71) | ~r2_hidden(A_69, k2_zfmisc_1(B_70, C_71)))), inference(cnfTransformation, [status(thm)], [f_115])).
% 14.57/6.09  tff(c_23091, plain, (![A_70853, D_70854]: (r2_hidden(k2_mcart_1(A_70853), D_70854) | ~r2_hidden(A_70853, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_23041, c_118])).
% 14.57/6.09  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 14.57/6.09  tff(c_23155, plain, (![D_70854, A_70853]: (~v1_xboole_0(D_70854) | ~r2_hidden(A_70853, k1_xboole_0))), inference(resolution, [status(thm)], [c_23091, c_2])).
% 14.57/6.09  tff(c_23156, plain, (![A_70853]: (~r2_hidden(A_70853, k1_xboole_0))), inference(splitLeft, [status(thm)], [c_23155])).
% 14.57/6.09  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 14.57/6.09  tff(c_372, plain, (![A_143, C_144, B_145]: (r2_hidden(k2_mcart_1(A_143), C_144) | ~r2_hidden(A_143, k2_zfmisc_1(B_145, C_144)))), inference(cnfTransformation, [status(thm)], [f_115])).
% 14.57/6.09  tff(c_23408, plain, (![B_70879, C_70880]: (r2_hidden(k2_mcart_1('#skF_1'(k2_zfmisc_1(B_70879, C_70880))), C_70880) | v1_xboole_0(k2_zfmisc_1(B_70879, C_70880)))), inference(resolution, [status(thm)], [c_4, c_372])).
% 14.57/6.09  tff(c_23464, plain, (![B_70879]: (v1_xboole_0(k2_zfmisc_1(B_70879, k1_xboole_0)))), inference(resolution, [status(thm)], [c_23408, c_23156])).
% 14.57/6.09  tff(c_24175, plain, (![A_71008, B_71009, C_71010]: (r2_hidden('#skF_2'(A_71008, B_71009, C_71010), A_71008) | r2_hidden('#skF_3'(A_71008, B_71009, C_71010), C_71010) | k3_xboole_0(A_71008, B_71009)=C_71010)), inference(cnfTransformation, [status(thm)], [f_40])).
% 14.57/6.09  tff(c_24302, plain, (![B_71011, C_71012]: (r2_hidden('#skF_3'(k1_xboole_0, B_71011, C_71012), C_71012) | k3_xboole_0(k1_xboole_0, B_71011)=C_71012)), inference(resolution, [status(thm)], [c_24175, c_23156])).
% 14.57/6.09  tff(c_24357, plain, (![B_71011]: (k3_xboole_0(k1_xboole_0, B_71011)=k1_xboole_0)), inference(resolution, [status(thm)], [c_24302, c_23156])).
% 14.57/6.09  tff(c_24368, plain, (![C_71012, B_71011]: (~v1_xboole_0(C_71012) | k3_xboole_0(k1_xboole_0, B_71011)=C_71012)), inference(resolution, [status(thm)], [c_24302, c_2])).
% 14.57/6.09  tff(c_24441, plain, (![C_71014]: (~v1_xboole_0(C_71014) | k1_xboole_0=C_71014)), inference(demodulation, [status(thm), theory('equality')], [c_24357, c_24368])).
% 14.57/6.09  tff(c_24498, plain, (![B_70879]: (k2_zfmisc_1(B_70879, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_23464, c_24441])).
% 14.57/6.09  tff(c_144, plain, (v1_funct_2('#skF_13', '#skF_10', k1_tarski('#skF_11'))), inference(cnfTransformation, [status(thm)], [f_158])).
% 14.57/6.09  tff(c_142, plain, (m1_subset_1('#skF_13', k1_zfmisc_1(k2_zfmisc_1('#skF_10', k1_tarski('#skF_11'))))), inference(cnfTransformation, [status(thm)], [f_158])).
% 14.57/6.09  tff(c_140, plain, (r2_hidden('#skF_12', '#skF_10')), inference(cnfTransformation, [status(thm)], [f_158])).
% 14.57/6.09  tff(c_32866, plain, (![D_108211, C_108212, B_108213, A_108214]: (r2_hidden(k1_funct_1(D_108211, C_108212), B_108213) | k1_xboole_0=B_108213 | ~r2_hidden(C_108212, A_108214) | ~m1_subset_1(D_108211, k1_zfmisc_1(k2_zfmisc_1(A_108214, B_108213))) | ~v1_funct_2(D_108211, A_108214, B_108213) | ~v1_funct_1(D_108211))), inference(cnfTransformation, [status(thm)], [f_147])).
% 14.57/6.09  tff(c_33742, plain, (![D_108888, B_108889]: (r2_hidden(k1_funct_1(D_108888, '#skF_12'), B_108889) | k1_xboole_0=B_108889 | ~m1_subset_1(D_108888, k1_zfmisc_1(k2_zfmisc_1('#skF_10', B_108889))) | ~v1_funct_2(D_108888, '#skF_10', B_108889) | ~v1_funct_1(D_108888))), inference(resolution, [status(thm)], [c_140, c_32866])).
% 14.57/6.09  tff(c_33773, plain, (r2_hidden(k1_funct_1('#skF_13', '#skF_12'), k1_tarski('#skF_11')) | k1_tarski('#skF_11')=k1_xboole_0 | ~v1_funct_2('#skF_13', '#skF_10', k1_tarski('#skF_11')) | ~v1_funct_1('#skF_13')), inference(resolution, [status(thm)], [c_142, c_33742])).
% 14.57/6.09  tff(c_33778, plain, (r2_hidden(k1_funct_1('#skF_13', '#skF_12'), k1_tarski('#skF_11')) | k1_tarski('#skF_11')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_146, c_144, c_33773])).
% 14.57/6.09  tff(c_33779, plain, (k1_tarski('#skF_11')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_33778])).
% 14.57/6.09  tff(c_112, plain, (![A_62]: (~v1_xboole_0(k1_zfmisc_1(A_62)))), inference(cnfTransformation, [status(thm)], [f_101])).
% 14.57/6.09  tff(c_270, plain, (![A_114, B_115]: (r2_hidden(A_114, B_115) | v1_xboole_0(B_115) | ~m1_subset_1(A_114, B_115))), inference(cnfTransformation, [status(thm)], [f_107])).
% 14.57/6.09  tff(c_58, plain, (![C_51, A_47]: (r1_tarski(C_51, A_47) | ~r2_hidden(C_51, k1_zfmisc_1(A_47)))), inference(cnfTransformation, [status(thm)], [f_74])).
% 14.57/6.09  tff(c_274, plain, (![A_114, A_47]: (r1_tarski(A_114, A_47) | v1_xboole_0(k1_zfmisc_1(A_47)) | ~m1_subset_1(A_114, k1_zfmisc_1(A_47)))), inference(resolution, [status(thm)], [c_270, c_58])).
% 14.57/6.09  tff(c_282, plain, (![A_116, A_117]: (r1_tarski(A_116, A_117) | ~m1_subset_1(A_116, k1_zfmisc_1(A_117)))), inference(negUnitSimplification, [status(thm)], [c_112, c_274])).
% 14.57/6.09  tff(c_286, plain, (r1_tarski('#skF_13', k2_zfmisc_1('#skF_10', k1_tarski('#skF_11')))), inference(resolution, [status(thm)], [c_142, c_282])).
% 14.57/6.09  tff(c_24, plain, (![A_11, B_12]: (k3_xboole_0(A_11, B_12)=A_11 | ~r1_tarski(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_44])).
% 14.57/6.09  tff(c_301, plain, (k3_xboole_0('#skF_13', k2_zfmisc_1('#skF_10', k1_tarski('#skF_11')))='#skF_13'), inference(resolution, [status(thm)], [c_286, c_24])).
% 14.57/6.09  tff(c_309, plain, (![D_121, B_122, A_123]: (r2_hidden(D_121, B_122) | ~r2_hidden(D_121, k3_xboole_0(A_123, B_122)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 14.57/6.09  tff(c_312, plain, (![D_121]: (r2_hidden(D_121, k2_zfmisc_1('#skF_10', k1_tarski('#skF_11'))) | ~r2_hidden(D_121, '#skF_13'))), inference(superposition, [status(thm), theory('equality')], [c_301, c_309])).
% 14.57/6.09  tff(c_381, plain, (![D_121]: (r2_hidden(k2_mcart_1(D_121), k1_tarski('#skF_11')) | ~r2_hidden(D_121, '#skF_13'))), inference(resolution, [status(thm)], [c_312, c_372])).
% 14.57/6.09  tff(c_44, plain, (![A_19]: (k2_tarski(A_19, A_19)=k1_tarski(A_19))), inference(cnfTransformation, [status(thm)], [f_55])).
% 14.57/6.09  tff(c_440, plain, (![D_184, B_185, A_186]: (D_184=B_185 | D_184=A_186 | ~r2_hidden(D_184, k2_tarski(A_186, B_185)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 14.57/6.09  tff(c_468, plain, (![D_187, A_188]: (D_187=A_188 | D_187=A_188 | ~r2_hidden(D_187, k1_tarski(A_188)))), inference(superposition, [status(thm), theory('equality')], [c_44, c_440])).
% 14.57/6.09  tff(c_492, plain, (![D_189]: (k2_mcart_1(D_189)='#skF_11' | ~r2_hidden(D_189, '#skF_13'))), inference(resolution, [status(thm)], [c_381, c_468])).
% 14.57/6.09  tff(c_502, plain, (k2_mcart_1('#skF_1'('#skF_13'))='#skF_11' | v1_xboole_0('#skF_13')), inference(resolution, [status(thm)], [c_4, c_492])).
% 14.57/6.09  tff(c_518, plain, (v1_xboole_0('#skF_13')), inference(splitLeft, [status(thm)], [c_502])).
% 14.57/6.09  tff(c_247, plain, (![C_107, A_108]: (r1_tarski(C_107, A_108) | ~r2_hidden(C_107, k1_zfmisc_1(A_108)))), inference(cnfTransformation, [status(thm)], [f_74])).
% 14.57/6.09  tff(c_251, plain, (![A_108]: (r1_tarski('#skF_1'(k1_zfmisc_1(A_108)), A_108) | v1_xboole_0(k1_zfmisc_1(A_108)))), inference(resolution, [status(thm)], [c_4, c_247])).
% 14.57/6.09  tff(c_254, plain, (![A_108]: (r1_tarski('#skF_1'(k1_zfmisc_1(A_108)), A_108))), inference(negUnitSimplification, [status(thm)], [c_112, c_251])).
% 14.57/6.09  tff(c_256, plain, (![A_110, B_111]: (k3_xboole_0(A_110, B_111)=A_110 | ~r1_tarski(A_110, B_111))), inference(cnfTransformation, [status(thm)], [f_44])).
% 14.57/6.09  tff(c_260, plain, (![A_108]: (k3_xboole_0('#skF_1'(k1_zfmisc_1(A_108)), A_108)='#skF_1'(k1_zfmisc_1(A_108)))), inference(resolution, [status(thm)], [c_254, c_256])).
% 14.57/6.09  tff(c_533, plain, (![A_200, B_201]: (r2_hidden('#skF_1'(k3_xboole_0(A_200, B_201)), B_201) | v1_xboole_0(k3_xboole_0(A_200, B_201)))), inference(resolution, [status(thm)], [c_4, c_309])).
% 14.57/6.09  tff(c_594, plain, (![B_202, A_203]: (~v1_xboole_0(B_202) | v1_xboole_0(k3_xboole_0(A_203, B_202)))), inference(resolution, [status(thm)], [c_533, c_2])).
% 14.57/6.09  tff(c_597, plain, (![A_108]: (~v1_xboole_0(A_108) | v1_xboole_0('#skF_1'(k1_zfmisc_1(A_108))))), inference(superposition, [status(thm), theory('equality')], [c_260, c_594])).
% 14.57/6.09  tff(c_1516, plain, (![B_338, C_339]: (r2_hidden(k2_mcart_1('#skF_1'(k2_zfmisc_1(B_338, C_339))), C_339) | v1_xboole_0(k2_zfmisc_1(B_338, C_339)))), inference(resolution, [status(thm)], [c_4, c_372])).
% 14.57/6.09  tff(c_955, plain, (![D_233, A_234, B_235]: (r2_hidden(D_233, k3_xboole_0(A_234, B_235)) | ~r2_hidden(D_233, B_235) | ~r2_hidden(D_233, A_234))), inference(cnfTransformation, [status(thm)], [f_40])).
% 14.57/6.09  tff(c_1139, plain, (![A_250, B_251, D_252]: (~v1_xboole_0(k3_xboole_0(A_250, B_251)) | ~r2_hidden(D_252, B_251) | ~r2_hidden(D_252, A_250))), inference(resolution, [status(thm)], [c_955, c_2])).
% 14.57/6.09  tff(c_1151, plain, (![D_252]: (~v1_xboole_0('#skF_13') | ~r2_hidden(D_252, k2_zfmisc_1('#skF_10', k1_tarski('#skF_11'))) | ~r2_hidden(D_252, '#skF_13'))), inference(superposition, [status(thm), theory('equality')], [c_301, c_1139])).
% 14.57/6.09  tff(c_1158, plain, (![D_253]: (~r2_hidden(D_253, k2_zfmisc_1('#skF_10', k1_tarski('#skF_11'))) | ~r2_hidden(D_253, '#skF_13'))), inference(demodulation, [status(thm), theory('equality')], [c_518, c_1151])).
% 14.57/6.09  tff(c_1185, plain, (![D_121]: (~r2_hidden(D_121, '#skF_13'))), inference(resolution, [status(thm)], [c_312, c_1158])).
% 14.57/6.09  tff(c_1572, plain, (![B_338]: (v1_xboole_0(k2_zfmisc_1(B_338, '#skF_13')))), inference(resolution, [status(thm)], [c_1516, c_1185])).
% 14.57/6.09  tff(c_2383, plain, (![A_423, B_424, C_425]: (r2_hidden('#skF_2'(A_423, B_424, C_425), A_423) | r2_hidden('#skF_3'(A_423, B_424, C_425), C_425) | k3_xboole_0(A_423, B_424)=C_425)), inference(cnfTransformation, [status(thm)], [f_40])).
% 14.57/6.09  tff(c_18, plain, (![A_5, B_6, C_7]: (~r2_hidden('#skF_2'(A_5, B_6, C_7), C_7) | r2_hidden('#skF_3'(A_5, B_6, C_7), C_7) | k3_xboole_0(A_5, B_6)=C_7)), inference(cnfTransformation, [status(thm)], [f_40])).
% 14.57/6.09  tff(c_2525, plain, (![A_426, B_427]: (r2_hidden('#skF_3'(A_426, B_427, A_426), A_426) | k3_xboole_0(A_426, B_427)=A_426)), inference(resolution, [status(thm)], [c_2383, c_18])).
% 14.57/6.09  tff(c_2585, plain, (![B_427]: (k3_xboole_0('#skF_13', B_427)='#skF_13')), inference(resolution, [status(thm)], [c_2525, c_1185])).
% 14.57/6.09  tff(c_2500, plain, (![B_424, C_425]: (r2_hidden('#skF_3'('#skF_13', B_424, C_425), C_425) | k3_xboole_0('#skF_13', B_424)=C_425)), inference(resolution, [status(thm)], [c_2383, c_1185])).
% 14.57/6.09  tff(c_2737, plain, (![B_430, C_431]: (r2_hidden('#skF_3'('#skF_13', B_430, C_431), C_431) | C_431='#skF_13')), inference(demodulation, [status(thm), theory('equality')], [c_2585, c_2500])).
% 14.57/6.09  tff(c_2848, plain, (![C_432]: (~v1_xboole_0(C_432) | C_432='#skF_13')), inference(resolution, [status(thm)], [c_2737, c_2])).
% 14.57/6.09  tff(c_2920, plain, (![B_338]: (k2_zfmisc_1(B_338, '#skF_13')='#skF_13')), inference(resolution, [status(thm)], [c_1572, c_2848])).
% 14.57/6.09  tff(c_805, plain, (![A_213, B_214, C_215, D_216]: (k3_zfmisc_1(k2_zfmisc_1(A_213, B_214), C_215, D_216)=k4_zfmisc_1(A_213, B_214, C_215, D_216))), inference(cnfTransformation, [status(thm)], [f_135])).
% 14.57/6.09  tff(c_812, plain, (![A_213, B_214, D_216]: (k4_zfmisc_1(A_213, B_214, k1_xboole_0, D_216)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_805, c_130])).
% 14.57/6.09  tff(c_883, plain, (![A_224, B_225, C_226, D_227]: (k2_zfmisc_1(k3_zfmisc_1(A_224, B_225, C_226), D_227)=k4_zfmisc_1(A_224, B_225, C_226, D_227))), inference(cnfTransformation, [status(thm)], [f_109])).
% 14.57/6.09  tff(c_905, plain, (![A_75, B_76, D_227]: (k4_zfmisc_1(A_75, B_76, k1_xboole_0, D_227)=k2_zfmisc_1(k1_xboole_0, D_227))), inference(superposition, [status(thm), theory('equality')], [c_128, c_883])).
% 14.57/6.09  tff(c_912, plain, (![D_228]: (k2_zfmisc_1(k1_xboole_0, D_228)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_812, c_905])).
% 14.57/6.09  tff(c_974, plain, (![A_236, D_237]: (r2_hidden(k2_mcart_1(A_236), D_237) | ~r2_hidden(A_236, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_912, c_118])).
% 14.57/6.09  tff(c_1032, plain, (![D_237, A_236]: (~v1_xboole_0(D_237) | ~r2_hidden(A_236, k1_xboole_0))), inference(resolution, [status(thm)], [c_974, c_2])).
% 14.57/6.09  tff(c_1033, plain, (![A_236]: (~r2_hidden(A_236, k1_xboole_0))), inference(splitLeft, [status(thm)], [c_1032])).
% 14.57/6.09  tff(c_2799, plain, (k1_xboole_0='#skF_13'), inference(resolution, [status(thm)], [c_2737, c_1033])).
% 14.57/6.09  tff(c_136, plain, (![D_85, C_84, B_83, A_82]: (r2_hidden(k1_funct_1(D_85, C_84), B_83) | k1_xboole_0=B_83 | ~r2_hidden(C_84, A_82) | ~m1_subset_1(D_85, k1_zfmisc_1(k2_zfmisc_1(A_82, B_83))) | ~v1_funct_2(D_85, A_82, B_83) | ~v1_funct_1(D_85))), inference(cnfTransformation, [status(thm)], [f_147])).
% 14.57/6.09  tff(c_10831, plain, (![D_32249, C_32250, B_32251, A_32252]: (r2_hidden(k1_funct_1(D_32249, C_32250), B_32251) | B_32251='#skF_13' | ~r2_hidden(C_32250, A_32252) | ~m1_subset_1(D_32249, k1_zfmisc_1(k2_zfmisc_1(A_32252, B_32251))) | ~v1_funct_2(D_32249, A_32252, B_32251) | ~v1_funct_1(D_32249))), inference(demodulation, [status(thm), theory('equality')], [c_2799, c_136])).
% 14.57/6.09  tff(c_11130, plain, (![D_32756, B_32757]: (r2_hidden(k1_funct_1(D_32756, '#skF_12'), B_32757) | B_32757='#skF_13' | ~m1_subset_1(D_32756, k1_zfmisc_1(k2_zfmisc_1('#skF_10', B_32757))) | ~v1_funct_2(D_32756, '#skF_10', B_32757) | ~v1_funct_1(D_32756))), inference(resolution, [status(thm)], [c_140, c_10831])).
% 14.57/6.09  tff(c_11161, plain, (r2_hidden(k1_funct_1('#skF_13', '#skF_12'), k1_tarski('#skF_11')) | k1_tarski('#skF_11')='#skF_13' | ~v1_funct_2('#skF_13', '#skF_10', k1_tarski('#skF_11')) | ~v1_funct_1('#skF_13')), inference(resolution, [status(thm)], [c_142, c_11130])).
% 14.57/6.09  tff(c_11166, plain, (r2_hidden(k1_funct_1('#skF_13', '#skF_12'), k1_tarski('#skF_11')) | k1_tarski('#skF_11')='#skF_13'), inference(demodulation, [status(thm), theory('equality')], [c_146, c_144, c_11161])).
% 14.57/6.09  tff(c_11185, plain, (k1_tarski('#skF_11')='#skF_13'), inference(splitLeft, [status(thm)], [c_11166])).
% 14.57/6.09  tff(c_323, plain, (![D_124]: (r2_hidden(D_124, k2_zfmisc_1('#skF_10', k1_tarski('#skF_11'))) | ~r2_hidden(D_124, '#skF_13'))), inference(superposition, [status(thm), theory('equality')], [c_301, c_309])).
% 14.57/6.09  tff(c_327, plain, (![D_124]: (~v1_xboole_0(k2_zfmisc_1('#skF_10', k1_tarski('#skF_11'))) | ~r2_hidden(D_124, '#skF_13'))), inference(resolution, [status(thm)], [c_323, c_2])).
% 14.57/6.09  tff(c_354, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_10', k1_tarski('#skF_11')))), inference(splitLeft, [status(thm)], [c_327])).
% 14.57/6.09  tff(c_11186, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_10', '#skF_13'))), inference(demodulation, [status(thm), theory('equality')], [c_11185, c_354])).
% 14.57/6.09  tff(c_11192, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_518, c_2920, c_11186])).
% 14.57/6.09  tff(c_11193, plain, (r2_hidden(k1_funct_1('#skF_13', '#skF_12'), k1_tarski('#skF_11'))), inference(splitRight, [status(thm)], [c_11166])).
% 14.57/6.09  tff(c_454, plain, (![D_184, A_19]: (D_184=A_19 | D_184=A_19 | ~r2_hidden(D_184, k1_tarski(A_19)))), inference(superposition, [status(thm), theory('equality')], [c_44, c_440])).
% 14.57/6.09  tff(c_11199, plain, (k1_funct_1('#skF_13', '#skF_12')='#skF_11'), inference(resolution, [status(thm)], [c_11193, c_454])).
% 14.57/6.09  tff(c_11207, plain, $false, inference(negUnitSimplification, [status(thm)], [c_138, c_138, c_11199])).
% 14.57/6.09  tff(c_11208, plain, (![D_237]: (~v1_xboole_0(D_237))), inference(splitRight, [status(thm)], [c_1032])).
% 14.57/6.09  tff(c_577, plain, (![A_108]: (r2_hidden('#skF_1'('#skF_1'(k1_zfmisc_1(A_108))), A_108) | v1_xboole_0(k3_xboole_0('#skF_1'(k1_zfmisc_1(A_108)), A_108)))), inference(superposition, [status(thm), theory('equality')], [c_260, c_533])).
% 14.57/6.09  tff(c_752, plain, (![A_212]: (r2_hidden('#skF_1'('#skF_1'(k1_zfmisc_1(A_212))), A_212) | v1_xboole_0('#skF_1'(k1_zfmisc_1(A_212))))), inference(demodulation, [status(thm), theory('equality')], [c_260, c_577])).
% 14.57/6.09  tff(c_483, plain, (![D_121]: (k2_mcart_1(D_121)='#skF_11' | ~r2_hidden(D_121, '#skF_13'))), inference(resolution, [status(thm)], [c_381, c_468])).
% 14.57/6.09  tff(c_794, plain, (k2_mcart_1('#skF_1'('#skF_1'(k1_zfmisc_1('#skF_13'))))='#skF_11' | v1_xboole_0('#skF_1'(k1_zfmisc_1('#skF_13')))), inference(resolution, [status(thm)], [c_752, c_483])).
% 14.57/6.09  tff(c_881, plain, (v1_xboole_0('#skF_1'(k1_zfmisc_1('#skF_13')))), inference(splitLeft, [status(thm)], [c_794])).
% 14.57/6.09  tff(c_11221, plain, $false, inference(negUnitSimplification, [status(thm)], [c_11208, c_881])).
% 14.57/6.09  tff(c_11223, plain, (~v1_xboole_0('#skF_1'(k1_zfmisc_1('#skF_13')))), inference(splitRight, [status(thm)], [c_794])).
% 14.57/6.09  tff(c_11226, plain, (~v1_xboole_0('#skF_13')), inference(resolution, [status(thm)], [c_597, c_11223])).
% 14.57/6.09  tff(c_11230, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_518, c_11226])).
% 14.57/6.09  tff(c_11232, plain, (~v1_xboole_0('#skF_13')), inference(splitRight, [status(thm)], [c_502])).
% 14.57/6.09  tff(c_11272, plain, (![A_33440, B_33441]: (r2_hidden('#skF_1'(k3_xboole_0(A_33440, B_33441)), B_33441) | v1_xboole_0(k3_xboole_0(A_33440, B_33441)))), inference(resolution, [status(thm)], [c_4, c_309])).
% 14.57/6.09  tff(c_11319, plain, (r2_hidden('#skF_1'('#skF_13'), k2_zfmisc_1('#skF_10', k1_tarski('#skF_11'))) | v1_xboole_0(k3_xboole_0('#skF_13', k2_zfmisc_1('#skF_10', k1_tarski('#skF_11'))))), inference(superposition, [status(thm), theory('equality')], [c_301, c_11272])).
% 14.57/6.09  tff(c_11332, plain, (r2_hidden('#skF_1'('#skF_13'), k2_zfmisc_1('#skF_10', k1_tarski('#skF_11'))) | v1_xboole_0('#skF_13')), inference(demodulation, [status(thm), theory('equality')], [c_301, c_11319])).
% 14.57/6.09  tff(c_11333, plain, (r2_hidden('#skF_1'('#skF_13'), k2_zfmisc_1('#skF_10', k1_tarski('#skF_11')))), inference(negUnitSimplification, [status(thm)], [c_11232, c_11332])).
% 14.57/6.09  tff(c_33797, plain, (r2_hidden('#skF_1'('#skF_13'), k2_zfmisc_1('#skF_10', k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_33779, c_11333])).
% 14.57/6.09  tff(c_33829, plain, (r2_hidden('#skF_1'('#skF_13'), k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_24498, c_33797])).
% 14.57/6.09  tff(c_33831, plain, $false, inference(negUnitSimplification, [status(thm)], [c_23156, c_33829])).
% 14.57/6.09  tff(c_33832, plain, (r2_hidden(k1_funct_1('#skF_13', '#skF_12'), k1_tarski('#skF_11'))), inference(splitRight, [status(thm)], [c_33778])).
% 14.57/6.09  tff(c_33838, plain, (k1_funct_1('#skF_13', '#skF_12')='#skF_11'), inference(resolution, [status(thm)], [c_33832, c_454])).
% 14.57/6.09  tff(c_33846, plain, $false, inference(negUnitSimplification, [status(thm)], [c_138, c_138, c_33838])).
% 14.57/6.09  tff(c_33847, plain, (![D_70854]: (~v1_xboole_0(D_70854))), inference(splitRight, [status(thm)], [c_23155])).
% 14.57/6.09  tff(c_287, plain, (![D_118, A_119, B_120]: (r2_hidden(D_118, A_119) | ~r2_hidden(D_118, k3_xboole_0(A_119, B_120)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 14.57/6.09  tff(c_297, plain, (![A_119, B_120]: (r2_hidden('#skF_1'(k3_xboole_0(A_119, B_120)), A_119) | v1_xboole_0(k3_xboole_0(A_119, B_120)))), inference(resolution, [status(thm)], [c_4, c_287])).
% 14.57/6.09  tff(c_34029, plain, (![A_109394, B_109395]: (r2_hidden('#skF_1'(k3_xboole_0(A_109394, B_109395)), A_109394))), inference(negUnitSimplification, [status(thm)], [c_33847, c_297])).
% 14.57/6.09  tff(c_34108, plain, (![A_109397, B_109398]: ('#skF_1'(k3_xboole_0(k1_tarski(A_109397), B_109398))=A_109397)), inference(resolution, [status(thm)], [c_34029, c_454])).
% 14.57/6.09  tff(c_322, plain, (![A_123, B_122]: (r2_hidden('#skF_1'(k3_xboole_0(A_123, B_122)), B_122) | v1_xboole_0(k3_xboole_0(A_123, B_122)))), inference(resolution, [status(thm)], [c_4, c_309])).
% 14.57/6.09  tff(c_33855, plain, (![A_123, B_122]: (r2_hidden('#skF_1'(k3_xboole_0(A_123, B_122)), B_122))), inference(negUnitSimplification, [status(thm)], [c_33847, c_322])).
% 14.57/6.09  tff(c_34120, plain, (![A_109397, B_109398]: (r2_hidden(A_109397, B_109398))), inference(superposition, [status(thm), theory('equality')], [c_34108, c_33855])).
% 14.57/6.09  tff(c_34178, plain, (![D_109401, A_109402]: (D_109401=A_109402)), inference(demodulation, [status(thm), theory('equality')], [c_34120, c_454])).
% 14.57/6.09  tff(c_36504, plain, (![D_109401]: (D_109401!='#skF_11')), inference(superposition, [status(thm), theory('equality')], [c_34178, c_138])).
% 14.57/6.09  tff(c_36582, plain, $false, inference(reflexivity, [status(thm), theory('equality')], [c_36504])).
% 14.57/6.09  tff(c_36584, plain, (v1_xboole_0(k2_zfmisc_1('#skF_10', k1_tarski('#skF_11')))), inference(splitRight, [status(thm)], [c_327])).
% 14.57/6.09  tff(c_38543, plain, (![A_111520, B_111521, C_111522]: (r2_hidden('#skF_2'(A_111520, B_111521, C_111522), B_111521) | r2_hidden('#skF_3'(A_111520, B_111521, C_111522), C_111522) | k3_xboole_0(A_111520, B_111521)=C_111522)), inference(cnfTransformation, [status(thm)], [f_40])).
% 14.57/6.09  tff(c_36583, plain, (![D_124]: (~r2_hidden(D_124, '#skF_13'))), inference(splitRight, [status(thm)], [c_327])).
% 14.57/6.09  tff(c_38680, plain, (![A_111523, C_111524]: (r2_hidden('#skF_3'(A_111523, '#skF_13', C_111524), C_111524) | k3_xboole_0(A_111523, '#skF_13')=C_111524)), inference(resolution, [status(thm)], [c_38543, c_36583])).
% 14.57/6.09  tff(c_38746, plain, (![A_111523]: (k3_xboole_0(A_111523, '#skF_13')='#skF_13')), inference(resolution, [status(thm)], [c_38680, c_36583])).
% 14.57/6.09  tff(c_38751, plain, (![C_111524, A_111523]: (~v1_xboole_0(C_111524) | k3_xboole_0(A_111523, '#skF_13')=C_111524)), inference(resolution, [status(thm)], [c_38680, c_2])).
% 14.57/6.09  tff(c_39158, plain, (![C_111531]: (~v1_xboole_0(C_111531) | C_111531='#skF_13')), inference(demodulation, [status(thm), theory('equality')], [c_38746, c_38751])).
% 14.57/6.09  tff(c_39221, plain, (k2_zfmisc_1('#skF_10', k1_tarski('#skF_11'))='#skF_13'), inference(resolution, [status(thm)], [c_36584, c_39158])).
% 14.57/6.09  tff(c_39487, plain, (m1_subset_1('#skF_13', k1_zfmisc_1('#skF_13'))), inference(demodulation, [status(thm), theory('equality')], [c_39221, c_142])).
% 14.57/6.09  tff(c_37142, plain, (![A_111335, B_111336, C_111337, D_111338]: (k3_zfmisc_1(k2_zfmisc_1(A_111335, B_111336), C_111337, D_111338)=k4_zfmisc_1(A_111335, B_111336, C_111337, D_111338))), inference(cnfTransformation, [status(thm)], [f_135])).
% 14.57/6.09  tff(c_37155, plain, (![A_111335, B_111336, D_111338]: (k4_zfmisc_1(A_111335, B_111336, k1_xboole_0, D_111338)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_37142, c_130])).
% 14.57/6.09  tff(c_37038, plain, (![A_111315, B_111316, C_111317, D_111318]: (k2_zfmisc_1(k3_zfmisc_1(A_111315, B_111316, C_111317), D_111318)=k4_zfmisc_1(A_111315, B_111316, C_111317, D_111318))), inference(cnfTransformation, [status(thm)], [f_109])).
% 14.57/6.09  tff(c_37054, plain, (![A_75, B_76, D_111318]: (k4_zfmisc_1(A_75, B_76, k1_xboole_0, D_111318)=k2_zfmisc_1(k1_xboole_0, D_111318))), inference(superposition, [status(thm), theory('equality')], [c_128, c_37038])).
% 14.57/6.09  tff(c_37200, plain, (![D_111342]: (k2_zfmisc_1(k1_xboole_0, D_111342)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_37155, c_37054])).
% 14.57/6.09  tff(c_37369, plain, (![A_111357, D_111358]: (r2_hidden(k2_mcart_1(A_111357), D_111358) | ~r2_hidden(A_111357, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_37200, c_118])).
% 14.57/6.09  tff(c_37415, plain, (![A_111357]: (~r2_hidden(A_111357, k1_xboole_0))), inference(resolution, [status(thm)], [c_37369, c_36583])).
% 14.57/6.09  tff(c_38740, plain, (![A_111523]: (k3_xboole_0(A_111523, '#skF_13')=k1_xboole_0)), inference(resolution, [status(thm)], [c_38680, c_37415])).
% 14.57/6.09  tff(c_38850, plain, (k1_xboole_0='#skF_13'), inference(demodulation, [status(thm), theory('equality')], [c_38746, c_38740])).
% 14.57/6.09  tff(c_43421, plain, (![D_137187, C_137188, B_137189, A_137190]: (r2_hidden(k1_funct_1(D_137187, C_137188), B_137189) | B_137189='#skF_13' | ~r2_hidden(C_137188, A_137190) | ~m1_subset_1(D_137187, k1_zfmisc_1(k2_zfmisc_1(A_137190, B_137189))) | ~v1_funct_2(D_137187, A_137190, B_137189) | ~v1_funct_1(D_137187))), inference(demodulation, [status(thm), theory('equality')], [c_38850, c_136])).
% 14.57/6.09  tff(c_43551, plain, (![D_137357, B_137358]: (r2_hidden(k1_funct_1(D_137357, '#skF_12'), B_137358) | B_137358='#skF_13' | ~m1_subset_1(D_137357, k1_zfmisc_1(k2_zfmisc_1('#skF_10', B_137358))) | ~v1_funct_2(D_137357, '#skF_10', B_137358) | ~v1_funct_1(D_137357))), inference(resolution, [status(thm)], [c_140, c_43421])).
% 14.57/6.09  tff(c_43562, plain, (![D_137357]: (r2_hidden(k1_funct_1(D_137357, '#skF_12'), k1_tarski('#skF_11')) | k1_tarski('#skF_11')='#skF_13' | ~m1_subset_1(D_137357, k1_zfmisc_1('#skF_13')) | ~v1_funct_2(D_137357, '#skF_10', k1_tarski('#skF_11')) | ~v1_funct_1(D_137357))), inference(superposition, [status(thm), theory('equality')], [c_39221, c_43551])).
% 14.57/6.09  tff(c_43694, plain, (k1_tarski('#skF_11')='#skF_13'), inference(splitLeft, [status(thm)], [c_43562])).
% 14.57/6.09  tff(c_181, plain, (![A_97]: (k2_tarski(A_97, A_97)=k1_tarski(A_97))), inference(cnfTransformation, [status(thm)], [f_55])).
% 14.57/6.09  tff(c_28, plain, (![D_18, A_13]: (r2_hidden(D_18, k2_tarski(A_13, D_18)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 14.57/6.09  tff(c_189, plain, (![A_97]: (r2_hidden(A_97, k1_tarski(A_97)))), inference(superposition, [status(thm), theory('equality')], [c_181, c_28])).
% 14.57/6.09  tff(c_43728, plain, (r2_hidden('#skF_11', '#skF_13')), inference(superposition, [status(thm), theory('equality')], [c_43694, c_189])).
% 14.57/6.09  tff(c_43740, plain, $false, inference(negUnitSimplification, [status(thm)], [c_36583, c_43728])).
% 14.57/6.09  tff(c_44356, plain, (![D_139208]: (r2_hidden(k1_funct_1(D_139208, '#skF_12'), k1_tarski('#skF_11')) | ~m1_subset_1(D_139208, k1_zfmisc_1('#skF_13')) | ~v1_funct_2(D_139208, '#skF_10', k1_tarski('#skF_11')) | ~v1_funct_1(D_139208))), inference(splitRight, [status(thm)], [c_43562])).
% 14.57/6.09  tff(c_36652, plain, (![D_111275, B_111276, A_111277]: (D_111275=B_111276 | D_111275=A_111277 | ~r2_hidden(D_111275, k2_tarski(A_111277, B_111276)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 14.57/6.09  tff(c_36666, plain, (![D_111275, A_19]: (D_111275=A_19 | D_111275=A_19 | ~r2_hidden(D_111275, k1_tarski(A_19)))), inference(superposition, [status(thm), theory('equality')], [c_44, c_36652])).
% 14.57/6.09  tff(c_45640, plain, (![D_140894]: (k1_funct_1(D_140894, '#skF_12')='#skF_11' | ~m1_subset_1(D_140894, k1_zfmisc_1('#skF_13')) | ~v1_funct_2(D_140894, '#skF_10', k1_tarski('#skF_11')) | ~v1_funct_1(D_140894))), inference(resolution, [status(thm)], [c_44356, c_36666])).
% 14.57/6.09  tff(c_45643, plain, (k1_funct_1('#skF_13', '#skF_12')='#skF_11' | ~m1_subset_1('#skF_13', k1_zfmisc_1('#skF_13')) | ~v1_funct_1('#skF_13')), inference(resolution, [status(thm)], [c_144, c_45640])).
% 14.57/6.09  tff(c_45646, plain, (k1_funct_1('#skF_13', '#skF_12')='#skF_11'), inference(demodulation, [status(thm), theory('equality')], [c_146, c_39487, c_45643])).
% 14.57/6.09  tff(c_45648, plain, $false, inference(negUnitSimplification, [status(thm)], [c_138, c_45646])).
% 14.57/6.09  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 14.57/6.09  
% 14.57/6.09  Inference rules
% 14.57/6.09  ----------------------
% 14.57/6.09  #Ref     : 1
% 14.57/6.09  #Sup     : 9011
% 14.57/6.09  #Fact    : 30
% 14.57/6.09  #Define  : 0
% 14.57/6.09  #Split   : 23
% 14.57/6.09  #Chain   : 0
% 14.57/6.09  #Close   : 0
% 14.57/6.09  
% 14.57/6.09  Ordering : KBO
% 14.57/6.09  
% 14.57/6.09  Simplification rules
% 14.57/6.09  ----------------------
% 14.57/6.09  #Subsume      : 1575
% 14.57/6.09  #Demod        : 3655
% 14.57/6.09  #Tautology    : 3610
% 14.57/6.09  #SimpNegUnit  : 389
% 14.57/6.09  #BackRed      : 260
% 14.57/6.09  
% 14.57/6.09  #Partial instantiations: 50280
% 14.57/6.09  #Strategies tried      : 1
% 14.57/6.09  
% 14.57/6.09  Timing (in seconds)
% 14.57/6.09  ----------------------
% 14.57/6.10  Preprocessing        : 0.39
% 14.57/6.10  Parsing              : 0.19
% 14.57/6.10  CNF conversion       : 0.03
% 14.57/6.10  Main loop            : 4.92
% 14.57/6.10  Inferencing          : 1.91
% 14.57/6.10  Reduction            : 1.54
% 14.57/6.10  Demodulation         : 1.15
% 14.57/6.10  BG Simplification    : 0.14
% 14.57/6.10  Subsumption          : 1.04
% 14.57/6.10  Abstraction          : 0.18
% 14.57/6.10  MUC search           : 0.00
% 14.57/6.10  Cooper               : 0.00
% 14.57/6.10  Total                : 5.37
% 14.57/6.10  Index Insertion      : 0.00
% 14.57/6.10  Index Deletion       : 0.00
% 14.57/6.10  Index Matching       : 0.00
% 14.57/6.10  BG Taut test         : 0.00
%------------------------------------------------------------------------------
