%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:10:09 EST 2020

% Result     : Theorem 4.01s
% Output     : CNFRefutation 4.34s
% Verified   : 
% Statistics : Number of formulae       :  167 ( 482 expanded)
%              Number of leaves         :   33 ( 167 expanded)
%              Depth                    :    9
%              Number of atoms          :  251 (1291 expanded)
%              Number of equality atoms :   93 ( 389 expanded)
%              Maximal formula depth    :   16 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k7_mcart_1 > k6_mcart_1 > k5_mcart_1 > k3_zfmisc_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_mcart_1 > k1_zfmisc_1 > k1_mcart_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_8 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k7_mcart_1,type,(
    k7_mcart_1: ( $i * $i * $i * $i ) > $i )).

tff(k3_zfmisc_1,type,(
    k3_zfmisc_1: ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff(k5_mcart_1,type,(
    k5_mcart_1: ( $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_mcart_1,type,(
    k2_mcart_1: $i > $i )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff(k6_mcart_1,type,(
    k6_mcart_1: ( $i * $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_mcart_1,type,(
    k1_mcart_1: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_105,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( m1_subset_1(D,k1_zfmisc_1(A))
       => ! [E] :
            ( m1_subset_1(E,k1_zfmisc_1(B))
           => ! [F] :
                ( m1_subset_1(F,k1_zfmisc_1(C))
               => ! [G] :
                    ( m1_subset_1(G,k3_zfmisc_1(A,B,C))
                   => ( r2_hidden(G,k3_zfmisc_1(D,E,F))
                     => ( r2_hidden(k5_mcart_1(A,B,C,G),D)
                        & r2_hidden(k6_mcart_1(A,B,C,G),E)
                        & r2_hidden(k7_mcart_1(A,B,C,G),F) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t76_mcart_1)).

tff(f_46,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_xboole_0(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_subset_1)).

tff(f_59,axiom,(
    ! [A,B,C] : k3_zfmisc_1(A,B,C) = k2_zfmisc_1(k2_zfmisc_1(A,B),C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_zfmisc_1)).

tff(f_65,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k2_zfmisc_1(B,C))
     => ( r2_hidden(k1_mcart_1(A),B)
        & r2_hidden(k2_mcart_1(A),C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_mcart_1)).

tff(f_85,axiom,(
    ! [A,B,C] :
      ~ ( A != k1_xboole_0
        & B != k1_xboole_0
        & C != k1_xboole_0
        & ~ ! [D] :
              ( m1_subset_1(D,k3_zfmisc_1(A,B,C))
             => ( k5_mcart_1(A,B,C,D) = k1_mcart_1(k1_mcart_1(D))
                & k6_mcart_1(A,B,C,D) = k2_mcart_1(k1_mcart_1(D))
                & k7_mcart_1(A,B,C,D) = k2_mcart_1(D) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_mcart_1)).

tff(f_33,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_57,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

tff(c_38,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_69,plain,(
    ! [B_46,A_47] :
      ( v1_xboole_0(B_46)
      | ~ m1_subset_1(B_46,k1_zfmisc_1(A_47))
      | ~ v1_xboole_0(A_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_79,plain,
    ( v1_xboole_0('#skF_7')
    | ~ v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_38,c_69])).

tff(c_82,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_79])).

tff(c_40,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_80,plain,
    ( v1_xboole_0('#skF_6')
    | ~ v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_40,c_69])).

tff(c_998,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_80])).

tff(c_34,plain,(
    r2_hidden('#skF_8',k3_zfmisc_1('#skF_5','#skF_6','#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_1036,plain,(
    ! [A_212,B_213,C_214] : k2_zfmisc_1(k2_zfmisc_1(A_212,B_213),C_214) = k3_zfmisc_1(A_212,B_213,C_214) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_22,plain,(
    ! [A_20,C_22,B_21] :
      ( r2_hidden(k2_mcart_1(A_20),C_22)
      | ~ r2_hidden(A_20,k2_zfmisc_1(B_21,C_22)) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_1072,plain,(
    ! [A_223,C_224,A_225,B_226] :
      ( r2_hidden(k2_mcart_1(A_223),C_224)
      | ~ r2_hidden(A_223,k3_zfmisc_1(A_225,B_226,C_224)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1036,c_22])).

tff(c_1082,plain,(
    r2_hidden(k2_mcart_1('#skF_8'),'#skF_7') ),
    inference(resolution,[status(thm)],[c_34,c_1072])).

tff(c_42,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_81,plain,
    ( v1_xboole_0('#skF_5')
    | ~ v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_42,c_69])).

tff(c_92,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_81])).

tff(c_36,plain,(
    m1_subset_1('#skF_8',k3_zfmisc_1('#skF_2','#skF_3','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_1169,plain,(
    ! [A_247,B_248,C_249,D_250] :
      ( k7_mcart_1(A_247,B_248,C_249,D_250) = k2_mcart_1(D_250)
      | ~ m1_subset_1(D_250,k3_zfmisc_1(A_247,B_248,C_249))
      | k1_xboole_0 = C_249
      | k1_xboole_0 = B_248
      | k1_xboole_0 = A_247 ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_1173,plain,
    ( k7_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8') = k2_mcart_1('#skF_8')
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_36,c_1169])).

tff(c_1259,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_1173])).

tff(c_6,plain,(
    ! [A_5] : r1_tarski(k1_xboole_0,A_5) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_50,plain,(
    ! [B_43,A_44] :
      ( ~ r1_tarski(B_43,A_44)
      | ~ r2_hidden(A_44,B_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_63,plain,(
    ! [A_45] :
      ( ~ r1_tarski(A_45,'#skF_1'(A_45))
      | v1_xboole_0(A_45) ) ),
    inference(resolution,[status(thm)],[c_4,c_50])).

tff(c_68,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_6,c_63])).

tff(c_1264,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1259,c_68])).

tff(c_1267,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_92,c_1264])).

tff(c_1268,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_4'
    | k7_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8') = k2_mcart_1('#skF_8') ),
    inference(splitRight,[status(thm)],[c_1173])).

tff(c_1279,plain,(
    k7_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8') = k2_mcart_1('#skF_8') ),
    inference(splitLeft,[status(thm)],[c_1268])).

tff(c_32,plain,
    ( ~ r2_hidden(k7_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8'),'#skF_7')
    | ~ r2_hidden(k6_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8'),'#skF_6')
    | ~ r2_hidden(k5_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8'),'#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_93,plain,(
    ~ r2_hidden(k5_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8'),'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_32])).

tff(c_94,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_80])).

tff(c_240,plain,(
    ! [A_85,B_86,C_87,D_88] :
      ( k7_mcart_1(A_85,B_86,C_87,D_88) = k2_mcart_1(D_88)
      | ~ m1_subset_1(D_88,k3_zfmisc_1(A_85,B_86,C_87))
      | k1_xboole_0 = C_87
      | k1_xboole_0 = B_86
      | k1_xboole_0 = A_85 ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_244,plain,
    ( k7_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8') = k2_mcart_1('#skF_8')
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_36,c_240])).

tff(c_307,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_244])).

tff(c_310,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_307,c_68])).

tff(c_313,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_92,c_310])).

tff(c_315,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(splitRight,[status(thm)],[c_244])).

tff(c_294,plain,(
    ! [A_104,B_105,C_106,D_107] :
      ( k6_mcart_1(A_104,B_105,C_106,D_107) = k2_mcart_1(k1_mcart_1(D_107))
      | ~ m1_subset_1(D_107,k3_zfmisc_1(A_104,B_105,C_106))
      | k1_xboole_0 = C_106
      | k1_xboole_0 = B_105
      | k1_xboole_0 = A_104 ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_298,plain,
    ( k2_mcart_1(k1_mcart_1('#skF_8')) = k6_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8')
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_36,c_294])).

tff(c_506,plain,
    ( k2_mcart_1(k1_mcart_1('#skF_8')) = k6_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8')
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_315,c_298])).

tff(c_507,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_506])).

tff(c_516,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_507,c_68])).

tff(c_519,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_94,c_516])).

tff(c_521,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_506])).

tff(c_331,plain,(
    ! [A_110,B_111,C_112,D_113] :
      ( k5_mcart_1(A_110,B_111,C_112,D_113) = k1_mcart_1(k1_mcart_1(D_113))
      | ~ m1_subset_1(D_113,k3_zfmisc_1(A_110,B_111,C_112))
      | k1_xboole_0 = C_112
      | k1_xboole_0 = B_111
      | k1_xboole_0 = A_110 ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_334,plain,
    ( k1_mcart_1(k1_mcart_1('#skF_8')) = k5_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8')
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_36,c_331])).

tff(c_337,plain,
    ( k1_mcart_1(k1_mcart_1('#skF_8')) = k5_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8')
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_315,c_334])).

tff(c_733,plain,
    ( k1_mcart_1(k1_mcart_1('#skF_8')) = k5_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8')
    | k1_xboole_0 = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_521,c_337])).

tff(c_734,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_733])).

tff(c_744,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_734,c_68])).

tff(c_747,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_744])).

tff(c_748,plain,(
    k1_mcart_1(k1_mcart_1('#skF_8')) = k5_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8') ),
    inference(splitRight,[status(thm)],[c_733])).

tff(c_114,plain,(
    ! [A_55,B_56,C_57] : k2_zfmisc_1(k2_zfmisc_1(A_55,B_56),C_57) = k3_zfmisc_1(A_55,B_56,C_57) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_24,plain,(
    ! [A_20,B_21,C_22] :
      ( r2_hidden(k1_mcart_1(A_20),B_21)
      | ~ r2_hidden(A_20,k2_zfmisc_1(B_21,C_22)) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_673,plain,(
    ! [A_149,A_150,B_151,C_152] :
      ( r2_hidden(k1_mcart_1(A_149),k2_zfmisc_1(A_150,B_151))
      | ~ r2_hidden(A_149,k3_zfmisc_1(A_150,B_151,C_152)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_114,c_24])).

tff(c_710,plain,(
    r2_hidden(k1_mcart_1('#skF_8'),k2_zfmisc_1('#skF_5','#skF_6')) ),
    inference(resolution,[status(thm)],[c_34,c_673])).

tff(c_730,plain,(
    r2_hidden(k1_mcart_1(k1_mcart_1('#skF_8')),'#skF_5') ),
    inference(resolution,[status(thm)],[c_710,c_24])).

tff(c_779,plain,(
    r2_hidden(k5_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8'),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_748,c_730])).

tff(c_781,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_93,c_779])).

tff(c_782,plain,(
    v1_xboole_0('#skF_6') ),
    inference(splitRight,[status(thm)],[c_80])).

tff(c_821,plain,(
    ! [A_161,C_162,B_163] :
      ( r2_hidden(k2_mcart_1(A_161),C_162)
      | ~ r2_hidden(A_161,k2_zfmisc_1(B_163,C_162)) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_950,plain,(
    ! [B_200,C_201] :
      ( r2_hidden(k2_mcart_1('#skF_1'(k2_zfmisc_1(B_200,C_201))),C_201)
      | v1_xboole_0(k2_zfmisc_1(B_200,C_201)) ) ),
    inference(resolution,[status(thm)],[c_4,c_821])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_983,plain,(
    ! [C_202,B_203] :
      ( ~ v1_xboole_0(C_202)
      | v1_xboole_0(k2_zfmisc_1(B_203,C_202)) ) ),
    inference(resolution,[status(thm)],[c_950,c_2])).

tff(c_20,plain,(
    ! [A_17,B_18,C_19] : k2_zfmisc_1(k2_zfmisc_1(A_17,B_18),C_19) = k3_zfmisc_1(A_17,B_18,C_19) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_810,plain,(
    ! [A_158,B_159,C_160] :
      ( r2_hidden(k1_mcart_1(A_158),B_159)
      | ~ r2_hidden(A_158,k2_zfmisc_1(B_159,C_160)) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_897,plain,(
    ! [B_184,C_185] :
      ( r2_hidden(k1_mcart_1('#skF_1'(k2_zfmisc_1(B_184,C_185))),B_184)
      | v1_xboole_0(k2_zfmisc_1(B_184,C_185)) ) ),
    inference(resolution,[status(thm)],[c_4,c_810])).

tff(c_924,plain,(
    ! [B_186,C_187] :
      ( ~ v1_xboole_0(B_186)
      | v1_xboole_0(k2_zfmisc_1(B_186,C_187)) ) ),
    inference(resolution,[status(thm)],[c_897,c_2])).

tff(c_931,plain,(
    ! [A_188,B_189,C_190] :
      ( ~ v1_xboole_0(k2_zfmisc_1(A_188,B_189))
      | v1_xboole_0(k3_zfmisc_1(A_188,B_189,C_190)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_924])).

tff(c_62,plain,(
    ~ v1_xboole_0(k3_zfmisc_1('#skF_5','#skF_6','#skF_7')) ),
    inference(resolution,[status(thm)],[c_34,c_2])).

tff(c_935,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_5','#skF_6')) ),
    inference(resolution,[status(thm)],[c_931,c_62])).

tff(c_986,plain,(
    ~ v1_xboole_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_983,c_935])).

tff(c_995,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_782,c_986])).

tff(c_996,plain,
    ( ~ r2_hidden(k6_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8'),'#skF_6')
    | ~ r2_hidden(k7_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8'),'#skF_7') ),
    inference(splitRight,[status(thm)],[c_32])).

tff(c_1013,plain,(
    ~ r2_hidden(k7_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8'),'#skF_7') ),
    inference(splitLeft,[status(thm)],[c_996])).

tff(c_1288,plain,(
    ~ r2_hidden(k2_mcart_1('#skF_8'),'#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1279,c_1013])).

tff(c_1291,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1082,c_1288])).

tff(c_1292,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_1268])).

tff(c_1294,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_1292])).

tff(c_1302,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1294,c_68])).

tff(c_1305,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_998,c_1302])).

tff(c_1306,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_1292])).

tff(c_1321,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1306,c_68])).

tff(c_1324,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_1321])).

tff(c_1325,plain,(
    ~ r2_hidden(k6_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8'),'#skF_6') ),
    inference(splitRight,[status(thm)],[c_996])).

tff(c_1484,plain,(
    ! [A_314,B_315,C_316,D_317] :
      ( k7_mcart_1(A_314,B_315,C_316,D_317) = k2_mcart_1(D_317)
      | ~ m1_subset_1(D_317,k3_zfmisc_1(A_314,B_315,C_316))
      | k1_xboole_0 = C_316
      | k1_xboole_0 = B_315
      | k1_xboole_0 = A_314 ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_1488,plain,
    ( k7_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8') = k2_mcart_1('#skF_8')
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_36,c_1484])).

tff(c_1528,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_1488])).

tff(c_1530,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1528,c_68])).

tff(c_1533,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_92,c_1530])).

tff(c_1535,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(splitRight,[status(thm)],[c_1488])).

tff(c_1545,plain,(
    ! [A_325,B_326,C_327,D_328] :
      ( k6_mcart_1(A_325,B_326,C_327,D_328) = k2_mcart_1(k1_mcart_1(D_328))
      | ~ m1_subset_1(D_328,k3_zfmisc_1(A_325,B_326,C_327))
      | k1_xboole_0 = C_327
      | k1_xboole_0 = B_326
      | k1_xboole_0 = A_325 ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_1548,plain,
    ( k2_mcart_1(k1_mcart_1('#skF_8')) = k6_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8')
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_36,c_1545])).

tff(c_1551,plain,
    ( k2_mcart_1(k1_mcart_1('#skF_8')) = k6_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8')
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_1535,c_1548])).

tff(c_1573,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_1551])).

tff(c_1578,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1573,c_68])).

tff(c_1581,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_998,c_1578])).

tff(c_1582,plain,
    ( k1_xboole_0 = '#skF_4'
    | k2_mcart_1(k1_mcart_1('#skF_8')) = k6_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8') ),
    inference(splitRight,[status(thm)],[c_1551])).

tff(c_1625,plain,(
    k2_mcart_1(k1_mcart_1('#skF_8')) = k6_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8') ),
    inference(splitLeft,[status(thm)],[c_1582])).

tff(c_1358,plain,(
    ! [A_279,B_280,C_281] : k2_zfmisc_1(k2_zfmisc_1(A_279,B_280),C_281) = k3_zfmisc_1(A_279,B_280,C_281) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_1796,plain,(
    ! [A_358,A_359,B_360,C_361] :
      ( r2_hidden(k1_mcart_1(A_358),k2_zfmisc_1(A_359,B_360))
      | ~ r2_hidden(A_358,k3_zfmisc_1(A_359,B_360,C_361)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1358,c_24])).

tff(c_1825,plain,(
    r2_hidden(k1_mcart_1('#skF_8'),k2_zfmisc_1('#skF_5','#skF_6')) ),
    inference(resolution,[status(thm)],[c_34,c_1796])).

tff(c_1832,plain,(
    r2_hidden(k2_mcart_1(k1_mcart_1('#skF_8')),'#skF_6') ),
    inference(resolution,[status(thm)],[c_1825,c_22])).

tff(c_1843,plain,(
    r2_hidden(k6_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1625,c_1832])).

tff(c_1845,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1325,c_1843])).

tff(c_1846,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_1582])).

tff(c_1857,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1846,c_68])).

tff(c_1860,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_1857])).

tff(c_1861,plain,(
    v1_xboole_0('#skF_6') ),
    inference(splitRight,[status(thm)],[c_80])).

tff(c_1897,plain,(
    ! [A_367,C_368,B_369] :
      ( r2_hidden(k2_mcart_1(A_367),C_368)
      | ~ r2_hidden(A_367,k2_zfmisc_1(B_369,C_368)) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_1995,plain,(
    ! [B_402,C_403] :
      ( r2_hidden(k2_mcart_1('#skF_1'(k2_zfmisc_1(B_402,C_403))),C_403)
      | v1_xboole_0(k2_zfmisc_1(B_402,C_403)) ) ),
    inference(resolution,[status(thm)],[c_4,c_1897])).

tff(c_2018,plain,(
    ! [C_403,B_402] :
      ( ~ v1_xboole_0(C_403)
      | v1_xboole_0(k2_zfmisc_1(B_402,C_403)) ) ),
    inference(resolution,[status(thm)],[c_1995,c_2])).

tff(c_1908,plain,(
    ! [A_370,B_371,C_372] :
      ( r2_hidden(k1_mcart_1(A_370),B_371)
      | ~ r2_hidden(A_370,k2_zfmisc_1(B_371,C_372)) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_2040,plain,(
    ! [B_409,C_410] :
      ( r2_hidden(k1_mcart_1('#skF_1'(k2_zfmisc_1(B_409,C_410))),B_409)
      | v1_xboole_0(k2_zfmisc_1(B_409,C_410)) ) ),
    inference(resolution,[status(thm)],[c_4,c_1908])).

tff(c_2067,plain,(
    ! [B_411,C_412] :
      ( ~ v1_xboole_0(B_411)
      | v1_xboole_0(k2_zfmisc_1(B_411,C_412)) ) ),
    inference(resolution,[status(thm)],[c_2040,c_2])).

tff(c_2081,plain,(
    ! [A_417,B_418,C_419] :
      ( ~ v1_xboole_0(k2_zfmisc_1(A_417,B_418))
      | v1_xboole_0(k3_zfmisc_1(A_417,B_418,C_419)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_2067])).

tff(c_2085,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_5','#skF_6')) ),
    inference(resolution,[status(thm)],[c_2081,c_62])).

tff(c_2091,plain,(
    ~ v1_xboole_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_2018,c_2085])).

tff(c_2096,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1861,c_2091])).

tff(c_2097,plain,(
    v1_xboole_0('#skF_5') ),
    inference(splitRight,[status(thm)],[c_81])).

tff(c_2112,plain,(
    ! [A_422,B_423,C_424] :
      ( r2_hidden(k1_mcart_1(A_422),B_423)
      | ~ r2_hidden(A_422,k2_zfmisc_1(B_423,C_424)) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_2219,plain,(
    ! [B_456,C_457] :
      ( r2_hidden(k1_mcart_1('#skF_1'(k2_zfmisc_1(B_456,C_457))),B_456)
      | v1_xboole_0(k2_zfmisc_1(B_456,C_457)) ) ),
    inference(resolution,[status(thm)],[c_4,c_2112])).

tff(c_2244,plain,(
    ! [B_456,C_457] :
      ( ~ v1_xboole_0(B_456)
      | v1_xboole_0(k2_zfmisc_1(B_456,C_457)) ) ),
    inference(resolution,[status(thm)],[c_2219,c_2])).

tff(c_2246,plain,(
    ! [B_458,C_459] :
      ( ~ v1_xboole_0(B_458)
      | v1_xboole_0(k2_zfmisc_1(B_458,C_459)) ) ),
    inference(resolution,[status(thm)],[c_2219,c_2])).

tff(c_2258,plain,(
    ! [A_464,B_465,C_466] :
      ( ~ v1_xboole_0(k2_zfmisc_1(A_464,B_465))
      | v1_xboole_0(k3_zfmisc_1(A_464,B_465,C_466)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_2246])).

tff(c_2262,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_5','#skF_6')) ),
    inference(resolution,[status(thm)],[c_2258,c_62])).

tff(c_2265,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_2244,c_2262])).

tff(c_2269,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2097,c_2265])).

tff(c_2270,plain,(
    v1_xboole_0('#skF_7') ),
    inference(splitRight,[status(thm)],[c_79])).

tff(c_2303,plain,(
    ! [A_474,B_475,C_476] : k2_zfmisc_1(k2_zfmisc_1(A_474,B_475),C_476) = k3_zfmisc_1(A_474,B_475,C_476) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_2374,plain,(
    ! [A_492,C_493,A_494,B_495] :
      ( r2_hidden(k2_mcart_1(A_492),C_493)
      | ~ r2_hidden(A_492,k3_zfmisc_1(A_494,B_495,C_493)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2303,c_22])).

tff(c_2384,plain,(
    r2_hidden(k2_mcart_1('#skF_8'),'#skF_7') ),
    inference(resolution,[status(thm)],[c_34,c_2374])).

tff(c_2391,plain,(
    ~ v1_xboole_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_2384,c_2])).

tff(c_2396,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2270,c_2391])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:40:35 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.01/1.72  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.01/1.74  
% 4.01/1.74  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.01/1.74  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k7_mcart_1 > k6_mcart_1 > k5_mcart_1 > k3_zfmisc_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_mcart_1 > k1_zfmisc_1 > k1_mcart_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_8 > #skF_4
% 4.01/1.74  
% 4.01/1.74  %Foreground sorts:
% 4.01/1.74  
% 4.01/1.74  
% 4.01/1.74  %Background operators:
% 4.01/1.74  
% 4.01/1.74  
% 4.01/1.74  %Foreground operators:
% 4.01/1.74  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.01/1.74  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.01/1.74  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 4.01/1.74  tff('#skF_1', type, '#skF_1': $i > $i).
% 4.01/1.74  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.01/1.74  tff('#skF_7', type, '#skF_7': $i).
% 4.01/1.74  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.01/1.74  tff('#skF_5', type, '#skF_5': $i).
% 4.01/1.74  tff('#skF_6', type, '#skF_6': $i).
% 4.01/1.74  tff('#skF_2', type, '#skF_2': $i).
% 4.01/1.74  tff('#skF_3', type, '#skF_3': $i).
% 4.01/1.74  tff(k7_mcart_1, type, k7_mcart_1: ($i * $i * $i * $i) > $i).
% 4.01/1.74  tff(k3_zfmisc_1, type, k3_zfmisc_1: ($i * $i * $i) > $i).
% 4.01/1.74  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.01/1.74  tff('#skF_8', type, '#skF_8': $i).
% 4.01/1.74  tff(k5_mcart_1, type, k5_mcart_1: ($i * $i * $i * $i) > $i).
% 4.01/1.74  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.01/1.74  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 4.01/1.74  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.01/1.74  tff('#skF_4', type, '#skF_4': $i).
% 4.01/1.74  tff(k6_mcart_1, type, k6_mcart_1: ($i * $i * $i * $i) > $i).
% 4.01/1.74  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.01/1.74  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 4.01/1.74  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.01/1.74  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.01/1.74  
% 4.34/1.76  tff(f_105, negated_conjecture, ~(![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(A)) => (![E]: (m1_subset_1(E, k1_zfmisc_1(B)) => (![F]: (m1_subset_1(F, k1_zfmisc_1(C)) => (![G]: (m1_subset_1(G, k3_zfmisc_1(A, B, C)) => (r2_hidden(G, k3_zfmisc_1(D, E, F)) => ((r2_hidden(k5_mcart_1(A, B, C, G), D) & r2_hidden(k6_mcart_1(A, B, C, G), E)) & r2_hidden(k7_mcart_1(A, B, C, G), F))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t76_mcart_1)).
% 4.34/1.76  tff(f_46, axiom, (![A]: (v1_xboole_0(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_subset_1)).
% 4.34/1.76  tff(f_59, axiom, (![A, B, C]: (k3_zfmisc_1(A, B, C) = k2_zfmisc_1(k2_zfmisc_1(A, B), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_zfmisc_1)).
% 4.34/1.76  tff(f_65, axiom, (![A, B, C]: (r2_hidden(A, k2_zfmisc_1(B, C)) => (r2_hidden(k1_mcart_1(A), B) & r2_hidden(k2_mcart_1(A), C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_mcart_1)).
% 4.34/1.76  tff(f_85, axiom, (![A, B, C]: ~(((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0)) & ~(![D]: (m1_subset_1(D, k3_zfmisc_1(A, B, C)) => (((k5_mcart_1(A, B, C, D) = k1_mcart_1(k1_mcart_1(D))) & (k6_mcart_1(A, B, C, D) = k2_mcart_1(k1_mcart_1(D)))) & (k7_mcart_1(A, B, C, D) = k2_mcart_1(D))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t50_mcart_1)).
% 4.34/1.76  tff(f_33, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 4.34/1.76  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 4.34/1.76  tff(f_57, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 4.34/1.76  tff(c_38, plain, (m1_subset_1('#skF_7', k1_zfmisc_1('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_105])).
% 4.34/1.76  tff(c_69, plain, (![B_46, A_47]: (v1_xboole_0(B_46) | ~m1_subset_1(B_46, k1_zfmisc_1(A_47)) | ~v1_xboole_0(A_47))), inference(cnfTransformation, [status(thm)], [f_46])).
% 4.34/1.76  tff(c_79, plain, (v1_xboole_0('#skF_7') | ~v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_38, c_69])).
% 4.34/1.76  tff(c_82, plain, (~v1_xboole_0('#skF_4')), inference(splitLeft, [status(thm)], [c_79])).
% 4.34/1.76  tff(c_40, plain, (m1_subset_1('#skF_6', k1_zfmisc_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_105])).
% 4.34/1.76  tff(c_80, plain, (v1_xboole_0('#skF_6') | ~v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_40, c_69])).
% 4.34/1.76  tff(c_998, plain, (~v1_xboole_0('#skF_3')), inference(splitLeft, [status(thm)], [c_80])).
% 4.34/1.76  tff(c_34, plain, (r2_hidden('#skF_8', k3_zfmisc_1('#skF_5', '#skF_6', '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_105])).
% 4.34/1.76  tff(c_1036, plain, (![A_212, B_213, C_214]: (k2_zfmisc_1(k2_zfmisc_1(A_212, B_213), C_214)=k3_zfmisc_1(A_212, B_213, C_214))), inference(cnfTransformation, [status(thm)], [f_59])).
% 4.34/1.76  tff(c_22, plain, (![A_20, C_22, B_21]: (r2_hidden(k2_mcart_1(A_20), C_22) | ~r2_hidden(A_20, k2_zfmisc_1(B_21, C_22)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 4.34/1.76  tff(c_1072, plain, (![A_223, C_224, A_225, B_226]: (r2_hidden(k2_mcart_1(A_223), C_224) | ~r2_hidden(A_223, k3_zfmisc_1(A_225, B_226, C_224)))), inference(superposition, [status(thm), theory('equality')], [c_1036, c_22])).
% 4.34/1.76  tff(c_1082, plain, (r2_hidden(k2_mcart_1('#skF_8'), '#skF_7')), inference(resolution, [status(thm)], [c_34, c_1072])).
% 4.34/1.76  tff(c_42, plain, (m1_subset_1('#skF_5', k1_zfmisc_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_105])).
% 4.34/1.76  tff(c_81, plain, (v1_xboole_0('#skF_5') | ~v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_42, c_69])).
% 4.34/1.76  tff(c_92, plain, (~v1_xboole_0('#skF_2')), inference(splitLeft, [status(thm)], [c_81])).
% 4.34/1.76  tff(c_36, plain, (m1_subset_1('#skF_8', k3_zfmisc_1('#skF_2', '#skF_3', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_105])).
% 4.34/1.76  tff(c_1169, plain, (![A_247, B_248, C_249, D_250]: (k7_mcart_1(A_247, B_248, C_249, D_250)=k2_mcart_1(D_250) | ~m1_subset_1(D_250, k3_zfmisc_1(A_247, B_248, C_249)) | k1_xboole_0=C_249 | k1_xboole_0=B_248 | k1_xboole_0=A_247)), inference(cnfTransformation, [status(thm)], [f_85])).
% 4.34/1.76  tff(c_1173, plain, (k7_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8')=k2_mcart_1('#skF_8') | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_36, c_1169])).
% 4.34/1.76  tff(c_1259, plain, (k1_xboole_0='#skF_2'), inference(splitLeft, [status(thm)], [c_1173])).
% 4.34/1.76  tff(c_6, plain, (![A_5]: (r1_tarski(k1_xboole_0, A_5))), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.34/1.76  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.34/1.76  tff(c_50, plain, (![B_43, A_44]: (~r1_tarski(B_43, A_44) | ~r2_hidden(A_44, B_43))), inference(cnfTransformation, [status(thm)], [f_57])).
% 4.34/1.76  tff(c_63, plain, (![A_45]: (~r1_tarski(A_45, '#skF_1'(A_45)) | v1_xboole_0(A_45))), inference(resolution, [status(thm)], [c_4, c_50])).
% 4.34/1.76  tff(c_68, plain, (v1_xboole_0(k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_63])).
% 4.34/1.76  tff(c_1264, plain, (v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1259, c_68])).
% 4.34/1.76  tff(c_1267, plain, $false, inference(negUnitSimplification, [status(thm)], [c_92, c_1264])).
% 4.34/1.76  tff(c_1268, plain, (k1_xboole_0='#skF_3' | k1_xboole_0='#skF_4' | k7_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8')=k2_mcart_1('#skF_8')), inference(splitRight, [status(thm)], [c_1173])).
% 4.34/1.76  tff(c_1279, plain, (k7_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8')=k2_mcart_1('#skF_8')), inference(splitLeft, [status(thm)], [c_1268])).
% 4.34/1.76  tff(c_32, plain, (~r2_hidden(k7_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8'), '#skF_7') | ~r2_hidden(k6_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8'), '#skF_6') | ~r2_hidden(k5_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8'), '#skF_5')), inference(cnfTransformation, [status(thm)], [f_105])).
% 4.34/1.76  tff(c_93, plain, (~r2_hidden(k5_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8'), '#skF_5')), inference(splitLeft, [status(thm)], [c_32])).
% 4.34/1.76  tff(c_94, plain, (~v1_xboole_0('#skF_3')), inference(splitLeft, [status(thm)], [c_80])).
% 4.34/1.76  tff(c_240, plain, (![A_85, B_86, C_87, D_88]: (k7_mcart_1(A_85, B_86, C_87, D_88)=k2_mcart_1(D_88) | ~m1_subset_1(D_88, k3_zfmisc_1(A_85, B_86, C_87)) | k1_xboole_0=C_87 | k1_xboole_0=B_86 | k1_xboole_0=A_85)), inference(cnfTransformation, [status(thm)], [f_85])).
% 4.34/1.76  tff(c_244, plain, (k7_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8')=k2_mcart_1('#skF_8') | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_36, c_240])).
% 4.34/1.76  tff(c_307, plain, (k1_xboole_0='#skF_2'), inference(splitLeft, [status(thm)], [c_244])).
% 4.34/1.76  tff(c_310, plain, (v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_307, c_68])).
% 4.34/1.76  tff(c_313, plain, $false, inference(negUnitSimplification, [status(thm)], [c_92, c_310])).
% 4.34/1.76  tff(c_315, plain, (k1_xboole_0!='#skF_2'), inference(splitRight, [status(thm)], [c_244])).
% 4.34/1.76  tff(c_294, plain, (![A_104, B_105, C_106, D_107]: (k6_mcart_1(A_104, B_105, C_106, D_107)=k2_mcart_1(k1_mcart_1(D_107)) | ~m1_subset_1(D_107, k3_zfmisc_1(A_104, B_105, C_106)) | k1_xboole_0=C_106 | k1_xboole_0=B_105 | k1_xboole_0=A_104)), inference(cnfTransformation, [status(thm)], [f_85])).
% 4.34/1.76  tff(c_298, plain, (k2_mcart_1(k1_mcart_1('#skF_8'))=k6_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8') | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_36, c_294])).
% 4.34/1.76  tff(c_506, plain, (k2_mcart_1(k1_mcart_1('#skF_8'))=k6_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8') | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_315, c_298])).
% 4.34/1.76  tff(c_507, plain, (k1_xboole_0='#skF_3'), inference(splitLeft, [status(thm)], [c_506])).
% 4.34/1.76  tff(c_516, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_507, c_68])).
% 4.34/1.76  tff(c_519, plain, $false, inference(negUnitSimplification, [status(thm)], [c_94, c_516])).
% 4.34/1.76  tff(c_521, plain, (k1_xboole_0!='#skF_3'), inference(splitRight, [status(thm)], [c_506])).
% 4.34/1.76  tff(c_331, plain, (![A_110, B_111, C_112, D_113]: (k5_mcart_1(A_110, B_111, C_112, D_113)=k1_mcart_1(k1_mcart_1(D_113)) | ~m1_subset_1(D_113, k3_zfmisc_1(A_110, B_111, C_112)) | k1_xboole_0=C_112 | k1_xboole_0=B_111 | k1_xboole_0=A_110)), inference(cnfTransformation, [status(thm)], [f_85])).
% 4.34/1.76  tff(c_334, plain, (k1_mcart_1(k1_mcart_1('#skF_8'))=k5_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8') | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_36, c_331])).
% 4.34/1.76  tff(c_337, plain, (k1_mcart_1(k1_mcart_1('#skF_8'))=k5_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8') | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_315, c_334])).
% 4.34/1.76  tff(c_733, plain, (k1_mcart_1(k1_mcart_1('#skF_8'))=k5_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8') | k1_xboole_0='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_521, c_337])).
% 4.34/1.76  tff(c_734, plain, (k1_xboole_0='#skF_4'), inference(splitLeft, [status(thm)], [c_733])).
% 4.34/1.76  tff(c_744, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_734, c_68])).
% 4.34/1.76  tff(c_747, plain, $false, inference(negUnitSimplification, [status(thm)], [c_82, c_744])).
% 4.34/1.76  tff(c_748, plain, (k1_mcart_1(k1_mcart_1('#skF_8'))=k5_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8')), inference(splitRight, [status(thm)], [c_733])).
% 4.34/1.76  tff(c_114, plain, (![A_55, B_56, C_57]: (k2_zfmisc_1(k2_zfmisc_1(A_55, B_56), C_57)=k3_zfmisc_1(A_55, B_56, C_57))), inference(cnfTransformation, [status(thm)], [f_59])).
% 4.34/1.76  tff(c_24, plain, (![A_20, B_21, C_22]: (r2_hidden(k1_mcart_1(A_20), B_21) | ~r2_hidden(A_20, k2_zfmisc_1(B_21, C_22)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 4.34/1.76  tff(c_673, plain, (![A_149, A_150, B_151, C_152]: (r2_hidden(k1_mcart_1(A_149), k2_zfmisc_1(A_150, B_151)) | ~r2_hidden(A_149, k3_zfmisc_1(A_150, B_151, C_152)))), inference(superposition, [status(thm), theory('equality')], [c_114, c_24])).
% 4.34/1.76  tff(c_710, plain, (r2_hidden(k1_mcart_1('#skF_8'), k2_zfmisc_1('#skF_5', '#skF_6'))), inference(resolution, [status(thm)], [c_34, c_673])).
% 4.34/1.76  tff(c_730, plain, (r2_hidden(k1_mcart_1(k1_mcart_1('#skF_8')), '#skF_5')), inference(resolution, [status(thm)], [c_710, c_24])).
% 4.34/1.76  tff(c_779, plain, (r2_hidden(k5_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8'), '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_748, c_730])).
% 4.34/1.76  tff(c_781, plain, $false, inference(negUnitSimplification, [status(thm)], [c_93, c_779])).
% 4.34/1.76  tff(c_782, plain, (v1_xboole_0('#skF_6')), inference(splitRight, [status(thm)], [c_80])).
% 4.34/1.76  tff(c_821, plain, (![A_161, C_162, B_163]: (r2_hidden(k2_mcart_1(A_161), C_162) | ~r2_hidden(A_161, k2_zfmisc_1(B_163, C_162)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 4.34/1.76  tff(c_950, plain, (![B_200, C_201]: (r2_hidden(k2_mcart_1('#skF_1'(k2_zfmisc_1(B_200, C_201))), C_201) | v1_xboole_0(k2_zfmisc_1(B_200, C_201)))), inference(resolution, [status(thm)], [c_4, c_821])).
% 4.34/1.76  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.34/1.76  tff(c_983, plain, (![C_202, B_203]: (~v1_xboole_0(C_202) | v1_xboole_0(k2_zfmisc_1(B_203, C_202)))), inference(resolution, [status(thm)], [c_950, c_2])).
% 4.34/1.76  tff(c_20, plain, (![A_17, B_18, C_19]: (k2_zfmisc_1(k2_zfmisc_1(A_17, B_18), C_19)=k3_zfmisc_1(A_17, B_18, C_19))), inference(cnfTransformation, [status(thm)], [f_59])).
% 4.34/1.76  tff(c_810, plain, (![A_158, B_159, C_160]: (r2_hidden(k1_mcart_1(A_158), B_159) | ~r2_hidden(A_158, k2_zfmisc_1(B_159, C_160)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 4.34/1.76  tff(c_897, plain, (![B_184, C_185]: (r2_hidden(k1_mcart_1('#skF_1'(k2_zfmisc_1(B_184, C_185))), B_184) | v1_xboole_0(k2_zfmisc_1(B_184, C_185)))), inference(resolution, [status(thm)], [c_4, c_810])).
% 4.34/1.76  tff(c_924, plain, (![B_186, C_187]: (~v1_xboole_0(B_186) | v1_xboole_0(k2_zfmisc_1(B_186, C_187)))), inference(resolution, [status(thm)], [c_897, c_2])).
% 4.34/1.76  tff(c_931, plain, (![A_188, B_189, C_190]: (~v1_xboole_0(k2_zfmisc_1(A_188, B_189)) | v1_xboole_0(k3_zfmisc_1(A_188, B_189, C_190)))), inference(superposition, [status(thm), theory('equality')], [c_20, c_924])).
% 4.34/1.76  tff(c_62, plain, (~v1_xboole_0(k3_zfmisc_1('#skF_5', '#skF_6', '#skF_7'))), inference(resolution, [status(thm)], [c_34, c_2])).
% 4.34/1.76  tff(c_935, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_5', '#skF_6'))), inference(resolution, [status(thm)], [c_931, c_62])).
% 4.34/1.76  tff(c_986, plain, (~v1_xboole_0('#skF_6')), inference(resolution, [status(thm)], [c_983, c_935])).
% 4.34/1.76  tff(c_995, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_782, c_986])).
% 4.34/1.76  tff(c_996, plain, (~r2_hidden(k6_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8'), '#skF_6') | ~r2_hidden(k7_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8'), '#skF_7')), inference(splitRight, [status(thm)], [c_32])).
% 4.34/1.76  tff(c_1013, plain, (~r2_hidden(k7_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8'), '#skF_7')), inference(splitLeft, [status(thm)], [c_996])).
% 4.34/1.76  tff(c_1288, plain, (~r2_hidden(k2_mcart_1('#skF_8'), '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_1279, c_1013])).
% 4.34/1.76  tff(c_1291, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1082, c_1288])).
% 4.34/1.76  tff(c_1292, plain, (k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_1268])).
% 4.34/1.76  tff(c_1294, plain, (k1_xboole_0='#skF_3'), inference(splitLeft, [status(thm)], [c_1292])).
% 4.34/1.76  tff(c_1302, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1294, c_68])).
% 4.34/1.76  tff(c_1305, plain, $false, inference(negUnitSimplification, [status(thm)], [c_998, c_1302])).
% 4.34/1.76  tff(c_1306, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_1292])).
% 4.34/1.76  tff(c_1321, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1306, c_68])).
% 4.34/1.76  tff(c_1324, plain, $false, inference(negUnitSimplification, [status(thm)], [c_82, c_1321])).
% 4.34/1.76  tff(c_1325, plain, (~r2_hidden(k6_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8'), '#skF_6')), inference(splitRight, [status(thm)], [c_996])).
% 4.34/1.76  tff(c_1484, plain, (![A_314, B_315, C_316, D_317]: (k7_mcart_1(A_314, B_315, C_316, D_317)=k2_mcart_1(D_317) | ~m1_subset_1(D_317, k3_zfmisc_1(A_314, B_315, C_316)) | k1_xboole_0=C_316 | k1_xboole_0=B_315 | k1_xboole_0=A_314)), inference(cnfTransformation, [status(thm)], [f_85])).
% 4.34/1.76  tff(c_1488, plain, (k7_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8')=k2_mcart_1('#skF_8') | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_36, c_1484])).
% 4.34/1.76  tff(c_1528, plain, (k1_xboole_0='#skF_2'), inference(splitLeft, [status(thm)], [c_1488])).
% 4.34/1.76  tff(c_1530, plain, (v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1528, c_68])).
% 4.34/1.76  tff(c_1533, plain, $false, inference(negUnitSimplification, [status(thm)], [c_92, c_1530])).
% 4.34/1.76  tff(c_1535, plain, (k1_xboole_0!='#skF_2'), inference(splitRight, [status(thm)], [c_1488])).
% 4.34/1.76  tff(c_1545, plain, (![A_325, B_326, C_327, D_328]: (k6_mcart_1(A_325, B_326, C_327, D_328)=k2_mcart_1(k1_mcart_1(D_328)) | ~m1_subset_1(D_328, k3_zfmisc_1(A_325, B_326, C_327)) | k1_xboole_0=C_327 | k1_xboole_0=B_326 | k1_xboole_0=A_325)), inference(cnfTransformation, [status(thm)], [f_85])).
% 4.34/1.76  tff(c_1548, plain, (k2_mcart_1(k1_mcart_1('#skF_8'))=k6_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8') | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_36, c_1545])).
% 4.34/1.76  tff(c_1551, plain, (k2_mcart_1(k1_mcart_1('#skF_8'))=k6_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8') | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_1535, c_1548])).
% 4.34/1.76  tff(c_1573, plain, (k1_xboole_0='#skF_3'), inference(splitLeft, [status(thm)], [c_1551])).
% 4.34/1.76  tff(c_1578, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1573, c_68])).
% 4.34/1.76  tff(c_1581, plain, $false, inference(negUnitSimplification, [status(thm)], [c_998, c_1578])).
% 4.34/1.76  tff(c_1582, plain, (k1_xboole_0='#skF_4' | k2_mcart_1(k1_mcart_1('#skF_8'))=k6_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8')), inference(splitRight, [status(thm)], [c_1551])).
% 4.34/1.76  tff(c_1625, plain, (k2_mcart_1(k1_mcart_1('#skF_8'))=k6_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8')), inference(splitLeft, [status(thm)], [c_1582])).
% 4.34/1.76  tff(c_1358, plain, (![A_279, B_280, C_281]: (k2_zfmisc_1(k2_zfmisc_1(A_279, B_280), C_281)=k3_zfmisc_1(A_279, B_280, C_281))), inference(cnfTransformation, [status(thm)], [f_59])).
% 4.34/1.76  tff(c_1796, plain, (![A_358, A_359, B_360, C_361]: (r2_hidden(k1_mcart_1(A_358), k2_zfmisc_1(A_359, B_360)) | ~r2_hidden(A_358, k3_zfmisc_1(A_359, B_360, C_361)))), inference(superposition, [status(thm), theory('equality')], [c_1358, c_24])).
% 4.34/1.76  tff(c_1825, plain, (r2_hidden(k1_mcart_1('#skF_8'), k2_zfmisc_1('#skF_5', '#skF_6'))), inference(resolution, [status(thm)], [c_34, c_1796])).
% 4.34/1.76  tff(c_1832, plain, (r2_hidden(k2_mcart_1(k1_mcart_1('#skF_8')), '#skF_6')), inference(resolution, [status(thm)], [c_1825, c_22])).
% 4.34/1.76  tff(c_1843, plain, (r2_hidden(k6_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_1625, c_1832])).
% 4.34/1.76  tff(c_1845, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1325, c_1843])).
% 4.34/1.76  tff(c_1846, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_1582])).
% 4.34/1.76  tff(c_1857, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1846, c_68])).
% 4.34/1.76  tff(c_1860, plain, $false, inference(negUnitSimplification, [status(thm)], [c_82, c_1857])).
% 4.34/1.76  tff(c_1861, plain, (v1_xboole_0('#skF_6')), inference(splitRight, [status(thm)], [c_80])).
% 4.34/1.76  tff(c_1897, plain, (![A_367, C_368, B_369]: (r2_hidden(k2_mcart_1(A_367), C_368) | ~r2_hidden(A_367, k2_zfmisc_1(B_369, C_368)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 4.34/1.76  tff(c_1995, plain, (![B_402, C_403]: (r2_hidden(k2_mcart_1('#skF_1'(k2_zfmisc_1(B_402, C_403))), C_403) | v1_xboole_0(k2_zfmisc_1(B_402, C_403)))), inference(resolution, [status(thm)], [c_4, c_1897])).
% 4.34/1.76  tff(c_2018, plain, (![C_403, B_402]: (~v1_xboole_0(C_403) | v1_xboole_0(k2_zfmisc_1(B_402, C_403)))), inference(resolution, [status(thm)], [c_1995, c_2])).
% 4.34/1.76  tff(c_1908, plain, (![A_370, B_371, C_372]: (r2_hidden(k1_mcart_1(A_370), B_371) | ~r2_hidden(A_370, k2_zfmisc_1(B_371, C_372)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 4.34/1.76  tff(c_2040, plain, (![B_409, C_410]: (r2_hidden(k1_mcart_1('#skF_1'(k2_zfmisc_1(B_409, C_410))), B_409) | v1_xboole_0(k2_zfmisc_1(B_409, C_410)))), inference(resolution, [status(thm)], [c_4, c_1908])).
% 4.34/1.76  tff(c_2067, plain, (![B_411, C_412]: (~v1_xboole_0(B_411) | v1_xboole_0(k2_zfmisc_1(B_411, C_412)))), inference(resolution, [status(thm)], [c_2040, c_2])).
% 4.34/1.76  tff(c_2081, plain, (![A_417, B_418, C_419]: (~v1_xboole_0(k2_zfmisc_1(A_417, B_418)) | v1_xboole_0(k3_zfmisc_1(A_417, B_418, C_419)))), inference(superposition, [status(thm), theory('equality')], [c_20, c_2067])).
% 4.34/1.76  tff(c_2085, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_5', '#skF_6'))), inference(resolution, [status(thm)], [c_2081, c_62])).
% 4.34/1.76  tff(c_2091, plain, (~v1_xboole_0('#skF_6')), inference(resolution, [status(thm)], [c_2018, c_2085])).
% 4.34/1.76  tff(c_2096, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1861, c_2091])).
% 4.34/1.76  tff(c_2097, plain, (v1_xboole_0('#skF_5')), inference(splitRight, [status(thm)], [c_81])).
% 4.34/1.76  tff(c_2112, plain, (![A_422, B_423, C_424]: (r2_hidden(k1_mcart_1(A_422), B_423) | ~r2_hidden(A_422, k2_zfmisc_1(B_423, C_424)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 4.34/1.76  tff(c_2219, plain, (![B_456, C_457]: (r2_hidden(k1_mcart_1('#skF_1'(k2_zfmisc_1(B_456, C_457))), B_456) | v1_xboole_0(k2_zfmisc_1(B_456, C_457)))), inference(resolution, [status(thm)], [c_4, c_2112])).
% 4.34/1.76  tff(c_2244, plain, (![B_456, C_457]: (~v1_xboole_0(B_456) | v1_xboole_0(k2_zfmisc_1(B_456, C_457)))), inference(resolution, [status(thm)], [c_2219, c_2])).
% 4.34/1.76  tff(c_2246, plain, (![B_458, C_459]: (~v1_xboole_0(B_458) | v1_xboole_0(k2_zfmisc_1(B_458, C_459)))), inference(resolution, [status(thm)], [c_2219, c_2])).
% 4.34/1.76  tff(c_2258, plain, (![A_464, B_465, C_466]: (~v1_xboole_0(k2_zfmisc_1(A_464, B_465)) | v1_xboole_0(k3_zfmisc_1(A_464, B_465, C_466)))), inference(superposition, [status(thm), theory('equality')], [c_20, c_2246])).
% 4.34/1.76  tff(c_2262, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_5', '#skF_6'))), inference(resolution, [status(thm)], [c_2258, c_62])).
% 4.34/1.76  tff(c_2265, plain, (~v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_2244, c_2262])).
% 4.34/1.76  tff(c_2269, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2097, c_2265])).
% 4.34/1.76  tff(c_2270, plain, (v1_xboole_0('#skF_7')), inference(splitRight, [status(thm)], [c_79])).
% 4.34/1.76  tff(c_2303, plain, (![A_474, B_475, C_476]: (k2_zfmisc_1(k2_zfmisc_1(A_474, B_475), C_476)=k3_zfmisc_1(A_474, B_475, C_476))), inference(cnfTransformation, [status(thm)], [f_59])).
% 4.34/1.76  tff(c_2374, plain, (![A_492, C_493, A_494, B_495]: (r2_hidden(k2_mcart_1(A_492), C_493) | ~r2_hidden(A_492, k3_zfmisc_1(A_494, B_495, C_493)))), inference(superposition, [status(thm), theory('equality')], [c_2303, c_22])).
% 4.34/1.76  tff(c_2384, plain, (r2_hidden(k2_mcart_1('#skF_8'), '#skF_7')), inference(resolution, [status(thm)], [c_34, c_2374])).
% 4.34/1.76  tff(c_2391, plain, (~v1_xboole_0('#skF_7')), inference(resolution, [status(thm)], [c_2384, c_2])).
% 4.34/1.76  tff(c_2396, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2270, c_2391])).
% 4.34/1.76  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.34/1.76  
% 4.34/1.76  Inference rules
% 4.34/1.76  ----------------------
% 4.34/1.76  #Ref     : 0
% 4.34/1.76  #Sup     : 521
% 4.34/1.76  #Fact    : 0
% 4.34/1.76  #Define  : 0
% 4.34/1.76  #Split   : 38
% 4.34/1.76  #Chain   : 0
% 4.34/1.76  #Close   : 0
% 4.34/1.76  
% 4.34/1.76  Ordering : KBO
% 4.34/1.76  
% 4.34/1.76  Simplification rules
% 4.34/1.76  ----------------------
% 4.34/1.76  #Subsume      : 65
% 4.34/1.76  #Demod        : 237
% 4.34/1.76  #Tautology    : 71
% 4.34/1.76  #SimpNegUnit  : 38
% 4.34/1.76  #BackRed      : 107
% 4.34/1.76  
% 4.34/1.76  #Partial instantiations: 0
% 4.34/1.76  #Strategies tried      : 1
% 4.34/1.76  
% 4.34/1.76  Timing (in seconds)
% 4.34/1.76  ----------------------
% 4.34/1.77  Preprocessing        : 0.32
% 4.34/1.77  Parsing              : 0.17
% 4.34/1.77  CNF conversion       : 0.02
% 4.34/1.77  Main loop            : 0.66
% 4.34/1.77  Inferencing          : 0.24
% 4.34/1.77  Reduction            : 0.20
% 4.34/1.77  Demodulation         : 0.14
% 4.34/1.77  BG Simplification    : 0.03
% 4.34/1.77  Subsumption          : 0.11
% 4.34/1.77  Abstraction          : 0.03
% 4.34/1.77  MUC search           : 0.00
% 4.34/1.77  Cooper               : 0.00
% 4.34/1.77  Total                : 1.03
% 4.34/1.77  Index Insertion      : 0.00
% 4.34/1.77  Index Deletion       : 0.00
% 4.34/1.77  Index Matching       : 0.00
% 4.34/1.77  BG Taut test         : 0.00
%------------------------------------------------------------------------------
