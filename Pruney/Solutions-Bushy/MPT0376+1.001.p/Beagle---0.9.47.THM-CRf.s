%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0376+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:36:12 EST 2020

% Result     : Theorem 8.89s
% Output     : CNFRefutation 8.89s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 226 expanded)
%              Number of leaves         :   27 (  84 expanded)
%              Depth                    :   11
%              Number of atoms          :  123 ( 628 expanded)
%              Number of equality atoms :   32 ( 120 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k2_enumset1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_4 > #skF_7 > #skF_10 > #skF_6 > #skF_9 > #skF_3 > #skF_8 > #skF_2 > #skF_1 > #skF_5

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_95,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,A)
       => ! [C] :
            ( m1_subset_1(C,A)
           => ! [D] :
                ( m1_subset_1(D,A)
               => ! [E] :
                    ( m1_subset_1(E,A)
                   => ( A != k1_xboole_0
                     => m1_subset_1(k2_enumset1(B,C,D,E),k1_zfmisc_1(A)) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t58_subset_1)).

tff(f_62,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_69,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_49,axiom,(
    ! [A,B,C,D,E] :
      ( E = k2_enumset1(A,B,C,D)
    <=> ! [F] :
          ( r2_hidden(F,E)
        <=> ~ ( F != A
              & F != B
              & F != C
              & F != D ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_enumset1)).

tff(f_78,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_boole)).

tff(f_73,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_boole)).

tff(c_64,plain,(
    k1_xboole_0 != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_68,plain,(
    m1_subset_1('#skF_9','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_107,plain,(
    ! [B_62,A_63] :
      ( v1_xboole_0(B_62)
      | ~ m1_subset_1(B_62,A_63)
      | ~ v1_xboole_0(A_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_124,plain,
    ( v1_xboole_0('#skF_9')
    | ~ v1_xboole_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_68,c_107])).

tff(c_128,plain,(
    ~ v1_xboole_0('#skF_6') ),
    inference(splitLeft,[status(thm)],[c_124])).

tff(c_4,plain,(
    ! [C_5,A_1] :
      ( r2_hidden(C_5,k1_zfmisc_1(A_1))
      | ~ r1_tarski(C_5,A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_145,plain,(
    ! [B_72,A_73] :
      ( m1_subset_1(B_72,A_73)
      | ~ r2_hidden(B_72,A_73)
      | v1_xboole_0(A_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_400,plain,(
    ! [C_143,A_144] :
      ( m1_subset_1(C_143,k1_zfmisc_1(A_144))
      | v1_xboole_0(k1_zfmisc_1(A_144))
      | ~ r1_tarski(C_143,A_144) ) ),
    inference(resolution,[status(thm)],[c_4,c_145])).

tff(c_62,plain,(
    ~ m1_subset_1(k2_enumset1('#skF_7','#skF_8','#skF_9','#skF_10'),k1_zfmisc_1('#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_417,plain,
    ( v1_xboole_0(k1_zfmisc_1('#skF_6'))
    | ~ r1_tarski(k2_enumset1('#skF_7','#skF_8','#skF_9','#skF_10'),'#skF_6') ),
    inference(resolution,[status(thm)],[c_400,c_62])).

tff(c_418,plain,(
    ~ r1_tarski(k2_enumset1('#skF_7','#skF_8','#skF_9','#skF_10'),'#skF_6') ),
    inference(splitLeft,[status(thm)],[c_417])).

tff(c_70,plain,(
    m1_subset_1('#skF_8','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_66,plain,(
    m1_subset_1('#skF_10','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_72,plain,(
    m1_subset_1('#skF_7','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_56,plain,(
    ! [A_16,B_17] :
      ( r2_hidden('#skF_5'(A_16,B_17),A_16)
      | r1_tarski(A_16,B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_461,plain,(
    ! [A_155,D_152,F_151,C_153,B_154] :
      ( F_151 = D_152
      | F_151 = C_153
      | F_151 = B_154
      | F_151 = A_155
      | ~ r2_hidden(F_151,k2_enumset1(A_155,B_154,C_153,D_152)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_5250,plain,(
    ! [B_601,D_604,A_602,B_603,C_605] :
      ( '#skF_5'(k2_enumset1(A_602,B_603,C_605,D_604),B_601) = D_604
      | '#skF_5'(k2_enumset1(A_602,B_603,C_605,D_604),B_601) = C_605
      | '#skF_5'(k2_enumset1(A_602,B_603,C_605,D_604),B_601) = B_603
      | '#skF_5'(k2_enumset1(A_602,B_603,C_605,D_604),B_601) = A_602
      | r1_tarski(k2_enumset1(A_602,B_603,C_605,D_604),B_601) ) ),
    inference(resolution,[status(thm)],[c_56,c_461])).

tff(c_5323,plain,
    ( '#skF_5'(k2_enumset1('#skF_7','#skF_8','#skF_9','#skF_10'),'#skF_6') = '#skF_10'
    | '#skF_5'(k2_enumset1('#skF_7','#skF_8','#skF_9','#skF_10'),'#skF_6') = '#skF_9'
    | '#skF_5'(k2_enumset1('#skF_7','#skF_8','#skF_9','#skF_10'),'#skF_6') = '#skF_8'
    | '#skF_5'(k2_enumset1('#skF_7','#skF_8','#skF_9','#skF_10'),'#skF_6') = '#skF_7' ),
    inference(resolution,[status(thm)],[c_5250,c_418])).

tff(c_5602,plain,(
    '#skF_5'(k2_enumset1('#skF_7','#skF_8','#skF_9','#skF_10'),'#skF_6') = '#skF_7' ),
    inference(splitLeft,[status(thm)],[c_5323])).

tff(c_46,plain,(
    ! [B_15,A_14] :
      ( r2_hidden(B_15,A_14)
      | ~ m1_subset_1(B_15,A_14)
      | v1_xboole_0(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_212,plain,(
    ! [A_92,B_93] :
      ( ~ r2_hidden('#skF_5'(A_92,B_93),B_93)
      | r1_tarski(A_92,B_93) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_225,plain,(
    ! [A_92,A_14] :
      ( r1_tarski(A_92,A_14)
      | ~ m1_subset_1('#skF_5'(A_92,A_14),A_14)
      | v1_xboole_0(A_14) ) ),
    inference(resolution,[status(thm)],[c_46,c_212])).

tff(c_5622,plain,
    ( r1_tarski(k2_enumset1('#skF_7','#skF_8','#skF_9','#skF_10'),'#skF_6')
    | ~ m1_subset_1('#skF_7','#skF_6')
    | v1_xboole_0('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_5602,c_225])).

tff(c_5643,plain,
    ( r1_tarski(k2_enumset1('#skF_7','#skF_8','#skF_9','#skF_10'),'#skF_6')
    | v1_xboole_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_5622])).

tff(c_5645,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_128,c_418,c_5643])).

tff(c_5646,plain,
    ( '#skF_5'(k2_enumset1('#skF_7','#skF_8','#skF_9','#skF_10'),'#skF_6') = '#skF_8'
    | '#skF_5'(k2_enumset1('#skF_7','#skF_8','#skF_9','#skF_10'),'#skF_6') = '#skF_9'
    | '#skF_5'(k2_enumset1('#skF_7','#skF_8','#skF_9','#skF_10'),'#skF_6') = '#skF_10' ),
    inference(splitRight,[status(thm)],[c_5323])).

tff(c_6102,plain,(
    '#skF_5'(k2_enumset1('#skF_7','#skF_8','#skF_9','#skF_10'),'#skF_6') = '#skF_10' ),
    inference(splitLeft,[status(thm)],[c_5646])).

tff(c_6126,plain,
    ( r1_tarski(k2_enumset1('#skF_7','#skF_8','#skF_9','#skF_10'),'#skF_6')
    | ~ m1_subset_1('#skF_10','#skF_6')
    | v1_xboole_0('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_6102,c_225])).

tff(c_6149,plain,
    ( r1_tarski(k2_enumset1('#skF_7','#skF_8','#skF_9','#skF_10'),'#skF_6')
    | v1_xboole_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_6126])).

tff(c_6151,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_128,c_418,c_6149])).

tff(c_6152,plain,
    ( '#skF_5'(k2_enumset1('#skF_7','#skF_8','#skF_9','#skF_10'),'#skF_6') = '#skF_9'
    | '#skF_5'(k2_enumset1('#skF_7','#skF_8','#skF_9','#skF_10'),'#skF_6') = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_5646])).

tff(c_6266,plain,(
    '#skF_5'(k2_enumset1('#skF_7','#skF_8','#skF_9','#skF_10'),'#skF_6') = '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_6152])).

tff(c_6313,plain,
    ( r1_tarski(k2_enumset1('#skF_7','#skF_8','#skF_9','#skF_10'),'#skF_6')
    | ~ m1_subset_1('#skF_8','#skF_6')
    | v1_xboole_0('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_6266,c_225])).

tff(c_6336,plain,
    ( r1_tarski(k2_enumset1('#skF_7','#skF_8','#skF_9','#skF_10'),'#skF_6')
    | v1_xboole_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_6313])).

tff(c_6338,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_128,c_418,c_6336])).

tff(c_6339,plain,(
    '#skF_5'(k2_enumset1('#skF_7','#skF_8','#skF_9','#skF_10'),'#skF_6') = '#skF_9' ),
    inference(splitRight,[status(thm)],[c_6152])).

tff(c_6365,plain,
    ( r1_tarski(k2_enumset1('#skF_7','#skF_8','#skF_9','#skF_10'),'#skF_6')
    | ~ m1_subset_1('#skF_9','#skF_6')
    | v1_xboole_0('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_6339,c_225])).

tff(c_6388,plain,
    ( r1_tarski(k2_enumset1('#skF_7','#skF_8','#skF_9','#skF_10'),'#skF_6')
    | v1_xboole_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_6365])).

tff(c_6390,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_128,c_418,c_6388])).

tff(c_6391,plain,(
    v1_xboole_0(k1_zfmisc_1('#skF_6')) ),
    inference(splitRight,[status(thm)],[c_417])).

tff(c_81,plain,(
    ! [C_46,A_47] :
      ( r2_hidden(C_46,k1_zfmisc_1(A_47))
      | ~ r1_tarski(C_46,A_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_60,plain,(
    ! [B_23,A_22] :
      ( ~ v1_xboole_0(B_23)
      | ~ r2_hidden(A_22,B_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_85,plain,(
    ! [A_47,C_46] :
      ( ~ v1_xboole_0(k1_zfmisc_1(A_47))
      | ~ r1_tarski(C_46,A_47) ) ),
    inference(resolution,[status(thm)],[c_81,c_60])).

tff(c_6398,plain,(
    ! [C_46] : ~ r1_tarski(C_46,'#skF_6') ),
    inference(resolution,[status(thm)],[c_6391,c_85])).

tff(c_6392,plain,(
    r1_tarski(k2_enumset1('#skF_7','#skF_8','#skF_9','#skF_10'),'#skF_6') ),
    inference(splitRight,[status(thm)],[c_417])).

tff(c_6417,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_6398,c_6392])).

tff(c_6419,plain,(
    v1_xboole_0('#skF_6') ),
    inference(splitRight,[status(thm)],[c_124])).

tff(c_58,plain,(
    ! [A_21] :
      ( k1_xboole_0 = A_21
      | ~ v1_xboole_0(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_6426,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(resolution,[status(thm)],[c_6419,c_58])).

tff(c_6430,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_6426])).

%------------------------------------------------------------------------------
