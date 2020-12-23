%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0375+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:36:12 EST 2020

% Result     : Theorem 8.27s
% Output     : CNFRefutation 8.27s
% Verified   : 
% Statistics : Number of formulae       :   72 ( 177 expanded)
%              Number of leaves         :   26 (  69 expanded)
%              Depth                    :   10
%              Number of atoms          :  111 ( 447 expanded)
%              Number of equality atoms :   24 (  73 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k1_enumset1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_7 > #skF_3 > #skF_2 > #skF_6 > #skF_9 > #skF_8 > #skF_1 > #skF_5 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_89,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,A)
       => ! [C] :
            ( m1_subset_1(C,A)
           => ! [D] :
                ( m1_subset_1(D,A)
               => ( A != k1_xboole_0
                 => m1_subset_1(k1_enumset1(B,C,D),k1_zfmisc_1(A)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t57_subset_1)).

tff(f_66,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_59,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_46,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_39,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

tff(f_75,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_boole)).

tff(f_70,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_boole)).

tff(c_58,plain,(
    k1_xboole_0 != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_180,plain,(
    ! [A_67,B_68] :
      ( r2_hidden('#skF_5'(A_67,B_68),A_67)
      | r1_tarski(A_67,B_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_48,plain,(
    ! [A_15,B_16] :
      ( ~ r2_hidden('#skF_5'(A_15,B_16),B_16)
      | r1_tarski(A_15,B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_195,plain,(
    ! [A_67] : r1_tarski(A_67,A_67) ),
    inference(resolution,[status(thm)],[c_180,c_48])).

tff(c_60,plain,(
    m1_subset_1('#skF_9','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_83,plain,(
    ! [B_42,A_43] :
      ( v1_xboole_0(B_42)
      | ~ m1_subset_1(B_42,A_43)
      | ~ v1_xboole_0(A_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_93,plain,
    ( v1_xboole_0('#skF_9')
    | ~ v1_xboole_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_60,c_83])).

tff(c_96,plain,(
    ~ v1_xboole_0('#skF_6') ),
    inference(splitLeft,[status(thm)],[c_93])).

tff(c_28,plain,(
    ! [C_12,A_8] :
      ( r2_hidden(C_12,k1_zfmisc_1(A_8))
      | ~ r1_tarski(C_12,A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_127,plain,(
    ! [B_54,A_55] :
      ( m1_subset_1(B_54,A_55)
      | ~ r2_hidden(B_54,A_55)
      | v1_xboole_0(A_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_296,plain,(
    ! [C_95,A_96] :
      ( m1_subset_1(C_95,k1_zfmisc_1(A_96))
      | v1_xboole_0(k1_zfmisc_1(A_96))
      | ~ r1_tarski(C_95,A_96) ) ),
    inference(resolution,[status(thm)],[c_28,c_127])).

tff(c_56,plain,(
    ~ m1_subset_1(k1_enumset1('#skF_7','#skF_8','#skF_9'),k1_zfmisc_1('#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_313,plain,
    ( v1_xboole_0(k1_zfmisc_1('#skF_6'))
    | ~ r1_tarski(k1_enumset1('#skF_7','#skF_8','#skF_9'),'#skF_6') ),
    inference(resolution,[status(thm)],[c_296,c_56])).

tff(c_314,plain,(
    ~ r1_tarski(k1_enumset1('#skF_7','#skF_8','#skF_9'),'#skF_6') ),
    inference(splitLeft,[status(thm)],[c_313])).

tff(c_62,plain,(
    m1_subset_1('#skF_8','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_64,plain,(
    m1_subset_1('#skF_7','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_50,plain,(
    ! [A_15,B_16] :
      ( r2_hidden('#skF_5'(A_15,B_16),A_15)
      | r1_tarski(A_15,B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_268,plain,(
    ! [E_91,C_92,B_93,A_94] :
      ( E_91 = C_92
      | E_91 = B_93
      | E_91 = A_94
      | ~ r2_hidden(E_91,k1_enumset1(A_94,B_93,C_92)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_5452,plain,(
    ! [A_618,B_619,C_620,B_621] :
      ( '#skF_5'(k1_enumset1(A_618,B_619,C_620),B_621) = C_620
      | '#skF_5'(k1_enumset1(A_618,B_619,C_620),B_621) = B_619
      | '#skF_5'(k1_enumset1(A_618,B_619,C_620),B_621) = A_618
      | r1_tarski(k1_enumset1(A_618,B_619,C_620),B_621) ) ),
    inference(resolution,[status(thm)],[c_50,c_268])).

tff(c_5514,plain,
    ( '#skF_5'(k1_enumset1('#skF_7','#skF_8','#skF_9'),'#skF_6') = '#skF_9'
    | '#skF_5'(k1_enumset1('#skF_7','#skF_8','#skF_9'),'#skF_6') = '#skF_8'
    | '#skF_5'(k1_enumset1('#skF_7','#skF_8','#skF_9'),'#skF_6') = '#skF_7' ),
    inference(resolution,[status(thm)],[c_5452,c_314])).

tff(c_5645,plain,(
    '#skF_5'(k1_enumset1('#skF_7','#skF_8','#skF_9'),'#skF_6') = '#skF_7' ),
    inference(splitLeft,[status(thm)],[c_5514])).

tff(c_40,plain,(
    ! [B_14,A_13] :
      ( r2_hidden(B_14,A_13)
      | ~ m1_subset_1(B_14,A_13)
      | v1_xboole_0(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_169,plain,(
    ! [A_65,B_66] :
      ( ~ r2_hidden('#skF_5'(A_65,B_66),B_66)
      | r1_tarski(A_65,B_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_178,plain,(
    ! [A_65,A_13] :
      ( r1_tarski(A_65,A_13)
      | ~ m1_subset_1('#skF_5'(A_65,A_13),A_13)
      | v1_xboole_0(A_13) ) ),
    inference(resolution,[status(thm)],[c_40,c_169])).

tff(c_5663,plain,
    ( r1_tarski(k1_enumset1('#skF_7','#skF_8','#skF_9'),'#skF_6')
    | ~ m1_subset_1('#skF_7','#skF_6')
    | v1_xboole_0('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_5645,c_178])).

tff(c_5680,plain,
    ( r1_tarski(k1_enumset1('#skF_7','#skF_8','#skF_9'),'#skF_6')
    | v1_xboole_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_5663])).

tff(c_5682,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_96,c_314,c_5680])).

tff(c_5683,plain,
    ( '#skF_5'(k1_enumset1('#skF_7','#skF_8','#skF_9'),'#skF_6') = '#skF_8'
    | '#skF_5'(k1_enumset1('#skF_7','#skF_8','#skF_9'),'#skF_6') = '#skF_9' ),
    inference(splitRight,[status(thm)],[c_5514])).

tff(c_5685,plain,(
    '#skF_5'(k1_enumset1('#skF_7','#skF_8','#skF_9'),'#skF_6') = '#skF_9' ),
    inference(splitLeft,[status(thm)],[c_5683])).

tff(c_5704,plain,
    ( r1_tarski(k1_enumset1('#skF_7','#skF_8','#skF_9'),'#skF_6')
    | ~ m1_subset_1('#skF_9','#skF_6')
    | v1_xboole_0('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_5685,c_178])).

tff(c_5721,plain,
    ( r1_tarski(k1_enumset1('#skF_7','#skF_8','#skF_9'),'#skF_6')
    | v1_xboole_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_5704])).

tff(c_5723,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_96,c_314,c_5721])).

tff(c_5724,plain,(
    '#skF_5'(k1_enumset1('#skF_7','#skF_8','#skF_9'),'#skF_6') = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_5683])).

tff(c_5744,plain,
    ( r1_tarski(k1_enumset1('#skF_7','#skF_8','#skF_9'),'#skF_6')
    | ~ m1_subset_1('#skF_8','#skF_6')
    | v1_xboole_0('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_5724,c_178])).

tff(c_5761,plain,
    ( r1_tarski(k1_enumset1('#skF_7','#skF_8','#skF_9'),'#skF_6')
    | v1_xboole_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_5744])).

tff(c_5763,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_96,c_314,c_5761])).

tff(c_5764,plain,(
    v1_xboole_0(k1_zfmisc_1('#skF_6')) ),
    inference(splitRight,[status(thm)],[c_313])).

tff(c_107,plain,(
    ! [C_48,A_49] :
      ( r2_hidden(C_48,k1_zfmisc_1(A_49))
      | ~ r1_tarski(C_48,A_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_54,plain,(
    ! [B_22,A_21] :
      ( ~ v1_xboole_0(B_22)
      | ~ r2_hidden(A_21,B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_115,plain,(
    ! [A_49,C_48] :
      ( ~ v1_xboole_0(k1_zfmisc_1(A_49))
      | ~ r1_tarski(C_48,A_49) ) ),
    inference(resolution,[status(thm)],[c_107,c_54])).

tff(c_5795,plain,(
    ! [C_636] : ~ r1_tarski(C_636,'#skF_6') ),
    inference(resolution,[status(thm)],[c_5764,c_115])).

tff(c_5806,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_195,c_5795])).

tff(c_5808,plain,(
    v1_xboole_0('#skF_6') ),
    inference(splitRight,[status(thm)],[c_93])).

tff(c_52,plain,(
    ! [A_20] :
      ( k1_xboole_0 = A_20
      | ~ v1_xboole_0(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_5816,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(resolution,[status(thm)],[c_5808,c_52])).

tff(c_5820,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_5816])).

%------------------------------------------------------------------------------
