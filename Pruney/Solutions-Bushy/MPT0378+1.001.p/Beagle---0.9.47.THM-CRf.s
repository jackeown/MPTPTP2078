%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0378+1.001 : TPTP v7.4.0. Released v7.4.0.
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

% Result     : Theorem 10.79s
% Output     : CNFRefutation 10.79s
% Verified   : 
% Statistics : Number of formulae       :   99 ( 404 expanded)
%              Number of leaves         :   29 ( 140 expanded)
%              Depth                    :   13
%              Number of atoms          :  172 (1312 expanded)
%              Number of equality atoms :   52 ( 274 expanded)
%              Maximal formula depth    :   18 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k4_enumset1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_11 > #skF_7 > #skF_3 > #skF_10 > #skF_6 > #skF_9 > #skF_8 > #skF_5 > #skF_2 > #skF_4 > #skF_1 > #skF_12

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_11',type,(
    '#skF_11': $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_12',type,(
    '#skF_12': $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_107,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,A)
       => ! [C] :
            ( m1_subset_1(C,A)
           => ! [D] :
                ( m1_subset_1(D,A)
               => ! [E] :
                    ( m1_subset_1(E,A)
                   => ! [F] :
                        ( m1_subset_1(F,A)
                       => ! [G] :
                            ( m1_subset_1(G,A)
                           => ( A != k1_xboole_0
                             => m1_subset_1(k4_enumset1(B,C,D,E,F,G),k1_zfmisc_1(A)) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_subset_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_44,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_75,axiom,(
    ! [A,B,C,D,E,F,G] :
      ( G = k4_enumset1(A,B,C,D,E,F)
    <=> ! [H] :
          ( r2_hidden(H,G)
        <=> ~ ( H != A
              & H != B
              & H != C
              & H != D
              & H != E
              & H != F ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_enumset1)).

tff(f_79,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_boole)).

tff(f_84,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_boole)).

tff(c_76,plain,(
    k1_xboole_0 != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_10593,plain,(
    ! [A_1047,B_1048] :
      ( r2_hidden('#skF_3'(A_1047,B_1048),A_1047)
      | r1_tarski(A_1047,B_1048) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_24,plain,(
    ! [A_8,B_9] :
      ( ~ r2_hidden('#skF_3'(A_8,B_9),B_9)
      | r1_tarski(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_10626,plain,(
    ! [A_1051] : r1_tarski(A_1051,A_1051) ),
    inference(resolution,[status(thm)],[c_10593,c_24])).

tff(c_84,plain,(
    m1_subset_1('#skF_9','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_91,plain,(
    ! [B_86,A_87] :
      ( v1_xboole_0(B_86)
      | ~ m1_subset_1(B_86,A_87)
      | ~ v1_xboole_0(A_87) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_110,plain,
    ( v1_xboole_0('#skF_9')
    | ~ v1_xboole_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_84,c_91])).

tff(c_116,plain,(
    ~ v1_xboole_0('#skF_6') ),
    inference(splitLeft,[status(thm)],[c_110])).

tff(c_117,plain,(
    ! [B_88,A_89] :
      ( m1_subset_1(B_88,A_89)
      | ~ v1_xboole_0(B_88)
      | ~ v1_xboole_0(A_89) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_74,plain,(
    ~ m1_subset_1(k4_enumset1('#skF_7','#skF_8','#skF_9','#skF_10','#skF_11','#skF_12'),k1_zfmisc_1('#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_125,plain,
    ( ~ v1_xboole_0(k4_enumset1('#skF_7','#skF_8','#skF_9','#skF_10','#skF_11','#skF_12'))
    | ~ v1_xboole_0(k1_zfmisc_1('#skF_6')) ),
    inference(resolution,[status(thm)],[c_117,c_74])).

tff(c_126,plain,(
    ~ v1_xboole_0(k1_zfmisc_1('#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_125])).

tff(c_4,plain,(
    ! [C_5,A_1] :
      ( r2_hidden(C_5,k1_zfmisc_1(A_1))
      | ~ r1_tarski(C_5,A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_148,plain,(
    ! [B_98,A_99] :
      ( m1_subset_1(B_98,A_99)
      | ~ r2_hidden(B_98,A_99)
      | v1_xboole_0(A_99) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_337,plain,(
    ! [C_190,A_191] :
      ( m1_subset_1(C_190,k1_zfmisc_1(A_191))
      | v1_xboole_0(k1_zfmisc_1(A_191))
      | ~ r1_tarski(C_190,A_191) ) ),
    inference(resolution,[status(thm)],[c_4,c_148])).

tff(c_343,plain,
    ( v1_xboole_0(k1_zfmisc_1('#skF_6'))
    | ~ r1_tarski(k4_enumset1('#skF_7','#skF_8','#skF_9','#skF_10','#skF_11','#skF_12'),'#skF_6') ),
    inference(resolution,[status(thm)],[c_337,c_74])).

tff(c_347,plain,(
    ~ r1_tarski(k4_enumset1('#skF_7','#skF_8','#skF_9','#skF_10','#skF_11','#skF_12'),'#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_126,c_343])).

tff(c_82,plain,(
    m1_subset_1('#skF_10','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_80,plain,(
    m1_subset_1('#skF_11','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_86,plain,(
    m1_subset_1('#skF_8','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_78,plain,(
    m1_subset_1('#skF_12','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_88,plain,(
    m1_subset_1('#skF_7','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_26,plain,(
    ! [A_8,B_9] :
      ( r2_hidden('#skF_3'(A_8,B_9),A_8)
      | r1_tarski(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_470,plain,(
    ! [E_219,C_221,D_216,B_217,A_220,H_218,F_215] :
      ( H_218 = F_215
      | H_218 = E_219
      | H_218 = D_216
      | H_218 = C_221
      | H_218 = B_217
      | H_218 = A_220
      | ~ r2_hidden(H_218,k4_enumset1(A_220,B_217,C_221,D_216,E_219,F_215)) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_8346,plain,(
    ! [B_943,C_938,F_942,D_939,E_941,A_944,B_940] :
      ( '#skF_3'(k4_enumset1(A_944,B_940,C_938,D_939,E_941,F_942),B_943) = F_942
      | '#skF_3'(k4_enumset1(A_944,B_940,C_938,D_939,E_941,F_942),B_943) = E_941
      | '#skF_3'(k4_enumset1(A_944,B_940,C_938,D_939,E_941,F_942),B_943) = D_939
      | '#skF_3'(k4_enumset1(A_944,B_940,C_938,D_939,E_941,F_942),B_943) = C_938
      | '#skF_3'(k4_enumset1(A_944,B_940,C_938,D_939,E_941,F_942),B_943) = B_940
      | '#skF_3'(k4_enumset1(A_944,B_940,C_938,D_939,E_941,F_942),B_943) = A_944
      | r1_tarski(k4_enumset1(A_944,B_940,C_938,D_939,E_941,F_942),B_943) ) ),
    inference(resolution,[status(thm)],[c_26,c_470])).

tff(c_8469,plain,
    ( '#skF_3'(k4_enumset1('#skF_7','#skF_8','#skF_9','#skF_10','#skF_11','#skF_12'),'#skF_6') = '#skF_12'
    | '#skF_3'(k4_enumset1('#skF_7','#skF_8','#skF_9','#skF_10','#skF_11','#skF_12'),'#skF_6') = '#skF_11'
    | '#skF_3'(k4_enumset1('#skF_7','#skF_8','#skF_9','#skF_10','#skF_11','#skF_12'),'#skF_6') = '#skF_10'
    | '#skF_3'(k4_enumset1('#skF_7','#skF_8','#skF_9','#skF_10','#skF_11','#skF_12'),'#skF_6') = '#skF_9'
    | '#skF_3'(k4_enumset1('#skF_7','#skF_8','#skF_9','#skF_10','#skF_11','#skF_12'),'#skF_6') = '#skF_8'
    | '#skF_3'(k4_enumset1('#skF_7','#skF_8','#skF_9','#skF_10','#skF_11','#skF_12'),'#skF_6') = '#skF_7' ),
    inference(resolution,[status(thm)],[c_8346,c_347])).

tff(c_8679,plain,(
    '#skF_3'(k4_enumset1('#skF_7','#skF_8','#skF_9','#skF_10','#skF_11','#skF_12'),'#skF_6') = '#skF_7' ),
    inference(splitLeft,[status(thm)],[c_8469])).

tff(c_16,plain,(
    ! [B_7,A_6] :
      ( r2_hidden(B_7,A_6)
      | ~ m1_subset_1(B_7,A_6)
      | v1_xboole_0(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_172,plain,(
    ! [A_104,B_105] :
      ( ~ r2_hidden('#skF_3'(A_104,B_105),B_105)
      | r1_tarski(A_104,B_105) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_186,plain,(
    ! [A_104,A_6] :
      ( r1_tarski(A_104,A_6)
      | ~ m1_subset_1('#skF_3'(A_104,A_6),A_6)
      | v1_xboole_0(A_6) ) ),
    inference(resolution,[status(thm)],[c_16,c_172])).

tff(c_8705,plain,
    ( r1_tarski(k4_enumset1('#skF_7','#skF_8','#skF_9','#skF_10','#skF_11','#skF_12'),'#skF_6')
    | ~ m1_subset_1('#skF_7','#skF_6')
    | v1_xboole_0('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_8679,c_186])).

tff(c_8730,plain,
    ( r1_tarski(k4_enumset1('#skF_7','#skF_8','#skF_9','#skF_10','#skF_11','#skF_12'),'#skF_6')
    | v1_xboole_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_8705])).

tff(c_8732,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_116,c_347,c_8730])).

tff(c_8733,plain,
    ( '#skF_3'(k4_enumset1('#skF_7','#skF_8','#skF_9','#skF_10','#skF_11','#skF_12'),'#skF_6') = '#skF_8'
    | '#skF_3'(k4_enumset1('#skF_7','#skF_8','#skF_9','#skF_10','#skF_11','#skF_12'),'#skF_6') = '#skF_9'
    | '#skF_3'(k4_enumset1('#skF_7','#skF_8','#skF_9','#skF_10','#skF_11','#skF_12'),'#skF_6') = '#skF_10'
    | '#skF_3'(k4_enumset1('#skF_7','#skF_8','#skF_9','#skF_10','#skF_11','#skF_12'),'#skF_6') = '#skF_11'
    | '#skF_3'(k4_enumset1('#skF_7','#skF_8','#skF_9','#skF_10','#skF_11','#skF_12'),'#skF_6') = '#skF_12' ),
    inference(splitRight,[status(thm)],[c_8469])).

tff(c_9123,plain,(
    '#skF_3'(k4_enumset1('#skF_7','#skF_8','#skF_9','#skF_10','#skF_11','#skF_12'),'#skF_6') = '#skF_12' ),
    inference(splitLeft,[status(thm)],[c_8733])).

tff(c_9150,plain,
    ( r1_tarski(k4_enumset1('#skF_7','#skF_8','#skF_9','#skF_10','#skF_11','#skF_12'),'#skF_6')
    | ~ m1_subset_1('#skF_12','#skF_6')
    | v1_xboole_0('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_9123,c_186])).

tff(c_9175,plain,
    ( r1_tarski(k4_enumset1('#skF_7','#skF_8','#skF_9','#skF_10','#skF_11','#skF_12'),'#skF_6')
    | v1_xboole_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_9150])).

tff(c_9177,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_116,c_347,c_9175])).

tff(c_9178,plain,
    ( '#skF_3'(k4_enumset1('#skF_7','#skF_8','#skF_9','#skF_10','#skF_11','#skF_12'),'#skF_6') = '#skF_11'
    | '#skF_3'(k4_enumset1('#skF_7','#skF_8','#skF_9','#skF_10','#skF_11','#skF_12'),'#skF_6') = '#skF_10'
    | '#skF_3'(k4_enumset1('#skF_7','#skF_8','#skF_9','#skF_10','#skF_11','#skF_12'),'#skF_6') = '#skF_9'
    | '#skF_3'(k4_enumset1('#skF_7','#skF_8','#skF_9','#skF_10','#skF_11','#skF_12'),'#skF_6') = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_8733])).

tff(c_9407,plain,(
    '#skF_3'(k4_enumset1('#skF_7','#skF_8','#skF_9','#skF_10','#skF_11','#skF_12'),'#skF_6') = '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_9178])).

tff(c_9435,plain,
    ( r1_tarski(k4_enumset1('#skF_7','#skF_8','#skF_9','#skF_10','#skF_11','#skF_12'),'#skF_6')
    | ~ m1_subset_1('#skF_8','#skF_6')
    | v1_xboole_0('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_9407,c_186])).

tff(c_9460,plain,
    ( r1_tarski(k4_enumset1('#skF_7','#skF_8','#skF_9','#skF_10','#skF_11','#skF_12'),'#skF_6')
    | v1_xboole_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_9435])).

tff(c_9462,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_116,c_347,c_9460])).

tff(c_9463,plain,
    ( '#skF_3'(k4_enumset1('#skF_7','#skF_8','#skF_9','#skF_10','#skF_11','#skF_12'),'#skF_6') = '#skF_9'
    | '#skF_3'(k4_enumset1('#skF_7','#skF_8','#skF_9','#skF_10','#skF_11','#skF_12'),'#skF_6') = '#skF_10'
    | '#skF_3'(k4_enumset1('#skF_7','#skF_8','#skF_9','#skF_10','#skF_11','#skF_12'),'#skF_6') = '#skF_11' ),
    inference(splitRight,[status(thm)],[c_9178])).

tff(c_9865,plain,(
    '#skF_3'(k4_enumset1('#skF_7','#skF_8','#skF_9','#skF_10','#skF_11','#skF_12'),'#skF_6') = '#skF_11' ),
    inference(splitLeft,[status(thm)],[c_9463])).

tff(c_9894,plain,
    ( r1_tarski(k4_enumset1('#skF_7','#skF_8','#skF_9','#skF_10','#skF_11','#skF_12'),'#skF_6')
    | ~ m1_subset_1('#skF_11','#skF_6')
    | v1_xboole_0('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_9865,c_186])).

tff(c_9919,plain,
    ( r1_tarski(k4_enumset1('#skF_7','#skF_8','#skF_9','#skF_10','#skF_11','#skF_12'),'#skF_6')
    | v1_xboole_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_9894])).

tff(c_9921,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_116,c_347,c_9919])).

tff(c_9922,plain,
    ( '#skF_3'(k4_enumset1('#skF_7','#skF_8','#skF_9','#skF_10','#skF_11','#skF_12'),'#skF_6') = '#skF_10'
    | '#skF_3'(k4_enumset1('#skF_7','#skF_8','#skF_9','#skF_10','#skF_11','#skF_12'),'#skF_6') = '#skF_9' ),
    inference(splitRight,[status(thm)],[c_9463])).

tff(c_10402,plain,(
    '#skF_3'(k4_enumset1('#skF_7','#skF_8','#skF_9','#skF_10','#skF_11','#skF_12'),'#skF_6') = '#skF_9' ),
    inference(splitLeft,[status(thm)],[c_9922])).

tff(c_10432,plain,
    ( r1_tarski(k4_enumset1('#skF_7','#skF_8','#skF_9','#skF_10','#skF_11','#skF_12'),'#skF_6')
    | ~ m1_subset_1('#skF_9','#skF_6')
    | v1_xboole_0('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_10402,c_186])).

tff(c_10457,plain,
    ( r1_tarski(k4_enumset1('#skF_7','#skF_8','#skF_9','#skF_10','#skF_11','#skF_12'),'#skF_6')
    | v1_xboole_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_10432])).

tff(c_10459,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_116,c_347,c_10457])).

tff(c_10460,plain,(
    '#skF_3'(k4_enumset1('#skF_7','#skF_8','#skF_9','#skF_10','#skF_11','#skF_12'),'#skF_6') = '#skF_10' ),
    inference(splitRight,[status(thm)],[c_9922])).

tff(c_10491,plain,
    ( r1_tarski(k4_enumset1('#skF_7','#skF_8','#skF_9','#skF_10','#skF_11','#skF_12'),'#skF_6')
    | ~ m1_subset_1('#skF_10','#skF_6')
    | v1_xboole_0('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_10460,c_186])).

tff(c_10516,plain,
    ( r1_tarski(k4_enumset1('#skF_7','#skF_8','#skF_9','#skF_10','#skF_11','#skF_12'),'#skF_6')
    | v1_xboole_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_10491])).

tff(c_10518,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_116,c_347,c_10516])).

tff(c_10520,plain,(
    v1_xboole_0(k1_zfmisc_1('#skF_6')) ),
    inference(splitRight,[status(thm)],[c_125])).

tff(c_70,plain,(
    ! [A_23] :
      ( k1_xboole_0 = A_23
      | ~ v1_xboole_0(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_10524,plain,(
    k1_zfmisc_1('#skF_6') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_10520,c_70])).

tff(c_10525,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10524,c_10520])).

tff(c_10536,plain,(
    ! [C_1035,A_1036] :
      ( r2_hidden(C_1035,k1_zfmisc_1(A_1036))
      | ~ r1_tarski(C_1035,A_1036) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_72,plain,(
    ! [B_25,A_24] :
      ( ~ v1_xboole_0(B_25)
      | ~ r2_hidden(A_24,B_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_10544,plain,(
    ! [A_1037,C_1038] :
      ( ~ v1_xboole_0(k1_zfmisc_1(A_1037))
      | ~ r1_tarski(C_1038,A_1037) ) ),
    inference(resolution,[status(thm)],[c_10536,c_72])).

tff(c_10546,plain,(
    ! [C_1038] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | ~ r1_tarski(C_1038,'#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10524,c_10544])).

tff(c_10548,plain,(
    ! [C_1038] : ~ r1_tarski(C_1038,'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10525,c_10546])).

tff(c_10631,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_10626,c_10548])).

tff(c_10633,plain,(
    v1_xboole_0('#skF_6') ),
    inference(splitRight,[status(thm)],[c_110])).

tff(c_10640,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(resolution,[status(thm)],[c_10633,c_70])).

tff(c_10644,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_10640])).

%------------------------------------------------------------------------------
