%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:56:23 EST 2020

% Result     : Theorem 28.18s
% Output     : CNFRefutation 28.39s
% Verified   : 
% Statistics : Number of formulae       :  111 ( 322 expanded)
%              Number of leaves         :   53 ( 128 expanded)
%              Depth                    :   13
%              Number of atoms          :  146 ( 668 expanded)
%              Number of equality atoms :   26 ( 120 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_zfmisc_1 > k1_tarski > k1_subset_1 > k1_xboole_0 > #skF_9 > #skF_11 > #skF_6 > #skF_2 > #skF_3 > #skF_14 > #skF_13 > #skF_10 > #skF_8 > #skF_7 > #skF_1 > #skF_5 > #skF_12 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_9',type,(
    '#skF_9': $i > $i )).

tff('#skF_11',type,(
    '#skF_11': ( $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff('#skF_14',type,(
    '#skF_14': $i )).

tff('#skF_13',type,(
    '#skF_13': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_10',type,(
    '#skF_10': ( $i * $i ) > $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_subset_1,type,(
    k1_subset_1: $i > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': ( $i * $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff('#skF_12',type,(
    '#skF_12': $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_200,negated_conjecture,(
    ~ ! [A,B,C] :
        ( m1_subset_1(C,k1_zfmisc_1(A))
       => ( ( r1_tarski(B,C)
            & r1_tarski(B,k3_subset_1(A,C)) )
         => B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_subset_1)).

tff(f_166,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_113,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_50,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_185,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(A))
         => ( r1_tarski(B,C)
          <=> r1_tarski(k3_subset_1(A,C),k3_subset_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_subset_1)).

tff(f_168,axiom,(
    ! [A] : k1_subset_1(A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_subset_1)).

tff(f_191,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ( r1_tarski(B,k3_subset_1(A,B))
      <=> B = k1_subset_1(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_subset_1)).

tff(f_86,axiom,(
    ! [A,B] :
      ~ ( v1_xboole_0(A)
        & A != B
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_boole)).

tff(f_153,axiom,(
    ! [A] : k3_tarski(k1_zfmisc_1(A)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t99_zfmisc_1)).

tff(f_78,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_boole)).

tff(f_140,axiom,(
    k3_tarski(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_zfmisc_1)).

tff(f_52,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_147,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k4_xboole_0(B,k1_tarski(C)))
    <=> ( r2_hidden(A,B)
        & A != C ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_zfmisc_1)).

tff(c_132,plain,(
    m1_subset_1('#skF_14',k1_zfmisc_1('#skF_12')) ),
    inference(cnfTransformation,[status(thm)],[f_200])).

tff(c_218,plain,(
    ! [B_170,A_171] :
      ( v1_xboole_0(B_170)
      | ~ m1_subset_1(B_170,A_171)
      | ~ v1_xboole_0(A_171) ) ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_222,plain,
    ( v1_xboole_0('#skF_14')
    | ~ v1_xboole_0(k1_zfmisc_1('#skF_12')) ),
    inference(resolution,[status(thm)],[c_132,c_218])).

tff(c_223,plain,(
    ~ v1_xboole_0(k1_zfmisc_1('#skF_12')) ),
    inference(splitLeft,[status(thm)],[c_222])).

tff(c_130,plain,(
    r1_tarski('#skF_13','#skF_14') ),
    inference(cnfTransformation,[status(thm)],[f_200])).

tff(c_320,plain,(
    ! [B_190,A_191] :
      ( r2_hidden(B_190,A_191)
      | ~ m1_subset_1(B_190,A_191)
      | v1_xboole_0(A_191) ) ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_50,plain,(
    ! [C_61,A_57] :
      ( r1_tarski(C_61,A_57)
      | ~ r2_hidden(C_61,k1_zfmisc_1(A_57)) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_5077,plain,(
    ! [B_399,A_400] :
      ( r1_tarski(B_399,A_400)
      | ~ m1_subset_1(B_399,k1_zfmisc_1(A_400))
      | v1_xboole_0(k1_zfmisc_1(A_400)) ) ),
    inference(resolution,[status(thm)],[c_320,c_50])).

tff(c_5104,plain,
    ( r1_tarski('#skF_14','#skF_12')
    | v1_xboole_0(k1_zfmisc_1('#skF_12')) ),
    inference(resolution,[status(thm)],[c_132,c_5077])).

tff(c_5118,plain,(
    r1_tarski('#skF_14','#skF_12') ),
    inference(negUnitSimplification,[status(thm)],[c_223,c_5104])).

tff(c_14,plain,(
    ! [A_12,C_14,B_13] :
      ( r1_tarski(A_12,C_14)
      | ~ r1_tarski(B_13,C_14)
      | ~ r1_tarski(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_5146,plain,(
    ! [A_402] :
      ( r1_tarski(A_402,'#skF_12')
      | ~ r1_tarski(A_402,'#skF_14') ) ),
    inference(resolution,[status(thm)],[c_5118,c_14])).

tff(c_5224,plain,(
    r1_tarski('#skF_13','#skF_12') ),
    inference(resolution,[status(thm)],[c_130,c_5146])).

tff(c_52,plain,(
    ! [C_61,A_57] :
      ( r2_hidden(C_61,k1_zfmisc_1(A_57))
      | ~ r1_tarski(C_61,A_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_284,plain,(
    ! [B_184,A_185] :
      ( m1_subset_1(B_184,A_185)
      | ~ r2_hidden(B_184,A_185)
      | v1_xboole_0(A_185) ) ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_291,plain,(
    ! [C_61,A_57] :
      ( m1_subset_1(C_61,k1_zfmisc_1(A_57))
      | v1_xboole_0(k1_zfmisc_1(A_57))
      | ~ r1_tarski(C_61,A_57) ) ),
    inference(resolution,[status(thm)],[c_52,c_284])).

tff(c_126,plain,(
    k1_xboole_0 != '#skF_13' ),
    inference(cnfTransformation,[status(thm)],[f_200])).

tff(c_128,plain,(
    r1_tarski('#skF_13',k3_subset_1('#skF_12','#skF_14')) ),
    inference(cnfTransformation,[status(thm)],[f_200])).

tff(c_7373,plain,(
    ! [A_462,C_463,B_464] :
      ( r1_tarski(k3_subset_1(A_462,C_463),k3_subset_1(A_462,B_464))
      | ~ r1_tarski(B_464,C_463)
      | ~ m1_subset_1(C_463,k1_zfmisc_1(A_462))
      | ~ m1_subset_1(B_464,k1_zfmisc_1(A_462)) ) ),
    inference(cnfTransformation,[status(thm)],[f_185])).

tff(c_76254,plain,(
    ! [A_1337,A_1338,B_1339,C_1340] :
      ( r1_tarski(A_1337,k3_subset_1(A_1338,B_1339))
      | ~ r1_tarski(A_1337,k3_subset_1(A_1338,C_1340))
      | ~ r1_tarski(B_1339,C_1340)
      | ~ m1_subset_1(C_1340,k1_zfmisc_1(A_1338))
      | ~ m1_subset_1(B_1339,k1_zfmisc_1(A_1338)) ) ),
    inference(resolution,[status(thm)],[c_7373,c_14])).

tff(c_76575,plain,(
    ! [B_1339] :
      ( r1_tarski('#skF_13',k3_subset_1('#skF_12',B_1339))
      | ~ r1_tarski(B_1339,'#skF_14')
      | ~ m1_subset_1('#skF_14',k1_zfmisc_1('#skF_12'))
      | ~ m1_subset_1(B_1339,k1_zfmisc_1('#skF_12')) ) ),
    inference(resolution,[status(thm)],[c_128,c_76254])).

tff(c_76964,plain,(
    ! [B_1342] :
      ( r1_tarski('#skF_13',k3_subset_1('#skF_12',B_1342))
      | ~ r1_tarski(B_1342,'#skF_14')
      | ~ m1_subset_1(B_1342,k1_zfmisc_1('#skF_12')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_132,c_76575])).

tff(c_112,plain,(
    ! [A_143] : k1_subset_1(A_143) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_168])).

tff(c_124,plain,(
    ! [A_152,B_153] :
      ( k1_subset_1(A_152) = B_153
      | ~ r1_tarski(B_153,k3_subset_1(A_152,B_153))
      | ~ m1_subset_1(B_153,k1_zfmisc_1(A_152)) ) ),
    inference(cnfTransformation,[status(thm)],[f_191])).

tff(c_134,plain,(
    ! [B_153,A_152] :
      ( k1_xboole_0 = B_153
      | ~ r1_tarski(B_153,k3_subset_1(A_152,B_153))
      | ~ m1_subset_1(B_153,k1_zfmisc_1(A_152)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_112,c_124])).

tff(c_76978,plain,
    ( k1_xboole_0 = '#skF_13'
    | ~ r1_tarski('#skF_13','#skF_14')
    | ~ m1_subset_1('#skF_13',k1_zfmisc_1('#skF_12')) ),
    inference(resolution,[status(thm)],[c_76964,c_134])).

tff(c_77002,plain,
    ( k1_xboole_0 = '#skF_13'
    | ~ m1_subset_1('#skF_13',k1_zfmisc_1('#skF_12')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_130,c_76978])).

tff(c_77003,plain,(
    ~ m1_subset_1('#skF_13',k1_zfmisc_1('#skF_12')) ),
    inference(negUnitSimplification,[status(thm)],[c_126,c_77002])).

tff(c_77013,plain,
    ( v1_xboole_0(k1_zfmisc_1('#skF_12'))
    | ~ r1_tarski('#skF_13','#skF_12') ),
    inference(resolution,[status(thm)],[c_291,c_77003])).

tff(c_77019,plain,(
    v1_xboole_0(k1_zfmisc_1('#skF_12')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5224,c_77013])).

tff(c_77021,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_223,c_77019])).

tff(c_77023,plain,(
    v1_xboole_0(k1_zfmisc_1('#skF_12')) ),
    inference(splitRight,[status(thm)],[c_222])).

tff(c_77022,plain,(
    v1_xboole_0('#skF_14') ),
    inference(splitRight,[status(thm)],[c_222])).

tff(c_28,plain,(
    ! [B_22,A_21] :
      ( ~ v1_xboole_0(B_22)
      | B_22 = A_21
      | ~ v1_xboole_0(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_77071,plain,(
    ! [A_1346] :
      ( A_1346 = '#skF_14'
      | ~ v1_xboole_0(A_1346) ) ),
    inference(resolution,[status(thm)],[c_77022,c_28])).

tff(c_77078,plain,(
    k1_zfmisc_1('#skF_12') = '#skF_14' ),
    inference(resolution,[status(thm)],[c_77023,c_77071])).

tff(c_102,plain,(
    ! [A_140] : k3_tarski(k1_zfmisc_1(A_140)) = A_140 ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_77088,plain,(
    k3_tarski('#skF_14') = '#skF_12' ),
    inference(superposition,[status(thm),theory(equality)],[c_77078,c_102])).

tff(c_26,plain,(
    ! [A_20] :
      ( k1_xboole_0 = A_20
      | ~ v1_xboole_0(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_77030,plain,(
    k1_xboole_0 = '#skF_14' ),
    inference(resolution,[status(thm)],[c_77022,c_26])).

tff(c_92,plain,(
    k3_tarski(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_77038,plain,(
    k3_tarski('#skF_14') = '#skF_14' ),
    inference(demodulation,[status(thm),theory(equality)],[c_77030,c_77030,c_92])).

tff(c_77098,plain,(
    '#skF_14' = '#skF_12' ),
    inference(demodulation,[status(thm),theory(equality)],[c_77088,c_77038])).

tff(c_77117,plain,(
    r1_tarski('#skF_13','#skF_12') ),
    inference(demodulation,[status(thm),theory(equality)],[c_77098,c_130])).

tff(c_16,plain,(
    ! [A_15] : r1_tarski(k1_xboole_0,A_15) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_77036,plain,(
    ! [A_15] : r1_tarski('#skF_14',A_15) ),
    inference(demodulation,[status(thm),theory(equality)],[c_77030,c_16])).

tff(c_77109,plain,(
    ! [A_15] : r1_tarski('#skF_12',A_15) ),
    inference(demodulation,[status(thm),theory(equality)],[c_77098,c_77036])).

tff(c_77619,plain,(
    ! [A_1405,C_1406,B_1407] :
      ( r1_tarski(A_1405,C_1406)
      | ~ r1_tarski(B_1407,C_1406)
      | ~ r1_tarski(A_1405,B_1407) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_77668,plain,(
    ! [A_1411,A_1412] :
      ( r1_tarski(A_1411,A_1412)
      | ~ r1_tarski(A_1411,'#skF_12') ) ),
    inference(resolution,[status(thm)],[c_77109,c_77619])).

tff(c_77693,plain,(
    ! [A_1412] : r1_tarski('#skF_13',A_1412) ),
    inference(resolution,[status(thm)],[c_77117,c_77668])).

tff(c_77108,plain,(
    k1_zfmisc_1('#skF_12') = '#skF_12' ),
    inference(demodulation,[status(thm),theory(equality)],[c_77098,c_77078])).

tff(c_77170,plain,(
    ! [C_61] :
      ( r2_hidden(C_61,'#skF_12')
      | ~ r1_tarski(C_61,'#skF_12') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_77108,c_52])).

tff(c_77644,plain,(
    ! [C_1408,B_1409,A_1410] :
      ( r2_hidden(C_1408,B_1409)
      | ~ r2_hidden(C_1408,A_1410)
      | ~ r1_tarski(A_1410,B_1409) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_77654,plain,(
    ! [C_61,B_1409] :
      ( r2_hidden(C_61,B_1409)
      | ~ r1_tarski('#skF_12',B_1409)
      | ~ r1_tarski(C_61,'#skF_12') ) ),
    inference(resolution,[status(thm)],[c_77170,c_77644])).

tff(c_77744,plain,(
    ! [C_1416,B_1417] :
      ( r2_hidden(C_1416,B_1417)
      | ~ r1_tarski(C_1416,'#skF_12') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_77109,c_77654])).

tff(c_96,plain,(
    ! [C_137,B_136] : ~ r2_hidden(C_137,k4_xboole_0(B_136,k1_tarski(C_137))) ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_77805,plain,(
    ! [C_1418] : ~ r1_tarski(C_1418,'#skF_12') ),
    inference(resolution,[status(thm)],[c_77744,c_96])).

tff(c_77824,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_77693,c_77805])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.00/0.11  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.31  % Computer   : n003.cluster.edu
% 0.12/0.31  % Model      : x86_64 x86_64
% 0.12/0.31  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.31  % Memory     : 8042.1875MB
% 0.12/0.31  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.31  % CPULimit   : 60
% 0.12/0.31  % DateTime   : Tue Dec  1 19:05:12 EST 2020
% 0.12/0.32  % CPUTime    : 
% 0.12/0.32  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 28.18/19.47  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 28.18/19.48  
% 28.18/19.48  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 28.31/19.48  %$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_zfmisc_1 > k1_tarski > k1_subset_1 > k1_xboole_0 > #skF_9 > #skF_11 > #skF_6 > #skF_2 > #skF_3 > #skF_14 > #skF_13 > #skF_10 > #skF_8 > #skF_7 > #skF_1 > #skF_5 > #skF_12 > #skF_4
% 28.31/19.48  
% 28.31/19.48  %Foreground sorts:
% 28.31/19.48  
% 28.31/19.48  
% 28.31/19.48  %Background operators:
% 28.31/19.48  
% 28.31/19.48  
% 28.31/19.48  %Foreground operators:
% 28.31/19.48  tff('#skF_9', type, '#skF_9': $i > $i).
% 28.31/19.48  tff('#skF_11', type, '#skF_11': ($i * $i) > $i).
% 28.31/19.48  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 28.31/19.48  tff('#skF_2', type, '#skF_2': $i > $i).
% 28.31/19.48  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 28.31/19.48  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 28.31/19.48  tff(k1_tarski, type, k1_tarski: $i > $i).
% 28.31/19.48  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 28.31/19.48  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 28.31/19.48  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 28.31/19.48  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 28.31/19.48  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 28.31/19.48  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 28.31/19.48  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 28.31/19.48  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 28.31/19.48  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 28.31/19.48  tff('#skF_14', type, '#skF_14': $i).
% 28.31/19.48  tff('#skF_13', type, '#skF_13': $i).
% 28.31/19.48  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 28.31/19.48  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 28.31/19.48  tff('#skF_10', type, '#skF_10': ($i * $i) > $i).
% 28.31/19.48  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 28.31/19.48  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 28.31/19.48  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 28.31/19.48  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 28.31/19.48  tff(k3_tarski, type, k3_tarski: $i > $i).
% 28.31/19.48  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 28.31/19.48  tff(k1_subset_1, type, k1_subset_1: $i > $i).
% 28.31/19.48  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 28.31/19.48  tff('#skF_8', type, '#skF_8': ($i * $i * $i) > $i).
% 28.31/19.48  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 28.31/19.48  tff('#skF_7', type, '#skF_7': ($i * $i) > $i).
% 28.31/19.48  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 28.31/19.48  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 28.31/19.48  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 28.31/19.48  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 28.31/19.48  tff('#skF_12', type, '#skF_12': $i).
% 28.31/19.48  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 28.31/19.48  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 28.31/19.48  
% 28.39/19.50  tff(f_200, negated_conjecture, ~(![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => ((r1_tarski(B, C) & r1_tarski(B, k3_subset_1(A, C))) => (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t40_subset_1)).
% 28.39/19.50  tff(f_166, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 28.39/19.50  tff(f_113, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 28.39/19.50  tff(f_50, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 28.39/19.50  tff(f_185, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (r1_tarski(B, C) <=> r1_tarski(k3_subset_1(A, C), k3_subset_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_subset_1)).
% 28.39/19.50  tff(f_168, axiom, (![A]: (k1_subset_1(A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_subset_1)).
% 28.39/19.50  tff(f_191, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (r1_tarski(B, k3_subset_1(A, B)) <=> (B = k1_subset_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_subset_1)).
% 28.39/19.50  tff(f_86, axiom, (![A, B]: ~((v1_xboole_0(A) & ~(A = B)) & v1_xboole_0(B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_boole)).
% 28.39/19.50  tff(f_153, axiom, (![A]: (k3_tarski(k1_zfmisc_1(A)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t99_zfmisc_1)).
% 28.39/19.50  tff(f_78, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_boole)).
% 28.39/19.50  tff(f_140, axiom, (k3_tarski(k1_xboole_0) = k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_zfmisc_1)).
% 28.39/19.50  tff(f_52, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 28.39/19.50  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 28.39/19.50  tff(f_147, axiom, (![A, B, C]: (r2_hidden(A, k4_xboole_0(B, k1_tarski(C))) <=> (r2_hidden(A, B) & ~(A = C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_zfmisc_1)).
% 28.39/19.50  tff(c_132, plain, (m1_subset_1('#skF_14', k1_zfmisc_1('#skF_12'))), inference(cnfTransformation, [status(thm)], [f_200])).
% 28.39/19.50  tff(c_218, plain, (![B_170, A_171]: (v1_xboole_0(B_170) | ~m1_subset_1(B_170, A_171) | ~v1_xboole_0(A_171))), inference(cnfTransformation, [status(thm)], [f_166])).
% 28.39/19.50  tff(c_222, plain, (v1_xboole_0('#skF_14') | ~v1_xboole_0(k1_zfmisc_1('#skF_12'))), inference(resolution, [status(thm)], [c_132, c_218])).
% 28.39/19.50  tff(c_223, plain, (~v1_xboole_0(k1_zfmisc_1('#skF_12'))), inference(splitLeft, [status(thm)], [c_222])).
% 28.39/19.50  tff(c_130, plain, (r1_tarski('#skF_13', '#skF_14')), inference(cnfTransformation, [status(thm)], [f_200])).
% 28.39/19.50  tff(c_320, plain, (![B_190, A_191]: (r2_hidden(B_190, A_191) | ~m1_subset_1(B_190, A_191) | v1_xboole_0(A_191))), inference(cnfTransformation, [status(thm)], [f_166])).
% 28.39/19.50  tff(c_50, plain, (![C_61, A_57]: (r1_tarski(C_61, A_57) | ~r2_hidden(C_61, k1_zfmisc_1(A_57)))), inference(cnfTransformation, [status(thm)], [f_113])).
% 28.39/19.50  tff(c_5077, plain, (![B_399, A_400]: (r1_tarski(B_399, A_400) | ~m1_subset_1(B_399, k1_zfmisc_1(A_400)) | v1_xboole_0(k1_zfmisc_1(A_400)))), inference(resolution, [status(thm)], [c_320, c_50])).
% 28.39/19.50  tff(c_5104, plain, (r1_tarski('#skF_14', '#skF_12') | v1_xboole_0(k1_zfmisc_1('#skF_12'))), inference(resolution, [status(thm)], [c_132, c_5077])).
% 28.39/19.50  tff(c_5118, plain, (r1_tarski('#skF_14', '#skF_12')), inference(negUnitSimplification, [status(thm)], [c_223, c_5104])).
% 28.39/19.50  tff(c_14, plain, (![A_12, C_14, B_13]: (r1_tarski(A_12, C_14) | ~r1_tarski(B_13, C_14) | ~r1_tarski(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_50])).
% 28.39/19.50  tff(c_5146, plain, (![A_402]: (r1_tarski(A_402, '#skF_12') | ~r1_tarski(A_402, '#skF_14'))), inference(resolution, [status(thm)], [c_5118, c_14])).
% 28.39/19.50  tff(c_5224, plain, (r1_tarski('#skF_13', '#skF_12')), inference(resolution, [status(thm)], [c_130, c_5146])).
% 28.39/19.50  tff(c_52, plain, (![C_61, A_57]: (r2_hidden(C_61, k1_zfmisc_1(A_57)) | ~r1_tarski(C_61, A_57))), inference(cnfTransformation, [status(thm)], [f_113])).
% 28.39/19.50  tff(c_284, plain, (![B_184, A_185]: (m1_subset_1(B_184, A_185) | ~r2_hidden(B_184, A_185) | v1_xboole_0(A_185))), inference(cnfTransformation, [status(thm)], [f_166])).
% 28.39/19.50  tff(c_291, plain, (![C_61, A_57]: (m1_subset_1(C_61, k1_zfmisc_1(A_57)) | v1_xboole_0(k1_zfmisc_1(A_57)) | ~r1_tarski(C_61, A_57))), inference(resolution, [status(thm)], [c_52, c_284])).
% 28.39/19.50  tff(c_126, plain, (k1_xboole_0!='#skF_13'), inference(cnfTransformation, [status(thm)], [f_200])).
% 28.39/19.50  tff(c_128, plain, (r1_tarski('#skF_13', k3_subset_1('#skF_12', '#skF_14'))), inference(cnfTransformation, [status(thm)], [f_200])).
% 28.39/19.50  tff(c_7373, plain, (![A_462, C_463, B_464]: (r1_tarski(k3_subset_1(A_462, C_463), k3_subset_1(A_462, B_464)) | ~r1_tarski(B_464, C_463) | ~m1_subset_1(C_463, k1_zfmisc_1(A_462)) | ~m1_subset_1(B_464, k1_zfmisc_1(A_462)))), inference(cnfTransformation, [status(thm)], [f_185])).
% 28.39/19.50  tff(c_76254, plain, (![A_1337, A_1338, B_1339, C_1340]: (r1_tarski(A_1337, k3_subset_1(A_1338, B_1339)) | ~r1_tarski(A_1337, k3_subset_1(A_1338, C_1340)) | ~r1_tarski(B_1339, C_1340) | ~m1_subset_1(C_1340, k1_zfmisc_1(A_1338)) | ~m1_subset_1(B_1339, k1_zfmisc_1(A_1338)))), inference(resolution, [status(thm)], [c_7373, c_14])).
% 28.39/19.50  tff(c_76575, plain, (![B_1339]: (r1_tarski('#skF_13', k3_subset_1('#skF_12', B_1339)) | ~r1_tarski(B_1339, '#skF_14') | ~m1_subset_1('#skF_14', k1_zfmisc_1('#skF_12')) | ~m1_subset_1(B_1339, k1_zfmisc_1('#skF_12')))), inference(resolution, [status(thm)], [c_128, c_76254])).
% 28.39/19.50  tff(c_76964, plain, (![B_1342]: (r1_tarski('#skF_13', k3_subset_1('#skF_12', B_1342)) | ~r1_tarski(B_1342, '#skF_14') | ~m1_subset_1(B_1342, k1_zfmisc_1('#skF_12')))), inference(demodulation, [status(thm), theory('equality')], [c_132, c_76575])).
% 28.39/19.50  tff(c_112, plain, (![A_143]: (k1_subset_1(A_143)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_168])).
% 28.39/19.50  tff(c_124, plain, (![A_152, B_153]: (k1_subset_1(A_152)=B_153 | ~r1_tarski(B_153, k3_subset_1(A_152, B_153)) | ~m1_subset_1(B_153, k1_zfmisc_1(A_152)))), inference(cnfTransformation, [status(thm)], [f_191])).
% 28.39/19.50  tff(c_134, plain, (![B_153, A_152]: (k1_xboole_0=B_153 | ~r1_tarski(B_153, k3_subset_1(A_152, B_153)) | ~m1_subset_1(B_153, k1_zfmisc_1(A_152)))), inference(demodulation, [status(thm), theory('equality')], [c_112, c_124])).
% 28.39/19.50  tff(c_76978, plain, (k1_xboole_0='#skF_13' | ~r1_tarski('#skF_13', '#skF_14') | ~m1_subset_1('#skF_13', k1_zfmisc_1('#skF_12'))), inference(resolution, [status(thm)], [c_76964, c_134])).
% 28.39/19.50  tff(c_77002, plain, (k1_xboole_0='#skF_13' | ~m1_subset_1('#skF_13', k1_zfmisc_1('#skF_12'))), inference(demodulation, [status(thm), theory('equality')], [c_130, c_76978])).
% 28.39/19.50  tff(c_77003, plain, (~m1_subset_1('#skF_13', k1_zfmisc_1('#skF_12'))), inference(negUnitSimplification, [status(thm)], [c_126, c_77002])).
% 28.39/19.50  tff(c_77013, plain, (v1_xboole_0(k1_zfmisc_1('#skF_12')) | ~r1_tarski('#skF_13', '#skF_12')), inference(resolution, [status(thm)], [c_291, c_77003])).
% 28.39/19.50  tff(c_77019, plain, (v1_xboole_0(k1_zfmisc_1('#skF_12'))), inference(demodulation, [status(thm), theory('equality')], [c_5224, c_77013])).
% 28.39/19.50  tff(c_77021, plain, $false, inference(negUnitSimplification, [status(thm)], [c_223, c_77019])).
% 28.39/19.50  tff(c_77023, plain, (v1_xboole_0(k1_zfmisc_1('#skF_12'))), inference(splitRight, [status(thm)], [c_222])).
% 28.39/19.50  tff(c_77022, plain, (v1_xboole_0('#skF_14')), inference(splitRight, [status(thm)], [c_222])).
% 28.39/19.50  tff(c_28, plain, (![B_22, A_21]: (~v1_xboole_0(B_22) | B_22=A_21 | ~v1_xboole_0(A_21))), inference(cnfTransformation, [status(thm)], [f_86])).
% 28.39/19.50  tff(c_77071, plain, (![A_1346]: (A_1346='#skF_14' | ~v1_xboole_0(A_1346))), inference(resolution, [status(thm)], [c_77022, c_28])).
% 28.39/19.50  tff(c_77078, plain, (k1_zfmisc_1('#skF_12')='#skF_14'), inference(resolution, [status(thm)], [c_77023, c_77071])).
% 28.39/19.50  tff(c_102, plain, (![A_140]: (k3_tarski(k1_zfmisc_1(A_140))=A_140)), inference(cnfTransformation, [status(thm)], [f_153])).
% 28.39/19.50  tff(c_77088, plain, (k3_tarski('#skF_14')='#skF_12'), inference(superposition, [status(thm), theory('equality')], [c_77078, c_102])).
% 28.39/19.50  tff(c_26, plain, (![A_20]: (k1_xboole_0=A_20 | ~v1_xboole_0(A_20))), inference(cnfTransformation, [status(thm)], [f_78])).
% 28.39/19.50  tff(c_77030, plain, (k1_xboole_0='#skF_14'), inference(resolution, [status(thm)], [c_77022, c_26])).
% 28.39/19.50  tff(c_92, plain, (k3_tarski(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_140])).
% 28.39/19.50  tff(c_77038, plain, (k3_tarski('#skF_14')='#skF_14'), inference(demodulation, [status(thm), theory('equality')], [c_77030, c_77030, c_92])).
% 28.39/19.50  tff(c_77098, plain, ('#skF_14'='#skF_12'), inference(demodulation, [status(thm), theory('equality')], [c_77088, c_77038])).
% 28.39/19.50  tff(c_77117, plain, (r1_tarski('#skF_13', '#skF_12')), inference(demodulation, [status(thm), theory('equality')], [c_77098, c_130])).
% 28.39/19.50  tff(c_16, plain, (![A_15]: (r1_tarski(k1_xboole_0, A_15))), inference(cnfTransformation, [status(thm)], [f_52])).
% 28.39/19.50  tff(c_77036, plain, (![A_15]: (r1_tarski('#skF_14', A_15))), inference(demodulation, [status(thm), theory('equality')], [c_77030, c_16])).
% 28.39/19.50  tff(c_77109, plain, (![A_15]: (r1_tarski('#skF_12', A_15))), inference(demodulation, [status(thm), theory('equality')], [c_77098, c_77036])).
% 28.39/19.50  tff(c_77619, plain, (![A_1405, C_1406, B_1407]: (r1_tarski(A_1405, C_1406) | ~r1_tarski(B_1407, C_1406) | ~r1_tarski(A_1405, B_1407))), inference(cnfTransformation, [status(thm)], [f_50])).
% 28.39/19.50  tff(c_77668, plain, (![A_1411, A_1412]: (r1_tarski(A_1411, A_1412) | ~r1_tarski(A_1411, '#skF_12'))), inference(resolution, [status(thm)], [c_77109, c_77619])).
% 28.39/19.50  tff(c_77693, plain, (![A_1412]: (r1_tarski('#skF_13', A_1412))), inference(resolution, [status(thm)], [c_77117, c_77668])).
% 28.39/19.50  tff(c_77108, plain, (k1_zfmisc_1('#skF_12')='#skF_12'), inference(demodulation, [status(thm), theory('equality')], [c_77098, c_77078])).
% 28.39/19.50  tff(c_77170, plain, (![C_61]: (r2_hidden(C_61, '#skF_12') | ~r1_tarski(C_61, '#skF_12'))), inference(superposition, [status(thm), theory('equality')], [c_77108, c_52])).
% 28.39/19.50  tff(c_77644, plain, (![C_1408, B_1409, A_1410]: (r2_hidden(C_1408, B_1409) | ~r2_hidden(C_1408, A_1410) | ~r1_tarski(A_1410, B_1409))), inference(cnfTransformation, [status(thm)], [f_32])).
% 28.39/19.50  tff(c_77654, plain, (![C_61, B_1409]: (r2_hidden(C_61, B_1409) | ~r1_tarski('#skF_12', B_1409) | ~r1_tarski(C_61, '#skF_12'))), inference(resolution, [status(thm)], [c_77170, c_77644])).
% 28.39/19.50  tff(c_77744, plain, (![C_1416, B_1417]: (r2_hidden(C_1416, B_1417) | ~r1_tarski(C_1416, '#skF_12'))), inference(demodulation, [status(thm), theory('equality')], [c_77109, c_77654])).
% 28.39/19.50  tff(c_96, plain, (![C_137, B_136]: (~r2_hidden(C_137, k4_xboole_0(B_136, k1_tarski(C_137))))), inference(cnfTransformation, [status(thm)], [f_147])).
% 28.39/19.50  tff(c_77805, plain, (![C_1418]: (~r1_tarski(C_1418, '#skF_12'))), inference(resolution, [status(thm)], [c_77744, c_96])).
% 28.39/19.50  tff(c_77824, plain, $false, inference(resolution, [status(thm)], [c_77693, c_77805])).
% 28.39/19.50  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 28.39/19.50  
% 28.39/19.50  Inference rules
% 28.39/19.50  ----------------------
% 28.39/19.50  #Ref     : 0
% 28.39/19.50  #Sup     : 18044
% 28.39/19.50  #Fact    : 0
% 28.39/19.50  #Define  : 0
% 28.39/19.50  #Split   : 90
% 28.39/19.50  #Chain   : 0
% 28.39/19.50  #Close   : 0
% 28.39/19.50  
% 28.39/19.50  Ordering : KBO
% 28.39/19.50  
% 28.39/19.50  Simplification rules
% 28.39/19.50  ----------------------
% 28.39/19.50  #Subsume      : 4255
% 28.39/19.50  #Demod        : 8501
% 28.39/19.50  #Tautology    : 3873
% 28.39/19.50  #SimpNegUnit  : 695
% 28.39/19.50  #BackRed      : 470
% 28.39/19.50  
% 28.39/19.50  #Partial instantiations: 0
% 28.39/19.50  #Strategies tried      : 1
% 28.39/19.50  
% 28.39/19.50  Timing (in seconds)
% 28.39/19.50  ----------------------
% 28.39/19.50  Preprocessing        : 0.39
% 28.39/19.50  Parsing              : 0.20
% 28.39/19.50  CNF conversion       : 0.03
% 28.39/19.50  Main loop            : 18.36
% 28.39/19.50  Inferencing          : 2.36
% 28.39/19.50  Reduction            : 8.51
% 28.39/19.50  Demodulation         : 6.78
% 28.39/19.50  BG Simplification    : 0.22
% 28.39/19.50  Subsumption          : 6.02
% 28.39/19.50  Abstraction          : 0.30
% 28.39/19.50  MUC search           : 0.00
% 28.39/19.50  Cooper               : 0.00
% 28.39/19.50  Total                : 18.79
% 28.39/19.50  Index Insertion      : 0.00
% 28.39/19.50  Index Deletion       : 0.00
% 28.39/19.50  Index Matching       : 0.00
% 28.39/19.50  BG Taut test         : 0.00
%------------------------------------------------------------------------------
