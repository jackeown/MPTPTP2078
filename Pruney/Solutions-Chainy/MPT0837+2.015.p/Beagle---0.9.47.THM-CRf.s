%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:08:07 EST 2020

% Result     : Theorem 4.33s
% Output     : CNFRefutation 4.33s
% Verified   : 
% Statistics : Number of formulae       :   98 ( 220 expanded)
%              Number of leaves         :   39 (  92 expanded)
%              Depth                    :   10
%              Number of atoms          :  160 ( 495 expanded)
%              Number of equality atoms :    8 (  31 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k2_relset_1 > k9_relat_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_11 > #skF_4 > #skF_7 > #skF_3 > #skF_10 > #skF_6 > #skF_5 > #skF_9 > #skF_8 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_11',type,(
    '#skF_11': $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_58,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_102,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B] :
            ( ~ v1_xboole_0(B)
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(B,A)))
               => ! [D] :
                    ( r2_hidden(D,k2_relset_1(B,A,C))
                  <=> ? [E] :
                        ( m1_subset_1(E,B)
                        & r2_hidden(k4_tarski(E,D),C) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_relset_1)).

tff(f_42,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_79,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_83,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_73,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k9_relat_1(A,k1_relat_1(A)) = k2_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_relat_1)).

tff(f_48,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_69,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k9_relat_1(C,B))
      <=> ? [D] :
            ( r2_hidden(D,k1_relat_1(C))
            & r2_hidden(k4_tarski(D,A),C)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t143_relat_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

tff(f_56,axiom,(
    ! [A,B] :
      ( B = k2_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(D,C),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_relat_1)).

tff(c_26,plain,(
    ! [A_30,B_31] : v1_relat_1(k2_zfmisc_1(A_30,B_31)) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_44,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_7','#skF_6'))) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_81,plain,(
    ! [B_94,A_95] :
      ( v1_relat_1(B_94)
      | ~ m1_subset_1(B_94,k1_zfmisc_1(A_95))
      | ~ v1_relat_1(A_95) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_87,plain,
    ( v1_relat_1('#skF_8')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_7','#skF_6')) ),
    inference(resolution,[status(thm)],[c_44,c_81])).

tff(c_91,plain,(
    v1_relat_1('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_87])).

tff(c_133,plain,(
    ! [C_111,A_112,B_113] :
      ( v4_relat_1(C_111,A_112)
      | ~ m1_subset_1(C_111,k1_zfmisc_1(k2_zfmisc_1(A_112,B_113))) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_142,plain,(
    v4_relat_1('#skF_8','#skF_7') ),
    inference(resolution,[status(thm)],[c_44,c_133])).

tff(c_726,plain,(
    ! [A_236,B_237,C_238] :
      ( k2_relset_1(A_236,B_237,C_238) = k2_relat_1(C_238)
      | ~ m1_subset_1(C_238,k1_zfmisc_1(k2_zfmisc_1(A_236,B_237))) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_735,plain,(
    k2_relset_1('#skF_7','#skF_6','#skF_8') = k2_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_44,c_726])).

tff(c_60,plain,
    ( m1_subset_1('#skF_10','#skF_7')
    | r2_hidden('#skF_11',k2_relset_1('#skF_7','#skF_6','#skF_8')) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_92,plain,(
    r2_hidden('#skF_11',k2_relset_1('#skF_7','#skF_6','#skF_8')) ),
    inference(splitLeft,[status(thm)],[c_60])).

tff(c_737,plain,(
    r2_hidden('#skF_11',k2_relat_1('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_735,c_92])).

tff(c_36,plain,(
    ! [A_38] :
      ( k9_relat_1(A_38,k1_relat_1(A_38)) = k2_relat_1(A_38)
      | ~ v1_relat_1(A_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_12,plain,(
    ! [B_10,A_9] :
      ( r1_tarski(k1_relat_1(B_10),A_9)
      | ~ v4_relat_1(B_10,A_9)
      | ~ v1_relat_1(B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_1395,plain,(
    ! [A_357,B_358,C_359] :
      ( r2_hidden('#skF_5'(A_357,B_358,C_359),k1_relat_1(C_359))
      | ~ r2_hidden(A_357,k9_relat_1(C_359,B_358))
      | ~ v1_relat_1(C_359) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( m1_subset_1(A_1,k1_zfmisc_1(B_2))
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_154,plain,(
    ! [A_117,C_118,B_119] :
      ( m1_subset_1(A_117,C_118)
      | ~ m1_subset_1(B_119,k1_zfmisc_1(C_118))
      | ~ r2_hidden(A_117,B_119) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_159,plain,(
    ! [A_117,B_2,A_1] :
      ( m1_subset_1(A_117,B_2)
      | ~ r2_hidden(A_117,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(resolution,[status(thm)],[c_4,c_154])).

tff(c_1545,plain,(
    ! [A_389,B_390,C_391,B_392] :
      ( m1_subset_1('#skF_5'(A_389,B_390,C_391),B_392)
      | ~ r1_tarski(k1_relat_1(C_391),B_392)
      | ~ r2_hidden(A_389,k9_relat_1(C_391,B_390))
      | ~ v1_relat_1(C_391) ) ),
    inference(resolution,[status(thm)],[c_1395,c_159])).

tff(c_1549,plain,(
    ! [A_393,B_394,B_395,A_396] :
      ( m1_subset_1('#skF_5'(A_393,B_394,B_395),A_396)
      | ~ r2_hidden(A_393,k9_relat_1(B_395,B_394))
      | ~ v4_relat_1(B_395,A_396)
      | ~ v1_relat_1(B_395) ) ),
    inference(resolution,[status(thm)],[c_12,c_1545])).

tff(c_1934,plain,(
    ! [A_436,A_437,A_438] :
      ( m1_subset_1('#skF_5'(A_436,k1_relat_1(A_437),A_437),A_438)
      | ~ r2_hidden(A_436,k2_relat_1(A_437))
      | ~ v4_relat_1(A_437,A_438)
      | ~ v1_relat_1(A_437)
      | ~ v1_relat_1(A_437) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_1549])).

tff(c_1399,plain,(
    ! [A_360,B_361,C_362] :
      ( r2_hidden(k4_tarski('#skF_5'(A_360,B_361,C_362),A_360),C_362)
      | ~ r2_hidden(A_360,k9_relat_1(C_362,B_361))
      | ~ v1_relat_1(C_362) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_50,plain,(
    ! [E_86] :
      ( ~ r2_hidden('#skF_9',k2_relset_1('#skF_7','#skF_6','#skF_8'))
      | ~ r2_hidden(k4_tarski(E_86,'#skF_11'),'#skF_8')
      | ~ m1_subset_1(E_86,'#skF_7') ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_1266,plain,(
    ! [E_86] :
      ( ~ r2_hidden('#skF_9',k2_relat_1('#skF_8'))
      | ~ r2_hidden(k4_tarski(E_86,'#skF_11'),'#skF_8')
      | ~ m1_subset_1(E_86,'#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_735,c_50])).

tff(c_1267,plain,(
    ~ r2_hidden('#skF_9',k2_relat_1('#skF_8')) ),
    inference(splitLeft,[status(thm)],[c_1266])).

tff(c_784,plain,(
    ! [A_254,B_255,C_256] :
      ( r2_hidden('#skF_5'(A_254,B_255,C_256),k1_relat_1(C_256))
      | ~ r2_hidden(A_254,k9_relat_1(C_256,B_255))
      | ~ v1_relat_1(C_256) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_996,plain,(
    ! [A_294,B_295,C_296,B_297] :
      ( m1_subset_1('#skF_5'(A_294,B_295,C_296),B_297)
      | ~ r1_tarski(k1_relat_1(C_296),B_297)
      | ~ r2_hidden(A_294,k9_relat_1(C_296,B_295))
      | ~ v1_relat_1(C_296) ) ),
    inference(resolution,[status(thm)],[c_784,c_159])).

tff(c_1009,plain,(
    ! [A_301,B_302,B_303,A_304] :
      ( m1_subset_1('#skF_5'(A_301,B_302,B_303),A_304)
      | ~ r2_hidden(A_301,k9_relat_1(B_303,B_302))
      | ~ v4_relat_1(B_303,A_304)
      | ~ v1_relat_1(B_303) ) ),
    inference(resolution,[status(thm)],[c_12,c_996])).

tff(c_1234,plain,(
    ! [A_330,A_331,A_332] :
      ( m1_subset_1('#skF_5'(A_330,k1_relat_1(A_331),A_331),A_332)
      | ~ r2_hidden(A_330,k2_relat_1(A_331))
      | ~ v4_relat_1(A_331,A_332)
      | ~ v1_relat_1(A_331)
      | ~ v1_relat_1(A_331) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_1009])).

tff(c_788,plain,(
    ! [A_257,B_258,C_259] :
      ( r2_hidden(k4_tarski('#skF_5'(A_257,B_258,C_259),A_257),C_259)
      | ~ r2_hidden(A_257,k9_relat_1(C_259,B_258))
      | ~ v1_relat_1(C_259) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_52,plain,(
    ! [E_86] :
      ( r2_hidden(k4_tarski('#skF_10','#skF_9'),'#skF_8')
      | ~ r2_hidden(k4_tarski(E_86,'#skF_11'),'#skF_8')
      | ~ m1_subset_1(E_86,'#skF_7') ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_746,plain,(
    ! [E_86] :
      ( ~ r2_hidden(k4_tarski(E_86,'#skF_11'),'#skF_8')
      | ~ m1_subset_1(E_86,'#skF_7') ) ),
    inference(splitLeft,[status(thm)],[c_52])).

tff(c_792,plain,(
    ! [B_258] :
      ( ~ m1_subset_1('#skF_5'('#skF_11',B_258,'#skF_8'),'#skF_7')
      | ~ r2_hidden('#skF_11',k9_relat_1('#skF_8',B_258))
      | ~ v1_relat_1('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_788,c_746])).

tff(c_827,plain,(
    ! [B_263] :
      ( ~ m1_subset_1('#skF_5'('#skF_11',B_263,'#skF_8'),'#skF_7')
      | ~ r2_hidden('#skF_11',k9_relat_1('#skF_8',B_263)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_91,c_792])).

tff(c_831,plain,
    ( ~ m1_subset_1('#skF_5'('#skF_11',k1_relat_1('#skF_8'),'#skF_8'),'#skF_7')
    | ~ r2_hidden('#skF_11',k2_relat_1('#skF_8'))
    | ~ v1_relat_1('#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_827])).

tff(c_833,plain,(
    ~ m1_subset_1('#skF_5'('#skF_11',k1_relat_1('#skF_8'),'#skF_8'),'#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_91,c_737,c_831])).

tff(c_1237,plain,
    ( ~ r2_hidden('#skF_11',k2_relat_1('#skF_8'))
    | ~ v4_relat_1('#skF_8','#skF_7')
    | ~ v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_1234,c_833])).

tff(c_1264,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_91,c_142,c_737,c_1237])).

tff(c_1265,plain,(
    r2_hidden(k4_tarski('#skF_10','#skF_9'),'#skF_8') ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_16,plain,(
    ! [C_26,A_11,D_29] :
      ( r2_hidden(C_26,k2_relat_1(A_11))
      | ~ r2_hidden(k4_tarski(D_29,C_26),A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_1272,plain,(
    r2_hidden('#skF_9',k2_relat_1('#skF_8')) ),
    inference(resolution,[status(thm)],[c_1265,c_16])).

tff(c_1277,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1267,c_1272])).

tff(c_1278,plain,(
    ! [E_86] :
      ( ~ r2_hidden(k4_tarski(E_86,'#skF_11'),'#skF_8')
      | ~ m1_subset_1(E_86,'#skF_7') ) ),
    inference(splitRight,[status(thm)],[c_1266])).

tff(c_1406,plain,(
    ! [B_361] :
      ( ~ m1_subset_1('#skF_5'('#skF_11',B_361,'#skF_8'),'#skF_7')
      | ~ r2_hidden('#skF_11',k9_relat_1('#skF_8',B_361))
      | ~ v1_relat_1('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_1399,c_1278])).

tff(c_1443,plain,(
    ! [B_369] :
      ( ~ m1_subset_1('#skF_5'('#skF_11',B_369,'#skF_8'),'#skF_7')
      | ~ r2_hidden('#skF_11',k9_relat_1('#skF_8',B_369)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_91,c_1406])).

tff(c_1447,plain,
    ( ~ m1_subset_1('#skF_5'('#skF_11',k1_relat_1('#skF_8'),'#skF_8'),'#skF_7')
    | ~ r2_hidden('#skF_11',k2_relat_1('#skF_8'))
    | ~ v1_relat_1('#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_1443])).

tff(c_1449,plain,(
    ~ m1_subset_1('#skF_5'('#skF_11',k1_relat_1('#skF_8'),'#skF_8'),'#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_91,c_737,c_1447])).

tff(c_1937,plain,
    ( ~ r2_hidden('#skF_11',k2_relat_1('#skF_8'))
    | ~ v4_relat_1('#skF_8','#skF_7')
    | ~ v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_1934,c_1449])).

tff(c_1964,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_91,c_142,c_737,c_1937])).

tff(c_1966,plain,(
    ~ r2_hidden('#skF_11',k2_relset_1('#skF_7','#skF_6','#skF_8')) ),
    inference(splitRight,[status(thm)],[c_60])).

tff(c_58,plain,
    ( r2_hidden(k4_tarski('#skF_10','#skF_9'),'#skF_8')
    | r2_hidden('#skF_11',k2_relset_1('#skF_7','#skF_6','#skF_8')) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_1993,plain,(
    r2_hidden(k4_tarski('#skF_10','#skF_9'),'#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_1966,c_58])).

tff(c_1997,plain,(
    r2_hidden('#skF_9',k2_relat_1('#skF_8')) ),
    inference(resolution,[status(thm)],[c_1993,c_16])).

tff(c_2098,plain,(
    ! [A_473,B_474,C_475] :
      ( k2_relset_1(A_473,B_474,C_475) = k2_relat_1(C_475)
      | ~ m1_subset_1(C_475,k1_zfmisc_1(k2_zfmisc_1(A_473,B_474))) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_2112,plain,(
    k2_relset_1('#skF_7','#skF_6','#skF_8') = k2_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_44,c_2098])).

tff(c_56,plain,
    ( ~ r2_hidden('#skF_9',k2_relset_1('#skF_7','#skF_6','#skF_8'))
    | r2_hidden('#skF_11',k2_relset_1('#skF_7','#skF_6','#skF_8')) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_2049,plain,(
    ~ r2_hidden('#skF_9',k2_relset_1('#skF_7','#skF_6','#skF_8')) ),
    inference(negUnitSimplification,[status(thm)],[c_1966,c_56])).

tff(c_2113,plain,(
    ~ r2_hidden('#skF_9',k2_relat_1('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2112,c_2049])).

tff(c_2117,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1997,c_2113])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n006.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 18:33:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.33/1.73  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.33/1.74  
% 4.33/1.74  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.33/1.74  %$ v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k2_relset_1 > k9_relat_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_11 > #skF_4 > #skF_7 > #skF_3 > #skF_10 > #skF_6 > #skF_5 > #skF_9 > #skF_8 > #skF_2 > #skF_1
% 4.33/1.74  
% 4.33/1.74  %Foreground sorts:
% 4.33/1.74  
% 4.33/1.74  
% 4.33/1.74  %Background operators:
% 4.33/1.74  
% 4.33/1.74  
% 4.33/1.74  %Foreground operators:
% 4.33/1.74  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 4.33/1.74  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.33/1.74  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.33/1.74  tff('#skF_11', type, '#skF_11': $i).
% 4.33/1.74  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 4.33/1.74  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 4.33/1.74  tff('#skF_7', type, '#skF_7': $i).
% 4.33/1.74  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 4.33/1.74  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.33/1.74  tff('#skF_10', type, '#skF_10': $i).
% 4.33/1.74  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 4.33/1.74  tff('#skF_6', type, '#skF_6': $i).
% 4.33/1.74  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 4.33/1.74  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 4.33/1.74  tff('#skF_9', type, '#skF_9': $i).
% 4.33/1.75  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 4.33/1.75  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.33/1.75  tff('#skF_8', type, '#skF_8': $i).
% 4.33/1.75  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.33/1.75  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.33/1.75  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.33/1.75  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.33/1.75  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 4.33/1.75  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 4.33/1.75  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 4.33/1.75  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.33/1.75  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.33/1.75  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.33/1.75  
% 4.33/1.76  tff(f_58, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 4.33/1.76  tff(f_102, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => (![D]: (r2_hidden(D, k2_relset_1(B, A, C)) <=> (?[E]: (m1_subset_1(E, B) & r2_hidden(k4_tarski(E, D), C))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_relset_1)).
% 4.33/1.76  tff(f_42, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 4.33/1.76  tff(f_79, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 4.33/1.76  tff(f_83, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 4.33/1.76  tff(f_73, axiom, (![A]: (v1_relat_1(A) => (k9_relat_1(A, k1_relat_1(A)) = k2_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t146_relat_1)).
% 4.33/1.76  tff(f_48, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d18_relat_1)).
% 4.33/1.76  tff(f_69, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k9_relat_1(C, B)) <=> (?[D]: ((r2_hidden(D, k1_relat_1(C)) & r2_hidden(k4_tarski(D, A), C)) & r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t143_relat_1)).
% 4.33/1.76  tff(f_29, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 4.33/1.76  tff(f_35, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset)).
% 4.33/1.76  tff(f_56, axiom, (![A, B]: ((B = k2_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(D, C), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_relat_1)).
% 4.33/1.76  tff(c_26, plain, (![A_30, B_31]: (v1_relat_1(k2_zfmisc_1(A_30, B_31)))), inference(cnfTransformation, [status(thm)], [f_58])).
% 4.33/1.76  tff(c_44, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_7', '#skF_6')))), inference(cnfTransformation, [status(thm)], [f_102])).
% 4.33/1.76  tff(c_81, plain, (![B_94, A_95]: (v1_relat_1(B_94) | ~m1_subset_1(B_94, k1_zfmisc_1(A_95)) | ~v1_relat_1(A_95))), inference(cnfTransformation, [status(thm)], [f_42])).
% 4.33/1.76  tff(c_87, plain, (v1_relat_1('#skF_8') | ~v1_relat_1(k2_zfmisc_1('#skF_7', '#skF_6'))), inference(resolution, [status(thm)], [c_44, c_81])).
% 4.33/1.76  tff(c_91, plain, (v1_relat_1('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_87])).
% 4.33/1.76  tff(c_133, plain, (![C_111, A_112, B_113]: (v4_relat_1(C_111, A_112) | ~m1_subset_1(C_111, k1_zfmisc_1(k2_zfmisc_1(A_112, B_113))))), inference(cnfTransformation, [status(thm)], [f_79])).
% 4.33/1.76  tff(c_142, plain, (v4_relat_1('#skF_8', '#skF_7')), inference(resolution, [status(thm)], [c_44, c_133])).
% 4.33/1.76  tff(c_726, plain, (![A_236, B_237, C_238]: (k2_relset_1(A_236, B_237, C_238)=k2_relat_1(C_238) | ~m1_subset_1(C_238, k1_zfmisc_1(k2_zfmisc_1(A_236, B_237))))), inference(cnfTransformation, [status(thm)], [f_83])).
% 4.33/1.76  tff(c_735, plain, (k2_relset_1('#skF_7', '#skF_6', '#skF_8')=k2_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_44, c_726])).
% 4.33/1.76  tff(c_60, plain, (m1_subset_1('#skF_10', '#skF_7') | r2_hidden('#skF_11', k2_relset_1('#skF_7', '#skF_6', '#skF_8'))), inference(cnfTransformation, [status(thm)], [f_102])).
% 4.33/1.76  tff(c_92, plain, (r2_hidden('#skF_11', k2_relset_1('#skF_7', '#skF_6', '#skF_8'))), inference(splitLeft, [status(thm)], [c_60])).
% 4.33/1.76  tff(c_737, plain, (r2_hidden('#skF_11', k2_relat_1('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_735, c_92])).
% 4.33/1.76  tff(c_36, plain, (![A_38]: (k9_relat_1(A_38, k1_relat_1(A_38))=k2_relat_1(A_38) | ~v1_relat_1(A_38))), inference(cnfTransformation, [status(thm)], [f_73])).
% 4.33/1.76  tff(c_12, plain, (![B_10, A_9]: (r1_tarski(k1_relat_1(B_10), A_9) | ~v4_relat_1(B_10, A_9) | ~v1_relat_1(B_10))), inference(cnfTransformation, [status(thm)], [f_48])).
% 4.33/1.76  tff(c_1395, plain, (![A_357, B_358, C_359]: (r2_hidden('#skF_5'(A_357, B_358, C_359), k1_relat_1(C_359)) | ~r2_hidden(A_357, k9_relat_1(C_359, B_358)) | ~v1_relat_1(C_359))), inference(cnfTransformation, [status(thm)], [f_69])).
% 4.33/1.76  tff(c_4, plain, (![A_1, B_2]: (m1_subset_1(A_1, k1_zfmisc_1(B_2)) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 4.33/1.76  tff(c_154, plain, (![A_117, C_118, B_119]: (m1_subset_1(A_117, C_118) | ~m1_subset_1(B_119, k1_zfmisc_1(C_118)) | ~r2_hidden(A_117, B_119))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.33/1.76  tff(c_159, plain, (![A_117, B_2, A_1]: (m1_subset_1(A_117, B_2) | ~r2_hidden(A_117, A_1) | ~r1_tarski(A_1, B_2))), inference(resolution, [status(thm)], [c_4, c_154])).
% 4.33/1.76  tff(c_1545, plain, (![A_389, B_390, C_391, B_392]: (m1_subset_1('#skF_5'(A_389, B_390, C_391), B_392) | ~r1_tarski(k1_relat_1(C_391), B_392) | ~r2_hidden(A_389, k9_relat_1(C_391, B_390)) | ~v1_relat_1(C_391))), inference(resolution, [status(thm)], [c_1395, c_159])).
% 4.33/1.76  tff(c_1549, plain, (![A_393, B_394, B_395, A_396]: (m1_subset_1('#skF_5'(A_393, B_394, B_395), A_396) | ~r2_hidden(A_393, k9_relat_1(B_395, B_394)) | ~v4_relat_1(B_395, A_396) | ~v1_relat_1(B_395))), inference(resolution, [status(thm)], [c_12, c_1545])).
% 4.33/1.76  tff(c_1934, plain, (![A_436, A_437, A_438]: (m1_subset_1('#skF_5'(A_436, k1_relat_1(A_437), A_437), A_438) | ~r2_hidden(A_436, k2_relat_1(A_437)) | ~v4_relat_1(A_437, A_438) | ~v1_relat_1(A_437) | ~v1_relat_1(A_437))), inference(superposition, [status(thm), theory('equality')], [c_36, c_1549])).
% 4.33/1.76  tff(c_1399, plain, (![A_360, B_361, C_362]: (r2_hidden(k4_tarski('#skF_5'(A_360, B_361, C_362), A_360), C_362) | ~r2_hidden(A_360, k9_relat_1(C_362, B_361)) | ~v1_relat_1(C_362))), inference(cnfTransformation, [status(thm)], [f_69])).
% 4.33/1.76  tff(c_50, plain, (![E_86]: (~r2_hidden('#skF_9', k2_relset_1('#skF_7', '#skF_6', '#skF_8')) | ~r2_hidden(k4_tarski(E_86, '#skF_11'), '#skF_8') | ~m1_subset_1(E_86, '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_102])).
% 4.33/1.76  tff(c_1266, plain, (![E_86]: (~r2_hidden('#skF_9', k2_relat_1('#skF_8')) | ~r2_hidden(k4_tarski(E_86, '#skF_11'), '#skF_8') | ~m1_subset_1(E_86, '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_735, c_50])).
% 4.33/1.76  tff(c_1267, plain, (~r2_hidden('#skF_9', k2_relat_1('#skF_8'))), inference(splitLeft, [status(thm)], [c_1266])).
% 4.33/1.76  tff(c_784, plain, (![A_254, B_255, C_256]: (r2_hidden('#skF_5'(A_254, B_255, C_256), k1_relat_1(C_256)) | ~r2_hidden(A_254, k9_relat_1(C_256, B_255)) | ~v1_relat_1(C_256))), inference(cnfTransformation, [status(thm)], [f_69])).
% 4.33/1.76  tff(c_996, plain, (![A_294, B_295, C_296, B_297]: (m1_subset_1('#skF_5'(A_294, B_295, C_296), B_297) | ~r1_tarski(k1_relat_1(C_296), B_297) | ~r2_hidden(A_294, k9_relat_1(C_296, B_295)) | ~v1_relat_1(C_296))), inference(resolution, [status(thm)], [c_784, c_159])).
% 4.33/1.76  tff(c_1009, plain, (![A_301, B_302, B_303, A_304]: (m1_subset_1('#skF_5'(A_301, B_302, B_303), A_304) | ~r2_hidden(A_301, k9_relat_1(B_303, B_302)) | ~v4_relat_1(B_303, A_304) | ~v1_relat_1(B_303))), inference(resolution, [status(thm)], [c_12, c_996])).
% 4.33/1.76  tff(c_1234, plain, (![A_330, A_331, A_332]: (m1_subset_1('#skF_5'(A_330, k1_relat_1(A_331), A_331), A_332) | ~r2_hidden(A_330, k2_relat_1(A_331)) | ~v4_relat_1(A_331, A_332) | ~v1_relat_1(A_331) | ~v1_relat_1(A_331))), inference(superposition, [status(thm), theory('equality')], [c_36, c_1009])).
% 4.33/1.76  tff(c_788, plain, (![A_257, B_258, C_259]: (r2_hidden(k4_tarski('#skF_5'(A_257, B_258, C_259), A_257), C_259) | ~r2_hidden(A_257, k9_relat_1(C_259, B_258)) | ~v1_relat_1(C_259))), inference(cnfTransformation, [status(thm)], [f_69])).
% 4.33/1.76  tff(c_52, plain, (![E_86]: (r2_hidden(k4_tarski('#skF_10', '#skF_9'), '#skF_8') | ~r2_hidden(k4_tarski(E_86, '#skF_11'), '#skF_8') | ~m1_subset_1(E_86, '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_102])).
% 4.33/1.76  tff(c_746, plain, (![E_86]: (~r2_hidden(k4_tarski(E_86, '#skF_11'), '#skF_8') | ~m1_subset_1(E_86, '#skF_7'))), inference(splitLeft, [status(thm)], [c_52])).
% 4.33/1.76  tff(c_792, plain, (![B_258]: (~m1_subset_1('#skF_5'('#skF_11', B_258, '#skF_8'), '#skF_7') | ~r2_hidden('#skF_11', k9_relat_1('#skF_8', B_258)) | ~v1_relat_1('#skF_8'))), inference(resolution, [status(thm)], [c_788, c_746])).
% 4.33/1.76  tff(c_827, plain, (![B_263]: (~m1_subset_1('#skF_5'('#skF_11', B_263, '#skF_8'), '#skF_7') | ~r2_hidden('#skF_11', k9_relat_1('#skF_8', B_263)))), inference(demodulation, [status(thm), theory('equality')], [c_91, c_792])).
% 4.33/1.76  tff(c_831, plain, (~m1_subset_1('#skF_5'('#skF_11', k1_relat_1('#skF_8'), '#skF_8'), '#skF_7') | ~r2_hidden('#skF_11', k2_relat_1('#skF_8')) | ~v1_relat_1('#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_36, c_827])).
% 4.33/1.76  tff(c_833, plain, (~m1_subset_1('#skF_5'('#skF_11', k1_relat_1('#skF_8'), '#skF_8'), '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_91, c_737, c_831])).
% 4.33/1.76  tff(c_1237, plain, (~r2_hidden('#skF_11', k2_relat_1('#skF_8')) | ~v4_relat_1('#skF_8', '#skF_7') | ~v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_1234, c_833])).
% 4.33/1.76  tff(c_1264, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_91, c_142, c_737, c_1237])).
% 4.33/1.76  tff(c_1265, plain, (r2_hidden(k4_tarski('#skF_10', '#skF_9'), '#skF_8')), inference(splitRight, [status(thm)], [c_52])).
% 4.33/1.76  tff(c_16, plain, (![C_26, A_11, D_29]: (r2_hidden(C_26, k2_relat_1(A_11)) | ~r2_hidden(k4_tarski(D_29, C_26), A_11))), inference(cnfTransformation, [status(thm)], [f_56])).
% 4.33/1.76  tff(c_1272, plain, (r2_hidden('#skF_9', k2_relat_1('#skF_8'))), inference(resolution, [status(thm)], [c_1265, c_16])).
% 4.33/1.76  tff(c_1277, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1267, c_1272])).
% 4.33/1.76  tff(c_1278, plain, (![E_86]: (~r2_hidden(k4_tarski(E_86, '#skF_11'), '#skF_8') | ~m1_subset_1(E_86, '#skF_7'))), inference(splitRight, [status(thm)], [c_1266])).
% 4.33/1.76  tff(c_1406, plain, (![B_361]: (~m1_subset_1('#skF_5'('#skF_11', B_361, '#skF_8'), '#skF_7') | ~r2_hidden('#skF_11', k9_relat_1('#skF_8', B_361)) | ~v1_relat_1('#skF_8'))), inference(resolution, [status(thm)], [c_1399, c_1278])).
% 4.33/1.76  tff(c_1443, plain, (![B_369]: (~m1_subset_1('#skF_5'('#skF_11', B_369, '#skF_8'), '#skF_7') | ~r2_hidden('#skF_11', k9_relat_1('#skF_8', B_369)))), inference(demodulation, [status(thm), theory('equality')], [c_91, c_1406])).
% 4.33/1.76  tff(c_1447, plain, (~m1_subset_1('#skF_5'('#skF_11', k1_relat_1('#skF_8'), '#skF_8'), '#skF_7') | ~r2_hidden('#skF_11', k2_relat_1('#skF_8')) | ~v1_relat_1('#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_36, c_1443])).
% 4.33/1.76  tff(c_1449, plain, (~m1_subset_1('#skF_5'('#skF_11', k1_relat_1('#skF_8'), '#skF_8'), '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_91, c_737, c_1447])).
% 4.33/1.76  tff(c_1937, plain, (~r2_hidden('#skF_11', k2_relat_1('#skF_8')) | ~v4_relat_1('#skF_8', '#skF_7') | ~v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_1934, c_1449])).
% 4.33/1.76  tff(c_1964, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_91, c_142, c_737, c_1937])).
% 4.33/1.76  tff(c_1966, plain, (~r2_hidden('#skF_11', k2_relset_1('#skF_7', '#skF_6', '#skF_8'))), inference(splitRight, [status(thm)], [c_60])).
% 4.33/1.76  tff(c_58, plain, (r2_hidden(k4_tarski('#skF_10', '#skF_9'), '#skF_8') | r2_hidden('#skF_11', k2_relset_1('#skF_7', '#skF_6', '#skF_8'))), inference(cnfTransformation, [status(thm)], [f_102])).
% 4.33/1.76  tff(c_1993, plain, (r2_hidden(k4_tarski('#skF_10', '#skF_9'), '#skF_8')), inference(negUnitSimplification, [status(thm)], [c_1966, c_58])).
% 4.33/1.76  tff(c_1997, plain, (r2_hidden('#skF_9', k2_relat_1('#skF_8'))), inference(resolution, [status(thm)], [c_1993, c_16])).
% 4.33/1.76  tff(c_2098, plain, (![A_473, B_474, C_475]: (k2_relset_1(A_473, B_474, C_475)=k2_relat_1(C_475) | ~m1_subset_1(C_475, k1_zfmisc_1(k2_zfmisc_1(A_473, B_474))))), inference(cnfTransformation, [status(thm)], [f_83])).
% 4.33/1.76  tff(c_2112, plain, (k2_relset_1('#skF_7', '#skF_6', '#skF_8')=k2_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_44, c_2098])).
% 4.33/1.76  tff(c_56, plain, (~r2_hidden('#skF_9', k2_relset_1('#skF_7', '#skF_6', '#skF_8')) | r2_hidden('#skF_11', k2_relset_1('#skF_7', '#skF_6', '#skF_8'))), inference(cnfTransformation, [status(thm)], [f_102])).
% 4.33/1.76  tff(c_2049, plain, (~r2_hidden('#skF_9', k2_relset_1('#skF_7', '#skF_6', '#skF_8'))), inference(negUnitSimplification, [status(thm)], [c_1966, c_56])).
% 4.33/1.76  tff(c_2113, plain, (~r2_hidden('#skF_9', k2_relat_1('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_2112, c_2049])).
% 4.33/1.76  tff(c_2117, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1997, c_2113])).
% 4.33/1.76  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.33/1.76  
% 4.33/1.76  Inference rules
% 4.33/1.76  ----------------------
% 4.33/1.76  #Ref     : 0
% 4.33/1.76  #Sup     : 447
% 4.33/1.76  #Fact    : 0
% 4.33/1.76  #Define  : 0
% 4.33/1.76  #Split   : 13
% 4.33/1.76  #Chain   : 0
% 4.33/1.76  #Close   : 0
% 4.33/1.76  
% 4.33/1.76  Ordering : KBO
% 4.33/1.76  
% 4.33/1.76  Simplification rules
% 4.33/1.76  ----------------------
% 4.33/1.76  #Subsume      : 19
% 4.33/1.76  #Demod        : 54
% 4.33/1.76  #Tautology    : 46
% 4.33/1.76  #SimpNegUnit  : 3
% 4.33/1.76  #BackRed      : 6
% 4.33/1.76  
% 4.33/1.76  #Partial instantiations: 0
% 4.33/1.76  #Strategies tried      : 1
% 4.33/1.76  
% 4.33/1.76  Timing (in seconds)
% 4.33/1.76  ----------------------
% 4.33/1.77  Preprocessing        : 0.33
% 4.33/1.77  Parsing              : 0.16
% 4.33/1.77  CNF conversion       : 0.03
% 4.33/1.77  Main loop            : 0.67
% 4.33/1.77  Inferencing          : 0.25
% 4.33/1.77  Reduction            : 0.18
% 4.33/1.77  Demodulation         : 0.12
% 4.33/1.77  BG Simplification    : 0.03
% 4.33/1.77  Subsumption          : 0.13
% 4.33/1.77  Abstraction          : 0.04
% 4.33/1.77  MUC search           : 0.00
% 4.33/1.77  Cooper               : 0.00
% 4.33/1.77  Total                : 1.03
% 4.33/1.77  Index Insertion      : 0.00
% 4.33/1.77  Index Deletion       : 0.00
% 4.33/1.77  Index Matching       : 0.00
% 4.33/1.77  BG Taut test         : 0.00
%------------------------------------------------------------------------------
