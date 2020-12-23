%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:08:07 EST 2020

% Result     : Theorem 4.62s
% Output     : CNFRefutation 4.95s
% Verified   : 
% Statistics : Number of formulae       :  120 ( 261 expanded)
%              Number of leaves         :   43 ( 107 expanded)
%              Depth                    :    9
%              Number of atoms          :  182 ( 580 expanded)
%              Number of equality atoms :   23 (  64 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k8_relset_1 > k7_relset_1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_11 > #skF_4 > #skF_7 > #skF_3 > #skF_10 > #skF_6 > #skF_5 > #skF_9 > #skF_8 > #skF_2 > #skF_1

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

tff(k8_relset_1,type,(
    k8_relset_1: ( $i * $i * $i * $i ) > $i )).

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

tff(k7_relset_1,type,(
    k7_relset_1: ( $i * $i * $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

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

tff(f_108,negated_conjecture,(
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

tff(f_75,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_79,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_58,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_42,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_83,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_89,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( k7_relset_1(A,B,C,A) = k2_relset_1(A,B,C)
        & k8_relset_1(A,B,C,B) = k1_relset_1(A,B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_relset_1)).

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

tff(c_48,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_7','#skF_6'))) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_95,plain,(
    ! [C_103,A_104,B_105] :
      ( v4_relat_1(C_103,A_104)
      | ~ m1_subset_1(C_103,k1_zfmisc_1(k2_zfmisc_1(A_104,B_105))) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_104,plain,(
    v4_relat_1('#skF_8','#skF_7') ),
    inference(resolution,[status(thm)],[c_48,c_95])).

tff(c_1644,plain,(
    ! [A_386,B_387,C_388] :
      ( k2_relset_1(A_386,B_387,C_388) = k2_relat_1(C_388)
      | ~ m1_subset_1(C_388,k1_zfmisc_1(k2_zfmisc_1(A_386,B_387))) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_1658,plain,(
    k2_relset_1('#skF_7','#skF_6','#skF_8') = k2_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_48,c_1644])).

tff(c_64,plain,
    ( m1_subset_1('#skF_10','#skF_7')
    | r2_hidden('#skF_11',k2_relset_1('#skF_7','#skF_6','#skF_8')) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_87,plain,(
    r2_hidden('#skF_11',k2_relset_1('#skF_7','#skF_6','#skF_8')) ),
    inference(splitLeft,[status(thm)],[c_64])).

tff(c_1662,plain,(
    r2_hidden('#skF_11',k2_relat_1('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1658,c_87])).

tff(c_26,plain,(
    ! [A_30,B_31] : v1_relat_1(k2_zfmisc_1(A_30,B_31)) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_76,plain,(
    ! [B_99,A_100] :
      ( v1_relat_1(B_99)
      | ~ m1_subset_1(B_99,k1_zfmisc_1(A_100))
      | ~ v1_relat_1(A_100) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_82,plain,
    ( v1_relat_1('#skF_8')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_7','#skF_6')) ),
    inference(resolution,[status(thm)],[c_48,c_76])).

tff(c_86,plain,(
    v1_relat_1('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_82])).

tff(c_1728,plain,(
    ! [A_411,B_412,C_413,D_414] :
      ( k7_relset_1(A_411,B_412,C_413,D_414) = k9_relat_1(C_413,D_414)
      | ~ m1_subset_1(C_413,k1_zfmisc_1(k2_zfmisc_1(A_411,B_412))) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_1739,plain,(
    ! [D_414] : k7_relset_1('#skF_7','#skF_6','#skF_8',D_414) = k9_relat_1('#skF_8',D_414) ),
    inference(resolution,[status(thm)],[c_48,c_1728])).

tff(c_1838,plain,(
    ! [A_442,B_443,C_444] :
      ( k7_relset_1(A_442,B_443,C_444,A_442) = k2_relset_1(A_442,B_443,C_444)
      | ~ m1_subset_1(C_444,k1_zfmisc_1(k2_zfmisc_1(A_442,B_443))) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_1846,plain,(
    k7_relset_1('#skF_7','#skF_6','#skF_8','#skF_7') = k2_relset_1('#skF_7','#skF_6','#skF_8') ),
    inference(resolution,[status(thm)],[c_48,c_1838])).

tff(c_1850,plain,(
    k9_relat_1('#skF_8','#skF_7') = k2_relat_1('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1739,c_1658,c_1846])).

tff(c_12,plain,(
    ! [B_10,A_9] :
      ( r1_tarski(k1_relat_1(B_10),A_9)
      | ~ v4_relat_1(B_10,A_9)
      | ~ v1_relat_1(B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_1762,plain,(
    ! [A_420,B_421,C_422] :
      ( r2_hidden('#skF_5'(A_420,B_421,C_422),k1_relat_1(C_422))
      | ~ r2_hidden(A_420,k9_relat_1(C_422,B_421))
      | ~ v1_relat_1(C_422) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( m1_subset_1(A_1,k1_zfmisc_1(B_2))
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_800,plain,(
    ! [A_240,C_241,B_242] :
      ( m1_subset_1(A_240,C_241)
      | ~ m1_subset_1(B_242,k1_zfmisc_1(C_241))
      | ~ r2_hidden(A_240,B_242) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_805,plain,(
    ! [A_240,B_2,A_1] :
      ( m1_subset_1(A_240,B_2)
      | ~ r2_hidden(A_240,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(resolution,[status(thm)],[c_4,c_800])).

tff(c_2384,plain,(
    ! [A_504,B_505,C_506,B_507] :
      ( m1_subset_1('#skF_5'(A_504,B_505,C_506),B_507)
      | ~ r1_tarski(k1_relat_1(C_506),B_507)
      | ~ r2_hidden(A_504,k9_relat_1(C_506,B_505))
      | ~ v1_relat_1(C_506) ) ),
    inference(resolution,[status(thm)],[c_1762,c_805])).

tff(c_2388,plain,(
    ! [A_508,B_509,B_510,A_511] :
      ( m1_subset_1('#skF_5'(A_508,B_509,B_510),A_511)
      | ~ r2_hidden(A_508,k9_relat_1(B_510,B_509))
      | ~ v4_relat_1(B_510,A_511)
      | ~ v1_relat_1(B_510) ) ),
    inference(resolution,[status(thm)],[c_12,c_2384])).

tff(c_2398,plain,(
    ! [A_508,A_511] :
      ( m1_subset_1('#skF_5'(A_508,'#skF_7','#skF_8'),A_511)
      | ~ r2_hidden(A_508,k2_relat_1('#skF_8'))
      | ~ v4_relat_1('#skF_8',A_511)
      | ~ v1_relat_1('#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1850,c_2388])).

tff(c_2424,plain,(
    ! [A_512,A_513] :
      ( m1_subset_1('#skF_5'(A_512,'#skF_7','#skF_8'),A_513)
      | ~ r2_hidden(A_512,k2_relat_1('#skF_8'))
      | ~ v4_relat_1('#skF_8',A_513) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_2398])).

tff(c_2463,plain,(
    ! [A_514] :
      ( m1_subset_1('#skF_5'('#skF_11','#skF_7','#skF_8'),A_514)
      | ~ v4_relat_1('#skF_8',A_514) ) ),
    inference(resolution,[status(thm)],[c_1662,c_2424])).

tff(c_1797,plain,(
    ! [A_435,B_436,C_437] :
      ( r2_hidden(k4_tarski('#skF_5'(A_435,B_436,C_437),A_435),C_437)
      | ~ r2_hidden(A_435,k9_relat_1(C_437,B_436))
      | ~ v1_relat_1(C_437) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_825,plain,(
    ! [A_257,B_258,C_259] :
      ( k2_relset_1(A_257,B_258,C_259) = k2_relat_1(C_259)
      | ~ m1_subset_1(C_259,k1_zfmisc_1(k2_zfmisc_1(A_257,B_258))) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_834,plain,(
    k2_relset_1('#skF_7','#skF_6','#skF_8') = k2_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_48,c_825])).

tff(c_849,plain,(
    r2_hidden('#skF_11',k2_relat_1('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_834,c_87])).

tff(c_880,plain,(
    ! [A_271,B_272,C_273,D_274] :
      ( k7_relset_1(A_271,B_272,C_273,D_274) = k9_relat_1(C_273,D_274)
      | ~ m1_subset_1(C_273,k1_zfmisc_1(k2_zfmisc_1(A_271,B_272))) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_887,plain,(
    ! [D_274] : k7_relset_1('#skF_7','#skF_6','#skF_8',D_274) = k9_relat_1('#skF_8',D_274) ),
    inference(resolution,[status(thm)],[c_48,c_880])).

tff(c_911,plain,(
    ! [A_286,B_287,C_288] :
      ( k7_relset_1(A_286,B_287,C_288,A_286) = k2_relset_1(A_286,B_287,C_288)
      | ~ m1_subset_1(C_288,k1_zfmisc_1(k2_zfmisc_1(A_286,B_287))) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_916,plain,(
    k7_relset_1('#skF_7','#skF_6','#skF_8','#skF_7') = k2_relset_1('#skF_7','#skF_6','#skF_8') ),
    inference(resolution,[status(thm)],[c_48,c_911])).

tff(c_919,plain,(
    k9_relat_1('#skF_8','#skF_7') = k2_relat_1('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_887,c_834,c_916])).

tff(c_906,plain,(
    ! [A_280,B_281,C_282] :
      ( r2_hidden('#skF_5'(A_280,B_281,C_282),k1_relat_1(C_282))
      | ~ r2_hidden(A_280,k9_relat_1(C_282,B_281))
      | ~ v1_relat_1(C_282) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_1423,plain,(
    ! [A_361,B_362,C_363,B_364] :
      ( m1_subset_1('#skF_5'(A_361,B_362,C_363),B_364)
      | ~ r1_tarski(k1_relat_1(C_363),B_364)
      | ~ r2_hidden(A_361,k9_relat_1(C_363,B_362))
      | ~ v1_relat_1(C_363) ) ),
    inference(resolution,[status(thm)],[c_906,c_805])).

tff(c_1427,plain,(
    ! [A_365,B_366,B_367,A_368] :
      ( m1_subset_1('#skF_5'(A_365,B_366,B_367),A_368)
      | ~ r2_hidden(A_365,k9_relat_1(B_367,B_366))
      | ~ v4_relat_1(B_367,A_368)
      | ~ v1_relat_1(B_367) ) ),
    inference(resolution,[status(thm)],[c_12,c_1423])).

tff(c_1443,plain,(
    ! [A_365,A_368] :
      ( m1_subset_1('#skF_5'(A_365,'#skF_7','#skF_8'),A_368)
      | ~ r2_hidden(A_365,k2_relat_1('#skF_8'))
      | ~ v4_relat_1('#skF_8',A_368)
      | ~ v1_relat_1('#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_919,c_1427])).

tff(c_1463,plain,(
    ! [A_369,A_370] :
      ( m1_subset_1('#skF_5'(A_369,'#skF_7','#skF_8'),A_370)
      | ~ r2_hidden(A_369,k2_relat_1('#skF_8'))
      | ~ v4_relat_1('#skF_8',A_370) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_1443])).

tff(c_1503,plain,(
    ! [A_371] :
      ( m1_subset_1('#skF_5'('#skF_11','#skF_7','#skF_8'),A_371)
      | ~ v4_relat_1('#skF_8',A_371) ) ),
    inference(resolution,[status(thm)],[c_849,c_1463])).

tff(c_933,plain,(
    ! [A_292,B_293,C_294] :
      ( r2_hidden(k4_tarski('#skF_5'(A_292,B_293,C_294),A_292),C_294)
      | ~ r2_hidden(A_292,k9_relat_1(C_294,B_293))
      | ~ v1_relat_1(C_294) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_56,plain,(
    ! [E_92] :
      ( r2_hidden(k4_tarski('#skF_10','#skF_9'),'#skF_8')
      | ~ r2_hidden(k4_tarski(E_92,'#skF_11'),'#skF_8')
      | ~ m1_subset_1(E_92,'#skF_7') ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_821,plain,(
    ! [E_92] :
      ( ~ r2_hidden(k4_tarski(E_92,'#skF_11'),'#skF_8')
      | ~ m1_subset_1(E_92,'#skF_7') ) ),
    inference(splitLeft,[status(thm)],[c_56])).

tff(c_937,plain,(
    ! [B_293] :
      ( ~ m1_subset_1('#skF_5'('#skF_11',B_293,'#skF_8'),'#skF_7')
      | ~ r2_hidden('#skF_11',k9_relat_1('#skF_8',B_293))
      | ~ v1_relat_1('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_933,c_821])).

tff(c_986,plain,(
    ! [B_301] :
      ( ~ m1_subset_1('#skF_5'('#skF_11',B_301,'#skF_8'),'#skF_7')
      | ~ r2_hidden('#skF_11',k9_relat_1('#skF_8',B_301)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_937])).

tff(c_989,plain,
    ( ~ m1_subset_1('#skF_5'('#skF_11','#skF_7','#skF_8'),'#skF_7')
    | ~ r2_hidden('#skF_11',k2_relat_1('#skF_8')) ),
    inference(superposition,[status(thm),theory(equality)],[c_919,c_986])).

tff(c_991,plain,(
    ~ m1_subset_1('#skF_5'('#skF_11','#skF_7','#skF_8'),'#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_849,c_989])).

tff(c_1506,plain,(
    ~ v4_relat_1('#skF_8','#skF_7') ),
    inference(resolution,[status(thm)],[c_1503,c_991])).

tff(c_1542,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_1506])).

tff(c_1543,plain,(
    r2_hidden(k4_tarski('#skF_10','#skF_9'),'#skF_8') ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_16,plain,(
    ! [C_26,A_11,D_29] :
      ( r2_hidden(C_26,k2_relat_1(A_11))
      | ~ r2_hidden(k4_tarski(D_29,C_26),A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_1550,plain,(
    r2_hidden('#skF_9',k2_relat_1('#skF_8')) ),
    inference(resolution,[status(thm)],[c_1543,c_16])).

tff(c_1598,plain,(
    ! [A_376,B_377,C_378] :
      ( k2_relset_1(A_376,B_377,C_378) = k2_relat_1(C_378)
      | ~ m1_subset_1(C_378,k1_zfmisc_1(k2_zfmisc_1(A_376,B_377))) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_1612,plain,(
    k2_relset_1('#skF_7','#skF_6','#skF_8') = k2_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_48,c_1598])).

tff(c_54,plain,(
    ! [E_92] :
      ( ~ r2_hidden('#skF_9',k2_relset_1('#skF_7','#skF_6','#skF_8'))
      | ~ r2_hidden(k4_tarski(E_92,'#skF_11'),'#skF_8')
      | ~ m1_subset_1(E_92,'#skF_7') ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_1580,plain,(
    ~ r2_hidden('#skF_9',k2_relset_1('#skF_7','#skF_6','#skF_8')) ),
    inference(splitLeft,[status(thm)],[c_54])).

tff(c_1613,plain,(
    ~ r2_hidden('#skF_9',k2_relat_1('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1612,c_1580])).

tff(c_1618,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1550,c_1613])).

tff(c_1619,plain,(
    ! [E_92] :
      ( ~ r2_hidden(k4_tarski(E_92,'#skF_11'),'#skF_8')
      | ~ m1_subset_1(E_92,'#skF_7') ) ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_1804,plain,(
    ! [B_436] :
      ( ~ m1_subset_1('#skF_5'('#skF_11',B_436,'#skF_8'),'#skF_7')
      | ~ r2_hidden('#skF_11',k9_relat_1('#skF_8',B_436))
      | ~ v1_relat_1('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_1797,c_1619])).

tff(c_1813,plain,(
    ! [B_436] :
      ( ~ m1_subset_1('#skF_5'('#skF_11',B_436,'#skF_8'),'#skF_7')
      | ~ r2_hidden('#skF_11',k9_relat_1('#skF_8',B_436)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_1804])).

tff(c_1871,plain,
    ( ~ m1_subset_1('#skF_5'('#skF_11','#skF_7','#skF_8'),'#skF_7')
    | ~ r2_hidden('#skF_11',k2_relat_1('#skF_8')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1850,c_1813])).

tff(c_1878,plain,(
    ~ m1_subset_1('#skF_5'('#skF_11','#skF_7','#skF_8'),'#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1662,c_1871])).

tff(c_2466,plain,(
    ~ v4_relat_1('#skF_8','#skF_7') ),
    inference(resolution,[status(thm)],[c_2463,c_1878])).

tff(c_2502,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_2466])).

tff(c_2504,plain,(
    ~ r2_hidden('#skF_11',k2_relset_1('#skF_7','#skF_6','#skF_8')) ),
    inference(splitRight,[status(thm)],[c_64])).

tff(c_62,plain,
    ( r2_hidden(k4_tarski('#skF_10','#skF_9'),'#skF_8')
    | r2_hidden('#skF_11',k2_relset_1('#skF_7','#skF_6','#skF_8')) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_2574,plain,(
    r2_hidden(k4_tarski('#skF_10','#skF_9'),'#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_2504,c_62])).

tff(c_2578,plain,(
    r2_hidden('#skF_9',k2_relat_1('#skF_8')) ),
    inference(resolution,[status(thm)],[c_2574,c_16])).

tff(c_2635,plain,(
    ! [A_548,B_549,C_550] :
      ( k2_relset_1(A_548,B_549,C_550) = k2_relat_1(C_550)
      | ~ m1_subset_1(C_550,k1_zfmisc_1(k2_zfmisc_1(A_548,B_549))) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_2649,plain,(
    k2_relset_1('#skF_7','#skF_6','#skF_8') = k2_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_48,c_2635])).

tff(c_60,plain,
    ( ~ r2_hidden('#skF_9',k2_relset_1('#skF_7','#skF_6','#skF_8'))
    | r2_hidden('#skF_11',k2_relset_1('#skF_7','#skF_6','#skF_8')) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_2587,plain,(
    ~ r2_hidden('#skF_9',k2_relset_1('#skF_7','#skF_6','#skF_8')) ),
    inference(negUnitSimplification,[status(thm)],[c_2504,c_60])).

tff(c_2650,plain,(
    ~ r2_hidden('#skF_9',k2_relat_1('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2649,c_2587])).

tff(c_2654,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2578,c_2650])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.33  % Computer   : n011.cluster.edu
% 0.14/0.33  % Model      : x86_64 x86_64
% 0.14/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.33  % Memory     : 8042.1875MB
% 0.14/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 11:17:27 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.62/1.90  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.95/1.91  
% 4.95/1.91  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.95/1.91  %$ v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k8_relset_1 > k7_relset_1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_11 > #skF_4 > #skF_7 > #skF_3 > #skF_10 > #skF_6 > #skF_5 > #skF_9 > #skF_8 > #skF_2 > #skF_1
% 4.95/1.91  
% 4.95/1.91  %Foreground sorts:
% 4.95/1.91  
% 4.95/1.91  
% 4.95/1.91  %Background operators:
% 4.95/1.91  
% 4.95/1.91  
% 4.95/1.91  %Foreground operators:
% 4.95/1.91  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 4.95/1.91  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.95/1.91  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.95/1.91  tff('#skF_11', type, '#skF_11': $i).
% 4.95/1.91  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 4.95/1.91  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 4.95/1.91  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 4.95/1.91  tff('#skF_7', type, '#skF_7': $i).
% 4.95/1.91  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 4.95/1.91  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.95/1.91  tff('#skF_10', type, '#skF_10': $i).
% 4.95/1.91  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 4.95/1.91  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 4.95/1.91  tff('#skF_6', type, '#skF_6': $i).
% 4.95/1.91  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 4.95/1.91  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 4.95/1.91  tff('#skF_9', type, '#skF_9': $i).
% 4.95/1.91  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 4.95/1.91  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 4.95/1.91  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.95/1.91  tff('#skF_8', type, '#skF_8': $i).
% 4.95/1.91  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.95/1.91  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.95/1.91  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.95/1.91  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.95/1.91  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 4.95/1.91  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 4.95/1.91  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 4.95/1.91  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.95/1.91  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.95/1.91  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.95/1.91  
% 4.95/1.93  tff(f_108, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => (![D]: (r2_hidden(D, k2_relset_1(B, A, C)) <=> (?[E]: (m1_subset_1(E, B) & r2_hidden(k4_tarski(E, D), C))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_relset_1)).
% 4.95/1.93  tff(f_75, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 4.95/1.93  tff(f_79, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 4.95/1.93  tff(f_58, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 4.95/1.93  tff(f_42, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 4.95/1.93  tff(f_83, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 4.95/1.93  tff(f_89, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((k7_relset_1(A, B, C, A) = k2_relset_1(A, B, C)) & (k8_relset_1(A, B, C, B) = k1_relset_1(A, B, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_relset_1)).
% 4.95/1.93  tff(f_48, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d18_relat_1)).
% 4.95/1.93  tff(f_69, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k9_relat_1(C, B)) <=> (?[D]: ((r2_hidden(D, k1_relat_1(C)) & r2_hidden(k4_tarski(D, A), C)) & r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t143_relat_1)).
% 4.95/1.93  tff(f_29, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 4.95/1.93  tff(f_35, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset)).
% 4.95/1.93  tff(f_56, axiom, (![A, B]: ((B = k2_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(D, C), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_relat_1)).
% 4.95/1.93  tff(c_48, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_7', '#skF_6')))), inference(cnfTransformation, [status(thm)], [f_108])).
% 4.95/1.93  tff(c_95, plain, (![C_103, A_104, B_105]: (v4_relat_1(C_103, A_104) | ~m1_subset_1(C_103, k1_zfmisc_1(k2_zfmisc_1(A_104, B_105))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 4.95/1.93  tff(c_104, plain, (v4_relat_1('#skF_8', '#skF_7')), inference(resolution, [status(thm)], [c_48, c_95])).
% 4.95/1.93  tff(c_1644, plain, (![A_386, B_387, C_388]: (k2_relset_1(A_386, B_387, C_388)=k2_relat_1(C_388) | ~m1_subset_1(C_388, k1_zfmisc_1(k2_zfmisc_1(A_386, B_387))))), inference(cnfTransformation, [status(thm)], [f_79])).
% 4.95/1.93  tff(c_1658, plain, (k2_relset_1('#skF_7', '#skF_6', '#skF_8')=k2_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_48, c_1644])).
% 4.95/1.93  tff(c_64, plain, (m1_subset_1('#skF_10', '#skF_7') | r2_hidden('#skF_11', k2_relset_1('#skF_7', '#skF_6', '#skF_8'))), inference(cnfTransformation, [status(thm)], [f_108])).
% 4.95/1.93  tff(c_87, plain, (r2_hidden('#skF_11', k2_relset_1('#skF_7', '#skF_6', '#skF_8'))), inference(splitLeft, [status(thm)], [c_64])).
% 4.95/1.93  tff(c_1662, plain, (r2_hidden('#skF_11', k2_relat_1('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_1658, c_87])).
% 4.95/1.93  tff(c_26, plain, (![A_30, B_31]: (v1_relat_1(k2_zfmisc_1(A_30, B_31)))), inference(cnfTransformation, [status(thm)], [f_58])).
% 4.95/1.93  tff(c_76, plain, (![B_99, A_100]: (v1_relat_1(B_99) | ~m1_subset_1(B_99, k1_zfmisc_1(A_100)) | ~v1_relat_1(A_100))), inference(cnfTransformation, [status(thm)], [f_42])).
% 4.95/1.93  tff(c_82, plain, (v1_relat_1('#skF_8') | ~v1_relat_1(k2_zfmisc_1('#skF_7', '#skF_6'))), inference(resolution, [status(thm)], [c_48, c_76])).
% 4.95/1.93  tff(c_86, plain, (v1_relat_1('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_82])).
% 4.95/1.93  tff(c_1728, plain, (![A_411, B_412, C_413, D_414]: (k7_relset_1(A_411, B_412, C_413, D_414)=k9_relat_1(C_413, D_414) | ~m1_subset_1(C_413, k1_zfmisc_1(k2_zfmisc_1(A_411, B_412))))), inference(cnfTransformation, [status(thm)], [f_83])).
% 4.95/1.93  tff(c_1739, plain, (![D_414]: (k7_relset_1('#skF_7', '#skF_6', '#skF_8', D_414)=k9_relat_1('#skF_8', D_414))), inference(resolution, [status(thm)], [c_48, c_1728])).
% 4.95/1.93  tff(c_1838, plain, (![A_442, B_443, C_444]: (k7_relset_1(A_442, B_443, C_444, A_442)=k2_relset_1(A_442, B_443, C_444) | ~m1_subset_1(C_444, k1_zfmisc_1(k2_zfmisc_1(A_442, B_443))))), inference(cnfTransformation, [status(thm)], [f_89])).
% 4.95/1.93  tff(c_1846, plain, (k7_relset_1('#skF_7', '#skF_6', '#skF_8', '#skF_7')=k2_relset_1('#skF_7', '#skF_6', '#skF_8')), inference(resolution, [status(thm)], [c_48, c_1838])).
% 4.95/1.93  tff(c_1850, plain, (k9_relat_1('#skF_8', '#skF_7')=k2_relat_1('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_1739, c_1658, c_1846])).
% 4.95/1.93  tff(c_12, plain, (![B_10, A_9]: (r1_tarski(k1_relat_1(B_10), A_9) | ~v4_relat_1(B_10, A_9) | ~v1_relat_1(B_10))), inference(cnfTransformation, [status(thm)], [f_48])).
% 4.95/1.93  tff(c_1762, plain, (![A_420, B_421, C_422]: (r2_hidden('#skF_5'(A_420, B_421, C_422), k1_relat_1(C_422)) | ~r2_hidden(A_420, k9_relat_1(C_422, B_421)) | ~v1_relat_1(C_422))), inference(cnfTransformation, [status(thm)], [f_69])).
% 4.95/1.93  tff(c_4, plain, (![A_1, B_2]: (m1_subset_1(A_1, k1_zfmisc_1(B_2)) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 4.95/1.93  tff(c_800, plain, (![A_240, C_241, B_242]: (m1_subset_1(A_240, C_241) | ~m1_subset_1(B_242, k1_zfmisc_1(C_241)) | ~r2_hidden(A_240, B_242))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.95/1.93  tff(c_805, plain, (![A_240, B_2, A_1]: (m1_subset_1(A_240, B_2) | ~r2_hidden(A_240, A_1) | ~r1_tarski(A_1, B_2))), inference(resolution, [status(thm)], [c_4, c_800])).
% 4.95/1.93  tff(c_2384, plain, (![A_504, B_505, C_506, B_507]: (m1_subset_1('#skF_5'(A_504, B_505, C_506), B_507) | ~r1_tarski(k1_relat_1(C_506), B_507) | ~r2_hidden(A_504, k9_relat_1(C_506, B_505)) | ~v1_relat_1(C_506))), inference(resolution, [status(thm)], [c_1762, c_805])).
% 4.95/1.93  tff(c_2388, plain, (![A_508, B_509, B_510, A_511]: (m1_subset_1('#skF_5'(A_508, B_509, B_510), A_511) | ~r2_hidden(A_508, k9_relat_1(B_510, B_509)) | ~v4_relat_1(B_510, A_511) | ~v1_relat_1(B_510))), inference(resolution, [status(thm)], [c_12, c_2384])).
% 4.95/1.93  tff(c_2398, plain, (![A_508, A_511]: (m1_subset_1('#skF_5'(A_508, '#skF_7', '#skF_8'), A_511) | ~r2_hidden(A_508, k2_relat_1('#skF_8')) | ~v4_relat_1('#skF_8', A_511) | ~v1_relat_1('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_1850, c_2388])).
% 4.95/1.93  tff(c_2424, plain, (![A_512, A_513]: (m1_subset_1('#skF_5'(A_512, '#skF_7', '#skF_8'), A_513) | ~r2_hidden(A_512, k2_relat_1('#skF_8')) | ~v4_relat_1('#skF_8', A_513))), inference(demodulation, [status(thm), theory('equality')], [c_86, c_2398])).
% 4.95/1.93  tff(c_2463, plain, (![A_514]: (m1_subset_1('#skF_5'('#skF_11', '#skF_7', '#skF_8'), A_514) | ~v4_relat_1('#skF_8', A_514))), inference(resolution, [status(thm)], [c_1662, c_2424])).
% 4.95/1.93  tff(c_1797, plain, (![A_435, B_436, C_437]: (r2_hidden(k4_tarski('#skF_5'(A_435, B_436, C_437), A_435), C_437) | ~r2_hidden(A_435, k9_relat_1(C_437, B_436)) | ~v1_relat_1(C_437))), inference(cnfTransformation, [status(thm)], [f_69])).
% 4.95/1.93  tff(c_825, plain, (![A_257, B_258, C_259]: (k2_relset_1(A_257, B_258, C_259)=k2_relat_1(C_259) | ~m1_subset_1(C_259, k1_zfmisc_1(k2_zfmisc_1(A_257, B_258))))), inference(cnfTransformation, [status(thm)], [f_79])).
% 4.95/1.93  tff(c_834, plain, (k2_relset_1('#skF_7', '#skF_6', '#skF_8')=k2_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_48, c_825])).
% 4.95/1.93  tff(c_849, plain, (r2_hidden('#skF_11', k2_relat_1('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_834, c_87])).
% 4.95/1.93  tff(c_880, plain, (![A_271, B_272, C_273, D_274]: (k7_relset_1(A_271, B_272, C_273, D_274)=k9_relat_1(C_273, D_274) | ~m1_subset_1(C_273, k1_zfmisc_1(k2_zfmisc_1(A_271, B_272))))), inference(cnfTransformation, [status(thm)], [f_83])).
% 4.95/1.93  tff(c_887, plain, (![D_274]: (k7_relset_1('#skF_7', '#skF_6', '#skF_8', D_274)=k9_relat_1('#skF_8', D_274))), inference(resolution, [status(thm)], [c_48, c_880])).
% 4.95/1.93  tff(c_911, plain, (![A_286, B_287, C_288]: (k7_relset_1(A_286, B_287, C_288, A_286)=k2_relset_1(A_286, B_287, C_288) | ~m1_subset_1(C_288, k1_zfmisc_1(k2_zfmisc_1(A_286, B_287))))), inference(cnfTransformation, [status(thm)], [f_89])).
% 4.95/1.93  tff(c_916, plain, (k7_relset_1('#skF_7', '#skF_6', '#skF_8', '#skF_7')=k2_relset_1('#skF_7', '#skF_6', '#skF_8')), inference(resolution, [status(thm)], [c_48, c_911])).
% 4.95/1.93  tff(c_919, plain, (k9_relat_1('#skF_8', '#skF_7')=k2_relat_1('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_887, c_834, c_916])).
% 4.95/1.93  tff(c_906, plain, (![A_280, B_281, C_282]: (r2_hidden('#skF_5'(A_280, B_281, C_282), k1_relat_1(C_282)) | ~r2_hidden(A_280, k9_relat_1(C_282, B_281)) | ~v1_relat_1(C_282))), inference(cnfTransformation, [status(thm)], [f_69])).
% 4.95/1.93  tff(c_1423, plain, (![A_361, B_362, C_363, B_364]: (m1_subset_1('#skF_5'(A_361, B_362, C_363), B_364) | ~r1_tarski(k1_relat_1(C_363), B_364) | ~r2_hidden(A_361, k9_relat_1(C_363, B_362)) | ~v1_relat_1(C_363))), inference(resolution, [status(thm)], [c_906, c_805])).
% 4.95/1.93  tff(c_1427, plain, (![A_365, B_366, B_367, A_368]: (m1_subset_1('#skF_5'(A_365, B_366, B_367), A_368) | ~r2_hidden(A_365, k9_relat_1(B_367, B_366)) | ~v4_relat_1(B_367, A_368) | ~v1_relat_1(B_367))), inference(resolution, [status(thm)], [c_12, c_1423])).
% 4.95/1.93  tff(c_1443, plain, (![A_365, A_368]: (m1_subset_1('#skF_5'(A_365, '#skF_7', '#skF_8'), A_368) | ~r2_hidden(A_365, k2_relat_1('#skF_8')) | ~v4_relat_1('#skF_8', A_368) | ~v1_relat_1('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_919, c_1427])).
% 4.95/1.93  tff(c_1463, plain, (![A_369, A_370]: (m1_subset_1('#skF_5'(A_369, '#skF_7', '#skF_8'), A_370) | ~r2_hidden(A_369, k2_relat_1('#skF_8')) | ~v4_relat_1('#skF_8', A_370))), inference(demodulation, [status(thm), theory('equality')], [c_86, c_1443])).
% 4.95/1.93  tff(c_1503, plain, (![A_371]: (m1_subset_1('#skF_5'('#skF_11', '#skF_7', '#skF_8'), A_371) | ~v4_relat_1('#skF_8', A_371))), inference(resolution, [status(thm)], [c_849, c_1463])).
% 4.95/1.93  tff(c_933, plain, (![A_292, B_293, C_294]: (r2_hidden(k4_tarski('#skF_5'(A_292, B_293, C_294), A_292), C_294) | ~r2_hidden(A_292, k9_relat_1(C_294, B_293)) | ~v1_relat_1(C_294))), inference(cnfTransformation, [status(thm)], [f_69])).
% 4.95/1.93  tff(c_56, plain, (![E_92]: (r2_hidden(k4_tarski('#skF_10', '#skF_9'), '#skF_8') | ~r2_hidden(k4_tarski(E_92, '#skF_11'), '#skF_8') | ~m1_subset_1(E_92, '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_108])).
% 4.95/1.93  tff(c_821, plain, (![E_92]: (~r2_hidden(k4_tarski(E_92, '#skF_11'), '#skF_8') | ~m1_subset_1(E_92, '#skF_7'))), inference(splitLeft, [status(thm)], [c_56])).
% 4.95/1.93  tff(c_937, plain, (![B_293]: (~m1_subset_1('#skF_5'('#skF_11', B_293, '#skF_8'), '#skF_7') | ~r2_hidden('#skF_11', k9_relat_1('#skF_8', B_293)) | ~v1_relat_1('#skF_8'))), inference(resolution, [status(thm)], [c_933, c_821])).
% 4.95/1.93  tff(c_986, plain, (![B_301]: (~m1_subset_1('#skF_5'('#skF_11', B_301, '#skF_8'), '#skF_7') | ~r2_hidden('#skF_11', k9_relat_1('#skF_8', B_301)))), inference(demodulation, [status(thm), theory('equality')], [c_86, c_937])).
% 4.95/1.93  tff(c_989, plain, (~m1_subset_1('#skF_5'('#skF_11', '#skF_7', '#skF_8'), '#skF_7') | ~r2_hidden('#skF_11', k2_relat_1('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_919, c_986])).
% 4.95/1.93  tff(c_991, plain, (~m1_subset_1('#skF_5'('#skF_11', '#skF_7', '#skF_8'), '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_849, c_989])).
% 4.95/1.93  tff(c_1506, plain, (~v4_relat_1('#skF_8', '#skF_7')), inference(resolution, [status(thm)], [c_1503, c_991])).
% 4.95/1.93  tff(c_1542, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_104, c_1506])).
% 4.95/1.93  tff(c_1543, plain, (r2_hidden(k4_tarski('#skF_10', '#skF_9'), '#skF_8')), inference(splitRight, [status(thm)], [c_56])).
% 4.95/1.93  tff(c_16, plain, (![C_26, A_11, D_29]: (r2_hidden(C_26, k2_relat_1(A_11)) | ~r2_hidden(k4_tarski(D_29, C_26), A_11))), inference(cnfTransformation, [status(thm)], [f_56])).
% 4.95/1.93  tff(c_1550, plain, (r2_hidden('#skF_9', k2_relat_1('#skF_8'))), inference(resolution, [status(thm)], [c_1543, c_16])).
% 4.95/1.93  tff(c_1598, plain, (![A_376, B_377, C_378]: (k2_relset_1(A_376, B_377, C_378)=k2_relat_1(C_378) | ~m1_subset_1(C_378, k1_zfmisc_1(k2_zfmisc_1(A_376, B_377))))), inference(cnfTransformation, [status(thm)], [f_79])).
% 4.95/1.93  tff(c_1612, plain, (k2_relset_1('#skF_7', '#skF_6', '#skF_8')=k2_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_48, c_1598])).
% 4.95/1.93  tff(c_54, plain, (![E_92]: (~r2_hidden('#skF_9', k2_relset_1('#skF_7', '#skF_6', '#skF_8')) | ~r2_hidden(k4_tarski(E_92, '#skF_11'), '#skF_8') | ~m1_subset_1(E_92, '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_108])).
% 4.95/1.93  tff(c_1580, plain, (~r2_hidden('#skF_9', k2_relset_1('#skF_7', '#skF_6', '#skF_8'))), inference(splitLeft, [status(thm)], [c_54])).
% 4.95/1.93  tff(c_1613, plain, (~r2_hidden('#skF_9', k2_relat_1('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_1612, c_1580])).
% 4.95/1.93  tff(c_1618, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1550, c_1613])).
% 4.95/1.93  tff(c_1619, plain, (![E_92]: (~r2_hidden(k4_tarski(E_92, '#skF_11'), '#skF_8') | ~m1_subset_1(E_92, '#skF_7'))), inference(splitRight, [status(thm)], [c_54])).
% 4.95/1.93  tff(c_1804, plain, (![B_436]: (~m1_subset_1('#skF_5'('#skF_11', B_436, '#skF_8'), '#skF_7') | ~r2_hidden('#skF_11', k9_relat_1('#skF_8', B_436)) | ~v1_relat_1('#skF_8'))), inference(resolution, [status(thm)], [c_1797, c_1619])).
% 4.95/1.93  tff(c_1813, plain, (![B_436]: (~m1_subset_1('#skF_5'('#skF_11', B_436, '#skF_8'), '#skF_7') | ~r2_hidden('#skF_11', k9_relat_1('#skF_8', B_436)))), inference(demodulation, [status(thm), theory('equality')], [c_86, c_1804])).
% 4.95/1.93  tff(c_1871, plain, (~m1_subset_1('#skF_5'('#skF_11', '#skF_7', '#skF_8'), '#skF_7') | ~r2_hidden('#skF_11', k2_relat_1('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_1850, c_1813])).
% 4.95/1.93  tff(c_1878, plain, (~m1_subset_1('#skF_5'('#skF_11', '#skF_7', '#skF_8'), '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_1662, c_1871])).
% 4.95/1.93  tff(c_2466, plain, (~v4_relat_1('#skF_8', '#skF_7')), inference(resolution, [status(thm)], [c_2463, c_1878])).
% 4.95/1.93  tff(c_2502, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_104, c_2466])).
% 4.95/1.93  tff(c_2504, plain, (~r2_hidden('#skF_11', k2_relset_1('#skF_7', '#skF_6', '#skF_8'))), inference(splitRight, [status(thm)], [c_64])).
% 4.95/1.93  tff(c_62, plain, (r2_hidden(k4_tarski('#skF_10', '#skF_9'), '#skF_8') | r2_hidden('#skF_11', k2_relset_1('#skF_7', '#skF_6', '#skF_8'))), inference(cnfTransformation, [status(thm)], [f_108])).
% 4.95/1.93  tff(c_2574, plain, (r2_hidden(k4_tarski('#skF_10', '#skF_9'), '#skF_8')), inference(negUnitSimplification, [status(thm)], [c_2504, c_62])).
% 4.95/1.93  tff(c_2578, plain, (r2_hidden('#skF_9', k2_relat_1('#skF_8'))), inference(resolution, [status(thm)], [c_2574, c_16])).
% 4.95/1.93  tff(c_2635, plain, (![A_548, B_549, C_550]: (k2_relset_1(A_548, B_549, C_550)=k2_relat_1(C_550) | ~m1_subset_1(C_550, k1_zfmisc_1(k2_zfmisc_1(A_548, B_549))))), inference(cnfTransformation, [status(thm)], [f_79])).
% 4.95/1.93  tff(c_2649, plain, (k2_relset_1('#skF_7', '#skF_6', '#skF_8')=k2_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_48, c_2635])).
% 4.95/1.93  tff(c_60, plain, (~r2_hidden('#skF_9', k2_relset_1('#skF_7', '#skF_6', '#skF_8')) | r2_hidden('#skF_11', k2_relset_1('#skF_7', '#skF_6', '#skF_8'))), inference(cnfTransformation, [status(thm)], [f_108])).
% 4.95/1.93  tff(c_2587, plain, (~r2_hidden('#skF_9', k2_relset_1('#skF_7', '#skF_6', '#skF_8'))), inference(negUnitSimplification, [status(thm)], [c_2504, c_60])).
% 4.95/1.93  tff(c_2650, plain, (~r2_hidden('#skF_9', k2_relat_1('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_2649, c_2587])).
% 4.95/1.93  tff(c_2654, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2578, c_2650])).
% 4.95/1.93  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.95/1.93  
% 4.95/1.93  Inference rules
% 4.95/1.93  ----------------------
% 4.95/1.93  #Ref     : 0
% 4.95/1.93  #Sup     : 578
% 4.95/1.93  #Fact    : 0
% 4.95/1.93  #Define  : 0
% 4.95/1.93  #Split   : 15
% 4.95/1.93  #Chain   : 0
% 4.95/1.93  #Close   : 0
% 4.95/1.93  
% 4.95/1.93  Ordering : KBO
% 4.95/1.93  
% 4.95/1.93  Simplification rules
% 4.95/1.93  ----------------------
% 4.95/1.93  #Subsume      : 30
% 4.95/1.93  #Demod        : 85
% 4.95/1.93  #Tautology    : 65
% 4.95/1.93  #SimpNegUnit  : 2
% 4.95/1.93  #BackRed      : 13
% 4.95/1.93  
% 4.95/1.93  #Partial instantiations: 0
% 4.95/1.93  #Strategies tried      : 1
% 4.95/1.93  
% 4.95/1.93  Timing (in seconds)
% 4.95/1.93  ----------------------
% 4.95/1.93  Preprocessing        : 0.32
% 4.95/1.93  Parsing              : 0.17
% 4.95/1.93  CNF conversion       : 0.03
% 4.95/1.93  Main loop            : 0.75
% 4.95/1.93  Inferencing          : 0.29
% 4.95/1.93  Reduction            : 0.21
% 4.95/1.93  Demodulation         : 0.13
% 4.95/1.93  BG Simplification    : 0.04
% 4.95/1.93  Subsumption          : 0.14
% 4.95/1.93  Abstraction          : 0.04
% 4.95/1.93  MUC search           : 0.00
% 4.95/1.93  Cooper               : 0.00
% 4.95/1.93  Total                : 1.12
% 4.95/1.93  Index Insertion      : 0.00
% 4.95/1.93  Index Deletion       : 0.00
% 4.95/1.93  Index Matching       : 0.00
% 4.95/1.93  BG Taut test         : 0.00
%------------------------------------------------------------------------------
