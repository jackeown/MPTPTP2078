%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:10:56 EST 2020

% Result     : Theorem 5.16s
% Output     : CNFRefutation 5.34s
% Verified   : 
% Statistics : Number of formulae       :  141 ( 860 expanded)
%              Number of leaves         :   35 ( 283 expanded)
%              Depth                    :   16
%              Number of atoms          :  241 (2207 expanded)
%              Number of equality atoms :   62 ( 393 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k3_mcart_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_mcart_1,type,(
    k3_mcart_1: ( $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_124,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_relat_1(B)
          & v1_funct_1(B) )
       => ( r1_tarski(k2_relat_1(B),A)
         => ( v1_funct_1(B)
            & v1_funct_2(B,k1_relat_1(B),A)
            & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B),A))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_funct_2)).

tff(f_32,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_64,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( ( r1_tarski(k1_relat_1(C),A)
          & r1_tarski(k2_relat_1(C),B) )
       => m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_relset_1)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_80,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] :
            ~ ( r2_hidden(B,A)
              & ! [C,D,E] :
                  ~ ( ( r2_hidden(C,A)
                      | r2_hidden(D,A) )
                    & B = k3_mcart_1(C,D,E) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_mcart_1)).

tff(f_42,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_49,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

tff(f_56,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_98,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( ( ( B = k1_xboole_0
           => A = k1_xboole_0 )
         => ( v1_funct_2(C,A,B)
          <=> A = k1_relset_1(A,B,C) ) )
        & ( B = k1_xboole_0
         => ( A = k1_xboole_0
            | ( v1_funct_2(C,A,B)
            <=> C = k1_xboole_0 ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).

tff(f_38,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_111,axiom,(
    ! [A,B] :
    ? [C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
      & v1_relat_1(C)
      & v4_relat_1(C,A)
      & v5_relat_1(C,B)
      & v1_funct_1(C)
      & v1_funct_2(C,A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc1_funct_2)).

tff(f_52,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(c_66,plain,(
    v1_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_8,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_62,plain,(
    r1_tarski(k2_relat_1('#skF_4'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_3339,plain,(
    ! [C_449,A_450,B_451] :
      ( m1_subset_1(C_449,k1_zfmisc_1(k2_zfmisc_1(A_450,B_451)))
      | ~ r1_tarski(k2_relat_1(C_449),B_451)
      | ~ r1_tarski(k1_relat_1(C_449),A_450)
      | ~ v1_relat_1(C_449) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_30,plain,(
    ! [A_16] :
      ( r2_hidden('#skF_1'(A_16),A_16)
      | k1_xboole_0 = A_16 ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_18,plain,(
    ! [A_5,B_6] :
      ( m1_subset_1(A_5,k1_zfmisc_1(B_6))
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_181,plain,(
    ! [C_66,B_67,A_68] :
      ( ~ v1_xboole_0(C_66)
      | ~ m1_subset_1(B_67,k1_zfmisc_1(C_66))
      | ~ r2_hidden(A_68,B_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_342,plain,(
    ! [B_90,A_91,A_92] :
      ( ~ v1_xboole_0(B_90)
      | ~ r2_hidden(A_91,A_92)
      | ~ r1_tarski(A_92,B_90) ) ),
    inference(resolution,[status(thm)],[c_18,c_181])).

tff(c_346,plain,(
    ! [B_93,A_94] :
      ( ~ v1_xboole_0(B_93)
      | ~ r1_tarski(A_94,B_93)
      | k1_xboole_0 = A_94 ) ),
    inference(resolution,[status(thm)],[c_30,c_342])).

tff(c_357,plain,
    ( ~ v1_xboole_0('#skF_3')
    | k2_relat_1('#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_62,c_346])).

tff(c_381,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_357])).

tff(c_64,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_60,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'),'#skF_3')))
    | ~ v1_funct_2('#skF_4',k1_relat_1('#skF_4'),'#skF_3')
    | ~ v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_68,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'),'#skF_3')))
    | ~ v1_funct_2('#skF_4',k1_relat_1('#skF_4'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_60])).

tff(c_105,plain,(
    ~ v1_funct_2('#skF_4',k1_relat_1('#skF_4'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_68])).

tff(c_382,plain,(
    ! [C_99,A_100,B_101] :
      ( m1_subset_1(C_99,k1_zfmisc_1(k2_zfmisc_1(A_100,B_101)))
      | ~ r1_tarski(k2_relat_1(C_99),B_101)
      | ~ r1_tarski(k1_relat_1(C_99),A_100)
      | ~ v1_relat_1(C_99) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_16,plain,(
    ! [A_5,B_6] :
      ( r1_tarski(A_5,B_6)
      | ~ m1_subset_1(A_5,k1_zfmisc_1(B_6)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_712,plain,(
    ! [C_153,A_154,B_155] :
      ( r1_tarski(C_153,k2_zfmisc_1(A_154,B_155))
      | ~ r1_tarski(k2_relat_1(C_153),B_155)
      | ~ r1_tarski(k1_relat_1(C_153),A_154)
      | ~ v1_relat_1(C_153) ) ),
    inference(resolution,[status(thm)],[c_382,c_16])).

tff(c_714,plain,(
    ! [A_154] :
      ( r1_tarski('#skF_4',k2_zfmisc_1(A_154,'#skF_3'))
      | ~ r1_tarski(k1_relat_1('#skF_4'),A_154)
      | ~ v1_relat_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_62,c_712])).

tff(c_726,plain,(
    ! [A_156] :
      ( r1_tarski('#skF_4',k2_zfmisc_1(A_156,'#skF_3'))
      | ~ r1_tarski(k1_relat_1('#skF_4'),A_156) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_714])).

tff(c_731,plain,(
    r1_tarski('#skF_4',k2_zfmisc_1(k1_relat_1('#skF_4'),'#skF_3')) ),
    inference(resolution,[status(thm)],[c_8,c_726])).

tff(c_359,plain,(
    ! [A_95,B_96,C_97] :
      ( k1_relset_1(A_95,B_96,C_97) = k1_relat_1(C_97)
      | ~ m1_subset_1(C_97,k1_zfmisc_1(k2_zfmisc_1(A_95,B_96))) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_374,plain,(
    ! [A_95,B_96,A_5] :
      ( k1_relset_1(A_95,B_96,A_5) = k1_relat_1(A_5)
      | ~ r1_tarski(A_5,k2_zfmisc_1(A_95,B_96)) ) ),
    inference(resolution,[status(thm)],[c_18,c_359])).

tff(c_740,plain,(
    k1_relset_1(k1_relat_1('#skF_4'),'#skF_3','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_731,c_374])).

tff(c_477,plain,(
    ! [B_118,C_119,A_120] :
      ( k1_xboole_0 = B_118
      | v1_funct_2(C_119,A_120,B_118)
      | k1_relset_1(A_120,B_118,C_119) != A_120
      | ~ m1_subset_1(C_119,k1_zfmisc_1(k2_zfmisc_1(A_120,B_118))) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_1284,plain,(
    ! [B_201,A_202,A_203] :
      ( k1_xboole_0 = B_201
      | v1_funct_2(A_202,A_203,B_201)
      | k1_relset_1(A_203,B_201,A_202) != A_203
      | ~ r1_tarski(A_202,k2_zfmisc_1(A_203,B_201)) ) ),
    inference(resolution,[status(thm)],[c_18,c_477])).

tff(c_1293,plain,
    ( k1_xboole_0 = '#skF_3'
    | v1_funct_2('#skF_4',k1_relat_1('#skF_4'),'#skF_3')
    | k1_relset_1(k1_relat_1('#skF_4'),'#skF_3','#skF_4') != k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_731,c_1284])).

tff(c_1311,plain,
    ( k1_xboole_0 = '#skF_3'
    | v1_funct_2('#skF_4',k1_relat_1('#skF_4'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_740,c_1293])).

tff(c_1312,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_105,c_1311])).

tff(c_1372,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1312,c_2])).

tff(c_1374,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_381,c_1372])).

tff(c_1376,plain,(
    v1_xboole_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_357])).

tff(c_358,plain,(
    ! [B_2] :
      ( ~ v1_xboole_0(B_2)
      | k1_xboole_0 = B_2 ) ),
    inference(resolution,[status(thm)],[c_8,c_346])).

tff(c_1380,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_1376,c_358])).

tff(c_1375,plain,(
    k2_relat_1('#skF_4') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_357])).

tff(c_1407,plain,(
    k2_relat_1('#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1380,c_1375])).

tff(c_152,plain,(
    ! [B_62,A_63] :
      ( B_62 = A_63
      | ~ r1_tarski(B_62,A_63)
      | ~ r1_tarski(A_63,B_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_163,plain,
    ( k2_relat_1('#skF_4') = '#skF_3'
    | ~ r1_tarski('#skF_3',k2_relat_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_62,c_152])).

tff(c_180,plain,(
    ~ r1_tarski('#skF_3',k2_relat_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_163])).

tff(c_1408,plain,(
    ~ r1_tarski('#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1407,c_180])).

tff(c_1412,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_1408])).

tff(c_1413,plain,(
    k2_relat_1('#skF_4') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_163])).

tff(c_1657,plain,(
    ! [C_252,A_253,B_254] :
      ( m1_subset_1(C_252,k1_zfmisc_1(k2_zfmisc_1(A_253,B_254)))
      | ~ r1_tarski(k2_relat_1(C_252),B_254)
      | ~ r1_tarski(k1_relat_1(C_252),A_253)
      | ~ v1_relat_1(C_252) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_1914,plain,(
    ! [C_290,A_291,B_292] :
      ( r1_tarski(C_290,k2_zfmisc_1(A_291,B_292))
      | ~ r1_tarski(k2_relat_1(C_290),B_292)
      | ~ r1_tarski(k1_relat_1(C_290),A_291)
      | ~ v1_relat_1(C_290) ) ),
    inference(resolution,[status(thm)],[c_1657,c_16])).

tff(c_2139,plain,(
    ! [C_319,A_320] :
      ( r1_tarski(C_319,k2_zfmisc_1(A_320,k2_relat_1(C_319)))
      | ~ r1_tarski(k1_relat_1(C_319),A_320)
      | ~ v1_relat_1(C_319) ) ),
    inference(resolution,[status(thm)],[c_8,c_1914])).

tff(c_2159,plain,(
    ! [A_320] :
      ( r1_tarski('#skF_4',k2_zfmisc_1(A_320,'#skF_3'))
      | ~ r1_tarski(k1_relat_1('#skF_4'),A_320)
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1413,c_2139])).

tff(c_2190,plain,(
    ! [A_322] :
      ( r1_tarski('#skF_4',k2_zfmisc_1(A_322,'#skF_3'))
      | ~ r1_tarski(k1_relat_1('#skF_4'),A_322) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_2159])).

tff(c_2200,plain,(
    r1_tarski('#skF_4',k2_zfmisc_1(k1_relat_1('#skF_4'),'#skF_3')) ),
    inference(resolution,[status(thm)],[c_8,c_2190])).

tff(c_1623,plain,(
    ! [A_240,B_241,C_242] :
      ( k1_relset_1(A_240,B_241,C_242) = k1_relat_1(C_242)
      | ~ m1_subset_1(C_242,k1_zfmisc_1(k2_zfmisc_1(A_240,B_241))) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_1638,plain,(
    ! [A_240,B_241,A_5] :
      ( k1_relset_1(A_240,B_241,A_5) = k1_relat_1(A_5)
      | ~ r1_tarski(A_5,k2_zfmisc_1(A_240,B_241)) ) ),
    inference(resolution,[status(thm)],[c_18,c_1623])).

tff(c_2209,plain,(
    k1_relset_1(k1_relat_1('#skF_4'),'#skF_3','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_2200,c_1638])).

tff(c_1751,plain,(
    ! [B_267,C_268,A_269] :
      ( k1_xboole_0 = B_267
      | v1_funct_2(C_268,A_269,B_267)
      | k1_relset_1(A_269,B_267,C_268) != A_269
      | ~ m1_subset_1(C_268,k1_zfmisc_1(k2_zfmisc_1(A_269,B_267))) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_2212,plain,(
    ! [B_323,A_324,A_325] :
      ( k1_xboole_0 = B_323
      | v1_funct_2(A_324,A_325,B_323)
      | k1_relset_1(A_325,B_323,A_324) != A_325
      | ~ r1_tarski(A_324,k2_zfmisc_1(A_325,B_323)) ) ),
    inference(resolution,[status(thm)],[c_18,c_1751])).

tff(c_2215,plain,
    ( k1_xboole_0 = '#skF_3'
    | v1_funct_2('#skF_4',k1_relat_1('#skF_4'),'#skF_3')
    | k1_relset_1(k1_relat_1('#skF_4'),'#skF_3','#skF_4') != k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_2200,c_2212])).

tff(c_2240,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relset_1(k1_relat_1('#skF_4'),'#skF_3','#skF_4') != k1_relat_1('#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_105,c_2215])).

tff(c_2267,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2209,c_2240])).

tff(c_12,plain,(
    ! [A_3] : k2_zfmisc_1(A_3,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_1882,plain,(
    ! [C_285,A_286] :
      ( m1_subset_1(C_285,k1_zfmisc_1(k1_xboole_0))
      | ~ r1_tarski(k2_relat_1(C_285),k1_xboole_0)
      | ~ r1_tarski(k1_relat_1(C_285),A_286)
      | ~ v1_relat_1(C_285) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_1657])).

tff(c_1884,plain,(
    ! [A_286] :
      ( m1_subset_1('#skF_4',k1_zfmisc_1(k1_xboole_0))
      | ~ r1_tarski('#skF_3',k1_xboole_0)
      | ~ r1_tarski(k1_relat_1('#skF_4'),A_286)
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1413,c_1882])).

tff(c_1888,plain,(
    ! [A_286] :
      ( m1_subset_1('#skF_4',k1_zfmisc_1(k1_xboole_0))
      | ~ r1_tarski('#skF_3',k1_xboole_0)
      | ~ r1_tarski(k1_relat_1('#skF_4'),A_286) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_1884])).

tff(c_1891,plain,(
    ~ r1_tarski('#skF_3',k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_1888])).

tff(c_2280,plain,(
    ~ r1_tarski('#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2267,c_1891])).

tff(c_2319,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_2280])).

tff(c_2321,plain,(
    r1_tarski('#skF_3',k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_1888])).

tff(c_1422,plain,(
    ! [C_204,B_205,A_206] :
      ( ~ v1_xboole_0(C_204)
      | ~ m1_subset_1(B_205,k1_zfmisc_1(C_204))
      | ~ r2_hidden(A_206,B_205) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_1593,plain,(
    ! [B_232,A_233,A_234] :
      ( ~ v1_xboole_0(B_232)
      | ~ r2_hidden(A_233,A_234)
      | ~ r1_tarski(A_234,B_232) ) ),
    inference(resolution,[status(thm)],[c_18,c_1422])).

tff(c_1596,plain,(
    ! [B_232,A_16] :
      ( ~ v1_xboole_0(B_232)
      | ~ r1_tarski(A_16,B_232)
      | k1_xboole_0 = A_16 ) ),
    inference(resolution,[status(thm)],[c_30,c_1593])).

tff(c_2328,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_2321,c_1596])).

tff(c_2335,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_2328])).

tff(c_2849,plain,(
    ! [A_360] :
      ( r2_hidden('#skF_1'(A_360),A_360)
      | A_360 = '#skF_3' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2335,c_30])).

tff(c_2373,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2335,c_2])).

tff(c_2320,plain,(
    ! [A_286] :
      ( ~ r1_tarski(k1_relat_1('#skF_4'),A_286)
      | m1_subset_1('#skF_4',k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(splitRight,[status(thm)],[c_1888])).

tff(c_2405,plain,(
    ! [A_286] :
      ( ~ r1_tarski(k1_relat_1('#skF_4'),A_286)
      | m1_subset_1('#skF_4',k1_zfmisc_1('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2335,c_2320])).

tff(c_2550,plain,(
    ! [A_338] : ~ r1_tarski(k1_relat_1('#skF_4'),A_338) ),
    inference(splitLeft,[status(thm)],[c_2405])).

tff(c_2555,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_8,c_2550])).

tff(c_2556,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_2405])).

tff(c_20,plain,(
    ! [C_9,B_8,A_7] :
      ( ~ v1_xboole_0(C_9)
      | ~ m1_subset_1(B_8,k1_zfmisc_1(C_9))
      | ~ r2_hidden(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_2562,plain,(
    ! [A_7] :
      ( ~ v1_xboole_0('#skF_3')
      | ~ r2_hidden(A_7,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_2556,c_20])).

tff(c_2568,plain,(
    ! [A_7] : ~ r2_hidden(A_7,'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2373,c_2562])).

tff(c_2864,plain,(
    '#skF_3' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_2849,c_2568])).

tff(c_2569,plain,(
    r1_tarski('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_2556,c_16])).

tff(c_4,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_2573,plain,
    ( '#skF_3' = '#skF_4'
    | ~ r1_tarski('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_2569,c_4])).

tff(c_2843,plain,(
    ~ r1_tarski('#skF_3','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_2573])).

tff(c_2870,plain,(
    ~ r1_tarski('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2864,c_2843])).

tff(c_2900,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_2870])).

tff(c_2901,plain,(
    '#skF_3' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_2573])).

tff(c_129,plain,(
    ! [A_56,B_57] : m1_subset_1('#skF_2'(A_56,B_57),k1_zfmisc_1(k2_zfmisc_1(A_56,B_57))) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_138,plain,(
    ! [A_3] : m1_subset_1('#skF_2'(A_3,k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_129])).

tff(c_1424,plain,(
    ! [A_206,A_3] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | ~ r2_hidden(A_206,'#skF_2'(A_3,k1_xboole_0)) ) ),
    inference(resolution,[status(thm)],[c_138,c_1422])).

tff(c_1439,plain,(
    ! [A_207,A_208] : ~ r2_hidden(A_207,'#skF_2'(A_208,k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_1424])).

tff(c_1444,plain,(
    ! [A_208] : '#skF_2'(A_208,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_30,c_1439])).

tff(c_2574,plain,(
    ! [A_342] : '#skF_2'(A_342,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2335,c_2335,c_1444])).

tff(c_48,plain,(
    ! [A_33,B_34] : v1_funct_2('#skF_2'(A_33,B_34),A_33,B_34) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_2594,plain,(
    ! [A_342] : v1_funct_2('#skF_3',A_342,'#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_2574,c_48])).

tff(c_2905,plain,(
    ! [A_342] : v1_funct_2('#skF_4',A_342,'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2901,c_2901,c_2594])).

tff(c_24,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_2372,plain,(
    k1_relat_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2335,c_2335,c_24])).

tff(c_2920,plain,(
    k1_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2901,c_2901,c_2372])).

tff(c_2928,plain,(
    ~ v1_funct_2('#skF_4',k1_relat_1('#skF_4'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2901,c_105])).

tff(c_2959,plain,(
    ~ v1_funct_2('#skF_4','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2920,c_2928])).

tff(c_2992,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2905,c_2959])).

tff(c_2993,plain,(
    ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'),'#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_68])).

tff(c_3347,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_4'),'#skF_3')
    | ~ r1_tarski(k1_relat_1('#skF_4'),k1_relat_1('#skF_4'))
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_3339,c_2993])).

tff(c_3362,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_8,c_62,c_3347])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:23:32 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.16/1.96  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.16/1.97  
% 5.16/1.97  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.16/1.97  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k3_mcart_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2
% 5.16/1.97  
% 5.16/1.97  %Foreground sorts:
% 5.16/1.97  
% 5.16/1.97  
% 5.16/1.97  %Background operators:
% 5.16/1.97  
% 5.16/1.97  
% 5.16/1.97  %Foreground operators:
% 5.16/1.97  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 5.16/1.97  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.16/1.97  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.16/1.97  tff('#skF_1', type, '#skF_1': $i > $i).
% 5.16/1.97  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.16/1.97  tff(k3_mcart_1, type, k3_mcart_1: ($i * $i * $i) > $i).
% 5.16/1.97  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.16/1.97  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 5.16/1.97  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 5.16/1.97  tff('#skF_3', type, '#skF_3': $i).
% 5.16/1.97  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 5.16/1.97  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 5.16/1.97  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.16/1.97  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.16/1.97  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.16/1.97  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 5.16/1.97  tff('#skF_4', type, '#skF_4': $i).
% 5.16/1.97  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.16/1.97  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 5.16/1.97  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 5.16/1.97  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 5.16/1.97  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 5.16/1.97  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.16/1.97  
% 5.34/1.99  tff(f_124, negated_conjecture, ~(![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r1_tarski(k2_relat_1(B), A) => ((v1_funct_1(B) & v1_funct_2(B, k1_relat_1(B), A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B), A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_funct_2)).
% 5.34/1.99  tff(f_32, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 5.34/1.99  tff(f_64, axiom, (![A, B, C]: (v1_relat_1(C) => ((r1_tarski(k1_relat_1(C), A) & r1_tarski(k2_relat_1(C), B)) => m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_relset_1)).
% 5.34/1.99  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 5.34/1.99  tff(f_80, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~(r2_hidden(B, A) & (![C, D, E]: ~((r2_hidden(C, A) | r2_hidden(D, A)) & (B = k3_mcart_1(C, D, E)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_mcart_1)).
% 5.34/1.99  tff(f_42, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 5.34/1.99  tff(f_49, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_subset)).
% 5.34/1.99  tff(f_56, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 5.34/1.99  tff(f_98, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 5.34/1.99  tff(f_38, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 5.34/1.99  tff(f_111, axiom, (![A, B]: (?[C]: (((((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & v1_relat_1(C)) & v4_relat_1(C, A)) & v5_relat_1(C, B)) & v1_funct_1(C)) & v1_funct_2(C, A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', rc1_funct_2)).
% 5.34/1.99  tff(f_52, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 5.34/1.99  tff(c_66, plain, (v1_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_124])).
% 5.34/1.99  tff(c_8, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.34/1.99  tff(c_62, plain, (r1_tarski(k2_relat_1('#skF_4'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_124])).
% 5.34/1.99  tff(c_3339, plain, (![C_449, A_450, B_451]: (m1_subset_1(C_449, k1_zfmisc_1(k2_zfmisc_1(A_450, B_451))) | ~r1_tarski(k2_relat_1(C_449), B_451) | ~r1_tarski(k1_relat_1(C_449), A_450) | ~v1_relat_1(C_449))), inference(cnfTransformation, [status(thm)], [f_64])).
% 5.34/1.99  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 5.34/1.99  tff(c_30, plain, (![A_16]: (r2_hidden('#skF_1'(A_16), A_16) | k1_xboole_0=A_16)), inference(cnfTransformation, [status(thm)], [f_80])).
% 5.34/1.99  tff(c_18, plain, (![A_5, B_6]: (m1_subset_1(A_5, k1_zfmisc_1(B_6)) | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_42])).
% 5.34/1.99  tff(c_181, plain, (![C_66, B_67, A_68]: (~v1_xboole_0(C_66) | ~m1_subset_1(B_67, k1_zfmisc_1(C_66)) | ~r2_hidden(A_68, B_67))), inference(cnfTransformation, [status(thm)], [f_49])).
% 5.34/1.99  tff(c_342, plain, (![B_90, A_91, A_92]: (~v1_xboole_0(B_90) | ~r2_hidden(A_91, A_92) | ~r1_tarski(A_92, B_90))), inference(resolution, [status(thm)], [c_18, c_181])).
% 5.34/1.99  tff(c_346, plain, (![B_93, A_94]: (~v1_xboole_0(B_93) | ~r1_tarski(A_94, B_93) | k1_xboole_0=A_94)), inference(resolution, [status(thm)], [c_30, c_342])).
% 5.34/1.99  tff(c_357, plain, (~v1_xboole_0('#skF_3') | k2_relat_1('#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_62, c_346])).
% 5.34/1.99  tff(c_381, plain, (~v1_xboole_0('#skF_3')), inference(splitLeft, [status(thm)], [c_357])).
% 5.34/1.99  tff(c_64, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_124])).
% 5.34/1.99  tff(c_60, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'), '#skF_3'))) | ~v1_funct_2('#skF_4', k1_relat_1('#skF_4'), '#skF_3') | ~v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_124])).
% 5.34/1.99  tff(c_68, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'), '#skF_3'))) | ~v1_funct_2('#skF_4', k1_relat_1('#skF_4'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_60])).
% 5.34/1.99  tff(c_105, plain, (~v1_funct_2('#skF_4', k1_relat_1('#skF_4'), '#skF_3')), inference(splitLeft, [status(thm)], [c_68])).
% 5.34/1.99  tff(c_382, plain, (![C_99, A_100, B_101]: (m1_subset_1(C_99, k1_zfmisc_1(k2_zfmisc_1(A_100, B_101))) | ~r1_tarski(k2_relat_1(C_99), B_101) | ~r1_tarski(k1_relat_1(C_99), A_100) | ~v1_relat_1(C_99))), inference(cnfTransformation, [status(thm)], [f_64])).
% 5.34/1.99  tff(c_16, plain, (![A_5, B_6]: (r1_tarski(A_5, B_6) | ~m1_subset_1(A_5, k1_zfmisc_1(B_6)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 5.34/1.99  tff(c_712, plain, (![C_153, A_154, B_155]: (r1_tarski(C_153, k2_zfmisc_1(A_154, B_155)) | ~r1_tarski(k2_relat_1(C_153), B_155) | ~r1_tarski(k1_relat_1(C_153), A_154) | ~v1_relat_1(C_153))), inference(resolution, [status(thm)], [c_382, c_16])).
% 5.34/1.99  tff(c_714, plain, (![A_154]: (r1_tarski('#skF_4', k2_zfmisc_1(A_154, '#skF_3')) | ~r1_tarski(k1_relat_1('#skF_4'), A_154) | ~v1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_62, c_712])).
% 5.34/1.99  tff(c_726, plain, (![A_156]: (r1_tarski('#skF_4', k2_zfmisc_1(A_156, '#skF_3')) | ~r1_tarski(k1_relat_1('#skF_4'), A_156))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_714])).
% 5.34/1.99  tff(c_731, plain, (r1_tarski('#skF_4', k2_zfmisc_1(k1_relat_1('#skF_4'), '#skF_3'))), inference(resolution, [status(thm)], [c_8, c_726])).
% 5.34/1.99  tff(c_359, plain, (![A_95, B_96, C_97]: (k1_relset_1(A_95, B_96, C_97)=k1_relat_1(C_97) | ~m1_subset_1(C_97, k1_zfmisc_1(k2_zfmisc_1(A_95, B_96))))), inference(cnfTransformation, [status(thm)], [f_56])).
% 5.34/1.99  tff(c_374, plain, (![A_95, B_96, A_5]: (k1_relset_1(A_95, B_96, A_5)=k1_relat_1(A_5) | ~r1_tarski(A_5, k2_zfmisc_1(A_95, B_96)))), inference(resolution, [status(thm)], [c_18, c_359])).
% 5.34/1.99  tff(c_740, plain, (k1_relset_1(k1_relat_1('#skF_4'), '#skF_3', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_731, c_374])).
% 5.34/1.99  tff(c_477, plain, (![B_118, C_119, A_120]: (k1_xboole_0=B_118 | v1_funct_2(C_119, A_120, B_118) | k1_relset_1(A_120, B_118, C_119)!=A_120 | ~m1_subset_1(C_119, k1_zfmisc_1(k2_zfmisc_1(A_120, B_118))))), inference(cnfTransformation, [status(thm)], [f_98])).
% 5.34/1.99  tff(c_1284, plain, (![B_201, A_202, A_203]: (k1_xboole_0=B_201 | v1_funct_2(A_202, A_203, B_201) | k1_relset_1(A_203, B_201, A_202)!=A_203 | ~r1_tarski(A_202, k2_zfmisc_1(A_203, B_201)))), inference(resolution, [status(thm)], [c_18, c_477])).
% 5.34/1.99  tff(c_1293, plain, (k1_xboole_0='#skF_3' | v1_funct_2('#skF_4', k1_relat_1('#skF_4'), '#skF_3') | k1_relset_1(k1_relat_1('#skF_4'), '#skF_3', '#skF_4')!=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_731, c_1284])).
% 5.34/1.99  tff(c_1311, plain, (k1_xboole_0='#skF_3' | v1_funct_2('#skF_4', k1_relat_1('#skF_4'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_740, c_1293])).
% 5.34/1.99  tff(c_1312, plain, (k1_xboole_0='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_105, c_1311])).
% 5.34/1.99  tff(c_1372, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1312, c_2])).
% 5.34/1.99  tff(c_1374, plain, $false, inference(negUnitSimplification, [status(thm)], [c_381, c_1372])).
% 5.34/1.99  tff(c_1376, plain, (v1_xboole_0('#skF_3')), inference(splitRight, [status(thm)], [c_357])).
% 5.34/1.99  tff(c_358, plain, (![B_2]: (~v1_xboole_0(B_2) | k1_xboole_0=B_2)), inference(resolution, [status(thm)], [c_8, c_346])).
% 5.34/1.99  tff(c_1380, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_1376, c_358])).
% 5.34/1.99  tff(c_1375, plain, (k2_relat_1('#skF_4')=k1_xboole_0), inference(splitRight, [status(thm)], [c_357])).
% 5.34/1.99  tff(c_1407, plain, (k2_relat_1('#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1380, c_1375])).
% 5.34/1.99  tff(c_152, plain, (![B_62, A_63]: (B_62=A_63 | ~r1_tarski(B_62, A_63) | ~r1_tarski(A_63, B_62))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.34/1.99  tff(c_163, plain, (k2_relat_1('#skF_4')='#skF_3' | ~r1_tarski('#skF_3', k2_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_62, c_152])).
% 5.34/1.99  tff(c_180, plain, (~r1_tarski('#skF_3', k2_relat_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_163])).
% 5.34/1.99  tff(c_1408, plain, (~r1_tarski('#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1407, c_180])).
% 5.34/1.99  tff(c_1412, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_8, c_1408])).
% 5.34/1.99  tff(c_1413, plain, (k2_relat_1('#skF_4')='#skF_3'), inference(splitRight, [status(thm)], [c_163])).
% 5.34/1.99  tff(c_1657, plain, (![C_252, A_253, B_254]: (m1_subset_1(C_252, k1_zfmisc_1(k2_zfmisc_1(A_253, B_254))) | ~r1_tarski(k2_relat_1(C_252), B_254) | ~r1_tarski(k1_relat_1(C_252), A_253) | ~v1_relat_1(C_252))), inference(cnfTransformation, [status(thm)], [f_64])).
% 5.34/1.99  tff(c_1914, plain, (![C_290, A_291, B_292]: (r1_tarski(C_290, k2_zfmisc_1(A_291, B_292)) | ~r1_tarski(k2_relat_1(C_290), B_292) | ~r1_tarski(k1_relat_1(C_290), A_291) | ~v1_relat_1(C_290))), inference(resolution, [status(thm)], [c_1657, c_16])).
% 5.34/1.99  tff(c_2139, plain, (![C_319, A_320]: (r1_tarski(C_319, k2_zfmisc_1(A_320, k2_relat_1(C_319))) | ~r1_tarski(k1_relat_1(C_319), A_320) | ~v1_relat_1(C_319))), inference(resolution, [status(thm)], [c_8, c_1914])).
% 5.34/1.99  tff(c_2159, plain, (![A_320]: (r1_tarski('#skF_4', k2_zfmisc_1(A_320, '#skF_3')) | ~r1_tarski(k1_relat_1('#skF_4'), A_320) | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_1413, c_2139])).
% 5.34/1.99  tff(c_2190, plain, (![A_322]: (r1_tarski('#skF_4', k2_zfmisc_1(A_322, '#skF_3')) | ~r1_tarski(k1_relat_1('#skF_4'), A_322))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_2159])).
% 5.34/1.99  tff(c_2200, plain, (r1_tarski('#skF_4', k2_zfmisc_1(k1_relat_1('#skF_4'), '#skF_3'))), inference(resolution, [status(thm)], [c_8, c_2190])).
% 5.34/1.99  tff(c_1623, plain, (![A_240, B_241, C_242]: (k1_relset_1(A_240, B_241, C_242)=k1_relat_1(C_242) | ~m1_subset_1(C_242, k1_zfmisc_1(k2_zfmisc_1(A_240, B_241))))), inference(cnfTransformation, [status(thm)], [f_56])).
% 5.34/1.99  tff(c_1638, plain, (![A_240, B_241, A_5]: (k1_relset_1(A_240, B_241, A_5)=k1_relat_1(A_5) | ~r1_tarski(A_5, k2_zfmisc_1(A_240, B_241)))), inference(resolution, [status(thm)], [c_18, c_1623])).
% 5.34/1.99  tff(c_2209, plain, (k1_relset_1(k1_relat_1('#skF_4'), '#skF_3', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_2200, c_1638])).
% 5.34/1.99  tff(c_1751, plain, (![B_267, C_268, A_269]: (k1_xboole_0=B_267 | v1_funct_2(C_268, A_269, B_267) | k1_relset_1(A_269, B_267, C_268)!=A_269 | ~m1_subset_1(C_268, k1_zfmisc_1(k2_zfmisc_1(A_269, B_267))))), inference(cnfTransformation, [status(thm)], [f_98])).
% 5.34/1.99  tff(c_2212, plain, (![B_323, A_324, A_325]: (k1_xboole_0=B_323 | v1_funct_2(A_324, A_325, B_323) | k1_relset_1(A_325, B_323, A_324)!=A_325 | ~r1_tarski(A_324, k2_zfmisc_1(A_325, B_323)))), inference(resolution, [status(thm)], [c_18, c_1751])).
% 5.34/1.99  tff(c_2215, plain, (k1_xboole_0='#skF_3' | v1_funct_2('#skF_4', k1_relat_1('#skF_4'), '#skF_3') | k1_relset_1(k1_relat_1('#skF_4'), '#skF_3', '#skF_4')!=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_2200, c_2212])).
% 5.34/1.99  tff(c_2240, plain, (k1_xboole_0='#skF_3' | k1_relset_1(k1_relat_1('#skF_4'), '#skF_3', '#skF_4')!=k1_relat_1('#skF_4')), inference(negUnitSimplification, [status(thm)], [c_105, c_2215])).
% 5.34/1.99  tff(c_2267, plain, (k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_2209, c_2240])).
% 5.34/1.99  tff(c_12, plain, (![A_3]: (k2_zfmisc_1(A_3, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_38])).
% 5.34/1.99  tff(c_1882, plain, (![C_285, A_286]: (m1_subset_1(C_285, k1_zfmisc_1(k1_xboole_0)) | ~r1_tarski(k2_relat_1(C_285), k1_xboole_0) | ~r1_tarski(k1_relat_1(C_285), A_286) | ~v1_relat_1(C_285))), inference(superposition, [status(thm), theory('equality')], [c_12, c_1657])).
% 5.34/1.99  tff(c_1884, plain, (![A_286]: (m1_subset_1('#skF_4', k1_zfmisc_1(k1_xboole_0)) | ~r1_tarski('#skF_3', k1_xboole_0) | ~r1_tarski(k1_relat_1('#skF_4'), A_286) | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_1413, c_1882])).
% 5.34/1.99  tff(c_1888, plain, (![A_286]: (m1_subset_1('#skF_4', k1_zfmisc_1(k1_xboole_0)) | ~r1_tarski('#skF_3', k1_xboole_0) | ~r1_tarski(k1_relat_1('#skF_4'), A_286))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_1884])).
% 5.34/1.99  tff(c_1891, plain, (~r1_tarski('#skF_3', k1_xboole_0)), inference(splitLeft, [status(thm)], [c_1888])).
% 5.34/1.99  tff(c_2280, plain, (~r1_tarski('#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2267, c_1891])).
% 5.34/1.99  tff(c_2319, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_8, c_2280])).
% 5.34/1.99  tff(c_2321, plain, (r1_tarski('#skF_3', k1_xboole_0)), inference(splitRight, [status(thm)], [c_1888])).
% 5.34/1.99  tff(c_1422, plain, (![C_204, B_205, A_206]: (~v1_xboole_0(C_204) | ~m1_subset_1(B_205, k1_zfmisc_1(C_204)) | ~r2_hidden(A_206, B_205))), inference(cnfTransformation, [status(thm)], [f_49])).
% 5.34/1.99  tff(c_1593, plain, (![B_232, A_233, A_234]: (~v1_xboole_0(B_232) | ~r2_hidden(A_233, A_234) | ~r1_tarski(A_234, B_232))), inference(resolution, [status(thm)], [c_18, c_1422])).
% 5.34/1.99  tff(c_1596, plain, (![B_232, A_16]: (~v1_xboole_0(B_232) | ~r1_tarski(A_16, B_232) | k1_xboole_0=A_16)), inference(resolution, [status(thm)], [c_30, c_1593])).
% 5.34/1.99  tff(c_2328, plain, (~v1_xboole_0(k1_xboole_0) | k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_2321, c_1596])).
% 5.34/1.99  tff(c_2335, plain, (k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_2, c_2328])).
% 5.34/1.99  tff(c_2849, plain, (![A_360]: (r2_hidden('#skF_1'(A_360), A_360) | A_360='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2335, c_30])).
% 5.34/1.99  tff(c_2373, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2335, c_2])).
% 5.34/1.99  tff(c_2320, plain, (![A_286]: (~r1_tarski(k1_relat_1('#skF_4'), A_286) | m1_subset_1('#skF_4', k1_zfmisc_1(k1_xboole_0)))), inference(splitRight, [status(thm)], [c_1888])).
% 5.34/1.99  tff(c_2405, plain, (![A_286]: (~r1_tarski(k1_relat_1('#skF_4'), A_286) | m1_subset_1('#skF_4', k1_zfmisc_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_2335, c_2320])).
% 5.34/1.99  tff(c_2550, plain, (![A_338]: (~r1_tarski(k1_relat_1('#skF_4'), A_338))), inference(splitLeft, [status(thm)], [c_2405])).
% 5.34/1.99  tff(c_2555, plain, $false, inference(resolution, [status(thm)], [c_8, c_2550])).
% 5.34/1.99  tff(c_2556, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_3'))), inference(splitRight, [status(thm)], [c_2405])).
% 5.34/1.99  tff(c_20, plain, (![C_9, B_8, A_7]: (~v1_xboole_0(C_9) | ~m1_subset_1(B_8, k1_zfmisc_1(C_9)) | ~r2_hidden(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_49])).
% 5.34/1.99  tff(c_2562, plain, (![A_7]: (~v1_xboole_0('#skF_3') | ~r2_hidden(A_7, '#skF_4'))), inference(resolution, [status(thm)], [c_2556, c_20])).
% 5.34/1.99  tff(c_2568, plain, (![A_7]: (~r2_hidden(A_7, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_2373, c_2562])).
% 5.34/1.99  tff(c_2864, plain, ('#skF_3'='#skF_4'), inference(resolution, [status(thm)], [c_2849, c_2568])).
% 5.34/1.99  tff(c_2569, plain, (r1_tarski('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_2556, c_16])).
% 5.34/1.99  tff(c_4, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.34/1.99  tff(c_2573, plain, ('#skF_3'='#skF_4' | ~r1_tarski('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_2569, c_4])).
% 5.34/1.99  tff(c_2843, plain, (~r1_tarski('#skF_3', '#skF_4')), inference(splitLeft, [status(thm)], [c_2573])).
% 5.34/1.99  tff(c_2870, plain, (~r1_tarski('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2864, c_2843])).
% 5.34/1.99  tff(c_2900, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_8, c_2870])).
% 5.34/1.99  tff(c_2901, plain, ('#skF_3'='#skF_4'), inference(splitRight, [status(thm)], [c_2573])).
% 5.34/1.99  tff(c_129, plain, (![A_56, B_57]: (m1_subset_1('#skF_2'(A_56, B_57), k1_zfmisc_1(k2_zfmisc_1(A_56, B_57))))), inference(cnfTransformation, [status(thm)], [f_111])).
% 5.34/1.99  tff(c_138, plain, (![A_3]: (m1_subset_1('#skF_2'(A_3, k1_xboole_0), k1_zfmisc_1(k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_129])).
% 5.34/1.99  tff(c_1424, plain, (![A_206, A_3]: (~v1_xboole_0(k1_xboole_0) | ~r2_hidden(A_206, '#skF_2'(A_3, k1_xboole_0)))), inference(resolution, [status(thm)], [c_138, c_1422])).
% 5.34/1.99  tff(c_1439, plain, (![A_207, A_208]: (~r2_hidden(A_207, '#skF_2'(A_208, k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_1424])).
% 5.34/1.99  tff(c_1444, plain, (![A_208]: ('#skF_2'(A_208, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_30, c_1439])).
% 5.34/1.99  tff(c_2574, plain, (![A_342]: ('#skF_2'(A_342, '#skF_3')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2335, c_2335, c_1444])).
% 5.34/1.99  tff(c_48, plain, (![A_33, B_34]: (v1_funct_2('#skF_2'(A_33, B_34), A_33, B_34))), inference(cnfTransformation, [status(thm)], [f_111])).
% 5.34/1.99  tff(c_2594, plain, (![A_342]: (v1_funct_2('#skF_3', A_342, '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_2574, c_48])).
% 5.34/1.99  tff(c_2905, plain, (![A_342]: (v1_funct_2('#skF_4', A_342, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_2901, c_2901, c_2594])).
% 5.34/1.99  tff(c_24, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_52])).
% 5.34/1.99  tff(c_2372, plain, (k1_relat_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_2335, c_2335, c_24])).
% 5.34/1.99  tff(c_2920, plain, (k1_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_2901, c_2901, c_2372])).
% 5.34/1.99  tff(c_2928, plain, (~v1_funct_2('#skF_4', k1_relat_1('#skF_4'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2901, c_105])).
% 5.34/1.99  tff(c_2959, plain, (~v1_funct_2('#skF_4', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2920, c_2928])).
% 5.34/1.99  tff(c_2992, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2905, c_2959])).
% 5.34/1.99  tff(c_2993, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'), '#skF_3')))), inference(splitRight, [status(thm)], [c_68])).
% 5.34/1.99  tff(c_3347, plain, (~r1_tarski(k2_relat_1('#skF_4'), '#skF_3') | ~r1_tarski(k1_relat_1('#skF_4'), k1_relat_1('#skF_4')) | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_3339, c_2993])).
% 5.34/1.99  tff(c_3362, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_66, c_8, c_62, c_3347])).
% 5.34/1.99  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.34/1.99  
% 5.34/1.99  Inference rules
% 5.34/1.99  ----------------------
% 5.34/1.99  #Ref     : 0
% 5.34/1.99  #Sup     : 674
% 5.34/1.99  #Fact    : 0
% 5.34/1.99  #Define  : 0
% 5.34/1.99  #Split   : 18
% 5.34/1.99  #Chain   : 0
% 5.34/1.99  #Close   : 0
% 5.34/1.99  
% 5.34/1.99  Ordering : KBO
% 5.34/1.99  
% 5.34/1.99  Simplification rules
% 5.34/1.99  ----------------------
% 5.34/1.99  #Subsume      : 64
% 5.34/1.99  #Demod        : 981
% 5.34/1.99  #Tautology    : 371
% 5.34/1.99  #SimpNegUnit  : 3
% 5.34/1.99  #BackRed      : 239
% 5.34/1.99  
% 5.34/1.99  #Partial instantiations: 0
% 5.34/1.99  #Strategies tried      : 1
% 5.34/1.99  
% 5.34/1.99  Timing (in seconds)
% 5.34/1.99  ----------------------
% 5.34/1.99  Preprocessing        : 0.34
% 5.34/1.99  Parsing              : 0.18
% 5.34/2.00  CNF conversion       : 0.02
% 5.34/2.00  Main loop            : 0.84
% 5.34/2.00  Inferencing          : 0.28
% 5.34/2.00  Reduction            : 0.30
% 5.34/2.00  Demodulation         : 0.20
% 5.34/2.00  BG Simplification    : 0.04
% 5.34/2.00  Subsumption          : 0.16
% 5.34/2.00  Abstraction          : 0.04
% 5.34/2.00  MUC search           : 0.00
% 5.34/2.00  Cooper               : 0.00
% 5.34/2.00  Total                : 1.23
% 5.34/2.00  Index Insertion      : 0.00
% 5.34/2.00  Index Deletion       : 0.00
% 5.34/2.00  Index Matching       : 0.00
% 5.34/2.00  BG Taut test         : 0.00
%------------------------------------------------------------------------------
