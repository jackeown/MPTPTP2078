%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:17:18 EST 2020

% Result     : Theorem 4.70s
% Output     : CNFRefutation 4.70s
% Verified   : 
% Statistics : Number of formulae       :   94 ( 139 expanded)
%              Number of leaves         :   40 (  65 expanded)
%              Depth                    :    6
%              Number of atoms          :  141 ( 368 expanded)
%              Number of equality atoms :   27 (  44 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v1_partfun1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k8_relset_1 > k7_relset_1 > k1_relset_1 > k9_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k8_relset_1,type,(
    k8_relset_1: ( $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k7_relset_1,type,(
    k7_relset_1: ( $i * $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff(v1_partfun1,type,(
    v1_partfun1: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_160,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B] :
            ( ~ v1_xboole_0(B)
           => ! [C] :
                ( ( v1_funct_1(C)
                  & v1_funct_2(C,A,B)
                  & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
               => ! [D] :
                    ( m1_subset_1(D,k1_zfmisc_1(A))
                   => ! [E] :
                        ( m1_subset_1(E,k1_zfmisc_1(B))
                       => ( r1_tarski(k7_relset_1(A,B,C,D),E)
                        <=> r1_tarski(D,k8_relset_1(A,B,C,E)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t172_funct_2)).

tff(f_92,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k8_relset_1(A,B,C,D) = k10_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

tff(f_80,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_55,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r1_tarski(A,B)
       => r1_tarski(k9_relat_1(C,A),k9_relat_1(C,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t156_relat_1)).

tff(f_61,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => r1_tarski(k9_relat_1(B,k10_relat_1(B,A)),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t145_funct_1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_88,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_84,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_135,axiom,(
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

tff(f_71,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( ( r1_tarski(A,k1_relat_1(C))
          & r1_tarski(k9_relat_1(C,A),B) )
       => r1_tarski(A,k10_relat_1(C,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t163_funct_1)).

tff(f_39,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_76,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

tff(c_64,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_58,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_1874,plain,(
    ! [A_328,B_329,C_330,D_331] :
      ( k8_relset_1(A_328,B_329,C_330,D_331) = k10_relat_1(C_330,D_331)
      | ~ m1_subset_1(C_330,k1_zfmisc_1(k2_zfmisc_1(A_328,B_329))) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_1885,plain,(
    ! [D_331] : k8_relset_1('#skF_2','#skF_3','#skF_4',D_331) = k10_relat_1('#skF_4',D_331) ),
    inference(resolution,[status(thm)],[c_58,c_1874])).

tff(c_149,plain,(
    ! [C_89,A_90,B_91] :
      ( v1_relat_1(C_89)
      | ~ m1_subset_1(C_89,k1_zfmisc_1(k2_zfmisc_1(A_90,B_91))) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_162,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_58,c_149])).

tff(c_728,plain,(
    ! [A_167,B_168,C_169,D_170] :
      ( k8_relset_1(A_167,B_168,C_169,D_170) = k10_relat_1(C_169,D_170)
      | ~ m1_subset_1(C_169,k1_zfmisc_1(k2_zfmisc_1(A_167,B_168))) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_739,plain,(
    ! [D_170] : k8_relset_1('#skF_2','#skF_3','#skF_4',D_170) = k10_relat_1('#skF_4',D_170) ),
    inference(resolution,[status(thm)],[c_58,c_728])).

tff(c_68,plain,
    ( ~ r1_tarski('#skF_5',k8_relset_1('#skF_2','#skF_3','#skF_4','#skF_6'))
    | ~ r1_tarski(k7_relset_1('#skF_2','#skF_3','#skF_4','#skF_5'),'#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_132,plain,(
    ~ r1_tarski(k7_relset_1('#skF_2','#skF_3','#skF_4','#skF_5'),'#skF_6') ),
    inference(splitLeft,[status(thm)],[c_68])).

tff(c_74,plain,
    ( r1_tarski(k7_relset_1('#skF_2','#skF_3','#skF_4','#skF_5'),'#skF_6')
    | r1_tarski('#skF_5',k8_relset_1('#skF_2','#skF_3','#skF_4','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_188,plain,(
    r1_tarski('#skF_5',k8_relset_1('#skF_2','#skF_3','#skF_4','#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_132,c_74])).

tff(c_743,plain,(
    r1_tarski('#skF_5',k10_relat_1('#skF_4','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_739,c_188])).

tff(c_62,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_20,plain,(
    ! [C_15,A_13,B_14] :
      ( r1_tarski(k9_relat_1(C_15,A_13),k9_relat_1(C_15,B_14))
      | ~ r1_tarski(A_13,B_14)
      | ~ v1_relat_1(C_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_268,plain,(
    ! [B_108,A_109] :
      ( r1_tarski(k9_relat_1(B_108,k10_relat_1(B_108,A_109)),A_109)
      | ~ v1_funct_1(B_108)
      | ~ v1_relat_1(B_108) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_6,plain,(
    ! [A_5,C_7,B_6] :
      ( r1_tarski(A_5,C_7)
      | ~ r1_tarski(B_6,C_7)
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_1179,plain,(
    ! [A_241,A_242,B_243] :
      ( r1_tarski(A_241,A_242)
      | ~ r1_tarski(A_241,k9_relat_1(B_243,k10_relat_1(B_243,A_242)))
      | ~ v1_funct_1(B_243)
      | ~ v1_relat_1(B_243) ) ),
    inference(resolution,[status(thm)],[c_268,c_6])).

tff(c_1201,plain,(
    ! [C_244,A_245,A_246] :
      ( r1_tarski(k9_relat_1(C_244,A_245),A_246)
      | ~ v1_funct_1(C_244)
      | ~ r1_tarski(A_245,k10_relat_1(C_244,A_246))
      | ~ v1_relat_1(C_244) ) ),
    inference(resolution,[status(thm)],[c_20,c_1179])).

tff(c_768,plain,(
    ! [A_173,B_174,C_175,D_176] :
      ( k7_relset_1(A_173,B_174,C_175,D_176) = k9_relat_1(C_175,D_176)
      | ~ m1_subset_1(C_175,k1_zfmisc_1(k2_zfmisc_1(A_173,B_174))) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_779,plain,(
    ! [D_176] : k7_relset_1('#skF_2','#skF_3','#skF_4',D_176) = k9_relat_1('#skF_4',D_176) ),
    inference(resolution,[status(thm)],[c_58,c_768])).

tff(c_780,plain,(
    ~ r1_tarski(k9_relat_1('#skF_4','#skF_5'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_779,c_132])).

tff(c_1238,plain,
    ( ~ v1_funct_1('#skF_4')
    | ~ r1_tarski('#skF_5',k10_relat_1('#skF_4','#skF_6'))
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_1201,c_780])).

tff(c_1302,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_162,c_743,c_62,c_1238])).

tff(c_1303,plain,(
    ~ r1_tarski('#skF_5',k8_relset_1('#skF_2','#skF_3','#skF_4','#skF_6')) ),
    inference(splitRight,[status(thm)],[c_68])).

tff(c_1886,plain,(
    ~ r1_tarski('#skF_5',k10_relat_1('#skF_4','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1885,c_1303])).

tff(c_1321,plain,(
    ! [C_251,A_252,B_253] :
      ( v1_relat_1(C_251)
      | ~ m1_subset_1(C_251,k1_zfmisc_1(k2_zfmisc_1(A_252,B_253))) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_1334,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_58,c_1321])).

tff(c_56,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_119,plain,(
    ! [A_83,B_84] :
      ( r1_tarski(A_83,B_84)
      | ~ m1_subset_1(A_83,k1_zfmisc_1(B_84)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_131,plain,(
    r1_tarski('#skF_5','#skF_2') ),
    inference(resolution,[status(thm)],[c_56,c_119])).

tff(c_60,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_1613,plain,(
    ! [A_287,B_288,C_289] :
      ( k1_relset_1(A_287,B_288,C_289) = k1_relat_1(C_289)
      | ~ m1_subset_1(C_289,k1_zfmisc_1(k2_zfmisc_1(A_287,B_288))) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_1628,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_58,c_1613])).

tff(c_2287,plain,(
    ! [B_382,A_383,C_384] :
      ( k1_xboole_0 = B_382
      | k1_relset_1(A_383,B_382,C_384) = A_383
      | ~ v1_funct_2(C_384,A_383,B_382)
      | ~ m1_subset_1(C_384,k1_zfmisc_1(k2_zfmisc_1(A_383,B_382))) ) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_2294,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relset_1('#skF_2','#skF_3','#skF_4') = '#skF_2'
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_58,c_2287])).

tff(c_2304,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relat_1('#skF_4') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_1628,c_2294])).

tff(c_2306,plain,(
    k1_relat_1('#skF_4') = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_2304])).

tff(c_1913,plain,(
    ! [A_338,B_339,C_340,D_341] :
      ( k7_relset_1(A_338,B_339,C_340,D_341) = k9_relat_1(C_340,D_341)
      | ~ m1_subset_1(C_340,k1_zfmisc_1(k2_zfmisc_1(A_338,B_339))) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_1924,plain,(
    ! [D_341] : k7_relset_1('#skF_2','#skF_3','#skF_4',D_341) = k9_relat_1('#skF_4',D_341) ),
    inference(resolution,[status(thm)],[c_58,c_1913])).

tff(c_1304,plain,(
    r1_tarski(k7_relset_1('#skF_2','#skF_3','#skF_4','#skF_5'),'#skF_6') ),
    inference(splitRight,[status(thm)],[c_68])).

tff(c_1930,plain,(
    r1_tarski(k9_relat_1('#skF_4','#skF_5'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1924,c_1304])).

tff(c_2395,plain,(
    ! [A_399,C_400,B_401] :
      ( r1_tarski(A_399,k10_relat_1(C_400,B_401))
      | ~ r1_tarski(k9_relat_1(C_400,A_399),B_401)
      | ~ r1_tarski(A_399,k1_relat_1(C_400))
      | ~ v1_funct_1(C_400)
      | ~ v1_relat_1(C_400) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_2416,plain,
    ( r1_tarski('#skF_5',k10_relat_1('#skF_4','#skF_6'))
    | ~ r1_tarski('#skF_5',k1_relat_1('#skF_4'))
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_1930,c_2395])).

tff(c_2454,plain,(
    r1_tarski('#skF_5',k10_relat_1('#skF_4','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1334,c_62,c_131,c_2306,c_2416])).

tff(c_2456,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1886,c_2454])).

tff(c_2457,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_2304])).

tff(c_8,plain,(
    ! [A_8] : r1_tarski(k1_xboole_0,A_8) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_108,plain,(
    ! [B_80,A_81] :
      ( ~ r1_tarski(B_80,A_81)
      | ~ r2_hidden(A_81,B_80) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_113,plain,(
    ! [A_82] :
      ( ~ r1_tarski(A_82,'#skF_1'(A_82))
      | v1_xboole_0(A_82) ) ),
    inference(resolution,[status(thm)],[c_4,c_108])).

tff(c_118,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_8,c_113])).

tff(c_2498,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2457,c_118])).

tff(c_2503,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_2498])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n007.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 09:49:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.70/1.88  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.70/1.89  
% 4.70/1.89  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.70/1.89  %$ v1_funct_2 > v1_partfun1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k8_relset_1 > k7_relset_1 > k1_relset_1 > k9_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_4
% 4.70/1.89  
% 4.70/1.89  %Foreground sorts:
% 4.70/1.89  
% 4.70/1.89  
% 4.70/1.89  %Background operators:
% 4.70/1.89  
% 4.70/1.89  
% 4.70/1.89  %Foreground operators:
% 4.70/1.89  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.70/1.89  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.70/1.89  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.70/1.89  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 4.70/1.89  tff('#skF_1', type, '#skF_1': $i > $i).
% 4.70/1.89  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.70/1.89  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.70/1.89  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 4.70/1.89  tff('#skF_5', type, '#skF_5': $i).
% 4.70/1.89  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.70/1.89  tff('#skF_6', type, '#skF_6': $i).
% 4.70/1.89  tff('#skF_2', type, '#skF_2': $i).
% 4.70/1.89  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 4.70/1.89  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 4.70/1.89  tff('#skF_3', type, '#skF_3': $i).
% 4.70/1.89  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 4.70/1.89  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.70/1.89  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.70/1.89  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 4.70/1.89  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.70/1.89  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.70/1.89  tff('#skF_4', type, '#skF_4': $i).
% 4.70/1.89  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.70/1.89  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.70/1.89  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.70/1.89  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.70/1.89  
% 4.70/1.91  tff(f_160, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (m1_subset_1(D, k1_zfmisc_1(A)) => (![E]: (m1_subset_1(E, k1_zfmisc_1(B)) => (r1_tarski(k7_relset_1(A, B, C, D), E) <=> r1_tarski(D, k8_relset_1(A, B, C, E))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t172_funct_2)).
% 4.70/1.91  tff(f_92, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k8_relset_1(A, B, C, D) = k10_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k8_relset_1)).
% 4.70/1.91  tff(f_80, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 4.70/1.91  tff(f_55, axiom, (![A, B, C]: (v1_relat_1(C) => (r1_tarski(A, B) => r1_tarski(k9_relat_1(C, A), k9_relat_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t156_relat_1)).
% 4.70/1.91  tff(f_61, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => r1_tarski(k9_relat_1(B, k10_relat_1(B, A)), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t145_funct_1)).
% 4.70/1.91  tff(f_37, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 4.70/1.91  tff(f_88, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 4.70/1.91  tff(f_49, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 4.70/1.91  tff(f_84, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 4.70/1.91  tff(f_135, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 4.70/1.91  tff(f_71, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => ((r1_tarski(A, k1_relat_1(C)) & r1_tarski(k9_relat_1(C, A), B)) => r1_tarski(A, k10_relat_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t163_funct_1)).
% 4.70/1.91  tff(f_39, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 4.70/1.91  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 4.70/1.91  tff(f_76, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 4.70/1.91  tff(c_64, plain, (~v1_xboole_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_160])).
% 4.70/1.91  tff(c_58, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_160])).
% 4.70/1.91  tff(c_1874, plain, (![A_328, B_329, C_330, D_331]: (k8_relset_1(A_328, B_329, C_330, D_331)=k10_relat_1(C_330, D_331) | ~m1_subset_1(C_330, k1_zfmisc_1(k2_zfmisc_1(A_328, B_329))))), inference(cnfTransformation, [status(thm)], [f_92])).
% 4.70/1.91  tff(c_1885, plain, (![D_331]: (k8_relset_1('#skF_2', '#skF_3', '#skF_4', D_331)=k10_relat_1('#skF_4', D_331))), inference(resolution, [status(thm)], [c_58, c_1874])).
% 4.70/1.91  tff(c_149, plain, (![C_89, A_90, B_91]: (v1_relat_1(C_89) | ~m1_subset_1(C_89, k1_zfmisc_1(k2_zfmisc_1(A_90, B_91))))), inference(cnfTransformation, [status(thm)], [f_80])).
% 4.70/1.91  tff(c_162, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_58, c_149])).
% 4.70/1.91  tff(c_728, plain, (![A_167, B_168, C_169, D_170]: (k8_relset_1(A_167, B_168, C_169, D_170)=k10_relat_1(C_169, D_170) | ~m1_subset_1(C_169, k1_zfmisc_1(k2_zfmisc_1(A_167, B_168))))), inference(cnfTransformation, [status(thm)], [f_92])).
% 4.70/1.91  tff(c_739, plain, (![D_170]: (k8_relset_1('#skF_2', '#skF_3', '#skF_4', D_170)=k10_relat_1('#skF_4', D_170))), inference(resolution, [status(thm)], [c_58, c_728])).
% 4.70/1.91  tff(c_68, plain, (~r1_tarski('#skF_5', k8_relset_1('#skF_2', '#skF_3', '#skF_4', '#skF_6')) | ~r1_tarski(k7_relset_1('#skF_2', '#skF_3', '#skF_4', '#skF_5'), '#skF_6')), inference(cnfTransformation, [status(thm)], [f_160])).
% 4.70/1.91  tff(c_132, plain, (~r1_tarski(k7_relset_1('#skF_2', '#skF_3', '#skF_4', '#skF_5'), '#skF_6')), inference(splitLeft, [status(thm)], [c_68])).
% 4.70/1.91  tff(c_74, plain, (r1_tarski(k7_relset_1('#skF_2', '#skF_3', '#skF_4', '#skF_5'), '#skF_6') | r1_tarski('#skF_5', k8_relset_1('#skF_2', '#skF_3', '#skF_4', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_160])).
% 4.70/1.91  tff(c_188, plain, (r1_tarski('#skF_5', k8_relset_1('#skF_2', '#skF_3', '#skF_4', '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_132, c_74])).
% 4.70/1.91  tff(c_743, plain, (r1_tarski('#skF_5', k10_relat_1('#skF_4', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_739, c_188])).
% 4.70/1.91  tff(c_62, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_160])).
% 4.70/1.91  tff(c_20, plain, (![C_15, A_13, B_14]: (r1_tarski(k9_relat_1(C_15, A_13), k9_relat_1(C_15, B_14)) | ~r1_tarski(A_13, B_14) | ~v1_relat_1(C_15))), inference(cnfTransformation, [status(thm)], [f_55])).
% 4.70/1.91  tff(c_268, plain, (![B_108, A_109]: (r1_tarski(k9_relat_1(B_108, k10_relat_1(B_108, A_109)), A_109) | ~v1_funct_1(B_108) | ~v1_relat_1(B_108))), inference(cnfTransformation, [status(thm)], [f_61])).
% 4.70/1.91  tff(c_6, plain, (![A_5, C_7, B_6]: (r1_tarski(A_5, C_7) | ~r1_tarski(B_6, C_7) | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.70/1.91  tff(c_1179, plain, (![A_241, A_242, B_243]: (r1_tarski(A_241, A_242) | ~r1_tarski(A_241, k9_relat_1(B_243, k10_relat_1(B_243, A_242))) | ~v1_funct_1(B_243) | ~v1_relat_1(B_243))), inference(resolution, [status(thm)], [c_268, c_6])).
% 4.70/1.91  tff(c_1201, plain, (![C_244, A_245, A_246]: (r1_tarski(k9_relat_1(C_244, A_245), A_246) | ~v1_funct_1(C_244) | ~r1_tarski(A_245, k10_relat_1(C_244, A_246)) | ~v1_relat_1(C_244))), inference(resolution, [status(thm)], [c_20, c_1179])).
% 4.70/1.91  tff(c_768, plain, (![A_173, B_174, C_175, D_176]: (k7_relset_1(A_173, B_174, C_175, D_176)=k9_relat_1(C_175, D_176) | ~m1_subset_1(C_175, k1_zfmisc_1(k2_zfmisc_1(A_173, B_174))))), inference(cnfTransformation, [status(thm)], [f_88])).
% 4.70/1.91  tff(c_779, plain, (![D_176]: (k7_relset_1('#skF_2', '#skF_3', '#skF_4', D_176)=k9_relat_1('#skF_4', D_176))), inference(resolution, [status(thm)], [c_58, c_768])).
% 4.70/1.91  tff(c_780, plain, (~r1_tarski(k9_relat_1('#skF_4', '#skF_5'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_779, c_132])).
% 4.70/1.91  tff(c_1238, plain, (~v1_funct_1('#skF_4') | ~r1_tarski('#skF_5', k10_relat_1('#skF_4', '#skF_6')) | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_1201, c_780])).
% 4.70/1.91  tff(c_1302, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_162, c_743, c_62, c_1238])).
% 4.70/1.91  tff(c_1303, plain, (~r1_tarski('#skF_5', k8_relset_1('#skF_2', '#skF_3', '#skF_4', '#skF_6'))), inference(splitRight, [status(thm)], [c_68])).
% 4.70/1.91  tff(c_1886, plain, (~r1_tarski('#skF_5', k10_relat_1('#skF_4', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_1885, c_1303])).
% 4.70/1.91  tff(c_1321, plain, (![C_251, A_252, B_253]: (v1_relat_1(C_251) | ~m1_subset_1(C_251, k1_zfmisc_1(k2_zfmisc_1(A_252, B_253))))), inference(cnfTransformation, [status(thm)], [f_80])).
% 4.70/1.91  tff(c_1334, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_58, c_1321])).
% 4.70/1.91  tff(c_56, plain, (m1_subset_1('#skF_5', k1_zfmisc_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_160])).
% 4.70/1.91  tff(c_119, plain, (![A_83, B_84]: (r1_tarski(A_83, B_84) | ~m1_subset_1(A_83, k1_zfmisc_1(B_84)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 4.70/1.91  tff(c_131, plain, (r1_tarski('#skF_5', '#skF_2')), inference(resolution, [status(thm)], [c_56, c_119])).
% 4.70/1.91  tff(c_60, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_160])).
% 4.70/1.91  tff(c_1613, plain, (![A_287, B_288, C_289]: (k1_relset_1(A_287, B_288, C_289)=k1_relat_1(C_289) | ~m1_subset_1(C_289, k1_zfmisc_1(k2_zfmisc_1(A_287, B_288))))), inference(cnfTransformation, [status(thm)], [f_84])).
% 4.70/1.91  tff(c_1628, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_58, c_1613])).
% 4.70/1.91  tff(c_2287, plain, (![B_382, A_383, C_384]: (k1_xboole_0=B_382 | k1_relset_1(A_383, B_382, C_384)=A_383 | ~v1_funct_2(C_384, A_383, B_382) | ~m1_subset_1(C_384, k1_zfmisc_1(k2_zfmisc_1(A_383, B_382))))), inference(cnfTransformation, [status(thm)], [f_135])).
% 4.70/1.91  tff(c_2294, plain, (k1_xboole_0='#skF_3' | k1_relset_1('#skF_2', '#skF_3', '#skF_4')='#skF_2' | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_58, c_2287])).
% 4.70/1.91  tff(c_2304, plain, (k1_xboole_0='#skF_3' | k1_relat_1('#skF_4')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_60, c_1628, c_2294])).
% 4.70/1.91  tff(c_2306, plain, (k1_relat_1('#skF_4')='#skF_2'), inference(splitLeft, [status(thm)], [c_2304])).
% 4.70/1.91  tff(c_1913, plain, (![A_338, B_339, C_340, D_341]: (k7_relset_1(A_338, B_339, C_340, D_341)=k9_relat_1(C_340, D_341) | ~m1_subset_1(C_340, k1_zfmisc_1(k2_zfmisc_1(A_338, B_339))))), inference(cnfTransformation, [status(thm)], [f_88])).
% 4.70/1.91  tff(c_1924, plain, (![D_341]: (k7_relset_1('#skF_2', '#skF_3', '#skF_4', D_341)=k9_relat_1('#skF_4', D_341))), inference(resolution, [status(thm)], [c_58, c_1913])).
% 4.70/1.91  tff(c_1304, plain, (r1_tarski(k7_relset_1('#skF_2', '#skF_3', '#skF_4', '#skF_5'), '#skF_6')), inference(splitRight, [status(thm)], [c_68])).
% 4.70/1.91  tff(c_1930, plain, (r1_tarski(k9_relat_1('#skF_4', '#skF_5'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_1924, c_1304])).
% 4.70/1.91  tff(c_2395, plain, (![A_399, C_400, B_401]: (r1_tarski(A_399, k10_relat_1(C_400, B_401)) | ~r1_tarski(k9_relat_1(C_400, A_399), B_401) | ~r1_tarski(A_399, k1_relat_1(C_400)) | ~v1_funct_1(C_400) | ~v1_relat_1(C_400))), inference(cnfTransformation, [status(thm)], [f_71])).
% 4.70/1.91  tff(c_2416, plain, (r1_tarski('#skF_5', k10_relat_1('#skF_4', '#skF_6')) | ~r1_tarski('#skF_5', k1_relat_1('#skF_4')) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_1930, c_2395])).
% 4.70/1.91  tff(c_2454, plain, (r1_tarski('#skF_5', k10_relat_1('#skF_4', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_1334, c_62, c_131, c_2306, c_2416])).
% 4.70/1.91  tff(c_2456, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1886, c_2454])).
% 4.70/1.91  tff(c_2457, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_2304])).
% 4.70/1.91  tff(c_8, plain, (![A_8]: (r1_tarski(k1_xboole_0, A_8))), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.70/1.91  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.70/1.91  tff(c_108, plain, (![B_80, A_81]: (~r1_tarski(B_80, A_81) | ~r2_hidden(A_81, B_80))), inference(cnfTransformation, [status(thm)], [f_76])).
% 4.70/1.91  tff(c_113, plain, (![A_82]: (~r1_tarski(A_82, '#skF_1'(A_82)) | v1_xboole_0(A_82))), inference(resolution, [status(thm)], [c_4, c_108])).
% 4.70/1.91  tff(c_118, plain, (v1_xboole_0(k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_113])).
% 4.70/1.91  tff(c_2498, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2457, c_118])).
% 4.70/1.91  tff(c_2503, plain, $false, inference(negUnitSimplification, [status(thm)], [c_64, c_2498])).
% 4.70/1.91  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.70/1.91  
% 4.70/1.91  Inference rules
% 4.70/1.91  ----------------------
% 4.70/1.91  #Ref     : 0
% 4.70/1.91  #Sup     : 534
% 4.70/1.91  #Fact    : 0
% 4.70/1.91  #Define  : 0
% 4.70/1.91  #Split   : 17
% 4.70/1.91  #Chain   : 0
% 4.70/1.91  #Close   : 0
% 4.70/1.91  
% 4.70/1.91  Ordering : KBO
% 4.70/1.91  
% 4.70/1.91  Simplification rules
% 4.70/1.91  ----------------------
% 4.70/1.91  #Subsume      : 102
% 4.70/1.91  #Demod        : 226
% 4.70/1.91  #Tautology    : 168
% 4.70/1.91  #SimpNegUnit  : 31
% 4.70/1.91  #BackRed      : 67
% 4.70/1.91  
% 4.70/1.91  #Partial instantiations: 0
% 4.70/1.91  #Strategies tried      : 1
% 4.70/1.91  
% 4.70/1.91  Timing (in seconds)
% 4.70/1.91  ----------------------
% 4.70/1.91  Preprocessing        : 0.36
% 4.70/1.91  Parsing              : 0.19
% 4.70/1.91  CNF conversion       : 0.03
% 4.70/1.91  Main loop            : 0.76
% 4.70/1.91  Inferencing          : 0.26
% 4.70/1.91  Reduction            : 0.24
% 4.70/1.91  Demodulation         : 0.16
% 4.70/1.91  BG Simplification    : 0.03
% 4.70/1.91  Subsumption          : 0.16
% 4.70/1.91  Abstraction          : 0.04
% 4.70/1.92  MUC search           : 0.00
% 4.70/1.92  Cooper               : 0.00
% 4.70/1.92  Total                : 1.17
% 4.70/1.92  Index Insertion      : 0.00
% 4.70/1.92  Index Deletion       : 0.00
% 4.70/1.92  Index Matching       : 0.00
% 4.70/1.92  BG Taut test         : 0.00
%------------------------------------------------------------------------------
