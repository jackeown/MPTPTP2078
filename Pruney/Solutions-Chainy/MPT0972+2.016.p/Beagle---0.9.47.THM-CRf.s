%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:11:36 EST 2020

% Result     : Theorem 4.51s
% Output     : CNFRefutation 4.51s
% Verified   : 
% Statistics : Number of formulae       :  108 ( 736 expanded)
%              Number of leaves         :   36 ( 257 expanded)
%              Depth                    :   14
%              Number of atoms          :  187 (1957 expanded)
%              Number of equality atoms :   58 ( 330 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_relset_1,type,(
    r2_relset_1: ( $i * $i * $i * $i ) > $o )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_137,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ! [D] :
            ( ( v1_funct_1(D)
              & v1_funct_2(D,A,B)
              & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
           => ( ! [E] :
                  ( r2_hidden(E,A)
                 => k1_funct_1(C,E) = k1_funct_1(D,E) )
             => r2_relset_1(A,B,C,D) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_funct_2)).

tff(f_88,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(B,A)))
         => v1_xboole_0(C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc4_relset_1)).

tff(f_98,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => r2_relset_1(A,B,C,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',reflexivity_r2_relset_1)).

tff(f_81,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_92,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_116,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).

tff(f_77,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( ( v1_relat_1(B)
            & v1_funct_1(B) )
         => ( ( k1_relat_1(A) = k1_relat_1(B)
              & ! [C] :
                  ( r2_hidden(C,k1_relat_1(A))
                 => k1_funct_1(A,C) = k1_funct_1(B,C) ) )
           => A = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_funct_1)).

tff(f_39,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_45,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_53,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(c_58,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_1177,plain,(
    ! [C_195,B_196,A_197] :
      ( v1_xboole_0(C_195)
      | ~ m1_subset_1(C_195,k1_zfmisc_1(k2_zfmisc_1(B_196,A_197)))
      | ~ v1_xboole_0(A_197) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_1204,plain,
    ( v1_xboole_0('#skF_7')
    | ~ v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_58,c_1177])).

tff(c_1210,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_1204])).

tff(c_64,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_1391,plain,(
    ! [A_215,B_216,C_217,D_218] :
      ( r2_relset_1(A_215,B_216,C_217,C_217)
      | ~ m1_subset_1(D_218,k1_zfmisc_1(k2_zfmisc_1(A_215,B_216)))
      | ~ m1_subset_1(C_217,k1_zfmisc_1(k2_zfmisc_1(A_215,B_216))) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_1490,plain,(
    ! [C_230] :
      ( r2_relset_1('#skF_4','#skF_5',C_230,C_230)
      | ~ m1_subset_1(C_230,k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_5'))) ) ),
    inference(resolution,[status(thm)],[c_64,c_1391])).

tff(c_1507,plain,(
    r2_relset_1('#skF_4','#skF_5','#skF_6','#skF_6') ),
    inference(resolution,[status(thm)],[c_64,c_1490])).

tff(c_106,plain,(
    ! [C_54,A_55,B_56] :
      ( v1_relat_1(C_54)
      | ~ m1_subset_1(C_54,k1_zfmisc_1(k2_zfmisc_1(A_55,B_56))) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_121,plain,(
    v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_58,c_106])).

tff(c_62,plain,(
    v1_funct_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_60,plain,(
    v1_funct_2('#skF_7','#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_1211,plain,(
    ! [A_198,B_199,C_200] :
      ( k1_relset_1(A_198,B_199,C_200) = k1_relat_1(C_200)
      | ~ m1_subset_1(C_200,k1_zfmisc_1(k2_zfmisc_1(A_198,B_199))) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_1238,plain,(
    k1_relset_1('#skF_4','#skF_5','#skF_7') = k1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_58,c_1211])).

tff(c_1309,plain,(
    ! [B_209,A_210,C_211] :
      ( k1_xboole_0 = B_209
      | k1_relset_1(A_210,B_209,C_211) = A_210
      | ~ v1_funct_2(C_211,A_210,B_209)
      | ~ m1_subset_1(C_211,k1_zfmisc_1(k2_zfmisc_1(A_210,B_209))) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_1320,plain,
    ( k1_xboole_0 = '#skF_5'
    | k1_relset_1('#skF_4','#skF_5','#skF_7') = '#skF_4'
    | ~ v1_funct_2('#skF_7','#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_58,c_1309])).

tff(c_1338,plain,
    ( k1_xboole_0 = '#skF_5'
    | k1_relat_1('#skF_7') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_1238,c_1320])).

tff(c_1345,plain,(
    k1_relat_1('#skF_7') = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_1338])).

tff(c_122,plain,(
    v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_64,c_106])).

tff(c_68,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_66,plain,(
    v1_funct_2('#skF_6','#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_1239,plain,(
    k1_relset_1('#skF_4','#skF_5','#skF_6') = k1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_64,c_1211])).

tff(c_1323,plain,
    ( k1_xboole_0 = '#skF_5'
    | k1_relset_1('#skF_4','#skF_5','#skF_6') = '#skF_4'
    | ~ v1_funct_2('#skF_6','#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_64,c_1309])).

tff(c_1341,plain,
    ( k1_xboole_0 = '#skF_5'
    | k1_relat_1('#skF_6') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_1239,c_1323])).

tff(c_1351,plain,(
    k1_relat_1('#skF_6') = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_1341])).

tff(c_1663,plain,(
    ! [A_253,B_254] :
      ( r2_hidden('#skF_3'(A_253,B_254),k1_relat_1(A_253))
      | B_254 = A_253
      | k1_relat_1(B_254) != k1_relat_1(A_253)
      | ~ v1_funct_1(B_254)
      | ~ v1_relat_1(B_254)
      | ~ v1_funct_1(A_253)
      | ~ v1_relat_1(A_253) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_1671,plain,(
    ! [B_254] :
      ( r2_hidden('#skF_3'('#skF_6',B_254),'#skF_4')
      | B_254 = '#skF_6'
      | k1_relat_1(B_254) != k1_relat_1('#skF_6')
      | ~ v1_funct_1(B_254)
      | ~ v1_relat_1(B_254)
      | ~ v1_funct_1('#skF_6')
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1351,c_1663])).

tff(c_2412,plain,(
    ! [B_307] :
      ( r2_hidden('#skF_3'('#skF_6',B_307),'#skF_4')
      | B_307 = '#skF_6'
      | k1_relat_1(B_307) != '#skF_4'
      | ~ v1_funct_1(B_307)
      | ~ v1_relat_1(B_307) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_122,c_68,c_1351,c_1671])).

tff(c_56,plain,(
    ! [E_45] :
      ( k1_funct_1('#skF_7',E_45) = k1_funct_1('#skF_6',E_45)
      | ~ r2_hidden(E_45,'#skF_4') ) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_2466,plain,(
    ! [B_313] :
      ( k1_funct_1('#skF_7','#skF_3'('#skF_6',B_313)) = k1_funct_1('#skF_6','#skF_3'('#skF_6',B_313))
      | B_313 = '#skF_6'
      | k1_relat_1(B_313) != '#skF_4'
      | ~ v1_funct_1(B_313)
      | ~ v1_relat_1(B_313) ) ),
    inference(resolution,[status(thm)],[c_2412,c_56])).

tff(c_30,plain,(
    ! [B_22,A_18] :
      ( k1_funct_1(B_22,'#skF_3'(A_18,B_22)) != k1_funct_1(A_18,'#skF_3'(A_18,B_22))
      | B_22 = A_18
      | k1_relat_1(B_22) != k1_relat_1(A_18)
      | ~ v1_funct_1(B_22)
      | ~ v1_relat_1(B_22)
      | ~ v1_funct_1(A_18)
      | ~ v1_relat_1(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_2473,plain,
    ( k1_relat_1('#skF_7') != k1_relat_1('#skF_6')
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6')
    | '#skF_7' = '#skF_6'
    | k1_relat_1('#skF_7') != '#skF_4'
    | ~ v1_funct_1('#skF_7')
    | ~ v1_relat_1('#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_2466,c_30])).

tff(c_2480,plain,(
    '#skF_7' = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_121,c_62,c_1345,c_122,c_68,c_1345,c_1351,c_2473])).

tff(c_54,plain,(
    ~ r2_relset_1('#skF_4','#skF_5','#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_2495,plain,(
    ~ r2_relset_1('#skF_4','#skF_5','#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2480,c_54])).

tff(c_2505,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1507,c_2495])).

tff(c_2506,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_1341])).

tff(c_12,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_2528,plain,(
    v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2506,c_12])).

tff(c_2530,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1210,c_2528])).

tff(c_2531,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_1338])).

tff(c_2553,plain,(
    v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2531,c_12])).

tff(c_2555,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1210,c_2553])).

tff(c_2557,plain,(
    v1_xboole_0('#skF_5') ),
    inference(splitRight,[status(thm)],[c_1204])).

tff(c_1205,plain,
    ( v1_xboole_0('#skF_6')
    | ~ v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_64,c_1177])).

tff(c_2644,plain,(
    v1_xboole_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2557,c_1205])).

tff(c_149,plain,(
    ! [A_63,B_64] :
      ( r2_hidden('#skF_2'(A_63,B_64),A_63)
      | r1_tarski(A_63,B_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_164,plain,(
    ! [A_63,B_64] :
      ( ~ v1_xboole_0(A_63)
      | r1_tarski(A_63,B_64) ) ),
    inference(resolution,[status(thm)],[c_149,c_2])).

tff(c_172,plain,(
    ! [A_67,B_68] :
      ( ~ v1_xboole_0(A_67)
      | r1_tarski(A_67,B_68) ) ),
    inference(resolution,[status(thm)],[c_149,c_2])).

tff(c_14,plain,(
    ! [B_11,A_10] :
      ( B_11 = A_10
      | ~ r1_tarski(B_11,A_10)
      | ~ r1_tarski(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_176,plain,(
    ! [B_69,A_70] :
      ( B_69 = A_70
      | ~ r1_tarski(B_69,A_70)
      | ~ v1_xboole_0(A_70) ) ),
    inference(resolution,[status(thm)],[c_172,c_14])).

tff(c_186,plain,(
    ! [B_71,A_72] :
      ( B_71 = A_72
      | ~ v1_xboole_0(B_71)
      | ~ v1_xboole_0(A_72) ) ),
    inference(resolution,[status(thm)],[c_164,c_176])).

tff(c_189,plain,(
    ! [A_72] :
      ( k1_xboole_0 = A_72
      | ~ v1_xboole_0(A_72) ) ),
    inference(resolution,[status(thm)],[c_12,c_186])).

tff(c_2570,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_2557,c_189])).

tff(c_2556,plain,(
    v1_xboole_0('#skF_7') ),
    inference(splitRight,[status(thm)],[c_1204])).

tff(c_2563,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(resolution,[status(thm)],[c_2556,c_189])).

tff(c_2622,plain,(
    '#skF_7' = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2570,c_2563])).

tff(c_183,plain,(
    ! [B_64,A_63] :
      ( B_64 = A_63
      | ~ v1_xboole_0(B_64)
      | ~ v1_xboole_0(A_63) ) ),
    inference(resolution,[status(thm)],[c_164,c_176])).

tff(c_2564,plain,(
    ! [A_63] :
      ( A_63 = '#skF_7'
      | ~ v1_xboole_0(A_63) ) ),
    inference(resolution,[status(thm)],[c_2556,c_183])).

tff(c_2649,plain,(
    ! [A_317] :
      ( A_317 = '#skF_5'
      | ~ v1_xboole_0(A_317) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2622,c_2564])).

tff(c_2656,plain,(
    '#skF_5' = '#skF_6' ),
    inference(resolution,[status(thm)],[c_2644,c_2649])).

tff(c_2662,plain,(
    '#skF_7' = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2656,c_2622])).

tff(c_26,plain,(
    ! [A_14] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_14)) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_2612,plain,(
    ! [A_14] : m1_subset_1('#skF_7',k1_zfmisc_1(A_14)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2563,c_26])).

tff(c_2709,plain,(
    ! [A_14] : m1_subset_1('#skF_6',k1_zfmisc_1(A_14)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2662,c_2612])).

tff(c_2830,plain,(
    ! [A_336,B_337,C_338,D_339] :
      ( r2_relset_1(A_336,B_337,C_338,C_338)
      | ~ m1_subset_1(D_339,k1_zfmisc_1(k2_zfmisc_1(A_336,B_337)))
      | ~ m1_subset_1(C_338,k1_zfmisc_1(k2_zfmisc_1(A_336,B_337))) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_3312,plain,(
    ! [A_388,B_389,C_390] :
      ( r2_relset_1(A_388,B_389,C_390,C_390)
      | ~ m1_subset_1(C_390,k1_zfmisc_1(k2_zfmisc_1(A_388,B_389))) ) ),
    inference(resolution,[status(thm)],[c_2709,c_2830])).

tff(c_3328,plain,(
    ! [A_388,B_389] : r2_relset_1(A_388,B_389,'#skF_6','#skF_6') ),
    inference(resolution,[status(thm)],[c_2709,c_3312])).

tff(c_2635,plain,(
    ~ r2_relset_1('#skF_4','#skF_5','#skF_6','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2622,c_54])).

tff(c_2761,plain,(
    ~ r2_relset_1('#skF_4','#skF_6','#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2656,c_2656,c_2635])).

tff(c_3331,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3328,c_2761])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n003.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 10:23:42 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.51/1.90  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.51/1.91  
% 4.51/1.91  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.51/1.91  %$ r2_relset_1 > v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_4 > #skF_2
% 4.51/1.91  
% 4.51/1.91  %Foreground sorts:
% 4.51/1.91  
% 4.51/1.91  
% 4.51/1.91  %Background operators:
% 4.51/1.91  
% 4.51/1.91  
% 4.51/1.91  %Foreground operators:
% 4.51/1.91  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.51/1.91  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.51/1.91  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 4.51/1.91  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.51/1.91  tff('#skF_1', type, '#skF_1': $i > $i).
% 4.51/1.91  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.51/1.91  tff('#skF_7', type, '#skF_7': $i).
% 4.51/1.91  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 4.51/1.91  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.51/1.91  tff('#skF_5', type, '#skF_5': $i).
% 4.51/1.91  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.51/1.91  tff('#skF_6', type, '#skF_6': $i).
% 4.51/1.91  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 4.51/1.91  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.51/1.91  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 4.51/1.91  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.51/1.91  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.51/1.91  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.51/1.91  tff('#skF_4', type, '#skF_4': $i).
% 4.51/1.91  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.51/1.91  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 4.51/1.91  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.51/1.91  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.51/1.91  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.51/1.91  
% 4.51/1.93  tff(f_137, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((![E]: (r2_hidden(E, A) => (k1_funct_1(C, E) = k1_funct_1(D, E)))) => r2_relset_1(A, B, C, D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t18_funct_2)).
% 4.51/1.93  tff(f_88, axiom, (![A, B]: (v1_xboole_0(A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => v1_xboole_0(C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc4_relset_1)).
% 4.51/1.93  tff(f_98, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => r2_relset_1(A, B, C, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', reflexivity_r2_relset_1)).
% 4.51/1.93  tff(f_81, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 4.51/1.93  tff(f_92, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 4.51/1.93  tff(f_116, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 4.51/1.93  tff(f_77, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (((k1_relat_1(A) = k1_relat_1(B)) & (![C]: (r2_hidden(C, k1_relat_1(A)) => (k1_funct_1(A, C) = k1_funct_1(B, C))))) => (A = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t9_funct_1)).
% 4.51/1.93  tff(f_39, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 4.51/1.93  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 4.51/1.93  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 4.51/1.93  tff(f_45, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 4.51/1.93  tff(f_53, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 4.51/1.93  tff(c_58, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_5')))), inference(cnfTransformation, [status(thm)], [f_137])).
% 4.51/1.93  tff(c_1177, plain, (![C_195, B_196, A_197]: (v1_xboole_0(C_195) | ~m1_subset_1(C_195, k1_zfmisc_1(k2_zfmisc_1(B_196, A_197))) | ~v1_xboole_0(A_197))), inference(cnfTransformation, [status(thm)], [f_88])).
% 4.51/1.93  tff(c_1204, plain, (v1_xboole_0('#skF_7') | ~v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_58, c_1177])).
% 4.51/1.93  tff(c_1210, plain, (~v1_xboole_0('#skF_5')), inference(splitLeft, [status(thm)], [c_1204])).
% 4.51/1.93  tff(c_64, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_5')))), inference(cnfTransformation, [status(thm)], [f_137])).
% 4.51/1.93  tff(c_1391, plain, (![A_215, B_216, C_217, D_218]: (r2_relset_1(A_215, B_216, C_217, C_217) | ~m1_subset_1(D_218, k1_zfmisc_1(k2_zfmisc_1(A_215, B_216))) | ~m1_subset_1(C_217, k1_zfmisc_1(k2_zfmisc_1(A_215, B_216))))), inference(cnfTransformation, [status(thm)], [f_98])).
% 4.51/1.93  tff(c_1490, plain, (![C_230]: (r2_relset_1('#skF_4', '#skF_5', C_230, C_230) | ~m1_subset_1(C_230, k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_5'))))), inference(resolution, [status(thm)], [c_64, c_1391])).
% 4.51/1.93  tff(c_1507, plain, (r2_relset_1('#skF_4', '#skF_5', '#skF_6', '#skF_6')), inference(resolution, [status(thm)], [c_64, c_1490])).
% 4.51/1.93  tff(c_106, plain, (![C_54, A_55, B_56]: (v1_relat_1(C_54) | ~m1_subset_1(C_54, k1_zfmisc_1(k2_zfmisc_1(A_55, B_56))))), inference(cnfTransformation, [status(thm)], [f_81])).
% 4.51/1.93  tff(c_121, plain, (v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_58, c_106])).
% 4.51/1.93  tff(c_62, plain, (v1_funct_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_137])).
% 4.51/1.93  tff(c_60, plain, (v1_funct_2('#skF_7', '#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_137])).
% 4.51/1.93  tff(c_1211, plain, (![A_198, B_199, C_200]: (k1_relset_1(A_198, B_199, C_200)=k1_relat_1(C_200) | ~m1_subset_1(C_200, k1_zfmisc_1(k2_zfmisc_1(A_198, B_199))))), inference(cnfTransformation, [status(thm)], [f_92])).
% 4.51/1.93  tff(c_1238, plain, (k1_relset_1('#skF_4', '#skF_5', '#skF_7')=k1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_58, c_1211])).
% 4.51/1.93  tff(c_1309, plain, (![B_209, A_210, C_211]: (k1_xboole_0=B_209 | k1_relset_1(A_210, B_209, C_211)=A_210 | ~v1_funct_2(C_211, A_210, B_209) | ~m1_subset_1(C_211, k1_zfmisc_1(k2_zfmisc_1(A_210, B_209))))), inference(cnfTransformation, [status(thm)], [f_116])).
% 4.51/1.93  tff(c_1320, plain, (k1_xboole_0='#skF_5' | k1_relset_1('#skF_4', '#skF_5', '#skF_7')='#skF_4' | ~v1_funct_2('#skF_7', '#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_58, c_1309])).
% 4.51/1.93  tff(c_1338, plain, (k1_xboole_0='#skF_5' | k1_relat_1('#skF_7')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_60, c_1238, c_1320])).
% 4.51/1.93  tff(c_1345, plain, (k1_relat_1('#skF_7')='#skF_4'), inference(splitLeft, [status(thm)], [c_1338])).
% 4.51/1.93  tff(c_122, plain, (v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_64, c_106])).
% 4.51/1.93  tff(c_68, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_137])).
% 4.51/1.93  tff(c_66, plain, (v1_funct_2('#skF_6', '#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_137])).
% 4.51/1.93  tff(c_1239, plain, (k1_relset_1('#skF_4', '#skF_5', '#skF_6')=k1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_64, c_1211])).
% 4.51/1.93  tff(c_1323, plain, (k1_xboole_0='#skF_5' | k1_relset_1('#skF_4', '#skF_5', '#skF_6')='#skF_4' | ~v1_funct_2('#skF_6', '#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_64, c_1309])).
% 4.51/1.93  tff(c_1341, plain, (k1_xboole_0='#skF_5' | k1_relat_1('#skF_6')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_66, c_1239, c_1323])).
% 4.51/1.93  tff(c_1351, plain, (k1_relat_1('#skF_6')='#skF_4'), inference(splitLeft, [status(thm)], [c_1341])).
% 4.51/1.93  tff(c_1663, plain, (![A_253, B_254]: (r2_hidden('#skF_3'(A_253, B_254), k1_relat_1(A_253)) | B_254=A_253 | k1_relat_1(B_254)!=k1_relat_1(A_253) | ~v1_funct_1(B_254) | ~v1_relat_1(B_254) | ~v1_funct_1(A_253) | ~v1_relat_1(A_253))), inference(cnfTransformation, [status(thm)], [f_77])).
% 4.51/1.93  tff(c_1671, plain, (![B_254]: (r2_hidden('#skF_3'('#skF_6', B_254), '#skF_4') | B_254='#skF_6' | k1_relat_1(B_254)!=k1_relat_1('#skF_6') | ~v1_funct_1(B_254) | ~v1_relat_1(B_254) | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_1351, c_1663])).
% 4.51/1.93  tff(c_2412, plain, (![B_307]: (r2_hidden('#skF_3'('#skF_6', B_307), '#skF_4') | B_307='#skF_6' | k1_relat_1(B_307)!='#skF_4' | ~v1_funct_1(B_307) | ~v1_relat_1(B_307))), inference(demodulation, [status(thm), theory('equality')], [c_122, c_68, c_1351, c_1671])).
% 4.51/1.93  tff(c_56, plain, (![E_45]: (k1_funct_1('#skF_7', E_45)=k1_funct_1('#skF_6', E_45) | ~r2_hidden(E_45, '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_137])).
% 4.51/1.93  tff(c_2466, plain, (![B_313]: (k1_funct_1('#skF_7', '#skF_3'('#skF_6', B_313))=k1_funct_1('#skF_6', '#skF_3'('#skF_6', B_313)) | B_313='#skF_6' | k1_relat_1(B_313)!='#skF_4' | ~v1_funct_1(B_313) | ~v1_relat_1(B_313))), inference(resolution, [status(thm)], [c_2412, c_56])).
% 4.51/1.93  tff(c_30, plain, (![B_22, A_18]: (k1_funct_1(B_22, '#skF_3'(A_18, B_22))!=k1_funct_1(A_18, '#skF_3'(A_18, B_22)) | B_22=A_18 | k1_relat_1(B_22)!=k1_relat_1(A_18) | ~v1_funct_1(B_22) | ~v1_relat_1(B_22) | ~v1_funct_1(A_18) | ~v1_relat_1(A_18))), inference(cnfTransformation, [status(thm)], [f_77])).
% 4.51/1.93  tff(c_2473, plain, (k1_relat_1('#skF_7')!=k1_relat_1('#skF_6') | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6') | '#skF_7'='#skF_6' | k1_relat_1('#skF_7')!='#skF_4' | ~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_2466, c_30])).
% 4.51/1.93  tff(c_2480, plain, ('#skF_7'='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_121, c_62, c_1345, c_122, c_68, c_1345, c_1351, c_2473])).
% 4.51/1.93  tff(c_54, plain, (~r2_relset_1('#skF_4', '#skF_5', '#skF_6', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_137])).
% 4.51/1.93  tff(c_2495, plain, (~r2_relset_1('#skF_4', '#skF_5', '#skF_6', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_2480, c_54])).
% 4.51/1.93  tff(c_2505, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1507, c_2495])).
% 4.51/1.93  tff(c_2506, plain, (k1_xboole_0='#skF_5'), inference(splitRight, [status(thm)], [c_1341])).
% 4.51/1.93  tff(c_12, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.51/1.93  tff(c_2528, plain, (v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_2506, c_12])).
% 4.51/1.93  tff(c_2530, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1210, c_2528])).
% 4.51/1.93  tff(c_2531, plain, (k1_xboole_0='#skF_5'), inference(splitRight, [status(thm)], [c_1338])).
% 4.51/1.93  tff(c_2553, plain, (v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_2531, c_12])).
% 4.51/1.93  tff(c_2555, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1210, c_2553])).
% 4.51/1.93  tff(c_2557, plain, (v1_xboole_0('#skF_5')), inference(splitRight, [status(thm)], [c_1204])).
% 4.51/1.93  tff(c_1205, plain, (v1_xboole_0('#skF_6') | ~v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_64, c_1177])).
% 4.51/1.93  tff(c_2644, plain, (v1_xboole_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_2557, c_1205])).
% 4.51/1.93  tff(c_149, plain, (![A_63, B_64]: (r2_hidden('#skF_2'(A_63, B_64), A_63) | r1_tarski(A_63, B_64))), inference(cnfTransformation, [status(thm)], [f_38])).
% 4.51/1.93  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.51/1.93  tff(c_164, plain, (![A_63, B_64]: (~v1_xboole_0(A_63) | r1_tarski(A_63, B_64))), inference(resolution, [status(thm)], [c_149, c_2])).
% 4.51/1.93  tff(c_172, plain, (![A_67, B_68]: (~v1_xboole_0(A_67) | r1_tarski(A_67, B_68))), inference(resolution, [status(thm)], [c_149, c_2])).
% 4.51/1.93  tff(c_14, plain, (![B_11, A_10]: (B_11=A_10 | ~r1_tarski(B_11, A_10) | ~r1_tarski(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_45])).
% 4.51/1.93  tff(c_176, plain, (![B_69, A_70]: (B_69=A_70 | ~r1_tarski(B_69, A_70) | ~v1_xboole_0(A_70))), inference(resolution, [status(thm)], [c_172, c_14])).
% 4.51/1.93  tff(c_186, plain, (![B_71, A_72]: (B_71=A_72 | ~v1_xboole_0(B_71) | ~v1_xboole_0(A_72))), inference(resolution, [status(thm)], [c_164, c_176])).
% 4.51/1.93  tff(c_189, plain, (![A_72]: (k1_xboole_0=A_72 | ~v1_xboole_0(A_72))), inference(resolution, [status(thm)], [c_12, c_186])).
% 4.51/1.93  tff(c_2570, plain, (k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_2557, c_189])).
% 4.51/1.93  tff(c_2556, plain, (v1_xboole_0('#skF_7')), inference(splitRight, [status(thm)], [c_1204])).
% 4.51/1.93  tff(c_2563, plain, (k1_xboole_0='#skF_7'), inference(resolution, [status(thm)], [c_2556, c_189])).
% 4.51/1.93  tff(c_2622, plain, ('#skF_7'='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_2570, c_2563])).
% 4.51/1.93  tff(c_183, plain, (![B_64, A_63]: (B_64=A_63 | ~v1_xboole_0(B_64) | ~v1_xboole_0(A_63))), inference(resolution, [status(thm)], [c_164, c_176])).
% 4.51/1.93  tff(c_2564, plain, (![A_63]: (A_63='#skF_7' | ~v1_xboole_0(A_63))), inference(resolution, [status(thm)], [c_2556, c_183])).
% 4.51/1.93  tff(c_2649, plain, (![A_317]: (A_317='#skF_5' | ~v1_xboole_0(A_317))), inference(demodulation, [status(thm), theory('equality')], [c_2622, c_2564])).
% 4.51/1.93  tff(c_2656, plain, ('#skF_5'='#skF_6'), inference(resolution, [status(thm)], [c_2644, c_2649])).
% 4.51/1.93  tff(c_2662, plain, ('#skF_7'='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_2656, c_2622])).
% 4.51/1.93  tff(c_26, plain, (![A_14]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_14)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 4.51/1.93  tff(c_2612, plain, (![A_14]: (m1_subset_1('#skF_7', k1_zfmisc_1(A_14)))), inference(demodulation, [status(thm), theory('equality')], [c_2563, c_26])).
% 4.51/1.93  tff(c_2709, plain, (![A_14]: (m1_subset_1('#skF_6', k1_zfmisc_1(A_14)))), inference(demodulation, [status(thm), theory('equality')], [c_2662, c_2612])).
% 4.51/1.93  tff(c_2830, plain, (![A_336, B_337, C_338, D_339]: (r2_relset_1(A_336, B_337, C_338, C_338) | ~m1_subset_1(D_339, k1_zfmisc_1(k2_zfmisc_1(A_336, B_337))) | ~m1_subset_1(C_338, k1_zfmisc_1(k2_zfmisc_1(A_336, B_337))))), inference(cnfTransformation, [status(thm)], [f_98])).
% 4.51/1.93  tff(c_3312, plain, (![A_388, B_389, C_390]: (r2_relset_1(A_388, B_389, C_390, C_390) | ~m1_subset_1(C_390, k1_zfmisc_1(k2_zfmisc_1(A_388, B_389))))), inference(resolution, [status(thm)], [c_2709, c_2830])).
% 4.51/1.93  tff(c_3328, plain, (![A_388, B_389]: (r2_relset_1(A_388, B_389, '#skF_6', '#skF_6'))), inference(resolution, [status(thm)], [c_2709, c_3312])).
% 4.51/1.93  tff(c_2635, plain, (~r2_relset_1('#skF_4', '#skF_5', '#skF_6', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_2622, c_54])).
% 4.51/1.93  tff(c_2761, plain, (~r2_relset_1('#skF_4', '#skF_6', '#skF_6', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_2656, c_2656, c_2635])).
% 4.51/1.93  tff(c_3331, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3328, c_2761])).
% 4.51/1.93  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.51/1.93  
% 4.51/1.93  Inference rules
% 4.51/1.93  ----------------------
% 4.51/1.93  #Ref     : 2
% 4.51/1.93  #Sup     : 687
% 4.51/1.93  #Fact    : 0
% 4.51/1.93  #Define  : 0
% 4.51/1.93  #Split   : 15
% 4.51/1.93  #Chain   : 0
% 4.51/1.93  #Close   : 0
% 4.51/1.93  
% 4.51/1.93  Ordering : KBO
% 4.51/1.93  
% 4.51/1.93  Simplification rules
% 4.51/1.93  ----------------------
% 4.51/1.93  #Subsume      : 168
% 4.51/1.93  #Demod        : 591
% 4.51/1.93  #Tautology    : 349
% 4.51/1.93  #SimpNegUnit  : 25
% 4.51/1.93  #BackRed      : 134
% 4.51/1.93  
% 4.51/1.93  #Partial instantiations: 0
% 4.51/1.93  #Strategies tried      : 1
% 4.51/1.93  
% 4.51/1.93  Timing (in seconds)
% 4.51/1.93  ----------------------
% 4.51/1.93  Preprocessing        : 0.30
% 4.51/1.93  Parsing              : 0.15
% 4.51/1.93  CNF conversion       : 0.02
% 4.51/1.93  Main loop            : 0.75
% 4.51/1.93  Inferencing          : 0.24
% 4.51/1.93  Reduction            : 0.23
% 4.51/1.93  Demodulation         : 0.16
% 4.51/1.94  BG Simplification    : 0.03
% 4.51/1.94  Subsumption          : 0.17
% 4.51/1.94  Abstraction          : 0.03
% 4.51/1.94  MUC search           : 0.00
% 4.51/1.94  Cooper               : 0.00
% 4.51/1.94  Total                : 1.09
% 4.51/1.94  Index Insertion      : 0.00
% 4.51/1.94  Index Deletion       : 0.00
% 4.51/1.94  Index Matching       : 0.00
% 4.51/1.94  BG Taut test         : 0.00
%------------------------------------------------------------------------------
