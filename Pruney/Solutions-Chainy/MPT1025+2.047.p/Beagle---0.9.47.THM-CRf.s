%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:16:36 EST 2020

% Result     : Theorem 6.05s
% Output     : CNFRefutation 6.30s
% Verified   : 
% Statistics : Number of formulae       :  107 ( 831 expanded)
%              Number of leaves         :   40 ( 305 expanded)
%              Depth                    :   12
%              Number of atoms          :  182 (2631 expanded)
%              Number of equality atoms :   49 ( 942 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k1_relset_1 > k9_relat_1 > k4_tarski > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_4 > #skF_7 > #skF_10 > #skF_6 > #skF_2 > #skF_9 > #skF_8 > #skF_5 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff(k7_relset_1,type,(
    k7_relset_1: ( $i * $i * $i * $i ) > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_44,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_122,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ! [E] :
            ~ ( r2_hidden(E,k7_relset_1(A,B,D,C))
              & ! [F] :
                  ( m1_subset_1(F,A)
                 => ~ ( r2_hidden(F,C)
                      & E = k1_funct_1(D,F) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t116_funct_2)).

tff(f_42,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_72,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B,C] :
          ( C = k9_relat_1(A,B)
        <=> ! [D] :
              ( r2_hidden(D,C)
            <=> ? [E] :
                  ( r2_hidden(E,k1_relat_1(A))
                  & r2_hidden(E,B)
                  & D = k1_funct_1(A,E) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d12_funct_1)).

tff(f_81,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_103,axiom,(
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

tff(f_31,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

tff(f_85,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_27,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_55,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k9_relat_1(C,B))
      <=> ? [D] :
            ( r2_hidden(D,k1_relat_1(C))
            & r2_hidden(k4_tarski(D,A),C)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t143_relat_1)).

tff(f_77,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

tff(c_12,plain,(
    ! [A_9,B_10] : v1_relat_1(k2_zfmisc_1(A_9,B_10)) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_68,plain,(
    m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_7'))) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_96,plain,(
    ! [B_88,A_89] :
      ( v1_relat_1(B_88)
      | ~ m1_subset_1(B_88,k1_zfmisc_1(A_89))
      | ~ v1_relat_1(A_89) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_102,plain,
    ( v1_relat_1('#skF_9')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_6','#skF_7')) ),
    inference(resolution,[status(thm)],[c_68,c_96])).

tff(c_106,plain,(
    v1_relat_1('#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_102])).

tff(c_72,plain,(
    v1_funct_1('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_24,plain,(
    ! [A_17,B_40,D_55] :
      ( k1_funct_1(A_17,'#skF_5'(A_17,B_40,k9_relat_1(A_17,B_40),D_55)) = D_55
      | ~ r2_hidden(D_55,k9_relat_1(A_17,B_40))
      | ~ v1_funct_1(A_17)
      | ~ v1_relat_1(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_70,plain,(
    v1_funct_2('#skF_9','#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_126,plain,(
    ! [A_94,B_95,C_96] :
      ( k1_relset_1(A_94,B_95,C_96) = k1_relat_1(C_96)
      | ~ m1_subset_1(C_96,k1_zfmisc_1(k2_zfmisc_1(A_94,B_95))) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_135,plain,(
    k1_relset_1('#skF_6','#skF_7','#skF_9') = k1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_68,c_126])).

tff(c_2692,plain,(
    ! [B_399,A_400,C_401] :
      ( k1_xboole_0 = B_399
      | k1_relset_1(A_400,B_399,C_401) = A_400
      | ~ v1_funct_2(C_401,A_400,B_399)
      | ~ m1_subset_1(C_401,k1_zfmisc_1(k2_zfmisc_1(A_400,B_399))) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_2699,plain,
    ( k1_xboole_0 = '#skF_7'
    | k1_relset_1('#skF_6','#skF_7','#skF_9') = '#skF_6'
    | ~ v1_funct_2('#skF_9','#skF_6','#skF_7') ),
    inference(resolution,[status(thm)],[c_68,c_2692])).

tff(c_2703,plain,
    ( k1_xboole_0 = '#skF_7'
    | k1_relat_1('#skF_9') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_135,c_2699])).

tff(c_2704,plain,(
    k1_relat_1('#skF_9') = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_2703])).

tff(c_3273,plain,(
    ! [A_490,B_491,D_492] :
      ( r2_hidden('#skF_5'(A_490,B_491,k9_relat_1(A_490,B_491),D_492),k1_relat_1(A_490))
      | ~ r2_hidden(D_492,k9_relat_1(A_490,B_491))
      | ~ v1_funct_1(A_490)
      | ~ v1_relat_1(A_490) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_3287,plain,(
    ! [B_491,D_492] :
      ( r2_hidden('#skF_5'('#skF_9',B_491,k9_relat_1('#skF_9',B_491),D_492),'#skF_6')
      | ~ r2_hidden(D_492,k9_relat_1('#skF_9',B_491))
      | ~ v1_funct_1('#skF_9')
      | ~ v1_relat_1('#skF_9') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2704,c_3273])).

tff(c_3294,plain,(
    ! [B_493,D_494] :
      ( r2_hidden('#skF_5'('#skF_9',B_493,k9_relat_1('#skF_9',B_493),D_494),'#skF_6')
      | ~ r2_hidden(D_494,k9_relat_1('#skF_9',B_493)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_106,c_72,c_3287])).

tff(c_4,plain,(
    ! [A_2,B_3] :
      ( m1_subset_1(A_2,B_3)
      | ~ r2_hidden(A_2,B_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_3307,plain,(
    ! [B_497,D_498] :
      ( m1_subset_1('#skF_5'('#skF_9',B_497,k9_relat_1('#skF_9',B_497),D_498),'#skF_6')
      | ~ r2_hidden(D_498,k9_relat_1('#skF_9',B_497)) ) ),
    inference(resolution,[status(thm)],[c_3294,c_4])).

tff(c_2907,plain,(
    ! [A_443,B_444,D_445] :
      ( r2_hidden('#skF_5'(A_443,B_444,k9_relat_1(A_443,B_444),D_445),B_444)
      | ~ r2_hidden(D_445,k9_relat_1(A_443,B_444))
      | ~ v1_funct_1(A_443)
      | ~ v1_relat_1(A_443) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_64,plain,(
    ! [F_75] :
      ( k1_funct_1('#skF_9',F_75) != '#skF_10'
      | ~ r2_hidden(F_75,'#skF_8')
      | ~ m1_subset_1(F_75,'#skF_6') ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_2982,plain,(
    ! [A_443,D_445] :
      ( k1_funct_1('#skF_9','#skF_5'(A_443,'#skF_8',k9_relat_1(A_443,'#skF_8'),D_445)) != '#skF_10'
      | ~ m1_subset_1('#skF_5'(A_443,'#skF_8',k9_relat_1(A_443,'#skF_8'),D_445),'#skF_6')
      | ~ r2_hidden(D_445,k9_relat_1(A_443,'#skF_8'))
      | ~ v1_funct_1(A_443)
      | ~ v1_relat_1(A_443) ) ),
    inference(resolution,[status(thm)],[c_2907,c_64])).

tff(c_3311,plain,(
    ! [D_498] :
      ( k1_funct_1('#skF_9','#skF_5'('#skF_9','#skF_8',k9_relat_1('#skF_9','#skF_8'),D_498)) != '#skF_10'
      | ~ v1_funct_1('#skF_9')
      | ~ v1_relat_1('#skF_9')
      | ~ r2_hidden(D_498,k9_relat_1('#skF_9','#skF_8')) ) ),
    inference(resolution,[status(thm)],[c_3307,c_2982])).

tff(c_3316,plain,(
    ! [D_500] :
      ( k1_funct_1('#skF_9','#skF_5'('#skF_9','#skF_8',k9_relat_1('#skF_9','#skF_8'),D_500)) != '#skF_10'
      | ~ r2_hidden(D_500,k9_relat_1('#skF_9','#skF_8')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_106,c_72,c_3311])).

tff(c_3320,plain,(
    ! [D_55] :
      ( D_55 != '#skF_10'
      | ~ r2_hidden(D_55,k9_relat_1('#skF_9','#skF_8'))
      | ~ r2_hidden(D_55,k9_relat_1('#skF_9','#skF_8'))
      | ~ v1_funct_1('#skF_9')
      | ~ v1_relat_1('#skF_9') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_3316])).

tff(c_3323,plain,(
    ~ r2_hidden('#skF_10',k9_relat_1('#skF_9','#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_106,c_72,c_3320])).

tff(c_207,plain,(
    ! [A_118,B_119,C_120,D_121] :
      ( k7_relset_1(A_118,B_119,C_120,D_121) = k9_relat_1(C_120,D_121)
      | ~ m1_subset_1(C_120,k1_zfmisc_1(k2_zfmisc_1(A_118,B_119))) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_214,plain,(
    ! [D_121] : k7_relset_1('#skF_6','#skF_7','#skF_9',D_121) = k9_relat_1('#skF_9',D_121) ),
    inference(resolution,[status(thm)],[c_68,c_207])).

tff(c_66,plain,(
    r2_hidden('#skF_10',k7_relset_1('#skF_6','#skF_7','#skF_9','#skF_8')) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_217,plain,(
    r2_hidden('#skF_10',k9_relat_1('#skF_9','#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_214,c_66])).

tff(c_3325,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3323,c_217])).

tff(c_3327,plain,(
    k1_relat_1('#skF_9') != '#skF_6' ),
    inference(splitRight,[status(thm)],[c_2703])).

tff(c_87,plain,(
    ! [A_86,B_87] :
      ( r1_tarski(A_86,B_87)
      | ~ m1_subset_1(A_86,k1_zfmisc_1(B_87)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_95,plain,(
    r1_tarski('#skF_9',k2_zfmisc_1('#skF_6','#skF_7')) ),
    inference(resolution,[status(thm)],[c_68,c_87])).

tff(c_3326,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_2703])).

tff(c_8,plain,(
    ! [A_4,B_5] :
      ( m1_subset_1(A_4,k1_zfmisc_1(B_5))
      | ~ r1_tarski(A_4,B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_227,plain,(
    ! [C_123,A_124] :
      ( k1_xboole_0 = C_123
      | ~ v1_funct_2(C_123,A_124,k1_xboole_0)
      | k1_xboole_0 = A_124
      | ~ m1_subset_1(C_123,k1_zfmisc_1(k2_zfmisc_1(A_124,k1_xboole_0))) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_232,plain,(
    ! [A_4,A_124] :
      ( k1_xboole_0 = A_4
      | ~ v1_funct_2(A_4,A_124,k1_xboole_0)
      | k1_xboole_0 = A_124
      | ~ r1_tarski(A_4,k2_zfmisc_1(A_124,k1_xboole_0)) ) ),
    inference(resolution,[status(thm)],[c_8,c_227])).

tff(c_4358,plain,(
    ! [A_607,A_608] :
      ( A_607 = '#skF_7'
      | ~ v1_funct_2(A_607,A_608,'#skF_7')
      | A_608 = '#skF_7'
      | ~ r1_tarski(A_607,k2_zfmisc_1(A_608,'#skF_7')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3326,c_3326,c_3326,c_3326,c_232])).

tff(c_4365,plain,
    ( '#skF_7' = '#skF_9'
    | ~ v1_funct_2('#skF_9','#skF_6','#skF_7')
    | '#skF_7' = '#skF_6' ),
    inference(resolution,[status(thm)],[c_95,c_4358])).

tff(c_4370,plain,
    ( '#skF_7' = '#skF_9'
    | '#skF_7' = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_4365])).

tff(c_4371,plain,(
    '#skF_7' = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_4370])).

tff(c_4395,plain,(
    v1_funct_2('#skF_9','#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4371,c_70])).

tff(c_4392,plain,(
    k1_relset_1('#skF_6','#skF_6','#skF_9') = k1_relat_1('#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4371,c_135])).

tff(c_4393,plain,(
    r1_tarski('#skF_9',k2_zfmisc_1('#skF_6','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4371,c_95])).

tff(c_2663,plain,(
    ! [B_391,C_392] :
      ( k1_relset_1(k1_xboole_0,B_391,C_392) = k1_xboole_0
      | ~ v1_funct_2(C_392,k1_xboole_0,B_391)
      | ~ m1_subset_1(C_392,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_391))) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_2668,plain,(
    ! [B_391,A_4] :
      ( k1_relset_1(k1_xboole_0,B_391,A_4) = k1_xboole_0
      | ~ v1_funct_2(A_4,k1_xboole_0,B_391)
      | ~ r1_tarski(A_4,k2_zfmisc_1(k1_xboole_0,B_391)) ) ),
    inference(resolution,[status(thm)],[c_8,c_2663])).

tff(c_3330,plain,(
    ! [B_391,A_4] :
      ( k1_relset_1('#skF_7',B_391,A_4) = '#skF_7'
      | ~ v1_funct_2(A_4,'#skF_7',B_391)
      | ~ r1_tarski(A_4,k2_zfmisc_1('#skF_7',B_391)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3326,c_3326,c_3326,c_3326,c_2668])).

tff(c_5228,plain,(
    ! [B_671,A_672] :
      ( k1_relset_1('#skF_6',B_671,A_672) = '#skF_6'
      | ~ v1_funct_2(A_672,'#skF_6',B_671)
      | ~ r1_tarski(A_672,k2_zfmisc_1('#skF_6',B_671)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4371,c_4371,c_4371,c_4371,c_3330])).

tff(c_5231,plain,
    ( k1_relset_1('#skF_6','#skF_6','#skF_9') = '#skF_6'
    | ~ v1_funct_2('#skF_9','#skF_6','#skF_6') ),
    inference(resolution,[status(thm)],[c_4393,c_5228])).

tff(c_5238,plain,(
    k1_relat_1('#skF_9') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4395,c_4392,c_5231])).

tff(c_5240,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3327,c_5238])).

tff(c_5241,plain,(
    '#skF_7' = '#skF_9' ),
    inference(splitRight,[status(thm)],[c_4370])).

tff(c_2,plain,(
    ! [A_1] : r1_tarski(k1_xboole_0,A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_115,plain,(
    ! [A_92,B_93] :
      ( v1_relat_1(A_92)
      | ~ v1_relat_1(B_93)
      | ~ r1_tarski(A_92,B_93) ) ),
    inference(resolution,[status(thm)],[c_8,c_96])).

tff(c_125,plain,(
    ! [A_1] :
      ( v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(A_1) ) ),
    inference(resolution,[status(thm)],[c_2,c_115])).

tff(c_136,plain,(
    ! [A_1] : ~ v1_relat_1(A_1) ),
    inference(splitLeft,[status(thm)],[c_125])).

tff(c_141,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_136,c_106])).

tff(c_142,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_125])).

tff(c_2604,plain,(
    ! [A_381,B_382,C_383] :
      ( r2_hidden(k4_tarski('#skF_1'(A_381,B_382,C_383),A_381),C_383)
      | ~ r2_hidden(A_381,k9_relat_1(C_383,B_382))
      | ~ v1_relat_1(C_383) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_46,plain,(
    ! [B_60,A_59] :
      ( ~ r1_tarski(B_60,A_59)
      | ~ r2_hidden(A_59,B_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_2684,plain,(
    ! [C_396,A_397,B_398] :
      ( ~ r1_tarski(C_396,k4_tarski('#skF_1'(A_397,B_398,C_396),A_397))
      | ~ r2_hidden(A_397,k9_relat_1(C_396,B_398))
      | ~ v1_relat_1(C_396) ) ),
    inference(resolution,[status(thm)],[c_2604,c_46])).

tff(c_2688,plain,(
    ! [A_397,B_398] :
      ( ~ r2_hidden(A_397,k9_relat_1(k1_xboole_0,B_398))
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_2,c_2684])).

tff(c_2691,plain,(
    ! [A_397,B_398] : ~ r2_hidden(A_397,k9_relat_1(k1_xboole_0,B_398)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_142,c_2688])).

tff(c_3389,plain,(
    ! [A_397,B_398] : ~ r2_hidden(A_397,k9_relat_1('#skF_7',B_398)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3326,c_2691])).

tff(c_5256,plain,(
    ! [A_397,B_398] : ~ r2_hidden(A_397,k9_relat_1('#skF_9',B_398)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5241,c_3389])).

tff(c_5341,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_5256,c_217])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n004.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 09:46:08 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.05/2.26  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.30/2.28  
% 6.30/2.28  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.30/2.28  %$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k1_relset_1 > k9_relat_1 > k4_tarski > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_4 > #skF_7 > #skF_10 > #skF_6 > #skF_2 > #skF_9 > #skF_8 > #skF_5 > #skF_3
% 6.30/2.28  
% 6.30/2.28  %Foreground sorts:
% 6.30/2.28  
% 6.30/2.28  
% 6.30/2.28  %Background operators:
% 6.30/2.28  
% 6.30/2.28  
% 6.30/2.28  %Foreground operators:
% 6.30/2.28  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 6.30/2.28  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 6.30/2.28  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.30/2.28  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 6.30/2.28  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 6.30/2.28  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 6.30/2.28  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 6.30/2.28  tff('#skF_7', type, '#skF_7': $i).
% 6.30/2.28  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.30/2.28  tff('#skF_10', type, '#skF_10': $i).
% 6.30/2.28  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 6.30/2.28  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 6.30/2.28  tff('#skF_6', type, '#skF_6': $i).
% 6.30/2.28  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 6.30/2.28  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 6.30/2.28  tff('#skF_9', type, '#skF_9': $i).
% 6.30/2.28  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 6.30/2.28  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 6.30/2.28  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 6.30/2.28  tff('#skF_8', type, '#skF_8': $i).
% 6.30/2.28  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.30/2.28  tff('#skF_5', type, '#skF_5': ($i * $i * $i * $i) > $i).
% 6.30/2.28  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 6.30/2.28  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 6.30/2.28  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 6.30/2.28  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.30/2.28  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 6.30/2.28  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 6.30/2.28  
% 6.30/2.32  tff(f_44, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 6.30/2.32  tff(f_122, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: ~(r2_hidden(E, k7_relset_1(A, B, D, C)) & (![F]: (m1_subset_1(F, A) => ~(r2_hidden(F, C) & (E = k1_funct_1(D, F))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t116_funct_2)).
% 6.30/2.32  tff(f_42, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 6.30/2.32  tff(f_72, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B, C]: ((C = k9_relat_1(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (?[E]: ((r2_hidden(E, k1_relat_1(A)) & r2_hidden(E, B)) & (D = k1_funct_1(A, E)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d12_funct_1)).
% 6.30/2.32  tff(f_81, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 6.30/2.32  tff(f_103, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 6.30/2.32  tff(f_31, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_subset)).
% 6.30/2.32  tff(f_85, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 6.30/2.32  tff(f_35, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 6.30/2.32  tff(f_27, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 6.30/2.32  tff(f_55, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k9_relat_1(C, B)) <=> (?[D]: ((r2_hidden(D, k1_relat_1(C)) & r2_hidden(k4_tarski(D, A), C)) & r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t143_relat_1)).
% 6.30/2.32  tff(f_77, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 6.30/2.32  tff(c_12, plain, (![A_9, B_10]: (v1_relat_1(k2_zfmisc_1(A_9, B_10)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 6.30/2.32  tff(c_68, plain, (m1_subset_1('#skF_9', k1_zfmisc_1(k2_zfmisc_1('#skF_6', '#skF_7')))), inference(cnfTransformation, [status(thm)], [f_122])).
% 6.30/2.32  tff(c_96, plain, (![B_88, A_89]: (v1_relat_1(B_88) | ~m1_subset_1(B_88, k1_zfmisc_1(A_89)) | ~v1_relat_1(A_89))), inference(cnfTransformation, [status(thm)], [f_42])).
% 6.30/2.32  tff(c_102, plain, (v1_relat_1('#skF_9') | ~v1_relat_1(k2_zfmisc_1('#skF_6', '#skF_7'))), inference(resolution, [status(thm)], [c_68, c_96])).
% 6.30/2.32  tff(c_106, plain, (v1_relat_1('#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_12, c_102])).
% 6.30/2.32  tff(c_72, plain, (v1_funct_1('#skF_9')), inference(cnfTransformation, [status(thm)], [f_122])).
% 6.30/2.32  tff(c_24, plain, (![A_17, B_40, D_55]: (k1_funct_1(A_17, '#skF_5'(A_17, B_40, k9_relat_1(A_17, B_40), D_55))=D_55 | ~r2_hidden(D_55, k9_relat_1(A_17, B_40)) | ~v1_funct_1(A_17) | ~v1_relat_1(A_17))), inference(cnfTransformation, [status(thm)], [f_72])).
% 6.30/2.32  tff(c_70, plain, (v1_funct_2('#skF_9', '#skF_6', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_122])).
% 6.30/2.32  tff(c_126, plain, (![A_94, B_95, C_96]: (k1_relset_1(A_94, B_95, C_96)=k1_relat_1(C_96) | ~m1_subset_1(C_96, k1_zfmisc_1(k2_zfmisc_1(A_94, B_95))))), inference(cnfTransformation, [status(thm)], [f_81])).
% 6.30/2.32  tff(c_135, plain, (k1_relset_1('#skF_6', '#skF_7', '#skF_9')=k1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_68, c_126])).
% 6.30/2.32  tff(c_2692, plain, (![B_399, A_400, C_401]: (k1_xboole_0=B_399 | k1_relset_1(A_400, B_399, C_401)=A_400 | ~v1_funct_2(C_401, A_400, B_399) | ~m1_subset_1(C_401, k1_zfmisc_1(k2_zfmisc_1(A_400, B_399))))), inference(cnfTransformation, [status(thm)], [f_103])).
% 6.30/2.32  tff(c_2699, plain, (k1_xboole_0='#skF_7' | k1_relset_1('#skF_6', '#skF_7', '#skF_9')='#skF_6' | ~v1_funct_2('#skF_9', '#skF_6', '#skF_7')), inference(resolution, [status(thm)], [c_68, c_2692])).
% 6.30/2.32  tff(c_2703, plain, (k1_xboole_0='#skF_7' | k1_relat_1('#skF_9')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_70, c_135, c_2699])).
% 6.30/2.32  tff(c_2704, plain, (k1_relat_1('#skF_9')='#skF_6'), inference(splitLeft, [status(thm)], [c_2703])).
% 6.30/2.32  tff(c_3273, plain, (![A_490, B_491, D_492]: (r2_hidden('#skF_5'(A_490, B_491, k9_relat_1(A_490, B_491), D_492), k1_relat_1(A_490)) | ~r2_hidden(D_492, k9_relat_1(A_490, B_491)) | ~v1_funct_1(A_490) | ~v1_relat_1(A_490))), inference(cnfTransformation, [status(thm)], [f_72])).
% 6.30/2.32  tff(c_3287, plain, (![B_491, D_492]: (r2_hidden('#skF_5'('#skF_9', B_491, k9_relat_1('#skF_9', B_491), D_492), '#skF_6') | ~r2_hidden(D_492, k9_relat_1('#skF_9', B_491)) | ~v1_funct_1('#skF_9') | ~v1_relat_1('#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_2704, c_3273])).
% 6.30/2.32  tff(c_3294, plain, (![B_493, D_494]: (r2_hidden('#skF_5'('#skF_9', B_493, k9_relat_1('#skF_9', B_493), D_494), '#skF_6') | ~r2_hidden(D_494, k9_relat_1('#skF_9', B_493)))), inference(demodulation, [status(thm), theory('equality')], [c_106, c_72, c_3287])).
% 6.30/2.32  tff(c_4, plain, (![A_2, B_3]: (m1_subset_1(A_2, B_3) | ~r2_hidden(A_2, B_3))), inference(cnfTransformation, [status(thm)], [f_31])).
% 6.30/2.32  tff(c_3307, plain, (![B_497, D_498]: (m1_subset_1('#skF_5'('#skF_9', B_497, k9_relat_1('#skF_9', B_497), D_498), '#skF_6') | ~r2_hidden(D_498, k9_relat_1('#skF_9', B_497)))), inference(resolution, [status(thm)], [c_3294, c_4])).
% 6.30/2.32  tff(c_2907, plain, (![A_443, B_444, D_445]: (r2_hidden('#skF_5'(A_443, B_444, k9_relat_1(A_443, B_444), D_445), B_444) | ~r2_hidden(D_445, k9_relat_1(A_443, B_444)) | ~v1_funct_1(A_443) | ~v1_relat_1(A_443))), inference(cnfTransformation, [status(thm)], [f_72])).
% 6.30/2.32  tff(c_64, plain, (![F_75]: (k1_funct_1('#skF_9', F_75)!='#skF_10' | ~r2_hidden(F_75, '#skF_8') | ~m1_subset_1(F_75, '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_122])).
% 6.30/2.32  tff(c_2982, plain, (![A_443, D_445]: (k1_funct_1('#skF_9', '#skF_5'(A_443, '#skF_8', k9_relat_1(A_443, '#skF_8'), D_445))!='#skF_10' | ~m1_subset_1('#skF_5'(A_443, '#skF_8', k9_relat_1(A_443, '#skF_8'), D_445), '#skF_6') | ~r2_hidden(D_445, k9_relat_1(A_443, '#skF_8')) | ~v1_funct_1(A_443) | ~v1_relat_1(A_443))), inference(resolution, [status(thm)], [c_2907, c_64])).
% 6.30/2.32  tff(c_3311, plain, (![D_498]: (k1_funct_1('#skF_9', '#skF_5'('#skF_9', '#skF_8', k9_relat_1('#skF_9', '#skF_8'), D_498))!='#skF_10' | ~v1_funct_1('#skF_9') | ~v1_relat_1('#skF_9') | ~r2_hidden(D_498, k9_relat_1('#skF_9', '#skF_8')))), inference(resolution, [status(thm)], [c_3307, c_2982])).
% 6.30/2.32  tff(c_3316, plain, (![D_500]: (k1_funct_1('#skF_9', '#skF_5'('#skF_9', '#skF_8', k9_relat_1('#skF_9', '#skF_8'), D_500))!='#skF_10' | ~r2_hidden(D_500, k9_relat_1('#skF_9', '#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_106, c_72, c_3311])).
% 6.30/2.32  tff(c_3320, plain, (![D_55]: (D_55!='#skF_10' | ~r2_hidden(D_55, k9_relat_1('#skF_9', '#skF_8')) | ~r2_hidden(D_55, k9_relat_1('#skF_9', '#skF_8')) | ~v1_funct_1('#skF_9') | ~v1_relat_1('#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_24, c_3316])).
% 6.30/2.32  tff(c_3323, plain, (~r2_hidden('#skF_10', k9_relat_1('#skF_9', '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_106, c_72, c_3320])).
% 6.30/2.32  tff(c_207, plain, (![A_118, B_119, C_120, D_121]: (k7_relset_1(A_118, B_119, C_120, D_121)=k9_relat_1(C_120, D_121) | ~m1_subset_1(C_120, k1_zfmisc_1(k2_zfmisc_1(A_118, B_119))))), inference(cnfTransformation, [status(thm)], [f_85])).
% 6.30/2.32  tff(c_214, plain, (![D_121]: (k7_relset_1('#skF_6', '#skF_7', '#skF_9', D_121)=k9_relat_1('#skF_9', D_121))), inference(resolution, [status(thm)], [c_68, c_207])).
% 6.30/2.32  tff(c_66, plain, (r2_hidden('#skF_10', k7_relset_1('#skF_6', '#skF_7', '#skF_9', '#skF_8'))), inference(cnfTransformation, [status(thm)], [f_122])).
% 6.30/2.32  tff(c_217, plain, (r2_hidden('#skF_10', k9_relat_1('#skF_9', '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_214, c_66])).
% 6.30/2.32  tff(c_3325, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3323, c_217])).
% 6.30/2.32  tff(c_3327, plain, (k1_relat_1('#skF_9')!='#skF_6'), inference(splitRight, [status(thm)], [c_2703])).
% 6.30/2.32  tff(c_87, plain, (![A_86, B_87]: (r1_tarski(A_86, B_87) | ~m1_subset_1(A_86, k1_zfmisc_1(B_87)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 6.30/2.32  tff(c_95, plain, (r1_tarski('#skF_9', k2_zfmisc_1('#skF_6', '#skF_7'))), inference(resolution, [status(thm)], [c_68, c_87])).
% 6.30/2.32  tff(c_3326, plain, (k1_xboole_0='#skF_7'), inference(splitRight, [status(thm)], [c_2703])).
% 6.30/2.32  tff(c_8, plain, (![A_4, B_5]: (m1_subset_1(A_4, k1_zfmisc_1(B_5)) | ~r1_tarski(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_35])).
% 6.30/2.32  tff(c_227, plain, (![C_123, A_124]: (k1_xboole_0=C_123 | ~v1_funct_2(C_123, A_124, k1_xboole_0) | k1_xboole_0=A_124 | ~m1_subset_1(C_123, k1_zfmisc_1(k2_zfmisc_1(A_124, k1_xboole_0))))), inference(cnfTransformation, [status(thm)], [f_103])).
% 6.30/2.32  tff(c_232, plain, (![A_4, A_124]: (k1_xboole_0=A_4 | ~v1_funct_2(A_4, A_124, k1_xboole_0) | k1_xboole_0=A_124 | ~r1_tarski(A_4, k2_zfmisc_1(A_124, k1_xboole_0)))), inference(resolution, [status(thm)], [c_8, c_227])).
% 6.30/2.32  tff(c_4358, plain, (![A_607, A_608]: (A_607='#skF_7' | ~v1_funct_2(A_607, A_608, '#skF_7') | A_608='#skF_7' | ~r1_tarski(A_607, k2_zfmisc_1(A_608, '#skF_7')))), inference(demodulation, [status(thm), theory('equality')], [c_3326, c_3326, c_3326, c_3326, c_232])).
% 6.30/2.32  tff(c_4365, plain, ('#skF_7'='#skF_9' | ~v1_funct_2('#skF_9', '#skF_6', '#skF_7') | '#skF_7'='#skF_6'), inference(resolution, [status(thm)], [c_95, c_4358])).
% 6.30/2.32  tff(c_4370, plain, ('#skF_7'='#skF_9' | '#skF_7'='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_70, c_4365])).
% 6.30/2.32  tff(c_4371, plain, ('#skF_7'='#skF_6'), inference(splitLeft, [status(thm)], [c_4370])).
% 6.30/2.32  tff(c_4395, plain, (v1_funct_2('#skF_9', '#skF_6', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_4371, c_70])).
% 6.30/2.32  tff(c_4392, plain, (k1_relset_1('#skF_6', '#skF_6', '#skF_9')=k1_relat_1('#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_4371, c_135])).
% 6.30/2.32  tff(c_4393, plain, (r1_tarski('#skF_9', k2_zfmisc_1('#skF_6', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_4371, c_95])).
% 6.30/2.32  tff(c_2663, plain, (![B_391, C_392]: (k1_relset_1(k1_xboole_0, B_391, C_392)=k1_xboole_0 | ~v1_funct_2(C_392, k1_xboole_0, B_391) | ~m1_subset_1(C_392, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_391))))), inference(cnfTransformation, [status(thm)], [f_103])).
% 6.30/2.32  tff(c_2668, plain, (![B_391, A_4]: (k1_relset_1(k1_xboole_0, B_391, A_4)=k1_xboole_0 | ~v1_funct_2(A_4, k1_xboole_0, B_391) | ~r1_tarski(A_4, k2_zfmisc_1(k1_xboole_0, B_391)))), inference(resolution, [status(thm)], [c_8, c_2663])).
% 6.30/2.32  tff(c_3330, plain, (![B_391, A_4]: (k1_relset_1('#skF_7', B_391, A_4)='#skF_7' | ~v1_funct_2(A_4, '#skF_7', B_391) | ~r1_tarski(A_4, k2_zfmisc_1('#skF_7', B_391)))), inference(demodulation, [status(thm), theory('equality')], [c_3326, c_3326, c_3326, c_3326, c_2668])).
% 6.30/2.32  tff(c_5228, plain, (![B_671, A_672]: (k1_relset_1('#skF_6', B_671, A_672)='#skF_6' | ~v1_funct_2(A_672, '#skF_6', B_671) | ~r1_tarski(A_672, k2_zfmisc_1('#skF_6', B_671)))), inference(demodulation, [status(thm), theory('equality')], [c_4371, c_4371, c_4371, c_4371, c_3330])).
% 6.30/2.32  tff(c_5231, plain, (k1_relset_1('#skF_6', '#skF_6', '#skF_9')='#skF_6' | ~v1_funct_2('#skF_9', '#skF_6', '#skF_6')), inference(resolution, [status(thm)], [c_4393, c_5228])).
% 6.30/2.32  tff(c_5238, plain, (k1_relat_1('#skF_9')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_4395, c_4392, c_5231])).
% 6.30/2.32  tff(c_5240, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3327, c_5238])).
% 6.30/2.32  tff(c_5241, plain, ('#skF_7'='#skF_9'), inference(splitRight, [status(thm)], [c_4370])).
% 6.30/2.32  tff(c_2, plain, (![A_1]: (r1_tarski(k1_xboole_0, A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 6.30/2.32  tff(c_115, plain, (![A_92, B_93]: (v1_relat_1(A_92) | ~v1_relat_1(B_93) | ~r1_tarski(A_92, B_93))), inference(resolution, [status(thm)], [c_8, c_96])).
% 6.30/2.32  tff(c_125, plain, (![A_1]: (v1_relat_1(k1_xboole_0) | ~v1_relat_1(A_1))), inference(resolution, [status(thm)], [c_2, c_115])).
% 6.30/2.32  tff(c_136, plain, (![A_1]: (~v1_relat_1(A_1))), inference(splitLeft, [status(thm)], [c_125])).
% 6.30/2.32  tff(c_141, plain, $false, inference(negUnitSimplification, [status(thm)], [c_136, c_106])).
% 6.30/2.32  tff(c_142, plain, (v1_relat_1(k1_xboole_0)), inference(splitRight, [status(thm)], [c_125])).
% 6.30/2.32  tff(c_2604, plain, (![A_381, B_382, C_383]: (r2_hidden(k4_tarski('#skF_1'(A_381, B_382, C_383), A_381), C_383) | ~r2_hidden(A_381, k9_relat_1(C_383, B_382)) | ~v1_relat_1(C_383))), inference(cnfTransformation, [status(thm)], [f_55])).
% 6.30/2.32  tff(c_46, plain, (![B_60, A_59]: (~r1_tarski(B_60, A_59) | ~r2_hidden(A_59, B_60))), inference(cnfTransformation, [status(thm)], [f_77])).
% 6.30/2.32  tff(c_2684, plain, (![C_396, A_397, B_398]: (~r1_tarski(C_396, k4_tarski('#skF_1'(A_397, B_398, C_396), A_397)) | ~r2_hidden(A_397, k9_relat_1(C_396, B_398)) | ~v1_relat_1(C_396))), inference(resolution, [status(thm)], [c_2604, c_46])).
% 6.30/2.32  tff(c_2688, plain, (![A_397, B_398]: (~r2_hidden(A_397, k9_relat_1(k1_xboole_0, B_398)) | ~v1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_2, c_2684])).
% 6.30/2.32  tff(c_2691, plain, (![A_397, B_398]: (~r2_hidden(A_397, k9_relat_1(k1_xboole_0, B_398)))), inference(demodulation, [status(thm), theory('equality')], [c_142, c_2688])).
% 6.30/2.32  tff(c_3389, plain, (![A_397, B_398]: (~r2_hidden(A_397, k9_relat_1('#skF_7', B_398)))), inference(demodulation, [status(thm), theory('equality')], [c_3326, c_2691])).
% 6.30/2.32  tff(c_5256, plain, (![A_397, B_398]: (~r2_hidden(A_397, k9_relat_1('#skF_9', B_398)))), inference(demodulation, [status(thm), theory('equality')], [c_5241, c_3389])).
% 6.30/2.32  tff(c_5341, plain, $false, inference(negUnitSimplification, [status(thm)], [c_5256, c_217])).
% 6.30/2.32  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.30/2.32  
% 6.30/2.32  Inference rules
% 6.30/2.32  ----------------------
% 6.30/2.32  #Ref     : 0
% 6.30/2.32  #Sup     : 1036
% 6.30/2.32  #Fact    : 0
% 6.30/2.32  #Define  : 0
% 6.30/2.32  #Split   : 15
% 6.30/2.32  #Chain   : 0
% 6.30/2.32  #Close   : 0
% 6.30/2.32  
% 6.30/2.32  Ordering : KBO
% 6.30/2.32  
% 6.30/2.32  Simplification rules
% 6.30/2.32  ----------------------
% 6.30/2.32  #Subsume      : 150
% 6.30/2.32  #Demod        : 597
% 6.30/2.32  #Tautology    : 192
% 6.30/2.32  #SimpNegUnit  : 16
% 6.30/2.32  #BackRed      : 232
% 6.30/2.32  
% 6.30/2.32  #Partial instantiations: 0
% 6.30/2.32  #Strategies tried      : 1
% 6.30/2.32  
% 6.30/2.32  Timing (in seconds)
% 6.30/2.32  ----------------------
% 6.30/2.32  Preprocessing        : 0.38
% 6.30/2.32  Parsing              : 0.19
% 6.30/2.32  CNF conversion       : 0.03
% 6.30/2.32  Main loop            : 1.10
% 6.30/2.32  Inferencing          : 0.39
% 6.30/2.32  Reduction            : 0.32
% 6.30/2.32  Demodulation         : 0.22
% 6.30/2.32  BG Simplification    : 0.05
% 6.30/2.32  Subsumption          : 0.23
% 6.30/2.32  Abstraction          : 0.06
% 6.30/2.32  MUC search           : 0.00
% 6.30/2.33  Cooper               : 0.00
% 6.30/2.33  Total                : 1.54
% 6.30/2.33  Index Insertion      : 0.00
% 6.30/2.33  Index Deletion       : 0.00
% 6.30/2.33  Index Matching       : 0.00
% 6.30/2.33  BG Taut test         : 0.00
%------------------------------------------------------------------------------
