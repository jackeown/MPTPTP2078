%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:16:32 EST 2020

% Result     : Theorem 8.65s
% Output     : CNFRefutation 8.92s
% Verified   : 
% Statistics : Number of formulae       :   98 ( 160 expanded)
%              Number of leaves         :   50 (  80 expanded)
%              Depth                    :   12
%              Number of atoms          :  160 ( 381 expanded)
%              Number of equality atoms :   29 (  71 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k1_relset_1 > k9_relat_1 > k4_tarski > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_11 > #skF_15 > #skF_1 > #skF_4 > #skF_14 > #skF_13 > #skF_5 > #skF_2 > #skF_6 > #skF_8 > #skF_3 > #skF_7 > #skF_9 > #skF_12 > #skF_10

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_11',type,(
    '#skF_11': $i )).

tff('#skF_15',type,(
    '#skF_15': $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k7_relset_1,type,(
    k7_relset_1: ( $i * $i * $i * $i ) > $i )).

tff('#skF_14',type,(
    '#skF_14': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_13',type,(
    '#skF_13': $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': ( $i * $i ) > $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

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

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_9',type,(
    '#skF_9': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_12',type,(
    '#skF_12': $i )).

tff('#skF_10',type,(
    '#skF_10': ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_167,negated_conjecture,(
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

tff(f_122,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_116,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_71,axiom,(
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

tff(f_126,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_148,axiom,(
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

tff(f_37,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

tff(f_130,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_33,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_97,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A)
        & v1_funct_1(B) )
     => ! [C] :
          ( r2_hidden(C,k1_relat_1(B))
         => r2_hidden(k1_funct_1(B,C),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t172_funct_1)).

tff(f_112,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

tff(f_54,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k9_relat_1(C,B))
      <=> ? [D] :
            ( r2_hidden(D,k1_relat_1(C))
            & r2_hidden(k4_tarski(D,A),C)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t143_relat_1)).

tff(c_94,plain,(
    m1_subset_1('#skF_14',k1_zfmisc_1(k2_zfmisc_1('#skF_11','#skF_12'))) ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_185,plain,(
    ! [C_149,B_150,A_151] :
      ( v5_relat_1(C_149,B_150)
      | ~ m1_subset_1(C_149,k1_zfmisc_1(k2_zfmisc_1(A_151,B_150))) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_194,plain,(
    v5_relat_1('#skF_14','#skF_12') ),
    inference(resolution,[status(thm)],[c_94,c_185])).

tff(c_135,plain,(
    ! [C_138,A_139,B_140] :
      ( v1_relat_1(C_138)
      | ~ m1_subset_1(C_138,k1_zfmisc_1(k2_zfmisc_1(A_139,B_140))) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_144,plain,(
    v1_relat_1('#skF_14') ),
    inference(resolution,[status(thm)],[c_94,c_135])).

tff(c_98,plain,(
    v1_funct_1('#skF_14') ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_22,plain,(
    ! [A_16,B_39,D_54] :
      ( k1_funct_1(A_16,'#skF_6'(A_16,B_39,k9_relat_1(A_16,B_39),D_54)) = D_54
      | ~ r2_hidden(D_54,k9_relat_1(A_16,B_39))
      | ~ v1_funct_1(A_16)
      | ~ v1_relat_1(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_96,plain,(
    v1_funct_2('#skF_14','#skF_11','#skF_12') ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_196,plain,(
    ! [A_152,B_153,C_154] :
      ( k1_relset_1(A_152,B_153,C_154) = k1_relat_1(C_154)
      | ~ m1_subset_1(C_154,k1_zfmisc_1(k2_zfmisc_1(A_152,B_153))) ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_205,plain,(
    k1_relset_1('#skF_11','#skF_12','#skF_14') = k1_relat_1('#skF_14') ),
    inference(resolution,[status(thm)],[c_94,c_196])).

tff(c_2920,plain,(
    ! [B_568,A_569,C_570] :
      ( k1_xboole_0 = B_568
      | k1_relset_1(A_569,B_568,C_570) = A_569
      | ~ v1_funct_2(C_570,A_569,B_568)
      | ~ m1_subset_1(C_570,k1_zfmisc_1(k2_zfmisc_1(A_569,B_568))) ) ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_2935,plain,
    ( k1_xboole_0 = '#skF_12'
    | k1_relset_1('#skF_11','#skF_12','#skF_14') = '#skF_11'
    | ~ v1_funct_2('#skF_14','#skF_11','#skF_12') ),
    inference(resolution,[status(thm)],[c_94,c_2920])).

tff(c_2941,plain,
    ( k1_xboole_0 = '#skF_12'
    | k1_relat_1('#skF_14') = '#skF_11' ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_205,c_2935])).

tff(c_2942,plain,(
    k1_relat_1('#skF_14') = '#skF_11' ),
    inference(splitLeft,[status(thm)],[c_2941])).

tff(c_5004,plain,(
    ! [A_639,B_640,D_641] :
      ( r2_hidden('#skF_6'(A_639,B_640,k9_relat_1(A_639,B_640),D_641),k1_relat_1(A_639))
      | ~ r2_hidden(D_641,k9_relat_1(A_639,B_640))
      | ~ v1_funct_1(A_639)
      | ~ v1_relat_1(A_639) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_5038,plain,(
    ! [B_640,D_641] :
      ( r2_hidden('#skF_6'('#skF_14',B_640,k9_relat_1('#skF_14',B_640),D_641),'#skF_11')
      | ~ r2_hidden(D_641,k9_relat_1('#skF_14',B_640))
      | ~ v1_funct_1('#skF_14')
      | ~ v1_relat_1('#skF_14') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2942,c_5004])).

tff(c_5063,plain,(
    ! [B_645,D_646] :
      ( r2_hidden('#skF_6'('#skF_14',B_645,k9_relat_1('#skF_14',B_645),D_646),'#skF_11')
      | ~ r2_hidden(D_646,k9_relat_1('#skF_14',B_645)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_144,c_98,c_5038])).

tff(c_8,plain,(
    ! [A_6,B_7] :
      ( m1_subset_1(A_6,B_7)
      | ~ r2_hidden(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_5381,plain,(
    ! [B_656,D_657] :
      ( m1_subset_1('#skF_6'('#skF_14',B_656,k9_relat_1('#skF_14',B_656),D_657),'#skF_11')
      | ~ r2_hidden(D_657,k9_relat_1('#skF_14',B_656)) ) ),
    inference(resolution,[status(thm)],[c_5063,c_8])).

tff(c_3071,plain,(
    ! [A_574,B_575,D_576] :
      ( r2_hidden('#skF_6'(A_574,B_575,k9_relat_1(A_574,B_575),D_576),B_575)
      | ~ r2_hidden(D_576,k9_relat_1(A_574,B_575))
      | ~ v1_funct_1(A_574)
      | ~ v1_relat_1(A_574) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_90,plain,(
    ! [F_127] :
      ( k1_funct_1('#skF_14',F_127) != '#skF_15'
      | ~ r2_hidden(F_127,'#skF_13')
      | ~ m1_subset_1(F_127,'#skF_11') ) ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_3226,plain,(
    ! [A_574,D_576] :
      ( k1_funct_1('#skF_14','#skF_6'(A_574,'#skF_13',k9_relat_1(A_574,'#skF_13'),D_576)) != '#skF_15'
      | ~ m1_subset_1('#skF_6'(A_574,'#skF_13',k9_relat_1(A_574,'#skF_13'),D_576),'#skF_11')
      | ~ r2_hidden(D_576,k9_relat_1(A_574,'#skF_13'))
      | ~ v1_funct_1(A_574)
      | ~ v1_relat_1(A_574) ) ),
    inference(resolution,[status(thm)],[c_3071,c_90])).

tff(c_5385,plain,(
    ! [D_657] :
      ( k1_funct_1('#skF_14','#skF_6'('#skF_14','#skF_13',k9_relat_1('#skF_14','#skF_13'),D_657)) != '#skF_15'
      | ~ v1_funct_1('#skF_14')
      | ~ v1_relat_1('#skF_14')
      | ~ r2_hidden(D_657,k9_relat_1('#skF_14','#skF_13')) ) ),
    inference(resolution,[status(thm)],[c_5381,c_3226])).

tff(c_8355,plain,(
    ! [D_765] :
      ( k1_funct_1('#skF_14','#skF_6'('#skF_14','#skF_13',k9_relat_1('#skF_14','#skF_13'),D_765)) != '#skF_15'
      | ~ r2_hidden(D_765,k9_relat_1('#skF_14','#skF_13')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_144,c_98,c_5385])).

tff(c_8359,plain,(
    ! [D_54] :
      ( D_54 != '#skF_15'
      | ~ r2_hidden(D_54,k9_relat_1('#skF_14','#skF_13'))
      | ~ r2_hidden(D_54,k9_relat_1('#skF_14','#skF_13'))
      | ~ v1_funct_1('#skF_14')
      | ~ v1_relat_1('#skF_14') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_8355])).

tff(c_8362,plain,(
    ~ r2_hidden('#skF_15',k9_relat_1('#skF_14','#skF_13')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_144,c_98,c_8359])).

tff(c_379,plain,(
    ! [A_203,B_204,C_205,D_206] :
      ( k7_relset_1(A_203,B_204,C_205,D_206) = k9_relat_1(C_205,D_206)
      | ~ m1_subset_1(C_205,k1_zfmisc_1(k2_zfmisc_1(A_203,B_204))) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_386,plain,(
    ! [D_206] : k7_relset_1('#skF_11','#skF_12','#skF_14',D_206) = k9_relat_1('#skF_14',D_206) ),
    inference(resolution,[status(thm)],[c_94,c_379])).

tff(c_92,plain,(
    r2_hidden('#skF_15',k7_relset_1('#skF_11','#skF_12','#skF_14','#skF_13')) ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_390,plain,(
    r2_hidden('#skF_15',k9_relat_1('#skF_14','#skF_13')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_386,c_92])).

tff(c_8364,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_8362,c_390])).

tff(c_8365,plain,(
    k1_xboole_0 = '#skF_12' ),
    inference(splitRight,[status(thm)],[c_2941])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_6,plain,(
    ! [A_5] : r1_tarski(k1_xboole_0,A_5) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_2243,plain,(
    ! [B_459,C_460,A_461] :
      ( r2_hidden(k1_funct_1(B_459,C_460),A_461)
      | ~ r2_hidden(C_460,k1_relat_1(B_459))
      | ~ v1_funct_1(B_459)
      | ~ v5_relat_1(B_459,A_461)
      | ~ v1_relat_1(B_459) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_66,plain,(
    ! [B_106,A_105] :
      ( ~ r1_tarski(B_106,A_105)
      | ~ r2_hidden(A_105,B_106) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_2677,plain,(
    ! [A_525,B_526,C_527] :
      ( ~ r1_tarski(A_525,k1_funct_1(B_526,C_527))
      | ~ r2_hidden(C_527,k1_relat_1(B_526))
      | ~ v1_funct_1(B_526)
      | ~ v5_relat_1(B_526,A_525)
      | ~ v1_relat_1(B_526) ) ),
    inference(resolution,[status(thm)],[c_2243,c_66])).

tff(c_2684,plain,(
    ! [C_528,B_529] :
      ( ~ r2_hidden(C_528,k1_relat_1(B_529))
      | ~ v1_funct_1(B_529)
      | ~ v5_relat_1(B_529,k1_xboole_0)
      | ~ v1_relat_1(B_529) ) ),
    inference(resolution,[status(thm)],[c_6,c_2677])).

tff(c_2718,plain,(
    ! [B_530] :
      ( ~ v1_funct_1(B_530)
      | ~ v5_relat_1(B_530,k1_xboole_0)
      | ~ v1_relat_1(B_530)
      | v1_xboole_0(k1_relat_1(B_530)) ) ),
    inference(resolution,[status(thm)],[c_4,c_2684])).

tff(c_436,plain,(
    ! [A_208,B_209,C_210] :
      ( r2_hidden('#skF_2'(A_208,B_209,C_210),k1_relat_1(C_210))
      | ~ r2_hidden(A_208,k9_relat_1(C_210,B_209))
      | ~ v1_relat_1(C_210) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_453,plain,(
    ! [C_211,A_212,B_213] :
      ( ~ v1_xboole_0(k1_relat_1(C_211))
      | ~ r2_hidden(A_212,k9_relat_1(C_211,B_213))
      | ~ v1_relat_1(C_211) ) ),
    inference(resolution,[status(thm)],[c_436,c_2])).

tff(c_456,plain,
    ( ~ v1_xboole_0(k1_relat_1('#skF_14'))
    | ~ v1_relat_1('#skF_14') ),
    inference(resolution,[status(thm)],[c_390,c_453])).

tff(c_471,plain,(
    ~ v1_xboole_0(k1_relat_1('#skF_14')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_144,c_456])).

tff(c_2721,plain,
    ( ~ v1_funct_1('#skF_14')
    | ~ v5_relat_1('#skF_14',k1_xboole_0)
    | ~ v1_relat_1('#skF_14') ),
    inference(resolution,[status(thm)],[c_2718,c_471])).

tff(c_2724,plain,(
    ~ v5_relat_1('#skF_14',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_144,c_98,c_2721])).

tff(c_8376,plain,(
    ~ v5_relat_1('#skF_14','#skF_12') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8365,c_2724])).

tff(c_8400,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_194,c_8376])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n019.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 18:42:52 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.65/2.97  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.65/2.98  
% 8.65/2.98  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.65/2.98  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k1_relset_1 > k9_relat_1 > k4_tarski > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_11 > #skF_15 > #skF_1 > #skF_4 > #skF_14 > #skF_13 > #skF_5 > #skF_2 > #skF_6 > #skF_8 > #skF_3 > #skF_7 > #skF_9 > #skF_12 > #skF_10
% 8.65/2.98  
% 8.65/2.98  %Foreground sorts:
% 8.65/2.98  
% 8.65/2.98  
% 8.65/2.98  %Background operators:
% 8.65/2.98  
% 8.65/2.98  
% 8.65/2.98  %Foreground operators:
% 8.65/2.98  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 8.65/2.98  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.65/2.98  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 8.65/2.98  tff('#skF_11', type, '#skF_11': $i).
% 8.65/2.98  tff('#skF_15', type, '#skF_15': $i).
% 8.65/2.98  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 8.65/2.98  tff('#skF_1', type, '#skF_1': $i > $i).
% 8.65/2.98  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 8.65/2.98  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 8.65/2.98  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 8.65/2.98  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 8.65/2.98  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 8.65/2.98  tff('#skF_14', type, '#skF_14': $i).
% 8.65/2.98  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 8.65/2.98  tff('#skF_13', type, '#skF_13': $i).
% 8.65/2.98  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 8.65/2.98  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 8.65/2.98  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 8.65/2.98  tff('#skF_6', type, '#skF_6': ($i * $i * $i * $i) > $i).
% 8.65/2.98  tff('#skF_8', type, '#skF_8': ($i * $i) > $i).
% 8.65/2.98  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 8.65/2.98  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 8.65/2.98  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 8.65/2.98  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 8.65/2.98  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.65/2.98  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 8.65/2.98  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 8.65/2.98  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 8.65/2.98  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.65/2.98  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 8.65/2.98  tff('#skF_7', type, '#skF_7': ($i * $i) > $i).
% 8.65/2.98  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 8.65/2.98  tff('#skF_9', type, '#skF_9': ($i * $i) > $i).
% 8.65/2.98  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 8.65/2.98  tff('#skF_12', type, '#skF_12': $i).
% 8.65/2.98  tff('#skF_10', type, '#skF_10': ($i * $i * $i) > $i).
% 8.65/2.98  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 8.65/2.98  
% 8.92/2.99  tff(f_167, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: ~(r2_hidden(E, k7_relset_1(A, B, D, C)) & (![F]: (m1_subset_1(F, A) => ~(r2_hidden(F, C) & (E = k1_funct_1(D, F))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t116_funct_2)).
% 8.92/2.99  tff(f_122, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 8.92/2.99  tff(f_116, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 8.92/2.99  tff(f_71, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B, C]: ((C = k9_relat_1(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (?[E]: ((r2_hidden(E, k1_relat_1(A)) & r2_hidden(E, B)) & (D = k1_funct_1(A, E)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d12_funct_1)).
% 8.92/2.99  tff(f_126, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 8.92/2.99  tff(f_148, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 8.92/2.99  tff(f_37, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_subset)).
% 8.92/2.99  tff(f_130, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 8.92/2.99  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 8.92/2.99  tff(f_33, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 8.92/2.99  tff(f_97, axiom, (![A, B]: (((v1_relat_1(B) & v5_relat_1(B, A)) & v1_funct_1(B)) => (![C]: (r2_hidden(C, k1_relat_1(B)) => r2_hidden(k1_funct_1(B, C), A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t172_funct_1)).
% 8.92/2.99  tff(f_112, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 8.92/2.99  tff(f_54, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k9_relat_1(C, B)) <=> (?[D]: ((r2_hidden(D, k1_relat_1(C)) & r2_hidden(k4_tarski(D, A), C)) & r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t143_relat_1)).
% 8.92/2.99  tff(c_94, plain, (m1_subset_1('#skF_14', k1_zfmisc_1(k2_zfmisc_1('#skF_11', '#skF_12')))), inference(cnfTransformation, [status(thm)], [f_167])).
% 8.92/2.99  tff(c_185, plain, (![C_149, B_150, A_151]: (v5_relat_1(C_149, B_150) | ~m1_subset_1(C_149, k1_zfmisc_1(k2_zfmisc_1(A_151, B_150))))), inference(cnfTransformation, [status(thm)], [f_122])).
% 8.92/2.99  tff(c_194, plain, (v5_relat_1('#skF_14', '#skF_12')), inference(resolution, [status(thm)], [c_94, c_185])).
% 8.92/2.99  tff(c_135, plain, (![C_138, A_139, B_140]: (v1_relat_1(C_138) | ~m1_subset_1(C_138, k1_zfmisc_1(k2_zfmisc_1(A_139, B_140))))), inference(cnfTransformation, [status(thm)], [f_116])).
% 8.92/2.99  tff(c_144, plain, (v1_relat_1('#skF_14')), inference(resolution, [status(thm)], [c_94, c_135])).
% 8.92/2.99  tff(c_98, plain, (v1_funct_1('#skF_14')), inference(cnfTransformation, [status(thm)], [f_167])).
% 8.92/2.99  tff(c_22, plain, (![A_16, B_39, D_54]: (k1_funct_1(A_16, '#skF_6'(A_16, B_39, k9_relat_1(A_16, B_39), D_54))=D_54 | ~r2_hidden(D_54, k9_relat_1(A_16, B_39)) | ~v1_funct_1(A_16) | ~v1_relat_1(A_16))), inference(cnfTransformation, [status(thm)], [f_71])).
% 8.92/2.99  tff(c_96, plain, (v1_funct_2('#skF_14', '#skF_11', '#skF_12')), inference(cnfTransformation, [status(thm)], [f_167])).
% 8.92/2.99  tff(c_196, plain, (![A_152, B_153, C_154]: (k1_relset_1(A_152, B_153, C_154)=k1_relat_1(C_154) | ~m1_subset_1(C_154, k1_zfmisc_1(k2_zfmisc_1(A_152, B_153))))), inference(cnfTransformation, [status(thm)], [f_126])).
% 8.92/2.99  tff(c_205, plain, (k1_relset_1('#skF_11', '#skF_12', '#skF_14')=k1_relat_1('#skF_14')), inference(resolution, [status(thm)], [c_94, c_196])).
% 8.92/2.99  tff(c_2920, plain, (![B_568, A_569, C_570]: (k1_xboole_0=B_568 | k1_relset_1(A_569, B_568, C_570)=A_569 | ~v1_funct_2(C_570, A_569, B_568) | ~m1_subset_1(C_570, k1_zfmisc_1(k2_zfmisc_1(A_569, B_568))))), inference(cnfTransformation, [status(thm)], [f_148])).
% 8.92/2.99  tff(c_2935, plain, (k1_xboole_0='#skF_12' | k1_relset_1('#skF_11', '#skF_12', '#skF_14')='#skF_11' | ~v1_funct_2('#skF_14', '#skF_11', '#skF_12')), inference(resolution, [status(thm)], [c_94, c_2920])).
% 8.92/2.99  tff(c_2941, plain, (k1_xboole_0='#skF_12' | k1_relat_1('#skF_14')='#skF_11'), inference(demodulation, [status(thm), theory('equality')], [c_96, c_205, c_2935])).
% 8.92/2.99  tff(c_2942, plain, (k1_relat_1('#skF_14')='#skF_11'), inference(splitLeft, [status(thm)], [c_2941])).
% 8.92/2.99  tff(c_5004, plain, (![A_639, B_640, D_641]: (r2_hidden('#skF_6'(A_639, B_640, k9_relat_1(A_639, B_640), D_641), k1_relat_1(A_639)) | ~r2_hidden(D_641, k9_relat_1(A_639, B_640)) | ~v1_funct_1(A_639) | ~v1_relat_1(A_639))), inference(cnfTransformation, [status(thm)], [f_71])).
% 8.92/2.99  tff(c_5038, plain, (![B_640, D_641]: (r2_hidden('#skF_6'('#skF_14', B_640, k9_relat_1('#skF_14', B_640), D_641), '#skF_11') | ~r2_hidden(D_641, k9_relat_1('#skF_14', B_640)) | ~v1_funct_1('#skF_14') | ~v1_relat_1('#skF_14'))), inference(superposition, [status(thm), theory('equality')], [c_2942, c_5004])).
% 8.92/2.99  tff(c_5063, plain, (![B_645, D_646]: (r2_hidden('#skF_6'('#skF_14', B_645, k9_relat_1('#skF_14', B_645), D_646), '#skF_11') | ~r2_hidden(D_646, k9_relat_1('#skF_14', B_645)))), inference(demodulation, [status(thm), theory('equality')], [c_144, c_98, c_5038])).
% 8.92/2.99  tff(c_8, plain, (![A_6, B_7]: (m1_subset_1(A_6, B_7) | ~r2_hidden(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_37])).
% 8.92/2.99  tff(c_5381, plain, (![B_656, D_657]: (m1_subset_1('#skF_6'('#skF_14', B_656, k9_relat_1('#skF_14', B_656), D_657), '#skF_11') | ~r2_hidden(D_657, k9_relat_1('#skF_14', B_656)))), inference(resolution, [status(thm)], [c_5063, c_8])).
% 8.92/2.99  tff(c_3071, plain, (![A_574, B_575, D_576]: (r2_hidden('#skF_6'(A_574, B_575, k9_relat_1(A_574, B_575), D_576), B_575) | ~r2_hidden(D_576, k9_relat_1(A_574, B_575)) | ~v1_funct_1(A_574) | ~v1_relat_1(A_574))), inference(cnfTransformation, [status(thm)], [f_71])).
% 8.92/2.99  tff(c_90, plain, (![F_127]: (k1_funct_1('#skF_14', F_127)!='#skF_15' | ~r2_hidden(F_127, '#skF_13') | ~m1_subset_1(F_127, '#skF_11'))), inference(cnfTransformation, [status(thm)], [f_167])).
% 8.92/2.99  tff(c_3226, plain, (![A_574, D_576]: (k1_funct_1('#skF_14', '#skF_6'(A_574, '#skF_13', k9_relat_1(A_574, '#skF_13'), D_576))!='#skF_15' | ~m1_subset_1('#skF_6'(A_574, '#skF_13', k9_relat_1(A_574, '#skF_13'), D_576), '#skF_11') | ~r2_hidden(D_576, k9_relat_1(A_574, '#skF_13')) | ~v1_funct_1(A_574) | ~v1_relat_1(A_574))), inference(resolution, [status(thm)], [c_3071, c_90])).
% 8.92/2.99  tff(c_5385, plain, (![D_657]: (k1_funct_1('#skF_14', '#skF_6'('#skF_14', '#skF_13', k9_relat_1('#skF_14', '#skF_13'), D_657))!='#skF_15' | ~v1_funct_1('#skF_14') | ~v1_relat_1('#skF_14') | ~r2_hidden(D_657, k9_relat_1('#skF_14', '#skF_13')))), inference(resolution, [status(thm)], [c_5381, c_3226])).
% 8.92/2.99  tff(c_8355, plain, (![D_765]: (k1_funct_1('#skF_14', '#skF_6'('#skF_14', '#skF_13', k9_relat_1('#skF_14', '#skF_13'), D_765))!='#skF_15' | ~r2_hidden(D_765, k9_relat_1('#skF_14', '#skF_13')))), inference(demodulation, [status(thm), theory('equality')], [c_144, c_98, c_5385])).
% 8.92/2.99  tff(c_8359, plain, (![D_54]: (D_54!='#skF_15' | ~r2_hidden(D_54, k9_relat_1('#skF_14', '#skF_13')) | ~r2_hidden(D_54, k9_relat_1('#skF_14', '#skF_13')) | ~v1_funct_1('#skF_14') | ~v1_relat_1('#skF_14'))), inference(superposition, [status(thm), theory('equality')], [c_22, c_8355])).
% 8.92/2.99  tff(c_8362, plain, (~r2_hidden('#skF_15', k9_relat_1('#skF_14', '#skF_13'))), inference(demodulation, [status(thm), theory('equality')], [c_144, c_98, c_8359])).
% 8.92/2.99  tff(c_379, plain, (![A_203, B_204, C_205, D_206]: (k7_relset_1(A_203, B_204, C_205, D_206)=k9_relat_1(C_205, D_206) | ~m1_subset_1(C_205, k1_zfmisc_1(k2_zfmisc_1(A_203, B_204))))), inference(cnfTransformation, [status(thm)], [f_130])).
% 8.92/2.99  tff(c_386, plain, (![D_206]: (k7_relset_1('#skF_11', '#skF_12', '#skF_14', D_206)=k9_relat_1('#skF_14', D_206))), inference(resolution, [status(thm)], [c_94, c_379])).
% 8.92/2.99  tff(c_92, plain, (r2_hidden('#skF_15', k7_relset_1('#skF_11', '#skF_12', '#skF_14', '#skF_13'))), inference(cnfTransformation, [status(thm)], [f_167])).
% 8.92/2.99  tff(c_390, plain, (r2_hidden('#skF_15', k9_relat_1('#skF_14', '#skF_13'))), inference(demodulation, [status(thm), theory('equality')], [c_386, c_92])).
% 8.92/2.99  tff(c_8364, plain, $false, inference(negUnitSimplification, [status(thm)], [c_8362, c_390])).
% 8.92/2.99  tff(c_8365, plain, (k1_xboole_0='#skF_12'), inference(splitRight, [status(thm)], [c_2941])).
% 8.92/2.99  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 8.92/2.99  tff(c_6, plain, (![A_5]: (r1_tarski(k1_xboole_0, A_5))), inference(cnfTransformation, [status(thm)], [f_33])).
% 8.92/2.99  tff(c_2243, plain, (![B_459, C_460, A_461]: (r2_hidden(k1_funct_1(B_459, C_460), A_461) | ~r2_hidden(C_460, k1_relat_1(B_459)) | ~v1_funct_1(B_459) | ~v5_relat_1(B_459, A_461) | ~v1_relat_1(B_459))), inference(cnfTransformation, [status(thm)], [f_97])).
% 8.92/2.99  tff(c_66, plain, (![B_106, A_105]: (~r1_tarski(B_106, A_105) | ~r2_hidden(A_105, B_106))), inference(cnfTransformation, [status(thm)], [f_112])).
% 8.92/2.99  tff(c_2677, plain, (![A_525, B_526, C_527]: (~r1_tarski(A_525, k1_funct_1(B_526, C_527)) | ~r2_hidden(C_527, k1_relat_1(B_526)) | ~v1_funct_1(B_526) | ~v5_relat_1(B_526, A_525) | ~v1_relat_1(B_526))), inference(resolution, [status(thm)], [c_2243, c_66])).
% 8.92/2.99  tff(c_2684, plain, (![C_528, B_529]: (~r2_hidden(C_528, k1_relat_1(B_529)) | ~v1_funct_1(B_529) | ~v5_relat_1(B_529, k1_xboole_0) | ~v1_relat_1(B_529))), inference(resolution, [status(thm)], [c_6, c_2677])).
% 8.92/2.99  tff(c_2718, plain, (![B_530]: (~v1_funct_1(B_530) | ~v5_relat_1(B_530, k1_xboole_0) | ~v1_relat_1(B_530) | v1_xboole_0(k1_relat_1(B_530)))), inference(resolution, [status(thm)], [c_4, c_2684])).
% 8.92/2.99  tff(c_436, plain, (![A_208, B_209, C_210]: (r2_hidden('#skF_2'(A_208, B_209, C_210), k1_relat_1(C_210)) | ~r2_hidden(A_208, k9_relat_1(C_210, B_209)) | ~v1_relat_1(C_210))), inference(cnfTransformation, [status(thm)], [f_54])).
% 8.92/2.99  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 8.92/2.99  tff(c_453, plain, (![C_211, A_212, B_213]: (~v1_xboole_0(k1_relat_1(C_211)) | ~r2_hidden(A_212, k9_relat_1(C_211, B_213)) | ~v1_relat_1(C_211))), inference(resolution, [status(thm)], [c_436, c_2])).
% 8.92/2.99  tff(c_456, plain, (~v1_xboole_0(k1_relat_1('#skF_14')) | ~v1_relat_1('#skF_14')), inference(resolution, [status(thm)], [c_390, c_453])).
% 8.92/2.99  tff(c_471, plain, (~v1_xboole_0(k1_relat_1('#skF_14'))), inference(demodulation, [status(thm), theory('equality')], [c_144, c_456])).
% 8.92/2.99  tff(c_2721, plain, (~v1_funct_1('#skF_14') | ~v5_relat_1('#skF_14', k1_xboole_0) | ~v1_relat_1('#skF_14')), inference(resolution, [status(thm)], [c_2718, c_471])).
% 8.92/2.99  tff(c_2724, plain, (~v5_relat_1('#skF_14', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_144, c_98, c_2721])).
% 8.92/2.99  tff(c_8376, plain, (~v5_relat_1('#skF_14', '#skF_12')), inference(demodulation, [status(thm), theory('equality')], [c_8365, c_2724])).
% 8.92/2.99  tff(c_8400, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_194, c_8376])).
% 8.92/2.99  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.92/2.99  
% 8.92/2.99  Inference rules
% 8.92/2.99  ----------------------
% 8.92/2.99  #Ref     : 0
% 8.92/2.99  #Sup     : 1746
% 8.92/2.99  #Fact    : 0
% 8.92/2.99  #Define  : 0
% 8.92/2.99  #Split   : 20
% 8.92/2.99  #Chain   : 0
% 8.92/2.99  #Close   : 0
% 8.92/2.99  
% 8.92/2.99  Ordering : KBO
% 8.92/2.99  
% 8.92/2.99  Simplification rules
% 8.92/2.99  ----------------------
% 8.92/2.99  #Subsume      : 230
% 8.92/2.99  #Demod        : 379
% 8.92/2.99  #Tautology    : 46
% 8.92/2.99  #SimpNegUnit  : 30
% 8.92/2.99  #BackRed      : 82
% 8.92/2.99  
% 8.92/2.99  #Partial instantiations: 0
% 8.92/2.99  #Strategies tried      : 1
% 8.92/2.99  
% 8.92/2.99  Timing (in seconds)
% 8.92/2.99  ----------------------
% 8.92/3.00  Preprocessing        : 0.38
% 8.92/3.00  Parsing              : 0.19
% 8.92/3.00  CNF conversion       : 0.03
% 8.92/3.00  Main loop            : 1.84
% 8.92/3.00  Inferencing          : 0.56
% 8.92/3.00  Reduction            : 0.43
% 8.92/3.00  Demodulation         : 0.29
% 8.92/3.00  BG Simplification    : 0.07
% 8.92/3.00  Subsumption          : 0.62
% 8.92/3.00  Abstraction          : 0.09
% 8.92/3.00  MUC search           : 0.00
% 8.92/3.00  Cooper               : 0.00
% 8.92/3.00  Total                : 2.26
% 8.92/3.00  Index Insertion      : 0.00
% 8.92/3.00  Index Deletion       : 0.00
% 8.92/3.00  Index Matching       : 0.00
% 8.92/3.00  BG Taut test         : 0.00
%------------------------------------------------------------------------------
