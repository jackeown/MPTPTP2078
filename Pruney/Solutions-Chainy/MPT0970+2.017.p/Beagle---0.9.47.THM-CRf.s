%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:11:21 EST 2020

% Result     : Theorem 5.74s
% Output     : CNFRefutation 5.78s
% Verified   : 
% Statistics : Number of formulae       :  130 ( 474 expanded)
%              Number of leaves         :   38 ( 178 expanded)
%              Depth                    :   13
%              Number of atoms          :  237 (1345 expanded)
%              Number of equality atoms :   69 ( 458 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1 > #skF_6

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

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

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_6',type,(
    '#skF_6': $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_119,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( ! [D] :
              ~ ( r2_hidden(D,B)
                & ! [E] :
                    ~ ( r2_hidden(E,A)
                      & D = k1_funct_1(C,E) ) )
         => k2_relset_1(A,B,C) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_funct_2)).

tff(f_82,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_68,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_74,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_32,axiom,(
    ! [A,B] :
      ( ! [C] :
          ( r2_hidden(C,A)
        <=> r2_hidden(C,B) )
     => A = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tarski)).

tff(f_41,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

tff(f_78,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_100,axiom,(
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

tff(f_59,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r2_hidden(A,k1_relat_1(B))
       => r2_hidden(k1_funct_1(B,A),k2_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_funct_1)).

tff(f_34,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_64,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

tff(c_50,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_227,plain,(
    ! [A_84,B_85,C_86] :
      ( k2_relset_1(A_84,B_85,C_86) = k2_relat_1(C_86)
      | ~ m1_subset_1(C_86,k1_zfmisc_1(k2_zfmisc_1(A_84,B_85))) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_236,plain,(
    k2_relset_1('#skF_3','#skF_4','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_50,c_227])).

tff(c_48,plain,(
    k2_relset_1('#skF_3','#skF_4','#skF_5') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_237,plain,(
    k2_relat_1('#skF_5') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_236,c_48])).

tff(c_86,plain,(
    ! [C_47,A_48,B_49] :
      ( v1_relat_1(C_47)
      | ~ m1_subset_1(C_47,k1_zfmisc_1(k2_zfmisc_1(A_48,B_49))) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_95,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_50,c_86])).

tff(c_123,plain,(
    ! [C_58,B_59,A_60] :
      ( v5_relat_1(C_58,B_59)
      | ~ m1_subset_1(C_58,k1_zfmisc_1(k2_zfmisc_1(A_60,B_59))) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_132,plain,(
    v5_relat_1('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_50,c_123])).

tff(c_20,plain,(
    ! [B_12,A_11] :
      ( r1_tarski(k2_relat_1(B_12),A_11)
      | ~ v5_relat_1(B_12,A_11)
      | ~ v1_relat_1(B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_16,plain,(
    ! [A_9,B_10] :
      ( m1_subset_1(A_9,k1_zfmisc_1(B_10))
      | ~ r1_tarski(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_2794,plain,(
    ! [A_368,B_369] :
      ( r2_hidden('#skF_1'(A_368,B_369),B_369)
      | r2_hidden('#skF_2'(A_368,B_369),A_368)
      | B_369 = A_368 ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_487,plain,(
    ! [A_126,B_127] :
      ( r2_hidden('#skF_1'(A_126,B_127),B_127)
      | r2_hidden('#skF_2'(A_126,B_127),A_126)
      | B_127 = A_126 ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_12,plain,(
    ! [C_8,A_5,B_6] :
      ( r2_hidden(C_8,A_5)
      | ~ r2_hidden(C_8,B_6)
      | ~ m1_subset_1(B_6,k1_zfmisc_1(A_5)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_1643,plain,(
    ! [A_245,B_246,A_247] :
      ( r2_hidden('#skF_2'(A_245,B_246),A_247)
      | ~ m1_subset_1(A_245,k1_zfmisc_1(A_247))
      | r2_hidden('#skF_1'(A_245,B_246),B_246)
      | B_246 = A_245 ) ),
    inference(resolution,[status(thm)],[c_487,c_12])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),B_2)
      | ~ r2_hidden('#skF_2'(A_1,B_2),B_2)
      | B_2 = A_1 ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_1670,plain,(
    ! [A_245,A_247] :
      ( ~ m1_subset_1(A_245,k1_zfmisc_1(A_247))
      | r2_hidden('#skF_1'(A_245,A_247),A_247)
      | A_247 = A_245 ) ),
    inference(resolution,[status(thm)],[c_1643,c_4])).

tff(c_58,plain,(
    ! [D_35] :
      ( r2_hidden('#skF_6'(D_35),'#skF_3')
      | ~ r2_hidden(D_35,'#skF_4') ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_52,plain,(
    v1_funct_2('#skF_5','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_477,plain,(
    ! [A_123,B_124,C_125] :
      ( k1_relset_1(A_123,B_124,C_125) = k1_relat_1(C_125)
      | ~ m1_subset_1(C_125,k1_zfmisc_1(k2_zfmisc_1(A_123,B_124))) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_486,plain,(
    k1_relset_1('#skF_3','#skF_4','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_50,c_477])).

tff(c_1048,plain,(
    ! [B_197,A_198,C_199] :
      ( k1_xboole_0 = B_197
      | k1_relset_1(A_198,B_197,C_199) = A_198
      | ~ v1_funct_2(C_199,A_198,B_197)
      | ~ m1_subset_1(C_199,k1_zfmisc_1(k2_zfmisc_1(A_198,B_197))) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_1055,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relset_1('#skF_3','#skF_4','#skF_5') = '#skF_3'
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_50,c_1048])).

tff(c_1059,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relat_1('#skF_5') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_486,c_1055])).

tff(c_1060,plain,(
    k1_relat_1('#skF_5') = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_1059])).

tff(c_54,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_56,plain,(
    ! [D_35] :
      ( k1_funct_1('#skF_5','#skF_6'(D_35)) = D_35
      | ~ r2_hidden(D_35,'#skF_4') ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_782,plain,(
    ! [B_155,A_156] :
      ( r2_hidden(k1_funct_1(B_155,A_156),k2_relat_1(B_155))
      | ~ r2_hidden(A_156,k1_relat_1(B_155))
      | ~ v1_funct_1(B_155)
      | ~ v1_relat_1(B_155) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_793,plain,(
    ! [D_35] :
      ( r2_hidden(D_35,k2_relat_1('#skF_5'))
      | ~ r2_hidden('#skF_6'(D_35),k1_relat_1('#skF_5'))
      | ~ v1_funct_1('#skF_5')
      | ~ v1_relat_1('#skF_5')
      | ~ r2_hidden(D_35,'#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_56,c_782])).

tff(c_799,plain,(
    ! [D_35] :
      ( r2_hidden(D_35,k2_relat_1('#skF_5'))
      | ~ r2_hidden('#skF_6'(D_35),k1_relat_1('#skF_5'))
      | ~ r2_hidden(D_35,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_95,c_54,c_793])).

tff(c_1094,plain,(
    ! [D_202] :
      ( r2_hidden(D_202,k2_relat_1('#skF_5'))
      | ~ r2_hidden('#skF_6'(D_202),'#skF_3')
      | ~ r2_hidden(D_202,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1060,c_799])).

tff(c_1103,plain,(
    ! [D_35] :
      ( r2_hidden(D_35,k2_relat_1('#skF_5'))
      | ~ r2_hidden(D_35,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_58,c_1094])).

tff(c_286,plain,(
    ! [A_91,B_92] :
      ( ~ r2_hidden('#skF_1'(A_91,B_92),A_91)
      | r2_hidden('#skF_2'(A_91,B_92),A_91)
      | B_92 = A_91 ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_1970,plain,(
    ! [A_281,B_282,A_283] :
      ( r2_hidden('#skF_2'(A_281,B_282),A_283)
      | ~ m1_subset_1(A_281,k1_zfmisc_1(A_283))
      | ~ r2_hidden('#skF_1'(A_281,B_282),A_281)
      | B_282 = A_281 ) ),
    inference(resolution,[status(thm)],[c_286,c_12])).

tff(c_2377,plain,(
    ! [B_340,A_341] :
      ( r2_hidden('#skF_2'(k2_relat_1('#skF_5'),B_340),A_341)
      | ~ m1_subset_1(k2_relat_1('#skF_5'),k1_zfmisc_1(A_341))
      | k2_relat_1('#skF_5') = B_340
      | ~ r2_hidden('#skF_1'(k2_relat_1('#skF_5'),B_340),'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_1103,c_1970])).

tff(c_1122,plain,(
    ! [D_206] :
      ( r2_hidden(D_206,k2_relat_1('#skF_5'))
      | ~ r2_hidden(D_206,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_58,c_1094])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),A_1)
      | ~ r2_hidden('#skF_2'(A_1,B_2),B_2)
      | B_2 = A_1 ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_1140,plain,(
    ! [B_2] :
      ( ~ r2_hidden('#skF_2'(k2_relat_1('#skF_5'),B_2),B_2)
      | k2_relat_1('#skF_5') = B_2
      | ~ r2_hidden('#skF_1'(k2_relat_1('#skF_5'),B_2),'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_1122,c_2])).

tff(c_2399,plain,(
    ! [A_342] :
      ( ~ m1_subset_1(k2_relat_1('#skF_5'),k1_zfmisc_1(A_342))
      | k2_relat_1('#skF_5') = A_342
      | ~ r2_hidden('#skF_1'(k2_relat_1('#skF_5'),A_342),'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_2377,c_1140])).

tff(c_2413,plain,
    ( ~ m1_subset_1(k2_relat_1('#skF_5'),k1_zfmisc_1('#skF_4'))
    | k2_relat_1('#skF_5') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_1670,c_2399])).

tff(c_2424,plain,(
    ~ m1_subset_1(k2_relat_1('#skF_5'),k1_zfmisc_1('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_237,c_237,c_2413])).

tff(c_2428,plain,(
    ~ r1_tarski(k2_relat_1('#skF_5'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_16,c_2424])).

tff(c_2431,plain,
    ( ~ v5_relat_1('#skF_5','#skF_4')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_20,c_2428])).

tff(c_2435,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_95,c_132,c_2431])).

tff(c_2436,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_1059])).

tff(c_10,plain,(
    ! [A_4] : r1_tarski(k1_xboole_0,A_4) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_96,plain,(
    ! [A_50,A_51,B_52] :
      ( v1_relat_1(A_50)
      | ~ r1_tarski(A_50,k2_zfmisc_1(A_51,B_52)) ) ),
    inference(resolution,[status(thm)],[c_16,c_86])).

tff(c_106,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_10,c_96])).

tff(c_150,plain,(
    ! [A_65,B_66,A_67] :
      ( v5_relat_1(A_65,B_66)
      | ~ r1_tarski(A_65,k2_zfmisc_1(A_67,B_66)) ) ),
    inference(resolution,[status(thm)],[c_16,c_123])).

tff(c_165,plain,(
    ! [B_66] : v5_relat_1(k1_xboole_0,B_66) ),
    inference(resolution,[status(thm)],[c_10,c_150])).

tff(c_24,plain,(
    ! [B_16,A_15] :
      ( ~ r1_tarski(B_16,A_15)
      | ~ r2_hidden(A_15,B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_545,plain,(
    ! [A_139,B_140] :
      ( ~ r1_tarski(A_139,'#skF_2'(A_139,B_140))
      | r2_hidden('#skF_1'(A_139,B_140),B_140)
      | B_140 = A_139 ) ),
    inference(resolution,[status(thm)],[c_487,c_24])).

tff(c_554,plain,(
    ! [B_141] :
      ( r2_hidden('#skF_1'(k1_xboole_0,B_141),B_141)
      | k1_xboole_0 = B_141 ) ),
    inference(resolution,[status(thm)],[c_10,c_545])).

tff(c_593,plain,(
    ! [B_145,A_146] :
      ( r2_hidden('#skF_1'(k1_xboole_0,B_145),A_146)
      | ~ m1_subset_1(B_145,k1_zfmisc_1(A_146))
      | k1_xboole_0 = B_145 ) ),
    inference(resolution,[status(thm)],[c_554,c_12])).

tff(c_293,plain,(
    ! [A_91,B_92] :
      ( ~ r1_tarski(A_91,'#skF_2'(A_91,B_92))
      | ~ r2_hidden('#skF_1'(A_91,B_92),A_91)
      | B_92 = A_91 ) ),
    inference(resolution,[status(thm)],[c_286,c_24])).

tff(c_597,plain,(
    ! [B_145] :
      ( ~ r1_tarski(k1_xboole_0,'#skF_2'(k1_xboole_0,B_145))
      | ~ m1_subset_1(B_145,k1_zfmisc_1(k1_xboole_0))
      | k1_xboole_0 = B_145 ) ),
    inference(resolution,[status(thm)],[c_593,c_293])).

tff(c_612,plain,(
    ! [B_147] :
      ( ~ m1_subset_1(B_147,k1_zfmisc_1(k1_xboole_0))
      | k1_xboole_0 = B_147 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_597])).

tff(c_618,plain,(
    ! [A_148] :
      ( k1_xboole_0 = A_148
      | ~ r1_tarski(A_148,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_16,c_612])).

tff(c_640,plain,(
    ! [B_152] :
      ( k2_relat_1(B_152) = k1_xboole_0
      | ~ v5_relat_1(B_152,k1_xboole_0)
      | ~ v1_relat_1(B_152) ) ),
    inference(resolution,[status(thm)],[c_20,c_618])).

tff(c_676,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_165,c_640])).

tff(c_703,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_106,c_676])).

tff(c_2457,plain,(
    k2_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2436,c_2436,c_703])).

tff(c_2472,plain,(
    ! [A_4] : r1_tarski('#skF_4',A_4) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2436,c_10])).

tff(c_66,plain,(
    ! [A_41,B_42] :
      ( r1_tarski(A_41,B_42)
      | ~ m1_subset_1(A_41,k1_zfmisc_1(B_42)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_70,plain,(
    r1_tarski('#skF_5',k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_50,c_66])).

tff(c_587,plain,(
    ! [C_143,A_144] :
      ( k1_xboole_0 = C_143
      | ~ v1_funct_2(C_143,A_144,k1_xboole_0)
      | k1_xboole_0 = A_144
      | ~ m1_subset_1(C_143,k1_zfmisc_1(k2_zfmisc_1(A_144,k1_xboole_0))) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_592,plain,(
    ! [A_9,A_144] :
      ( k1_xboole_0 = A_9
      | ~ v1_funct_2(A_9,A_144,k1_xboole_0)
      | k1_xboole_0 = A_144
      | ~ r1_tarski(A_9,k2_zfmisc_1(A_144,k1_xboole_0)) ) ),
    inference(resolution,[status(thm)],[c_16,c_587])).

tff(c_2626,plain,(
    ! [A_351,A_352] :
      ( A_351 = '#skF_4'
      | ~ v1_funct_2(A_351,A_352,'#skF_4')
      | A_352 = '#skF_4'
      | ~ r1_tarski(A_351,k2_zfmisc_1(A_352,'#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2436,c_2436,c_2436,c_2436,c_592])).

tff(c_2637,plain,
    ( '#skF_5' = '#skF_4'
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_4')
    | '#skF_3' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_70,c_2626])).

tff(c_2643,plain,
    ( '#skF_5' = '#skF_4'
    | '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_2637])).

tff(c_2644,plain,(
    '#skF_3' = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_2643])).

tff(c_172,plain,(
    ! [C_71,A_72,B_73] :
      ( r2_hidden(C_71,A_72)
      | ~ r2_hidden(C_71,B_73)
      | ~ m1_subset_1(B_73,k1_zfmisc_1(A_72)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_184,plain,(
    ! [D_77,A_78] :
      ( r2_hidden('#skF_6'(D_77),A_78)
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_78))
      | ~ r2_hidden(D_77,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_58,c_172])).

tff(c_256,plain,(
    ! [A_88,D_89] :
      ( ~ r1_tarski(A_88,'#skF_6'(D_89))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_88))
      | ~ r2_hidden(D_89,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_184,c_24])).

tff(c_266,plain,(
    ! [D_89] :
      ( ~ m1_subset_1('#skF_3',k1_zfmisc_1(k1_xboole_0))
      | ~ r2_hidden(D_89,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_10,c_256])).

tff(c_267,plain,(
    ~ m1_subset_1('#skF_3',k1_zfmisc_1(k1_xboole_0)) ),
    inference(splitLeft,[status(thm)],[c_266])).

tff(c_271,plain,(
    ~ r1_tarski('#skF_3',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_16,c_267])).

tff(c_2467,plain,(
    ~ r1_tarski('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2436,c_271])).

tff(c_2646,plain,(
    ~ r1_tarski('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2644,c_2467])).

tff(c_2670,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2472,c_2646])).

tff(c_2671,plain,(
    '#skF_5' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_2643])).

tff(c_2682,plain,(
    k2_relat_1('#skF_4') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2671,c_237])).

tff(c_2699,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2457,c_2682])).

tff(c_2700,plain,(
    ! [D_89] : ~ r2_hidden(D_89,'#skF_4') ),
    inference(splitRight,[status(thm)],[c_266])).

tff(c_2822,plain,(
    ! [B_370] :
      ( r2_hidden('#skF_1'('#skF_4',B_370),B_370)
      | B_370 = '#skF_4' ) ),
    inference(resolution,[status(thm)],[c_2794,c_2700])).

tff(c_3033,plain,(
    ! [B_388,A_389] :
      ( r2_hidden('#skF_1'('#skF_4',B_388),A_389)
      | ~ m1_subset_1(B_388,k1_zfmisc_1(A_389))
      | B_388 = '#skF_4' ) ),
    inference(resolution,[status(thm)],[c_2822,c_12])).

tff(c_3050,plain,(
    ! [B_390] :
      ( ~ m1_subset_1(B_390,k1_zfmisc_1('#skF_4'))
      | B_390 = '#skF_4' ) ),
    inference(resolution,[status(thm)],[c_3033,c_2700])).

tff(c_3110,plain,(
    ! [A_392] :
      ( A_392 = '#skF_4'
      | ~ r1_tarski(A_392,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_16,c_3050])).

tff(c_3192,plain,(
    ! [B_397] :
      ( k2_relat_1(B_397) = '#skF_4'
      | ~ v5_relat_1(B_397,'#skF_4')
      | ~ v1_relat_1(B_397) ) ),
    inference(resolution,[status(thm)],[c_20,c_3110])).

tff(c_3219,plain,
    ( k2_relat_1('#skF_5') = '#skF_4'
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_132,c_3192])).

tff(c_3240,plain,(
    k2_relat_1('#skF_5') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_95,c_3219])).

tff(c_3242,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_237,c_3240])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n015.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 10:27:23 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.74/2.11  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.78/2.12  
% 5.78/2.12  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.78/2.13  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1 > #skF_6
% 5.78/2.13  
% 5.78/2.13  %Foreground sorts:
% 5.78/2.13  
% 5.78/2.13  
% 5.78/2.13  %Background operators:
% 5.78/2.13  
% 5.78/2.13  
% 5.78/2.13  %Foreground operators:
% 5.78/2.13  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 5.78/2.13  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 5.78/2.13  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.78/2.13  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.78/2.13  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.78/2.13  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.78/2.13  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 5.78/2.13  tff('#skF_5', type, '#skF_5': $i).
% 5.78/2.13  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 5.78/2.13  tff('#skF_3', type, '#skF_3': $i).
% 5.78/2.13  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 5.78/2.13  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 5.78/2.13  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.78/2.13  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 5.78/2.13  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.78/2.13  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.78/2.13  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 5.78/2.13  tff('#skF_4', type, '#skF_4': $i).
% 5.78/2.13  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.78/2.13  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 5.78/2.13  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 5.78/2.13  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 5.78/2.13  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 5.78/2.13  tff('#skF_6', type, '#skF_6': $i > $i).
% 5.78/2.13  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.78/2.13  
% 5.78/2.15  tff(f_119, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((![D]: ~(r2_hidden(D, B) & (![E]: ~(r2_hidden(E, A) & (D = k1_funct_1(C, E)))))) => (k2_relset_1(A, B, C) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t16_funct_2)).
% 5.78/2.15  tff(f_82, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 5.78/2.15  tff(f_68, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 5.78/2.15  tff(f_74, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 5.78/2.15  tff(f_51, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 5.78/2.15  tff(f_45, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 5.78/2.15  tff(f_32, axiom, (![A, B]: ((![C]: (r2_hidden(C, A) <=> r2_hidden(C, B))) => (A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_tarski)).
% 5.78/2.15  tff(f_41, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_subset_1)).
% 5.78/2.15  tff(f_78, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 5.78/2.15  tff(f_100, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 5.78/2.15  tff(f_59, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r2_hidden(A, k1_relat_1(B)) => r2_hidden(k1_funct_1(B, A), k2_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_funct_1)).
% 5.78/2.15  tff(f_34, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 5.78/2.15  tff(f_64, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 5.78/2.15  tff(c_50, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_119])).
% 5.78/2.15  tff(c_227, plain, (![A_84, B_85, C_86]: (k2_relset_1(A_84, B_85, C_86)=k2_relat_1(C_86) | ~m1_subset_1(C_86, k1_zfmisc_1(k2_zfmisc_1(A_84, B_85))))), inference(cnfTransformation, [status(thm)], [f_82])).
% 5.78/2.15  tff(c_236, plain, (k2_relset_1('#skF_3', '#skF_4', '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_50, c_227])).
% 5.78/2.15  tff(c_48, plain, (k2_relset_1('#skF_3', '#skF_4', '#skF_5')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_119])).
% 5.78/2.15  tff(c_237, plain, (k2_relat_1('#skF_5')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_236, c_48])).
% 5.78/2.15  tff(c_86, plain, (![C_47, A_48, B_49]: (v1_relat_1(C_47) | ~m1_subset_1(C_47, k1_zfmisc_1(k2_zfmisc_1(A_48, B_49))))), inference(cnfTransformation, [status(thm)], [f_68])).
% 5.78/2.15  tff(c_95, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_50, c_86])).
% 5.78/2.15  tff(c_123, plain, (![C_58, B_59, A_60]: (v5_relat_1(C_58, B_59) | ~m1_subset_1(C_58, k1_zfmisc_1(k2_zfmisc_1(A_60, B_59))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 5.78/2.15  tff(c_132, plain, (v5_relat_1('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_50, c_123])).
% 5.78/2.15  tff(c_20, plain, (![B_12, A_11]: (r1_tarski(k2_relat_1(B_12), A_11) | ~v5_relat_1(B_12, A_11) | ~v1_relat_1(B_12))), inference(cnfTransformation, [status(thm)], [f_51])).
% 5.78/2.15  tff(c_16, plain, (![A_9, B_10]: (m1_subset_1(A_9, k1_zfmisc_1(B_10)) | ~r1_tarski(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_45])).
% 5.78/2.15  tff(c_2794, plain, (![A_368, B_369]: (r2_hidden('#skF_1'(A_368, B_369), B_369) | r2_hidden('#skF_2'(A_368, B_369), A_368) | B_369=A_368)), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.78/2.15  tff(c_487, plain, (![A_126, B_127]: (r2_hidden('#skF_1'(A_126, B_127), B_127) | r2_hidden('#skF_2'(A_126, B_127), A_126) | B_127=A_126)), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.78/2.15  tff(c_12, plain, (![C_8, A_5, B_6]: (r2_hidden(C_8, A_5) | ~r2_hidden(C_8, B_6) | ~m1_subset_1(B_6, k1_zfmisc_1(A_5)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 5.78/2.15  tff(c_1643, plain, (![A_245, B_246, A_247]: (r2_hidden('#skF_2'(A_245, B_246), A_247) | ~m1_subset_1(A_245, k1_zfmisc_1(A_247)) | r2_hidden('#skF_1'(A_245, B_246), B_246) | B_246=A_245)), inference(resolution, [status(thm)], [c_487, c_12])).
% 5.78/2.15  tff(c_4, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), B_2) | ~r2_hidden('#skF_2'(A_1, B_2), B_2) | B_2=A_1)), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.78/2.15  tff(c_1670, plain, (![A_245, A_247]: (~m1_subset_1(A_245, k1_zfmisc_1(A_247)) | r2_hidden('#skF_1'(A_245, A_247), A_247) | A_247=A_245)), inference(resolution, [status(thm)], [c_1643, c_4])).
% 5.78/2.15  tff(c_58, plain, (![D_35]: (r2_hidden('#skF_6'(D_35), '#skF_3') | ~r2_hidden(D_35, '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_119])).
% 5.78/2.15  tff(c_52, plain, (v1_funct_2('#skF_5', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_119])).
% 5.78/2.15  tff(c_477, plain, (![A_123, B_124, C_125]: (k1_relset_1(A_123, B_124, C_125)=k1_relat_1(C_125) | ~m1_subset_1(C_125, k1_zfmisc_1(k2_zfmisc_1(A_123, B_124))))), inference(cnfTransformation, [status(thm)], [f_78])).
% 5.78/2.15  tff(c_486, plain, (k1_relset_1('#skF_3', '#skF_4', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_50, c_477])).
% 5.78/2.15  tff(c_1048, plain, (![B_197, A_198, C_199]: (k1_xboole_0=B_197 | k1_relset_1(A_198, B_197, C_199)=A_198 | ~v1_funct_2(C_199, A_198, B_197) | ~m1_subset_1(C_199, k1_zfmisc_1(k2_zfmisc_1(A_198, B_197))))), inference(cnfTransformation, [status(thm)], [f_100])).
% 5.78/2.15  tff(c_1055, plain, (k1_xboole_0='#skF_4' | k1_relset_1('#skF_3', '#skF_4', '#skF_5')='#skF_3' | ~v1_funct_2('#skF_5', '#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_50, c_1048])).
% 5.78/2.15  tff(c_1059, plain, (k1_xboole_0='#skF_4' | k1_relat_1('#skF_5')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_52, c_486, c_1055])).
% 5.78/2.15  tff(c_1060, plain, (k1_relat_1('#skF_5')='#skF_3'), inference(splitLeft, [status(thm)], [c_1059])).
% 5.78/2.15  tff(c_54, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_119])).
% 5.78/2.15  tff(c_56, plain, (![D_35]: (k1_funct_1('#skF_5', '#skF_6'(D_35))=D_35 | ~r2_hidden(D_35, '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_119])).
% 5.78/2.15  tff(c_782, plain, (![B_155, A_156]: (r2_hidden(k1_funct_1(B_155, A_156), k2_relat_1(B_155)) | ~r2_hidden(A_156, k1_relat_1(B_155)) | ~v1_funct_1(B_155) | ~v1_relat_1(B_155))), inference(cnfTransformation, [status(thm)], [f_59])).
% 5.78/2.15  tff(c_793, plain, (![D_35]: (r2_hidden(D_35, k2_relat_1('#skF_5')) | ~r2_hidden('#skF_6'(D_35), k1_relat_1('#skF_5')) | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5') | ~r2_hidden(D_35, '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_56, c_782])).
% 5.78/2.15  tff(c_799, plain, (![D_35]: (r2_hidden(D_35, k2_relat_1('#skF_5')) | ~r2_hidden('#skF_6'(D_35), k1_relat_1('#skF_5')) | ~r2_hidden(D_35, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_95, c_54, c_793])).
% 5.78/2.15  tff(c_1094, plain, (![D_202]: (r2_hidden(D_202, k2_relat_1('#skF_5')) | ~r2_hidden('#skF_6'(D_202), '#skF_3') | ~r2_hidden(D_202, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_1060, c_799])).
% 5.78/2.15  tff(c_1103, plain, (![D_35]: (r2_hidden(D_35, k2_relat_1('#skF_5')) | ~r2_hidden(D_35, '#skF_4'))), inference(resolution, [status(thm)], [c_58, c_1094])).
% 5.78/2.15  tff(c_286, plain, (![A_91, B_92]: (~r2_hidden('#skF_1'(A_91, B_92), A_91) | r2_hidden('#skF_2'(A_91, B_92), A_91) | B_92=A_91)), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.78/2.15  tff(c_1970, plain, (![A_281, B_282, A_283]: (r2_hidden('#skF_2'(A_281, B_282), A_283) | ~m1_subset_1(A_281, k1_zfmisc_1(A_283)) | ~r2_hidden('#skF_1'(A_281, B_282), A_281) | B_282=A_281)), inference(resolution, [status(thm)], [c_286, c_12])).
% 5.78/2.15  tff(c_2377, plain, (![B_340, A_341]: (r2_hidden('#skF_2'(k2_relat_1('#skF_5'), B_340), A_341) | ~m1_subset_1(k2_relat_1('#skF_5'), k1_zfmisc_1(A_341)) | k2_relat_1('#skF_5')=B_340 | ~r2_hidden('#skF_1'(k2_relat_1('#skF_5'), B_340), '#skF_4'))), inference(resolution, [status(thm)], [c_1103, c_1970])).
% 5.78/2.15  tff(c_1122, plain, (![D_206]: (r2_hidden(D_206, k2_relat_1('#skF_5')) | ~r2_hidden(D_206, '#skF_4'))), inference(resolution, [status(thm)], [c_58, c_1094])).
% 5.78/2.15  tff(c_2, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), A_1) | ~r2_hidden('#skF_2'(A_1, B_2), B_2) | B_2=A_1)), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.78/2.15  tff(c_1140, plain, (![B_2]: (~r2_hidden('#skF_2'(k2_relat_1('#skF_5'), B_2), B_2) | k2_relat_1('#skF_5')=B_2 | ~r2_hidden('#skF_1'(k2_relat_1('#skF_5'), B_2), '#skF_4'))), inference(resolution, [status(thm)], [c_1122, c_2])).
% 5.78/2.15  tff(c_2399, plain, (![A_342]: (~m1_subset_1(k2_relat_1('#skF_5'), k1_zfmisc_1(A_342)) | k2_relat_1('#skF_5')=A_342 | ~r2_hidden('#skF_1'(k2_relat_1('#skF_5'), A_342), '#skF_4'))), inference(resolution, [status(thm)], [c_2377, c_1140])).
% 5.78/2.15  tff(c_2413, plain, (~m1_subset_1(k2_relat_1('#skF_5'), k1_zfmisc_1('#skF_4')) | k2_relat_1('#skF_5')='#skF_4'), inference(resolution, [status(thm)], [c_1670, c_2399])).
% 5.78/2.15  tff(c_2424, plain, (~m1_subset_1(k2_relat_1('#skF_5'), k1_zfmisc_1('#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_237, c_237, c_2413])).
% 5.78/2.15  tff(c_2428, plain, (~r1_tarski(k2_relat_1('#skF_5'), '#skF_4')), inference(resolution, [status(thm)], [c_16, c_2424])).
% 5.78/2.15  tff(c_2431, plain, (~v5_relat_1('#skF_5', '#skF_4') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_20, c_2428])).
% 5.78/2.15  tff(c_2435, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_95, c_132, c_2431])).
% 5.78/2.15  tff(c_2436, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_1059])).
% 5.78/2.15  tff(c_10, plain, (![A_4]: (r1_tarski(k1_xboole_0, A_4))), inference(cnfTransformation, [status(thm)], [f_34])).
% 5.78/2.15  tff(c_96, plain, (![A_50, A_51, B_52]: (v1_relat_1(A_50) | ~r1_tarski(A_50, k2_zfmisc_1(A_51, B_52)))), inference(resolution, [status(thm)], [c_16, c_86])).
% 5.78/2.15  tff(c_106, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_10, c_96])).
% 5.78/2.15  tff(c_150, plain, (![A_65, B_66, A_67]: (v5_relat_1(A_65, B_66) | ~r1_tarski(A_65, k2_zfmisc_1(A_67, B_66)))), inference(resolution, [status(thm)], [c_16, c_123])).
% 5.78/2.15  tff(c_165, plain, (![B_66]: (v5_relat_1(k1_xboole_0, B_66))), inference(resolution, [status(thm)], [c_10, c_150])).
% 5.78/2.15  tff(c_24, plain, (![B_16, A_15]: (~r1_tarski(B_16, A_15) | ~r2_hidden(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_64])).
% 5.78/2.15  tff(c_545, plain, (![A_139, B_140]: (~r1_tarski(A_139, '#skF_2'(A_139, B_140)) | r2_hidden('#skF_1'(A_139, B_140), B_140) | B_140=A_139)), inference(resolution, [status(thm)], [c_487, c_24])).
% 5.78/2.15  tff(c_554, plain, (![B_141]: (r2_hidden('#skF_1'(k1_xboole_0, B_141), B_141) | k1_xboole_0=B_141)), inference(resolution, [status(thm)], [c_10, c_545])).
% 5.78/2.15  tff(c_593, plain, (![B_145, A_146]: (r2_hidden('#skF_1'(k1_xboole_0, B_145), A_146) | ~m1_subset_1(B_145, k1_zfmisc_1(A_146)) | k1_xboole_0=B_145)), inference(resolution, [status(thm)], [c_554, c_12])).
% 5.78/2.15  tff(c_293, plain, (![A_91, B_92]: (~r1_tarski(A_91, '#skF_2'(A_91, B_92)) | ~r2_hidden('#skF_1'(A_91, B_92), A_91) | B_92=A_91)), inference(resolution, [status(thm)], [c_286, c_24])).
% 5.78/2.15  tff(c_597, plain, (![B_145]: (~r1_tarski(k1_xboole_0, '#skF_2'(k1_xboole_0, B_145)) | ~m1_subset_1(B_145, k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0=B_145)), inference(resolution, [status(thm)], [c_593, c_293])).
% 5.78/2.15  tff(c_612, plain, (![B_147]: (~m1_subset_1(B_147, k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0=B_147)), inference(demodulation, [status(thm), theory('equality')], [c_10, c_597])).
% 5.78/2.15  tff(c_618, plain, (![A_148]: (k1_xboole_0=A_148 | ~r1_tarski(A_148, k1_xboole_0))), inference(resolution, [status(thm)], [c_16, c_612])).
% 5.78/2.15  tff(c_640, plain, (![B_152]: (k2_relat_1(B_152)=k1_xboole_0 | ~v5_relat_1(B_152, k1_xboole_0) | ~v1_relat_1(B_152))), inference(resolution, [status(thm)], [c_20, c_618])).
% 5.78/2.15  tff(c_676, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_165, c_640])).
% 5.78/2.15  tff(c_703, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_106, c_676])).
% 5.78/2.15  tff(c_2457, plain, (k2_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_2436, c_2436, c_703])).
% 5.78/2.15  tff(c_2472, plain, (![A_4]: (r1_tarski('#skF_4', A_4))), inference(demodulation, [status(thm), theory('equality')], [c_2436, c_10])).
% 5.78/2.15  tff(c_66, plain, (![A_41, B_42]: (r1_tarski(A_41, B_42) | ~m1_subset_1(A_41, k1_zfmisc_1(B_42)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 5.78/2.15  tff(c_70, plain, (r1_tarski('#skF_5', k2_zfmisc_1('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_50, c_66])).
% 5.78/2.15  tff(c_587, plain, (![C_143, A_144]: (k1_xboole_0=C_143 | ~v1_funct_2(C_143, A_144, k1_xboole_0) | k1_xboole_0=A_144 | ~m1_subset_1(C_143, k1_zfmisc_1(k2_zfmisc_1(A_144, k1_xboole_0))))), inference(cnfTransformation, [status(thm)], [f_100])).
% 5.78/2.15  tff(c_592, plain, (![A_9, A_144]: (k1_xboole_0=A_9 | ~v1_funct_2(A_9, A_144, k1_xboole_0) | k1_xboole_0=A_144 | ~r1_tarski(A_9, k2_zfmisc_1(A_144, k1_xboole_0)))), inference(resolution, [status(thm)], [c_16, c_587])).
% 5.78/2.15  tff(c_2626, plain, (![A_351, A_352]: (A_351='#skF_4' | ~v1_funct_2(A_351, A_352, '#skF_4') | A_352='#skF_4' | ~r1_tarski(A_351, k2_zfmisc_1(A_352, '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_2436, c_2436, c_2436, c_2436, c_592])).
% 5.78/2.15  tff(c_2637, plain, ('#skF_5'='#skF_4' | ~v1_funct_2('#skF_5', '#skF_3', '#skF_4') | '#skF_3'='#skF_4'), inference(resolution, [status(thm)], [c_70, c_2626])).
% 5.78/2.15  tff(c_2643, plain, ('#skF_5'='#skF_4' | '#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_52, c_2637])).
% 5.78/2.15  tff(c_2644, plain, ('#skF_3'='#skF_4'), inference(splitLeft, [status(thm)], [c_2643])).
% 5.78/2.15  tff(c_172, plain, (![C_71, A_72, B_73]: (r2_hidden(C_71, A_72) | ~r2_hidden(C_71, B_73) | ~m1_subset_1(B_73, k1_zfmisc_1(A_72)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 5.78/2.15  tff(c_184, plain, (![D_77, A_78]: (r2_hidden('#skF_6'(D_77), A_78) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_78)) | ~r2_hidden(D_77, '#skF_4'))), inference(resolution, [status(thm)], [c_58, c_172])).
% 5.78/2.15  tff(c_256, plain, (![A_88, D_89]: (~r1_tarski(A_88, '#skF_6'(D_89)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_88)) | ~r2_hidden(D_89, '#skF_4'))), inference(resolution, [status(thm)], [c_184, c_24])).
% 5.78/2.15  tff(c_266, plain, (![D_89]: (~m1_subset_1('#skF_3', k1_zfmisc_1(k1_xboole_0)) | ~r2_hidden(D_89, '#skF_4'))), inference(resolution, [status(thm)], [c_10, c_256])).
% 5.78/2.15  tff(c_267, plain, (~m1_subset_1('#skF_3', k1_zfmisc_1(k1_xboole_0))), inference(splitLeft, [status(thm)], [c_266])).
% 5.78/2.15  tff(c_271, plain, (~r1_tarski('#skF_3', k1_xboole_0)), inference(resolution, [status(thm)], [c_16, c_267])).
% 5.78/2.15  tff(c_2467, plain, (~r1_tarski('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2436, c_271])).
% 5.78/2.15  tff(c_2646, plain, (~r1_tarski('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2644, c_2467])).
% 5.78/2.15  tff(c_2670, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2472, c_2646])).
% 5.78/2.15  tff(c_2671, plain, ('#skF_5'='#skF_4'), inference(splitRight, [status(thm)], [c_2643])).
% 5.78/2.15  tff(c_2682, plain, (k2_relat_1('#skF_4')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_2671, c_237])).
% 5.78/2.15  tff(c_2699, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2457, c_2682])).
% 5.78/2.15  tff(c_2700, plain, (![D_89]: (~r2_hidden(D_89, '#skF_4'))), inference(splitRight, [status(thm)], [c_266])).
% 5.78/2.15  tff(c_2822, plain, (![B_370]: (r2_hidden('#skF_1'('#skF_4', B_370), B_370) | B_370='#skF_4')), inference(resolution, [status(thm)], [c_2794, c_2700])).
% 5.78/2.15  tff(c_3033, plain, (![B_388, A_389]: (r2_hidden('#skF_1'('#skF_4', B_388), A_389) | ~m1_subset_1(B_388, k1_zfmisc_1(A_389)) | B_388='#skF_4')), inference(resolution, [status(thm)], [c_2822, c_12])).
% 5.78/2.15  tff(c_3050, plain, (![B_390]: (~m1_subset_1(B_390, k1_zfmisc_1('#skF_4')) | B_390='#skF_4')), inference(resolution, [status(thm)], [c_3033, c_2700])).
% 5.78/2.15  tff(c_3110, plain, (![A_392]: (A_392='#skF_4' | ~r1_tarski(A_392, '#skF_4'))), inference(resolution, [status(thm)], [c_16, c_3050])).
% 5.78/2.15  tff(c_3192, plain, (![B_397]: (k2_relat_1(B_397)='#skF_4' | ~v5_relat_1(B_397, '#skF_4') | ~v1_relat_1(B_397))), inference(resolution, [status(thm)], [c_20, c_3110])).
% 5.78/2.15  tff(c_3219, plain, (k2_relat_1('#skF_5')='#skF_4' | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_132, c_3192])).
% 5.78/2.15  tff(c_3240, plain, (k2_relat_1('#skF_5')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_95, c_3219])).
% 5.78/2.15  tff(c_3242, plain, $false, inference(negUnitSimplification, [status(thm)], [c_237, c_3240])).
% 5.78/2.15  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.78/2.15  
% 5.78/2.15  Inference rules
% 5.78/2.15  ----------------------
% 5.78/2.15  #Ref     : 0
% 5.78/2.15  #Sup     : 547
% 5.78/2.15  #Fact    : 0
% 5.78/2.15  #Define  : 0
% 5.78/2.15  #Split   : 13
% 5.78/2.15  #Chain   : 0
% 5.78/2.15  #Close   : 0
% 5.78/2.15  
% 5.78/2.15  Ordering : KBO
% 5.78/2.15  
% 5.78/2.15  Simplification rules
% 5.78/2.15  ----------------------
% 5.78/2.15  #Subsume      : 106
% 5.78/2.15  #Demod        : 834
% 5.78/2.15  #Tautology    : 198
% 5.78/2.15  #SimpNegUnit  : 14
% 5.78/2.15  #BackRed      : 244
% 5.78/2.15  
% 5.78/2.15  #Partial instantiations: 0
% 5.78/2.15  #Strategies tried      : 1
% 5.78/2.15  
% 5.78/2.15  Timing (in seconds)
% 5.78/2.15  ----------------------
% 5.78/2.15  Preprocessing        : 0.36
% 5.78/2.15  Parsing              : 0.18
% 5.78/2.15  CNF conversion       : 0.03
% 5.78/2.15  Main loop            : 0.96
% 5.78/2.15  Inferencing          : 0.32
% 5.78/2.15  Reduction            : 0.32
% 5.78/2.15  Demodulation         : 0.20
% 5.78/2.15  BG Simplification    : 0.04
% 5.78/2.15  Subsumption          : 0.20
% 5.78/2.15  Abstraction          : 0.04
% 5.78/2.15  MUC search           : 0.00
% 5.78/2.15  Cooper               : 0.00
% 5.78/2.15  Total                : 1.36
% 5.78/2.15  Index Insertion      : 0.00
% 5.78/2.15  Index Deletion       : 0.00
% 5.78/2.15  Index Matching       : 0.00
% 5.78/2.15  BG Taut test         : 0.00
%------------------------------------------------------------------------------
