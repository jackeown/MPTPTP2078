%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:11:06 EST 2020

% Result     : Theorem 3.25s
% Output     : CNFRefutation 3.25s
% Verified   : 
% Statistics : Number of formulae       :   97 ( 142 expanded)
%              Number of leaves         :   38 (  66 expanded)
%              Depth                    :   11
%              Number of atoms          :  151 ( 315 expanded)
%              Number of equality atoms :   34 (  64 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_3 > #skF_6 > #skF_5 > #skF_9 > #skF_8 > #skF_2 > #skF_4

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

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

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

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_117,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( r2_hidden(C,A)
         => ( B = k1_xboole_0
            | r2_hidden(k1_funct_1(D,C),B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_funct_2)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_82,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_104,axiom,(
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
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_57,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_74,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( B = k2_relat_1(A)
        <=> ! [C] :
              ( r2_hidden(C,B)
            <=> ? [D] :
                  ( r2_hidden(D,k1_relat_1(A))
                  & C = k1_funct_1(A,D) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_funct_1)).

tff(f_86,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_78,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k2_relset_1(A,B,C),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_relset_1)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

tff(f_37,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(f_50,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

tff(c_56,plain,(
    r2_hidden('#skF_8','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_64,plain,(
    ! [B_72,A_73] :
      ( ~ r2_hidden(B_72,A_73)
      | ~ v1_xboole_0(A_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_68,plain,(
    ~ v1_xboole_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_56,c_64])).

tff(c_54,plain,(
    k1_xboole_0 != '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_60,plain,(
    v1_funct_2('#skF_9','#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_58,plain,(
    m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_7'))) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_778,plain,(
    ! [A_222,B_223,C_224] :
      ( k1_relset_1(A_222,B_223,C_224) = k1_relat_1(C_224)
      | ~ m1_subset_1(C_224,k1_zfmisc_1(k2_zfmisc_1(A_222,B_223))) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_782,plain,(
    k1_relset_1('#skF_6','#skF_7','#skF_9') = k1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_58,c_778])).

tff(c_1004,plain,(
    ! [B_265,A_266,C_267] :
      ( k1_xboole_0 = B_265
      | k1_relset_1(A_266,B_265,C_267) = A_266
      | ~ v1_funct_2(C_267,A_266,B_265)
      | ~ m1_subset_1(C_267,k1_zfmisc_1(k2_zfmisc_1(A_266,B_265))) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_1011,plain,
    ( k1_xboole_0 = '#skF_7'
    | k1_relset_1('#skF_6','#skF_7','#skF_9') = '#skF_6'
    | ~ v1_funct_2('#skF_9','#skF_6','#skF_7') ),
    inference(resolution,[status(thm)],[c_58,c_1004])).

tff(c_1015,plain,
    ( k1_xboole_0 = '#skF_7'
    | k1_relat_1('#skF_9') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_782,c_1011])).

tff(c_1016,plain,(
    k1_relat_1('#skF_9') = '#skF_6' ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_1015])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_14,plain,(
    ! [A_16,B_17] : v1_relat_1(k2_zfmisc_1(A_16,B_17)) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_760,plain,(
    ! [B_212,A_213] :
      ( v1_relat_1(B_212)
      | ~ m1_subset_1(B_212,k1_zfmisc_1(A_213))
      | ~ v1_relat_1(A_213) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_763,plain,
    ( v1_relat_1('#skF_9')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_6','#skF_7')) ),
    inference(resolution,[status(thm)],[c_58,c_760])).

tff(c_766,plain,(
    v1_relat_1('#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_763])).

tff(c_62,plain,(
    v1_funct_1('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_845,plain,(
    ! [A_232,D_233] :
      ( r2_hidden(k1_funct_1(A_232,D_233),k2_relat_1(A_232))
      | ~ r2_hidden(D_233,k1_relat_1(A_232))
      | ~ v1_funct_1(A_232)
      | ~ v1_relat_1(A_232) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_111,plain,(
    ! [A_90,B_91,C_92] :
      ( k1_relset_1(A_90,B_91,C_92) = k1_relat_1(C_92)
      | ~ m1_subset_1(C_92,k1_zfmisc_1(k2_zfmisc_1(A_90,B_91))) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_115,plain,(
    k1_relset_1('#skF_6','#skF_7','#skF_9') = k1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_58,c_111])).

tff(c_696,plain,(
    ! [B_205,A_206,C_207] :
      ( k1_xboole_0 = B_205
      | k1_relset_1(A_206,B_205,C_207) = A_206
      | ~ v1_funct_2(C_207,A_206,B_205)
      | ~ m1_subset_1(C_207,k1_zfmisc_1(k2_zfmisc_1(A_206,B_205))) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_703,plain,
    ( k1_xboole_0 = '#skF_7'
    | k1_relset_1('#skF_6','#skF_7','#skF_9') = '#skF_6'
    | ~ v1_funct_2('#skF_9','#skF_6','#skF_7') ),
    inference(resolution,[status(thm)],[c_58,c_696])).

tff(c_707,plain,
    ( k1_xboole_0 = '#skF_7'
    | k1_relat_1('#skF_9') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_115,c_703])).

tff(c_708,plain,(
    k1_relat_1('#skF_9') = '#skF_6' ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_707])).

tff(c_84,plain,(
    ! [B_77,A_78] :
      ( v1_relat_1(B_77)
      | ~ m1_subset_1(B_77,k1_zfmisc_1(A_78))
      | ~ v1_relat_1(A_78) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_87,plain,
    ( v1_relat_1('#skF_9')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_6','#skF_7')) ),
    inference(resolution,[status(thm)],[c_58,c_84])).

tff(c_90,plain,(
    v1_relat_1('#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_87])).

tff(c_417,plain,(
    ! [A_148,D_149] :
      ( r2_hidden(k1_funct_1(A_148,D_149),k2_relat_1(A_148))
      | ~ r2_hidden(D_149,k1_relat_1(A_148))
      | ~ v1_funct_1(A_148)
      | ~ v1_relat_1(A_148) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_101,plain,(
    ! [A_86,B_87,C_88] :
      ( k2_relset_1(A_86,B_87,C_88) = k2_relat_1(C_88)
      | ~ m1_subset_1(C_88,k1_zfmisc_1(k2_zfmisc_1(A_86,B_87))) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_105,plain,(
    k2_relset_1('#skF_6','#skF_7','#skF_9') = k2_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_58,c_101])).

tff(c_120,plain,(
    ! [A_93,B_94,C_95] :
      ( m1_subset_1(k2_relset_1(A_93,B_94,C_95),k1_zfmisc_1(B_94))
      | ~ m1_subset_1(C_95,k1_zfmisc_1(k2_zfmisc_1(A_93,B_94))) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_138,plain,
    ( m1_subset_1(k2_relat_1('#skF_9'),k1_zfmisc_1('#skF_7'))
    | ~ m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_7'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_105,c_120])).

tff(c_145,plain,(
    m1_subset_1(k2_relat_1('#skF_9'),k1_zfmisc_1('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_138])).

tff(c_8,plain,(
    ! [A_7,C_9,B_8] :
      ( m1_subset_1(A_7,C_9)
      | ~ m1_subset_1(B_8,k1_zfmisc_1(C_9))
      | ~ r2_hidden(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_153,plain,(
    ! [A_7] :
      ( m1_subset_1(A_7,'#skF_7')
      | ~ r2_hidden(A_7,k2_relat_1('#skF_9')) ) ),
    inference(resolution,[status(thm)],[c_145,c_8])).

tff(c_421,plain,(
    ! [D_149] :
      ( m1_subset_1(k1_funct_1('#skF_9',D_149),'#skF_7')
      | ~ r2_hidden(D_149,k1_relat_1('#skF_9'))
      | ~ v1_funct_1('#skF_9')
      | ~ v1_relat_1('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_417,c_153])).

tff(c_427,plain,(
    ! [D_149] :
      ( m1_subset_1(k1_funct_1('#skF_9',D_149),'#skF_7')
      | ~ r2_hidden(D_149,k1_relat_1('#skF_9')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_62,c_421])).

tff(c_746,plain,(
    ! [D_211] :
      ( m1_subset_1(k1_funct_1('#skF_9',D_211),'#skF_7')
      | ~ r2_hidden(D_211,'#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_708,c_427])).

tff(c_74,plain,(
    ! [A_75,B_76] :
      ( r2_hidden(A_75,B_76)
      | v1_xboole_0(B_76)
      | ~ m1_subset_1(A_75,B_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_52,plain,(
    ~ r2_hidden(k1_funct_1('#skF_9','#skF_8'),'#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_82,plain,
    ( v1_xboole_0('#skF_7')
    | ~ m1_subset_1(k1_funct_1('#skF_9','#skF_8'),'#skF_7') ),
    inference(resolution,[status(thm)],[c_74,c_52])).

tff(c_83,plain,(
    ~ m1_subset_1(k1_funct_1('#skF_9','#skF_8'),'#skF_7') ),
    inference(splitLeft,[status(thm)],[c_82])).

tff(c_749,plain,(
    ~ r2_hidden('#skF_8','#skF_6') ),
    inference(resolution,[status(thm)],[c_746,c_83])).

tff(c_757,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_749])).

tff(c_758,plain,(
    v1_xboole_0('#skF_7') ),
    inference(splitRight,[status(thm)],[c_82])).

tff(c_787,plain,(
    ! [A_225,B_226,C_227] :
      ( k2_relset_1(A_225,B_226,C_227) = k2_relat_1(C_227)
      | ~ m1_subset_1(C_227,k1_zfmisc_1(k2_zfmisc_1(A_225,B_226))) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_791,plain,(
    k2_relset_1('#skF_6','#skF_7','#skF_9') = k2_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_58,c_787])).

tff(c_796,plain,(
    ! [A_228,B_229,C_230] :
      ( m1_subset_1(k2_relset_1(A_228,B_229,C_230),k1_zfmisc_1(B_229))
      | ~ m1_subset_1(C_230,k1_zfmisc_1(k2_zfmisc_1(A_228,B_229))) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_814,plain,
    ( m1_subset_1(k2_relat_1('#skF_9'),k1_zfmisc_1('#skF_7'))
    | ~ m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_7'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_791,c_796])).

tff(c_821,plain,(
    m1_subset_1(k2_relat_1('#skF_9'),k1_zfmisc_1('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_814])).

tff(c_10,plain,(
    ! [C_12,B_11,A_10] :
      ( ~ v1_xboole_0(C_12)
      | ~ m1_subset_1(B_11,k1_zfmisc_1(C_12))
      | ~ r2_hidden(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_825,plain,(
    ! [A_10] :
      ( ~ v1_xboole_0('#skF_7')
      | ~ r2_hidden(A_10,k2_relat_1('#skF_9')) ) ),
    inference(resolution,[status(thm)],[c_821,c_10])).

tff(c_832,plain,(
    ! [A_10] : ~ r2_hidden(A_10,k2_relat_1('#skF_9')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_758,c_825])).

tff(c_849,plain,(
    ! [D_233] :
      ( ~ r2_hidden(D_233,k1_relat_1('#skF_9'))
      | ~ v1_funct_1('#skF_9')
      | ~ v1_relat_1('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_845,c_832])).

tff(c_857,plain,(
    ! [D_234] : ~ r2_hidden(D_234,k1_relat_1('#skF_9')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_766,c_62,c_849])).

tff(c_867,plain,(
    v1_xboole_0(k1_relat_1('#skF_9')) ),
    inference(resolution,[status(thm)],[c_4,c_857])).

tff(c_1017,plain,(
    v1_xboole_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1016,c_867])).

tff(c_1021,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_1017])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:40:50 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.25/1.54  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.25/1.55  
% 3.25/1.55  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.25/1.55  %$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_3 > #skF_6 > #skF_5 > #skF_9 > #skF_8 > #skF_2 > #skF_4
% 3.25/1.55  
% 3.25/1.55  %Foreground sorts:
% 3.25/1.55  
% 3.25/1.55  
% 3.25/1.55  %Background operators:
% 3.25/1.55  
% 3.25/1.55  
% 3.25/1.55  %Foreground operators:
% 3.25/1.55  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 3.25/1.55  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.25/1.55  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.25/1.55  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.25/1.55  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.25/1.55  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.25/1.55  tff('#skF_7', type, '#skF_7': $i).
% 3.25/1.55  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 3.25/1.55  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.25/1.55  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.25/1.55  tff('#skF_6', type, '#skF_6': $i).
% 3.25/1.55  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 3.25/1.55  tff('#skF_9', type, '#skF_9': $i).
% 3.25/1.55  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.25/1.55  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.25/1.55  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.25/1.55  tff('#skF_8', type, '#skF_8': $i).
% 3.25/1.55  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.25/1.55  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.25/1.55  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.25/1.55  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.25/1.55  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.25/1.55  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.25/1.55  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.25/1.55  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 3.25/1.55  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.25/1.55  
% 3.25/1.57  tff(f_117, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_hidden(C, A) => ((B = k1_xboole_0) | r2_hidden(k1_funct_1(D, C), B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_funct_2)).
% 3.25/1.57  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 3.25/1.57  tff(f_82, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.25/1.57  tff(f_104, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 3.25/1.57  tff(f_59, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 3.25/1.57  tff(f_57, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 3.25/1.57  tff(f_74, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((B = k2_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: (r2_hidden(D, k1_relat_1(A)) & (C = k1_funct_1(A, D)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_funct_1)).
% 3.25/1.57  tff(f_86, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 3.25/1.57  tff(f_78, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k2_relset_1(A, B, C), k1_zfmisc_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_relset_1)).
% 3.25/1.57  tff(f_43, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset)).
% 3.25/1.57  tff(f_37, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 3.25/1.57  tff(f_50, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_subset)).
% 3.25/1.57  tff(c_56, plain, (r2_hidden('#skF_8', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_117])).
% 3.25/1.57  tff(c_64, plain, (![B_72, A_73]: (~r2_hidden(B_72, A_73) | ~v1_xboole_0(A_73))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.25/1.57  tff(c_68, plain, (~v1_xboole_0('#skF_6')), inference(resolution, [status(thm)], [c_56, c_64])).
% 3.25/1.57  tff(c_54, plain, (k1_xboole_0!='#skF_7'), inference(cnfTransformation, [status(thm)], [f_117])).
% 3.25/1.57  tff(c_60, plain, (v1_funct_2('#skF_9', '#skF_6', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_117])).
% 3.25/1.57  tff(c_58, plain, (m1_subset_1('#skF_9', k1_zfmisc_1(k2_zfmisc_1('#skF_6', '#skF_7')))), inference(cnfTransformation, [status(thm)], [f_117])).
% 3.25/1.57  tff(c_778, plain, (![A_222, B_223, C_224]: (k1_relset_1(A_222, B_223, C_224)=k1_relat_1(C_224) | ~m1_subset_1(C_224, k1_zfmisc_1(k2_zfmisc_1(A_222, B_223))))), inference(cnfTransformation, [status(thm)], [f_82])).
% 3.25/1.57  tff(c_782, plain, (k1_relset_1('#skF_6', '#skF_7', '#skF_9')=k1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_58, c_778])).
% 3.25/1.57  tff(c_1004, plain, (![B_265, A_266, C_267]: (k1_xboole_0=B_265 | k1_relset_1(A_266, B_265, C_267)=A_266 | ~v1_funct_2(C_267, A_266, B_265) | ~m1_subset_1(C_267, k1_zfmisc_1(k2_zfmisc_1(A_266, B_265))))), inference(cnfTransformation, [status(thm)], [f_104])).
% 3.25/1.57  tff(c_1011, plain, (k1_xboole_0='#skF_7' | k1_relset_1('#skF_6', '#skF_7', '#skF_9')='#skF_6' | ~v1_funct_2('#skF_9', '#skF_6', '#skF_7')), inference(resolution, [status(thm)], [c_58, c_1004])).
% 3.25/1.57  tff(c_1015, plain, (k1_xboole_0='#skF_7' | k1_relat_1('#skF_9')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_60, c_782, c_1011])).
% 3.25/1.57  tff(c_1016, plain, (k1_relat_1('#skF_9')='#skF_6'), inference(negUnitSimplification, [status(thm)], [c_54, c_1015])).
% 3.25/1.57  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.25/1.57  tff(c_14, plain, (![A_16, B_17]: (v1_relat_1(k2_zfmisc_1(A_16, B_17)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.25/1.57  tff(c_760, plain, (![B_212, A_213]: (v1_relat_1(B_212) | ~m1_subset_1(B_212, k1_zfmisc_1(A_213)) | ~v1_relat_1(A_213))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.25/1.57  tff(c_763, plain, (v1_relat_1('#skF_9') | ~v1_relat_1(k2_zfmisc_1('#skF_6', '#skF_7'))), inference(resolution, [status(thm)], [c_58, c_760])).
% 3.25/1.57  tff(c_766, plain, (v1_relat_1('#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_14, c_763])).
% 3.25/1.57  tff(c_62, plain, (v1_funct_1('#skF_9')), inference(cnfTransformation, [status(thm)], [f_117])).
% 3.25/1.57  tff(c_845, plain, (![A_232, D_233]: (r2_hidden(k1_funct_1(A_232, D_233), k2_relat_1(A_232)) | ~r2_hidden(D_233, k1_relat_1(A_232)) | ~v1_funct_1(A_232) | ~v1_relat_1(A_232))), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.25/1.57  tff(c_111, plain, (![A_90, B_91, C_92]: (k1_relset_1(A_90, B_91, C_92)=k1_relat_1(C_92) | ~m1_subset_1(C_92, k1_zfmisc_1(k2_zfmisc_1(A_90, B_91))))), inference(cnfTransformation, [status(thm)], [f_82])).
% 3.25/1.57  tff(c_115, plain, (k1_relset_1('#skF_6', '#skF_7', '#skF_9')=k1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_58, c_111])).
% 3.25/1.57  tff(c_696, plain, (![B_205, A_206, C_207]: (k1_xboole_0=B_205 | k1_relset_1(A_206, B_205, C_207)=A_206 | ~v1_funct_2(C_207, A_206, B_205) | ~m1_subset_1(C_207, k1_zfmisc_1(k2_zfmisc_1(A_206, B_205))))), inference(cnfTransformation, [status(thm)], [f_104])).
% 3.25/1.57  tff(c_703, plain, (k1_xboole_0='#skF_7' | k1_relset_1('#skF_6', '#skF_7', '#skF_9')='#skF_6' | ~v1_funct_2('#skF_9', '#skF_6', '#skF_7')), inference(resolution, [status(thm)], [c_58, c_696])).
% 3.25/1.57  tff(c_707, plain, (k1_xboole_0='#skF_7' | k1_relat_1('#skF_9')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_60, c_115, c_703])).
% 3.25/1.57  tff(c_708, plain, (k1_relat_1('#skF_9')='#skF_6'), inference(negUnitSimplification, [status(thm)], [c_54, c_707])).
% 3.25/1.57  tff(c_84, plain, (![B_77, A_78]: (v1_relat_1(B_77) | ~m1_subset_1(B_77, k1_zfmisc_1(A_78)) | ~v1_relat_1(A_78))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.25/1.57  tff(c_87, plain, (v1_relat_1('#skF_9') | ~v1_relat_1(k2_zfmisc_1('#skF_6', '#skF_7'))), inference(resolution, [status(thm)], [c_58, c_84])).
% 3.25/1.57  tff(c_90, plain, (v1_relat_1('#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_14, c_87])).
% 3.25/1.57  tff(c_417, plain, (![A_148, D_149]: (r2_hidden(k1_funct_1(A_148, D_149), k2_relat_1(A_148)) | ~r2_hidden(D_149, k1_relat_1(A_148)) | ~v1_funct_1(A_148) | ~v1_relat_1(A_148))), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.25/1.57  tff(c_101, plain, (![A_86, B_87, C_88]: (k2_relset_1(A_86, B_87, C_88)=k2_relat_1(C_88) | ~m1_subset_1(C_88, k1_zfmisc_1(k2_zfmisc_1(A_86, B_87))))), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.25/1.57  tff(c_105, plain, (k2_relset_1('#skF_6', '#skF_7', '#skF_9')=k2_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_58, c_101])).
% 3.25/1.57  tff(c_120, plain, (![A_93, B_94, C_95]: (m1_subset_1(k2_relset_1(A_93, B_94, C_95), k1_zfmisc_1(B_94)) | ~m1_subset_1(C_95, k1_zfmisc_1(k2_zfmisc_1(A_93, B_94))))), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.25/1.57  tff(c_138, plain, (m1_subset_1(k2_relat_1('#skF_9'), k1_zfmisc_1('#skF_7')) | ~m1_subset_1('#skF_9', k1_zfmisc_1(k2_zfmisc_1('#skF_6', '#skF_7')))), inference(superposition, [status(thm), theory('equality')], [c_105, c_120])).
% 3.25/1.57  tff(c_145, plain, (m1_subset_1(k2_relat_1('#skF_9'), k1_zfmisc_1('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_138])).
% 3.25/1.57  tff(c_8, plain, (![A_7, C_9, B_8]: (m1_subset_1(A_7, C_9) | ~m1_subset_1(B_8, k1_zfmisc_1(C_9)) | ~r2_hidden(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.25/1.57  tff(c_153, plain, (![A_7]: (m1_subset_1(A_7, '#skF_7') | ~r2_hidden(A_7, k2_relat_1('#skF_9')))), inference(resolution, [status(thm)], [c_145, c_8])).
% 3.25/1.57  tff(c_421, plain, (![D_149]: (m1_subset_1(k1_funct_1('#skF_9', D_149), '#skF_7') | ~r2_hidden(D_149, k1_relat_1('#skF_9')) | ~v1_funct_1('#skF_9') | ~v1_relat_1('#skF_9'))), inference(resolution, [status(thm)], [c_417, c_153])).
% 3.25/1.57  tff(c_427, plain, (![D_149]: (m1_subset_1(k1_funct_1('#skF_9', D_149), '#skF_7') | ~r2_hidden(D_149, k1_relat_1('#skF_9')))), inference(demodulation, [status(thm), theory('equality')], [c_90, c_62, c_421])).
% 3.25/1.57  tff(c_746, plain, (![D_211]: (m1_subset_1(k1_funct_1('#skF_9', D_211), '#skF_7') | ~r2_hidden(D_211, '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_708, c_427])).
% 3.25/1.57  tff(c_74, plain, (![A_75, B_76]: (r2_hidden(A_75, B_76) | v1_xboole_0(B_76) | ~m1_subset_1(A_75, B_76))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.25/1.57  tff(c_52, plain, (~r2_hidden(k1_funct_1('#skF_9', '#skF_8'), '#skF_7')), inference(cnfTransformation, [status(thm)], [f_117])).
% 3.25/1.57  tff(c_82, plain, (v1_xboole_0('#skF_7') | ~m1_subset_1(k1_funct_1('#skF_9', '#skF_8'), '#skF_7')), inference(resolution, [status(thm)], [c_74, c_52])).
% 3.25/1.57  tff(c_83, plain, (~m1_subset_1(k1_funct_1('#skF_9', '#skF_8'), '#skF_7')), inference(splitLeft, [status(thm)], [c_82])).
% 3.25/1.57  tff(c_749, plain, (~r2_hidden('#skF_8', '#skF_6')), inference(resolution, [status(thm)], [c_746, c_83])).
% 3.25/1.57  tff(c_757, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_56, c_749])).
% 3.25/1.57  tff(c_758, plain, (v1_xboole_0('#skF_7')), inference(splitRight, [status(thm)], [c_82])).
% 3.25/1.57  tff(c_787, plain, (![A_225, B_226, C_227]: (k2_relset_1(A_225, B_226, C_227)=k2_relat_1(C_227) | ~m1_subset_1(C_227, k1_zfmisc_1(k2_zfmisc_1(A_225, B_226))))), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.25/1.57  tff(c_791, plain, (k2_relset_1('#skF_6', '#skF_7', '#skF_9')=k2_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_58, c_787])).
% 3.25/1.57  tff(c_796, plain, (![A_228, B_229, C_230]: (m1_subset_1(k2_relset_1(A_228, B_229, C_230), k1_zfmisc_1(B_229)) | ~m1_subset_1(C_230, k1_zfmisc_1(k2_zfmisc_1(A_228, B_229))))), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.25/1.57  tff(c_814, plain, (m1_subset_1(k2_relat_1('#skF_9'), k1_zfmisc_1('#skF_7')) | ~m1_subset_1('#skF_9', k1_zfmisc_1(k2_zfmisc_1('#skF_6', '#skF_7')))), inference(superposition, [status(thm), theory('equality')], [c_791, c_796])).
% 3.25/1.57  tff(c_821, plain, (m1_subset_1(k2_relat_1('#skF_9'), k1_zfmisc_1('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_814])).
% 3.25/1.57  tff(c_10, plain, (![C_12, B_11, A_10]: (~v1_xboole_0(C_12) | ~m1_subset_1(B_11, k1_zfmisc_1(C_12)) | ~r2_hidden(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.25/1.57  tff(c_825, plain, (![A_10]: (~v1_xboole_0('#skF_7') | ~r2_hidden(A_10, k2_relat_1('#skF_9')))), inference(resolution, [status(thm)], [c_821, c_10])).
% 3.25/1.57  tff(c_832, plain, (![A_10]: (~r2_hidden(A_10, k2_relat_1('#skF_9')))), inference(demodulation, [status(thm), theory('equality')], [c_758, c_825])).
% 3.25/1.57  tff(c_849, plain, (![D_233]: (~r2_hidden(D_233, k1_relat_1('#skF_9')) | ~v1_funct_1('#skF_9') | ~v1_relat_1('#skF_9'))), inference(resolution, [status(thm)], [c_845, c_832])).
% 3.25/1.57  tff(c_857, plain, (![D_234]: (~r2_hidden(D_234, k1_relat_1('#skF_9')))), inference(demodulation, [status(thm), theory('equality')], [c_766, c_62, c_849])).
% 3.25/1.57  tff(c_867, plain, (v1_xboole_0(k1_relat_1('#skF_9'))), inference(resolution, [status(thm)], [c_4, c_857])).
% 3.25/1.57  tff(c_1017, plain, (v1_xboole_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_1016, c_867])).
% 3.25/1.57  tff(c_1021, plain, $false, inference(negUnitSimplification, [status(thm)], [c_68, c_1017])).
% 3.25/1.57  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.25/1.57  
% 3.25/1.57  Inference rules
% 3.25/1.57  ----------------------
% 3.25/1.57  #Ref     : 0
% 3.25/1.57  #Sup     : 182
% 3.25/1.57  #Fact    : 0
% 3.25/1.57  #Define  : 0
% 3.25/1.57  #Split   : 10
% 3.25/1.57  #Chain   : 0
% 3.25/1.57  #Close   : 0
% 3.25/1.57  
% 3.25/1.57  Ordering : KBO
% 3.25/1.57  
% 3.25/1.57  Simplification rules
% 3.25/1.57  ----------------------
% 3.25/1.57  #Subsume      : 38
% 3.25/1.57  #Demod        : 87
% 3.25/1.57  #Tautology    : 36
% 3.25/1.57  #SimpNegUnit  : 12
% 3.25/1.57  #BackRed      : 12
% 3.25/1.57  
% 3.25/1.57  #Partial instantiations: 0
% 3.25/1.57  #Strategies tried      : 1
% 3.25/1.57  
% 3.25/1.57  Timing (in seconds)
% 3.25/1.57  ----------------------
% 3.25/1.57  Preprocessing        : 0.34
% 3.25/1.57  Parsing              : 0.18
% 3.25/1.57  CNF conversion       : 0.03
% 3.25/1.57  Main loop            : 0.40
% 3.25/1.57  Inferencing          : 0.16
% 3.25/1.57  Reduction            : 0.11
% 3.25/1.57  Demodulation         : 0.07
% 3.25/1.57  BG Simplification    : 0.02
% 3.25/1.57  Subsumption          : 0.07
% 3.25/1.57  Abstraction          : 0.02
% 3.25/1.57  MUC search           : 0.00
% 3.25/1.57  Cooper               : 0.00
% 3.25/1.57  Total                : 0.77
% 3.25/1.57  Index Insertion      : 0.00
% 3.25/1.57  Index Deletion       : 0.00
% 3.25/1.57  Index Matching       : 0.00
% 3.25/1.57  BG Taut test         : 0.00
%------------------------------------------------------------------------------
