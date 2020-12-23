%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:16:37 EST 2020

% Result     : Theorem 5.10s
% Output     : CNFRefutation 5.23s
% Verified   : 
% Statistics : Number of formulae       :  147 ( 908 expanded)
%              Number of leaves         :   36 ( 326 expanded)
%              Depth                    :   12
%              Number of atoms          :  266 (2840 expanded)
%              Number of equality atoms :   70 ( 933 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k1_relset_1 > k9_relat_1 > k4_tarski > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(k7_relset_1,type,(
    k7_relset_1: ( $i * $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_54,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_120,negated_conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t116_funct_2)).

tff(f_52,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_83,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_65,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k9_relat_1(C,B))
      <=> ? [D] :
            ( r2_hidden(D,k1_relat_1(C))
            & r2_hidden(k4_tarski(D,A),C)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t143_relat_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_79,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_101,axiom,(
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

tff(f_32,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_75,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( r2_hidden(k4_tarski(A,B),C)
      <=> ( r2_hidden(A,k1_relat_1(C))
          & B = k1_funct_1(C,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_funct_1)).

tff(c_18,plain,(
    ! [A_10,B_11] : v1_relat_1(k2_zfmisc_1(A_10,B_11)) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_54,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_97,plain,(
    ! [B_48,A_49] :
      ( v1_relat_1(B_48)
      | ~ m1_subset_1(B_48,k1_zfmisc_1(A_49))
      | ~ v1_relat_1(A_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_108,plain,
    ( v1_relat_1('#skF_6')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_54,c_97])).

tff(c_113,plain,(
    v1_relat_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_108])).

tff(c_319,plain,(
    ! [A_101,B_102,C_103,D_104] :
      ( k7_relset_1(A_101,B_102,C_103,D_104) = k9_relat_1(C_103,D_104)
      | ~ m1_subset_1(C_103,k1_zfmisc_1(k2_zfmisc_1(A_101,B_102))) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_330,plain,(
    ! [D_104] : k7_relset_1('#skF_3','#skF_4','#skF_6',D_104) = k9_relat_1('#skF_6',D_104) ),
    inference(resolution,[status(thm)],[c_54,c_319])).

tff(c_52,plain,(
    r2_hidden('#skF_7',k7_relset_1('#skF_3','#skF_4','#skF_6','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_333,plain,(
    r2_hidden('#skF_7',k9_relat_1('#skF_6','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_330,c_52])).

tff(c_187,plain,(
    ! [A_61,B_62,C_63] :
      ( r2_hidden('#skF_2'(A_61,B_62,C_63),B_62)
      | ~ r2_hidden(A_61,k9_relat_1(C_63,B_62))
      | ~ v1_relat_1(C_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_50,plain,(
    ! [F_35] :
      ( k1_funct_1('#skF_6',F_35) != '#skF_7'
      | ~ r2_hidden(F_35,'#skF_5')
      | ~ m1_subset_1(F_35,'#skF_3') ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_198,plain,(
    ! [A_61,C_63] :
      ( k1_funct_1('#skF_6','#skF_2'(A_61,'#skF_5',C_63)) != '#skF_7'
      | ~ m1_subset_1('#skF_2'(A_61,'#skF_5',C_63),'#skF_3')
      | ~ r2_hidden(A_61,k9_relat_1(C_63,'#skF_5'))
      | ~ v1_relat_1(C_63) ) ),
    inference(resolution,[status(thm)],[c_187,c_50])).

tff(c_375,plain,
    ( k1_funct_1('#skF_6','#skF_2'('#skF_7','#skF_5','#skF_6')) != '#skF_7'
    | ~ m1_subset_1('#skF_2'('#skF_7','#skF_5','#skF_6'),'#skF_3')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_333,c_198])).

tff(c_390,plain,
    ( k1_funct_1('#skF_6','#skF_2'('#skF_7','#skF_5','#skF_6')) != '#skF_7'
    | ~ m1_subset_1('#skF_2'('#skF_7','#skF_5','#skF_6'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_113,c_375])).

tff(c_398,plain,(
    ~ m1_subset_1('#skF_2'('#skF_7','#skF_5','#skF_6'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_390])).

tff(c_12,plain,(
    ! [B_6,A_5] :
      ( m1_subset_1(B_6,A_5)
      | ~ v1_xboole_0(B_6)
      | ~ v1_xboole_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_127,plain,(
    ! [F_52] :
      ( k1_funct_1('#skF_6',F_52) != '#skF_7'
      | ~ r2_hidden(F_52,'#skF_5')
      | ~ m1_subset_1(F_52,'#skF_3') ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_137,plain,
    ( k1_funct_1('#skF_6','#skF_1'('#skF_5')) != '#skF_7'
    | ~ m1_subset_1('#skF_1'('#skF_5'),'#skF_3')
    | v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_4,c_127])).

tff(c_141,plain,(
    ~ m1_subset_1('#skF_1'('#skF_5'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_137])).

tff(c_145,plain,
    ( ~ v1_xboole_0('#skF_1'('#skF_5'))
    | ~ v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_12,c_141])).

tff(c_153,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_145])).

tff(c_56,plain,(
    v1_funct_2('#skF_6','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_168,plain,(
    ! [A_58,B_59,C_60] :
      ( k1_relset_1(A_58,B_59,C_60) = k1_relat_1(C_60)
      | ~ m1_subset_1(C_60,k1_zfmisc_1(k2_zfmisc_1(A_58,B_59))) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_182,plain,(
    k1_relset_1('#skF_3','#skF_4','#skF_6') = k1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_54,c_168])).

tff(c_880,plain,(
    ! [B_185,A_186,C_187] :
      ( k1_xboole_0 = B_185
      | k1_relset_1(A_186,B_185,C_187) = A_186
      | ~ v1_funct_2(C_187,A_186,B_185)
      | ~ m1_subset_1(C_187,k1_zfmisc_1(k2_zfmisc_1(A_186,B_185))) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_891,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relset_1('#skF_3','#skF_4','#skF_6') = '#skF_3'
    | ~ v1_funct_2('#skF_6','#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_54,c_880])).

tff(c_896,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relat_1('#skF_6') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_182,c_891])).

tff(c_897,plain,(
    k1_relat_1('#skF_6') = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_896])).

tff(c_26,plain,(
    ! [A_12,B_13,C_14] :
      ( r2_hidden('#skF_2'(A_12,B_13,C_14),k1_relat_1(C_14))
      | ~ r2_hidden(A_12,k9_relat_1(C_14,B_13))
      | ~ v1_relat_1(C_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_918,plain,(
    ! [A_12,B_13] :
      ( r2_hidden('#skF_2'(A_12,B_13,'#skF_6'),'#skF_3')
      | ~ r2_hidden(A_12,k9_relat_1('#skF_6',B_13))
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_897,c_26])).

tff(c_944,plain,(
    ! [A_190,B_191] :
      ( r2_hidden('#skF_2'(A_190,B_191,'#skF_6'),'#skF_3')
      | ~ r2_hidden(A_190,k9_relat_1('#skF_6',B_191)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_113,c_918])).

tff(c_8,plain,(
    ! [B_6,A_5] :
      ( m1_subset_1(B_6,A_5)
      | ~ r2_hidden(B_6,A_5)
      | v1_xboole_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_947,plain,(
    ! [A_190,B_191] :
      ( m1_subset_1('#skF_2'(A_190,B_191,'#skF_6'),'#skF_3')
      | v1_xboole_0('#skF_3')
      | ~ r2_hidden(A_190,k9_relat_1('#skF_6',B_191)) ) ),
    inference(resolution,[status(thm)],[c_944,c_8])).

tff(c_955,plain,(
    ! [A_192,B_193] :
      ( m1_subset_1('#skF_2'(A_192,B_193,'#skF_6'),'#skF_3')
      | ~ r2_hidden(A_192,k9_relat_1('#skF_6',B_193)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_153,c_947])).

tff(c_966,plain,(
    m1_subset_1('#skF_2'('#skF_7','#skF_5','#skF_6'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_333,c_955])).

tff(c_984,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_398,c_966])).

tff(c_985,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_896])).

tff(c_6,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_997,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_985,c_6])).

tff(c_40,plain,(
    ! [C_30,A_28] :
      ( k1_xboole_0 = C_30
      | ~ v1_funct_2(C_30,A_28,k1_xboole_0)
      | k1_xboole_0 = A_28
      | ~ m1_subset_1(C_30,k1_zfmisc_1(k2_zfmisc_1(A_28,k1_xboole_0))) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_1107,plain,(
    ! [C_207,A_208] :
      ( C_207 = '#skF_4'
      | ~ v1_funct_2(C_207,A_208,'#skF_4')
      | A_208 = '#skF_4'
      | ~ m1_subset_1(C_207,k1_zfmisc_1(k2_zfmisc_1(A_208,'#skF_4'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_985,c_985,c_985,c_985,c_40])).

tff(c_1118,plain,
    ( '#skF_6' = '#skF_4'
    | ~ v1_funct_2('#skF_6','#skF_3','#skF_4')
    | '#skF_3' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_54,c_1107])).

tff(c_1123,plain,
    ( '#skF_6' = '#skF_4'
    | '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_1118])).

tff(c_1124,plain,(
    '#skF_3' = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_1123])).

tff(c_1146,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1124,c_153])).

tff(c_1154,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_997,c_1146])).

tff(c_1155,plain,(
    '#skF_6' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_1123])).

tff(c_58,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_428,plain,(
    ! [A_116,C_117] :
      ( r2_hidden(k4_tarski(A_116,k1_funct_1(C_117,A_116)),C_117)
      | ~ r2_hidden(A_116,k1_relat_1(C_117))
      | ~ v1_funct_1(C_117)
      | ~ v1_relat_1(C_117) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_487,plain,(
    ! [C_120,A_121] :
      ( ~ v1_xboole_0(C_120)
      | ~ r2_hidden(A_121,k1_relat_1(C_120))
      | ~ v1_funct_1(C_120)
      | ~ v1_relat_1(C_120) ) ),
    inference(resolution,[status(thm)],[c_428,c_2])).

tff(c_512,plain,(
    ! [C_122] :
      ( ~ v1_xboole_0(C_122)
      | ~ v1_funct_1(C_122)
      | ~ v1_relat_1(C_122)
      | v1_xboole_0(k1_relat_1(C_122)) ) ),
    inference(resolution,[status(thm)],[c_4,c_487])).

tff(c_274,plain,(
    ! [A_89,B_90,C_91] :
      ( r2_hidden('#skF_2'(A_89,B_90,C_91),k1_relat_1(C_91))
      | ~ r2_hidden(A_89,k9_relat_1(C_91,B_90))
      | ~ v1_relat_1(C_91) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_283,plain,(
    ! [C_92,A_93,B_94] :
      ( ~ v1_xboole_0(k1_relat_1(C_92))
      | ~ r2_hidden(A_93,k9_relat_1(C_92,B_94))
      | ~ v1_relat_1(C_92) ) ),
    inference(resolution,[status(thm)],[c_274,c_2])).

tff(c_298,plain,(
    ! [C_92,B_94] :
      ( ~ v1_xboole_0(k1_relat_1(C_92))
      | ~ v1_relat_1(C_92)
      | v1_xboole_0(k9_relat_1(C_92,B_94)) ) ),
    inference(resolution,[status(thm)],[c_4,c_283])).

tff(c_79,plain,(
    ~ v1_xboole_0(k7_relset_1('#skF_3','#skF_4','#skF_6','#skF_5')) ),
    inference(resolution,[status(thm)],[c_52,c_2])).

tff(c_332,plain,(
    ~ v1_xboole_0(k9_relat_1('#skF_6','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_330,c_79])).

tff(c_345,plain,
    ( ~ v1_xboole_0(k1_relat_1('#skF_6'))
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_298,c_332])).

tff(c_351,plain,(
    ~ v1_xboole_0(k1_relat_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_113,c_345])).

tff(c_515,plain,
    ( ~ v1_xboole_0('#skF_6')
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_512,c_351])).

tff(c_520,plain,(
    ~ v1_xboole_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_113,c_58,c_515])).

tff(c_1162,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1155,c_520])).

tff(c_1181,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_997,c_1162])).

tff(c_1182,plain,(
    k1_funct_1('#skF_6','#skF_2'('#skF_7','#skF_5','#skF_6')) != '#skF_7' ),
    inference(splitRight,[status(thm)],[c_390])).

tff(c_1231,plain,(
    ! [A_221,B_222,C_223] :
      ( r2_hidden(k4_tarski('#skF_2'(A_221,B_222,C_223),A_221),C_223)
      | ~ r2_hidden(A_221,k9_relat_1(C_223,B_222))
      | ~ v1_relat_1(C_223) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_30,plain,(
    ! [C_20,A_18,B_19] :
      ( k1_funct_1(C_20,A_18) = B_19
      | ~ r2_hidden(k4_tarski(A_18,B_19),C_20)
      | ~ v1_funct_1(C_20)
      | ~ v1_relat_1(C_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_1970,plain,(
    ! [C_313,A_314,B_315] :
      ( k1_funct_1(C_313,'#skF_2'(A_314,B_315,C_313)) = A_314
      | ~ v1_funct_1(C_313)
      | ~ r2_hidden(A_314,k9_relat_1(C_313,B_315))
      | ~ v1_relat_1(C_313) ) ),
    inference(resolution,[status(thm)],[c_1231,c_30])).

tff(c_1980,plain,
    ( k1_funct_1('#skF_6','#skF_2'('#skF_7','#skF_5','#skF_6')) = '#skF_7'
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_333,c_1970])).

tff(c_1995,plain,(
    k1_funct_1('#skF_6','#skF_2'('#skF_7','#skF_5','#skF_6')) = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_113,c_58,c_1980])).

tff(c_1997,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1182,c_1995])).

tff(c_1999,plain,(
    v1_xboole_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_145])).

tff(c_2001,plain,(
    ! [A_317,B_318,C_319] :
      ( k1_relset_1(A_317,B_318,C_319) = k1_relat_1(C_319)
      | ~ m1_subset_1(C_319,k1_zfmisc_1(k2_zfmisc_1(A_317,B_318))) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_2015,plain,(
    k1_relset_1('#skF_3','#skF_4','#skF_6') = k1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_54,c_2001])).

tff(c_2624,plain,(
    ! [B_419,A_420,C_421] :
      ( k1_xboole_0 = B_419
      | k1_relset_1(A_420,B_419,C_421) = A_420
      | ~ v1_funct_2(C_421,A_420,B_419)
      | ~ m1_subset_1(C_421,k1_zfmisc_1(k2_zfmisc_1(A_420,B_419))) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_2635,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relset_1('#skF_3','#skF_4','#skF_6') = '#skF_3'
    | ~ v1_funct_2('#skF_6','#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_54,c_2624])).

tff(c_2640,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relat_1('#skF_6') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_2015,c_2635])).

tff(c_2641,plain,(
    k1_relat_1('#skF_6') = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_2640])).

tff(c_2124,plain,(
    ! [A_351,B_352,C_353,D_354] :
      ( k7_relset_1(A_351,B_352,C_353,D_354) = k9_relat_1(C_353,D_354)
      | ~ m1_subset_1(C_353,k1_zfmisc_1(k2_zfmisc_1(A_351,B_352))) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_2135,plain,(
    ! [D_354] : k7_relset_1('#skF_3','#skF_4','#skF_6',D_354) = k9_relat_1('#skF_6',D_354) ),
    inference(resolution,[status(thm)],[c_54,c_2124])).

tff(c_2138,plain,(
    r2_hidden('#skF_7',k9_relat_1('#skF_6','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2135,c_52])).

tff(c_2206,plain,(
    ! [A_360,B_361,C_362] :
      ( r2_hidden('#skF_2'(A_360,B_361,C_362),k1_relat_1(C_362))
      | ~ r2_hidden(A_360,k9_relat_1(C_362,B_361))
      | ~ v1_relat_1(C_362) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_2253,plain,(
    ! [C_365,A_366,B_367] :
      ( ~ v1_xboole_0(k1_relat_1(C_365))
      | ~ r2_hidden(A_366,k9_relat_1(C_365,B_367))
      | ~ v1_relat_1(C_365) ) ),
    inference(resolution,[status(thm)],[c_2206,c_2])).

tff(c_2260,plain,
    ( ~ v1_xboole_0(k1_relat_1('#skF_6'))
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_2138,c_2253])).

tff(c_2276,plain,(
    ~ v1_xboole_0(k1_relat_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_113,c_2260])).

tff(c_2642,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2641,c_2276])).

tff(c_2646,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1999,c_2642])).

tff(c_2647,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_2640])).

tff(c_2656,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2647,c_6])).

tff(c_2697,plain,(
    ! [C_432,A_433] :
      ( C_432 = '#skF_4'
      | ~ v1_funct_2(C_432,A_433,'#skF_4')
      | A_433 = '#skF_4'
      | ~ m1_subset_1(C_432,k1_zfmisc_1(k2_zfmisc_1(A_433,'#skF_4'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2647,c_2647,c_2647,c_2647,c_40])).

tff(c_2708,plain,
    ( '#skF_6' = '#skF_4'
    | ~ v1_funct_2('#skF_6','#skF_3','#skF_4')
    | '#skF_3' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_54,c_2697])).

tff(c_2713,plain,
    ( '#skF_6' = '#skF_4'
    | '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_2708])).

tff(c_2714,plain,(
    '#skF_3' = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_2713])).

tff(c_2648,plain,(
    k1_relat_1('#skF_6') != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_2640])).

tff(c_2723,plain,(
    k1_relat_1('#skF_6') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2714,c_2648])).

tff(c_2739,plain,(
    v1_funct_2('#skF_6','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2714,c_56])).

tff(c_2733,plain,(
    k1_relset_1('#skF_4','#skF_4','#skF_6') = k1_relat_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2714,c_2015])).

tff(c_2738,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2714,c_54])).

tff(c_46,plain,(
    ! [B_29,C_30] :
      ( k1_relset_1(k1_xboole_0,B_29,C_30) = k1_xboole_0
      | ~ v1_funct_2(C_30,k1_xboole_0,B_29)
      | ~ m1_subset_1(C_30,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_29))) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_2920,plain,(
    ! [B_455,C_456] :
      ( k1_relset_1('#skF_4',B_455,C_456) = '#skF_4'
      | ~ v1_funct_2(C_456,'#skF_4',B_455)
      | ~ m1_subset_1(C_456,k1_zfmisc_1(k2_zfmisc_1('#skF_4',B_455))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2647,c_2647,c_2647,c_2647,c_46])).

tff(c_2923,plain,
    ( k1_relset_1('#skF_4','#skF_4','#skF_6') = '#skF_4'
    | ~ v1_funct_2('#skF_6','#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_2738,c_2920])).

tff(c_2934,plain,(
    k1_relat_1('#skF_6') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2739,c_2733,c_2923])).

tff(c_2936,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2723,c_2934])).

tff(c_2937,plain,(
    '#skF_6' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_2713])).

tff(c_2215,plain,(
    ! [A_363,C_364] :
      ( r2_hidden(k4_tarski(A_363,k1_funct_1(C_364,A_363)),C_364)
      | ~ r2_hidden(A_363,k1_relat_1(C_364))
      | ~ v1_funct_1(C_364)
      | ~ v1_relat_1(C_364) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_2291,plain,(
    ! [C_370,A_371] :
      ( ~ v1_xboole_0(C_370)
      | ~ r2_hidden(A_371,k1_relat_1(C_370))
      | ~ v1_funct_1(C_370)
      | ~ v1_relat_1(C_370) ) ),
    inference(resolution,[status(thm)],[c_2215,c_2])).

tff(c_2316,plain,(
    ! [C_372] :
      ( ~ v1_xboole_0(C_372)
      | ~ v1_funct_1(C_372)
      | ~ v1_relat_1(C_372)
      | v1_xboole_0(k1_relat_1(C_372)) ) ),
    inference(resolution,[status(thm)],[c_4,c_2291])).

tff(c_2319,plain,
    ( ~ v1_xboole_0('#skF_6')
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_2316,c_2276])).

tff(c_2324,plain,(
    ~ v1_xboole_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_113,c_58,c_2319])).

tff(c_2952,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2937,c_2324])).

tff(c_2971,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2656,c_2952])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:41:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.10/1.97  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.23/1.99  
% 5.23/1.99  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.23/1.99  %$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k1_relset_1 > k9_relat_1 > k4_tarski > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_4
% 5.23/1.99  
% 5.23/1.99  %Foreground sorts:
% 5.23/1.99  
% 5.23/1.99  
% 5.23/1.99  %Background operators:
% 5.23/1.99  
% 5.23/1.99  
% 5.23/1.99  %Foreground operators:
% 5.23/1.99  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 5.23/1.99  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.23/1.99  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.23/1.99  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 5.23/1.99  tff('#skF_1', type, '#skF_1': $i > $i).
% 5.23/1.99  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.23/1.99  tff('#skF_7', type, '#skF_7': $i).
% 5.23/1.99  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 5.23/1.99  tff('#skF_5', type, '#skF_5': $i).
% 5.23/1.99  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 5.23/1.99  tff('#skF_6', type, '#skF_6': $i).
% 5.23/1.99  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 5.23/1.99  tff('#skF_3', type, '#skF_3': $i).
% 5.23/1.99  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 5.23/1.99  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 5.23/1.99  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.23/1.99  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 5.23/1.99  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.23/1.99  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.23/1.99  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 5.23/1.99  tff('#skF_4', type, '#skF_4': $i).
% 5.23/1.99  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.23/1.99  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 5.23/1.99  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 5.23/1.99  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.23/1.99  
% 5.23/2.01  tff(f_54, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 5.23/2.01  tff(f_120, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: ~(r2_hidden(E, k7_relset_1(A, B, D, C)) & (![F]: (m1_subset_1(F, A) => ~(r2_hidden(F, C) & (E = k1_funct_1(D, F))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t116_funct_2)).
% 5.23/2.01  tff(f_52, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 5.23/2.01  tff(f_83, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 5.23/2.01  tff(f_65, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k9_relat_1(C, B)) <=> (?[D]: ((r2_hidden(D, k1_relat_1(C)) & r2_hidden(k4_tarski(D, A), C)) & r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t143_relat_1)).
% 5.23/2.01  tff(f_45, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 5.23/2.01  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 5.23/2.01  tff(f_79, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 5.23/2.01  tff(f_101, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 5.23/2.01  tff(f_32, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 5.23/2.01  tff(f_75, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(k4_tarski(A, B), C) <=> (r2_hidden(A, k1_relat_1(C)) & (B = k1_funct_1(C, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_funct_1)).
% 5.23/2.01  tff(c_18, plain, (![A_10, B_11]: (v1_relat_1(k2_zfmisc_1(A_10, B_11)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 5.23/2.01  tff(c_54, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_120])).
% 5.23/2.01  tff(c_97, plain, (![B_48, A_49]: (v1_relat_1(B_48) | ~m1_subset_1(B_48, k1_zfmisc_1(A_49)) | ~v1_relat_1(A_49))), inference(cnfTransformation, [status(thm)], [f_52])).
% 5.23/2.01  tff(c_108, plain, (v1_relat_1('#skF_6') | ~v1_relat_1(k2_zfmisc_1('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_54, c_97])).
% 5.23/2.01  tff(c_113, plain, (v1_relat_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_18, c_108])).
% 5.23/2.01  tff(c_319, plain, (![A_101, B_102, C_103, D_104]: (k7_relset_1(A_101, B_102, C_103, D_104)=k9_relat_1(C_103, D_104) | ~m1_subset_1(C_103, k1_zfmisc_1(k2_zfmisc_1(A_101, B_102))))), inference(cnfTransformation, [status(thm)], [f_83])).
% 5.23/2.01  tff(c_330, plain, (![D_104]: (k7_relset_1('#skF_3', '#skF_4', '#skF_6', D_104)=k9_relat_1('#skF_6', D_104))), inference(resolution, [status(thm)], [c_54, c_319])).
% 5.23/2.01  tff(c_52, plain, (r2_hidden('#skF_7', k7_relset_1('#skF_3', '#skF_4', '#skF_6', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_120])).
% 5.23/2.01  tff(c_333, plain, (r2_hidden('#skF_7', k9_relat_1('#skF_6', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_330, c_52])).
% 5.23/2.01  tff(c_187, plain, (![A_61, B_62, C_63]: (r2_hidden('#skF_2'(A_61, B_62, C_63), B_62) | ~r2_hidden(A_61, k9_relat_1(C_63, B_62)) | ~v1_relat_1(C_63))), inference(cnfTransformation, [status(thm)], [f_65])).
% 5.23/2.01  tff(c_50, plain, (![F_35]: (k1_funct_1('#skF_6', F_35)!='#skF_7' | ~r2_hidden(F_35, '#skF_5') | ~m1_subset_1(F_35, '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_120])).
% 5.23/2.01  tff(c_198, plain, (![A_61, C_63]: (k1_funct_1('#skF_6', '#skF_2'(A_61, '#skF_5', C_63))!='#skF_7' | ~m1_subset_1('#skF_2'(A_61, '#skF_5', C_63), '#skF_3') | ~r2_hidden(A_61, k9_relat_1(C_63, '#skF_5')) | ~v1_relat_1(C_63))), inference(resolution, [status(thm)], [c_187, c_50])).
% 5.23/2.01  tff(c_375, plain, (k1_funct_1('#skF_6', '#skF_2'('#skF_7', '#skF_5', '#skF_6'))!='#skF_7' | ~m1_subset_1('#skF_2'('#skF_7', '#skF_5', '#skF_6'), '#skF_3') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_333, c_198])).
% 5.23/2.01  tff(c_390, plain, (k1_funct_1('#skF_6', '#skF_2'('#skF_7', '#skF_5', '#skF_6'))!='#skF_7' | ~m1_subset_1('#skF_2'('#skF_7', '#skF_5', '#skF_6'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_113, c_375])).
% 5.23/2.01  tff(c_398, plain, (~m1_subset_1('#skF_2'('#skF_7', '#skF_5', '#skF_6'), '#skF_3')), inference(splitLeft, [status(thm)], [c_390])).
% 5.23/2.01  tff(c_12, plain, (![B_6, A_5]: (m1_subset_1(B_6, A_5) | ~v1_xboole_0(B_6) | ~v1_xboole_0(A_5))), inference(cnfTransformation, [status(thm)], [f_45])).
% 5.23/2.01  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.23/2.01  tff(c_127, plain, (![F_52]: (k1_funct_1('#skF_6', F_52)!='#skF_7' | ~r2_hidden(F_52, '#skF_5') | ~m1_subset_1(F_52, '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_120])).
% 5.23/2.01  tff(c_137, plain, (k1_funct_1('#skF_6', '#skF_1'('#skF_5'))!='#skF_7' | ~m1_subset_1('#skF_1'('#skF_5'), '#skF_3') | v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_4, c_127])).
% 5.23/2.01  tff(c_141, plain, (~m1_subset_1('#skF_1'('#skF_5'), '#skF_3')), inference(splitLeft, [status(thm)], [c_137])).
% 5.23/2.01  tff(c_145, plain, (~v1_xboole_0('#skF_1'('#skF_5')) | ~v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_12, c_141])).
% 5.23/2.01  tff(c_153, plain, (~v1_xboole_0('#skF_3')), inference(splitLeft, [status(thm)], [c_145])).
% 5.23/2.01  tff(c_56, plain, (v1_funct_2('#skF_6', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_120])).
% 5.23/2.01  tff(c_168, plain, (![A_58, B_59, C_60]: (k1_relset_1(A_58, B_59, C_60)=k1_relat_1(C_60) | ~m1_subset_1(C_60, k1_zfmisc_1(k2_zfmisc_1(A_58, B_59))))), inference(cnfTransformation, [status(thm)], [f_79])).
% 5.23/2.01  tff(c_182, plain, (k1_relset_1('#skF_3', '#skF_4', '#skF_6')=k1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_54, c_168])).
% 5.23/2.01  tff(c_880, plain, (![B_185, A_186, C_187]: (k1_xboole_0=B_185 | k1_relset_1(A_186, B_185, C_187)=A_186 | ~v1_funct_2(C_187, A_186, B_185) | ~m1_subset_1(C_187, k1_zfmisc_1(k2_zfmisc_1(A_186, B_185))))), inference(cnfTransformation, [status(thm)], [f_101])).
% 5.23/2.01  tff(c_891, plain, (k1_xboole_0='#skF_4' | k1_relset_1('#skF_3', '#skF_4', '#skF_6')='#skF_3' | ~v1_funct_2('#skF_6', '#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_54, c_880])).
% 5.23/2.01  tff(c_896, plain, (k1_xboole_0='#skF_4' | k1_relat_1('#skF_6')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_56, c_182, c_891])).
% 5.23/2.01  tff(c_897, plain, (k1_relat_1('#skF_6')='#skF_3'), inference(splitLeft, [status(thm)], [c_896])).
% 5.23/2.01  tff(c_26, plain, (![A_12, B_13, C_14]: (r2_hidden('#skF_2'(A_12, B_13, C_14), k1_relat_1(C_14)) | ~r2_hidden(A_12, k9_relat_1(C_14, B_13)) | ~v1_relat_1(C_14))), inference(cnfTransformation, [status(thm)], [f_65])).
% 5.23/2.01  tff(c_918, plain, (![A_12, B_13]: (r2_hidden('#skF_2'(A_12, B_13, '#skF_6'), '#skF_3') | ~r2_hidden(A_12, k9_relat_1('#skF_6', B_13)) | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_897, c_26])).
% 5.23/2.01  tff(c_944, plain, (![A_190, B_191]: (r2_hidden('#skF_2'(A_190, B_191, '#skF_6'), '#skF_3') | ~r2_hidden(A_190, k9_relat_1('#skF_6', B_191)))), inference(demodulation, [status(thm), theory('equality')], [c_113, c_918])).
% 5.23/2.01  tff(c_8, plain, (![B_6, A_5]: (m1_subset_1(B_6, A_5) | ~r2_hidden(B_6, A_5) | v1_xboole_0(A_5))), inference(cnfTransformation, [status(thm)], [f_45])).
% 5.23/2.01  tff(c_947, plain, (![A_190, B_191]: (m1_subset_1('#skF_2'(A_190, B_191, '#skF_6'), '#skF_3') | v1_xboole_0('#skF_3') | ~r2_hidden(A_190, k9_relat_1('#skF_6', B_191)))), inference(resolution, [status(thm)], [c_944, c_8])).
% 5.23/2.01  tff(c_955, plain, (![A_192, B_193]: (m1_subset_1('#skF_2'(A_192, B_193, '#skF_6'), '#skF_3') | ~r2_hidden(A_192, k9_relat_1('#skF_6', B_193)))), inference(negUnitSimplification, [status(thm)], [c_153, c_947])).
% 5.23/2.01  tff(c_966, plain, (m1_subset_1('#skF_2'('#skF_7', '#skF_5', '#skF_6'), '#skF_3')), inference(resolution, [status(thm)], [c_333, c_955])).
% 5.23/2.01  tff(c_984, plain, $false, inference(negUnitSimplification, [status(thm)], [c_398, c_966])).
% 5.23/2.01  tff(c_985, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_896])).
% 5.23/2.01  tff(c_6, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.23/2.01  tff(c_997, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_985, c_6])).
% 5.23/2.01  tff(c_40, plain, (![C_30, A_28]: (k1_xboole_0=C_30 | ~v1_funct_2(C_30, A_28, k1_xboole_0) | k1_xboole_0=A_28 | ~m1_subset_1(C_30, k1_zfmisc_1(k2_zfmisc_1(A_28, k1_xboole_0))))), inference(cnfTransformation, [status(thm)], [f_101])).
% 5.23/2.01  tff(c_1107, plain, (![C_207, A_208]: (C_207='#skF_4' | ~v1_funct_2(C_207, A_208, '#skF_4') | A_208='#skF_4' | ~m1_subset_1(C_207, k1_zfmisc_1(k2_zfmisc_1(A_208, '#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_985, c_985, c_985, c_985, c_40])).
% 5.23/2.01  tff(c_1118, plain, ('#skF_6'='#skF_4' | ~v1_funct_2('#skF_6', '#skF_3', '#skF_4') | '#skF_3'='#skF_4'), inference(resolution, [status(thm)], [c_54, c_1107])).
% 5.23/2.01  tff(c_1123, plain, ('#skF_6'='#skF_4' | '#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_56, c_1118])).
% 5.23/2.01  tff(c_1124, plain, ('#skF_3'='#skF_4'), inference(splitLeft, [status(thm)], [c_1123])).
% 5.23/2.01  tff(c_1146, plain, (~v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1124, c_153])).
% 5.23/2.01  tff(c_1154, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_997, c_1146])).
% 5.23/2.01  tff(c_1155, plain, ('#skF_6'='#skF_4'), inference(splitRight, [status(thm)], [c_1123])).
% 5.23/2.01  tff(c_58, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_120])).
% 5.23/2.01  tff(c_428, plain, (![A_116, C_117]: (r2_hidden(k4_tarski(A_116, k1_funct_1(C_117, A_116)), C_117) | ~r2_hidden(A_116, k1_relat_1(C_117)) | ~v1_funct_1(C_117) | ~v1_relat_1(C_117))), inference(cnfTransformation, [status(thm)], [f_75])).
% 5.23/2.01  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.23/2.01  tff(c_487, plain, (![C_120, A_121]: (~v1_xboole_0(C_120) | ~r2_hidden(A_121, k1_relat_1(C_120)) | ~v1_funct_1(C_120) | ~v1_relat_1(C_120))), inference(resolution, [status(thm)], [c_428, c_2])).
% 5.23/2.01  tff(c_512, plain, (![C_122]: (~v1_xboole_0(C_122) | ~v1_funct_1(C_122) | ~v1_relat_1(C_122) | v1_xboole_0(k1_relat_1(C_122)))), inference(resolution, [status(thm)], [c_4, c_487])).
% 5.23/2.01  tff(c_274, plain, (![A_89, B_90, C_91]: (r2_hidden('#skF_2'(A_89, B_90, C_91), k1_relat_1(C_91)) | ~r2_hidden(A_89, k9_relat_1(C_91, B_90)) | ~v1_relat_1(C_91))), inference(cnfTransformation, [status(thm)], [f_65])).
% 5.23/2.01  tff(c_283, plain, (![C_92, A_93, B_94]: (~v1_xboole_0(k1_relat_1(C_92)) | ~r2_hidden(A_93, k9_relat_1(C_92, B_94)) | ~v1_relat_1(C_92))), inference(resolution, [status(thm)], [c_274, c_2])).
% 5.23/2.01  tff(c_298, plain, (![C_92, B_94]: (~v1_xboole_0(k1_relat_1(C_92)) | ~v1_relat_1(C_92) | v1_xboole_0(k9_relat_1(C_92, B_94)))), inference(resolution, [status(thm)], [c_4, c_283])).
% 5.23/2.01  tff(c_79, plain, (~v1_xboole_0(k7_relset_1('#skF_3', '#skF_4', '#skF_6', '#skF_5'))), inference(resolution, [status(thm)], [c_52, c_2])).
% 5.23/2.01  tff(c_332, plain, (~v1_xboole_0(k9_relat_1('#skF_6', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_330, c_79])).
% 5.23/2.01  tff(c_345, plain, (~v1_xboole_0(k1_relat_1('#skF_6')) | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_298, c_332])).
% 5.23/2.01  tff(c_351, plain, (~v1_xboole_0(k1_relat_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_113, c_345])).
% 5.23/2.01  tff(c_515, plain, (~v1_xboole_0('#skF_6') | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_512, c_351])).
% 5.23/2.01  tff(c_520, plain, (~v1_xboole_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_113, c_58, c_515])).
% 5.23/2.01  tff(c_1162, plain, (~v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1155, c_520])).
% 5.23/2.01  tff(c_1181, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_997, c_1162])).
% 5.23/2.01  tff(c_1182, plain, (k1_funct_1('#skF_6', '#skF_2'('#skF_7', '#skF_5', '#skF_6'))!='#skF_7'), inference(splitRight, [status(thm)], [c_390])).
% 5.23/2.01  tff(c_1231, plain, (![A_221, B_222, C_223]: (r2_hidden(k4_tarski('#skF_2'(A_221, B_222, C_223), A_221), C_223) | ~r2_hidden(A_221, k9_relat_1(C_223, B_222)) | ~v1_relat_1(C_223))), inference(cnfTransformation, [status(thm)], [f_65])).
% 5.23/2.01  tff(c_30, plain, (![C_20, A_18, B_19]: (k1_funct_1(C_20, A_18)=B_19 | ~r2_hidden(k4_tarski(A_18, B_19), C_20) | ~v1_funct_1(C_20) | ~v1_relat_1(C_20))), inference(cnfTransformation, [status(thm)], [f_75])).
% 5.23/2.01  tff(c_1970, plain, (![C_313, A_314, B_315]: (k1_funct_1(C_313, '#skF_2'(A_314, B_315, C_313))=A_314 | ~v1_funct_1(C_313) | ~r2_hidden(A_314, k9_relat_1(C_313, B_315)) | ~v1_relat_1(C_313))), inference(resolution, [status(thm)], [c_1231, c_30])).
% 5.23/2.01  tff(c_1980, plain, (k1_funct_1('#skF_6', '#skF_2'('#skF_7', '#skF_5', '#skF_6'))='#skF_7' | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_333, c_1970])).
% 5.23/2.01  tff(c_1995, plain, (k1_funct_1('#skF_6', '#skF_2'('#skF_7', '#skF_5', '#skF_6'))='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_113, c_58, c_1980])).
% 5.23/2.01  tff(c_1997, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1182, c_1995])).
% 5.23/2.01  tff(c_1999, plain, (v1_xboole_0('#skF_3')), inference(splitRight, [status(thm)], [c_145])).
% 5.23/2.01  tff(c_2001, plain, (![A_317, B_318, C_319]: (k1_relset_1(A_317, B_318, C_319)=k1_relat_1(C_319) | ~m1_subset_1(C_319, k1_zfmisc_1(k2_zfmisc_1(A_317, B_318))))), inference(cnfTransformation, [status(thm)], [f_79])).
% 5.23/2.01  tff(c_2015, plain, (k1_relset_1('#skF_3', '#skF_4', '#skF_6')=k1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_54, c_2001])).
% 5.23/2.01  tff(c_2624, plain, (![B_419, A_420, C_421]: (k1_xboole_0=B_419 | k1_relset_1(A_420, B_419, C_421)=A_420 | ~v1_funct_2(C_421, A_420, B_419) | ~m1_subset_1(C_421, k1_zfmisc_1(k2_zfmisc_1(A_420, B_419))))), inference(cnfTransformation, [status(thm)], [f_101])).
% 5.23/2.01  tff(c_2635, plain, (k1_xboole_0='#skF_4' | k1_relset_1('#skF_3', '#skF_4', '#skF_6')='#skF_3' | ~v1_funct_2('#skF_6', '#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_54, c_2624])).
% 5.23/2.01  tff(c_2640, plain, (k1_xboole_0='#skF_4' | k1_relat_1('#skF_6')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_56, c_2015, c_2635])).
% 5.23/2.01  tff(c_2641, plain, (k1_relat_1('#skF_6')='#skF_3'), inference(splitLeft, [status(thm)], [c_2640])).
% 5.23/2.01  tff(c_2124, plain, (![A_351, B_352, C_353, D_354]: (k7_relset_1(A_351, B_352, C_353, D_354)=k9_relat_1(C_353, D_354) | ~m1_subset_1(C_353, k1_zfmisc_1(k2_zfmisc_1(A_351, B_352))))), inference(cnfTransformation, [status(thm)], [f_83])).
% 5.23/2.01  tff(c_2135, plain, (![D_354]: (k7_relset_1('#skF_3', '#skF_4', '#skF_6', D_354)=k9_relat_1('#skF_6', D_354))), inference(resolution, [status(thm)], [c_54, c_2124])).
% 5.23/2.01  tff(c_2138, plain, (r2_hidden('#skF_7', k9_relat_1('#skF_6', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_2135, c_52])).
% 5.23/2.01  tff(c_2206, plain, (![A_360, B_361, C_362]: (r2_hidden('#skF_2'(A_360, B_361, C_362), k1_relat_1(C_362)) | ~r2_hidden(A_360, k9_relat_1(C_362, B_361)) | ~v1_relat_1(C_362))), inference(cnfTransformation, [status(thm)], [f_65])).
% 5.23/2.01  tff(c_2253, plain, (![C_365, A_366, B_367]: (~v1_xboole_0(k1_relat_1(C_365)) | ~r2_hidden(A_366, k9_relat_1(C_365, B_367)) | ~v1_relat_1(C_365))), inference(resolution, [status(thm)], [c_2206, c_2])).
% 5.23/2.01  tff(c_2260, plain, (~v1_xboole_0(k1_relat_1('#skF_6')) | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_2138, c_2253])).
% 5.23/2.01  tff(c_2276, plain, (~v1_xboole_0(k1_relat_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_113, c_2260])).
% 5.23/2.01  tff(c_2642, plain, (~v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2641, c_2276])).
% 5.23/2.01  tff(c_2646, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1999, c_2642])).
% 5.23/2.01  tff(c_2647, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_2640])).
% 5.23/2.01  tff(c_2656, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2647, c_6])).
% 5.23/2.01  tff(c_2697, plain, (![C_432, A_433]: (C_432='#skF_4' | ~v1_funct_2(C_432, A_433, '#skF_4') | A_433='#skF_4' | ~m1_subset_1(C_432, k1_zfmisc_1(k2_zfmisc_1(A_433, '#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_2647, c_2647, c_2647, c_2647, c_40])).
% 5.23/2.01  tff(c_2708, plain, ('#skF_6'='#skF_4' | ~v1_funct_2('#skF_6', '#skF_3', '#skF_4') | '#skF_3'='#skF_4'), inference(resolution, [status(thm)], [c_54, c_2697])).
% 5.23/2.01  tff(c_2713, plain, ('#skF_6'='#skF_4' | '#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_56, c_2708])).
% 5.23/2.01  tff(c_2714, plain, ('#skF_3'='#skF_4'), inference(splitLeft, [status(thm)], [c_2713])).
% 5.23/2.01  tff(c_2648, plain, (k1_relat_1('#skF_6')!='#skF_3'), inference(splitRight, [status(thm)], [c_2640])).
% 5.23/2.01  tff(c_2723, plain, (k1_relat_1('#skF_6')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_2714, c_2648])).
% 5.23/2.01  tff(c_2739, plain, (v1_funct_2('#skF_6', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2714, c_56])).
% 5.23/2.01  tff(c_2733, plain, (k1_relset_1('#skF_4', '#skF_4', '#skF_6')=k1_relat_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_2714, c_2015])).
% 5.23/2.01  tff(c_2738, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_2714, c_54])).
% 5.23/2.01  tff(c_46, plain, (![B_29, C_30]: (k1_relset_1(k1_xboole_0, B_29, C_30)=k1_xboole_0 | ~v1_funct_2(C_30, k1_xboole_0, B_29) | ~m1_subset_1(C_30, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_29))))), inference(cnfTransformation, [status(thm)], [f_101])).
% 5.23/2.01  tff(c_2920, plain, (![B_455, C_456]: (k1_relset_1('#skF_4', B_455, C_456)='#skF_4' | ~v1_funct_2(C_456, '#skF_4', B_455) | ~m1_subset_1(C_456, k1_zfmisc_1(k2_zfmisc_1('#skF_4', B_455))))), inference(demodulation, [status(thm), theory('equality')], [c_2647, c_2647, c_2647, c_2647, c_46])).
% 5.23/2.01  tff(c_2923, plain, (k1_relset_1('#skF_4', '#skF_4', '#skF_6')='#skF_4' | ~v1_funct_2('#skF_6', '#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_2738, c_2920])).
% 5.23/2.01  tff(c_2934, plain, (k1_relat_1('#skF_6')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_2739, c_2733, c_2923])).
% 5.23/2.01  tff(c_2936, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2723, c_2934])).
% 5.23/2.01  tff(c_2937, plain, ('#skF_6'='#skF_4'), inference(splitRight, [status(thm)], [c_2713])).
% 5.23/2.01  tff(c_2215, plain, (![A_363, C_364]: (r2_hidden(k4_tarski(A_363, k1_funct_1(C_364, A_363)), C_364) | ~r2_hidden(A_363, k1_relat_1(C_364)) | ~v1_funct_1(C_364) | ~v1_relat_1(C_364))), inference(cnfTransformation, [status(thm)], [f_75])).
% 5.23/2.01  tff(c_2291, plain, (![C_370, A_371]: (~v1_xboole_0(C_370) | ~r2_hidden(A_371, k1_relat_1(C_370)) | ~v1_funct_1(C_370) | ~v1_relat_1(C_370))), inference(resolution, [status(thm)], [c_2215, c_2])).
% 5.23/2.01  tff(c_2316, plain, (![C_372]: (~v1_xboole_0(C_372) | ~v1_funct_1(C_372) | ~v1_relat_1(C_372) | v1_xboole_0(k1_relat_1(C_372)))), inference(resolution, [status(thm)], [c_4, c_2291])).
% 5.23/2.01  tff(c_2319, plain, (~v1_xboole_0('#skF_6') | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_2316, c_2276])).
% 5.23/2.01  tff(c_2324, plain, (~v1_xboole_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_113, c_58, c_2319])).
% 5.23/2.01  tff(c_2952, plain, (~v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2937, c_2324])).
% 5.23/2.01  tff(c_2971, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2656, c_2952])).
% 5.23/2.01  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.23/2.01  
% 5.23/2.01  Inference rules
% 5.23/2.01  ----------------------
% 5.23/2.01  #Ref     : 0
% 5.23/2.01  #Sup     : 570
% 5.23/2.01  #Fact    : 0
% 5.23/2.01  #Define  : 0
% 5.23/2.01  #Split   : 18
% 5.23/2.01  #Chain   : 0
% 5.23/2.01  #Close   : 0
% 5.23/2.01  
% 5.23/2.01  Ordering : KBO
% 5.23/2.01  
% 5.23/2.01  Simplification rules
% 5.23/2.01  ----------------------
% 5.23/2.01  #Subsume      : 120
% 5.23/2.01  #Demod        : 281
% 5.23/2.01  #Tautology    : 53
% 5.23/2.01  #SimpNegUnit  : 29
% 5.23/2.01  #BackRed      : 110
% 5.23/2.01  
% 5.23/2.01  #Partial instantiations: 0
% 5.23/2.01  #Strategies tried      : 1
% 5.23/2.01  
% 5.23/2.01  Timing (in seconds)
% 5.23/2.01  ----------------------
% 5.23/2.02  Preprocessing        : 0.34
% 5.23/2.02  Parsing              : 0.17
% 5.23/2.02  CNF conversion       : 0.02
% 5.23/2.02  Main loop            : 0.88
% 5.23/2.02  Inferencing          : 0.31
% 5.23/2.02  Reduction            : 0.23
% 5.23/2.02  Demodulation         : 0.15
% 5.23/2.02  BG Simplification    : 0.04
% 5.23/2.02  Subsumption          : 0.21
% 5.23/2.02  Abstraction          : 0.06
% 5.23/2.02  MUC search           : 0.00
% 5.23/2.02  Cooper               : 0.00
% 5.23/2.02  Total                : 1.27
% 5.23/2.02  Index Insertion      : 0.00
% 5.23/2.02  Index Deletion       : 0.00
% 5.23/2.02  Index Matching       : 0.00
% 5.23/2.02  BG Taut test         : 0.00
%------------------------------------------------------------------------------
