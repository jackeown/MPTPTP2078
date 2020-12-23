%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:16:23 EST 2020

% Result     : Theorem 3.22s
% Output     : CNFRefutation 3.38s
% Verified   : 
% Statistics : Number of formulae       :   85 ( 252 expanded)
%              Number of leaves         :   37 ( 105 expanded)
%              Depth                    :   12
%              Number of atoms          :  152 ( 705 expanded)
%              Number of equality atoms :   28 ( 139 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k1_relset_1 > k9_relat_1 > k4_tarski > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_4

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

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_119,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ! [E] :
            ~ ( r2_hidden(E,k7_relset_1(A,B,D,C))
              & ! [F] :
                  ~ ( r2_hidden(F,A)
                    & r2_hidden(F,C)
                    & E = k1_funct_1(D,F) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t115_funct_2)).

tff(f_68,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_74,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_82,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_38,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k9_relat_1(C,B))
      <=> ? [D] :
            ( r2_hidden(D,k1_relat_1(C))
            & r2_hidden(k4_tarski(D,A),C)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t143_relat_1)).

tff(f_59,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( r2_hidden(k4_tarski(A,B),C)
      <=> ( r2_hidden(A,k1_relat_1(C))
          & B = k1_funct_1(C,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_funct_1)).

tff(f_78,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).

tff(f_49,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A)
        & v1_funct_1(B) )
     => ! [C] :
          ( r2_hidden(C,k1_relat_1(B))
         => r2_hidden(k1_funct_1(B,C),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t172_funct_1)).

tff(f_64,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

tff(f_27,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(c_48,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_59,plain,(
    ! [C_41,A_42,B_43] :
      ( v1_relat_1(C_41)
      | ~ m1_subset_1(C_41,k1_zfmisc_1(k2_zfmisc_1(A_42,B_43))) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_63,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_48,c_59])).

tff(c_65,plain,(
    ! [C_45,B_46,A_47] :
      ( v5_relat_1(C_45,B_46)
      | ~ m1_subset_1(C_45,k1_zfmisc_1(k2_zfmisc_1(A_47,B_46))) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_69,plain,(
    v5_relat_1('#skF_5','#skF_3') ),
    inference(resolution,[status(thm)],[c_48,c_65])).

tff(c_52,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_115,plain,(
    ! [A_74,B_75,C_76,D_77] :
      ( k7_relset_1(A_74,B_75,C_76,D_77) = k9_relat_1(C_76,D_77)
      | ~ m1_subset_1(C_76,k1_zfmisc_1(k2_zfmisc_1(A_74,B_75))) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_118,plain,(
    ! [D_77] : k7_relset_1('#skF_2','#skF_3','#skF_5',D_77) = k9_relat_1('#skF_5',D_77) ),
    inference(resolution,[status(thm)],[c_48,c_115])).

tff(c_46,plain,(
    r2_hidden('#skF_6',k7_relset_1('#skF_2','#skF_3','#skF_5','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_121,plain,(
    r2_hidden('#skF_6',k9_relat_1('#skF_5','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_118,c_46])).

tff(c_10,plain,(
    ! [A_2,B_3,C_4] :
      ( r2_hidden('#skF_1'(A_2,B_3,C_4),k1_relat_1(C_4))
      | ~ r2_hidden(A_2,k9_relat_1(C_4,B_3))
      | ~ v1_relat_1(C_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_6,plain,(
    ! [A_2,B_3,C_4] :
      ( r2_hidden('#skF_1'(A_2,B_3,C_4),B_3)
      | ~ r2_hidden(A_2,k9_relat_1(C_4,B_3))
      | ~ v1_relat_1(C_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_172,plain,(
    ! [A_93,B_94,C_95] :
      ( r2_hidden(k4_tarski('#skF_1'(A_93,B_94,C_95),A_93),C_95)
      | ~ r2_hidden(A_93,k9_relat_1(C_95,B_94))
      | ~ v1_relat_1(C_95) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_16,plain,(
    ! [C_14,A_12,B_13] :
      ( k1_funct_1(C_14,A_12) = B_13
      | ~ r2_hidden(k4_tarski(A_12,B_13),C_14)
      | ~ v1_funct_1(C_14)
      | ~ v1_relat_1(C_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_465,plain,(
    ! [C_138,A_139,B_140] :
      ( k1_funct_1(C_138,'#skF_1'(A_139,B_140,C_138)) = A_139
      | ~ v1_funct_1(C_138)
      | ~ r2_hidden(A_139,k9_relat_1(C_138,B_140))
      | ~ v1_relat_1(C_138) ) ),
    inference(resolution,[status(thm)],[c_172,c_16])).

tff(c_476,plain,
    ( k1_funct_1('#skF_5','#skF_1'('#skF_6','#skF_4','#skF_5')) = '#skF_6'
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_121,c_465])).

tff(c_485,plain,(
    k1_funct_1('#skF_5','#skF_1'('#skF_6','#skF_4','#skF_5')) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_63,c_52,c_476])).

tff(c_50,plain,(
    v1_funct_2('#skF_5','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_75,plain,(
    ! [A_51,B_52,C_53] :
      ( k1_relset_1(A_51,B_52,C_53) = k1_relat_1(C_53)
      | ~ m1_subset_1(C_53,k1_zfmisc_1(k2_zfmisc_1(A_51,B_52))) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_79,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_48,c_75])).

tff(c_306,plain,(
    ! [B_119,A_120,C_121] :
      ( k1_xboole_0 = B_119
      | k1_relset_1(A_120,B_119,C_121) = A_120
      | ~ v1_funct_2(C_121,A_120,B_119)
      | ~ m1_subset_1(C_121,k1_zfmisc_1(k2_zfmisc_1(A_120,B_119))) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_309,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relset_1('#skF_2','#skF_3','#skF_5') = '#skF_2'
    | ~ v1_funct_2('#skF_5','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_48,c_306])).

tff(c_312,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relat_1('#skF_5') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_79,c_309])).

tff(c_313,plain,(
    k1_relat_1('#skF_5') = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_312])).

tff(c_323,plain,(
    ! [A_2,B_3] :
      ( r2_hidden('#skF_1'(A_2,B_3,'#skF_5'),'#skF_2')
      | ~ r2_hidden(A_2,k9_relat_1('#skF_5',B_3))
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_313,c_10])).

tff(c_331,plain,(
    ! [A_2,B_3] :
      ( r2_hidden('#skF_1'(A_2,B_3,'#skF_5'),'#skF_2')
      | ~ r2_hidden(A_2,k9_relat_1('#skF_5',B_3)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_63,c_323])).

tff(c_200,plain,(
    ! [B_96,C_97,A_98] :
      ( r2_hidden(k1_funct_1(B_96,C_97),A_98)
      | ~ r2_hidden(C_97,k1_relat_1(B_96))
      | ~ v1_funct_1(B_96)
      | ~ v5_relat_1(B_96,A_98)
      | ~ v1_relat_1(B_96) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_20,plain,(
    ! [B_16,A_15] :
      ( ~ r1_tarski(B_16,A_15)
      | ~ r2_hidden(A_15,B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_219,plain,(
    ! [A_98,B_96,C_97] :
      ( ~ r1_tarski(A_98,k1_funct_1(B_96,C_97))
      | ~ r2_hidden(C_97,k1_relat_1(B_96))
      | ~ v1_funct_1(B_96)
      | ~ v5_relat_1(B_96,A_98)
      | ~ v1_relat_1(B_96) ) ),
    inference(resolution,[status(thm)],[c_200,c_20])).

tff(c_489,plain,(
    ! [A_98] :
      ( ~ r1_tarski(A_98,'#skF_6')
      | ~ r2_hidden('#skF_1'('#skF_6','#skF_4','#skF_5'),k1_relat_1('#skF_5'))
      | ~ v1_funct_1('#skF_5')
      | ~ v5_relat_1('#skF_5',A_98)
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_485,c_219])).

tff(c_505,plain,(
    ! [A_98] :
      ( ~ r1_tarski(A_98,'#skF_6')
      | ~ r2_hidden('#skF_1'('#skF_6','#skF_4','#skF_5'),'#skF_2')
      | ~ v5_relat_1('#skF_5',A_98) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_63,c_52,c_313,c_489])).

tff(c_537,plain,(
    ~ r2_hidden('#skF_1'('#skF_6','#skF_4','#skF_5'),'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_505])).

tff(c_540,plain,(
    ~ r2_hidden('#skF_6',k9_relat_1('#skF_5','#skF_4')) ),
    inference(resolution,[status(thm)],[c_331,c_537])).

tff(c_544,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_121,c_540])).

tff(c_546,plain,(
    r2_hidden('#skF_1'('#skF_6','#skF_4','#skF_5'),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_505])).

tff(c_44,plain,(
    ! [F_37] :
      ( k1_funct_1('#skF_5',F_37) != '#skF_6'
      | ~ r2_hidden(F_37,'#skF_4')
      | ~ r2_hidden(F_37,'#skF_2') ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_564,plain,
    ( k1_funct_1('#skF_5','#skF_1'('#skF_6','#skF_4','#skF_5')) != '#skF_6'
    | ~ r2_hidden('#skF_1'('#skF_6','#skF_4','#skF_5'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_546,c_44])).

tff(c_571,plain,(
    ~ r2_hidden('#skF_1'('#skF_6','#skF_4','#skF_5'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_485,c_564])).

tff(c_575,plain,
    ( ~ r2_hidden('#skF_6',k9_relat_1('#skF_5','#skF_4'))
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_6,c_571])).

tff(c_579,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_63,c_121,c_575])).

tff(c_580,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_312])).

tff(c_2,plain,(
    ! [A_1] : r1_tarski(k1_xboole_0,A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_301,plain,(
    ! [A_116,B_117,C_118] :
      ( ~ r1_tarski(A_116,k1_funct_1(B_117,C_118))
      | ~ r2_hidden(C_118,k1_relat_1(B_117))
      | ~ v1_funct_1(B_117)
      | ~ v5_relat_1(B_117,A_116)
      | ~ v1_relat_1(B_117) ) ),
    inference(resolution,[status(thm)],[c_200,c_20])).

tff(c_305,plain,(
    ! [C_118,B_117] :
      ( ~ r2_hidden(C_118,k1_relat_1(B_117))
      | ~ v1_funct_1(B_117)
      | ~ v5_relat_1(B_117,k1_xboole_0)
      | ~ v1_relat_1(B_117) ) ),
    inference(resolution,[status(thm)],[c_2,c_301])).

tff(c_648,plain,(
    ! [C_154,B_155] :
      ( ~ r2_hidden(C_154,k1_relat_1(B_155))
      | ~ v1_funct_1(B_155)
      | ~ v5_relat_1(B_155,'#skF_3')
      | ~ v1_relat_1(B_155) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_580,c_305])).

tff(c_714,plain,(
    ! [C_164,A_165,B_166] :
      ( ~ v1_funct_1(C_164)
      | ~ v5_relat_1(C_164,'#skF_3')
      | ~ r2_hidden(A_165,k9_relat_1(C_164,B_166))
      | ~ v1_relat_1(C_164) ) ),
    inference(resolution,[status(thm)],[c_10,c_648])).

tff(c_729,plain,
    ( ~ v1_funct_1('#skF_5')
    | ~ v5_relat_1('#skF_5','#skF_3')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_121,c_714])).

tff(c_740,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_63,c_69,c_52,c_729])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:20:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.22/1.48  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.22/1.49  
% 3.22/1.49  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.22/1.49  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k1_relset_1 > k9_relat_1 > k4_tarski > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_4
% 3.22/1.49  
% 3.22/1.49  %Foreground sorts:
% 3.22/1.49  
% 3.22/1.49  
% 3.22/1.49  %Background operators:
% 3.22/1.49  
% 3.22/1.49  
% 3.22/1.49  %Foreground operators:
% 3.22/1.49  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 3.22/1.49  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.22/1.49  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.22/1.49  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.22/1.49  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 3.22/1.49  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.22/1.49  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.22/1.49  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 3.22/1.49  tff('#skF_5', type, '#skF_5': $i).
% 3.22/1.49  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.22/1.49  tff('#skF_6', type, '#skF_6': $i).
% 3.22/1.49  tff('#skF_2', type, '#skF_2': $i).
% 3.22/1.49  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 3.22/1.49  tff('#skF_3', type, '#skF_3': $i).
% 3.22/1.49  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.22/1.49  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.22/1.49  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.22/1.49  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.22/1.49  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.22/1.49  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.22/1.49  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.22/1.49  tff('#skF_4', type, '#skF_4': $i).
% 3.22/1.49  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.22/1.49  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.22/1.49  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.22/1.49  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.22/1.49  
% 3.38/1.51  tff(f_119, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: ~(r2_hidden(E, k7_relset_1(A, B, D, C)) & (![F]: ~((r2_hidden(F, A) & r2_hidden(F, C)) & (E = k1_funct_1(D, F)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t115_funct_2)).
% 3.38/1.51  tff(f_68, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.38/1.51  tff(f_74, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.38/1.51  tff(f_82, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 3.38/1.51  tff(f_38, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k9_relat_1(C, B)) <=> (?[D]: ((r2_hidden(D, k1_relat_1(C)) & r2_hidden(k4_tarski(D, A), C)) & r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t143_relat_1)).
% 3.38/1.51  tff(f_59, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(k4_tarski(A, B), C) <=> (r2_hidden(A, k1_relat_1(C)) & (B = k1_funct_1(C, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_funct_1)).
% 3.38/1.51  tff(f_78, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.38/1.51  tff(f_100, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 3.38/1.51  tff(f_49, axiom, (![A, B]: (((v1_relat_1(B) & v5_relat_1(B, A)) & v1_funct_1(B)) => (![C]: (r2_hidden(C, k1_relat_1(B)) => r2_hidden(k1_funct_1(B, C), A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t172_funct_1)).
% 3.38/1.51  tff(f_64, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 3.38/1.51  tff(f_27, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 3.38/1.51  tff(c_48, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_119])).
% 3.38/1.51  tff(c_59, plain, (![C_41, A_42, B_43]: (v1_relat_1(C_41) | ~m1_subset_1(C_41, k1_zfmisc_1(k2_zfmisc_1(A_42, B_43))))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.38/1.51  tff(c_63, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_48, c_59])).
% 3.38/1.51  tff(c_65, plain, (![C_45, B_46, A_47]: (v5_relat_1(C_45, B_46) | ~m1_subset_1(C_45, k1_zfmisc_1(k2_zfmisc_1(A_47, B_46))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.38/1.51  tff(c_69, plain, (v5_relat_1('#skF_5', '#skF_3')), inference(resolution, [status(thm)], [c_48, c_65])).
% 3.38/1.51  tff(c_52, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_119])).
% 3.38/1.51  tff(c_115, plain, (![A_74, B_75, C_76, D_77]: (k7_relset_1(A_74, B_75, C_76, D_77)=k9_relat_1(C_76, D_77) | ~m1_subset_1(C_76, k1_zfmisc_1(k2_zfmisc_1(A_74, B_75))))), inference(cnfTransformation, [status(thm)], [f_82])).
% 3.38/1.51  tff(c_118, plain, (![D_77]: (k7_relset_1('#skF_2', '#skF_3', '#skF_5', D_77)=k9_relat_1('#skF_5', D_77))), inference(resolution, [status(thm)], [c_48, c_115])).
% 3.38/1.51  tff(c_46, plain, (r2_hidden('#skF_6', k7_relset_1('#skF_2', '#skF_3', '#skF_5', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_119])).
% 3.38/1.51  tff(c_121, plain, (r2_hidden('#skF_6', k9_relat_1('#skF_5', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_118, c_46])).
% 3.38/1.51  tff(c_10, plain, (![A_2, B_3, C_4]: (r2_hidden('#skF_1'(A_2, B_3, C_4), k1_relat_1(C_4)) | ~r2_hidden(A_2, k9_relat_1(C_4, B_3)) | ~v1_relat_1(C_4))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.38/1.51  tff(c_6, plain, (![A_2, B_3, C_4]: (r2_hidden('#skF_1'(A_2, B_3, C_4), B_3) | ~r2_hidden(A_2, k9_relat_1(C_4, B_3)) | ~v1_relat_1(C_4))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.38/1.51  tff(c_172, plain, (![A_93, B_94, C_95]: (r2_hidden(k4_tarski('#skF_1'(A_93, B_94, C_95), A_93), C_95) | ~r2_hidden(A_93, k9_relat_1(C_95, B_94)) | ~v1_relat_1(C_95))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.38/1.51  tff(c_16, plain, (![C_14, A_12, B_13]: (k1_funct_1(C_14, A_12)=B_13 | ~r2_hidden(k4_tarski(A_12, B_13), C_14) | ~v1_funct_1(C_14) | ~v1_relat_1(C_14))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.38/1.51  tff(c_465, plain, (![C_138, A_139, B_140]: (k1_funct_1(C_138, '#skF_1'(A_139, B_140, C_138))=A_139 | ~v1_funct_1(C_138) | ~r2_hidden(A_139, k9_relat_1(C_138, B_140)) | ~v1_relat_1(C_138))), inference(resolution, [status(thm)], [c_172, c_16])).
% 3.38/1.51  tff(c_476, plain, (k1_funct_1('#skF_5', '#skF_1'('#skF_6', '#skF_4', '#skF_5'))='#skF_6' | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_121, c_465])).
% 3.38/1.51  tff(c_485, plain, (k1_funct_1('#skF_5', '#skF_1'('#skF_6', '#skF_4', '#skF_5'))='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_63, c_52, c_476])).
% 3.38/1.51  tff(c_50, plain, (v1_funct_2('#skF_5', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_119])).
% 3.38/1.51  tff(c_75, plain, (![A_51, B_52, C_53]: (k1_relset_1(A_51, B_52, C_53)=k1_relat_1(C_53) | ~m1_subset_1(C_53, k1_zfmisc_1(k2_zfmisc_1(A_51, B_52))))), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.38/1.51  tff(c_79, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_48, c_75])).
% 3.38/1.51  tff(c_306, plain, (![B_119, A_120, C_121]: (k1_xboole_0=B_119 | k1_relset_1(A_120, B_119, C_121)=A_120 | ~v1_funct_2(C_121, A_120, B_119) | ~m1_subset_1(C_121, k1_zfmisc_1(k2_zfmisc_1(A_120, B_119))))), inference(cnfTransformation, [status(thm)], [f_100])).
% 3.38/1.51  tff(c_309, plain, (k1_xboole_0='#skF_3' | k1_relset_1('#skF_2', '#skF_3', '#skF_5')='#skF_2' | ~v1_funct_2('#skF_5', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_48, c_306])).
% 3.38/1.51  tff(c_312, plain, (k1_xboole_0='#skF_3' | k1_relat_1('#skF_5')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_50, c_79, c_309])).
% 3.38/1.51  tff(c_313, plain, (k1_relat_1('#skF_5')='#skF_2'), inference(splitLeft, [status(thm)], [c_312])).
% 3.38/1.51  tff(c_323, plain, (![A_2, B_3]: (r2_hidden('#skF_1'(A_2, B_3, '#skF_5'), '#skF_2') | ~r2_hidden(A_2, k9_relat_1('#skF_5', B_3)) | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_313, c_10])).
% 3.38/1.51  tff(c_331, plain, (![A_2, B_3]: (r2_hidden('#skF_1'(A_2, B_3, '#skF_5'), '#skF_2') | ~r2_hidden(A_2, k9_relat_1('#skF_5', B_3)))), inference(demodulation, [status(thm), theory('equality')], [c_63, c_323])).
% 3.38/1.51  tff(c_200, plain, (![B_96, C_97, A_98]: (r2_hidden(k1_funct_1(B_96, C_97), A_98) | ~r2_hidden(C_97, k1_relat_1(B_96)) | ~v1_funct_1(B_96) | ~v5_relat_1(B_96, A_98) | ~v1_relat_1(B_96))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.38/1.51  tff(c_20, plain, (![B_16, A_15]: (~r1_tarski(B_16, A_15) | ~r2_hidden(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.38/1.51  tff(c_219, plain, (![A_98, B_96, C_97]: (~r1_tarski(A_98, k1_funct_1(B_96, C_97)) | ~r2_hidden(C_97, k1_relat_1(B_96)) | ~v1_funct_1(B_96) | ~v5_relat_1(B_96, A_98) | ~v1_relat_1(B_96))), inference(resolution, [status(thm)], [c_200, c_20])).
% 3.38/1.51  tff(c_489, plain, (![A_98]: (~r1_tarski(A_98, '#skF_6') | ~r2_hidden('#skF_1'('#skF_6', '#skF_4', '#skF_5'), k1_relat_1('#skF_5')) | ~v1_funct_1('#skF_5') | ~v5_relat_1('#skF_5', A_98) | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_485, c_219])).
% 3.38/1.51  tff(c_505, plain, (![A_98]: (~r1_tarski(A_98, '#skF_6') | ~r2_hidden('#skF_1'('#skF_6', '#skF_4', '#skF_5'), '#skF_2') | ~v5_relat_1('#skF_5', A_98))), inference(demodulation, [status(thm), theory('equality')], [c_63, c_52, c_313, c_489])).
% 3.38/1.51  tff(c_537, plain, (~r2_hidden('#skF_1'('#skF_6', '#skF_4', '#skF_5'), '#skF_2')), inference(splitLeft, [status(thm)], [c_505])).
% 3.38/1.51  tff(c_540, plain, (~r2_hidden('#skF_6', k9_relat_1('#skF_5', '#skF_4'))), inference(resolution, [status(thm)], [c_331, c_537])).
% 3.38/1.51  tff(c_544, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_121, c_540])).
% 3.38/1.51  tff(c_546, plain, (r2_hidden('#skF_1'('#skF_6', '#skF_4', '#skF_5'), '#skF_2')), inference(splitRight, [status(thm)], [c_505])).
% 3.38/1.51  tff(c_44, plain, (![F_37]: (k1_funct_1('#skF_5', F_37)!='#skF_6' | ~r2_hidden(F_37, '#skF_4') | ~r2_hidden(F_37, '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_119])).
% 3.38/1.51  tff(c_564, plain, (k1_funct_1('#skF_5', '#skF_1'('#skF_6', '#skF_4', '#skF_5'))!='#skF_6' | ~r2_hidden('#skF_1'('#skF_6', '#skF_4', '#skF_5'), '#skF_4')), inference(resolution, [status(thm)], [c_546, c_44])).
% 3.38/1.51  tff(c_571, plain, (~r2_hidden('#skF_1'('#skF_6', '#skF_4', '#skF_5'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_485, c_564])).
% 3.38/1.51  tff(c_575, plain, (~r2_hidden('#skF_6', k9_relat_1('#skF_5', '#skF_4')) | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_6, c_571])).
% 3.38/1.51  tff(c_579, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_63, c_121, c_575])).
% 3.38/1.51  tff(c_580, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_312])).
% 3.38/1.51  tff(c_2, plain, (![A_1]: (r1_tarski(k1_xboole_0, A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.38/1.51  tff(c_301, plain, (![A_116, B_117, C_118]: (~r1_tarski(A_116, k1_funct_1(B_117, C_118)) | ~r2_hidden(C_118, k1_relat_1(B_117)) | ~v1_funct_1(B_117) | ~v5_relat_1(B_117, A_116) | ~v1_relat_1(B_117))), inference(resolution, [status(thm)], [c_200, c_20])).
% 3.38/1.51  tff(c_305, plain, (![C_118, B_117]: (~r2_hidden(C_118, k1_relat_1(B_117)) | ~v1_funct_1(B_117) | ~v5_relat_1(B_117, k1_xboole_0) | ~v1_relat_1(B_117))), inference(resolution, [status(thm)], [c_2, c_301])).
% 3.38/1.51  tff(c_648, plain, (![C_154, B_155]: (~r2_hidden(C_154, k1_relat_1(B_155)) | ~v1_funct_1(B_155) | ~v5_relat_1(B_155, '#skF_3') | ~v1_relat_1(B_155))), inference(demodulation, [status(thm), theory('equality')], [c_580, c_305])).
% 3.38/1.51  tff(c_714, plain, (![C_164, A_165, B_166]: (~v1_funct_1(C_164) | ~v5_relat_1(C_164, '#skF_3') | ~r2_hidden(A_165, k9_relat_1(C_164, B_166)) | ~v1_relat_1(C_164))), inference(resolution, [status(thm)], [c_10, c_648])).
% 3.38/1.51  tff(c_729, plain, (~v1_funct_1('#skF_5') | ~v5_relat_1('#skF_5', '#skF_3') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_121, c_714])).
% 3.38/1.51  tff(c_740, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_63, c_69, c_52, c_729])).
% 3.38/1.51  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.38/1.51  
% 3.38/1.51  Inference rules
% 3.38/1.51  ----------------------
% 3.38/1.51  #Ref     : 0
% 3.38/1.51  #Sup     : 139
% 3.38/1.51  #Fact    : 0
% 3.38/1.51  #Define  : 0
% 3.38/1.51  #Split   : 7
% 3.38/1.51  #Chain   : 0
% 3.38/1.51  #Close   : 0
% 3.38/1.51  
% 3.38/1.51  Ordering : KBO
% 3.38/1.51  
% 3.38/1.51  Simplification rules
% 3.38/1.51  ----------------------
% 3.38/1.51  #Subsume      : 13
% 3.38/1.51  #Demod        : 73
% 3.38/1.51  #Tautology    : 16
% 3.38/1.51  #SimpNegUnit  : 0
% 3.38/1.51  #BackRed      : 15
% 3.38/1.51  
% 3.38/1.51  #Partial instantiations: 0
% 3.38/1.51  #Strategies tried      : 1
% 3.38/1.51  
% 3.38/1.51  Timing (in seconds)
% 3.38/1.51  ----------------------
% 3.38/1.51  Preprocessing        : 0.35
% 3.38/1.51  Parsing              : 0.18
% 3.38/1.51  CNF conversion       : 0.02
% 3.38/1.52  Main loop            : 0.39
% 3.38/1.52  Inferencing          : 0.14
% 3.38/1.52  Reduction            : 0.10
% 3.38/1.52  Demodulation         : 0.08
% 3.38/1.52  BG Simplification    : 0.02
% 3.38/1.52  Subsumption          : 0.09
% 3.38/1.52  Abstraction          : 0.02
% 3.38/1.52  MUC search           : 0.00
% 3.38/1.52  Cooper               : 0.00
% 3.38/1.52  Total                : 0.77
% 3.38/1.52  Index Insertion      : 0.00
% 3.38/1.52  Index Deletion       : 0.00
% 3.38/1.52  Index Matching       : 0.00
% 3.38/1.52  BG Taut test         : 0.00
%------------------------------------------------------------------------------
