%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:16:29 EST 2020

% Result     : Theorem 2.76s
% Output     : CNFRefutation 3.18s
% Verified   : 
% Statistics : Number of formulae       :   92 ( 562 expanded)
%              Number of leaves         :   35 ( 210 expanded)
%              Depth                    :   12
%              Number of atoms          :  148 (1783 expanded)
%              Number of equality atoms :   48 ( 647 expanded)
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

tff(f_107,negated_conjecture,(
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

tff(f_70,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_41,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_39,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_66,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_88,axiom,(
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

tff(f_52,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k9_relat_1(C,B))
      <=> ? [D] :
            ( r2_hidden(D,k1_relat_1(C))
            & r2_hidden(k4_tarski(D,A),C)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t143_relat_1)).

tff(f_62,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( r2_hidden(k4_tarski(A,B),C)
      <=> ( r2_hidden(A,k1_relat_1(C))
          & B = k1_funct_1(C,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_funct_1)).

tff(f_32,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(c_46,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_141,plain,(
    ! [A_79,B_80,C_81,D_82] :
      ( k7_relset_1(A_79,B_80,C_81,D_82) = k9_relat_1(C_81,D_82)
      | ~ m1_subset_1(C_81,k1_zfmisc_1(k2_zfmisc_1(A_79,B_80))) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_144,plain,(
    ! [D_82] : k7_relset_1('#skF_3','#skF_4','#skF_6',D_82) = k9_relat_1('#skF_6',D_82) ),
    inference(resolution,[status(thm)],[c_46,c_141])).

tff(c_44,plain,(
    r2_hidden('#skF_7',k7_relset_1('#skF_3','#skF_4','#skF_6','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_146,plain,(
    r2_hidden('#skF_7',k9_relat_1('#skF_6','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_144,c_44])).

tff(c_10,plain,(
    ! [A_8,B_9] : v1_relat_1(k2_zfmisc_1(A_8,B_9)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_68,plain,(
    ! [B_40,A_41] :
      ( v1_relat_1(B_40)
      | ~ m1_subset_1(B_40,k1_zfmisc_1(A_41))
      | ~ v1_relat_1(A_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_71,plain,
    ( v1_relat_1('#skF_6')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_46,c_68])).

tff(c_74,plain,(
    v1_relat_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_71])).

tff(c_48,plain,(
    v1_funct_2('#skF_6','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_76,plain,(
    ! [A_42,B_43,C_44] :
      ( k1_relset_1(A_42,B_43,C_44) = k1_relat_1(C_44)
      | ~ m1_subset_1(C_44,k1_zfmisc_1(k2_zfmisc_1(A_42,B_43))) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_80,plain,(
    k1_relset_1('#skF_3','#skF_4','#skF_6') = k1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_46,c_76])).

tff(c_429,plain,(
    ! [B_131,A_132,C_133] :
      ( k1_xboole_0 = B_131
      | k1_relset_1(A_132,B_131,C_133) = A_132
      | ~ v1_funct_2(C_133,A_132,B_131)
      | ~ m1_subset_1(C_133,k1_zfmisc_1(k2_zfmisc_1(A_132,B_131))) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_432,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relset_1('#skF_3','#skF_4','#skF_6') = '#skF_3'
    | ~ v1_funct_2('#skF_6','#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_46,c_429])).

tff(c_435,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relat_1('#skF_6') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_80,c_432])).

tff(c_436,plain,(
    k1_relat_1('#skF_6') = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_435])).

tff(c_18,plain,(
    ! [A_10,B_11,C_12] :
      ( r2_hidden('#skF_2'(A_10,B_11,C_12),k1_relat_1(C_12))
      | ~ r2_hidden(A_10,k9_relat_1(C_12,B_11))
      | ~ v1_relat_1(C_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_454,plain,(
    ! [A_10,B_11] :
      ( r2_hidden('#skF_2'(A_10,B_11,'#skF_6'),'#skF_3')
      | ~ r2_hidden(A_10,k9_relat_1('#skF_6',B_11))
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_436,c_18])).

tff(c_472,plain,(
    ! [A_134,B_135] :
      ( r2_hidden('#skF_2'(A_134,B_135,'#skF_6'),'#skF_3')
      | ~ r2_hidden(A_134,k9_relat_1('#skF_6',B_135)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_454])).

tff(c_86,plain,(
    ! [A_46,B_47,C_48] :
      ( r2_hidden('#skF_2'(A_46,B_47,C_48),B_47)
      | ~ r2_hidden(A_46,k9_relat_1(C_48,B_47))
      | ~ v1_relat_1(C_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_42,plain,(
    ! [F_33] :
      ( k1_funct_1('#skF_6',F_33) != '#skF_7'
      | ~ r2_hidden(F_33,'#skF_5')
      | ~ r2_hidden(F_33,'#skF_3') ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_94,plain,(
    ! [A_46,C_48] :
      ( k1_funct_1('#skF_6','#skF_2'(A_46,'#skF_5',C_48)) != '#skF_7'
      | ~ r2_hidden('#skF_2'(A_46,'#skF_5',C_48),'#skF_3')
      | ~ r2_hidden(A_46,k9_relat_1(C_48,'#skF_5'))
      | ~ v1_relat_1(C_48) ) ),
    inference(resolution,[status(thm)],[c_86,c_42])).

tff(c_476,plain,(
    ! [A_134] :
      ( k1_funct_1('#skF_6','#skF_2'(A_134,'#skF_5','#skF_6')) != '#skF_7'
      | ~ v1_relat_1('#skF_6')
      | ~ r2_hidden(A_134,k9_relat_1('#skF_6','#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_472,c_94])).

tff(c_484,plain,(
    ! [A_136] :
      ( k1_funct_1('#skF_6','#skF_2'(A_136,'#skF_5','#skF_6')) != '#skF_7'
      | ~ r2_hidden(A_136,k9_relat_1('#skF_6','#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_476])).

tff(c_506,plain,(
    k1_funct_1('#skF_6','#skF_2'('#skF_7','#skF_5','#skF_6')) != '#skF_7' ),
    inference(resolution,[status(thm)],[c_146,c_484])).

tff(c_50,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_184,plain,(
    ! [A_84,B_85,C_86] :
      ( r2_hidden(k4_tarski('#skF_2'(A_84,B_85,C_86),A_84),C_86)
      | ~ r2_hidden(A_84,k9_relat_1(C_86,B_85))
      | ~ v1_relat_1(C_86) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_22,plain,(
    ! [C_18,A_16,B_17] :
      ( k1_funct_1(C_18,A_16) = B_17
      | ~ r2_hidden(k4_tarski(A_16,B_17),C_18)
      | ~ v1_funct_1(C_18)
      | ~ v1_relat_1(C_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_551,plain,(
    ! [C_148,A_149,B_150] :
      ( k1_funct_1(C_148,'#skF_2'(A_149,B_150,C_148)) = A_149
      | ~ v1_funct_1(C_148)
      | ~ r2_hidden(A_149,k9_relat_1(C_148,B_150))
      | ~ v1_relat_1(C_148) ) ),
    inference(resolution,[status(thm)],[c_184,c_22])).

tff(c_559,plain,
    ( k1_funct_1('#skF_6','#skF_2'('#skF_7','#skF_5','#skF_6')) = '#skF_7'
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_146,c_551])).

tff(c_570,plain,(
    k1_funct_1('#skF_6','#skF_2'('#skF_7','#skF_5','#skF_6')) = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_50,c_559])).

tff(c_572,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_506,c_570])).

tff(c_573,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_435])).

tff(c_6,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_580,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_573,c_6])).

tff(c_32,plain,(
    ! [C_28,A_26] :
      ( k1_xboole_0 = C_28
      | ~ v1_funct_2(C_28,A_26,k1_xboole_0)
      | k1_xboole_0 = A_26
      | ~ m1_subset_1(C_28,k1_zfmisc_1(k2_zfmisc_1(A_26,k1_xboole_0))) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_586,plain,(
    ! [C_152,A_153] :
      ( C_152 = '#skF_4'
      | ~ v1_funct_2(C_152,A_153,'#skF_4')
      | A_153 = '#skF_4'
      | ~ m1_subset_1(C_152,k1_zfmisc_1(k2_zfmisc_1(A_153,'#skF_4'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_573,c_573,c_573,c_573,c_32])).

tff(c_589,plain,
    ( '#skF_6' = '#skF_4'
    | ~ v1_funct_2('#skF_6','#skF_3','#skF_4')
    | '#skF_3' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_46,c_586])).

tff(c_592,plain,
    ( '#skF_6' = '#skF_4'
    | '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_589])).

tff(c_593,plain,(
    '#skF_3' = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_592])).

tff(c_574,plain,(
    k1_relat_1('#skF_6') != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_435])).

tff(c_601,plain,(
    k1_relat_1('#skF_6') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_593,c_574])).

tff(c_608,plain,(
    v1_funct_2('#skF_6','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_593,c_48])).

tff(c_604,plain,(
    k1_relset_1('#skF_4','#skF_4','#skF_6') = k1_relat_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_593,c_80])).

tff(c_607,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_593,c_46])).

tff(c_38,plain,(
    ! [B_27,C_28] :
      ( k1_relset_1(k1_xboole_0,B_27,C_28) = k1_xboole_0
      | ~ v1_funct_2(C_28,k1_xboole_0,B_27)
      | ~ m1_subset_1(C_28,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_27))) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_696,plain,(
    ! [B_166,C_167] :
      ( k1_relset_1('#skF_4',B_166,C_167) = '#skF_4'
      | ~ v1_funct_2(C_167,'#skF_4',B_166)
      | ~ m1_subset_1(C_167,k1_zfmisc_1(k2_zfmisc_1('#skF_4',B_166))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_573,c_573,c_573,c_573,c_38])).

tff(c_699,plain,
    ( k1_relset_1('#skF_4','#skF_4','#skF_6') = '#skF_4'
    | ~ v1_funct_2('#skF_6','#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_607,c_696])).

tff(c_702,plain,(
    k1_relat_1('#skF_6') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_608,c_604,c_699])).

tff(c_704,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_601,c_702])).

tff(c_705,plain,(
    '#skF_6' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_592])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_217,plain,(
    ! [C_87,A_88,B_89] :
      ( ~ v1_xboole_0(C_87)
      | ~ r2_hidden(A_88,k9_relat_1(C_87,B_89))
      | ~ v1_relat_1(C_87) ) ),
    inference(resolution,[status(thm)],[c_184,c_2])).

tff(c_224,plain,
    ( ~ v1_xboole_0('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_146,c_217])).

tff(c_236,plain,(
    ~ v1_xboole_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_224])).

tff(c_708,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_705,c_236])).

tff(c_722,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_580,c_708])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:00:09 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.76/1.44  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.76/1.45  
% 2.76/1.45  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.76/1.46  %$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k1_relset_1 > k9_relat_1 > k4_tarski > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_4
% 2.76/1.46  
% 2.76/1.46  %Foreground sorts:
% 2.76/1.46  
% 2.76/1.46  
% 2.76/1.46  %Background operators:
% 2.76/1.46  
% 2.76/1.46  
% 2.76/1.46  %Foreground operators:
% 2.76/1.46  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.76/1.46  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.76/1.46  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.76/1.46  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.76/1.46  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.76/1.46  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.76/1.46  tff('#skF_7', type, '#skF_7': $i).
% 2.76/1.46  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 2.76/1.46  tff('#skF_5', type, '#skF_5': $i).
% 2.76/1.46  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.76/1.46  tff('#skF_6', type, '#skF_6': $i).
% 2.76/1.46  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.76/1.46  tff('#skF_3', type, '#skF_3': $i).
% 2.76/1.46  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.76/1.46  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.76/1.46  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.76/1.46  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.76/1.46  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.76/1.46  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.76/1.46  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.76/1.46  tff('#skF_4', type, '#skF_4': $i).
% 2.76/1.46  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.76/1.46  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.76/1.46  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.76/1.46  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.76/1.46  
% 3.18/1.47  tff(f_107, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: ~(r2_hidden(E, k7_relset_1(A, B, D, C)) & (![F]: ~((r2_hidden(F, A) & r2_hidden(F, C)) & (E = k1_funct_1(D, F)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t115_funct_2)).
% 3.18/1.47  tff(f_70, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 3.18/1.47  tff(f_41, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 3.18/1.47  tff(f_39, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 3.18/1.47  tff(f_66, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.18/1.47  tff(f_88, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 3.18/1.47  tff(f_52, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k9_relat_1(C, B)) <=> (?[D]: ((r2_hidden(D, k1_relat_1(C)) & r2_hidden(k4_tarski(D, A), C)) & r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t143_relat_1)).
% 3.18/1.47  tff(f_62, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(k4_tarski(A, B), C) <=> (r2_hidden(A, k1_relat_1(C)) & (B = k1_funct_1(C, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_funct_1)).
% 3.18/1.47  tff(f_32, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 3.18/1.47  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 3.18/1.47  tff(c_46, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_107])).
% 3.18/1.47  tff(c_141, plain, (![A_79, B_80, C_81, D_82]: (k7_relset_1(A_79, B_80, C_81, D_82)=k9_relat_1(C_81, D_82) | ~m1_subset_1(C_81, k1_zfmisc_1(k2_zfmisc_1(A_79, B_80))))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.18/1.47  tff(c_144, plain, (![D_82]: (k7_relset_1('#skF_3', '#skF_4', '#skF_6', D_82)=k9_relat_1('#skF_6', D_82))), inference(resolution, [status(thm)], [c_46, c_141])).
% 3.18/1.47  tff(c_44, plain, (r2_hidden('#skF_7', k7_relset_1('#skF_3', '#skF_4', '#skF_6', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_107])).
% 3.18/1.47  tff(c_146, plain, (r2_hidden('#skF_7', k9_relat_1('#skF_6', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_144, c_44])).
% 3.18/1.47  tff(c_10, plain, (![A_8, B_9]: (v1_relat_1(k2_zfmisc_1(A_8, B_9)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.18/1.47  tff(c_68, plain, (![B_40, A_41]: (v1_relat_1(B_40) | ~m1_subset_1(B_40, k1_zfmisc_1(A_41)) | ~v1_relat_1(A_41))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.18/1.47  tff(c_71, plain, (v1_relat_1('#skF_6') | ~v1_relat_1(k2_zfmisc_1('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_46, c_68])).
% 3.18/1.47  tff(c_74, plain, (v1_relat_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_10, c_71])).
% 3.18/1.47  tff(c_48, plain, (v1_funct_2('#skF_6', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_107])).
% 3.18/1.47  tff(c_76, plain, (![A_42, B_43, C_44]: (k1_relset_1(A_42, B_43, C_44)=k1_relat_1(C_44) | ~m1_subset_1(C_44, k1_zfmisc_1(k2_zfmisc_1(A_42, B_43))))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.18/1.47  tff(c_80, plain, (k1_relset_1('#skF_3', '#skF_4', '#skF_6')=k1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_46, c_76])).
% 3.18/1.47  tff(c_429, plain, (![B_131, A_132, C_133]: (k1_xboole_0=B_131 | k1_relset_1(A_132, B_131, C_133)=A_132 | ~v1_funct_2(C_133, A_132, B_131) | ~m1_subset_1(C_133, k1_zfmisc_1(k2_zfmisc_1(A_132, B_131))))), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.18/1.47  tff(c_432, plain, (k1_xboole_0='#skF_4' | k1_relset_1('#skF_3', '#skF_4', '#skF_6')='#skF_3' | ~v1_funct_2('#skF_6', '#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_46, c_429])).
% 3.18/1.47  tff(c_435, plain, (k1_xboole_0='#skF_4' | k1_relat_1('#skF_6')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_48, c_80, c_432])).
% 3.18/1.47  tff(c_436, plain, (k1_relat_1('#skF_6')='#skF_3'), inference(splitLeft, [status(thm)], [c_435])).
% 3.18/1.47  tff(c_18, plain, (![A_10, B_11, C_12]: (r2_hidden('#skF_2'(A_10, B_11, C_12), k1_relat_1(C_12)) | ~r2_hidden(A_10, k9_relat_1(C_12, B_11)) | ~v1_relat_1(C_12))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.18/1.47  tff(c_454, plain, (![A_10, B_11]: (r2_hidden('#skF_2'(A_10, B_11, '#skF_6'), '#skF_3') | ~r2_hidden(A_10, k9_relat_1('#skF_6', B_11)) | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_436, c_18])).
% 3.18/1.47  tff(c_472, plain, (![A_134, B_135]: (r2_hidden('#skF_2'(A_134, B_135, '#skF_6'), '#skF_3') | ~r2_hidden(A_134, k9_relat_1('#skF_6', B_135)))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_454])).
% 3.18/1.47  tff(c_86, plain, (![A_46, B_47, C_48]: (r2_hidden('#skF_2'(A_46, B_47, C_48), B_47) | ~r2_hidden(A_46, k9_relat_1(C_48, B_47)) | ~v1_relat_1(C_48))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.18/1.47  tff(c_42, plain, (![F_33]: (k1_funct_1('#skF_6', F_33)!='#skF_7' | ~r2_hidden(F_33, '#skF_5') | ~r2_hidden(F_33, '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_107])).
% 3.18/1.47  tff(c_94, plain, (![A_46, C_48]: (k1_funct_1('#skF_6', '#skF_2'(A_46, '#skF_5', C_48))!='#skF_7' | ~r2_hidden('#skF_2'(A_46, '#skF_5', C_48), '#skF_3') | ~r2_hidden(A_46, k9_relat_1(C_48, '#skF_5')) | ~v1_relat_1(C_48))), inference(resolution, [status(thm)], [c_86, c_42])).
% 3.18/1.47  tff(c_476, plain, (![A_134]: (k1_funct_1('#skF_6', '#skF_2'(A_134, '#skF_5', '#skF_6'))!='#skF_7' | ~v1_relat_1('#skF_6') | ~r2_hidden(A_134, k9_relat_1('#skF_6', '#skF_5')))), inference(resolution, [status(thm)], [c_472, c_94])).
% 3.18/1.47  tff(c_484, plain, (![A_136]: (k1_funct_1('#skF_6', '#skF_2'(A_136, '#skF_5', '#skF_6'))!='#skF_7' | ~r2_hidden(A_136, k9_relat_1('#skF_6', '#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_476])).
% 3.18/1.47  tff(c_506, plain, (k1_funct_1('#skF_6', '#skF_2'('#skF_7', '#skF_5', '#skF_6'))!='#skF_7'), inference(resolution, [status(thm)], [c_146, c_484])).
% 3.18/1.47  tff(c_50, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_107])).
% 3.18/1.47  tff(c_184, plain, (![A_84, B_85, C_86]: (r2_hidden(k4_tarski('#skF_2'(A_84, B_85, C_86), A_84), C_86) | ~r2_hidden(A_84, k9_relat_1(C_86, B_85)) | ~v1_relat_1(C_86))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.18/1.47  tff(c_22, plain, (![C_18, A_16, B_17]: (k1_funct_1(C_18, A_16)=B_17 | ~r2_hidden(k4_tarski(A_16, B_17), C_18) | ~v1_funct_1(C_18) | ~v1_relat_1(C_18))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.18/1.47  tff(c_551, plain, (![C_148, A_149, B_150]: (k1_funct_1(C_148, '#skF_2'(A_149, B_150, C_148))=A_149 | ~v1_funct_1(C_148) | ~r2_hidden(A_149, k9_relat_1(C_148, B_150)) | ~v1_relat_1(C_148))), inference(resolution, [status(thm)], [c_184, c_22])).
% 3.18/1.47  tff(c_559, plain, (k1_funct_1('#skF_6', '#skF_2'('#skF_7', '#skF_5', '#skF_6'))='#skF_7' | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_146, c_551])).
% 3.18/1.47  tff(c_570, plain, (k1_funct_1('#skF_6', '#skF_2'('#skF_7', '#skF_5', '#skF_6'))='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_74, c_50, c_559])).
% 3.18/1.47  tff(c_572, plain, $false, inference(negUnitSimplification, [status(thm)], [c_506, c_570])).
% 3.18/1.47  tff(c_573, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_435])).
% 3.18/1.47  tff(c_6, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.18/1.47  tff(c_580, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_573, c_6])).
% 3.18/1.47  tff(c_32, plain, (![C_28, A_26]: (k1_xboole_0=C_28 | ~v1_funct_2(C_28, A_26, k1_xboole_0) | k1_xboole_0=A_26 | ~m1_subset_1(C_28, k1_zfmisc_1(k2_zfmisc_1(A_26, k1_xboole_0))))), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.18/1.47  tff(c_586, plain, (![C_152, A_153]: (C_152='#skF_4' | ~v1_funct_2(C_152, A_153, '#skF_4') | A_153='#skF_4' | ~m1_subset_1(C_152, k1_zfmisc_1(k2_zfmisc_1(A_153, '#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_573, c_573, c_573, c_573, c_32])).
% 3.18/1.47  tff(c_589, plain, ('#skF_6'='#skF_4' | ~v1_funct_2('#skF_6', '#skF_3', '#skF_4') | '#skF_3'='#skF_4'), inference(resolution, [status(thm)], [c_46, c_586])).
% 3.18/1.47  tff(c_592, plain, ('#skF_6'='#skF_4' | '#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_48, c_589])).
% 3.18/1.47  tff(c_593, plain, ('#skF_3'='#skF_4'), inference(splitLeft, [status(thm)], [c_592])).
% 3.18/1.47  tff(c_574, plain, (k1_relat_1('#skF_6')!='#skF_3'), inference(splitRight, [status(thm)], [c_435])).
% 3.18/1.47  tff(c_601, plain, (k1_relat_1('#skF_6')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_593, c_574])).
% 3.18/1.47  tff(c_608, plain, (v1_funct_2('#skF_6', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_593, c_48])).
% 3.18/1.47  tff(c_604, plain, (k1_relset_1('#skF_4', '#skF_4', '#skF_6')=k1_relat_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_593, c_80])).
% 3.18/1.47  tff(c_607, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_593, c_46])).
% 3.18/1.47  tff(c_38, plain, (![B_27, C_28]: (k1_relset_1(k1_xboole_0, B_27, C_28)=k1_xboole_0 | ~v1_funct_2(C_28, k1_xboole_0, B_27) | ~m1_subset_1(C_28, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_27))))), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.18/1.47  tff(c_696, plain, (![B_166, C_167]: (k1_relset_1('#skF_4', B_166, C_167)='#skF_4' | ~v1_funct_2(C_167, '#skF_4', B_166) | ~m1_subset_1(C_167, k1_zfmisc_1(k2_zfmisc_1('#skF_4', B_166))))), inference(demodulation, [status(thm), theory('equality')], [c_573, c_573, c_573, c_573, c_38])).
% 3.18/1.47  tff(c_699, plain, (k1_relset_1('#skF_4', '#skF_4', '#skF_6')='#skF_4' | ~v1_funct_2('#skF_6', '#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_607, c_696])).
% 3.18/1.47  tff(c_702, plain, (k1_relat_1('#skF_6')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_608, c_604, c_699])).
% 3.18/1.47  tff(c_704, plain, $false, inference(negUnitSimplification, [status(thm)], [c_601, c_702])).
% 3.18/1.47  tff(c_705, plain, ('#skF_6'='#skF_4'), inference(splitRight, [status(thm)], [c_592])).
% 3.18/1.47  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.18/1.47  tff(c_217, plain, (![C_87, A_88, B_89]: (~v1_xboole_0(C_87) | ~r2_hidden(A_88, k9_relat_1(C_87, B_89)) | ~v1_relat_1(C_87))), inference(resolution, [status(thm)], [c_184, c_2])).
% 3.18/1.47  tff(c_224, plain, (~v1_xboole_0('#skF_6') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_146, c_217])).
% 3.18/1.47  tff(c_236, plain, (~v1_xboole_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_224])).
% 3.18/1.47  tff(c_708, plain, (~v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_705, c_236])).
% 3.18/1.47  tff(c_722, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_580, c_708])).
% 3.18/1.47  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.18/1.47  
% 3.18/1.47  Inference rules
% 3.18/1.47  ----------------------
% 3.18/1.47  #Ref     : 0
% 3.18/1.47  #Sup     : 125
% 3.18/1.47  #Fact    : 0
% 3.18/1.47  #Define  : 0
% 3.18/1.47  #Split   : 4
% 3.18/1.47  #Chain   : 0
% 3.18/1.47  #Close   : 0
% 3.18/1.47  
% 3.18/1.47  Ordering : KBO
% 3.18/1.47  
% 3.18/1.47  Simplification rules
% 3.18/1.47  ----------------------
% 3.18/1.47  #Subsume      : 19
% 3.18/1.47  #Demod        : 90
% 3.18/1.47  #Tautology    : 25
% 3.18/1.47  #SimpNegUnit  : 4
% 3.18/1.47  #BackRed      : 31
% 3.18/1.47  
% 3.18/1.47  #Partial instantiations: 0
% 3.18/1.47  #Strategies tried      : 1
% 3.18/1.47  
% 3.18/1.47  Timing (in seconds)
% 3.18/1.47  ----------------------
% 3.18/1.48  Preprocessing        : 0.32
% 3.18/1.48  Parsing              : 0.16
% 3.18/1.48  CNF conversion       : 0.02
% 3.18/1.48  Main loop            : 0.38
% 3.18/1.48  Inferencing          : 0.14
% 3.18/1.48  Reduction            : 0.10
% 3.18/1.48  Demodulation         : 0.07
% 3.18/1.48  BG Simplification    : 0.02
% 3.18/1.48  Subsumption          : 0.09
% 3.18/1.48  Abstraction          : 0.02
% 3.18/1.48  MUC search           : 0.00
% 3.18/1.48  Cooper               : 0.00
% 3.18/1.48  Total                : 0.74
% 3.18/1.48  Index Insertion      : 0.00
% 3.18/1.48  Index Deletion       : 0.00
% 3.18/1.48  Index Matching       : 0.00
% 3.18/1.48  BG Taut test         : 0.00
%------------------------------------------------------------------------------
