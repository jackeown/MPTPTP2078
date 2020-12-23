%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:18:01 EST 2020

% Result     : Theorem 5.79s
% Output     : CNFRefutation 6.05s
% Verified   : 
% Statistics : Number of formulae       :  111 ( 246 expanded)
%              Number of leaves         :   44 ( 102 expanded)
%              Depth                    :   11
%              Number of atoms          :  182 ( 588 expanded)
%              Number of equality atoms :   38 ( 160 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k4_tarski > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_4 > #skF_3 > #skF_2

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

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

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

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

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

tff(f_146,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,B,C)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,C))) )
       => ~ ( r2_hidden(A,k2_relset_1(B,C,D))
            & ! [E] :
                ( m1_subset_1(E,B)
               => A != k1_funct_1(D,E) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t190_funct_2)).

tff(f_112,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_104,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_108,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_130,axiom,(
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

tff(f_81,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k9_relat_1(A,k1_relat_1(A)) = k2_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_relat_1)).

tff(f_77,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k9_relat_1(C,B))
      <=> ? [D] :
            ( r2_hidden(D,k1_relat_1(C))
            & r2_hidden(k4_tarski(D,A),C)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t143_relat_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

tff(f_100,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( r2_hidden(k4_tarski(A,B),C)
      <=> ( r2_hidden(A,k1_relat_1(C))
          & B = k1_funct_1(C,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_funct_1)).

tff(f_39,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_45,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_66,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_64,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_58,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A) )
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(B))
         => v5_relat_1(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc6_relat_1)).

tff(c_70,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_6'))) ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_292,plain,(
    ! [A_96,B_97,C_98] :
      ( k2_relset_1(A_96,B_97,C_98) = k2_relat_1(C_98)
      | ~ m1_subset_1(C_98,k1_zfmisc_1(k2_zfmisc_1(A_96,B_97))) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_317,plain,(
    k2_relset_1('#skF_5','#skF_6','#skF_7') = k2_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_70,c_292])).

tff(c_68,plain,(
    r2_hidden('#skF_4',k2_relset_1('#skF_5','#skF_6','#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_321,plain,(
    r2_hidden('#skF_4',k2_relat_1('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_317,c_68])).

tff(c_155,plain,(
    ! [C_67,A_68,B_69] :
      ( v1_relat_1(C_67)
      | ~ m1_subset_1(C_67,k1_zfmisc_1(k2_zfmisc_1(A_68,B_69))) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_168,plain,(
    v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_70,c_155])).

tff(c_72,plain,(
    v1_funct_2('#skF_7','#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_453,plain,(
    ! [A_113,B_114,C_115] :
      ( k1_relset_1(A_113,B_114,C_115) = k1_relat_1(C_115)
      | ~ m1_subset_1(C_115,k1_zfmisc_1(k2_zfmisc_1(A_113,B_114))) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_478,plain,(
    k1_relset_1('#skF_5','#skF_6','#skF_7') = k1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_70,c_453])).

tff(c_1516,plain,(
    ! [B_230,A_231,C_232] :
      ( k1_xboole_0 = B_230
      | k1_relset_1(A_231,B_230,C_232) = A_231
      | ~ v1_funct_2(C_232,A_231,B_230)
      | ~ m1_subset_1(C_232,k1_zfmisc_1(k2_zfmisc_1(A_231,B_230))) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_1535,plain,
    ( k1_xboole_0 = '#skF_6'
    | k1_relset_1('#skF_5','#skF_6','#skF_7') = '#skF_5'
    | ~ v1_funct_2('#skF_7','#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_70,c_1516])).

tff(c_1548,plain,
    ( k1_xboole_0 = '#skF_6'
    | k1_relat_1('#skF_7') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_478,c_1535])).

tff(c_1550,plain,(
    k1_relat_1('#skF_7') = '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_1548])).

tff(c_38,plain,(
    ! [A_28] :
      ( k9_relat_1(A_28,k1_relat_1(A_28)) = k2_relat_1(A_28)
      | ~ v1_relat_1(A_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_1570,plain,
    ( k9_relat_1('#skF_7','#skF_5') = k2_relat_1('#skF_7')
    | ~ v1_relat_1('#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_1550,c_38])).

tff(c_1584,plain,(
    k9_relat_1('#skF_7','#skF_5') = k2_relat_1('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_168,c_1570])).

tff(c_36,plain,(
    ! [A_22,B_23,C_24] :
      ( r2_hidden('#skF_3'(A_22,B_23,C_24),k1_relat_1(C_24))
      | ~ r2_hidden(A_22,k9_relat_1(C_24,B_23))
      | ~ v1_relat_1(C_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_1565,plain,(
    ! [A_22,B_23] :
      ( r2_hidden('#skF_3'(A_22,B_23,'#skF_7'),'#skF_5')
      | ~ r2_hidden(A_22,k9_relat_1('#skF_7',B_23))
      | ~ v1_relat_1('#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1550,c_36])).

tff(c_1842,plain,(
    ! [A_242,B_243] :
      ( r2_hidden('#skF_3'(A_242,B_243,'#skF_7'),'#skF_5')
      | ~ r2_hidden(A_242,k9_relat_1('#skF_7',B_243)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_168,c_1565])).

tff(c_20,plain,(
    ! [A_12,B_13] :
      ( m1_subset_1(A_12,B_13)
      | ~ r2_hidden(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_2025,plain,(
    ! [A_256,B_257] :
      ( m1_subset_1('#skF_3'(A_256,B_257,'#skF_7'),'#skF_5')
      | ~ r2_hidden(A_256,k9_relat_1('#skF_7',B_257)) ) ),
    inference(resolution,[status(thm)],[c_1842,c_20])).

tff(c_2070,plain,(
    ! [A_258] :
      ( m1_subset_1('#skF_3'(A_258,'#skF_5','#skF_7'),'#skF_5')
      | ~ r2_hidden(A_258,k2_relat_1('#skF_7')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1584,c_2025])).

tff(c_2106,plain,(
    m1_subset_1('#skF_3'('#skF_4','#skF_5','#skF_7'),'#skF_5') ),
    inference(resolution,[status(thm)],[c_321,c_2070])).

tff(c_66,plain,(
    ! [E_49] :
      ( k1_funct_1('#skF_7',E_49) != '#skF_4'
      | ~ m1_subset_1(E_49,'#skF_5') ) ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_2115,plain,(
    k1_funct_1('#skF_7','#skF_3'('#skF_4','#skF_5','#skF_7')) != '#skF_4' ),
    inference(resolution,[status(thm)],[c_2106,c_66])).

tff(c_74,plain,(
    v1_funct_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_1253,plain,(
    ! [A_211,B_212,C_213] :
      ( r2_hidden(k4_tarski('#skF_3'(A_211,B_212,C_213),A_211),C_213)
      | ~ r2_hidden(A_211,k9_relat_1(C_213,B_212))
      | ~ v1_relat_1(C_213) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_44,plain,(
    ! [C_35,A_33,B_34] :
      ( k1_funct_1(C_35,A_33) = B_34
      | ~ r2_hidden(k4_tarski(A_33,B_34),C_35)
      | ~ v1_funct_1(C_35)
      | ~ v1_relat_1(C_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_4472,plain,(
    ! [C_412,A_413,B_414] :
      ( k1_funct_1(C_412,'#skF_3'(A_413,B_414,C_412)) = A_413
      | ~ v1_funct_1(C_412)
      | ~ r2_hidden(A_413,k9_relat_1(C_412,B_414))
      | ~ v1_relat_1(C_412) ) ),
    inference(resolution,[status(thm)],[c_1253,c_44])).

tff(c_4485,plain,(
    ! [A_413] :
      ( k1_funct_1('#skF_7','#skF_3'(A_413,'#skF_5','#skF_7')) = A_413
      | ~ v1_funct_1('#skF_7')
      | ~ r2_hidden(A_413,k2_relat_1('#skF_7'))
      | ~ v1_relat_1('#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1584,c_4472])).

tff(c_4522,plain,(
    ! [A_415] :
      ( k1_funct_1('#skF_7','#skF_3'(A_415,'#skF_5','#skF_7')) = A_415
      | ~ r2_hidden(A_415,k2_relat_1('#skF_7')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_168,c_74,c_4485])).

tff(c_4553,plain,(
    k1_funct_1('#skF_7','#skF_3'('#skF_4','#skF_5','#skF_7')) = '#skF_4' ),
    inference(resolution,[status(thm)],[c_321,c_4522])).

tff(c_4576,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2115,c_4553])).

tff(c_4577,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_1548])).

tff(c_12,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_4598,plain,(
    v1_xboole_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4577,c_12])).

tff(c_16,plain,(
    ! [A_10] : k2_zfmisc_1(A_10,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_4596,plain,(
    ! [A_10] : k2_zfmisc_1(A_10,'#skF_6') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4577,c_4577,c_16])).

tff(c_28,plain,(
    ! [A_20,B_21] : v1_relat_1(k2_zfmisc_1(A_20,B_21)) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_1297,plain,(
    ! [C_214,A_215,B_216] :
      ( ~ v1_xboole_0(C_214)
      | ~ r2_hidden(A_215,k9_relat_1(C_214,B_216))
      | ~ v1_relat_1(C_214) ) ),
    inference(resolution,[status(thm)],[c_1253,c_2])).

tff(c_1336,plain,(
    ! [C_217,B_218] :
      ( ~ v1_xboole_0(C_217)
      | ~ v1_relat_1(C_217)
      | v1_xboole_0(k9_relat_1(C_217,B_218)) ) ),
    inference(resolution,[status(thm)],[c_4,c_1297])).

tff(c_1424,plain,(
    ! [A_225] :
      ( ~ v1_xboole_0(A_225)
      | ~ v1_relat_1(A_225)
      | v1_xboole_0(k2_relat_1(A_225))
      | ~ v1_relat_1(A_225) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_1336])).

tff(c_10,plain,(
    ! [A_5,B_6] :
      ( r2_hidden('#skF_2'(A_5,B_6),A_5)
      | r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_185,plain,(
    ! [A_72,B_73] :
      ( ~ r2_hidden('#skF_2'(A_72,B_73),B_73)
      | r1_tarski(A_72,B_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_190,plain,(
    ! [A_5] : r1_tarski(A_5,A_5) ),
    inference(resolution,[status(thm)],[c_10,c_185])).

tff(c_219,plain,(
    ! [B_82,A_83] :
      ( v5_relat_1(B_82,A_83)
      | ~ r1_tarski(k2_relat_1(B_82),A_83)
      | ~ v1_relat_1(B_82) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_232,plain,(
    ! [B_82] :
      ( v5_relat_1(B_82,k2_relat_1(B_82))
      | ~ v1_relat_1(B_82) ) ),
    inference(resolution,[status(thm)],[c_190,c_219])).

tff(c_412,plain,(
    ! [C_109,A_110,B_111] :
      ( v5_relat_1(C_109,A_110)
      | ~ m1_subset_1(C_109,k1_zfmisc_1(B_111))
      | ~ v5_relat_1(B_111,A_110)
      | ~ v1_relat_1(B_111) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_423,plain,(
    ! [A_110] :
      ( v5_relat_1('#skF_7',A_110)
      | ~ v5_relat_1(k2_zfmisc_1('#skF_5','#skF_6'),A_110)
      | ~ v1_relat_1(k2_zfmisc_1('#skF_5','#skF_6')) ) ),
    inference(resolution,[status(thm)],[c_70,c_412])).

tff(c_430,plain,(
    ! [A_112] :
      ( v5_relat_1('#skF_7',A_112)
      | ~ v5_relat_1(k2_zfmisc_1('#skF_5','#skF_6'),A_112) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_423])).

tff(c_434,plain,
    ( v5_relat_1('#skF_7',k2_relat_1(k2_zfmisc_1('#skF_5','#skF_6')))
    | ~ v1_relat_1(k2_zfmisc_1('#skF_5','#skF_6')) ),
    inference(resolution,[status(thm)],[c_232,c_430])).

tff(c_437,plain,(
    v5_relat_1('#skF_7',k2_relat_1(k2_zfmisc_1('#skF_5','#skF_6'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_434])).

tff(c_26,plain,(
    ! [B_19,A_18] :
      ( r1_tarski(k2_relat_1(B_19),A_18)
      | ~ v5_relat_1(B_19,A_18)
      | ~ v1_relat_1(B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_209,plain,(
    ! [C_79,B_80,A_81] :
      ( r2_hidden(C_79,B_80)
      | ~ r2_hidden(C_79,A_81)
      | ~ r1_tarski(A_81,B_80) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_218,plain,(
    ! [B_80] :
      ( r2_hidden('#skF_4',B_80)
      | ~ r1_tarski(k2_relset_1('#skF_5','#skF_6','#skF_7'),B_80) ) ),
    inference(resolution,[status(thm)],[c_68,c_209])).

tff(c_339,plain,(
    ! [B_100] :
      ( r2_hidden('#skF_4',B_100)
      | ~ r1_tarski(k2_relat_1('#skF_7'),B_100) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_317,c_218])).

tff(c_343,plain,(
    ! [A_18] :
      ( r2_hidden('#skF_4',A_18)
      | ~ v5_relat_1('#skF_7',A_18)
      | ~ v1_relat_1('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_26,c_339])).

tff(c_354,plain,(
    ! [A_18] :
      ( r2_hidden('#skF_4',A_18)
      | ~ v5_relat_1('#skF_7',A_18) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_168,c_343])).

tff(c_441,plain,(
    r2_hidden('#skF_4',k2_relat_1(k2_zfmisc_1('#skF_5','#skF_6'))) ),
    inference(resolution,[status(thm)],[c_437,c_354])).

tff(c_452,plain,(
    ~ v1_xboole_0(k2_relat_1(k2_zfmisc_1('#skF_5','#skF_6'))) ),
    inference(resolution,[status(thm)],[c_441,c_2])).

tff(c_1427,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1('#skF_5','#skF_6'))
    | ~ v1_relat_1(k2_zfmisc_1('#skF_5','#skF_6')) ),
    inference(resolution,[status(thm)],[c_1424,c_452])).

tff(c_1435,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_5','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_1427])).

tff(c_4627,plain,(
    ~ v1_xboole_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4596,c_1435])).

tff(c_4640,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4598,c_4627])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:09:09 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.79/2.11  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.93/2.12  
% 5.93/2.12  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.93/2.12  %$ v1_funct_2 > v5_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k4_tarski > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_4 > #skF_3 > #skF_2
% 5.93/2.12  
% 5.93/2.12  %Foreground sorts:
% 5.93/2.12  
% 5.93/2.12  
% 5.93/2.12  %Background operators:
% 5.93/2.12  
% 5.93/2.12  
% 5.93/2.12  %Foreground operators:
% 5.93/2.12  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 5.93/2.12  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 5.93/2.12  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.93/2.12  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.93/2.12  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 5.93/2.12  tff('#skF_1', type, '#skF_1': $i > $i).
% 5.93/2.12  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.93/2.12  tff('#skF_7', type, '#skF_7': $i).
% 5.93/2.12  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.93/2.12  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 5.93/2.12  tff('#skF_5', type, '#skF_5': $i).
% 5.93/2.12  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 5.93/2.12  tff('#skF_6', type, '#skF_6': $i).
% 5.93/2.12  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 5.93/2.12  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 5.93/2.12  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 5.93/2.12  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.93/2.12  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 5.93/2.12  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.93/2.12  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.93/2.12  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 5.93/2.12  tff('#skF_4', type, '#skF_4': $i).
% 5.93/2.12  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 5.93/2.12  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.93/2.12  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 5.93/2.12  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 5.93/2.12  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 5.93/2.12  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.93/2.12  
% 5.93/2.14  tff(f_146, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, B, C)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => ~(r2_hidden(A, k2_relset_1(B, C, D)) & (![E]: (m1_subset_1(E, B) => ~(A = k1_funct_1(D, E))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t190_funct_2)).
% 5.93/2.14  tff(f_112, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 5.93/2.14  tff(f_104, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 5.93/2.14  tff(f_108, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 5.93/2.14  tff(f_130, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 5.93/2.14  tff(f_81, axiom, (![A]: (v1_relat_1(A) => (k9_relat_1(A, k1_relat_1(A)) = k2_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t146_relat_1)).
% 5.93/2.14  tff(f_77, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k9_relat_1(C, B)) <=> (?[D]: ((r2_hidden(D, k1_relat_1(C)) & r2_hidden(k4_tarski(D, A), C)) & r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t143_relat_1)).
% 5.93/2.14  tff(f_49, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_subset)).
% 5.93/2.14  tff(f_100, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(k4_tarski(A, B), C) <=> (r2_hidden(A, k1_relat_1(C)) & (B = k1_funct_1(C, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_funct_1)).
% 5.93/2.14  tff(f_39, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 5.93/2.14  tff(f_45, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 5.93/2.14  tff(f_66, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 5.93/2.14  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 5.93/2.14  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 5.93/2.14  tff(f_64, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 5.93/2.14  tff(f_58, axiom, (![A, B]: ((v1_relat_1(B) & v5_relat_1(B, A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(B)) => v5_relat_1(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc6_relat_1)).
% 5.93/2.14  tff(c_70, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_6')))), inference(cnfTransformation, [status(thm)], [f_146])).
% 5.93/2.14  tff(c_292, plain, (![A_96, B_97, C_98]: (k2_relset_1(A_96, B_97, C_98)=k2_relat_1(C_98) | ~m1_subset_1(C_98, k1_zfmisc_1(k2_zfmisc_1(A_96, B_97))))), inference(cnfTransformation, [status(thm)], [f_112])).
% 5.93/2.14  tff(c_317, plain, (k2_relset_1('#skF_5', '#skF_6', '#skF_7')=k2_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_70, c_292])).
% 5.93/2.14  tff(c_68, plain, (r2_hidden('#skF_4', k2_relset_1('#skF_5', '#skF_6', '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_146])).
% 5.93/2.14  tff(c_321, plain, (r2_hidden('#skF_4', k2_relat_1('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_317, c_68])).
% 5.93/2.14  tff(c_155, plain, (![C_67, A_68, B_69]: (v1_relat_1(C_67) | ~m1_subset_1(C_67, k1_zfmisc_1(k2_zfmisc_1(A_68, B_69))))), inference(cnfTransformation, [status(thm)], [f_104])).
% 5.93/2.14  tff(c_168, plain, (v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_70, c_155])).
% 5.93/2.14  tff(c_72, plain, (v1_funct_2('#skF_7', '#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_146])).
% 5.93/2.14  tff(c_453, plain, (![A_113, B_114, C_115]: (k1_relset_1(A_113, B_114, C_115)=k1_relat_1(C_115) | ~m1_subset_1(C_115, k1_zfmisc_1(k2_zfmisc_1(A_113, B_114))))), inference(cnfTransformation, [status(thm)], [f_108])).
% 5.93/2.14  tff(c_478, plain, (k1_relset_1('#skF_5', '#skF_6', '#skF_7')=k1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_70, c_453])).
% 5.93/2.14  tff(c_1516, plain, (![B_230, A_231, C_232]: (k1_xboole_0=B_230 | k1_relset_1(A_231, B_230, C_232)=A_231 | ~v1_funct_2(C_232, A_231, B_230) | ~m1_subset_1(C_232, k1_zfmisc_1(k2_zfmisc_1(A_231, B_230))))), inference(cnfTransformation, [status(thm)], [f_130])).
% 5.93/2.14  tff(c_1535, plain, (k1_xboole_0='#skF_6' | k1_relset_1('#skF_5', '#skF_6', '#skF_7')='#skF_5' | ~v1_funct_2('#skF_7', '#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_70, c_1516])).
% 5.93/2.14  tff(c_1548, plain, (k1_xboole_0='#skF_6' | k1_relat_1('#skF_7')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_72, c_478, c_1535])).
% 5.93/2.14  tff(c_1550, plain, (k1_relat_1('#skF_7')='#skF_5'), inference(splitLeft, [status(thm)], [c_1548])).
% 5.93/2.14  tff(c_38, plain, (![A_28]: (k9_relat_1(A_28, k1_relat_1(A_28))=k2_relat_1(A_28) | ~v1_relat_1(A_28))), inference(cnfTransformation, [status(thm)], [f_81])).
% 5.93/2.14  tff(c_1570, plain, (k9_relat_1('#skF_7', '#skF_5')=k2_relat_1('#skF_7') | ~v1_relat_1('#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_1550, c_38])).
% 5.93/2.14  tff(c_1584, plain, (k9_relat_1('#skF_7', '#skF_5')=k2_relat_1('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_168, c_1570])).
% 5.93/2.14  tff(c_36, plain, (![A_22, B_23, C_24]: (r2_hidden('#skF_3'(A_22, B_23, C_24), k1_relat_1(C_24)) | ~r2_hidden(A_22, k9_relat_1(C_24, B_23)) | ~v1_relat_1(C_24))), inference(cnfTransformation, [status(thm)], [f_77])).
% 5.93/2.14  tff(c_1565, plain, (![A_22, B_23]: (r2_hidden('#skF_3'(A_22, B_23, '#skF_7'), '#skF_5') | ~r2_hidden(A_22, k9_relat_1('#skF_7', B_23)) | ~v1_relat_1('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_1550, c_36])).
% 5.93/2.14  tff(c_1842, plain, (![A_242, B_243]: (r2_hidden('#skF_3'(A_242, B_243, '#skF_7'), '#skF_5') | ~r2_hidden(A_242, k9_relat_1('#skF_7', B_243)))), inference(demodulation, [status(thm), theory('equality')], [c_168, c_1565])).
% 5.93/2.14  tff(c_20, plain, (![A_12, B_13]: (m1_subset_1(A_12, B_13) | ~r2_hidden(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_49])).
% 5.93/2.14  tff(c_2025, plain, (![A_256, B_257]: (m1_subset_1('#skF_3'(A_256, B_257, '#skF_7'), '#skF_5') | ~r2_hidden(A_256, k9_relat_1('#skF_7', B_257)))), inference(resolution, [status(thm)], [c_1842, c_20])).
% 5.93/2.14  tff(c_2070, plain, (![A_258]: (m1_subset_1('#skF_3'(A_258, '#skF_5', '#skF_7'), '#skF_5') | ~r2_hidden(A_258, k2_relat_1('#skF_7')))), inference(superposition, [status(thm), theory('equality')], [c_1584, c_2025])).
% 5.93/2.14  tff(c_2106, plain, (m1_subset_1('#skF_3'('#skF_4', '#skF_5', '#skF_7'), '#skF_5')), inference(resolution, [status(thm)], [c_321, c_2070])).
% 5.93/2.14  tff(c_66, plain, (![E_49]: (k1_funct_1('#skF_7', E_49)!='#skF_4' | ~m1_subset_1(E_49, '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_146])).
% 5.93/2.14  tff(c_2115, plain, (k1_funct_1('#skF_7', '#skF_3'('#skF_4', '#skF_5', '#skF_7'))!='#skF_4'), inference(resolution, [status(thm)], [c_2106, c_66])).
% 5.93/2.14  tff(c_74, plain, (v1_funct_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_146])).
% 5.93/2.14  tff(c_1253, plain, (![A_211, B_212, C_213]: (r2_hidden(k4_tarski('#skF_3'(A_211, B_212, C_213), A_211), C_213) | ~r2_hidden(A_211, k9_relat_1(C_213, B_212)) | ~v1_relat_1(C_213))), inference(cnfTransformation, [status(thm)], [f_77])).
% 5.93/2.14  tff(c_44, plain, (![C_35, A_33, B_34]: (k1_funct_1(C_35, A_33)=B_34 | ~r2_hidden(k4_tarski(A_33, B_34), C_35) | ~v1_funct_1(C_35) | ~v1_relat_1(C_35))), inference(cnfTransformation, [status(thm)], [f_100])).
% 5.93/2.14  tff(c_4472, plain, (![C_412, A_413, B_414]: (k1_funct_1(C_412, '#skF_3'(A_413, B_414, C_412))=A_413 | ~v1_funct_1(C_412) | ~r2_hidden(A_413, k9_relat_1(C_412, B_414)) | ~v1_relat_1(C_412))), inference(resolution, [status(thm)], [c_1253, c_44])).
% 5.93/2.14  tff(c_4485, plain, (![A_413]: (k1_funct_1('#skF_7', '#skF_3'(A_413, '#skF_5', '#skF_7'))=A_413 | ~v1_funct_1('#skF_7') | ~r2_hidden(A_413, k2_relat_1('#skF_7')) | ~v1_relat_1('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_1584, c_4472])).
% 5.93/2.14  tff(c_4522, plain, (![A_415]: (k1_funct_1('#skF_7', '#skF_3'(A_415, '#skF_5', '#skF_7'))=A_415 | ~r2_hidden(A_415, k2_relat_1('#skF_7')))), inference(demodulation, [status(thm), theory('equality')], [c_168, c_74, c_4485])).
% 5.93/2.14  tff(c_4553, plain, (k1_funct_1('#skF_7', '#skF_3'('#skF_4', '#skF_5', '#skF_7'))='#skF_4'), inference(resolution, [status(thm)], [c_321, c_4522])).
% 5.93/2.14  tff(c_4576, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2115, c_4553])).
% 5.93/2.14  tff(c_4577, plain, (k1_xboole_0='#skF_6'), inference(splitRight, [status(thm)], [c_1548])).
% 5.93/2.14  tff(c_12, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 5.93/2.14  tff(c_4598, plain, (v1_xboole_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_4577, c_12])).
% 5.93/2.14  tff(c_16, plain, (![A_10]: (k2_zfmisc_1(A_10, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_45])).
% 5.93/2.14  tff(c_4596, plain, (![A_10]: (k2_zfmisc_1(A_10, '#skF_6')='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_4577, c_4577, c_16])).
% 5.93/2.14  tff(c_28, plain, (![A_20, B_21]: (v1_relat_1(k2_zfmisc_1(A_20, B_21)))), inference(cnfTransformation, [status(thm)], [f_66])).
% 5.93/2.14  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.93/2.14  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.93/2.14  tff(c_1297, plain, (![C_214, A_215, B_216]: (~v1_xboole_0(C_214) | ~r2_hidden(A_215, k9_relat_1(C_214, B_216)) | ~v1_relat_1(C_214))), inference(resolution, [status(thm)], [c_1253, c_2])).
% 6.05/2.14  tff(c_1336, plain, (![C_217, B_218]: (~v1_xboole_0(C_217) | ~v1_relat_1(C_217) | v1_xboole_0(k9_relat_1(C_217, B_218)))), inference(resolution, [status(thm)], [c_4, c_1297])).
% 6.05/2.14  tff(c_1424, plain, (![A_225]: (~v1_xboole_0(A_225) | ~v1_relat_1(A_225) | v1_xboole_0(k2_relat_1(A_225)) | ~v1_relat_1(A_225))), inference(superposition, [status(thm), theory('equality')], [c_38, c_1336])).
% 6.05/2.14  tff(c_10, plain, (![A_5, B_6]: (r2_hidden('#skF_2'(A_5, B_6), A_5) | r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_38])).
% 6.05/2.14  tff(c_185, plain, (![A_72, B_73]: (~r2_hidden('#skF_2'(A_72, B_73), B_73) | r1_tarski(A_72, B_73))), inference(cnfTransformation, [status(thm)], [f_38])).
% 6.05/2.14  tff(c_190, plain, (![A_5]: (r1_tarski(A_5, A_5))), inference(resolution, [status(thm)], [c_10, c_185])).
% 6.05/2.14  tff(c_219, plain, (![B_82, A_83]: (v5_relat_1(B_82, A_83) | ~r1_tarski(k2_relat_1(B_82), A_83) | ~v1_relat_1(B_82))), inference(cnfTransformation, [status(thm)], [f_64])).
% 6.05/2.14  tff(c_232, plain, (![B_82]: (v5_relat_1(B_82, k2_relat_1(B_82)) | ~v1_relat_1(B_82))), inference(resolution, [status(thm)], [c_190, c_219])).
% 6.05/2.14  tff(c_412, plain, (![C_109, A_110, B_111]: (v5_relat_1(C_109, A_110) | ~m1_subset_1(C_109, k1_zfmisc_1(B_111)) | ~v5_relat_1(B_111, A_110) | ~v1_relat_1(B_111))), inference(cnfTransformation, [status(thm)], [f_58])).
% 6.05/2.14  tff(c_423, plain, (![A_110]: (v5_relat_1('#skF_7', A_110) | ~v5_relat_1(k2_zfmisc_1('#skF_5', '#skF_6'), A_110) | ~v1_relat_1(k2_zfmisc_1('#skF_5', '#skF_6')))), inference(resolution, [status(thm)], [c_70, c_412])).
% 6.05/2.14  tff(c_430, plain, (![A_112]: (v5_relat_1('#skF_7', A_112) | ~v5_relat_1(k2_zfmisc_1('#skF_5', '#skF_6'), A_112))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_423])).
% 6.05/2.14  tff(c_434, plain, (v5_relat_1('#skF_7', k2_relat_1(k2_zfmisc_1('#skF_5', '#skF_6'))) | ~v1_relat_1(k2_zfmisc_1('#skF_5', '#skF_6'))), inference(resolution, [status(thm)], [c_232, c_430])).
% 6.05/2.14  tff(c_437, plain, (v5_relat_1('#skF_7', k2_relat_1(k2_zfmisc_1('#skF_5', '#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_434])).
% 6.05/2.14  tff(c_26, plain, (![B_19, A_18]: (r1_tarski(k2_relat_1(B_19), A_18) | ~v5_relat_1(B_19, A_18) | ~v1_relat_1(B_19))), inference(cnfTransformation, [status(thm)], [f_64])).
% 6.05/2.14  tff(c_209, plain, (![C_79, B_80, A_81]: (r2_hidden(C_79, B_80) | ~r2_hidden(C_79, A_81) | ~r1_tarski(A_81, B_80))), inference(cnfTransformation, [status(thm)], [f_38])).
% 6.05/2.14  tff(c_218, plain, (![B_80]: (r2_hidden('#skF_4', B_80) | ~r1_tarski(k2_relset_1('#skF_5', '#skF_6', '#skF_7'), B_80))), inference(resolution, [status(thm)], [c_68, c_209])).
% 6.05/2.14  tff(c_339, plain, (![B_100]: (r2_hidden('#skF_4', B_100) | ~r1_tarski(k2_relat_1('#skF_7'), B_100))), inference(demodulation, [status(thm), theory('equality')], [c_317, c_218])).
% 6.05/2.14  tff(c_343, plain, (![A_18]: (r2_hidden('#skF_4', A_18) | ~v5_relat_1('#skF_7', A_18) | ~v1_relat_1('#skF_7'))), inference(resolution, [status(thm)], [c_26, c_339])).
% 6.05/2.14  tff(c_354, plain, (![A_18]: (r2_hidden('#skF_4', A_18) | ~v5_relat_1('#skF_7', A_18))), inference(demodulation, [status(thm), theory('equality')], [c_168, c_343])).
% 6.05/2.14  tff(c_441, plain, (r2_hidden('#skF_4', k2_relat_1(k2_zfmisc_1('#skF_5', '#skF_6')))), inference(resolution, [status(thm)], [c_437, c_354])).
% 6.05/2.14  tff(c_452, plain, (~v1_xboole_0(k2_relat_1(k2_zfmisc_1('#skF_5', '#skF_6')))), inference(resolution, [status(thm)], [c_441, c_2])).
% 6.05/2.14  tff(c_1427, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_5', '#skF_6')) | ~v1_relat_1(k2_zfmisc_1('#skF_5', '#skF_6'))), inference(resolution, [status(thm)], [c_1424, c_452])).
% 6.05/2.14  tff(c_1435, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_5', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_1427])).
% 6.05/2.14  tff(c_4627, plain, (~v1_xboole_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_4596, c_1435])).
% 6.05/2.14  tff(c_4640, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4598, c_4627])).
% 6.05/2.14  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.05/2.14  
% 6.05/2.14  Inference rules
% 6.05/2.14  ----------------------
% 6.05/2.14  #Ref     : 0
% 6.05/2.14  #Sup     : 1002
% 6.05/2.14  #Fact    : 0
% 6.05/2.14  #Define  : 0
% 6.05/2.14  #Split   : 8
% 6.05/2.14  #Chain   : 0
% 6.05/2.14  #Close   : 0
% 6.05/2.14  
% 6.05/2.14  Ordering : KBO
% 6.05/2.14  
% 6.05/2.14  Simplification rules
% 6.05/2.14  ----------------------
% 6.05/2.14  #Subsume      : 519
% 6.05/2.14  #Demod        : 206
% 6.05/2.14  #Tautology    : 70
% 6.05/2.14  #SimpNegUnit  : 45
% 6.05/2.14  #BackRed      : 56
% 6.05/2.14  
% 6.05/2.14  #Partial instantiations: 0
% 6.05/2.14  #Strategies tried      : 1
% 6.05/2.14  
% 6.05/2.14  Timing (in seconds)
% 6.05/2.14  ----------------------
% 6.05/2.15  Preprocessing        : 0.35
% 6.05/2.15  Parsing              : 0.18
% 6.05/2.15  CNF conversion       : 0.03
% 6.05/2.15  Main loop            : 1.03
% 6.05/2.15  Inferencing          : 0.34
% 6.05/2.15  Reduction            : 0.30
% 6.05/2.15  Demodulation         : 0.19
% 6.05/2.15  BG Simplification    : 0.04
% 6.05/2.15  Subsumption          : 0.28
% 6.05/2.15  Abstraction          : 0.05
% 6.05/2.15  MUC search           : 0.00
% 6.05/2.15  Cooper               : 0.00
% 6.05/2.15  Total                : 1.42
% 6.05/2.15  Index Insertion      : 0.00
% 6.05/2.15  Index Deletion       : 0.00
% 6.05/2.15  Index Matching       : 0.00
% 6.05/2.15  BG Taut test         : 0.00
%------------------------------------------------------------------------------
