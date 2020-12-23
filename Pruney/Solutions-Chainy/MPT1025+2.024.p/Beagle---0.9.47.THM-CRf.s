%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:16:33 EST 2020

% Result     : Theorem 4.71s
% Output     : CNFRefutation 5.04s
% Verified   : 
% Statistics : Number of formulae       :   91 ( 148 expanded)
%              Number of leaves         :   42 (  71 expanded)
%              Depth                    :   12
%              Number of atoms          :  144 ( 356 expanded)
%              Number of equality atoms :   31 (  70 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k1_relset_1 > k9_relat_1 > k4_tarski > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_11 > #skF_1 > #skF_4 > #skF_7 > #skF_10 > #skF_5 > #skF_2 > #skF_6 > #skF_9 > #skF_8 > #skF_3

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

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

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

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i * $i ) > $i )).

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

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_139,negated_conjecture,(
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

tff(f_87,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_94,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(B,A)))
         => v1_xboole_0(C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc4_relset_1)).

tff(f_78,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d12_funct_1)).

tff(f_98,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_120,axiom,(
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

tff(f_50,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

tff(f_102,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_33,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_83,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

tff(f_61,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k9_relat_1(C,B))
      <=> ? [D] :
            ( r2_hidden(D,k1_relat_1(C))
            & r2_hidden(k4_tarski(D,A),C)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t143_relat_1)).

tff(c_76,plain,(
    m1_subset_1('#skF_10',k1_zfmisc_1(k2_zfmisc_1('#skF_7','#skF_8'))) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_131,plain,(
    ! [C_96,A_97,B_98] :
      ( v1_relat_1(C_96)
      | ~ m1_subset_1(C_96,k1_zfmisc_1(k2_zfmisc_1(A_97,B_98))) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_145,plain,(
    v1_relat_1('#skF_10') ),
    inference(resolution,[status(thm)],[c_76,c_131])).

tff(c_182,plain,(
    ! [C_104,B_105,A_106] :
      ( v1_xboole_0(C_104)
      | ~ m1_subset_1(C_104,k1_zfmisc_1(k2_zfmisc_1(B_105,A_106)))
      | ~ v1_xboole_0(A_106) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_196,plain,
    ( v1_xboole_0('#skF_10')
    | ~ v1_xboole_0('#skF_8') ),
    inference(resolution,[status(thm)],[c_76,c_182])).

tff(c_197,plain,(
    ~ v1_xboole_0('#skF_8') ),
    inference(splitLeft,[status(thm)],[c_196])).

tff(c_80,plain,(
    v1_funct_1('#skF_10') ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_28,plain,(
    ! [A_16,B_39,D_54] :
      ( k1_funct_1(A_16,'#skF_6'(A_16,B_39,k9_relat_1(A_16,B_39),D_54)) = D_54
      | ~ r2_hidden(D_54,k9_relat_1(A_16,B_39))
      | ~ v1_funct_1(A_16)
      | ~ v1_relat_1(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_78,plain,(
    v1_funct_2('#skF_10','#skF_7','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_207,plain,(
    ! [A_111,B_112,C_113] :
      ( k1_relset_1(A_111,B_112,C_113) = k1_relat_1(C_113)
      | ~ m1_subset_1(C_113,k1_zfmisc_1(k2_zfmisc_1(A_111,B_112))) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_223,plain,(
    k1_relset_1('#skF_7','#skF_8','#skF_10') = k1_relat_1('#skF_10') ),
    inference(resolution,[status(thm)],[c_76,c_207])).

tff(c_1090,plain,(
    ! [B_260,A_261,C_262] :
      ( k1_xboole_0 = B_260
      | k1_relset_1(A_261,B_260,C_262) = A_261
      | ~ v1_funct_2(C_262,A_261,B_260)
      | ~ m1_subset_1(C_262,k1_zfmisc_1(k2_zfmisc_1(A_261,B_260))) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_1101,plain,
    ( k1_xboole_0 = '#skF_8'
    | k1_relset_1('#skF_7','#skF_8','#skF_10') = '#skF_7'
    | ~ v1_funct_2('#skF_10','#skF_7','#skF_8') ),
    inference(resolution,[status(thm)],[c_76,c_1090])).

tff(c_1108,plain,
    ( k1_xboole_0 = '#skF_8'
    | k1_relat_1('#skF_10') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_223,c_1101])).

tff(c_1109,plain,(
    k1_relat_1('#skF_10') = '#skF_7' ),
    inference(splitLeft,[status(thm)],[c_1108])).

tff(c_1762,plain,(
    ! [A_326,B_327,D_328] :
      ( r2_hidden('#skF_6'(A_326,B_327,k9_relat_1(A_326,B_327),D_328),k1_relat_1(A_326))
      | ~ r2_hidden(D_328,k9_relat_1(A_326,B_327))
      | ~ v1_funct_1(A_326)
      | ~ v1_relat_1(A_326) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_1779,plain,(
    ! [B_327,D_328] :
      ( r2_hidden('#skF_6'('#skF_10',B_327,k9_relat_1('#skF_10',B_327),D_328),'#skF_7')
      | ~ r2_hidden(D_328,k9_relat_1('#skF_10',B_327))
      | ~ v1_funct_1('#skF_10')
      | ~ v1_relat_1('#skF_10') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1109,c_1762])).

tff(c_1787,plain,(
    ! [B_329,D_330] :
      ( r2_hidden('#skF_6'('#skF_10',B_329,k9_relat_1('#skF_10',B_329),D_330),'#skF_7')
      | ~ r2_hidden(D_330,k9_relat_1('#skF_10',B_329)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_145,c_80,c_1779])).

tff(c_16,plain,(
    ! [A_8,B_9] :
      ( m1_subset_1(A_8,B_9)
      | ~ r2_hidden(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_1809,plain,(
    ! [B_336,D_337] :
      ( m1_subset_1('#skF_6'('#skF_10',B_336,k9_relat_1('#skF_10',B_336),D_337),'#skF_7')
      | ~ r2_hidden(D_337,k9_relat_1('#skF_10',B_336)) ) ),
    inference(resolution,[status(thm)],[c_1787,c_16])).

tff(c_1548,plain,(
    ! [A_308,B_309,D_310] :
      ( r2_hidden('#skF_6'(A_308,B_309,k9_relat_1(A_308,B_309),D_310),B_309)
      | ~ r2_hidden(D_310,k9_relat_1(A_308,B_309))
      | ~ v1_funct_1(A_308)
      | ~ v1_relat_1(A_308) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_72,plain,(
    ! [F_81] :
      ( k1_funct_1('#skF_10',F_81) != '#skF_11'
      | ~ r2_hidden(F_81,'#skF_9')
      | ~ m1_subset_1(F_81,'#skF_7') ) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_1639,plain,(
    ! [A_308,D_310] :
      ( k1_funct_1('#skF_10','#skF_6'(A_308,'#skF_9',k9_relat_1(A_308,'#skF_9'),D_310)) != '#skF_11'
      | ~ m1_subset_1('#skF_6'(A_308,'#skF_9',k9_relat_1(A_308,'#skF_9'),D_310),'#skF_7')
      | ~ r2_hidden(D_310,k9_relat_1(A_308,'#skF_9'))
      | ~ v1_funct_1(A_308)
      | ~ v1_relat_1(A_308) ) ),
    inference(resolution,[status(thm)],[c_1548,c_72])).

tff(c_1813,plain,(
    ! [D_337] :
      ( k1_funct_1('#skF_10','#skF_6'('#skF_10','#skF_9',k9_relat_1('#skF_10','#skF_9'),D_337)) != '#skF_11'
      | ~ v1_funct_1('#skF_10')
      | ~ v1_relat_1('#skF_10')
      | ~ r2_hidden(D_337,k9_relat_1('#skF_10','#skF_9')) ) ),
    inference(resolution,[status(thm)],[c_1809,c_1639])).

tff(c_2183,plain,(
    ! [D_380] :
      ( k1_funct_1('#skF_10','#skF_6'('#skF_10','#skF_9',k9_relat_1('#skF_10','#skF_9'),D_380)) != '#skF_11'
      | ~ r2_hidden(D_380,k9_relat_1('#skF_10','#skF_9')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_145,c_80,c_1813])).

tff(c_2187,plain,(
    ! [D_54] :
      ( D_54 != '#skF_11'
      | ~ r2_hidden(D_54,k9_relat_1('#skF_10','#skF_9'))
      | ~ r2_hidden(D_54,k9_relat_1('#skF_10','#skF_9'))
      | ~ v1_funct_1('#skF_10')
      | ~ v1_relat_1('#skF_10') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_2183])).

tff(c_2190,plain,(
    ~ r2_hidden('#skF_11',k9_relat_1('#skF_10','#skF_9')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_145,c_80,c_2187])).

tff(c_425,plain,(
    ! [A_161,B_162,C_163,D_164] :
      ( k7_relset_1(A_161,B_162,C_163,D_164) = k9_relat_1(C_163,D_164)
      | ~ m1_subset_1(C_163,k1_zfmisc_1(k2_zfmisc_1(A_161,B_162))) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_438,plain,(
    ! [D_164] : k7_relset_1('#skF_7','#skF_8','#skF_10',D_164) = k9_relat_1('#skF_10',D_164) ),
    inference(resolution,[status(thm)],[c_76,c_425])).

tff(c_74,plain,(
    r2_hidden('#skF_11',k7_relset_1('#skF_7','#skF_8','#skF_10','#skF_9')) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_442,plain,(
    r2_hidden('#skF_11',k9_relat_1('#skF_10','#skF_9')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_438,c_74])).

tff(c_2192,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2190,c_442])).

tff(c_2193,plain,(
    k1_xboole_0 = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_1108])).

tff(c_6,plain,(
    ! [A_5] : r1_tarski(k1_xboole_0,A_5) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_93,plain,(
    ! [B_88,A_89] :
      ( ~ r1_tarski(B_88,A_89)
      | ~ r2_hidden(A_89,B_88) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_111,plain,(
    ! [A_91] :
      ( ~ r1_tarski(A_91,'#skF_1'(A_91))
      | v1_xboole_0(A_91) ) ),
    inference(resolution,[status(thm)],[c_4,c_93])).

tff(c_116,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_6,c_111])).

tff(c_2206,plain,(
    v1_xboole_0('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2193,c_116])).

tff(c_2209,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_197,c_2206])).

tff(c_2210,plain,(
    v1_xboole_0('#skF_10') ),
    inference(splitRight,[status(thm)],[c_196])).

tff(c_2359,plain,(
    ! [A_411,B_412,C_413,D_414] :
      ( k7_relset_1(A_411,B_412,C_413,D_414) = k9_relat_1(C_413,D_414)
      | ~ m1_subset_1(C_413,k1_zfmisc_1(k2_zfmisc_1(A_411,B_412))) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_2372,plain,(
    ! [D_414] : k7_relset_1('#skF_7','#skF_8','#skF_10',D_414) = k9_relat_1('#skF_10',D_414) ),
    inference(resolution,[status(thm)],[c_76,c_2359])).

tff(c_2376,plain,(
    r2_hidden('#skF_11',k9_relat_1('#skF_10','#skF_9')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2372,c_74])).

tff(c_2590,plain,(
    ! [A_460,B_461,C_462] :
      ( r2_hidden(k4_tarski('#skF_2'(A_460,B_461,C_462),A_460),C_462)
      | ~ r2_hidden(A_460,k9_relat_1(C_462,B_461))
      | ~ v1_relat_1(C_462) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_2647,plain,(
    ! [C_463,A_464,B_465] :
      ( ~ v1_xboole_0(C_463)
      | ~ r2_hidden(A_464,k9_relat_1(C_463,B_465))
      | ~ v1_relat_1(C_463) ) ),
    inference(resolution,[status(thm)],[c_2590,c_2])).

tff(c_2654,plain,
    ( ~ v1_xboole_0('#skF_10')
    | ~ v1_relat_1('#skF_10') ),
    inference(resolution,[status(thm)],[c_2376,c_2647])).

tff(c_2671,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_145,c_2210,c_2654])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:21:34 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.71/1.91  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.71/1.92  
% 4.71/1.92  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.71/1.92  %$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k1_relset_1 > k9_relat_1 > k4_tarski > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_11 > #skF_1 > #skF_4 > #skF_7 > #skF_10 > #skF_5 > #skF_2 > #skF_6 > #skF_9 > #skF_8 > #skF_3
% 4.71/1.92  
% 4.71/1.92  %Foreground sorts:
% 4.71/1.92  
% 4.71/1.92  
% 4.71/1.92  %Background operators:
% 4.71/1.92  
% 4.71/1.92  
% 4.71/1.92  %Foreground operators:
% 4.71/1.92  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.71/1.92  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.71/1.92  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.71/1.92  tff('#skF_11', type, '#skF_11': $i).
% 4.71/1.92  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 4.71/1.92  tff('#skF_1', type, '#skF_1': $i > $i).
% 4.71/1.92  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.71/1.92  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 4.71/1.92  tff('#skF_7', type, '#skF_7': $i).
% 4.71/1.92  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.71/1.92  tff('#skF_10', type, '#skF_10': $i).
% 4.71/1.92  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 4.71/1.92  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.71/1.92  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 4.71/1.92  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 4.71/1.92  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 4.71/1.92  tff('#skF_6', type, '#skF_6': ($i * $i * $i * $i) > $i).
% 4.71/1.92  tff('#skF_9', type, '#skF_9': $i).
% 4.71/1.92  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 4.71/1.92  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.71/1.92  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 4.71/1.92  tff('#skF_8', type, '#skF_8': $i).
% 4.71/1.92  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.71/1.92  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.71/1.92  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.71/1.92  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 4.71/1.92  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.71/1.92  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.71/1.92  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.71/1.92  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.71/1.92  
% 5.04/1.94  tff(f_139, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: ~(r2_hidden(E, k7_relset_1(A, B, D, C)) & (![F]: (m1_subset_1(F, A) => ~(r2_hidden(F, C) & (E = k1_funct_1(D, F))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t116_funct_2)).
% 5.04/1.94  tff(f_87, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 5.04/1.94  tff(f_94, axiom, (![A, B]: (v1_xboole_0(A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => v1_xboole_0(C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc4_relset_1)).
% 5.04/1.94  tff(f_78, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B, C]: ((C = k9_relat_1(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (?[E]: ((r2_hidden(E, k1_relat_1(A)) & r2_hidden(E, B)) & (D = k1_funct_1(A, E)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d12_funct_1)).
% 5.04/1.94  tff(f_98, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 5.04/1.94  tff(f_120, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 5.04/1.94  tff(f_50, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_subset)).
% 5.04/1.94  tff(f_102, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 5.04/1.94  tff(f_33, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 5.04/1.94  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 5.04/1.94  tff(f_83, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 5.04/1.94  tff(f_61, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k9_relat_1(C, B)) <=> (?[D]: ((r2_hidden(D, k1_relat_1(C)) & r2_hidden(k4_tarski(D, A), C)) & r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t143_relat_1)).
% 5.04/1.94  tff(c_76, plain, (m1_subset_1('#skF_10', k1_zfmisc_1(k2_zfmisc_1('#skF_7', '#skF_8')))), inference(cnfTransformation, [status(thm)], [f_139])).
% 5.04/1.94  tff(c_131, plain, (![C_96, A_97, B_98]: (v1_relat_1(C_96) | ~m1_subset_1(C_96, k1_zfmisc_1(k2_zfmisc_1(A_97, B_98))))), inference(cnfTransformation, [status(thm)], [f_87])).
% 5.04/1.94  tff(c_145, plain, (v1_relat_1('#skF_10')), inference(resolution, [status(thm)], [c_76, c_131])).
% 5.04/1.94  tff(c_182, plain, (![C_104, B_105, A_106]: (v1_xboole_0(C_104) | ~m1_subset_1(C_104, k1_zfmisc_1(k2_zfmisc_1(B_105, A_106))) | ~v1_xboole_0(A_106))), inference(cnfTransformation, [status(thm)], [f_94])).
% 5.04/1.94  tff(c_196, plain, (v1_xboole_0('#skF_10') | ~v1_xboole_0('#skF_8')), inference(resolution, [status(thm)], [c_76, c_182])).
% 5.04/1.94  tff(c_197, plain, (~v1_xboole_0('#skF_8')), inference(splitLeft, [status(thm)], [c_196])).
% 5.04/1.94  tff(c_80, plain, (v1_funct_1('#skF_10')), inference(cnfTransformation, [status(thm)], [f_139])).
% 5.04/1.94  tff(c_28, plain, (![A_16, B_39, D_54]: (k1_funct_1(A_16, '#skF_6'(A_16, B_39, k9_relat_1(A_16, B_39), D_54))=D_54 | ~r2_hidden(D_54, k9_relat_1(A_16, B_39)) | ~v1_funct_1(A_16) | ~v1_relat_1(A_16))), inference(cnfTransformation, [status(thm)], [f_78])).
% 5.04/1.94  tff(c_78, plain, (v1_funct_2('#skF_10', '#skF_7', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_139])).
% 5.04/1.94  tff(c_207, plain, (![A_111, B_112, C_113]: (k1_relset_1(A_111, B_112, C_113)=k1_relat_1(C_113) | ~m1_subset_1(C_113, k1_zfmisc_1(k2_zfmisc_1(A_111, B_112))))), inference(cnfTransformation, [status(thm)], [f_98])).
% 5.04/1.94  tff(c_223, plain, (k1_relset_1('#skF_7', '#skF_8', '#skF_10')=k1_relat_1('#skF_10')), inference(resolution, [status(thm)], [c_76, c_207])).
% 5.04/1.94  tff(c_1090, plain, (![B_260, A_261, C_262]: (k1_xboole_0=B_260 | k1_relset_1(A_261, B_260, C_262)=A_261 | ~v1_funct_2(C_262, A_261, B_260) | ~m1_subset_1(C_262, k1_zfmisc_1(k2_zfmisc_1(A_261, B_260))))), inference(cnfTransformation, [status(thm)], [f_120])).
% 5.04/1.94  tff(c_1101, plain, (k1_xboole_0='#skF_8' | k1_relset_1('#skF_7', '#skF_8', '#skF_10')='#skF_7' | ~v1_funct_2('#skF_10', '#skF_7', '#skF_8')), inference(resolution, [status(thm)], [c_76, c_1090])).
% 5.04/1.94  tff(c_1108, plain, (k1_xboole_0='#skF_8' | k1_relat_1('#skF_10')='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_78, c_223, c_1101])).
% 5.04/1.94  tff(c_1109, plain, (k1_relat_1('#skF_10')='#skF_7'), inference(splitLeft, [status(thm)], [c_1108])).
% 5.04/1.94  tff(c_1762, plain, (![A_326, B_327, D_328]: (r2_hidden('#skF_6'(A_326, B_327, k9_relat_1(A_326, B_327), D_328), k1_relat_1(A_326)) | ~r2_hidden(D_328, k9_relat_1(A_326, B_327)) | ~v1_funct_1(A_326) | ~v1_relat_1(A_326))), inference(cnfTransformation, [status(thm)], [f_78])).
% 5.04/1.94  tff(c_1779, plain, (![B_327, D_328]: (r2_hidden('#skF_6'('#skF_10', B_327, k9_relat_1('#skF_10', B_327), D_328), '#skF_7') | ~r2_hidden(D_328, k9_relat_1('#skF_10', B_327)) | ~v1_funct_1('#skF_10') | ~v1_relat_1('#skF_10'))), inference(superposition, [status(thm), theory('equality')], [c_1109, c_1762])).
% 5.04/1.94  tff(c_1787, plain, (![B_329, D_330]: (r2_hidden('#skF_6'('#skF_10', B_329, k9_relat_1('#skF_10', B_329), D_330), '#skF_7') | ~r2_hidden(D_330, k9_relat_1('#skF_10', B_329)))), inference(demodulation, [status(thm), theory('equality')], [c_145, c_80, c_1779])).
% 5.04/1.94  tff(c_16, plain, (![A_8, B_9]: (m1_subset_1(A_8, B_9) | ~r2_hidden(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_50])).
% 5.04/1.94  tff(c_1809, plain, (![B_336, D_337]: (m1_subset_1('#skF_6'('#skF_10', B_336, k9_relat_1('#skF_10', B_336), D_337), '#skF_7') | ~r2_hidden(D_337, k9_relat_1('#skF_10', B_336)))), inference(resolution, [status(thm)], [c_1787, c_16])).
% 5.04/1.94  tff(c_1548, plain, (![A_308, B_309, D_310]: (r2_hidden('#skF_6'(A_308, B_309, k9_relat_1(A_308, B_309), D_310), B_309) | ~r2_hidden(D_310, k9_relat_1(A_308, B_309)) | ~v1_funct_1(A_308) | ~v1_relat_1(A_308))), inference(cnfTransformation, [status(thm)], [f_78])).
% 5.04/1.94  tff(c_72, plain, (![F_81]: (k1_funct_1('#skF_10', F_81)!='#skF_11' | ~r2_hidden(F_81, '#skF_9') | ~m1_subset_1(F_81, '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_139])).
% 5.04/1.94  tff(c_1639, plain, (![A_308, D_310]: (k1_funct_1('#skF_10', '#skF_6'(A_308, '#skF_9', k9_relat_1(A_308, '#skF_9'), D_310))!='#skF_11' | ~m1_subset_1('#skF_6'(A_308, '#skF_9', k9_relat_1(A_308, '#skF_9'), D_310), '#skF_7') | ~r2_hidden(D_310, k9_relat_1(A_308, '#skF_9')) | ~v1_funct_1(A_308) | ~v1_relat_1(A_308))), inference(resolution, [status(thm)], [c_1548, c_72])).
% 5.04/1.94  tff(c_1813, plain, (![D_337]: (k1_funct_1('#skF_10', '#skF_6'('#skF_10', '#skF_9', k9_relat_1('#skF_10', '#skF_9'), D_337))!='#skF_11' | ~v1_funct_1('#skF_10') | ~v1_relat_1('#skF_10') | ~r2_hidden(D_337, k9_relat_1('#skF_10', '#skF_9')))), inference(resolution, [status(thm)], [c_1809, c_1639])).
% 5.04/1.94  tff(c_2183, plain, (![D_380]: (k1_funct_1('#skF_10', '#skF_6'('#skF_10', '#skF_9', k9_relat_1('#skF_10', '#skF_9'), D_380))!='#skF_11' | ~r2_hidden(D_380, k9_relat_1('#skF_10', '#skF_9')))), inference(demodulation, [status(thm), theory('equality')], [c_145, c_80, c_1813])).
% 5.04/1.94  tff(c_2187, plain, (![D_54]: (D_54!='#skF_11' | ~r2_hidden(D_54, k9_relat_1('#skF_10', '#skF_9')) | ~r2_hidden(D_54, k9_relat_1('#skF_10', '#skF_9')) | ~v1_funct_1('#skF_10') | ~v1_relat_1('#skF_10'))), inference(superposition, [status(thm), theory('equality')], [c_28, c_2183])).
% 5.04/1.94  tff(c_2190, plain, (~r2_hidden('#skF_11', k9_relat_1('#skF_10', '#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_145, c_80, c_2187])).
% 5.04/1.94  tff(c_425, plain, (![A_161, B_162, C_163, D_164]: (k7_relset_1(A_161, B_162, C_163, D_164)=k9_relat_1(C_163, D_164) | ~m1_subset_1(C_163, k1_zfmisc_1(k2_zfmisc_1(A_161, B_162))))), inference(cnfTransformation, [status(thm)], [f_102])).
% 5.04/1.94  tff(c_438, plain, (![D_164]: (k7_relset_1('#skF_7', '#skF_8', '#skF_10', D_164)=k9_relat_1('#skF_10', D_164))), inference(resolution, [status(thm)], [c_76, c_425])).
% 5.04/1.94  tff(c_74, plain, (r2_hidden('#skF_11', k7_relset_1('#skF_7', '#skF_8', '#skF_10', '#skF_9'))), inference(cnfTransformation, [status(thm)], [f_139])).
% 5.04/1.94  tff(c_442, plain, (r2_hidden('#skF_11', k9_relat_1('#skF_10', '#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_438, c_74])).
% 5.04/1.94  tff(c_2192, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2190, c_442])).
% 5.04/1.94  tff(c_2193, plain, (k1_xboole_0='#skF_8'), inference(splitRight, [status(thm)], [c_1108])).
% 5.04/1.94  tff(c_6, plain, (![A_5]: (r1_tarski(k1_xboole_0, A_5))), inference(cnfTransformation, [status(thm)], [f_33])).
% 5.04/1.94  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.04/1.94  tff(c_93, plain, (![B_88, A_89]: (~r1_tarski(B_88, A_89) | ~r2_hidden(A_89, B_88))), inference(cnfTransformation, [status(thm)], [f_83])).
% 5.04/1.94  tff(c_111, plain, (![A_91]: (~r1_tarski(A_91, '#skF_1'(A_91)) | v1_xboole_0(A_91))), inference(resolution, [status(thm)], [c_4, c_93])).
% 5.04/1.94  tff(c_116, plain, (v1_xboole_0(k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_111])).
% 5.04/1.94  tff(c_2206, plain, (v1_xboole_0('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_2193, c_116])).
% 5.04/1.94  tff(c_2209, plain, $false, inference(negUnitSimplification, [status(thm)], [c_197, c_2206])).
% 5.04/1.94  tff(c_2210, plain, (v1_xboole_0('#skF_10')), inference(splitRight, [status(thm)], [c_196])).
% 5.04/1.94  tff(c_2359, plain, (![A_411, B_412, C_413, D_414]: (k7_relset_1(A_411, B_412, C_413, D_414)=k9_relat_1(C_413, D_414) | ~m1_subset_1(C_413, k1_zfmisc_1(k2_zfmisc_1(A_411, B_412))))), inference(cnfTransformation, [status(thm)], [f_102])).
% 5.04/1.94  tff(c_2372, plain, (![D_414]: (k7_relset_1('#skF_7', '#skF_8', '#skF_10', D_414)=k9_relat_1('#skF_10', D_414))), inference(resolution, [status(thm)], [c_76, c_2359])).
% 5.04/1.94  tff(c_2376, plain, (r2_hidden('#skF_11', k9_relat_1('#skF_10', '#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_2372, c_74])).
% 5.04/1.94  tff(c_2590, plain, (![A_460, B_461, C_462]: (r2_hidden(k4_tarski('#skF_2'(A_460, B_461, C_462), A_460), C_462) | ~r2_hidden(A_460, k9_relat_1(C_462, B_461)) | ~v1_relat_1(C_462))), inference(cnfTransformation, [status(thm)], [f_61])).
% 5.04/1.94  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.04/1.94  tff(c_2647, plain, (![C_463, A_464, B_465]: (~v1_xboole_0(C_463) | ~r2_hidden(A_464, k9_relat_1(C_463, B_465)) | ~v1_relat_1(C_463))), inference(resolution, [status(thm)], [c_2590, c_2])).
% 5.04/1.94  tff(c_2654, plain, (~v1_xboole_0('#skF_10') | ~v1_relat_1('#skF_10')), inference(resolution, [status(thm)], [c_2376, c_2647])).
% 5.04/1.94  tff(c_2671, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_145, c_2210, c_2654])).
% 5.04/1.94  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.04/1.94  
% 5.04/1.94  Inference rules
% 5.04/1.94  ----------------------
% 5.04/1.94  #Ref     : 0
% 5.04/1.94  #Sup     : 503
% 5.04/1.94  #Fact    : 0
% 5.04/1.94  #Define  : 0
% 5.04/1.94  #Split   : 20
% 5.04/1.94  #Chain   : 0
% 5.04/1.94  #Close   : 0
% 5.04/1.94  
% 5.04/1.94  Ordering : KBO
% 5.04/1.94  
% 5.04/1.94  Simplification rules
% 5.04/1.94  ----------------------
% 5.04/1.94  #Subsume      : 123
% 5.04/1.94  #Demod        : 168
% 5.04/1.94  #Tautology    : 44
% 5.04/1.94  #SimpNegUnit  : 39
% 5.04/1.94  #BackRed      : 41
% 5.04/1.94  
% 5.04/1.94  #Partial instantiations: 0
% 5.04/1.94  #Strategies tried      : 1
% 5.04/1.94  
% 5.04/1.94  Timing (in seconds)
% 5.04/1.94  ----------------------
% 5.04/1.94  Preprocessing        : 0.37
% 5.04/1.94  Parsing              : 0.18
% 5.04/1.94  CNF conversion       : 0.03
% 5.04/1.94  Main loop            : 0.80
% 5.04/1.94  Inferencing          : 0.28
% 5.04/1.94  Reduction            : 0.22
% 5.04/1.94  Demodulation         : 0.15
% 5.04/1.94  BG Simplification    : 0.04
% 5.04/1.95  Subsumption          : 0.20
% 5.04/1.95  Abstraction          : 0.04
% 5.04/1.95  MUC search           : 0.00
% 5.04/1.95  Cooper               : 0.00
% 5.04/1.95  Total                : 1.21
% 5.04/1.95  Index Insertion      : 0.00
% 5.04/1.95  Index Deletion       : 0.00
% 5.04/1.95  Index Matching       : 0.00
% 5.04/1.95  BG Taut test         : 0.00
%------------------------------------------------------------------------------
