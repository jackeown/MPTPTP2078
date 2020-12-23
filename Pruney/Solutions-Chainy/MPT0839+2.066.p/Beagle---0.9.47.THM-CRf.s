%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:08:30 EST 2020

% Result     : Theorem 6.79s
% Output     : CNFRefutation 6.90s
% Verified   : 
% Statistics : Number of formulae       :   94 ( 178 expanded)
%              Number of leaves         :   38 (  75 expanded)
%              Depth                    :   12
%              Number of atoms          :  137 ( 336 expanded)
%              Number of equality atoms :   32 (  86 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k2_relset_1 > k1_relset_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_7 > #skF_3 > #skF_6 > #skF_5 > #skF_8 > #skF_2 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_110,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B] :
            ( ~ v1_xboole_0(B)
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(B,A)))
               => ~ ( k2_relset_1(B,A,C) != k1_xboole_0
                    & ! [D] :
                        ( m1_subset_1(D,B)
                       => ~ r2_hidden(D,k1_relset_1(B,A,C)) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_relset_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_67,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_57,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_76,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( k1_relat_1(A) = k1_xboole_0
      <=> k2_relat_1(A) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_relat_1)).

tff(f_70,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_65,axiom,(
    ! [A,B] :
      ( B = k1_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(C,D),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_1)).

tff(f_34,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_81,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_40,axiom,(
    ! [A,B,C,D] :
      ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(C,D))
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,D) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l54_zfmisc_1)).

tff(f_50,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

tff(f_85,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_89,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(c_54,plain,(
    k2_relset_1('#skF_7','#skF_6','#skF_8') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_129,plain,(
    ! [A_78,B_79] :
      ( r2_hidden('#skF_1'(A_78,B_79),A_78)
      | r1_tarski(A_78,B_79) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_141,plain,(
    ! [A_78] : r1_tarski(A_78,A_78) ),
    inference(resolution,[status(thm)],[c_129,c_4])).

tff(c_36,plain,(
    ! [A_38,B_39] : v1_relat_1(k2_zfmisc_1(A_38,B_39)) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_56,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_7','#skF_6'))) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_83,plain,(
    ! [B_71,A_72] :
      ( v1_relat_1(B_71)
      | ~ m1_subset_1(B_71,k1_zfmisc_1(A_72))
      | ~ v1_relat_1(A_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_89,plain,
    ( v1_relat_1('#skF_8')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_7','#skF_6')) ),
    inference(resolution,[status(thm)],[c_56,c_83])).

tff(c_93,plain,(
    v1_relat_1('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_89])).

tff(c_94,plain,(
    ! [A_73] :
      ( k1_relat_1(A_73) = k1_xboole_0
      | k2_relat_1(A_73) != k1_xboole_0
      | ~ v1_relat_1(A_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_101,plain,
    ( k1_relat_1('#skF_8') = k1_xboole_0
    | k2_relat_1('#skF_8') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_93,c_94])).

tff(c_103,plain,(
    k2_relat_1('#skF_8') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_101])).

tff(c_149,plain,(
    ! [A_81] :
      ( k2_relat_1(A_81) = k1_xboole_0
      | k1_relat_1(A_81) != k1_xboole_0
      | ~ v1_relat_1(A_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_155,plain,
    ( k2_relat_1('#skF_8') = k1_xboole_0
    | k1_relat_1('#skF_8') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_93,c_149])).

tff(c_164,plain,(
    k1_relat_1('#skF_8') != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_103,c_155])).

tff(c_40,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_784,plain,(
    ! [A_205,B_206] :
      ( r2_hidden(k4_tarski('#skF_2'(A_205,B_206),'#skF_3'(A_205,B_206)),A_205)
      | r2_hidden('#skF_4'(A_205,B_206),B_206)
      | k1_relat_1(A_205) = B_206 ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_8,plain,(
    ! [A_6] : r1_tarski(k1_xboole_0,A_6) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_453,plain,(
    ! [C_154,A_155] :
      ( r2_hidden(k4_tarski(C_154,'#skF_5'(A_155,k1_relat_1(A_155),C_154)),A_155)
      | ~ r2_hidden(C_154,k1_relat_1(A_155)) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_478,plain,(
    ! [C_154] :
      ( r2_hidden(k4_tarski(C_154,'#skF_5'(k1_xboole_0,k1_xboole_0,C_154)),k1_xboole_0)
      | ~ r2_hidden(C_154,k1_relat_1(k1_xboole_0)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_453])).

tff(c_503,plain,(
    ! [C_159] :
      ( r2_hidden(k4_tarski(C_159,'#skF_5'(k1_xboole_0,k1_xboole_0,C_159)),k1_xboole_0)
      | ~ r2_hidden(C_159,k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_478])).

tff(c_46,plain,(
    ! [B_42,A_41] :
      ( ~ r1_tarski(B_42,A_41)
      | ~ r2_hidden(A_41,B_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_513,plain,(
    ! [C_159] :
      ( ~ r1_tarski(k1_xboole_0,k4_tarski(C_159,'#skF_5'(k1_xboole_0,k1_xboole_0,C_159)))
      | ~ r2_hidden(C_159,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_503,c_46])).

tff(c_524,plain,(
    ! [C_159] : ~ r2_hidden(C_159,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_513])).

tff(c_793,plain,(
    ! [B_206] :
      ( r2_hidden('#skF_4'(k1_xboole_0,B_206),B_206)
      | k1_relat_1(k1_xboole_0) = B_206 ) ),
    inference(resolution,[status(thm)],[c_784,c_524])).

tff(c_823,plain,(
    ! [B_206] :
      ( r2_hidden('#skF_4'(k1_xboole_0,B_206),B_206)
      | k1_xboole_0 = B_206 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_793])).

tff(c_73,plain,(
    ! [A_67,B_68] :
      ( r1_tarski(A_67,B_68)
      | ~ m1_subset_1(A_67,k1_zfmisc_1(B_68)) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_77,plain,(
    r1_tarski('#skF_8',k2_zfmisc_1('#skF_7','#skF_6')) ),
    inference(resolution,[status(thm)],[c_56,c_73])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_1772,plain,(
    ! [C_247,A_248,B_249] :
      ( r2_hidden(k4_tarski(C_247,'#skF_5'(A_248,k1_relat_1(A_248),C_247)),B_249)
      | ~ r1_tarski(A_248,B_249)
      | ~ r2_hidden(C_247,k1_relat_1(A_248)) ) ),
    inference(resolution,[status(thm)],[c_453,c_2])).

tff(c_26,plain,(
    ! [C_34,A_19,D_37] :
      ( r2_hidden(C_34,k1_relat_1(A_19))
      | ~ r2_hidden(k4_tarski(C_34,D_37),A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_6575,plain,(
    ! [C_355,B_356,A_357] :
      ( r2_hidden(C_355,k1_relat_1(B_356))
      | ~ r1_tarski(A_357,B_356)
      | ~ r2_hidden(C_355,k1_relat_1(A_357)) ) ),
    inference(resolution,[status(thm)],[c_1772,c_26])).

tff(c_6613,plain,(
    ! [C_358] :
      ( r2_hidden(C_358,k1_relat_1(k2_zfmisc_1('#skF_7','#skF_6')))
      | ~ r2_hidden(C_358,k1_relat_1('#skF_8')) ) ),
    inference(resolution,[status(thm)],[c_77,c_6575])).

tff(c_14,plain,(
    ! [A_7,C_9,B_8,D_10] :
      ( r2_hidden(A_7,C_9)
      | ~ r2_hidden(k4_tarski(A_7,B_8),k2_zfmisc_1(C_9,D_10)) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_482,plain,(
    ! [C_154,C_9,D_10] :
      ( r2_hidden(C_154,C_9)
      | ~ r2_hidden(C_154,k1_relat_1(k2_zfmisc_1(C_9,D_10))) ) ),
    inference(resolution,[status(thm)],[c_453,c_14])).

tff(c_6676,plain,(
    ! [C_359] :
      ( r2_hidden(C_359,'#skF_7')
      | ~ r2_hidden(C_359,k1_relat_1('#skF_8')) ) ),
    inference(resolution,[status(thm)],[c_6613,c_482])).

tff(c_6742,plain,
    ( r2_hidden('#skF_4'(k1_xboole_0,k1_relat_1('#skF_8')),'#skF_7')
    | k1_relat_1('#skF_8') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_823,c_6676])).

tff(c_6779,plain,(
    r2_hidden('#skF_4'(k1_xboole_0,k1_relat_1('#skF_8')),'#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_164,c_6742])).

tff(c_18,plain,(
    ! [A_11,B_12] :
      ( m1_subset_1(A_11,k1_zfmisc_1(B_12))
      | ~ r1_tarski(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_180,plain,(
    ! [A_95,C_96,B_97] :
      ( m1_subset_1(A_95,C_96)
      | ~ m1_subset_1(B_97,k1_zfmisc_1(C_96))
      | ~ r2_hidden(A_95,B_97) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_185,plain,(
    ! [A_95,B_12,A_11] :
      ( m1_subset_1(A_95,B_12)
      | ~ r2_hidden(A_95,A_11)
      | ~ r1_tarski(A_11,B_12) ) ),
    inference(resolution,[status(thm)],[c_18,c_180])).

tff(c_8236,plain,(
    ! [B_411] :
      ( m1_subset_1('#skF_4'(k1_xboole_0,k1_relat_1('#skF_8')),B_411)
      | ~ r1_tarski('#skF_7',B_411) ) ),
    inference(resolution,[status(thm)],[c_6779,c_185])).

tff(c_832,plain,(
    ! [B_207] :
      ( r2_hidden('#skF_4'(k1_xboole_0,B_207),B_207)
      | k1_xboole_0 = B_207 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_793])).

tff(c_275,plain,(
    ! [A_123,B_124,C_125] :
      ( k1_relset_1(A_123,B_124,C_125) = k1_relat_1(C_125)
      | ~ m1_subset_1(C_125,k1_zfmisc_1(k2_zfmisc_1(A_123,B_124))) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_289,plain,(
    k1_relset_1('#skF_7','#skF_6','#skF_8') = k1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_56,c_275])).

tff(c_52,plain,(
    ! [D_60] :
      ( ~ r2_hidden(D_60,k1_relset_1('#skF_7','#skF_6','#skF_8'))
      | ~ m1_subset_1(D_60,'#skF_7') ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_292,plain,(
    ! [D_60] :
      ( ~ r2_hidden(D_60,k1_relat_1('#skF_8'))
      | ~ m1_subset_1(D_60,'#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_289,c_52])).

tff(c_849,plain,
    ( ~ m1_subset_1('#skF_4'(k1_xboole_0,k1_relat_1('#skF_8')),'#skF_7')
    | k1_relat_1('#skF_8') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_832,c_292])).

tff(c_864,plain,(
    ~ m1_subset_1('#skF_4'(k1_xboole_0,k1_relat_1('#skF_8')),'#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_164,c_849])).

tff(c_8257,plain,(
    ~ r1_tarski('#skF_7','#skF_7') ),
    inference(resolution,[status(thm)],[c_8236,c_864])).

tff(c_8285,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_141,c_8257])).

tff(c_8287,plain,(
    k2_relat_1('#skF_8') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_101])).

tff(c_8424,plain,(
    ! [A_452,B_453,C_454] :
      ( k2_relset_1(A_452,B_453,C_454) = k2_relat_1(C_454)
      | ~ m1_subset_1(C_454,k1_zfmisc_1(k2_zfmisc_1(A_452,B_453))) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_8431,plain,(
    k2_relset_1('#skF_7','#skF_6','#skF_8') = k2_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_56,c_8424])).

tff(c_8434,plain,(
    k2_relset_1('#skF_7','#skF_6','#skF_8') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8287,c_8431])).

tff(c_8436,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_8434])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:28:37 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.79/2.37  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.79/2.38  
% 6.79/2.38  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.90/2.38  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k2_relset_1 > k1_relset_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_7 > #skF_3 > #skF_6 > #skF_5 > #skF_8 > #skF_2 > #skF_1 > #skF_4
% 6.90/2.38  
% 6.90/2.38  %Foreground sorts:
% 6.90/2.38  
% 6.90/2.38  
% 6.90/2.38  %Background operators:
% 6.90/2.38  
% 6.90/2.38  
% 6.90/2.38  %Foreground operators:
% 6.90/2.38  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 6.90/2.38  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.90/2.38  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 6.90/2.38  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 6.90/2.38  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 6.90/2.38  tff('#skF_7', type, '#skF_7': $i).
% 6.90/2.38  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 6.90/2.38  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.90/2.38  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 6.90/2.38  tff('#skF_6', type, '#skF_6': $i).
% 6.90/2.38  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 6.90/2.38  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 6.90/2.38  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 6.90/2.38  tff('#skF_8', type, '#skF_8': $i).
% 6.90/2.38  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.90/2.38  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 6.90/2.38  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 6.90/2.38  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.90/2.38  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 6.90/2.38  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 6.90/2.38  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 6.90/2.38  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 6.90/2.38  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 6.90/2.38  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 6.90/2.38  
% 6.90/2.40  tff(f_110, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => ~(~(k2_relset_1(B, A, C) = k1_xboole_0) & (![D]: (m1_subset_1(D, B) => ~r2_hidden(D, k1_relset_1(B, A, C))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t50_relset_1)).
% 6.90/2.40  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 6.90/2.40  tff(f_67, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 6.90/2.40  tff(f_57, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 6.90/2.40  tff(f_76, axiom, (![A]: (v1_relat_1(A) => ((k1_relat_1(A) = k1_xboole_0) <=> (k2_relat_1(A) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_relat_1)).
% 6.90/2.40  tff(f_70, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 6.90/2.40  tff(f_65, axiom, (![A, B]: ((B = k1_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(C, D), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_relat_1)).
% 6.90/2.40  tff(f_34, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 6.90/2.40  tff(f_81, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 6.90/2.40  tff(f_44, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 6.90/2.40  tff(f_40, axiom, (![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(C, D)) <=> (r2_hidden(A, C) & r2_hidden(B, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l54_zfmisc_1)).
% 6.90/2.40  tff(f_50, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset)).
% 6.90/2.40  tff(f_85, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 6.90/2.40  tff(f_89, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 6.90/2.40  tff(c_54, plain, (k2_relset_1('#skF_7', '#skF_6', '#skF_8')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_110])).
% 6.90/2.40  tff(c_129, plain, (![A_78, B_79]: (r2_hidden('#skF_1'(A_78, B_79), A_78) | r1_tarski(A_78, B_79))), inference(cnfTransformation, [status(thm)], [f_32])).
% 6.90/2.40  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 6.90/2.40  tff(c_141, plain, (![A_78]: (r1_tarski(A_78, A_78))), inference(resolution, [status(thm)], [c_129, c_4])).
% 6.90/2.40  tff(c_36, plain, (![A_38, B_39]: (v1_relat_1(k2_zfmisc_1(A_38, B_39)))), inference(cnfTransformation, [status(thm)], [f_67])).
% 6.90/2.40  tff(c_56, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_7', '#skF_6')))), inference(cnfTransformation, [status(thm)], [f_110])).
% 6.90/2.40  tff(c_83, plain, (![B_71, A_72]: (v1_relat_1(B_71) | ~m1_subset_1(B_71, k1_zfmisc_1(A_72)) | ~v1_relat_1(A_72))), inference(cnfTransformation, [status(thm)], [f_57])).
% 6.90/2.40  tff(c_89, plain, (v1_relat_1('#skF_8') | ~v1_relat_1(k2_zfmisc_1('#skF_7', '#skF_6'))), inference(resolution, [status(thm)], [c_56, c_83])).
% 6.90/2.40  tff(c_93, plain, (v1_relat_1('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_89])).
% 6.90/2.40  tff(c_94, plain, (![A_73]: (k1_relat_1(A_73)=k1_xboole_0 | k2_relat_1(A_73)!=k1_xboole_0 | ~v1_relat_1(A_73))), inference(cnfTransformation, [status(thm)], [f_76])).
% 6.90/2.40  tff(c_101, plain, (k1_relat_1('#skF_8')=k1_xboole_0 | k2_relat_1('#skF_8')!=k1_xboole_0), inference(resolution, [status(thm)], [c_93, c_94])).
% 6.90/2.40  tff(c_103, plain, (k2_relat_1('#skF_8')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_101])).
% 6.90/2.40  tff(c_149, plain, (![A_81]: (k2_relat_1(A_81)=k1_xboole_0 | k1_relat_1(A_81)!=k1_xboole_0 | ~v1_relat_1(A_81))), inference(cnfTransformation, [status(thm)], [f_76])).
% 6.90/2.40  tff(c_155, plain, (k2_relat_1('#skF_8')=k1_xboole_0 | k1_relat_1('#skF_8')!=k1_xboole_0), inference(resolution, [status(thm)], [c_93, c_149])).
% 6.90/2.40  tff(c_164, plain, (k1_relat_1('#skF_8')!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_103, c_155])).
% 6.90/2.40  tff(c_40, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_70])).
% 6.90/2.40  tff(c_784, plain, (![A_205, B_206]: (r2_hidden(k4_tarski('#skF_2'(A_205, B_206), '#skF_3'(A_205, B_206)), A_205) | r2_hidden('#skF_4'(A_205, B_206), B_206) | k1_relat_1(A_205)=B_206)), inference(cnfTransformation, [status(thm)], [f_65])).
% 6.90/2.40  tff(c_8, plain, (![A_6]: (r1_tarski(k1_xboole_0, A_6))), inference(cnfTransformation, [status(thm)], [f_34])).
% 6.90/2.40  tff(c_453, plain, (![C_154, A_155]: (r2_hidden(k4_tarski(C_154, '#skF_5'(A_155, k1_relat_1(A_155), C_154)), A_155) | ~r2_hidden(C_154, k1_relat_1(A_155)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 6.90/2.40  tff(c_478, plain, (![C_154]: (r2_hidden(k4_tarski(C_154, '#skF_5'(k1_xboole_0, k1_xboole_0, C_154)), k1_xboole_0) | ~r2_hidden(C_154, k1_relat_1(k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_40, c_453])).
% 6.90/2.40  tff(c_503, plain, (![C_159]: (r2_hidden(k4_tarski(C_159, '#skF_5'(k1_xboole_0, k1_xboole_0, C_159)), k1_xboole_0) | ~r2_hidden(C_159, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_478])).
% 6.90/2.40  tff(c_46, plain, (![B_42, A_41]: (~r1_tarski(B_42, A_41) | ~r2_hidden(A_41, B_42))), inference(cnfTransformation, [status(thm)], [f_81])).
% 6.90/2.40  tff(c_513, plain, (![C_159]: (~r1_tarski(k1_xboole_0, k4_tarski(C_159, '#skF_5'(k1_xboole_0, k1_xboole_0, C_159))) | ~r2_hidden(C_159, k1_xboole_0))), inference(resolution, [status(thm)], [c_503, c_46])).
% 6.90/2.40  tff(c_524, plain, (![C_159]: (~r2_hidden(C_159, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_513])).
% 6.90/2.40  tff(c_793, plain, (![B_206]: (r2_hidden('#skF_4'(k1_xboole_0, B_206), B_206) | k1_relat_1(k1_xboole_0)=B_206)), inference(resolution, [status(thm)], [c_784, c_524])).
% 6.90/2.40  tff(c_823, plain, (![B_206]: (r2_hidden('#skF_4'(k1_xboole_0, B_206), B_206) | k1_xboole_0=B_206)), inference(demodulation, [status(thm), theory('equality')], [c_40, c_793])).
% 6.90/2.40  tff(c_73, plain, (![A_67, B_68]: (r1_tarski(A_67, B_68) | ~m1_subset_1(A_67, k1_zfmisc_1(B_68)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 6.90/2.40  tff(c_77, plain, (r1_tarski('#skF_8', k2_zfmisc_1('#skF_7', '#skF_6'))), inference(resolution, [status(thm)], [c_56, c_73])).
% 6.90/2.40  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 6.90/2.40  tff(c_1772, plain, (![C_247, A_248, B_249]: (r2_hidden(k4_tarski(C_247, '#skF_5'(A_248, k1_relat_1(A_248), C_247)), B_249) | ~r1_tarski(A_248, B_249) | ~r2_hidden(C_247, k1_relat_1(A_248)))), inference(resolution, [status(thm)], [c_453, c_2])).
% 6.90/2.40  tff(c_26, plain, (![C_34, A_19, D_37]: (r2_hidden(C_34, k1_relat_1(A_19)) | ~r2_hidden(k4_tarski(C_34, D_37), A_19))), inference(cnfTransformation, [status(thm)], [f_65])).
% 6.90/2.40  tff(c_6575, plain, (![C_355, B_356, A_357]: (r2_hidden(C_355, k1_relat_1(B_356)) | ~r1_tarski(A_357, B_356) | ~r2_hidden(C_355, k1_relat_1(A_357)))), inference(resolution, [status(thm)], [c_1772, c_26])).
% 6.90/2.40  tff(c_6613, plain, (![C_358]: (r2_hidden(C_358, k1_relat_1(k2_zfmisc_1('#skF_7', '#skF_6'))) | ~r2_hidden(C_358, k1_relat_1('#skF_8')))), inference(resolution, [status(thm)], [c_77, c_6575])).
% 6.90/2.40  tff(c_14, plain, (![A_7, C_9, B_8, D_10]: (r2_hidden(A_7, C_9) | ~r2_hidden(k4_tarski(A_7, B_8), k2_zfmisc_1(C_9, D_10)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 6.90/2.40  tff(c_482, plain, (![C_154, C_9, D_10]: (r2_hidden(C_154, C_9) | ~r2_hidden(C_154, k1_relat_1(k2_zfmisc_1(C_9, D_10))))), inference(resolution, [status(thm)], [c_453, c_14])).
% 6.90/2.40  tff(c_6676, plain, (![C_359]: (r2_hidden(C_359, '#skF_7') | ~r2_hidden(C_359, k1_relat_1('#skF_8')))), inference(resolution, [status(thm)], [c_6613, c_482])).
% 6.90/2.40  tff(c_6742, plain, (r2_hidden('#skF_4'(k1_xboole_0, k1_relat_1('#skF_8')), '#skF_7') | k1_relat_1('#skF_8')=k1_xboole_0), inference(resolution, [status(thm)], [c_823, c_6676])).
% 6.90/2.40  tff(c_6779, plain, (r2_hidden('#skF_4'(k1_xboole_0, k1_relat_1('#skF_8')), '#skF_7')), inference(negUnitSimplification, [status(thm)], [c_164, c_6742])).
% 6.90/2.40  tff(c_18, plain, (![A_11, B_12]: (m1_subset_1(A_11, k1_zfmisc_1(B_12)) | ~r1_tarski(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_44])).
% 6.90/2.40  tff(c_180, plain, (![A_95, C_96, B_97]: (m1_subset_1(A_95, C_96) | ~m1_subset_1(B_97, k1_zfmisc_1(C_96)) | ~r2_hidden(A_95, B_97))), inference(cnfTransformation, [status(thm)], [f_50])).
% 6.90/2.40  tff(c_185, plain, (![A_95, B_12, A_11]: (m1_subset_1(A_95, B_12) | ~r2_hidden(A_95, A_11) | ~r1_tarski(A_11, B_12))), inference(resolution, [status(thm)], [c_18, c_180])).
% 6.90/2.40  tff(c_8236, plain, (![B_411]: (m1_subset_1('#skF_4'(k1_xboole_0, k1_relat_1('#skF_8')), B_411) | ~r1_tarski('#skF_7', B_411))), inference(resolution, [status(thm)], [c_6779, c_185])).
% 6.90/2.40  tff(c_832, plain, (![B_207]: (r2_hidden('#skF_4'(k1_xboole_0, B_207), B_207) | k1_xboole_0=B_207)), inference(demodulation, [status(thm), theory('equality')], [c_40, c_793])).
% 6.90/2.40  tff(c_275, plain, (![A_123, B_124, C_125]: (k1_relset_1(A_123, B_124, C_125)=k1_relat_1(C_125) | ~m1_subset_1(C_125, k1_zfmisc_1(k2_zfmisc_1(A_123, B_124))))), inference(cnfTransformation, [status(thm)], [f_85])).
% 6.90/2.40  tff(c_289, plain, (k1_relset_1('#skF_7', '#skF_6', '#skF_8')=k1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_56, c_275])).
% 6.90/2.40  tff(c_52, plain, (![D_60]: (~r2_hidden(D_60, k1_relset_1('#skF_7', '#skF_6', '#skF_8')) | ~m1_subset_1(D_60, '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_110])).
% 6.90/2.40  tff(c_292, plain, (![D_60]: (~r2_hidden(D_60, k1_relat_1('#skF_8')) | ~m1_subset_1(D_60, '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_289, c_52])).
% 6.90/2.40  tff(c_849, plain, (~m1_subset_1('#skF_4'(k1_xboole_0, k1_relat_1('#skF_8')), '#skF_7') | k1_relat_1('#skF_8')=k1_xboole_0), inference(resolution, [status(thm)], [c_832, c_292])).
% 6.90/2.40  tff(c_864, plain, (~m1_subset_1('#skF_4'(k1_xboole_0, k1_relat_1('#skF_8')), '#skF_7')), inference(negUnitSimplification, [status(thm)], [c_164, c_849])).
% 6.90/2.40  tff(c_8257, plain, (~r1_tarski('#skF_7', '#skF_7')), inference(resolution, [status(thm)], [c_8236, c_864])).
% 6.90/2.40  tff(c_8285, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_141, c_8257])).
% 6.90/2.40  tff(c_8287, plain, (k2_relat_1('#skF_8')=k1_xboole_0), inference(splitRight, [status(thm)], [c_101])).
% 6.90/2.40  tff(c_8424, plain, (![A_452, B_453, C_454]: (k2_relset_1(A_452, B_453, C_454)=k2_relat_1(C_454) | ~m1_subset_1(C_454, k1_zfmisc_1(k2_zfmisc_1(A_452, B_453))))), inference(cnfTransformation, [status(thm)], [f_89])).
% 6.90/2.40  tff(c_8431, plain, (k2_relset_1('#skF_7', '#skF_6', '#skF_8')=k2_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_56, c_8424])).
% 6.90/2.40  tff(c_8434, plain, (k2_relset_1('#skF_7', '#skF_6', '#skF_8')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_8287, c_8431])).
% 6.90/2.40  tff(c_8436, plain, $false, inference(negUnitSimplification, [status(thm)], [c_54, c_8434])).
% 6.90/2.40  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.90/2.40  
% 6.90/2.40  Inference rules
% 6.90/2.40  ----------------------
% 6.90/2.40  #Ref     : 0
% 6.90/2.40  #Sup     : 1958
% 6.90/2.40  #Fact    : 0
% 6.90/2.40  #Define  : 0
% 6.90/2.40  #Split   : 8
% 6.90/2.40  #Chain   : 0
% 6.90/2.40  #Close   : 0
% 6.90/2.40  
% 6.90/2.40  Ordering : KBO
% 6.90/2.40  
% 6.90/2.40  Simplification rules
% 6.90/2.40  ----------------------
% 6.90/2.40  #Subsume      : 537
% 6.90/2.40  #Demod        : 1022
% 6.90/2.40  #Tautology    : 586
% 6.90/2.40  #SimpNegUnit  : 43
% 6.90/2.40  #BackRed      : 16
% 6.90/2.40  
% 6.90/2.40  #Partial instantiations: 0
% 6.90/2.40  #Strategies tried      : 1
% 6.90/2.40  
% 6.90/2.40  Timing (in seconds)
% 6.90/2.40  ----------------------
% 6.90/2.40  Preprocessing        : 0.32
% 6.90/2.40  Parsing              : 0.17
% 6.90/2.40  CNF conversion       : 0.03
% 6.90/2.40  Main loop            : 1.30
% 6.90/2.40  Inferencing          : 0.40
% 6.90/2.40  Reduction            : 0.39
% 6.90/2.40  Demodulation         : 0.26
% 6.90/2.40  BG Simplification    : 0.05
% 6.90/2.40  Subsumption          : 0.36
% 6.90/2.40  Abstraction          : 0.06
% 6.90/2.40  MUC search           : 0.00
% 6.90/2.40  Cooper               : 0.00
% 6.90/2.40  Total                : 1.66
% 6.90/2.40  Index Insertion      : 0.00
% 6.90/2.40  Index Deletion       : 0.00
% 6.90/2.40  Index Matching       : 0.00
% 6.90/2.40  BG Taut test         : 0.00
%------------------------------------------------------------------------------
