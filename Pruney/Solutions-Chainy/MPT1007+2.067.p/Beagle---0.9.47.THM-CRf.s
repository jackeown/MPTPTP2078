%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:14:20 EST 2020

% Result     : Theorem 3.84s
% Output     : CNFRefutation 4.06s
% Verified   : 
% Statistics : Number of formulae       :   86 ( 133 expanded)
%              Number of leaves         :   46 (  68 expanded)
%              Depth                    :   13
%              Number of atoms          :  114 ( 233 expanded)
%              Number of equality atoms :   36 (  50 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k9_relat_1 > k7_relat_1 > k4_xboole_0 > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > k11_relat_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_4 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

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

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff(k11_relat_1,type,(
    k11_relat_1: ( $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

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

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_78,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_167,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,k1_tarski(A),B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A),B))) )
       => ( B != k1_xboole_0
         => r2_hidden(k1_funct_1(C,A),B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_2)).

tff(f_65,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_112,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_76,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_98,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_82,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_70,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] : k11_relat_1(A,B) = k9_relat_1(A,k1_tarski(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d16_relat_1)).

tff(f_116,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_155,axiom,(
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

tff(f_51,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

tff(f_106,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r2_hidden(A,k1_relat_1(B))
       => k11_relat_1(B,A) = k1_tarski(k1_funct_1(B,A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t117_funct_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(c_46,plain,(
    ! [A_28,B_29] : v1_relat_1(k2_zfmisc_1(A_28,B_29)) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_82,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_5'),'#skF_6'))) ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_239,plain,(
    ! [B_93,A_94] :
      ( v1_relat_1(B_93)
      | ~ m1_subset_1(B_93,k1_zfmisc_1(A_94))
      | ~ v1_relat_1(A_94) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_242,plain,
    ( v1_relat_1('#skF_7')
    | ~ v1_relat_1(k2_zfmisc_1(k1_tarski('#skF_5'),'#skF_6')) ),
    inference(resolution,[status(thm)],[c_82,c_239])).

tff(c_245,plain,(
    v1_relat_1('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_242])).

tff(c_246,plain,(
    ! [C_95,B_96,A_97] :
      ( v5_relat_1(C_95,B_96)
      | ~ m1_subset_1(C_95,k1_zfmisc_1(k2_zfmisc_1(A_97,B_96))) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_250,plain,(
    v5_relat_1('#skF_7','#skF_6') ),
    inference(resolution,[status(thm)],[c_82,c_246])).

tff(c_44,plain,(
    ! [B_27,A_26] :
      ( r1_tarski(k2_relat_1(B_27),A_26)
      | ~ v5_relat_1(B_27,A_26)
      | ~ v1_relat_1(B_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_86,plain,(
    v1_funct_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_336,plain,(
    ! [C_113,A_114,B_115] :
      ( v4_relat_1(C_113,A_114)
      | ~ m1_subset_1(C_113,k1_zfmisc_1(k2_zfmisc_1(A_114,B_115))) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_340,plain,(
    v4_relat_1('#skF_7',k1_tarski('#skF_5')) ),
    inference(resolution,[status(thm)],[c_82,c_336])).

tff(c_52,plain,(
    ! [B_35,A_34] :
      ( k7_relat_1(B_35,A_34) = B_35
      | ~ v4_relat_1(B_35,A_34)
      | ~ v1_relat_1(B_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_350,plain,
    ( k7_relat_1('#skF_7',k1_tarski('#skF_5')) = '#skF_7'
    | ~ v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_340,c_52])).

tff(c_353,plain,(
    k7_relat_1('#skF_7',k1_tarski('#skF_5')) = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_245,c_350])).

tff(c_48,plain,(
    ! [B_31,A_30] :
      ( k2_relat_1(k7_relat_1(B_31,A_30)) = k9_relat_1(B_31,A_30)
      | ~ v1_relat_1(B_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_357,plain,
    ( k9_relat_1('#skF_7',k1_tarski('#skF_5')) = k2_relat_1('#skF_7')
    | ~ v1_relat_1('#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_353,c_48])).

tff(c_361,plain,(
    k9_relat_1('#skF_7',k1_tarski('#skF_5')) = k2_relat_1('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_245,c_357])).

tff(c_40,plain,(
    ! [A_23,B_25] :
      ( k9_relat_1(A_23,k1_tarski(B_25)) = k11_relat_1(A_23,B_25)
      | ~ v1_relat_1(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_366,plain,
    ( k11_relat_1('#skF_7','#skF_5') = k2_relat_1('#skF_7')
    | ~ v1_relat_1('#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_361,c_40])).

tff(c_373,plain,(
    k11_relat_1('#skF_7','#skF_5') = k2_relat_1('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_245,c_366])).

tff(c_80,plain,(
    k1_xboole_0 != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_84,plain,(
    v1_funct_2('#skF_7',k1_tarski('#skF_5'),'#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_483,plain,(
    ! [A_133,B_134,C_135] :
      ( k1_relset_1(A_133,B_134,C_135) = k1_relat_1(C_135)
      | ~ m1_subset_1(C_135,k1_zfmisc_1(k2_zfmisc_1(A_133,B_134))) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_487,plain,(
    k1_relset_1(k1_tarski('#skF_5'),'#skF_6','#skF_7') = k1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_82,c_483])).

tff(c_982,plain,(
    ! [B_203,A_204,C_205] :
      ( k1_xboole_0 = B_203
      | k1_relset_1(A_204,B_203,C_205) = A_204
      | ~ v1_funct_2(C_205,A_204,B_203)
      | ~ m1_subset_1(C_205,k1_zfmisc_1(k2_zfmisc_1(A_204,B_203))) ) ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_985,plain,
    ( k1_xboole_0 = '#skF_6'
    | k1_relset_1(k1_tarski('#skF_5'),'#skF_6','#skF_7') = k1_tarski('#skF_5')
    | ~ v1_funct_2('#skF_7',k1_tarski('#skF_5'),'#skF_6') ),
    inference(resolution,[status(thm)],[c_82,c_982])).

tff(c_988,plain,
    ( k1_xboole_0 = '#skF_6'
    | k1_tarski('#skF_5') = k1_relat_1('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_487,c_985])).

tff(c_989,plain,(
    k1_tarski('#skF_5') = k1_relat_1('#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_988])).

tff(c_22,plain,(
    ! [C_16] : r2_hidden(C_16,k1_tarski(C_16)) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_1090,plain,(
    r2_hidden('#skF_5',k1_relat_1('#skF_7')) ),
    inference(superposition,[status(thm),theory(equality)],[c_989,c_22])).

tff(c_54,plain,(
    ! [B_37,A_36] :
      ( k1_tarski(k1_funct_1(B_37,A_36)) = k11_relat_1(B_37,A_36)
      | ~ r2_hidden(A_36,k1_relat_1(B_37))
      | ~ v1_funct_1(B_37)
      | ~ v1_relat_1(B_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_1127,plain,
    ( k1_tarski(k1_funct_1('#skF_7','#skF_5')) = k11_relat_1('#skF_7','#skF_5')
    | ~ v1_funct_1('#skF_7')
    | ~ v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_1090,c_54])).

tff(c_1132,plain,(
    k1_tarski(k1_funct_1('#skF_7','#skF_5')) = k2_relat_1('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_245,c_86,c_373,c_1127])).

tff(c_319,plain,(
    ! [C_108,B_109,A_110] :
      ( r2_hidden(C_108,B_109)
      | ~ r2_hidden(C_108,A_110)
      | ~ r1_tarski(A_110,B_109) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_328,plain,(
    ! [C_16,B_109] :
      ( r2_hidden(C_16,B_109)
      | ~ r1_tarski(k1_tarski(C_16),B_109) ) ),
    inference(resolution,[status(thm)],[c_22,c_319])).

tff(c_1836,plain,(
    ! [B_236] :
      ( r2_hidden(k1_funct_1('#skF_7','#skF_5'),B_236)
      | ~ r1_tarski(k2_relat_1('#skF_7'),B_236) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1132,c_328])).

tff(c_78,plain,(
    ~ r2_hidden(k1_funct_1('#skF_7','#skF_5'),'#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_1870,plain,(
    ~ r1_tarski(k2_relat_1('#skF_7'),'#skF_6') ),
    inference(resolution,[status(thm)],[c_1836,c_78])).

tff(c_1873,plain,
    ( ~ v5_relat_1('#skF_7','#skF_6')
    | ~ v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_44,c_1870])).

tff(c_1877,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_245,c_250,c_1873])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.36  % Computer   : n006.cluster.edu
% 0.14/0.36  % Model      : x86_64 x86_64
% 0.14/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.36  % Memory     : 8042.1875MB
% 0.14/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.36  % CPULimit   : 60
% 0.14/0.36  % DateTime   : Tue Dec  1 09:41:52 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.22/0.37  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.84/1.67  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.84/1.67  
% 3.84/1.67  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.84/1.67  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k9_relat_1 > k7_relat_1 > k4_xboole_0 > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > k11_relat_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_4 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_1
% 3.84/1.67  
% 3.84/1.67  %Foreground sorts:
% 3.84/1.67  
% 3.84/1.67  
% 3.84/1.67  %Background operators:
% 3.84/1.67  
% 3.84/1.67  
% 3.84/1.67  %Foreground operators:
% 3.84/1.67  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.84/1.67  tff('#skF_4', type, '#skF_4': $i > $i).
% 3.84/1.67  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.84/1.67  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.84/1.67  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.84/1.67  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.84/1.67  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 3.84/1.67  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.84/1.67  tff('#skF_7', type, '#skF_7': $i).
% 3.84/1.67  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 3.84/1.67  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.84/1.67  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.84/1.67  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.84/1.67  tff('#skF_5', type, '#skF_5': $i).
% 3.84/1.67  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.84/1.67  tff(k11_relat_1, type, k11_relat_1: ($i * $i) > $i).
% 3.84/1.67  tff('#skF_6', type, '#skF_6': $i).
% 3.84/1.67  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.84/1.67  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 3.84/1.67  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.84/1.67  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.84/1.67  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.84/1.67  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.84/1.67  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.84/1.67  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.84/1.67  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.84/1.67  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.84/1.67  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.84/1.67  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.84/1.67  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.84/1.67  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.84/1.67  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.84/1.67  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.84/1.67  
% 4.06/1.69  tff(f_78, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 4.06/1.69  tff(f_167, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, k1_tarski(A), B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A), B)))) => (~(B = k1_xboole_0) => r2_hidden(k1_funct_1(C, A), B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t61_funct_2)).
% 4.06/1.69  tff(f_65, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 4.06/1.69  tff(f_112, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 4.06/1.69  tff(f_76, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 4.06/1.69  tff(f_98, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t209_relat_1)).
% 4.06/1.69  tff(f_82, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_relat_1)).
% 4.06/1.69  tff(f_70, axiom, (![A]: (v1_relat_1(A) => (![B]: (k11_relat_1(A, B) = k9_relat_1(A, k1_tarski(B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d16_relat_1)).
% 4.06/1.69  tff(f_116, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 4.06/1.69  tff(f_155, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 4.06/1.69  tff(f_51, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 4.06/1.69  tff(f_106, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r2_hidden(A, k1_relat_1(B)) => (k11_relat_1(B, A) = k1_tarski(k1_funct_1(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t117_funct_1)).
% 4.06/1.69  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 4.06/1.69  tff(c_46, plain, (![A_28, B_29]: (v1_relat_1(k2_zfmisc_1(A_28, B_29)))), inference(cnfTransformation, [status(thm)], [f_78])).
% 4.06/1.69  tff(c_82, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_5'), '#skF_6')))), inference(cnfTransformation, [status(thm)], [f_167])).
% 4.06/1.69  tff(c_239, plain, (![B_93, A_94]: (v1_relat_1(B_93) | ~m1_subset_1(B_93, k1_zfmisc_1(A_94)) | ~v1_relat_1(A_94))), inference(cnfTransformation, [status(thm)], [f_65])).
% 4.06/1.69  tff(c_242, plain, (v1_relat_1('#skF_7') | ~v1_relat_1(k2_zfmisc_1(k1_tarski('#skF_5'), '#skF_6'))), inference(resolution, [status(thm)], [c_82, c_239])).
% 4.06/1.69  tff(c_245, plain, (v1_relat_1('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_242])).
% 4.06/1.69  tff(c_246, plain, (![C_95, B_96, A_97]: (v5_relat_1(C_95, B_96) | ~m1_subset_1(C_95, k1_zfmisc_1(k2_zfmisc_1(A_97, B_96))))), inference(cnfTransformation, [status(thm)], [f_112])).
% 4.06/1.69  tff(c_250, plain, (v5_relat_1('#skF_7', '#skF_6')), inference(resolution, [status(thm)], [c_82, c_246])).
% 4.06/1.69  tff(c_44, plain, (![B_27, A_26]: (r1_tarski(k2_relat_1(B_27), A_26) | ~v5_relat_1(B_27, A_26) | ~v1_relat_1(B_27))), inference(cnfTransformation, [status(thm)], [f_76])).
% 4.06/1.69  tff(c_86, plain, (v1_funct_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_167])).
% 4.06/1.69  tff(c_336, plain, (![C_113, A_114, B_115]: (v4_relat_1(C_113, A_114) | ~m1_subset_1(C_113, k1_zfmisc_1(k2_zfmisc_1(A_114, B_115))))), inference(cnfTransformation, [status(thm)], [f_112])).
% 4.06/1.69  tff(c_340, plain, (v4_relat_1('#skF_7', k1_tarski('#skF_5'))), inference(resolution, [status(thm)], [c_82, c_336])).
% 4.06/1.69  tff(c_52, plain, (![B_35, A_34]: (k7_relat_1(B_35, A_34)=B_35 | ~v4_relat_1(B_35, A_34) | ~v1_relat_1(B_35))), inference(cnfTransformation, [status(thm)], [f_98])).
% 4.06/1.69  tff(c_350, plain, (k7_relat_1('#skF_7', k1_tarski('#skF_5'))='#skF_7' | ~v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_340, c_52])).
% 4.06/1.69  tff(c_353, plain, (k7_relat_1('#skF_7', k1_tarski('#skF_5'))='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_245, c_350])).
% 4.06/1.69  tff(c_48, plain, (![B_31, A_30]: (k2_relat_1(k7_relat_1(B_31, A_30))=k9_relat_1(B_31, A_30) | ~v1_relat_1(B_31))), inference(cnfTransformation, [status(thm)], [f_82])).
% 4.06/1.69  tff(c_357, plain, (k9_relat_1('#skF_7', k1_tarski('#skF_5'))=k2_relat_1('#skF_7') | ~v1_relat_1('#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_353, c_48])).
% 4.06/1.69  tff(c_361, plain, (k9_relat_1('#skF_7', k1_tarski('#skF_5'))=k2_relat_1('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_245, c_357])).
% 4.06/1.69  tff(c_40, plain, (![A_23, B_25]: (k9_relat_1(A_23, k1_tarski(B_25))=k11_relat_1(A_23, B_25) | ~v1_relat_1(A_23))), inference(cnfTransformation, [status(thm)], [f_70])).
% 4.06/1.69  tff(c_366, plain, (k11_relat_1('#skF_7', '#skF_5')=k2_relat_1('#skF_7') | ~v1_relat_1('#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_361, c_40])).
% 4.06/1.69  tff(c_373, plain, (k11_relat_1('#skF_7', '#skF_5')=k2_relat_1('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_245, c_366])).
% 4.06/1.69  tff(c_80, plain, (k1_xboole_0!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_167])).
% 4.06/1.69  tff(c_84, plain, (v1_funct_2('#skF_7', k1_tarski('#skF_5'), '#skF_6')), inference(cnfTransformation, [status(thm)], [f_167])).
% 4.06/1.69  tff(c_483, plain, (![A_133, B_134, C_135]: (k1_relset_1(A_133, B_134, C_135)=k1_relat_1(C_135) | ~m1_subset_1(C_135, k1_zfmisc_1(k2_zfmisc_1(A_133, B_134))))), inference(cnfTransformation, [status(thm)], [f_116])).
% 4.06/1.69  tff(c_487, plain, (k1_relset_1(k1_tarski('#skF_5'), '#skF_6', '#skF_7')=k1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_82, c_483])).
% 4.06/1.69  tff(c_982, plain, (![B_203, A_204, C_205]: (k1_xboole_0=B_203 | k1_relset_1(A_204, B_203, C_205)=A_204 | ~v1_funct_2(C_205, A_204, B_203) | ~m1_subset_1(C_205, k1_zfmisc_1(k2_zfmisc_1(A_204, B_203))))), inference(cnfTransformation, [status(thm)], [f_155])).
% 4.06/1.69  tff(c_985, plain, (k1_xboole_0='#skF_6' | k1_relset_1(k1_tarski('#skF_5'), '#skF_6', '#skF_7')=k1_tarski('#skF_5') | ~v1_funct_2('#skF_7', k1_tarski('#skF_5'), '#skF_6')), inference(resolution, [status(thm)], [c_82, c_982])).
% 4.06/1.69  tff(c_988, plain, (k1_xboole_0='#skF_6' | k1_tarski('#skF_5')=k1_relat_1('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_84, c_487, c_985])).
% 4.06/1.69  tff(c_989, plain, (k1_tarski('#skF_5')=k1_relat_1('#skF_7')), inference(negUnitSimplification, [status(thm)], [c_80, c_988])).
% 4.06/1.69  tff(c_22, plain, (![C_16]: (r2_hidden(C_16, k1_tarski(C_16)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 4.06/1.69  tff(c_1090, plain, (r2_hidden('#skF_5', k1_relat_1('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_989, c_22])).
% 4.06/1.69  tff(c_54, plain, (![B_37, A_36]: (k1_tarski(k1_funct_1(B_37, A_36))=k11_relat_1(B_37, A_36) | ~r2_hidden(A_36, k1_relat_1(B_37)) | ~v1_funct_1(B_37) | ~v1_relat_1(B_37))), inference(cnfTransformation, [status(thm)], [f_106])).
% 4.06/1.69  tff(c_1127, plain, (k1_tarski(k1_funct_1('#skF_7', '#skF_5'))=k11_relat_1('#skF_7', '#skF_5') | ~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_1090, c_54])).
% 4.06/1.69  tff(c_1132, plain, (k1_tarski(k1_funct_1('#skF_7', '#skF_5'))=k2_relat_1('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_245, c_86, c_373, c_1127])).
% 4.06/1.69  tff(c_319, plain, (![C_108, B_109, A_110]: (r2_hidden(C_108, B_109) | ~r2_hidden(C_108, A_110) | ~r1_tarski(A_110, B_109))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.06/1.69  tff(c_328, plain, (![C_16, B_109]: (r2_hidden(C_16, B_109) | ~r1_tarski(k1_tarski(C_16), B_109))), inference(resolution, [status(thm)], [c_22, c_319])).
% 4.06/1.69  tff(c_1836, plain, (![B_236]: (r2_hidden(k1_funct_1('#skF_7', '#skF_5'), B_236) | ~r1_tarski(k2_relat_1('#skF_7'), B_236))), inference(superposition, [status(thm), theory('equality')], [c_1132, c_328])).
% 4.06/1.69  tff(c_78, plain, (~r2_hidden(k1_funct_1('#skF_7', '#skF_5'), '#skF_6')), inference(cnfTransformation, [status(thm)], [f_167])).
% 4.06/1.69  tff(c_1870, plain, (~r1_tarski(k2_relat_1('#skF_7'), '#skF_6')), inference(resolution, [status(thm)], [c_1836, c_78])).
% 4.06/1.69  tff(c_1873, plain, (~v5_relat_1('#skF_7', '#skF_6') | ~v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_44, c_1870])).
% 4.06/1.69  tff(c_1877, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_245, c_250, c_1873])).
% 4.06/1.69  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.06/1.69  
% 4.06/1.69  Inference rules
% 4.06/1.69  ----------------------
% 4.06/1.69  #Ref     : 0
% 4.06/1.69  #Sup     : 410
% 4.06/1.69  #Fact    : 0
% 4.06/1.69  #Define  : 0
% 4.06/1.69  #Split   : 0
% 4.06/1.69  #Chain   : 0
% 4.06/1.69  #Close   : 0
% 4.06/1.69  
% 4.06/1.69  Ordering : KBO
% 4.06/1.69  
% 4.06/1.69  Simplification rules
% 4.06/1.69  ----------------------
% 4.06/1.69  #Subsume      : 31
% 4.06/1.69  #Demod        : 222
% 4.06/1.69  #Tautology    : 174
% 4.06/1.69  #SimpNegUnit  : 39
% 4.06/1.69  #BackRed      : 8
% 4.06/1.69  
% 4.06/1.69  #Partial instantiations: 0
% 4.06/1.69  #Strategies tried      : 1
% 4.06/1.69  
% 4.06/1.69  Timing (in seconds)
% 4.06/1.69  ----------------------
% 4.06/1.69  Preprocessing        : 0.36
% 4.06/1.69  Parsing              : 0.18
% 4.06/1.69  CNF conversion       : 0.03
% 4.06/1.69  Main loop            : 0.55
% 4.06/1.69  Inferencing          : 0.19
% 4.06/1.69  Reduction            : 0.18
% 4.06/1.69  Demodulation         : 0.12
% 4.06/1.69  BG Simplification    : 0.03
% 4.06/1.69  Subsumption          : 0.11
% 4.06/1.69  Abstraction          : 0.03
% 4.06/1.69  MUC search           : 0.00
% 4.06/1.69  Cooper               : 0.00
% 4.06/1.69  Total                : 0.94
% 4.06/1.69  Index Insertion      : 0.00
% 4.06/1.69  Index Deletion       : 0.00
% 4.06/1.69  Index Matching       : 0.00
% 4.06/1.69  BG Taut test         : 0.00
%------------------------------------------------------------------------------
