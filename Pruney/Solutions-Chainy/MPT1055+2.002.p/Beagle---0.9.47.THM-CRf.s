%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:17:18 EST 2020

% Result     : Theorem 36.37s
% Output     : CNFRefutation 36.37s
% Verified   : 
% Statistics : Number of formulae       :  148 ( 365 expanded)
%              Number of leaves         :   48 ( 146 expanded)
%              Depth                    :   10
%              Number of atoms          :  215 ( 986 expanded)
%              Number of equality atoms :   56 ( 157 expanded)
%              Maximal formula depth    :   13 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k8_relset_1 > k7_relset_1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k2_zfmisc_1 > k2_xboole_0 > k10_relat_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_7 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k8_relset_1,type,(
    k8_relset_1: ( $i * $i * $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

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

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_188,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B] :
            ( ~ v1_xboole_0(B)
           => ! [C] :
                ( ( v1_funct_1(C)
                  & v1_funct_2(C,A,B)
                  & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
               => ! [D] :
                    ( m1_subset_1(D,k1_zfmisc_1(A))
                   => ! [E] :
                        ( m1_subset_1(E,k1_zfmisc_1(B))
                       => ( r1_tarski(k7_relset_1(A,B,C,D),E)
                        <=> r1_tarski(D,k8_relset_1(A,B,C,E)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t172_funct_2)).

tff(f_41,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_145,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k8_relset_1(A,B,C,D) = k10_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

tff(f_137,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_151,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( k7_relset_1(A,B,C,A) = k2_relset_1(A,B,C)
        & k8_relset_1(A,B,C,B) = k1_relset_1(A,B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_relset_1)).

tff(f_163,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( ( B = k1_xboole_0
         => A = k1_xboole_0 )
       => k8_relset_1(A,B,C,B) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_funct_2)).

tff(f_82,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_49,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_xboole_0(A,B),C)
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_xboole_1)).

tff(f_127,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_103,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r1_tarski(A,B)
       => r1_tarski(k9_relat_1(C,A),k9_relat_1(C,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t156_relat_1)).

tff(f_113,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => r1_tarski(k9_relat_1(B,k10_relat_1(B,A)),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t145_funct_1)).

tff(f_55,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_141,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_123,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( ( r1_tarski(A,k1_relat_1(C))
          & r1_tarski(k9_relat_1(C,A),B) )
       => r1_tarski(A,k10_relat_1(C,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t163_funct_1)).

tff(f_61,axiom,(
    ! [A] :
      ( r1_tarski(A,k1_xboole_0)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).

tff(f_35,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(c_90,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_188])).

tff(c_16,plain,(
    ! [B_9] : r1_tarski(B_9,B_9) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_88,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_188])).

tff(c_86,plain,(
    v1_funct_2('#skF_5','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_188])).

tff(c_84,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_188])).

tff(c_132871,plain,(
    ! [A_2915,B_2916,C_2917,D_2918] :
      ( k8_relset_1(A_2915,B_2916,C_2917,D_2918) = k10_relat_1(C_2917,D_2918)
      | ~ m1_subset_1(C_2917,k1_zfmisc_1(k2_zfmisc_1(A_2915,B_2916))) ) ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_132889,plain,(
    ! [D_2918] : k8_relset_1('#skF_3','#skF_4','#skF_5',D_2918) = k10_relat_1('#skF_5',D_2918) ),
    inference(resolution,[status(thm)],[c_84,c_132871])).

tff(c_132328,plain,(
    ! [A_2887,B_2888,C_2889] :
      ( k1_relset_1(A_2887,B_2888,C_2889) = k1_relat_1(C_2889)
      | ~ m1_subset_1(C_2889,k1_zfmisc_1(k2_zfmisc_1(A_2887,B_2888))) ) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_132352,plain,(
    k1_relset_1('#skF_3','#skF_4','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_84,c_132328])).

tff(c_132911,plain,(
    ! [A_2920,B_2921,C_2922] :
      ( k8_relset_1(A_2920,B_2921,C_2922,B_2921) = k1_relset_1(A_2920,B_2921,C_2922)
      | ~ m1_subset_1(C_2922,k1_zfmisc_1(k2_zfmisc_1(A_2920,B_2921))) ) ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_132919,plain,(
    k8_relset_1('#skF_3','#skF_4','#skF_5','#skF_4') = k1_relset_1('#skF_3','#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_84,c_132911])).

tff(c_132930,plain,(
    k10_relat_1('#skF_5','#skF_4') = k1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_132889,c_132352,c_132919])).

tff(c_133794,plain,(
    ! [B_2948,A_2949,C_2950] :
      ( k1_xboole_0 = B_2948
      | k8_relset_1(A_2949,B_2948,C_2950,B_2948) = A_2949
      | ~ m1_subset_1(C_2950,k1_zfmisc_1(k2_zfmisc_1(A_2949,B_2948)))
      | ~ v1_funct_2(C_2950,A_2949,B_2948)
      | ~ v1_funct_1(C_2950) ) ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_133802,plain,
    ( k1_xboole_0 = '#skF_4'
    | k8_relset_1('#skF_3','#skF_4','#skF_5','#skF_4') = '#skF_3'
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_84,c_133794])).

tff(c_133814,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relat_1('#skF_5') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_86,c_132930,c_132889,c_133802])).

tff(c_133823,plain,(
    k1_relat_1('#skF_5') = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_133814])).

tff(c_82,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_188])).

tff(c_126304,plain,(
    ! [A_2611,B_2612] :
      ( r1_tarski(A_2611,B_2612)
      | ~ m1_subset_1(A_2611,k1_zfmisc_1(B_2612)) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_126320,plain,(
    r1_tarski('#skF_6','#skF_3') ),
    inference(resolution,[status(thm)],[c_82,c_126304])).

tff(c_126328,plain,(
    ! [A_2614,B_2615] :
      ( k2_xboole_0(A_2614,B_2615) = B_2615
      | ~ r1_tarski(A_2614,B_2615) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_126358,plain,(
    k2_xboole_0('#skF_6','#skF_3') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_126320,c_126328])).

tff(c_130495,plain,(
    ! [A_2797,C_2798,B_2799] :
      ( r1_tarski(A_2797,C_2798)
      | ~ r1_tarski(k2_xboole_0(A_2797,B_2799),C_2798) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_130540,plain,(
    ! [C_2800] :
      ( r1_tarski('#skF_6',C_2800)
      | ~ r1_tarski('#skF_3',C_2800) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_126358,c_130495])).

tff(c_80,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_188])).

tff(c_126319,plain,(
    r1_tarski('#skF_7','#skF_4') ),
    inference(resolution,[status(thm)],[c_80,c_126304])).

tff(c_126603,plain,(
    ! [B_2621,A_2622] :
      ( B_2621 = A_2622
      | ~ r1_tarski(B_2621,A_2622)
      | ~ r1_tarski(A_2622,B_2621) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_126625,plain,
    ( '#skF_7' = '#skF_4'
    | ~ r1_tarski('#skF_4','#skF_7') ),
    inference(resolution,[status(thm)],[c_126319,c_126603])).

tff(c_126636,plain,(
    ~ r1_tarski('#skF_4','#skF_7') ),
    inference(splitLeft,[status(thm)],[c_126625])).

tff(c_129469,plain,(
    ! [A_2751,B_2752,C_2753,D_2754] :
      ( k8_relset_1(A_2751,B_2752,C_2753,D_2754) = k10_relat_1(C_2753,D_2754)
      | ~ m1_subset_1(C_2753,k1_zfmisc_1(k2_zfmisc_1(A_2751,B_2752))) ) ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_129487,plain,(
    ! [D_2754] : k8_relset_1('#skF_3','#skF_4','#skF_5',D_2754) = k10_relat_1('#skF_5',D_2754) ),
    inference(resolution,[status(thm)],[c_84,c_129469])).

tff(c_129110,plain,(
    ! [A_2736,B_2737,C_2738] :
      ( k1_relset_1(A_2736,B_2737,C_2738) = k1_relat_1(C_2738)
      | ~ m1_subset_1(C_2738,k1_zfmisc_1(k2_zfmisc_1(A_2736,B_2737))) ) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_129134,plain,(
    k1_relset_1('#skF_3','#skF_4','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_84,c_129110])).

tff(c_129561,plain,(
    ! [A_2757,B_2758,C_2759] :
      ( k8_relset_1(A_2757,B_2758,C_2759,B_2758) = k1_relset_1(A_2757,B_2758,C_2759)
      | ~ m1_subset_1(C_2759,k1_zfmisc_1(k2_zfmisc_1(A_2757,B_2758))) ) ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_129569,plain,(
    k8_relset_1('#skF_3','#skF_4','#skF_5','#skF_4') = k1_relset_1('#skF_3','#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_84,c_129561])).

tff(c_129580,plain,(
    k10_relat_1('#skF_5','#skF_4') = k1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_129487,c_129134,c_129569])).

tff(c_130187,plain,(
    ! [B_2774,A_2775,C_2776] :
      ( k1_xboole_0 = B_2774
      | k8_relset_1(A_2775,B_2774,C_2776,B_2774) = A_2775
      | ~ m1_subset_1(C_2776,k1_zfmisc_1(k2_zfmisc_1(A_2775,B_2774)))
      | ~ v1_funct_2(C_2776,A_2775,B_2774)
      | ~ v1_funct_1(C_2776) ) ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_130195,plain,
    ( k1_xboole_0 = '#skF_4'
    | k8_relset_1('#skF_3','#skF_4','#skF_5','#skF_4') = '#skF_3'
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_84,c_130187])).

tff(c_130207,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relat_1('#skF_5') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_86,c_129580,c_129487,c_130195])).

tff(c_130210,plain,(
    k1_relat_1('#skF_5') = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_130207])).

tff(c_126724,plain,(
    ! [A_2629,C_2630,B_2631] :
      ( r1_tarski(A_2629,C_2630)
      | ~ r1_tarski(k2_xboole_0(A_2629,B_2631),C_2630) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_126748,plain,(
    ! [C_2630] :
      ( r1_tarski('#skF_6',C_2630)
      | ~ r1_tarski('#skF_3',C_2630) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_126358,c_126724])).

tff(c_566,plain,(
    ! [C_125,A_126,B_127] :
      ( v1_relat_1(C_125)
      | ~ m1_subset_1(C_125,k1_zfmisc_1(k2_zfmisc_1(A_126,B_127))) ) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_583,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_84,c_566])).

tff(c_3038,plain,(
    ! [A_243,B_244,C_245,D_246] :
      ( k8_relset_1(A_243,B_244,C_245,D_246) = k10_relat_1(C_245,D_246)
      | ~ m1_subset_1(C_245,k1_zfmisc_1(k2_zfmisc_1(A_243,B_244))) ) ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_3056,plain,(
    ! [D_246] : k8_relset_1('#skF_3','#skF_4','#skF_5',D_246) = k10_relat_1('#skF_5',D_246) ),
    inference(resolution,[status(thm)],[c_84,c_3038])).

tff(c_100,plain,
    ( r1_tarski(k7_relset_1('#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_7')
    | r1_tarski('#skF_6',k8_relset_1('#skF_3','#skF_4','#skF_5','#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_188])).

tff(c_320,plain,(
    r1_tarski('#skF_6',k8_relset_1('#skF_3','#skF_4','#skF_5','#skF_7')) ),
    inference(splitLeft,[status(thm)],[c_100])).

tff(c_3106,plain,(
    r1_tarski('#skF_6',k10_relat_1('#skF_5','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3056,c_320])).

tff(c_52,plain,(
    ! [C_39,A_37,B_38] :
      ( r1_tarski(k9_relat_1(C_39,A_37),k9_relat_1(C_39,B_38))
      | ~ r1_tarski(A_37,B_38)
      | ~ v1_relat_1(C_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_2450,plain,(
    ! [B_219,A_220] :
      ( r1_tarski(k9_relat_1(B_219,k10_relat_1(B_219,A_220)),A_220)
      | ~ v1_funct_1(B_219)
      | ~ v1_relat_1(B_219) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_22,plain,(
    ! [A_15,C_17,B_16] :
      ( r1_tarski(A_15,C_17)
      | ~ r1_tarski(B_16,C_17)
      | ~ r1_tarski(A_15,B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_72133,plain,(
    ! [A_1801,A_1802,B_1803] :
      ( r1_tarski(A_1801,A_1802)
      | ~ r1_tarski(A_1801,k9_relat_1(B_1803,k10_relat_1(B_1803,A_1802)))
      | ~ v1_funct_1(B_1803)
      | ~ v1_relat_1(B_1803) ) ),
    inference(resolution,[status(thm)],[c_2450,c_22])).

tff(c_125862,plain,(
    ! [C_2604,A_2605,A_2606] :
      ( r1_tarski(k9_relat_1(C_2604,A_2605),A_2606)
      | ~ v1_funct_1(C_2604)
      | ~ r1_tarski(A_2605,k10_relat_1(C_2604,A_2606))
      | ~ v1_relat_1(C_2604) ) ),
    inference(resolution,[status(thm)],[c_52,c_72133])).

tff(c_3001,plain,(
    ! [A_238,B_239,C_240,D_241] :
      ( k7_relset_1(A_238,B_239,C_240,D_241) = k9_relat_1(C_240,D_241)
      | ~ m1_subset_1(C_240,k1_zfmisc_1(k2_zfmisc_1(A_238,B_239))) ) ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_3019,plain,(
    ! [D_241] : k7_relset_1('#skF_3','#skF_4','#skF_5',D_241) = k9_relat_1('#skF_5',D_241) ),
    inference(resolution,[status(thm)],[c_84,c_3001])).

tff(c_94,plain,
    ( ~ r1_tarski('#skF_6',k8_relset_1('#skF_3','#skF_4','#skF_5','#skF_7'))
    | ~ r1_tarski(k7_relset_1('#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_188])).

tff(c_196,plain,(
    ~ r1_tarski(k7_relset_1('#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_7') ),
    inference(splitLeft,[status(thm)],[c_94])).

tff(c_3024,plain,(
    ~ r1_tarski(k9_relat_1('#skF_5','#skF_6'),'#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3019,c_196])).

tff(c_126021,plain,
    ( ~ v1_funct_1('#skF_5')
    | ~ r1_tarski('#skF_6',k10_relat_1('#skF_5','#skF_7'))
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_125862,c_3024])).

tff(c_126095,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_583,c_3106,c_88,c_126021])).

tff(c_126096,plain,(
    r1_tarski(k7_relset_1('#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_7') ),
    inference(splitRight,[status(thm)],[c_100])).

tff(c_126298,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_126096,c_196])).

tff(c_126299,plain,(
    ~ r1_tarski('#skF_6',k8_relset_1('#skF_3','#skF_4','#skF_5','#skF_7')) ),
    inference(splitRight,[status(thm)],[c_94])).

tff(c_129494,plain,(
    ~ r1_tarski('#skF_6',k10_relat_1('#skF_5','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_129487,c_126299])).

tff(c_126825,plain,(
    ! [C_2634,A_2635,B_2636] :
      ( v1_relat_1(C_2634)
      | ~ m1_subset_1(C_2634,k1_zfmisc_1(k2_zfmisc_1(A_2635,B_2636))) ) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_126842,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_84,c_126825])).

tff(c_129148,plain,(
    ! [A_2739,B_2740,C_2741,D_2742] :
      ( k7_relset_1(A_2739,B_2740,C_2741,D_2742) = k9_relat_1(C_2741,D_2742)
      | ~ m1_subset_1(C_2741,k1_zfmisc_1(k2_zfmisc_1(A_2739,B_2740))) ) ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_129166,plain,(
    ! [D_2742] : k7_relset_1('#skF_3','#skF_4','#skF_5',D_2742) = k9_relat_1('#skF_5',D_2742) ),
    inference(resolution,[status(thm)],[c_84,c_129148])).

tff(c_126300,plain,(
    r1_tarski(k7_relset_1('#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_7') ),
    inference(splitRight,[status(thm)],[c_94])).

tff(c_129421,plain,(
    r1_tarski(k9_relat_1('#skF_5','#skF_6'),'#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_129166,c_126300])).

tff(c_130046,plain,(
    ! [A_2771,C_2772,B_2773] :
      ( r1_tarski(A_2771,k10_relat_1(C_2772,B_2773))
      | ~ r1_tarski(k9_relat_1(C_2772,A_2771),B_2773)
      | ~ r1_tarski(A_2771,k1_relat_1(C_2772))
      | ~ v1_funct_1(C_2772)
      | ~ v1_relat_1(C_2772) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_130061,plain,
    ( r1_tarski('#skF_6',k10_relat_1('#skF_5','#skF_7'))
    | ~ r1_tarski('#skF_6',k1_relat_1('#skF_5'))
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_129421,c_130046])).

tff(c_130118,plain,
    ( r1_tarski('#skF_6',k10_relat_1('#skF_5','#skF_7'))
    | ~ r1_tarski('#skF_6',k1_relat_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_126842,c_88,c_130061])).

tff(c_130119,plain,(
    ~ r1_tarski('#skF_6',k1_relat_1('#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_129494,c_130118])).

tff(c_130135,plain,(
    ~ r1_tarski('#skF_3',k1_relat_1('#skF_5')) ),
    inference(resolution,[status(thm)],[c_126748,c_130119])).

tff(c_130212,plain,(
    ~ r1_tarski('#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_130210,c_130135])).

tff(c_130220,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_130212])).

tff(c_130221,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_130207])).

tff(c_126359,plain,(
    k2_xboole_0('#skF_7','#skF_4') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_126319,c_126328])).

tff(c_126793,plain,(
    ! [C_2632] :
      ( r1_tarski('#skF_7',C_2632)
      | ~ r1_tarski('#skF_4',C_2632) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_126359,c_126724])).

tff(c_26,plain,(
    ! [A_19] :
      ( k1_xboole_0 = A_19
      | ~ r1_tarski(A_19,k1_xboole_0) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_126805,plain,
    ( k1_xboole_0 = '#skF_7'
    | ~ r1_tarski('#skF_4',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_126793,c_26])).

tff(c_126806,plain,(
    ~ r1_tarski('#skF_4',k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_126805])).

tff(c_130239,plain,(
    ~ r1_tarski('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_130221,c_126806])).

tff(c_130252,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_130239])).

tff(c_130253,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_126805])).

tff(c_130254,plain,(
    r1_tarski('#skF_4',k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_126805])).

tff(c_130270,plain,(
    r1_tarski('#skF_4','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_130253,c_130254])).

tff(c_130271,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_126636,c_130270])).

tff(c_130272,plain,(
    '#skF_7' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_126625])).

tff(c_130278,plain,(
    ~ r1_tarski('#skF_6',k8_relset_1('#skF_3','#skF_4','#skF_5','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_130272,c_126299])).

tff(c_130563,plain,(
    ~ r1_tarski('#skF_3',k8_relset_1('#skF_3','#skF_4','#skF_5','#skF_4')) ),
    inference(resolution,[status(thm)],[c_130540,c_130278])).

tff(c_132894,plain,(
    ~ r1_tarski('#skF_3',k10_relat_1('#skF_5','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_132889,c_130563])).

tff(c_132932,plain,(
    ~ r1_tarski('#skF_3',k1_relat_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_132930,c_132894])).

tff(c_133827,plain,(
    ~ r1_tarski('#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_133823,c_132932])).

tff(c_133833,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_133827])).

tff(c_133834,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_133814])).

tff(c_10,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_133864,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_133834,c_10])).

tff(c_133867,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_90,c_133864])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:24:25 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 36.37/23.08  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 36.37/23.10  
% 36.37/23.10  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 36.37/23.10  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k8_relset_1 > k7_relset_1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k2_zfmisc_1 > k2_xboole_0 > k10_relat_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_7 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_1
% 36.37/23.10  
% 36.37/23.10  %Foreground sorts:
% 36.37/23.10  
% 36.37/23.10  
% 36.37/23.10  %Background operators:
% 36.37/23.10  
% 36.37/23.10  
% 36.37/23.10  %Foreground operators:
% 36.37/23.10  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 36.37/23.10  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 36.37/23.10  tff('#skF_2', type, '#skF_2': $i > $i).
% 36.37/23.10  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 36.37/23.10  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 36.37/23.10  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 36.37/23.10  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 36.37/23.10  tff('#skF_7', type, '#skF_7': $i).
% 36.37/23.10  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 36.37/23.10  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 36.37/23.10  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 36.37/23.10  tff('#skF_5', type, '#skF_5': $i).
% 36.37/23.10  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 36.37/23.10  tff('#skF_6', type, '#skF_6': $i).
% 36.37/23.10  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 36.37/23.10  tff('#skF_3', type, '#skF_3': $i).
% 36.37/23.10  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 36.37/23.10  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 36.37/23.10  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 36.37/23.10  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 36.37/23.10  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 36.37/23.10  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 36.37/23.10  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 36.37/23.10  tff('#skF_4', type, '#skF_4': $i).
% 36.37/23.10  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 36.37/23.10  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 36.37/23.10  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 36.37/23.10  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 36.37/23.10  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 36.37/23.10  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 36.37/23.10  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 36.37/23.10  
% 36.37/23.12  tff(f_188, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (m1_subset_1(D, k1_zfmisc_1(A)) => (![E]: (m1_subset_1(E, k1_zfmisc_1(B)) => (r1_tarski(k7_relset_1(A, B, C, D), E) <=> r1_tarski(D, k8_relset_1(A, B, C, E))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t172_funct_2)).
% 36.37/23.12  tff(f_41, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 36.37/23.12  tff(f_145, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k8_relset_1(A, B, C, D) = k10_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k8_relset_1)).
% 36.37/23.12  tff(f_137, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 36.37/23.12  tff(f_151, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((k7_relset_1(A, B, C, A) = k2_relset_1(A, B, C)) & (k8_relset_1(A, B, C, B) = k1_relset_1(A, B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_relset_1)).
% 36.37/23.12  tff(f_163, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((B = k1_xboole_0) => (A = k1_xboole_0)) => (k8_relset_1(A, B, C, B) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_funct_2)).
% 36.37/23.12  tff(f_82, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 36.37/23.12  tff(f_49, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 36.37/23.12  tff(f_45, axiom, (![A, B, C]: (r1_tarski(k2_xboole_0(A, B), C) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_xboole_1)).
% 36.37/23.12  tff(f_127, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 36.37/23.12  tff(f_103, axiom, (![A, B, C]: (v1_relat_1(C) => (r1_tarski(A, B) => r1_tarski(k9_relat_1(C, A), k9_relat_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t156_relat_1)).
% 36.37/23.12  tff(f_113, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => r1_tarski(k9_relat_1(B, k10_relat_1(B, A)), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t145_funct_1)).
% 36.37/23.12  tff(f_55, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 36.37/23.12  tff(f_141, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 36.37/23.12  tff(f_123, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => ((r1_tarski(A, k1_relat_1(C)) & r1_tarski(k9_relat_1(C, A), B)) => r1_tarski(A, k10_relat_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t163_funct_1)).
% 36.37/23.12  tff(f_61, axiom, (![A]: (r1_tarski(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_1)).
% 36.37/23.12  tff(f_35, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 36.37/23.12  tff(c_90, plain, (~v1_xboole_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_188])).
% 36.37/23.12  tff(c_16, plain, (![B_9]: (r1_tarski(B_9, B_9))), inference(cnfTransformation, [status(thm)], [f_41])).
% 36.37/23.12  tff(c_88, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_188])).
% 36.37/23.12  tff(c_86, plain, (v1_funct_2('#skF_5', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_188])).
% 36.37/23.12  tff(c_84, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_188])).
% 36.37/23.12  tff(c_132871, plain, (![A_2915, B_2916, C_2917, D_2918]: (k8_relset_1(A_2915, B_2916, C_2917, D_2918)=k10_relat_1(C_2917, D_2918) | ~m1_subset_1(C_2917, k1_zfmisc_1(k2_zfmisc_1(A_2915, B_2916))))), inference(cnfTransformation, [status(thm)], [f_145])).
% 36.37/23.12  tff(c_132889, plain, (![D_2918]: (k8_relset_1('#skF_3', '#skF_4', '#skF_5', D_2918)=k10_relat_1('#skF_5', D_2918))), inference(resolution, [status(thm)], [c_84, c_132871])).
% 36.37/23.12  tff(c_132328, plain, (![A_2887, B_2888, C_2889]: (k1_relset_1(A_2887, B_2888, C_2889)=k1_relat_1(C_2889) | ~m1_subset_1(C_2889, k1_zfmisc_1(k2_zfmisc_1(A_2887, B_2888))))), inference(cnfTransformation, [status(thm)], [f_137])).
% 36.37/23.12  tff(c_132352, plain, (k1_relset_1('#skF_3', '#skF_4', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_84, c_132328])).
% 36.37/23.12  tff(c_132911, plain, (![A_2920, B_2921, C_2922]: (k8_relset_1(A_2920, B_2921, C_2922, B_2921)=k1_relset_1(A_2920, B_2921, C_2922) | ~m1_subset_1(C_2922, k1_zfmisc_1(k2_zfmisc_1(A_2920, B_2921))))), inference(cnfTransformation, [status(thm)], [f_151])).
% 36.37/23.12  tff(c_132919, plain, (k8_relset_1('#skF_3', '#skF_4', '#skF_5', '#skF_4')=k1_relset_1('#skF_3', '#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_84, c_132911])).
% 36.37/23.12  tff(c_132930, plain, (k10_relat_1('#skF_5', '#skF_4')=k1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_132889, c_132352, c_132919])).
% 36.37/23.12  tff(c_133794, plain, (![B_2948, A_2949, C_2950]: (k1_xboole_0=B_2948 | k8_relset_1(A_2949, B_2948, C_2950, B_2948)=A_2949 | ~m1_subset_1(C_2950, k1_zfmisc_1(k2_zfmisc_1(A_2949, B_2948))) | ~v1_funct_2(C_2950, A_2949, B_2948) | ~v1_funct_1(C_2950))), inference(cnfTransformation, [status(thm)], [f_163])).
% 36.37/23.12  tff(c_133802, plain, (k1_xboole_0='#skF_4' | k8_relset_1('#skF_3', '#skF_4', '#skF_5', '#skF_4')='#skF_3' | ~v1_funct_2('#skF_5', '#skF_3', '#skF_4') | ~v1_funct_1('#skF_5')), inference(resolution, [status(thm)], [c_84, c_133794])).
% 36.37/23.12  tff(c_133814, plain, (k1_xboole_0='#skF_4' | k1_relat_1('#skF_5')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_88, c_86, c_132930, c_132889, c_133802])).
% 36.37/23.12  tff(c_133823, plain, (k1_relat_1('#skF_5')='#skF_3'), inference(splitLeft, [status(thm)], [c_133814])).
% 36.37/23.12  tff(c_82, plain, (m1_subset_1('#skF_6', k1_zfmisc_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_188])).
% 36.37/23.12  tff(c_126304, plain, (![A_2611, B_2612]: (r1_tarski(A_2611, B_2612) | ~m1_subset_1(A_2611, k1_zfmisc_1(B_2612)))), inference(cnfTransformation, [status(thm)], [f_82])).
% 36.37/23.12  tff(c_126320, plain, (r1_tarski('#skF_6', '#skF_3')), inference(resolution, [status(thm)], [c_82, c_126304])).
% 36.37/23.12  tff(c_126328, plain, (![A_2614, B_2615]: (k2_xboole_0(A_2614, B_2615)=B_2615 | ~r1_tarski(A_2614, B_2615))), inference(cnfTransformation, [status(thm)], [f_49])).
% 36.37/23.12  tff(c_126358, plain, (k2_xboole_0('#skF_6', '#skF_3')='#skF_3'), inference(resolution, [status(thm)], [c_126320, c_126328])).
% 36.37/23.12  tff(c_130495, plain, (![A_2797, C_2798, B_2799]: (r1_tarski(A_2797, C_2798) | ~r1_tarski(k2_xboole_0(A_2797, B_2799), C_2798))), inference(cnfTransformation, [status(thm)], [f_45])).
% 36.37/23.12  tff(c_130540, plain, (![C_2800]: (r1_tarski('#skF_6', C_2800) | ~r1_tarski('#skF_3', C_2800))), inference(superposition, [status(thm), theory('equality')], [c_126358, c_130495])).
% 36.37/23.12  tff(c_80, plain, (m1_subset_1('#skF_7', k1_zfmisc_1('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_188])).
% 36.37/23.12  tff(c_126319, plain, (r1_tarski('#skF_7', '#skF_4')), inference(resolution, [status(thm)], [c_80, c_126304])).
% 36.37/23.12  tff(c_126603, plain, (![B_2621, A_2622]: (B_2621=A_2622 | ~r1_tarski(B_2621, A_2622) | ~r1_tarski(A_2622, B_2621))), inference(cnfTransformation, [status(thm)], [f_41])).
% 36.37/23.12  tff(c_126625, plain, ('#skF_7'='#skF_4' | ~r1_tarski('#skF_4', '#skF_7')), inference(resolution, [status(thm)], [c_126319, c_126603])).
% 36.37/23.12  tff(c_126636, plain, (~r1_tarski('#skF_4', '#skF_7')), inference(splitLeft, [status(thm)], [c_126625])).
% 36.37/23.12  tff(c_129469, plain, (![A_2751, B_2752, C_2753, D_2754]: (k8_relset_1(A_2751, B_2752, C_2753, D_2754)=k10_relat_1(C_2753, D_2754) | ~m1_subset_1(C_2753, k1_zfmisc_1(k2_zfmisc_1(A_2751, B_2752))))), inference(cnfTransformation, [status(thm)], [f_145])).
% 36.37/23.12  tff(c_129487, plain, (![D_2754]: (k8_relset_1('#skF_3', '#skF_4', '#skF_5', D_2754)=k10_relat_1('#skF_5', D_2754))), inference(resolution, [status(thm)], [c_84, c_129469])).
% 36.37/23.12  tff(c_129110, plain, (![A_2736, B_2737, C_2738]: (k1_relset_1(A_2736, B_2737, C_2738)=k1_relat_1(C_2738) | ~m1_subset_1(C_2738, k1_zfmisc_1(k2_zfmisc_1(A_2736, B_2737))))), inference(cnfTransformation, [status(thm)], [f_137])).
% 36.37/23.12  tff(c_129134, plain, (k1_relset_1('#skF_3', '#skF_4', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_84, c_129110])).
% 36.37/23.12  tff(c_129561, plain, (![A_2757, B_2758, C_2759]: (k8_relset_1(A_2757, B_2758, C_2759, B_2758)=k1_relset_1(A_2757, B_2758, C_2759) | ~m1_subset_1(C_2759, k1_zfmisc_1(k2_zfmisc_1(A_2757, B_2758))))), inference(cnfTransformation, [status(thm)], [f_151])).
% 36.37/23.12  tff(c_129569, plain, (k8_relset_1('#skF_3', '#skF_4', '#skF_5', '#skF_4')=k1_relset_1('#skF_3', '#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_84, c_129561])).
% 36.37/23.12  tff(c_129580, plain, (k10_relat_1('#skF_5', '#skF_4')=k1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_129487, c_129134, c_129569])).
% 36.37/23.12  tff(c_130187, plain, (![B_2774, A_2775, C_2776]: (k1_xboole_0=B_2774 | k8_relset_1(A_2775, B_2774, C_2776, B_2774)=A_2775 | ~m1_subset_1(C_2776, k1_zfmisc_1(k2_zfmisc_1(A_2775, B_2774))) | ~v1_funct_2(C_2776, A_2775, B_2774) | ~v1_funct_1(C_2776))), inference(cnfTransformation, [status(thm)], [f_163])).
% 36.37/23.12  tff(c_130195, plain, (k1_xboole_0='#skF_4' | k8_relset_1('#skF_3', '#skF_4', '#skF_5', '#skF_4')='#skF_3' | ~v1_funct_2('#skF_5', '#skF_3', '#skF_4') | ~v1_funct_1('#skF_5')), inference(resolution, [status(thm)], [c_84, c_130187])).
% 36.37/23.12  tff(c_130207, plain, (k1_xboole_0='#skF_4' | k1_relat_1('#skF_5')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_88, c_86, c_129580, c_129487, c_130195])).
% 36.37/23.12  tff(c_130210, plain, (k1_relat_1('#skF_5')='#skF_3'), inference(splitLeft, [status(thm)], [c_130207])).
% 36.37/23.12  tff(c_126724, plain, (![A_2629, C_2630, B_2631]: (r1_tarski(A_2629, C_2630) | ~r1_tarski(k2_xboole_0(A_2629, B_2631), C_2630))), inference(cnfTransformation, [status(thm)], [f_45])).
% 36.37/23.12  tff(c_126748, plain, (![C_2630]: (r1_tarski('#skF_6', C_2630) | ~r1_tarski('#skF_3', C_2630))), inference(superposition, [status(thm), theory('equality')], [c_126358, c_126724])).
% 36.37/23.12  tff(c_566, plain, (![C_125, A_126, B_127]: (v1_relat_1(C_125) | ~m1_subset_1(C_125, k1_zfmisc_1(k2_zfmisc_1(A_126, B_127))))), inference(cnfTransformation, [status(thm)], [f_127])).
% 36.37/23.12  tff(c_583, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_84, c_566])).
% 36.37/23.12  tff(c_3038, plain, (![A_243, B_244, C_245, D_246]: (k8_relset_1(A_243, B_244, C_245, D_246)=k10_relat_1(C_245, D_246) | ~m1_subset_1(C_245, k1_zfmisc_1(k2_zfmisc_1(A_243, B_244))))), inference(cnfTransformation, [status(thm)], [f_145])).
% 36.37/23.12  tff(c_3056, plain, (![D_246]: (k8_relset_1('#skF_3', '#skF_4', '#skF_5', D_246)=k10_relat_1('#skF_5', D_246))), inference(resolution, [status(thm)], [c_84, c_3038])).
% 36.37/23.12  tff(c_100, plain, (r1_tarski(k7_relset_1('#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_7') | r1_tarski('#skF_6', k8_relset_1('#skF_3', '#skF_4', '#skF_5', '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_188])).
% 36.37/23.12  tff(c_320, plain, (r1_tarski('#skF_6', k8_relset_1('#skF_3', '#skF_4', '#skF_5', '#skF_7'))), inference(splitLeft, [status(thm)], [c_100])).
% 36.37/23.12  tff(c_3106, plain, (r1_tarski('#skF_6', k10_relat_1('#skF_5', '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_3056, c_320])).
% 36.37/23.12  tff(c_52, plain, (![C_39, A_37, B_38]: (r1_tarski(k9_relat_1(C_39, A_37), k9_relat_1(C_39, B_38)) | ~r1_tarski(A_37, B_38) | ~v1_relat_1(C_39))), inference(cnfTransformation, [status(thm)], [f_103])).
% 36.37/23.12  tff(c_2450, plain, (![B_219, A_220]: (r1_tarski(k9_relat_1(B_219, k10_relat_1(B_219, A_220)), A_220) | ~v1_funct_1(B_219) | ~v1_relat_1(B_219))), inference(cnfTransformation, [status(thm)], [f_113])).
% 36.37/23.12  tff(c_22, plain, (![A_15, C_17, B_16]: (r1_tarski(A_15, C_17) | ~r1_tarski(B_16, C_17) | ~r1_tarski(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_55])).
% 36.37/23.12  tff(c_72133, plain, (![A_1801, A_1802, B_1803]: (r1_tarski(A_1801, A_1802) | ~r1_tarski(A_1801, k9_relat_1(B_1803, k10_relat_1(B_1803, A_1802))) | ~v1_funct_1(B_1803) | ~v1_relat_1(B_1803))), inference(resolution, [status(thm)], [c_2450, c_22])).
% 36.37/23.12  tff(c_125862, plain, (![C_2604, A_2605, A_2606]: (r1_tarski(k9_relat_1(C_2604, A_2605), A_2606) | ~v1_funct_1(C_2604) | ~r1_tarski(A_2605, k10_relat_1(C_2604, A_2606)) | ~v1_relat_1(C_2604))), inference(resolution, [status(thm)], [c_52, c_72133])).
% 36.37/23.12  tff(c_3001, plain, (![A_238, B_239, C_240, D_241]: (k7_relset_1(A_238, B_239, C_240, D_241)=k9_relat_1(C_240, D_241) | ~m1_subset_1(C_240, k1_zfmisc_1(k2_zfmisc_1(A_238, B_239))))), inference(cnfTransformation, [status(thm)], [f_141])).
% 36.37/23.12  tff(c_3019, plain, (![D_241]: (k7_relset_1('#skF_3', '#skF_4', '#skF_5', D_241)=k9_relat_1('#skF_5', D_241))), inference(resolution, [status(thm)], [c_84, c_3001])).
% 36.37/23.12  tff(c_94, plain, (~r1_tarski('#skF_6', k8_relset_1('#skF_3', '#skF_4', '#skF_5', '#skF_7')) | ~r1_tarski(k7_relset_1('#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_7')), inference(cnfTransformation, [status(thm)], [f_188])).
% 36.37/23.12  tff(c_196, plain, (~r1_tarski(k7_relset_1('#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_7')), inference(splitLeft, [status(thm)], [c_94])).
% 36.37/23.12  tff(c_3024, plain, (~r1_tarski(k9_relat_1('#skF_5', '#skF_6'), '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_3019, c_196])).
% 36.37/23.12  tff(c_126021, plain, (~v1_funct_1('#skF_5') | ~r1_tarski('#skF_6', k10_relat_1('#skF_5', '#skF_7')) | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_125862, c_3024])).
% 36.37/23.12  tff(c_126095, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_583, c_3106, c_88, c_126021])).
% 36.37/23.12  tff(c_126096, plain, (r1_tarski(k7_relset_1('#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_7')), inference(splitRight, [status(thm)], [c_100])).
% 36.37/23.12  tff(c_126298, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_126096, c_196])).
% 36.37/23.12  tff(c_126299, plain, (~r1_tarski('#skF_6', k8_relset_1('#skF_3', '#skF_4', '#skF_5', '#skF_7'))), inference(splitRight, [status(thm)], [c_94])).
% 36.37/23.12  tff(c_129494, plain, (~r1_tarski('#skF_6', k10_relat_1('#skF_5', '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_129487, c_126299])).
% 36.37/23.12  tff(c_126825, plain, (![C_2634, A_2635, B_2636]: (v1_relat_1(C_2634) | ~m1_subset_1(C_2634, k1_zfmisc_1(k2_zfmisc_1(A_2635, B_2636))))), inference(cnfTransformation, [status(thm)], [f_127])).
% 36.37/23.12  tff(c_126842, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_84, c_126825])).
% 36.37/23.12  tff(c_129148, plain, (![A_2739, B_2740, C_2741, D_2742]: (k7_relset_1(A_2739, B_2740, C_2741, D_2742)=k9_relat_1(C_2741, D_2742) | ~m1_subset_1(C_2741, k1_zfmisc_1(k2_zfmisc_1(A_2739, B_2740))))), inference(cnfTransformation, [status(thm)], [f_141])).
% 36.37/23.12  tff(c_129166, plain, (![D_2742]: (k7_relset_1('#skF_3', '#skF_4', '#skF_5', D_2742)=k9_relat_1('#skF_5', D_2742))), inference(resolution, [status(thm)], [c_84, c_129148])).
% 36.37/23.12  tff(c_126300, plain, (r1_tarski(k7_relset_1('#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_7')), inference(splitRight, [status(thm)], [c_94])).
% 36.37/23.12  tff(c_129421, plain, (r1_tarski(k9_relat_1('#skF_5', '#skF_6'), '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_129166, c_126300])).
% 36.37/23.12  tff(c_130046, plain, (![A_2771, C_2772, B_2773]: (r1_tarski(A_2771, k10_relat_1(C_2772, B_2773)) | ~r1_tarski(k9_relat_1(C_2772, A_2771), B_2773) | ~r1_tarski(A_2771, k1_relat_1(C_2772)) | ~v1_funct_1(C_2772) | ~v1_relat_1(C_2772))), inference(cnfTransformation, [status(thm)], [f_123])).
% 36.37/23.12  tff(c_130061, plain, (r1_tarski('#skF_6', k10_relat_1('#skF_5', '#skF_7')) | ~r1_tarski('#skF_6', k1_relat_1('#skF_5')) | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_129421, c_130046])).
% 36.37/23.12  tff(c_130118, plain, (r1_tarski('#skF_6', k10_relat_1('#skF_5', '#skF_7')) | ~r1_tarski('#skF_6', k1_relat_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_126842, c_88, c_130061])).
% 36.37/23.12  tff(c_130119, plain, (~r1_tarski('#skF_6', k1_relat_1('#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_129494, c_130118])).
% 36.37/23.12  tff(c_130135, plain, (~r1_tarski('#skF_3', k1_relat_1('#skF_5'))), inference(resolution, [status(thm)], [c_126748, c_130119])).
% 36.37/23.12  tff(c_130212, plain, (~r1_tarski('#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_130210, c_130135])).
% 36.37/23.12  tff(c_130220, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_16, c_130212])).
% 36.37/23.12  tff(c_130221, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_130207])).
% 36.37/23.12  tff(c_126359, plain, (k2_xboole_0('#skF_7', '#skF_4')='#skF_4'), inference(resolution, [status(thm)], [c_126319, c_126328])).
% 36.37/23.12  tff(c_126793, plain, (![C_2632]: (r1_tarski('#skF_7', C_2632) | ~r1_tarski('#skF_4', C_2632))), inference(superposition, [status(thm), theory('equality')], [c_126359, c_126724])).
% 36.37/23.12  tff(c_26, plain, (![A_19]: (k1_xboole_0=A_19 | ~r1_tarski(A_19, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_61])).
% 36.37/23.12  tff(c_126805, plain, (k1_xboole_0='#skF_7' | ~r1_tarski('#skF_4', k1_xboole_0)), inference(resolution, [status(thm)], [c_126793, c_26])).
% 36.37/23.12  tff(c_126806, plain, (~r1_tarski('#skF_4', k1_xboole_0)), inference(splitLeft, [status(thm)], [c_126805])).
% 36.37/23.12  tff(c_130239, plain, (~r1_tarski('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_130221, c_126806])).
% 36.37/23.12  tff(c_130252, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_16, c_130239])).
% 36.37/23.12  tff(c_130253, plain, (k1_xboole_0='#skF_7'), inference(splitRight, [status(thm)], [c_126805])).
% 36.37/23.12  tff(c_130254, plain, (r1_tarski('#skF_4', k1_xboole_0)), inference(splitRight, [status(thm)], [c_126805])).
% 36.37/23.12  tff(c_130270, plain, (r1_tarski('#skF_4', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_130253, c_130254])).
% 36.37/23.12  tff(c_130271, plain, $false, inference(negUnitSimplification, [status(thm)], [c_126636, c_130270])).
% 36.37/23.12  tff(c_130272, plain, ('#skF_7'='#skF_4'), inference(splitRight, [status(thm)], [c_126625])).
% 36.37/23.12  tff(c_130278, plain, (~r1_tarski('#skF_6', k8_relset_1('#skF_3', '#skF_4', '#skF_5', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_130272, c_126299])).
% 36.37/23.12  tff(c_130563, plain, (~r1_tarski('#skF_3', k8_relset_1('#skF_3', '#skF_4', '#skF_5', '#skF_4'))), inference(resolution, [status(thm)], [c_130540, c_130278])).
% 36.37/23.12  tff(c_132894, plain, (~r1_tarski('#skF_3', k10_relat_1('#skF_5', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_132889, c_130563])).
% 36.37/23.12  tff(c_132932, plain, (~r1_tarski('#skF_3', k1_relat_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_132930, c_132894])).
% 36.37/23.12  tff(c_133827, plain, (~r1_tarski('#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_133823, c_132932])).
% 36.37/23.12  tff(c_133833, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_16, c_133827])).
% 36.37/23.12  tff(c_133834, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_133814])).
% 36.37/23.12  tff(c_10, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_35])).
% 36.37/23.12  tff(c_133864, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_133834, c_10])).
% 36.37/23.12  tff(c_133867, plain, $false, inference(negUnitSimplification, [status(thm)], [c_90, c_133864])).
% 36.37/23.12  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 36.37/23.12  
% 36.37/23.12  Inference rules
% 36.37/23.12  ----------------------
% 36.37/23.12  #Ref     : 0
% 36.37/23.12  #Sup     : 33780
% 36.37/23.12  #Fact    : 0
% 36.37/23.12  #Define  : 0
% 36.37/23.12  #Split   : 95
% 36.37/23.12  #Chain   : 0
% 36.37/23.12  #Close   : 0
% 36.37/23.12  
% 36.37/23.12  Ordering : KBO
% 36.37/23.12  
% 36.37/23.12  Simplification rules
% 36.37/23.12  ----------------------
% 36.37/23.12  #Subsume      : 16696
% 36.37/23.12  #Demod        : 12986
% 36.37/23.12  #Tautology    : 6989
% 36.37/23.12  #SimpNegUnit  : 472
% 36.37/23.12  #BackRed      : 333
% 36.37/23.12  
% 36.37/23.12  #Partial instantiations: 0
% 36.37/23.12  #Strategies tried      : 1
% 36.37/23.12  
% 36.37/23.12  Timing (in seconds)
% 36.37/23.12  ----------------------
% 36.37/23.12  Preprocessing        : 0.61
% 36.37/23.12  Parsing              : 0.31
% 36.37/23.12  CNF conversion       : 0.05
% 36.37/23.12  Main loop            : 21.59
% 36.37/23.12  Inferencing          : 3.46
% 36.37/23.12  Reduction            : 10.25
% 36.37/23.12  Demodulation         : 7.93
% 36.37/23.12  BG Simplification    : 0.30
% 36.37/23.12  Subsumption          : 6.08
% 36.37/23.12  Abstraction          : 0.44
% 36.37/23.13  MUC search           : 0.00
% 36.37/23.13  Cooper               : 0.00
% 36.37/23.13  Total                : 22.26
% 36.37/23.13  Index Insertion      : 0.00
% 36.37/23.13  Index Deletion       : 0.00
% 36.37/23.13  Index Matching       : 0.00
% 36.37/23.13  BG Taut test         : 0.00
%------------------------------------------------------------------------------
