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
% DateTime   : Thu Dec  3 09:57:59 EST 2020

% Result     : Theorem 3.54s
% Output     : CNFRefutation 3.88s
% Verified   : 
% Statistics : Number of formulae       :  107 ( 387 expanded)
%              Number of leaves         :   30 ( 138 expanded)
%              Depth                    :   13
%              Number of atoms          :  161 ( 805 expanded)
%              Number of equality atoms :   63 ( 207 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > k8_setfam_1 > k6_setfam_1 > k4_xboole_0 > #nlpp > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k8_setfam_1,type,(
    k8_setfam_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff(k6_setfam_1,type,(
    k6_setfam_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_38,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_42,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_100,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
       => ! [C] :
            ( m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(A)))
           => ( r1_tarski(B,C)
             => r1_tarski(k8_setfam_1(A,C),k8_setfam_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t59_setfam_1)).

tff(f_54,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ~ ( r1_tarski(B,A)
          & r1_xboole_0(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_xboole_1)).

tff(f_90,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => ( A = k1_xboole_0
        | r1_tarski(k1_setfam_1(B),k1_setfam_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_setfam_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_77,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_84,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

tff(f_73,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => k6_setfam_1(A,B) = k1_setfam_1(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_setfam_1)).

tff(f_65,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => ( ( B != k1_xboole_0
         => k8_setfam_1(A,B) = k6_setfam_1(A,B) )
        & ( B = k1_xboole_0
         => k8_setfam_1(A,B) = A ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_setfam_1)).

tff(f_69,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => m1_subset_1(k8_setfam_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k8_setfam_1)).

tff(c_12,plain,(
    ! [B_7] : r1_tarski(B_7,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_59,plain,(
    ! [A_33,B_34] :
      ( k4_xboole_0(A_33,B_34) = k1_xboole_0
      | ~ r1_tarski(A_33,B_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_74,plain,(
    ! [B_7] : k4_xboole_0(B_7,B_7) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_12,c_59])).

tff(c_42,plain,(
    r1_tarski('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_75,plain,(
    k4_xboole_0('#skF_3','#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_42,c_59])).

tff(c_22,plain,(
    ! [A_12,B_13] :
      ( r1_xboole_0(A_12,B_13)
      | k4_xboole_0(A_12,B_13) != A_12 ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_122,plain,(
    ! [B_46,A_47] :
      ( ~ r1_xboole_0(B_46,A_47)
      | ~ r1_tarski(B_46,A_47)
      | v1_xboole_0(B_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_551,plain,(
    ! [A_103,B_104] :
      ( ~ r1_tarski(A_103,B_104)
      | v1_xboole_0(A_103)
      | k4_xboole_0(A_103,B_104) != A_103 ) ),
    inference(resolution,[status(thm)],[c_22,c_122])).

tff(c_572,plain,
    ( v1_xboole_0('#skF_3')
    | k4_xboole_0('#skF_3','#skF_4') != '#skF_3' ),
    inference(resolution,[status(thm)],[c_42,c_551])).

tff(c_584,plain,
    ( v1_xboole_0('#skF_3')
    | k1_xboole_0 != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_75,c_572])).

tff(c_585,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_584])).

tff(c_38,plain,(
    ! [B_26,A_25] :
      ( r1_tarski(k1_setfam_1(B_26),k1_setfam_1(A_25))
      | k1_xboole_0 = A_25
      | ~ r1_tarski(A_25,B_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_34,plain,(
    ! [A_20,B_21] :
      ( m1_subset_1(A_20,k1_zfmisc_1(B_21))
      | ~ r1_tarski(A_20,B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_151,plain,(
    ! [C_50,B_51,A_52] :
      ( ~ v1_xboole_0(C_50)
      | ~ m1_subset_1(B_51,k1_zfmisc_1(C_50))
      | ~ r2_hidden(A_52,B_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_176,plain,(
    ! [B_56,A_57,A_58] :
      ( ~ v1_xboole_0(B_56)
      | ~ r2_hidden(A_57,A_58)
      | ~ r1_tarski(A_58,B_56) ) ),
    inference(resolution,[status(thm)],[c_34,c_151])).

tff(c_180,plain,(
    ! [B_59,A_60,B_61] :
      ( ~ v1_xboole_0(B_59)
      | ~ r1_tarski(A_60,B_59)
      | r1_tarski(A_60,B_61) ) ),
    inference(resolution,[status(thm)],[c_6,c_176])).

tff(c_196,plain,(
    ! [B_62,B_63] :
      ( ~ v1_xboole_0(B_62)
      | r1_tarski(B_62,B_63) ) ),
    inference(resolution,[status(thm)],[c_12,c_180])).

tff(c_127,plain,(
    ! [B_48,A_49] :
      ( B_48 = A_49
      | ~ r1_tarski(B_48,A_49)
      | ~ r1_tarski(A_49,B_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_145,plain,
    ( '#skF_3' = '#skF_4'
    | ~ r1_tarski('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_42,c_127])).

tff(c_146,plain,(
    ~ r1_tarski('#skF_4','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_145])).

tff(c_219,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_196,c_146])).

tff(c_44,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k1_zfmisc_1('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_49,plain,(
    ! [A_29,B_30] :
      ( r1_tarski(A_29,B_30)
      | ~ m1_subset_1(A_29,k1_zfmisc_1(B_30)) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_57,plain,(
    r1_tarski('#skF_4',k1_zfmisc_1('#skF_2')) ),
    inference(resolution,[status(thm)],[c_44,c_49])).

tff(c_72,plain,(
    k4_xboole_0('#skF_4',k1_zfmisc_1('#skF_2')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_57,c_59])).

tff(c_563,plain,
    ( v1_xboole_0('#skF_4')
    | k4_xboole_0('#skF_4',k1_zfmisc_1('#skF_2')) != '#skF_4' ),
    inference(resolution,[status(thm)],[c_57,c_551])).

tff(c_577,plain,
    ( v1_xboole_0('#skF_4')
    | k1_xboole_0 != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_563])).

tff(c_578,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_219,c_577])).

tff(c_419,plain,(
    ! [A_87,B_88] :
      ( k6_setfam_1(A_87,B_88) = k1_setfam_1(B_88)
      | ~ m1_subset_1(B_88,k1_zfmisc_1(k1_zfmisc_1(A_87))) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_432,plain,(
    k6_setfam_1('#skF_2','#skF_4') = k1_setfam_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_44,c_419])).

tff(c_697,plain,(
    ! [A_112,B_113] :
      ( k8_setfam_1(A_112,B_113) = k6_setfam_1(A_112,B_113)
      | k1_xboole_0 = B_113
      | ~ m1_subset_1(B_113,k1_zfmisc_1(k1_zfmisc_1(A_112))) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_711,plain,
    ( k8_setfam_1('#skF_2','#skF_4') = k6_setfam_1('#skF_2','#skF_4')
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_44,c_697])).

tff(c_718,plain,
    ( k8_setfam_1('#skF_2','#skF_4') = k1_setfam_1('#skF_4')
    | k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_432,c_711])).

tff(c_719,plain,(
    k8_setfam_1('#skF_2','#skF_4') = k1_setfam_1('#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_578,c_718])).

tff(c_46,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k1_zfmisc_1('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_431,plain,(
    k6_setfam_1('#skF_2','#skF_3') = k1_setfam_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_46,c_419])).

tff(c_708,plain,
    ( k8_setfam_1('#skF_2','#skF_3') = k6_setfam_1('#skF_2','#skF_3')
    | k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_46,c_697])).

tff(c_715,plain,
    ( k8_setfam_1('#skF_2','#skF_3') = k1_setfam_1('#skF_3')
    | k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_431,c_708])).

tff(c_716,plain,(
    k8_setfam_1('#skF_2','#skF_3') = k1_setfam_1('#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_585,c_715])).

tff(c_40,plain,(
    ~ r1_tarski(k8_setfam_1('#skF_2','#skF_4'),k8_setfam_1('#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_721,plain,(
    ~ r1_tarski(k8_setfam_1('#skF_2','#skF_4'),k1_setfam_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_716,c_40])).

tff(c_746,plain,(
    ~ r1_tarski(k1_setfam_1('#skF_4'),k1_setfam_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_719,c_721])).

tff(c_749,plain,
    ( k1_xboole_0 = '#skF_3'
    | ~ r1_tarski('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_38,c_746])).

tff(c_758,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_749])).

tff(c_760,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_585,c_758])).

tff(c_762,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_584])).

tff(c_779,plain,(
    '#skF_3' != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_762,c_578])).

tff(c_26,plain,(
    ! [A_14,B_15] :
      ( k8_setfam_1(A_14,B_15) = k6_setfam_1(A_14,B_15)
      | k1_xboole_0 = B_15
      | ~ m1_subset_1(B_15,k1_zfmisc_1(k1_zfmisc_1(A_14))) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_894,plain,(
    ! [A_121,B_122] :
      ( k8_setfam_1(A_121,B_122) = k6_setfam_1(A_121,B_122)
      | B_122 = '#skF_3'
      | ~ m1_subset_1(B_122,k1_zfmisc_1(k1_zfmisc_1(A_121))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_762,c_26])).

tff(c_908,plain,
    ( k8_setfam_1('#skF_2','#skF_4') = k6_setfam_1('#skF_2','#skF_4')
    | '#skF_3' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_44,c_894])).

tff(c_915,plain,
    ( k8_setfam_1('#skF_2','#skF_4') = k1_setfam_1('#skF_4')
    | '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_432,c_908])).

tff(c_916,plain,(
    k8_setfam_1('#skF_2','#skF_4') = k1_setfam_1('#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_779,c_915])).

tff(c_372,plain,(
    ! [A_85,B_86] :
      ( ~ r1_tarski(A_85,B_86)
      | v1_xboole_0(A_85)
      | k4_xboole_0(A_85,B_86) != A_85 ) ),
    inference(resolution,[status(thm)],[c_22,c_122])).

tff(c_390,plain,(
    ! [B_7] :
      ( v1_xboole_0(B_7)
      | k4_xboole_0(B_7,B_7) != B_7 ) ),
    inference(resolution,[status(thm)],[c_12,c_372])).

tff(c_407,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_390])).

tff(c_194,plain,(
    ! [B_7,B_61] :
      ( ~ v1_xboole_0(B_7)
      | r1_tarski(B_7,B_61) ) ),
    inference(resolution,[status(thm)],[c_12,c_180])).

tff(c_251,plain,(
    ! [A_70] :
      ( k8_setfam_1(A_70,k1_xboole_0) = A_70
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(A_70))) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_256,plain,(
    ! [A_71] :
      ( k8_setfam_1(A_71,k1_xboole_0) = A_71
      | ~ r1_tarski(k1_xboole_0,k1_zfmisc_1(A_71)) ) ),
    inference(resolution,[status(thm)],[c_34,c_251])).

tff(c_263,plain,(
    ! [A_71] :
      ( k8_setfam_1(A_71,k1_xboole_0) = A_71
      | ~ v1_xboole_0(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_194,c_256])).

tff(c_265,plain,(
    ~ v1_xboole_0(k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_263])).

tff(c_410,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_407,c_265])).

tff(c_411,plain,(
    ! [A_71] : k8_setfam_1(A_71,k1_xboole_0) = A_71 ),
    inference(splitRight,[status(thm)],[c_263])).

tff(c_786,plain,(
    ! [A_71] : k8_setfam_1(A_71,'#skF_3') = A_71 ),
    inference(demodulation,[status(thm),theory(equality)],[c_762,c_411])).

tff(c_853,plain,(
    ~ r1_tarski(k8_setfam_1('#skF_2','#skF_4'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_786,c_40])).

tff(c_923,plain,(
    ~ r1_tarski(k1_setfam_1('#skF_4'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_916,c_853])).

tff(c_28,plain,(
    ! [A_16,B_17] :
      ( m1_subset_1(k8_setfam_1(A_16,B_17),k1_zfmisc_1(A_16))
      | ~ m1_subset_1(B_17,k1_zfmisc_1(k1_zfmisc_1(A_16))) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_928,plain,
    ( m1_subset_1(k1_setfam_1('#skF_4'),k1_zfmisc_1('#skF_2'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k1_zfmisc_1('#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_916,c_28])).

tff(c_932,plain,(
    m1_subset_1(k1_setfam_1('#skF_4'),k1_zfmisc_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_928])).

tff(c_32,plain,(
    ! [A_20,B_21] :
      ( r1_tarski(A_20,B_21)
      | ~ m1_subset_1(A_20,k1_zfmisc_1(B_21)) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_973,plain,(
    r1_tarski(k1_setfam_1('#skF_4'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_932,c_32])).

tff(c_978,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_923,c_973])).

tff(c_979,plain,(
    '#skF_3' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_145])).

tff(c_95,plain,(
    ! [A_36,B_37] :
      ( r1_tarski(A_36,B_37)
      | k4_xboole_0(A_36,B_37) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_103,plain,(
    k4_xboole_0(k8_setfam_1('#skF_2','#skF_4'),k8_setfam_1('#skF_2','#skF_3')) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_95,c_40])).

tff(c_981,plain,(
    k4_xboole_0(k8_setfam_1('#skF_2','#skF_4'),k8_setfam_1('#skF_2','#skF_4')) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_979,c_103])).

tff(c_990,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_981])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:33:05 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.54/2.00  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.54/2.01  
% 3.54/2.01  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.88/2.02  %$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > k8_setfam_1 > k6_setfam_1 > k4_xboole_0 > #nlpp > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 3.88/2.02  
% 3.88/2.02  %Foreground sorts:
% 3.88/2.02  
% 3.88/2.02  
% 3.88/2.02  %Background operators:
% 3.88/2.02  
% 3.88/2.02  
% 3.88/2.02  %Foreground operators:
% 3.88/2.02  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.88/2.02  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.88/2.02  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.88/2.02  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.88/2.02  tff(k8_setfam_1, type, k8_setfam_1: ($i * $i) > $i).
% 3.88/2.02  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.88/2.02  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.88/2.02  tff('#skF_2', type, '#skF_2': $i).
% 3.88/2.02  tff('#skF_3', type, '#skF_3': $i).
% 3.88/2.02  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.88/2.02  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.88/2.02  tff('#skF_4', type, '#skF_4': $i).
% 3.88/2.02  tff(k6_setfam_1, type, k6_setfam_1: ($i * $i) > $i).
% 3.88/2.02  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.88/2.02  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.88/2.02  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.88/2.02  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.88/2.02  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 3.88/2.02  
% 3.88/2.05  tff(f_38, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.88/2.05  tff(f_42, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 3.88/2.05  tff(f_100, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(A))) => (r1_tarski(B, C) => r1_tarski(k8_setfam_1(A, C), k8_setfam_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t59_setfam_1)).
% 3.88/2.05  tff(f_54, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_xboole_1)).
% 3.88/2.05  tff(f_50, axiom, (![A, B]: (~v1_xboole_0(B) => ~(r1_tarski(B, A) & r1_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_xboole_1)).
% 3.88/2.05  tff(f_90, axiom, (![A, B]: (r1_tarski(A, B) => ((A = k1_xboole_0) | r1_tarski(k1_setfam_1(B), k1_setfam_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_setfam_1)).
% 3.88/2.05  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 3.88/2.05  tff(f_77, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 3.88/2.05  tff(f_84, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_subset)).
% 3.88/2.05  tff(f_73, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (k6_setfam_1(A, B) = k1_setfam_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_setfam_1)).
% 3.88/2.05  tff(f_65, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => ((~(B = k1_xboole_0) => (k8_setfam_1(A, B) = k6_setfam_1(A, B))) & ((B = k1_xboole_0) => (k8_setfam_1(A, B) = A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_setfam_1)).
% 3.88/2.05  tff(f_69, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => m1_subset_1(k8_setfam_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k8_setfam_1)).
% 3.88/2.05  tff(c_12, plain, (![B_7]: (r1_tarski(B_7, B_7))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.88/2.05  tff(c_59, plain, (![A_33, B_34]: (k4_xboole_0(A_33, B_34)=k1_xboole_0 | ~r1_tarski(A_33, B_34))), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.88/2.05  tff(c_74, plain, (![B_7]: (k4_xboole_0(B_7, B_7)=k1_xboole_0)), inference(resolution, [status(thm)], [c_12, c_59])).
% 3.88/2.05  tff(c_42, plain, (r1_tarski('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_100])).
% 3.88/2.05  tff(c_75, plain, (k4_xboole_0('#skF_3', '#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_42, c_59])).
% 3.88/2.05  tff(c_22, plain, (![A_12, B_13]: (r1_xboole_0(A_12, B_13) | k4_xboole_0(A_12, B_13)!=A_12)), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.88/2.05  tff(c_122, plain, (![B_46, A_47]: (~r1_xboole_0(B_46, A_47) | ~r1_tarski(B_46, A_47) | v1_xboole_0(B_46))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.88/2.05  tff(c_551, plain, (![A_103, B_104]: (~r1_tarski(A_103, B_104) | v1_xboole_0(A_103) | k4_xboole_0(A_103, B_104)!=A_103)), inference(resolution, [status(thm)], [c_22, c_122])).
% 3.88/2.05  tff(c_572, plain, (v1_xboole_0('#skF_3') | k4_xboole_0('#skF_3', '#skF_4')!='#skF_3'), inference(resolution, [status(thm)], [c_42, c_551])).
% 3.88/2.05  tff(c_584, plain, (v1_xboole_0('#skF_3') | k1_xboole_0!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_75, c_572])).
% 3.88/2.05  tff(c_585, plain, (k1_xboole_0!='#skF_3'), inference(splitLeft, [status(thm)], [c_584])).
% 3.88/2.05  tff(c_38, plain, (![B_26, A_25]: (r1_tarski(k1_setfam_1(B_26), k1_setfam_1(A_25)) | k1_xboole_0=A_25 | ~r1_tarski(A_25, B_26))), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.88/2.05  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.88/2.05  tff(c_34, plain, (![A_20, B_21]: (m1_subset_1(A_20, k1_zfmisc_1(B_21)) | ~r1_tarski(A_20, B_21))), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.88/2.05  tff(c_151, plain, (![C_50, B_51, A_52]: (~v1_xboole_0(C_50) | ~m1_subset_1(B_51, k1_zfmisc_1(C_50)) | ~r2_hidden(A_52, B_51))), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.88/2.05  tff(c_176, plain, (![B_56, A_57, A_58]: (~v1_xboole_0(B_56) | ~r2_hidden(A_57, A_58) | ~r1_tarski(A_58, B_56))), inference(resolution, [status(thm)], [c_34, c_151])).
% 3.88/2.05  tff(c_180, plain, (![B_59, A_60, B_61]: (~v1_xboole_0(B_59) | ~r1_tarski(A_60, B_59) | r1_tarski(A_60, B_61))), inference(resolution, [status(thm)], [c_6, c_176])).
% 3.88/2.05  tff(c_196, plain, (![B_62, B_63]: (~v1_xboole_0(B_62) | r1_tarski(B_62, B_63))), inference(resolution, [status(thm)], [c_12, c_180])).
% 3.88/2.05  tff(c_127, plain, (![B_48, A_49]: (B_48=A_49 | ~r1_tarski(B_48, A_49) | ~r1_tarski(A_49, B_48))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.88/2.05  tff(c_145, plain, ('#skF_3'='#skF_4' | ~r1_tarski('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_42, c_127])).
% 3.88/2.05  tff(c_146, plain, (~r1_tarski('#skF_4', '#skF_3')), inference(splitLeft, [status(thm)], [c_145])).
% 3.88/2.05  tff(c_219, plain, (~v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_196, c_146])).
% 3.88/2.05  tff(c_44, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k1_zfmisc_1('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_100])).
% 3.88/2.05  tff(c_49, plain, (![A_29, B_30]: (r1_tarski(A_29, B_30) | ~m1_subset_1(A_29, k1_zfmisc_1(B_30)))), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.88/2.05  tff(c_57, plain, (r1_tarski('#skF_4', k1_zfmisc_1('#skF_2'))), inference(resolution, [status(thm)], [c_44, c_49])).
% 3.88/2.05  tff(c_72, plain, (k4_xboole_0('#skF_4', k1_zfmisc_1('#skF_2'))=k1_xboole_0), inference(resolution, [status(thm)], [c_57, c_59])).
% 3.88/2.05  tff(c_563, plain, (v1_xboole_0('#skF_4') | k4_xboole_0('#skF_4', k1_zfmisc_1('#skF_2'))!='#skF_4'), inference(resolution, [status(thm)], [c_57, c_551])).
% 3.88/2.05  tff(c_577, plain, (v1_xboole_0('#skF_4') | k1_xboole_0!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_72, c_563])).
% 3.88/2.05  tff(c_578, plain, (k1_xboole_0!='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_219, c_577])).
% 3.88/2.05  tff(c_419, plain, (![A_87, B_88]: (k6_setfam_1(A_87, B_88)=k1_setfam_1(B_88) | ~m1_subset_1(B_88, k1_zfmisc_1(k1_zfmisc_1(A_87))))), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.88/2.05  tff(c_432, plain, (k6_setfam_1('#skF_2', '#skF_4')=k1_setfam_1('#skF_4')), inference(resolution, [status(thm)], [c_44, c_419])).
% 3.88/2.05  tff(c_697, plain, (![A_112, B_113]: (k8_setfam_1(A_112, B_113)=k6_setfam_1(A_112, B_113) | k1_xboole_0=B_113 | ~m1_subset_1(B_113, k1_zfmisc_1(k1_zfmisc_1(A_112))))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.88/2.05  tff(c_711, plain, (k8_setfam_1('#skF_2', '#skF_4')=k6_setfam_1('#skF_2', '#skF_4') | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_44, c_697])).
% 3.88/2.05  tff(c_718, plain, (k8_setfam_1('#skF_2', '#skF_4')=k1_setfam_1('#skF_4') | k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_432, c_711])).
% 3.88/2.05  tff(c_719, plain, (k8_setfam_1('#skF_2', '#skF_4')=k1_setfam_1('#skF_4')), inference(negUnitSimplification, [status(thm)], [c_578, c_718])).
% 3.88/2.05  tff(c_46, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k1_zfmisc_1('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_100])).
% 3.88/2.05  tff(c_431, plain, (k6_setfam_1('#skF_2', '#skF_3')=k1_setfam_1('#skF_3')), inference(resolution, [status(thm)], [c_46, c_419])).
% 3.88/2.05  tff(c_708, plain, (k8_setfam_1('#skF_2', '#skF_3')=k6_setfam_1('#skF_2', '#skF_3') | k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_46, c_697])).
% 3.88/2.05  tff(c_715, plain, (k8_setfam_1('#skF_2', '#skF_3')=k1_setfam_1('#skF_3') | k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_431, c_708])).
% 3.88/2.05  tff(c_716, plain, (k8_setfam_1('#skF_2', '#skF_3')=k1_setfam_1('#skF_3')), inference(negUnitSimplification, [status(thm)], [c_585, c_715])).
% 3.88/2.05  tff(c_40, plain, (~r1_tarski(k8_setfam_1('#skF_2', '#skF_4'), k8_setfam_1('#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_100])).
% 3.88/2.05  tff(c_721, plain, (~r1_tarski(k8_setfam_1('#skF_2', '#skF_4'), k1_setfam_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_716, c_40])).
% 3.88/2.05  tff(c_746, plain, (~r1_tarski(k1_setfam_1('#skF_4'), k1_setfam_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_719, c_721])).
% 3.88/2.05  tff(c_749, plain, (k1_xboole_0='#skF_3' | ~r1_tarski('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_38, c_746])).
% 3.88/2.05  tff(c_758, plain, (k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_42, c_749])).
% 3.88/2.05  tff(c_760, plain, $false, inference(negUnitSimplification, [status(thm)], [c_585, c_758])).
% 3.88/2.05  tff(c_762, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_584])).
% 3.88/2.05  tff(c_779, plain, ('#skF_3'!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_762, c_578])).
% 3.88/2.05  tff(c_26, plain, (![A_14, B_15]: (k8_setfam_1(A_14, B_15)=k6_setfam_1(A_14, B_15) | k1_xboole_0=B_15 | ~m1_subset_1(B_15, k1_zfmisc_1(k1_zfmisc_1(A_14))))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.88/2.05  tff(c_894, plain, (![A_121, B_122]: (k8_setfam_1(A_121, B_122)=k6_setfam_1(A_121, B_122) | B_122='#skF_3' | ~m1_subset_1(B_122, k1_zfmisc_1(k1_zfmisc_1(A_121))))), inference(demodulation, [status(thm), theory('equality')], [c_762, c_26])).
% 3.88/2.05  tff(c_908, plain, (k8_setfam_1('#skF_2', '#skF_4')=k6_setfam_1('#skF_2', '#skF_4') | '#skF_3'='#skF_4'), inference(resolution, [status(thm)], [c_44, c_894])).
% 3.88/2.05  tff(c_915, plain, (k8_setfam_1('#skF_2', '#skF_4')=k1_setfam_1('#skF_4') | '#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_432, c_908])).
% 3.88/2.05  tff(c_916, plain, (k8_setfam_1('#skF_2', '#skF_4')=k1_setfam_1('#skF_4')), inference(negUnitSimplification, [status(thm)], [c_779, c_915])).
% 3.88/2.05  tff(c_372, plain, (![A_85, B_86]: (~r1_tarski(A_85, B_86) | v1_xboole_0(A_85) | k4_xboole_0(A_85, B_86)!=A_85)), inference(resolution, [status(thm)], [c_22, c_122])).
% 3.88/2.05  tff(c_390, plain, (![B_7]: (v1_xboole_0(B_7) | k4_xboole_0(B_7, B_7)!=B_7)), inference(resolution, [status(thm)], [c_12, c_372])).
% 3.88/2.05  tff(c_407, plain, (v1_xboole_0(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_74, c_390])).
% 3.88/2.05  tff(c_194, plain, (![B_7, B_61]: (~v1_xboole_0(B_7) | r1_tarski(B_7, B_61))), inference(resolution, [status(thm)], [c_12, c_180])).
% 3.88/2.05  tff(c_251, plain, (![A_70]: (k8_setfam_1(A_70, k1_xboole_0)=A_70 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_zfmisc_1(A_70))))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.88/2.05  tff(c_256, plain, (![A_71]: (k8_setfam_1(A_71, k1_xboole_0)=A_71 | ~r1_tarski(k1_xboole_0, k1_zfmisc_1(A_71)))), inference(resolution, [status(thm)], [c_34, c_251])).
% 3.88/2.05  tff(c_263, plain, (![A_71]: (k8_setfam_1(A_71, k1_xboole_0)=A_71 | ~v1_xboole_0(k1_xboole_0))), inference(resolution, [status(thm)], [c_194, c_256])).
% 3.88/2.05  tff(c_265, plain, (~v1_xboole_0(k1_xboole_0)), inference(splitLeft, [status(thm)], [c_263])).
% 3.88/2.05  tff(c_410, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_407, c_265])).
% 3.88/2.05  tff(c_411, plain, (![A_71]: (k8_setfam_1(A_71, k1_xboole_0)=A_71)), inference(splitRight, [status(thm)], [c_263])).
% 3.88/2.05  tff(c_786, plain, (![A_71]: (k8_setfam_1(A_71, '#skF_3')=A_71)), inference(demodulation, [status(thm), theory('equality')], [c_762, c_411])).
% 3.88/2.05  tff(c_853, plain, (~r1_tarski(k8_setfam_1('#skF_2', '#skF_4'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_786, c_40])).
% 3.88/2.05  tff(c_923, plain, (~r1_tarski(k1_setfam_1('#skF_4'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_916, c_853])).
% 3.88/2.05  tff(c_28, plain, (![A_16, B_17]: (m1_subset_1(k8_setfam_1(A_16, B_17), k1_zfmisc_1(A_16)) | ~m1_subset_1(B_17, k1_zfmisc_1(k1_zfmisc_1(A_16))))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.88/2.05  tff(c_928, plain, (m1_subset_1(k1_setfam_1('#skF_4'), k1_zfmisc_1('#skF_2')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k1_zfmisc_1('#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_916, c_28])).
% 3.88/2.05  tff(c_932, plain, (m1_subset_1(k1_setfam_1('#skF_4'), k1_zfmisc_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_928])).
% 3.88/2.05  tff(c_32, plain, (![A_20, B_21]: (r1_tarski(A_20, B_21) | ~m1_subset_1(A_20, k1_zfmisc_1(B_21)))), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.88/2.05  tff(c_973, plain, (r1_tarski(k1_setfam_1('#skF_4'), '#skF_2')), inference(resolution, [status(thm)], [c_932, c_32])).
% 3.88/2.05  tff(c_978, plain, $false, inference(negUnitSimplification, [status(thm)], [c_923, c_973])).
% 3.88/2.05  tff(c_979, plain, ('#skF_3'='#skF_4'), inference(splitRight, [status(thm)], [c_145])).
% 3.88/2.05  tff(c_95, plain, (![A_36, B_37]: (r1_tarski(A_36, B_37) | k4_xboole_0(A_36, B_37)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.88/2.05  tff(c_103, plain, (k4_xboole_0(k8_setfam_1('#skF_2', '#skF_4'), k8_setfam_1('#skF_2', '#skF_3'))!=k1_xboole_0), inference(resolution, [status(thm)], [c_95, c_40])).
% 3.88/2.05  tff(c_981, plain, (k4_xboole_0(k8_setfam_1('#skF_2', '#skF_4'), k8_setfam_1('#skF_2', '#skF_4'))!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_979, c_103])).
% 3.88/2.05  tff(c_990, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_74, c_981])).
% 3.88/2.05  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.88/2.05  
% 3.88/2.05  Inference rules
% 3.88/2.05  ----------------------
% 3.88/2.05  #Ref     : 0
% 3.88/2.05  #Sup     : 214
% 3.88/2.05  #Fact    : 0
% 3.88/2.05  #Define  : 0
% 3.88/2.05  #Split   : 7
% 3.88/2.05  #Chain   : 0
% 3.88/2.05  #Close   : 0
% 3.88/2.05  
% 3.88/2.05  Ordering : KBO
% 3.88/2.05  
% 3.88/2.05  Simplification rules
% 3.88/2.05  ----------------------
% 3.88/2.05  #Subsume      : 36
% 3.88/2.05  #Demod        : 84
% 3.88/2.05  #Tautology    : 85
% 3.88/2.05  #SimpNegUnit  : 9
% 3.88/2.05  #BackRed      : 36
% 3.88/2.05  
% 3.88/2.05  #Partial instantiations: 0
% 3.88/2.05  #Strategies tried      : 1
% 3.88/2.05  
% 3.88/2.05  Timing (in seconds)
% 3.88/2.05  ----------------------
% 3.88/2.05  Preprocessing        : 0.49
% 3.88/2.05  Parsing              : 0.25
% 3.88/2.05  CNF conversion       : 0.04
% 3.88/2.05  Main loop            : 0.65
% 3.88/2.05  Inferencing          : 0.23
% 3.88/2.05  Reduction            : 0.20
% 3.88/2.05  Demodulation         : 0.14
% 3.88/2.05  BG Simplification    : 0.03
% 3.88/2.05  Subsumption          : 0.13
% 3.88/2.05  Abstraction          : 0.04
% 3.88/2.05  MUC search           : 0.00
% 3.88/2.05  Cooper               : 0.00
% 3.88/2.05  Total                : 1.20
% 3.88/2.05  Index Insertion      : 0.00
% 3.88/2.05  Index Deletion       : 0.00
% 3.88/2.05  Index Matching       : 0.00
% 3.88/2.05  BG Taut test         : 0.00
%------------------------------------------------------------------------------
