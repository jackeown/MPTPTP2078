%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:58:02 EST 2020

% Result     : Theorem 2.91s
% Output     : CNFRefutation 3.06s
% Verified   : 
% Statistics : Number of formulae       :  105 ( 286 expanded)
%              Number of leaves         :   39 ( 108 expanded)
%              Depth                    :   10
%              Number of atoms          :  134 ( 573 expanded)
%              Number of equality atoms :   53 ( 246 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k8_setfam_1 > k6_subset_1 > k6_setfam_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_tarski > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_1 > #skF_5 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k8_setfam_1,type,(
    k8_setfam_1: ( $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k6_subset_1,type,(
    k6_subset_1: ( $i * $i ) > $i )).

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_107,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
       => ! [C] :
            ( m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(A)))
           => ( r1_tarski(B,C)
             => r1_tarski(k8_setfam_1(A,C),k8_setfam_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t59_setfam_1)).

tff(f_37,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_53,axiom,(
    ! [A,B] : k6_subset_1(A,B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

tff(f_48,axiom,(
    ! [A,B] : m1_subset_1(k6_subset_1(A,B),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_subset_1)).

tff(f_84,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_72,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => k6_setfam_1(A,B) = k1_setfam_1(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_setfam_1)).

tff(f_64,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => ( ( B != k1_xboole_0
         => k8_setfam_1(A,B) = k6_setfam_1(A,B) )
        & ( B = k1_xboole_0
         => k8_setfam_1(A,B) = A ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_setfam_1)).

tff(f_68,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => m1_subset_1(k8_setfam_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k8_setfam_1)).

tff(f_97,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => ( A = k1_xboole_0
        | r1_tarski(k1_setfam_1(B),k1_setfam_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_setfam_1)).

tff(f_51,axiom,(
    ! [A] :
    ? [B] : m1_subset_1(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',existence_m1_subset_1)).

tff(f_80,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(f_43,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => k2_xboole_0(k1_tarski(A),B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l22_zfmisc_1)).

tff(f_46,axiom,(
    ! [A,B] : k2_xboole_0(k1_tarski(A),B) != k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_zfmisc_1)).

tff(f_33,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_91,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

tff(c_44,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k1_zfmisc_1('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_6,plain,(
    ! [A_5] : k4_xboole_0(A_5,k1_xboole_0) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_18,plain,(
    ! [A_16,B_17] : k6_subset_1(A_16,B_17) = k4_xboole_0(A_16,B_17) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_14,plain,(
    ! [A_12,B_13] : m1_subset_1(k6_subset_1(A_12,B_13),k1_zfmisc_1(A_12)) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_69,plain,(
    ! [A_43,B_44] : m1_subset_1(k4_xboole_0(A_43,B_44),k1_zfmisc_1(A_43)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_14])).

tff(c_72,plain,(
    ! [A_5] : m1_subset_1(A_5,k1_zfmisc_1(A_5)) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_69])).

tff(c_75,plain,(
    ! [A_48,B_49] :
      ( r1_tarski(A_48,B_49)
      | ~ m1_subset_1(A_48,k1_zfmisc_1(B_49)) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_96,plain,(
    ! [A_5] : r1_tarski(A_5,A_5) ),
    inference(resolution,[status(thm)],[c_72,c_75])).

tff(c_46,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k1_zfmisc_1('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_311,plain,(
    ! [A_83,B_84] :
      ( k6_setfam_1(A_83,B_84) = k1_setfam_1(B_84)
      | ~ m1_subset_1(B_84,k1_zfmisc_1(k1_zfmisc_1(A_83))) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_342,plain,(
    k6_setfam_1('#skF_3','#skF_4') = k1_setfam_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_46,c_311])).

tff(c_506,plain,(
    ! [A_106,B_107] :
      ( k8_setfam_1(A_106,B_107) = k6_setfam_1(A_106,B_107)
      | k1_xboole_0 = B_107
      | ~ m1_subset_1(B_107,k1_zfmisc_1(k1_zfmisc_1(A_106))) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_533,plain,
    ( k8_setfam_1('#skF_3','#skF_4') = k6_setfam_1('#skF_3','#skF_4')
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_46,c_506])).

tff(c_551,plain,
    ( k8_setfam_1('#skF_3','#skF_4') = k1_setfam_1('#skF_4')
    | k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_342,c_533])).

tff(c_555,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_551])).

tff(c_343,plain,(
    k6_setfam_1('#skF_3','#skF_5') = k1_setfam_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_44,c_311])).

tff(c_536,plain,
    ( k8_setfam_1('#skF_3','#skF_5') = k6_setfam_1('#skF_3','#skF_5')
    | k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_44,c_506])).

tff(c_553,plain,
    ( k8_setfam_1('#skF_3','#skF_5') = k1_setfam_1('#skF_5')
    | k1_xboole_0 = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_343,c_536])).

tff(c_588,plain,
    ( k8_setfam_1('#skF_3','#skF_5') = k1_setfam_1('#skF_5')
    | '#skF_5' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_555,c_553])).

tff(c_589,plain,(
    '#skF_5' = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_588])).

tff(c_40,plain,(
    ~ r1_tarski(k8_setfam_1('#skF_3','#skF_5'),k8_setfam_1('#skF_3','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_592,plain,(
    ~ r1_tarski(k8_setfam_1('#skF_3','#skF_4'),k8_setfam_1('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_589,c_40])).

tff(c_599,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_592])).

tff(c_600,plain,(
    k8_setfam_1('#skF_3','#skF_5') = k1_setfam_1('#skF_5') ),
    inference(splitRight,[status(thm)],[c_588])).

tff(c_24,plain,(
    ! [A_20,B_21] :
      ( m1_subset_1(k8_setfam_1(A_20,B_21),k1_zfmisc_1(A_20))
      | ~ m1_subset_1(B_21,k1_zfmisc_1(k1_zfmisc_1(A_20))) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_643,plain,
    ( m1_subset_1(k1_setfam_1('#skF_5'),k1_zfmisc_1('#skF_3'))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k1_zfmisc_1('#skF_3'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_600,c_24])).

tff(c_647,plain,(
    m1_subset_1(k1_setfam_1('#skF_5'),k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_643])).

tff(c_32,plain,(
    ! [A_28,B_29] :
      ( r1_tarski(A_28,B_29)
      | ~ m1_subset_1(A_28,k1_zfmisc_1(B_29)) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_661,plain,(
    r1_tarski(k1_setfam_1('#skF_5'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_647,c_32])).

tff(c_98,plain,(
    r1_tarski('#skF_4',k1_zfmisc_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_46,c_75])).

tff(c_34,plain,(
    ! [A_28,B_29] :
      ( m1_subset_1(A_28,k1_zfmisc_1(B_29))
      | ~ r1_tarski(A_28,B_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_254,plain,(
    ! [A_76] :
      ( k8_setfam_1(A_76,k1_xboole_0) = A_76
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(A_76))) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_258,plain,(
    ! [A_76] :
      ( k8_setfam_1(A_76,k1_xboole_0) = A_76
      | ~ r1_tarski(k1_xboole_0,k1_zfmisc_1(A_76)) ) ),
    inference(resolution,[status(thm)],[c_34,c_254])).

tff(c_747,plain,(
    ! [A_123] :
      ( k8_setfam_1(A_123,'#skF_4') = A_123
      | ~ r1_tarski('#skF_4',k1_zfmisc_1(A_123)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_555,c_555,c_258])).

tff(c_759,plain,(
    k8_setfam_1('#skF_3','#skF_4') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_98,c_747])).

tff(c_639,plain,(
    ~ r1_tarski(k1_setfam_1('#skF_5'),k8_setfam_1('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_600,c_40])).

tff(c_760,plain,(
    ~ r1_tarski(k1_setfam_1('#skF_5'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_759,c_639])).

tff(c_763,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_661,c_760])).

tff(c_765,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_551])).

tff(c_42,plain,(
    r1_tarski('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_38,plain,(
    ! [B_34,A_33] :
      ( r1_tarski(k1_setfam_1(B_34),k1_setfam_1(A_33))
      | k1_xboole_0 = A_33
      | ~ r1_tarski(A_33,B_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_788,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_553])).

tff(c_790,plain,(
    '#skF_5' != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_788,c_765])).

tff(c_16,plain,(
    ! [A_14] : m1_subset_1('#skF_2'(A_14),A_14) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_30,plain,(
    ! [A_26,B_27] :
      ( r2_hidden(A_26,B_27)
      | v1_xboole_0(B_27)
      | ~ m1_subset_1(A_26,B_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_149,plain,(
    ! [A_61,B_62] :
      ( k2_xboole_0(k1_tarski(A_61),B_62) = B_62
      | ~ r2_hidden(A_61,B_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_12,plain,(
    ! [A_10,B_11] : k2_xboole_0(k1_tarski(A_10),B_11) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_161,plain,(
    ! [B_63,A_64] :
      ( k1_xboole_0 != B_63
      | ~ r2_hidden(A_64,B_63) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_149,c_12])).

tff(c_171,plain,(
    ! [B_65,A_66] :
      ( k1_xboole_0 != B_65
      | v1_xboole_0(B_65)
      | ~ m1_subset_1(A_66,B_65) ) ),
    inference(resolution,[status(thm)],[c_30,c_161])).

tff(c_195,plain,(
    ! [A_14] :
      ( k1_xboole_0 != A_14
      | v1_xboole_0(A_14) ) ),
    inference(resolution,[status(thm)],[c_16,c_171])).

tff(c_846,plain,(
    v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_788,c_195])).

tff(c_2,plain,(
    ! [A_1] :
      ( r2_hidden('#skF_1'(A_1),A_1)
      | k1_xboole_0 = A_1 ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_810,plain,(
    ! [A_1] :
      ( r2_hidden('#skF_1'(A_1),A_1)
      | A_1 = '#skF_5' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_788,c_2])).

tff(c_225,plain,(
    ! [C_71,B_72,A_73] :
      ( ~ v1_xboole_0(C_71)
      | ~ m1_subset_1(B_72,k1_zfmisc_1(C_71))
      | ~ r2_hidden(A_73,B_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_1036,plain,(
    ! [B_145,A_146,A_147] :
      ( ~ v1_xboole_0(B_145)
      | ~ r2_hidden(A_146,A_147)
      | ~ r1_tarski(A_147,B_145) ) ),
    inference(resolution,[status(thm)],[c_34,c_225])).

tff(c_1043,plain,(
    ! [B_148,A_149] :
      ( ~ v1_xboole_0(B_148)
      | ~ r1_tarski(A_149,B_148)
      | A_149 = '#skF_5' ) ),
    inference(resolution,[status(thm)],[c_810,c_1036])).

tff(c_1070,plain,
    ( ~ v1_xboole_0('#skF_5')
    | '#skF_5' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_42,c_1043])).

tff(c_1084,plain,(
    '#skF_5' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_846,c_1070])).

tff(c_1086,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_790,c_1084])).

tff(c_1087,plain,(
    k8_setfam_1('#skF_3','#skF_5') = k1_setfam_1('#skF_5') ),
    inference(splitRight,[status(thm)],[c_553])).

tff(c_764,plain,(
    k8_setfam_1('#skF_3','#skF_4') = k1_setfam_1('#skF_4') ),
    inference(splitRight,[status(thm)],[c_551])).

tff(c_766,plain,(
    ~ r1_tarski(k8_setfam_1('#skF_3','#skF_5'),k1_setfam_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_764,c_40])).

tff(c_1089,plain,(
    ~ r1_tarski(k1_setfam_1('#skF_5'),k1_setfam_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1087,c_766])).

tff(c_1101,plain,
    ( k1_xboole_0 = '#skF_4'
    | ~ r1_tarski('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_38,c_1089])).

tff(c_1104,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_1101])).

tff(c_1106,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_765,c_1104])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:03:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.91/1.46  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.91/1.47  
% 2.91/1.47  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.91/1.47  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k8_setfam_1 > k6_subset_1 > k6_setfam_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_tarski > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_1 > #skF_5 > #skF_3 > #skF_4
% 2.91/1.47  
% 2.91/1.47  %Foreground sorts:
% 2.91/1.47  
% 2.91/1.47  
% 2.91/1.47  %Background operators:
% 2.91/1.47  
% 2.91/1.47  
% 2.91/1.47  %Foreground operators:
% 2.91/1.47  tff('#skF_2', type, '#skF_2': $i > $i).
% 2.91/1.47  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.91/1.47  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.91/1.47  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.91/1.47  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.91/1.47  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.91/1.47  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.91/1.47  tff(k8_setfam_1, type, k8_setfam_1: ($i * $i) > $i).
% 2.91/1.47  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.91/1.47  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.91/1.47  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.91/1.47  tff('#skF_5', type, '#skF_5': $i).
% 2.91/1.47  tff(k6_subset_1, type, k6_subset_1: ($i * $i) > $i).
% 2.91/1.47  tff('#skF_3', type, '#skF_3': $i).
% 2.91/1.47  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.91/1.47  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.91/1.47  tff('#skF_4', type, '#skF_4': $i).
% 2.91/1.47  tff(k6_setfam_1, type, k6_setfam_1: ($i * $i) > $i).
% 2.91/1.47  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.91/1.47  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.91/1.47  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.91/1.47  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.91/1.47  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.91/1.47  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.91/1.47  
% 3.06/1.49  tff(f_107, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(A))) => (r1_tarski(B, C) => r1_tarski(k8_setfam_1(A, C), k8_setfam_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t59_setfam_1)).
% 3.06/1.49  tff(f_37, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 3.06/1.49  tff(f_53, axiom, (![A, B]: (k6_subset_1(A, B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 3.06/1.49  tff(f_48, axiom, (![A, B]: m1_subset_1(k6_subset_1(A, B), k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_subset_1)).
% 3.06/1.49  tff(f_84, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 3.06/1.49  tff(f_72, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (k6_setfam_1(A, B) = k1_setfam_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_setfam_1)).
% 3.06/1.49  tff(f_64, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => ((~(B = k1_xboole_0) => (k8_setfam_1(A, B) = k6_setfam_1(A, B))) & ((B = k1_xboole_0) => (k8_setfam_1(A, B) = A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_setfam_1)).
% 3.06/1.49  tff(f_68, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => m1_subset_1(k8_setfam_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k8_setfam_1)).
% 3.06/1.49  tff(f_97, axiom, (![A, B]: (r1_tarski(A, B) => ((A = k1_xboole_0) | r1_tarski(k1_setfam_1(B), k1_setfam_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_setfam_1)).
% 3.06/1.49  tff(f_51, axiom, (![A]: (?[B]: m1_subset_1(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', existence_m1_subset_1)).
% 3.06/1.49  tff(f_80, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 3.06/1.49  tff(f_43, axiom, (![A, B]: (r2_hidden(A, B) => (k2_xboole_0(k1_tarski(A), B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l22_zfmisc_1)).
% 3.06/1.49  tff(f_46, axiom, (![A, B]: ~(k2_xboole_0(k1_tarski(A), B) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_zfmisc_1)).
% 3.06/1.49  tff(f_33, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 3.06/1.49  tff(f_91, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_subset)).
% 3.06/1.49  tff(c_44, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k1_zfmisc_1('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_107])).
% 3.06/1.49  tff(c_6, plain, (![A_5]: (k4_xboole_0(A_5, k1_xboole_0)=A_5)), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.06/1.49  tff(c_18, plain, (![A_16, B_17]: (k6_subset_1(A_16, B_17)=k4_xboole_0(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.06/1.49  tff(c_14, plain, (![A_12, B_13]: (m1_subset_1(k6_subset_1(A_12, B_13), k1_zfmisc_1(A_12)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.06/1.49  tff(c_69, plain, (![A_43, B_44]: (m1_subset_1(k4_xboole_0(A_43, B_44), k1_zfmisc_1(A_43)))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_14])).
% 3.06/1.49  tff(c_72, plain, (![A_5]: (m1_subset_1(A_5, k1_zfmisc_1(A_5)))), inference(superposition, [status(thm), theory('equality')], [c_6, c_69])).
% 3.06/1.49  tff(c_75, plain, (![A_48, B_49]: (r1_tarski(A_48, B_49) | ~m1_subset_1(A_48, k1_zfmisc_1(B_49)))), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.06/1.49  tff(c_96, plain, (![A_5]: (r1_tarski(A_5, A_5))), inference(resolution, [status(thm)], [c_72, c_75])).
% 3.06/1.49  tff(c_46, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k1_zfmisc_1('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_107])).
% 3.06/1.49  tff(c_311, plain, (![A_83, B_84]: (k6_setfam_1(A_83, B_84)=k1_setfam_1(B_84) | ~m1_subset_1(B_84, k1_zfmisc_1(k1_zfmisc_1(A_83))))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.06/1.49  tff(c_342, plain, (k6_setfam_1('#skF_3', '#skF_4')=k1_setfam_1('#skF_4')), inference(resolution, [status(thm)], [c_46, c_311])).
% 3.06/1.49  tff(c_506, plain, (![A_106, B_107]: (k8_setfam_1(A_106, B_107)=k6_setfam_1(A_106, B_107) | k1_xboole_0=B_107 | ~m1_subset_1(B_107, k1_zfmisc_1(k1_zfmisc_1(A_106))))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.06/1.49  tff(c_533, plain, (k8_setfam_1('#skF_3', '#skF_4')=k6_setfam_1('#skF_3', '#skF_4') | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_46, c_506])).
% 3.06/1.49  tff(c_551, plain, (k8_setfam_1('#skF_3', '#skF_4')=k1_setfam_1('#skF_4') | k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_342, c_533])).
% 3.06/1.49  tff(c_555, plain, (k1_xboole_0='#skF_4'), inference(splitLeft, [status(thm)], [c_551])).
% 3.06/1.49  tff(c_343, plain, (k6_setfam_1('#skF_3', '#skF_5')=k1_setfam_1('#skF_5')), inference(resolution, [status(thm)], [c_44, c_311])).
% 3.06/1.49  tff(c_536, plain, (k8_setfam_1('#skF_3', '#skF_5')=k6_setfam_1('#skF_3', '#skF_5') | k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_44, c_506])).
% 3.06/1.49  tff(c_553, plain, (k8_setfam_1('#skF_3', '#skF_5')=k1_setfam_1('#skF_5') | k1_xboole_0='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_343, c_536])).
% 3.06/1.49  tff(c_588, plain, (k8_setfam_1('#skF_3', '#skF_5')=k1_setfam_1('#skF_5') | '#skF_5'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_555, c_553])).
% 3.06/1.49  tff(c_589, plain, ('#skF_5'='#skF_4'), inference(splitLeft, [status(thm)], [c_588])).
% 3.06/1.49  tff(c_40, plain, (~r1_tarski(k8_setfam_1('#skF_3', '#skF_5'), k8_setfam_1('#skF_3', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_107])).
% 3.06/1.49  tff(c_592, plain, (~r1_tarski(k8_setfam_1('#skF_3', '#skF_4'), k8_setfam_1('#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_589, c_40])).
% 3.06/1.49  tff(c_599, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_96, c_592])).
% 3.06/1.49  tff(c_600, plain, (k8_setfam_1('#skF_3', '#skF_5')=k1_setfam_1('#skF_5')), inference(splitRight, [status(thm)], [c_588])).
% 3.06/1.49  tff(c_24, plain, (![A_20, B_21]: (m1_subset_1(k8_setfam_1(A_20, B_21), k1_zfmisc_1(A_20)) | ~m1_subset_1(B_21, k1_zfmisc_1(k1_zfmisc_1(A_20))))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.06/1.49  tff(c_643, plain, (m1_subset_1(k1_setfam_1('#skF_5'), k1_zfmisc_1('#skF_3')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k1_zfmisc_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_600, c_24])).
% 3.06/1.49  tff(c_647, plain, (m1_subset_1(k1_setfam_1('#skF_5'), k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_643])).
% 3.06/1.49  tff(c_32, plain, (![A_28, B_29]: (r1_tarski(A_28, B_29) | ~m1_subset_1(A_28, k1_zfmisc_1(B_29)))), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.06/1.49  tff(c_661, plain, (r1_tarski(k1_setfam_1('#skF_5'), '#skF_3')), inference(resolution, [status(thm)], [c_647, c_32])).
% 3.06/1.49  tff(c_98, plain, (r1_tarski('#skF_4', k1_zfmisc_1('#skF_3'))), inference(resolution, [status(thm)], [c_46, c_75])).
% 3.06/1.49  tff(c_34, plain, (![A_28, B_29]: (m1_subset_1(A_28, k1_zfmisc_1(B_29)) | ~r1_tarski(A_28, B_29))), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.06/1.49  tff(c_254, plain, (![A_76]: (k8_setfam_1(A_76, k1_xboole_0)=A_76 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_zfmisc_1(A_76))))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.06/1.49  tff(c_258, plain, (![A_76]: (k8_setfam_1(A_76, k1_xboole_0)=A_76 | ~r1_tarski(k1_xboole_0, k1_zfmisc_1(A_76)))), inference(resolution, [status(thm)], [c_34, c_254])).
% 3.06/1.49  tff(c_747, plain, (![A_123]: (k8_setfam_1(A_123, '#skF_4')=A_123 | ~r1_tarski('#skF_4', k1_zfmisc_1(A_123)))), inference(demodulation, [status(thm), theory('equality')], [c_555, c_555, c_258])).
% 3.06/1.49  tff(c_759, plain, (k8_setfam_1('#skF_3', '#skF_4')='#skF_3'), inference(resolution, [status(thm)], [c_98, c_747])).
% 3.06/1.49  tff(c_639, plain, (~r1_tarski(k1_setfam_1('#skF_5'), k8_setfam_1('#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_600, c_40])).
% 3.06/1.49  tff(c_760, plain, (~r1_tarski(k1_setfam_1('#skF_5'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_759, c_639])).
% 3.06/1.49  tff(c_763, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_661, c_760])).
% 3.06/1.49  tff(c_765, plain, (k1_xboole_0!='#skF_4'), inference(splitRight, [status(thm)], [c_551])).
% 3.06/1.49  tff(c_42, plain, (r1_tarski('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_107])).
% 3.06/1.49  tff(c_38, plain, (![B_34, A_33]: (r1_tarski(k1_setfam_1(B_34), k1_setfam_1(A_33)) | k1_xboole_0=A_33 | ~r1_tarski(A_33, B_34))), inference(cnfTransformation, [status(thm)], [f_97])).
% 3.06/1.49  tff(c_788, plain, (k1_xboole_0='#skF_5'), inference(splitLeft, [status(thm)], [c_553])).
% 3.06/1.49  tff(c_790, plain, ('#skF_5'!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_788, c_765])).
% 3.06/1.49  tff(c_16, plain, (![A_14]: (m1_subset_1('#skF_2'(A_14), A_14))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.06/1.49  tff(c_30, plain, (![A_26, B_27]: (r2_hidden(A_26, B_27) | v1_xboole_0(B_27) | ~m1_subset_1(A_26, B_27))), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.06/1.49  tff(c_149, plain, (![A_61, B_62]: (k2_xboole_0(k1_tarski(A_61), B_62)=B_62 | ~r2_hidden(A_61, B_62))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.06/1.49  tff(c_12, plain, (![A_10, B_11]: (k2_xboole_0(k1_tarski(A_10), B_11)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.06/1.49  tff(c_161, plain, (![B_63, A_64]: (k1_xboole_0!=B_63 | ~r2_hidden(A_64, B_63))), inference(superposition, [status(thm), theory('equality')], [c_149, c_12])).
% 3.06/1.49  tff(c_171, plain, (![B_65, A_66]: (k1_xboole_0!=B_65 | v1_xboole_0(B_65) | ~m1_subset_1(A_66, B_65))), inference(resolution, [status(thm)], [c_30, c_161])).
% 3.06/1.49  tff(c_195, plain, (![A_14]: (k1_xboole_0!=A_14 | v1_xboole_0(A_14))), inference(resolution, [status(thm)], [c_16, c_171])).
% 3.06/1.49  tff(c_846, plain, (v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_788, c_195])).
% 3.06/1.49  tff(c_2, plain, (![A_1]: (r2_hidden('#skF_1'(A_1), A_1) | k1_xboole_0=A_1)), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.06/1.49  tff(c_810, plain, (![A_1]: (r2_hidden('#skF_1'(A_1), A_1) | A_1='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_788, c_2])).
% 3.06/1.49  tff(c_225, plain, (![C_71, B_72, A_73]: (~v1_xboole_0(C_71) | ~m1_subset_1(B_72, k1_zfmisc_1(C_71)) | ~r2_hidden(A_73, B_72))), inference(cnfTransformation, [status(thm)], [f_91])).
% 3.06/1.49  tff(c_1036, plain, (![B_145, A_146, A_147]: (~v1_xboole_0(B_145) | ~r2_hidden(A_146, A_147) | ~r1_tarski(A_147, B_145))), inference(resolution, [status(thm)], [c_34, c_225])).
% 3.06/1.49  tff(c_1043, plain, (![B_148, A_149]: (~v1_xboole_0(B_148) | ~r1_tarski(A_149, B_148) | A_149='#skF_5')), inference(resolution, [status(thm)], [c_810, c_1036])).
% 3.06/1.49  tff(c_1070, plain, (~v1_xboole_0('#skF_5') | '#skF_5'='#skF_4'), inference(resolution, [status(thm)], [c_42, c_1043])).
% 3.06/1.49  tff(c_1084, plain, ('#skF_5'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_846, c_1070])).
% 3.06/1.49  tff(c_1086, plain, $false, inference(negUnitSimplification, [status(thm)], [c_790, c_1084])).
% 3.06/1.49  tff(c_1087, plain, (k8_setfam_1('#skF_3', '#skF_5')=k1_setfam_1('#skF_5')), inference(splitRight, [status(thm)], [c_553])).
% 3.06/1.49  tff(c_764, plain, (k8_setfam_1('#skF_3', '#skF_4')=k1_setfam_1('#skF_4')), inference(splitRight, [status(thm)], [c_551])).
% 3.06/1.49  tff(c_766, plain, (~r1_tarski(k8_setfam_1('#skF_3', '#skF_5'), k1_setfam_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_764, c_40])).
% 3.06/1.49  tff(c_1089, plain, (~r1_tarski(k1_setfam_1('#skF_5'), k1_setfam_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_1087, c_766])).
% 3.06/1.49  tff(c_1101, plain, (k1_xboole_0='#skF_4' | ~r1_tarski('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_38, c_1089])).
% 3.06/1.49  tff(c_1104, plain, (k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_42, c_1101])).
% 3.06/1.49  tff(c_1106, plain, $false, inference(negUnitSimplification, [status(thm)], [c_765, c_1104])).
% 3.06/1.49  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.06/1.49  
% 3.06/1.49  Inference rules
% 3.06/1.49  ----------------------
% 3.06/1.49  #Ref     : 1
% 3.06/1.49  #Sup     : 225
% 3.06/1.49  #Fact    : 0
% 3.06/1.49  #Define  : 0
% 3.06/1.49  #Split   : 7
% 3.06/1.49  #Chain   : 0
% 3.06/1.49  #Close   : 0
% 3.06/1.49  
% 3.06/1.49  Ordering : KBO
% 3.06/1.49  
% 3.06/1.49  Simplification rules
% 3.06/1.49  ----------------------
% 3.06/1.49  #Subsume      : 56
% 3.06/1.49  #Demod        : 112
% 3.06/1.49  #Tautology    : 98
% 3.06/1.49  #SimpNegUnit  : 7
% 3.06/1.49  #BackRed      : 61
% 3.06/1.49  
% 3.06/1.49  #Partial instantiations: 0
% 3.06/1.49  #Strategies tried      : 1
% 3.06/1.49  
% 3.06/1.49  Timing (in seconds)
% 3.06/1.49  ----------------------
% 3.06/1.49  Preprocessing        : 0.31
% 3.06/1.49  Parsing              : 0.17
% 3.06/1.49  CNF conversion       : 0.02
% 3.06/1.49  Main loop            : 0.40
% 3.06/1.49  Inferencing          : 0.14
% 3.06/1.49  Reduction            : 0.13
% 3.06/1.49  Demodulation         : 0.09
% 3.06/1.49  BG Simplification    : 0.02
% 3.06/1.49  Subsumption          : 0.07
% 3.06/1.49  Abstraction          : 0.02
% 3.06/1.49  MUC search           : 0.00
% 3.06/1.49  Cooper               : 0.00
% 3.06/1.49  Total                : 0.75
% 3.06/1.49  Index Insertion      : 0.00
% 3.06/1.49  Index Deletion       : 0.00
% 3.06/1.49  Index Matching       : 0.00
% 3.06/1.49  BG Taut test         : 0.00
%------------------------------------------------------------------------------
