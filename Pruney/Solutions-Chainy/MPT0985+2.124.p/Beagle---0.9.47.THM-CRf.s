%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:12:46 EST 2020

% Result     : Theorem 3.34s
% Output     : CNFRefutation 3.49s
% Verified   : 
% Statistics : Number of formulae       :  100 ( 231 expanded)
%              Number of leaves         :   32 (  91 expanded)
%              Depth                    :    9
%              Number of atoms          :  171 ( 639 expanded)
%              Number of equality atoms :   25 (  86 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k7_relat_1 > k3_xboole_0 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff(k2_funct_1,type,(
    k2_funct_1: $i > $i )).

tff(v2_funct_1,type,(
    v2_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_110,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( ( v2_funct_1(C)
            & k2_relset_1(A,B,C) = B )
         => ( v1_funct_1(k2_funct_1(C))
            & v1_funct_2(k2_funct_1(C),B,A)
            & m1_subset_1(k2_funct_1(C),k1_zfmisc_1(k2_zfmisc_1(B,A))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_funct_2)).

tff(f_69,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_73,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k7_relat_1(B,A) = k3_xboole_0(B,k2_zfmisc_1(A,k2_relat_1(B))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t96_relat_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k1_relat_1(k7_relat_1(B,A)),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_relat_1)).

tff(f_65,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k2_relat_1(A) = k1_relat_1(k2_funct_1(A))
          & k1_relat_1(A) = k2_relat_1(k2_funct_1(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_55,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).

tff(f_81,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( ( r1_tarski(k1_relat_1(C),A)
          & r1_tarski(k2_relat_1(C),B) )
       => m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_relset_1)).

tff(f_93,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r1_tarski(k2_relat_1(B),A)
       => ( v1_funct_1(B)
          & v1_funct_2(B,k1_relat_1(B),A)
          & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B),A))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_funct_2)).

tff(c_44,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_456,plain,(
    ! [C_88,A_89,B_90] :
      ( v1_relat_1(C_88)
      | ~ m1_subset_1(C_88,k1_zfmisc_1(k2_zfmisc_1(A_89,B_90))) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_469,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_44,c_456])).

tff(c_40,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_529,plain,(
    ! [A_103,B_104,C_105] :
      ( k2_relset_1(A_103,B_104,C_105) = k2_relat_1(C_105)
      | ~ m1_subset_1(C_105,k1_zfmisc_1(k2_zfmisc_1(A_103,B_104))) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_539,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_44,c_529])).

tff(c_543,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_539])).

tff(c_16,plain,(
    ! [B_10,A_9] :
      ( k3_xboole_0(B_10,k2_zfmisc_1(A_9,k2_relat_1(B_10))) = k7_relat_1(B_10,A_9)
      | ~ v1_relat_1(B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_547,plain,(
    ! [A_9] :
      ( k3_xboole_0('#skF_3',k2_zfmisc_1(A_9,'#skF_2')) = k7_relat_1('#skF_3',A_9)
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_543,c_16])).

tff(c_557,plain,(
    ! [A_106] : k3_xboole_0('#skF_3',k2_zfmisc_1(A_106,'#skF_2')) = k7_relat_1('#skF_3',A_106) ),
    inference(demodulation,[status(thm),theory(equality)],[c_469,c_547])).

tff(c_57,plain,(
    ! [A_28,B_29] :
      ( r1_tarski(A_28,B_29)
      | ~ m1_subset_1(A_28,k1_zfmisc_1(B_29)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_65,plain,(
    r1_tarski('#skF_3',k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_44,c_57])).

tff(c_131,plain,(
    ! [A_42,B_43] :
      ( k3_xboole_0(A_42,B_43) = A_42
      | ~ r1_tarski(A_42,B_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_138,plain,(
    k3_xboole_0('#skF_3',k2_zfmisc_1('#skF_1','#skF_2')) = '#skF_3' ),
    inference(resolution,[status(thm)],[c_65,c_131])).

tff(c_563,plain,(
    k7_relat_1('#skF_3','#skF_1') = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_557,c_138])).

tff(c_14,plain,(
    ! [B_8,A_7] :
      ( r1_tarski(k1_relat_1(k7_relat_1(B_8,A_7)),A_7)
      | ~ v1_relat_1(B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_575,plain,
    ( r1_tarski(k1_relat_1('#skF_3'),'#skF_1')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_563,c_14])).

tff(c_579,plain,(
    r1_tarski(k1_relat_1('#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_469,c_575])).

tff(c_48,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_42,plain,(
    v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_22,plain,(
    ! [A_12] :
      ( k2_relat_1(k2_funct_1(A_12)) = k1_relat_1(A_12)
      | ~ v2_funct_1(A_12)
      | ~ v1_funct_1(A_12)
      | ~ v1_relat_1(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_163,plain,(
    ! [C_47,A_48,B_49] :
      ( v1_relat_1(C_47)
      | ~ m1_subset_1(C_47,k1_zfmisc_1(k2_zfmisc_1(A_48,B_49))) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_172,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_44,c_163])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_235,plain,(
    ! [A_64,B_65,C_66] :
      ( k2_relset_1(A_64,B_65,C_66) = k2_relat_1(C_66)
      | ~ m1_subset_1(C_66,k1_zfmisc_1(k2_zfmisc_1(A_64,B_65))) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_242,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_44,c_235])).

tff(c_245,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_242])).

tff(c_24,plain,(
    ! [A_12] :
      ( k1_relat_1(k2_funct_1(A_12)) = k2_relat_1(A_12)
      | ~ v2_funct_1(A_12)
      | ~ v1_funct_1(A_12)
      | ~ v1_relat_1(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_249,plain,(
    ! [A_9] :
      ( k3_xboole_0('#skF_3',k2_zfmisc_1(A_9,'#skF_2')) = k7_relat_1('#skF_3',A_9)
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_245,c_16])).

tff(c_259,plain,(
    ! [A_69] : k3_xboole_0('#skF_3',k2_zfmisc_1(A_69,'#skF_2')) = k7_relat_1('#skF_3',A_69) ),
    inference(demodulation,[status(thm),theory(equality)],[c_172,c_249])).

tff(c_265,plain,(
    k7_relat_1('#skF_3','#skF_1') = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_259,c_138])).

tff(c_277,plain,
    ( r1_tarski(k1_relat_1('#skF_3'),'#skF_1')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_265,c_14])).

tff(c_281,plain,(
    r1_tarski(k1_relat_1('#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_172,c_277])).

tff(c_20,plain,(
    ! [A_11] :
      ( v1_relat_1(k2_funct_1(A_11))
      | ~ v1_funct_1(A_11)
      | ~ v1_relat_1(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_376,plain,(
    ! [C_83,A_84,B_85] :
      ( m1_subset_1(C_83,k1_zfmisc_1(k2_zfmisc_1(A_84,B_85)))
      | ~ r1_tarski(k2_relat_1(C_83),B_85)
      | ~ r1_tarski(k1_relat_1(C_83),A_84)
      | ~ v1_relat_1(C_83) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_18,plain,(
    ! [A_11] :
      ( v1_funct_1(k2_funct_1(A_11))
      | ~ v1_funct_1(A_11)
      | ~ v1_relat_1(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_38,plain,
    ( ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_66,plain,(
    ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_38])).

tff(c_69,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_18,c_66])).

tff(c_72,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_69])).

tff(c_115,plain,(
    ! [C_38,A_39,B_40] :
      ( v1_relat_1(C_38)
      | ~ m1_subset_1(C_38,k1_zfmisc_1(k2_zfmisc_1(A_39,B_40))) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_122,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_44,c_115])).

tff(c_127,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_122])).

tff(c_128,plain,
    ( ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_38])).

tff(c_158,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_128])).

tff(c_391,plain,
    ( ~ r1_tarski(k2_relat_1(k2_funct_1('#skF_3')),'#skF_1')
    | ~ r1_tarski(k1_relat_1(k2_funct_1('#skF_3')),'#skF_2')
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_376,c_158])).

tff(c_393,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_391])).

tff(c_396,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_20,c_393])).

tff(c_400,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_172,c_48,c_396])).

tff(c_401,plain,
    ( ~ r1_tarski(k1_relat_1(k2_funct_1('#skF_3')),'#skF_2')
    | ~ r1_tarski(k2_relat_1(k2_funct_1('#skF_3')),'#skF_1') ),
    inference(splitRight,[status(thm)],[c_391])).

tff(c_403,plain,(
    ~ r1_tarski(k2_relat_1(k2_funct_1('#skF_3')),'#skF_1') ),
    inference(splitLeft,[status(thm)],[c_401])).

tff(c_406,plain,
    ( ~ r1_tarski(k1_relat_1('#skF_3'),'#skF_1')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_403])).

tff(c_409,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_172,c_48,c_42,c_281,c_406])).

tff(c_410,plain,(
    ~ r1_tarski(k1_relat_1(k2_funct_1('#skF_3')),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_401])).

tff(c_426,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_3'),'#skF_2')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_410])).

tff(c_429,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_172,c_48,c_42,c_6,c_245,c_426])).

tff(c_431,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_128])).

tff(c_467,plain,(
    v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_431,c_456])).

tff(c_129,plain,(
    v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_38])).

tff(c_594,plain,(
    ! [B_107,A_108] :
      ( v1_funct_2(B_107,k1_relat_1(B_107),A_108)
      | ~ r1_tarski(k2_relat_1(B_107),A_108)
      | ~ v1_funct_1(B_107)
      | ~ v1_relat_1(B_107) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_1221,plain,(
    ! [A_156,A_157] :
      ( v1_funct_2(k2_funct_1(A_156),k2_relat_1(A_156),A_157)
      | ~ r1_tarski(k2_relat_1(k2_funct_1(A_156)),A_157)
      | ~ v1_funct_1(k2_funct_1(A_156))
      | ~ v1_relat_1(k2_funct_1(A_156))
      | ~ v2_funct_1(A_156)
      | ~ v1_funct_1(A_156)
      | ~ v1_relat_1(A_156) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_594])).

tff(c_1224,plain,(
    ! [A_157] :
      ( v1_funct_2(k2_funct_1('#skF_3'),'#skF_2',A_157)
      | ~ r1_tarski(k2_relat_1(k2_funct_1('#skF_3')),A_157)
      | ~ v1_funct_1(k2_funct_1('#skF_3'))
      | ~ v1_relat_1(k2_funct_1('#skF_3'))
      | ~ v2_funct_1('#skF_3')
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_543,c_1221])).

tff(c_1252,plain,(
    ! [A_159] :
      ( v1_funct_2(k2_funct_1('#skF_3'),'#skF_2',A_159)
      | ~ r1_tarski(k2_relat_1(k2_funct_1('#skF_3')),A_159) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_469,c_48,c_42,c_467,c_129,c_1224])).

tff(c_1263,plain,(
    ! [A_159] :
      ( v1_funct_2(k2_funct_1('#skF_3'),'#skF_2',A_159)
      | ~ r1_tarski(k1_relat_1('#skF_3'),A_159)
      | ~ v2_funct_1('#skF_3')
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_1252])).

tff(c_1279,plain,(
    ! [A_160] :
      ( v1_funct_2(k2_funct_1('#skF_3'),'#skF_2',A_160)
      | ~ r1_tarski(k1_relat_1('#skF_3'),A_160) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_469,c_48,c_42,c_1263])).

tff(c_430,plain,(
    ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_128])).

tff(c_1282,plain,(
    ~ r1_tarski(k1_relat_1('#skF_3'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_1279,c_430])).

tff(c_1286,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_579,c_1282])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:38:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.34/1.51  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.34/1.52  
% 3.34/1.52  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.34/1.52  %$ v1_funct_2 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k7_relat_1 > k3_xboole_0 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 3.34/1.52  
% 3.34/1.52  %Foreground sorts:
% 3.34/1.52  
% 3.34/1.52  
% 3.34/1.52  %Background operators:
% 3.34/1.52  
% 3.34/1.52  
% 3.34/1.52  %Foreground operators:
% 3.34/1.52  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 3.34/1.52  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.34/1.52  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 3.34/1.52  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 3.34/1.52  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.34/1.52  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 3.34/1.52  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.34/1.52  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.34/1.52  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.34/1.52  tff('#skF_2', type, '#skF_2': $i).
% 3.34/1.52  tff('#skF_3', type, '#skF_3': $i).
% 3.34/1.52  tff('#skF_1', type, '#skF_1': $i).
% 3.34/1.52  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.34/1.52  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.34/1.52  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.34/1.52  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.34/1.52  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.34/1.52  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.34/1.52  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.34/1.52  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.34/1.52  
% 3.49/1.54  tff(f_110, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((v2_funct_1(C) & (k2_relset_1(A, B, C) = B)) => ((v1_funct_1(k2_funct_1(C)) & v1_funct_2(k2_funct_1(C), B, A)) & m1_subset_1(k2_funct_1(C), k1_zfmisc_1(k2_zfmisc_1(B, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_funct_2)).
% 3.49/1.54  tff(f_69, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.49/1.54  tff(f_73, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 3.49/1.54  tff(f_47, axiom, (![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k3_xboole_0(B, k2_zfmisc_1(A, k2_relat_1(B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t96_relat_1)).
% 3.49/1.54  tff(f_39, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 3.49/1.54  tff(f_35, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 3.49/1.54  tff(f_43, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k7_relat_1(B, A)), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t87_relat_1)).
% 3.49/1.54  tff(f_65, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k2_relat_1(A) = k1_relat_1(k2_funct_1(A))) & (k1_relat_1(A) = k2_relat_1(k2_funct_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_funct_1)).
% 3.49/1.54  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.49/1.54  tff(f_55, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 3.49/1.54  tff(f_81, axiom, (![A, B, C]: (v1_relat_1(C) => ((r1_tarski(k1_relat_1(C), A) & r1_tarski(k2_relat_1(C), B)) => m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_relset_1)).
% 3.49/1.54  tff(f_93, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r1_tarski(k2_relat_1(B), A) => ((v1_funct_1(B) & v1_funct_2(B, k1_relat_1(B), A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B), A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_funct_2)).
% 3.49/1.54  tff(c_44, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_110])).
% 3.49/1.54  tff(c_456, plain, (![C_88, A_89, B_90]: (v1_relat_1(C_88) | ~m1_subset_1(C_88, k1_zfmisc_1(k2_zfmisc_1(A_89, B_90))))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.49/1.54  tff(c_469, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_44, c_456])).
% 3.49/1.54  tff(c_40, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_2'), inference(cnfTransformation, [status(thm)], [f_110])).
% 3.49/1.54  tff(c_529, plain, (![A_103, B_104, C_105]: (k2_relset_1(A_103, B_104, C_105)=k2_relat_1(C_105) | ~m1_subset_1(C_105, k1_zfmisc_1(k2_zfmisc_1(A_103, B_104))))), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.49/1.54  tff(c_539, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_44, c_529])).
% 3.49/1.54  tff(c_543, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_40, c_539])).
% 3.49/1.54  tff(c_16, plain, (![B_10, A_9]: (k3_xboole_0(B_10, k2_zfmisc_1(A_9, k2_relat_1(B_10)))=k7_relat_1(B_10, A_9) | ~v1_relat_1(B_10))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.49/1.54  tff(c_547, plain, (![A_9]: (k3_xboole_0('#skF_3', k2_zfmisc_1(A_9, '#skF_2'))=k7_relat_1('#skF_3', A_9) | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_543, c_16])).
% 3.49/1.54  tff(c_557, plain, (![A_106]: (k3_xboole_0('#skF_3', k2_zfmisc_1(A_106, '#skF_2'))=k7_relat_1('#skF_3', A_106))), inference(demodulation, [status(thm), theory('equality')], [c_469, c_547])).
% 3.49/1.54  tff(c_57, plain, (![A_28, B_29]: (r1_tarski(A_28, B_29) | ~m1_subset_1(A_28, k1_zfmisc_1(B_29)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.49/1.54  tff(c_65, plain, (r1_tarski('#skF_3', k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_44, c_57])).
% 3.49/1.54  tff(c_131, plain, (![A_42, B_43]: (k3_xboole_0(A_42, B_43)=A_42 | ~r1_tarski(A_42, B_43))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.49/1.54  tff(c_138, plain, (k3_xboole_0('#skF_3', k2_zfmisc_1('#skF_1', '#skF_2'))='#skF_3'), inference(resolution, [status(thm)], [c_65, c_131])).
% 3.49/1.54  tff(c_563, plain, (k7_relat_1('#skF_3', '#skF_1')='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_557, c_138])).
% 3.49/1.54  tff(c_14, plain, (![B_8, A_7]: (r1_tarski(k1_relat_1(k7_relat_1(B_8, A_7)), A_7) | ~v1_relat_1(B_8))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.49/1.54  tff(c_575, plain, (r1_tarski(k1_relat_1('#skF_3'), '#skF_1') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_563, c_14])).
% 3.49/1.54  tff(c_579, plain, (r1_tarski(k1_relat_1('#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_469, c_575])).
% 3.49/1.54  tff(c_48, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_110])).
% 3.49/1.54  tff(c_42, plain, (v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_110])).
% 3.49/1.54  tff(c_22, plain, (![A_12]: (k2_relat_1(k2_funct_1(A_12))=k1_relat_1(A_12) | ~v2_funct_1(A_12) | ~v1_funct_1(A_12) | ~v1_relat_1(A_12))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.49/1.54  tff(c_163, plain, (![C_47, A_48, B_49]: (v1_relat_1(C_47) | ~m1_subset_1(C_47, k1_zfmisc_1(k2_zfmisc_1(A_48, B_49))))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.49/1.54  tff(c_172, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_44, c_163])).
% 3.49/1.54  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.49/1.54  tff(c_235, plain, (![A_64, B_65, C_66]: (k2_relset_1(A_64, B_65, C_66)=k2_relat_1(C_66) | ~m1_subset_1(C_66, k1_zfmisc_1(k2_zfmisc_1(A_64, B_65))))), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.49/1.54  tff(c_242, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_44, c_235])).
% 3.49/1.54  tff(c_245, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_40, c_242])).
% 3.49/1.54  tff(c_24, plain, (![A_12]: (k1_relat_1(k2_funct_1(A_12))=k2_relat_1(A_12) | ~v2_funct_1(A_12) | ~v1_funct_1(A_12) | ~v1_relat_1(A_12))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.49/1.54  tff(c_249, plain, (![A_9]: (k3_xboole_0('#skF_3', k2_zfmisc_1(A_9, '#skF_2'))=k7_relat_1('#skF_3', A_9) | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_245, c_16])).
% 3.49/1.54  tff(c_259, plain, (![A_69]: (k3_xboole_0('#skF_3', k2_zfmisc_1(A_69, '#skF_2'))=k7_relat_1('#skF_3', A_69))), inference(demodulation, [status(thm), theory('equality')], [c_172, c_249])).
% 3.49/1.54  tff(c_265, plain, (k7_relat_1('#skF_3', '#skF_1')='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_259, c_138])).
% 3.49/1.54  tff(c_277, plain, (r1_tarski(k1_relat_1('#skF_3'), '#skF_1') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_265, c_14])).
% 3.49/1.54  tff(c_281, plain, (r1_tarski(k1_relat_1('#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_172, c_277])).
% 3.49/1.54  tff(c_20, plain, (![A_11]: (v1_relat_1(k2_funct_1(A_11)) | ~v1_funct_1(A_11) | ~v1_relat_1(A_11))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.49/1.54  tff(c_376, plain, (![C_83, A_84, B_85]: (m1_subset_1(C_83, k1_zfmisc_1(k2_zfmisc_1(A_84, B_85))) | ~r1_tarski(k2_relat_1(C_83), B_85) | ~r1_tarski(k1_relat_1(C_83), A_84) | ~v1_relat_1(C_83))), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.49/1.54  tff(c_18, plain, (![A_11]: (v1_funct_1(k2_funct_1(A_11)) | ~v1_funct_1(A_11) | ~v1_relat_1(A_11))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.49/1.54  tff(c_38, plain, (~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | ~v1_funct_1(k2_funct_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_110])).
% 3.49/1.54  tff(c_66, plain, (~v1_funct_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_38])).
% 3.49/1.54  tff(c_69, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_18, c_66])).
% 3.49/1.54  tff(c_72, plain, (~v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_69])).
% 3.49/1.54  tff(c_115, plain, (![C_38, A_39, B_40]: (v1_relat_1(C_38) | ~m1_subset_1(C_38, k1_zfmisc_1(k2_zfmisc_1(A_39, B_40))))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.49/1.54  tff(c_122, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_44, c_115])).
% 3.49/1.54  tff(c_127, plain, $false, inference(negUnitSimplification, [status(thm)], [c_72, c_122])).
% 3.49/1.54  tff(c_128, plain, (~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | ~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(splitRight, [status(thm)], [c_38])).
% 3.49/1.54  tff(c_158, plain, (~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(splitLeft, [status(thm)], [c_128])).
% 3.49/1.54  tff(c_391, plain, (~r1_tarski(k2_relat_1(k2_funct_1('#skF_3')), '#skF_1') | ~r1_tarski(k1_relat_1(k2_funct_1('#skF_3')), '#skF_2') | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_376, c_158])).
% 3.49/1.54  tff(c_393, plain, (~v1_relat_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_391])).
% 3.49/1.54  tff(c_396, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_20, c_393])).
% 3.49/1.54  tff(c_400, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_172, c_48, c_396])).
% 3.49/1.54  tff(c_401, plain, (~r1_tarski(k1_relat_1(k2_funct_1('#skF_3')), '#skF_2') | ~r1_tarski(k2_relat_1(k2_funct_1('#skF_3')), '#skF_1')), inference(splitRight, [status(thm)], [c_391])).
% 3.49/1.54  tff(c_403, plain, (~r1_tarski(k2_relat_1(k2_funct_1('#skF_3')), '#skF_1')), inference(splitLeft, [status(thm)], [c_401])).
% 3.49/1.54  tff(c_406, plain, (~r1_tarski(k1_relat_1('#skF_3'), '#skF_1') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_22, c_403])).
% 3.49/1.54  tff(c_409, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_172, c_48, c_42, c_281, c_406])).
% 3.49/1.54  tff(c_410, plain, (~r1_tarski(k1_relat_1(k2_funct_1('#skF_3')), '#skF_2')), inference(splitRight, [status(thm)], [c_401])).
% 3.49/1.54  tff(c_426, plain, (~r1_tarski(k2_relat_1('#skF_3'), '#skF_2') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_24, c_410])).
% 3.49/1.54  tff(c_429, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_172, c_48, c_42, c_6, c_245, c_426])).
% 3.49/1.54  tff(c_431, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(splitRight, [status(thm)], [c_128])).
% 3.49/1.54  tff(c_467, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_431, c_456])).
% 3.49/1.54  tff(c_129, plain, (v1_funct_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_38])).
% 3.49/1.54  tff(c_594, plain, (![B_107, A_108]: (v1_funct_2(B_107, k1_relat_1(B_107), A_108) | ~r1_tarski(k2_relat_1(B_107), A_108) | ~v1_funct_1(B_107) | ~v1_relat_1(B_107))), inference(cnfTransformation, [status(thm)], [f_93])).
% 3.49/1.54  tff(c_1221, plain, (![A_156, A_157]: (v1_funct_2(k2_funct_1(A_156), k2_relat_1(A_156), A_157) | ~r1_tarski(k2_relat_1(k2_funct_1(A_156)), A_157) | ~v1_funct_1(k2_funct_1(A_156)) | ~v1_relat_1(k2_funct_1(A_156)) | ~v2_funct_1(A_156) | ~v1_funct_1(A_156) | ~v1_relat_1(A_156))), inference(superposition, [status(thm), theory('equality')], [c_24, c_594])).
% 3.49/1.54  tff(c_1224, plain, (![A_157]: (v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', A_157) | ~r1_tarski(k2_relat_1(k2_funct_1('#skF_3')), A_157) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_543, c_1221])).
% 3.49/1.54  tff(c_1252, plain, (![A_159]: (v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', A_159) | ~r1_tarski(k2_relat_1(k2_funct_1('#skF_3')), A_159))), inference(demodulation, [status(thm), theory('equality')], [c_469, c_48, c_42, c_467, c_129, c_1224])).
% 3.49/1.54  tff(c_1263, plain, (![A_159]: (v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', A_159) | ~r1_tarski(k1_relat_1('#skF_3'), A_159) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_22, c_1252])).
% 3.49/1.54  tff(c_1279, plain, (![A_160]: (v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', A_160) | ~r1_tarski(k1_relat_1('#skF_3'), A_160))), inference(demodulation, [status(thm), theory('equality')], [c_469, c_48, c_42, c_1263])).
% 3.49/1.54  tff(c_430, plain, (~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_128])).
% 3.49/1.54  tff(c_1282, plain, (~r1_tarski(k1_relat_1('#skF_3'), '#skF_1')), inference(resolution, [status(thm)], [c_1279, c_430])).
% 3.49/1.54  tff(c_1286, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_579, c_1282])).
% 3.49/1.54  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.49/1.54  
% 3.49/1.54  Inference rules
% 3.49/1.54  ----------------------
% 3.49/1.54  #Ref     : 0
% 3.49/1.54  #Sup     : 276
% 3.49/1.54  #Fact    : 0
% 3.49/1.54  #Define  : 0
% 3.49/1.54  #Split   : 13
% 3.49/1.54  #Chain   : 0
% 3.49/1.54  #Close   : 0
% 3.49/1.54  
% 3.49/1.54  Ordering : KBO
% 3.49/1.54  
% 3.49/1.54  Simplification rules
% 3.49/1.54  ----------------------
% 3.49/1.54  #Subsume      : 7
% 3.49/1.54  #Demod        : 163
% 3.49/1.54  #Tautology    : 132
% 3.49/1.54  #SimpNegUnit  : 1
% 3.49/1.54  #BackRed      : 0
% 3.49/1.54  
% 3.49/1.54  #Partial instantiations: 0
% 3.49/1.54  #Strategies tried      : 1
% 3.49/1.54  
% 3.49/1.54  Timing (in seconds)
% 3.49/1.54  ----------------------
% 3.49/1.55  Preprocessing        : 0.33
% 3.49/1.55  Parsing              : 0.18
% 3.49/1.55  CNF conversion       : 0.02
% 3.49/1.55  Main loop            : 0.45
% 3.49/1.55  Inferencing          : 0.17
% 3.49/1.55  Reduction            : 0.13
% 3.49/1.55  Demodulation         : 0.09
% 3.49/1.55  BG Simplification    : 0.02
% 3.49/1.55  Subsumption          : 0.08
% 3.49/1.55  Abstraction          : 0.02
% 3.49/1.55  MUC search           : 0.00
% 3.49/1.55  Cooper               : 0.00
% 3.49/1.55  Total                : 0.81
% 3.49/1.55  Index Insertion      : 0.00
% 3.49/1.55  Index Deletion       : 0.00
% 3.49/1.55  Index Matching       : 0.00
% 3.49/1.55  BG Taut test         : 0.00
%------------------------------------------------------------------------------
