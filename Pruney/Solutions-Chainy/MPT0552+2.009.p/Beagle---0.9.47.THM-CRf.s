%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:00:58 EST 2020

% Result     : Theorem 20.96s
% Output     : CNFRefutation 21.07s
% Verified   : 
% Statistics : Number of formulae       :   98 ( 253 expanded)
%              Number of leaves         :   30 (  97 expanded)
%              Depth                    :   10
%              Number of atoms          :  171 ( 520 expanded)
%              Number of equality atoms :   25 (  86 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > k9_relat_1 > k7_relat_1 > k3_xboole_0 > k2_tarski > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_setfam_1 > k1_relat_1 > #skF_1 > #skF_5 > #skF_3 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_89,negated_conjecture,(
    ~ ! [A,B,C] :
        ( v1_relat_1(C)
       => r1_tarski(k9_relat_1(C,k3_xboole_0(A,B)),k3_xboole_0(k9_relat_1(C,A),k9_relat_1(C,B))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t154_relat_1)).

tff(f_65,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k7_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).

tff(f_36,axiom,(
    ! [A,B,C] :
      ( C = k3_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_42,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_69,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k7_relat_1(C,k3_xboole_0(A,B)) = k3_xboole_0(k7_relat_1(C,A),k7_relat_1(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t108_relat_1)).

tff(f_40,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(k3_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t108_xboole_1)).

tff(f_73,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_84,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(A,B)
           => ( r1_tarski(k1_relat_1(A),k1_relat_1(B))
              & r1_tarski(k2_relat_1(A),k2_relat_1(B)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_relat_1)).

tff(f_48,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(A,C) )
     => r1_tarski(A,k3_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_xboole_1)).

tff(c_48,plain,(
    v1_relat_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_36,plain,(
    ! [A_24,B_25] :
      ( v1_relat_1(k7_relat_1(A_24,B_25))
      | ~ v1_relat_1(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_22293,plain,(
    ! [A_1721,B_1722,C_1723] :
      ( r2_hidden('#skF_1'(A_1721,B_1722,C_1723),A_1721)
      | r2_hidden('#skF_2'(A_1721,B_1722,C_1723),C_1723)
      | k3_xboole_0(A_1721,B_1722) = C_1723 ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_16,plain,(
    ! [A_3,B_4,C_5] :
      ( ~ r2_hidden('#skF_1'(A_3,B_4,C_5),C_5)
      | r2_hidden('#skF_2'(A_3,B_4,C_5),C_5)
      | k3_xboole_0(A_3,B_4) = C_5 ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_22314,plain,(
    ! [A_1721,B_1722] :
      ( r2_hidden('#skF_2'(A_1721,B_1722,A_1721),A_1721)
      | k3_xboole_0(A_1721,B_1722) = A_1721 ) ),
    inference(resolution,[status(thm)],[c_22293,c_16])).

tff(c_18,plain,(
    ! [A_3,B_4,C_5] :
      ( r2_hidden('#skF_1'(A_3,B_4,C_5),B_4)
      | r2_hidden('#skF_2'(A_3,B_4,C_5),C_5)
      | k3_xboole_0(A_3,B_4) = C_5 ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_22600,plain,(
    ! [A_1761,B_1762,C_1763] :
      ( r2_hidden('#skF_1'(A_1761,B_1762,C_1763),B_1762)
      | ~ r2_hidden('#skF_2'(A_1761,B_1762,C_1763),B_1762)
      | ~ r2_hidden('#skF_2'(A_1761,B_1762,C_1763),A_1761)
      | k3_xboole_0(A_1761,B_1762) = C_1763 ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_23529,plain,(
    ! [C_1868,B_1869] :
      ( ~ r2_hidden('#skF_2'(C_1868,B_1869,C_1868),B_1869)
      | r2_hidden('#skF_1'(C_1868,B_1869,C_1868),B_1869)
      | k3_xboole_0(C_1868,B_1869) = C_1868 ) ),
    inference(resolution,[status(thm)],[c_18,c_22600])).

tff(c_10,plain,(
    ! [A_3,B_4,C_5] :
      ( ~ r2_hidden('#skF_1'(A_3,B_4,C_5),C_5)
      | ~ r2_hidden('#skF_2'(A_3,B_4,C_5),B_4)
      | ~ r2_hidden('#skF_2'(A_3,B_4,C_5),A_3)
      | k3_xboole_0(A_3,B_4) = C_5 ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_23559,plain,(
    ! [B_1870] :
      ( ~ r2_hidden('#skF_2'(B_1870,B_1870,B_1870),B_1870)
      | k3_xboole_0(B_1870,B_1870) = B_1870 ) ),
    inference(resolution,[status(thm)],[c_23529,c_10])).

tff(c_23580,plain,(
    ! [B_1871] : k3_xboole_0(B_1871,B_1871) = B_1871 ),
    inference(resolution,[status(thm)],[c_22314,c_23559])).

tff(c_51,plain,(
    ! [B_36,A_37] : k3_xboole_0(B_36,A_37) = k3_xboole_0(A_37,B_36) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_24,plain,(
    ! [A_12,B_13] : r1_tarski(k3_xboole_0(A_12,B_13),A_12) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_66,plain,(
    ! [B_36,A_37] : r1_tarski(k3_xboole_0(B_36,A_37),A_37) ),
    inference(superposition,[status(thm),theory(equality)],[c_51,c_24])).

tff(c_23995,plain,(
    ! [B_1871] : r1_tarski(B_1871,B_1871) ),
    inference(superposition,[status(thm),theory(equality)],[c_23580,c_66])).

tff(c_22140,plain,(
    ! [C_1706,A_1707,B_1708] :
      ( k3_xboole_0(k7_relat_1(C_1706,A_1707),k7_relat_1(C_1706,B_1708)) = k7_relat_1(C_1706,k3_xboole_0(A_1707,B_1708))
      | ~ v1_relat_1(C_1706) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_144,plain,(
    ! [A_56,C_57,B_58] :
      ( r1_tarski(k3_xboole_0(A_56,C_57),B_58)
      | ~ r1_tarski(A_56,B_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_150,plain,(
    ! [B_2,A_1,B_58] :
      ( r1_tarski(k3_xboole_0(B_2,A_1),B_58)
      | ~ r1_tarski(A_1,B_58) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_144])).

tff(c_22185,plain,(
    ! [C_1706,A_1707,B_1708,B_58] :
      ( r1_tarski(k7_relat_1(C_1706,k3_xboole_0(A_1707,B_1708)),B_58)
      | ~ r1_tarski(k7_relat_1(C_1706,B_1708),B_58)
      | ~ v1_relat_1(C_1706) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22140,c_150])).

tff(c_40,plain,(
    ! [B_30,A_29] :
      ( k2_relat_1(k7_relat_1(B_30,A_29)) = k9_relat_1(B_30,A_29)
      | ~ v1_relat_1(B_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_21926,plain,(
    ! [A_1670,B_1671] :
      ( r1_tarski(k2_relat_1(A_1670),k2_relat_1(B_1671))
      | ~ r1_tarski(A_1670,B_1671)
      | ~ v1_relat_1(B_1671)
      | ~ v1_relat_1(A_1670) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_25215,plain,(
    ! [B_1962,A_1963,B_1964] :
      ( r1_tarski(k9_relat_1(B_1962,A_1963),k2_relat_1(B_1964))
      | ~ r1_tarski(k7_relat_1(B_1962,A_1963),B_1964)
      | ~ v1_relat_1(B_1964)
      | ~ v1_relat_1(k7_relat_1(B_1962,A_1963))
      | ~ v1_relat_1(B_1962) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_21926])).

tff(c_43705,plain,(
    ! [B_3258,A_3259,B_3260,A_3261] :
      ( r1_tarski(k9_relat_1(B_3258,A_3259),k9_relat_1(B_3260,A_3261))
      | ~ r1_tarski(k7_relat_1(B_3258,A_3259),k7_relat_1(B_3260,A_3261))
      | ~ v1_relat_1(k7_relat_1(B_3260,A_3261))
      | ~ v1_relat_1(k7_relat_1(B_3258,A_3259))
      | ~ v1_relat_1(B_3258)
      | ~ v1_relat_1(B_3260) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_25215])).

tff(c_675,plain,(
    ! [A_143,B_144,C_145] :
      ( ~ r2_hidden('#skF_1'(A_143,B_144,C_145),C_145)
      | r2_hidden('#skF_2'(A_143,B_144,C_145),C_145)
      | k3_xboole_0(A_143,B_144) = C_145 ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_689,plain,(
    ! [A_3,B_4] :
      ( r2_hidden('#skF_2'(A_3,B_4,B_4),B_4)
      | k3_xboole_0(A_3,B_4) = B_4 ) ),
    inference(resolution,[status(thm)],[c_18,c_675])).

tff(c_20,plain,(
    ! [A_3,B_4,C_5] :
      ( r2_hidden('#skF_1'(A_3,B_4,C_5),A_3)
      | r2_hidden('#skF_2'(A_3,B_4,C_5),C_5)
      | k3_xboole_0(A_3,B_4) = C_5 ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_713,plain,(
    ! [A_150,B_151,C_152] :
      ( r2_hidden('#skF_1'(A_150,B_151,C_152),A_150)
      | ~ r2_hidden('#skF_2'(A_150,B_151,C_152),B_151)
      | ~ r2_hidden('#skF_2'(A_150,B_151,C_152),A_150)
      | k3_xboole_0(A_150,B_151) = C_152 ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_1860,plain,(
    ! [A_287,C_288] :
      ( ~ r2_hidden('#skF_2'(A_287,C_288,C_288),A_287)
      | r2_hidden('#skF_1'(A_287,C_288,C_288),A_287)
      | k3_xboole_0(A_287,C_288) = C_288 ) ),
    inference(resolution,[status(thm)],[c_20,c_713])).

tff(c_1890,plain,(
    ! [A_289] :
      ( ~ r2_hidden('#skF_2'(A_289,A_289,A_289),A_289)
      | k3_xboole_0(A_289,A_289) = A_289 ) ),
    inference(resolution,[status(thm)],[c_1860,c_10])).

tff(c_1911,plain,(
    ! [B_290] : k3_xboole_0(B_290,B_290) = B_290 ),
    inference(resolution,[status(thm)],[c_689,c_1890])).

tff(c_2311,plain,(
    ! [B_290] : r1_tarski(B_290,B_290) ),
    inference(superposition,[status(thm),theory(equality)],[c_1911,c_66])).

tff(c_477,plain,(
    ! [C_122,A_123,B_124] :
      ( k3_xboole_0(k7_relat_1(C_122,A_123),k7_relat_1(C_122,B_124)) = k7_relat_1(C_122,k3_xboole_0(A_123,B_124))
      | ~ v1_relat_1(C_122) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_22,plain,(
    ! [A_9,C_11,B_10] :
      ( r1_tarski(k3_xboole_0(A_9,C_11),B_10)
      | ~ r1_tarski(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_525,plain,(
    ! [C_122,A_123,B_124,B_10] :
      ( r1_tarski(k7_relat_1(C_122,k3_xboole_0(A_123,B_124)),B_10)
      | ~ r1_tarski(k7_relat_1(C_122,A_123),B_10)
      | ~ v1_relat_1(C_122) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_477,c_22])).

tff(c_296,plain,(
    ! [A_91,B_92] :
      ( r1_tarski(k2_relat_1(A_91),k2_relat_1(B_92))
      | ~ r1_tarski(A_91,B_92)
      | ~ v1_relat_1(B_92)
      | ~ v1_relat_1(A_91) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_3028,plain,(
    ! [A_348,B_349,A_350] :
      ( r1_tarski(k2_relat_1(A_348),k9_relat_1(B_349,A_350))
      | ~ r1_tarski(A_348,k7_relat_1(B_349,A_350))
      | ~ v1_relat_1(k7_relat_1(B_349,A_350))
      | ~ v1_relat_1(A_348)
      | ~ v1_relat_1(B_349) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_296])).

tff(c_21295,plain,(
    ! [B_1624,A_1625,B_1626,A_1627] :
      ( r1_tarski(k9_relat_1(B_1624,A_1625),k9_relat_1(B_1626,A_1627))
      | ~ r1_tarski(k7_relat_1(B_1624,A_1625),k7_relat_1(B_1626,A_1627))
      | ~ v1_relat_1(k7_relat_1(B_1626,A_1627))
      | ~ v1_relat_1(k7_relat_1(B_1624,A_1625))
      | ~ v1_relat_1(B_1626)
      | ~ v1_relat_1(B_1624) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_3028])).

tff(c_202,plain,(
    ! [A_73,B_74,C_75] :
      ( r1_tarski(A_73,k3_xboole_0(B_74,C_75))
      | ~ r1_tarski(A_73,C_75)
      | ~ r1_tarski(A_73,B_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_46,plain,(
    ~ r1_tarski(k9_relat_1('#skF_5',k3_xboole_0('#skF_3','#skF_4')),k3_xboole_0(k9_relat_1('#skF_5','#skF_3'),k9_relat_1('#skF_5','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_49,plain,(
    ~ r1_tarski(k9_relat_1('#skF_5',k3_xboole_0('#skF_4','#skF_3')),k3_xboole_0(k9_relat_1('#skF_5','#skF_4'),k9_relat_1('#skF_5','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_2,c_46])).

tff(c_219,plain,
    ( ~ r1_tarski(k9_relat_1('#skF_5',k3_xboole_0('#skF_4','#skF_3')),k9_relat_1('#skF_5','#skF_3'))
    | ~ r1_tarski(k9_relat_1('#skF_5',k3_xboole_0('#skF_4','#skF_3')),k9_relat_1('#skF_5','#skF_4')) ),
    inference(resolution,[status(thm)],[c_202,c_49])).

tff(c_250,plain,(
    ~ r1_tarski(k9_relat_1('#skF_5',k3_xboole_0('#skF_4','#skF_3')),k9_relat_1('#skF_5','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_219])).

tff(c_21356,plain,
    ( ~ r1_tarski(k7_relat_1('#skF_5',k3_xboole_0('#skF_4','#skF_3')),k7_relat_1('#skF_5','#skF_4'))
    | ~ v1_relat_1(k7_relat_1('#skF_5','#skF_4'))
    | ~ v1_relat_1(k7_relat_1('#skF_5',k3_xboole_0('#skF_4','#skF_3')))
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_21295,c_250])).

tff(c_21393,plain,
    ( ~ r1_tarski(k7_relat_1('#skF_5',k3_xboole_0('#skF_4','#skF_3')),k7_relat_1('#skF_5','#skF_4'))
    | ~ v1_relat_1(k7_relat_1('#skF_5','#skF_4'))
    | ~ v1_relat_1(k7_relat_1('#skF_5',k3_xboole_0('#skF_4','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_21356])).

tff(c_21536,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_5',k3_xboole_0('#skF_4','#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_21393])).

tff(c_21539,plain,(
    ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_36,c_21536])).

tff(c_21543,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_21539])).

tff(c_21544,plain,
    ( ~ v1_relat_1(k7_relat_1('#skF_5','#skF_4'))
    | ~ r1_tarski(k7_relat_1('#skF_5',k3_xboole_0('#skF_4','#skF_3')),k7_relat_1('#skF_5','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_21393])).

tff(c_21826,plain,(
    ~ r1_tarski(k7_relat_1('#skF_5',k3_xboole_0('#skF_4','#skF_3')),k7_relat_1('#skF_5','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_21544])).

tff(c_21832,plain,
    ( ~ r1_tarski(k7_relat_1('#skF_5','#skF_4'),k7_relat_1('#skF_5','#skF_4'))
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_525,c_21826])).

tff(c_21842,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_2311,c_21832])).

tff(c_21843,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_5','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_21544])).

tff(c_21847,plain,(
    ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_36,c_21843])).

tff(c_21851,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_21847])).

tff(c_21852,plain,(
    ~ r1_tarski(k9_relat_1('#skF_5',k3_xboole_0('#skF_4','#skF_3')),k9_relat_1('#skF_5','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_219])).

tff(c_43766,plain,
    ( ~ r1_tarski(k7_relat_1('#skF_5',k3_xboole_0('#skF_4','#skF_3')),k7_relat_1('#skF_5','#skF_3'))
    | ~ v1_relat_1(k7_relat_1('#skF_5','#skF_3'))
    | ~ v1_relat_1(k7_relat_1('#skF_5',k3_xboole_0('#skF_4','#skF_3')))
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_43705,c_21852])).

tff(c_43803,plain,
    ( ~ r1_tarski(k7_relat_1('#skF_5',k3_xboole_0('#skF_4','#skF_3')),k7_relat_1('#skF_5','#skF_3'))
    | ~ v1_relat_1(k7_relat_1('#skF_5','#skF_3'))
    | ~ v1_relat_1(k7_relat_1('#skF_5',k3_xboole_0('#skF_4','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_43766])).

tff(c_43918,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_5',k3_xboole_0('#skF_4','#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_43803])).

tff(c_43921,plain,(
    ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_36,c_43918])).

tff(c_43925,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_43921])).

tff(c_43926,plain,
    ( ~ v1_relat_1(k7_relat_1('#skF_5','#skF_3'))
    | ~ r1_tarski(k7_relat_1('#skF_5',k3_xboole_0('#skF_4','#skF_3')),k7_relat_1('#skF_5','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_43803])).

tff(c_43928,plain,(
    ~ r1_tarski(k7_relat_1('#skF_5',k3_xboole_0('#skF_4','#skF_3')),k7_relat_1('#skF_5','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_43926])).

tff(c_43931,plain,
    ( ~ r1_tarski(k7_relat_1('#skF_5','#skF_3'),k7_relat_1('#skF_5','#skF_3'))
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_22185,c_43928])).

tff(c_43941,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_23995,c_43931])).

tff(c_43942,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_5','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_43926])).

tff(c_43946,plain,(
    ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_36,c_43942])).

tff(c_43950,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_43946])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:23:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 20.96/10.91  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 20.96/10.91  
% 20.96/10.91  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 20.96/10.92  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > k9_relat_1 > k7_relat_1 > k3_xboole_0 > k2_tarski > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_setfam_1 > k1_relat_1 > #skF_1 > #skF_5 > #skF_3 > #skF_2 > #skF_4
% 20.96/10.92  
% 20.96/10.92  %Foreground sorts:
% 20.96/10.92  
% 20.96/10.92  
% 20.96/10.92  %Background operators:
% 20.96/10.92  
% 20.96/10.92  
% 20.96/10.92  %Foreground operators:
% 20.96/10.92  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 20.96/10.92  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 20.96/10.92  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 20.96/10.92  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 20.96/10.92  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 20.96/10.92  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 20.96/10.92  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 20.96/10.92  tff('#skF_5', type, '#skF_5': $i).
% 20.96/10.92  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 20.96/10.92  tff('#skF_3', type, '#skF_3': $i).
% 20.96/10.92  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 20.96/10.92  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 20.96/10.92  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 20.96/10.92  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 20.96/10.92  tff('#skF_4', type, '#skF_4': $i).
% 20.96/10.92  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 20.96/10.92  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 20.96/10.92  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 20.96/10.92  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 20.96/10.92  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 20.96/10.92  
% 21.07/10.94  tff(f_89, negated_conjecture, ~(![A, B, C]: (v1_relat_1(C) => r1_tarski(k9_relat_1(C, k3_xboole_0(A, B)), k3_xboole_0(k9_relat_1(C, A), k9_relat_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t154_relat_1)).
% 21.07/10.94  tff(f_65, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k7_relat_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 21.07/10.94  tff(f_36, axiom, (![A, B, C]: ((C = k3_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_xboole_0)).
% 21.07/10.94  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 21.07/10.94  tff(f_42, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 21.07/10.94  tff(f_69, axiom, (![A, B, C]: (v1_relat_1(C) => (k7_relat_1(C, k3_xboole_0(A, B)) = k3_xboole_0(k7_relat_1(C, A), k7_relat_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t108_relat_1)).
% 21.07/10.94  tff(f_40, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(k3_xboole_0(A, C), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t108_xboole_1)).
% 21.07/10.94  tff(f_73, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_relat_1)).
% 21.07/10.94  tff(f_84, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(A, B) => (r1_tarski(k1_relat_1(A), k1_relat_1(B)) & r1_tarski(k2_relat_1(A), k2_relat_1(B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t25_relat_1)).
% 21.07/10.94  tff(f_48, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(A, C)) => r1_tarski(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t19_xboole_1)).
% 21.07/10.94  tff(c_48, plain, (v1_relat_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_89])).
% 21.07/10.94  tff(c_36, plain, (![A_24, B_25]: (v1_relat_1(k7_relat_1(A_24, B_25)) | ~v1_relat_1(A_24))), inference(cnfTransformation, [status(thm)], [f_65])).
% 21.07/10.94  tff(c_22293, plain, (![A_1721, B_1722, C_1723]: (r2_hidden('#skF_1'(A_1721, B_1722, C_1723), A_1721) | r2_hidden('#skF_2'(A_1721, B_1722, C_1723), C_1723) | k3_xboole_0(A_1721, B_1722)=C_1723)), inference(cnfTransformation, [status(thm)], [f_36])).
% 21.07/10.94  tff(c_16, plain, (![A_3, B_4, C_5]: (~r2_hidden('#skF_1'(A_3, B_4, C_5), C_5) | r2_hidden('#skF_2'(A_3, B_4, C_5), C_5) | k3_xboole_0(A_3, B_4)=C_5)), inference(cnfTransformation, [status(thm)], [f_36])).
% 21.07/10.94  tff(c_22314, plain, (![A_1721, B_1722]: (r2_hidden('#skF_2'(A_1721, B_1722, A_1721), A_1721) | k3_xboole_0(A_1721, B_1722)=A_1721)), inference(resolution, [status(thm)], [c_22293, c_16])).
% 21.07/10.94  tff(c_18, plain, (![A_3, B_4, C_5]: (r2_hidden('#skF_1'(A_3, B_4, C_5), B_4) | r2_hidden('#skF_2'(A_3, B_4, C_5), C_5) | k3_xboole_0(A_3, B_4)=C_5)), inference(cnfTransformation, [status(thm)], [f_36])).
% 21.07/10.94  tff(c_22600, plain, (![A_1761, B_1762, C_1763]: (r2_hidden('#skF_1'(A_1761, B_1762, C_1763), B_1762) | ~r2_hidden('#skF_2'(A_1761, B_1762, C_1763), B_1762) | ~r2_hidden('#skF_2'(A_1761, B_1762, C_1763), A_1761) | k3_xboole_0(A_1761, B_1762)=C_1763)), inference(cnfTransformation, [status(thm)], [f_36])).
% 21.07/10.94  tff(c_23529, plain, (![C_1868, B_1869]: (~r2_hidden('#skF_2'(C_1868, B_1869, C_1868), B_1869) | r2_hidden('#skF_1'(C_1868, B_1869, C_1868), B_1869) | k3_xboole_0(C_1868, B_1869)=C_1868)), inference(resolution, [status(thm)], [c_18, c_22600])).
% 21.07/10.94  tff(c_10, plain, (![A_3, B_4, C_5]: (~r2_hidden('#skF_1'(A_3, B_4, C_5), C_5) | ~r2_hidden('#skF_2'(A_3, B_4, C_5), B_4) | ~r2_hidden('#skF_2'(A_3, B_4, C_5), A_3) | k3_xboole_0(A_3, B_4)=C_5)), inference(cnfTransformation, [status(thm)], [f_36])).
% 21.07/10.94  tff(c_23559, plain, (![B_1870]: (~r2_hidden('#skF_2'(B_1870, B_1870, B_1870), B_1870) | k3_xboole_0(B_1870, B_1870)=B_1870)), inference(resolution, [status(thm)], [c_23529, c_10])).
% 21.07/10.94  tff(c_23580, plain, (![B_1871]: (k3_xboole_0(B_1871, B_1871)=B_1871)), inference(resolution, [status(thm)], [c_22314, c_23559])).
% 21.07/10.94  tff(c_51, plain, (![B_36, A_37]: (k3_xboole_0(B_36, A_37)=k3_xboole_0(A_37, B_36))), inference(cnfTransformation, [status(thm)], [f_27])).
% 21.07/10.94  tff(c_24, plain, (![A_12, B_13]: (r1_tarski(k3_xboole_0(A_12, B_13), A_12))), inference(cnfTransformation, [status(thm)], [f_42])).
% 21.07/10.94  tff(c_66, plain, (![B_36, A_37]: (r1_tarski(k3_xboole_0(B_36, A_37), A_37))), inference(superposition, [status(thm), theory('equality')], [c_51, c_24])).
% 21.07/10.94  tff(c_23995, plain, (![B_1871]: (r1_tarski(B_1871, B_1871))), inference(superposition, [status(thm), theory('equality')], [c_23580, c_66])).
% 21.07/10.94  tff(c_22140, plain, (![C_1706, A_1707, B_1708]: (k3_xboole_0(k7_relat_1(C_1706, A_1707), k7_relat_1(C_1706, B_1708))=k7_relat_1(C_1706, k3_xboole_0(A_1707, B_1708)) | ~v1_relat_1(C_1706))), inference(cnfTransformation, [status(thm)], [f_69])).
% 21.07/10.94  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 21.07/10.94  tff(c_144, plain, (![A_56, C_57, B_58]: (r1_tarski(k3_xboole_0(A_56, C_57), B_58) | ~r1_tarski(A_56, B_58))), inference(cnfTransformation, [status(thm)], [f_40])).
% 21.07/10.94  tff(c_150, plain, (![B_2, A_1, B_58]: (r1_tarski(k3_xboole_0(B_2, A_1), B_58) | ~r1_tarski(A_1, B_58))), inference(superposition, [status(thm), theory('equality')], [c_2, c_144])).
% 21.07/10.94  tff(c_22185, plain, (![C_1706, A_1707, B_1708, B_58]: (r1_tarski(k7_relat_1(C_1706, k3_xboole_0(A_1707, B_1708)), B_58) | ~r1_tarski(k7_relat_1(C_1706, B_1708), B_58) | ~v1_relat_1(C_1706))), inference(superposition, [status(thm), theory('equality')], [c_22140, c_150])).
% 21.07/10.94  tff(c_40, plain, (![B_30, A_29]: (k2_relat_1(k7_relat_1(B_30, A_29))=k9_relat_1(B_30, A_29) | ~v1_relat_1(B_30))), inference(cnfTransformation, [status(thm)], [f_73])).
% 21.07/10.94  tff(c_21926, plain, (![A_1670, B_1671]: (r1_tarski(k2_relat_1(A_1670), k2_relat_1(B_1671)) | ~r1_tarski(A_1670, B_1671) | ~v1_relat_1(B_1671) | ~v1_relat_1(A_1670))), inference(cnfTransformation, [status(thm)], [f_84])).
% 21.07/10.94  tff(c_25215, plain, (![B_1962, A_1963, B_1964]: (r1_tarski(k9_relat_1(B_1962, A_1963), k2_relat_1(B_1964)) | ~r1_tarski(k7_relat_1(B_1962, A_1963), B_1964) | ~v1_relat_1(B_1964) | ~v1_relat_1(k7_relat_1(B_1962, A_1963)) | ~v1_relat_1(B_1962))), inference(superposition, [status(thm), theory('equality')], [c_40, c_21926])).
% 21.07/10.94  tff(c_43705, plain, (![B_3258, A_3259, B_3260, A_3261]: (r1_tarski(k9_relat_1(B_3258, A_3259), k9_relat_1(B_3260, A_3261)) | ~r1_tarski(k7_relat_1(B_3258, A_3259), k7_relat_1(B_3260, A_3261)) | ~v1_relat_1(k7_relat_1(B_3260, A_3261)) | ~v1_relat_1(k7_relat_1(B_3258, A_3259)) | ~v1_relat_1(B_3258) | ~v1_relat_1(B_3260))), inference(superposition, [status(thm), theory('equality')], [c_40, c_25215])).
% 21.07/10.94  tff(c_675, plain, (![A_143, B_144, C_145]: (~r2_hidden('#skF_1'(A_143, B_144, C_145), C_145) | r2_hidden('#skF_2'(A_143, B_144, C_145), C_145) | k3_xboole_0(A_143, B_144)=C_145)), inference(cnfTransformation, [status(thm)], [f_36])).
% 21.07/10.94  tff(c_689, plain, (![A_3, B_4]: (r2_hidden('#skF_2'(A_3, B_4, B_4), B_4) | k3_xboole_0(A_3, B_4)=B_4)), inference(resolution, [status(thm)], [c_18, c_675])).
% 21.07/10.94  tff(c_20, plain, (![A_3, B_4, C_5]: (r2_hidden('#skF_1'(A_3, B_4, C_5), A_3) | r2_hidden('#skF_2'(A_3, B_4, C_5), C_5) | k3_xboole_0(A_3, B_4)=C_5)), inference(cnfTransformation, [status(thm)], [f_36])).
% 21.07/10.94  tff(c_713, plain, (![A_150, B_151, C_152]: (r2_hidden('#skF_1'(A_150, B_151, C_152), A_150) | ~r2_hidden('#skF_2'(A_150, B_151, C_152), B_151) | ~r2_hidden('#skF_2'(A_150, B_151, C_152), A_150) | k3_xboole_0(A_150, B_151)=C_152)), inference(cnfTransformation, [status(thm)], [f_36])).
% 21.07/10.94  tff(c_1860, plain, (![A_287, C_288]: (~r2_hidden('#skF_2'(A_287, C_288, C_288), A_287) | r2_hidden('#skF_1'(A_287, C_288, C_288), A_287) | k3_xboole_0(A_287, C_288)=C_288)), inference(resolution, [status(thm)], [c_20, c_713])).
% 21.07/10.94  tff(c_1890, plain, (![A_289]: (~r2_hidden('#skF_2'(A_289, A_289, A_289), A_289) | k3_xboole_0(A_289, A_289)=A_289)), inference(resolution, [status(thm)], [c_1860, c_10])).
% 21.07/10.94  tff(c_1911, plain, (![B_290]: (k3_xboole_0(B_290, B_290)=B_290)), inference(resolution, [status(thm)], [c_689, c_1890])).
% 21.07/10.94  tff(c_2311, plain, (![B_290]: (r1_tarski(B_290, B_290))), inference(superposition, [status(thm), theory('equality')], [c_1911, c_66])).
% 21.07/10.94  tff(c_477, plain, (![C_122, A_123, B_124]: (k3_xboole_0(k7_relat_1(C_122, A_123), k7_relat_1(C_122, B_124))=k7_relat_1(C_122, k3_xboole_0(A_123, B_124)) | ~v1_relat_1(C_122))), inference(cnfTransformation, [status(thm)], [f_69])).
% 21.07/10.94  tff(c_22, plain, (![A_9, C_11, B_10]: (r1_tarski(k3_xboole_0(A_9, C_11), B_10) | ~r1_tarski(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_40])).
% 21.07/10.94  tff(c_525, plain, (![C_122, A_123, B_124, B_10]: (r1_tarski(k7_relat_1(C_122, k3_xboole_0(A_123, B_124)), B_10) | ~r1_tarski(k7_relat_1(C_122, A_123), B_10) | ~v1_relat_1(C_122))), inference(superposition, [status(thm), theory('equality')], [c_477, c_22])).
% 21.07/10.94  tff(c_296, plain, (![A_91, B_92]: (r1_tarski(k2_relat_1(A_91), k2_relat_1(B_92)) | ~r1_tarski(A_91, B_92) | ~v1_relat_1(B_92) | ~v1_relat_1(A_91))), inference(cnfTransformation, [status(thm)], [f_84])).
% 21.07/10.94  tff(c_3028, plain, (![A_348, B_349, A_350]: (r1_tarski(k2_relat_1(A_348), k9_relat_1(B_349, A_350)) | ~r1_tarski(A_348, k7_relat_1(B_349, A_350)) | ~v1_relat_1(k7_relat_1(B_349, A_350)) | ~v1_relat_1(A_348) | ~v1_relat_1(B_349))), inference(superposition, [status(thm), theory('equality')], [c_40, c_296])).
% 21.07/10.94  tff(c_21295, plain, (![B_1624, A_1625, B_1626, A_1627]: (r1_tarski(k9_relat_1(B_1624, A_1625), k9_relat_1(B_1626, A_1627)) | ~r1_tarski(k7_relat_1(B_1624, A_1625), k7_relat_1(B_1626, A_1627)) | ~v1_relat_1(k7_relat_1(B_1626, A_1627)) | ~v1_relat_1(k7_relat_1(B_1624, A_1625)) | ~v1_relat_1(B_1626) | ~v1_relat_1(B_1624))), inference(superposition, [status(thm), theory('equality')], [c_40, c_3028])).
% 21.07/10.94  tff(c_202, plain, (![A_73, B_74, C_75]: (r1_tarski(A_73, k3_xboole_0(B_74, C_75)) | ~r1_tarski(A_73, C_75) | ~r1_tarski(A_73, B_74))), inference(cnfTransformation, [status(thm)], [f_48])).
% 21.07/10.94  tff(c_46, plain, (~r1_tarski(k9_relat_1('#skF_5', k3_xboole_0('#skF_3', '#skF_4')), k3_xboole_0(k9_relat_1('#skF_5', '#skF_3'), k9_relat_1('#skF_5', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_89])).
% 21.07/10.94  tff(c_49, plain, (~r1_tarski(k9_relat_1('#skF_5', k3_xboole_0('#skF_4', '#skF_3')), k3_xboole_0(k9_relat_1('#skF_5', '#skF_4'), k9_relat_1('#skF_5', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_2, c_46])).
% 21.07/10.94  tff(c_219, plain, (~r1_tarski(k9_relat_1('#skF_5', k3_xboole_0('#skF_4', '#skF_3')), k9_relat_1('#skF_5', '#skF_3')) | ~r1_tarski(k9_relat_1('#skF_5', k3_xboole_0('#skF_4', '#skF_3')), k9_relat_1('#skF_5', '#skF_4'))), inference(resolution, [status(thm)], [c_202, c_49])).
% 21.07/10.94  tff(c_250, plain, (~r1_tarski(k9_relat_1('#skF_5', k3_xboole_0('#skF_4', '#skF_3')), k9_relat_1('#skF_5', '#skF_4'))), inference(splitLeft, [status(thm)], [c_219])).
% 21.07/10.94  tff(c_21356, plain, (~r1_tarski(k7_relat_1('#skF_5', k3_xboole_0('#skF_4', '#skF_3')), k7_relat_1('#skF_5', '#skF_4')) | ~v1_relat_1(k7_relat_1('#skF_5', '#skF_4')) | ~v1_relat_1(k7_relat_1('#skF_5', k3_xboole_0('#skF_4', '#skF_3'))) | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_21295, c_250])).
% 21.07/10.94  tff(c_21393, plain, (~r1_tarski(k7_relat_1('#skF_5', k3_xboole_0('#skF_4', '#skF_3')), k7_relat_1('#skF_5', '#skF_4')) | ~v1_relat_1(k7_relat_1('#skF_5', '#skF_4')) | ~v1_relat_1(k7_relat_1('#skF_5', k3_xboole_0('#skF_4', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_21356])).
% 21.07/10.94  tff(c_21536, plain, (~v1_relat_1(k7_relat_1('#skF_5', k3_xboole_0('#skF_4', '#skF_3')))), inference(splitLeft, [status(thm)], [c_21393])).
% 21.07/10.94  tff(c_21539, plain, (~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_36, c_21536])).
% 21.07/10.94  tff(c_21543, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_48, c_21539])).
% 21.07/10.94  tff(c_21544, plain, (~v1_relat_1(k7_relat_1('#skF_5', '#skF_4')) | ~r1_tarski(k7_relat_1('#skF_5', k3_xboole_0('#skF_4', '#skF_3')), k7_relat_1('#skF_5', '#skF_4'))), inference(splitRight, [status(thm)], [c_21393])).
% 21.07/10.94  tff(c_21826, plain, (~r1_tarski(k7_relat_1('#skF_5', k3_xboole_0('#skF_4', '#skF_3')), k7_relat_1('#skF_5', '#skF_4'))), inference(splitLeft, [status(thm)], [c_21544])).
% 21.07/10.94  tff(c_21832, plain, (~r1_tarski(k7_relat_1('#skF_5', '#skF_4'), k7_relat_1('#skF_5', '#skF_4')) | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_525, c_21826])).
% 21.07/10.94  tff(c_21842, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_48, c_2311, c_21832])).
% 21.07/10.94  tff(c_21843, plain, (~v1_relat_1(k7_relat_1('#skF_5', '#skF_4'))), inference(splitRight, [status(thm)], [c_21544])).
% 21.07/10.94  tff(c_21847, plain, (~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_36, c_21843])).
% 21.07/10.94  tff(c_21851, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_48, c_21847])).
% 21.07/10.94  tff(c_21852, plain, (~r1_tarski(k9_relat_1('#skF_5', k3_xboole_0('#skF_4', '#skF_3')), k9_relat_1('#skF_5', '#skF_3'))), inference(splitRight, [status(thm)], [c_219])).
% 21.07/10.94  tff(c_43766, plain, (~r1_tarski(k7_relat_1('#skF_5', k3_xboole_0('#skF_4', '#skF_3')), k7_relat_1('#skF_5', '#skF_3')) | ~v1_relat_1(k7_relat_1('#skF_5', '#skF_3')) | ~v1_relat_1(k7_relat_1('#skF_5', k3_xboole_0('#skF_4', '#skF_3'))) | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_43705, c_21852])).
% 21.07/10.94  tff(c_43803, plain, (~r1_tarski(k7_relat_1('#skF_5', k3_xboole_0('#skF_4', '#skF_3')), k7_relat_1('#skF_5', '#skF_3')) | ~v1_relat_1(k7_relat_1('#skF_5', '#skF_3')) | ~v1_relat_1(k7_relat_1('#skF_5', k3_xboole_0('#skF_4', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_43766])).
% 21.07/10.94  tff(c_43918, plain, (~v1_relat_1(k7_relat_1('#skF_5', k3_xboole_0('#skF_4', '#skF_3')))), inference(splitLeft, [status(thm)], [c_43803])).
% 21.07/10.94  tff(c_43921, plain, (~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_36, c_43918])).
% 21.07/10.94  tff(c_43925, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_48, c_43921])).
% 21.07/10.94  tff(c_43926, plain, (~v1_relat_1(k7_relat_1('#skF_5', '#skF_3')) | ~r1_tarski(k7_relat_1('#skF_5', k3_xboole_0('#skF_4', '#skF_3')), k7_relat_1('#skF_5', '#skF_3'))), inference(splitRight, [status(thm)], [c_43803])).
% 21.07/10.94  tff(c_43928, plain, (~r1_tarski(k7_relat_1('#skF_5', k3_xboole_0('#skF_4', '#skF_3')), k7_relat_1('#skF_5', '#skF_3'))), inference(splitLeft, [status(thm)], [c_43926])).
% 21.07/10.94  tff(c_43931, plain, (~r1_tarski(k7_relat_1('#skF_5', '#skF_3'), k7_relat_1('#skF_5', '#skF_3')) | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_22185, c_43928])).
% 21.07/10.94  tff(c_43941, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_48, c_23995, c_43931])).
% 21.07/10.94  tff(c_43942, plain, (~v1_relat_1(k7_relat_1('#skF_5', '#skF_3'))), inference(splitRight, [status(thm)], [c_43926])).
% 21.07/10.94  tff(c_43946, plain, (~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_36, c_43942])).
% 21.07/10.94  tff(c_43950, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_48, c_43946])).
% 21.07/10.94  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 21.07/10.94  
% 21.07/10.94  Inference rules
% 21.07/10.94  ----------------------
% 21.07/10.94  #Ref     : 0
% 21.07/10.94  #Sup     : 12174
% 21.07/10.94  #Fact    : 0
% 21.07/10.94  #Define  : 0
% 21.07/10.94  #Split   : 6
% 21.07/10.94  #Chain   : 0
% 21.07/10.94  #Close   : 0
% 21.07/10.94  
% 21.07/10.94  Ordering : KBO
% 21.07/10.94  
% 21.07/10.94  Simplification rules
% 21.07/10.94  ----------------------
% 21.07/10.94  #Subsume      : 5742
% 21.07/10.94  #Demod        : 650
% 21.07/10.94  #Tautology    : 268
% 21.07/10.94  #SimpNegUnit  : 0
% 21.07/10.94  #BackRed      : 0
% 21.07/10.94  
% 21.07/10.94  #Partial instantiations: 0
% 21.07/10.94  #Strategies tried      : 1
% 21.07/10.94  
% 21.07/10.94  Timing (in seconds)
% 21.07/10.94  ----------------------
% 21.07/10.94  Preprocessing        : 0.32
% 21.07/10.94  Parsing              : 0.18
% 21.07/10.94  CNF conversion       : 0.02
% 21.07/10.94  Main loop            : 9.78
% 21.07/10.94  Inferencing          : 1.71
% 21.07/10.94  Reduction            : 2.34
% 21.07/10.94  Demodulation         : 1.90
% 21.07/10.94  BG Simplification    : 0.18
% 21.07/10.94  Subsumption          : 5.00
% 21.07/10.94  Abstraction          : 0.23
% 21.07/10.94  MUC search           : 0.00
% 21.07/10.94  Cooper               : 0.00
% 21.07/10.94  Total                : 10.14
% 21.14/10.94  Index Insertion      : 0.00
% 21.14/10.94  Index Deletion       : 0.00
% 21.14/10.94  Index Matching       : 0.00
% 21.14/10.94  BG Taut test         : 0.00
%------------------------------------------------------------------------------
