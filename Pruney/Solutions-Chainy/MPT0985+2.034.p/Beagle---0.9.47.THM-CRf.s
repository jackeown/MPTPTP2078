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
% DateTime   : Thu Dec  3 10:12:30 EST 2020

% Result     : Theorem 40.21s
% Output     : CNFRefutation 40.82s
% Verified   : 
% Statistics : Number of formulae       :  404 (20328 expanded)
%              Number of leaves         :   49 (6454 expanded)
%              Depth                    :   26
%              Number of atoms          :  776 (49565 expanded)
%              Number of equality atoms :  143 (10999 expanded)
%              Maximal formula depth    :   12 (   3 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r2_hidden > r1_tarski > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k9_relat_1 > k7_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2

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

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff(v1_partfun1,type,(
    v1_partfun1: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_49,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_202,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( ( v2_funct_1(C)
            & k2_relset_1(A,B,C) = B )
         => ( v1_funct_1(k2_funct_1(C))
            & v1_funct_2(k2_funct_1(C),B,A)
            & m1_subset_1(k2_funct_1(C),k1_zfmisc_1(k2_zfmisc_1(B,A))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_funct_2)).

tff(f_128,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_39,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_63,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_122,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_100,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).

tff(f_118,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k2_relat_1(A) = k1_relat_1(k2_funct_1(A))
          & k1_relat_1(A) = k2_relat_1(k2_funct_1(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).

tff(f_139,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_166,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_funct_1(A)
        & v1_funct_2(A,k1_relat_1(A),k2_relat_1(A))
        & m1_subset_1(A,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A)))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_funct_2)).

tff(f_80,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_185,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r1_tarski(B,C)
       => ( ( B = k1_xboole_0
            & A != k1_xboole_0 )
          | ( v1_funct_1(D)
            & v1_funct_2(D,A,C)
            & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,C))) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_funct_2)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_67,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_74,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

tff(f_135,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => v1_xboole_0(C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc3_relset_1)).

tff(f_92,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k7_relat_1(B,A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_relat_1)).

tff(f_88,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k1_relat_1(k7_relat_1(B,A)),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_relat_1)).

tff(f_43,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(c_20,plain,(
    ! [B_12] : r1_tarski(B_12,B_12) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_96,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_202])).

tff(c_688,plain,(
    ! [C_145,A_146,B_147] :
      ( v4_relat_1(C_145,A_146)
      | ~ m1_subset_1(C_145,k1_zfmisc_1(k2_zfmisc_1(A_146,B_147))) ) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_703,plain,(
    v4_relat_1('#skF_5','#skF_3') ),
    inference(resolution,[status(thm)],[c_96,c_688])).

tff(c_12,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_26,plain,(
    ! [A_15] : k2_zfmisc_1(A_15,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_221,plain,(
    ! [C_89,A_90,B_91] :
      ( v1_relat_1(C_89)
      | ~ m1_subset_1(C_89,k1_zfmisc_1(k2_zfmisc_1(A_90,B_91))) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_234,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_96,c_221])).

tff(c_100,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_202])).

tff(c_46,plain,(
    ! [A_30] :
      ( v1_funct_1(k2_funct_1(A_30))
      | ~ v1_funct_1(A_30)
      | ~ v1_relat_1(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_90,plain,
    ( ~ m1_subset_1(k2_funct_1('#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_3')))
    | ~ v1_funct_2(k2_funct_1('#skF_5'),'#skF_4','#skF_3')
    | ~ v1_funct_1(k2_funct_1('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_202])).

tff(c_160,plain,(
    ~ v1_funct_1(k2_funct_1('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_90])).

tff(c_163,plain,
    ( ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_46,c_160])).

tff(c_166,plain,(
    ~ v1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_163])).

tff(c_196,plain,(
    ! [C_84,A_85,B_86] :
      ( v1_relat_1(C_84)
      | ~ m1_subset_1(C_84,k1_zfmisc_1(k2_zfmisc_1(A_85,B_86))) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_203,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_96,c_196])).

tff(c_212,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_166,c_203])).

tff(c_214,plain,(
    v1_funct_1(k2_funct_1('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_90])).

tff(c_94,plain,(
    v2_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_202])).

tff(c_52,plain,(
    ! [A_33] :
      ( k2_relat_1(k2_funct_1(A_33)) = k1_relat_1(A_33)
      | ~ v2_funct_1(A_33)
      | ~ v1_funct_1(A_33)
      | ~ v1_relat_1(A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_48,plain,(
    ! [A_30] :
      ( v1_relat_1(k2_funct_1(A_30))
      | ~ v1_funct_1(A_30)
      | ~ v1_relat_1(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_92,plain,(
    k2_relset_1('#skF_3','#skF_4','#skF_5') = '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_202])).

tff(c_1186,plain,(
    ! [A_208,B_209,C_210] :
      ( k2_relset_1(A_208,B_209,C_210) = k2_relat_1(C_210)
      | ~ m1_subset_1(C_210,k1_zfmisc_1(k2_zfmisc_1(A_208,B_209))) ) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_1196,plain,(
    k2_relset_1('#skF_3','#skF_4','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_96,c_1186])).

tff(c_1206,plain,(
    k2_relat_1('#skF_5') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_1196])).

tff(c_954,plain,(
    ! [A_187] :
      ( k1_relat_1(k2_funct_1(A_187)) = k2_relat_1(A_187)
      | ~ v2_funct_1(A_187)
      | ~ v1_funct_1(A_187)
      | ~ v1_relat_1(A_187) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_74,plain,(
    ! [A_54] :
      ( v1_funct_2(A_54,k1_relat_1(A_54),k2_relat_1(A_54))
      | ~ v1_funct_1(A_54)
      | ~ v1_relat_1(A_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_19485,plain,(
    ! [A_743] :
      ( v1_funct_2(k2_funct_1(A_743),k2_relat_1(A_743),k2_relat_1(k2_funct_1(A_743)))
      | ~ v1_funct_1(k2_funct_1(A_743))
      | ~ v1_relat_1(k2_funct_1(A_743))
      | ~ v2_funct_1(A_743)
      | ~ v1_funct_1(A_743)
      | ~ v1_relat_1(A_743) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_954,c_74])).

tff(c_19503,plain,
    ( v1_funct_2(k2_funct_1('#skF_5'),'#skF_4',k2_relat_1(k2_funct_1('#skF_5')))
    | ~ v1_funct_1(k2_funct_1('#skF_5'))
    | ~ v1_relat_1(k2_funct_1('#skF_5'))
    | ~ v2_funct_1('#skF_5')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_1206,c_19485])).

tff(c_19524,plain,
    ( v1_funct_2(k2_funct_1('#skF_5'),'#skF_4',k2_relat_1(k2_funct_1('#skF_5')))
    | ~ v1_relat_1(k2_funct_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_234,c_100,c_94,c_214,c_19503])).

tff(c_19525,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_19524])).

tff(c_19528,plain,
    ( ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_48,c_19525])).

tff(c_19532,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_234,c_100,c_19528])).

tff(c_19533,plain,(
    v1_funct_2(k2_funct_1('#skF_5'),'#skF_4',k2_relat_1(k2_funct_1('#skF_5'))) ),
    inference(splitRight,[status(thm)],[c_19524])).

tff(c_19593,plain,
    ( v1_funct_2(k2_funct_1('#skF_5'),'#skF_4',k1_relat_1('#skF_5'))
    | ~ v2_funct_1('#skF_5')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_52,c_19533])).

tff(c_19595,plain,(
    v1_funct_2(k2_funct_1('#skF_5'),'#skF_4',k1_relat_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_234,c_100,c_94,c_19593])).

tff(c_19534,plain,(
    v1_relat_1(k2_funct_1('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_19524])).

tff(c_54,plain,(
    ! [A_33] :
      ( k1_relat_1(k2_funct_1(A_33)) = k2_relat_1(A_33)
      | ~ v2_funct_1(A_33)
      | ~ v1_funct_1(A_33)
      | ~ v1_relat_1(A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_1100,plain,(
    ! [A_202] :
      ( m1_subset_1(A_202,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_202),k2_relat_1(A_202))))
      | ~ v1_funct_1(A_202)
      | ~ v1_relat_1(A_202) ) ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_21363,plain,(
    ! [A_793] :
      ( m1_subset_1(k2_funct_1(A_793),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(A_793),k2_relat_1(k2_funct_1(A_793)))))
      | ~ v1_funct_1(k2_funct_1(A_793))
      | ~ v1_relat_1(k2_funct_1(A_793))
      | ~ v2_funct_1(A_793)
      | ~ v1_funct_1(A_793)
      | ~ v1_relat_1(A_793) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_54,c_1100])).

tff(c_21407,plain,
    ( m1_subset_1(k2_funct_1('#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_4',k2_relat_1(k2_funct_1('#skF_5')))))
    | ~ v1_funct_1(k2_funct_1('#skF_5'))
    | ~ v1_relat_1(k2_funct_1('#skF_5'))
    | ~ v2_funct_1('#skF_5')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_1206,c_21363])).

tff(c_21437,plain,(
    m1_subset_1(k2_funct_1('#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_4',k2_relat_1(k2_funct_1('#skF_5'))))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_234,c_100,c_94,c_19534,c_214,c_21407])).

tff(c_21466,plain,
    ( m1_subset_1(k2_funct_1('#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_4',k1_relat_1('#skF_5'))))
    | ~ v2_funct_1('#skF_5')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_52,c_21437])).

tff(c_21482,plain,(
    m1_subset_1(k2_funct_1('#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_4',k1_relat_1('#skF_5')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_234,c_100,c_94,c_21466])).

tff(c_38,plain,(
    ! [B_23,A_22] :
      ( r1_tarski(k1_relat_1(B_23),A_22)
      | ~ v4_relat_1(B_23,A_22)
      | ~ v1_relat_1(B_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_1761,plain,(
    ! [B_244,D_245,A_246,C_247] :
      ( k1_xboole_0 = B_244
      | v1_funct_2(D_245,A_246,C_247)
      | ~ r1_tarski(B_244,C_247)
      | ~ m1_subset_1(D_245,k1_zfmisc_1(k2_zfmisc_1(A_246,B_244)))
      | ~ v1_funct_2(D_245,A_246,B_244)
      | ~ v1_funct_1(D_245) ) ),
    inference(cnfTransformation,[status(thm)],[f_185])).

tff(c_25846,plain,(
    ! [B_876,D_877,A_878,A_879] :
      ( k1_relat_1(B_876) = k1_xboole_0
      | v1_funct_2(D_877,A_878,A_879)
      | ~ m1_subset_1(D_877,k1_zfmisc_1(k2_zfmisc_1(A_878,k1_relat_1(B_876))))
      | ~ v1_funct_2(D_877,A_878,k1_relat_1(B_876))
      | ~ v1_funct_1(D_877)
      | ~ v4_relat_1(B_876,A_879)
      | ~ v1_relat_1(B_876) ) ),
    inference(resolution,[status(thm)],[c_38,c_1761])).

tff(c_25855,plain,(
    ! [A_879] :
      ( k1_relat_1('#skF_5') = k1_xboole_0
      | v1_funct_2(k2_funct_1('#skF_5'),'#skF_4',A_879)
      | ~ v1_funct_2(k2_funct_1('#skF_5'),'#skF_4',k1_relat_1('#skF_5'))
      | ~ v1_funct_1(k2_funct_1('#skF_5'))
      | ~ v4_relat_1('#skF_5',A_879)
      | ~ v1_relat_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_21482,c_25846])).

tff(c_25941,plain,(
    ! [A_879] :
      ( k1_relat_1('#skF_5') = k1_xboole_0
      | v1_funct_2(k2_funct_1('#skF_5'),'#skF_4',A_879)
      | ~ v4_relat_1('#skF_5',A_879) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_234,c_214,c_19595,c_25855])).

tff(c_25971,plain,(
    k1_relat_1('#skF_5') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_25941])).

tff(c_310,plain,(
    ! [A_103,B_104] :
      ( r2_hidden('#skF_2'(A_103,B_104),A_103)
      | r1_tarski(A_103,B_104) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_315,plain,(
    ! [A_105,B_106] :
      ( ~ v1_xboole_0(A_105)
      | r1_tarski(A_105,B_106) ) ),
    inference(resolution,[status(thm)],[c_310,c_2])).

tff(c_32,plain,(
    ! [A_17,B_18] :
      ( m1_subset_1(A_17,k1_zfmisc_1(B_18))
      | ~ r1_tarski(A_17,B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_213,plain,
    ( ~ v1_funct_2(k2_funct_1('#skF_5'),'#skF_4','#skF_3')
    | ~ m1_subset_1(k2_funct_1('#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_90])).

tff(c_216,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_213])).

tff(c_220,plain,(
    ~ r1_tarski(k2_funct_1('#skF_5'),k2_zfmisc_1('#skF_4','#skF_3')) ),
    inference(resolution,[status(thm)],[c_32,c_216])).

tff(c_336,plain,(
    ~ v1_xboole_0(k2_funct_1('#skF_5')) ),
    inference(resolution,[status(thm)],[c_315,c_220])).

tff(c_30,plain,(
    ! [A_17,B_18] :
      ( r1_tarski(A_17,B_18)
      | ~ m1_subset_1(A_17,k1_zfmisc_1(B_18)) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_21643,plain,(
    r1_tarski(k2_funct_1('#skF_5'),k2_zfmisc_1('#skF_4',k1_relat_1('#skF_5'))) ),
    inference(resolution,[status(thm)],[c_21482,c_30])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_721,plain,(
    ! [C_154,B_155,A_156] :
      ( ~ v1_xboole_0(C_154)
      | ~ m1_subset_1(B_155,k1_zfmisc_1(C_154))
      | ~ r2_hidden(A_156,B_155) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_917,plain,(
    ! [B_182,A_183,A_184] :
      ( ~ v1_xboole_0(B_182)
      | ~ r2_hidden(A_183,A_184)
      | ~ r1_tarski(A_184,B_182) ) ),
    inference(resolution,[status(thm)],[c_32,c_721])).

tff(c_923,plain,(
    ! [B_182,A_1] :
      ( ~ v1_xboole_0(B_182)
      | ~ r1_tarski(A_1,B_182)
      | v1_xboole_0(A_1) ) ),
    inference(resolution,[status(thm)],[c_4,c_917])).

tff(c_21670,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1('#skF_4',k1_relat_1('#skF_5')))
    | v1_xboole_0(k2_funct_1('#skF_5')) ),
    inference(resolution,[status(thm)],[c_21643,c_923])).

tff(c_21700,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_4',k1_relat_1('#skF_5'))) ),
    inference(negUnitSimplification,[status(thm)],[c_336,c_21670])).

tff(c_25974,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_4',k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_25971,c_21700])).

tff(c_25991,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_26,c_25974])).

tff(c_25993,plain,(
    k1_relat_1('#skF_5') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_25941])).

tff(c_2042,plain,(
    ! [B_261,D_262,A_263,C_264] :
      ( k1_xboole_0 = B_261
      | m1_subset_1(D_262,k1_zfmisc_1(k2_zfmisc_1(A_263,C_264)))
      | ~ r1_tarski(B_261,C_264)
      | ~ m1_subset_1(D_262,k1_zfmisc_1(k2_zfmisc_1(A_263,B_261)))
      | ~ v1_funct_2(D_262,A_263,B_261)
      | ~ v1_funct_1(D_262) ) ),
    inference(cnfTransformation,[status(thm)],[f_185])).

tff(c_26812,plain,(
    ! [B_907,D_908,A_909,A_910] :
      ( k1_relat_1(B_907) = k1_xboole_0
      | m1_subset_1(D_908,k1_zfmisc_1(k2_zfmisc_1(A_909,A_910)))
      | ~ m1_subset_1(D_908,k1_zfmisc_1(k2_zfmisc_1(A_909,k1_relat_1(B_907))))
      | ~ v1_funct_2(D_908,A_909,k1_relat_1(B_907))
      | ~ v1_funct_1(D_908)
      | ~ v4_relat_1(B_907,A_910)
      | ~ v1_relat_1(B_907) ) ),
    inference(resolution,[status(thm)],[c_38,c_2042])).

tff(c_26821,plain,(
    ! [A_910] :
      ( k1_relat_1('#skF_5') = k1_xboole_0
      | m1_subset_1(k2_funct_1('#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_4',A_910)))
      | ~ v1_funct_2(k2_funct_1('#skF_5'),'#skF_4',k1_relat_1('#skF_5'))
      | ~ v1_funct_1(k2_funct_1('#skF_5'))
      | ~ v4_relat_1('#skF_5',A_910)
      | ~ v1_relat_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_21482,c_26812])).

tff(c_26907,plain,(
    ! [A_910] :
      ( k1_relat_1('#skF_5') = k1_xboole_0
      | m1_subset_1(k2_funct_1('#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_4',A_910)))
      | ~ v4_relat_1('#skF_5',A_910) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_234,c_214,c_19595,c_26821])).

tff(c_26943,plain,(
    ! [A_911] :
      ( m1_subset_1(k2_funct_1('#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_4',A_911)))
      | ~ v4_relat_1('#skF_5',A_911) ) ),
    inference(negUnitSimplification,[status(thm)],[c_25993,c_26907])).

tff(c_26995,plain,(
    ~ v4_relat_1('#skF_5','#skF_3') ),
    inference(resolution,[status(thm)],[c_26943,c_216])).

tff(c_27040,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_703,c_26995])).

tff(c_27042,plain,(
    m1_subset_1(k2_funct_1('#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_213])).

tff(c_27629,plain,(
    ! [C_987,A_988,B_989] :
      ( v1_xboole_0(C_987)
      | ~ m1_subset_1(C_987,k1_zfmisc_1(k2_zfmisc_1(A_988,B_989)))
      | ~ v1_xboole_0(A_988) ) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_27646,plain,
    ( v1_xboole_0(k2_funct_1('#skF_5'))
    | ~ v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_27042,c_27629])).

tff(c_27652,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_27646])).

tff(c_27101,plain,(
    ! [C_920,A_921,B_922] :
      ( v1_relat_1(C_920)
      | ~ m1_subset_1(C_920,k1_zfmisc_1(k2_zfmisc_1(A_921,B_922))) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_27118,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_96,c_27101])).

tff(c_28,plain,(
    ! [B_16] : k2_zfmisc_1(k1_xboole_0,B_16) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_27119,plain,(
    ! [C_923] :
      ( v1_relat_1(C_923)
      | ~ m1_subset_1(C_923,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_27101])).

tff(c_27126,plain,(
    ! [A_924] :
      ( v1_relat_1(A_924)
      | ~ r1_tarski(A_924,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_32,c_27119])).

tff(c_27146,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_20,c_27126])).

tff(c_44,plain,(
    ! [B_29,A_28] :
      ( r1_tarski(k7_relat_1(B_29,A_28),B_29)
      | ~ v1_relat_1(B_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_27066,plain,(
    ! [A_914,B_915] :
      ( r2_hidden('#skF_2'(A_914,B_915),A_914)
      | r1_tarski(A_914,B_915) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_27071,plain,(
    ! [A_916,B_917] :
      ( ~ v1_xboole_0(A_916)
      | r1_tarski(A_916,B_917) ) ),
    inference(resolution,[status(thm)],[c_27066,c_2])).

tff(c_16,plain,(
    ! [B_12,A_11] :
      ( B_12 = A_11
      | ~ r1_tarski(B_12,A_11)
      | ~ r1_tarski(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_27075,plain,(
    ! [B_918,A_919] :
      ( B_918 = A_919
      | ~ r1_tarski(B_918,A_919)
      | ~ v1_xboole_0(A_919) ) ),
    inference(resolution,[status(thm)],[c_27071,c_16])).

tff(c_27222,plain,(
    ! [B_937,A_938] :
      ( k7_relat_1(B_937,A_938) = B_937
      | ~ v1_xboole_0(B_937)
      | ~ v1_relat_1(B_937) ) ),
    inference(resolution,[status(thm)],[c_44,c_27075])).

tff(c_27224,plain,(
    ! [A_938] :
      ( k7_relat_1(k1_xboole_0,A_938) = k1_xboole_0
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_12,c_27222])).

tff(c_27230,plain,(
    ! [A_939] : k7_relat_1(k1_xboole_0,A_939) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_27146,c_27224])).

tff(c_42,plain,(
    ! [B_27,A_26] :
      ( r1_tarski(k1_relat_1(k7_relat_1(B_27,A_26)),A_26)
      | ~ v1_relat_1(B_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_27239,plain,(
    ! [A_939] :
      ( r1_tarski(k1_relat_1(k1_xboole_0),A_939)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_27230,c_42])).

tff(c_27260,plain,(
    ! [A_943] : r1_tarski(k1_relat_1(k1_xboole_0),A_943) ),
    inference(demodulation,[status(thm),theory(equality)],[c_27146,c_27239])).

tff(c_27074,plain,(
    ! [B_917,A_916] :
      ( B_917 = A_916
      | ~ r1_tarski(B_917,A_916)
      | ~ v1_xboole_0(A_916) ) ),
    inference(resolution,[status(thm)],[c_27071,c_16])).

tff(c_27280,plain,(
    ! [A_944] :
      ( k1_relat_1(k1_xboole_0) = A_944
      | ~ v1_xboole_0(A_944) ) ),
    inference(resolution,[status(thm)],[c_27260,c_27074])).

tff(c_27284,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_12,c_27280])).

tff(c_52218,plain,(
    ! [A_1702,B_1703,C_1704] :
      ( k2_relset_1(A_1702,B_1703,C_1704) = k2_relat_1(C_1704)
      | ~ m1_subset_1(C_1704,k1_zfmisc_1(k2_zfmisc_1(A_1702,B_1703))) ) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_52228,plain,(
    k2_relset_1('#skF_3','#skF_4','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_96,c_52218])).

tff(c_52238,plain,(
    k2_relat_1('#skF_5') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_52228])).

tff(c_27046,plain,(
    r1_tarski(k2_funct_1('#skF_5'),k2_zfmisc_1('#skF_4','#skF_3')) ),
    inference(resolution,[status(thm)],[c_27042,c_30])).

tff(c_52961,plain,(
    ! [B_1748,D_1749,A_1750,C_1751] :
      ( k1_xboole_0 = B_1748
      | v1_funct_2(D_1749,A_1750,C_1751)
      | ~ r1_tarski(B_1748,C_1751)
      | ~ m1_subset_1(D_1749,k1_zfmisc_1(k2_zfmisc_1(A_1750,B_1748)))
      | ~ v1_funct_2(D_1749,A_1750,B_1748)
      | ~ v1_funct_1(D_1749) ) ),
    inference(cnfTransformation,[status(thm)],[f_185])).

tff(c_52986,plain,(
    ! [D_1749,A_1750] :
      ( k2_funct_1('#skF_5') = k1_xboole_0
      | v1_funct_2(D_1749,A_1750,k2_zfmisc_1('#skF_4','#skF_3'))
      | ~ m1_subset_1(D_1749,k1_zfmisc_1(k2_zfmisc_1(A_1750,k2_funct_1('#skF_5'))))
      | ~ v1_funct_2(D_1749,A_1750,k2_funct_1('#skF_5'))
      | ~ v1_funct_1(D_1749) ) ),
    inference(resolution,[status(thm)],[c_27046,c_52961])).

tff(c_60234,plain,(
    k2_funct_1('#skF_5') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_52986])).

tff(c_60258,plain,
    ( k2_relat_1('#skF_5') = k1_relat_1(k1_xboole_0)
    | ~ v2_funct_1('#skF_5')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_60234,c_54])).

tff(c_60270,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_27118,c_100,c_94,c_27284,c_52238,c_60258])).

tff(c_60366,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60270,c_12])).

tff(c_60368,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_27652,c_60366])).

tff(c_60370,plain,(
    k2_funct_1('#skF_5') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_52986])).

tff(c_27575,plain,(
    ! [C_974,A_975,B_976] :
      ( v4_relat_1(C_974,A_975)
      | ~ m1_subset_1(C_974,k1_zfmisc_1(k2_zfmisc_1(A_975,B_976))) ) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_27594,plain,(
    v4_relat_1('#skF_5','#skF_3') ),
    inference(resolution,[status(thm)],[c_96,c_27575])).

tff(c_27116,plain,(
    v1_relat_1(k2_funct_1('#skF_5')) ),
    inference(resolution,[status(thm)],[c_27042,c_27101])).

tff(c_52023,plain,(
    ! [A_1677] :
      ( k1_relat_1(k2_funct_1(A_1677)) = k2_relat_1(A_1677)
      | ~ v2_funct_1(A_1677)
      | ~ v1_funct_1(A_1677)
      | ~ v1_relat_1(A_1677) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_70193,plain,(
    ! [A_2256] :
      ( v1_funct_2(k2_funct_1(A_2256),k2_relat_1(A_2256),k2_relat_1(k2_funct_1(A_2256)))
      | ~ v1_funct_1(k2_funct_1(A_2256))
      | ~ v1_relat_1(k2_funct_1(A_2256))
      | ~ v2_funct_1(A_2256)
      | ~ v1_funct_1(A_2256)
      | ~ v1_relat_1(A_2256) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_52023,c_74])).

tff(c_70214,plain,
    ( v1_funct_2(k2_funct_1('#skF_5'),'#skF_4',k2_relat_1(k2_funct_1('#skF_5')))
    | ~ v1_funct_1(k2_funct_1('#skF_5'))
    | ~ v1_relat_1(k2_funct_1('#skF_5'))
    | ~ v2_funct_1('#skF_5')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_52238,c_70193])).

tff(c_70237,plain,(
    v1_funct_2(k2_funct_1('#skF_5'),'#skF_4',k2_relat_1(k2_funct_1('#skF_5'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_27118,c_100,c_94,c_27116,c_214,c_70214])).

tff(c_70240,plain,
    ( v1_funct_2(k2_funct_1('#skF_5'),'#skF_4',k1_relat_1('#skF_5'))
    | ~ v2_funct_1('#skF_5')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_52,c_70237])).

tff(c_70242,plain,(
    v1_funct_2(k2_funct_1('#skF_5'),'#skF_4',k1_relat_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_27118,c_100,c_94,c_70240])).

tff(c_52310,plain,(
    ! [A_1708] :
      ( m1_subset_1(A_1708,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_1708),k2_relat_1(A_1708))))
      | ~ v1_funct_1(A_1708)
      | ~ v1_relat_1(A_1708) ) ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_71744,plain,(
    ! [A_2277] :
      ( m1_subset_1(k2_funct_1(A_2277),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(A_2277),k2_relat_1(k2_funct_1(A_2277)))))
      | ~ v1_funct_1(k2_funct_1(A_2277))
      | ~ v1_relat_1(k2_funct_1(A_2277))
      | ~ v2_funct_1(A_2277)
      | ~ v1_funct_1(A_2277)
      | ~ v1_relat_1(A_2277) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_54,c_52310])).

tff(c_71791,plain,
    ( m1_subset_1(k2_funct_1('#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_4',k2_relat_1(k2_funct_1('#skF_5')))))
    | ~ v1_funct_1(k2_funct_1('#skF_5'))
    | ~ v1_relat_1(k2_funct_1('#skF_5'))
    | ~ v2_funct_1('#skF_5')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_52238,c_71744])).

tff(c_71823,plain,(
    m1_subset_1(k2_funct_1('#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_4',k2_relat_1(k2_funct_1('#skF_5'))))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_27118,c_100,c_94,c_27116,c_214,c_71791])).

tff(c_71852,plain,
    ( m1_subset_1(k2_funct_1('#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_4',k1_relat_1('#skF_5'))))
    | ~ v2_funct_1('#skF_5')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_52,c_71823])).

tff(c_71868,plain,(
    m1_subset_1(k2_funct_1('#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_4',k1_relat_1('#skF_5')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_27118,c_100,c_94,c_71852])).

tff(c_73756,plain,(
    ! [B_2319,D_2320,A_2321,A_2322] :
      ( k1_relat_1(B_2319) = k1_xboole_0
      | v1_funct_2(D_2320,A_2321,A_2322)
      | ~ m1_subset_1(D_2320,k1_zfmisc_1(k2_zfmisc_1(A_2321,k1_relat_1(B_2319))))
      | ~ v1_funct_2(D_2320,A_2321,k1_relat_1(B_2319))
      | ~ v1_funct_1(D_2320)
      | ~ v4_relat_1(B_2319,A_2322)
      | ~ v1_relat_1(B_2319) ) ),
    inference(resolution,[status(thm)],[c_38,c_52961])).

tff(c_73760,plain,(
    ! [A_2322] :
      ( k1_relat_1('#skF_5') = k1_xboole_0
      | v1_funct_2(k2_funct_1('#skF_5'),'#skF_4',A_2322)
      | ~ v1_funct_2(k2_funct_1('#skF_5'),'#skF_4',k1_relat_1('#skF_5'))
      | ~ v1_funct_1(k2_funct_1('#skF_5'))
      | ~ v4_relat_1('#skF_5',A_2322)
      | ~ v1_relat_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_71868,c_73756])).

tff(c_73842,plain,(
    ! [A_2322] :
      ( k1_relat_1('#skF_5') = k1_xboole_0
      | v1_funct_2(k2_funct_1('#skF_5'),'#skF_4',A_2322)
      | ~ v4_relat_1('#skF_5',A_2322) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_27118,c_214,c_70242,c_73760])).

tff(c_74606,plain,(
    k1_relat_1('#skF_5') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_73842])).

tff(c_71866,plain,(
    r1_tarski(k2_funct_1('#skF_5'),k2_zfmisc_1('#skF_4',k2_relat_1(k2_funct_1('#skF_5')))) ),
    inference(resolution,[status(thm)],[c_71823,c_30])).

tff(c_71973,plain,
    ( r1_tarski(k2_funct_1('#skF_5'),k2_zfmisc_1('#skF_4',k1_relat_1('#skF_5')))
    | ~ v2_funct_1('#skF_5')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_52,c_71866])).

tff(c_72001,plain,(
    r1_tarski(k2_funct_1('#skF_5'),k2_zfmisc_1('#skF_4',k1_relat_1('#skF_5'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_27118,c_100,c_94,c_71973])).

tff(c_27503,plain,(
    ! [C_962,B_963,A_964] :
      ( ~ v1_xboole_0(C_962)
      | ~ m1_subset_1(B_963,k1_zfmisc_1(C_962))
      | ~ r2_hidden(A_964,B_963) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_52108,plain,(
    ! [B_1687,A_1688,A_1689] :
      ( ~ v1_xboole_0(B_1687)
      | ~ r2_hidden(A_1688,A_1689)
      | ~ r1_tarski(A_1689,B_1687) ) ),
    inference(resolution,[status(thm)],[c_32,c_27503])).

tff(c_52114,plain,(
    ! [B_1687,A_1] :
      ( ~ v1_xboole_0(B_1687)
      | ~ r1_tarski(A_1,B_1687)
      | v1_xboole_0(A_1) ) ),
    inference(resolution,[status(thm)],[c_4,c_52108])).

tff(c_72060,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1('#skF_4',k1_relat_1('#skF_5')))
    | v1_xboole_0(k2_funct_1('#skF_5')) ),
    inference(resolution,[status(thm)],[c_72001,c_52114])).

tff(c_72111,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_4',k1_relat_1('#skF_5'))) ),
    inference(splitLeft,[status(thm)],[c_72060])).

tff(c_74608,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_4',k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74606,c_72111])).

tff(c_74624,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_26,c_74608])).

tff(c_74692,plain,(
    ! [A_2339] :
      ( v1_funct_2(k2_funct_1('#skF_5'),'#skF_4',A_2339)
      | ~ v4_relat_1('#skF_5',A_2339) ) ),
    inference(splitRight,[status(thm)],[c_73842])).

tff(c_27041,plain,(
    ~ v1_funct_2(k2_funct_1('#skF_5'),'#skF_4','#skF_3') ),
    inference(splitRight,[status(thm)],[c_213])).

tff(c_74695,plain,(
    ~ v4_relat_1('#skF_5','#skF_3') ),
    inference(resolution,[status(thm)],[c_74692,c_27041])).

tff(c_74699,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_27594,c_74695])).

tff(c_74700,plain,(
    v1_xboole_0(k2_funct_1('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_72060])).

tff(c_14,plain,(
    ! [A_10] :
      ( k1_xboole_0 = A_10
      | ~ v1_xboole_0(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_74748,plain,(
    k2_funct_1('#skF_5') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_74700,c_14])).

tff(c_74778,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_60370,c_74748])).

tff(c_74780,plain,(
    v1_xboole_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_27646])).

tff(c_74794,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_74780,c_14])).

tff(c_74832,plain,(
    ! [B_16] : k2_zfmisc_1('#skF_4',B_16) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_74794,c_74794,c_28])).

tff(c_27095,plain,
    ( k2_zfmisc_1('#skF_4','#skF_3') = k2_funct_1('#skF_5')
    | ~ v1_xboole_0(k2_zfmisc_1('#skF_4','#skF_3')) ),
    inference(resolution,[status(thm)],[c_27046,c_27075])).

tff(c_27285,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_4','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_27095])).

tff(c_74952,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74832,c_27285])).

tff(c_74955,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_74780,c_74952])).

tff(c_74957,plain,(
    v1_xboole_0(k2_zfmisc_1('#skF_4','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_27095])).

tff(c_75003,plain,(
    k2_zfmisc_1('#skF_4','#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_74957,c_14])).

tff(c_24,plain,(
    ! [B_16,A_15] :
      ( k1_xboole_0 = B_16
      | k1_xboole_0 = A_15
      | k2_zfmisc_1(A_15,B_16) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_75021,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_75003,c_24])).

tff(c_75082,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_75021])).

tff(c_27249,plain,(
    ! [A_939] : r1_tarski(k1_relat_1(k1_xboole_0),A_939) ),
    inference(demodulation,[status(thm),theory(equality)],[c_27146,c_27239])).

tff(c_74959,plain,(
    ! [A_939] : r1_tarski(k1_xboole_0,A_939) ),
    inference(demodulation,[status(thm),theory(equality)],[c_27284,c_27249])).

tff(c_75088,plain,(
    ! [A_939] : r1_tarski('#skF_4',A_939) ),
    inference(demodulation,[status(thm),theory(equality)],[c_75082,c_74959])).

tff(c_75098,plain,(
    ! [A_15] : k2_zfmisc_1(A_15,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_75082,c_75082,c_26])).

tff(c_150,plain,(
    ! [A_72,B_73] :
      ( r1_tarski(A_72,B_73)
      | ~ m1_subset_1(A_72,k1_zfmisc_1(B_73)) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_158,plain,(
    r1_tarski('#skF_5',k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_96,c_150])).

tff(c_27047,plain,(
    ! [B_912,A_913] :
      ( B_912 = A_913
      | ~ r1_tarski(B_912,A_913)
      | ~ r1_tarski(A_913,B_912) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_27061,plain,
    ( k2_zfmisc_1('#skF_3','#skF_4') = '#skF_5'
    | ~ r1_tarski(k2_zfmisc_1('#skF_3','#skF_4'),'#skF_5') ),
    inference(resolution,[status(thm)],[c_158,c_27047])).

tff(c_27209,plain,(
    ~ r1_tarski(k2_zfmisc_1('#skF_3','#skF_4'),'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_27061])).

tff(c_75253,plain,(
    ~ r1_tarski('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_75098,c_27209])).

tff(c_75259,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_75088,c_75253])).

tff(c_75260,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_75021])).

tff(c_75267,plain,(
    ! [A_939] : r1_tarski('#skF_3',A_939) ),
    inference(demodulation,[status(thm),theory(equality)],[c_75260,c_74959])).

tff(c_75276,plain,(
    ! [B_16] : k2_zfmisc_1('#skF_3',B_16) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_75260,c_75260,c_28])).

tff(c_75431,plain,(
    ~ r1_tarski('#skF_3','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_75276,c_27209])).

tff(c_75437,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_75267,c_75431])).

tff(c_75438,plain,(
    k2_zfmisc_1('#skF_3','#skF_4') = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_27061])).

tff(c_27098,plain,
    ( k2_zfmisc_1('#skF_3','#skF_4') = '#skF_5'
    | ~ v1_xboole_0(k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_158,c_27075])).

tff(c_27125,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_27098])).

tff(c_75440,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_75438,c_27125])).

tff(c_133683,plain,(
    ! [C_3620,A_3621,B_3622] :
      ( v1_xboole_0(C_3620)
      | ~ m1_subset_1(C_3620,k1_zfmisc_1(k2_zfmisc_1(A_3621,B_3622)))
      | ~ v1_xboole_0(A_3621) ) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_133700,plain,
    ( v1_xboole_0(k2_funct_1('#skF_5'))
    | ~ v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_27042,c_133683])).

tff(c_133704,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_133700])).

tff(c_75442,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_75438,c_96])).

tff(c_134075,plain,(
    ! [A_3655,B_3656,C_3657] :
      ( k2_relset_1(A_3655,B_3656,C_3657) = k2_relat_1(C_3657)
      | ~ m1_subset_1(C_3657,k1_zfmisc_1(k2_zfmisc_1(A_3655,B_3656))) ) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_134193,plain,(
    ! [C_3663] :
      ( k2_relset_1('#skF_3','#skF_4',C_3663) = k2_relat_1(C_3663)
      | ~ m1_subset_1(C_3663,k1_zfmisc_1('#skF_5')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_75438,c_134075])).

tff(c_134196,plain,(
    k2_relset_1('#skF_3','#skF_4','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_75442,c_134193])).

tff(c_134202,plain,(
    k2_relat_1('#skF_5') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_134196])).

tff(c_75565,plain,(
    ! [B_2393,A_2394] :
      ( k7_relat_1(B_2393,A_2394) = B_2393
      | ~ v1_xboole_0(B_2393)
      | ~ v1_relat_1(B_2393) ) ),
    inference(resolution,[status(thm)],[c_44,c_27075])).

tff(c_75567,plain,(
    ! [A_2394] :
      ( k7_relat_1(k1_xboole_0,A_2394) = k1_xboole_0
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_12,c_75565])).

tff(c_75573,plain,(
    ! [A_2395] : k7_relat_1(k1_xboole_0,A_2395) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_27146,c_75567])).

tff(c_75586,plain,(
    ! [A_2395] :
      ( r1_tarski(k1_relat_1(k1_xboole_0),A_2395)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_75573,c_42])).

tff(c_75622,plain,(
    ! [A_2399] : r1_tarski(k1_relat_1(k1_xboole_0),A_2399) ),
    inference(demodulation,[status(thm),theory(equality)],[c_27146,c_75586])).

tff(c_75510,plain,(
    ! [C_2382,B_2383,A_2384] :
      ( ~ v1_xboole_0(C_2382)
      | ~ m1_subset_1(B_2383,k1_zfmisc_1(C_2382))
      | ~ r2_hidden(A_2384,B_2383) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_75521,plain,(
    ! [B_2385,A_2386,A_2387] :
      ( ~ v1_xboole_0(B_2385)
      | ~ r2_hidden(A_2386,A_2387)
      | ~ r1_tarski(A_2387,B_2385) ) ),
    inference(resolution,[status(thm)],[c_32,c_75510])).

tff(c_75527,plain,(
    ! [B_2385,A_1] :
      ( ~ v1_xboole_0(B_2385)
      | ~ r1_tarski(A_1,B_2385)
      | v1_xboole_0(A_1) ) ),
    inference(resolution,[status(thm)],[c_4,c_75521])).

tff(c_75647,plain,(
    ! [A_2399] :
      ( ~ v1_xboole_0(A_2399)
      | v1_xboole_0(k1_relat_1(k1_xboole_0)) ) ),
    inference(resolution,[status(thm)],[c_75622,c_75527])).

tff(c_75666,plain,(
    ! [A_2399] : ~ v1_xboole_0(A_2399) ),
    inference(splitLeft,[status(thm)],[c_75647])).

tff(c_75670,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_75666,c_12])).

tff(c_75671,plain,(
    v1_xboole_0(k1_relat_1(k1_xboole_0)) ),
    inference(splitRight,[status(thm)],[c_75647])).

tff(c_75688,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_75671,c_14])).

tff(c_135265,plain,(
    ! [B_3716,D_3717,A_3718,C_3719] :
      ( k1_xboole_0 = B_3716
      | v1_funct_2(D_3717,A_3718,C_3719)
      | ~ r1_tarski(B_3716,C_3719)
      | ~ m1_subset_1(D_3717,k1_zfmisc_1(k2_zfmisc_1(A_3718,B_3716)))
      | ~ v1_funct_2(D_3717,A_3718,B_3716)
      | ~ v1_funct_1(D_3717) ) ),
    inference(cnfTransformation,[status(thm)],[f_185])).

tff(c_135293,plain,(
    ! [D_3717,A_3718] :
      ( k2_funct_1('#skF_5') = k1_xboole_0
      | v1_funct_2(D_3717,A_3718,k2_zfmisc_1('#skF_4','#skF_3'))
      | ~ m1_subset_1(D_3717,k1_zfmisc_1(k2_zfmisc_1(A_3718,k2_funct_1('#skF_5'))))
      | ~ v1_funct_2(D_3717,A_3718,k2_funct_1('#skF_5'))
      | ~ v1_funct_1(D_3717) ) ),
    inference(resolution,[status(thm)],[c_27046,c_135265])).

tff(c_135386,plain,(
    k2_funct_1('#skF_5') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_135293])).

tff(c_135409,plain,
    ( k2_relat_1('#skF_5') = k1_relat_1(k1_xboole_0)
    | ~ v2_funct_1('#skF_5')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_135386,c_54])).

tff(c_135424,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_27118,c_100,c_94,c_134202,c_75688,c_135409])).

tff(c_135485,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_135424,c_12])).

tff(c_135487,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_133704,c_135485])).

tff(c_135489,plain,(
    k2_funct_1('#skF_5') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_135293])).

tff(c_75784,plain,(
    ! [C_2409,A_2410,B_2411] :
      ( v4_relat_1(C_2409,A_2410)
      | ~ m1_subset_1(C_2409,k1_zfmisc_1(k2_zfmisc_1(A_2410,B_2411))) ) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_75810,plain,(
    ! [C_2415] :
      ( v4_relat_1(C_2415,'#skF_3')
      | ~ m1_subset_1(C_2415,k1_zfmisc_1('#skF_5')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_75438,c_75784])).

tff(c_75818,plain,(
    v4_relat_1('#skF_5','#skF_3') ),
    inference(resolution,[status(thm)],[c_75442,c_75810])).

tff(c_133940,plain,(
    ! [A_3641] :
      ( k1_relat_1(k2_funct_1(A_3641)) = k2_relat_1(A_3641)
      | ~ v2_funct_1(A_3641)
      | ~ v1_funct_1(A_3641)
      | ~ v1_relat_1(A_3641) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_203266,plain,(
    ! [A_5065] :
      ( v1_funct_2(k2_funct_1(A_5065),k2_relat_1(A_5065),k2_relat_1(k2_funct_1(A_5065)))
      | ~ v1_funct_1(k2_funct_1(A_5065))
      | ~ v1_relat_1(k2_funct_1(A_5065))
      | ~ v2_funct_1(A_5065)
      | ~ v1_funct_1(A_5065)
      | ~ v1_relat_1(A_5065) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_133940,c_74])).

tff(c_203305,plain,
    ( v1_funct_2(k2_funct_1('#skF_5'),'#skF_4',k2_relat_1(k2_funct_1('#skF_5')))
    | ~ v1_funct_1(k2_funct_1('#skF_5'))
    | ~ v1_relat_1(k2_funct_1('#skF_5'))
    | ~ v2_funct_1('#skF_5')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_134202,c_203266])).

tff(c_203324,plain,(
    v1_funct_2(k2_funct_1('#skF_5'),'#skF_4',k2_relat_1(k2_funct_1('#skF_5'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_27118,c_100,c_94,c_27116,c_214,c_203305])).

tff(c_203371,plain,
    ( v1_funct_2(k2_funct_1('#skF_5'),'#skF_4',k1_relat_1('#skF_5'))
    | ~ v2_funct_1('#skF_5')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_52,c_203324])).

tff(c_203373,plain,(
    v1_funct_2(k2_funct_1('#skF_5'),'#skF_4',k1_relat_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_27118,c_100,c_94,c_203371])).

tff(c_134316,plain,(
    ! [A_3671] :
      ( m1_subset_1(A_3671,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_3671),k2_relat_1(A_3671))))
      | ~ v1_funct_1(A_3671)
      | ~ v1_relat_1(A_3671) ) ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_205686,plain,(
    ! [A_5105] :
      ( m1_subset_1(k2_funct_1(A_5105),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(A_5105),k2_relat_1(k2_funct_1(A_5105)))))
      | ~ v1_funct_1(k2_funct_1(A_5105))
      | ~ v1_relat_1(k2_funct_1(A_5105))
      | ~ v2_funct_1(A_5105)
      | ~ v1_funct_1(A_5105)
      | ~ v1_relat_1(A_5105) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_54,c_134316])).

tff(c_205751,plain,
    ( m1_subset_1(k2_funct_1('#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_4',k2_relat_1(k2_funct_1('#skF_5')))))
    | ~ v1_funct_1(k2_funct_1('#skF_5'))
    | ~ v1_relat_1(k2_funct_1('#skF_5'))
    | ~ v2_funct_1('#skF_5')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_134202,c_205686])).

tff(c_205787,plain,(
    m1_subset_1(k2_funct_1('#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_4',k2_relat_1(k2_funct_1('#skF_5'))))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_27118,c_100,c_94,c_27116,c_214,c_205751])).

tff(c_205866,plain,
    ( m1_subset_1(k2_funct_1('#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_4',k1_relat_1('#skF_5'))))
    | ~ v2_funct_1('#skF_5')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_52,c_205787])).

tff(c_205882,plain,(
    m1_subset_1(k2_funct_1('#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_4',k1_relat_1('#skF_5')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_27118,c_100,c_94,c_205866])).

tff(c_211742,plain,(
    ! [B_5185,D_5186,A_5187,A_5188] :
      ( k1_relat_1(B_5185) = k1_xboole_0
      | v1_funct_2(D_5186,A_5187,A_5188)
      | ~ m1_subset_1(D_5186,k1_zfmisc_1(k2_zfmisc_1(A_5187,k1_relat_1(B_5185))))
      | ~ v1_funct_2(D_5186,A_5187,k1_relat_1(B_5185))
      | ~ v1_funct_1(D_5186)
      | ~ v4_relat_1(B_5185,A_5188)
      | ~ v1_relat_1(B_5185) ) ),
    inference(resolution,[status(thm)],[c_38,c_135265])).

tff(c_211765,plain,(
    ! [A_5188] :
      ( k1_relat_1('#skF_5') = k1_xboole_0
      | v1_funct_2(k2_funct_1('#skF_5'),'#skF_4',A_5188)
      | ~ v1_funct_2(k2_funct_1('#skF_5'),'#skF_4',k1_relat_1('#skF_5'))
      | ~ v1_funct_1(k2_funct_1('#skF_5'))
      | ~ v4_relat_1('#skF_5',A_5188)
      | ~ v1_relat_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_205882,c_211742])).

tff(c_211835,plain,(
    ! [A_5188] :
      ( k1_relat_1('#skF_5') = k1_xboole_0
      | v1_funct_2(k2_funct_1('#skF_5'),'#skF_4',A_5188)
      | ~ v4_relat_1('#skF_5',A_5188) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_27118,c_214,c_203373,c_211765])).

tff(c_214593,plain,(
    k1_relat_1('#skF_5') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_211835])).

tff(c_205880,plain,(
    r1_tarski(k2_funct_1('#skF_5'),k2_zfmisc_1('#skF_4',k2_relat_1(k2_funct_1('#skF_5')))) ),
    inference(resolution,[status(thm)],[c_205787,c_30])).

tff(c_205931,plain,
    ( r1_tarski(k2_funct_1('#skF_5'),k2_zfmisc_1('#skF_4',k1_relat_1('#skF_5')))
    | ~ v2_funct_1('#skF_5')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_52,c_205880])).

tff(c_205959,plain,(
    r1_tarski(k2_funct_1('#skF_5'),k2_zfmisc_1('#skF_4',k1_relat_1('#skF_5'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_27118,c_100,c_94,c_205931])).

tff(c_206022,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1('#skF_4',k1_relat_1('#skF_5')))
    | v1_xboole_0(k2_funct_1('#skF_5')) ),
    inference(resolution,[status(thm)],[c_205959,c_75527])).

tff(c_206069,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_4',k1_relat_1('#skF_5'))) ),
    inference(splitLeft,[status(thm)],[c_206022])).

tff(c_214605,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_4',k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_214593,c_206069])).

tff(c_214616,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_26,c_214605])).

tff(c_214719,plain,(
    ! [A_5240] :
      ( v1_funct_2(k2_funct_1('#skF_5'),'#skF_4',A_5240)
      | ~ v4_relat_1('#skF_5',A_5240) ) ),
    inference(splitRight,[status(thm)],[c_211835])).

tff(c_214722,plain,(
    ~ v4_relat_1('#skF_5','#skF_3') ),
    inference(resolution,[status(thm)],[c_214719,c_27041])).

tff(c_214726,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_75818,c_214722])).

tff(c_214727,plain,(
    v1_xboole_0(k2_funct_1('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_206022])).

tff(c_214772,plain,(
    k2_funct_1('#skF_5') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_214727,c_14])).

tff(c_214804,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_135489,c_214772])).

tff(c_214806,plain,(
    v1_xboole_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_133700])).

tff(c_214820,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_214806,c_14])).

tff(c_75451,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 != '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_75438,c_24])).

tff(c_75507,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_75451])).

tff(c_214853,plain,(
    '#skF_5' != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_214820,c_75507])).

tff(c_214860,plain,(
    ! [A_15] : k2_zfmisc_1(A_15,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_214820,c_214820,c_26])).

tff(c_214995,plain,(
    '#skF_5' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_214860,c_75438])).

tff(c_214997,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_214853,c_214995])).

tff(c_214999,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_75451])).

tff(c_215008,plain,(
    v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_214999,c_12])).

tff(c_215012,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_75440,c_215008])).

tff(c_215013,plain,(
    k2_zfmisc_1('#skF_3','#skF_4') = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_27098])).

tff(c_215015,plain,(
    ~ r1_tarski(k2_zfmisc_1('#skF_3','#skF_4'),'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_27061])).

tff(c_215097,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_215013,c_215015])).

tff(c_215098,plain,(
    k2_zfmisc_1('#skF_3','#skF_4') = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_27061])).

tff(c_215014,plain,(
    v1_xboole_0(k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_27098])).

tff(c_215115,plain,(
    v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_215098,c_215014])).

tff(c_215122,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_215115,c_14])).

tff(c_215134,plain,(
    ! [B_5253,A_5254] :
      ( B_5253 = '#skF_5'
      | A_5254 = '#skF_5'
      | k2_zfmisc_1(A_5254,B_5253) != '#skF_5' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_215122,c_215122,c_215122,c_24])).

tff(c_215138,plain,
    ( '#skF_5' = '#skF_4'
    | '#skF_5' = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_215098,c_215134])).

tff(c_215182,plain,(
    '#skF_5' = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_215138])).

tff(c_215192,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_215182,c_27118])).

tff(c_215200,plain,(
    v1_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_215182,c_100])).

tff(c_215199,plain,(
    v2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_215182,c_94])).

tff(c_10,plain,(
    ! [A_5,B_6] :
      ( r2_hidden('#skF_2'(A_5,B_6),A_5)
      | r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_215188,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_215182,c_215115])).

tff(c_215101,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_215098,c_96])).

tff(c_215189,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_215182,c_215182,c_215101])).

tff(c_215527,plain,(
    ! [C_5306,B_5307,A_5308] :
      ( ~ v1_xboole_0(C_5306)
      | ~ m1_subset_1(B_5307,k1_zfmisc_1(C_5306))
      | ~ r2_hidden(A_5308,B_5307) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_215529,plain,(
    ! [A_5308] :
      ( ~ v1_xboole_0('#skF_3')
      | ~ r2_hidden(A_5308,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_215189,c_215527])).

tff(c_215536,plain,(
    ! [A_5309] : ~ r2_hidden(A_5309,'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_215188,c_215529])).

tff(c_215548,plain,(
    ! [B_5310] : r1_tarski('#skF_3',B_5310) ),
    inference(resolution,[status(thm)],[c_10,c_215536])).

tff(c_215575,plain,(
    ! [B_5311] :
      ( B_5311 = '#skF_3'
      | ~ r1_tarski(B_5311,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_215548,c_16])).

tff(c_215591,plain,(
    ! [A_28] :
      ( k7_relat_1('#skF_3',A_28) = '#skF_3'
      | ~ v1_relat_1('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_44,c_215575])).

tff(c_215609,plain,(
    ! [A_5312] : k7_relat_1('#skF_3',A_5312) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_215192,c_215591])).

tff(c_215621,plain,(
    ! [A_5312] :
      ( r1_tarski(k1_relat_1('#skF_3'),A_5312)
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_215609,c_42])).

tff(c_215669,plain,(
    ! [A_5315] : r1_tarski(k1_relat_1('#skF_3'),A_5315) ),
    inference(demodulation,[status(thm),theory(equality)],[c_215192,c_215621])).

tff(c_215573,plain,(
    ! [B_5310] :
      ( B_5310 = '#skF_3'
      | ~ r1_tarski(B_5310,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_215548,c_16])).

tff(c_215694,plain,(
    k1_relat_1('#skF_3') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_215669,c_215573])).

tff(c_215126,plain,(
    ! [A_15] : k2_zfmisc_1(A_15,'#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_215122,c_215122,c_26])).

tff(c_215184,plain,(
    ! [A_15] : k2_zfmisc_1(A_15,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_215182,c_215182,c_215126])).

tff(c_215194,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_215182,c_27042])).

tff(c_215335,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_215184,c_215194])).

tff(c_215344,plain,(
    r1_tarski(k2_funct_1('#skF_3'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_215335,c_30])).

tff(c_215350,plain,
    ( k2_funct_1('#skF_3') = '#skF_3'
    | ~ v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_215344,c_27074])).

tff(c_215357,plain,(
    k2_funct_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_215188,c_215350])).

tff(c_216081,plain,(
    ! [A_5353] :
      ( k1_relat_1(k2_funct_1(A_5353)) = k2_relat_1(A_5353)
      | ~ v2_funct_1(A_5353)
      | ~ v1_funct_1(A_5353)
      | ~ v1_relat_1(A_5353) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_216104,plain,
    ( k2_relat_1('#skF_3') = k1_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_215357,c_216081])).

tff(c_216108,plain,(
    k2_relat_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_215192,c_215200,c_215199,c_215694,c_216104])).

tff(c_215125,plain,(
    ! [B_16] : k2_zfmisc_1('#skF_5',B_16) = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_215122,c_215122,c_28])).

tff(c_215183,plain,(
    ! [B_16] : k2_zfmisc_1('#skF_3',B_16) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_215182,c_215182,c_215125])).

tff(c_216916,plain,(
    ! [A_5417,B_5418,C_5419] :
      ( k2_relset_1(A_5417,B_5418,C_5419) = k2_relat_1(C_5419)
      | ~ m1_subset_1(C_5419,k1_zfmisc_1(k2_zfmisc_1(A_5417,B_5418))) ) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_221384,plain,(
    ! [B_5615,C_5616] :
      ( k2_relset_1('#skF_3',B_5615,C_5616) = k2_relat_1(C_5616)
      | ~ m1_subset_1(C_5616,k1_zfmisc_1('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_215183,c_216916])).

tff(c_221386,plain,(
    ! [B_5615] : k2_relset_1('#skF_3',B_5615,'#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_215189,c_221384])).

tff(c_221393,plain,(
    ! [B_5617] : k2_relset_1('#skF_3',B_5617,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_216108,c_221386])).

tff(c_215197,plain,(
    k2_relset_1('#skF_3','#skF_4','#skF_3') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_215182,c_92])).

tff(c_221400,plain,(
    '#skF_3' = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_221393,c_215197])).

tff(c_215781,plain,(
    ! [A_5321] :
      ( v1_funct_2(A_5321,k1_relat_1(A_5321),k2_relat_1(A_5321))
      | ~ v1_funct_1(A_5321)
      | ~ v1_relat_1(A_5321) ) ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_215787,plain,
    ( v1_funct_2('#skF_3','#skF_3',k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_215694,c_215781])).

tff(c_215792,plain,(
    v1_funct_2('#skF_3','#skF_3',k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_215192,c_215200,c_215787])).

tff(c_216109,plain,(
    v1_funct_2('#skF_3','#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_216108,c_215792])).

tff(c_215545,plain,(
    ! [B_6] : r1_tarski('#skF_3',B_6) ),
    inference(resolution,[status(thm)],[c_10,c_215536])).

tff(c_215187,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_215182,c_215122])).

tff(c_82,plain,(
    ! [D_58,C_57,B_56] :
      ( v1_funct_2(D_58,k1_xboole_0,C_57)
      | ~ r1_tarski(B_56,C_57)
      | ~ m1_subset_1(D_58,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_56)))
      | ~ v1_funct_2(D_58,k1_xboole_0,B_56)
      | ~ v1_funct_1(D_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_185])).

tff(c_102,plain,(
    ! [D_58,C_57,B_56] :
      ( v1_funct_2(D_58,k1_xboole_0,C_57)
      | ~ r1_tarski(B_56,C_57)
      | ~ m1_subset_1(D_58,k1_zfmisc_1(k1_xboole_0))
      | ~ v1_funct_2(D_58,k1_xboole_0,B_56)
      | ~ v1_funct_1(D_58) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_82])).

tff(c_218066,plain,(
    ! [D_5484,C_5485,B_5486] :
      ( v1_funct_2(D_5484,'#skF_3',C_5485)
      | ~ r1_tarski(B_5486,C_5485)
      | ~ m1_subset_1(D_5484,k1_zfmisc_1('#skF_3'))
      | ~ v1_funct_2(D_5484,'#skF_3',B_5486)
      | ~ v1_funct_1(D_5484) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_215187,c_215187,c_215187,c_102])).

tff(c_218205,plain,(
    ! [D_5494,B_5495] :
      ( v1_funct_2(D_5494,'#skF_3',B_5495)
      | ~ m1_subset_1(D_5494,k1_zfmisc_1('#skF_3'))
      | ~ v1_funct_2(D_5494,'#skF_3','#skF_3')
      | ~ v1_funct_1(D_5494) ) ),
    inference(resolution,[status(thm)],[c_215545,c_218066])).

tff(c_218207,plain,(
    ! [B_5495] :
      ( v1_funct_2('#skF_3','#skF_3',B_5495)
      | ~ v1_funct_2('#skF_3','#skF_3','#skF_3')
      | ~ v1_funct_1('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_215189,c_218205])).

tff(c_218213,plain,(
    ! [B_5495] : v1_funct_2('#skF_3','#skF_3',B_5495) ),
    inference(demodulation,[status(thm),theory(equality)],[c_215200,c_216109,c_218207])).

tff(c_221433,plain,(
    ! [B_5495] : v1_funct_2('#skF_4','#skF_4',B_5495) ),
    inference(demodulation,[status(thm),theory(equality)],[c_221400,c_221400,c_218213])).

tff(c_215195,plain,(
    ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_215182,c_27041])).

tff(c_215361,plain,(
    ~ v1_funct_2('#skF_3','#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_215357,c_215195])).

tff(c_221482,plain,(
    ~ v1_funct_2('#skF_4','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_221400,c_221400,c_215361])).

tff(c_222392,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_221433,c_221482])).

tff(c_222393,plain,(
    '#skF_5' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_215138])).

tff(c_222412,plain,(
    v1_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_222393,c_100])).

tff(c_222404,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_222393,c_27118])).

tff(c_222411,plain,(
    v2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_222393,c_94])).

tff(c_222400,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_222393,c_215115])).

tff(c_222401,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_222393,c_222393,c_215101])).

tff(c_222636,plain,(
    ! [C_5656,B_5657,A_5658] :
      ( ~ v1_xboole_0(C_5656)
      | ~ m1_subset_1(B_5657,k1_zfmisc_1(C_5656))
      | ~ r2_hidden(A_5658,B_5657) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_222638,plain,(
    ! [A_5658] :
      ( ~ v1_xboole_0('#skF_4')
      | ~ r2_hidden(A_5658,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_222401,c_222636])).

tff(c_222645,plain,(
    ! [A_5659] : ~ r2_hidden(A_5659,'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_222400,c_222638])).

tff(c_222657,plain,(
    ! [B_5660] : r1_tarski('#skF_4',B_5660) ),
    inference(resolution,[status(thm)],[c_10,c_222645])).

tff(c_222677,plain,(
    ! [B_5661] :
      ( B_5661 = '#skF_4'
      | ~ r1_tarski(B_5661,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_222657,c_16])).

tff(c_222693,plain,(
    ! [A_28] :
      ( k7_relat_1('#skF_4',A_28) = '#skF_4'
      | ~ v1_relat_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_44,c_222677])).

tff(c_222711,plain,(
    ! [A_5662] : k7_relat_1('#skF_4',A_5662) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_222404,c_222693])).

tff(c_222719,plain,(
    ! [A_5662] :
      ( r1_tarski(k1_relat_1('#skF_4'),A_5662)
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_222711,c_42])).

tff(c_222733,plain,(
    ! [A_5663] : r1_tarski(k1_relat_1('#skF_4'),A_5663) ),
    inference(demodulation,[status(thm),theory(equality)],[c_222404,c_222719])).

tff(c_222676,plain,(
    ! [B_5660] :
      ( B_5660 = '#skF_4'
      | ~ r1_tarski(B_5660,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_222657,c_16])).

tff(c_222754,plain,(
    k1_relat_1('#skF_4') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_222733,c_222676])).

tff(c_222395,plain,(
    ! [B_16] : k2_zfmisc_1('#skF_4',B_16) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_222393,c_222393,c_215125])).

tff(c_222406,plain,(
    m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_222393,c_27042])).

tff(c_222531,plain,(
    m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_222395,c_222406])).

tff(c_222535,plain,(
    r1_tarski(k2_funct_1('#skF_4'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_222531,c_30])).

tff(c_222541,plain,
    ( k2_funct_1('#skF_4') = '#skF_4'
    | ~ v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_222535,c_27074])).

tff(c_222548,plain,(
    k2_funct_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_222400,c_222541])).

tff(c_223413,plain,(
    ! [A_5741] :
      ( k1_relat_1(k2_funct_1(A_5741)) = k2_relat_1(A_5741)
      | ~ v2_funct_1(A_5741)
      | ~ v1_funct_1(A_5741)
      | ~ v1_relat_1(A_5741) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_223442,plain,
    ( k2_relat_1('#skF_4') = k1_relat_1('#skF_4')
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_222548,c_223413])).

tff(c_223446,plain,(
    k2_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_222404,c_222412,c_222411,c_222754,c_223442])).

tff(c_223088,plain,(
    ! [A_5709] :
      ( v1_funct_2(A_5709,k1_relat_1(A_5709),k2_relat_1(A_5709))
      | ~ v1_funct_1(A_5709)
      | ~ v1_relat_1(A_5709) ) ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_223094,plain,
    ( v1_funct_2('#skF_4','#skF_4',k2_relat_1('#skF_4'))
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_222754,c_223088])).

tff(c_223099,plain,(
    v1_funct_2('#skF_4','#skF_4',k2_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_222404,c_222412,c_223094])).

tff(c_223447,plain,(
    v1_funct_2('#skF_4','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_223446,c_223099])).

tff(c_222654,plain,(
    ! [B_6] : r1_tarski('#skF_4',B_6) ),
    inference(resolution,[status(thm)],[c_10,c_222645])).

tff(c_222399,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_222393,c_215122])).

tff(c_226018,plain,(
    ! [D_5879,C_5880,B_5881] :
      ( v1_funct_2(D_5879,'#skF_4',C_5880)
      | ~ r1_tarski(B_5881,C_5880)
      | ~ m1_subset_1(D_5879,k1_zfmisc_1('#skF_4'))
      | ~ v1_funct_2(D_5879,'#skF_4',B_5881)
      | ~ v1_funct_1(D_5879) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_222399,c_222399,c_222399,c_102])).

tff(c_226333,plain,(
    ! [D_5891,B_5892] :
      ( v1_funct_2(D_5891,'#skF_4',B_5892)
      | ~ m1_subset_1(D_5891,k1_zfmisc_1('#skF_4'))
      | ~ v1_funct_2(D_5891,'#skF_4','#skF_4')
      | ~ v1_funct_1(D_5891) ) ),
    inference(resolution,[status(thm)],[c_222654,c_226018])).

tff(c_226335,plain,(
    ! [B_5892] :
      ( v1_funct_2('#skF_4','#skF_4',B_5892)
      | ~ v1_funct_2('#skF_4','#skF_4','#skF_4')
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_222401,c_226333])).

tff(c_226341,plain,(
    ! [B_5892] : v1_funct_2('#skF_4','#skF_4',B_5892) ),
    inference(demodulation,[status(thm),theory(equality)],[c_222412,c_223447,c_226335])).

tff(c_222407,plain,(
    ~ v1_funct_2(k2_funct_1('#skF_4'),'#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_222393,c_27041])).

tff(c_222552,plain,(
    ~ v1_funct_2('#skF_4','#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_222548,c_222407])).

tff(c_226346,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_226341,c_222552])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n018.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 17:37:27 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 40.21/29.49  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 40.38/29.57  
% 40.38/29.57  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 40.38/29.57  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r2_hidden > r1_tarski > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k9_relat_1 > k7_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2
% 40.38/29.57  
% 40.38/29.57  %Foreground sorts:
% 40.38/29.57  
% 40.38/29.57  
% 40.38/29.57  %Background operators:
% 40.38/29.57  
% 40.38/29.57  
% 40.38/29.57  %Foreground operators:
% 40.38/29.57  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 40.38/29.57  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 40.38/29.57  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 40.38/29.57  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 40.38/29.57  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 40.38/29.57  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 40.38/29.57  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 40.38/29.57  tff('#skF_1', type, '#skF_1': $i > $i).
% 40.38/29.57  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 40.38/29.57  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 40.38/29.57  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 40.38/29.57  tff('#skF_5', type, '#skF_5': $i).
% 40.38/29.57  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 40.38/29.57  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 40.38/29.57  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 40.38/29.57  tff('#skF_3', type, '#skF_3': $i).
% 40.38/29.57  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 40.38/29.57  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 40.38/29.57  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 40.38/29.57  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 40.38/29.57  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 40.38/29.57  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 40.38/29.57  tff('#skF_4', type, '#skF_4': $i).
% 40.38/29.57  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 40.38/29.57  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 40.38/29.57  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 40.38/29.57  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 40.38/29.57  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 40.38/29.57  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 40.38/29.57  
% 40.82/29.61  tff(f_49, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 40.82/29.61  tff(f_202, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((v2_funct_1(C) & (k2_relset_1(A, B, C) = B)) => ((v1_funct_1(k2_funct_1(C)) & v1_funct_2(k2_funct_1(C), B, A)) & m1_subset_1(k2_funct_1(C), k1_zfmisc_1(k2_zfmisc_1(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_funct_2)).
% 40.82/29.61  tff(f_128, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 40.82/29.61  tff(f_39, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 40.82/29.61  tff(f_63, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 40.82/29.61  tff(f_122, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 40.82/29.61  tff(f_100, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 40.82/29.61  tff(f_118, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k2_relat_1(A) = k1_relat_1(k2_funct_1(A))) & (k1_relat_1(A) = k2_relat_1(k2_funct_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_funct_1)).
% 40.82/29.61  tff(f_139, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 40.82/29.61  tff(f_166, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => ((v1_funct_1(A) & v1_funct_2(A, k1_relat_1(A), k2_relat_1(A))) & m1_subset_1(A, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_funct_2)).
% 40.82/29.61  tff(f_80, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d18_relat_1)).
% 40.82/29.61  tff(f_185, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r1_tarski(B, C) => (((B = k1_xboole_0) & ~(A = k1_xboole_0)) | ((v1_funct_1(D) & v1_funct_2(D, A, C)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t9_funct_2)).
% 40.82/29.61  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 40.82/29.61  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 40.82/29.61  tff(f_67, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 40.82/29.61  tff(f_74, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_subset)).
% 40.82/29.61  tff(f_135, axiom, (![A, B]: (v1_xboole_0(A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_xboole_0(C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc3_relset_1)).
% 40.82/29.61  tff(f_92, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k7_relat_1(B, A), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t88_relat_1)).
% 40.82/29.61  tff(f_88, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k7_relat_1(B, A)), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t87_relat_1)).
% 40.82/29.61  tff(f_43, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 40.82/29.61  tff(c_20, plain, (![B_12]: (r1_tarski(B_12, B_12))), inference(cnfTransformation, [status(thm)], [f_49])).
% 40.82/29.61  tff(c_96, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_202])).
% 40.82/29.61  tff(c_688, plain, (![C_145, A_146, B_147]: (v4_relat_1(C_145, A_146) | ~m1_subset_1(C_145, k1_zfmisc_1(k2_zfmisc_1(A_146, B_147))))), inference(cnfTransformation, [status(thm)], [f_128])).
% 40.82/29.61  tff(c_703, plain, (v4_relat_1('#skF_5', '#skF_3')), inference(resolution, [status(thm)], [c_96, c_688])).
% 40.82/29.61  tff(c_12, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 40.82/29.61  tff(c_26, plain, (![A_15]: (k2_zfmisc_1(A_15, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_63])).
% 40.82/29.61  tff(c_221, plain, (![C_89, A_90, B_91]: (v1_relat_1(C_89) | ~m1_subset_1(C_89, k1_zfmisc_1(k2_zfmisc_1(A_90, B_91))))), inference(cnfTransformation, [status(thm)], [f_122])).
% 40.82/29.61  tff(c_234, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_96, c_221])).
% 40.82/29.61  tff(c_100, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_202])).
% 40.82/29.61  tff(c_46, plain, (![A_30]: (v1_funct_1(k2_funct_1(A_30)) | ~v1_funct_1(A_30) | ~v1_relat_1(A_30))), inference(cnfTransformation, [status(thm)], [f_100])).
% 40.82/29.61  tff(c_90, plain, (~m1_subset_1(k2_funct_1('#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_3'))) | ~v1_funct_2(k2_funct_1('#skF_5'), '#skF_4', '#skF_3') | ~v1_funct_1(k2_funct_1('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_202])).
% 40.82/29.61  tff(c_160, plain, (~v1_funct_1(k2_funct_1('#skF_5'))), inference(splitLeft, [status(thm)], [c_90])).
% 40.82/29.61  tff(c_163, plain, (~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_46, c_160])).
% 40.82/29.61  tff(c_166, plain, (~v1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_100, c_163])).
% 40.82/29.61  tff(c_196, plain, (![C_84, A_85, B_86]: (v1_relat_1(C_84) | ~m1_subset_1(C_84, k1_zfmisc_1(k2_zfmisc_1(A_85, B_86))))), inference(cnfTransformation, [status(thm)], [f_122])).
% 40.82/29.61  tff(c_203, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_96, c_196])).
% 40.82/29.61  tff(c_212, plain, $false, inference(negUnitSimplification, [status(thm)], [c_166, c_203])).
% 40.82/29.61  tff(c_214, plain, (v1_funct_1(k2_funct_1('#skF_5'))), inference(splitRight, [status(thm)], [c_90])).
% 40.82/29.61  tff(c_94, plain, (v2_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_202])).
% 40.82/29.61  tff(c_52, plain, (![A_33]: (k2_relat_1(k2_funct_1(A_33))=k1_relat_1(A_33) | ~v2_funct_1(A_33) | ~v1_funct_1(A_33) | ~v1_relat_1(A_33))), inference(cnfTransformation, [status(thm)], [f_118])).
% 40.82/29.61  tff(c_48, plain, (![A_30]: (v1_relat_1(k2_funct_1(A_30)) | ~v1_funct_1(A_30) | ~v1_relat_1(A_30))), inference(cnfTransformation, [status(thm)], [f_100])).
% 40.82/29.61  tff(c_92, plain, (k2_relset_1('#skF_3', '#skF_4', '#skF_5')='#skF_4'), inference(cnfTransformation, [status(thm)], [f_202])).
% 40.82/29.61  tff(c_1186, plain, (![A_208, B_209, C_210]: (k2_relset_1(A_208, B_209, C_210)=k2_relat_1(C_210) | ~m1_subset_1(C_210, k1_zfmisc_1(k2_zfmisc_1(A_208, B_209))))), inference(cnfTransformation, [status(thm)], [f_139])).
% 40.82/29.61  tff(c_1196, plain, (k2_relset_1('#skF_3', '#skF_4', '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_96, c_1186])).
% 40.82/29.61  tff(c_1206, plain, (k2_relat_1('#skF_5')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_92, c_1196])).
% 40.82/29.61  tff(c_954, plain, (![A_187]: (k1_relat_1(k2_funct_1(A_187))=k2_relat_1(A_187) | ~v2_funct_1(A_187) | ~v1_funct_1(A_187) | ~v1_relat_1(A_187))), inference(cnfTransformation, [status(thm)], [f_118])).
% 40.82/29.61  tff(c_74, plain, (![A_54]: (v1_funct_2(A_54, k1_relat_1(A_54), k2_relat_1(A_54)) | ~v1_funct_1(A_54) | ~v1_relat_1(A_54))), inference(cnfTransformation, [status(thm)], [f_166])).
% 40.82/29.61  tff(c_19485, plain, (![A_743]: (v1_funct_2(k2_funct_1(A_743), k2_relat_1(A_743), k2_relat_1(k2_funct_1(A_743))) | ~v1_funct_1(k2_funct_1(A_743)) | ~v1_relat_1(k2_funct_1(A_743)) | ~v2_funct_1(A_743) | ~v1_funct_1(A_743) | ~v1_relat_1(A_743))), inference(superposition, [status(thm), theory('equality')], [c_954, c_74])).
% 40.82/29.61  tff(c_19503, plain, (v1_funct_2(k2_funct_1('#skF_5'), '#skF_4', k2_relat_1(k2_funct_1('#skF_5'))) | ~v1_funct_1(k2_funct_1('#skF_5')) | ~v1_relat_1(k2_funct_1('#skF_5')) | ~v2_funct_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_1206, c_19485])).
% 40.82/29.61  tff(c_19524, plain, (v1_funct_2(k2_funct_1('#skF_5'), '#skF_4', k2_relat_1(k2_funct_1('#skF_5'))) | ~v1_relat_1(k2_funct_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_234, c_100, c_94, c_214, c_19503])).
% 40.82/29.61  tff(c_19525, plain, (~v1_relat_1(k2_funct_1('#skF_5'))), inference(splitLeft, [status(thm)], [c_19524])).
% 40.82/29.61  tff(c_19528, plain, (~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_48, c_19525])).
% 40.82/29.61  tff(c_19532, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_234, c_100, c_19528])).
% 40.82/29.61  tff(c_19533, plain, (v1_funct_2(k2_funct_1('#skF_5'), '#skF_4', k2_relat_1(k2_funct_1('#skF_5')))), inference(splitRight, [status(thm)], [c_19524])).
% 40.82/29.61  tff(c_19593, plain, (v1_funct_2(k2_funct_1('#skF_5'), '#skF_4', k1_relat_1('#skF_5')) | ~v2_funct_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_52, c_19533])).
% 40.82/29.61  tff(c_19595, plain, (v1_funct_2(k2_funct_1('#skF_5'), '#skF_4', k1_relat_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_234, c_100, c_94, c_19593])).
% 40.82/29.61  tff(c_19534, plain, (v1_relat_1(k2_funct_1('#skF_5'))), inference(splitRight, [status(thm)], [c_19524])).
% 40.82/29.61  tff(c_54, plain, (![A_33]: (k1_relat_1(k2_funct_1(A_33))=k2_relat_1(A_33) | ~v2_funct_1(A_33) | ~v1_funct_1(A_33) | ~v1_relat_1(A_33))), inference(cnfTransformation, [status(thm)], [f_118])).
% 40.82/29.61  tff(c_1100, plain, (![A_202]: (m1_subset_1(A_202, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_202), k2_relat_1(A_202)))) | ~v1_funct_1(A_202) | ~v1_relat_1(A_202))), inference(cnfTransformation, [status(thm)], [f_166])).
% 40.82/29.61  tff(c_21363, plain, (![A_793]: (m1_subset_1(k2_funct_1(A_793), k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(A_793), k2_relat_1(k2_funct_1(A_793))))) | ~v1_funct_1(k2_funct_1(A_793)) | ~v1_relat_1(k2_funct_1(A_793)) | ~v2_funct_1(A_793) | ~v1_funct_1(A_793) | ~v1_relat_1(A_793))), inference(superposition, [status(thm), theory('equality')], [c_54, c_1100])).
% 40.82/29.61  tff(c_21407, plain, (m1_subset_1(k2_funct_1('#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', k2_relat_1(k2_funct_1('#skF_5'))))) | ~v1_funct_1(k2_funct_1('#skF_5')) | ~v1_relat_1(k2_funct_1('#skF_5')) | ~v2_funct_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_1206, c_21363])).
% 40.82/29.61  tff(c_21437, plain, (m1_subset_1(k2_funct_1('#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', k2_relat_1(k2_funct_1('#skF_5')))))), inference(demodulation, [status(thm), theory('equality')], [c_234, c_100, c_94, c_19534, c_214, c_21407])).
% 40.82/29.61  tff(c_21466, plain, (m1_subset_1(k2_funct_1('#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', k1_relat_1('#skF_5')))) | ~v2_funct_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_52, c_21437])).
% 40.82/29.61  tff(c_21482, plain, (m1_subset_1(k2_funct_1('#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', k1_relat_1('#skF_5'))))), inference(demodulation, [status(thm), theory('equality')], [c_234, c_100, c_94, c_21466])).
% 40.82/29.61  tff(c_38, plain, (![B_23, A_22]: (r1_tarski(k1_relat_1(B_23), A_22) | ~v4_relat_1(B_23, A_22) | ~v1_relat_1(B_23))), inference(cnfTransformation, [status(thm)], [f_80])).
% 40.82/29.61  tff(c_1761, plain, (![B_244, D_245, A_246, C_247]: (k1_xboole_0=B_244 | v1_funct_2(D_245, A_246, C_247) | ~r1_tarski(B_244, C_247) | ~m1_subset_1(D_245, k1_zfmisc_1(k2_zfmisc_1(A_246, B_244))) | ~v1_funct_2(D_245, A_246, B_244) | ~v1_funct_1(D_245))), inference(cnfTransformation, [status(thm)], [f_185])).
% 40.82/29.61  tff(c_25846, plain, (![B_876, D_877, A_878, A_879]: (k1_relat_1(B_876)=k1_xboole_0 | v1_funct_2(D_877, A_878, A_879) | ~m1_subset_1(D_877, k1_zfmisc_1(k2_zfmisc_1(A_878, k1_relat_1(B_876)))) | ~v1_funct_2(D_877, A_878, k1_relat_1(B_876)) | ~v1_funct_1(D_877) | ~v4_relat_1(B_876, A_879) | ~v1_relat_1(B_876))), inference(resolution, [status(thm)], [c_38, c_1761])).
% 40.82/29.61  tff(c_25855, plain, (![A_879]: (k1_relat_1('#skF_5')=k1_xboole_0 | v1_funct_2(k2_funct_1('#skF_5'), '#skF_4', A_879) | ~v1_funct_2(k2_funct_1('#skF_5'), '#skF_4', k1_relat_1('#skF_5')) | ~v1_funct_1(k2_funct_1('#skF_5')) | ~v4_relat_1('#skF_5', A_879) | ~v1_relat_1('#skF_5'))), inference(resolution, [status(thm)], [c_21482, c_25846])).
% 40.82/29.61  tff(c_25941, plain, (![A_879]: (k1_relat_1('#skF_5')=k1_xboole_0 | v1_funct_2(k2_funct_1('#skF_5'), '#skF_4', A_879) | ~v4_relat_1('#skF_5', A_879))), inference(demodulation, [status(thm), theory('equality')], [c_234, c_214, c_19595, c_25855])).
% 40.82/29.61  tff(c_25971, plain, (k1_relat_1('#skF_5')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_25941])).
% 40.82/29.61  tff(c_310, plain, (![A_103, B_104]: (r2_hidden('#skF_2'(A_103, B_104), A_103) | r1_tarski(A_103, B_104))), inference(cnfTransformation, [status(thm)], [f_38])).
% 40.82/29.61  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 40.82/29.61  tff(c_315, plain, (![A_105, B_106]: (~v1_xboole_0(A_105) | r1_tarski(A_105, B_106))), inference(resolution, [status(thm)], [c_310, c_2])).
% 40.82/29.61  tff(c_32, plain, (![A_17, B_18]: (m1_subset_1(A_17, k1_zfmisc_1(B_18)) | ~r1_tarski(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_67])).
% 40.82/29.61  tff(c_213, plain, (~v1_funct_2(k2_funct_1('#skF_5'), '#skF_4', '#skF_3') | ~m1_subset_1(k2_funct_1('#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_3')))), inference(splitRight, [status(thm)], [c_90])).
% 40.82/29.61  tff(c_216, plain, (~m1_subset_1(k2_funct_1('#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_3')))), inference(splitLeft, [status(thm)], [c_213])).
% 40.82/29.61  tff(c_220, plain, (~r1_tarski(k2_funct_1('#skF_5'), k2_zfmisc_1('#skF_4', '#skF_3'))), inference(resolution, [status(thm)], [c_32, c_216])).
% 40.82/29.61  tff(c_336, plain, (~v1_xboole_0(k2_funct_1('#skF_5'))), inference(resolution, [status(thm)], [c_315, c_220])).
% 40.82/29.61  tff(c_30, plain, (![A_17, B_18]: (r1_tarski(A_17, B_18) | ~m1_subset_1(A_17, k1_zfmisc_1(B_18)))), inference(cnfTransformation, [status(thm)], [f_67])).
% 40.82/29.61  tff(c_21643, plain, (r1_tarski(k2_funct_1('#skF_5'), k2_zfmisc_1('#skF_4', k1_relat_1('#skF_5')))), inference(resolution, [status(thm)], [c_21482, c_30])).
% 40.82/29.61  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 40.82/29.61  tff(c_721, plain, (![C_154, B_155, A_156]: (~v1_xboole_0(C_154) | ~m1_subset_1(B_155, k1_zfmisc_1(C_154)) | ~r2_hidden(A_156, B_155))), inference(cnfTransformation, [status(thm)], [f_74])).
% 40.82/29.61  tff(c_917, plain, (![B_182, A_183, A_184]: (~v1_xboole_0(B_182) | ~r2_hidden(A_183, A_184) | ~r1_tarski(A_184, B_182))), inference(resolution, [status(thm)], [c_32, c_721])).
% 40.82/29.61  tff(c_923, plain, (![B_182, A_1]: (~v1_xboole_0(B_182) | ~r1_tarski(A_1, B_182) | v1_xboole_0(A_1))), inference(resolution, [status(thm)], [c_4, c_917])).
% 40.82/29.61  tff(c_21670, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_4', k1_relat_1('#skF_5'))) | v1_xboole_0(k2_funct_1('#skF_5'))), inference(resolution, [status(thm)], [c_21643, c_923])).
% 40.82/29.61  tff(c_21700, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_4', k1_relat_1('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_336, c_21670])).
% 40.82/29.61  tff(c_25974, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_4', k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_25971, c_21700])).
% 40.82/29.61  tff(c_25991, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12, c_26, c_25974])).
% 40.82/29.61  tff(c_25993, plain, (k1_relat_1('#skF_5')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_25941])).
% 40.82/29.61  tff(c_2042, plain, (![B_261, D_262, A_263, C_264]: (k1_xboole_0=B_261 | m1_subset_1(D_262, k1_zfmisc_1(k2_zfmisc_1(A_263, C_264))) | ~r1_tarski(B_261, C_264) | ~m1_subset_1(D_262, k1_zfmisc_1(k2_zfmisc_1(A_263, B_261))) | ~v1_funct_2(D_262, A_263, B_261) | ~v1_funct_1(D_262))), inference(cnfTransformation, [status(thm)], [f_185])).
% 40.82/29.61  tff(c_26812, plain, (![B_907, D_908, A_909, A_910]: (k1_relat_1(B_907)=k1_xboole_0 | m1_subset_1(D_908, k1_zfmisc_1(k2_zfmisc_1(A_909, A_910))) | ~m1_subset_1(D_908, k1_zfmisc_1(k2_zfmisc_1(A_909, k1_relat_1(B_907)))) | ~v1_funct_2(D_908, A_909, k1_relat_1(B_907)) | ~v1_funct_1(D_908) | ~v4_relat_1(B_907, A_910) | ~v1_relat_1(B_907))), inference(resolution, [status(thm)], [c_38, c_2042])).
% 40.82/29.61  tff(c_26821, plain, (![A_910]: (k1_relat_1('#skF_5')=k1_xboole_0 | m1_subset_1(k2_funct_1('#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', A_910))) | ~v1_funct_2(k2_funct_1('#skF_5'), '#skF_4', k1_relat_1('#skF_5')) | ~v1_funct_1(k2_funct_1('#skF_5')) | ~v4_relat_1('#skF_5', A_910) | ~v1_relat_1('#skF_5'))), inference(resolution, [status(thm)], [c_21482, c_26812])).
% 40.82/29.61  tff(c_26907, plain, (![A_910]: (k1_relat_1('#skF_5')=k1_xboole_0 | m1_subset_1(k2_funct_1('#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', A_910))) | ~v4_relat_1('#skF_5', A_910))), inference(demodulation, [status(thm), theory('equality')], [c_234, c_214, c_19595, c_26821])).
% 40.82/29.61  tff(c_26943, plain, (![A_911]: (m1_subset_1(k2_funct_1('#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', A_911))) | ~v4_relat_1('#skF_5', A_911))), inference(negUnitSimplification, [status(thm)], [c_25993, c_26907])).
% 40.82/29.61  tff(c_26995, plain, (~v4_relat_1('#skF_5', '#skF_3')), inference(resolution, [status(thm)], [c_26943, c_216])).
% 40.82/29.61  tff(c_27040, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_703, c_26995])).
% 40.82/29.61  tff(c_27042, plain, (m1_subset_1(k2_funct_1('#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_3')))), inference(splitRight, [status(thm)], [c_213])).
% 40.82/29.61  tff(c_27629, plain, (![C_987, A_988, B_989]: (v1_xboole_0(C_987) | ~m1_subset_1(C_987, k1_zfmisc_1(k2_zfmisc_1(A_988, B_989))) | ~v1_xboole_0(A_988))), inference(cnfTransformation, [status(thm)], [f_135])).
% 40.82/29.61  tff(c_27646, plain, (v1_xboole_0(k2_funct_1('#skF_5')) | ~v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_27042, c_27629])).
% 40.82/29.61  tff(c_27652, plain, (~v1_xboole_0('#skF_4')), inference(splitLeft, [status(thm)], [c_27646])).
% 40.82/29.61  tff(c_27101, plain, (![C_920, A_921, B_922]: (v1_relat_1(C_920) | ~m1_subset_1(C_920, k1_zfmisc_1(k2_zfmisc_1(A_921, B_922))))), inference(cnfTransformation, [status(thm)], [f_122])).
% 40.82/29.61  tff(c_27118, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_96, c_27101])).
% 40.82/29.61  tff(c_28, plain, (![B_16]: (k2_zfmisc_1(k1_xboole_0, B_16)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_63])).
% 40.82/29.61  tff(c_27119, plain, (![C_923]: (v1_relat_1(C_923) | ~m1_subset_1(C_923, k1_zfmisc_1(k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_28, c_27101])).
% 40.82/29.61  tff(c_27126, plain, (![A_924]: (v1_relat_1(A_924) | ~r1_tarski(A_924, k1_xboole_0))), inference(resolution, [status(thm)], [c_32, c_27119])).
% 40.82/29.61  tff(c_27146, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_20, c_27126])).
% 40.82/29.61  tff(c_44, plain, (![B_29, A_28]: (r1_tarski(k7_relat_1(B_29, A_28), B_29) | ~v1_relat_1(B_29))), inference(cnfTransformation, [status(thm)], [f_92])).
% 40.82/29.61  tff(c_27066, plain, (![A_914, B_915]: (r2_hidden('#skF_2'(A_914, B_915), A_914) | r1_tarski(A_914, B_915))), inference(cnfTransformation, [status(thm)], [f_38])).
% 40.82/29.61  tff(c_27071, plain, (![A_916, B_917]: (~v1_xboole_0(A_916) | r1_tarski(A_916, B_917))), inference(resolution, [status(thm)], [c_27066, c_2])).
% 40.82/29.61  tff(c_16, plain, (![B_12, A_11]: (B_12=A_11 | ~r1_tarski(B_12, A_11) | ~r1_tarski(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_49])).
% 40.82/29.61  tff(c_27075, plain, (![B_918, A_919]: (B_918=A_919 | ~r1_tarski(B_918, A_919) | ~v1_xboole_0(A_919))), inference(resolution, [status(thm)], [c_27071, c_16])).
% 40.82/29.61  tff(c_27222, plain, (![B_937, A_938]: (k7_relat_1(B_937, A_938)=B_937 | ~v1_xboole_0(B_937) | ~v1_relat_1(B_937))), inference(resolution, [status(thm)], [c_44, c_27075])).
% 40.82/29.61  tff(c_27224, plain, (![A_938]: (k7_relat_1(k1_xboole_0, A_938)=k1_xboole_0 | ~v1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_12, c_27222])).
% 40.82/29.61  tff(c_27230, plain, (![A_939]: (k7_relat_1(k1_xboole_0, A_939)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_27146, c_27224])).
% 40.82/29.61  tff(c_42, plain, (![B_27, A_26]: (r1_tarski(k1_relat_1(k7_relat_1(B_27, A_26)), A_26) | ~v1_relat_1(B_27))), inference(cnfTransformation, [status(thm)], [f_88])).
% 40.82/29.61  tff(c_27239, plain, (![A_939]: (r1_tarski(k1_relat_1(k1_xboole_0), A_939) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_27230, c_42])).
% 40.82/29.61  tff(c_27260, plain, (![A_943]: (r1_tarski(k1_relat_1(k1_xboole_0), A_943))), inference(demodulation, [status(thm), theory('equality')], [c_27146, c_27239])).
% 40.82/29.61  tff(c_27074, plain, (![B_917, A_916]: (B_917=A_916 | ~r1_tarski(B_917, A_916) | ~v1_xboole_0(A_916))), inference(resolution, [status(thm)], [c_27071, c_16])).
% 40.82/29.61  tff(c_27280, plain, (![A_944]: (k1_relat_1(k1_xboole_0)=A_944 | ~v1_xboole_0(A_944))), inference(resolution, [status(thm)], [c_27260, c_27074])).
% 40.82/29.61  tff(c_27284, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_12, c_27280])).
% 40.82/29.61  tff(c_52218, plain, (![A_1702, B_1703, C_1704]: (k2_relset_1(A_1702, B_1703, C_1704)=k2_relat_1(C_1704) | ~m1_subset_1(C_1704, k1_zfmisc_1(k2_zfmisc_1(A_1702, B_1703))))), inference(cnfTransformation, [status(thm)], [f_139])).
% 40.82/29.61  tff(c_52228, plain, (k2_relset_1('#skF_3', '#skF_4', '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_96, c_52218])).
% 40.82/29.61  tff(c_52238, plain, (k2_relat_1('#skF_5')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_92, c_52228])).
% 40.82/29.61  tff(c_27046, plain, (r1_tarski(k2_funct_1('#skF_5'), k2_zfmisc_1('#skF_4', '#skF_3'))), inference(resolution, [status(thm)], [c_27042, c_30])).
% 40.82/29.61  tff(c_52961, plain, (![B_1748, D_1749, A_1750, C_1751]: (k1_xboole_0=B_1748 | v1_funct_2(D_1749, A_1750, C_1751) | ~r1_tarski(B_1748, C_1751) | ~m1_subset_1(D_1749, k1_zfmisc_1(k2_zfmisc_1(A_1750, B_1748))) | ~v1_funct_2(D_1749, A_1750, B_1748) | ~v1_funct_1(D_1749))), inference(cnfTransformation, [status(thm)], [f_185])).
% 40.82/29.61  tff(c_52986, plain, (![D_1749, A_1750]: (k2_funct_1('#skF_5')=k1_xboole_0 | v1_funct_2(D_1749, A_1750, k2_zfmisc_1('#skF_4', '#skF_3')) | ~m1_subset_1(D_1749, k1_zfmisc_1(k2_zfmisc_1(A_1750, k2_funct_1('#skF_5')))) | ~v1_funct_2(D_1749, A_1750, k2_funct_1('#skF_5')) | ~v1_funct_1(D_1749))), inference(resolution, [status(thm)], [c_27046, c_52961])).
% 40.82/29.61  tff(c_60234, plain, (k2_funct_1('#skF_5')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_52986])).
% 40.82/29.61  tff(c_60258, plain, (k2_relat_1('#skF_5')=k1_relat_1(k1_xboole_0) | ~v2_funct_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_60234, c_54])).
% 40.82/29.61  tff(c_60270, plain, (k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_27118, c_100, c_94, c_27284, c_52238, c_60258])).
% 40.82/29.61  tff(c_60366, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_60270, c_12])).
% 40.82/29.61  tff(c_60368, plain, $false, inference(negUnitSimplification, [status(thm)], [c_27652, c_60366])).
% 40.82/29.61  tff(c_60370, plain, (k2_funct_1('#skF_5')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_52986])).
% 40.82/29.61  tff(c_27575, plain, (![C_974, A_975, B_976]: (v4_relat_1(C_974, A_975) | ~m1_subset_1(C_974, k1_zfmisc_1(k2_zfmisc_1(A_975, B_976))))), inference(cnfTransformation, [status(thm)], [f_128])).
% 40.82/29.62  tff(c_27594, plain, (v4_relat_1('#skF_5', '#skF_3')), inference(resolution, [status(thm)], [c_96, c_27575])).
% 40.82/29.62  tff(c_27116, plain, (v1_relat_1(k2_funct_1('#skF_5'))), inference(resolution, [status(thm)], [c_27042, c_27101])).
% 40.82/29.62  tff(c_52023, plain, (![A_1677]: (k1_relat_1(k2_funct_1(A_1677))=k2_relat_1(A_1677) | ~v2_funct_1(A_1677) | ~v1_funct_1(A_1677) | ~v1_relat_1(A_1677))), inference(cnfTransformation, [status(thm)], [f_118])).
% 40.82/29.62  tff(c_70193, plain, (![A_2256]: (v1_funct_2(k2_funct_1(A_2256), k2_relat_1(A_2256), k2_relat_1(k2_funct_1(A_2256))) | ~v1_funct_1(k2_funct_1(A_2256)) | ~v1_relat_1(k2_funct_1(A_2256)) | ~v2_funct_1(A_2256) | ~v1_funct_1(A_2256) | ~v1_relat_1(A_2256))), inference(superposition, [status(thm), theory('equality')], [c_52023, c_74])).
% 40.82/29.62  tff(c_70214, plain, (v1_funct_2(k2_funct_1('#skF_5'), '#skF_4', k2_relat_1(k2_funct_1('#skF_5'))) | ~v1_funct_1(k2_funct_1('#skF_5')) | ~v1_relat_1(k2_funct_1('#skF_5')) | ~v2_funct_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_52238, c_70193])).
% 40.82/29.62  tff(c_70237, plain, (v1_funct_2(k2_funct_1('#skF_5'), '#skF_4', k2_relat_1(k2_funct_1('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_27118, c_100, c_94, c_27116, c_214, c_70214])).
% 40.82/29.62  tff(c_70240, plain, (v1_funct_2(k2_funct_1('#skF_5'), '#skF_4', k1_relat_1('#skF_5')) | ~v2_funct_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_52, c_70237])).
% 40.82/29.62  tff(c_70242, plain, (v1_funct_2(k2_funct_1('#skF_5'), '#skF_4', k1_relat_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_27118, c_100, c_94, c_70240])).
% 40.82/29.62  tff(c_52310, plain, (![A_1708]: (m1_subset_1(A_1708, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_1708), k2_relat_1(A_1708)))) | ~v1_funct_1(A_1708) | ~v1_relat_1(A_1708))), inference(cnfTransformation, [status(thm)], [f_166])).
% 40.82/29.62  tff(c_71744, plain, (![A_2277]: (m1_subset_1(k2_funct_1(A_2277), k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(A_2277), k2_relat_1(k2_funct_1(A_2277))))) | ~v1_funct_1(k2_funct_1(A_2277)) | ~v1_relat_1(k2_funct_1(A_2277)) | ~v2_funct_1(A_2277) | ~v1_funct_1(A_2277) | ~v1_relat_1(A_2277))), inference(superposition, [status(thm), theory('equality')], [c_54, c_52310])).
% 40.82/29.62  tff(c_71791, plain, (m1_subset_1(k2_funct_1('#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', k2_relat_1(k2_funct_1('#skF_5'))))) | ~v1_funct_1(k2_funct_1('#skF_5')) | ~v1_relat_1(k2_funct_1('#skF_5')) | ~v2_funct_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_52238, c_71744])).
% 40.82/29.62  tff(c_71823, plain, (m1_subset_1(k2_funct_1('#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', k2_relat_1(k2_funct_1('#skF_5')))))), inference(demodulation, [status(thm), theory('equality')], [c_27118, c_100, c_94, c_27116, c_214, c_71791])).
% 40.82/29.62  tff(c_71852, plain, (m1_subset_1(k2_funct_1('#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', k1_relat_1('#skF_5')))) | ~v2_funct_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_52, c_71823])).
% 40.82/29.62  tff(c_71868, plain, (m1_subset_1(k2_funct_1('#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', k1_relat_1('#skF_5'))))), inference(demodulation, [status(thm), theory('equality')], [c_27118, c_100, c_94, c_71852])).
% 40.82/29.62  tff(c_73756, plain, (![B_2319, D_2320, A_2321, A_2322]: (k1_relat_1(B_2319)=k1_xboole_0 | v1_funct_2(D_2320, A_2321, A_2322) | ~m1_subset_1(D_2320, k1_zfmisc_1(k2_zfmisc_1(A_2321, k1_relat_1(B_2319)))) | ~v1_funct_2(D_2320, A_2321, k1_relat_1(B_2319)) | ~v1_funct_1(D_2320) | ~v4_relat_1(B_2319, A_2322) | ~v1_relat_1(B_2319))), inference(resolution, [status(thm)], [c_38, c_52961])).
% 40.82/29.62  tff(c_73760, plain, (![A_2322]: (k1_relat_1('#skF_5')=k1_xboole_0 | v1_funct_2(k2_funct_1('#skF_5'), '#skF_4', A_2322) | ~v1_funct_2(k2_funct_1('#skF_5'), '#skF_4', k1_relat_1('#skF_5')) | ~v1_funct_1(k2_funct_1('#skF_5')) | ~v4_relat_1('#skF_5', A_2322) | ~v1_relat_1('#skF_5'))), inference(resolution, [status(thm)], [c_71868, c_73756])).
% 40.82/29.62  tff(c_73842, plain, (![A_2322]: (k1_relat_1('#skF_5')=k1_xboole_0 | v1_funct_2(k2_funct_1('#skF_5'), '#skF_4', A_2322) | ~v4_relat_1('#skF_5', A_2322))), inference(demodulation, [status(thm), theory('equality')], [c_27118, c_214, c_70242, c_73760])).
% 40.82/29.62  tff(c_74606, plain, (k1_relat_1('#skF_5')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_73842])).
% 40.82/29.62  tff(c_71866, plain, (r1_tarski(k2_funct_1('#skF_5'), k2_zfmisc_1('#skF_4', k2_relat_1(k2_funct_1('#skF_5'))))), inference(resolution, [status(thm)], [c_71823, c_30])).
% 40.82/29.62  tff(c_71973, plain, (r1_tarski(k2_funct_1('#skF_5'), k2_zfmisc_1('#skF_4', k1_relat_1('#skF_5'))) | ~v2_funct_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_52, c_71866])).
% 40.82/29.62  tff(c_72001, plain, (r1_tarski(k2_funct_1('#skF_5'), k2_zfmisc_1('#skF_4', k1_relat_1('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_27118, c_100, c_94, c_71973])).
% 40.82/29.62  tff(c_27503, plain, (![C_962, B_963, A_964]: (~v1_xboole_0(C_962) | ~m1_subset_1(B_963, k1_zfmisc_1(C_962)) | ~r2_hidden(A_964, B_963))), inference(cnfTransformation, [status(thm)], [f_74])).
% 40.82/29.62  tff(c_52108, plain, (![B_1687, A_1688, A_1689]: (~v1_xboole_0(B_1687) | ~r2_hidden(A_1688, A_1689) | ~r1_tarski(A_1689, B_1687))), inference(resolution, [status(thm)], [c_32, c_27503])).
% 40.82/29.62  tff(c_52114, plain, (![B_1687, A_1]: (~v1_xboole_0(B_1687) | ~r1_tarski(A_1, B_1687) | v1_xboole_0(A_1))), inference(resolution, [status(thm)], [c_4, c_52108])).
% 40.82/29.62  tff(c_72060, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_4', k1_relat_1('#skF_5'))) | v1_xboole_0(k2_funct_1('#skF_5'))), inference(resolution, [status(thm)], [c_72001, c_52114])).
% 40.82/29.62  tff(c_72111, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_4', k1_relat_1('#skF_5')))), inference(splitLeft, [status(thm)], [c_72060])).
% 40.82/29.62  tff(c_74608, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_4', k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_74606, c_72111])).
% 40.82/29.62  tff(c_74624, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12, c_26, c_74608])).
% 40.82/29.62  tff(c_74692, plain, (![A_2339]: (v1_funct_2(k2_funct_1('#skF_5'), '#skF_4', A_2339) | ~v4_relat_1('#skF_5', A_2339))), inference(splitRight, [status(thm)], [c_73842])).
% 40.82/29.62  tff(c_27041, plain, (~v1_funct_2(k2_funct_1('#skF_5'), '#skF_4', '#skF_3')), inference(splitRight, [status(thm)], [c_213])).
% 40.82/29.62  tff(c_74695, plain, (~v4_relat_1('#skF_5', '#skF_3')), inference(resolution, [status(thm)], [c_74692, c_27041])).
% 40.82/29.62  tff(c_74699, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_27594, c_74695])).
% 40.82/29.62  tff(c_74700, plain, (v1_xboole_0(k2_funct_1('#skF_5'))), inference(splitRight, [status(thm)], [c_72060])).
% 40.82/29.62  tff(c_14, plain, (![A_10]: (k1_xboole_0=A_10 | ~v1_xboole_0(A_10))), inference(cnfTransformation, [status(thm)], [f_43])).
% 40.82/29.62  tff(c_74748, plain, (k2_funct_1('#skF_5')=k1_xboole_0), inference(resolution, [status(thm)], [c_74700, c_14])).
% 40.82/29.62  tff(c_74778, plain, $false, inference(negUnitSimplification, [status(thm)], [c_60370, c_74748])).
% 40.82/29.62  tff(c_74780, plain, (v1_xboole_0('#skF_4')), inference(splitRight, [status(thm)], [c_27646])).
% 40.82/29.62  tff(c_74794, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_74780, c_14])).
% 40.82/29.62  tff(c_74832, plain, (![B_16]: (k2_zfmisc_1('#skF_4', B_16)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_74794, c_74794, c_28])).
% 40.82/29.62  tff(c_27095, plain, (k2_zfmisc_1('#skF_4', '#skF_3')=k2_funct_1('#skF_5') | ~v1_xboole_0(k2_zfmisc_1('#skF_4', '#skF_3'))), inference(resolution, [status(thm)], [c_27046, c_27075])).
% 40.82/29.62  tff(c_27285, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_4', '#skF_3'))), inference(splitLeft, [status(thm)], [c_27095])).
% 40.82/29.62  tff(c_74952, plain, (~v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_74832, c_27285])).
% 40.82/29.62  tff(c_74955, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_74780, c_74952])).
% 40.82/29.62  tff(c_74957, plain, (v1_xboole_0(k2_zfmisc_1('#skF_4', '#skF_3'))), inference(splitRight, [status(thm)], [c_27095])).
% 40.82/29.62  tff(c_75003, plain, (k2_zfmisc_1('#skF_4', '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_74957, c_14])).
% 40.82/29.62  tff(c_24, plain, (![B_16, A_15]: (k1_xboole_0=B_16 | k1_xboole_0=A_15 | k2_zfmisc_1(A_15, B_16)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_63])).
% 40.82/29.62  tff(c_75021, plain, (k1_xboole_0='#skF_3' | k1_xboole_0='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_75003, c_24])).
% 40.82/29.62  tff(c_75082, plain, (k1_xboole_0='#skF_4'), inference(splitLeft, [status(thm)], [c_75021])).
% 40.82/29.62  tff(c_27249, plain, (![A_939]: (r1_tarski(k1_relat_1(k1_xboole_0), A_939))), inference(demodulation, [status(thm), theory('equality')], [c_27146, c_27239])).
% 40.82/29.62  tff(c_74959, plain, (![A_939]: (r1_tarski(k1_xboole_0, A_939))), inference(demodulation, [status(thm), theory('equality')], [c_27284, c_27249])).
% 40.82/29.62  tff(c_75088, plain, (![A_939]: (r1_tarski('#skF_4', A_939))), inference(demodulation, [status(thm), theory('equality')], [c_75082, c_74959])).
% 40.82/29.62  tff(c_75098, plain, (![A_15]: (k2_zfmisc_1(A_15, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_75082, c_75082, c_26])).
% 40.82/29.62  tff(c_150, plain, (![A_72, B_73]: (r1_tarski(A_72, B_73) | ~m1_subset_1(A_72, k1_zfmisc_1(B_73)))), inference(cnfTransformation, [status(thm)], [f_67])).
% 40.82/29.62  tff(c_158, plain, (r1_tarski('#skF_5', k2_zfmisc_1('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_96, c_150])).
% 40.82/29.62  tff(c_27047, plain, (![B_912, A_913]: (B_912=A_913 | ~r1_tarski(B_912, A_913) | ~r1_tarski(A_913, B_912))), inference(cnfTransformation, [status(thm)], [f_49])).
% 40.82/29.62  tff(c_27061, plain, (k2_zfmisc_1('#skF_3', '#skF_4')='#skF_5' | ~r1_tarski(k2_zfmisc_1('#skF_3', '#skF_4'), '#skF_5')), inference(resolution, [status(thm)], [c_158, c_27047])).
% 40.82/29.62  tff(c_27209, plain, (~r1_tarski(k2_zfmisc_1('#skF_3', '#skF_4'), '#skF_5')), inference(splitLeft, [status(thm)], [c_27061])).
% 40.82/29.62  tff(c_75253, plain, (~r1_tarski('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_75098, c_27209])).
% 40.82/29.62  tff(c_75259, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_75088, c_75253])).
% 40.82/29.62  tff(c_75260, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_75021])).
% 40.82/29.62  tff(c_75267, plain, (![A_939]: (r1_tarski('#skF_3', A_939))), inference(demodulation, [status(thm), theory('equality')], [c_75260, c_74959])).
% 40.82/29.62  tff(c_75276, plain, (![B_16]: (k2_zfmisc_1('#skF_3', B_16)='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_75260, c_75260, c_28])).
% 40.82/29.62  tff(c_75431, plain, (~r1_tarski('#skF_3', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_75276, c_27209])).
% 40.82/29.62  tff(c_75437, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_75267, c_75431])).
% 40.82/29.62  tff(c_75438, plain, (k2_zfmisc_1('#skF_3', '#skF_4')='#skF_5'), inference(splitRight, [status(thm)], [c_27061])).
% 40.82/29.62  tff(c_27098, plain, (k2_zfmisc_1('#skF_3', '#skF_4')='#skF_5' | ~v1_xboole_0(k2_zfmisc_1('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_158, c_27075])).
% 40.82/29.62  tff(c_27125, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_3', '#skF_4'))), inference(splitLeft, [status(thm)], [c_27098])).
% 40.82/29.62  tff(c_75440, plain, (~v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_75438, c_27125])).
% 40.82/29.62  tff(c_133683, plain, (![C_3620, A_3621, B_3622]: (v1_xboole_0(C_3620) | ~m1_subset_1(C_3620, k1_zfmisc_1(k2_zfmisc_1(A_3621, B_3622))) | ~v1_xboole_0(A_3621))), inference(cnfTransformation, [status(thm)], [f_135])).
% 40.82/29.62  tff(c_133700, plain, (v1_xboole_0(k2_funct_1('#skF_5')) | ~v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_27042, c_133683])).
% 40.82/29.62  tff(c_133704, plain, (~v1_xboole_0('#skF_4')), inference(splitLeft, [status(thm)], [c_133700])).
% 40.82/29.62  tff(c_75442, plain, (m1_subset_1('#skF_5', k1_zfmisc_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_75438, c_96])).
% 40.82/29.62  tff(c_134075, plain, (![A_3655, B_3656, C_3657]: (k2_relset_1(A_3655, B_3656, C_3657)=k2_relat_1(C_3657) | ~m1_subset_1(C_3657, k1_zfmisc_1(k2_zfmisc_1(A_3655, B_3656))))), inference(cnfTransformation, [status(thm)], [f_139])).
% 40.82/29.62  tff(c_134193, plain, (![C_3663]: (k2_relset_1('#skF_3', '#skF_4', C_3663)=k2_relat_1(C_3663) | ~m1_subset_1(C_3663, k1_zfmisc_1('#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_75438, c_134075])).
% 40.82/29.62  tff(c_134196, plain, (k2_relset_1('#skF_3', '#skF_4', '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_75442, c_134193])).
% 40.82/29.62  tff(c_134202, plain, (k2_relat_1('#skF_5')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_92, c_134196])).
% 40.82/29.62  tff(c_75565, plain, (![B_2393, A_2394]: (k7_relat_1(B_2393, A_2394)=B_2393 | ~v1_xboole_0(B_2393) | ~v1_relat_1(B_2393))), inference(resolution, [status(thm)], [c_44, c_27075])).
% 40.82/29.62  tff(c_75567, plain, (![A_2394]: (k7_relat_1(k1_xboole_0, A_2394)=k1_xboole_0 | ~v1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_12, c_75565])).
% 40.82/29.62  tff(c_75573, plain, (![A_2395]: (k7_relat_1(k1_xboole_0, A_2395)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_27146, c_75567])).
% 40.82/29.62  tff(c_75586, plain, (![A_2395]: (r1_tarski(k1_relat_1(k1_xboole_0), A_2395) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_75573, c_42])).
% 40.82/29.62  tff(c_75622, plain, (![A_2399]: (r1_tarski(k1_relat_1(k1_xboole_0), A_2399))), inference(demodulation, [status(thm), theory('equality')], [c_27146, c_75586])).
% 40.82/29.62  tff(c_75510, plain, (![C_2382, B_2383, A_2384]: (~v1_xboole_0(C_2382) | ~m1_subset_1(B_2383, k1_zfmisc_1(C_2382)) | ~r2_hidden(A_2384, B_2383))), inference(cnfTransformation, [status(thm)], [f_74])).
% 40.82/29.62  tff(c_75521, plain, (![B_2385, A_2386, A_2387]: (~v1_xboole_0(B_2385) | ~r2_hidden(A_2386, A_2387) | ~r1_tarski(A_2387, B_2385))), inference(resolution, [status(thm)], [c_32, c_75510])).
% 40.82/29.62  tff(c_75527, plain, (![B_2385, A_1]: (~v1_xboole_0(B_2385) | ~r1_tarski(A_1, B_2385) | v1_xboole_0(A_1))), inference(resolution, [status(thm)], [c_4, c_75521])).
% 40.82/29.62  tff(c_75647, plain, (![A_2399]: (~v1_xboole_0(A_2399) | v1_xboole_0(k1_relat_1(k1_xboole_0)))), inference(resolution, [status(thm)], [c_75622, c_75527])).
% 40.82/29.62  tff(c_75666, plain, (![A_2399]: (~v1_xboole_0(A_2399))), inference(splitLeft, [status(thm)], [c_75647])).
% 40.82/29.62  tff(c_75670, plain, $false, inference(negUnitSimplification, [status(thm)], [c_75666, c_12])).
% 40.82/29.62  tff(c_75671, plain, (v1_xboole_0(k1_relat_1(k1_xboole_0))), inference(splitRight, [status(thm)], [c_75647])).
% 40.82/29.62  tff(c_75688, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_75671, c_14])).
% 40.82/29.62  tff(c_135265, plain, (![B_3716, D_3717, A_3718, C_3719]: (k1_xboole_0=B_3716 | v1_funct_2(D_3717, A_3718, C_3719) | ~r1_tarski(B_3716, C_3719) | ~m1_subset_1(D_3717, k1_zfmisc_1(k2_zfmisc_1(A_3718, B_3716))) | ~v1_funct_2(D_3717, A_3718, B_3716) | ~v1_funct_1(D_3717))), inference(cnfTransformation, [status(thm)], [f_185])).
% 40.82/29.62  tff(c_135293, plain, (![D_3717, A_3718]: (k2_funct_1('#skF_5')=k1_xboole_0 | v1_funct_2(D_3717, A_3718, k2_zfmisc_1('#skF_4', '#skF_3')) | ~m1_subset_1(D_3717, k1_zfmisc_1(k2_zfmisc_1(A_3718, k2_funct_1('#skF_5')))) | ~v1_funct_2(D_3717, A_3718, k2_funct_1('#skF_5')) | ~v1_funct_1(D_3717))), inference(resolution, [status(thm)], [c_27046, c_135265])).
% 40.82/29.62  tff(c_135386, plain, (k2_funct_1('#skF_5')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_135293])).
% 40.82/29.62  tff(c_135409, plain, (k2_relat_1('#skF_5')=k1_relat_1(k1_xboole_0) | ~v2_funct_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_135386, c_54])).
% 40.82/29.62  tff(c_135424, plain, (k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_27118, c_100, c_94, c_134202, c_75688, c_135409])).
% 40.82/29.62  tff(c_135485, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_135424, c_12])).
% 40.82/29.62  tff(c_135487, plain, $false, inference(negUnitSimplification, [status(thm)], [c_133704, c_135485])).
% 40.82/29.62  tff(c_135489, plain, (k2_funct_1('#skF_5')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_135293])).
% 40.82/29.62  tff(c_75784, plain, (![C_2409, A_2410, B_2411]: (v4_relat_1(C_2409, A_2410) | ~m1_subset_1(C_2409, k1_zfmisc_1(k2_zfmisc_1(A_2410, B_2411))))), inference(cnfTransformation, [status(thm)], [f_128])).
% 40.82/29.62  tff(c_75810, plain, (![C_2415]: (v4_relat_1(C_2415, '#skF_3') | ~m1_subset_1(C_2415, k1_zfmisc_1('#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_75438, c_75784])).
% 40.82/29.62  tff(c_75818, plain, (v4_relat_1('#skF_5', '#skF_3')), inference(resolution, [status(thm)], [c_75442, c_75810])).
% 40.82/29.62  tff(c_133940, plain, (![A_3641]: (k1_relat_1(k2_funct_1(A_3641))=k2_relat_1(A_3641) | ~v2_funct_1(A_3641) | ~v1_funct_1(A_3641) | ~v1_relat_1(A_3641))), inference(cnfTransformation, [status(thm)], [f_118])).
% 40.82/29.62  tff(c_203266, plain, (![A_5065]: (v1_funct_2(k2_funct_1(A_5065), k2_relat_1(A_5065), k2_relat_1(k2_funct_1(A_5065))) | ~v1_funct_1(k2_funct_1(A_5065)) | ~v1_relat_1(k2_funct_1(A_5065)) | ~v2_funct_1(A_5065) | ~v1_funct_1(A_5065) | ~v1_relat_1(A_5065))), inference(superposition, [status(thm), theory('equality')], [c_133940, c_74])).
% 40.82/29.62  tff(c_203305, plain, (v1_funct_2(k2_funct_1('#skF_5'), '#skF_4', k2_relat_1(k2_funct_1('#skF_5'))) | ~v1_funct_1(k2_funct_1('#skF_5')) | ~v1_relat_1(k2_funct_1('#skF_5')) | ~v2_funct_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_134202, c_203266])).
% 40.82/29.62  tff(c_203324, plain, (v1_funct_2(k2_funct_1('#skF_5'), '#skF_4', k2_relat_1(k2_funct_1('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_27118, c_100, c_94, c_27116, c_214, c_203305])).
% 40.82/29.62  tff(c_203371, plain, (v1_funct_2(k2_funct_1('#skF_5'), '#skF_4', k1_relat_1('#skF_5')) | ~v2_funct_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_52, c_203324])).
% 40.82/29.62  tff(c_203373, plain, (v1_funct_2(k2_funct_1('#skF_5'), '#skF_4', k1_relat_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_27118, c_100, c_94, c_203371])).
% 40.82/29.62  tff(c_134316, plain, (![A_3671]: (m1_subset_1(A_3671, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_3671), k2_relat_1(A_3671)))) | ~v1_funct_1(A_3671) | ~v1_relat_1(A_3671))), inference(cnfTransformation, [status(thm)], [f_166])).
% 40.82/29.62  tff(c_205686, plain, (![A_5105]: (m1_subset_1(k2_funct_1(A_5105), k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(A_5105), k2_relat_1(k2_funct_1(A_5105))))) | ~v1_funct_1(k2_funct_1(A_5105)) | ~v1_relat_1(k2_funct_1(A_5105)) | ~v2_funct_1(A_5105) | ~v1_funct_1(A_5105) | ~v1_relat_1(A_5105))), inference(superposition, [status(thm), theory('equality')], [c_54, c_134316])).
% 40.82/29.62  tff(c_205751, plain, (m1_subset_1(k2_funct_1('#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', k2_relat_1(k2_funct_1('#skF_5'))))) | ~v1_funct_1(k2_funct_1('#skF_5')) | ~v1_relat_1(k2_funct_1('#skF_5')) | ~v2_funct_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_134202, c_205686])).
% 40.82/29.62  tff(c_205787, plain, (m1_subset_1(k2_funct_1('#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', k2_relat_1(k2_funct_1('#skF_5')))))), inference(demodulation, [status(thm), theory('equality')], [c_27118, c_100, c_94, c_27116, c_214, c_205751])).
% 40.82/29.62  tff(c_205866, plain, (m1_subset_1(k2_funct_1('#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', k1_relat_1('#skF_5')))) | ~v2_funct_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_52, c_205787])).
% 40.82/29.62  tff(c_205882, plain, (m1_subset_1(k2_funct_1('#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', k1_relat_1('#skF_5'))))), inference(demodulation, [status(thm), theory('equality')], [c_27118, c_100, c_94, c_205866])).
% 40.82/29.62  tff(c_211742, plain, (![B_5185, D_5186, A_5187, A_5188]: (k1_relat_1(B_5185)=k1_xboole_0 | v1_funct_2(D_5186, A_5187, A_5188) | ~m1_subset_1(D_5186, k1_zfmisc_1(k2_zfmisc_1(A_5187, k1_relat_1(B_5185)))) | ~v1_funct_2(D_5186, A_5187, k1_relat_1(B_5185)) | ~v1_funct_1(D_5186) | ~v4_relat_1(B_5185, A_5188) | ~v1_relat_1(B_5185))), inference(resolution, [status(thm)], [c_38, c_135265])).
% 40.82/29.62  tff(c_211765, plain, (![A_5188]: (k1_relat_1('#skF_5')=k1_xboole_0 | v1_funct_2(k2_funct_1('#skF_5'), '#skF_4', A_5188) | ~v1_funct_2(k2_funct_1('#skF_5'), '#skF_4', k1_relat_1('#skF_5')) | ~v1_funct_1(k2_funct_1('#skF_5')) | ~v4_relat_1('#skF_5', A_5188) | ~v1_relat_1('#skF_5'))), inference(resolution, [status(thm)], [c_205882, c_211742])).
% 40.82/29.62  tff(c_211835, plain, (![A_5188]: (k1_relat_1('#skF_5')=k1_xboole_0 | v1_funct_2(k2_funct_1('#skF_5'), '#skF_4', A_5188) | ~v4_relat_1('#skF_5', A_5188))), inference(demodulation, [status(thm), theory('equality')], [c_27118, c_214, c_203373, c_211765])).
% 40.82/29.62  tff(c_214593, plain, (k1_relat_1('#skF_5')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_211835])).
% 40.82/29.62  tff(c_205880, plain, (r1_tarski(k2_funct_1('#skF_5'), k2_zfmisc_1('#skF_4', k2_relat_1(k2_funct_1('#skF_5'))))), inference(resolution, [status(thm)], [c_205787, c_30])).
% 40.82/29.62  tff(c_205931, plain, (r1_tarski(k2_funct_1('#skF_5'), k2_zfmisc_1('#skF_4', k1_relat_1('#skF_5'))) | ~v2_funct_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_52, c_205880])).
% 40.82/29.62  tff(c_205959, plain, (r1_tarski(k2_funct_1('#skF_5'), k2_zfmisc_1('#skF_4', k1_relat_1('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_27118, c_100, c_94, c_205931])).
% 40.82/29.62  tff(c_206022, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_4', k1_relat_1('#skF_5'))) | v1_xboole_0(k2_funct_1('#skF_5'))), inference(resolution, [status(thm)], [c_205959, c_75527])).
% 40.82/29.62  tff(c_206069, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_4', k1_relat_1('#skF_5')))), inference(splitLeft, [status(thm)], [c_206022])).
% 40.82/29.62  tff(c_214605, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_4', k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_214593, c_206069])).
% 40.82/29.62  tff(c_214616, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12, c_26, c_214605])).
% 40.82/29.62  tff(c_214719, plain, (![A_5240]: (v1_funct_2(k2_funct_1('#skF_5'), '#skF_4', A_5240) | ~v4_relat_1('#skF_5', A_5240))), inference(splitRight, [status(thm)], [c_211835])).
% 40.82/29.62  tff(c_214722, plain, (~v4_relat_1('#skF_5', '#skF_3')), inference(resolution, [status(thm)], [c_214719, c_27041])).
% 40.82/29.62  tff(c_214726, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_75818, c_214722])).
% 40.82/29.62  tff(c_214727, plain, (v1_xboole_0(k2_funct_1('#skF_5'))), inference(splitRight, [status(thm)], [c_206022])).
% 40.82/29.62  tff(c_214772, plain, (k2_funct_1('#skF_5')=k1_xboole_0), inference(resolution, [status(thm)], [c_214727, c_14])).
% 40.82/29.62  tff(c_214804, plain, $false, inference(negUnitSimplification, [status(thm)], [c_135489, c_214772])).
% 40.82/29.62  tff(c_214806, plain, (v1_xboole_0('#skF_4')), inference(splitRight, [status(thm)], [c_133700])).
% 40.82/29.62  tff(c_214820, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_214806, c_14])).
% 40.82/29.62  tff(c_75451, plain, (k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3' | k1_xboole_0!='#skF_5'), inference(superposition, [status(thm), theory('equality')], [c_75438, c_24])).
% 40.82/29.62  tff(c_75507, plain, (k1_xboole_0!='#skF_5'), inference(splitLeft, [status(thm)], [c_75451])).
% 40.82/29.62  tff(c_214853, plain, ('#skF_5'!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_214820, c_75507])).
% 40.82/29.62  tff(c_214860, plain, (![A_15]: (k2_zfmisc_1(A_15, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_214820, c_214820, c_26])).
% 40.82/29.62  tff(c_214995, plain, ('#skF_5'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_214860, c_75438])).
% 40.82/29.62  tff(c_214997, plain, $false, inference(negUnitSimplification, [status(thm)], [c_214853, c_214995])).
% 40.82/29.62  tff(c_214999, plain, (k1_xboole_0='#skF_5'), inference(splitRight, [status(thm)], [c_75451])).
% 40.82/29.62  tff(c_215008, plain, (v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_214999, c_12])).
% 40.82/29.62  tff(c_215012, plain, $false, inference(negUnitSimplification, [status(thm)], [c_75440, c_215008])).
% 40.82/29.62  tff(c_215013, plain, (k2_zfmisc_1('#skF_3', '#skF_4')='#skF_5'), inference(splitRight, [status(thm)], [c_27098])).
% 40.82/29.62  tff(c_215015, plain, (~r1_tarski(k2_zfmisc_1('#skF_3', '#skF_4'), '#skF_5')), inference(splitLeft, [status(thm)], [c_27061])).
% 40.82/29.62  tff(c_215097, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_20, c_215013, c_215015])).
% 40.82/29.62  tff(c_215098, plain, (k2_zfmisc_1('#skF_3', '#skF_4')='#skF_5'), inference(splitRight, [status(thm)], [c_27061])).
% 40.82/29.62  tff(c_215014, plain, (v1_xboole_0(k2_zfmisc_1('#skF_3', '#skF_4'))), inference(splitRight, [status(thm)], [c_27098])).
% 40.82/29.62  tff(c_215115, plain, (v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_215098, c_215014])).
% 40.82/29.62  tff(c_215122, plain, (k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_215115, c_14])).
% 40.82/29.62  tff(c_215134, plain, (![B_5253, A_5254]: (B_5253='#skF_5' | A_5254='#skF_5' | k2_zfmisc_1(A_5254, B_5253)!='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_215122, c_215122, c_215122, c_24])).
% 40.82/29.62  tff(c_215138, plain, ('#skF_5'='#skF_4' | '#skF_5'='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_215098, c_215134])).
% 40.82/29.62  tff(c_215182, plain, ('#skF_5'='#skF_3'), inference(splitLeft, [status(thm)], [c_215138])).
% 40.82/29.62  tff(c_215192, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_215182, c_27118])).
% 40.82/29.62  tff(c_215200, plain, (v1_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_215182, c_100])).
% 40.82/29.62  tff(c_215199, plain, (v2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_215182, c_94])).
% 40.82/29.62  tff(c_10, plain, (![A_5, B_6]: (r2_hidden('#skF_2'(A_5, B_6), A_5) | r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_38])).
% 40.82/29.62  tff(c_215188, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_215182, c_215115])).
% 40.82/29.62  tff(c_215101, plain, (m1_subset_1('#skF_5', k1_zfmisc_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_215098, c_96])).
% 40.82/29.62  tff(c_215189, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_215182, c_215182, c_215101])).
% 40.82/29.62  tff(c_215527, plain, (![C_5306, B_5307, A_5308]: (~v1_xboole_0(C_5306) | ~m1_subset_1(B_5307, k1_zfmisc_1(C_5306)) | ~r2_hidden(A_5308, B_5307))), inference(cnfTransformation, [status(thm)], [f_74])).
% 40.82/29.62  tff(c_215529, plain, (![A_5308]: (~v1_xboole_0('#skF_3') | ~r2_hidden(A_5308, '#skF_3'))), inference(resolution, [status(thm)], [c_215189, c_215527])).
% 40.82/29.62  tff(c_215536, plain, (![A_5309]: (~r2_hidden(A_5309, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_215188, c_215529])).
% 40.82/29.62  tff(c_215548, plain, (![B_5310]: (r1_tarski('#skF_3', B_5310))), inference(resolution, [status(thm)], [c_10, c_215536])).
% 40.82/29.62  tff(c_215575, plain, (![B_5311]: (B_5311='#skF_3' | ~r1_tarski(B_5311, '#skF_3'))), inference(resolution, [status(thm)], [c_215548, c_16])).
% 40.82/29.62  tff(c_215591, plain, (![A_28]: (k7_relat_1('#skF_3', A_28)='#skF_3' | ~v1_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_44, c_215575])).
% 40.82/29.62  tff(c_215609, plain, (![A_5312]: (k7_relat_1('#skF_3', A_5312)='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_215192, c_215591])).
% 40.82/29.62  tff(c_215621, plain, (![A_5312]: (r1_tarski(k1_relat_1('#skF_3'), A_5312) | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_215609, c_42])).
% 40.82/29.62  tff(c_215669, plain, (![A_5315]: (r1_tarski(k1_relat_1('#skF_3'), A_5315))), inference(demodulation, [status(thm), theory('equality')], [c_215192, c_215621])).
% 40.82/29.62  tff(c_215573, plain, (![B_5310]: (B_5310='#skF_3' | ~r1_tarski(B_5310, '#skF_3'))), inference(resolution, [status(thm)], [c_215548, c_16])).
% 40.82/29.62  tff(c_215694, plain, (k1_relat_1('#skF_3')='#skF_3'), inference(resolution, [status(thm)], [c_215669, c_215573])).
% 40.82/29.62  tff(c_215126, plain, (![A_15]: (k2_zfmisc_1(A_15, '#skF_5')='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_215122, c_215122, c_26])).
% 40.82/29.62  tff(c_215184, plain, (![A_15]: (k2_zfmisc_1(A_15, '#skF_3')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_215182, c_215182, c_215126])).
% 40.82/29.62  tff(c_215194, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_215182, c_27042])).
% 40.82/29.62  tff(c_215335, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_215184, c_215194])).
% 40.82/29.62  tff(c_215344, plain, (r1_tarski(k2_funct_1('#skF_3'), '#skF_3')), inference(resolution, [status(thm)], [c_215335, c_30])).
% 40.82/29.62  tff(c_215350, plain, (k2_funct_1('#skF_3')='#skF_3' | ~v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_215344, c_27074])).
% 40.82/29.62  tff(c_215357, plain, (k2_funct_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_215188, c_215350])).
% 40.82/29.62  tff(c_216081, plain, (![A_5353]: (k1_relat_1(k2_funct_1(A_5353))=k2_relat_1(A_5353) | ~v2_funct_1(A_5353) | ~v1_funct_1(A_5353) | ~v1_relat_1(A_5353))), inference(cnfTransformation, [status(thm)], [f_118])).
% 40.82/29.62  tff(c_216104, plain, (k2_relat_1('#skF_3')=k1_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_215357, c_216081])).
% 40.82/29.62  tff(c_216108, plain, (k2_relat_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_215192, c_215200, c_215199, c_215694, c_216104])).
% 40.82/29.62  tff(c_215125, plain, (![B_16]: (k2_zfmisc_1('#skF_5', B_16)='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_215122, c_215122, c_28])).
% 40.82/29.62  tff(c_215183, plain, (![B_16]: (k2_zfmisc_1('#skF_3', B_16)='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_215182, c_215182, c_215125])).
% 40.82/29.62  tff(c_216916, plain, (![A_5417, B_5418, C_5419]: (k2_relset_1(A_5417, B_5418, C_5419)=k2_relat_1(C_5419) | ~m1_subset_1(C_5419, k1_zfmisc_1(k2_zfmisc_1(A_5417, B_5418))))), inference(cnfTransformation, [status(thm)], [f_139])).
% 40.82/29.62  tff(c_221384, plain, (![B_5615, C_5616]: (k2_relset_1('#skF_3', B_5615, C_5616)=k2_relat_1(C_5616) | ~m1_subset_1(C_5616, k1_zfmisc_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_215183, c_216916])).
% 40.82/29.62  tff(c_221386, plain, (![B_5615]: (k2_relset_1('#skF_3', B_5615, '#skF_3')=k2_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_215189, c_221384])).
% 40.82/29.62  tff(c_221393, plain, (![B_5617]: (k2_relset_1('#skF_3', B_5617, '#skF_3')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_216108, c_221386])).
% 40.82/29.62  tff(c_215197, plain, (k2_relset_1('#skF_3', '#skF_4', '#skF_3')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_215182, c_92])).
% 40.82/29.62  tff(c_221400, plain, ('#skF_3'='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_221393, c_215197])).
% 40.82/29.62  tff(c_215781, plain, (![A_5321]: (v1_funct_2(A_5321, k1_relat_1(A_5321), k2_relat_1(A_5321)) | ~v1_funct_1(A_5321) | ~v1_relat_1(A_5321))), inference(cnfTransformation, [status(thm)], [f_166])).
% 40.82/29.62  tff(c_215787, plain, (v1_funct_2('#skF_3', '#skF_3', k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_215694, c_215781])).
% 40.82/29.62  tff(c_215792, plain, (v1_funct_2('#skF_3', '#skF_3', k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_215192, c_215200, c_215787])).
% 40.82/29.62  tff(c_216109, plain, (v1_funct_2('#skF_3', '#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_216108, c_215792])).
% 40.82/29.62  tff(c_215545, plain, (![B_6]: (r1_tarski('#skF_3', B_6))), inference(resolution, [status(thm)], [c_10, c_215536])).
% 40.82/29.62  tff(c_215187, plain, (k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_215182, c_215122])).
% 40.82/29.62  tff(c_82, plain, (![D_58, C_57, B_56]: (v1_funct_2(D_58, k1_xboole_0, C_57) | ~r1_tarski(B_56, C_57) | ~m1_subset_1(D_58, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_56))) | ~v1_funct_2(D_58, k1_xboole_0, B_56) | ~v1_funct_1(D_58))), inference(cnfTransformation, [status(thm)], [f_185])).
% 40.82/29.62  tff(c_102, plain, (![D_58, C_57, B_56]: (v1_funct_2(D_58, k1_xboole_0, C_57) | ~r1_tarski(B_56, C_57) | ~m1_subset_1(D_58, k1_zfmisc_1(k1_xboole_0)) | ~v1_funct_2(D_58, k1_xboole_0, B_56) | ~v1_funct_1(D_58))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_82])).
% 40.82/29.62  tff(c_218066, plain, (![D_5484, C_5485, B_5486]: (v1_funct_2(D_5484, '#skF_3', C_5485) | ~r1_tarski(B_5486, C_5485) | ~m1_subset_1(D_5484, k1_zfmisc_1('#skF_3')) | ~v1_funct_2(D_5484, '#skF_3', B_5486) | ~v1_funct_1(D_5484))), inference(demodulation, [status(thm), theory('equality')], [c_215187, c_215187, c_215187, c_102])).
% 40.82/29.62  tff(c_218205, plain, (![D_5494, B_5495]: (v1_funct_2(D_5494, '#skF_3', B_5495) | ~m1_subset_1(D_5494, k1_zfmisc_1('#skF_3')) | ~v1_funct_2(D_5494, '#skF_3', '#skF_3') | ~v1_funct_1(D_5494))), inference(resolution, [status(thm)], [c_215545, c_218066])).
% 40.82/29.62  tff(c_218207, plain, (![B_5495]: (v1_funct_2('#skF_3', '#skF_3', B_5495) | ~v1_funct_2('#skF_3', '#skF_3', '#skF_3') | ~v1_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_215189, c_218205])).
% 40.82/29.62  tff(c_218213, plain, (![B_5495]: (v1_funct_2('#skF_3', '#skF_3', B_5495))), inference(demodulation, [status(thm), theory('equality')], [c_215200, c_216109, c_218207])).
% 40.82/29.62  tff(c_221433, plain, (![B_5495]: (v1_funct_2('#skF_4', '#skF_4', B_5495))), inference(demodulation, [status(thm), theory('equality')], [c_221400, c_221400, c_218213])).
% 40.82/29.62  tff(c_215195, plain, (~v1_funct_2(k2_funct_1('#skF_3'), '#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_215182, c_27041])).
% 40.82/29.62  tff(c_215361, plain, (~v1_funct_2('#skF_3', '#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_215357, c_215195])).
% 40.82/29.62  tff(c_221482, plain, (~v1_funct_2('#skF_4', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_221400, c_221400, c_215361])).
% 40.82/29.62  tff(c_222392, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_221433, c_221482])).
% 40.82/29.62  tff(c_222393, plain, ('#skF_5'='#skF_4'), inference(splitRight, [status(thm)], [c_215138])).
% 40.82/29.62  tff(c_222412, plain, (v1_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_222393, c_100])).
% 40.82/29.62  tff(c_222404, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_222393, c_27118])).
% 40.82/29.62  tff(c_222411, plain, (v2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_222393, c_94])).
% 40.82/29.62  tff(c_222400, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_222393, c_215115])).
% 40.82/29.62  tff(c_222401, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_222393, c_222393, c_215101])).
% 40.82/29.62  tff(c_222636, plain, (![C_5656, B_5657, A_5658]: (~v1_xboole_0(C_5656) | ~m1_subset_1(B_5657, k1_zfmisc_1(C_5656)) | ~r2_hidden(A_5658, B_5657))), inference(cnfTransformation, [status(thm)], [f_74])).
% 40.82/29.62  tff(c_222638, plain, (![A_5658]: (~v1_xboole_0('#skF_4') | ~r2_hidden(A_5658, '#skF_4'))), inference(resolution, [status(thm)], [c_222401, c_222636])).
% 40.82/29.62  tff(c_222645, plain, (![A_5659]: (~r2_hidden(A_5659, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_222400, c_222638])).
% 40.82/29.62  tff(c_222657, plain, (![B_5660]: (r1_tarski('#skF_4', B_5660))), inference(resolution, [status(thm)], [c_10, c_222645])).
% 40.82/29.62  tff(c_222677, plain, (![B_5661]: (B_5661='#skF_4' | ~r1_tarski(B_5661, '#skF_4'))), inference(resolution, [status(thm)], [c_222657, c_16])).
% 40.82/29.62  tff(c_222693, plain, (![A_28]: (k7_relat_1('#skF_4', A_28)='#skF_4' | ~v1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_44, c_222677])).
% 40.82/29.62  tff(c_222711, plain, (![A_5662]: (k7_relat_1('#skF_4', A_5662)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_222404, c_222693])).
% 40.82/29.62  tff(c_222719, plain, (![A_5662]: (r1_tarski(k1_relat_1('#skF_4'), A_5662) | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_222711, c_42])).
% 40.82/29.62  tff(c_222733, plain, (![A_5663]: (r1_tarski(k1_relat_1('#skF_4'), A_5663))), inference(demodulation, [status(thm), theory('equality')], [c_222404, c_222719])).
% 40.82/29.62  tff(c_222676, plain, (![B_5660]: (B_5660='#skF_4' | ~r1_tarski(B_5660, '#skF_4'))), inference(resolution, [status(thm)], [c_222657, c_16])).
% 40.82/29.62  tff(c_222754, plain, (k1_relat_1('#skF_4')='#skF_4'), inference(resolution, [status(thm)], [c_222733, c_222676])).
% 40.82/29.62  tff(c_222395, plain, (![B_16]: (k2_zfmisc_1('#skF_4', B_16)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_222393, c_222393, c_215125])).
% 40.82/29.62  tff(c_222406, plain, (m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_222393, c_27042])).
% 40.82/29.62  tff(c_222531, plain, (m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_222395, c_222406])).
% 40.82/29.62  tff(c_222535, plain, (r1_tarski(k2_funct_1('#skF_4'), '#skF_4')), inference(resolution, [status(thm)], [c_222531, c_30])).
% 40.82/29.62  tff(c_222541, plain, (k2_funct_1('#skF_4')='#skF_4' | ~v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_222535, c_27074])).
% 40.82/29.62  tff(c_222548, plain, (k2_funct_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_222400, c_222541])).
% 40.82/29.62  tff(c_223413, plain, (![A_5741]: (k1_relat_1(k2_funct_1(A_5741))=k2_relat_1(A_5741) | ~v2_funct_1(A_5741) | ~v1_funct_1(A_5741) | ~v1_relat_1(A_5741))), inference(cnfTransformation, [status(thm)], [f_118])).
% 40.82/29.62  tff(c_223442, plain, (k2_relat_1('#skF_4')=k1_relat_1('#skF_4') | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_222548, c_223413])).
% 40.82/29.62  tff(c_223446, plain, (k2_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_222404, c_222412, c_222411, c_222754, c_223442])).
% 40.82/29.62  tff(c_223088, plain, (![A_5709]: (v1_funct_2(A_5709, k1_relat_1(A_5709), k2_relat_1(A_5709)) | ~v1_funct_1(A_5709) | ~v1_relat_1(A_5709))), inference(cnfTransformation, [status(thm)], [f_166])).
% 40.82/29.62  tff(c_223094, plain, (v1_funct_2('#skF_4', '#skF_4', k2_relat_1('#skF_4')) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_222754, c_223088])).
% 40.82/29.62  tff(c_223099, plain, (v1_funct_2('#skF_4', '#skF_4', k2_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_222404, c_222412, c_223094])).
% 40.82/29.62  tff(c_223447, plain, (v1_funct_2('#skF_4', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_223446, c_223099])).
% 40.82/29.62  tff(c_222654, plain, (![B_6]: (r1_tarski('#skF_4', B_6))), inference(resolution, [status(thm)], [c_10, c_222645])).
% 40.82/29.62  tff(c_222399, plain, (k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_222393, c_215122])).
% 40.82/29.62  tff(c_226018, plain, (![D_5879, C_5880, B_5881]: (v1_funct_2(D_5879, '#skF_4', C_5880) | ~r1_tarski(B_5881, C_5880) | ~m1_subset_1(D_5879, k1_zfmisc_1('#skF_4')) | ~v1_funct_2(D_5879, '#skF_4', B_5881) | ~v1_funct_1(D_5879))), inference(demodulation, [status(thm), theory('equality')], [c_222399, c_222399, c_222399, c_102])).
% 40.82/29.62  tff(c_226333, plain, (![D_5891, B_5892]: (v1_funct_2(D_5891, '#skF_4', B_5892) | ~m1_subset_1(D_5891, k1_zfmisc_1('#skF_4')) | ~v1_funct_2(D_5891, '#skF_4', '#skF_4') | ~v1_funct_1(D_5891))), inference(resolution, [status(thm)], [c_222654, c_226018])).
% 40.82/29.62  tff(c_226335, plain, (![B_5892]: (v1_funct_2('#skF_4', '#skF_4', B_5892) | ~v1_funct_2('#skF_4', '#skF_4', '#skF_4') | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_222401, c_226333])).
% 40.82/29.62  tff(c_226341, plain, (![B_5892]: (v1_funct_2('#skF_4', '#skF_4', B_5892))), inference(demodulation, [status(thm), theory('equality')], [c_222412, c_223447, c_226335])).
% 40.82/29.62  tff(c_222407, plain, (~v1_funct_2(k2_funct_1('#skF_4'), '#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_222393, c_27041])).
% 40.82/29.62  tff(c_222552, plain, (~v1_funct_2('#skF_4', '#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_222548, c_222407])).
% 40.82/29.62  tff(c_226346, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_226341, c_222552])).
% 40.82/29.62  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 40.82/29.62  
% 40.82/29.62  Inference rules
% 40.82/29.62  ----------------------
% 40.82/29.62  #Ref     : 0
% 40.82/29.62  #Sup     : 52276
% 40.82/29.62  #Fact    : 0
% 40.82/29.62  #Define  : 0
% 40.82/29.62  #Split   : 139
% 40.82/29.62  #Chain   : 0
% 40.82/29.62  #Close   : 0
% 40.82/29.62  
% 40.82/29.62  Ordering : KBO
% 40.82/29.62  
% 40.82/29.62  Simplification rules
% 40.82/29.62  ----------------------
% 40.82/29.62  #Subsume      : 17347
% 40.82/29.62  #Demod        : 56487
% 40.82/29.62  #Tautology    : 22447
% 40.82/29.62  #SimpNegUnit  : 1154
% 40.82/29.62  #BackRed      : 1312
% 40.82/29.62  
% 40.82/29.62  #Partial instantiations: 0
% 40.82/29.62  #Strategies tried      : 1
% 40.82/29.62  
% 40.82/29.62  Timing (in seconds)
% 40.82/29.62  ----------------------
% 40.82/29.62  Preprocessing        : 0.42
% 40.82/29.62  Parsing              : 0.22
% 40.82/29.62  CNF conversion       : 0.03
% 40.82/29.62  Main loop            : 28.30
% 40.82/29.62  Inferencing          : 5.15
% 40.82/29.62  Reduction            : 11.38
% 40.82/29.62  Demodulation         : 8.95
% 40.82/29.62  BG Simplification    : 0.49
% 40.82/29.62  Subsumption          : 9.97
% 40.82/29.62  Abstraction          : 0.80
% 40.82/29.62  MUC search           : 0.00
% 40.82/29.62  Cooper               : 0.00
% 40.82/29.62  Total                : 28.85
% 40.82/29.62  Index Insertion      : 0.00
% 40.82/29.62  Index Deletion       : 0.00
% 40.82/29.62  Index Matching       : 0.00
% 40.82/29.62  BG Taut test         : 0.00
%------------------------------------------------------------------------------
