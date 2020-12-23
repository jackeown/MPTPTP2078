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
% DateTime   : Thu Dec  3 10:14:38 EST 2020

% Result     : Theorem 2.81s
% Output     : CNFRefutation 2.81s
% Verified   : 
% Statistics : Number of formulae       :   92 ( 170 expanded)
%              Number of leaves         :   46 (  78 expanded)
%              Depth                    :   11
%              Number of atoms          :  131 ( 320 expanded)
%              Number of equality atoms :   54 (  98 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_enumset1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k7_relat_1 > k4_xboole_0 > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > k11_relat_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff(k11_relat_1,type,(
    k11_relat_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

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

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_123,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,k1_tarski(A),B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A),B))) )
       => ( B != k1_xboole_0
         => k2_relset_1(k1_tarski(A),B,C) = k1_tarski(k1_funct_1(C,A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_funct_2)).

tff(f_93,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_61,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_48,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_85,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_71,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_65,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_53,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] : k11_relat_1(A,B) = k9_relat_1(A,k1_tarski(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d16_relat_1)).

tff(f_31,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_59,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( k3_xboole_0(A,k1_tarski(B)) = k1_tarski(B)
     => r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l29_zfmisc_1)).

tff(f_89,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_111,axiom,(
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

tff(f_79,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r2_hidden(A,k1_relat_1(B))
       => k11_relat_1(B,A) = k1_tarski(k1_funct_1(B,A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t117_funct_1)).

tff(c_56,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_1'),'#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_374,plain,(
    ! [A_86,B_87,C_88] :
      ( k2_relset_1(A_86,B_87,C_88) = k2_relat_1(C_88)
      | ~ m1_subset_1(C_88,k1_zfmisc_1(k2_zfmisc_1(A_86,B_87))) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_378,plain,(
    k2_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_56,c_374])).

tff(c_52,plain,(
    k2_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_3') != k1_tarski(k1_funct_1('#skF_3','#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_379,plain,(
    k1_tarski(k1_funct_1('#skF_3','#skF_1')) != k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_378,c_52])).

tff(c_24,plain,(
    ! [A_19,B_20] : v1_relat_1(k2_zfmisc_1(A_19,B_20)) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_138,plain,(
    ! [B_52,A_53] :
      ( v1_relat_1(B_52)
      | ~ m1_subset_1(B_52,k1_zfmisc_1(A_53))
      | ~ v1_relat_1(A_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_141,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1(k1_tarski('#skF_1'),'#skF_2')) ),
    inference(resolution,[status(thm)],[c_56,c_138])).

tff(c_144,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_141])).

tff(c_60,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_170,plain,(
    ! [C_57,A_58,B_59] :
      ( v4_relat_1(C_57,A_58)
      | ~ m1_subset_1(C_57,k1_zfmisc_1(k2_zfmisc_1(A_58,B_59))) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_174,plain,(
    v4_relat_1('#skF_3',k1_tarski('#skF_1')) ),
    inference(resolution,[status(thm)],[c_56,c_170])).

tff(c_204,plain,(
    ! [B_69,A_70] :
      ( k7_relat_1(B_69,A_70) = B_69
      | ~ v4_relat_1(B_69,A_70)
      | ~ v1_relat_1(B_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_207,plain,
    ( k7_relat_1('#skF_3',k1_tarski('#skF_1')) = '#skF_3'
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_174,c_204])).

tff(c_210,plain,(
    k7_relat_1('#skF_3',k1_tarski('#skF_1')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_144,c_207])).

tff(c_26,plain,(
    ! [B_22,A_21] :
      ( k2_relat_1(k7_relat_1(B_22,A_21)) = k9_relat_1(B_22,A_21)
      | ~ v1_relat_1(B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_214,plain,
    ( k9_relat_1('#skF_3',k1_tarski('#skF_1')) = k2_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_210,c_26])).

tff(c_218,plain,(
    k9_relat_1('#skF_3',k1_tarski('#skF_1')) = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_144,c_214])).

tff(c_18,plain,(
    ! [A_14,B_16] :
      ( k9_relat_1(A_14,k1_tarski(B_16)) = k11_relat_1(A_14,B_16)
      | ~ v1_relat_1(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_223,plain,
    ( k11_relat_1('#skF_3','#skF_1') = k2_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_218,c_18])).

tff(c_230,plain,(
    k11_relat_1('#skF_3','#skF_1') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_144,c_223])).

tff(c_6,plain,(
    ! [A_3] : k4_xboole_0(A_3,k1_xboole_0) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_184,plain,(
    ! [B_62,A_63] :
      ( r1_tarski(k1_relat_1(B_62),A_63)
      | ~ v4_relat_1(B_62,A_63)
      | ~ v1_relat_1(B_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( k4_xboole_0(A_1,B_2) = k1_xboole_0
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_240,plain,(
    ! [B_73,A_74] :
      ( k4_xboole_0(k1_relat_1(B_73),A_74) = k1_xboole_0
      | ~ v4_relat_1(B_73,A_74)
      | ~ v1_relat_1(B_73) ) ),
    inference(resolution,[status(thm)],[c_184,c_4])).

tff(c_8,plain,(
    ! [A_4,B_5] : k4_xboole_0(A_4,k4_xboole_0(A_4,B_5)) = k3_xboole_0(A_4,B_5) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_254,plain,(
    ! [B_73,A_74] :
      ( k4_xboole_0(k1_relat_1(B_73),k1_xboole_0) = k3_xboole_0(k1_relat_1(B_73),A_74)
      | ~ v4_relat_1(B_73,A_74)
      | ~ v1_relat_1(B_73) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_240,c_8])).

tff(c_433,plain,(
    ! [B_93,A_94] :
      ( k3_xboole_0(k1_relat_1(B_93),A_94) = k1_relat_1(B_93)
      | ~ v4_relat_1(B_93,A_94)
      | ~ v1_relat_1(B_93) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_254])).

tff(c_14,plain,(
    ! [B_10,A_9] :
      ( r2_hidden(B_10,A_9)
      | k3_xboole_0(A_9,k1_tarski(B_10)) != k1_tarski(B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_695,plain,(
    ! [B_110,B_111] :
      ( r2_hidden(B_110,k1_relat_1(B_111))
      | k1_tarski(B_110) != k1_relat_1(B_111)
      | ~ v4_relat_1(B_111,k1_tarski(B_110))
      | ~ v1_relat_1(B_111) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_433,c_14])).

tff(c_698,plain,
    ( r2_hidden('#skF_1',k1_relat_1('#skF_3'))
    | k1_tarski('#skF_1') != k1_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_174,c_695])).

tff(c_701,plain,
    ( r2_hidden('#skF_1',k1_relat_1('#skF_3'))
    | k1_tarski('#skF_1') != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_144,c_698])).

tff(c_703,plain,(
    k1_tarski('#skF_1') != k1_relat_1('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_701])).

tff(c_54,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_58,plain,(
    v1_funct_2('#skF_3',k1_tarski('#skF_1'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_286,plain,(
    ! [A_76,B_77,C_78] :
      ( k1_relset_1(A_76,B_77,C_78) = k1_relat_1(C_78)
      | ~ m1_subset_1(C_78,k1_zfmisc_1(k2_zfmisc_1(A_76,B_77))) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_290,plain,(
    k1_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_56,c_286])).

tff(c_709,plain,(
    ! [B_115,A_116,C_117] :
      ( k1_xboole_0 = B_115
      | k1_relset_1(A_116,B_115,C_117) = A_116
      | ~ v1_funct_2(C_117,A_116,B_115)
      | ~ m1_subset_1(C_117,k1_zfmisc_1(k2_zfmisc_1(A_116,B_115))) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_712,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_3') = k1_tarski('#skF_1')
    | ~ v1_funct_2('#skF_3',k1_tarski('#skF_1'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_56,c_709])).

tff(c_715,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_tarski('#skF_1') = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_290,c_712])).

tff(c_717,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_703,c_54,c_715])).

tff(c_718,plain,(
    r2_hidden('#skF_1',k1_relat_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_701])).

tff(c_30,plain,(
    ! [B_26,A_25] :
      ( k1_tarski(k1_funct_1(B_26,A_25)) = k11_relat_1(B_26,A_25)
      | ~ r2_hidden(A_25,k1_relat_1(B_26))
      | ~ v1_funct_1(B_26)
      | ~ v1_relat_1(B_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_722,plain,
    ( k1_tarski(k1_funct_1('#skF_3','#skF_1')) = k11_relat_1('#skF_3','#skF_1')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_718,c_30])).

tff(c_725,plain,(
    k1_tarski(k1_funct_1('#skF_3','#skF_1')) = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_144,c_60,c_230,c_722])).

tff(c_727,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_379,c_725])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n013.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 14:35:39 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.81/1.40  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.81/1.41  
% 2.81/1.41  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.81/1.41  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_enumset1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k7_relat_1 > k4_xboole_0 > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > k11_relat_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.81/1.41  
% 2.81/1.41  %Foreground sorts:
% 2.81/1.41  
% 2.81/1.41  
% 2.81/1.41  %Background operators:
% 2.81/1.41  
% 2.81/1.41  
% 2.81/1.41  %Foreground operators:
% 2.81/1.41  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 2.81/1.41  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.81/1.41  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.81/1.41  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.81/1.41  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.81/1.41  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.81/1.41  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.81/1.41  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.81/1.41  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.81/1.41  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.81/1.41  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.81/1.41  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.81/1.41  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.81/1.41  tff(k11_relat_1, type, k11_relat_1: ($i * $i) > $i).
% 2.81/1.41  tff('#skF_2', type, '#skF_2': $i).
% 2.81/1.41  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.81/1.41  tff('#skF_3', type, '#skF_3': $i).
% 2.81/1.41  tff('#skF_1', type, '#skF_1': $i).
% 2.81/1.41  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.81/1.41  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.81/1.41  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.81/1.41  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.81/1.41  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.81/1.41  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.81/1.41  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.81/1.41  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.81/1.41  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.81/1.41  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.81/1.41  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.81/1.41  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.81/1.41  
% 2.81/1.43  tff(f_123, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, k1_tarski(A), B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A), B)))) => (~(B = k1_xboole_0) => (k2_relset_1(k1_tarski(A), B, C) = k1_tarski(k1_funct_1(C, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t62_funct_2)).
% 2.81/1.43  tff(f_93, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 2.81/1.43  tff(f_61, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 2.81/1.43  tff(f_48, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 2.81/1.43  tff(f_85, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.81/1.43  tff(f_71, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t209_relat_1)).
% 2.81/1.43  tff(f_65, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_relat_1)).
% 2.81/1.43  tff(f_53, axiom, (![A]: (v1_relat_1(A) => (![B]: (k11_relat_1(A, B) = k9_relat_1(A, k1_tarski(B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d16_relat_1)).
% 2.81/1.43  tff(f_31, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 2.81/1.43  tff(f_59, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d18_relat_1)).
% 2.81/1.43  tff(f_29, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 2.81/1.43  tff(f_33, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 2.81/1.43  tff(f_41, axiom, (![A, B]: ((k3_xboole_0(A, k1_tarski(B)) = k1_tarski(B)) => r2_hidden(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l29_zfmisc_1)).
% 2.81/1.43  tff(f_89, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.81/1.43  tff(f_111, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 2.81/1.43  tff(f_79, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r2_hidden(A, k1_relat_1(B)) => (k11_relat_1(B, A) = k1_tarski(k1_funct_1(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t117_funct_1)).
% 2.81/1.43  tff(c_56, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_1'), '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_123])).
% 2.81/1.43  tff(c_374, plain, (![A_86, B_87, C_88]: (k2_relset_1(A_86, B_87, C_88)=k2_relat_1(C_88) | ~m1_subset_1(C_88, k1_zfmisc_1(k2_zfmisc_1(A_86, B_87))))), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.81/1.43  tff(c_378, plain, (k2_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_56, c_374])).
% 2.81/1.43  tff(c_52, plain, (k2_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_3')!=k1_tarski(k1_funct_1('#skF_3', '#skF_1'))), inference(cnfTransformation, [status(thm)], [f_123])).
% 2.81/1.43  tff(c_379, plain, (k1_tarski(k1_funct_1('#skF_3', '#skF_1'))!=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_378, c_52])).
% 2.81/1.43  tff(c_24, plain, (![A_19, B_20]: (v1_relat_1(k2_zfmisc_1(A_19, B_20)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.81/1.43  tff(c_138, plain, (![B_52, A_53]: (v1_relat_1(B_52) | ~m1_subset_1(B_52, k1_zfmisc_1(A_53)) | ~v1_relat_1(A_53))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.81/1.43  tff(c_141, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1(k1_tarski('#skF_1'), '#skF_2'))), inference(resolution, [status(thm)], [c_56, c_138])).
% 2.81/1.43  tff(c_144, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_24, c_141])).
% 2.81/1.43  tff(c_60, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_123])).
% 2.81/1.43  tff(c_170, plain, (![C_57, A_58, B_59]: (v4_relat_1(C_57, A_58) | ~m1_subset_1(C_57, k1_zfmisc_1(k2_zfmisc_1(A_58, B_59))))), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.81/1.43  tff(c_174, plain, (v4_relat_1('#skF_3', k1_tarski('#skF_1'))), inference(resolution, [status(thm)], [c_56, c_170])).
% 2.81/1.43  tff(c_204, plain, (![B_69, A_70]: (k7_relat_1(B_69, A_70)=B_69 | ~v4_relat_1(B_69, A_70) | ~v1_relat_1(B_69))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.81/1.43  tff(c_207, plain, (k7_relat_1('#skF_3', k1_tarski('#skF_1'))='#skF_3' | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_174, c_204])).
% 2.81/1.43  tff(c_210, plain, (k7_relat_1('#skF_3', k1_tarski('#skF_1'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_144, c_207])).
% 2.81/1.43  tff(c_26, plain, (![B_22, A_21]: (k2_relat_1(k7_relat_1(B_22, A_21))=k9_relat_1(B_22, A_21) | ~v1_relat_1(B_22))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.81/1.43  tff(c_214, plain, (k9_relat_1('#skF_3', k1_tarski('#skF_1'))=k2_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_210, c_26])).
% 2.81/1.43  tff(c_218, plain, (k9_relat_1('#skF_3', k1_tarski('#skF_1'))=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_144, c_214])).
% 2.81/1.43  tff(c_18, plain, (![A_14, B_16]: (k9_relat_1(A_14, k1_tarski(B_16))=k11_relat_1(A_14, B_16) | ~v1_relat_1(A_14))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.81/1.43  tff(c_223, plain, (k11_relat_1('#skF_3', '#skF_1')=k2_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_218, c_18])).
% 2.81/1.43  tff(c_230, plain, (k11_relat_1('#skF_3', '#skF_1')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_144, c_223])).
% 2.81/1.43  tff(c_6, plain, (![A_3]: (k4_xboole_0(A_3, k1_xboole_0)=A_3)), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.81/1.43  tff(c_184, plain, (![B_62, A_63]: (r1_tarski(k1_relat_1(B_62), A_63) | ~v4_relat_1(B_62, A_63) | ~v1_relat_1(B_62))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.81/1.43  tff(c_4, plain, (![A_1, B_2]: (k4_xboole_0(A_1, B_2)=k1_xboole_0 | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.81/1.43  tff(c_240, plain, (![B_73, A_74]: (k4_xboole_0(k1_relat_1(B_73), A_74)=k1_xboole_0 | ~v4_relat_1(B_73, A_74) | ~v1_relat_1(B_73))), inference(resolution, [status(thm)], [c_184, c_4])).
% 2.81/1.43  tff(c_8, plain, (![A_4, B_5]: (k4_xboole_0(A_4, k4_xboole_0(A_4, B_5))=k3_xboole_0(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.81/1.43  tff(c_254, plain, (![B_73, A_74]: (k4_xboole_0(k1_relat_1(B_73), k1_xboole_0)=k3_xboole_0(k1_relat_1(B_73), A_74) | ~v4_relat_1(B_73, A_74) | ~v1_relat_1(B_73))), inference(superposition, [status(thm), theory('equality')], [c_240, c_8])).
% 2.81/1.43  tff(c_433, plain, (![B_93, A_94]: (k3_xboole_0(k1_relat_1(B_93), A_94)=k1_relat_1(B_93) | ~v4_relat_1(B_93, A_94) | ~v1_relat_1(B_93))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_254])).
% 2.81/1.43  tff(c_14, plain, (![B_10, A_9]: (r2_hidden(B_10, A_9) | k3_xboole_0(A_9, k1_tarski(B_10))!=k1_tarski(B_10))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.81/1.43  tff(c_695, plain, (![B_110, B_111]: (r2_hidden(B_110, k1_relat_1(B_111)) | k1_tarski(B_110)!=k1_relat_1(B_111) | ~v4_relat_1(B_111, k1_tarski(B_110)) | ~v1_relat_1(B_111))), inference(superposition, [status(thm), theory('equality')], [c_433, c_14])).
% 2.81/1.43  tff(c_698, plain, (r2_hidden('#skF_1', k1_relat_1('#skF_3')) | k1_tarski('#skF_1')!=k1_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_174, c_695])).
% 2.81/1.43  tff(c_701, plain, (r2_hidden('#skF_1', k1_relat_1('#skF_3')) | k1_tarski('#skF_1')!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_144, c_698])).
% 2.81/1.43  tff(c_703, plain, (k1_tarski('#skF_1')!=k1_relat_1('#skF_3')), inference(splitLeft, [status(thm)], [c_701])).
% 2.81/1.43  tff(c_54, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_123])).
% 2.81/1.43  tff(c_58, plain, (v1_funct_2('#skF_3', k1_tarski('#skF_1'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_123])).
% 2.81/1.43  tff(c_286, plain, (![A_76, B_77, C_78]: (k1_relset_1(A_76, B_77, C_78)=k1_relat_1(C_78) | ~m1_subset_1(C_78, k1_zfmisc_1(k2_zfmisc_1(A_76, B_77))))), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.81/1.43  tff(c_290, plain, (k1_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_56, c_286])).
% 2.81/1.43  tff(c_709, plain, (![B_115, A_116, C_117]: (k1_xboole_0=B_115 | k1_relset_1(A_116, B_115, C_117)=A_116 | ~v1_funct_2(C_117, A_116, B_115) | ~m1_subset_1(C_117, k1_zfmisc_1(k2_zfmisc_1(A_116, B_115))))), inference(cnfTransformation, [status(thm)], [f_111])).
% 2.81/1.43  tff(c_712, plain, (k1_xboole_0='#skF_2' | k1_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_3')=k1_tarski('#skF_1') | ~v1_funct_2('#skF_3', k1_tarski('#skF_1'), '#skF_2')), inference(resolution, [status(thm)], [c_56, c_709])).
% 2.81/1.43  tff(c_715, plain, (k1_xboole_0='#skF_2' | k1_tarski('#skF_1')=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_290, c_712])).
% 2.81/1.43  tff(c_717, plain, $false, inference(negUnitSimplification, [status(thm)], [c_703, c_54, c_715])).
% 2.81/1.43  tff(c_718, plain, (r2_hidden('#skF_1', k1_relat_1('#skF_3'))), inference(splitRight, [status(thm)], [c_701])).
% 2.81/1.43  tff(c_30, plain, (![B_26, A_25]: (k1_tarski(k1_funct_1(B_26, A_25))=k11_relat_1(B_26, A_25) | ~r2_hidden(A_25, k1_relat_1(B_26)) | ~v1_funct_1(B_26) | ~v1_relat_1(B_26))), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.81/1.43  tff(c_722, plain, (k1_tarski(k1_funct_1('#skF_3', '#skF_1'))=k11_relat_1('#skF_3', '#skF_1') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_718, c_30])).
% 2.81/1.43  tff(c_725, plain, (k1_tarski(k1_funct_1('#skF_3', '#skF_1'))=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_144, c_60, c_230, c_722])).
% 2.81/1.43  tff(c_727, plain, $false, inference(negUnitSimplification, [status(thm)], [c_379, c_725])).
% 2.81/1.43  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.81/1.43  
% 2.81/1.43  Inference rules
% 2.81/1.43  ----------------------
% 2.81/1.43  #Ref     : 0
% 2.81/1.43  #Sup     : 157
% 2.81/1.43  #Fact    : 0
% 2.81/1.43  #Define  : 0
% 2.81/1.43  #Split   : 2
% 2.81/1.43  #Chain   : 0
% 2.81/1.43  #Close   : 0
% 2.81/1.43  
% 2.81/1.43  Ordering : KBO
% 2.81/1.43  
% 2.81/1.43  Simplification rules
% 2.81/1.43  ----------------------
% 2.81/1.43  #Subsume      : 5
% 2.81/1.43  #Demod        : 49
% 2.81/1.43  #Tautology    : 69
% 2.81/1.43  #SimpNegUnit  : 2
% 2.81/1.43  #BackRed      : 1
% 2.81/1.43  
% 2.81/1.43  #Partial instantiations: 0
% 2.81/1.43  #Strategies tried      : 1
% 2.81/1.43  
% 2.81/1.43  Timing (in seconds)
% 2.81/1.43  ----------------------
% 2.81/1.43  Preprocessing        : 0.34
% 2.81/1.43  Parsing              : 0.18
% 2.81/1.43  CNF conversion       : 0.02
% 2.81/1.43  Main loop            : 0.33
% 2.81/1.43  Inferencing          : 0.12
% 2.81/1.43  Reduction            : 0.11
% 2.81/1.43  Demodulation         : 0.07
% 2.81/1.43  BG Simplification    : 0.02
% 2.81/1.43  Subsumption          : 0.06
% 2.81/1.43  Abstraction          : 0.02
% 2.81/1.43  MUC search           : 0.00
% 2.81/1.43  Cooper               : 0.00
% 2.81/1.43  Total                : 0.71
% 2.81/1.43  Index Insertion      : 0.00
% 2.81/1.43  Index Deletion       : 0.00
% 2.81/1.43  Index Matching       : 0.00
% 2.81/1.43  BG Taut test         : 0.00
%------------------------------------------------------------------------------
