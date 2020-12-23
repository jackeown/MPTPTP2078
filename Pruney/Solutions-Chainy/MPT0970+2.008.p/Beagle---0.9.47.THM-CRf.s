%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:11:19 EST 2020

% Result     : Theorem 3.98s
% Output     : CNFRefutation 3.98s
% Verified   : 
% Statistics : Number of formulae       :   92 ( 171 expanded)
%              Number of leaves         :   38 (  75 expanded)
%              Depth                    :   11
%              Number of atoms          :  151 ( 424 expanded)
%              Number of equality atoms :   32 (  99 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

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

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_119,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( ! [D] :
              ~ ( r2_hidden(D,B)
                & ! [E] :
                    ~ ( r2_hidden(E,A)
                      & D = k1_funct_1(C,E) ) )
         => k2_relset_1(A,B,C) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_funct_2)).

tff(f_68,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_74,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_56,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_82,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_39,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_43,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_50,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

tff(f_78,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_100,axiom,(
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

tff(f_64,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r2_hidden(A,k1_relat_1(B))
       => r2_hidden(k1_funct_1(B,A),k2_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_funct_1)).

tff(f_33,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(c_52,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_94,plain,(
    ! [C_48,A_49,B_50] :
      ( v1_relat_1(C_48)
      | ~ m1_subset_1(C_48,k1_zfmisc_1(k2_zfmisc_1(A_49,B_50))) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_103,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_52,c_94])).

tff(c_123,plain,(
    ! [C_58,B_59,A_60] :
      ( v5_relat_1(C_58,B_59)
      | ~ m1_subset_1(C_58,k1_zfmisc_1(k2_zfmisc_1(A_60,B_59))) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_132,plain,(
    v5_relat_1('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_52,c_123])).

tff(c_24,plain,(
    ! [B_14,A_13] :
      ( r1_tarski(k2_relat_1(B_14),A_13)
      | ~ v5_relat_1(B_14,A_13)
      | ~ v1_relat_1(B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_498,plain,(
    ! [A_133,B_134,C_135] :
      ( k2_relset_1(A_133,B_134,C_135) = k2_relat_1(C_135)
      | ~ m1_subset_1(C_135,k1_zfmisc_1(k2_zfmisc_1(A_133,B_134))) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_507,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_52,c_498])).

tff(c_50,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_4') != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_508,plain,(
    k2_relat_1('#skF_4') != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_507,c_50])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_14,plain,(
    ! [B_7] : r1_tarski(B_7,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_18,plain,(
    ! [A_8,B_9] :
      ( m1_subset_1(A_8,k1_zfmisc_1(B_9))
      | ~ r1_tarski(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_166,plain,(
    ! [C_71,B_72,A_73] :
      ( ~ v1_xboole_0(C_71)
      | ~ m1_subset_1(B_72,k1_zfmisc_1(C_71))
      | ~ r2_hidden(A_73,B_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_205,plain,(
    ! [B_84,A_85,A_86] :
      ( ~ v1_xboole_0(B_84)
      | ~ r2_hidden(A_85,A_86)
      | ~ r1_tarski(A_86,B_84) ) ),
    inference(resolution,[status(thm)],[c_18,c_166])).

tff(c_215,plain,(
    ! [B_87,A_88,B_89] :
      ( ~ v1_xboole_0(B_87)
      | ~ r1_tarski(A_88,B_87)
      | r1_tarski(A_88,B_89) ) ),
    inference(resolution,[status(thm)],[c_6,c_205])).

tff(c_225,plain,(
    ! [B_90,B_91] :
      ( ~ v1_xboole_0(B_90)
      | r1_tarski(B_90,B_91) ) ),
    inference(resolution,[status(thm)],[c_14,c_215])).

tff(c_10,plain,(
    ! [B_7,A_6] :
      ( B_7 = A_6
      | ~ r1_tarski(B_7,A_6)
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_469,plain,(
    ! [B_127,B_126] :
      ( B_127 = B_126
      | ~ r1_tarski(B_126,B_127)
      | ~ v1_xboole_0(B_127) ) ),
    inference(resolution,[status(thm)],[c_225,c_10])).

tff(c_688,plain,(
    ! [B_161,A_162] :
      ( k2_relat_1(B_161) = A_162
      | ~ v1_xboole_0(A_162)
      | ~ v5_relat_1(B_161,A_162)
      | ~ v1_relat_1(B_161) ) ),
    inference(resolution,[status(thm)],[c_24,c_469])).

tff(c_700,plain,
    ( k2_relat_1('#skF_4') = '#skF_3'
    | ~ v1_xboole_0('#skF_3')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_132,c_688])).

tff(c_709,plain,
    ( k2_relat_1('#skF_4') = '#skF_3'
    | ~ v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_103,c_700])).

tff(c_710,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_508,c_709])).

tff(c_54,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_448,plain,(
    ! [A_120,B_121,C_122] :
      ( k1_relset_1(A_120,B_121,C_122) = k1_relat_1(C_122)
      | ~ m1_subset_1(C_122,k1_zfmisc_1(k2_zfmisc_1(A_120,B_121))) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_457,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_52,c_448])).

tff(c_1599,plain,(
    ! [B_250,A_251,C_252] :
      ( k1_xboole_0 = B_250
      | k1_relset_1(A_251,B_250,C_252) = A_251
      | ~ v1_funct_2(C_252,A_251,B_250)
      | ~ m1_subset_1(C_252,k1_zfmisc_1(k2_zfmisc_1(A_251,B_250))) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_1606,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relset_1('#skF_2','#skF_3','#skF_4') = '#skF_2'
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_52,c_1599])).

tff(c_1610,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relat_1('#skF_4') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_457,c_1606])).

tff(c_1611,plain,(
    k1_relat_1('#skF_4') = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_1610])).

tff(c_60,plain,(
    ! [D_35] :
      ( r2_hidden('#skF_5'(D_35),'#skF_2')
      | ~ r2_hidden(D_35,'#skF_3') ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_145,plain,(
    ! [C_66,B_67,A_68] :
      ( r2_hidden(C_66,B_67)
      | ~ r2_hidden(C_66,A_68)
      | ~ r1_tarski(A_68,B_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_151,plain,(
    ! [D_35,B_67] :
      ( r2_hidden('#skF_5'(D_35),B_67)
      | ~ r1_tarski('#skF_2',B_67)
      | ~ r2_hidden(D_35,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_60,c_145])).

tff(c_56,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_58,plain,(
    ! [D_35] :
      ( k1_funct_1('#skF_4','#skF_5'(D_35)) = D_35
      | ~ r2_hidden(D_35,'#skF_3') ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_868,plain,(
    ! [B_178,A_179] :
      ( r2_hidden(k1_funct_1(B_178,A_179),k2_relat_1(B_178))
      | ~ r2_hidden(A_179,k1_relat_1(B_178))
      | ~ v1_funct_1(B_178)
      | ~ v1_relat_1(B_178) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_881,plain,(
    ! [D_35] :
      ( r2_hidden(D_35,k2_relat_1('#skF_4'))
      | ~ r2_hidden('#skF_5'(D_35),k1_relat_1('#skF_4'))
      | ~ v1_funct_1('#skF_4')
      | ~ v1_relat_1('#skF_4')
      | ~ r2_hidden(D_35,'#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_58,c_868])).

tff(c_918,plain,(
    ! [D_181] :
      ( r2_hidden(D_181,k2_relat_1('#skF_4'))
      | ~ r2_hidden('#skF_5'(D_181),k1_relat_1('#skF_4'))
      | ~ r2_hidden(D_181,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_103,c_56,c_881])).

tff(c_923,plain,(
    ! [D_35] :
      ( r2_hidden(D_35,k2_relat_1('#skF_4'))
      | ~ r1_tarski('#skF_2',k1_relat_1('#skF_4'))
      | ~ r2_hidden(D_35,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_151,c_918])).

tff(c_1105,plain,(
    ~ r1_tarski('#skF_2',k1_relat_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_923])).

tff(c_1612,plain,(
    ~ r1_tarski('#skF_2','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1611,c_1105])).

tff(c_1617,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_1612])).

tff(c_1618,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_1610])).

tff(c_8,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_1643,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1618,c_8])).

tff(c_1645,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_710,c_1643])).

tff(c_1672,plain,(
    ! [D_253] :
      ( r2_hidden(D_253,k2_relat_1('#skF_4'))
      | ~ r2_hidden(D_253,'#skF_3') ) ),
    inference(splitRight,[status(thm)],[c_923])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_1953,plain,(
    ! [A_272] :
      ( r1_tarski(A_272,k2_relat_1('#skF_4'))
      | ~ r2_hidden('#skF_1'(A_272,k2_relat_1('#skF_4')),'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_1672,c_4])).

tff(c_1958,plain,(
    r1_tarski('#skF_3',k2_relat_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_6,c_1953])).

tff(c_1990,plain,
    ( k2_relat_1('#skF_4') = '#skF_3'
    | ~ r1_tarski(k2_relat_1('#skF_4'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_1958,c_10])).

tff(c_1998,plain,(
    ~ r1_tarski(k2_relat_1('#skF_4'),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_508,c_1990])).

tff(c_2004,plain,
    ( ~ v5_relat_1('#skF_4','#skF_3')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_24,c_1998])).

tff(c_2009,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_103,c_132,c_2004])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:16:15 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.98/1.78  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.98/1.79  
% 3.98/1.79  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.98/1.79  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 3.98/1.79  
% 3.98/1.79  %Foreground sorts:
% 3.98/1.79  
% 3.98/1.79  
% 3.98/1.79  %Background operators:
% 3.98/1.79  
% 3.98/1.79  
% 3.98/1.79  %Foreground operators:
% 3.98/1.79  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 3.98/1.79  tff('#skF_5', type, '#skF_5': $i > $i).
% 3.98/1.79  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.98/1.79  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.98/1.79  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.98/1.79  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.98/1.79  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.98/1.79  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.98/1.79  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.98/1.79  tff('#skF_2', type, '#skF_2': $i).
% 3.98/1.79  tff('#skF_3', type, '#skF_3': $i).
% 3.98/1.79  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.98/1.79  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.98/1.79  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.98/1.79  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.98/1.79  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.98/1.79  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.98/1.79  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.98/1.79  tff('#skF_4', type, '#skF_4': $i).
% 3.98/1.79  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.98/1.79  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.98/1.79  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.98/1.79  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.98/1.79  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.98/1.79  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.98/1.79  
% 3.98/1.81  tff(f_119, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((![D]: ~(r2_hidden(D, B) & (![E]: ~(r2_hidden(E, A) & (D = k1_funct_1(C, E)))))) => (k2_relset_1(A, B, C) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t16_funct_2)).
% 3.98/1.81  tff(f_68, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.98/1.81  tff(f_74, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.98/1.81  tff(f_56, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 3.98/1.81  tff(f_82, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 3.98/1.81  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 3.98/1.81  tff(f_39, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.98/1.81  tff(f_43, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 3.98/1.81  tff(f_50, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_subset)).
% 3.98/1.81  tff(f_78, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.98/1.81  tff(f_100, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 3.98/1.81  tff(f_64, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r2_hidden(A, k1_relat_1(B)) => r2_hidden(k1_funct_1(B, A), k2_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_funct_1)).
% 3.98/1.81  tff(f_33, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 3.98/1.81  tff(c_52, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_119])).
% 3.98/1.81  tff(c_94, plain, (![C_48, A_49, B_50]: (v1_relat_1(C_48) | ~m1_subset_1(C_48, k1_zfmisc_1(k2_zfmisc_1(A_49, B_50))))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.98/1.81  tff(c_103, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_52, c_94])).
% 3.98/1.81  tff(c_123, plain, (![C_58, B_59, A_60]: (v5_relat_1(C_58, B_59) | ~m1_subset_1(C_58, k1_zfmisc_1(k2_zfmisc_1(A_60, B_59))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.98/1.81  tff(c_132, plain, (v5_relat_1('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_52, c_123])).
% 3.98/1.81  tff(c_24, plain, (![B_14, A_13]: (r1_tarski(k2_relat_1(B_14), A_13) | ~v5_relat_1(B_14, A_13) | ~v1_relat_1(B_14))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.98/1.81  tff(c_498, plain, (![A_133, B_134, C_135]: (k2_relset_1(A_133, B_134, C_135)=k2_relat_1(C_135) | ~m1_subset_1(C_135, k1_zfmisc_1(k2_zfmisc_1(A_133, B_134))))), inference(cnfTransformation, [status(thm)], [f_82])).
% 3.98/1.81  tff(c_507, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_52, c_498])).
% 3.98/1.81  tff(c_50, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_4')!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_119])).
% 3.98/1.81  tff(c_508, plain, (k2_relat_1('#skF_4')!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_507, c_50])).
% 3.98/1.81  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.98/1.81  tff(c_14, plain, (![B_7]: (r1_tarski(B_7, B_7))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.98/1.81  tff(c_18, plain, (![A_8, B_9]: (m1_subset_1(A_8, k1_zfmisc_1(B_9)) | ~r1_tarski(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.98/1.81  tff(c_166, plain, (![C_71, B_72, A_73]: (~v1_xboole_0(C_71) | ~m1_subset_1(B_72, k1_zfmisc_1(C_71)) | ~r2_hidden(A_73, B_72))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.98/1.81  tff(c_205, plain, (![B_84, A_85, A_86]: (~v1_xboole_0(B_84) | ~r2_hidden(A_85, A_86) | ~r1_tarski(A_86, B_84))), inference(resolution, [status(thm)], [c_18, c_166])).
% 3.98/1.81  tff(c_215, plain, (![B_87, A_88, B_89]: (~v1_xboole_0(B_87) | ~r1_tarski(A_88, B_87) | r1_tarski(A_88, B_89))), inference(resolution, [status(thm)], [c_6, c_205])).
% 3.98/1.81  tff(c_225, plain, (![B_90, B_91]: (~v1_xboole_0(B_90) | r1_tarski(B_90, B_91))), inference(resolution, [status(thm)], [c_14, c_215])).
% 3.98/1.81  tff(c_10, plain, (![B_7, A_6]: (B_7=A_6 | ~r1_tarski(B_7, A_6) | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.98/1.81  tff(c_469, plain, (![B_127, B_126]: (B_127=B_126 | ~r1_tarski(B_126, B_127) | ~v1_xboole_0(B_127))), inference(resolution, [status(thm)], [c_225, c_10])).
% 3.98/1.81  tff(c_688, plain, (![B_161, A_162]: (k2_relat_1(B_161)=A_162 | ~v1_xboole_0(A_162) | ~v5_relat_1(B_161, A_162) | ~v1_relat_1(B_161))), inference(resolution, [status(thm)], [c_24, c_469])).
% 3.98/1.81  tff(c_700, plain, (k2_relat_1('#skF_4')='#skF_3' | ~v1_xboole_0('#skF_3') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_132, c_688])).
% 3.98/1.81  tff(c_709, plain, (k2_relat_1('#skF_4')='#skF_3' | ~v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_103, c_700])).
% 3.98/1.81  tff(c_710, plain, (~v1_xboole_0('#skF_3')), inference(negUnitSimplification, [status(thm)], [c_508, c_709])).
% 3.98/1.81  tff(c_54, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_119])).
% 3.98/1.81  tff(c_448, plain, (![A_120, B_121, C_122]: (k1_relset_1(A_120, B_121, C_122)=k1_relat_1(C_122) | ~m1_subset_1(C_122, k1_zfmisc_1(k2_zfmisc_1(A_120, B_121))))), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.98/1.81  tff(c_457, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_52, c_448])).
% 3.98/1.81  tff(c_1599, plain, (![B_250, A_251, C_252]: (k1_xboole_0=B_250 | k1_relset_1(A_251, B_250, C_252)=A_251 | ~v1_funct_2(C_252, A_251, B_250) | ~m1_subset_1(C_252, k1_zfmisc_1(k2_zfmisc_1(A_251, B_250))))), inference(cnfTransformation, [status(thm)], [f_100])).
% 3.98/1.81  tff(c_1606, plain, (k1_xboole_0='#skF_3' | k1_relset_1('#skF_2', '#skF_3', '#skF_4')='#skF_2' | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_52, c_1599])).
% 3.98/1.81  tff(c_1610, plain, (k1_xboole_0='#skF_3' | k1_relat_1('#skF_4')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_54, c_457, c_1606])).
% 3.98/1.81  tff(c_1611, plain, (k1_relat_1('#skF_4')='#skF_2'), inference(splitLeft, [status(thm)], [c_1610])).
% 3.98/1.81  tff(c_60, plain, (![D_35]: (r2_hidden('#skF_5'(D_35), '#skF_2') | ~r2_hidden(D_35, '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_119])).
% 3.98/1.81  tff(c_145, plain, (![C_66, B_67, A_68]: (r2_hidden(C_66, B_67) | ~r2_hidden(C_66, A_68) | ~r1_tarski(A_68, B_67))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.98/1.81  tff(c_151, plain, (![D_35, B_67]: (r2_hidden('#skF_5'(D_35), B_67) | ~r1_tarski('#skF_2', B_67) | ~r2_hidden(D_35, '#skF_3'))), inference(resolution, [status(thm)], [c_60, c_145])).
% 3.98/1.81  tff(c_56, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_119])).
% 3.98/1.81  tff(c_58, plain, (![D_35]: (k1_funct_1('#skF_4', '#skF_5'(D_35))=D_35 | ~r2_hidden(D_35, '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_119])).
% 3.98/1.81  tff(c_868, plain, (![B_178, A_179]: (r2_hidden(k1_funct_1(B_178, A_179), k2_relat_1(B_178)) | ~r2_hidden(A_179, k1_relat_1(B_178)) | ~v1_funct_1(B_178) | ~v1_relat_1(B_178))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.98/1.81  tff(c_881, plain, (![D_35]: (r2_hidden(D_35, k2_relat_1('#skF_4')) | ~r2_hidden('#skF_5'(D_35), k1_relat_1('#skF_4')) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4') | ~r2_hidden(D_35, '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_58, c_868])).
% 3.98/1.81  tff(c_918, plain, (![D_181]: (r2_hidden(D_181, k2_relat_1('#skF_4')) | ~r2_hidden('#skF_5'(D_181), k1_relat_1('#skF_4')) | ~r2_hidden(D_181, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_103, c_56, c_881])).
% 3.98/1.81  tff(c_923, plain, (![D_35]: (r2_hidden(D_35, k2_relat_1('#skF_4')) | ~r1_tarski('#skF_2', k1_relat_1('#skF_4')) | ~r2_hidden(D_35, '#skF_3'))), inference(resolution, [status(thm)], [c_151, c_918])).
% 3.98/1.81  tff(c_1105, plain, (~r1_tarski('#skF_2', k1_relat_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_923])).
% 3.98/1.81  tff(c_1612, plain, (~r1_tarski('#skF_2', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1611, c_1105])).
% 3.98/1.81  tff(c_1617, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_14, c_1612])).
% 3.98/1.81  tff(c_1618, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_1610])).
% 3.98/1.81  tff(c_8, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.98/1.81  tff(c_1643, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1618, c_8])).
% 3.98/1.81  tff(c_1645, plain, $false, inference(negUnitSimplification, [status(thm)], [c_710, c_1643])).
% 3.98/1.81  tff(c_1672, plain, (![D_253]: (r2_hidden(D_253, k2_relat_1('#skF_4')) | ~r2_hidden(D_253, '#skF_3'))), inference(splitRight, [status(thm)], [c_923])).
% 3.98/1.81  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.98/1.81  tff(c_1953, plain, (![A_272]: (r1_tarski(A_272, k2_relat_1('#skF_4')) | ~r2_hidden('#skF_1'(A_272, k2_relat_1('#skF_4')), '#skF_3'))), inference(resolution, [status(thm)], [c_1672, c_4])).
% 3.98/1.81  tff(c_1958, plain, (r1_tarski('#skF_3', k2_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_6, c_1953])).
% 3.98/1.81  tff(c_1990, plain, (k2_relat_1('#skF_4')='#skF_3' | ~r1_tarski(k2_relat_1('#skF_4'), '#skF_3')), inference(resolution, [status(thm)], [c_1958, c_10])).
% 3.98/1.81  tff(c_1998, plain, (~r1_tarski(k2_relat_1('#skF_4'), '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_508, c_1990])).
% 3.98/1.81  tff(c_2004, plain, (~v5_relat_1('#skF_4', '#skF_3') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_24, c_1998])).
% 3.98/1.81  tff(c_2009, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_103, c_132, c_2004])).
% 3.98/1.81  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.98/1.81  
% 3.98/1.81  Inference rules
% 3.98/1.81  ----------------------
% 3.98/1.81  #Ref     : 0
% 3.98/1.81  #Sup     : 371
% 3.98/1.81  #Fact    : 0
% 3.98/1.81  #Define  : 0
% 3.98/1.81  #Split   : 14
% 3.98/1.81  #Chain   : 0
% 3.98/1.81  #Close   : 0
% 3.98/1.81  
% 3.98/1.81  Ordering : KBO
% 3.98/1.81  
% 3.98/1.81  Simplification rules
% 3.98/1.81  ----------------------
% 3.98/1.81  #Subsume      : 104
% 3.98/1.81  #Demod        : 394
% 3.98/1.81  #Tautology    : 128
% 3.98/1.81  #SimpNegUnit  : 9
% 3.98/1.81  #BackRed      : 99
% 3.98/1.81  
% 3.98/1.81  #Partial instantiations: 0
% 3.98/1.81  #Strategies tried      : 1
% 3.98/1.81  
% 3.98/1.81  Timing (in seconds)
% 3.98/1.81  ----------------------
% 3.98/1.81  Preprocessing        : 0.41
% 3.98/1.81  Parsing              : 0.22
% 3.98/1.81  CNF conversion       : 0.03
% 3.98/1.81  Main loop            : 0.56
% 3.98/1.81  Inferencing          : 0.19
% 3.98/1.81  Reduction            : 0.18
% 3.98/1.81  Demodulation         : 0.13
% 3.98/1.81  BG Simplification    : 0.03
% 3.98/1.81  Subsumption          : 0.11
% 3.98/1.81  Abstraction          : 0.03
% 3.98/1.81  MUC search           : 0.00
% 3.98/1.81  Cooper               : 0.00
% 3.98/1.81  Total                : 1.01
% 3.98/1.81  Index Insertion      : 0.00
% 3.98/1.81  Index Deletion       : 0.00
% 3.98/1.81  Index Matching       : 0.00
% 3.98/1.81  BG Taut test         : 0.00
%------------------------------------------------------------------------------
