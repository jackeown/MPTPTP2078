%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:11:19 EST 2020

% Result     : Theorem 3.51s
% Output     : CNFRefutation 3.88s
% Verified   : 
% Statistics : Number of formulae       :  119 ( 341 expanded)
%              Number of leaves         :   41 ( 133 expanded)
%              Depth                    :   15
%              Number of atoms          :  212 ( 900 expanded)
%              Number of equality atoms :   58 ( 198 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k4_tarski > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1

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

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_143,negated_conjecture,(
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

tff(f_104,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_90,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_96,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_38,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_100,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_124,axiom,(
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

tff(f_81,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r2_hidden(A,k1_relat_1(B))
       => r2_hidden(k1_funct_1(B,A),k2_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_funct_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_106,axiom,(
    ! [A,B] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(A,B))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_relset_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_52,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_55,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_86,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

tff(f_73,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B,C] :
          ( ( r2_hidden(B,k1_relat_1(A))
           => ( C = k1_funct_1(A,B)
            <=> r2_hidden(k4_tarski(B,C),A) ) )
          & ( ~ r2_hidden(B,k1_relat_1(A))
           => ( C = k1_funct_1(A,B)
            <=> C = k1_xboole_0 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_funct_1)).

tff(c_68,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_525,plain,(
    ! [A_129,B_130,C_131] :
      ( k2_relset_1(A_129,B_130,C_131) = k2_relat_1(C_131)
      | ~ m1_subset_1(C_131,k1_zfmisc_1(k2_zfmisc_1(A_129,B_130))) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_538,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_68,c_525])).

tff(c_66,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_4') != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_548,plain,(
    k2_relat_1('#skF_4') != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_538,c_66])).

tff(c_162,plain,(
    ! [C_64,A_65,B_66] :
      ( v1_relat_1(C_64)
      | ~ m1_subset_1(C_64,k1_zfmisc_1(k2_zfmisc_1(A_65,B_66))) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_173,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_68,c_162])).

tff(c_262,plain,(
    ! [C_82,B_83,A_84] :
      ( v5_relat_1(C_82,B_83)
      | ~ m1_subset_1(C_82,k1_zfmisc_1(k2_zfmisc_1(A_84,B_83))) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_275,plain,(
    v5_relat_1('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_68,c_262])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_12,plain,(
    ! [B_7] : r1_tarski(B_7,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_70,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_380,plain,(
    ! [A_103,B_104,C_105] :
      ( k1_relset_1(A_103,B_104,C_105) = k1_relat_1(C_105)
      | ~ m1_subset_1(C_105,k1_zfmisc_1(k2_zfmisc_1(A_103,B_104))) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_393,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_68,c_380])).

tff(c_1078,plain,(
    ! [B_194,A_195,C_196] :
      ( k1_xboole_0 = B_194
      | k1_relset_1(A_195,B_194,C_196) = A_195
      | ~ v1_funct_2(C_196,A_195,B_194)
      | ~ m1_subset_1(C_196,k1_zfmisc_1(k2_zfmisc_1(A_195,B_194))) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_1081,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relset_1('#skF_2','#skF_3','#skF_4') = '#skF_2'
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_68,c_1078])).

tff(c_1093,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relat_1('#skF_4') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_393,c_1081])).

tff(c_1097,plain,(
    k1_relat_1('#skF_4') = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_1093])).

tff(c_76,plain,(
    ! [D_43] :
      ( r2_hidden('#skF_5'(D_43),'#skF_2')
      | ~ r2_hidden(D_43,'#skF_3') ) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_278,plain,(
    ! [C_86,B_87,A_88] :
      ( r2_hidden(C_86,B_87)
      | ~ r2_hidden(C_86,A_88)
      | ~ r1_tarski(A_88,B_87) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_284,plain,(
    ! [D_43,B_87] :
      ( r2_hidden('#skF_5'(D_43),B_87)
      | ~ r1_tarski('#skF_2',B_87)
      | ~ r2_hidden(D_43,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_76,c_278])).

tff(c_72,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_74,plain,(
    ! [D_43] :
      ( k1_funct_1('#skF_4','#skF_5'(D_43)) = D_43
      | ~ r2_hidden(D_43,'#skF_3') ) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_719,plain,(
    ! [B_158,A_159] :
      ( r2_hidden(k1_funct_1(B_158,A_159),k2_relat_1(B_158))
      | ~ r2_hidden(A_159,k1_relat_1(B_158))
      | ~ v1_funct_1(B_158)
      | ~ v1_relat_1(B_158) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_730,plain,(
    ! [D_43] :
      ( r2_hidden(D_43,k2_relat_1('#skF_4'))
      | ~ r2_hidden('#skF_5'(D_43),k1_relat_1('#skF_4'))
      | ~ v1_funct_1('#skF_4')
      | ~ v1_relat_1('#skF_4')
      | ~ r2_hidden(D_43,'#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_74,c_719])).

tff(c_740,plain,(
    ! [D_160] :
      ( r2_hidden(D_160,k2_relat_1('#skF_4'))
      | ~ r2_hidden('#skF_5'(D_160),k1_relat_1('#skF_4'))
      | ~ r2_hidden(D_160,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_173,c_72,c_730])).

tff(c_748,plain,(
    ! [D_43] :
      ( r2_hidden(D_43,k2_relat_1('#skF_4'))
      | ~ r1_tarski('#skF_2',k1_relat_1('#skF_4'))
      | ~ r2_hidden(D_43,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_284,c_740])).

tff(c_752,plain,(
    ~ r1_tarski('#skF_2',k1_relat_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_748])).

tff(c_1102,plain,(
    ~ r1_tarski('#skF_2','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1097,c_752])).

tff(c_1107,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_1102])).

tff(c_1108,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_1093])).

tff(c_22,plain,(
    ! [B_11,A_10] :
      ( r1_tarski(k2_relat_1(B_11),A_10)
      | ~ v5_relat_1(B_11,A_10)
      | ~ v1_relat_1(B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_52,plain,(
    ! [A_35,B_36] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(A_35,B_36))) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_276,plain,(
    ! [B_36] : v5_relat_1(k1_xboole_0,B_36) ),
    inference(resolution,[status(thm)],[c_52,c_262])).

tff(c_93,plain,(
    ! [A_48] : k2_zfmisc_1(A_48,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_24,plain,(
    ! [A_12,B_13] : v1_relat_1(k2_zfmisc_1(A_12,B_13)) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_97,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_93,c_24])).

tff(c_26,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_205,plain,(
    ! [B_74,A_75] :
      ( r1_tarski(k2_relat_1(B_74),A_75)
      | ~ v5_relat_1(B_74,A_75)
      | ~ v1_relat_1(B_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_217,plain,(
    ! [A_75] :
      ( r1_tarski(k1_xboole_0,A_75)
      | ~ v5_relat_1(k1_xboole_0,A_75)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_205])).

tff(c_222,plain,(
    ! [A_75] :
      ( r1_tarski(k1_xboole_0,A_75)
      | ~ v5_relat_1(k1_xboole_0,A_75) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_97,c_217])).

tff(c_286,plain,(
    ! [A_75] : r1_tarski(k1_xboole_0,A_75) ),
    inference(demodulation,[status(thm),theory(equality)],[c_276,c_222])).

tff(c_427,plain,(
    ! [A_115,B_116,B_117] :
      ( r2_hidden('#skF_1'(A_115,B_116),B_117)
      | ~ r1_tarski(A_115,B_117)
      | r1_tarski(A_115,B_116) ) ),
    inference(resolution,[status(thm)],[c_6,c_278])).

tff(c_40,plain,(
    ! [B_22,A_21] :
      ( ~ r1_tarski(B_22,A_21)
      | ~ r2_hidden(A_21,B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_440,plain,(
    ! [B_118,A_119,B_120] :
      ( ~ r1_tarski(B_118,'#skF_1'(A_119,B_120))
      | ~ r1_tarski(A_119,B_118)
      | r1_tarski(A_119,B_120) ) ),
    inference(resolution,[status(thm)],[c_427,c_40])).

tff(c_456,plain,(
    ! [A_121,B_122] :
      ( ~ r1_tarski(A_121,k1_xboole_0)
      | r1_tarski(A_121,B_122) ) ),
    inference(resolution,[status(thm)],[c_286,c_440])).

tff(c_468,plain,(
    ! [B_11,B_122] :
      ( r1_tarski(k2_relat_1(B_11),B_122)
      | ~ v5_relat_1(B_11,k1_xboole_0)
      | ~ v1_relat_1(B_11) ) ),
    inference(resolution,[status(thm)],[c_22,c_456])).

tff(c_36,plain,(
    ! [A_14,B_17] :
      ( k1_funct_1(A_14,B_17) = k1_xboole_0
      | r2_hidden(B_17,k1_relat_1(A_14))
      | ~ v1_funct_1(A_14)
      | ~ v1_relat_1(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_747,plain,(
    ! [D_160] :
      ( r2_hidden(D_160,k2_relat_1('#skF_4'))
      | ~ r2_hidden(D_160,'#skF_3')
      | k1_funct_1('#skF_4','#skF_5'(D_160)) = k1_xboole_0
      | ~ v1_funct_1('#skF_4')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_36,c_740])).

tff(c_758,plain,(
    ! [D_164] :
      ( r2_hidden(D_164,k2_relat_1('#skF_4'))
      | ~ r2_hidden(D_164,'#skF_3')
      | k1_funct_1('#skF_4','#skF_5'(D_164)) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_173,c_72,c_747])).

tff(c_771,plain,(
    ! [D_165] :
      ( ~ r1_tarski(k2_relat_1('#skF_4'),D_165)
      | ~ r2_hidden(D_165,'#skF_3')
      | k1_funct_1('#skF_4','#skF_5'(D_165)) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_758,c_40])).

tff(c_775,plain,(
    ! [B_122] :
      ( ~ r2_hidden(B_122,'#skF_3')
      | k1_funct_1('#skF_4','#skF_5'(B_122)) = k1_xboole_0
      | ~ v5_relat_1('#skF_4',k1_xboole_0)
      | ~ v1_relat_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_468,c_771])).

tff(c_786,plain,(
    ! [B_122] :
      ( ~ r2_hidden(B_122,'#skF_3')
      | k1_funct_1('#skF_4','#skF_5'(B_122)) = k1_xboole_0
      | ~ v5_relat_1('#skF_4',k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_173,c_775])).

tff(c_833,plain,(
    ~ v5_relat_1('#skF_4',k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_786])).

tff(c_1118,plain,(
    ~ v5_relat_1('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1108,c_833])).

tff(c_1162,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_275,c_1118])).

tff(c_1164,plain,(
    v5_relat_1('#skF_4',k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_786])).

tff(c_290,plain,(
    ! [A_90] : r1_tarski(k1_xboole_0,A_90) ),
    inference(demodulation,[status(thm),theory(equality)],[c_276,c_222])).

tff(c_8,plain,(
    ! [B_7,A_6] :
      ( B_7 = A_6
      | ~ r1_tarski(B_7,A_6)
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_300,plain,(
    ! [A_91] :
      ( k1_xboole_0 = A_91
      | ~ r1_tarski(A_91,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_290,c_8])).

tff(c_315,plain,(
    ! [B_11] :
      ( k2_relat_1(B_11) = k1_xboole_0
      | ~ v5_relat_1(B_11,k1_xboole_0)
      | ~ v1_relat_1(B_11) ) ),
    inference(resolution,[status(thm)],[c_22,c_300])).

tff(c_1184,plain,
    ( k2_relat_1('#skF_4') = k1_xboole_0
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_1164,c_315])).

tff(c_1192,plain,(
    k2_relat_1('#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_173,c_1184])).

tff(c_1231,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1192,c_548])).

tff(c_1401,plain,(
    ! [B_204,A_205,C_206] :
      ( k1_xboole_0 = B_204
      | k1_relset_1(A_205,B_204,C_206) = A_205
      | ~ v1_funct_2(C_206,A_205,B_204)
      | ~ m1_subset_1(C_206,k1_zfmisc_1(k2_zfmisc_1(A_205,B_204))) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_1404,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relset_1('#skF_2','#skF_3','#skF_4') = '#skF_2'
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_68,c_1401])).

tff(c_1416,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relat_1('#skF_4') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_393,c_1404])).

tff(c_1417,plain,(
    k1_relat_1('#skF_4') = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_1231,c_1416])).

tff(c_1421,plain,(
    ~ r1_tarski('#skF_2','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1417,c_752])).

tff(c_1425,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_1421])).

tff(c_1436,plain,(
    ! [D_207] :
      ( r2_hidden(D_207,k2_relat_1('#skF_4'))
      | ~ r2_hidden(D_207,'#skF_3') ) ),
    inference(splitRight,[status(thm)],[c_748])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_1521,plain,(
    ! [A_218] :
      ( r1_tarski(A_218,k2_relat_1('#skF_4'))
      | ~ r2_hidden('#skF_1'(A_218,k2_relat_1('#skF_4')),'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_1436,c_4])).

tff(c_1531,plain,(
    r1_tarski('#skF_3',k2_relat_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_6,c_1521])).

tff(c_220,plain,(
    ! [B_74,A_75] :
      ( k2_relat_1(B_74) = A_75
      | ~ r1_tarski(A_75,k2_relat_1(B_74))
      | ~ v5_relat_1(B_74,A_75)
      | ~ v1_relat_1(B_74) ) ),
    inference(resolution,[status(thm)],[c_205,c_8])).

tff(c_1539,plain,
    ( k2_relat_1('#skF_4') = '#skF_3'
    | ~ v5_relat_1('#skF_4','#skF_3')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_1531,c_220])).

tff(c_1553,plain,(
    k2_relat_1('#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_173,c_275,c_1539])).

tff(c_1555,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_548,c_1553])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n011.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 18:57:57 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.51/1.59  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.51/1.60  
% 3.51/1.60  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.51/1.60  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k4_tarski > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 3.51/1.60  
% 3.51/1.60  %Foreground sorts:
% 3.51/1.60  
% 3.51/1.60  
% 3.51/1.60  %Background operators:
% 3.51/1.60  
% 3.51/1.60  
% 3.51/1.60  %Foreground operators:
% 3.51/1.60  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 3.51/1.60  tff('#skF_5', type, '#skF_5': $i > $i).
% 3.51/1.60  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.51/1.60  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.51/1.60  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.51/1.60  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 3.51/1.60  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.51/1.60  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.51/1.60  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.51/1.60  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.51/1.60  tff('#skF_2', type, '#skF_2': $i).
% 3.51/1.60  tff('#skF_3', type, '#skF_3': $i).
% 3.51/1.60  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.51/1.60  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.51/1.60  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.51/1.60  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.51/1.60  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.51/1.60  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.51/1.60  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.51/1.60  tff('#skF_4', type, '#skF_4': $i).
% 3.51/1.60  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.51/1.60  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.51/1.60  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.51/1.60  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.51/1.60  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.51/1.60  
% 3.88/1.62  tff(f_143, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((![D]: ~(r2_hidden(D, B) & (![E]: ~(r2_hidden(E, A) & (D = k1_funct_1(C, E)))))) => (k2_relset_1(A, B, C) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t16_funct_2)).
% 3.88/1.62  tff(f_104, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 3.88/1.62  tff(f_90, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.88/1.62  tff(f_96, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.88/1.62  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 3.88/1.62  tff(f_38, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.88/1.62  tff(f_100, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.88/1.62  tff(f_124, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 3.88/1.62  tff(f_81, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r2_hidden(A, k1_relat_1(B)) => r2_hidden(k1_funct_1(B, A), k2_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_funct_1)).
% 3.88/1.62  tff(f_50, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 3.88/1.62  tff(f_106, axiom, (![A, B]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(k2_zfmisc_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t25_relset_1)).
% 3.88/1.62  tff(f_44, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 3.88/1.62  tff(f_52, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 3.88/1.62  tff(f_55, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 3.88/1.62  tff(f_86, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 3.88/1.62  tff(f_73, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B, C]: ((r2_hidden(B, k1_relat_1(A)) => ((C = k1_funct_1(A, B)) <=> r2_hidden(k4_tarski(B, C), A))) & (~r2_hidden(B, k1_relat_1(A)) => ((C = k1_funct_1(A, B)) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_funct_1)).
% 3.88/1.62  tff(c_68, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_143])).
% 3.88/1.62  tff(c_525, plain, (![A_129, B_130, C_131]: (k2_relset_1(A_129, B_130, C_131)=k2_relat_1(C_131) | ~m1_subset_1(C_131, k1_zfmisc_1(k2_zfmisc_1(A_129, B_130))))), inference(cnfTransformation, [status(thm)], [f_104])).
% 3.88/1.62  tff(c_538, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_68, c_525])).
% 3.88/1.62  tff(c_66, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_4')!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_143])).
% 3.88/1.62  tff(c_548, plain, (k2_relat_1('#skF_4')!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_538, c_66])).
% 3.88/1.62  tff(c_162, plain, (![C_64, A_65, B_66]: (v1_relat_1(C_64) | ~m1_subset_1(C_64, k1_zfmisc_1(k2_zfmisc_1(A_65, B_66))))), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.88/1.62  tff(c_173, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_68, c_162])).
% 3.88/1.62  tff(c_262, plain, (![C_82, B_83, A_84]: (v5_relat_1(C_82, B_83) | ~m1_subset_1(C_82, k1_zfmisc_1(k2_zfmisc_1(A_84, B_83))))), inference(cnfTransformation, [status(thm)], [f_96])).
% 3.88/1.62  tff(c_275, plain, (v5_relat_1('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_68, c_262])).
% 3.88/1.62  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.88/1.62  tff(c_12, plain, (![B_7]: (r1_tarski(B_7, B_7))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.88/1.62  tff(c_70, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_143])).
% 3.88/1.62  tff(c_380, plain, (![A_103, B_104, C_105]: (k1_relset_1(A_103, B_104, C_105)=k1_relat_1(C_105) | ~m1_subset_1(C_105, k1_zfmisc_1(k2_zfmisc_1(A_103, B_104))))), inference(cnfTransformation, [status(thm)], [f_100])).
% 3.88/1.62  tff(c_393, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_68, c_380])).
% 3.88/1.62  tff(c_1078, plain, (![B_194, A_195, C_196]: (k1_xboole_0=B_194 | k1_relset_1(A_195, B_194, C_196)=A_195 | ~v1_funct_2(C_196, A_195, B_194) | ~m1_subset_1(C_196, k1_zfmisc_1(k2_zfmisc_1(A_195, B_194))))), inference(cnfTransformation, [status(thm)], [f_124])).
% 3.88/1.62  tff(c_1081, plain, (k1_xboole_0='#skF_3' | k1_relset_1('#skF_2', '#skF_3', '#skF_4')='#skF_2' | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_68, c_1078])).
% 3.88/1.62  tff(c_1093, plain, (k1_xboole_0='#skF_3' | k1_relat_1('#skF_4')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_70, c_393, c_1081])).
% 3.88/1.62  tff(c_1097, plain, (k1_relat_1('#skF_4')='#skF_2'), inference(splitLeft, [status(thm)], [c_1093])).
% 3.88/1.62  tff(c_76, plain, (![D_43]: (r2_hidden('#skF_5'(D_43), '#skF_2') | ~r2_hidden(D_43, '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_143])).
% 3.88/1.62  tff(c_278, plain, (![C_86, B_87, A_88]: (r2_hidden(C_86, B_87) | ~r2_hidden(C_86, A_88) | ~r1_tarski(A_88, B_87))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.88/1.62  tff(c_284, plain, (![D_43, B_87]: (r2_hidden('#skF_5'(D_43), B_87) | ~r1_tarski('#skF_2', B_87) | ~r2_hidden(D_43, '#skF_3'))), inference(resolution, [status(thm)], [c_76, c_278])).
% 3.88/1.62  tff(c_72, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_143])).
% 3.88/1.62  tff(c_74, plain, (![D_43]: (k1_funct_1('#skF_4', '#skF_5'(D_43))=D_43 | ~r2_hidden(D_43, '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_143])).
% 3.88/1.62  tff(c_719, plain, (![B_158, A_159]: (r2_hidden(k1_funct_1(B_158, A_159), k2_relat_1(B_158)) | ~r2_hidden(A_159, k1_relat_1(B_158)) | ~v1_funct_1(B_158) | ~v1_relat_1(B_158))), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.88/1.62  tff(c_730, plain, (![D_43]: (r2_hidden(D_43, k2_relat_1('#skF_4')) | ~r2_hidden('#skF_5'(D_43), k1_relat_1('#skF_4')) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4') | ~r2_hidden(D_43, '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_74, c_719])).
% 3.88/1.62  tff(c_740, plain, (![D_160]: (r2_hidden(D_160, k2_relat_1('#skF_4')) | ~r2_hidden('#skF_5'(D_160), k1_relat_1('#skF_4')) | ~r2_hidden(D_160, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_173, c_72, c_730])).
% 3.88/1.62  tff(c_748, plain, (![D_43]: (r2_hidden(D_43, k2_relat_1('#skF_4')) | ~r1_tarski('#skF_2', k1_relat_1('#skF_4')) | ~r2_hidden(D_43, '#skF_3'))), inference(resolution, [status(thm)], [c_284, c_740])).
% 3.88/1.62  tff(c_752, plain, (~r1_tarski('#skF_2', k1_relat_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_748])).
% 3.88/1.62  tff(c_1102, plain, (~r1_tarski('#skF_2', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1097, c_752])).
% 3.88/1.62  tff(c_1107, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12, c_1102])).
% 3.88/1.62  tff(c_1108, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_1093])).
% 3.88/1.62  tff(c_22, plain, (![B_11, A_10]: (r1_tarski(k2_relat_1(B_11), A_10) | ~v5_relat_1(B_11, A_10) | ~v1_relat_1(B_11))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.88/1.62  tff(c_52, plain, (![A_35, B_36]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(k2_zfmisc_1(A_35, B_36))))), inference(cnfTransformation, [status(thm)], [f_106])).
% 3.88/1.62  tff(c_276, plain, (![B_36]: (v5_relat_1(k1_xboole_0, B_36))), inference(resolution, [status(thm)], [c_52, c_262])).
% 3.88/1.62  tff(c_93, plain, (![A_48]: (k2_zfmisc_1(A_48, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.88/1.62  tff(c_24, plain, (![A_12, B_13]: (v1_relat_1(k2_zfmisc_1(A_12, B_13)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.88/1.62  tff(c_97, plain, (v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_93, c_24])).
% 3.88/1.62  tff(c_26, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.88/1.62  tff(c_205, plain, (![B_74, A_75]: (r1_tarski(k2_relat_1(B_74), A_75) | ~v5_relat_1(B_74, A_75) | ~v1_relat_1(B_74))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.88/1.62  tff(c_217, plain, (![A_75]: (r1_tarski(k1_xboole_0, A_75) | ~v5_relat_1(k1_xboole_0, A_75) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_26, c_205])).
% 3.88/1.62  tff(c_222, plain, (![A_75]: (r1_tarski(k1_xboole_0, A_75) | ~v5_relat_1(k1_xboole_0, A_75))), inference(demodulation, [status(thm), theory('equality')], [c_97, c_217])).
% 3.88/1.62  tff(c_286, plain, (![A_75]: (r1_tarski(k1_xboole_0, A_75))), inference(demodulation, [status(thm), theory('equality')], [c_276, c_222])).
% 3.88/1.62  tff(c_427, plain, (![A_115, B_116, B_117]: (r2_hidden('#skF_1'(A_115, B_116), B_117) | ~r1_tarski(A_115, B_117) | r1_tarski(A_115, B_116))), inference(resolution, [status(thm)], [c_6, c_278])).
% 3.88/1.62  tff(c_40, plain, (![B_22, A_21]: (~r1_tarski(B_22, A_21) | ~r2_hidden(A_21, B_22))), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.88/1.62  tff(c_440, plain, (![B_118, A_119, B_120]: (~r1_tarski(B_118, '#skF_1'(A_119, B_120)) | ~r1_tarski(A_119, B_118) | r1_tarski(A_119, B_120))), inference(resolution, [status(thm)], [c_427, c_40])).
% 3.88/1.62  tff(c_456, plain, (![A_121, B_122]: (~r1_tarski(A_121, k1_xboole_0) | r1_tarski(A_121, B_122))), inference(resolution, [status(thm)], [c_286, c_440])).
% 3.88/1.62  tff(c_468, plain, (![B_11, B_122]: (r1_tarski(k2_relat_1(B_11), B_122) | ~v5_relat_1(B_11, k1_xboole_0) | ~v1_relat_1(B_11))), inference(resolution, [status(thm)], [c_22, c_456])).
% 3.88/1.62  tff(c_36, plain, (![A_14, B_17]: (k1_funct_1(A_14, B_17)=k1_xboole_0 | r2_hidden(B_17, k1_relat_1(A_14)) | ~v1_funct_1(A_14) | ~v1_relat_1(A_14))), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.88/1.62  tff(c_747, plain, (![D_160]: (r2_hidden(D_160, k2_relat_1('#skF_4')) | ~r2_hidden(D_160, '#skF_3') | k1_funct_1('#skF_4', '#skF_5'(D_160))=k1_xboole_0 | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_36, c_740])).
% 3.88/1.62  tff(c_758, plain, (![D_164]: (r2_hidden(D_164, k2_relat_1('#skF_4')) | ~r2_hidden(D_164, '#skF_3') | k1_funct_1('#skF_4', '#skF_5'(D_164))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_173, c_72, c_747])).
% 3.88/1.62  tff(c_771, plain, (![D_165]: (~r1_tarski(k2_relat_1('#skF_4'), D_165) | ~r2_hidden(D_165, '#skF_3') | k1_funct_1('#skF_4', '#skF_5'(D_165))=k1_xboole_0)), inference(resolution, [status(thm)], [c_758, c_40])).
% 3.88/1.62  tff(c_775, plain, (![B_122]: (~r2_hidden(B_122, '#skF_3') | k1_funct_1('#skF_4', '#skF_5'(B_122))=k1_xboole_0 | ~v5_relat_1('#skF_4', k1_xboole_0) | ~v1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_468, c_771])).
% 3.88/1.62  tff(c_786, plain, (![B_122]: (~r2_hidden(B_122, '#skF_3') | k1_funct_1('#skF_4', '#skF_5'(B_122))=k1_xboole_0 | ~v5_relat_1('#skF_4', k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_173, c_775])).
% 3.88/1.62  tff(c_833, plain, (~v5_relat_1('#skF_4', k1_xboole_0)), inference(splitLeft, [status(thm)], [c_786])).
% 3.88/1.62  tff(c_1118, plain, (~v5_relat_1('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1108, c_833])).
% 3.88/1.62  tff(c_1162, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_275, c_1118])).
% 3.88/1.62  tff(c_1164, plain, (v5_relat_1('#skF_4', k1_xboole_0)), inference(splitRight, [status(thm)], [c_786])).
% 3.88/1.62  tff(c_290, plain, (![A_90]: (r1_tarski(k1_xboole_0, A_90))), inference(demodulation, [status(thm), theory('equality')], [c_276, c_222])).
% 3.88/1.62  tff(c_8, plain, (![B_7, A_6]: (B_7=A_6 | ~r1_tarski(B_7, A_6) | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.88/1.62  tff(c_300, plain, (![A_91]: (k1_xboole_0=A_91 | ~r1_tarski(A_91, k1_xboole_0))), inference(resolution, [status(thm)], [c_290, c_8])).
% 3.88/1.62  tff(c_315, plain, (![B_11]: (k2_relat_1(B_11)=k1_xboole_0 | ~v5_relat_1(B_11, k1_xboole_0) | ~v1_relat_1(B_11))), inference(resolution, [status(thm)], [c_22, c_300])).
% 3.88/1.62  tff(c_1184, plain, (k2_relat_1('#skF_4')=k1_xboole_0 | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_1164, c_315])).
% 3.88/1.62  tff(c_1192, plain, (k2_relat_1('#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_173, c_1184])).
% 3.88/1.62  tff(c_1231, plain, (k1_xboole_0!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1192, c_548])).
% 3.88/1.62  tff(c_1401, plain, (![B_204, A_205, C_206]: (k1_xboole_0=B_204 | k1_relset_1(A_205, B_204, C_206)=A_205 | ~v1_funct_2(C_206, A_205, B_204) | ~m1_subset_1(C_206, k1_zfmisc_1(k2_zfmisc_1(A_205, B_204))))), inference(cnfTransformation, [status(thm)], [f_124])).
% 3.88/1.62  tff(c_1404, plain, (k1_xboole_0='#skF_3' | k1_relset_1('#skF_2', '#skF_3', '#skF_4')='#skF_2' | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_68, c_1401])).
% 3.88/1.62  tff(c_1416, plain, (k1_xboole_0='#skF_3' | k1_relat_1('#skF_4')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_70, c_393, c_1404])).
% 3.88/1.62  tff(c_1417, plain, (k1_relat_1('#skF_4')='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_1231, c_1416])).
% 3.88/1.62  tff(c_1421, plain, (~r1_tarski('#skF_2', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1417, c_752])).
% 3.88/1.62  tff(c_1425, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12, c_1421])).
% 3.88/1.62  tff(c_1436, plain, (![D_207]: (r2_hidden(D_207, k2_relat_1('#skF_4')) | ~r2_hidden(D_207, '#skF_3'))), inference(splitRight, [status(thm)], [c_748])).
% 3.88/1.62  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.88/1.62  tff(c_1521, plain, (![A_218]: (r1_tarski(A_218, k2_relat_1('#skF_4')) | ~r2_hidden('#skF_1'(A_218, k2_relat_1('#skF_4')), '#skF_3'))), inference(resolution, [status(thm)], [c_1436, c_4])).
% 3.88/1.62  tff(c_1531, plain, (r1_tarski('#skF_3', k2_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_6, c_1521])).
% 3.88/1.62  tff(c_220, plain, (![B_74, A_75]: (k2_relat_1(B_74)=A_75 | ~r1_tarski(A_75, k2_relat_1(B_74)) | ~v5_relat_1(B_74, A_75) | ~v1_relat_1(B_74))), inference(resolution, [status(thm)], [c_205, c_8])).
% 3.88/1.62  tff(c_1539, plain, (k2_relat_1('#skF_4')='#skF_3' | ~v5_relat_1('#skF_4', '#skF_3') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_1531, c_220])).
% 3.88/1.62  tff(c_1553, plain, (k2_relat_1('#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_173, c_275, c_1539])).
% 3.88/1.62  tff(c_1555, plain, $false, inference(negUnitSimplification, [status(thm)], [c_548, c_1553])).
% 3.88/1.62  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.88/1.62  
% 3.88/1.62  Inference rules
% 3.88/1.62  ----------------------
% 3.88/1.62  #Ref     : 0
% 3.88/1.62  #Sup     : 289
% 3.88/1.62  #Fact    : 0
% 3.88/1.62  #Define  : 0
% 3.88/1.62  #Split   : 10
% 3.88/1.62  #Chain   : 0
% 3.88/1.62  #Close   : 0
% 3.88/1.62  
% 3.88/1.62  Ordering : KBO
% 3.88/1.62  
% 3.88/1.62  Simplification rules
% 3.88/1.62  ----------------------
% 3.88/1.62  #Subsume      : 62
% 3.88/1.62  #Demod        : 287
% 3.88/1.62  #Tautology    : 87
% 3.88/1.62  #SimpNegUnit  : 6
% 3.88/1.62  #BackRed      : 69
% 3.88/1.63  
% 3.88/1.63  #Partial instantiations: 0
% 3.88/1.63  #Strategies tried      : 1
% 3.88/1.63  
% 3.88/1.63  Timing (in seconds)
% 3.88/1.63  ----------------------
% 3.88/1.63  Preprocessing        : 0.34
% 3.88/1.63  Parsing              : 0.17
% 3.88/1.63  CNF conversion       : 0.02
% 3.88/1.63  Main loop            : 0.51
% 3.88/1.63  Inferencing          : 0.17
% 3.88/1.63  Reduction            : 0.16
% 3.88/1.63  Demodulation         : 0.11
% 3.88/1.63  BG Simplification    : 0.02
% 3.88/1.63  Subsumption          : 0.11
% 3.88/1.63  Abstraction          : 0.02
% 3.88/1.63  MUC search           : 0.00
% 3.88/1.63  Cooper               : 0.00
% 3.88/1.63  Total                : 0.89
% 3.88/1.63  Index Insertion      : 0.00
% 3.88/1.63  Index Deletion       : 0.00
% 3.88/1.63  Index Matching       : 0.00
% 3.88/1.63  BG Taut test         : 0.00
%------------------------------------------------------------------------------
