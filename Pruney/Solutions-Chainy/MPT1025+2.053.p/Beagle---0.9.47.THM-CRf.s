%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:16:37 EST 2020

% Result     : Theorem 12.21s
% Output     : CNFRefutation 12.21s
% Verified   : 
% Statistics : Number of formulae       :  109 ( 275 expanded)
%              Number of leaves         :   37 ( 108 expanded)
%              Depth                    :   14
%              Number of atoms          :  190 ( 679 expanded)
%              Number of equality atoms :   21 (  78 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k1_relset_1 > k9_relat_1 > k4_tarski > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > #skF_7 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_65,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_117,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ! [E] :
            ~ ( r2_hidden(E,k7_relset_1(A,B,D,C))
              & ! [F] :
                  ( m1_subset_1(F,A)
                 => ~ ( r2_hidden(F,C)
                      & E = k1_funct_1(D,F) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t116_funct_2)).

tff(f_63,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_76,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k9_relat_1(C,B))
      <=> ? [D] :
            ( r2_hidden(D,k1_relat_1(C))
            & r2_hidden(k4_tarski(D,A),C)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t143_relat_1)).

tff(f_98,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_94,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_90,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k1_relset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_relset_1)).

tff(f_56,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

tff(f_49,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_45,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_86,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( r2_hidden(k4_tarski(A,B),C)
      <=> ( r2_hidden(A,k1_relat_1(C))
          & B = k1_funct_1(C,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_funct_1)).

tff(c_24,plain,(
    ! [A_16,B_17] : v1_relat_1(k2_zfmisc_1(A_16,B_17)) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_50,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_87,plain,(
    ! [B_53,A_54] :
      ( v1_relat_1(B_53)
      | ~ m1_subset_1(B_53,k1_zfmisc_1(A_54))
      | ~ v1_relat_1(A_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_97,plain,
    ( v1_relat_1('#skF_6')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_50,c_87])).

tff(c_102,plain,(
    v1_relat_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_97])).

tff(c_40055,plain,(
    ! [A_3521,B_3522,C_3523] :
      ( r2_hidden('#skF_2'(A_3521,B_3522,C_3523),k1_relat_1(C_3523))
      | ~ r2_hidden(A_3521,k9_relat_1(C_3523,B_3522))
      | ~ v1_relat_1(C_3523) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_35210,plain,(
    ! [A_3097,B_3098,C_3099,D_3100] :
      ( k7_relset_1(A_3097,B_3098,C_3099,D_3100) = k9_relat_1(C_3099,D_3100)
      | ~ m1_subset_1(C_3099,k1_zfmisc_1(k2_zfmisc_1(A_3097,B_3098))) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_35229,plain,(
    ! [D_3100] : k7_relset_1('#skF_3','#skF_4','#skF_6',D_3100) = k9_relat_1('#skF_6',D_3100) ),
    inference(resolution,[status(thm)],[c_50,c_35210])).

tff(c_48,plain,(
    r2_hidden('#skF_7',k7_relset_1('#skF_3','#skF_4','#skF_6','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_35234,plain,(
    r2_hidden('#skF_7',k9_relat_1('#skF_6','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_35229,c_48])).

tff(c_34922,plain,(
    ! [A_3055,B_3056,C_3057] :
      ( r2_hidden('#skF_2'(A_3055,B_3056,C_3057),B_3056)
      | ~ r2_hidden(A_3055,k9_relat_1(C_3057,B_3056))
      | ~ v1_relat_1(C_3057) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_46,plain,(
    ! [F_41] :
      ( k1_funct_1('#skF_6',F_41) != '#skF_7'
      | ~ r2_hidden(F_41,'#skF_5')
      | ~ m1_subset_1(F_41,'#skF_3') ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_34937,plain,(
    ! [A_3055,C_3057] :
      ( k1_funct_1('#skF_6','#skF_2'(A_3055,'#skF_5',C_3057)) != '#skF_7'
      | ~ m1_subset_1('#skF_2'(A_3055,'#skF_5',C_3057),'#skF_3')
      | ~ r2_hidden(A_3055,k9_relat_1(C_3057,'#skF_5'))
      | ~ v1_relat_1(C_3057) ) ),
    inference(resolution,[status(thm)],[c_34922,c_46])).

tff(c_35250,plain,
    ( k1_funct_1('#skF_6','#skF_2'('#skF_7','#skF_5','#skF_6')) != '#skF_7'
    | ~ m1_subset_1('#skF_2'('#skF_7','#skF_5','#skF_6'),'#skF_3')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_35234,c_34937])).

tff(c_35263,plain,
    ( k1_funct_1('#skF_6','#skF_2'('#skF_7','#skF_5','#skF_6')) != '#skF_7'
    | ~ m1_subset_1('#skF_2'('#skF_7','#skF_5','#skF_6'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_35250])).

tff(c_35990,plain,(
    ~ m1_subset_1('#skF_2'('#skF_7','#skF_5','#skF_6'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_35263])).

tff(c_219,plain,(
    ! [A_85,B_86,C_87] :
      ( k1_relset_1(A_85,B_86,C_87) = k1_relat_1(C_87)
      | ~ m1_subset_1(C_87,k1_zfmisc_1(k2_zfmisc_1(A_85,B_86))) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_233,plain,(
    k1_relset_1('#skF_3','#skF_4','#skF_6') = k1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_50,c_219])).

tff(c_305,plain,(
    ! [A_96,B_97,C_98] :
      ( m1_subset_1(k1_relset_1(A_96,B_97,C_98),k1_zfmisc_1(A_96))
      | ~ m1_subset_1(C_98,k1_zfmisc_1(k2_zfmisc_1(A_96,B_97))) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_323,plain,
    ( m1_subset_1(k1_relat_1('#skF_6'),k1_zfmisc_1('#skF_3'))
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_233,c_305])).

tff(c_330,plain,(
    m1_subset_1(k1_relat_1('#skF_6'),k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_323])).

tff(c_20,plain,(
    ! [C_12,B_11,A_10] :
      ( ~ v1_xboole_0(C_12)
      | ~ m1_subset_1(B_11,k1_zfmisc_1(C_12))
      | ~ r2_hidden(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_342,plain,(
    ! [A_10] :
      ( ~ v1_xboole_0('#skF_3')
      | ~ r2_hidden(A_10,k1_relat_1('#skF_6')) ) ),
    inference(resolution,[status(thm)],[c_330,c_20])).

tff(c_20240,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_342])).

tff(c_16,plain,(
    ! [A_8,B_9] :
      ( r1_tarski(A_8,B_9)
      | ~ m1_subset_1(A_8,k1_zfmisc_1(B_9)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_344,plain,(
    r1_tarski(k1_relat_1('#skF_6'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_330,c_16])).

tff(c_10,plain,(
    ! [B_7,A_6] :
      ( r2_hidden(B_7,A_6)
      | ~ m1_subset_1(B_7,A_6)
      | v1_xboole_0(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_165,plain,(
    ! [C_73,B_74,A_75] :
      ( r2_hidden(C_73,B_74)
      | ~ r2_hidden(C_73,A_75)
      | ~ r1_tarski(A_75,B_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_20295,plain,(
    ! [B_1813,B_1814,A_1815] :
      ( r2_hidden(B_1813,B_1814)
      | ~ r1_tarski(A_1815,B_1814)
      | ~ m1_subset_1(B_1813,A_1815)
      | v1_xboole_0(A_1815) ) ),
    inference(resolution,[status(thm)],[c_10,c_165])).

tff(c_20304,plain,(
    ! [B_1813] :
      ( r2_hidden(B_1813,'#skF_3')
      | ~ m1_subset_1(B_1813,k1_relat_1('#skF_6'))
      | v1_xboole_0(k1_relat_1('#skF_6')) ) ),
    inference(resolution,[status(thm)],[c_344,c_20295])).

tff(c_26854,plain,(
    v1_xboole_0(k1_relat_1('#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_20304])).

tff(c_27384,plain,(
    ! [A_2518,B_2519,C_2520,D_2521] :
      ( k7_relset_1(A_2518,B_2519,C_2520,D_2521) = k9_relat_1(C_2520,D_2521)
      | ~ m1_subset_1(C_2520,k1_zfmisc_1(k2_zfmisc_1(A_2518,B_2519))) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_27403,plain,(
    ! [D_2521] : k7_relset_1('#skF_3','#skF_4','#skF_6',D_2521) = k9_relat_1('#skF_6',D_2521) ),
    inference(resolution,[status(thm)],[c_50,c_27384])).

tff(c_27409,plain,(
    r2_hidden('#skF_7',k9_relat_1('#skF_6','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_27403,c_48])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_136,plain,(
    ! [A_63,B_64] :
      ( ~ r2_hidden('#skF_1'(A_63,B_64),B_64)
      | r1_tarski(A_63,B_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_146,plain,(
    ! [A_1] : r1_tarski(A_1,A_1) ),
    inference(resolution,[status(thm)],[c_6,c_136])).

tff(c_27292,plain,(
    ! [A_2508,B_2509,C_2510] :
      ( r2_hidden('#skF_2'(A_2508,B_2509,C_2510),k1_relat_1(C_2510))
      | ~ r2_hidden(A_2508,k9_relat_1(C_2510,B_2509))
      | ~ v1_relat_1(C_2510) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_18,plain,(
    ! [A_8,B_9] :
      ( m1_subset_1(A_8,k1_zfmisc_1(B_9))
      | ~ r1_tarski(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_154,plain,(
    ! [C_70,B_71,A_72] :
      ( ~ v1_xboole_0(C_70)
      | ~ m1_subset_1(B_71,k1_zfmisc_1(C_70))
      | ~ r2_hidden(A_72,B_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_163,plain,(
    ! [B_9,A_72,A_8] :
      ( ~ v1_xboole_0(B_9)
      | ~ r2_hidden(A_72,A_8)
      | ~ r1_tarski(A_8,B_9) ) ),
    inference(resolution,[status(thm)],[c_18,c_154])).

tff(c_34437,plain,(
    ! [B_3013,C_3014,A_3015,B_3016] :
      ( ~ v1_xboole_0(B_3013)
      | ~ r1_tarski(k1_relat_1(C_3014),B_3013)
      | ~ r2_hidden(A_3015,k9_relat_1(C_3014,B_3016))
      | ~ v1_relat_1(C_3014) ) ),
    inference(resolution,[status(thm)],[c_27292,c_163])).

tff(c_34717,plain,(
    ! [C_3032,A_3033,B_3034] :
      ( ~ v1_xboole_0(k1_relat_1(C_3032))
      | ~ r2_hidden(A_3033,k9_relat_1(C_3032,B_3034))
      | ~ v1_relat_1(C_3032) ) ),
    inference(resolution,[status(thm)],[c_146,c_34437])).

tff(c_34747,plain,
    ( ~ v1_xboole_0(k1_relat_1('#skF_6'))
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_27409,c_34717])).

tff(c_34774,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_26854,c_34747])).

tff(c_34776,plain,(
    ~ v1_xboole_0(k1_relat_1('#skF_6')) ),
    inference(splitRight,[status(thm)],[c_20304])).

tff(c_35064,plain,(
    ! [A_3076,B_3077,C_3078] :
      ( r2_hidden('#skF_2'(A_3076,B_3077,C_3078),k1_relat_1(C_3078))
      | ~ r2_hidden(A_3076,k9_relat_1(C_3078,B_3077))
      | ~ v1_relat_1(C_3078) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_8,plain,(
    ! [B_7,A_6] :
      ( m1_subset_1(B_7,A_6)
      | ~ r2_hidden(B_7,A_6)
      | v1_xboole_0(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_37971,plain,(
    ! [A_3322,B_3323,C_3324] :
      ( m1_subset_1('#skF_2'(A_3322,B_3323,C_3324),k1_relat_1(C_3324))
      | v1_xboole_0(k1_relat_1(C_3324))
      | ~ r2_hidden(A_3322,k9_relat_1(C_3324,B_3323))
      | ~ v1_relat_1(C_3324) ) ),
    inference(resolution,[status(thm)],[c_35064,c_8])).

tff(c_34775,plain,(
    ! [B_1813] :
      ( r2_hidden(B_1813,'#skF_3')
      | ~ m1_subset_1(B_1813,k1_relat_1('#skF_6')) ) ),
    inference(splitRight,[status(thm)],[c_20304])).

tff(c_37975,plain,(
    ! [A_3322,B_3323] :
      ( r2_hidden('#skF_2'(A_3322,B_3323,'#skF_6'),'#skF_3')
      | v1_xboole_0(k1_relat_1('#skF_6'))
      | ~ r2_hidden(A_3322,k9_relat_1('#skF_6',B_3323))
      | ~ v1_relat_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_37971,c_34775])).

tff(c_37981,plain,(
    ! [A_3322,B_3323] :
      ( r2_hidden('#skF_2'(A_3322,B_3323,'#skF_6'),'#skF_3')
      | v1_xboole_0(k1_relat_1('#skF_6'))
      | ~ r2_hidden(A_3322,k9_relat_1('#skF_6',B_3323)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_37975])).

tff(c_37984,plain,(
    ! [A_3325,B_3326] :
      ( r2_hidden('#skF_2'(A_3325,B_3326,'#skF_6'),'#skF_3')
      | ~ r2_hidden(A_3325,k9_relat_1('#skF_6',B_3326)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_34776,c_37981])).

tff(c_37993,plain,(
    ! [A_3325,B_3326] :
      ( m1_subset_1('#skF_2'(A_3325,B_3326,'#skF_6'),'#skF_3')
      | v1_xboole_0('#skF_3')
      | ~ r2_hidden(A_3325,k9_relat_1('#skF_6',B_3326)) ) ),
    inference(resolution,[status(thm)],[c_37984,c_8])).

tff(c_38000,plain,(
    ! [A_3327,B_3328] :
      ( m1_subset_1('#skF_2'(A_3327,B_3328,'#skF_6'),'#skF_3')
      | ~ r2_hidden(A_3327,k9_relat_1('#skF_6',B_3328)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_20240,c_37993])).

tff(c_38019,plain,(
    m1_subset_1('#skF_2'('#skF_7','#skF_5','#skF_6'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_35234,c_38000])).

tff(c_38045,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_35990,c_38019])).

tff(c_38046,plain,(
    k1_funct_1('#skF_6','#skF_2'('#skF_7','#skF_5','#skF_6')) != '#skF_7' ),
    inference(splitRight,[status(thm)],[c_35263])).

tff(c_54,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_35458,plain,(
    ! [A_3123,B_3124,C_3125] :
      ( r2_hidden(k4_tarski('#skF_2'(A_3123,B_3124,C_3125),A_3123),C_3125)
      | ~ r2_hidden(A_3123,k9_relat_1(C_3125,B_3124))
      | ~ v1_relat_1(C_3125) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_36,plain,(
    ! [C_26,A_24,B_25] :
      ( k1_funct_1(C_26,A_24) = B_25
      | ~ r2_hidden(k4_tarski(A_24,B_25),C_26)
      | ~ v1_funct_1(C_26)
      | ~ v1_relat_1(C_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_39646,plain,(
    ! [C_3460,A_3461,B_3462] :
      ( k1_funct_1(C_3460,'#skF_2'(A_3461,B_3462,C_3460)) = A_3461
      | ~ v1_funct_1(C_3460)
      | ~ r2_hidden(A_3461,k9_relat_1(C_3460,B_3462))
      | ~ v1_relat_1(C_3460) ) ),
    inference(resolution,[status(thm)],[c_35458,c_36])).

tff(c_39659,plain,
    ( k1_funct_1('#skF_6','#skF_2'('#skF_7','#skF_5','#skF_6')) = '#skF_7'
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_35234,c_39646])).

tff(c_39678,plain,(
    k1_funct_1('#skF_6','#skF_2'('#skF_7','#skF_5','#skF_6')) = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_54,c_39659])).

tff(c_39680,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_38046,c_39678])).

tff(c_39681,plain,(
    ! [A_10] : ~ r2_hidden(A_10,k1_relat_1('#skF_6')) ),
    inference(splitRight,[status(thm)],[c_342])).

tff(c_40059,plain,(
    ! [A_3521,B_3522] :
      ( ~ r2_hidden(A_3521,k9_relat_1('#skF_6',B_3522))
      | ~ v1_relat_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_40055,c_39681])).

tff(c_40069,plain,(
    ! [A_3521,B_3522] : ~ r2_hidden(A_3521,k9_relat_1('#skF_6',B_3522)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_40059])).

tff(c_40203,plain,(
    ! [A_3540,B_3541,C_3542,D_3543] :
      ( k7_relset_1(A_3540,B_3541,C_3542,D_3543) = k9_relat_1(C_3542,D_3543)
      | ~ m1_subset_1(C_3542,k1_zfmisc_1(k2_zfmisc_1(A_3540,B_3541))) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_40222,plain,(
    ! [D_3543] : k7_relset_1('#skF_3','#skF_4','#skF_6',D_3543) = k9_relat_1('#skF_6',D_3543) ),
    inference(resolution,[status(thm)],[c_50,c_40203])).

tff(c_40227,plain,(
    r2_hidden('#skF_7',k9_relat_1('#skF_6','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40222,c_48])).

tff(c_40233,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_40069,c_40227])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n002.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 09:38:07 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 12.21/5.51  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 12.21/5.51  
% 12.21/5.51  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 12.21/5.52  %$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k1_relset_1 > k9_relat_1 > k4_tarski > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > #skF_7 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_4 > #skF_1
% 12.21/5.52  
% 12.21/5.52  %Foreground sorts:
% 12.21/5.52  
% 12.21/5.52  
% 12.21/5.52  %Background operators:
% 12.21/5.52  
% 12.21/5.52  
% 12.21/5.52  %Foreground operators:
% 12.21/5.52  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 12.21/5.52  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 12.21/5.52  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 12.21/5.52  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 12.21/5.52  tff('#skF_7', type, '#skF_7': $i).
% 12.21/5.52  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 12.21/5.52  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 12.21/5.52  tff('#skF_5', type, '#skF_5': $i).
% 12.21/5.52  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 12.21/5.52  tff('#skF_6', type, '#skF_6': $i).
% 12.21/5.52  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 12.21/5.52  tff('#skF_3', type, '#skF_3': $i).
% 12.21/5.52  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 12.21/5.52  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 12.21/5.52  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 12.21/5.52  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 12.21/5.52  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 12.21/5.52  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 12.21/5.52  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 12.21/5.52  tff('#skF_4', type, '#skF_4': $i).
% 12.21/5.52  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 12.21/5.52  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 12.21/5.52  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 12.21/5.52  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 12.21/5.52  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 12.21/5.52  
% 12.21/5.53  tff(f_65, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 12.21/5.53  tff(f_117, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: ~(r2_hidden(E, k7_relset_1(A, B, D, C)) & (![F]: (m1_subset_1(F, A) => ~(r2_hidden(F, C) & (E = k1_funct_1(D, F))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t116_funct_2)).
% 12.21/5.53  tff(f_63, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 12.21/5.53  tff(f_76, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k9_relat_1(C, B)) <=> (?[D]: ((r2_hidden(D, k1_relat_1(C)) & r2_hidden(k4_tarski(D, A), C)) & r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t143_relat_1)).
% 12.21/5.53  tff(f_98, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 12.21/5.53  tff(f_94, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 12.21/5.53  tff(f_90, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k1_relset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_relset_1)).
% 12.21/5.53  tff(f_56, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_subset)).
% 12.21/5.53  tff(f_49, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 12.21/5.53  tff(f_45, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 12.21/5.53  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 12.21/5.53  tff(f_86, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(k4_tarski(A, B), C) <=> (r2_hidden(A, k1_relat_1(C)) & (B = k1_funct_1(C, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_funct_1)).
% 12.21/5.53  tff(c_24, plain, (![A_16, B_17]: (v1_relat_1(k2_zfmisc_1(A_16, B_17)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 12.21/5.53  tff(c_50, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_117])).
% 12.21/5.53  tff(c_87, plain, (![B_53, A_54]: (v1_relat_1(B_53) | ~m1_subset_1(B_53, k1_zfmisc_1(A_54)) | ~v1_relat_1(A_54))), inference(cnfTransformation, [status(thm)], [f_63])).
% 12.21/5.53  tff(c_97, plain, (v1_relat_1('#skF_6') | ~v1_relat_1(k2_zfmisc_1('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_50, c_87])).
% 12.21/5.53  tff(c_102, plain, (v1_relat_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_24, c_97])).
% 12.21/5.53  tff(c_40055, plain, (![A_3521, B_3522, C_3523]: (r2_hidden('#skF_2'(A_3521, B_3522, C_3523), k1_relat_1(C_3523)) | ~r2_hidden(A_3521, k9_relat_1(C_3523, B_3522)) | ~v1_relat_1(C_3523))), inference(cnfTransformation, [status(thm)], [f_76])).
% 12.21/5.53  tff(c_35210, plain, (![A_3097, B_3098, C_3099, D_3100]: (k7_relset_1(A_3097, B_3098, C_3099, D_3100)=k9_relat_1(C_3099, D_3100) | ~m1_subset_1(C_3099, k1_zfmisc_1(k2_zfmisc_1(A_3097, B_3098))))), inference(cnfTransformation, [status(thm)], [f_98])).
% 12.21/5.53  tff(c_35229, plain, (![D_3100]: (k7_relset_1('#skF_3', '#skF_4', '#skF_6', D_3100)=k9_relat_1('#skF_6', D_3100))), inference(resolution, [status(thm)], [c_50, c_35210])).
% 12.21/5.53  tff(c_48, plain, (r2_hidden('#skF_7', k7_relset_1('#skF_3', '#skF_4', '#skF_6', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_117])).
% 12.21/5.53  tff(c_35234, plain, (r2_hidden('#skF_7', k9_relat_1('#skF_6', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_35229, c_48])).
% 12.21/5.53  tff(c_34922, plain, (![A_3055, B_3056, C_3057]: (r2_hidden('#skF_2'(A_3055, B_3056, C_3057), B_3056) | ~r2_hidden(A_3055, k9_relat_1(C_3057, B_3056)) | ~v1_relat_1(C_3057))), inference(cnfTransformation, [status(thm)], [f_76])).
% 12.21/5.53  tff(c_46, plain, (![F_41]: (k1_funct_1('#skF_6', F_41)!='#skF_7' | ~r2_hidden(F_41, '#skF_5') | ~m1_subset_1(F_41, '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_117])).
% 12.21/5.53  tff(c_34937, plain, (![A_3055, C_3057]: (k1_funct_1('#skF_6', '#skF_2'(A_3055, '#skF_5', C_3057))!='#skF_7' | ~m1_subset_1('#skF_2'(A_3055, '#skF_5', C_3057), '#skF_3') | ~r2_hidden(A_3055, k9_relat_1(C_3057, '#skF_5')) | ~v1_relat_1(C_3057))), inference(resolution, [status(thm)], [c_34922, c_46])).
% 12.21/5.53  tff(c_35250, plain, (k1_funct_1('#skF_6', '#skF_2'('#skF_7', '#skF_5', '#skF_6'))!='#skF_7' | ~m1_subset_1('#skF_2'('#skF_7', '#skF_5', '#skF_6'), '#skF_3') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_35234, c_34937])).
% 12.21/5.53  tff(c_35263, plain, (k1_funct_1('#skF_6', '#skF_2'('#skF_7', '#skF_5', '#skF_6'))!='#skF_7' | ~m1_subset_1('#skF_2'('#skF_7', '#skF_5', '#skF_6'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_102, c_35250])).
% 12.21/5.53  tff(c_35990, plain, (~m1_subset_1('#skF_2'('#skF_7', '#skF_5', '#skF_6'), '#skF_3')), inference(splitLeft, [status(thm)], [c_35263])).
% 12.21/5.53  tff(c_219, plain, (![A_85, B_86, C_87]: (k1_relset_1(A_85, B_86, C_87)=k1_relat_1(C_87) | ~m1_subset_1(C_87, k1_zfmisc_1(k2_zfmisc_1(A_85, B_86))))), inference(cnfTransformation, [status(thm)], [f_94])).
% 12.21/5.53  tff(c_233, plain, (k1_relset_1('#skF_3', '#skF_4', '#skF_6')=k1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_50, c_219])).
% 12.21/5.53  tff(c_305, plain, (![A_96, B_97, C_98]: (m1_subset_1(k1_relset_1(A_96, B_97, C_98), k1_zfmisc_1(A_96)) | ~m1_subset_1(C_98, k1_zfmisc_1(k2_zfmisc_1(A_96, B_97))))), inference(cnfTransformation, [status(thm)], [f_90])).
% 12.21/5.53  tff(c_323, plain, (m1_subset_1(k1_relat_1('#skF_6'), k1_zfmisc_1('#skF_3')) | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_233, c_305])).
% 12.21/5.53  tff(c_330, plain, (m1_subset_1(k1_relat_1('#skF_6'), k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_323])).
% 12.21/5.53  tff(c_20, plain, (![C_12, B_11, A_10]: (~v1_xboole_0(C_12) | ~m1_subset_1(B_11, k1_zfmisc_1(C_12)) | ~r2_hidden(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_56])).
% 12.21/5.53  tff(c_342, plain, (![A_10]: (~v1_xboole_0('#skF_3') | ~r2_hidden(A_10, k1_relat_1('#skF_6')))), inference(resolution, [status(thm)], [c_330, c_20])).
% 12.21/5.53  tff(c_20240, plain, (~v1_xboole_0('#skF_3')), inference(splitLeft, [status(thm)], [c_342])).
% 12.21/5.53  tff(c_16, plain, (![A_8, B_9]: (r1_tarski(A_8, B_9) | ~m1_subset_1(A_8, k1_zfmisc_1(B_9)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 12.21/5.53  tff(c_344, plain, (r1_tarski(k1_relat_1('#skF_6'), '#skF_3')), inference(resolution, [status(thm)], [c_330, c_16])).
% 12.21/5.53  tff(c_10, plain, (![B_7, A_6]: (r2_hidden(B_7, A_6) | ~m1_subset_1(B_7, A_6) | v1_xboole_0(A_6))), inference(cnfTransformation, [status(thm)], [f_45])).
% 12.21/5.53  tff(c_165, plain, (![C_73, B_74, A_75]: (r2_hidden(C_73, B_74) | ~r2_hidden(C_73, A_75) | ~r1_tarski(A_75, B_74))), inference(cnfTransformation, [status(thm)], [f_32])).
% 12.21/5.53  tff(c_20295, plain, (![B_1813, B_1814, A_1815]: (r2_hidden(B_1813, B_1814) | ~r1_tarski(A_1815, B_1814) | ~m1_subset_1(B_1813, A_1815) | v1_xboole_0(A_1815))), inference(resolution, [status(thm)], [c_10, c_165])).
% 12.21/5.53  tff(c_20304, plain, (![B_1813]: (r2_hidden(B_1813, '#skF_3') | ~m1_subset_1(B_1813, k1_relat_1('#skF_6')) | v1_xboole_0(k1_relat_1('#skF_6')))), inference(resolution, [status(thm)], [c_344, c_20295])).
% 12.21/5.53  tff(c_26854, plain, (v1_xboole_0(k1_relat_1('#skF_6'))), inference(splitLeft, [status(thm)], [c_20304])).
% 12.21/5.53  tff(c_27384, plain, (![A_2518, B_2519, C_2520, D_2521]: (k7_relset_1(A_2518, B_2519, C_2520, D_2521)=k9_relat_1(C_2520, D_2521) | ~m1_subset_1(C_2520, k1_zfmisc_1(k2_zfmisc_1(A_2518, B_2519))))), inference(cnfTransformation, [status(thm)], [f_98])).
% 12.21/5.53  tff(c_27403, plain, (![D_2521]: (k7_relset_1('#skF_3', '#skF_4', '#skF_6', D_2521)=k9_relat_1('#skF_6', D_2521))), inference(resolution, [status(thm)], [c_50, c_27384])).
% 12.21/5.53  tff(c_27409, plain, (r2_hidden('#skF_7', k9_relat_1('#skF_6', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_27403, c_48])).
% 12.21/5.53  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 12.21/5.53  tff(c_136, plain, (![A_63, B_64]: (~r2_hidden('#skF_1'(A_63, B_64), B_64) | r1_tarski(A_63, B_64))), inference(cnfTransformation, [status(thm)], [f_32])).
% 12.21/5.53  tff(c_146, plain, (![A_1]: (r1_tarski(A_1, A_1))), inference(resolution, [status(thm)], [c_6, c_136])).
% 12.21/5.53  tff(c_27292, plain, (![A_2508, B_2509, C_2510]: (r2_hidden('#skF_2'(A_2508, B_2509, C_2510), k1_relat_1(C_2510)) | ~r2_hidden(A_2508, k9_relat_1(C_2510, B_2509)) | ~v1_relat_1(C_2510))), inference(cnfTransformation, [status(thm)], [f_76])).
% 12.21/5.53  tff(c_18, plain, (![A_8, B_9]: (m1_subset_1(A_8, k1_zfmisc_1(B_9)) | ~r1_tarski(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_49])).
% 12.21/5.53  tff(c_154, plain, (![C_70, B_71, A_72]: (~v1_xboole_0(C_70) | ~m1_subset_1(B_71, k1_zfmisc_1(C_70)) | ~r2_hidden(A_72, B_71))), inference(cnfTransformation, [status(thm)], [f_56])).
% 12.21/5.53  tff(c_163, plain, (![B_9, A_72, A_8]: (~v1_xboole_0(B_9) | ~r2_hidden(A_72, A_8) | ~r1_tarski(A_8, B_9))), inference(resolution, [status(thm)], [c_18, c_154])).
% 12.21/5.53  tff(c_34437, plain, (![B_3013, C_3014, A_3015, B_3016]: (~v1_xboole_0(B_3013) | ~r1_tarski(k1_relat_1(C_3014), B_3013) | ~r2_hidden(A_3015, k9_relat_1(C_3014, B_3016)) | ~v1_relat_1(C_3014))), inference(resolution, [status(thm)], [c_27292, c_163])).
% 12.21/5.53  tff(c_34717, plain, (![C_3032, A_3033, B_3034]: (~v1_xboole_0(k1_relat_1(C_3032)) | ~r2_hidden(A_3033, k9_relat_1(C_3032, B_3034)) | ~v1_relat_1(C_3032))), inference(resolution, [status(thm)], [c_146, c_34437])).
% 12.21/5.53  tff(c_34747, plain, (~v1_xboole_0(k1_relat_1('#skF_6')) | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_27409, c_34717])).
% 12.21/5.53  tff(c_34774, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_102, c_26854, c_34747])).
% 12.21/5.53  tff(c_34776, plain, (~v1_xboole_0(k1_relat_1('#skF_6'))), inference(splitRight, [status(thm)], [c_20304])).
% 12.21/5.53  tff(c_35064, plain, (![A_3076, B_3077, C_3078]: (r2_hidden('#skF_2'(A_3076, B_3077, C_3078), k1_relat_1(C_3078)) | ~r2_hidden(A_3076, k9_relat_1(C_3078, B_3077)) | ~v1_relat_1(C_3078))), inference(cnfTransformation, [status(thm)], [f_76])).
% 12.21/5.53  tff(c_8, plain, (![B_7, A_6]: (m1_subset_1(B_7, A_6) | ~r2_hidden(B_7, A_6) | v1_xboole_0(A_6))), inference(cnfTransformation, [status(thm)], [f_45])).
% 12.21/5.53  tff(c_37971, plain, (![A_3322, B_3323, C_3324]: (m1_subset_1('#skF_2'(A_3322, B_3323, C_3324), k1_relat_1(C_3324)) | v1_xboole_0(k1_relat_1(C_3324)) | ~r2_hidden(A_3322, k9_relat_1(C_3324, B_3323)) | ~v1_relat_1(C_3324))), inference(resolution, [status(thm)], [c_35064, c_8])).
% 12.21/5.53  tff(c_34775, plain, (![B_1813]: (r2_hidden(B_1813, '#skF_3') | ~m1_subset_1(B_1813, k1_relat_1('#skF_6')))), inference(splitRight, [status(thm)], [c_20304])).
% 12.21/5.53  tff(c_37975, plain, (![A_3322, B_3323]: (r2_hidden('#skF_2'(A_3322, B_3323, '#skF_6'), '#skF_3') | v1_xboole_0(k1_relat_1('#skF_6')) | ~r2_hidden(A_3322, k9_relat_1('#skF_6', B_3323)) | ~v1_relat_1('#skF_6'))), inference(resolution, [status(thm)], [c_37971, c_34775])).
% 12.21/5.53  tff(c_37981, plain, (![A_3322, B_3323]: (r2_hidden('#skF_2'(A_3322, B_3323, '#skF_6'), '#skF_3') | v1_xboole_0(k1_relat_1('#skF_6')) | ~r2_hidden(A_3322, k9_relat_1('#skF_6', B_3323)))), inference(demodulation, [status(thm), theory('equality')], [c_102, c_37975])).
% 12.21/5.53  tff(c_37984, plain, (![A_3325, B_3326]: (r2_hidden('#skF_2'(A_3325, B_3326, '#skF_6'), '#skF_3') | ~r2_hidden(A_3325, k9_relat_1('#skF_6', B_3326)))), inference(negUnitSimplification, [status(thm)], [c_34776, c_37981])).
% 12.21/5.53  tff(c_37993, plain, (![A_3325, B_3326]: (m1_subset_1('#skF_2'(A_3325, B_3326, '#skF_6'), '#skF_3') | v1_xboole_0('#skF_3') | ~r2_hidden(A_3325, k9_relat_1('#skF_6', B_3326)))), inference(resolution, [status(thm)], [c_37984, c_8])).
% 12.21/5.53  tff(c_38000, plain, (![A_3327, B_3328]: (m1_subset_1('#skF_2'(A_3327, B_3328, '#skF_6'), '#skF_3') | ~r2_hidden(A_3327, k9_relat_1('#skF_6', B_3328)))), inference(negUnitSimplification, [status(thm)], [c_20240, c_37993])).
% 12.21/5.53  tff(c_38019, plain, (m1_subset_1('#skF_2'('#skF_7', '#skF_5', '#skF_6'), '#skF_3')), inference(resolution, [status(thm)], [c_35234, c_38000])).
% 12.21/5.53  tff(c_38045, plain, $false, inference(negUnitSimplification, [status(thm)], [c_35990, c_38019])).
% 12.21/5.53  tff(c_38046, plain, (k1_funct_1('#skF_6', '#skF_2'('#skF_7', '#skF_5', '#skF_6'))!='#skF_7'), inference(splitRight, [status(thm)], [c_35263])).
% 12.21/5.53  tff(c_54, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_117])).
% 12.21/5.53  tff(c_35458, plain, (![A_3123, B_3124, C_3125]: (r2_hidden(k4_tarski('#skF_2'(A_3123, B_3124, C_3125), A_3123), C_3125) | ~r2_hidden(A_3123, k9_relat_1(C_3125, B_3124)) | ~v1_relat_1(C_3125))), inference(cnfTransformation, [status(thm)], [f_76])).
% 12.21/5.53  tff(c_36, plain, (![C_26, A_24, B_25]: (k1_funct_1(C_26, A_24)=B_25 | ~r2_hidden(k4_tarski(A_24, B_25), C_26) | ~v1_funct_1(C_26) | ~v1_relat_1(C_26))), inference(cnfTransformation, [status(thm)], [f_86])).
% 12.21/5.53  tff(c_39646, plain, (![C_3460, A_3461, B_3462]: (k1_funct_1(C_3460, '#skF_2'(A_3461, B_3462, C_3460))=A_3461 | ~v1_funct_1(C_3460) | ~r2_hidden(A_3461, k9_relat_1(C_3460, B_3462)) | ~v1_relat_1(C_3460))), inference(resolution, [status(thm)], [c_35458, c_36])).
% 12.21/5.53  tff(c_39659, plain, (k1_funct_1('#skF_6', '#skF_2'('#skF_7', '#skF_5', '#skF_6'))='#skF_7' | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_35234, c_39646])).
% 12.21/5.53  tff(c_39678, plain, (k1_funct_1('#skF_6', '#skF_2'('#skF_7', '#skF_5', '#skF_6'))='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_102, c_54, c_39659])).
% 12.21/5.53  tff(c_39680, plain, $false, inference(negUnitSimplification, [status(thm)], [c_38046, c_39678])).
% 12.21/5.53  tff(c_39681, plain, (![A_10]: (~r2_hidden(A_10, k1_relat_1('#skF_6')))), inference(splitRight, [status(thm)], [c_342])).
% 12.21/5.53  tff(c_40059, plain, (![A_3521, B_3522]: (~r2_hidden(A_3521, k9_relat_1('#skF_6', B_3522)) | ~v1_relat_1('#skF_6'))), inference(resolution, [status(thm)], [c_40055, c_39681])).
% 12.21/5.53  tff(c_40069, plain, (![A_3521, B_3522]: (~r2_hidden(A_3521, k9_relat_1('#skF_6', B_3522)))), inference(demodulation, [status(thm), theory('equality')], [c_102, c_40059])).
% 12.21/5.53  tff(c_40203, plain, (![A_3540, B_3541, C_3542, D_3543]: (k7_relset_1(A_3540, B_3541, C_3542, D_3543)=k9_relat_1(C_3542, D_3543) | ~m1_subset_1(C_3542, k1_zfmisc_1(k2_zfmisc_1(A_3540, B_3541))))), inference(cnfTransformation, [status(thm)], [f_98])).
% 12.21/5.53  tff(c_40222, plain, (![D_3543]: (k7_relset_1('#skF_3', '#skF_4', '#skF_6', D_3543)=k9_relat_1('#skF_6', D_3543))), inference(resolution, [status(thm)], [c_50, c_40203])).
% 12.21/5.53  tff(c_40227, plain, (r2_hidden('#skF_7', k9_relat_1('#skF_6', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_40222, c_48])).
% 12.21/5.53  tff(c_40233, plain, $false, inference(negUnitSimplification, [status(thm)], [c_40069, c_40227])).
% 12.21/5.53  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 12.21/5.53  
% 12.21/5.53  Inference rules
% 12.21/5.53  ----------------------
% 12.21/5.53  #Ref     : 0
% 12.21/5.53  #Sup     : 8324
% 12.21/5.53  #Fact    : 0
% 12.21/5.53  #Define  : 0
% 12.21/5.53  #Split   : 214
% 12.21/5.53  #Chain   : 0
% 12.21/5.53  #Close   : 0
% 12.21/5.53  
% 12.21/5.53  Ordering : KBO
% 12.21/5.53  
% 12.21/5.53  Simplification rules
% 12.21/5.53  ----------------------
% 12.21/5.53  #Subsume      : 4317
% 12.21/5.53  #Demod        : 2244
% 12.21/5.53  #Tautology    : 1624
% 12.21/5.53  #SimpNegUnit  : 1505
% 12.21/5.53  #BackRed      : 834
% 12.21/5.53  
% 12.21/5.53  #Partial instantiations: 0
% 12.21/5.53  #Strategies tried      : 1
% 12.21/5.53  
% 12.21/5.53  Timing (in seconds)
% 12.21/5.53  ----------------------
% 12.21/5.54  Preprocessing        : 0.33
% 12.21/5.54  Parsing              : 0.18
% 12.21/5.54  CNF conversion       : 0.02
% 12.21/5.54  Main loop            : 4.48
% 12.21/5.54  Inferencing          : 1.36
% 12.21/5.54  Reduction            : 1.47
% 12.21/5.54  Demodulation         : 1.03
% 12.21/5.54  BG Simplification    : 0.12
% 12.21/5.54  Subsumption          : 1.13
% 12.21/5.54  Abstraction          : 0.19
% 12.21/5.54  MUC search           : 0.00
% 12.21/5.54  Cooper               : 0.00
% 12.21/5.54  Total                : 4.85
% 12.21/5.54  Index Insertion      : 0.00
% 12.21/5.54  Index Deletion       : 0.00
% 12.21/5.54  Index Matching       : 0.00
% 12.21/5.54  BG Taut test         : 0.00
%------------------------------------------------------------------------------
