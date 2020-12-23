%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:10:46 EST 2020

% Result     : Theorem 4.81s
% Output     : CNFRefutation 4.81s
% Verified   : 
% Statistics : Number of formulae       :   86 ( 481 expanded)
%              Number of leaves         :   24 ( 167 expanded)
%              Depth                    :   11
%              Number of atoms          :  136 (1274 expanded)
%              Number of equality atoms :   46 ( 466 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_84,negated_conjecture,(
    ~ ! [A] :
        ( ( v1_relat_1(A)
          & v1_funct_1(A) )
       => ( v1_funct_1(A)
          & v1_funct_2(A,k1_relat_1(A),k2_relat_1(A))
          & m1_subset_1(A,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A)))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_funct_2)).

tff(f_47,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => r1_tarski(A,k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_relat_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_33,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_55,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_73,axiom,(
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

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k1_relset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_relset_1)).

tff(c_42,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_3572,plain,(
    ! [A_232] :
      ( r1_tarski(A_232,k2_zfmisc_1(k1_relat_1(A_232),k2_relat_1(A_232)))
      | ~ v1_relat_1(A_232) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_18,plain,(
    ! [A_6,B_7] :
      ( m1_subset_1(A_6,k1_zfmisc_1(B_7))
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_8,plain,(
    ! [A_3] : r1_tarski(k1_xboole_0,A_3) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_12,plain,(
    ! [A_4] : k2_zfmisc_1(A_4,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_20,plain,(
    ! [A_8] :
      ( r1_tarski(A_8,k2_zfmisc_1(k1_relat_1(A_8),k2_relat_1(A_8)))
      | ~ v1_relat_1(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_142,plain,(
    ! [A_35,B_36,C_37] :
      ( k1_relset_1(A_35,B_36,C_37) = k1_relat_1(C_37)
      | ~ m1_subset_1(C_37,k1_zfmisc_1(k2_zfmisc_1(A_35,B_36))) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_353,plain,(
    ! [A_60,B_61,A_62] :
      ( k1_relset_1(A_60,B_61,A_62) = k1_relat_1(A_62)
      | ~ r1_tarski(A_62,k2_zfmisc_1(A_60,B_61)) ) ),
    inference(resolution,[status(thm)],[c_18,c_142])).

tff(c_371,plain,(
    ! [A_8] :
      ( k1_relset_1(k1_relat_1(A_8),k2_relat_1(A_8),A_8) = k1_relat_1(A_8)
      | ~ v1_relat_1(A_8) ) ),
    inference(resolution,[status(thm)],[c_20,c_353])).

tff(c_569,plain,(
    ! [B_82,C_83,A_84] :
      ( k1_xboole_0 = B_82
      | v1_funct_2(C_83,A_84,B_82)
      | k1_relset_1(A_84,B_82,C_83) != A_84
      | ~ m1_subset_1(C_83,k1_zfmisc_1(k2_zfmisc_1(A_84,B_82))) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_927,plain,(
    ! [B_113,A_114,A_115] :
      ( k1_xboole_0 = B_113
      | v1_funct_2(A_114,A_115,B_113)
      | k1_relset_1(A_115,B_113,A_114) != A_115
      | ~ r1_tarski(A_114,k2_zfmisc_1(A_115,B_113)) ) ),
    inference(resolution,[status(thm)],[c_18,c_569])).

tff(c_3139,plain,(
    ! [A_222] :
      ( k2_relat_1(A_222) = k1_xboole_0
      | v1_funct_2(A_222,k1_relat_1(A_222),k2_relat_1(A_222))
      | k1_relset_1(k1_relat_1(A_222),k2_relat_1(A_222),A_222) != k1_relat_1(A_222)
      | ~ v1_relat_1(A_222) ) ),
    inference(resolution,[status(thm)],[c_20,c_927])).

tff(c_40,plain,(
    v1_funct_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_38,plain,
    ( ~ m1_subset_1('#skF_1',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_1'),k2_relat_1('#skF_1'))))
    | ~ v1_funct_2('#skF_1',k1_relat_1('#skF_1'),k2_relat_1('#skF_1'))
    | ~ v1_funct_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_44,plain,
    ( ~ m1_subset_1('#skF_1',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_1'),k2_relat_1('#skF_1'))))
    | ~ v1_funct_2('#skF_1',k1_relat_1('#skF_1'),k2_relat_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38])).

tff(c_91,plain,(
    ~ v1_funct_2('#skF_1',k1_relat_1('#skF_1'),k2_relat_1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_44])).

tff(c_3146,plain,
    ( k2_relat_1('#skF_1') = k1_xboole_0
    | k1_relset_1(k1_relat_1('#skF_1'),k2_relat_1('#skF_1'),'#skF_1') != k1_relat_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_3139,c_91])).

tff(c_3158,plain,
    ( k2_relat_1('#skF_1') = k1_xboole_0
    | k1_relset_1(k1_relat_1('#skF_1'),k2_relat_1('#skF_1'),'#skF_1') != k1_relat_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_3146])).

tff(c_3161,plain,(
    k1_relset_1(k1_relat_1('#skF_1'),k2_relat_1('#skF_1'),'#skF_1') != k1_relat_1('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_3158])).

tff(c_3164,plain,(
    ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_371,c_3161])).

tff(c_3168,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_3164])).

tff(c_3169,plain,(
    k2_relat_1('#skF_1') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_3158])).

tff(c_115,plain,(
    ! [A_31] :
      ( r1_tarski(A_31,k2_zfmisc_1(k1_relat_1(A_31),k2_relat_1(A_31)))
      | ~ v1_relat_1(A_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_118,plain,(
    ! [A_31] :
      ( k2_zfmisc_1(k1_relat_1(A_31),k2_relat_1(A_31)) = A_31
      | ~ r1_tarski(k2_zfmisc_1(k1_relat_1(A_31),k2_relat_1(A_31)),A_31)
      | ~ v1_relat_1(A_31) ) ),
    inference(resolution,[status(thm)],[c_115,c_2])).

tff(c_3178,plain,
    ( k2_zfmisc_1(k1_relat_1('#skF_1'),k2_relat_1('#skF_1')) = '#skF_1'
    | ~ r1_tarski(k2_zfmisc_1(k1_relat_1('#skF_1'),k1_xboole_0),'#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_3169,c_118])).

tff(c_3190,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_8,c_12,c_12,c_3169,c_3178])).

tff(c_26,plain,(
    ! [A_15] :
      ( v1_funct_2(k1_xboole_0,A_15,k1_xboole_0)
      | k1_xboole_0 = A_15
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(A_15,k1_xboole_0))) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_47,plain,(
    ! [A_15] :
      ( v1_funct_2(k1_xboole_0,A_15,k1_xboole_0)
      | k1_xboole_0 = A_15
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_26])).

tff(c_119,plain,(
    ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(splitLeft,[status(thm)],[c_47])).

tff(c_122,plain,(
    ~ r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_18,c_119])).

tff(c_126,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_122])).

tff(c_128,plain,(
    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(splitRight,[status(thm)],[c_47])).

tff(c_14,plain,(
    ! [B_5] : k2_zfmisc_1(k1_xboole_0,B_5) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_180,plain,(
    ! [B_43,C_44] :
      ( k1_relset_1(k1_xboole_0,B_43,C_44) = k1_relat_1(C_44)
      | ~ m1_subset_1(C_44,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_142])).

tff(c_186,plain,(
    ! [B_43] : k1_relset_1(k1_xboole_0,B_43,k1_xboole_0) = k1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_128,c_180])).

tff(c_30,plain,(
    ! [C_17,B_16] :
      ( v1_funct_2(C_17,k1_xboole_0,B_16)
      | k1_relset_1(k1_xboole_0,B_16,C_17) != k1_xboole_0
      | ~ m1_subset_1(C_17,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_16))) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_203,plain,(
    ! [C_46,B_47] :
      ( v1_funct_2(C_46,k1_xboole_0,B_47)
      | k1_relset_1(k1_xboole_0,B_47,C_46) != k1_xboole_0
      | ~ m1_subset_1(C_46,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_30])).

tff(c_205,plain,(
    ! [B_47] :
      ( v1_funct_2(k1_xboole_0,k1_xboole_0,B_47)
      | k1_relset_1(k1_xboole_0,B_47,k1_xboole_0) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_128,c_203])).

tff(c_210,plain,(
    ! [B_47] :
      ( v1_funct_2(k1_xboole_0,k1_xboole_0,B_47)
      | k1_relat_1(k1_xboole_0) != k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_186,c_205])).

tff(c_212,plain,(
    k1_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_210])).

tff(c_224,plain,(
    ! [A_50,B_51,C_52] :
      ( m1_subset_1(k1_relset_1(A_50,B_51,C_52),k1_zfmisc_1(A_50))
      | ~ m1_subset_1(C_52,k1_zfmisc_1(k2_zfmisc_1(A_50,B_51))) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_243,plain,(
    ! [B_43] :
      ( m1_subset_1(k1_relat_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0))
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_43))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_186,c_224])).

tff(c_256,plain,(
    m1_subset_1(k1_relat_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_128,c_14,c_243])).

tff(c_16,plain,(
    ! [A_6,B_7] :
      ( r1_tarski(A_6,B_7)
      | ~ m1_subset_1(A_6,k1_zfmisc_1(B_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_271,plain,(
    r1_tarski(k1_relat_1(k1_xboole_0),k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_256,c_16])).

tff(c_92,plain,(
    ! [B_28,A_29] :
      ( B_28 = A_29
      | ~ r1_tarski(B_28,A_29)
      | ~ r1_tarski(A_29,B_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_101,plain,(
    ! [A_3] :
      ( k1_xboole_0 = A_3
      | ~ r1_tarski(A_3,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_8,c_92])).

tff(c_278,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_271,c_101])).

tff(c_286,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_212,c_278])).

tff(c_287,plain,(
    ! [B_47] : v1_funct_2(k1_xboole_0,k1_xboole_0,B_47) ),
    inference(splitRight,[status(thm)],[c_210])).

tff(c_3236,plain,(
    ! [B_47] : v1_funct_2('#skF_1','#skF_1',B_47) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3190,c_3190,c_287])).

tff(c_288,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_210])).

tff(c_3237,plain,(
    k1_relat_1('#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3190,c_3190,c_288])).

tff(c_3171,plain,(
    ~ v1_funct_2('#skF_1',k1_relat_1('#skF_1'),k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3169,c_91])).

tff(c_3196,plain,(
    ~ v1_funct_2('#skF_1',k1_relat_1('#skF_1'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3190,c_3171])).

tff(c_3552,plain,(
    ~ v1_funct_2('#skF_1','#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3237,c_3196])).

tff(c_3555,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3236,c_3552])).

tff(c_3556,plain,(
    ~ m1_subset_1('#skF_1',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_1'),k2_relat_1('#skF_1')))) ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_3561,plain,(
    ~ r1_tarski('#skF_1',k2_zfmisc_1(k1_relat_1('#skF_1'),k2_relat_1('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_18,c_3556])).

tff(c_3577,plain,(
    ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_3572,c_3561])).

tff(c_3582,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_3577])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n005.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 14:22:02 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.81/1.95  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.81/1.96  
% 4.81/1.96  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.81/1.96  %$ v1_funct_2 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1
% 4.81/1.96  
% 4.81/1.96  %Foreground sorts:
% 4.81/1.96  
% 4.81/1.96  
% 4.81/1.96  %Background operators:
% 4.81/1.96  
% 4.81/1.96  
% 4.81/1.96  %Foreground operators:
% 4.81/1.96  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.81/1.96  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.81/1.96  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.81/1.96  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.81/1.96  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 4.81/1.96  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.81/1.96  tff('#skF_1', type, '#skF_1': $i).
% 4.81/1.96  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 4.81/1.96  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.81/1.96  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.81/1.96  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.81/1.96  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.81/1.96  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.81/1.96  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.81/1.96  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.81/1.96  
% 4.81/1.98  tff(f_84, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => ((v1_funct_1(A) & v1_funct_2(A, k1_relat_1(A), k2_relat_1(A))) & m1_subset_1(A, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_funct_2)).
% 4.81/1.98  tff(f_47, axiom, (![A]: (v1_relat_1(A) => r1_tarski(A, k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t21_relat_1)).
% 4.81/1.98  tff(f_43, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 4.81/1.98  tff(f_33, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 4.81/1.98  tff(f_39, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 4.81/1.98  tff(f_55, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 4.81/1.98  tff(f_73, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 4.81/1.98  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 4.81/1.98  tff(f_51, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k1_relset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_relset_1)).
% 4.81/1.98  tff(c_42, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_84])).
% 4.81/1.98  tff(c_3572, plain, (![A_232]: (r1_tarski(A_232, k2_zfmisc_1(k1_relat_1(A_232), k2_relat_1(A_232))) | ~v1_relat_1(A_232))), inference(cnfTransformation, [status(thm)], [f_47])).
% 4.81/1.98  tff(c_18, plain, (![A_6, B_7]: (m1_subset_1(A_6, k1_zfmisc_1(B_7)) | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.81/1.98  tff(c_8, plain, (![A_3]: (r1_tarski(k1_xboole_0, A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.81/1.98  tff(c_12, plain, (![A_4]: (k2_zfmisc_1(A_4, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.81/1.98  tff(c_20, plain, (![A_8]: (r1_tarski(A_8, k2_zfmisc_1(k1_relat_1(A_8), k2_relat_1(A_8))) | ~v1_relat_1(A_8))), inference(cnfTransformation, [status(thm)], [f_47])).
% 4.81/1.98  tff(c_142, plain, (![A_35, B_36, C_37]: (k1_relset_1(A_35, B_36, C_37)=k1_relat_1(C_37) | ~m1_subset_1(C_37, k1_zfmisc_1(k2_zfmisc_1(A_35, B_36))))), inference(cnfTransformation, [status(thm)], [f_55])).
% 4.81/1.98  tff(c_353, plain, (![A_60, B_61, A_62]: (k1_relset_1(A_60, B_61, A_62)=k1_relat_1(A_62) | ~r1_tarski(A_62, k2_zfmisc_1(A_60, B_61)))), inference(resolution, [status(thm)], [c_18, c_142])).
% 4.81/1.98  tff(c_371, plain, (![A_8]: (k1_relset_1(k1_relat_1(A_8), k2_relat_1(A_8), A_8)=k1_relat_1(A_8) | ~v1_relat_1(A_8))), inference(resolution, [status(thm)], [c_20, c_353])).
% 4.81/1.98  tff(c_569, plain, (![B_82, C_83, A_84]: (k1_xboole_0=B_82 | v1_funct_2(C_83, A_84, B_82) | k1_relset_1(A_84, B_82, C_83)!=A_84 | ~m1_subset_1(C_83, k1_zfmisc_1(k2_zfmisc_1(A_84, B_82))))), inference(cnfTransformation, [status(thm)], [f_73])).
% 4.81/1.98  tff(c_927, plain, (![B_113, A_114, A_115]: (k1_xboole_0=B_113 | v1_funct_2(A_114, A_115, B_113) | k1_relset_1(A_115, B_113, A_114)!=A_115 | ~r1_tarski(A_114, k2_zfmisc_1(A_115, B_113)))), inference(resolution, [status(thm)], [c_18, c_569])).
% 4.81/1.98  tff(c_3139, plain, (![A_222]: (k2_relat_1(A_222)=k1_xboole_0 | v1_funct_2(A_222, k1_relat_1(A_222), k2_relat_1(A_222)) | k1_relset_1(k1_relat_1(A_222), k2_relat_1(A_222), A_222)!=k1_relat_1(A_222) | ~v1_relat_1(A_222))), inference(resolution, [status(thm)], [c_20, c_927])).
% 4.81/1.98  tff(c_40, plain, (v1_funct_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_84])).
% 4.81/1.98  tff(c_38, plain, (~m1_subset_1('#skF_1', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_1'), k2_relat_1('#skF_1')))) | ~v1_funct_2('#skF_1', k1_relat_1('#skF_1'), k2_relat_1('#skF_1')) | ~v1_funct_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_84])).
% 4.81/1.98  tff(c_44, plain, (~m1_subset_1('#skF_1', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_1'), k2_relat_1('#skF_1')))) | ~v1_funct_2('#skF_1', k1_relat_1('#skF_1'), k2_relat_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38])).
% 4.81/1.98  tff(c_91, plain, (~v1_funct_2('#skF_1', k1_relat_1('#skF_1'), k2_relat_1('#skF_1'))), inference(splitLeft, [status(thm)], [c_44])).
% 4.81/1.98  tff(c_3146, plain, (k2_relat_1('#skF_1')=k1_xboole_0 | k1_relset_1(k1_relat_1('#skF_1'), k2_relat_1('#skF_1'), '#skF_1')!=k1_relat_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_3139, c_91])).
% 4.81/1.98  tff(c_3158, plain, (k2_relat_1('#skF_1')=k1_xboole_0 | k1_relset_1(k1_relat_1('#skF_1'), k2_relat_1('#skF_1'), '#skF_1')!=k1_relat_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_3146])).
% 4.81/1.98  tff(c_3161, plain, (k1_relset_1(k1_relat_1('#skF_1'), k2_relat_1('#skF_1'), '#skF_1')!=k1_relat_1('#skF_1')), inference(splitLeft, [status(thm)], [c_3158])).
% 4.81/1.98  tff(c_3164, plain, (~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_371, c_3161])).
% 4.81/1.98  tff(c_3168, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_42, c_3164])).
% 4.81/1.98  tff(c_3169, plain, (k2_relat_1('#skF_1')=k1_xboole_0), inference(splitRight, [status(thm)], [c_3158])).
% 4.81/1.98  tff(c_115, plain, (![A_31]: (r1_tarski(A_31, k2_zfmisc_1(k1_relat_1(A_31), k2_relat_1(A_31))) | ~v1_relat_1(A_31))), inference(cnfTransformation, [status(thm)], [f_47])).
% 4.81/1.98  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.81/1.98  tff(c_118, plain, (![A_31]: (k2_zfmisc_1(k1_relat_1(A_31), k2_relat_1(A_31))=A_31 | ~r1_tarski(k2_zfmisc_1(k1_relat_1(A_31), k2_relat_1(A_31)), A_31) | ~v1_relat_1(A_31))), inference(resolution, [status(thm)], [c_115, c_2])).
% 4.81/1.98  tff(c_3178, plain, (k2_zfmisc_1(k1_relat_1('#skF_1'), k2_relat_1('#skF_1'))='#skF_1' | ~r1_tarski(k2_zfmisc_1(k1_relat_1('#skF_1'), k1_xboole_0), '#skF_1') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_3169, c_118])).
% 4.81/1.98  tff(c_3190, plain, (k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_42, c_8, c_12, c_12, c_3169, c_3178])).
% 4.81/1.98  tff(c_26, plain, (![A_15]: (v1_funct_2(k1_xboole_0, A_15, k1_xboole_0) | k1_xboole_0=A_15 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k2_zfmisc_1(A_15, k1_xboole_0))))), inference(cnfTransformation, [status(thm)], [f_73])).
% 4.81/1.98  tff(c_47, plain, (![A_15]: (v1_funct_2(k1_xboole_0, A_15, k1_xboole_0) | k1_xboole_0=A_15 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_26])).
% 4.81/1.98  tff(c_119, plain, (~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_xboole_0))), inference(splitLeft, [status(thm)], [c_47])).
% 4.81/1.98  tff(c_122, plain, (~r1_tarski(k1_xboole_0, k1_xboole_0)), inference(resolution, [status(thm)], [c_18, c_119])).
% 4.81/1.98  tff(c_126, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_8, c_122])).
% 4.81/1.98  tff(c_128, plain, (m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_xboole_0))), inference(splitRight, [status(thm)], [c_47])).
% 4.81/1.98  tff(c_14, plain, (![B_5]: (k2_zfmisc_1(k1_xboole_0, B_5)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.81/1.98  tff(c_180, plain, (![B_43, C_44]: (k1_relset_1(k1_xboole_0, B_43, C_44)=k1_relat_1(C_44) | ~m1_subset_1(C_44, k1_zfmisc_1(k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_14, c_142])).
% 4.81/1.98  tff(c_186, plain, (![B_43]: (k1_relset_1(k1_xboole_0, B_43, k1_xboole_0)=k1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_128, c_180])).
% 4.81/1.98  tff(c_30, plain, (![C_17, B_16]: (v1_funct_2(C_17, k1_xboole_0, B_16) | k1_relset_1(k1_xboole_0, B_16, C_17)!=k1_xboole_0 | ~m1_subset_1(C_17, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_16))))), inference(cnfTransformation, [status(thm)], [f_73])).
% 4.81/1.98  tff(c_203, plain, (![C_46, B_47]: (v1_funct_2(C_46, k1_xboole_0, B_47) | k1_relset_1(k1_xboole_0, B_47, C_46)!=k1_xboole_0 | ~m1_subset_1(C_46, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_30])).
% 4.81/1.98  tff(c_205, plain, (![B_47]: (v1_funct_2(k1_xboole_0, k1_xboole_0, B_47) | k1_relset_1(k1_xboole_0, B_47, k1_xboole_0)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_128, c_203])).
% 4.81/1.98  tff(c_210, plain, (![B_47]: (v1_funct_2(k1_xboole_0, k1_xboole_0, B_47) | k1_relat_1(k1_xboole_0)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_186, c_205])).
% 4.81/1.98  tff(c_212, plain, (k1_relat_1(k1_xboole_0)!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_210])).
% 4.81/1.98  tff(c_224, plain, (![A_50, B_51, C_52]: (m1_subset_1(k1_relset_1(A_50, B_51, C_52), k1_zfmisc_1(A_50)) | ~m1_subset_1(C_52, k1_zfmisc_1(k2_zfmisc_1(A_50, B_51))))), inference(cnfTransformation, [status(thm)], [f_51])).
% 4.81/1.98  tff(c_243, plain, (![B_43]: (m1_subset_1(k1_relat_1(k1_xboole_0), k1_zfmisc_1(k1_xboole_0)) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_43))))), inference(superposition, [status(thm), theory('equality')], [c_186, c_224])).
% 4.81/1.98  tff(c_256, plain, (m1_subset_1(k1_relat_1(k1_xboole_0), k1_zfmisc_1(k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_128, c_14, c_243])).
% 4.81/1.98  tff(c_16, plain, (![A_6, B_7]: (r1_tarski(A_6, B_7) | ~m1_subset_1(A_6, k1_zfmisc_1(B_7)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.81/1.98  tff(c_271, plain, (r1_tarski(k1_relat_1(k1_xboole_0), k1_xboole_0)), inference(resolution, [status(thm)], [c_256, c_16])).
% 4.81/1.98  tff(c_92, plain, (![B_28, A_29]: (B_28=A_29 | ~r1_tarski(B_28, A_29) | ~r1_tarski(A_29, B_28))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.81/1.98  tff(c_101, plain, (![A_3]: (k1_xboole_0=A_3 | ~r1_tarski(A_3, k1_xboole_0))), inference(resolution, [status(thm)], [c_8, c_92])).
% 4.81/1.98  tff(c_278, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_271, c_101])).
% 4.81/1.98  tff(c_286, plain, $false, inference(negUnitSimplification, [status(thm)], [c_212, c_278])).
% 4.81/1.98  tff(c_287, plain, (![B_47]: (v1_funct_2(k1_xboole_0, k1_xboole_0, B_47))), inference(splitRight, [status(thm)], [c_210])).
% 4.81/1.98  tff(c_3236, plain, (![B_47]: (v1_funct_2('#skF_1', '#skF_1', B_47))), inference(demodulation, [status(thm), theory('equality')], [c_3190, c_3190, c_287])).
% 4.81/1.98  tff(c_288, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(splitRight, [status(thm)], [c_210])).
% 4.81/1.98  tff(c_3237, plain, (k1_relat_1('#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_3190, c_3190, c_288])).
% 4.81/1.98  tff(c_3171, plain, (~v1_funct_2('#skF_1', k1_relat_1('#skF_1'), k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_3169, c_91])).
% 4.81/1.98  tff(c_3196, plain, (~v1_funct_2('#skF_1', k1_relat_1('#skF_1'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_3190, c_3171])).
% 4.81/1.98  tff(c_3552, plain, (~v1_funct_2('#skF_1', '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_3237, c_3196])).
% 4.81/1.98  tff(c_3555, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3236, c_3552])).
% 4.81/1.98  tff(c_3556, plain, (~m1_subset_1('#skF_1', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_1'), k2_relat_1('#skF_1'))))), inference(splitRight, [status(thm)], [c_44])).
% 4.81/1.98  tff(c_3561, plain, (~r1_tarski('#skF_1', k2_zfmisc_1(k1_relat_1('#skF_1'), k2_relat_1('#skF_1')))), inference(resolution, [status(thm)], [c_18, c_3556])).
% 4.81/1.98  tff(c_3577, plain, (~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_3572, c_3561])).
% 4.81/1.98  tff(c_3582, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_42, c_3577])).
% 4.81/1.98  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.81/1.98  
% 4.81/1.98  Inference rules
% 4.81/1.98  ----------------------
% 4.81/1.98  #Ref     : 0
% 4.81/1.98  #Sup     : 759
% 4.81/1.98  #Fact    : 0
% 4.81/1.98  #Define  : 0
% 4.81/1.98  #Split   : 4
% 4.81/1.98  #Chain   : 0
% 4.81/1.98  #Close   : 0
% 4.81/1.98  
% 4.81/1.98  Ordering : KBO
% 4.81/1.98  
% 4.81/1.98  Simplification rules
% 4.81/1.98  ----------------------
% 4.81/1.98  #Subsume      : 93
% 4.81/1.98  #Demod        : 1568
% 4.81/1.98  #Tautology    : 372
% 4.81/1.98  #SimpNegUnit  : 1
% 4.81/1.98  #BackRed      : 58
% 4.81/1.98  
% 4.81/1.98  #Partial instantiations: 0
% 4.81/1.98  #Strategies tried      : 1
% 4.81/1.98  
% 4.81/1.98  Timing (in seconds)
% 4.81/1.98  ----------------------
% 4.81/1.98  Preprocessing        : 0.33
% 4.81/1.98  Parsing              : 0.18
% 4.81/1.98  CNF conversion       : 0.02
% 4.81/1.98  Main loop            : 0.81
% 4.81/1.98  Inferencing          : 0.26
% 4.81/1.98  Reduction            : 0.29
% 4.81/1.98  Demodulation         : 0.23
% 4.81/1.98  BG Simplification    : 0.05
% 4.81/1.98  Subsumption          : 0.15
% 4.81/1.98  Abstraction          : 0.05
% 4.81/1.98  MUC search           : 0.00
% 4.81/1.98  Cooper               : 0.00
% 4.81/1.98  Total                : 1.18
% 4.81/1.98  Index Insertion      : 0.00
% 4.81/1.98  Index Deletion       : 0.00
% 4.81/1.98  Index Matching       : 0.00
% 4.81/1.98  BG Taut test         : 0.00
%------------------------------------------------------------------------------
