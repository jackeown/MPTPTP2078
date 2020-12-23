%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:10:47 EST 2020

% Result     : Theorem 5.49s
% Output     : CNFRefutation 5.98s
% Verified   : 
% Statistics : Number of formulae       :   88 ( 439 expanded)
%              Number of leaves         :   27 ( 156 expanded)
%              Depth                    :   12
%              Number of atoms          :  136 (1136 expanded)
%              Number of equality atoms :   50 ( 389 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

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

tff(f_91,negated_conjecture,(
    ~ ! [A] :
        ( ( v1_relat_1(A)
          & v1_funct_1(A) )
       => ( v1_funct_1(A)
          & v1_funct_2(A,k1_relat_1(A),k2_relat_1(A))
          & m1_subset_1(A,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A)))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_funct_2)).

tff(f_47,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => r1_tarski(A,k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_relat_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_33,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_58,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_80,axiom,(
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

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_50,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_62,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_54,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k2_relset_1(A,B,C),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_relset_1)).

tff(c_48,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_4420,plain,(
    ! [A_279] :
      ( r1_tarski(A_279,k2_zfmisc_1(k1_relat_1(A_279),k2_relat_1(A_279)))
      | ~ v1_relat_1(A_279) ) ),
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

tff(c_156,plain,(
    ! [A_35,B_36,C_37] :
      ( k1_relset_1(A_35,B_36,C_37) = k1_relat_1(C_37)
      | ~ m1_subset_1(C_37,k1_zfmisc_1(k2_zfmisc_1(A_35,B_36))) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_394,plain,(
    ! [A_71,B_72,A_73] :
      ( k1_relset_1(A_71,B_72,A_73) = k1_relat_1(A_73)
      | ~ r1_tarski(A_73,k2_zfmisc_1(A_71,B_72)) ) ),
    inference(resolution,[status(thm)],[c_18,c_156])).

tff(c_412,plain,(
    ! [A_8] :
      ( k1_relset_1(k1_relat_1(A_8),k2_relat_1(A_8),A_8) = k1_relat_1(A_8)
      | ~ v1_relat_1(A_8) ) ),
    inference(resolution,[status(thm)],[c_20,c_394])).

tff(c_635,plain,(
    ! [B_95,C_96,A_97] :
      ( k1_xboole_0 = B_95
      | v1_funct_2(C_96,A_97,B_95)
      | k1_relset_1(A_97,B_95,C_96) != A_97
      | ~ m1_subset_1(C_96,k1_zfmisc_1(k2_zfmisc_1(A_97,B_95))) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_1133,plain,(
    ! [B_135,A_136,A_137] :
      ( k1_xboole_0 = B_135
      | v1_funct_2(A_136,A_137,B_135)
      | k1_relset_1(A_137,B_135,A_136) != A_137
      | ~ r1_tarski(A_136,k2_zfmisc_1(A_137,B_135)) ) ),
    inference(resolution,[status(thm)],[c_18,c_635])).

tff(c_3859,plain,(
    ! [A_264] :
      ( k2_relat_1(A_264) = k1_xboole_0
      | v1_funct_2(A_264,k1_relat_1(A_264),k2_relat_1(A_264))
      | k1_relset_1(k1_relat_1(A_264),k2_relat_1(A_264),A_264) != k1_relat_1(A_264)
      | ~ v1_relat_1(A_264) ) ),
    inference(resolution,[status(thm)],[c_20,c_1133])).

tff(c_46,plain,(
    v1_funct_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_44,plain,
    ( ~ m1_subset_1('#skF_1',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_1'),k2_relat_1('#skF_1'))))
    | ~ v1_funct_2('#skF_1',k1_relat_1('#skF_1'),k2_relat_1('#skF_1'))
    | ~ v1_funct_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_50,plain,
    ( ~ m1_subset_1('#skF_1',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_1'),k2_relat_1('#skF_1'))))
    | ~ v1_funct_2('#skF_1',k1_relat_1('#skF_1'),k2_relat_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44])).

tff(c_89,plain,(
    ~ v1_funct_2('#skF_1',k1_relat_1('#skF_1'),k2_relat_1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_50])).

tff(c_3866,plain,
    ( k2_relat_1('#skF_1') = k1_xboole_0
    | k1_relset_1(k1_relat_1('#skF_1'),k2_relat_1('#skF_1'),'#skF_1') != k1_relat_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_3859,c_89])).

tff(c_3881,plain,
    ( k2_relat_1('#skF_1') = k1_xboole_0
    | k1_relset_1(k1_relat_1('#skF_1'),k2_relat_1('#skF_1'),'#skF_1') != k1_relat_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_3866])).

tff(c_3886,plain,(
    k1_relset_1(k1_relat_1('#skF_1'),k2_relat_1('#skF_1'),'#skF_1') != k1_relat_1('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_3881])).

tff(c_3889,plain,(
    ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_412,c_3886])).

tff(c_3893,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_3889])).

tff(c_3894,plain,(
    k2_relat_1('#skF_1') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_3881])).

tff(c_129,plain,(
    ! [A_34] :
      ( r1_tarski(A_34,k2_zfmisc_1(k1_relat_1(A_34),k2_relat_1(A_34)))
      | ~ v1_relat_1(A_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_138,plain,(
    ! [A_34] :
      ( k2_zfmisc_1(k1_relat_1(A_34),k2_relat_1(A_34)) = A_34
      | ~ r1_tarski(k2_zfmisc_1(k1_relat_1(A_34),k2_relat_1(A_34)),A_34)
      | ~ v1_relat_1(A_34) ) ),
    inference(resolution,[status(thm)],[c_129,c_2])).

tff(c_3909,plain,
    ( k2_zfmisc_1(k1_relat_1('#skF_1'),k2_relat_1('#skF_1')) = '#skF_1'
    | ~ r1_tarski(k2_zfmisc_1(k1_relat_1('#skF_1'),k1_xboole_0),'#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_3894,c_138])).

tff(c_3928,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_8,c_12,c_12,c_3894,c_3909])).

tff(c_24,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_32,plain,(
    ! [A_18] :
      ( v1_funct_2(k1_xboole_0,A_18,k1_xboole_0)
      | k1_xboole_0 = A_18
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(A_18,k1_xboole_0))) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_53,plain,(
    ! [A_18] :
      ( v1_funct_2(k1_xboole_0,A_18,k1_xboole_0)
      | k1_xboole_0 = A_18
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_32])).

tff(c_141,plain,(
    ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(splitLeft,[status(thm)],[c_53])).

tff(c_144,plain,(
    ~ r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_18,c_141])).

tff(c_148,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_144])).

tff(c_150,plain,(
    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(splitRight,[status(thm)],[c_53])).

tff(c_14,plain,(
    ! [B_5] : k2_zfmisc_1(k1_xboole_0,B_5) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_22,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_205,plain,(
    ! [A_46,B_47,C_48] :
      ( k2_relset_1(A_46,B_47,C_48) = k2_relat_1(C_48)
      | ~ m1_subset_1(C_48,k1_zfmisc_1(k2_zfmisc_1(A_46,B_47))) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_243,plain,(
    ! [B_52,C_53] :
      ( k2_relset_1(k1_xboole_0,B_52,C_53) = k2_relat_1(C_53)
      | ~ m1_subset_1(C_53,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_205])).

tff(c_245,plain,(
    ! [B_52] : k2_relset_1(k1_xboole_0,B_52,k1_xboole_0) = k2_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_150,c_243])).

tff(c_282,plain,(
    ! [B_57] : k2_relset_1(k1_xboole_0,B_57,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_245])).

tff(c_26,plain,(
    ! [A_9,B_10,C_11] :
      ( m1_subset_1(k2_relset_1(A_9,B_10,C_11),k1_zfmisc_1(B_10))
      | ~ m1_subset_1(C_11,k1_zfmisc_1(k2_zfmisc_1(A_9,B_10))) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_287,plain,(
    ! [B_57] :
      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(B_57))
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_57))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_282,c_26])).

tff(c_295,plain,(
    ! [B_58] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(B_58)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_150,c_14,c_287])).

tff(c_28,plain,(
    ! [A_12,B_13,C_14] :
      ( k1_relset_1(A_12,B_13,C_14) = k1_relat_1(C_14)
      | ~ m1_subset_1(C_14,k1_zfmisc_1(k2_zfmisc_1(A_12,B_13))) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_312,plain,(
    ! [A_12,B_13] : k1_relset_1(A_12,B_13,k1_xboole_0) = k1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_295,c_28])).

tff(c_325,plain,(
    ! [A_12,B_13] : k1_relset_1(A_12,B_13,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_312])).

tff(c_292,plain,(
    ! [B_57] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(B_57)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_150,c_14,c_287])).

tff(c_36,plain,(
    ! [C_20,B_19] :
      ( v1_funct_2(C_20,k1_xboole_0,B_19)
      | k1_relset_1(k1_xboole_0,B_19,C_20) != k1_xboole_0
      | ~ m1_subset_1(C_20,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_19))) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_767,plain,(
    ! [C_106,B_107] :
      ( v1_funct_2(C_106,k1_xboole_0,B_107)
      | k1_relset_1(k1_xboole_0,B_107,C_106) != k1_xboole_0
      | ~ m1_subset_1(C_106,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_36])).

tff(c_770,plain,(
    ! [B_107] :
      ( v1_funct_2(k1_xboole_0,k1_xboole_0,B_107)
      | k1_relset_1(k1_xboole_0,B_107,k1_xboole_0) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_292,c_767])).

tff(c_779,plain,(
    ! [B_107] : v1_funct_2(k1_xboole_0,k1_xboole_0,B_107) ),
    inference(demodulation,[status(thm),theory(equality)],[c_325,c_770])).

tff(c_3973,plain,(
    ! [B_107] : v1_funct_2('#skF_1','#skF_1',B_107) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3928,c_3928,c_779])).

tff(c_4001,plain,(
    k1_relat_1('#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3928,c_3928,c_24])).

tff(c_3896,plain,(
    ~ v1_funct_2('#skF_1',k1_relat_1('#skF_1'),k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3894,c_89])).

tff(c_3936,plain,(
    ~ v1_funct_2('#skF_1',k1_relat_1('#skF_1'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3928,c_3896])).

tff(c_4341,plain,(
    ~ v1_funct_2('#skF_1','#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4001,c_3936])).

tff(c_4374,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3973,c_4341])).

tff(c_4375,plain,(
    ~ m1_subset_1('#skF_1',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_1'),k2_relat_1('#skF_1')))) ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_4385,plain,(
    ~ r1_tarski('#skF_1',k2_zfmisc_1(k1_relat_1('#skF_1'),k2_relat_1('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_18,c_4375])).

tff(c_4425,plain,(
    ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_4420,c_4385])).

tff(c_4436,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_4425])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:28:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.49/2.17  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.90/2.18  
% 5.90/2.18  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.90/2.19  %$ v1_funct_2 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1
% 5.90/2.19  
% 5.90/2.19  %Foreground sorts:
% 5.90/2.19  
% 5.90/2.19  
% 5.90/2.19  %Background operators:
% 5.90/2.19  
% 5.90/2.19  
% 5.90/2.19  %Foreground operators:
% 5.90/2.19  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 5.90/2.19  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 5.90/2.19  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.90/2.19  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.90/2.19  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.90/2.19  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 5.90/2.19  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 5.90/2.19  tff('#skF_1', type, '#skF_1': $i).
% 5.90/2.19  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 5.90/2.19  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.90/2.19  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.90/2.19  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.90/2.19  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 5.90/2.19  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.90/2.19  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 5.90/2.19  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.90/2.19  
% 5.98/2.20  tff(f_91, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => ((v1_funct_1(A) & v1_funct_2(A, k1_relat_1(A), k2_relat_1(A))) & m1_subset_1(A, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_funct_2)).
% 5.98/2.20  tff(f_47, axiom, (![A]: (v1_relat_1(A) => r1_tarski(A, k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t21_relat_1)).
% 5.98/2.20  tff(f_43, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 5.98/2.20  tff(f_33, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 5.98/2.20  tff(f_39, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 5.98/2.20  tff(f_58, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 5.98/2.20  tff(f_80, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 5.98/2.20  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 5.98/2.20  tff(f_50, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 5.98/2.20  tff(f_62, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 5.98/2.20  tff(f_54, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k2_relset_1(A, B, C), k1_zfmisc_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_relset_1)).
% 5.98/2.20  tff(c_48, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_91])).
% 5.98/2.20  tff(c_4420, plain, (![A_279]: (r1_tarski(A_279, k2_zfmisc_1(k1_relat_1(A_279), k2_relat_1(A_279))) | ~v1_relat_1(A_279))), inference(cnfTransformation, [status(thm)], [f_47])).
% 5.98/2.20  tff(c_18, plain, (![A_6, B_7]: (m1_subset_1(A_6, k1_zfmisc_1(B_7)) | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_43])).
% 5.98/2.20  tff(c_8, plain, (![A_3]: (r1_tarski(k1_xboole_0, A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 5.98/2.20  tff(c_12, plain, (![A_4]: (k2_zfmisc_1(A_4, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 5.98/2.20  tff(c_20, plain, (![A_8]: (r1_tarski(A_8, k2_zfmisc_1(k1_relat_1(A_8), k2_relat_1(A_8))) | ~v1_relat_1(A_8))), inference(cnfTransformation, [status(thm)], [f_47])).
% 5.98/2.20  tff(c_156, plain, (![A_35, B_36, C_37]: (k1_relset_1(A_35, B_36, C_37)=k1_relat_1(C_37) | ~m1_subset_1(C_37, k1_zfmisc_1(k2_zfmisc_1(A_35, B_36))))), inference(cnfTransformation, [status(thm)], [f_58])).
% 5.98/2.20  tff(c_394, plain, (![A_71, B_72, A_73]: (k1_relset_1(A_71, B_72, A_73)=k1_relat_1(A_73) | ~r1_tarski(A_73, k2_zfmisc_1(A_71, B_72)))), inference(resolution, [status(thm)], [c_18, c_156])).
% 5.98/2.20  tff(c_412, plain, (![A_8]: (k1_relset_1(k1_relat_1(A_8), k2_relat_1(A_8), A_8)=k1_relat_1(A_8) | ~v1_relat_1(A_8))), inference(resolution, [status(thm)], [c_20, c_394])).
% 5.98/2.20  tff(c_635, plain, (![B_95, C_96, A_97]: (k1_xboole_0=B_95 | v1_funct_2(C_96, A_97, B_95) | k1_relset_1(A_97, B_95, C_96)!=A_97 | ~m1_subset_1(C_96, k1_zfmisc_1(k2_zfmisc_1(A_97, B_95))))), inference(cnfTransformation, [status(thm)], [f_80])).
% 5.98/2.20  tff(c_1133, plain, (![B_135, A_136, A_137]: (k1_xboole_0=B_135 | v1_funct_2(A_136, A_137, B_135) | k1_relset_1(A_137, B_135, A_136)!=A_137 | ~r1_tarski(A_136, k2_zfmisc_1(A_137, B_135)))), inference(resolution, [status(thm)], [c_18, c_635])).
% 5.98/2.20  tff(c_3859, plain, (![A_264]: (k2_relat_1(A_264)=k1_xboole_0 | v1_funct_2(A_264, k1_relat_1(A_264), k2_relat_1(A_264)) | k1_relset_1(k1_relat_1(A_264), k2_relat_1(A_264), A_264)!=k1_relat_1(A_264) | ~v1_relat_1(A_264))), inference(resolution, [status(thm)], [c_20, c_1133])).
% 5.98/2.20  tff(c_46, plain, (v1_funct_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_91])).
% 5.98/2.20  tff(c_44, plain, (~m1_subset_1('#skF_1', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_1'), k2_relat_1('#skF_1')))) | ~v1_funct_2('#skF_1', k1_relat_1('#skF_1'), k2_relat_1('#skF_1')) | ~v1_funct_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_91])).
% 5.98/2.20  tff(c_50, plain, (~m1_subset_1('#skF_1', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_1'), k2_relat_1('#skF_1')))) | ~v1_funct_2('#skF_1', k1_relat_1('#skF_1'), k2_relat_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44])).
% 5.98/2.20  tff(c_89, plain, (~v1_funct_2('#skF_1', k1_relat_1('#skF_1'), k2_relat_1('#skF_1'))), inference(splitLeft, [status(thm)], [c_50])).
% 5.98/2.20  tff(c_3866, plain, (k2_relat_1('#skF_1')=k1_xboole_0 | k1_relset_1(k1_relat_1('#skF_1'), k2_relat_1('#skF_1'), '#skF_1')!=k1_relat_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_3859, c_89])).
% 5.98/2.20  tff(c_3881, plain, (k2_relat_1('#skF_1')=k1_xboole_0 | k1_relset_1(k1_relat_1('#skF_1'), k2_relat_1('#skF_1'), '#skF_1')!=k1_relat_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_3866])).
% 5.98/2.20  tff(c_3886, plain, (k1_relset_1(k1_relat_1('#skF_1'), k2_relat_1('#skF_1'), '#skF_1')!=k1_relat_1('#skF_1')), inference(splitLeft, [status(thm)], [c_3881])).
% 5.98/2.20  tff(c_3889, plain, (~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_412, c_3886])).
% 5.98/2.20  tff(c_3893, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_48, c_3889])).
% 5.98/2.20  tff(c_3894, plain, (k2_relat_1('#skF_1')=k1_xboole_0), inference(splitRight, [status(thm)], [c_3881])).
% 5.98/2.20  tff(c_129, plain, (![A_34]: (r1_tarski(A_34, k2_zfmisc_1(k1_relat_1(A_34), k2_relat_1(A_34))) | ~v1_relat_1(A_34))), inference(cnfTransformation, [status(thm)], [f_47])).
% 5.98/2.20  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.98/2.20  tff(c_138, plain, (![A_34]: (k2_zfmisc_1(k1_relat_1(A_34), k2_relat_1(A_34))=A_34 | ~r1_tarski(k2_zfmisc_1(k1_relat_1(A_34), k2_relat_1(A_34)), A_34) | ~v1_relat_1(A_34))), inference(resolution, [status(thm)], [c_129, c_2])).
% 5.98/2.20  tff(c_3909, plain, (k2_zfmisc_1(k1_relat_1('#skF_1'), k2_relat_1('#skF_1'))='#skF_1' | ~r1_tarski(k2_zfmisc_1(k1_relat_1('#skF_1'), k1_xboole_0), '#skF_1') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_3894, c_138])).
% 5.98/2.20  tff(c_3928, plain, (k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_48, c_8, c_12, c_12, c_3894, c_3909])).
% 5.98/2.20  tff(c_24, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_50])).
% 5.98/2.20  tff(c_32, plain, (![A_18]: (v1_funct_2(k1_xboole_0, A_18, k1_xboole_0) | k1_xboole_0=A_18 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k2_zfmisc_1(A_18, k1_xboole_0))))), inference(cnfTransformation, [status(thm)], [f_80])).
% 5.98/2.20  tff(c_53, plain, (![A_18]: (v1_funct_2(k1_xboole_0, A_18, k1_xboole_0) | k1_xboole_0=A_18 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_32])).
% 5.98/2.20  tff(c_141, plain, (~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_xboole_0))), inference(splitLeft, [status(thm)], [c_53])).
% 5.98/2.20  tff(c_144, plain, (~r1_tarski(k1_xboole_0, k1_xboole_0)), inference(resolution, [status(thm)], [c_18, c_141])).
% 5.98/2.20  tff(c_148, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_8, c_144])).
% 5.98/2.20  tff(c_150, plain, (m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_xboole_0))), inference(splitRight, [status(thm)], [c_53])).
% 5.98/2.20  tff(c_14, plain, (![B_5]: (k2_zfmisc_1(k1_xboole_0, B_5)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 5.98/2.20  tff(c_22, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_50])).
% 5.98/2.20  tff(c_205, plain, (![A_46, B_47, C_48]: (k2_relset_1(A_46, B_47, C_48)=k2_relat_1(C_48) | ~m1_subset_1(C_48, k1_zfmisc_1(k2_zfmisc_1(A_46, B_47))))), inference(cnfTransformation, [status(thm)], [f_62])).
% 5.98/2.20  tff(c_243, plain, (![B_52, C_53]: (k2_relset_1(k1_xboole_0, B_52, C_53)=k2_relat_1(C_53) | ~m1_subset_1(C_53, k1_zfmisc_1(k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_14, c_205])).
% 5.98/2.20  tff(c_245, plain, (![B_52]: (k2_relset_1(k1_xboole_0, B_52, k1_xboole_0)=k2_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_150, c_243])).
% 5.98/2.20  tff(c_282, plain, (![B_57]: (k2_relset_1(k1_xboole_0, B_57, k1_xboole_0)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_22, c_245])).
% 5.98/2.20  tff(c_26, plain, (![A_9, B_10, C_11]: (m1_subset_1(k2_relset_1(A_9, B_10, C_11), k1_zfmisc_1(B_10)) | ~m1_subset_1(C_11, k1_zfmisc_1(k2_zfmisc_1(A_9, B_10))))), inference(cnfTransformation, [status(thm)], [f_54])).
% 5.98/2.20  tff(c_287, plain, (![B_57]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(B_57)) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_57))))), inference(superposition, [status(thm), theory('equality')], [c_282, c_26])).
% 5.98/2.20  tff(c_295, plain, (![B_58]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(B_58)))), inference(demodulation, [status(thm), theory('equality')], [c_150, c_14, c_287])).
% 5.98/2.20  tff(c_28, plain, (![A_12, B_13, C_14]: (k1_relset_1(A_12, B_13, C_14)=k1_relat_1(C_14) | ~m1_subset_1(C_14, k1_zfmisc_1(k2_zfmisc_1(A_12, B_13))))), inference(cnfTransformation, [status(thm)], [f_58])).
% 5.98/2.20  tff(c_312, plain, (![A_12, B_13]: (k1_relset_1(A_12, B_13, k1_xboole_0)=k1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_295, c_28])).
% 5.98/2.20  tff(c_325, plain, (![A_12, B_13]: (k1_relset_1(A_12, B_13, k1_xboole_0)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_24, c_312])).
% 5.98/2.20  tff(c_292, plain, (![B_57]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(B_57)))), inference(demodulation, [status(thm), theory('equality')], [c_150, c_14, c_287])).
% 5.98/2.20  tff(c_36, plain, (![C_20, B_19]: (v1_funct_2(C_20, k1_xboole_0, B_19) | k1_relset_1(k1_xboole_0, B_19, C_20)!=k1_xboole_0 | ~m1_subset_1(C_20, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_19))))), inference(cnfTransformation, [status(thm)], [f_80])).
% 5.98/2.20  tff(c_767, plain, (![C_106, B_107]: (v1_funct_2(C_106, k1_xboole_0, B_107) | k1_relset_1(k1_xboole_0, B_107, C_106)!=k1_xboole_0 | ~m1_subset_1(C_106, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_36])).
% 5.98/2.20  tff(c_770, plain, (![B_107]: (v1_funct_2(k1_xboole_0, k1_xboole_0, B_107) | k1_relset_1(k1_xboole_0, B_107, k1_xboole_0)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_292, c_767])).
% 5.98/2.20  tff(c_779, plain, (![B_107]: (v1_funct_2(k1_xboole_0, k1_xboole_0, B_107))), inference(demodulation, [status(thm), theory('equality')], [c_325, c_770])).
% 5.98/2.20  tff(c_3973, plain, (![B_107]: (v1_funct_2('#skF_1', '#skF_1', B_107))), inference(demodulation, [status(thm), theory('equality')], [c_3928, c_3928, c_779])).
% 5.98/2.20  tff(c_4001, plain, (k1_relat_1('#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_3928, c_3928, c_24])).
% 5.98/2.20  tff(c_3896, plain, (~v1_funct_2('#skF_1', k1_relat_1('#skF_1'), k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_3894, c_89])).
% 5.98/2.20  tff(c_3936, plain, (~v1_funct_2('#skF_1', k1_relat_1('#skF_1'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_3928, c_3896])).
% 5.98/2.20  tff(c_4341, plain, (~v1_funct_2('#skF_1', '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_4001, c_3936])).
% 5.98/2.20  tff(c_4374, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3973, c_4341])).
% 5.98/2.20  tff(c_4375, plain, (~m1_subset_1('#skF_1', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_1'), k2_relat_1('#skF_1'))))), inference(splitRight, [status(thm)], [c_50])).
% 5.98/2.20  tff(c_4385, plain, (~r1_tarski('#skF_1', k2_zfmisc_1(k1_relat_1('#skF_1'), k2_relat_1('#skF_1')))), inference(resolution, [status(thm)], [c_18, c_4375])).
% 5.98/2.20  tff(c_4425, plain, (~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_4420, c_4385])).
% 5.98/2.20  tff(c_4436, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_48, c_4425])).
% 5.98/2.20  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.98/2.20  
% 5.98/2.20  Inference rules
% 5.98/2.20  ----------------------
% 5.98/2.20  #Ref     : 0
% 5.98/2.20  #Sup     : 948
% 5.98/2.20  #Fact    : 0
% 5.98/2.20  #Define  : 0
% 5.98/2.20  #Split   : 3
% 5.98/2.20  #Chain   : 0
% 5.98/2.20  #Close   : 0
% 5.98/2.20  
% 5.98/2.20  Ordering : KBO
% 5.98/2.20  
% 5.98/2.20  Simplification rules
% 5.98/2.20  ----------------------
% 5.98/2.20  #Subsume      : 114
% 5.98/2.20  #Demod        : 2005
% 5.98/2.20  #Tautology    : 441
% 5.98/2.20  #SimpNegUnit  : 0
% 5.98/2.20  #BackRed      : 70
% 5.98/2.20  
% 5.98/2.20  #Partial instantiations: 0
% 5.98/2.20  #Strategies tried      : 1
% 5.98/2.20  
% 5.98/2.20  Timing (in seconds)
% 5.98/2.20  ----------------------
% 5.98/2.21  Preprocessing        : 0.36
% 5.98/2.21  Parsing              : 0.20
% 5.98/2.21  CNF conversion       : 0.02
% 5.98/2.21  Main loop            : 1.05
% 5.98/2.21  Inferencing          : 0.33
% 5.98/2.21  Reduction            : 0.38
% 5.98/2.21  Demodulation         : 0.30
% 5.98/2.21  BG Simplification    : 0.05
% 5.98/2.21  Subsumption          : 0.20
% 5.98/2.21  Abstraction          : 0.07
% 5.98/2.21  MUC search           : 0.00
% 5.98/2.21  Cooper               : 0.00
% 5.98/2.21  Total                : 1.45
% 5.98/2.21  Index Insertion      : 0.00
% 5.98/2.21  Index Deletion       : 0.00
% 5.98/2.21  Index Matching       : 0.00
% 5.98/2.21  BG Taut test         : 0.00
%------------------------------------------------------------------------------
