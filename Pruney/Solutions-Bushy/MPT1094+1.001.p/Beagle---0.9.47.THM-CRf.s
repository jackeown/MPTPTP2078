%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1094+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:37:24 EST 2020

% Result     : Theorem 1.98s
% Output     : CNFRefutation 2.11s
% Verified   : 
% Statistics : Number of formulae       :   56 (  71 expanded)
%              Number of leaves         :   26 (  35 expanded)
%              Depth                    :    8
%              Number of atoms          :   98 ( 141 expanded)
%              Number of equality atoms :    5 (   5 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > v1_finset_1 > k9_relat_1 > k9_funct_3 > k7_funct_3 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff(k7_funct_3,type,(
    k7_funct_3: ( $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k9_funct_3,type,(
    k9_funct_3: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

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

tff(v1_finset_1,type,(
    v1_finset_1: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_82,negated_conjecture,(
    ~ ! [A] :
        ( ( v1_relat_1(A)
          & v1_funct_1(A) )
       => ( v1_finset_1(k1_relat_1(A))
        <=> v1_finset_1(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_finset_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( v1_relat_1(k7_funct_3(A,B))
      & v1_funct_1(k7_funct_3(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_funct_3)).

tff(f_51,axiom,(
    ! [A,B] : k9_funct_3(A,B) = k7_funct_3(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_funct_3)).

tff(f_57,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => k9_relat_1(k9_funct_3(k1_relat_1(A),k2_relat_1(A)),A) = k1_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_funct_3)).

tff(f_43,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A)
        & v1_finset_1(B) )
     => v1_finset_1(k9_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc13_finset_1)).

tff(f_69,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_finset_1(k1_relat_1(A))
       => v1_finset_1(k2_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_finset_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( ( v1_finset_1(A)
        & v1_finset_1(B) )
     => v1_finset_1(k2_zfmisc_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc14_finset_1)).

tff(f_61,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => r1_tarski(A,k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_relat_1)).

tff(f_73,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_finset_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_finset_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_finset_1)).

tff(c_26,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_24,plain,(
    v1_funct_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_28,plain,
    ( ~ v1_finset_1('#skF_1')
    | ~ v1_finset_1(k1_relat_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_38,plain,(
    ~ v1_finset_1(k1_relat_1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_28])).

tff(c_34,plain,
    ( v1_finset_1(k1_relat_1('#skF_1'))
    | v1_finset_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_39,plain,(
    v1_finset_1('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_34])).

tff(c_4,plain,(
    ! [A_4,B_5] : v1_relat_1(k7_funct_3(A_4,B_5)) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_6,plain,(
    ! [A_4,B_5] : v1_funct_1(k7_funct_3(A_4,B_5)) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_12,plain,(
    ! [A_10,B_11] : k9_funct_3(A_10,B_11) = k7_funct_3(A_10,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_14,plain,(
    ! [A_12] :
      ( k9_relat_1(k9_funct_3(k1_relat_1(A_12),k2_relat_1(A_12)),A_12) = k1_relat_1(A_12)
      | ~ v1_funct_1(A_12)
      | ~ v1_relat_1(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_80,plain,(
    ! [A_40] :
      ( k9_relat_1(k7_funct_3(k1_relat_1(A_40),k2_relat_1(A_40)),A_40) = k1_relat_1(A_40)
      | ~ v1_funct_1(A_40)
      | ~ v1_relat_1(A_40) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_14])).

tff(c_8,plain,(
    ! [A_6,B_7] :
      ( v1_finset_1(k9_relat_1(A_6,B_7))
      | ~ v1_finset_1(B_7)
      | ~ v1_funct_1(A_6)
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_86,plain,(
    ! [A_40] :
      ( v1_finset_1(k1_relat_1(A_40))
      | ~ v1_finset_1(A_40)
      | ~ v1_funct_1(k7_funct_3(k1_relat_1(A_40),k2_relat_1(A_40)))
      | ~ v1_relat_1(k7_funct_3(k1_relat_1(A_40),k2_relat_1(A_40)))
      | ~ v1_funct_1(A_40)
      | ~ v1_relat_1(A_40) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_80,c_8])).

tff(c_94,plain,(
    ! [A_41] :
      ( v1_finset_1(k1_relat_1(A_41))
      | ~ v1_finset_1(A_41)
      | ~ v1_funct_1(A_41)
      | ~ v1_relat_1(A_41) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_6,c_86])).

tff(c_100,plain,
    ( ~ v1_finset_1('#skF_1')
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_94,c_38])).

tff(c_105,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_24,c_39,c_100])).

tff(c_106,plain,(
    ~ v1_finset_1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_28])).

tff(c_107,plain,(
    v1_finset_1(k1_relat_1('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_28])).

tff(c_18,plain,(
    ! [A_14] :
      ( v1_finset_1(k2_relat_1(A_14))
      | ~ v1_finset_1(k1_relat_1(A_14))
      | ~ v1_funct_1(A_14)
      | ~ v1_relat_1(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_10,plain,(
    ! [A_8,B_9] :
      ( v1_finset_1(k2_zfmisc_1(A_8,B_9))
      | ~ v1_finset_1(B_9)
      | ~ v1_finset_1(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_132,plain,(
    ! [A_54] :
      ( r1_tarski(A_54,k2_zfmisc_1(k1_relat_1(A_54),k2_relat_1(A_54)))
      | ~ v1_relat_1(A_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_22,plain,(
    ! [A_15,B_16] :
      ( m1_subset_1(A_15,k1_zfmisc_1(B_16))
      | ~ r1_tarski(A_15,B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_125,plain,(
    ! [B_48,A_49] :
      ( v1_finset_1(B_48)
      | ~ m1_subset_1(B_48,k1_zfmisc_1(A_49))
      | ~ v1_finset_1(A_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_129,plain,(
    ! [A_15,B_16] :
      ( v1_finset_1(A_15)
      | ~ v1_finset_1(B_16)
      | ~ r1_tarski(A_15,B_16) ) ),
    inference(resolution,[status(thm)],[c_22,c_125])).

tff(c_139,plain,(
    ! [A_58] :
      ( v1_finset_1(A_58)
      | ~ v1_finset_1(k2_zfmisc_1(k1_relat_1(A_58),k2_relat_1(A_58)))
      | ~ v1_relat_1(A_58) ) ),
    inference(resolution,[status(thm)],[c_132,c_129])).

tff(c_144,plain,(
    ! [A_59] :
      ( v1_finset_1(A_59)
      | ~ v1_relat_1(A_59)
      | ~ v1_finset_1(k2_relat_1(A_59))
      | ~ v1_finset_1(k1_relat_1(A_59)) ) ),
    inference(resolution,[status(thm)],[c_10,c_139])).

tff(c_164,plain,(
    ! [A_62] :
      ( v1_finset_1(A_62)
      | ~ v1_finset_1(k1_relat_1(A_62))
      | ~ v1_funct_1(A_62)
      | ~ v1_relat_1(A_62) ) ),
    inference(resolution,[status(thm)],[c_18,c_144])).

tff(c_170,plain,
    ( v1_finset_1('#skF_1')
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_107,c_164])).

tff(c_174,plain,(
    v1_finset_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_24,c_170])).

tff(c_176,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_106,c_174])).

%------------------------------------------------------------------------------
