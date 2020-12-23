%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:11:45 EST 2020

% Result     : Theorem 3.31s
% Output     : CNFRefutation 3.48s
% Verified   : 
% Statistics : Number of formulae       :   99 (1651 expanded)
%              Number of leaves         :   34 ( 607 expanded)
%              Depth                    :   22
%              Number of atoms          :  247 (6169 expanded)
%              Number of equality atoms :   49 (1655 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k5_relat_1 > k4_tarski > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_5 > #skF_2 > #skF_6 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

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

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_156,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ! [E] :
            ( ( v1_relat_1(E)
              & v1_funct_1(E) )
           => ( r2_hidden(C,A)
             => ( B = k1_xboole_0
                | k1_funct_1(k5_relat_1(D,E),C) = k1_funct_1(E,k1_funct_1(D,C)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_funct_2)).

tff(f_40,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_32,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_138,axiom,(
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

tff(f_120,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(B,A)))
     => ( ! [D] :
            ~ ( r2_hidden(D,B)
              & ! [E] : ~ r2_hidden(k4_tarski(D,E),C) )
      <=> k1_relset_1(B,A,C) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_relset_1)).

tff(f_108,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( r2_hidden(k4_tarski(A,B),C)
      <=> ( r2_hidden(A,k1_relat_1(C))
          & B = k1_funct_1(C,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_funct_1)).

tff(f_58,axiom,(
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

tff(f_85,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ! [C] :
          ( ( v1_relat_1(C)
            & v1_funct_1(C) )
         => ( r2_hidden(A,k1_relat_1(k5_relat_1(C,B)))
          <=> ( r2_hidden(A,k1_relat_1(C))
              & r2_hidden(k1_funct_1(C,A),k1_relat_1(B)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_funct_1)).

tff(f_98,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ! [C] :
          ( ( v1_relat_1(C)
            & v1_funct_1(C) )
         => ( r2_hidden(A,k1_relat_1(k5_relat_1(C,B)))
           => k1_funct_1(k5_relat_1(C,B),A) = k1_funct_1(B,k1_funct_1(C,A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_funct_1)).

tff(f_70,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A)
        & v1_relat_1(B)
        & v1_funct_1(B) )
     => ( v1_relat_1(k5_relat_1(A,B))
        & v1_funct_1(k5_relat_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_funct_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(A)
        & v1_relat_1(B) )
     => v1_relat_1(k5_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_relat_1)).

tff(c_60,plain,(
    v1_relat_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_58,plain,(
    v1_funct_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_6,plain,(
    ! [A_6,B_7] : v1_relat_1(k2_zfmisc_1(A_6,B_7)) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_62,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_69,plain,(
    ! [B_47,A_48] :
      ( v1_relat_1(B_47)
      | ~ m1_subset_1(B_47,k1_zfmisc_1(A_48))
      | ~ v1_relat_1(A_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_72,plain,
    ( v1_relat_1('#skF_6')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_62,c_69])).

tff(c_75,plain,(
    v1_relat_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_72])).

tff(c_66,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_54,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_64,plain,(
    v1_funct_2('#skF_6','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_104,plain,(
    ! [B_68,A_69,C_70] :
      ( k1_xboole_0 = B_68
      | k1_relset_1(A_69,B_68,C_70) = A_69
      | ~ v1_funct_2(C_70,A_69,B_68)
      | ~ m1_subset_1(C_70,k1_zfmisc_1(k2_zfmisc_1(A_69,B_68))) ) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_107,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relset_1('#skF_3','#skF_4','#skF_6') = '#skF_3'
    | ~ v1_funct_2('#skF_6','#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_62,c_104])).

tff(c_110,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relset_1('#skF_3','#skF_4','#skF_6') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_107])).

tff(c_111,plain,(
    k1_relset_1('#skF_3','#skF_4','#skF_6') = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_110])).

tff(c_56,plain,(
    r2_hidden('#skF_5','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_158,plain,(
    ! [D_90,A_91,B_92,C_93] :
      ( r2_hidden(k4_tarski(D_90,'#skF_2'(A_91,B_92,C_93,D_90)),C_93)
      | ~ r2_hidden(D_90,B_92)
      | k1_relset_1(B_92,A_91,C_93) != B_92
      | ~ m1_subset_1(C_93,k1_zfmisc_1(k2_zfmisc_1(B_92,A_91))) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_30,plain,(
    ! [C_25,A_23,B_24] :
      ( k1_funct_1(C_25,A_23) = B_24
      | ~ r2_hidden(k4_tarski(A_23,B_24),C_25)
      | ~ v1_funct_1(C_25)
      | ~ v1_relat_1(C_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_405,plain,(
    ! [C_129,D_130,A_131,B_132] :
      ( k1_funct_1(C_129,D_130) = '#skF_2'(A_131,B_132,C_129,D_130)
      | ~ v1_funct_1(C_129)
      | ~ v1_relat_1(C_129)
      | ~ r2_hidden(D_130,B_132)
      | k1_relset_1(B_132,A_131,C_129) != B_132
      | ~ m1_subset_1(C_129,k1_zfmisc_1(k2_zfmisc_1(B_132,A_131))) ) ),
    inference(resolution,[status(thm)],[c_158,c_30])).

tff(c_433,plain,(
    ! [C_133,A_134] :
      ( k1_funct_1(C_133,'#skF_5') = '#skF_2'(A_134,'#skF_3',C_133,'#skF_5')
      | ~ v1_funct_1(C_133)
      | ~ v1_relat_1(C_133)
      | k1_relset_1('#skF_3',A_134,C_133) != '#skF_3'
      | ~ m1_subset_1(C_133,k1_zfmisc_1(k2_zfmisc_1('#skF_3',A_134))) ) ),
    inference(resolution,[status(thm)],[c_56,c_405])).

tff(c_436,plain,
    ( k1_funct_1('#skF_6','#skF_5') = '#skF_2'('#skF_4','#skF_3','#skF_6','#skF_5')
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6')
    | k1_relset_1('#skF_3','#skF_4','#skF_6') != '#skF_3' ),
    inference(resolution,[status(thm)],[c_62,c_433])).

tff(c_439,plain,(
    k1_funct_1('#skF_6','#skF_5') = '#skF_2'('#skF_4','#skF_3','#skF_6','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_111,c_75,c_66,c_436])).

tff(c_14,plain,(
    ! [A_8,B_11] :
      ( k1_funct_1(A_8,B_11) = k1_xboole_0
      | r2_hidden(B_11,k1_relat_1(A_8))
      | ~ v1_funct_1(A_8)
      | ~ v1_relat_1(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_32,plain,(
    ! [A_23,C_25,B_24] :
      ( r2_hidden(A_23,k1_relat_1(C_25))
      | ~ r2_hidden(k4_tarski(A_23,B_24),C_25)
      | ~ v1_funct_1(C_25)
      | ~ v1_relat_1(C_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_218,plain,(
    ! [D_100,C_101,B_102,A_103] :
      ( r2_hidden(D_100,k1_relat_1(C_101))
      | ~ v1_funct_1(C_101)
      | ~ v1_relat_1(C_101)
      | ~ r2_hidden(D_100,B_102)
      | k1_relset_1(B_102,A_103,C_101) != B_102
      | ~ m1_subset_1(C_101,k1_zfmisc_1(k2_zfmisc_1(B_102,A_103))) ) ),
    inference(resolution,[status(thm)],[c_158,c_32])).

tff(c_237,plain,(
    ! [C_104,A_105] :
      ( r2_hidden('#skF_5',k1_relat_1(C_104))
      | ~ v1_funct_1(C_104)
      | ~ v1_relat_1(C_104)
      | k1_relset_1('#skF_3',A_105,C_104) != '#skF_3'
      | ~ m1_subset_1(C_104,k1_zfmisc_1(k2_zfmisc_1('#skF_3',A_105))) ) ),
    inference(resolution,[status(thm)],[c_56,c_218])).

tff(c_240,plain,
    ( r2_hidden('#skF_5',k1_relat_1('#skF_6'))
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6')
    | k1_relset_1('#skF_3','#skF_4','#skF_6') != '#skF_3' ),
    inference(resolution,[status(thm)],[c_62,c_237])).

tff(c_243,plain,(
    r2_hidden('#skF_5',k1_relat_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_111,c_75,c_66,c_240])).

tff(c_20,plain,(
    ! [A_15,C_18,B_16] :
      ( r2_hidden(A_15,k1_relat_1(k5_relat_1(C_18,B_16)))
      | ~ r2_hidden(k1_funct_1(C_18,A_15),k1_relat_1(B_16))
      | ~ r2_hidden(A_15,k1_relat_1(C_18))
      | ~ v1_funct_1(C_18)
      | ~ v1_relat_1(C_18)
      | ~ v1_funct_1(B_16)
      | ~ v1_relat_1(B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_445,plain,(
    ! [B_16] :
      ( r2_hidden('#skF_5',k1_relat_1(k5_relat_1('#skF_6',B_16)))
      | ~ r2_hidden('#skF_2'('#skF_4','#skF_3','#skF_6','#skF_5'),k1_relat_1(B_16))
      | ~ r2_hidden('#skF_5',k1_relat_1('#skF_6'))
      | ~ v1_funct_1('#skF_6')
      | ~ v1_relat_1('#skF_6')
      | ~ v1_funct_1(B_16)
      | ~ v1_relat_1(B_16) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_439,c_20])).

tff(c_481,plain,(
    ! [B_141] :
      ( r2_hidden('#skF_5',k1_relat_1(k5_relat_1('#skF_6',B_141)))
      | ~ r2_hidden('#skF_2'('#skF_4','#skF_3','#skF_6','#skF_5'),k1_relat_1(B_141))
      | ~ v1_funct_1(B_141)
      | ~ v1_relat_1(B_141) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_75,c_66,c_243,c_445])).

tff(c_523,plain,(
    ! [A_143] :
      ( r2_hidden('#skF_5',k1_relat_1(k5_relat_1('#skF_6',A_143)))
      | k1_funct_1(A_143,'#skF_2'('#skF_4','#skF_3','#skF_6','#skF_5')) = k1_xboole_0
      | ~ v1_funct_1(A_143)
      | ~ v1_relat_1(A_143) ) ),
    inference(resolution,[status(thm)],[c_14,c_481])).

tff(c_26,plain,(
    ! [C_22,B_20,A_19] :
      ( k1_funct_1(k5_relat_1(C_22,B_20),A_19) = k1_funct_1(B_20,k1_funct_1(C_22,A_19))
      | ~ r2_hidden(A_19,k1_relat_1(k5_relat_1(C_22,B_20)))
      | ~ v1_funct_1(C_22)
      | ~ v1_relat_1(C_22)
      | ~ v1_funct_1(B_20)
      | ~ v1_relat_1(B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_528,plain,(
    ! [A_143] :
      ( k1_funct_1(k5_relat_1('#skF_6',A_143),'#skF_5') = k1_funct_1(A_143,k1_funct_1('#skF_6','#skF_5'))
      | ~ v1_funct_1('#skF_6')
      | ~ v1_relat_1('#skF_6')
      | k1_funct_1(A_143,'#skF_2'('#skF_4','#skF_3','#skF_6','#skF_5')) = k1_xboole_0
      | ~ v1_funct_1(A_143)
      | ~ v1_relat_1(A_143) ) ),
    inference(resolution,[status(thm)],[c_523,c_26])).

tff(c_587,plain,(
    ! [A_146] :
      ( k1_funct_1(k5_relat_1('#skF_6',A_146),'#skF_5') = k1_funct_1(A_146,'#skF_2'('#skF_4','#skF_3','#skF_6','#skF_5'))
      | k1_funct_1(A_146,'#skF_2'('#skF_4','#skF_3','#skF_6','#skF_5')) = k1_xboole_0
      | ~ v1_funct_1(A_146)
      | ~ v1_relat_1(A_146) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_75,c_66,c_439,c_528])).

tff(c_52,plain,(
    k1_funct_1(k5_relat_1('#skF_6','#skF_7'),'#skF_5') != k1_funct_1('#skF_7',k1_funct_1('#skF_6','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_441,plain,(
    k1_funct_1(k5_relat_1('#skF_6','#skF_7'),'#skF_5') != k1_funct_1('#skF_7','#skF_2'('#skF_4','#skF_3','#skF_6','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_439,c_52])).

tff(c_593,plain,
    ( k1_funct_1('#skF_7','#skF_2'('#skF_4','#skF_3','#skF_6','#skF_5')) = k1_xboole_0
    | ~ v1_funct_1('#skF_7')
    | ~ v1_relat_1('#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_587,c_441])).

tff(c_616,plain,(
    k1_funct_1('#skF_7','#skF_2'('#skF_4','#skF_3','#skF_6','#skF_5')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_593])).

tff(c_627,plain,(
    k1_funct_1(k5_relat_1('#skF_6','#skF_7'),'#skF_5') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_616,c_441])).

tff(c_16,plain,(
    ! [A_13,B_14] :
      ( v1_funct_1(k5_relat_1(A_13,B_14))
      | ~ v1_funct_1(B_14)
      | ~ v1_relat_1(B_14)
      | ~ v1_funct_1(A_13)
      | ~ v1_relat_1(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_4,plain,(
    ! [A_4,B_5] :
      ( v1_relat_1(k5_relat_1(A_4,B_5))
      | ~ v1_relat_1(B_5)
      | ~ v1_relat_1(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_22,plain,(
    ! [C_18,A_15,B_16] :
      ( r2_hidden(k1_funct_1(C_18,A_15),k1_relat_1(B_16))
      | ~ r2_hidden(A_15,k1_relat_1(k5_relat_1(C_18,B_16)))
      | ~ v1_funct_1(C_18)
      | ~ v1_relat_1(C_18)
      | ~ v1_funct_1(B_16)
      | ~ v1_relat_1(B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_448,plain,(
    ! [B_16] :
      ( r2_hidden('#skF_2'('#skF_4','#skF_3','#skF_6','#skF_5'),k1_relat_1(B_16))
      | ~ r2_hidden('#skF_5',k1_relat_1(k5_relat_1('#skF_6',B_16)))
      | ~ v1_funct_1('#skF_6')
      | ~ v1_relat_1('#skF_6')
      | ~ v1_funct_1(B_16)
      | ~ v1_relat_1(B_16) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_439,c_22])).

tff(c_457,plain,(
    ! [B_16] :
      ( r2_hidden('#skF_2'('#skF_4','#skF_3','#skF_6','#skF_5'),k1_relat_1(B_16))
      | ~ r2_hidden('#skF_5',k1_relat_1(k5_relat_1('#skF_6',B_16)))
      | ~ v1_funct_1(B_16)
      | ~ v1_relat_1(B_16) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_75,c_66,c_448])).

tff(c_28,plain,(
    ! [A_23,C_25] :
      ( r2_hidden(k4_tarski(A_23,k1_funct_1(C_25,A_23)),C_25)
      | ~ r2_hidden(A_23,k1_relat_1(C_25))
      | ~ v1_funct_1(C_25)
      | ~ v1_relat_1(C_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_637,plain,
    ( r2_hidden(k4_tarski('#skF_2'('#skF_4','#skF_3','#skF_6','#skF_5'),k1_xboole_0),'#skF_7')
    | ~ r2_hidden('#skF_2'('#skF_4','#skF_3','#skF_6','#skF_5'),k1_relat_1('#skF_7'))
    | ~ v1_funct_1('#skF_7')
    | ~ v1_relat_1('#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_616,c_28])).

tff(c_645,plain,
    ( r2_hidden(k4_tarski('#skF_2'('#skF_4','#skF_3','#skF_6','#skF_5'),k1_xboole_0),'#skF_7')
    | ~ r2_hidden('#skF_2'('#skF_4','#skF_3','#skF_6','#skF_5'),k1_relat_1('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_637])).

tff(c_653,plain,(
    ~ r2_hidden('#skF_2'('#skF_4','#skF_3','#skF_6','#skF_5'),k1_relat_1('#skF_7')) ),
    inference(splitLeft,[status(thm)],[c_645])).

tff(c_676,plain,
    ( ~ r2_hidden('#skF_5',k1_relat_1(k5_relat_1('#skF_6','#skF_7')))
    | ~ v1_funct_1('#skF_7')
    | ~ v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_457,c_653])).

tff(c_685,plain,(
    ~ r2_hidden('#skF_5',k1_relat_1(k5_relat_1('#skF_6','#skF_7'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_676])).

tff(c_706,plain,
    ( k1_funct_1(k5_relat_1('#skF_6','#skF_7'),'#skF_5') = k1_xboole_0
    | ~ v1_funct_1(k5_relat_1('#skF_6','#skF_7'))
    | ~ v1_relat_1(k5_relat_1('#skF_6','#skF_7')) ),
    inference(resolution,[status(thm)],[c_14,c_685])).

tff(c_719,plain,
    ( ~ v1_funct_1(k5_relat_1('#skF_6','#skF_7'))
    | ~ v1_relat_1(k5_relat_1('#skF_6','#skF_7')) ),
    inference(negUnitSimplification,[status(thm)],[c_627,c_706])).

tff(c_720,plain,(
    ~ v1_relat_1(k5_relat_1('#skF_6','#skF_7')) ),
    inference(splitLeft,[status(thm)],[c_719])).

tff(c_723,plain,
    ( ~ v1_relat_1('#skF_7')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_4,c_720])).

tff(c_727,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_75,c_60,c_723])).

tff(c_728,plain,(
    ~ v1_funct_1(k5_relat_1('#skF_6','#skF_7')) ),
    inference(splitRight,[status(thm)],[c_719])).

tff(c_741,plain,
    ( ~ v1_funct_1('#skF_7')
    | ~ v1_relat_1('#skF_7')
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_16,c_728])).

tff(c_745,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_75,c_66,c_60,c_58,c_741])).

tff(c_747,plain,(
    r2_hidden('#skF_2'('#skF_4','#skF_3','#skF_6','#skF_5'),k1_relat_1('#skF_7')) ),
    inference(splitRight,[status(thm)],[c_645])).

tff(c_455,plain,(
    ! [B_16] :
      ( r2_hidden('#skF_5',k1_relat_1(k5_relat_1('#skF_6',B_16)))
      | ~ r2_hidden('#skF_2'('#skF_4','#skF_3','#skF_6','#skF_5'),k1_relat_1(B_16))
      | ~ v1_funct_1(B_16)
      | ~ v1_relat_1(B_16) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_75,c_66,c_243,c_445])).

tff(c_750,plain,
    ( r2_hidden('#skF_5',k1_relat_1(k5_relat_1('#skF_6','#skF_7')))
    | ~ v1_funct_1('#skF_7')
    | ~ v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_747,c_455])).

tff(c_757,plain,(
    r2_hidden('#skF_5',k1_relat_1(k5_relat_1('#skF_6','#skF_7'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_750])).

tff(c_764,plain,
    ( k1_funct_1(k5_relat_1('#skF_6','#skF_7'),'#skF_5') = k1_funct_1('#skF_7',k1_funct_1('#skF_6','#skF_5'))
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6')
    | ~ v1_funct_1('#skF_7')
    | ~ v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_757,c_26])).

tff(c_773,plain,(
    k1_funct_1(k5_relat_1('#skF_6','#skF_7'),'#skF_5') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_75,c_66,c_616,c_439,c_764])).

tff(c_775,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_627,c_773])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:26:01 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.31/1.53  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.31/1.54  
% 3.31/1.54  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.31/1.54  %$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k5_relat_1 > k4_tarski > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_5 > #skF_2 > #skF_6 > #skF_3 > #skF_4
% 3.31/1.54  
% 3.31/1.54  %Foreground sorts:
% 3.31/1.54  
% 3.31/1.54  
% 3.31/1.54  %Background operators:
% 3.31/1.54  
% 3.31/1.54  
% 3.31/1.54  %Foreground operators:
% 3.31/1.54  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 3.31/1.54  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.31/1.54  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.31/1.54  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.31/1.54  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 3.31/1.54  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.31/1.54  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 3.31/1.54  tff('#skF_7', type, '#skF_7': $i).
% 3.31/1.54  tff('#skF_5', type, '#skF_5': $i).
% 3.31/1.54  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.31/1.54  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 3.31/1.54  tff('#skF_6', type, '#skF_6': $i).
% 3.31/1.54  tff('#skF_3', type, '#skF_3': $i).
% 3.31/1.54  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.31/1.54  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.31/1.54  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.31/1.54  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.31/1.54  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.31/1.54  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.31/1.54  tff('#skF_4', type, '#skF_4': $i).
% 3.31/1.54  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.31/1.54  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.31/1.54  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.31/1.54  
% 3.48/1.56  tff(f_156, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: ((v1_relat_1(E) & v1_funct_1(E)) => (r2_hidden(C, A) => ((B = k1_xboole_0) | (k1_funct_1(k5_relat_1(D, E), C) = k1_funct_1(E, k1_funct_1(D, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t21_funct_2)).
% 3.48/1.56  tff(f_40, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 3.48/1.56  tff(f_32, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 3.48/1.56  tff(f_138, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 3.48/1.56  tff(f_120, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => ((![D]: ~(r2_hidden(D, B) & (![E]: ~r2_hidden(k4_tarski(D, E), C)))) <=> (k1_relset_1(B, A, C) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t22_relset_1)).
% 3.48/1.56  tff(f_108, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(k4_tarski(A, B), C) <=> (r2_hidden(A, k1_relat_1(C)) & (B = k1_funct_1(C, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_funct_1)).
% 3.48/1.56  tff(f_58, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B, C]: ((r2_hidden(B, k1_relat_1(A)) => ((C = k1_funct_1(A, B)) <=> r2_hidden(k4_tarski(B, C), A))) & (~r2_hidden(B, k1_relat_1(A)) => ((C = k1_funct_1(A, B)) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_funct_1)).
% 3.48/1.56  tff(f_85, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (![C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(A, k1_relat_1(k5_relat_1(C, B))) <=> (r2_hidden(A, k1_relat_1(C)) & r2_hidden(k1_funct_1(C, A), k1_relat_1(B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t21_funct_1)).
% 3.48/1.56  tff(f_98, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (![C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(A, k1_relat_1(k5_relat_1(C, B))) => (k1_funct_1(k5_relat_1(C, B), A) = k1_funct_1(B, k1_funct_1(C, A)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t22_funct_1)).
% 3.48/1.56  tff(f_70, axiom, (![A, B]: ((((v1_relat_1(A) & v1_funct_1(A)) & v1_relat_1(B)) & v1_funct_1(B)) => (v1_relat_1(k5_relat_1(A, B)) & v1_funct_1(k5_relat_1(A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_funct_1)).
% 3.48/1.56  tff(f_38, axiom, (![A, B]: ((v1_relat_1(A) & v1_relat_1(B)) => v1_relat_1(k5_relat_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k5_relat_1)).
% 3.48/1.56  tff(c_60, plain, (v1_relat_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_156])).
% 3.48/1.56  tff(c_58, plain, (v1_funct_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_156])).
% 3.48/1.56  tff(c_6, plain, (![A_6, B_7]: (v1_relat_1(k2_zfmisc_1(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.48/1.56  tff(c_62, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_156])).
% 3.48/1.56  tff(c_69, plain, (![B_47, A_48]: (v1_relat_1(B_47) | ~m1_subset_1(B_47, k1_zfmisc_1(A_48)) | ~v1_relat_1(A_48))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.48/1.56  tff(c_72, plain, (v1_relat_1('#skF_6') | ~v1_relat_1(k2_zfmisc_1('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_62, c_69])).
% 3.48/1.56  tff(c_75, plain, (v1_relat_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_6, c_72])).
% 3.48/1.56  tff(c_66, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_156])).
% 3.48/1.56  tff(c_54, plain, (k1_xboole_0!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_156])).
% 3.48/1.56  tff(c_64, plain, (v1_funct_2('#skF_6', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_156])).
% 3.48/1.56  tff(c_104, plain, (![B_68, A_69, C_70]: (k1_xboole_0=B_68 | k1_relset_1(A_69, B_68, C_70)=A_69 | ~v1_funct_2(C_70, A_69, B_68) | ~m1_subset_1(C_70, k1_zfmisc_1(k2_zfmisc_1(A_69, B_68))))), inference(cnfTransformation, [status(thm)], [f_138])).
% 3.48/1.56  tff(c_107, plain, (k1_xboole_0='#skF_4' | k1_relset_1('#skF_3', '#skF_4', '#skF_6')='#skF_3' | ~v1_funct_2('#skF_6', '#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_62, c_104])).
% 3.48/1.56  tff(c_110, plain, (k1_xboole_0='#skF_4' | k1_relset_1('#skF_3', '#skF_4', '#skF_6')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_64, c_107])).
% 3.48/1.56  tff(c_111, plain, (k1_relset_1('#skF_3', '#skF_4', '#skF_6')='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_54, c_110])).
% 3.48/1.56  tff(c_56, plain, (r2_hidden('#skF_5', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_156])).
% 3.48/1.56  tff(c_158, plain, (![D_90, A_91, B_92, C_93]: (r2_hidden(k4_tarski(D_90, '#skF_2'(A_91, B_92, C_93, D_90)), C_93) | ~r2_hidden(D_90, B_92) | k1_relset_1(B_92, A_91, C_93)!=B_92 | ~m1_subset_1(C_93, k1_zfmisc_1(k2_zfmisc_1(B_92, A_91))))), inference(cnfTransformation, [status(thm)], [f_120])).
% 3.48/1.56  tff(c_30, plain, (![C_25, A_23, B_24]: (k1_funct_1(C_25, A_23)=B_24 | ~r2_hidden(k4_tarski(A_23, B_24), C_25) | ~v1_funct_1(C_25) | ~v1_relat_1(C_25))), inference(cnfTransformation, [status(thm)], [f_108])).
% 3.48/1.56  tff(c_405, plain, (![C_129, D_130, A_131, B_132]: (k1_funct_1(C_129, D_130)='#skF_2'(A_131, B_132, C_129, D_130) | ~v1_funct_1(C_129) | ~v1_relat_1(C_129) | ~r2_hidden(D_130, B_132) | k1_relset_1(B_132, A_131, C_129)!=B_132 | ~m1_subset_1(C_129, k1_zfmisc_1(k2_zfmisc_1(B_132, A_131))))), inference(resolution, [status(thm)], [c_158, c_30])).
% 3.48/1.56  tff(c_433, plain, (![C_133, A_134]: (k1_funct_1(C_133, '#skF_5')='#skF_2'(A_134, '#skF_3', C_133, '#skF_5') | ~v1_funct_1(C_133) | ~v1_relat_1(C_133) | k1_relset_1('#skF_3', A_134, C_133)!='#skF_3' | ~m1_subset_1(C_133, k1_zfmisc_1(k2_zfmisc_1('#skF_3', A_134))))), inference(resolution, [status(thm)], [c_56, c_405])).
% 3.48/1.56  tff(c_436, plain, (k1_funct_1('#skF_6', '#skF_5')='#skF_2'('#skF_4', '#skF_3', '#skF_6', '#skF_5') | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6') | k1_relset_1('#skF_3', '#skF_4', '#skF_6')!='#skF_3'), inference(resolution, [status(thm)], [c_62, c_433])).
% 3.48/1.56  tff(c_439, plain, (k1_funct_1('#skF_6', '#skF_5')='#skF_2'('#skF_4', '#skF_3', '#skF_6', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_111, c_75, c_66, c_436])).
% 3.48/1.56  tff(c_14, plain, (![A_8, B_11]: (k1_funct_1(A_8, B_11)=k1_xboole_0 | r2_hidden(B_11, k1_relat_1(A_8)) | ~v1_funct_1(A_8) | ~v1_relat_1(A_8))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.48/1.56  tff(c_32, plain, (![A_23, C_25, B_24]: (r2_hidden(A_23, k1_relat_1(C_25)) | ~r2_hidden(k4_tarski(A_23, B_24), C_25) | ~v1_funct_1(C_25) | ~v1_relat_1(C_25))), inference(cnfTransformation, [status(thm)], [f_108])).
% 3.48/1.56  tff(c_218, plain, (![D_100, C_101, B_102, A_103]: (r2_hidden(D_100, k1_relat_1(C_101)) | ~v1_funct_1(C_101) | ~v1_relat_1(C_101) | ~r2_hidden(D_100, B_102) | k1_relset_1(B_102, A_103, C_101)!=B_102 | ~m1_subset_1(C_101, k1_zfmisc_1(k2_zfmisc_1(B_102, A_103))))), inference(resolution, [status(thm)], [c_158, c_32])).
% 3.48/1.56  tff(c_237, plain, (![C_104, A_105]: (r2_hidden('#skF_5', k1_relat_1(C_104)) | ~v1_funct_1(C_104) | ~v1_relat_1(C_104) | k1_relset_1('#skF_3', A_105, C_104)!='#skF_3' | ~m1_subset_1(C_104, k1_zfmisc_1(k2_zfmisc_1('#skF_3', A_105))))), inference(resolution, [status(thm)], [c_56, c_218])).
% 3.48/1.56  tff(c_240, plain, (r2_hidden('#skF_5', k1_relat_1('#skF_6')) | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6') | k1_relset_1('#skF_3', '#skF_4', '#skF_6')!='#skF_3'), inference(resolution, [status(thm)], [c_62, c_237])).
% 3.48/1.56  tff(c_243, plain, (r2_hidden('#skF_5', k1_relat_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_111, c_75, c_66, c_240])).
% 3.48/1.56  tff(c_20, plain, (![A_15, C_18, B_16]: (r2_hidden(A_15, k1_relat_1(k5_relat_1(C_18, B_16))) | ~r2_hidden(k1_funct_1(C_18, A_15), k1_relat_1(B_16)) | ~r2_hidden(A_15, k1_relat_1(C_18)) | ~v1_funct_1(C_18) | ~v1_relat_1(C_18) | ~v1_funct_1(B_16) | ~v1_relat_1(B_16))), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.48/1.56  tff(c_445, plain, (![B_16]: (r2_hidden('#skF_5', k1_relat_1(k5_relat_1('#skF_6', B_16))) | ~r2_hidden('#skF_2'('#skF_4', '#skF_3', '#skF_6', '#skF_5'), k1_relat_1(B_16)) | ~r2_hidden('#skF_5', k1_relat_1('#skF_6')) | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6') | ~v1_funct_1(B_16) | ~v1_relat_1(B_16))), inference(superposition, [status(thm), theory('equality')], [c_439, c_20])).
% 3.48/1.56  tff(c_481, plain, (![B_141]: (r2_hidden('#skF_5', k1_relat_1(k5_relat_1('#skF_6', B_141))) | ~r2_hidden('#skF_2'('#skF_4', '#skF_3', '#skF_6', '#skF_5'), k1_relat_1(B_141)) | ~v1_funct_1(B_141) | ~v1_relat_1(B_141))), inference(demodulation, [status(thm), theory('equality')], [c_75, c_66, c_243, c_445])).
% 3.48/1.56  tff(c_523, plain, (![A_143]: (r2_hidden('#skF_5', k1_relat_1(k5_relat_1('#skF_6', A_143))) | k1_funct_1(A_143, '#skF_2'('#skF_4', '#skF_3', '#skF_6', '#skF_5'))=k1_xboole_0 | ~v1_funct_1(A_143) | ~v1_relat_1(A_143))), inference(resolution, [status(thm)], [c_14, c_481])).
% 3.48/1.56  tff(c_26, plain, (![C_22, B_20, A_19]: (k1_funct_1(k5_relat_1(C_22, B_20), A_19)=k1_funct_1(B_20, k1_funct_1(C_22, A_19)) | ~r2_hidden(A_19, k1_relat_1(k5_relat_1(C_22, B_20))) | ~v1_funct_1(C_22) | ~v1_relat_1(C_22) | ~v1_funct_1(B_20) | ~v1_relat_1(B_20))), inference(cnfTransformation, [status(thm)], [f_98])).
% 3.48/1.56  tff(c_528, plain, (![A_143]: (k1_funct_1(k5_relat_1('#skF_6', A_143), '#skF_5')=k1_funct_1(A_143, k1_funct_1('#skF_6', '#skF_5')) | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6') | k1_funct_1(A_143, '#skF_2'('#skF_4', '#skF_3', '#skF_6', '#skF_5'))=k1_xboole_0 | ~v1_funct_1(A_143) | ~v1_relat_1(A_143))), inference(resolution, [status(thm)], [c_523, c_26])).
% 3.48/1.56  tff(c_587, plain, (![A_146]: (k1_funct_1(k5_relat_1('#skF_6', A_146), '#skF_5')=k1_funct_1(A_146, '#skF_2'('#skF_4', '#skF_3', '#skF_6', '#skF_5')) | k1_funct_1(A_146, '#skF_2'('#skF_4', '#skF_3', '#skF_6', '#skF_5'))=k1_xboole_0 | ~v1_funct_1(A_146) | ~v1_relat_1(A_146))), inference(demodulation, [status(thm), theory('equality')], [c_75, c_66, c_439, c_528])).
% 3.48/1.56  tff(c_52, plain, (k1_funct_1(k5_relat_1('#skF_6', '#skF_7'), '#skF_5')!=k1_funct_1('#skF_7', k1_funct_1('#skF_6', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_156])).
% 3.48/1.56  tff(c_441, plain, (k1_funct_1(k5_relat_1('#skF_6', '#skF_7'), '#skF_5')!=k1_funct_1('#skF_7', '#skF_2'('#skF_4', '#skF_3', '#skF_6', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_439, c_52])).
% 3.48/1.56  tff(c_593, plain, (k1_funct_1('#skF_7', '#skF_2'('#skF_4', '#skF_3', '#skF_6', '#skF_5'))=k1_xboole_0 | ~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_587, c_441])).
% 3.48/1.56  tff(c_616, plain, (k1_funct_1('#skF_7', '#skF_2'('#skF_4', '#skF_3', '#skF_6', '#skF_5'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_593])).
% 3.48/1.56  tff(c_627, plain, (k1_funct_1(k5_relat_1('#skF_6', '#skF_7'), '#skF_5')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_616, c_441])).
% 3.48/1.56  tff(c_16, plain, (![A_13, B_14]: (v1_funct_1(k5_relat_1(A_13, B_14)) | ~v1_funct_1(B_14) | ~v1_relat_1(B_14) | ~v1_funct_1(A_13) | ~v1_relat_1(A_13))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.48/1.56  tff(c_4, plain, (![A_4, B_5]: (v1_relat_1(k5_relat_1(A_4, B_5)) | ~v1_relat_1(B_5) | ~v1_relat_1(A_4))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.48/1.56  tff(c_22, plain, (![C_18, A_15, B_16]: (r2_hidden(k1_funct_1(C_18, A_15), k1_relat_1(B_16)) | ~r2_hidden(A_15, k1_relat_1(k5_relat_1(C_18, B_16))) | ~v1_funct_1(C_18) | ~v1_relat_1(C_18) | ~v1_funct_1(B_16) | ~v1_relat_1(B_16))), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.48/1.56  tff(c_448, plain, (![B_16]: (r2_hidden('#skF_2'('#skF_4', '#skF_3', '#skF_6', '#skF_5'), k1_relat_1(B_16)) | ~r2_hidden('#skF_5', k1_relat_1(k5_relat_1('#skF_6', B_16))) | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6') | ~v1_funct_1(B_16) | ~v1_relat_1(B_16))), inference(superposition, [status(thm), theory('equality')], [c_439, c_22])).
% 3.48/1.56  tff(c_457, plain, (![B_16]: (r2_hidden('#skF_2'('#skF_4', '#skF_3', '#skF_6', '#skF_5'), k1_relat_1(B_16)) | ~r2_hidden('#skF_5', k1_relat_1(k5_relat_1('#skF_6', B_16))) | ~v1_funct_1(B_16) | ~v1_relat_1(B_16))), inference(demodulation, [status(thm), theory('equality')], [c_75, c_66, c_448])).
% 3.48/1.56  tff(c_28, plain, (![A_23, C_25]: (r2_hidden(k4_tarski(A_23, k1_funct_1(C_25, A_23)), C_25) | ~r2_hidden(A_23, k1_relat_1(C_25)) | ~v1_funct_1(C_25) | ~v1_relat_1(C_25))), inference(cnfTransformation, [status(thm)], [f_108])).
% 3.48/1.56  tff(c_637, plain, (r2_hidden(k4_tarski('#skF_2'('#skF_4', '#skF_3', '#skF_6', '#skF_5'), k1_xboole_0), '#skF_7') | ~r2_hidden('#skF_2'('#skF_4', '#skF_3', '#skF_6', '#skF_5'), k1_relat_1('#skF_7')) | ~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_616, c_28])).
% 3.48/1.56  tff(c_645, plain, (r2_hidden(k4_tarski('#skF_2'('#skF_4', '#skF_3', '#skF_6', '#skF_5'), k1_xboole_0), '#skF_7') | ~r2_hidden('#skF_2'('#skF_4', '#skF_3', '#skF_6', '#skF_5'), k1_relat_1('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_637])).
% 3.48/1.56  tff(c_653, plain, (~r2_hidden('#skF_2'('#skF_4', '#skF_3', '#skF_6', '#skF_5'), k1_relat_1('#skF_7'))), inference(splitLeft, [status(thm)], [c_645])).
% 3.48/1.56  tff(c_676, plain, (~r2_hidden('#skF_5', k1_relat_1(k5_relat_1('#skF_6', '#skF_7'))) | ~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_457, c_653])).
% 3.48/1.56  tff(c_685, plain, (~r2_hidden('#skF_5', k1_relat_1(k5_relat_1('#skF_6', '#skF_7')))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_676])).
% 3.48/1.56  tff(c_706, plain, (k1_funct_1(k5_relat_1('#skF_6', '#skF_7'), '#skF_5')=k1_xboole_0 | ~v1_funct_1(k5_relat_1('#skF_6', '#skF_7')) | ~v1_relat_1(k5_relat_1('#skF_6', '#skF_7'))), inference(resolution, [status(thm)], [c_14, c_685])).
% 3.48/1.56  tff(c_719, plain, (~v1_funct_1(k5_relat_1('#skF_6', '#skF_7')) | ~v1_relat_1(k5_relat_1('#skF_6', '#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_627, c_706])).
% 3.48/1.56  tff(c_720, plain, (~v1_relat_1(k5_relat_1('#skF_6', '#skF_7'))), inference(splitLeft, [status(thm)], [c_719])).
% 3.48/1.56  tff(c_723, plain, (~v1_relat_1('#skF_7') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_4, c_720])).
% 3.48/1.56  tff(c_727, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_75, c_60, c_723])).
% 3.48/1.56  tff(c_728, plain, (~v1_funct_1(k5_relat_1('#skF_6', '#skF_7'))), inference(splitRight, [status(thm)], [c_719])).
% 3.48/1.56  tff(c_741, plain, (~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7') | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_16, c_728])).
% 3.48/1.56  tff(c_745, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_75, c_66, c_60, c_58, c_741])).
% 3.48/1.56  tff(c_747, plain, (r2_hidden('#skF_2'('#skF_4', '#skF_3', '#skF_6', '#skF_5'), k1_relat_1('#skF_7'))), inference(splitRight, [status(thm)], [c_645])).
% 3.48/1.56  tff(c_455, plain, (![B_16]: (r2_hidden('#skF_5', k1_relat_1(k5_relat_1('#skF_6', B_16))) | ~r2_hidden('#skF_2'('#skF_4', '#skF_3', '#skF_6', '#skF_5'), k1_relat_1(B_16)) | ~v1_funct_1(B_16) | ~v1_relat_1(B_16))), inference(demodulation, [status(thm), theory('equality')], [c_75, c_66, c_243, c_445])).
% 3.48/1.56  tff(c_750, plain, (r2_hidden('#skF_5', k1_relat_1(k5_relat_1('#skF_6', '#skF_7'))) | ~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_747, c_455])).
% 3.48/1.56  tff(c_757, plain, (r2_hidden('#skF_5', k1_relat_1(k5_relat_1('#skF_6', '#skF_7')))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_750])).
% 3.48/1.56  tff(c_764, plain, (k1_funct_1(k5_relat_1('#skF_6', '#skF_7'), '#skF_5')=k1_funct_1('#skF_7', k1_funct_1('#skF_6', '#skF_5')) | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6') | ~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_757, c_26])).
% 3.48/1.56  tff(c_773, plain, (k1_funct_1(k5_relat_1('#skF_6', '#skF_7'), '#skF_5')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_75, c_66, c_616, c_439, c_764])).
% 3.48/1.56  tff(c_775, plain, $false, inference(negUnitSimplification, [status(thm)], [c_627, c_773])).
% 3.48/1.56  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.48/1.56  
% 3.48/1.56  Inference rules
% 3.48/1.56  ----------------------
% 3.48/1.56  #Ref     : 0
% 3.48/1.56  #Sup     : 151
% 3.48/1.56  #Fact    : 0
% 3.48/1.56  #Define  : 0
% 3.48/1.56  #Split   : 2
% 3.48/1.56  #Chain   : 0
% 3.48/1.56  #Close   : 0
% 3.48/1.56  
% 3.48/1.56  Ordering : KBO
% 3.48/1.56  
% 3.48/1.56  Simplification rules
% 3.48/1.56  ----------------------
% 3.48/1.56  #Subsume      : 11
% 3.48/1.56  #Demod        : 101
% 3.48/1.56  #Tautology    : 37
% 3.48/1.56  #SimpNegUnit  : 4
% 3.48/1.56  #BackRed      : 2
% 3.48/1.56  
% 3.48/1.56  #Partial instantiations: 0
% 3.48/1.56  #Strategies tried      : 1
% 3.48/1.56  
% 3.48/1.56  Timing (in seconds)
% 3.48/1.56  ----------------------
% 3.48/1.57  Preprocessing        : 0.33
% 3.48/1.57  Parsing              : 0.17
% 3.48/1.57  CNF conversion       : 0.03
% 3.48/1.57  Main loop            : 0.41
% 3.48/1.57  Inferencing          : 0.15
% 3.48/1.57  Reduction            : 0.11
% 3.48/1.57  Demodulation         : 0.08
% 3.48/1.57  BG Simplification    : 0.03
% 3.48/1.57  Subsumption          : 0.09
% 3.48/1.57  Abstraction          : 0.02
% 3.48/1.57  MUC search           : 0.00
% 3.48/1.57  Cooper               : 0.00
% 3.48/1.57  Total                : 0.78
% 3.48/1.57  Index Insertion      : 0.00
% 3.48/1.57  Index Deletion       : 0.00
% 3.48/1.57  Index Matching       : 0.00
% 3.48/1.57  BG Taut test         : 0.00
%------------------------------------------------------------------------------
