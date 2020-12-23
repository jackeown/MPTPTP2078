%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:11:23 EST 2020

% Result     : Theorem 4.45s
% Output     : CNFRefutation 4.45s
% Verified   : 
% Statistics : Number of formulae       :   86 ( 195 expanded)
%              Number of leaves         :   34 (  82 expanded)
%              Depth                    :   11
%              Number of atoms          :  153 ( 523 expanded)
%              Number of equality atoms :   46 ( 166 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1 > #skF_6

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_6',type,(
    '#skF_6': $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_107,negated_conjecture,(
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

tff(f_70,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_62,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k2_relset_1(A,B,C),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_relset_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( ! [C] :
          ( r2_hidden(C,A)
        <=> r2_hidden(C,B) )
     => A = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tarski)).

tff(f_41,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

tff(f_66,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_88,axiom,(
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

tff(f_58,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r2_hidden(A,k1_relat_1(B))
       => r2_hidden(k1_funct_1(B,A),k2_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_funct_1)).

tff(f_34,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_54,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

tff(c_40,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_106,plain,(
    ! [A_52,B_53,C_54] :
      ( k2_relset_1(A_52,B_53,C_54) = k2_relat_1(C_54)
      | ~ m1_subset_1(C_54,k1_zfmisc_1(k2_zfmisc_1(A_52,B_53))) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_110,plain,(
    k2_relset_1('#skF_3','#skF_4','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_40,c_106])).

tff(c_38,plain,(
    k2_relset_1('#skF_3','#skF_4','#skF_5') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_111,plain,(
    k2_relat_1('#skF_5') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_110,c_38])).

tff(c_218,plain,(
    ! [A_79,B_80,C_81] :
      ( m1_subset_1(k2_relset_1(A_79,B_80,C_81),k1_zfmisc_1(B_80))
      | ~ m1_subset_1(C_81,k1_zfmisc_1(k2_zfmisc_1(A_79,B_80))) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_239,plain,
    ( m1_subset_1(k2_relat_1('#skF_5'),k1_zfmisc_1('#skF_4'))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_110,c_218])).

tff(c_246,plain,(
    m1_subset_1(k2_relat_1('#skF_5'),k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_239])).

tff(c_91,plain,(
    ! [A_50,B_51] :
      ( r2_hidden('#skF_1'(A_50,B_51),B_51)
      | r2_hidden('#skF_2'(A_50,B_51),A_50)
      | B_51 = A_50 ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_12,plain,(
    ! [C_8,A_5,B_6] :
      ( r2_hidden(C_8,A_5)
      | ~ r2_hidden(C_8,B_6)
      | ~ m1_subset_1(B_6,k1_zfmisc_1(A_5)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_517,plain,(
    ! [A_132,B_133,A_134] :
      ( r2_hidden('#skF_2'(A_132,B_133),A_134)
      | ~ m1_subset_1(A_132,k1_zfmisc_1(A_134))
      | r2_hidden('#skF_1'(A_132,B_133),B_133)
      | B_133 = A_132 ) ),
    inference(resolution,[status(thm)],[c_91,c_12])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),B_2)
      | ~ r2_hidden('#skF_2'(A_1,B_2),B_2)
      | B_2 = A_1 ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_544,plain,(
    ! [A_132,A_134] :
      ( ~ m1_subset_1(A_132,k1_zfmisc_1(A_134))
      | r2_hidden('#skF_1'(A_132,A_134),A_134)
      | A_134 = A_132 ) ),
    inference(resolution,[status(thm)],[c_517,c_4])).

tff(c_48,plain,(
    ! [D_31] :
      ( r2_hidden('#skF_6'(D_31),'#skF_3')
      | ~ r2_hidden(D_31,'#skF_4') ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_42,plain,(
    v1_funct_2('#skF_5','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_137,plain,(
    ! [A_59,B_60,C_61] :
      ( k1_relset_1(A_59,B_60,C_61) = k1_relat_1(C_61)
      | ~ m1_subset_1(C_61,k1_zfmisc_1(k2_zfmisc_1(A_59,B_60))) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_141,plain,(
    k1_relset_1('#skF_3','#skF_4','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_40,c_137])).

tff(c_420,plain,(
    ! [B_120,A_121,C_122] :
      ( k1_xboole_0 = B_120
      | k1_relset_1(A_121,B_120,C_122) = A_121
      | ~ v1_funct_2(C_122,A_121,B_120)
      | ~ m1_subset_1(C_122,k1_zfmisc_1(k2_zfmisc_1(A_121,B_120))) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_427,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relset_1('#skF_3','#skF_4','#skF_5') = '#skF_3'
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_40,c_420])).

tff(c_431,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relat_1('#skF_5') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_141,c_427])).

tff(c_432,plain,(
    k1_relat_1('#skF_5') = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_431])).

tff(c_57,plain,(
    ! [C_38,A_39,B_40] :
      ( v1_relat_1(C_38)
      | ~ m1_subset_1(C_38,k1_zfmisc_1(k2_zfmisc_1(A_39,B_40))) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_61,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_40,c_57])).

tff(c_44,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_46,plain,(
    ! [D_31] :
      ( k1_funct_1('#skF_5','#skF_6'(D_31)) = D_31
      | ~ r2_hidden(D_31,'#skF_4') ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_313,plain,(
    ! [B_92,A_93] :
      ( r2_hidden(k1_funct_1(B_92,A_93),k2_relat_1(B_92))
      | ~ r2_hidden(A_93,k1_relat_1(B_92))
      | ~ v1_funct_1(B_92)
      | ~ v1_relat_1(B_92) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_321,plain,(
    ! [D_31] :
      ( r2_hidden(D_31,k2_relat_1('#skF_5'))
      | ~ r2_hidden('#skF_6'(D_31),k1_relat_1('#skF_5'))
      | ~ v1_funct_1('#skF_5')
      | ~ v1_relat_1('#skF_5')
      | ~ r2_hidden(D_31,'#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_313])).

tff(c_325,plain,(
    ! [D_31] :
      ( r2_hidden(D_31,k2_relat_1('#skF_5'))
      | ~ r2_hidden('#skF_6'(D_31),k1_relat_1('#skF_5'))
      | ~ r2_hidden(D_31,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_61,c_44,c_321])).

tff(c_445,plain,(
    ! [D_123] :
      ( r2_hidden(D_123,k2_relat_1('#skF_5'))
      | ~ r2_hidden('#skF_6'(D_123),'#skF_3')
      | ~ r2_hidden(D_123,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_432,c_325])).

tff(c_454,plain,(
    ! [D_31] :
      ( r2_hidden(D_31,k2_relat_1('#skF_5'))
      | ~ r2_hidden(D_31,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_48,c_445])).

tff(c_116,plain,(
    ! [A_55,B_56] :
      ( ~ r2_hidden('#skF_1'(A_55,B_56),A_55)
      | r2_hidden('#skF_2'(A_55,B_56),A_55)
      | B_56 = A_55 ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_633,plain,(
    ! [A_147,B_148,A_149] :
      ( r2_hidden('#skF_2'(A_147,B_148),A_149)
      | ~ m1_subset_1(A_147,k1_zfmisc_1(A_149))
      | ~ r2_hidden('#skF_1'(A_147,B_148),A_147)
      | B_148 = A_147 ) ),
    inference(resolution,[status(thm)],[c_116,c_12])).

tff(c_1364,plain,(
    ! [B_332,A_333] :
      ( r2_hidden('#skF_2'(k2_relat_1('#skF_5'),B_332),A_333)
      | ~ m1_subset_1(k2_relat_1('#skF_5'),k1_zfmisc_1(A_333))
      | k2_relat_1('#skF_5') = B_332
      | ~ r2_hidden('#skF_1'(k2_relat_1('#skF_5'),B_332),'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_454,c_633])).

tff(c_455,plain,(
    ! [D_124] :
      ( r2_hidden(D_124,k2_relat_1('#skF_5'))
      | ~ r2_hidden(D_124,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_48,c_445])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),A_1)
      | ~ r2_hidden('#skF_2'(A_1,B_2),B_2)
      | B_2 = A_1 ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_473,plain,(
    ! [B_2] :
      ( ~ r2_hidden('#skF_2'(k2_relat_1('#skF_5'),B_2),B_2)
      | k2_relat_1('#skF_5') = B_2
      | ~ r2_hidden('#skF_1'(k2_relat_1('#skF_5'),B_2),'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_455,c_2])).

tff(c_1386,plain,(
    ! [A_334] :
      ( ~ m1_subset_1(k2_relat_1('#skF_5'),k1_zfmisc_1(A_334))
      | k2_relat_1('#skF_5') = A_334
      | ~ r2_hidden('#skF_1'(k2_relat_1('#skF_5'),A_334),'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_1364,c_473])).

tff(c_1408,plain,
    ( ~ m1_subset_1(k2_relat_1('#skF_5'),k1_zfmisc_1('#skF_4'))
    | k2_relat_1('#skF_5') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_544,c_1386])).

tff(c_1421,plain,(
    k2_relat_1('#skF_5') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_246,c_1408])).

tff(c_1423,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_111,c_1421])).

tff(c_1424,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_431])).

tff(c_10,plain,(
    ! [A_4] : r1_tarski(k1_xboole_0,A_4) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_16,plain,(
    ! [B_12,A_11] :
      ( ~ r1_tarski(B_12,A_11)
      | ~ r2_hidden(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_148,plain,(
    ! [B_64,A_65] :
      ( ~ r1_tarski(B_64,'#skF_1'(A_65,B_64))
      | r2_hidden('#skF_2'(A_65,B_64),A_65)
      | B_64 = A_65 ) ),
    inference(resolution,[status(thm)],[c_91,c_16])).

tff(c_153,plain,(
    ! [A_66] :
      ( r2_hidden('#skF_2'(A_66,k1_xboole_0),A_66)
      | k1_xboole_0 = A_66 ) ),
    inference(resolution,[status(thm)],[c_10,c_148])).

tff(c_178,plain,(
    ! [A_71,A_72] :
      ( r2_hidden('#skF_2'(A_71,k1_xboole_0),A_72)
      | ~ m1_subset_1(A_71,k1_zfmisc_1(A_72))
      | k1_xboole_0 = A_71 ) ),
    inference(resolution,[status(thm)],[c_153,c_12])).

tff(c_191,plain,(
    ! [A_73] :
      ( r2_hidden('#skF_1'(A_73,k1_xboole_0),k1_xboole_0)
      | ~ m1_subset_1(A_73,k1_zfmisc_1(k1_xboole_0))
      | k1_xboole_0 = A_73 ) ),
    inference(resolution,[status(thm)],[c_178,c_4])).

tff(c_199,plain,(
    ! [A_73] :
      ( ~ r1_tarski(k1_xboole_0,'#skF_1'(A_73,k1_xboole_0))
      | ~ m1_subset_1(A_73,k1_zfmisc_1(k1_xboole_0))
      | k1_xboole_0 = A_73 ) ),
    inference(resolution,[status(thm)],[c_191,c_16])).

tff(c_205,plain,(
    ! [A_73] :
      ( ~ m1_subset_1(A_73,k1_zfmisc_1(k1_xboole_0))
      | k1_xboole_0 = A_73 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_199])).

tff(c_1471,plain,(
    ! [A_338] :
      ( ~ m1_subset_1(A_338,k1_zfmisc_1('#skF_4'))
      | A_338 = '#skF_4' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1424,c_1424,c_205])).

tff(c_1474,plain,(
    k2_relat_1('#skF_5') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_246,c_1471])).

tff(c_1482,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_111,c_1474])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 12:50:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.45/1.77  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.45/1.78  
% 4.45/1.78  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.45/1.78  %$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1 > #skF_6
% 4.45/1.78  
% 4.45/1.78  %Foreground sorts:
% 4.45/1.78  
% 4.45/1.78  
% 4.45/1.78  %Background operators:
% 4.45/1.78  
% 4.45/1.78  
% 4.45/1.78  %Foreground operators:
% 4.45/1.78  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 4.45/1.78  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.45/1.78  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.45/1.78  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.45/1.78  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.45/1.78  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.45/1.78  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 4.45/1.78  tff('#skF_5', type, '#skF_5': $i).
% 4.45/1.78  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.45/1.78  tff('#skF_3', type, '#skF_3': $i).
% 4.45/1.78  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 4.45/1.78  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.45/1.78  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 4.45/1.78  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.45/1.78  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.45/1.78  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.45/1.78  tff('#skF_4', type, '#skF_4': $i).
% 4.45/1.78  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.45/1.78  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 4.45/1.78  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 4.45/1.78  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.45/1.78  tff('#skF_6', type, '#skF_6': $i > $i).
% 4.45/1.78  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.45/1.78  
% 4.45/1.80  tff(f_107, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((![D]: ~(r2_hidden(D, B) & (![E]: ~(r2_hidden(E, A) & (D = k1_funct_1(C, E)))))) => (k2_relset_1(A, B, C) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t16_funct_2)).
% 4.45/1.80  tff(f_70, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 4.45/1.80  tff(f_62, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k2_relset_1(A, B, C), k1_zfmisc_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_relset_1)).
% 4.45/1.80  tff(f_32, axiom, (![A, B]: ((![C]: (r2_hidden(C, A) <=> r2_hidden(C, B))) => (A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_tarski)).
% 4.45/1.80  tff(f_41, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_subset_1)).
% 4.45/1.80  tff(f_66, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 4.45/1.80  tff(f_88, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 4.45/1.80  tff(f_58, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 4.45/1.80  tff(f_49, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r2_hidden(A, k1_relat_1(B)) => r2_hidden(k1_funct_1(B, A), k2_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_funct_1)).
% 4.45/1.80  tff(f_34, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 4.45/1.80  tff(f_54, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 4.45/1.80  tff(c_40, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_107])).
% 4.45/1.80  tff(c_106, plain, (![A_52, B_53, C_54]: (k2_relset_1(A_52, B_53, C_54)=k2_relat_1(C_54) | ~m1_subset_1(C_54, k1_zfmisc_1(k2_zfmisc_1(A_52, B_53))))), inference(cnfTransformation, [status(thm)], [f_70])).
% 4.45/1.80  tff(c_110, plain, (k2_relset_1('#skF_3', '#skF_4', '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_40, c_106])).
% 4.45/1.80  tff(c_38, plain, (k2_relset_1('#skF_3', '#skF_4', '#skF_5')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_107])).
% 4.45/1.80  tff(c_111, plain, (k2_relat_1('#skF_5')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_110, c_38])).
% 4.45/1.80  tff(c_218, plain, (![A_79, B_80, C_81]: (m1_subset_1(k2_relset_1(A_79, B_80, C_81), k1_zfmisc_1(B_80)) | ~m1_subset_1(C_81, k1_zfmisc_1(k2_zfmisc_1(A_79, B_80))))), inference(cnfTransformation, [status(thm)], [f_62])).
% 4.45/1.80  tff(c_239, plain, (m1_subset_1(k2_relat_1('#skF_5'), k1_zfmisc_1('#skF_4')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_110, c_218])).
% 4.45/1.80  tff(c_246, plain, (m1_subset_1(k2_relat_1('#skF_5'), k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_239])).
% 4.45/1.80  tff(c_91, plain, (![A_50, B_51]: (r2_hidden('#skF_1'(A_50, B_51), B_51) | r2_hidden('#skF_2'(A_50, B_51), A_50) | B_51=A_50)), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.45/1.80  tff(c_12, plain, (![C_8, A_5, B_6]: (r2_hidden(C_8, A_5) | ~r2_hidden(C_8, B_6) | ~m1_subset_1(B_6, k1_zfmisc_1(A_5)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.45/1.80  tff(c_517, plain, (![A_132, B_133, A_134]: (r2_hidden('#skF_2'(A_132, B_133), A_134) | ~m1_subset_1(A_132, k1_zfmisc_1(A_134)) | r2_hidden('#skF_1'(A_132, B_133), B_133) | B_133=A_132)), inference(resolution, [status(thm)], [c_91, c_12])).
% 4.45/1.80  tff(c_4, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), B_2) | ~r2_hidden('#skF_2'(A_1, B_2), B_2) | B_2=A_1)), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.45/1.80  tff(c_544, plain, (![A_132, A_134]: (~m1_subset_1(A_132, k1_zfmisc_1(A_134)) | r2_hidden('#skF_1'(A_132, A_134), A_134) | A_134=A_132)), inference(resolution, [status(thm)], [c_517, c_4])).
% 4.45/1.80  tff(c_48, plain, (![D_31]: (r2_hidden('#skF_6'(D_31), '#skF_3') | ~r2_hidden(D_31, '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_107])).
% 4.45/1.80  tff(c_42, plain, (v1_funct_2('#skF_5', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_107])).
% 4.45/1.80  tff(c_137, plain, (![A_59, B_60, C_61]: (k1_relset_1(A_59, B_60, C_61)=k1_relat_1(C_61) | ~m1_subset_1(C_61, k1_zfmisc_1(k2_zfmisc_1(A_59, B_60))))), inference(cnfTransformation, [status(thm)], [f_66])).
% 4.45/1.80  tff(c_141, plain, (k1_relset_1('#skF_3', '#skF_4', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_40, c_137])).
% 4.45/1.80  tff(c_420, plain, (![B_120, A_121, C_122]: (k1_xboole_0=B_120 | k1_relset_1(A_121, B_120, C_122)=A_121 | ~v1_funct_2(C_122, A_121, B_120) | ~m1_subset_1(C_122, k1_zfmisc_1(k2_zfmisc_1(A_121, B_120))))), inference(cnfTransformation, [status(thm)], [f_88])).
% 4.45/1.80  tff(c_427, plain, (k1_xboole_0='#skF_4' | k1_relset_1('#skF_3', '#skF_4', '#skF_5')='#skF_3' | ~v1_funct_2('#skF_5', '#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_40, c_420])).
% 4.45/1.80  tff(c_431, plain, (k1_xboole_0='#skF_4' | k1_relat_1('#skF_5')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_42, c_141, c_427])).
% 4.45/1.80  tff(c_432, plain, (k1_relat_1('#skF_5')='#skF_3'), inference(splitLeft, [status(thm)], [c_431])).
% 4.45/1.80  tff(c_57, plain, (![C_38, A_39, B_40]: (v1_relat_1(C_38) | ~m1_subset_1(C_38, k1_zfmisc_1(k2_zfmisc_1(A_39, B_40))))), inference(cnfTransformation, [status(thm)], [f_58])).
% 4.45/1.80  tff(c_61, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_40, c_57])).
% 4.45/1.80  tff(c_44, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_107])).
% 4.45/1.80  tff(c_46, plain, (![D_31]: (k1_funct_1('#skF_5', '#skF_6'(D_31))=D_31 | ~r2_hidden(D_31, '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_107])).
% 4.45/1.80  tff(c_313, plain, (![B_92, A_93]: (r2_hidden(k1_funct_1(B_92, A_93), k2_relat_1(B_92)) | ~r2_hidden(A_93, k1_relat_1(B_92)) | ~v1_funct_1(B_92) | ~v1_relat_1(B_92))), inference(cnfTransformation, [status(thm)], [f_49])).
% 4.45/1.80  tff(c_321, plain, (![D_31]: (r2_hidden(D_31, k2_relat_1('#skF_5')) | ~r2_hidden('#skF_6'(D_31), k1_relat_1('#skF_5')) | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5') | ~r2_hidden(D_31, '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_46, c_313])).
% 4.45/1.80  tff(c_325, plain, (![D_31]: (r2_hidden(D_31, k2_relat_1('#skF_5')) | ~r2_hidden('#skF_6'(D_31), k1_relat_1('#skF_5')) | ~r2_hidden(D_31, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_61, c_44, c_321])).
% 4.45/1.80  tff(c_445, plain, (![D_123]: (r2_hidden(D_123, k2_relat_1('#skF_5')) | ~r2_hidden('#skF_6'(D_123), '#skF_3') | ~r2_hidden(D_123, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_432, c_325])).
% 4.45/1.80  tff(c_454, plain, (![D_31]: (r2_hidden(D_31, k2_relat_1('#skF_5')) | ~r2_hidden(D_31, '#skF_4'))), inference(resolution, [status(thm)], [c_48, c_445])).
% 4.45/1.80  tff(c_116, plain, (![A_55, B_56]: (~r2_hidden('#skF_1'(A_55, B_56), A_55) | r2_hidden('#skF_2'(A_55, B_56), A_55) | B_56=A_55)), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.45/1.80  tff(c_633, plain, (![A_147, B_148, A_149]: (r2_hidden('#skF_2'(A_147, B_148), A_149) | ~m1_subset_1(A_147, k1_zfmisc_1(A_149)) | ~r2_hidden('#skF_1'(A_147, B_148), A_147) | B_148=A_147)), inference(resolution, [status(thm)], [c_116, c_12])).
% 4.45/1.80  tff(c_1364, plain, (![B_332, A_333]: (r2_hidden('#skF_2'(k2_relat_1('#skF_5'), B_332), A_333) | ~m1_subset_1(k2_relat_1('#skF_5'), k1_zfmisc_1(A_333)) | k2_relat_1('#skF_5')=B_332 | ~r2_hidden('#skF_1'(k2_relat_1('#skF_5'), B_332), '#skF_4'))), inference(resolution, [status(thm)], [c_454, c_633])).
% 4.45/1.80  tff(c_455, plain, (![D_124]: (r2_hidden(D_124, k2_relat_1('#skF_5')) | ~r2_hidden(D_124, '#skF_4'))), inference(resolution, [status(thm)], [c_48, c_445])).
% 4.45/1.80  tff(c_2, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), A_1) | ~r2_hidden('#skF_2'(A_1, B_2), B_2) | B_2=A_1)), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.45/1.80  tff(c_473, plain, (![B_2]: (~r2_hidden('#skF_2'(k2_relat_1('#skF_5'), B_2), B_2) | k2_relat_1('#skF_5')=B_2 | ~r2_hidden('#skF_1'(k2_relat_1('#skF_5'), B_2), '#skF_4'))), inference(resolution, [status(thm)], [c_455, c_2])).
% 4.45/1.80  tff(c_1386, plain, (![A_334]: (~m1_subset_1(k2_relat_1('#skF_5'), k1_zfmisc_1(A_334)) | k2_relat_1('#skF_5')=A_334 | ~r2_hidden('#skF_1'(k2_relat_1('#skF_5'), A_334), '#skF_4'))), inference(resolution, [status(thm)], [c_1364, c_473])).
% 4.45/1.80  tff(c_1408, plain, (~m1_subset_1(k2_relat_1('#skF_5'), k1_zfmisc_1('#skF_4')) | k2_relat_1('#skF_5')='#skF_4'), inference(resolution, [status(thm)], [c_544, c_1386])).
% 4.45/1.80  tff(c_1421, plain, (k2_relat_1('#skF_5')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_246, c_1408])).
% 4.45/1.80  tff(c_1423, plain, $false, inference(negUnitSimplification, [status(thm)], [c_111, c_1421])).
% 4.45/1.80  tff(c_1424, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_431])).
% 4.45/1.80  tff(c_10, plain, (![A_4]: (r1_tarski(k1_xboole_0, A_4))), inference(cnfTransformation, [status(thm)], [f_34])).
% 4.45/1.80  tff(c_16, plain, (![B_12, A_11]: (~r1_tarski(B_12, A_11) | ~r2_hidden(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_54])).
% 4.45/1.80  tff(c_148, plain, (![B_64, A_65]: (~r1_tarski(B_64, '#skF_1'(A_65, B_64)) | r2_hidden('#skF_2'(A_65, B_64), A_65) | B_64=A_65)), inference(resolution, [status(thm)], [c_91, c_16])).
% 4.45/1.80  tff(c_153, plain, (![A_66]: (r2_hidden('#skF_2'(A_66, k1_xboole_0), A_66) | k1_xboole_0=A_66)), inference(resolution, [status(thm)], [c_10, c_148])).
% 4.45/1.80  tff(c_178, plain, (![A_71, A_72]: (r2_hidden('#skF_2'(A_71, k1_xboole_0), A_72) | ~m1_subset_1(A_71, k1_zfmisc_1(A_72)) | k1_xboole_0=A_71)), inference(resolution, [status(thm)], [c_153, c_12])).
% 4.45/1.80  tff(c_191, plain, (![A_73]: (r2_hidden('#skF_1'(A_73, k1_xboole_0), k1_xboole_0) | ~m1_subset_1(A_73, k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0=A_73)), inference(resolution, [status(thm)], [c_178, c_4])).
% 4.45/1.80  tff(c_199, plain, (![A_73]: (~r1_tarski(k1_xboole_0, '#skF_1'(A_73, k1_xboole_0)) | ~m1_subset_1(A_73, k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0=A_73)), inference(resolution, [status(thm)], [c_191, c_16])).
% 4.45/1.80  tff(c_205, plain, (![A_73]: (~m1_subset_1(A_73, k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0=A_73)), inference(demodulation, [status(thm), theory('equality')], [c_10, c_199])).
% 4.45/1.80  tff(c_1471, plain, (![A_338]: (~m1_subset_1(A_338, k1_zfmisc_1('#skF_4')) | A_338='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1424, c_1424, c_205])).
% 4.45/1.80  tff(c_1474, plain, (k2_relat_1('#skF_5')='#skF_4'), inference(resolution, [status(thm)], [c_246, c_1471])).
% 4.45/1.80  tff(c_1482, plain, $false, inference(negUnitSimplification, [status(thm)], [c_111, c_1474])).
% 4.45/1.80  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.45/1.80  
% 4.45/1.80  Inference rules
% 4.45/1.80  ----------------------
% 4.45/1.80  #Ref     : 0
% 4.45/1.80  #Sup     : 297
% 4.45/1.80  #Fact    : 0
% 4.45/1.80  #Define  : 0
% 4.45/1.80  #Split   : 8
% 4.45/1.80  #Chain   : 0
% 4.45/1.80  #Close   : 0
% 4.45/1.80  
% 4.45/1.80  Ordering : KBO
% 4.45/1.80  
% 4.45/1.80  Simplification rules
% 4.45/1.80  ----------------------
% 4.45/1.80  #Subsume      : 78
% 4.45/1.80  #Demod        : 84
% 4.45/1.80  #Tautology    : 41
% 4.45/1.80  #SimpNegUnit  : 5
% 4.45/1.80  #BackRed      : 31
% 4.45/1.80  
% 4.45/1.80  #Partial instantiations: 0
% 4.45/1.80  #Strategies tried      : 1
% 4.45/1.80  
% 4.45/1.80  Timing (in seconds)
% 4.45/1.80  ----------------------
% 4.45/1.80  Preprocessing        : 0.33
% 4.45/1.80  Parsing              : 0.17
% 4.45/1.80  CNF conversion       : 0.02
% 4.45/1.80  Main loop            : 0.69
% 4.45/1.80  Inferencing          : 0.25
% 4.45/1.80  Reduction            : 0.17
% 4.45/1.80  Demodulation         : 0.11
% 4.45/1.80  BG Simplification    : 0.03
% 4.45/1.80  Subsumption          : 0.19
% 4.45/1.80  Abstraction          : 0.03
% 4.45/1.80  MUC search           : 0.00
% 4.45/1.80  Cooper               : 0.00
% 4.45/1.80  Total                : 1.06
% 4.45/1.80  Index Insertion      : 0.00
% 4.45/1.80  Index Deletion       : 0.00
% 4.45/1.80  Index Matching       : 0.00
% 4.45/1.80  BG Taut test         : 0.00
%------------------------------------------------------------------------------
