%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:17:44 EST 2020

% Result     : Theorem 3.07s
% Output     : CNFRefutation 3.32s
% Verified   : 
% Statistics : Number of formulae       :   95 ( 214 expanded)
%              Number of leaves         :   39 (  97 expanded)
%              Depth                    :    9
%              Number of atoms          :  197 ( 884 expanded)
%              Number of equality atoms :   45 ( 190 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k8_funct_2 > k2_relset_1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_3 > #skF_8 > #skF_4 > #skF_2

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

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k1_partfun1,type,(
    k1_partfun1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff(k8_funct_2,type,(
    k8_funct_2: ( $i * $i * $i * $i * $i ) > $i )).

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

tff('#skF_8',type,(
    '#skF_8': $i )).

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_135,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ~ v1_xboole_0(C)
       => ! [D] :
            ( ( v1_funct_1(D)
              & v1_funct_2(D,B,C)
              & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,C))) )
           => ! [E] :
                ( ( v1_funct_1(E)
                  & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(C,A))) )
               => ! [F] :
                    ( m1_subset_1(F,B)
                   => ( r1_tarski(k2_relset_1(B,C,D),k1_relset_1(C,A,E))
                     => ( B = k1_xboole_0
                        | k1_funct_1(k8_funct_2(B,C,A,D,E),F) = k1_funct_1(E,k1_funct_1(D,F)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t185_funct_2)).

tff(f_61,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_59,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_83,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ! [E] :
          ( ( v1_funct_1(E)
            & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(B,C))) )
         => ( r1_tarski(k2_relset_1(A,B,D),k1_relset_1(B,C,E))
           => ( B = k1_xboole_0
              | k8_funct_2(A,B,C,D,E) = k1_partfun1(A,B,B,C,D,E) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d12_funct_2)).

tff(f_46,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_66,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

tff(f_110,axiom,(
    ! [A,B,C,D] :
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

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_44,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_52,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_93,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(c_40,plain,(
    m1_subset_1('#skF_8','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_24,plain,(
    ! [A_18,B_19] : v1_relat_1(k2_zfmisc_1(A_18,B_19)) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_42,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_98,plain,(
    ! [B_67,A_68] :
      ( v1_relat_1(B_67)
      | ~ m1_subset_1(B_67,k1_zfmisc_1(A_68))
      | ~ v1_relat_1(A_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_101,plain,
    ( v1_relat_1('#skF_7')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_5','#skF_3')) ),
    inference(resolution,[status(thm)],[c_42,c_98])).

tff(c_107,plain,(
    v1_relat_1('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_101])).

tff(c_44,plain,(
    v1_funct_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_36,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_52,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_50,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_48,plain,(
    v1_funct_2('#skF_6','#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_46,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_38,plain,(
    r1_tarski(k2_relset_1('#skF_4','#skF_5','#skF_6'),k1_relset_1('#skF_5','#skF_3','#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_442,plain,(
    ! [C_132,A_130,D_133,E_131,B_134] :
      ( k1_partfun1(A_130,B_134,B_134,C_132,D_133,E_131) = k8_funct_2(A_130,B_134,C_132,D_133,E_131)
      | k1_xboole_0 = B_134
      | ~ r1_tarski(k2_relset_1(A_130,B_134,D_133),k1_relset_1(B_134,C_132,E_131))
      | ~ m1_subset_1(E_131,k1_zfmisc_1(k2_zfmisc_1(B_134,C_132)))
      | ~ v1_funct_1(E_131)
      | ~ m1_subset_1(D_133,k1_zfmisc_1(k2_zfmisc_1(A_130,B_134)))
      | ~ v1_funct_2(D_133,A_130,B_134)
      | ~ v1_funct_1(D_133) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_445,plain,
    ( k1_partfun1('#skF_4','#skF_5','#skF_5','#skF_3','#skF_6','#skF_7') = k8_funct_2('#skF_4','#skF_5','#skF_3','#skF_6','#skF_7')
    | k1_xboole_0 = '#skF_5'
    | ~ m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_3')))
    | ~ v1_funct_1('#skF_7')
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_5')))
    | ~ v1_funct_2('#skF_6','#skF_4','#skF_5')
    | ~ v1_funct_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_38,c_442])).

tff(c_451,plain,
    ( k1_partfun1('#skF_4','#skF_5','#skF_5','#skF_3','#skF_6','#skF_7') = k8_funct_2('#skF_4','#skF_5','#skF_3','#skF_6','#skF_7')
    | k1_xboole_0 = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_46,c_44,c_42,c_445])).

tff(c_453,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_451])).

tff(c_18,plain,(
    ! [A_12] : r1_tarski(k1_xboole_0,A_12) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_59,plain,(
    ! [A_59] :
      ( v1_xboole_0(A_59)
      | r2_hidden('#skF_1'(A_59),A_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_26,plain,(
    ! [B_21,A_20] :
      ( ~ r1_tarski(B_21,A_20)
      | ~ r2_hidden(A_20,B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_68,plain,(
    ! [A_60] :
      ( ~ r1_tarski(A_60,'#skF_1'(A_60))
      | v1_xboole_0(A_60) ) ),
    inference(resolution,[status(thm)],[c_59,c_26])).

tff(c_73,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_18,c_68])).

tff(c_460,plain,(
    v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_453,c_73])).

tff(c_464,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_460])).

tff(c_466,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(splitRight,[status(thm)],[c_451])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_348,plain,(
    ! [C_115,A_111,D_112,B_113,E_114] :
      ( k1_funct_1(k5_relat_1(D_112,E_114),C_115) = k1_funct_1(E_114,k1_funct_1(D_112,C_115))
      | k1_xboole_0 = B_113
      | ~ r2_hidden(C_115,A_111)
      | ~ v1_funct_1(E_114)
      | ~ v1_relat_1(E_114)
      | ~ m1_subset_1(D_112,k1_zfmisc_1(k2_zfmisc_1(A_111,B_113)))
      | ~ v1_funct_2(D_112,A_111,B_113)
      | ~ v1_funct_1(D_112) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_552,plain,(
    ! [D_141,E_142,A_143,B_144] :
      ( k1_funct_1(k5_relat_1(D_141,E_142),'#skF_1'(A_143)) = k1_funct_1(E_142,k1_funct_1(D_141,'#skF_1'(A_143)))
      | k1_xboole_0 = B_144
      | ~ v1_funct_1(E_142)
      | ~ v1_relat_1(E_142)
      | ~ m1_subset_1(D_141,k1_zfmisc_1(k2_zfmisc_1(A_143,B_144)))
      | ~ v1_funct_2(D_141,A_143,B_144)
      | ~ v1_funct_1(D_141)
      | v1_xboole_0(A_143) ) ),
    inference(resolution,[status(thm)],[c_4,c_348])).

tff(c_556,plain,(
    ! [E_142] :
      ( k1_funct_1(k5_relat_1('#skF_6',E_142),'#skF_1'('#skF_4')) = k1_funct_1(E_142,k1_funct_1('#skF_6','#skF_1'('#skF_4')))
      | k1_xboole_0 = '#skF_5'
      | ~ v1_funct_1(E_142)
      | ~ v1_relat_1(E_142)
      | ~ v1_funct_2('#skF_6','#skF_4','#skF_5')
      | ~ v1_funct_1('#skF_6')
      | v1_xboole_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_46,c_552])).

tff(c_563,plain,(
    ! [E_142] :
      ( k1_funct_1(k5_relat_1('#skF_6',E_142),'#skF_1'('#skF_4')) = k1_funct_1(E_142,k1_funct_1('#skF_6','#skF_1'('#skF_4')))
      | k1_xboole_0 = '#skF_5'
      | ~ v1_funct_1(E_142)
      | ~ v1_relat_1(E_142)
      | v1_xboole_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_556])).

tff(c_564,plain,(
    ! [E_142] :
      ( k1_funct_1(k5_relat_1('#skF_6',E_142),'#skF_1'('#skF_4')) = k1_funct_1(E_142,k1_funct_1('#skF_6','#skF_1'('#skF_4')))
      | ~ v1_funct_1(E_142)
      | ~ v1_relat_1(E_142)
      | v1_xboole_0('#skF_4') ) ),
    inference(negUnitSimplification,[status(thm)],[c_466,c_563])).

tff(c_569,plain,(
    v1_xboole_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_564])).

tff(c_74,plain,(
    ! [A_61,B_62] :
      ( r2_hidden('#skF_2'(A_61,B_62),A_61)
      | r1_tarski(A_61,B_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_82,plain,(
    ! [A_61,B_62] :
      ( ~ v1_xboole_0(A_61)
      | r1_tarski(A_61,B_62) ) ),
    inference(resolution,[status(thm)],[c_74,c_2])).

tff(c_111,plain,(
    ! [B_69,A_70] :
      ( B_69 = A_70
      | ~ r1_tarski(B_69,A_70)
      | ~ r1_tarski(A_70,B_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_127,plain,(
    ! [A_71] :
      ( k1_xboole_0 = A_71
      | ~ r1_tarski(A_71,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_18,c_111])).

tff(c_140,plain,(
    ! [A_61] :
      ( k1_xboole_0 = A_61
      | ~ v1_xboole_0(A_61) ) ),
    inference(resolution,[status(thm)],[c_82,c_127])).

tff(c_575,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_569,c_140])).

tff(c_580,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_575])).

tff(c_582,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_564])).

tff(c_20,plain,(
    ! [A_13,B_14] :
      ( r2_hidden(A_13,B_14)
      | v1_xboole_0(B_14)
      | ~ m1_subset_1(A_13,B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_600,plain,(
    ! [E_148,B_152,D_151,B_149,A_150] :
      ( k1_funct_1(k5_relat_1(D_151,E_148),A_150) = k1_funct_1(E_148,k1_funct_1(D_151,A_150))
      | k1_xboole_0 = B_152
      | ~ v1_funct_1(E_148)
      | ~ v1_relat_1(E_148)
      | ~ m1_subset_1(D_151,k1_zfmisc_1(k2_zfmisc_1(B_149,B_152)))
      | ~ v1_funct_2(D_151,B_149,B_152)
      | ~ v1_funct_1(D_151)
      | v1_xboole_0(B_149)
      | ~ m1_subset_1(A_150,B_149) ) ),
    inference(resolution,[status(thm)],[c_20,c_348])).

tff(c_604,plain,(
    ! [E_148,A_150] :
      ( k1_funct_1(k5_relat_1('#skF_6',E_148),A_150) = k1_funct_1(E_148,k1_funct_1('#skF_6',A_150))
      | k1_xboole_0 = '#skF_5'
      | ~ v1_funct_1(E_148)
      | ~ v1_relat_1(E_148)
      | ~ v1_funct_2('#skF_6','#skF_4','#skF_5')
      | ~ v1_funct_1('#skF_6')
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(A_150,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_46,c_600])).

tff(c_611,plain,(
    ! [E_148,A_150] :
      ( k1_funct_1(k5_relat_1('#skF_6',E_148),A_150) = k1_funct_1(E_148,k1_funct_1('#skF_6',A_150))
      | k1_xboole_0 = '#skF_5'
      | ~ v1_funct_1(E_148)
      | ~ v1_relat_1(E_148)
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(A_150,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_604])).

tff(c_613,plain,(
    ! [E_153,A_154] :
      ( k1_funct_1(k5_relat_1('#skF_6',E_153),A_154) = k1_funct_1(E_153,k1_funct_1('#skF_6',A_154))
      | ~ v1_funct_1(E_153)
      | ~ v1_relat_1(E_153)
      | ~ m1_subset_1(A_154,'#skF_4') ) ),
    inference(negUnitSimplification,[status(thm)],[c_582,c_466,c_611])).

tff(c_465,plain,(
    k1_partfun1('#skF_4','#skF_5','#skF_5','#skF_3','#skF_6','#skF_7') = k8_funct_2('#skF_4','#skF_5','#skF_3','#skF_6','#skF_7') ),
    inference(splitRight,[status(thm)],[c_451])).

tff(c_238,plain,(
    ! [C_92,E_90,F_89,D_94,B_93,A_91] :
      ( k1_partfun1(A_91,B_93,C_92,D_94,E_90,F_89) = k5_relat_1(E_90,F_89)
      | ~ m1_subset_1(F_89,k1_zfmisc_1(k2_zfmisc_1(C_92,D_94)))
      | ~ v1_funct_1(F_89)
      | ~ m1_subset_1(E_90,k1_zfmisc_1(k2_zfmisc_1(A_91,B_93)))
      | ~ v1_funct_1(E_90) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_240,plain,(
    ! [A_91,B_93,E_90] :
      ( k1_partfun1(A_91,B_93,'#skF_5','#skF_3',E_90,'#skF_7') = k5_relat_1(E_90,'#skF_7')
      | ~ v1_funct_1('#skF_7')
      | ~ m1_subset_1(E_90,k1_zfmisc_1(k2_zfmisc_1(A_91,B_93)))
      | ~ v1_funct_1(E_90) ) ),
    inference(resolution,[status(thm)],[c_42,c_238])).

tff(c_529,plain,(
    ! [A_138,B_139,E_140] :
      ( k1_partfun1(A_138,B_139,'#skF_5','#skF_3',E_140,'#skF_7') = k5_relat_1(E_140,'#skF_7')
      | ~ m1_subset_1(E_140,k1_zfmisc_1(k2_zfmisc_1(A_138,B_139)))
      | ~ v1_funct_1(E_140) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_240])).

tff(c_535,plain,
    ( k1_partfun1('#skF_4','#skF_5','#skF_5','#skF_3','#skF_6','#skF_7') = k5_relat_1('#skF_6','#skF_7')
    | ~ v1_funct_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_46,c_529])).

tff(c_541,plain,(
    k8_funct_2('#skF_4','#skF_5','#skF_3','#skF_6','#skF_7') = k5_relat_1('#skF_6','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_465,c_535])).

tff(c_34,plain,(
    k1_funct_1(k8_funct_2('#skF_4','#skF_5','#skF_3','#skF_6','#skF_7'),'#skF_8') != k1_funct_1('#skF_7',k1_funct_1('#skF_6','#skF_8')) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_543,plain,(
    k1_funct_1(k5_relat_1('#skF_6','#skF_7'),'#skF_8') != k1_funct_1('#skF_7',k1_funct_1('#skF_6','#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_541,c_34])).

tff(c_623,plain,
    ( ~ v1_funct_1('#skF_7')
    | ~ v1_relat_1('#skF_7')
    | ~ m1_subset_1('#skF_8','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_613,c_543])).

tff(c_635,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_107,c_44,c_623])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:40:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.07/1.50  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.07/1.51  
% 3.07/1.51  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.07/1.51  %$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k8_funct_2 > k2_relset_1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_3 > #skF_8 > #skF_4 > #skF_2
% 3.07/1.51  
% 3.07/1.51  %Foreground sorts:
% 3.07/1.51  
% 3.07/1.51  
% 3.07/1.51  %Background operators:
% 3.07/1.51  
% 3.07/1.51  
% 3.07/1.51  %Foreground operators:
% 3.07/1.51  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 3.07/1.51  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.07/1.51  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.07/1.51  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.07/1.51  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.07/1.51  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.07/1.51  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 3.07/1.51  tff('#skF_7', type, '#skF_7': $i).
% 3.07/1.51  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.07/1.51  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.07/1.51  tff('#skF_5', type, '#skF_5': $i).
% 3.07/1.51  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.07/1.51  tff(k8_funct_2, type, k8_funct_2: ($i * $i * $i * $i * $i) > $i).
% 3.07/1.51  tff('#skF_6', type, '#skF_6': $i).
% 3.07/1.51  tff('#skF_3', type, '#skF_3': $i).
% 3.07/1.51  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.07/1.51  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.07/1.51  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.07/1.51  tff('#skF_8', type, '#skF_8': $i).
% 3.07/1.51  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.07/1.51  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.07/1.51  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.07/1.51  tff('#skF_4', type, '#skF_4': $i).
% 3.07/1.51  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.07/1.51  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.07/1.51  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.07/1.51  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.07/1.51  
% 3.32/1.53  tff(f_135, negated_conjecture, ~(![A, B, C]: (~v1_xboole_0(C) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, C)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (![E]: ((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(C, A)))) => (![F]: (m1_subset_1(F, B) => (r1_tarski(k2_relset_1(B, C, D), k1_relset_1(C, A, E)) => ((B = k1_xboole_0) | (k1_funct_1(k8_funct_2(B, C, A, D, E), F) = k1_funct_1(E, k1_funct_1(D, F))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t185_funct_2)).
% 3.32/1.53  tff(f_61, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 3.32/1.53  tff(f_59, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 3.32/1.53  tff(f_83, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: ((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (r1_tarski(k2_relset_1(A, B, D), k1_relset_1(B, C, E)) => ((B = k1_xboole_0) | (k8_funct_2(A, B, C, D, E) = k1_partfun1(A, B, B, C, D, E)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d12_funct_2)).
% 3.32/1.53  tff(f_46, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 3.32/1.53  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 3.32/1.53  tff(f_66, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 3.32/1.53  tff(f_110, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: ((v1_relat_1(E) & v1_funct_1(E)) => (r2_hidden(C, A) => ((B = k1_xboole_0) | (k1_funct_1(k5_relat_1(D, E), C) = k1_funct_1(E, k1_funct_1(D, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t21_funct_2)).
% 3.32/1.53  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 3.32/1.53  tff(f_44, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.32/1.53  tff(f_52, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 3.32/1.53  tff(f_93, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 3.32/1.53  tff(c_40, plain, (m1_subset_1('#skF_8', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_135])).
% 3.32/1.53  tff(c_24, plain, (![A_18, B_19]: (v1_relat_1(k2_zfmisc_1(A_18, B_19)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.32/1.53  tff(c_42, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_135])).
% 3.32/1.53  tff(c_98, plain, (![B_67, A_68]: (v1_relat_1(B_67) | ~m1_subset_1(B_67, k1_zfmisc_1(A_68)) | ~v1_relat_1(A_68))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.32/1.53  tff(c_101, plain, (v1_relat_1('#skF_7') | ~v1_relat_1(k2_zfmisc_1('#skF_5', '#skF_3'))), inference(resolution, [status(thm)], [c_42, c_98])).
% 3.32/1.53  tff(c_107, plain, (v1_relat_1('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_24, c_101])).
% 3.32/1.53  tff(c_44, plain, (v1_funct_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_135])).
% 3.32/1.53  tff(c_36, plain, (k1_xboole_0!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_135])).
% 3.32/1.53  tff(c_52, plain, (~v1_xboole_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_135])).
% 3.32/1.53  tff(c_50, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_135])).
% 3.32/1.53  tff(c_48, plain, (v1_funct_2('#skF_6', '#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_135])).
% 3.32/1.53  tff(c_46, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_5')))), inference(cnfTransformation, [status(thm)], [f_135])).
% 3.32/1.53  tff(c_38, plain, (r1_tarski(k2_relset_1('#skF_4', '#skF_5', '#skF_6'), k1_relset_1('#skF_5', '#skF_3', '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_135])).
% 3.32/1.53  tff(c_442, plain, (![C_132, A_130, D_133, E_131, B_134]: (k1_partfun1(A_130, B_134, B_134, C_132, D_133, E_131)=k8_funct_2(A_130, B_134, C_132, D_133, E_131) | k1_xboole_0=B_134 | ~r1_tarski(k2_relset_1(A_130, B_134, D_133), k1_relset_1(B_134, C_132, E_131)) | ~m1_subset_1(E_131, k1_zfmisc_1(k2_zfmisc_1(B_134, C_132))) | ~v1_funct_1(E_131) | ~m1_subset_1(D_133, k1_zfmisc_1(k2_zfmisc_1(A_130, B_134))) | ~v1_funct_2(D_133, A_130, B_134) | ~v1_funct_1(D_133))), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.32/1.53  tff(c_445, plain, (k1_partfun1('#skF_4', '#skF_5', '#skF_5', '#skF_3', '#skF_6', '#skF_7')=k8_funct_2('#skF_4', '#skF_5', '#skF_3', '#skF_6', '#skF_7') | k1_xboole_0='#skF_5' | ~m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_3'))) | ~v1_funct_1('#skF_7') | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_5'))) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_5') | ~v1_funct_1('#skF_6')), inference(resolution, [status(thm)], [c_38, c_442])).
% 3.32/1.53  tff(c_451, plain, (k1_partfun1('#skF_4', '#skF_5', '#skF_5', '#skF_3', '#skF_6', '#skF_7')=k8_funct_2('#skF_4', '#skF_5', '#skF_3', '#skF_6', '#skF_7') | k1_xboole_0='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_46, c_44, c_42, c_445])).
% 3.32/1.53  tff(c_453, plain, (k1_xboole_0='#skF_5'), inference(splitLeft, [status(thm)], [c_451])).
% 3.32/1.53  tff(c_18, plain, (![A_12]: (r1_tarski(k1_xboole_0, A_12))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.32/1.53  tff(c_59, plain, (![A_59]: (v1_xboole_0(A_59) | r2_hidden('#skF_1'(A_59), A_59))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.32/1.53  tff(c_26, plain, (![B_21, A_20]: (~r1_tarski(B_21, A_20) | ~r2_hidden(A_20, B_21))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.32/1.53  tff(c_68, plain, (![A_60]: (~r1_tarski(A_60, '#skF_1'(A_60)) | v1_xboole_0(A_60))), inference(resolution, [status(thm)], [c_59, c_26])).
% 3.32/1.53  tff(c_73, plain, (v1_xboole_0(k1_xboole_0)), inference(resolution, [status(thm)], [c_18, c_68])).
% 3.32/1.53  tff(c_460, plain, (v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_453, c_73])).
% 3.32/1.53  tff(c_464, plain, $false, inference(negUnitSimplification, [status(thm)], [c_52, c_460])).
% 3.32/1.53  tff(c_466, plain, (k1_xboole_0!='#skF_5'), inference(splitRight, [status(thm)], [c_451])).
% 3.32/1.53  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.32/1.53  tff(c_348, plain, (![C_115, A_111, D_112, B_113, E_114]: (k1_funct_1(k5_relat_1(D_112, E_114), C_115)=k1_funct_1(E_114, k1_funct_1(D_112, C_115)) | k1_xboole_0=B_113 | ~r2_hidden(C_115, A_111) | ~v1_funct_1(E_114) | ~v1_relat_1(E_114) | ~m1_subset_1(D_112, k1_zfmisc_1(k2_zfmisc_1(A_111, B_113))) | ~v1_funct_2(D_112, A_111, B_113) | ~v1_funct_1(D_112))), inference(cnfTransformation, [status(thm)], [f_110])).
% 3.32/1.53  tff(c_552, plain, (![D_141, E_142, A_143, B_144]: (k1_funct_1(k5_relat_1(D_141, E_142), '#skF_1'(A_143))=k1_funct_1(E_142, k1_funct_1(D_141, '#skF_1'(A_143))) | k1_xboole_0=B_144 | ~v1_funct_1(E_142) | ~v1_relat_1(E_142) | ~m1_subset_1(D_141, k1_zfmisc_1(k2_zfmisc_1(A_143, B_144))) | ~v1_funct_2(D_141, A_143, B_144) | ~v1_funct_1(D_141) | v1_xboole_0(A_143))), inference(resolution, [status(thm)], [c_4, c_348])).
% 3.32/1.53  tff(c_556, plain, (![E_142]: (k1_funct_1(k5_relat_1('#skF_6', E_142), '#skF_1'('#skF_4'))=k1_funct_1(E_142, k1_funct_1('#skF_6', '#skF_1'('#skF_4'))) | k1_xboole_0='#skF_5' | ~v1_funct_1(E_142) | ~v1_relat_1(E_142) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_5') | ~v1_funct_1('#skF_6') | v1_xboole_0('#skF_4'))), inference(resolution, [status(thm)], [c_46, c_552])).
% 3.32/1.53  tff(c_563, plain, (![E_142]: (k1_funct_1(k5_relat_1('#skF_6', E_142), '#skF_1'('#skF_4'))=k1_funct_1(E_142, k1_funct_1('#skF_6', '#skF_1'('#skF_4'))) | k1_xboole_0='#skF_5' | ~v1_funct_1(E_142) | ~v1_relat_1(E_142) | v1_xboole_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_556])).
% 3.32/1.53  tff(c_564, plain, (![E_142]: (k1_funct_1(k5_relat_1('#skF_6', E_142), '#skF_1'('#skF_4'))=k1_funct_1(E_142, k1_funct_1('#skF_6', '#skF_1'('#skF_4'))) | ~v1_funct_1(E_142) | ~v1_relat_1(E_142) | v1_xboole_0('#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_466, c_563])).
% 3.32/1.53  tff(c_569, plain, (v1_xboole_0('#skF_4')), inference(splitLeft, [status(thm)], [c_564])).
% 3.32/1.53  tff(c_74, plain, (![A_61, B_62]: (r2_hidden('#skF_2'(A_61, B_62), A_61) | r1_tarski(A_61, B_62))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.32/1.53  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.32/1.53  tff(c_82, plain, (![A_61, B_62]: (~v1_xboole_0(A_61) | r1_tarski(A_61, B_62))), inference(resolution, [status(thm)], [c_74, c_2])).
% 3.32/1.53  tff(c_111, plain, (![B_69, A_70]: (B_69=A_70 | ~r1_tarski(B_69, A_70) | ~r1_tarski(A_70, B_69))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.32/1.53  tff(c_127, plain, (![A_71]: (k1_xboole_0=A_71 | ~r1_tarski(A_71, k1_xboole_0))), inference(resolution, [status(thm)], [c_18, c_111])).
% 3.32/1.53  tff(c_140, plain, (![A_61]: (k1_xboole_0=A_61 | ~v1_xboole_0(A_61))), inference(resolution, [status(thm)], [c_82, c_127])).
% 3.32/1.53  tff(c_575, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_569, c_140])).
% 3.32/1.53  tff(c_580, plain, $false, inference(negUnitSimplification, [status(thm)], [c_36, c_575])).
% 3.32/1.53  tff(c_582, plain, (~v1_xboole_0('#skF_4')), inference(splitRight, [status(thm)], [c_564])).
% 3.32/1.53  tff(c_20, plain, (![A_13, B_14]: (r2_hidden(A_13, B_14) | v1_xboole_0(B_14) | ~m1_subset_1(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.32/1.53  tff(c_600, plain, (![E_148, B_152, D_151, B_149, A_150]: (k1_funct_1(k5_relat_1(D_151, E_148), A_150)=k1_funct_1(E_148, k1_funct_1(D_151, A_150)) | k1_xboole_0=B_152 | ~v1_funct_1(E_148) | ~v1_relat_1(E_148) | ~m1_subset_1(D_151, k1_zfmisc_1(k2_zfmisc_1(B_149, B_152))) | ~v1_funct_2(D_151, B_149, B_152) | ~v1_funct_1(D_151) | v1_xboole_0(B_149) | ~m1_subset_1(A_150, B_149))), inference(resolution, [status(thm)], [c_20, c_348])).
% 3.32/1.53  tff(c_604, plain, (![E_148, A_150]: (k1_funct_1(k5_relat_1('#skF_6', E_148), A_150)=k1_funct_1(E_148, k1_funct_1('#skF_6', A_150)) | k1_xboole_0='#skF_5' | ~v1_funct_1(E_148) | ~v1_relat_1(E_148) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_5') | ~v1_funct_1('#skF_6') | v1_xboole_0('#skF_4') | ~m1_subset_1(A_150, '#skF_4'))), inference(resolution, [status(thm)], [c_46, c_600])).
% 3.32/1.53  tff(c_611, plain, (![E_148, A_150]: (k1_funct_1(k5_relat_1('#skF_6', E_148), A_150)=k1_funct_1(E_148, k1_funct_1('#skF_6', A_150)) | k1_xboole_0='#skF_5' | ~v1_funct_1(E_148) | ~v1_relat_1(E_148) | v1_xboole_0('#skF_4') | ~m1_subset_1(A_150, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_604])).
% 3.32/1.53  tff(c_613, plain, (![E_153, A_154]: (k1_funct_1(k5_relat_1('#skF_6', E_153), A_154)=k1_funct_1(E_153, k1_funct_1('#skF_6', A_154)) | ~v1_funct_1(E_153) | ~v1_relat_1(E_153) | ~m1_subset_1(A_154, '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_582, c_466, c_611])).
% 3.32/1.53  tff(c_465, plain, (k1_partfun1('#skF_4', '#skF_5', '#skF_5', '#skF_3', '#skF_6', '#skF_7')=k8_funct_2('#skF_4', '#skF_5', '#skF_3', '#skF_6', '#skF_7')), inference(splitRight, [status(thm)], [c_451])).
% 3.32/1.53  tff(c_238, plain, (![C_92, E_90, F_89, D_94, B_93, A_91]: (k1_partfun1(A_91, B_93, C_92, D_94, E_90, F_89)=k5_relat_1(E_90, F_89) | ~m1_subset_1(F_89, k1_zfmisc_1(k2_zfmisc_1(C_92, D_94))) | ~v1_funct_1(F_89) | ~m1_subset_1(E_90, k1_zfmisc_1(k2_zfmisc_1(A_91, B_93))) | ~v1_funct_1(E_90))), inference(cnfTransformation, [status(thm)], [f_93])).
% 3.32/1.53  tff(c_240, plain, (![A_91, B_93, E_90]: (k1_partfun1(A_91, B_93, '#skF_5', '#skF_3', E_90, '#skF_7')=k5_relat_1(E_90, '#skF_7') | ~v1_funct_1('#skF_7') | ~m1_subset_1(E_90, k1_zfmisc_1(k2_zfmisc_1(A_91, B_93))) | ~v1_funct_1(E_90))), inference(resolution, [status(thm)], [c_42, c_238])).
% 3.32/1.53  tff(c_529, plain, (![A_138, B_139, E_140]: (k1_partfun1(A_138, B_139, '#skF_5', '#skF_3', E_140, '#skF_7')=k5_relat_1(E_140, '#skF_7') | ~m1_subset_1(E_140, k1_zfmisc_1(k2_zfmisc_1(A_138, B_139))) | ~v1_funct_1(E_140))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_240])).
% 3.32/1.53  tff(c_535, plain, (k1_partfun1('#skF_4', '#skF_5', '#skF_5', '#skF_3', '#skF_6', '#skF_7')=k5_relat_1('#skF_6', '#skF_7') | ~v1_funct_1('#skF_6')), inference(resolution, [status(thm)], [c_46, c_529])).
% 3.32/1.53  tff(c_541, plain, (k8_funct_2('#skF_4', '#skF_5', '#skF_3', '#skF_6', '#skF_7')=k5_relat_1('#skF_6', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_465, c_535])).
% 3.32/1.53  tff(c_34, plain, (k1_funct_1(k8_funct_2('#skF_4', '#skF_5', '#skF_3', '#skF_6', '#skF_7'), '#skF_8')!=k1_funct_1('#skF_7', k1_funct_1('#skF_6', '#skF_8'))), inference(cnfTransformation, [status(thm)], [f_135])).
% 3.32/1.53  tff(c_543, plain, (k1_funct_1(k5_relat_1('#skF_6', '#skF_7'), '#skF_8')!=k1_funct_1('#skF_7', k1_funct_1('#skF_6', '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_541, c_34])).
% 3.32/1.53  tff(c_623, plain, (~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7') | ~m1_subset_1('#skF_8', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_613, c_543])).
% 3.32/1.53  tff(c_635, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_40, c_107, c_44, c_623])).
% 3.32/1.53  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.32/1.53  
% 3.32/1.53  Inference rules
% 3.32/1.53  ----------------------
% 3.32/1.53  #Ref     : 0
% 3.32/1.53  #Sup     : 124
% 3.32/1.53  #Fact    : 0
% 3.32/1.53  #Define  : 0
% 3.32/1.53  #Split   : 7
% 3.32/1.53  #Chain   : 0
% 3.32/1.53  #Close   : 0
% 3.32/1.53  
% 3.32/1.53  Ordering : KBO
% 3.32/1.53  
% 3.32/1.53  Simplification rules
% 3.32/1.53  ----------------------
% 3.32/1.53  #Subsume      : 28
% 3.32/1.53  #Demod        : 65
% 3.32/1.53  #Tautology    : 46
% 3.32/1.53  #SimpNegUnit  : 7
% 3.32/1.53  #BackRed      : 17
% 3.32/1.53  
% 3.32/1.53  #Partial instantiations: 0
% 3.32/1.53  #Strategies tried      : 1
% 3.32/1.53  
% 3.32/1.53  Timing (in seconds)
% 3.32/1.53  ----------------------
% 3.32/1.54  Preprocessing        : 0.35
% 3.32/1.54  Parsing              : 0.18
% 3.32/1.54  CNF conversion       : 0.03
% 3.32/1.54  Main loop            : 0.40
% 3.32/1.54  Inferencing          : 0.14
% 3.32/1.54  Reduction            : 0.12
% 3.32/1.54  Demodulation         : 0.09
% 3.32/1.54  BG Simplification    : 0.02
% 3.32/1.54  Subsumption          : 0.09
% 3.32/1.54  Abstraction          : 0.02
% 3.32/1.54  MUC search           : 0.00
% 3.32/1.54  Cooper               : 0.00
% 3.32/1.54  Total                : 0.79
% 3.32/1.54  Index Insertion      : 0.00
% 3.32/1.54  Index Deletion       : 0.00
% 3.32/1.54  Index Matching       : 0.00
% 3.32/1.54  BG Taut test         : 0.00
%------------------------------------------------------------------------------
