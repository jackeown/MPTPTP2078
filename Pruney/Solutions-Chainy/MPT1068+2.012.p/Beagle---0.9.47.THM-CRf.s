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
% DateTime   : Thu Dec  3 10:17:42 EST 2020

% Result     : Theorem 2.80s
% Output     : CNFRefutation 3.19s
% Verified   : 
% Statistics : Number of formulae       :   91 ( 211 expanded)
%              Number of leaves         :   38 (  96 expanded)
%              Depth                    :    9
%              Number of atoms          :  189 ( 878 expanded)
%              Number of equality atoms :   45 ( 190 expanded)
%              Maximal formula depth    :   15 (   5 average)
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

tff(f_130,negated_conjecture,(
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
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_78,axiom,(
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

tff(f_57,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

tff(f_105,axiom,(
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

tff(f_88,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(c_38,plain,(
    m1_subset_1('#skF_8','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_40,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_71,plain,(
    ! [C_57,A_58,B_59] :
      ( v1_relat_1(C_57)
      | ~ m1_subset_1(C_57,k1_zfmisc_1(k2_zfmisc_1(A_58,B_59))) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_78,plain,(
    v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_40,c_71])).

tff(c_42,plain,(
    v1_funct_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_34,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_50,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_48,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_46,plain,(
    v1_funct_2('#skF_6','#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_44,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_36,plain,(
    r1_tarski(k2_relset_1('#skF_4','#skF_5','#skF_6'),k1_relset_1('#skF_5','#skF_3','#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_436,plain,(
    ! [A_130,E_131,D_129,C_127,B_128] :
      ( k1_partfun1(A_130,B_128,B_128,C_127,D_129,E_131) = k8_funct_2(A_130,B_128,C_127,D_129,E_131)
      | k1_xboole_0 = B_128
      | ~ r1_tarski(k2_relset_1(A_130,B_128,D_129),k1_relset_1(B_128,C_127,E_131))
      | ~ m1_subset_1(E_131,k1_zfmisc_1(k2_zfmisc_1(B_128,C_127)))
      | ~ v1_funct_1(E_131)
      | ~ m1_subset_1(D_129,k1_zfmisc_1(k2_zfmisc_1(A_130,B_128)))
      | ~ v1_funct_2(D_129,A_130,B_128)
      | ~ v1_funct_1(D_129) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_442,plain,
    ( k1_partfun1('#skF_4','#skF_5','#skF_5','#skF_3','#skF_6','#skF_7') = k8_funct_2('#skF_4','#skF_5','#skF_3','#skF_6','#skF_7')
    | k1_xboole_0 = '#skF_5'
    | ~ m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_3')))
    | ~ v1_funct_1('#skF_7')
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_5')))
    | ~ v1_funct_2('#skF_6','#skF_4','#skF_5')
    | ~ v1_funct_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_36,c_436])).

tff(c_446,plain,
    ( k1_partfun1('#skF_4','#skF_5','#skF_5','#skF_3','#skF_6','#skF_7') = k8_funct_2('#skF_4','#skF_5','#skF_3','#skF_6','#skF_7')
    | k1_xboole_0 = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_44,c_42,c_40,c_442])).

tff(c_451,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_446])).

tff(c_18,plain,(
    ! [A_12] : r1_tarski(k1_xboole_0,A_12) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_60,plain,(
    ! [B_54,A_55] :
      ( ~ r1_tarski(B_54,A_55)
      | ~ r2_hidden(A_55,B_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_65,plain,(
    ! [A_56] :
      ( ~ r1_tarski(A_56,'#skF_1'(A_56))
      | v1_xboole_0(A_56) ) ),
    inference(resolution,[status(thm)],[c_4,c_60])).

tff(c_70,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_18,c_65])).

tff(c_458,plain,(
    v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_451,c_70])).

tff(c_462,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_458])).

tff(c_464,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(splitRight,[status(thm)],[c_446])).

tff(c_357,plain,(
    ! [E_111,D_115,A_114,C_113,B_112] :
      ( k1_funct_1(k5_relat_1(D_115,E_111),C_113) = k1_funct_1(E_111,k1_funct_1(D_115,C_113))
      | k1_xboole_0 = B_112
      | ~ r2_hidden(C_113,A_114)
      | ~ v1_funct_1(E_111)
      | ~ v1_relat_1(E_111)
      | ~ m1_subset_1(D_115,k1_zfmisc_1(k2_zfmisc_1(A_114,B_112)))
      | ~ v1_funct_2(D_115,A_114,B_112)
      | ~ v1_funct_1(D_115) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_545,plain,(
    ! [D_138,E_139,A_140,B_141] :
      ( k1_funct_1(k5_relat_1(D_138,E_139),'#skF_1'(A_140)) = k1_funct_1(E_139,k1_funct_1(D_138,'#skF_1'(A_140)))
      | k1_xboole_0 = B_141
      | ~ v1_funct_1(E_139)
      | ~ v1_relat_1(E_139)
      | ~ m1_subset_1(D_138,k1_zfmisc_1(k2_zfmisc_1(A_140,B_141)))
      | ~ v1_funct_2(D_138,A_140,B_141)
      | ~ v1_funct_1(D_138)
      | v1_xboole_0(A_140) ) ),
    inference(resolution,[status(thm)],[c_4,c_357])).

tff(c_549,plain,(
    ! [E_139] :
      ( k1_funct_1(k5_relat_1('#skF_6',E_139),'#skF_1'('#skF_4')) = k1_funct_1(E_139,k1_funct_1('#skF_6','#skF_1'('#skF_4')))
      | k1_xboole_0 = '#skF_5'
      | ~ v1_funct_1(E_139)
      | ~ v1_relat_1(E_139)
      | ~ v1_funct_2('#skF_6','#skF_4','#skF_5')
      | ~ v1_funct_1('#skF_6')
      | v1_xboole_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_44,c_545])).

tff(c_556,plain,(
    ! [E_139] :
      ( k1_funct_1(k5_relat_1('#skF_6',E_139),'#skF_1'('#skF_4')) = k1_funct_1(E_139,k1_funct_1('#skF_6','#skF_1'('#skF_4')))
      | k1_xboole_0 = '#skF_5'
      | ~ v1_funct_1(E_139)
      | ~ v1_relat_1(E_139)
      | v1_xboole_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_549])).

tff(c_557,plain,(
    ! [E_139] :
      ( k1_funct_1(k5_relat_1('#skF_6',E_139),'#skF_1'('#skF_4')) = k1_funct_1(E_139,k1_funct_1('#skF_6','#skF_1'('#skF_4')))
      | ~ v1_funct_1(E_139)
      | ~ v1_relat_1(E_139)
      | v1_xboole_0('#skF_4') ) ),
    inference(negUnitSimplification,[status(thm)],[c_464,c_556])).

tff(c_562,plain,(
    v1_xboole_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_557])).

tff(c_106,plain,(
    ! [A_63,B_64] :
      ( r2_hidden('#skF_2'(A_63,B_64),A_63)
      | r1_tarski(A_63,B_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_115,plain,(
    ! [A_65,B_66] :
      ( ~ v1_xboole_0(A_65)
      | r1_tarski(A_65,B_66) ) ),
    inference(resolution,[status(thm)],[c_106,c_2])).

tff(c_80,plain,(
    ! [B_60,A_61] :
      ( B_60 = A_61
      | ~ r1_tarski(B_60,A_61)
      | ~ r1_tarski(A_61,B_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_89,plain,(
    ! [A_12] :
      ( k1_xboole_0 = A_12
      | ~ r1_tarski(A_12,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_18,c_80])).

tff(c_126,plain,(
    ! [A_65] :
      ( k1_xboole_0 = A_65
      | ~ v1_xboole_0(A_65) ) ),
    inference(resolution,[status(thm)],[c_115,c_89])).

tff(c_567,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_562,c_126])).

tff(c_572,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_567])).

tff(c_574,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_557])).

tff(c_20,plain,(
    ! [A_13,B_14] :
      ( r2_hidden(A_13,B_14)
      | v1_xboole_0(B_14)
      | ~ m1_subset_1(A_13,B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_593,plain,(
    ! [D_148,B_149,E_146,B_145,A_147] :
      ( k1_funct_1(k5_relat_1(D_148,E_146),A_147) = k1_funct_1(E_146,k1_funct_1(D_148,A_147))
      | k1_xboole_0 = B_149
      | ~ v1_funct_1(E_146)
      | ~ v1_relat_1(E_146)
      | ~ m1_subset_1(D_148,k1_zfmisc_1(k2_zfmisc_1(B_145,B_149)))
      | ~ v1_funct_2(D_148,B_145,B_149)
      | ~ v1_funct_1(D_148)
      | v1_xboole_0(B_145)
      | ~ m1_subset_1(A_147,B_145) ) ),
    inference(resolution,[status(thm)],[c_20,c_357])).

tff(c_597,plain,(
    ! [E_146,A_147] :
      ( k1_funct_1(k5_relat_1('#skF_6',E_146),A_147) = k1_funct_1(E_146,k1_funct_1('#skF_6',A_147))
      | k1_xboole_0 = '#skF_5'
      | ~ v1_funct_1(E_146)
      | ~ v1_relat_1(E_146)
      | ~ v1_funct_2('#skF_6','#skF_4','#skF_5')
      | ~ v1_funct_1('#skF_6')
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(A_147,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_44,c_593])).

tff(c_604,plain,(
    ! [E_146,A_147] :
      ( k1_funct_1(k5_relat_1('#skF_6',E_146),A_147) = k1_funct_1(E_146,k1_funct_1('#skF_6',A_147))
      | k1_xboole_0 = '#skF_5'
      | ~ v1_funct_1(E_146)
      | ~ v1_relat_1(E_146)
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(A_147,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_597])).

tff(c_606,plain,(
    ! [E_150,A_151] :
      ( k1_funct_1(k5_relat_1('#skF_6',E_150),A_151) = k1_funct_1(E_150,k1_funct_1('#skF_6',A_151))
      | ~ v1_funct_1(E_150)
      | ~ v1_relat_1(E_150)
      | ~ m1_subset_1(A_151,'#skF_4') ) ),
    inference(negUnitSimplification,[status(thm)],[c_574,c_464,c_604])).

tff(c_463,plain,(
    k1_partfun1('#skF_4','#skF_5','#skF_5','#skF_3','#skF_6','#skF_7') = k8_funct_2('#skF_4','#skF_5','#skF_3','#skF_6','#skF_7') ),
    inference(splitRight,[status(thm)],[c_446])).

tff(c_249,plain,(
    ! [C_92,D_88,F_91,B_89,E_93,A_90] :
      ( k1_partfun1(A_90,B_89,C_92,D_88,E_93,F_91) = k5_relat_1(E_93,F_91)
      | ~ m1_subset_1(F_91,k1_zfmisc_1(k2_zfmisc_1(C_92,D_88)))
      | ~ v1_funct_1(F_91)
      | ~ m1_subset_1(E_93,k1_zfmisc_1(k2_zfmisc_1(A_90,B_89)))
      | ~ v1_funct_1(E_93) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_251,plain,(
    ! [A_90,B_89,E_93] :
      ( k1_partfun1(A_90,B_89,'#skF_5','#skF_3',E_93,'#skF_7') = k5_relat_1(E_93,'#skF_7')
      | ~ v1_funct_1('#skF_7')
      | ~ m1_subset_1(E_93,k1_zfmisc_1(k2_zfmisc_1(A_90,B_89)))
      | ~ v1_funct_1(E_93) ) ),
    inference(resolution,[status(thm)],[c_40,c_249])).

tff(c_501,plain,(
    ! [A_132,B_133,E_134] :
      ( k1_partfun1(A_132,B_133,'#skF_5','#skF_3',E_134,'#skF_7') = k5_relat_1(E_134,'#skF_7')
      | ~ m1_subset_1(E_134,k1_zfmisc_1(k2_zfmisc_1(A_132,B_133)))
      | ~ v1_funct_1(E_134) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_251])).

tff(c_507,plain,
    ( k1_partfun1('#skF_4','#skF_5','#skF_5','#skF_3','#skF_6','#skF_7') = k5_relat_1('#skF_6','#skF_7')
    | ~ v1_funct_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_44,c_501])).

tff(c_513,plain,(
    k8_funct_2('#skF_4','#skF_5','#skF_3','#skF_6','#skF_7') = k5_relat_1('#skF_6','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_463,c_507])).

tff(c_32,plain,(
    k1_funct_1(k8_funct_2('#skF_4','#skF_5','#skF_3','#skF_6','#skF_7'),'#skF_8') != k1_funct_1('#skF_7',k1_funct_1('#skF_6','#skF_8')) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_515,plain,(
    k1_funct_1(k5_relat_1('#skF_6','#skF_7'),'#skF_8') != k1_funct_1('#skF_7',k1_funct_1('#skF_6','#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_513,c_32])).

tff(c_616,plain,
    ( ~ v1_funct_1('#skF_7')
    | ~ v1_relat_1('#skF_7')
    | ~ m1_subset_1('#skF_8','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_606,c_515])).

tff(c_628,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_78,c_42,c_616])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n011.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 15:10:57 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.80/1.45  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.80/1.45  
% 2.80/1.45  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.80/1.46  %$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k8_funct_2 > k2_relset_1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_3 > #skF_8 > #skF_4 > #skF_2
% 2.80/1.46  
% 2.80/1.46  %Foreground sorts:
% 2.80/1.46  
% 2.80/1.46  
% 2.80/1.46  %Background operators:
% 2.80/1.46  
% 2.80/1.46  
% 2.80/1.46  %Foreground operators:
% 2.80/1.46  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 2.80/1.46  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.80/1.46  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.80/1.46  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.80/1.46  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.80/1.46  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.80/1.46  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.80/1.46  tff('#skF_7', type, '#skF_7': $i).
% 2.80/1.46  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.80/1.46  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.80/1.46  tff('#skF_5', type, '#skF_5': $i).
% 2.80/1.46  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.80/1.46  tff(k8_funct_2, type, k8_funct_2: ($i * $i * $i * $i * $i) > $i).
% 2.80/1.46  tff('#skF_6', type, '#skF_6': $i).
% 2.80/1.46  tff('#skF_3', type, '#skF_3': $i).
% 2.80/1.46  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.80/1.46  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.80/1.46  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.80/1.46  tff('#skF_8', type, '#skF_8': $i).
% 2.80/1.46  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.80/1.46  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.80/1.46  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.80/1.46  tff('#skF_4', type, '#skF_4': $i).
% 2.80/1.46  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.80/1.46  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.80/1.46  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.80/1.46  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.80/1.46  
% 3.19/1.48  tff(f_130, negated_conjecture, ~(![A, B, C]: (~v1_xboole_0(C) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, C)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (![E]: ((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(C, A)))) => (![F]: (m1_subset_1(F, B) => (r1_tarski(k2_relset_1(B, C, D), k1_relset_1(C, A, E)) => ((B = k1_xboole_0) | (k1_funct_1(k8_funct_2(B, C, A, D, E), F) = k1_funct_1(E, k1_funct_1(D, F))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t185_funct_2)).
% 3.19/1.48  tff(f_61, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.19/1.48  tff(f_78, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: ((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (r1_tarski(k2_relset_1(A, B, D), k1_relset_1(B, C, E)) => ((B = k1_xboole_0) | (k8_funct_2(A, B, C, D, E) = k1_partfun1(A, B, B, C, D, E)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d12_funct_2)).
% 3.19/1.48  tff(f_46, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 3.19/1.48  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 3.19/1.48  tff(f_57, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 3.19/1.48  tff(f_105, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: ((v1_relat_1(E) & v1_funct_1(E)) => (r2_hidden(C, A) => ((B = k1_xboole_0) | (k1_funct_1(k5_relat_1(D, E), C) = k1_funct_1(E, k1_funct_1(D, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t21_funct_2)).
% 3.19/1.48  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 3.19/1.48  tff(f_44, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.19/1.48  tff(f_52, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 3.19/1.48  tff(f_88, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 3.19/1.48  tff(c_38, plain, (m1_subset_1('#skF_8', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_130])).
% 3.19/1.48  tff(c_40, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_130])).
% 3.19/1.48  tff(c_71, plain, (![C_57, A_58, B_59]: (v1_relat_1(C_57) | ~m1_subset_1(C_57, k1_zfmisc_1(k2_zfmisc_1(A_58, B_59))))), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.19/1.48  tff(c_78, plain, (v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_40, c_71])).
% 3.19/1.48  tff(c_42, plain, (v1_funct_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_130])).
% 3.19/1.48  tff(c_34, plain, (k1_xboole_0!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_130])).
% 3.19/1.48  tff(c_50, plain, (~v1_xboole_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_130])).
% 3.19/1.48  tff(c_48, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_130])).
% 3.19/1.48  tff(c_46, plain, (v1_funct_2('#skF_6', '#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_130])).
% 3.19/1.48  tff(c_44, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_5')))), inference(cnfTransformation, [status(thm)], [f_130])).
% 3.19/1.48  tff(c_36, plain, (r1_tarski(k2_relset_1('#skF_4', '#skF_5', '#skF_6'), k1_relset_1('#skF_5', '#skF_3', '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_130])).
% 3.19/1.48  tff(c_436, plain, (![A_130, E_131, D_129, C_127, B_128]: (k1_partfun1(A_130, B_128, B_128, C_127, D_129, E_131)=k8_funct_2(A_130, B_128, C_127, D_129, E_131) | k1_xboole_0=B_128 | ~r1_tarski(k2_relset_1(A_130, B_128, D_129), k1_relset_1(B_128, C_127, E_131)) | ~m1_subset_1(E_131, k1_zfmisc_1(k2_zfmisc_1(B_128, C_127))) | ~v1_funct_1(E_131) | ~m1_subset_1(D_129, k1_zfmisc_1(k2_zfmisc_1(A_130, B_128))) | ~v1_funct_2(D_129, A_130, B_128) | ~v1_funct_1(D_129))), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.19/1.48  tff(c_442, plain, (k1_partfun1('#skF_4', '#skF_5', '#skF_5', '#skF_3', '#skF_6', '#skF_7')=k8_funct_2('#skF_4', '#skF_5', '#skF_3', '#skF_6', '#skF_7') | k1_xboole_0='#skF_5' | ~m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_3'))) | ~v1_funct_1('#skF_7') | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_5'))) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_5') | ~v1_funct_1('#skF_6')), inference(resolution, [status(thm)], [c_36, c_436])).
% 3.19/1.48  tff(c_446, plain, (k1_partfun1('#skF_4', '#skF_5', '#skF_5', '#skF_3', '#skF_6', '#skF_7')=k8_funct_2('#skF_4', '#skF_5', '#skF_3', '#skF_6', '#skF_7') | k1_xboole_0='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_44, c_42, c_40, c_442])).
% 3.19/1.48  tff(c_451, plain, (k1_xboole_0='#skF_5'), inference(splitLeft, [status(thm)], [c_446])).
% 3.19/1.48  tff(c_18, plain, (![A_12]: (r1_tarski(k1_xboole_0, A_12))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.19/1.48  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.19/1.48  tff(c_60, plain, (![B_54, A_55]: (~r1_tarski(B_54, A_55) | ~r2_hidden(A_55, B_54))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.19/1.48  tff(c_65, plain, (![A_56]: (~r1_tarski(A_56, '#skF_1'(A_56)) | v1_xboole_0(A_56))), inference(resolution, [status(thm)], [c_4, c_60])).
% 3.19/1.48  tff(c_70, plain, (v1_xboole_0(k1_xboole_0)), inference(resolution, [status(thm)], [c_18, c_65])).
% 3.19/1.48  tff(c_458, plain, (v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_451, c_70])).
% 3.19/1.48  tff(c_462, plain, $false, inference(negUnitSimplification, [status(thm)], [c_50, c_458])).
% 3.19/1.48  tff(c_464, plain, (k1_xboole_0!='#skF_5'), inference(splitRight, [status(thm)], [c_446])).
% 3.19/1.48  tff(c_357, plain, (![E_111, D_115, A_114, C_113, B_112]: (k1_funct_1(k5_relat_1(D_115, E_111), C_113)=k1_funct_1(E_111, k1_funct_1(D_115, C_113)) | k1_xboole_0=B_112 | ~r2_hidden(C_113, A_114) | ~v1_funct_1(E_111) | ~v1_relat_1(E_111) | ~m1_subset_1(D_115, k1_zfmisc_1(k2_zfmisc_1(A_114, B_112))) | ~v1_funct_2(D_115, A_114, B_112) | ~v1_funct_1(D_115))), inference(cnfTransformation, [status(thm)], [f_105])).
% 3.19/1.48  tff(c_545, plain, (![D_138, E_139, A_140, B_141]: (k1_funct_1(k5_relat_1(D_138, E_139), '#skF_1'(A_140))=k1_funct_1(E_139, k1_funct_1(D_138, '#skF_1'(A_140))) | k1_xboole_0=B_141 | ~v1_funct_1(E_139) | ~v1_relat_1(E_139) | ~m1_subset_1(D_138, k1_zfmisc_1(k2_zfmisc_1(A_140, B_141))) | ~v1_funct_2(D_138, A_140, B_141) | ~v1_funct_1(D_138) | v1_xboole_0(A_140))), inference(resolution, [status(thm)], [c_4, c_357])).
% 3.19/1.48  tff(c_549, plain, (![E_139]: (k1_funct_1(k5_relat_1('#skF_6', E_139), '#skF_1'('#skF_4'))=k1_funct_1(E_139, k1_funct_1('#skF_6', '#skF_1'('#skF_4'))) | k1_xboole_0='#skF_5' | ~v1_funct_1(E_139) | ~v1_relat_1(E_139) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_5') | ~v1_funct_1('#skF_6') | v1_xboole_0('#skF_4'))), inference(resolution, [status(thm)], [c_44, c_545])).
% 3.19/1.48  tff(c_556, plain, (![E_139]: (k1_funct_1(k5_relat_1('#skF_6', E_139), '#skF_1'('#skF_4'))=k1_funct_1(E_139, k1_funct_1('#skF_6', '#skF_1'('#skF_4'))) | k1_xboole_0='#skF_5' | ~v1_funct_1(E_139) | ~v1_relat_1(E_139) | v1_xboole_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_549])).
% 3.19/1.48  tff(c_557, plain, (![E_139]: (k1_funct_1(k5_relat_1('#skF_6', E_139), '#skF_1'('#skF_4'))=k1_funct_1(E_139, k1_funct_1('#skF_6', '#skF_1'('#skF_4'))) | ~v1_funct_1(E_139) | ~v1_relat_1(E_139) | v1_xboole_0('#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_464, c_556])).
% 3.19/1.48  tff(c_562, plain, (v1_xboole_0('#skF_4')), inference(splitLeft, [status(thm)], [c_557])).
% 3.19/1.48  tff(c_106, plain, (![A_63, B_64]: (r2_hidden('#skF_2'(A_63, B_64), A_63) | r1_tarski(A_63, B_64))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.19/1.48  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.19/1.48  tff(c_115, plain, (![A_65, B_66]: (~v1_xboole_0(A_65) | r1_tarski(A_65, B_66))), inference(resolution, [status(thm)], [c_106, c_2])).
% 3.19/1.48  tff(c_80, plain, (![B_60, A_61]: (B_60=A_61 | ~r1_tarski(B_60, A_61) | ~r1_tarski(A_61, B_60))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.19/1.48  tff(c_89, plain, (![A_12]: (k1_xboole_0=A_12 | ~r1_tarski(A_12, k1_xboole_0))), inference(resolution, [status(thm)], [c_18, c_80])).
% 3.19/1.48  tff(c_126, plain, (![A_65]: (k1_xboole_0=A_65 | ~v1_xboole_0(A_65))), inference(resolution, [status(thm)], [c_115, c_89])).
% 3.19/1.48  tff(c_567, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_562, c_126])).
% 3.19/1.48  tff(c_572, plain, $false, inference(negUnitSimplification, [status(thm)], [c_34, c_567])).
% 3.19/1.48  tff(c_574, plain, (~v1_xboole_0('#skF_4')), inference(splitRight, [status(thm)], [c_557])).
% 3.19/1.48  tff(c_20, plain, (![A_13, B_14]: (r2_hidden(A_13, B_14) | v1_xboole_0(B_14) | ~m1_subset_1(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.19/1.48  tff(c_593, plain, (![D_148, B_149, E_146, B_145, A_147]: (k1_funct_1(k5_relat_1(D_148, E_146), A_147)=k1_funct_1(E_146, k1_funct_1(D_148, A_147)) | k1_xboole_0=B_149 | ~v1_funct_1(E_146) | ~v1_relat_1(E_146) | ~m1_subset_1(D_148, k1_zfmisc_1(k2_zfmisc_1(B_145, B_149))) | ~v1_funct_2(D_148, B_145, B_149) | ~v1_funct_1(D_148) | v1_xboole_0(B_145) | ~m1_subset_1(A_147, B_145))), inference(resolution, [status(thm)], [c_20, c_357])).
% 3.19/1.48  tff(c_597, plain, (![E_146, A_147]: (k1_funct_1(k5_relat_1('#skF_6', E_146), A_147)=k1_funct_1(E_146, k1_funct_1('#skF_6', A_147)) | k1_xboole_0='#skF_5' | ~v1_funct_1(E_146) | ~v1_relat_1(E_146) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_5') | ~v1_funct_1('#skF_6') | v1_xboole_0('#skF_4') | ~m1_subset_1(A_147, '#skF_4'))), inference(resolution, [status(thm)], [c_44, c_593])).
% 3.19/1.48  tff(c_604, plain, (![E_146, A_147]: (k1_funct_1(k5_relat_1('#skF_6', E_146), A_147)=k1_funct_1(E_146, k1_funct_1('#skF_6', A_147)) | k1_xboole_0='#skF_5' | ~v1_funct_1(E_146) | ~v1_relat_1(E_146) | v1_xboole_0('#skF_4') | ~m1_subset_1(A_147, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_597])).
% 3.19/1.48  tff(c_606, plain, (![E_150, A_151]: (k1_funct_1(k5_relat_1('#skF_6', E_150), A_151)=k1_funct_1(E_150, k1_funct_1('#skF_6', A_151)) | ~v1_funct_1(E_150) | ~v1_relat_1(E_150) | ~m1_subset_1(A_151, '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_574, c_464, c_604])).
% 3.19/1.48  tff(c_463, plain, (k1_partfun1('#skF_4', '#skF_5', '#skF_5', '#skF_3', '#skF_6', '#skF_7')=k8_funct_2('#skF_4', '#skF_5', '#skF_3', '#skF_6', '#skF_7')), inference(splitRight, [status(thm)], [c_446])).
% 3.19/1.48  tff(c_249, plain, (![C_92, D_88, F_91, B_89, E_93, A_90]: (k1_partfun1(A_90, B_89, C_92, D_88, E_93, F_91)=k5_relat_1(E_93, F_91) | ~m1_subset_1(F_91, k1_zfmisc_1(k2_zfmisc_1(C_92, D_88))) | ~v1_funct_1(F_91) | ~m1_subset_1(E_93, k1_zfmisc_1(k2_zfmisc_1(A_90, B_89))) | ~v1_funct_1(E_93))), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.19/1.48  tff(c_251, plain, (![A_90, B_89, E_93]: (k1_partfun1(A_90, B_89, '#skF_5', '#skF_3', E_93, '#skF_7')=k5_relat_1(E_93, '#skF_7') | ~v1_funct_1('#skF_7') | ~m1_subset_1(E_93, k1_zfmisc_1(k2_zfmisc_1(A_90, B_89))) | ~v1_funct_1(E_93))), inference(resolution, [status(thm)], [c_40, c_249])).
% 3.19/1.48  tff(c_501, plain, (![A_132, B_133, E_134]: (k1_partfun1(A_132, B_133, '#skF_5', '#skF_3', E_134, '#skF_7')=k5_relat_1(E_134, '#skF_7') | ~m1_subset_1(E_134, k1_zfmisc_1(k2_zfmisc_1(A_132, B_133))) | ~v1_funct_1(E_134))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_251])).
% 3.19/1.48  tff(c_507, plain, (k1_partfun1('#skF_4', '#skF_5', '#skF_5', '#skF_3', '#skF_6', '#skF_7')=k5_relat_1('#skF_6', '#skF_7') | ~v1_funct_1('#skF_6')), inference(resolution, [status(thm)], [c_44, c_501])).
% 3.19/1.48  tff(c_513, plain, (k8_funct_2('#skF_4', '#skF_5', '#skF_3', '#skF_6', '#skF_7')=k5_relat_1('#skF_6', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_463, c_507])).
% 3.19/1.48  tff(c_32, plain, (k1_funct_1(k8_funct_2('#skF_4', '#skF_5', '#skF_3', '#skF_6', '#skF_7'), '#skF_8')!=k1_funct_1('#skF_7', k1_funct_1('#skF_6', '#skF_8'))), inference(cnfTransformation, [status(thm)], [f_130])).
% 3.19/1.48  tff(c_515, plain, (k1_funct_1(k5_relat_1('#skF_6', '#skF_7'), '#skF_8')!=k1_funct_1('#skF_7', k1_funct_1('#skF_6', '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_513, c_32])).
% 3.19/1.48  tff(c_616, plain, (~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7') | ~m1_subset_1('#skF_8', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_606, c_515])).
% 3.19/1.48  tff(c_628, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_38, c_78, c_42, c_616])).
% 3.19/1.48  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.19/1.48  
% 3.19/1.48  Inference rules
% 3.19/1.48  ----------------------
% 3.19/1.48  #Ref     : 0
% 3.19/1.48  #Sup     : 124
% 3.19/1.48  #Fact    : 0
% 3.19/1.48  #Define  : 0
% 3.19/1.48  #Split   : 7
% 3.19/1.48  #Chain   : 0
% 3.19/1.48  #Close   : 0
% 3.19/1.48  
% 3.19/1.48  Ordering : KBO
% 3.19/1.48  
% 3.19/1.48  Simplification rules
% 3.19/1.48  ----------------------
% 3.19/1.48  #Subsume      : 29
% 3.19/1.48  #Demod        : 63
% 3.19/1.48  #Tautology    : 46
% 3.19/1.48  #SimpNegUnit  : 7
% 3.19/1.48  #BackRed      : 17
% 3.19/1.48  
% 3.19/1.48  #Partial instantiations: 0
% 3.19/1.48  #Strategies tried      : 1
% 3.19/1.48  
% 3.19/1.48  Timing (in seconds)
% 3.19/1.48  ----------------------
% 3.19/1.48  Preprocessing        : 0.35
% 3.19/1.48  Parsing              : 0.18
% 3.19/1.48  CNF conversion       : 0.03
% 3.19/1.48  Main loop            : 0.35
% 3.19/1.48  Inferencing          : 0.12
% 3.19/1.48  Reduction            : 0.11
% 3.19/1.48  Demodulation         : 0.07
% 3.19/1.48  BG Simplification    : 0.02
% 3.19/1.48  Subsumption          : 0.08
% 3.19/1.48  Abstraction          : 0.02
% 3.19/1.48  MUC search           : 0.00
% 3.19/1.48  Cooper               : 0.00
% 3.19/1.48  Total                : 0.74
% 3.19/1.48  Index Insertion      : 0.00
% 3.19/1.48  Index Deletion       : 0.00
% 3.19/1.48  Index Matching       : 0.00
% 3.19/1.48  BG Taut test         : 0.00
%------------------------------------------------------------------------------
