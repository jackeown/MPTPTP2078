%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:12:07 EST 2020

% Result     : Theorem 4.31s
% Output     : CNFRefutation 4.69s
% Verified   : 
% Statistics : Number of formulae       :  111 ( 251 expanded)
%              Number of leaves         :   45 ( 110 expanded)
%              Depth                    :    9
%              Number of atoms          :  195 ( 724 expanded)
%              Number of equality atoms :   33 (  73 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > r2_hidden > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff(v2_funct_1,type,(
    v2_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_relset_1,type,(
    r2_relset_1: ( $i * $i * $i * $i ) > $o )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k1_partfun1,type,(
    k1_partfun1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(v2_funct_2,type,(
    v2_funct_2: ( $i * $i ) > $o )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k6_partfun1,type,(
    k6_partfun1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_157,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ! [D] :
            ( ( v1_funct_1(D)
              & v1_funct_2(D,B,A)
              & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,A))) )
           => ( r2_relset_1(A,A,k1_partfun1(A,B,B,A,C,D),k6_partfun1(A))
             => ( v2_funct_1(C)
                & v2_funct_2(D,A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_funct_2)).

tff(f_62,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => v1_xboole_0(C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc3_relset_1)).

tff(f_98,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_45,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v2_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_funct_1)).

tff(f_96,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( v1_funct_1(k1_partfun1(A,B,C,D,E,F))
        & m1_subset_1(k1_partfun1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).

tff(f_76,axiom,(
    ! [A] : m1_subset_1(k6_relat_1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_relset_1)).

tff(f_74,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_137,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ! [E] :
          ( ( v1_funct_1(E)
            & v1_funct_2(E,B,C)
            & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(B,C))) )
         => ( v2_funct_1(k1_partfun1(A,B,B,C,D,E))
           => ( ( C = k1_xboole_0
                & B != k1_xboole_0 )
              | v2_funct_1(D) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_funct_2)).

tff(f_32,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_40,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_41,axiom,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_relat_1)).

tff(f_49,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_55,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_66,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_115,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ! [D] :
          ( ( v1_funct_1(D)
            & v1_funct_2(D,B,A)
            & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,A))) )
         => ( r2_relset_1(B,B,k1_partfun1(B,A,A,B,D,C),k6_partfun1(B))
           => k2_relset_1(A,B,C) = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_funct_2)).

tff(f_84,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A) )
     => ( v2_funct_2(B,A)
      <=> k2_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_funct_2)).

tff(c_48,plain,
    ( ~ v2_funct_2('#skF_6','#skF_3')
    | ~ v2_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_96,plain,(
    ~ v2_funct_1('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_48])).

tff(c_58,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_182,plain,(
    ! [C_68,A_69,B_70] :
      ( v1_xboole_0(C_68)
      | ~ m1_subset_1(C_68,k1_zfmisc_1(k2_zfmisc_1(A_69,B_70)))
      | ~ v1_xboole_0(A_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_200,plain,
    ( v1_xboole_0('#skF_5')
    | ~ v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_58,c_182])).

tff(c_202,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_200])).

tff(c_62,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_60,plain,(
    v1_funct_2('#skF_5','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_56,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_54,plain,(
    v1_funct_2('#skF_6','#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_52,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_40,plain,(
    ! [A_34] : k6_relat_1(A_34) = k6_partfun1(A_34) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_14,plain,(
    ! [A_7] : v2_funct_1(k6_relat_1(A_7)) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_64,plain,(
    ! [A_7] : v2_funct_1(k6_partfun1(A_7)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_14])).

tff(c_36,plain,(
    ! [C_30,E_32,D_31,B_29,F_33,A_28] :
      ( m1_subset_1(k1_partfun1(A_28,B_29,C_30,D_31,E_32,F_33),k1_zfmisc_1(k2_zfmisc_1(A_28,D_31)))
      | ~ m1_subset_1(F_33,k1_zfmisc_1(k2_zfmisc_1(C_30,D_31)))
      | ~ v1_funct_1(F_33)
      | ~ m1_subset_1(E_32,k1_zfmisc_1(k2_zfmisc_1(A_28,B_29)))
      | ~ v1_funct_1(E_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_30,plain,(
    ! [A_25] : m1_subset_1(k6_relat_1(A_25),k1_zfmisc_1(k2_zfmisc_1(A_25,A_25))) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_63,plain,(
    ! [A_25] : m1_subset_1(k6_partfun1(A_25),k1_zfmisc_1(k2_zfmisc_1(A_25,A_25))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_30])).

tff(c_50,plain,(
    r2_relset_1('#skF_3','#skF_3',k1_partfun1('#skF_3','#skF_4','#skF_4','#skF_3','#skF_5','#skF_6'),k6_partfun1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_333,plain,(
    ! [D_82,C_83,A_84,B_85] :
      ( D_82 = C_83
      | ~ r2_relset_1(A_84,B_85,C_83,D_82)
      | ~ m1_subset_1(D_82,k1_zfmisc_1(k2_zfmisc_1(A_84,B_85)))
      | ~ m1_subset_1(C_83,k1_zfmisc_1(k2_zfmisc_1(A_84,B_85))) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_341,plain,
    ( k1_partfun1('#skF_3','#skF_4','#skF_4','#skF_3','#skF_5','#skF_6') = k6_partfun1('#skF_3')
    | ~ m1_subset_1(k6_partfun1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3')))
    | ~ m1_subset_1(k1_partfun1('#skF_3','#skF_4','#skF_4','#skF_3','#skF_5','#skF_6'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3'))) ),
    inference(resolution,[status(thm)],[c_50,c_333])).

tff(c_356,plain,
    ( k1_partfun1('#skF_3','#skF_4','#skF_4','#skF_3','#skF_5','#skF_6') = k6_partfun1('#skF_3')
    | ~ m1_subset_1(k1_partfun1('#skF_3','#skF_4','#skF_4','#skF_3','#skF_5','#skF_6'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_63,c_341])).

tff(c_775,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_3','#skF_4','#skF_4','#skF_3','#skF_5','#skF_6'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_356])).

tff(c_778,plain,
    ( ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_3')))
    | ~ v1_funct_1('#skF_6')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4')))
    | ~ v1_funct_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_36,c_775])).

tff(c_782,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_58,c_56,c_52,c_778])).

tff(c_783,plain,(
    k1_partfun1('#skF_3','#skF_4','#skF_4','#skF_3','#skF_5','#skF_6') = k6_partfun1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_356])).

tff(c_830,plain,(
    ! [D_126,E_124,C_127,A_125,B_128] :
      ( k1_xboole_0 = C_127
      | v2_funct_1(D_126)
      | ~ v2_funct_1(k1_partfun1(A_125,B_128,B_128,C_127,D_126,E_124))
      | ~ m1_subset_1(E_124,k1_zfmisc_1(k2_zfmisc_1(B_128,C_127)))
      | ~ v1_funct_2(E_124,B_128,C_127)
      | ~ v1_funct_1(E_124)
      | ~ m1_subset_1(D_126,k1_zfmisc_1(k2_zfmisc_1(A_125,B_128)))
      | ~ v1_funct_2(D_126,A_125,B_128)
      | ~ v1_funct_1(D_126) ) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_832,plain,
    ( k1_xboole_0 = '#skF_3'
    | v2_funct_1('#skF_5')
    | ~ v2_funct_1(k6_partfun1('#skF_3'))
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_3')))
    | ~ v1_funct_2('#skF_6','#skF_4','#skF_3')
    | ~ v1_funct_1('#skF_6')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4')))
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_783,c_830])).

tff(c_834,plain,
    ( k1_xboole_0 = '#skF_3'
    | v2_funct_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_58,c_56,c_54,c_52,c_64,c_832])).

tff(c_835,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_96,c_834])).

tff(c_6,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_864,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_835,c_6])).

tff(c_866,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_202,c_864])).

tff(c_867,plain,(
    v1_xboole_0('#skF_5') ),
    inference(splitRight,[status(thm)],[c_200])).

tff(c_103,plain,(
    ! [A_53] :
      ( r2_hidden('#skF_2'(A_53),A_53)
      | k1_xboole_0 = A_53 ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_107,plain,(
    ! [A_53] :
      ( ~ v1_xboole_0(A_53)
      | k1_xboole_0 = A_53 ) ),
    inference(resolution,[status(thm)],[c_103,c_2])).

tff(c_872,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_867,c_107])).

tff(c_72,plain,(
    ! [A_49] : k6_relat_1(A_49) = k6_partfun1(A_49) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_10,plain,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_78,plain,(
    k6_partfun1(k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_72,c_10])).

tff(c_89,plain,(
    v2_funct_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_78,c_64])).

tff(c_883,plain,(
    v2_funct_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_872,c_89])).

tff(c_889,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_96,c_883])).

tff(c_890,plain,(
    ~ v2_funct_2('#skF_6','#skF_3') ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_913,plain,(
    ! [C_135,A_136,B_137] :
      ( v1_relat_1(C_135)
      | ~ m1_subset_1(C_135,k1_zfmisc_1(k2_zfmisc_1(A_136,B_137))) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_931,plain,(
    v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_52,c_913])).

tff(c_949,plain,(
    ! [C_141,B_142,A_143] :
      ( v5_relat_1(C_141,B_142)
      | ~ m1_subset_1(C_141,k1_zfmisc_1(k2_zfmisc_1(A_143,B_142))) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_965,plain,(
    v5_relat_1('#skF_6','#skF_3') ),
    inference(resolution,[status(thm)],[c_52,c_949])).

tff(c_1112,plain,(
    ! [A_157,B_158,D_159] :
      ( r2_relset_1(A_157,B_158,D_159,D_159)
      | ~ m1_subset_1(D_159,k1_zfmisc_1(k2_zfmisc_1(A_157,B_158))) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_1122,plain,(
    ! [A_25] : r2_relset_1(A_25,A_25,k6_partfun1(A_25),k6_partfun1(A_25)) ),
    inference(resolution,[status(thm)],[c_63,c_1112])).

tff(c_1140,plain,(
    ! [A_161,B_162,C_163] :
      ( k2_relset_1(A_161,B_162,C_163) = k2_relat_1(C_163)
      | ~ m1_subset_1(C_163,k1_zfmisc_1(k2_zfmisc_1(A_161,B_162))) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_1156,plain,(
    k2_relset_1('#skF_4','#skF_3','#skF_6') = k2_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_52,c_1140])).

tff(c_1169,plain,(
    ! [D_164,C_165,A_166,B_167] :
      ( D_164 = C_165
      | ~ r2_relset_1(A_166,B_167,C_165,D_164)
      | ~ m1_subset_1(D_164,k1_zfmisc_1(k2_zfmisc_1(A_166,B_167)))
      | ~ m1_subset_1(C_165,k1_zfmisc_1(k2_zfmisc_1(A_166,B_167))) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_1179,plain,
    ( k1_partfun1('#skF_3','#skF_4','#skF_4','#skF_3','#skF_5','#skF_6') = k6_partfun1('#skF_3')
    | ~ m1_subset_1(k6_partfun1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3')))
    | ~ m1_subset_1(k1_partfun1('#skF_3','#skF_4','#skF_4','#skF_3','#skF_5','#skF_6'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3'))) ),
    inference(resolution,[status(thm)],[c_50,c_1169])).

tff(c_1198,plain,
    ( k1_partfun1('#skF_3','#skF_4','#skF_4','#skF_3','#skF_5','#skF_6') = k6_partfun1('#skF_3')
    | ~ m1_subset_1(k1_partfun1('#skF_3','#skF_4','#skF_4','#skF_3','#skF_5','#skF_6'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_63,c_1179])).

tff(c_1740,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_3','#skF_4','#skF_4','#skF_3','#skF_5','#skF_6'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_1198])).

tff(c_1743,plain,
    ( ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_3')))
    | ~ v1_funct_1('#skF_6')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4')))
    | ~ v1_funct_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_36,c_1740])).

tff(c_1747,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_58,c_56,c_52,c_1743])).

tff(c_1748,plain,(
    k1_partfun1('#skF_3','#skF_4','#skF_4','#skF_3','#skF_5','#skF_6') = k6_partfun1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_1198])).

tff(c_1885,plain,(
    ! [A_218,B_219,C_220,D_221] :
      ( k2_relset_1(A_218,B_219,C_220) = B_219
      | ~ r2_relset_1(B_219,B_219,k1_partfun1(B_219,A_218,A_218,B_219,D_221,C_220),k6_partfun1(B_219))
      | ~ m1_subset_1(D_221,k1_zfmisc_1(k2_zfmisc_1(B_219,A_218)))
      | ~ v1_funct_2(D_221,B_219,A_218)
      | ~ v1_funct_1(D_221)
      | ~ m1_subset_1(C_220,k1_zfmisc_1(k2_zfmisc_1(A_218,B_219)))
      | ~ v1_funct_2(C_220,A_218,B_219)
      | ~ v1_funct_1(C_220) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_1888,plain,
    ( k2_relset_1('#skF_4','#skF_3','#skF_6') = '#skF_3'
    | ~ r2_relset_1('#skF_3','#skF_3',k6_partfun1('#skF_3'),k6_partfun1('#skF_3'))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4')))
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_5')
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_3')))
    | ~ v1_funct_2('#skF_6','#skF_4','#skF_3')
    | ~ v1_funct_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_1748,c_1885])).

tff(c_1896,plain,(
    k2_relat_1('#skF_6') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_52,c_62,c_60,c_58,c_1122,c_1156,c_1888])).

tff(c_32,plain,(
    ! [B_27] :
      ( v2_funct_2(B_27,k2_relat_1(B_27))
      | ~ v5_relat_1(B_27,k2_relat_1(B_27))
      | ~ v1_relat_1(B_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_1901,plain,
    ( v2_funct_2('#skF_6',k2_relat_1('#skF_6'))
    | ~ v5_relat_1('#skF_6','#skF_3')
    | ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_1896,c_32])).

tff(c_1905,plain,(
    v2_funct_2('#skF_6','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_931,c_965,c_1896,c_1901])).

tff(c_1907,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_890,c_1905])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.09  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.10  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.10/0.31  % Computer   : n019.cluster.edu
% 0.10/0.31  % Model      : x86_64 x86_64
% 0.10/0.31  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.10/0.31  % Memory     : 8042.1875MB
% 0.10/0.31  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.10/0.31  % CPULimit   : 60
% 0.10/0.31  % DateTime   : Tue Dec  1 18:08:52 EST 2020
% 0.10/0.31  % CPUTime    : 
% 0.10/0.32  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.31/1.74  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.60/1.75  
% 4.60/1.75  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.60/1.75  %$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > r2_hidden > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_4
% 4.60/1.75  
% 4.60/1.75  %Foreground sorts:
% 4.60/1.75  
% 4.60/1.75  
% 4.60/1.75  %Background operators:
% 4.60/1.75  
% 4.60/1.75  
% 4.60/1.75  %Foreground operators:
% 4.60/1.75  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 4.60/1.75  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.60/1.75  tff('#skF_2', type, '#skF_2': $i > $i).
% 4.60/1.75  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 4.60/1.75  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.60/1.75  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 4.60/1.75  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.60/1.75  tff('#skF_1', type, '#skF_1': $i > $i).
% 4.60/1.75  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.60/1.75  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 4.60/1.75  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 4.60/1.75  tff('#skF_5', type, '#skF_5': $i).
% 4.60/1.75  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.60/1.75  tff('#skF_6', type, '#skF_6': $i).
% 4.60/1.75  tff('#skF_3', type, '#skF_3': $i).
% 4.60/1.75  tff(v2_funct_2, type, v2_funct_2: ($i * $i) > $o).
% 4.60/1.75  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 4.60/1.75  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.60/1.75  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 4.60/1.75  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.60/1.75  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.60/1.75  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.60/1.75  tff('#skF_4', type, '#skF_4': $i).
% 4.60/1.75  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 4.60/1.75  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.60/1.75  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 4.60/1.75  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.60/1.75  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.60/1.75  
% 4.69/1.77  tff(f_157, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (r2_relset_1(A, A, k1_partfun1(A, B, B, A, C, D), k6_partfun1(A)) => (v2_funct_1(C) & v2_funct_2(D, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_funct_2)).
% 4.69/1.77  tff(f_62, axiom, (![A, B]: (v1_xboole_0(A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_xboole_0(C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc3_relset_1)).
% 4.69/1.77  tff(f_98, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 4.69/1.77  tff(f_45, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v2_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc4_funct_1)).
% 4.69/1.77  tff(f_96, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (v1_funct_1(k1_partfun1(A, B, C, D, E, F)) & m1_subset_1(k1_partfun1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 4.69/1.77  tff(f_76, axiom, (![A]: m1_subset_1(k6_relat_1(A), k1_zfmisc_1(k2_zfmisc_1(A, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_relset_1)).
% 4.69/1.77  tff(f_74, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 4.69/1.77  tff(f_137, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, B, C)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (v2_funct_1(k1_partfun1(A, B, B, C, D, E)) => (((C = k1_xboole_0) & ~(B = k1_xboole_0)) | v2_funct_1(D))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t26_funct_2)).
% 4.69/1.77  tff(f_32, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 4.69/1.77  tff(f_40, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 4.69/1.77  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 4.69/1.77  tff(f_41, axiom, (k6_relat_1(k1_xboole_0) = k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t81_relat_1)).
% 4.69/1.77  tff(f_49, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 4.69/1.77  tff(f_55, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 4.69/1.77  tff(f_66, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 4.69/1.77  tff(f_115, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (r2_relset_1(B, B, k1_partfun1(B, A, A, B, D, C), k6_partfun1(B)) => (k2_relset_1(A, B, C) = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t24_funct_2)).
% 4.69/1.77  tff(f_84, axiom, (![A, B]: ((v1_relat_1(B) & v5_relat_1(B, A)) => (v2_funct_2(B, A) <=> (k2_relat_1(B) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_funct_2)).
% 4.69/1.77  tff(c_48, plain, (~v2_funct_2('#skF_6', '#skF_3') | ~v2_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_157])).
% 4.69/1.77  tff(c_96, plain, (~v2_funct_1('#skF_5')), inference(splitLeft, [status(thm)], [c_48])).
% 4.69/1.77  tff(c_58, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_157])).
% 4.69/1.77  tff(c_182, plain, (![C_68, A_69, B_70]: (v1_xboole_0(C_68) | ~m1_subset_1(C_68, k1_zfmisc_1(k2_zfmisc_1(A_69, B_70))) | ~v1_xboole_0(A_69))), inference(cnfTransformation, [status(thm)], [f_62])).
% 4.69/1.77  tff(c_200, plain, (v1_xboole_0('#skF_5') | ~v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_58, c_182])).
% 4.69/1.77  tff(c_202, plain, (~v1_xboole_0('#skF_3')), inference(splitLeft, [status(thm)], [c_200])).
% 4.69/1.77  tff(c_62, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_157])).
% 4.69/1.77  tff(c_60, plain, (v1_funct_2('#skF_5', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_157])).
% 4.69/1.77  tff(c_56, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_157])).
% 4.69/1.77  tff(c_54, plain, (v1_funct_2('#skF_6', '#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_157])).
% 4.69/1.77  tff(c_52, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_157])).
% 4.69/1.77  tff(c_40, plain, (![A_34]: (k6_relat_1(A_34)=k6_partfun1(A_34))), inference(cnfTransformation, [status(thm)], [f_98])).
% 4.69/1.77  tff(c_14, plain, (![A_7]: (v2_funct_1(k6_relat_1(A_7)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 4.69/1.77  tff(c_64, plain, (![A_7]: (v2_funct_1(k6_partfun1(A_7)))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_14])).
% 4.69/1.77  tff(c_36, plain, (![C_30, E_32, D_31, B_29, F_33, A_28]: (m1_subset_1(k1_partfun1(A_28, B_29, C_30, D_31, E_32, F_33), k1_zfmisc_1(k2_zfmisc_1(A_28, D_31))) | ~m1_subset_1(F_33, k1_zfmisc_1(k2_zfmisc_1(C_30, D_31))) | ~v1_funct_1(F_33) | ~m1_subset_1(E_32, k1_zfmisc_1(k2_zfmisc_1(A_28, B_29))) | ~v1_funct_1(E_32))), inference(cnfTransformation, [status(thm)], [f_96])).
% 4.69/1.77  tff(c_30, plain, (![A_25]: (m1_subset_1(k6_relat_1(A_25), k1_zfmisc_1(k2_zfmisc_1(A_25, A_25))))), inference(cnfTransformation, [status(thm)], [f_76])).
% 4.69/1.77  tff(c_63, plain, (![A_25]: (m1_subset_1(k6_partfun1(A_25), k1_zfmisc_1(k2_zfmisc_1(A_25, A_25))))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_30])).
% 4.69/1.77  tff(c_50, plain, (r2_relset_1('#skF_3', '#skF_3', k1_partfun1('#skF_3', '#skF_4', '#skF_4', '#skF_3', '#skF_5', '#skF_6'), k6_partfun1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_157])).
% 4.69/1.77  tff(c_333, plain, (![D_82, C_83, A_84, B_85]: (D_82=C_83 | ~r2_relset_1(A_84, B_85, C_83, D_82) | ~m1_subset_1(D_82, k1_zfmisc_1(k2_zfmisc_1(A_84, B_85))) | ~m1_subset_1(C_83, k1_zfmisc_1(k2_zfmisc_1(A_84, B_85))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 4.69/1.77  tff(c_341, plain, (k1_partfun1('#skF_3', '#skF_4', '#skF_4', '#skF_3', '#skF_5', '#skF_6')=k6_partfun1('#skF_3') | ~m1_subset_1(k6_partfun1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3'))) | ~m1_subset_1(k1_partfun1('#skF_3', '#skF_4', '#skF_4', '#skF_3', '#skF_5', '#skF_6'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3')))), inference(resolution, [status(thm)], [c_50, c_333])).
% 4.69/1.77  tff(c_356, plain, (k1_partfun1('#skF_3', '#skF_4', '#skF_4', '#skF_3', '#skF_5', '#skF_6')=k6_partfun1('#skF_3') | ~m1_subset_1(k1_partfun1('#skF_3', '#skF_4', '#skF_4', '#skF_3', '#skF_5', '#skF_6'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_63, c_341])).
% 4.69/1.77  tff(c_775, plain, (~m1_subset_1(k1_partfun1('#skF_3', '#skF_4', '#skF_4', '#skF_3', '#skF_5', '#skF_6'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3')))), inference(splitLeft, [status(thm)], [c_356])).
% 4.69/1.77  tff(c_778, plain, (~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_3'))) | ~v1_funct_1('#skF_6') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4'))) | ~v1_funct_1('#skF_5')), inference(resolution, [status(thm)], [c_36, c_775])).
% 4.69/1.77  tff(c_782, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_62, c_58, c_56, c_52, c_778])).
% 4.69/1.77  tff(c_783, plain, (k1_partfun1('#skF_3', '#skF_4', '#skF_4', '#skF_3', '#skF_5', '#skF_6')=k6_partfun1('#skF_3')), inference(splitRight, [status(thm)], [c_356])).
% 4.69/1.77  tff(c_830, plain, (![D_126, E_124, C_127, A_125, B_128]: (k1_xboole_0=C_127 | v2_funct_1(D_126) | ~v2_funct_1(k1_partfun1(A_125, B_128, B_128, C_127, D_126, E_124)) | ~m1_subset_1(E_124, k1_zfmisc_1(k2_zfmisc_1(B_128, C_127))) | ~v1_funct_2(E_124, B_128, C_127) | ~v1_funct_1(E_124) | ~m1_subset_1(D_126, k1_zfmisc_1(k2_zfmisc_1(A_125, B_128))) | ~v1_funct_2(D_126, A_125, B_128) | ~v1_funct_1(D_126))), inference(cnfTransformation, [status(thm)], [f_137])).
% 4.69/1.77  tff(c_832, plain, (k1_xboole_0='#skF_3' | v2_funct_1('#skF_5') | ~v2_funct_1(k6_partfun1('#skF_3')) | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_3'))) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_3') | ~v1_funct_1('#skF_6') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4'))) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_4') | ~v1_funct_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_783, c_830])).
% 4.69/1.77  tff(c_834, plain, (k1_xboole_0='#skF_3' | v2_funct_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_58, c_56, c_54, c_52, c_64, c_832])).
% 4.69/1.77  tff(c_835, plain, (k1_xboole_0='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_96, c_834])).
% 4.69/1.77  tff(c_6, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.69/1.77  tff(c_864, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_835, c_6])).
% 4.69/1.77  tff(c_866, plain, $false, inference(negUnitSimplification, [status(thm)], [c_202, c_864])).
% 4.69/1.77  tff(c_867, plain, (v1_xboole_0('#skF_5')), inference(splitRight, [status(thm)], [c_200])).
% 4.69/1.77  tff(c_103, plain, (![A_53]: (r2_hidden('#skF_2'(A_53), A_53) | k1_xboole_0=A_53)), inference(cnfTransformation, [status(thm)], [f_40])).
% 4.69/1.77  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.69/1.77  tff(c_107, plain, (![A_53]: (~v1_xboole_0(A_53) | k1_xboole_0=A_53)), inference(resolution, [status(thm)], [c_103, c_2])).
% 4.69/1.77  tff(c_872, plain, (k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_867, c_107])).
% 4.69/1.77  tff(c_72, plain, (![A_49]: (k6_relat_1(A_49)=k6_partfun1(A_49))), inference(cnfTransformation, [status(thm)], [f_98])).
% 4.69/1.77  tff(c_10, plain, (k6_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.69/1.77  tff(c_78, plain, (k6_partfun1(k1_xboole_0)=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_72, c_10])).
% 4.69/1.77  tff(c_89, plain, (v2_funct_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_78, c_64])).
% 4.69/1.77  tff(c_883, plain, (v2_funct_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_872, c_89])).
% 4.69/1.77  tff(c_889, plain, $false, inference(negUnitSimplification, [status(thm)], [c_96, c_883])).
% 4.69/1.77  tff(c_890, plain, (~v2_funct_2('#skF_6', '#skF_3')), inference(splitRight, [status(thm)], [c_48])).
% 4.69/1.77  tff(c_913, plain, (![C_135, A_136, B_137]: (v1_relat_1(C_135) | ~m1_subset_1(C_135, k1_zfmisc_1(k2_zfmisc_1(A_136, B_137))))), inference(cnfTransformation, [status(thm)], [f_49])).
% 4.69/1.77  tff(c_931, plain, (v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_52, c_913])).
% 4.69/1.77  tff(c_949, plain, (![C_141, B_142, A_143]: (v5_relat_1(C_141, B_142) | ~m1_subset_1(C_141, k1_zfmisc_1(k2_zfmisc_1(A_143, B_142))))), inference(cnfTransformation, [status(thm)], [f_55])).
% 4.69/1.77  tff(c_965, plain, (v5_relat_1('#skF_6', '#skF_3')), inference(resolution, [status(thm)], [c_52, c_949])).
% 4.69/1.77  tff(c_1112, plain, (![A_157, B_158, D_159]: (r2_relset_1(A_157, B_158, D_159, D_159) | ~m1_subset_1(D_159, k1_zfmisc_1(k2_zfmisc_1(A_157, B_158))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 4.69/1.77  tff(c_1122, plain, (![A_25]: (r2_relset_1(A_25, A_25, k6_partfun1(A_25), k6_partfun1(A_25)))), inference(resolution, [status(thm)], [c_63, c_1112])).
% 4.69/1.77  tff(c_1140, plain, (![A_161, B_162, C_163]: (k2_relset_1(A_161, B_162, C_163)=k2_relat_1(C_163) | ~m1_subset_1(C_163, k1_zfmisc_1(k2_zfmisc_1(A_161, B_162))))), inference(cnfTransformation, [status(thm)], [f_66])).
% 4.69/1.77  tff(c_1156, plain, (k2_relset_1('#skF_4', '#skF_3', '#skF_6')=k2_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_52, c_1140])).
% 4.69/1.77  tff(c_1169, plain, (![D_164, C_165, A_166, B_167]: (D_164=C_165 | ~r2_relset_1(A_166, B_167, C_165, D_164) | ~m1_subset_1(D_164, k1_zfmisc_1(k2_zfmisc_1(A_166, B_167))) | ~m1_subset_1(C_165, k1_zfmisc_1(k2_zfmisc_1(A_166, B_167))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 4.69/1.77  tff(c_1179, plain, (k1_partfun1('#skF_3', '#skF_4', '#skF_4', '#skF_3', '#skF_5', '#skF_6')=k6_partfun1('#skF_3') | ~m1_subset_1(k6_partfun1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3'))) | ~m1_subset_1(k1_partfun1('#skF_3', '#skF_4', '#skF_4', '#skF_3', '#skF_5', '#skF_6'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3')))), inference(resolution, [status(thm)], [c_50, c_1169])).
% 4.69/1.77  tff(c_1198, plain, (k1_partfun1('#skF_3', '#skF_4', '#skF_4', '#skF_3', '#skF_5', '#skF_6')=k6_partfun1('#skF_3') | ~m1_subset_1(k1_partfun1('#skF_3', '#skF_4', '#skF_4', '#skF_3', '#skF_5', '#skF_6'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_63, c_1179])).
% 4.69/1.77  tff(c_1740, plain, (~m1_subset_1(k1_partfun1('#skF_3', '#skF_4', '#skF_4', '#skF_3', '#skF_5', '#skF_6'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3')))), inference(splitLeft, [status(thm)], [c_1198])).
% 4.69/1.77  tff(c_1743, plain, (~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_3'))) | ~v1_funct_1('#skF_6') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4'))) | ~v1_funct_1('#skF_5')), inference(resolution, [status(thm)], [c_36, c_1740])).
% 4.69/1.77  tff(c_1747, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_62, c_58, c_56, c_52, c_1743])).
% 4.69/1.77  tff(c_1748, plain, (k1_partfun1('#skF_3', '#skF_4', '#skF_4', '#skF_3', '#skF_5', '#skF_6')=k6_partfun1('#skF_3')), inference(splitRight, [status(thm)], [c_1198])).
% 4.69/1.77  tff(c_1885, plain, (![A_218, B_219, C_220, D_221]: (k2_relset_1(A_218, B_219, C_220)=B_219 | ~r2_relset_1(B_219, B_219, k1_partfun1(B_219, A_218, A_218, B_219, D_221, C_220), k6_partfun1(B_219)) | ~m1_subset_1(D_221, k1_zfmisc_1(k2_zfmisc_1(B_219, A_218))) | ~v1_funct_2(D_221, B_219, A_218) | ~v1_funct_1(D_221) | ~m1_subset_1(C_220, k1_zfmisc_1(k2_zfmisc_1(A_218, B_219))) | ~v1_funct_2(C_220, A_218, B_219) | ~v1_funct_1(C_220))), inference(cnfTransformation, [status(thm)], [f_115])).
% 4.69/1.77  tff(c_1888, plain, (k2_relset_1('#skF_4', '#skF_3', '#skF_6')='#skF_3' | ~r2_relset_1('#skF_3', '#skF_3', k6_partfun1('#skF_3'), k6_partfun1('#skF_3')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4'))) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_4') | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_3'))) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_3') | ~v1_funct_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_1748, c_1885])).
% 4.69/1.77  tff(c_1896, plain, (k2_relat_1('#skF_6')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_52, c_62, c_60, c_58, c_1122, c_1156, c_1888])).
% 4.69/1.77  tff(c_32, plain, (![B_27]: (v2_funct_2(B_27, k2_relat_1(B_27)) | ~v5_relat_1(B_27, k2_relat_1(B_27)) | ~v1_relat_1(B_27))), inference(cnfTransformation, [status(thm)], [f_84])).
% 4.69/1.77  tff(c_1901, plain, (v2_funct_2('#skF_6', k2_relat_1('#skF_6')) | ~v5_relat_1('#skF_6', '#skF_3') | ~v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_1896, c_32])).
% 4.69/1.77  tff(c_1905, plain, (v2_funct_2('#skF_6', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_931, c_965, c_1896, c_1901])).
% 4.69/1.77  tff(c_1907, plain, $false, inference(negUnitSimplification, [status(thm)], [c_890, c_1905])).
% 4.69/1.77  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.69/1.77  
% 4.69/1.77  Inference rules
% 4.69/1.77  ----------------------
% 4.69/1.77  #Ref     : 0
% 4.69/1.77  #Sup     : 416
% 4.69/1.77  #Fact    : 0
% 4.69/1.77  #Define  : 0
% 4.69/1.77  #Split   : 15
% 4.69/1.77  #Chain   : 0
% 4.69/1.77  #Close   : 0
% 4.69/1.77  
% 4.69/1.77  Ordering : KBO
% 4.69/1.77  
% 4.69/1.77  Simplification rules
% 4.69/1.77  ----------------------
% 4.69/1.77  #Subsume      : 62
% 4.69/1.77  #Demod        : 456
% 4.69/1.77  #Tautology    : 179
% 4.69/1.77  #SimpNegUnit  : 4
% 4.69/1.77  #BackRed      : 44
% 4.69/1.77  
% 4.69/1.77  #Partial instantiations: 0
% 4.69/1.77  #Strategies tried      : 1
% 4.69/1.77  
% 4.69/1.77  Timing (in seconds)
% 4.69/1.77  ----------------------
% 4.69/1.78  Preprocessing        : 0.37
% 4.69/1.78  Parsing              : 0.20
% 4.69/1.78  CNF conversion       : 0.03
% 4.69/1.78  Main loop            : 0.66
% 4.69/1.78  Inferencing          : 0.23
% 4.69/1.78  Reduction            : 0.22
% 4.69/1.78  Demodulation         : 0.16
% 4.69/1.78  BG Simplification    : 0.03
% 4.69/1.78  Subsumption          : 0.13
% 4.69/1.78  Abstraction          : 0.03
% 4.69/1.78  MUC search           : 0.00
% 4.69/1.78  Cooper               : 0.00
% 4.69/1.78  Total                : 1.07
% 4.69/1.78  Index Insertion      : 0.00
% 4.69/1.78  Index Deletion       : 0.00
% 4.69/1.78  Index Matching       : 0.00
% 4.69/1.78  BG Taut test         : 0.00
%------------------------------------------------------------------------------
