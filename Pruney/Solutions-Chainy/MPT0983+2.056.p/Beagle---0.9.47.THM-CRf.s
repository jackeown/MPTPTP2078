%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:12:09 EST 2020

% Result     : Theorem 4.72s
% Output     : CNFRefutation 4.72s
% Verified   : 
% Statistics : Number of formulae       :  119 ( 335 expanded)
%              Number of leaves         :   41 ( 134 expanded)
%              Depth                    :   11
%              Number of atoms          :  212 ( 943 expanded)
%              Number of equality atoms :   40 ( 106 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff(v2_funct_1,type,(
    v2_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_relset_1,type,(
    r2_relset_1: ( $i * $i * $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k1_partfun1,type,(
    k1_partfun1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

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

tff(f_152,negated_conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_funct_2)).

tff(f_57,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(B,A)))
         => v1_xboole_0(C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc4_relset_1)).

tff(f_93,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_40,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v2_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_funct_1)).

tff(f_91,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( v1_funct_1(k1_partfun1(A,B,C,D,E,F))
        & m1_subset_1(k1_partfun1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).

tff(f_71,axiom,(
    ! [A] : m1_subset_1(k6_relat_1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_relset_1)).

tff(f_69,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_132,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_funct_2)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_30,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_36,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_44,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_50,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_61,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_110,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_funct_2)).

tff(f_79,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A) )
     => ( v2_funct_2(B,A)
      <=> k2_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_funct_2)).

tff(c_52,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_198,plain,(
    ! [C_68,B_69,A_70] :
      ( v1_xboole_0(C_68)
      | ~ m1_subset_1(C_68,k1_zfmisc_1(k2_zfmisc_1(B_69,A_70)))
      | ~ v1_xboole_0(A_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_215,plain,
    ( v1_xboole_0('#skF_4')
    | ~ v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_52,c_198])).

tff(c_219,plain,(
    ~ v1_xboole_0('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_215])).

tff(c_48,plain,
    ( ~ v2_funct_2('#skF_4','#skF_1')
    | ~ v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_107,plain,(
    ~ v2_funct_1('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_48])).

tff(c_62,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_60,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_58,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_56,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_54,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_40,plain,(
    ! [A_31] : k6_relat_1(A_31) = k6_partfun1(A_31) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_14,plain,(
    ! [A_4] : v2_funct_1(k6_relat_1(A_4)) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_64,plain,(
    ! [A_4] : v2_funct_1(k6_partfun1(A_4)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_14])).

tff(c_36,plain,(
    ! [A_25,F_30,E_29,C_27,D_28,B_26] :
      ( m1_subset_1(k1_partfun1(A_25,B_26,C_27,D_28,E_29,F_30),k1_zfmisc_1(k2_zfmisc_1(A_25,D_28)))
      | ~ m1_subset_1(F_30,k1_zfmisc_1(k2_zfmisc_1(C_27,D_28)))
      | ~ v1_funct_1(F_30)
      | ~ m1_subset_1(E_29,k1_zfmisc_1(k2_zfmisc_1(A_25,B_26)))
      | ~ v1_funct_1(E_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_30,plain,(
    ! [A_22] : m1_subset_1(k6_relat_1(A_22),k1_zfmisc_1(k2_zfmisc_1(A_22,A_22))) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_63,plain,(
    ! [A_22] : m1_subset_1(k6_partfun1(A_22),k1_zfmisc_1(k2_zfmisc_1(A_22,A_22))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_30])).

tff(c_50,plain,(
    r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k6_partfun1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_457,plain,(
    ! [D_93,C_94,A_95,B_96] :
      ( D_93 = C_94
      | ~ r2_relset_1(A_95,B_96,C_94,D_93)
      | ~ m1_subset_1(D_93,k1_zfmisc_1(k2_zfmisc_1(A_95,B_96)))
      | ~ m1_subset_1(C_94,k1_zfmisc_1(k2_zfmisc_1(A_95,B_96))) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_467,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_50,c_457])).

tff(c_486,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_63,c_467])).

tff(c_499,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_486])).

tff(c_807,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_36,c_499])).

tff(c_811,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_58,c_56,c_52,c_807])).

tff(c_812,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_486])).

tff(c_1325,plain,(
    ! [B_180,D_181,C_183,A_179,E_182] :
      ( k1_xboole_0 = C_183
      | v2_funct_1(D_181)
      | ~ v2_funct_1(k1_partfun1(A_179,B_180,B_180,C_183,D_181,E_182))
      | ~ m1_subset_1(E_182,k1_zfmisc_1(k2_zfmisc_1(B_180,C_183)))
      | ~ v1_funct_2(E_182,B_180,C_183)
      | ~ v1_funct_1(E_182)
      | ~ m1_subset_1(D_181,k1_zfmisc_1(k2_zfmisc_1(A_179,B_180)))
      | ~ v1_funct_2(D_181,A_179,B_180)
      | ~ v1_funct_1(D_181) ) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_1327,plain,
    ( k1_xboole_0 = '#skF_1'
    | v2_funct_1('#skF_3')
    | ~ v2_funct_1(k6_partfun1('#skF_1'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_812,c_1325])).

tff(c_1329,plain,
    ( k1_xboole_0 = '#skF_1'
    | v2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_58,c_56,c_54,c_52,c_64,c_1327])).

tff(c_1330,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_107,c_1329])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_1371,plain,(
    v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1330,c_2])).

tff(c_1373,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_219,c_1371])).

tff(c_1374,plain,(
    v1_xboole_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_215])).

tff(c_1504,plain,(
    ! [A_189] :
      ( v1_xboole_0(k6_partfun1(A_189))
      | ~ v1_xboole_0(A_189) ) ),
    inference(resolution,[status(thm)],[c_63,c_198])).

tff(c_4,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_1379,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_1374,c_4])).

tff(c_1392,plain,(
    ! [A_1] :
      ( A_1 = '#skF_4'
      | ~ v1_xboole_0(A_1) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1379,c_4])).

tff(c_1518,plain,(
    ! [A_193] :
      ( k6_partfun1(A_193) = '#skF_4'
      | ~ v1_xboole_0(A_193) ) ),
    inference(resolution,[status(thm)],[c_1504,c_1392])).

tff(c_1526,plain,(
    k6_partfun1('#skF_4') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_1374,c_1518])).

tff(c_1545,plain,(
    v2_funct_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1526,c_64])).

tff(c_10,plain,(
    ! [B_3] : k2_zfmisc_1(k1_xboole_0,B_3) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_1390,plain,(
    ! [B_3] : k2_zfmisc_1('#skF_4',B_3) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1379,c_1379,c_10])).

tff(c_1375,plain,(
    v1_xboole_0('#skF_1') ),
    inference(splitRight,[status(thm)],[c_215])).

tff(c_1383,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_1375,c_4])).

tff(c_1399,plain,(
    '#skF_1' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1379,c_1383])).

tff(c_1405,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1399,c_58])).

tff(c_1527,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1390,c_1405])).

tff(c_8,plain,(
    ! [A_2] : k2_zfmisc_1(A_2,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_213,plain,(
    ! [C_68] :
      ( v1_xboole_0(C_68)
      | ~ m1_subset_1(C_68,k1_zfmisc_1(k1_xboole_0))
      | ~ v1_xboole_0(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_198])).

tff(c_218,plain,(
    ! [C_68] :
      ( v1_xboole_0(C_68)
      | ~ m1_subset_1(C_68,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_213])).

tff(c_1586,plain,(
    ! [C_197] :
      ( v1_xboole_0(C_197)
      | ~ m1_subset_1(C_197,k1_zfmisc_1('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1379,c_218])).

tff(c_1593,plain,(
    v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_1527,c_1586])).

tff(c_1603,plain,(
    '#skF_3' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_1593,c_1392])).

tff(c_1612,plain,(
    ~ v2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1603,c_107])).

tff(c_1621,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1545,c_1612])).

tff(c_1622,plain,(
    ~ v2_funct_2('#skF_4','#skF_1') ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_1634,plain,(
    ! [C_199,A_200,B_201] :
      ( v1_relat_1(C_199)
      | ~ m1_subset_1(C_199,k1_zfmisc_1(k2_zfmisc_1(A_200,B_201))) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_1650,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_52,c_1634])).

tff(c_1689,plain,(
    ! [C_209,B_210,A_211] :
      ( v5_relat_1(C_209,B_210)
      | ~ m1_subset_1(C_209,k1_zfmisc_1(k2_zfmisc_1(A_211,B_210))) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_1706,plain,(
    v5_relat_1('#skF_4','#skF_1') ),
    inference(resolution,[status(thm)],[c_52,c_1689])).

tff(c_1786,plain,(
    ! [A_223,B_224,D_225] :
      ( r2_relset_1(A_223,B_224,D_225,D_225)
      | ~ m1_subset_1(D_225,k1_zfmisc_1(k2_zfmisc_1(A_223,B_224))) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_1797,plain,(
    ! [A_22] : r2_relset_1(A_22,A_22,k6_partfun1(A_22),k6_partfun1(A_22)) ),
    inference(resolution,[status(thm)],[c_63,c_1786])).

tff(c_1842,plain,(
    ! [A_229,B_230,C_231] :
      ( k2_relset_1(A_229,B_230,C_231) = k2_relat_1(C_231)
      | ~ m1_subset_1(C_231,k1_zfmisc_1(k2_zfmisc_1(A_229,B_230))) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_1859,plain,(
    k2_relset_1('#skF_2','#skF_1','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_52,c_1842])).

tff(c_1927,plain,(
    ! [D_235,C_236,A_237,B_238] :
      ( D_235 = C_236
      | ~ r2_relset_1(A_237,B_238,C_236,D_235)
      | ~ m1_subset_1(D_235,k1_zfmisc_1(k2_zfmisc_1(A_237,B_238)))
      | ~ m1_subset_1(C_236,k1_zfmisc_1(k2_zfmisc_1(A_237,B_238))) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_1933,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_50,c_1927])).

tff(c_1944,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_63,c_1933])).

tff(c_1978,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_1944])).

tff(c_2320,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_36,c_1978])).

tff(c_2324,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_58,c_56,c_52,c_2320])).

tff(c_2325,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_1944])).

tff(c_2876,plain,(
    ! [A_341,B_342,C_343,D_344] :
      ( k2_relset_1(A_341,B_342,C_343) = B_342
      | ~ r2_relset_1(B_342,B_342,k1_partfun1(B_342,A_341,A_341,B_342,D_344,C_343),k6_partfun1(B_342))
      | ~ m1_subset_1(D_344,k1_zfmisc_1(k2_zfmisc_1(B_342,A_341)))
      | ~ v1_funct_2(D_344,B_342,A_341)
      | ~ v1_funct_1(D_344)
      | ~ m1_subset_1(C_343,k1_zfmisc_1(k2_zfmisc_1(A_341,B_342)))
      | ~ v1_funct_2(C_343,A_341,B_342)
      | ~ v1_funct_1(C_343) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_2879,plain,
    ( k2_relset_1('#skF_2','#skF_1','#skF_4') = '#skF_1'
    | ~ r2_relset_1('#skF_1','#skF_1',k6_partfun1('#skF_1'),k6_partfun1('#skF_1'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_2325,c_2876])).

tff(c_2887,plain,(
    k2_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_52,c_62,c_60,c_58,c_1797,c_1859,c_2879])).

tff(c_32,plain,(
    ! [B_24] :
      ( v2_funct_2(B_24,k2_relat_1(B_24))
      | ~ v5_relat_1(B_24,k2_relat_1(B_24))
      | ~ v1_relat_1(B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_2893,plain,
    ( v2_funct_2('#skF_4',k2_relat_1('#skF_4'))
    | ~ v5_relat_1('#skF_4','#skF_1')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_2887,c_32])).

tff(c_2897,plain,(
    v2_funct_2('#skF_4','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1650,c_1706,c_2887,c_2893])).

tff(c_2899,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1622,c_2897])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n010.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:00:44 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.72/1.82  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.72/1.83  
% 4.72/1.83  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.72/1.83  %$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 4.72/1.83  
% 4.72/1.83  %Foreground sorts:
% 4.72/1.83  
% 4.72/1.83  
% 4.72/1.83  %Background operators:
% 4.72/1.83  
% 4.72/1.83  
% 4.72/1.83  %Foreground operators:
% 4.72/1.83  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 4.72/1.83  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.72/1.83  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 4.72/1.83  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.72/1.83  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 4.72/1.83  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.72/1.83  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 4.72/1.83  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 4.72/1.83  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.72/1.83  tff('#skF_2', type, '#skF_2': $i).
% 4.72/1.83  tff('#skF_3', type, '#skF_3': $i).
% 4.72/1.83  tff('#skF_1', type, '#skF_1': $i).
% 4.72/1.83  tff(v2_funct_2, type, v2_funct_2: ($i * $i) > $o).
% 4.72/1.83  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 4.72/1.83  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.72/1.83  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 4.72/1.83  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.72/1.83  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.72/1.83  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.72/1.83  tff('#skF_4', type, '#skF_4': $i).
% 4.72/1.83  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 4.72/1.83  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.72/1.83  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 4.72/1.83  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.72/1.83  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.72/1.83  
% 4.72/1.85  tff(f_152, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (r2_relset_1(A, A, k1_partfun1(A, B, B, A, C, D), k6_partfun1(A)) => (v2_funct_1(C) & v2_funct_2(D, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_funct_2)).
% 4.72/1.85  tff(f_57, axiom, (![A, B]: (v1_xboole_0(A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => v1_xboole_0(C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc4_relset_1)).
% 4.72/1.85  tff(f_93, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 4.72/1.85  tff(f_40, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v2_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc4_funct_1)).
% 4.72/1.85  tff(f_91, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (v1_funct_1(k1_partfun1(A, B, C, D, E, F)) & m1_subset_1(k1_partfun1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 4.72/1.85  tff(f_71, axiom, (![A]: m1_subset_1(k6_relat_1(A), k1_zfmisc_1(k2_zfmisc_1(A, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_relset_1)).
% 4.72/1.85  tff(f_69, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 4.72/1.85  tff(f_132, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, B, C)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (v2_funct_1(k1_partfun1(A, B, B, C, D, E)) => (((C = k1_xboole_0) & ~(B = k1_xboole_0)) | v2_funct_1(D))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t26_funct_2)).
% 4.72/1.85  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 4.72/1.85  tff(f_30, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 4.72/1.85  tff(f_36, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 4.72/1.85  tff(f_44, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 4.72/1.85  tff(f_50, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 4.72/1.85  tff(f_61, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 4.72/1.85  tff(f_110, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (r2_relset_1(B, B, k1_partfun1(B, A, A, B, D, C), k6_partfun1(B)) => (k2_relset_1(A, B, C) = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t24_funct_2)).
% 4.72/1.85  tff(f_79, axiom, (![A, B]: ((v1_relat_1(B) & v5_relat_1(B, A)) => (v2_funct_2(B, A) <=> (k2_relat_1(B) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_funct_2)).
% 4.72/1.85  tff(c_52, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_152])).
% 4.72/1.85  tff(c_198, plain, (![C_68, B_69, A_70]: (v1_xboole_0(C_68) | ~m1_subset_1(C_68, k1_zfmisc_1(k2_zfmisc_1(B_69, A_70))) | ~v1_xboole_0(A_70))), inference(cnfTransformation, [status(thm)], [f_57])).
% 4.72/1.85  tff(c_215, plain, (v1_xboole_0('#skF_4') | ~v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_52, c_198])).
% 4.72/1.85  tff(c_219, plain, (~v1_xboole_0('#skF_1')), inference(splitLeft, [status(thm)], [c_215])).
% 4.72/1.85  tff(c_48, plain, (~v2_funct_2('#skF_4', '#skF_1') | ~v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_152])).
% 4.72/1.85  tff(c_107, plain, (~v2_funct_1('#skF_3')), inference(splitLeft, [status(thm)], [c_48])).
% 4.72/1.85  tff(c_62, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_152])).
% 4.72/1.85  tff(c_60, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_152])).
% 4.72/1.85  tff(c_58, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_152])).
% 4.72/1.85  tff(c_56, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_152])).
% 4.72/1.85  tff(c_54, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_152])).
% 4.72/1.85  tff(c_40, plain, (![A_31]: (k6_relat_1(A_31)=k6_partfun1(A_31))), inference(cnfTransformation, [status(thm)], [f_93])).
% 4.72/1.85  tff(c_14, plain, (![A_4]: (v2_funct_1(k6_relat_1(A_4)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 4.72/1.85  tff(c_64, plain, (![A_4]: (v2_funct_1(k6_partfun1(A_4)))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_14])).
% 4.72/1.85  tff(c_36, plain, (![A_25, F_30, E_29, C_27, D_28, B_26]: (m1_subset_1(k1_partfun1(A_25, B_26, C_27, D_28, E_29, F_30), k1_zfmisc_1(k2_zfmisc_1(A_25, D_28))) | ~m1_subset_1(F_30, k1_zfmisc_1(k2_zfmisc_1(C_27, D_28))) | ~v1_funct_1(F_30) | ~m1_subset_1(E_29, k1_zfmisc_1(k2_zfmisc_1(A_25, B_26))) | ~v1_funct_1(E_29))), inference(cnfTransformation, [status(thm)], [f_91])).
% 4.72/1.85  tff(c_30, plain, (![A_22]: (m1_subset_1(k6_relat_1(A_22), k1_zfmisc_1(k2_zfmisc_1(A_22, A_22))))), inference(cnfTransformation, [status(thm)], [f_71])).
% 4.72/1.85  tff(c_63, plain, (![A_22]: (m1_subset_1(k6_partfun1(A_22), k1_zfmisc_1(k2_zfmisc_1(A_22, A_22))))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_30])).
% 4.72/1.85  tff(c_50, plain, (r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k6_partfun1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_152])).
% 4.72/1.85  tff(c_457, plain, (![D_93, C_94, A_95, B_96]: (D_93=C_94 | ~r2_relset_1(A_95, B_96, C_94, D_93) | ~m1_subset_1(D_93, k1_zfmisc_1(k2_zfmisc_1(A_95, B_96))) | ~m1_subset_1(C_94, k1_zfmisc_1(k2_zfmisc_1(A_95, B_96))))), inference(cnfTransformation, [status(thm)], [f_69])).
% 4.72/1.85  tff(c_467, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_50, c_457])).
% 4.72/1.85  tff(c_486, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_63, c_467])).
% 4.72/1.85  tff(c_499, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_486])).
% 4.72/1.85  tff(c_807, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_36, c_499])).
% 4.72/1.85  tff(c_811, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_62, c_58, c_56, c_52, c_807])).
% 4.72/1.85  tff(c_812, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_486])).
% 4.72/1.85  tff(c_1325, plain, (![B_180, D_181, C_183, A_179, E_182]: (k1_xboole_0=C_183 | v2_funct_1(D_181) | ~v2_funct_1(k1_partfun1(A_179, B_180, B_180, C_183, D_181, E_182)) | ~m1_subset_1(E_182, k1_zfmisc_1(k2_zfmisc_1(B_180, C_183))) | ~v1_funct_2(E_182, B_180, C_183) | ~v1_funct_1(E_182) | ~m1_subset_1(D_181, k1_zfmisc_1(k2_zfmisc_1(A_179, B_180))) | ~v1_funct_2(D_181, A_179, B_180) | ~v1_funct_1(D_181))), inference(cnfTransformation, [status(thm)], [f_132])).
% 4.72/1.85  tff(c_1327, plain, (k1_xboole_0='#skF_1' | v2_funct_1('#skF_3') | ~v2_funct_1(k6_partfun1('#skF_1')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_812, c_1325])).
% 4.72/1.85  tff(c_1329, plain, (k1_xboole_0='#skF_1' | v2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_58, c_56, c_54, c_52, c_64, c_1327])).
% 4.72/1.85  tff(c_1330, plain, (k1_xboole_0='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_107, c_1329])).
% 4.72/1.85  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 4.72/1.85  tff(c_1371, plain, (v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1330, c_2])).
% 4.72/1.85  tff(c_1373, plain, $false, inference(negUnitSimplification, [status(thm)], [c_219, c_1371])).
% 4.72/1.85  tff(c_1374, plain, (v1_xboole_0('#skF_4')), inference(splitRight, [status(thm)], [c_215])).
% 4.72/1.85  tff(c_1504, plain, (![A_189]: (v1_xboole_0(k6_partfun1(A_189)) | ~v1_xboole_0(A_189))), inference(resolution, [status(thm)], [c_63, c_198])).
% 4.72/1.85  tff(c_4, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_30])).
% 4.72/1.85  tff(c_1379, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_1374, c_4])).
% 4.72/1.85  tff(c_1392, plain, (![A_1]: (A_1='#skF_4' | ~v1_xboole_0(A_1))), inference(demodulation, [status(thm), theory('equality')], [c_1379, c_4])).
% 4.72/1.85  tff(c_1518, plain, (![A_193]: (k6_partfun1(A_193)='#skF_4' | ~v1_xboole_0(A_193))), inference(resolution, [status(thm)], [c_1504, c_1392])).
% 4.72/1.85  tff(c_1526, plain, (k6_partfun1('#skF_4')='#skF_4'), inference(resolution, [status(thm)], [c_1374, c_1518])).
% 4.72/1.85  tff(c_1545, plain, (v2_funct_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1526, c_64])).
% 4.72/1.85  tff(c_10, plain, (![B_3]: (k2_zfmisc_1(k1_xboole_0, B_3)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_36])).
% 4.72/1.85  tff(c_1390, plain, (![B_3]: (k2_zfmisc_1('#skF_4', B_3)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1379, c_1379, c_10])).
% 4.72/1.85  tff(c_1375, plain, (v1_xboole_0('#skF_1')), inference(splitRight, [status(thm)], [c_215])).
% 4.72/1.85  tff(c_1383, plain, (k1_xboole_0='#skF_1'), inference(resolution, [status(thm)], [c_1375, c_4])).
% 4.72/1.85  tff(c_1399, plain, ('#skF_1'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_1379, c_1383])).
% 4.72/1.85  tff(c_1405, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_1399, c_58])).
% 4.72/1.85  tff(c_1527, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_1390, c_1405])).
% 4.72/1.85  tff(c_8, plain, (![A_2]: (k2_zfmisc_1(A_2, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_36])).
% 4.72/1.85  tff(c_213, plain, (![C_68]: (v1_xboole_0(C_68) | ~m1_subset_1(C_68, k1_zfmisc_1(k1_xboole_0)) | ~v1_xboole_0(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_8, c_198])).
% 4.72/1.85  tff(c_218, plain, (![C_68]: (v1_xboole_0(C_68) | ~m1_subset_1(C_68, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_213])).
% 4.72/1.85  tff(c_1586, plain, (![C_197]: (v1_xboole_0(C_197) | ~m1_subset_1(C_197, k1_zfmisc_1('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_1379, c_218])).
% 4.72/1.85  tff(c_1593, plain, (v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_1527, c_1586])).
% 4.72/1.85  tff(c_1603, plain, ('#skF_3'='#skF_4'), inference(resolution, [status(thm)], [c_1593, c_1392])).
% 4.72/1.85  tff(c_1612, plain, (~v2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1603, c_107])).
% 4.72/1.85  tff(c_1621, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1545, c_1612])).
% 4.72/1.85  tff(c_1622, plain, (~v2_funct_2('#skF_4', '#skF_1')), inference(splitRight, [status(thm)], [c_48])).
% 4.72/1.85  tff(c_1634, plain, (![C_199, A_200, B_201]: (v1_relat_1(C_199) | ~m1_subset_1(C_199, k1_zfmisc_1(k2_zfmisc_1(A_200, B_201))))), inference(cnfTransformation, [status(thm)], [f_44])).
% 4.72/1.85  tff(c_1650, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_52, c_1634])).
% 4.72/1.85  tff(c_1689, plain, (![C_209, B_210, A_211]: (v5_relat_1(C_209, B_210) | ~m1_subset_1(C_209, k1_zfmisc_1(k2_zfmisc_1(A_211, B_210))))), inference(cnfTransformation, [status(thm)], [f_50])).
% 4.72/1.85  tff(c_1706, plain, (v5_relat_1('#skF_4', '#skF_1')), inference(resolution, [status(thm)], [c_52, c_1689])).
% 4.72/1.85  tff(c_1786, plain, (![A_223, B_224, D_225]: (r2_relset_1(A_223, B_224, D_225, D_225) | ~m1_subset_1(D_225, k1_zfmisc_1(k2_zfmisc_1(A_223, B_224))))), inference(cnfTransformation, [status(thm)], [f_69])).
% 4.72/1.85  tff(c_1797, plain, (![A_22]: (r2_relset_1(A_22, A_22, k6_partfun1(A_22), k6_partfun1(A_22)))), inference(resolution, [status(thm)], [c_63, c_1786])).
% 4.72/1.85  tff(c_1842, plain, (![A_229, B_230, C_231]: (k2_relset_1(A_229, B_230, C_231)=k2_relat_1(C_231) | ~m1_subset_1(C_231, k1_zfmisc_1(k2_zfmisc_1(A_229, B_230))))), inference(cnfTransformation, [status(thm)], [f_61])).
% 4.72/1.85  tff(c_1859, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_52, c_1842])).
% 4.72/1.85  tff(c_1927, plain, (![D_235, C_236, A_237, B_238]: (D_235=C_236 | ~r2_relset_1(A_237, B_238, C_236, D_235) | ~m1_subset_1(D_235, k1_zfmisc_1(k2_zfmisc_1(A_237, B_238))) | ~m1_subset_1(C_236, k1_zfmisc_1(k2_zfmisc_1(A_237, B_238))))), inference(cnfTransformation, [status(thm)], [f_69])).
% 4.72/1.85  tff(c_1933, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_50, c_1927])).
% 4.72/1.85  tff(c_1944, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_63, c_1933])).
% 4.72/1.85  tff(c_1978, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_1944])).
% 4.72/1.85  tff(c_2320, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_36, c_1978])).
% 4.72/1.85  tff(c_2324, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_62, c_58, c_56, c_52, c_2320])).
% 4.72/1.85  tff(c_2325, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_1944])).
% 4.72/1.85  tff(c_2876, plain, (![A_341, B_342, C_343, D_344]: (k2_relset_1(A_341, B_342, C_343)=B_342 | ~r2_relset_1(B_342, B_342, k1_partfun1(B_342, A_341, A_341, B_342, D_344, C_343), k6_partfun1(B_342)) | ~m1_subset_1(D_344, k1_zfmisc_1(k2_zfmisc_1(B_342, A_341))) | ~v1_funct_2(D_344, B_342, A_341) | ~v1_funct_1(D_344) | ~m1_subset_1(C_343, k1_zfmisc_1(k2_zfmisc_1(A_341, B_342))) | ~v1_funct_2(C_343, A_341, B_342) | ~v1_funct_1(C_343))), inference(cnfTransformation, [status(thm)], [f_110])).
% 4.72/1.85  tff(c_2879, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')='#skF_1' | ~r2_relset_1('#skF_1', '#skF_1', k6_partfun1('#skF_1'), k6_partfun1('#skF_1')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_2325, c_2876])).
% 4.72/1.85  tff(c_2887, plain, (k2_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_52, c_62, c_60, c_58, c_1797, c_1859, c_2879])).
% 4.72/1.85  tff(c_32, plain, (![B_24]: (v2_funct_2(B_24, k2_relat_1(B_24)) | ~v5_relat_1(B_24, k2_relat_1(B_24)) | ~v1_relat_1(B_24))), inference(cnfTransformation, [status(thm)], [f_79])).
% 4.72/1.85  tff(c_2893, plain, (v2_funct_2('#skF_4', k2_relat_1('#skF_4')) | ~v5_relat_1('#skF_4', '#skF_1') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_2887, c_32])).
% 4.72/1.85  tff(c_2897, plain, (v2_funct_2('#skF_4', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1650, c_1706, c_2887, c_2893])).
% 4.72/1.85  tff(c_2899, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1622, c_2897])).
% 4.72/1.85  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.72/1.85  
% 4.72/1.85  Inference rules
% 4.72/1.85  ----------------------
% 4.72/1.85  #Ref     : 0
% 4.72/1.85  #Sup     : 642
% 4.72/1.85  #Fact    : 0
% 4.72/1.85  #Define  : 0
% 4.72/1.85  #Split   : 13
% 4.72/1.85  #Chain   : 0
% 4.72/1.85  #Close   : 0
% 4.72/1.85  
% 4.72/1.85  Ordering : KBO
% 4.72/1.85  
% 4.72/1.85  Simplification rules
% 4.72/1.85  ----------------------
% 4.72/1.85  #Subsume      : 59
% 4.72/1.85  #Demod        : 665
% 4.72/1.85  #Tautology    : 318
% 4.72/1.85  #SimpNegUnit  : 3
% 4.72/1.85  #BackRed      : 78
% 4.72/1.85  
% 4.72/1.85  #Partial instantiations: 0
% 4.72/1.85  #Strategies tried      : 1
% 4.72/1.85  
% 4.72/1.85  Timing (in seconds)
% 4.72/1.85  ----------------------
% 4.72/1.86  Preprocessing        : 0.35
% 4.72/1.86  Parsing              : 0.19
% 4.72/1.86  CNF conversion       : 0.02
% 4.72/1.86  Main loop            : 0.73
% 4.72/1.86  Inferencing          : 0.26
% 4.72/1.86  Reduction            : 0.26
% 4.72/1.86  Demodulation         : 0.19
% 4.72/1.86  BG Simplification    : 0.03
% 4.72/1.86  Subsumption          : 0.12
% 4.72/1.86  Abstraction          : 0.03
% 4.72/1.86  MUC search           : 0.00
% 4.72/1.86  Cooper               : 0.00
% 4.72/1.86  Total                : 1.12
% 4.72/1.86  Index Insertion      : 0.00
% 4.72/1.86  Index Deletion       : 0.00
% 4.72/1.86  Index Matching       : 0.00
% 4.72/1.86  BG Taut test         : 0.00
%------------------------------------------------------------------------------
