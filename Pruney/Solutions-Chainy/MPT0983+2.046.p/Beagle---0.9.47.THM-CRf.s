%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:12:07 EST 2020

% Result     : Theorem 3.88s
% Output     : CNFRefutation 4.41s
% Verified   : 
% Statistics : Number of formulae       :  109 ( 275 expanded)
%              Number of leaves         :   41 ( 115 expanded)
%              Depth                    :   10
%              Number of atoms          :  196 ( 836 expanded)
%              Number of equality atoms :   34 (  73 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > v1_partfun1 > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(v1_partfun1,type,(
    v1_partfun1: ( $i * $i ) > $o )).

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

tff(f_146,negated_conjecture,(
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

tff(f_49,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => v1_xboole_0(C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc3_relset_1)).

tff(f_87,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_32,axiom,(
    ! [A] : v2_funct_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_funct_1)).

tff(f_81,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( v1_funct_1(k1_partfun1(A,B,C,D,E,F))
        & m1_subset_1(k1_partfun1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).

tff(f_85,axiom,(
    ! [A] :
      ( v1_partfun1(k6_partfun1(A),A)
      & m1_subset_1(k6_partfun1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_partfun1)).

tff(f_61,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_126,axiom,(
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
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_42,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_53,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_104,axiom,(
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

tff(f_69,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A) )
     => ( v2_funct_2(B,A)
      <=> k2_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_funct_2)).

tff(c_52,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_120,plain,(
    ! [C_60,A_61,B_62] :
      ( v1_xboole_0(C_60)
      | ~ m1_subset_1(C_60,k1_zfmisc_1(k2_zfmisc_1(A_61,B_62)))
      | ~ v1_xboole_0(A_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_132,plain,
    ( v1_xboole_0('#skF_3')
    | ~ v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_52,c_120])).

tff(c_134,plain,(
    ~ v1_xboole_0('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_132])).

tff(c_42,plain,
    ( ~ v2_funct_2('#skF_4','#skF_1')
    | ~ v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_75,plain,(
    ~ v2_funct_1('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_42])).

tff(c_56,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_54,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_50,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_48,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_46,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_34,plain,(
    ! [A_29] : k6_relat_1(A_29) = k6_partfun1(A_29) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_6,plain,(
    ! [A_2] : v2_funct_1(k6_relat_1(A_2)) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_57,plain,(
    ! [A_2] : v2_funct_1(k6_partfun1(A_2)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_6])).

tff(c_26,plain,(
    ! [E_26,F_27,A_22,B_23,D_25,C_24] :
      ( m1_subset_1(k1_partfun1(A_22,B_23,C_24,D_25,E_26,F_27),k1_zfmisc_1(k2_zfmisc_1(A_22,D_25)))
      | ~ m1_subset_1(F_27,k1_zfmisc_1(k2_zfmisc_1(C_24,D_25)))
      | ~ v1_funct_1(F_27)
      | ~ m1_subset_1(E_26,k1_zfmisc_1(k2_zfmisc_1(A_22,B_23)))
      | ~ v1_funct_1(E_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_32,plain,(
    ! [A_28] : m1_subset_1(k6_partfun1(A_28),k1_zfmisc_1(k2_zfmisc_1(A_28,A_28))) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_44,plain,(
    r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k6_partfun1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_344,plain,(
    ! [D_77,C_78,A_79,B_80] :
      ( D_77 = C_78
      | ~ r2_relset_1(A_79,B_80,C_78,D_77)
      | ~ m1_subset_1(D_77,k1_zfmisc_1(k2_zfmisc_1(A_79,B_80)))
      | ~ m1_subset_1(C_78,k1_zfmisc_1(k2_zfmisc_1(A_79,B_80))) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_352,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_44,c_344])).

tff(c_367,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_352])).

tff(c_810,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_367])).

tff(c_813,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_26,c_810])).

tff(c_817,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_52,c_50,c_46,c_813])).

tff(c_818,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_367])).

tff(c_851,plain,(
    ! [A_119,E_122,D_121,C_120,B_123] :
      ( k1_xboole_0 = C_120
      | v2_funct_1(D_121)
      | ~ v2_funct_1(k1_partfun1(A_119,B_123,B_123,C_120,D_121,E_122))
      | ~ m1_subset_1(E_122,k1_zfmisc_1(k2_zfmisc_1(B_123,C_120)))
      | ~ v1_funct_2(E_122,B_123,C_120)
      | ~ v1_funct_1(E_122)
      | ~ m1_subset_1(D_121,k1_zfmisc_1(k2_zfmisc_1(A_119,B_123)))
      | ~ v1_funct_2(D_121,A_119,B_123)
      | ~ v1_funct_1(D_121) ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_853,plain,
    ( k1_xboole_0 = '#skF_1'
    | v2_funct_1('#skF_3')
    | ~ v2_funct_1(k6_partfun1('#skF_1'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_818,c_851])).

tff(c_855,plain,
    ( k1_xboole_0 = '#skF_1'
    | v2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_52,c_50,c_48,c_46,c_57,c_853])).

tff(c_856,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_75,c_855])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_887,plain,(
    v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_856,c_2])).

tff(c_889,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_134,c_887])).

tff(c_891,plain,(
    v1_xboole_0('#skF_1') ),
    inference(splitRight,[status(thm)],[c_132])).

tff(c_4,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_899,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_891,c_4])).

tff(c_890,plain,(
    v1_xboole_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_132])).

tff(c_895,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_890,c_4])).

tff(c_907,plain,(
    '#skF_3' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_899,c_895])).

tff(c_918,plain,(
    ~ v2_funct_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_907,c_75])).

tff(c_940,plain,(
    ! [A_128] :
      ( v1_xboole_0(k6_partfun1(A_128))
      | ~ v1_xboole_0(A_128) ) ),
    inference(resolution,[status(thm)],[c_32,c_120])).

tff(c_900,plain,(
    ! [A_1] :
      ( A_1 = '#skF_3'
      | ~ v1_xboole_0(A_1) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_895,c_4])).

tff(c_933,plain,(
    ! [A_1] :
      ( A_1 = '#skF_1'
      | ~ v1_xboole_0(A_1) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_907,c_900])).

tff(c_945,plain,(
    ! [A_129] :
      ( k6_partfun1(A_129) = '#skF_1'
      | ~ v1_xboole_0(A_129) ) ),
    inference(resolution,[status(thm)],[c_940,c_933])).

tff(c_953,plain,(
    k6_partfun1('#skF_1') = '#skF_1' ),
    inference(resolution,[status(thm)],[c_891,c_945])).

tff(c_973,plain,(
    v2_funct_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_953,c_57])).

tff(c_981,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_918,c_973])).

tff(c_982,plain,(
    ~ v2_funct_2('#skF_4','#skF_1') ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_985,plain,(
    ! [C_131,A_132,B_133] :
      ( v1_relat_1(C_131)
      | ~ m1_subset_1(C_131,k1_zfmisc_1(k2_zfmisc_1(A_132,B_133))) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_996,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_46,c_985])).

tff(c_1012,plain,(
    ! [C_138,B_139,A_140] :
      ( v5_relat_1(C_138,B_139)
      | ~ m1_subset_1(C_138,k1_zfmisc_1(k2_zfmisc_1(A_140,B_139))) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_1023,plain,(
    v5_relat_1('#skF_4','#skF_1') ),
    inference(resolution,[status(thm)],[c_46,c_1012])).

tff(c_1101,plain,(
    ! [A_151,B_152,D_153] :
      ( r2_relset_1(A_151,B_152,D_153,D_153)
      | ~ m1_subset_1(D_153,k1_zfmisc_1(k2_zfmisc_1(A_151,B_152))) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_1108,plain,(
    ! [A_28] : r2_relset_1(A_28,A_28,k6_partfun1(A_28),k6_partfun1(A_28)) ),
    inference(resolution,[status(thm)],[c_32,c_1101])).

tff(c_1186,plain,(
    ! [A_155,B_156,C_157] :
      ( k2_relset_1(A_155,B_156,C_157) = k2_relat_1(C_157)
      | ~ m1_subset_1(C_157,k1_zfmisc_1(k2_zfmisc_1(A_155,B_156))) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_1201,plain,(
    k2_relset_1('#skF_2','#skF_1','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_46,c_1186])).

tff(c_1221,plain,(
    ! [D_159,C_160,A_161,B_162] :
      ( D_159 = C_160
      | ~ r2_relset_1(A_161,B_162,C_160,D_159)
      | ~ m1_subset_1(D_159,k1_zfmisc_1(k2_zfmisc_1(A_161,B_162)))
      | ~ m1_subset_1(C_160,k1_zfmisc_1(k2_zfmisc_1(A_161,B_162))) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_1229,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_44,c_1221])).

tff(c_1244,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_1229])).

tff(c_1666,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_1244])).

tff(c_1702,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_26,c_1666])).

tff(c_1706,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_52,c_50,c_46,c_1702])).

tff(c_1707,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_1244])).

tff(c_1921,plain,(
    ! [A_212,B_213,C_214,D_215] :
      ( k2_relset_1(A_212,B_213,C_214) = B_213
      | ~ r2_relset_1(B_213,B_213,k1_partfun1(B_213,A_212,A_212,B_213,D_215,C_214),k6_partfun1(B_213))
      | ~ m1_subset_1(D_215,k1_zfmisc_1(k2_zfmisc_1(B_213,A_212)))
      | ~ v1_funct_2(D_215,B_213,A_212)
      | ~ v1_funct_1(D_215)
      | ~ m1_subset_1(C_214,k1_zfmisc_1(k2_zfmisc_1(A_212,B_213)))
      | ~ v1_funct_2(C_214,A_212,B_213)
      | ~ v1_funct_1(C_214) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_1924,plain,
    ( k2_relset_1('#skF_2','#skF_1','#skF_4') = '#skF_1'
    | ~ r2_relset_1('#skF_1','#skF_1',k6_partfun1('#skF_1'),k6_partfun1('#skF_1'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1707,c_1921])).

tff(c_1932,plain,(
    k2_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_46,c_56,c_54,c_52,c_1108,c_1201,c_1924])).

tff(c_22,plain,(
    ! [B_21] :
      ( v2_funct_2(B_21,k2_relat_1(B_21))
      | ~ v5_relat_1(B_21,k2_relat_1(B_21))
      | ~ v1_relat_1(B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_1937,plain,
    ( v2_funct_2('#skF_4',k2_relat_1('#skF_4'))
    | ~ v5_relat_1('#skF_4','#skF_1')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1932,c_22])).

tff(c_1941,plain,(
    v2_funct_2('#skF_4','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_996,c_1023,c_1932,c_1937])).

tff(c_1943,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_982,c_1941])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:50:51 EST 2020
% 0.19/0.34  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.88/1.76  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.21/1.78  
% 4.21/1.78  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.21/1.78  %$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > v1_partfun1 > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 4.21/1.78  
% 4.21/1.78  %Foreground sorts:
% 4.21/1.78  
% 4.21/1.78  
% 4.21/1.78  %Background operators:
% 4.21/1.78  
% 4.21/1.78  
% 4.21/1.78  %Foreground operators:
% 4.21/1.78  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 4.21/1.78  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.21/1.78  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 4.21/1.78  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.21/1.78  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 4.21/1.78  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.21/1.78  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 4.21/1.78  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 4.21/1.78  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.21/1.78  tff('#skF_2', type, '#skF_2': $i).
% 4.21/1.78  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 4.21/1.78  tff('#skF_3', type, '#skF_3': $i).
% 4.21/1.78  tff('#skF_1', type, '#skF_1': $i).
% 4.21/1.78  tff(v2_funct_2, type, v2_funct_2: ($i * $i) > $o).
% 4.21/1.78  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 4.21/1.78  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.21/1.78  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 4.21/1.78  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.21/1.78  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.21/1.78  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.21/1.78  tff('#skF_4', type, '#skF_4': $i).
% 4.21/1.78  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 4.21/1.78  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.21/1.78  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 4.21/1.78  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.21/1.78  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.21/1.78  
% 4.41/1.82  tff(f_146, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (r2_relset_1(A, A, k1_partfun1(A, B, B, A, C, D), k6_partfun1(A)) => (v2_funct_1(C) & v2_funct_2(D, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_funct_2)).
% 4.41/1.82  tff(f_49, axiom, (![A, B]: (v1_xboole_0(A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_xboole_0(C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc3_relset_1)).
% 4.41/1.82  tff(f_87, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 4.41/1.82  tff(f_32, axiom, (![A]: v2_funct_1(k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_funct_1)).
% 4.41/1.82  tff(f_81, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (v1_funct_1(k1_partfun1(A, B, C, D, E, F)) & m1_subset_1(k1_partfun1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 4.41/1.82  tff(f_85, axiom, (![A]: (v1_partfun1(k6_partfun1(A), A) & m1_subset_1(k6_partfun1(A), k1_zfmisc_1(k2_zfmisc_1(A, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_partfun1)).
% 4.41/1.82  tff(f_61, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 4.41/1.82  tff(f_126, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, B, C)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (v2_funct_1(k1_partfun1(A, B, B, C, D, E)) => (((C = k1_xboole_0) & ~(B = k1_xboole_0)) | v2_funct_1(D))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t26_funct_2)).
% 4.41/1.82  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 4.41/1.82  tff(f_30, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 4.41/1.82  tff(f_36, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 4.41/1.82  tff(f_42, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 4.41/1.82  tff(f_53, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 4.41/1.82  tff(f_104, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (r2_relset_1(B, B, k1_partfun1(B, A, A, B, D, C), k6_partfun1(B)) => (k2_relset_1(A, B, C) = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t24_funct_2)).
% 4.41/1.82  tff(f_69, axiom, (![A, B]: ((v1_relat_1(B) & v5_relat_1(B, A)) => (v2_funct_2(B, A) <=> (k2_relat_1(B) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_funct_2)).
% 4.41/1.82  tff(c_52, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_146])).
% 4.41/1.82  tff(c_120, plain, (![C_60, A_61, B_62]: (v1_xboole_0(C_60) | ~m1_subset_1(C_60, k1_zfmisc_1(k2_zfmisc_1(A_61, B_62))) | ~v1_xboole_0(A_61))), inference(cnfTransformation, [status(thm)], [f_49])).
% 4.41/1.82  tff(c_132, plain, (v1_xboole_0('#skF_3') | ~v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_52, c_120])).
% 4.41/1.82  tff(c_134, plain, (~v1_xboole_0('#skF_1')), inference(splitLeft, [status(thm)], [c_132])).
% 4.41/1.82  tff(c_42, plain, (~v2_funct_2('#skF_4', '#skF_1') | ~v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_146])).
% 4.41/1.82  tff(c_75, plain, (~v2_funct_1('#skF_3')), inference(splitLeft, [status(thm)], [c_42])).
% 4.41/1.82  tff(c_56, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_146])).
% 4.41/1.82  tff(c_54, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_146])).
% 4.41/1.82  tff(c_50, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_146])).
% 4.41/1.82  tff(c_48, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_146])).
% 4.41/1.82  tff(c_46, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_146])).
% 4.41/1.82  tff(c_34, plain, (![A_29]: (k6_relat_1(A_29)=k6_partfun1(A_29))), inference(cnfTransformation, [status(thm)], [f_87])).
% 4.41/1.82  tff(c_6, plain, (![A_2]: (v2_funct_1(k6_relat_1(A_2)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.41/1.82  tff(c_57, plain, (![A_2]: (v2_funct_1(k6_partfun1(A_2)))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_6])).
% 4.41/1.82  tff(c_26, plain, (![E_26, F_27, A_22, B_23, D_25, C_24]: (m1_subset_1(k1_partfun1(A_22, B_23, C_24, D_25, E_26, F_27), k1_zfmisc_1(k2_zfmisc_1(A_22, D_25))) | ~m1_subset_1(F_27, k1_zfmisc_1(k2_zfmisc_1(C_24, D_25))) | ~v1_funct_1(F_27) | ~m1_subset_1(E_26, k1_zfmisc_1(k2_zfmisc_1(A_22, B_23))) | ~v1_funct_1(E_26))), inference(cnfTransformation, [status(thm)], [f_81])).
% 4.41/1.82  tff(c_32, plain, (![A_28]: (m1_subset_1(k6_partfun1(A_28), k1_zfmisc_1(k2_zfmisc_1(A_28, A_28))))), inference(cnfTransformation, [status(thm)], [f_85])).
% 4.41/1.82  tff(c_44, plain, (r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k6_partfun1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_146])).
% 4.41/1.82  tff(c_344, plain, (![D_77, C_78, A_79, B_80]: (D_77=C_78 | ~r2_relset_1(A_79, B_80, C_78, D_77) | ~m1_subset_1(D_77, k1_zfmisc_1(k2_zfmisc_1(A_79, B_80))) | ~m1_subset_1(C_78, k1_zfmisc_1(k2_zfmisc_1(A_79, B_80))))), inference(cnfTransformation, [status(thm)], [f_61])).
% 4.41/1.82  tff(c_352, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_44, c_344])).
% 4.41/1.82  tff(c_367, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_352])).
% 4.41/1.82  tff(c_810, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_367])).
% 4.41/1.82  tff(c_813, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_26, c_810])).
% 4.41/1.82  tff(c_817, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_56, c_52, c_50, c_46, c_813])).
% 4.41/1.82  tff(c_818, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_367])).
% 4.41/1.82  tff(c_851, plain, (![A_119, E_122, D_121, C_120, B_123]: (k1_xboole_0=C_120 | v2_funct_1(D_121) | ~v2_funct_1(k1_partfun1(A_119, B_123, B_123, C_120, D_121, E_122)) | ~m1_subset_1(E_122, k1_zfmisc_1(k2_zfmisc_1(B_123, C_120))) | ~v1_funct_2(E_122, B_123, C_120) | ~v1_funct_1(E_122) | ~m1_subset_1(D_121, k1_zfmisc_1(k2_zfmisc_1(A_119, B_123))) | ~v1_funct_2(D_121, A_119, B_123) | ~v1_funct_1(D_121))), inference(cnfTransformation, [status(thm)], [f_126])).
% 4.41/1.82  tff(c_853, plain, (k1_xboole_0='#skF_1' | v2_funct_1('#skF_3') | ~v2_funct_1(k6_partfun1('#skF_1')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_818, c_851])).
% 4.41/1.82  tff(c_855, plain, (k1_xboole_0='#skF_1' | v2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_52, c_50, c_48, c_46, c_57, c_853])).
% 4.41/1.82  tff(c_856, plain, (k1_xboole_0='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_75, c_855])).
% 4.41/1.82  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 4.41/1.82  tff(c_887, plain, (v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_856, c_2])).
% 4.41/1.82  tff(c_889, plain, $false, inference(negUnitSimplification, [status(thm)], [c_134, c_887])).
% 4.41/1.82  tff(c_891, plain, (v1_xboole_0('#skF_1')), inference(splitRight, [status(thm)], [c_132])).
% 4.41/1.82  tff(c_4, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_30])).
% 4.41/1.82  tff(c_899, plain, (k1_xboole_0='#skF_1'), inference(resolution, [status(thm)], [c_891, c_4])).
% 4.41/1.82  tff(c_890, plain, (v1_xboole_0('#skF_3')), inference(splitRight, [status(thm)], [c_132])).
% 4.41/1.82  tff(c_895, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_890, c_4])).
% 4.41/1.82  tff(c_907, plain, ('#skF_3'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_899, c_895])).
% 4.41/1.82  tff(c_918, plain, (~v2_funct_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_907, c_75])).
% 4.41/1.82  tff(c_940, plain, (![A_128]: (v1_xboole_0(k6_partfun1(A_128)) | ~v1_xboole_0(A_128))), inference(resolution, [status(thm)], [c_32, c_120])).
% 4.41/1.82  tff(c_900, plain, (![A_1]: (A_1='#skF_3' | ~v1_xboole_0(A_1))), inference(demodulation, [status(thm), theory('equality')], [c_895, c_4])).
% 4.41/1.82  tff(c_933, plain, (![A_1]: (A_1='#skF_1' | ~v1_xboole_0(A_1))), inference(demodulation, [status(thm), theory('equality')], [c_907, c_900])).
% 4.41/1.82  tff(c_945, plain, (![A_129]: (k6_partfun1(A_129)='#skF_1' | ~v1_xboole_0(A_129))), inference(resolution, [status(thm)], [c_940, c_933])).
% 4.41/1.82  tff(c_953, plain, (k6_partfun1('#skF_1')='#skF_1'), inference(resolution, [status(thm)], [c_891, c_945])).
% 4.41/1.82  tff(c_973, plain, (v2_funct_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_953, c_57])).
% 4.41/1.82  tff(c_981, plain, $false, inference(negUnitSimplification, [status(thm)], [c_918, c_973])).
% 4.41/1.82  tff(c_982, plain, (~v2_funct_2('#skF_4', '#skF_1')), inference(splitRight, [status(thm)], [c_42])).
% 4.41/1.82  tff(c_985, plain, (![C_131, A_132, B_133]: (v1_relat_1(C_131) | ~m1_subset_1(C_131, k1_zfmisc_1(k2_zfmisc_1(A_132, B_133))))), inference(cnfTransformation, [status(thm)], [f_36])).
% 4.41/1.82  tff(c_996, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_46, c_985])).
% 4.41/1.82  tff(c_1012, plain, (![C_138, B_139, A_140]: (v5_relat_1(C_138, B_139) | ~m1_subset_1(C_138, k1_zfmisc_1(k2_zfmisc_1(A_140, B_139))))), inference(cnfTransformation, [status(thm)], [f_42])).
% 4.41/1.82  tff(c_1023, plain, (v5_relat_1('#skF_4', '#skF_1')), inference(resolution, [status(thm)], [c_46, c_1012])).
% 4.41/1.82  tff(c_1101, plain, (![A_151, B_152, D_153]: (r2_relset_1(A_151, B_152, D_153, D_153) | ~m1_subset_1(D_153, k1_zfmisc_1(k2_zfmisc_1(A_151, B_152))))), inference(cnfTransformation, [status(thm)], [f_61])).
% 4.41/1.82  tff(c_1108, plain, (![A_28]: (r2_relset_1(A_28, A_28, k6_partfun1(A_28), k6_partfun1(A_28)))), inference(resolution, [status(thm)], [c_32, c_1101])).
% 4.41/1.82  tff(c_1186, plain, (![A_155, B_156, C_157]: (k2_relset_1(A_155, B_156, C_157)=k2_relat_1(C_157) | ~m1_subset_1(C_157, k1_zfmisc_1(k2_zfmisc_1(A_155, B_156))))), inference(cnfTransformation, [status(thm)], [f_53])).
% 4.41/1.82  tff(c_1201, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_46, c_1186])).
% 4.41/1.82  tff(c_1221, plain, (![D_159, C_160, A_161, B_162]: (D_159=C_160 | ~r2_relset_1(A_161, B_162, C_160, D_159) | ~m1_subset_1(D_159, k1_zfmisc_1(k2_zfmisc_1(A_161, B_162))) | ~m1_subset_1(C_160, k1_zfmisc_1(k2_zfmisc_1(A_161, B_162))))), inference(cnfTransformation, [status(thm)], [f_61])).
% 4.41/1.82  tff(c_1229, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_44, c_1221])).
% 4.41/1.82  tff(c_1244, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_1229])).
% 4.41/1.82  tff(c_1666, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_1244])).
% 4.41/1.82  tff(c_1702, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_26, c_1666])).
% 4.41/1.82  tff(c_1706, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_56, c_52, c_50, c_46, c_1702])).
% 4.41/1.82  tff(c_1707, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_1244])).
% 4.41/1.82  tff(c_1921, plain, (![A_212, B_213, C_214, D_215]: (k2_relset_1(A_212, B_213, C_214)=B_213 | ~r2_relset_1(B_213, B_213, k1_partfun1(B_213, A_212, A_212, B_213, D_215, C_214), k6_partfun1(B_213)) | ~m1_subset_1(D_215, k1_zfmisc_1(k2_zfmisc_1(B_213, A_212))) | ~v1_funct_2(D_215, B_213, A_212) | ~v1_funct_1(D_215) | ~m1_subset_1(C_214, k1_zfmisc_1(k2_zfmisc_1(A_212, B_213))) | ~v1_funct_2(C_214, A_212, B_213) | ~v1_funct_1(C_214))), inference(cnfTransformation, [status(thm)], [f_104])).
% 4.41/1.82  tff(c_1924, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')='#skF_1' | ~r2_relset_1('#skF_1', '#skF_1', k6_partfun1('#skF_1'), k6_partfun1('#skF_1')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1707, c_1921])).
% 4.41/1.82  tff(c_1932, plain, (k2_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_46, c_56, c_54, c_52, c_1108, c_1201, c_1924])).
% 4.41/1.82  tff(c_22, plain, (![B_21]: (v2_funct_2(B_21, k2_relat_1(B_21)) | ~v5_relat_1(B_21, k2_relat_1(B_21)) | ~v1_relat_1(B_21))), inference(cnfTransformation, [status(thm)], [f_69])).
% 4.41/1.82  tff(c_1937, plain, (v2_funct_2('#skF_4', k2_relat_1('#skF_4')) | ~v5_relat_1('#skF_4', '#skF_1') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1932, c_22])).
% 4.41/1.82  tff(c_1941, plain, (v2_funct_2('#skF_4', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_996, c_1023, c_1932, c_1937])).
% 4.41/1.82  tff(c_1943, plain, $false, inference(negUnitSimplification, [status(thm)], [c_982, c_1941])).
% 4.41/1.82  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.41/1.82  
% 4.41/1.82  Inference rules
% 4.41/1.82  ----------------------
% 4.41/1.82  #Ref     : 0
% 4.41/1.82  #Sup     : 433
% 4.41/1.82  #Fact    : 0
% 4.41/1.82  #Define  : 0
% 4.41/1.82  #Split   : 14
% 4.41/1.82  #Chain   : 0
% 4.41/1.82  #Close   : 0
% 4.41/1.82  
% 4.41/1.82  Ordering : KBO
% 4.41/1.82  
% 4.41/1.82  Simplification rules
% 4.41/1.82  ----------------------
% 4.41/1.82  #Subsume      : 57
% 4.41/1.82  #Demod        : 451
% 4.41/1.82  #Tautology    : 194
% 4.41/1.82  #SimpNegUnit  : 4
% 4.41/1.82  #BackRed      : 48
% 4.41/1.82  
% 4.41/1.82  #Partial instantiations: 0
% 4.41/1.82  #Strategies tried      : 1
% 4.41/1.82  
% 4.41/1.82  Timing (in seconds)
% 4.41/1.82  ----------------------
% 4.41/1.83  Preprocessing        : 0.34
% 4.41/1.83  Parsing              : 0.18
% 4.41/1.83  CNF conversion       : 0.02
% 4.41/1.83  Main loop            : 0.60
% 4.41/1.83  Inferencing          : 0.22
% 4.41/1.83  Reduction            : 0.21
% 4.41/1.83  Demodulation         : 0.15
% 4.41/1.83  BG Simplification    : 0.03
% 4.41/1.83  Subsumption          : 0.10
% 4.41/1.83  Abstraction          : 0.03
% 4.41/1.83  MUC search           : 0.00
% 4.41/1.83  Cooper               : 0.00
% 4.41/1.83  Total                : 1.01
% 4.41/1.83  Index Insertion      : 0.00
% 4.41/1.83  Index Deletion       : 0.00
% 4.41/1.83  Index Matching       : 0.00
% 4.41/1.83  BG Taut test         : 0.00
%------------------------------------------------------------------------------
