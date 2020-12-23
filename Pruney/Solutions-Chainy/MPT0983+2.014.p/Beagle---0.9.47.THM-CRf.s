%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:12:02 EST 2020

% Result     : Theorem 4.80s
% Output     : CNFRefutation 5.14s
% Verified   : 
% Statistics : Number of formulae       :  107 ( 315 expanded)
%              Number of leaves         :   41 ( 133 expanded)
%              Depth                    :   11
%              Number of atoms          :  209 (1009 expanded)
%              Number of equality atoms :   31 ( 101 expanded)
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

tff(f_164,negated_conjecture,(
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

tff(f_56,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_48,axiom,(
    ! [A] :
      ( ( v1_xboole_0(A)
        & v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(A)
        & v1_funct_1(A)
        & v2_funct_1(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_funct_1)).

tff(f_105,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_52,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v2_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_funct_1)).

tff(f_103,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( v1_funct_1(k1_partfun1(A,B,C,D,E,F))
        & m1_subset_1(k1_partfun1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).

tff(f_83,axiom,(
    ! [A] : m1_subset_1(k6_relat_1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_relset_1)).

tff(f_81,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_144,axiom,(
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

tff(f_32,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_69,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(B,A)))
         => v1_xboole_0(C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc4_relset_1)).

tff(f_62,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_73,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_122,axiom,(
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

tff(f_91,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A) )
     => ( v2_funct_2(B,A)
      <=> k2_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_funct_2)).

tff(c_64,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_164])).

tff(c_123,plain,(
    ! [C_52,A_53,B_54] :
      ( v1_relat_1(C_52)
      | ~ m1_subset_1(C_52,k1_zfmisc_1(k2_zfmisc_1(A_53,B_54))) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_139,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_64,c_123])).

tff(c_68,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_164])).

tff(c_158,plain,(
    ! [A_58] :
      ( v2_funct_1(A_58)
      | ~ v1_funct_1(A_58)
      | ~ v1_relat_1(A_58)
      | ~ v1_xboole_0(A_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_54,plain,
    ( ~ v2_funct_2('#skF_4','#skF_1')
    | ~ v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_164])).

tff(c_112,plain,(
    ~ v2_funct_1('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_54])).

tff(c_161,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3')
    | ~ v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_158,c_112])).

tff(c_164,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_139,c_68,c_161])).

tff(c_66,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_164])).

tff(c_62,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_164])).

tff(c_60,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_164])).

tff(c_58,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_164])).

tff(c_46,plain,(
    ! [A_32] : k6_relat_1(A_32) = k6_partfun1(A_32) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_20,plain,(
    ! [A_5] : v2_funct_1(k6_relat_1(A_5)) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_70,plain,(
    ! [A_5] : v2_funct_1(k6_partfun1(A_5)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_20])).

tff(c_42,plain,(
    ! [B_27,D_29,A_26,E_30,F_31,C_28] :
      ( m1_subset_1(k1_partfun1(A_26,B_27,C_28,D_29,E_30,F_31),k1_zfmisc_1(k2_zfmisc_1(A_26,D_29)))
      | ~ m1_subset_1(F_31,k1_zfmisc_1(k2_zfmisc_1(C_28,D_29)))
      | ~ v1_funct_1(F_31)
      | ~ m1_subset_1(E_30,k1_zfmisc_1(k2_zfmisc_1(A_26,B_27)))
      | ~ v1_funct_1(E_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_36,plain,(
    ! [A_23] : m1_subset_1(k6_relat_1(A_23),k1_zfmisc_1(k2_zfmisc_1(A_23,A_23))) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_69,plain,(
    ! [A_23] : m1_subset_1(k6_partfun1(A_23),k1_zfmisc_1(k2_zfmisc_1(A_23,A_23))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_36])).

tff(c_56,plain,(
    r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k6_partfun1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_164])).

tff(c_1375,plain,(
    ! [D_270,C_271,A_272,B_273] :
      ( D_270 = C_271
      | ~ r2_relset_1(A_272,B_273,C_271,D_270)
      | ~ m1_subset_1(D_270,k1_zfmisc_1(k2_zfmisc_1(A_272,B_273)))
      | ~ m1_subset_1(C_271,k1_zfmisc_1(k2_zfmisc_1(A_272,B_273))) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_1383,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_56,c_1375])).

tff(c_1398,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_69,c_1383])).

tff(c_1639,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_1398])).

tff(c_1642,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_42,c_1639])).

tff(c_1646,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_64,c_62,c_58,c_1642])).

tff(c_1647,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_1398])).

tff(c_52,plain,(
    ! [D_41,E_43,B_39,A_38,C_40] :
      ( k1_xboole_0 = C_40
      | v2_funct_1(D_41)
      | ~ v2_funct_1(k1_partfun1(A_38,B_39,B_39,C_40,D_41,E_43))
      | ~ m1_subset_1(E_43,k1_zfmisc_1(k2_zfmisc_1(B_39,C_40)))
      | ~ v1_funct_2(E_43,B_39,C_40)
      | ~ v1_funct_1(E_43)
      | ~ m1_subset_1(D_41,k1_zfmisc_1(k2_zfmisc_1(A_38,B_39)))
      | ~ v1_funct_2(D_41,A_38,B_39)
      | ~ v1_funct_1(D_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_1659,plain,
    ( k1_xboole_0 = '#skF_1'
    | v2_funct_1('#skF_3')
    | ~ v2_funct_1(k6_partfun1('#skF_1'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1647,c_52])).

tff(c_1666,plain,
    ( k1_xboole_0 = '#skF_1'
    | v2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_64,c_62,c_60,c_58,c_70,c_1659])).

tff(c_1667,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_112,c_1666])).

tff(c_8,plain,(
    ! [B_2] : k2_zfmisc_1(k1_xboole_0,B_2) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_1705,plain,(
    ! [B_2] : k2_zfmisc_1('#skF_1',B_2) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1667,c_1667,c_8])).

tff(c_1720,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1705,c_64])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_6,plain,(
    ! [A_1] : k2_zfmisc_1(A_1,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_210,plain,(
    ! [C_70,B_71,A_72] :
      ( v1_xboole_0(C_70)
      | ~ m1_subset_1(C_70,k1_zfmisc_1(k2_zfmisc_1(B_71,A_72)))
      | ~ v1_xboole_0(A_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_222,plain,(
    ! [C_70] :
      ( v1_xboole_0(C_70)
      | ~ m1_subset_1(C_70,k1_zfmisc_1(k1_xboole_0))
      | ~ v1_xboole_0(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_210])).

tff(c_232,plain,(
    ! [C_70] :
      ( v1_xboole_0(C_70)
      | ~ m1_subset_1(C_70,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_222])).

tff(c_1869,plain,(
    ! [C_352] :
      ( v1_xboole_0(C_352)
      | ~ m1_subset_1(C_352,k1_zfmisc_1('#skF_1')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1667,c_232])).

tff(c_1875,plain,(
    v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_1720,c_1869])).

tff(c_1884,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_164,c_1875])).

tff(c_1885,plain,(
    ~ v2_funct_2('#skF_4','#skF_1') ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_1897,plain,(
    ! [C_354,A_355,B_356] :
      ( v1_relat_1(C_354)
      | ~ m1_subset_1(C_354,k1_zfmisc_1(k2_zfmisc_1(A_355,B_356))) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_1913,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_58,c_1897])).

tff(c_1933,plain,(
    ! [C_361,B_362,A_363] :
      ( v5_relat_1(C_361,B_362)
      | ~ m1_subset_1(C_361,k1_zfmisc_1(k2_zfmisc_1(A_363,B_362))) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_1950,plain,(
    v5_relat_1('#skF_4','#skF_1') ),
    inference(resolution,[status(thm)],[c_58,c_1933])).

tff(c_2018,plain,(
    ! [A_377,B_378,D_379] :
      ( r2_relset_1(A_377,B_378,D_379,D_379)
      | ~ m1_subset_1(D_379,k1_zfmisc_1(k2_zfmisc_1(A_377,B_378))) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_2029,plain,(
    ! [A_23] : r2_relset_1(A_23,A_23,k6_partfun1(A_23),k6_partfun1(A_23)) ),
    inference(resolution,[status(thm)],[c_69,c_2018])).

tff(c_2070,plain,(
    ! [A_385,B_386,C_387] :
      ( k2_relset_1(A_385,B_386,C_387) = k2_relat_1(C_387)
      | ~ m1_subset_1(C_387,k1_zfmisc_1(k2_zfmisc_1(A_385,B_386))) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_2087,plain,(
    k2_relset_1('#skF_2','#skF_1','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_58,c_2070])).

tff(c_2263,plain,(
    ! [D_421,F_424,C_425,B_422,E_426,A_423] :
      ( m1_subset_1(k1_partfun1(A_423,B_422,C_425,D_421,E_426,F_424),k1_zfmisc_1(k2_zfmisc_1(A_423,D_421)))
      | ~ m1_subset_1(F_424,k1_zfmisc_1(k2_zfmisc_1(C_425,D_421)))
      | ~ v1_funct_1(F_424)
      | ~ m1_subset_1(E_426,k1_zfmisc_1(k2_zfmisc_1(A_423,B_422)))
      | ~ v1_funct_1(E_426) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_2108,plain,(
    ! [D_392,C_393,A_394,B_395] :
      ( D_392 = C_393
      | ~ r2_relset_1(A_394,B_395,C_393,D_392)
      | ~ m1_subset_1(D_392,k1_zfmisc_1(k2_zfmisc_1(A_394,B_395)))
      | ~ m1_subset_1(C_393,k1_zfmisc_1(k2_zfmisc_1(A_394,B_395))) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_2116,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_56,c_2108])).

tff(c_2131,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_69,c_2116])).

tff(c_2142,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_2131])).

tff(c_2266,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_2263,c_2142])).

tff(c_2298,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_64,c_62,c_58,c_2266])).

tff(c_2299,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_2131])).

tff(c_2650,plain,(
    ! [A_531,B_532,C_533,D_534] :
      ( k2_relset_1(A_531,B_532,C_533) = B_532
      | ~ r2_relset_1(B_532,B_532,k1_partfun1(B_532,A_531,A_531,B_532,D_534,C_533),k6_partfun1(B_532))
      | ~ m1_subset_1(D_534,k1_zfmisc_1(k2_zfmisc_1(B_532,A_531)))
      | ~ v1_funct_2(D_534,B_532,A_531)
      | ~ v1_funct_1(D_534)
      | ~ m1_subset_1(C_533,k1_zfmisc_1(k2_zfmisc_1(A_531,B_532)))
      | ~ v1_funct_2(C_533,A_531,B_532)
      | ~ v1_funct_1(C_533) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_2653,plain,
    ( k2_relset_1('#skF_2','#skF_1','#skF_4') = '#skF_1'
    | ~ r2_relset_1('#skF_1','#skF_1',k6_partfun1('#skF_1'),k6_partfun1('#skF_1'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_2299,c_2650])).

tff(c_2655,plain,(
    k2_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_58,c_68,c_66,c_64,c_2029,c_2087,c_2653])).

tff(c_38,plain,(
    ! [B_25] :
      ( v2_funct_2(B_25,k2_relat_1(B_25))
      | ~ v5_relat_1(B_25,k2_relat_1(B_25))
      | ~ v1_relat_1(B_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_2660,plain,
    ( v2_funct_2('#skF_4',k2_relat_1('#skF_4'))
    | ~ v5_relat_1('#skF_4','#skF_1')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_2655,c_38])).

tff(c_2664,plain,(
    v2_funct_2('#skF_4','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1913,c_1950,c_2655,c_2660])).

tff(c_2666,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1885,c_2664])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n014.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 17:34:52 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.80/1.89  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.80/1.90  
% 4.80/1.90  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.80/1.90  %$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 4.80/1.90  
% 4.80/1.90  %Foreground sorts:
% 4.80/1.90  
% 4.80/1.90  
% 4.80/1.90  %Background operators:
% 4.80/1.90  
% 4.80/1.90  
% 4.80/1.90  %Foreground operators:
% 4.80/1.90  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 4.80/1.90  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.80/1.90  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 4.80/1.90  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.80/1.90  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 4.80/1.90  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.80/1.90  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 4.80/1.90  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 4.80/1.90  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.80/1.90  tff('#skF_2', type, '#skF_2': $i).
% 4.80/1.90  tff('#skF_3', type, '#skF_3': $i).
% 4.80/1.90  tff('#skF_1', type, '#skF_1': $i).
% 4.80/1.90  tff(v2_funct_2, type, v2_funct_2: ($i * $i) > $o).
% 4.80/1.90  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 4.80/1.90  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.80/1.90  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 4.80/1.90  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.80/1.90  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.80/1.90  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.80/1.90  tff('#skF_4', type, '#skF_4': $i).
% 4.80/1.90  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 4.80/1.90  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.80/1.90  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 4.80/1.90  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.80/1.90  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.80/1.90  
% 5.14/1.92  tff(f_164, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (r2_relset_1(A, A, k1_partfun1(A, B, B, A, C, D), k6_partfun1(A)) => (v2_funct_1(C) & v2_funct_2(D, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_funct_2)).
% 5.14/1.92  tff(f_56, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 5.14/1.92  tff(f_48, axiom, (![A]: (((v1_xboole_0(A) & v1_relat_1(A)) & v1_funct_1(A)) => ((v1_relat_1(A) & v1_funct_1(A)) & v2_funct_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_funct_1)).
% 5.14/1.92  tff(f_105, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 5.14/1.92  tff(f_52, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v2_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc4_funct_1)).
% 5.14/1.92  tff(f_103, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (v1_funct_1(k1_partfun1(A, B, C, D, E, F)) & m1_subset_1(k1_partfun1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 5.14/1.92  tff(f_83, axiom, (![A]: m1_subset_1(k6_relat_1(A), k1_zfmisc_1(k2_zfmisc_1(A, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_relset_1)).
% 5.14/1.92  tff(f_81, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 5.14/1.92  tff(f_144, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, B, C)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (v2_funct_1(k1_partfun1(A, B, B, C, D, E)) => (((C = k1_xboole_0) & ~(B = k1_xboole_0)) | v2_funct_1(D))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t26_funct_2)).
% 5.14/1.92  tff(f_32, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 5.14/1.92  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 5.14/1.92  tff(f_69, axiom, (![A, B]: (v1_xboole_0(A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => v1_xboole_0(C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc4_relset_1)).
% 5.14/1.92  tff(f_62, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 5.14/1.92  tff(f_73, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 5.14/1.92  tff(f_122, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (r2_relset_1(B, B, k1_partfun1(B, A, A, B, D, C), k6_partfun1(B)) => (k2_relset_1(A, B, C) = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t24_funct_2)).
% 5.14/1.92  tff(f_91, axiom, (![A, B]: ((v1_relat_1(B) & v5_relat_1(B, A)) => (v2_funct_2(B, A) <=> (k2_relat_1(B) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_funct_2)).
% 5.14/1.92  tff(c_64, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_164])).
% 5.14/1.92  tff(c_123, plain, (![C_52, A_53, B_54]: (v1_relat_1(C_52) | ~m1_subset_1(C_52, k1_zfmisc_1(k2_zfmisc_1(A_53, B_54))))), inference(cnfTransformation, [status(thm)], [f_56])).
% 5.14/1.92  tff(c_139, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_64, c_123])).
% 5.14/1.92  tff(c_68, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_164])).
% 5.14/1.92  tff(c_158, plain, (![A_58]: (v2_funct_1(A_58) | ~v1_funct_1(A_58) | ~v1_relat_1(A_58) | ~v1_xboole_0(A_58))), inference(cnfTransformation, [status(thm)], [f_48])).
% 5.14/1.92  tff(c_54, plain, (~v2_funct_2('#skF_4', '#skF_1') | ~v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_164])).
% 5.14/1.92  tff(c_112, plain, (~v2_funct_1('#skF_3')), inference(splitLeft, [status(thm)], [c_54])).
% 5.14/1.92  tff(c_161, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3') | ~v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_158, c_112])).
% 5.14/1.92  tff(c_164, plain, (~v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_139, c_68, c_161])).
% 5.14/1.92  tff(c_66, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_164])).
% 5.14/1.92  tff(c_62, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_164])).
% 5.14/1.92  tff(c_60, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_164])).
% 5.14/1.92  tff(c_58, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_164])).
% 5.14/1.92  tff(c_46, plain, (![A_32]: (k6_relat_1(A_32)=k6_partfun1(A_32))), inference(cnfTransformation, [status(thm)], [f_105])).
% 5.14/1.92  tff(c_20, plain, (![A_5]: (v2_funct_1(k6_relat_1(A_5)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 5.14/1.92  tff(c_70, plain, (![A_5]: (v2_funct_1(k6_partfun1(A_5)))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_20])).
% 5.14/1.92  tff(c_42, plain, (![B_27, D_29, A_26, E_30, F_31, C_28]: (m1_subset_1(k1_partfun1(A_26, B_27, C_28, D_29, E_30, F_31), k1_zfmisc_1(k2_zfmisc_1(A_26, D_29))) | ~m1_subset_1(F_31, k1_zfmisc_1(k2_zfmisc_1(C_28, D_29))) | ~v1_funct_1(F_31) | ~m1_subset_1(E_30, k1_zfmisc_1(k2_zfmisc_1(A_26, B_27))) | ~v1_funct_1(E_30))), inference(cnfTransformation, [status(thm)], [f_103])).
% 5.14/1.92  tff(c_36, plain, (![A_23]: (m1_subset_1(k6_relat_1(A_23), k1_zfmisc_1(k2_zfmisc_1(A_23, A_23))))), inference(cnfTransformation, [status(thm)], [f_83])).
% 5.14/1.92  tff(c_69, plain, (![A_23]: (m1_subset_1(k6_partfun1(A_23), k1_zfmisc_1(k2_zfmisc_1(A_23, A_23))))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_36])).
% 5.14/1.92  tff(c_56, plain, (r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k6_partfun1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_164])).
% 5.14/1.92  tff(c_1375, plain, (![D_270, C_271, A_272, B_273]: (D_270=C_271 | ~r2_relset_1(A_272, B_273, C_271, D_270) | ~m1_subset_1(D_270, k1_zfmisc_1(k2_zfmisc_1(A_272, B_273))) | ~m1_subset_1(C_271, k1_zfmisc_1(k2_zfmisc_1(A_272, B_273))))), inference(cnfTransformation, [status(thm)], [f_81])).
% 5.14/1.92  tff(c_1383, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_56, c_1375])).
% 5.14/1.92  tff(c_1398, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_69, c_1383])).
% 5.14/1.92  tff(c_1639, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_1398])).
% 5.14/1.92  tff(c_1642, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_42, c_1639])).
% 5.14/1.92  tff(c_1646, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_68, c_64, c_62, c_58, c_1642])).
% 5.14/1.92  tff(c_1647, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_1398])).
% 5.14/1.92  tff(c_52, plain, (![D_41, E_43, B_39, A_38, C_40]: (k1_xboole_0=C_40 | v2_funct_1(D_41) | ~v2_funct_1(k1_partfun1(A_38, B_39, B_39, C_40, D_41, E_43)) | ~m1_subset_1(E_43, k1_zfmisc_1(k2_zfmisc_1(B_39, C_40))) | ~v1_funct_2(E_43, B_39, C_40) | ~v1_funct_1(E_43) | ~m1_subset_1(D_41, k1_zfmisc_1(k2_zfmisc_1(A_38, B_39))) | ~v1_funct_2(D_41, A_38, B_39) | ~v1_funct_1(D_41))), inference(cnfTransformation, [status(thm)], [f_144])).
% 5.14/1.92  tff(c_1659, plain, (k1_xboole_0='#skF_1' | v2_funct_1('#skF_3') | ~v2_funct_1(k6_partfun1('#skF_1')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1647, c_52])).
% 5.14/1.92  tff(c_1666, plain, (k1_xboole_0='#skF_1' | v2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_66, c_64, c_62, c_60, c_58, c_70, c_1659])).
% 5.14/1.92  tff(c_1667, plain, (k1_xboole_0='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_112, c_1666])).
% 5.14/1.92  tff(c_8, plain, (![B_2]: (k2_zfmisc_1(k1_xboole_0, B_2)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.14/1.92  tff(c_1705, plain, (![B_2]: (k2_zfmisc_1('#skF_1', B_2)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1667, c_1667, c_8])).
% 5.14/1.92  tff(c_1720, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_1705, c_64])).
% 5.14/1.92  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 5.14/1.92  tff(c_6, plain, (![A_1]: (k2_zfmisc_1(A_1, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.14/1.92  tff(c_210, plain, (![C_70, B_71, A_72]: (v1_xboole_0(C_70) | ~m1_subset_1(C_70, k1_zfmisc_1(k2_zfmisc_1(B_71, A_72))) | ~v1_xboole_0(A_72))), inference(cnfTransformation, [status(thm)], [f_69])).
% 5.14/1.92  tff(c_222, plain, (![C_70]: (v1_xboole_0(C_70) | ~m1_subset_1(C_70, k1_zfmisc_1(k1_xboole_0)) | ~v1_xboole_0(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_6, c_210])).
% 5.14/1.92  tff(c_232, plain, (![C_70]: (v1_xboole_0(C_70) | ~m1_subset_1(C_70, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_222])).
% 5.14/1.92  tff(c_1869, plain, (![C_352]: (v1_xboole_0(C_352) | ~m1_subset_1(C_352, k1_zfmisc_1('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_1667, c_232])).
% 5.14/1.92  tff(c_1875, plain, (v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_1720, c_1869])).
% 5.14/1.92  tff(c_1884, plain, $false, inference(negUnitSimplification, [status(thm)], [c_164, c_1875])).
% 5.14/1.92  tff(c_1885, plain, (~v2_funct_2('#skF_4', '#skF_1')), inference(splitRight, [status(thm)], [c_54])).
% 5.14/1.92  tff(c_1897, plain, (![C_354, A_355, B_356]: (v1_relat_1(C_354) | ~m1_subset_1(C_354, k1_zfmisc_1(k2_zfmisc_1(A_355, B_356))))), inference(cnfTransformation, [status(thm)], [f_56])).
% 5.14/1.92  tff(c_1913, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_58, c_1897])).
% 5.14/1.92  tff(c_1933, plain, (![C_361, B_362, A_363]: (v5_relat_1(C_361, B_362) | ~m1_subset_1(C_361, k1_zfmisc_1(k2_zfmisc_1(A_363, B_362))))), inference(cnfTransformation, [status(thm)], [f_62])).
% 5.14/1.92  tff(c_1950, plain, (v5_relat_1('#skF_4', '#skF_1')), inference(resolution, [status(thm)], [c_58, c_1933])).
% 5.14/1.92  tff(c_2018, plain, (![A_377, B_378, D_379]: (r2_relset_1(A_377, B_378, D_379, D_379) | ~m1_subset_1(D_379, k1_zfmisc_1(k2_zfmisc_1(A_377, B_378))))), inference(cnfTransformation, [status(thm)], [f_81])).
% 5.14/1.92  tff(c_2029, plain, (![A_23]: (r2_relset_1(A_23, A_23, k6_partfun1(A_23), k6_partfun1(A_23)))), inference(resolution, [status(thm)], [c_69, c_2018])).
% 5.14/1.92  tff(c_2070, plain, (![A_385, B_386, C_387]: (k2_relset_1(A_385, B_386, C_387)=k2_relat_1(C_387) | ~m1_subset_1(C_387, k1_zfmisc_1(k2_zfmisc_1(A_385, B_386))))), inference(cnfTransformation, [status(thm)], [f_73])).
% 5.14/1.92  tff(c_2087, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_58, c_2070])).
% 5.14/1.92  tff(c_2263, plain, (![D_421, F_424, C_425, B_422, E_426, A_423]: (m1_subset_1(k1_partfun1(A_423, B_422, C_425, D_421, E_426, F_424), k1_zfmisc_1(k2_zfmisc_1(A_423, D_421))) | ~m1_subset_1(F_424, k1_zfmisc_1(k2_zfmisc_1(C_425, D_421))) | ~v1_funct_1(F_424) | ~m1_subset_1(E_426, k1_zfmisc_1(k2_zfmisc_1(A_423, B_422))) | ~v1_funct_1(E_426))), inference(cnfTransformation, [status(thm)], [f_103])).
% 5.14/1.92  tff(c_2108, plain, (![D_392, C_393, A_394, B_395]: (D_392=C_393 | ~r2_relset_1(A_394, B_395, C_393, D_392) | ~m1_subset_1(D_392, k1_zfmisc_1(k2_zfmisc_1(A_394, B_395))) | ~m1_subset_1(C_393, k1_zfmisc_1(k2_zfmisc_1(A_394, B_395))))), inference(cnfTransformation, [status(thm)], [f_81])).
% 5.14/1.92  tff(c_2116, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_56, c_2108])).
% 5.14/1.92  tff(c_2131, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_69, c_2116])).
% 5.14/1.92  tff(c_2142, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_2131])).
% 5.14/1.92  tff(c_2266, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_2263, c_2142])).
% 5.14/1.92  tff(c_2298, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_68, c_64, c_62, c_58, c_2266])).
% 5.14/1.92  tff(c_2299, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_2131])).
% 5.14/1.92  tff(c_2650, plain, (![A_531, B_532, C_533, D_534]: (k2_relset_1(A_531, B_532, C_533)=B_532 | ~r2_relset_1(B_532, B_532, k1_partfun1(B_532, A_531, A_531, B_532, D_534, C_533), k6_partfun1(B_532)) | ~m1_subset_1(D_534, k1_zfmisc_1(k2_zfmisc_1(B_532, A_531))) | ~v1_funct_2(D_534, B_532, A_531) | ~v1_funct_1(D_534) | ~m1_subset_1(C_533, k1_zfmisc_1(k2_zfmisc_1(A_531, B_532))) | ~v1_funct_2(C_533, A_531, B_532) | ~v1_funct_1(C_533))), inference(cnfTransformation, [status(thm)], [f_122])).
% 5.14/1.92  tff(c_2653, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')='#skF_1' | ~r2_relset_1('#skF_1', '#skF_1', k6_partfun1('#skF_1'), k6_partfun1('#skF_1')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_2299, c_2650])).
% 5.14/1.92  tff(c_2655, plain, (k2_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_58, c_68, c_66, c_64, c_2029, c_2087, c_2653])).
% 5.14/1.92  tff(c_38, plain, (![B_25]: (v2_funct_2(B_25, k2_relat_1(B_25)) | ~v5_relat_1(B_25, k2_relat_1(B_25)) | ~v1_relat_1(B_25))), inference(cnfTransformation, [status(thm)], [f_91])).
% 5.14/1.92  tff(c_2660, plain, (v2_funct_2('#skF_4', k2_relat_1('#skF_4')) | ~v5_relat_1('#skF_4', '#skF_1') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_2655, c_38])).
% 5.14/1.92  tff(c_2664, plain, (v2_funct_2('#skF_4', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1913, c_1950, c_2655, c_2660])).
% 5.14/1.92  tff(c_2666, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1885, c_2664])).
% 5.14/1.92  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.14/1.92  
% 5.14/1.92  Inference rules
% 5.14/1.92  ----------------------
% 5.14/1.92  #Ref     : 0
% 5.14/1.92  #Sup     : 570
% 5.14/1.92  #Fact    : 0
% 5.14/1.92  #Define  : 0
% 5.14/1.92  #Split   : 14
% 5.14/1.92  #Chain   : 0
% 5.14/1.92  #Close   : 0
% 5.14/1.92  
% 5.14/1.92  Ordering : KBO
% 5.14/1.92  
% 5.14/1.92  Simplification rules
% 5.14/1.92  ----------------------
% 5.14/1.92  #Subsume      : 12
% 5.14/1.92  #Demod        : 502
% 5.14/1.92  #Tautology    : 180
% 5.14/1.92  #SimpNegUnit  : 8
% 5.14/1.92  #BackRed      : 119
% 5.14/1.92  
% 5.14/1.92  #Partial instantiations: 0
% 5.14/1.92  #Strategies tried      : 1
% 5.14/1.92  
% 5.14/1.92  Timing (in seconds)
% 5.14/1.92  ----------------------
% 5.14/1.92  Preprocessing        : 0.34
% 5.14/1.92  Parsing              : 0.18
% 5.14/1.92  CNF conversion       : 0.02
% 5.14/1.92  Main loop            : 0.80
% 5.14/1.92  Inferencing          : 0.30
% 5.14/1.92  Reduction            : 0.27
% 5.14/1.92  Demodulation         : 0.20
% 5.14/1.92  BG Simplification    : 0.03
% 5.14/1.92  Subsumption          : 0.13
% 5.14/1.92  Abstraction          : 0.03
% 5.14/1.92  MUC search           : 0.00
% 5.14/1.92  Cooper               : 0.00
% 5.14/1.92  Total                : 1.18
% 5.14/1.92  Index Insertion      : 0.00
% 5.14/1.92  Index Deletion       : 0.00
% 5.14/1.92  Index Matching       : 0.00
% 5.14/1.92  BG Taut test         : 0.00
%------------------------------------------------------------------------------
