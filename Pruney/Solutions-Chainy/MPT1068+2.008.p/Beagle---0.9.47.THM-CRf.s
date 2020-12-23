%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:17:41 EST 2020

% Result     : Theorem 48.55s
% Output     : CNFRefutation 48.76s
% Verified   : 
% Statistics : Number of formulae       :  404 (4805 expanded)
%              Number of leaves         :   45 (1565 expanded)
%              Depth                    :   21
%              Number of atoms          :  947 (17007 expanded)
%              Number of equality atoms :  230 (5753 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k8_funct_2 > k2_relset_1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > o_1_1_funct_2 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(o_1_1_funct_2,type,(
    o_1_1_funct_2: $i > $i )).

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

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

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

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

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

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_163,negated_conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t185_funct_2)).

tff(f_128,axiom,(
    ! [A] : m1_subset_1(o_1_1_funct_2(A),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_o_1_1_funct_2)).

tff(f_81,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_91,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_126,axiom,(
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

tff(f_43,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(f_72,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ! [C] :
          ( ( v1_relat_1(C)
            & v1_funct_1(C) )
         => ( r2_hidden(A,k1_relat_1(B))
           => k1_funct_1(k5_relat_1(B,C),A) = k1_funct_1(C,k1_funct_1(B,A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_funct_1)).

tff(f_29,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_37,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_138,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_87,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_108,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d12_funct_2)).

tff(f_77,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

tff(c_68,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_46,plain,(
    ! [A_39] : m1_subset_1(o_1_1_funct_2(A_39),A_39) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_56,plain,(
    m1_subset_1('#skF_6','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_58,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_101,plain,(
    ! [C_69,A_70,B_71] :
      ( v1_relat_1(C_69)
      | ~ m1_subset_1(C_69,k1_zfmisc_1(k2_zfmisc_1(A_70,B_71))) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_122,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_58,c_101])).

tff(c_60,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_52,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_64,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_62,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_456,plain,(
    ! [A_123,B_124,C_125] :
      ( k1_relset_1(A_123,B_124,C_125) = k1_relat_1(C_125)
      | ~ m1_subset_1(C_125,k1_zfmisc_1(k2_zfmisc_1(A_123,B_124))) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_476,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_62,c_456])).

tff(c_4677,plain,(
    ! [B_394,A_395,C_396] :
      ( k1_xboole_0 = B_394
      | k1_relset_1(A_395,B_394,C_396) = A_395
      | ~ v1_funct_2(C_396,A_395,B_394)
      | ~ m1_subset_1(C_396,k1_zfmisc_1(k2_zfmisc_1(A_395,B_394))) ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_4684,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relset_1('#skF_2','#skF_3','#skF_4') = '#skF_2'
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_62,c_4677])).

tff(c_4699,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relat_1('#skF_4') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_476,c_4684])).

tff(c_4705,plain,(
    k1_relat_1('#skF_4') = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_4699])).

tff(c_121,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_62,c_101])).

tff(c_66,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_8,plain,(
    ! [A_6,B_7] :
      ( r2_hidden(A_6,B_7)
      | v1_xboole_0(B_7)
      | ~ m1_subset_1(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_238386,plain,(
    ! [B_7647,C_7648,A_7649] :
      ( k1_funct_1(k5_relat_1(B_7647,C_7648),A_7649) = k1_funct_1(C_7648,k1_funct_1(B_7647,A_7649))
      | ~ r2_hidden(A_7649,k1_relat_1(B_7647))
      | ~ v1_funct_1(C_7648)
      | ~ v1_relat_1(C_7648)
      | ~ v1_funct_1(B_7647)
      | ~ v1_relat_1(B_7647) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_241582,plain,(
    ! [B_7821,C_7822,A_7823] :
      ( k1_funct_1(k5_relat_1(B_7821,C_7822),A_7823) = k1_funct_1(C_7822,k1_funct_1(B_7821,A_7823))
      | ~ v1_funct_1(C_7822)
      | ~ v1_relat_1(C_7822)
      | ~ v1_funct_1(B_7821)
      | ~ v1_relat_1(B_7821)
      | v1_xboole_0(k1_relat_1(B_7821))
      | ~ m1_subset_1(A_7823,k1_relat_1(B_7821)) ) ),
    inference(resolution,[status(thm)],[c_8,c_238386])).

tff(c_241586,plain,(
    ! [C_7822,A_7823] :
      ( k1_funct_1(k5_relat_1('#skF_4',C_7822),A_7823) = k1_funct_1(C_7822,k1_funct_1('#skF_4',A_7823))
      | ~ v1_funct_1(C_7822)
      | ~ v1_relat_1(C_7822)
      | ~ v1_funct_1('#skF_4')
      | ~ v1_relat_1('#skF_4')
      | v1_xboole_0(k1_relat_1('#skF_4'))
      | ~ m1_subset_1(A_7823,'#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4705,c_241582])).

tff(c_241596,plain,(
    ! [C_7822,A_7823] :
      ( k1_funct_1(k5_relat_1('#skF_4',C_7822),A_7823) = k1_funct_1(C_7822,k1_funct_1('#skF_4',A_7823))
      | ~ v1_funct_1(C_7822)
      | ~ v1_relat_1(C_7822)
      | v1_xboole_0('#skF_2')
      | ~ m1_subset_1(A_7823,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4705,c_121,c_66,c_241586])).

tff(c_248356,plain,(
    v1_xboole_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_241596])).

tff(c_2,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_248359,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_248356,c_2])).

tff(c_248363,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_248359])).

tff(c_248364,plain,(
    ! [C_7822,A_7823] :
      ( k1_funct_1(k5_relat_1('#skF_4',C_7822),A_7823) = k1_funct_1(C_7822,k1_funct_1('#skF_4',A_7823))
      | ~ v1_funct_1(C_7822)
      | ~ v1_relat_1(C_7822)
      | ~ m1_subset_1(A_7823,'#skF_2') ) ),
    inference(splitRight,[status(thm)],[c_241596])).

tff(c_4825,plain,(
    ! [B_403,C_404,A_405] :
      ( k1_funct_1(k5_relat_1(B_403,C_404),A_405) = k1_funct_1(C_404,k1_funct_1(B_403,A_405))
      | ~ r2_hidden(A_405,k1_relat_1(B_403))
      | ~ v1_funct_1(C_404)
      | ~ v1_relat_1(C_404)
      | ~ v1_funct_1(B_403)
      | ~ v1_relat_1(B_403) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_110749,plain,(
    ! [B_3974,C_3975,A_3976] :
      ( k1_funct_1(k5_relat_1(B_3974,C_3975),A_3976) = k1_funct_1(C_3975,k1_funct_1(B_3974,A_3976))
      | ~ v1_funct_1(C_3975)
      | ~ v1_relat_1(C_3975)
      | ~ v1_funct_1(B_3974)
      | ~ v1_relat_1(B_3974)
      | v1_xboole_0(k1_relat_1(B_3974))
      | ~ m1_subset_1(A_3976,k1_relat_1(B_3974)) ) ),
    inference(resolution,[status(thm)],[c_8,c_4825])).

tff(c_110751,plain,(
    ! [C_3975,A_3976] :
      ( k1_funct_1(k5_relat_1('#skF_4',C_3975),A_3976) = k1_funct_1(C_3975,k1_funct_1('#skF_4',A_3976))
      | ~ v1_funct_1(C_3975)
      | ~ v1_relat_1(C_3975)
      | ~ v1_funct_1('#skF_4')
      | ~ v1_relat_1('#skF_4')
      | v1_xboole_0(k1_relat_1('#skF_4'))
      | ~ m1_subset_1(A_3976,'#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4705,c_110749])).

tff(c_110758,plain,(
    ! [C_3975,A_3976] :
      ( k1_funct_1(k5_relat_1('#skF_4',C_3975),A_3976) = k1_funct_1(C_3975,k1_funct_1('#skF_4',A_3976))
      | ~ v1_funct_1(C_3975)
      | ~ v1_relat_1(C_3975)
      | v1_xboole_0('#skF_2')
      | ~ m1_subset_1(A_3976,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4705,c_121,c_66,c_110751])).

tff(c_119301,plain,(
    v1_xboole_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_110758])).

tff(c_119304,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_119301,c_2])).

tff(c_119308,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_119304])).

tff(c_119309,plain,(
    ! [C_3975,A_3976] :
      ( k1_funct_1(k5_relat_1('#skF_4',C_3975),A_3976) = k1_funct_1(C_3975,k1_funct_1('#skF_4',A_3976))
      | ~ v1_funct_1(C_3975)
      | ~ v1_relat_1(C_3975)
      | ~ m1_subset_1(A_3976,'#skF_2') ) ),
    inference(splitRight,[status(thm)],[c_110758])).

tff(c_6,plain,(
    ! [A_5] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_5)) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_76,plain,(
    ! [A_63,B_64] :
      ( r1_tarski(A_63,B_64)
      | ~ m1_subset_1(A_63,k1_zfmisc_1(B_64)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_93,plain,(
    ! [A_5] : r1_tarski(k1_xboole_0,A_5) ),
    inference(resolution,[status(thm)],[c_6,c_76])).

tff(c_86936,plain,(
    ! [B_3141,C_3142,A_3143] :
      ( k1_funct_1(k5_relat_1(B_3141,C_3142),A_3143) = k1_funct_1(C_3142,k1_funct_1(B_3141,A_3143))
      | ~ v1_funct_1(C_3142)
      | ~ v1_relat_1(C_3142)
      | ~ v1_funct_1(B_3141)
      | ~ v1_relat_1(B_3141)
      | v1_xboole_0(k1_relat_1(B_3141))
      | ~ m1_subset_1(A_3143,k1_relat_1(B_3141)) ) ),
    inference(resolution,[status(thm)],[c_8,c_4825])).

tff(c_86940,plain,(
    ! [C_3142,A_3143] :
      ( k1_funct_1(k5_relat_1('#skF_4',C_3142),A_3143) = k1_funct_1(C_3142,k1_funct_1('#skF_4',A_3143))
      | ~ v1_funct_1(C_3142)
      | ~ v1_relat_1(C_3142)
      | ~ v1_funct_1('#skF_4')
      | ~ v1_relat_1('#skF_4')
      | v1_xboole_0(k1_relat_1('#skF_4'))
      | ~ m1_subset_1(A_3143,'#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4705,c_86936])).

tff(c_86950,plain,(
    ! [C_3142,A_3143] :
      ( k1_funct_1(k5_relat_1('#skF_4',C_3142),A_3143) = k1_funct_1(C_3142,k1_funct_1('#skF_4',A_3143))
      | ~ v1_funct_1(C_3142)
      | ~ v1_relat_1(C_3142)
      | v1_xboole_0('#skF_2')
      | ~ m1_subset_1(A_3143,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4705,c_121,c_66,c_86940])).

tff(c_95402,plain,(
    v1_xboole_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_86950])).

tff(c_95405,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_95402,c_2])).

tff(c_95409,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_95405])).

tff(c_95410,plain,(
    ! [C_3142,A_3143] :
      ( k1_funct_1(k5_relat_1('#skF_4',C_3142),A_3143) = k1_funct_1(C_3142,k1_funct_1('#skF_4',A_3143))
      | ~ v1_funct_1(C_3142)
      | ~ v1_relat_1(C_3142)
      | ~ m1_subset_1(A_3143,'#skF_2') ) ),
    inference(splitRight,[status(thm)],[c_86950])).

tff(c_4850,plain,(
    ! [C_410,F_409,B_411,A_407,D_408,E_406] :
      ( k1_partfun1(A_407,B_411,C_410,D_408,E_406,F_409) = k5_relat_1(E_406,F_409)
      | ~ m1_subset_1(F_409,k1_zfmisc_1(k2_zfmisc_1(C_410,D_408)))
      | ~ v1_funct_1(F_409)
      | ~ m1_subset_1(E_406,k1_zfmisc_1(k2_zfmisc_1(A_407,B_411)))
      | ~ v1_funct_1(E_406) ) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_4857,plain,(
    ! [A_407,B_411,E_406] :
      ( k1_partfun1(A_407,B_411,'#skF_3','#skF_1',E_406,'#skF_5') = k5_relat_1(E_406,'#skF_5')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1(E_406,k1_zfmisc_1(k2_zfmisc_1(A_407,B_411)))
      | ~ v1_funct_1(E_406) ) ),
    inference(resolution,[status(thm)],[c_58,c_4850])).

tff(c_85865,plain,(
    ! [A_3072,B_3073,E_3074] :
      ( k1_partfun1(A_3072,B_3073,'#skF_3','#skF_1',E_3074,'#skF_5') = k5_relat_1(E_3074,'#skF_5')
      | ~ m1_subset_1(E_3074,k1_zfmisc_1(k2_zfmisc_1(A_3072,B_3073)))
      | ~ v1_funct_1(E_3074) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_4857])).

tff(c_85872,plain,
    ( k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_1','#skF_4','#skF_5') = k5_relat_1('#skF_4','#skF_5')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_62,c_85865])).

tff(c_85887,plain,(
    k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_1','#skF_4','#skF_5') = k5_relat_1('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_85872])).

tff(c_477,plain,(
    k1_relset_1('#skF_3','#skF_1','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_58,c_456])).

tff(c_54,plain,(
    r1_tarski(k2_relset_1('#skF_2','#skF_3','#skF_4'),k1_relset_1('#skF_3','#skF_1','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_484,plain,(
    r1_tarski(k2_relset_1('#skF_2','#skF_3','#skF_4'),k1_relat_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_477,c_54])).

tff(c_190,plain,(
    ! [C_82,A_83,B_84] :
      ( v4_relat_1(C_82,A_83)
      | ~ m1_subset_1(C_82,k1_zfmisc_1(k2_zfmisc_1(A_83,B_84))) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_211,plain,(
    v4_relat_1('#skF_5','#skF_3') ),
    inference(resolution,[status(thm)],[c_58,c_190])).

tff(c_90,plain,(
    r1_tarski('#skF_4',k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_62,c_76])).

tff(c_314,plain,(
    ! [A_104,C_105,B_106] :
      ( r1_tarski(A_104,C_105)
      | ~ r1_tarski(B_106,C_105)
      | ~ r1_tarski(A_104,B_106) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_330,plain,(
    ! [A_104] :
      ( r1_tarski(A_104,k2_zfmisc_1('#skF_2','#skF_3'))
      | ~ r1_tarski(A_104,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_90,c_314])).

tff(c_12,plain,(
    ! [A_8,B_9] :
      ( m1_subset_1(A_8,k1_zfmisc_1(B_9))
      | ~ r1_tarski(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_4743,plain,(
    ! [B_397,C_398,A_399] :
      ( k1_xboole_0 = B_397
      | v1_funct_2(C_398,A_399,B_397)
      | k1_relset_1(A_399,B_397,C_398) != A_399
      | ~ m1_subset_1(C_398,k1_zfmisc_1(k2_zfmisc_1(A_399,B_397))) ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_85923,plain,(
    ! [B_3077,A_3078,A_3079] :
      ( k1_xboole_0 = B_3077
      | v1_funct_2(A_3078,A_3079,B_3077)
      | k1_relset_1(A_3079,B_3077,A_3078) != A_3079
      | ~ r1_tarski(A_3078,k2_zfmisc_1(A_3079,B_3077)) ) ),
    inference(resolution,[status(thm)],[c_12,c_4743])).

tff(c_85988,plain,(
    ! [A_104] :
      ( k1_xboole_0 = '#skF_3'
      | v1_funct_2(A_104,'#skF_2','#skF_3')
      | k1_relset_1('#skF_2','#skF_3',A_104) != '#skF_2'
      | ~ r1_tarski(A_104,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_330,c_85923])).

tff(c_92555,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_85988])).

tff(c_18,plain,(
    ! [B_14,A_13] :
      ( r1_tarski(k1_relat_1(B_14),A_13)
      | ~ v4_relat_1(B_14,A_13)
      | ~ v1_relat_1(B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_5297,plain,(
    ! [A_446,A_447,B_448] :
      ( r1_tarski(A_446,A_447)
      | ~ r1_tarski(A_446,k1_relat_1(B_448))
      | ~ v4_relat_1(B_448,A_447)
      | ~ v1_relat_1(B_448) ) ),
    inference(resolution,[status(thm)],[c_18,c_314])).

tff(c_5314,plain,(
    ! [A_447] :
      ( r1_tarski(k2_relset_1('#skF_2','#skF_3','#skF_4'),A_447)
      | ~ v4_relat_1('#skF_5',A_447)
      | ~ v1_relat_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_484,c_5297])).

tff(c_5341,plain,(
    ! [A_449] :
      ( r1_tarski(k2_relset_1('#skF_2','#skF_3','#skF_4'),A_449)
      | ~ v4_relat_1('#skF_5',A_449) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_122,c_5314])).

tff(c_332,plain,(
    ! [A_104,A_5] :
      ( r1_tarski(A_104,A_5)
      | ~ r1_tarski(A_104,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_93,c_314])).

tff(c_5409,plain,(
    ! [A_5] :
      ( r1_tarski(k2_relset_1('#skF_2','#skF_3','#skF_4'),A_5)
      | ~ v4_relat_1('#skF_5',k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_5341,c_332])).

tff(c_69800,plain,(
    ~ v4_relat_1('#skF_5',k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_5409])).

tff(c_92582,plain,(
    ~ v4_relat_1('#skF_5','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_92555,c_69800])).

tff(c_92617,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_211,c_92582])).

tff(c_92619,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_85988])).

tff(c_4907,plain,(
    ! [A_420,B_419,C_418,D_421,E_417] :
      ( k1_partfun1(A_420,B_419,B_419,C_418,D_421,E_417) = k8_funct_2(A_420,B_419,C_418,D_421,E_417)
      | k1_xboole_0 = B_419
      | ~ r1_tarski(k2_relset_1(A_420,B_419,D_421),k1_relset_1(B_419,C_418,E_417))
      | ~ m1_subset_1(E_417,k1_zfmisc_1(k2_zfmisc_1(B_419,C_418)))
      | ~ v1_funct_1(E_417)
      | ~ m1_subset_1(D_421,k1_zfmisc_1(k2_zfmisc_1(A_420,B_419)))
      | ~ v1_funct_2(D_421,A_420,B_419)
      | ~ v1_funct_1(D_421) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_4916,plain,(
    ! [A_420,D_421] :
      ( k1_partfun1(A_420,'#skF_3','#skF_3','#skF_1',D_421,'#skF_5') = k8_funct_2(A_420,'#skF_3','#skF_1',D_421,'#skF_5')
      | k1_xboole_0 = '#skF_3'
      | ~ r1_tarski(k2_relset_1(A_420,'#skF_3',D_421),k1_relat_1('#skF_5'))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_1')))
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1(D_421,k1_zfmisc_1(k2_zfmisc_1(A_420,'#skF_3')))
      | ~ v1_funct_2(D_421,A_420,'#skF_3')
      | ~ v1_funct_1(D_421) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_477,c_4907])).

tff(c_4923,plain,(
    ! [A_420,D_421] :
      ( k1_partfun1(A_420,'#skF_3','#skF_3','#skF_1',D_421,'#skF_5') = k8_funct_2(A_420,'#skF_3','#skF_1',D_421,'#skF_5')
      | k1_xboole_0 = '#skF_3'
      | ~ r1_tarski(k2_relset_1(A_420,'#skF_3',D_421),k1_relat_1('#skF_5'))
      | ~ m1_subset_1(D_421,k1_zfmisc_1(k2_zfmisc_1(A_420,'#skF_3')))
      | ~ v1_funct_2(D_421,A_420,'#skF_3')
      | ~ v1_funct_1(D_421) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_4916])).

tff(c_99401,plain,(
    ! [A_3483,D_3484] :
      ( k1_partfun1(A_3483,'#skF_3','#skF_3','#skF_1',D_3484,'#skF_5') = k8_funct_2(A_3483,'#skF_3','#skF_1',D_3484,'#skF_5')
      | ~ r1_tarski(k2_relset_1(A_3483,'#skF_3',D_3484),k1_relat_1('#skF_5'))
      | ~ m1_subset_1(D_3484,k1_zfmisc_1(k2_zfmisc_1(A_3483,'#skF_3')))
      | ~ v1_funct_2(D_3484,A_3483,'#skF_3')
      | ~ v1_funct_1(D_3484) ) ),
    inference(negUnitSimplification,[status(thm)],[c_92619,c_4923])).

tff(c_99408,plain,
    ( k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_1','#skF_4','#skF_5') = k8_funct_2('#skF_2','#skF_3','#skF_1','#skF_4','#skF_5')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_3')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_484,c_99401])).

tff(c_99414,plain,(
    k8_funct_2('#skF_2','#skF_3','#skF_1','#skF_4','#skF_5') = k5_relat_1('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_62,c_85887,c_99408])).

tff(c_50,plain,(
    k1_funct_1(k8_funct_2('#skF_2','#skF_3','#skF_1','#skF_4','#skF_5'),'#skF_6') != k1_funct_1('#skF_5',k1_funct_1('#skF_4','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_99671,plain,(
    k1_funct_1(k5_relat_1('#skF_4','#skF_5'),'#skF_6') != k1_funct_1('#skF_5',k1_funct_1('#skF_4','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_99414,c_50])).

tff(c_99678,plain,
    ( ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5')
    | ~ m1_subset_1('#skF_6','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_95410,c_99671])).

tff(c_99685,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_122,c_60,c_99678])).

tff(c_99706,plain,(
    ! [A_3486] : r1_tarski(k2_relset_1('#skF_2','#skF_3','#skF_4'),A_3486) ),
    inference(splitRight,[status(thm)],[c_5409])).

tff(c_126,plain,(
    ! [A_74,B_75] :
      ( r2_hidden(A_74,B_75)
      | v1_xboole_0(B_75)
      | ~ m1_subset_1(A_74,B_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_22,plain,(
    ! [B_20,A_19] :
      ( ~ r1_tarski(B_20,A_19)
      | ~ r2_hidden(A_19,B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_130,plain,(
    ! [B_75,A_74] :
      ( ~ r1_tarski(B_75,A_74)
      | v1_xboole_0(B_75)
      | ~ m1_subset_1(A_74,B_75) ) ),
    inference(resolution,[status(thm)],[c_126,c_22])).

tff(c_99793,plain,(
    ! [A_3486] :
      ( v1_xboole_0(k2_relset_1('#skF_2','#skF_3','#skF_4'))
      | ~ m1_subset_1(A_3486,k2_relset_1('#skF_2','#skF_3','#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_99706,c_130])).

tff(c_115670,plain,(
    ! [A_4106] : ~ m1_subset_1(A_4106,k2_relset_1('#skF_2','#skF_3','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_99793])).

tff(c_115680,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_46,c_115670])).

tff(c_115681,plain,(
    v1_xboole_0(k2_relset_1('#skF_2','#skF_3','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_99793])).

tff(c_115685,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_115681,c_2])).

tff(c_99854,plain,(
    ! [A_3493,B_3494,E_3495] :
      ( k1_partfun1(A_3493,B_3494,'#skF_3','#skF_1',E_3495,'#skF_5') = k5_relat_1(E_3495,'#skF_5')
      | ~ m1_subset_1(E_3495,k1_zfmisc_1(k2_zfmisc_1(A_3493,B_3494)))
      | ~ v1_funct_1(E_3495) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_4857])).

tff(c_99861,plain,
    ( k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_1','#skF_4','#skF_5') = k5_relat_1('#skF_4','#skF_5')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_62,c_99854])).

tff(c_99876,plain,(
    k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_1','#skF_4','#skF_5') = k5_relat_1('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_99861])).

tff(c_99687,plain,(
    v4_relat_1('#skF_5',k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_5409])).

tff(c_333,plain,(
    ! [A_107,A_108] :
      ( r1_tarski(A_107,A_108)
      | ~ r1_tarski(A_107,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_93,c_314])).

tff(c_4617,plain,(
    ! [B_392,A_393] :
      ( r1_tarski(k1_relat_1(B_392),A_393)
      | ~ v4_relat_1(B_392,k1_xboole_0)
      | ~ v1_relat_1(B_392) ) ),
    inference(resolution,[status(thm)],[c_18,c_333])).

tff(c_16,plain,(
    ! [B_14,A_13] :
      ( v4_relat_1(B_14,A_13)
      | ~ r1_tarski(k1_relat_1(B_14),A_13)
      | ~ v1_relat_1(B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_4671,plain,(
    ! [B_392,A_393] :
      ( v4_relat_1(B_392,A_393)
      | ~ v4_relat_1(B_392,k1_xboole_0)
      | ~ v1_relat_1(B_392) ) ),
    inference(resolution,[status(thm)],[c_4617,c_16])).

tff(c_99689,plain,(
    ! [A_393] :
      ( v4_relat_1('#skF_5',A_393)
      | ~ v1_relat_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_99687,c_4671])).

tff(c_99692,plain,(
    ! [A_393] : v4_relat_1('#skF_5',A_393) ),
    inference(demodulation,[status(thm),theory(equality)],[c_122,c_99689])).

tff(c_92,plain,(
    ! [B_64] : r1_tarski(o_1_1_funct_2(k1_zfmisc_1(B_64)),B_64) ),
    inference(resolution,[status(thm)],[c_46,c_76])).

tff(c_596,plain,(
    ! [A_137,B_138] :
      ( r1_tarski(A_137,B_138)
      | ~ r1_tarski(A_137,o_1_1_funct_2(k1_zfmisc_1(B_138))) ) ),
    inference(resolution,[status(thm)],[c_92,c_314])).

tff(c_111846,plain,(
    ! [B_4044,B_4045] :
      ( r1_tarski(k1_relat_1(B_4044),B_4045)
      | ~ v4_relat_1(B_4044,o_1_1_funct_2(k1_zfmisc_1(B_4045)))
      | ~ v1_relat_1(B_4044) ) ),
    inference(resolution,[status(thm)],[c_18,c_596])).

tff(c_111942,plain,(
    ! [B_4045] :
      ( r1_tarski(k1_relat_1('#skF_5'),B_4045)
      | ~ v1_relat_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_99692,c_111846])).

tff(c_112058,plain,(
    ! [B_4046] : r1_tarski(k1_relat_1('#skF_5'),B_4046) ),
    inference(demodulation,[status(thm),theory(equality)],[c_122,c_111942])).

tff(c_112192,plain,(
    ! [B_4046] :
      ( v1_xboole_0(k1_relat_1('#skF_5'))
      | ~ m1_subset_1(B_4046,k1_relat_1('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_112058,c_130])).

tff(c_112629,plain,(
    ! [B_4052] : ~ m1_subset_1(B_4052,k1_relat_1('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_112192])).

tff(c_112639,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_46,c_112629])).

tff(c_112640,plain,(
    v1_xboole_0(k1_relat_1('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_112192])).

tff(c_112644,plain,(
    k1_relat_1('#skF_5') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_112640,c_2])).

tff(c_4687,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_relset_1('#skF_3','#skF_1','#skF_5') = '#skF_3'
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_58,c_4677])).

tff(c_4701,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_relat_1('#skF_5') = '#skF_3'
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_477,c_4687])).

tff(c_4740,plain,(
    ~ v1_funct_2('#skF_5','#skF_3','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_4701])).

tff(c_4753,plain,
    ( k1_xboole_0 = '#skF_1'
    | v1_funct_2('#skF_5','#skF_3','#skF_1')
    | k1_relset_1('#skF_3','#skF_1','#skF_5') != '#skF_3' ),
    inference(resolution,[status(thm)],[c_58,c_4743])).

tff(c_4767,plain,
    ( k1_xboole_0 = '#skF_1'
    | v1_funct_2('#skF_5','#skF_3','#skF_1')
    | k1_relat_1('#skF_5') != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_477,c_4753])).

tff(c_4768,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_relat_1('#skF_5') != '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_4740,c_4767])).

tff(c_4772,plain,(
    k1_relat_1('#skF_5') != '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_4768])).

tff(c_112671,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_112644,c_4772])).

tff(c_122911,plain,(
    ! [A_420,D_421] :
      ( k1_partfun1(A_420,'#skF_3','#skF_3','#skF_1',D_421,'#skF_5') = k8_funct_2(A_420,'#skF_3','#skF_1',D_421,'#skF_5')
      | k1_xboole_0 = '#skF_3'
      | ~ r1_tarski(k2_relset_1(A_420,'#skF_3',D_421),k1_xboole_0)
      | ~ m1_subset_1(D_421,k1_zfmisc_1(k2_zfmisc_1(A_420,'#skF_3')))
      | ~ v1_funct_2(D_421,A_420,'#skF_3')
      | ~ v1_funct_1(D_421) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_112644,c_4923])).

tff(c_122913,plain,(
    ! [A_4345,D_4346] :
      ( k1_partfun1(A_4345,'#skF_3','#skF_3','#skF_1',D_4346,'#skF_5') = k8_funct_2(A_4345,'#skF_3','#skF_1',D_4346,'#skF_5')
      | ~ r1_tarski(k2_relset_1(A_4345,'#skF_3',D_4346),k1_xboole_0)
      | ~ m1_subset_1(D_4346,k1_zfmisc_1(k2_zfmisc_1(A_4345,'#skF_3')))
      | ~ v1_funct_2(D_4346,A_4345,'#skF_3')
      | ~ v1_funct_1(D_4346) ) ),
    inference(negUnitSimplification,[status(thm)],[c_112671,c_122911])).

tff(c_122924,plain,
    ( k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_1','#skF_4','#skF_5') = k8_funct_2('#skF_2','#skF_3','#skF_1','#skF_4','#skF_5')
    | ~ r1_tarski(k2_relset_1('#skF_2','#skF_3','#skF_4'),k1_xboole_0)
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_3')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_62,c_122913])).

tff(c_122937,plain,(
    k8_funct_2('#skF_2','#skF_3','#skF_1','#skF_4','#skF_5') = k5_relat_1('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_93,c_115685,c_99876,c_122924])).

tff(c_122940,plain,(
    k1_funct_1(k5_relat_1('#skF_4','#skF_5'),'#skF_6') != k1_funct_1('#skF_5',k1_funct_1('#skF_4','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_122937,c_50])).

tff(c_122947,plain,
    ( ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5')
    | ~ m1_subset_1('#skF_6','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_119309,c_122940])).

tff(c_122954,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_122,c_60,c_122947])).

tff(c_122955,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_4768])).

tff(c_122981,plain,(
    ! [A_5] : r1_tarski('#skF_1',A_5) ),
    inference(demodulation,[status(thm),theory(equality)],[c_122955,c_93])).

tff(c_122985,plain,(
    '#skF_2' != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_122955,c_52])).

tff(c_123044,plain,(
    ! [B_4348,C_4349,A_4350] :
      ( k1_funct_1(k5_relat_1(B_4348,C_4349),A_4350) = k1_funct_1(C_4349,k1_funct_1(B_4348,A_4350))
      | ~ r2_hidden(A_4350,k1_relat_1(B_4348))
      | ~ v1_funct_1(C_4349)
      | ~ v1_relat_1(C_4349)
      | ~ v1_funct_1(B_4348)
      | ~ v1_relat_1(B_4348) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_179217,plain,(
    ! [B_5873,C_5874,A_5875] :
      ( k1_funct_1(k5_relat_1(B_5873,C_5874),A_5875) = k1_funct_1(C_5874,k1_funct_1(B_5873,A_5875))
      | ~ v1_funct_1(C_5874)
      | ~ v1_relat_1(C_5874)
      | ~ v1_funct_1(B_5873)
      | ~ v1_relat_1(B_5873)
      | v1_xboole_0(k1_relat_1(B_5873))
      | ~ m1_subset_1(A_5875,k1_relat_1(B_5873)) ) ),
    inference(resolution,[status(thm)],[c_8,c_123044])).

tff(c_179223,plain,(
    ! [C_5874,A_5875] :
      ( k1_funct_1(k5_relat_1('#skF_4',C_5874),A_5875) = k1_funct_1(C_5874,k1_funct_1('#skF_4',A_5875))
      | ~ v1_funct_1(C_5874)
      | ~ v1_relat_1(C_5874)
      | ~ v1_funct_1('#skF_4')
      | ~ v1_relat_1('#skF_4')
      | v1_xboole_0(k1_relat_1('#skF_4'))
      | ~ m1_subset_1(A_5875,'#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4705,c_179217])).

tff(c_179233,plain,(
    ! [C_5874,A_5875] :
      ( k1_funct_1(k5_relat_1('#skF_4',C_5874),A_5875) = k1_funct_1(C_5874,k1_funct_1('#skF_4',A_5875))
      | ~ v1_funct_1(C_5874)
      | ~ v1_relat_1(C_5874)
      | v1_xboole_0('#skF_2')
      | ~ m1_subset_1(A_5875,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4705,c_121,c_66,c_179223])).

tff(c_194517,plain,(
    v1_xboole_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_179233])).

tff(c_122984,plain,(
    ! [A_1] :
      ( A_1 = '#skF_1'
      | ~ v1_xboole_0(A_1) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_122955,c_2])).

tff(c_194520,plain,(
    '#skF_2' = '#skF_1' ),
    inference(resolution,[status(thm)],[c_194517,c_122984])).

tff(c_194524,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_122985,c_194520])).

tff(c_194525,plain,(
    ! [C_5874,A_5875] :
      ( k1_funct_1(k5_relat_1('#skF_4',C_5874),A_5875) = k1_funct_1(C_5874,k1_funct_1('#skF_4',A_5875))
      | ~ v1_funct_1(C_5874)
      | ~ v1_relat_1(C_5874)
      | ~ m1_subset_1(A_5875,'#skF_2') ) ),
    inference(splitRight,[status(thm)],[c_179233])).

tff(c_122956,plain,(
    k1_relat_1('#skF_5') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_4768])).

tff(c_122993,plain,(
    r1_tarski(k2_relset_1('#skF_2','#skF_3','#skF_4'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_122956,c_484])).

tff(c_123158,plain,(
    ! [B_4363,F_4361,E_4358,D_4360,A_4359,C_4362] :
      ( k1_partfun1(A_4359,B_4363,C_4362,D_4360,E_4358,F_4361) = k5_relat_1(E_4358,F_4361)
      | ~ m1_subset_1(F_4361,k1_zfmisc_1(k2_zfmisc_1(C_4362,D_4360)))
      | ~ v1_funct_1(F_4361)
      | ~ m1_subset_1(E_4358,k1_zfmisc_1(k2_zfmisc_1(A_4359,B_4363)))
      | ~ v1_funct_1(E_4358) ) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_123168,plain,(
    ! [A_4359,B_4363,E_4358] :
      ( k1_partfun1(A_4359,B_4363,'#skF_3','#skF_1',E_4358,'#skF_5') = k5_relat_1(E_4358,'#skF_5')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1(E_4358,k1_zfmisc_1(k2_zfmisc_1(A_4359,B_4363)))
      | ~ v1_funct_1(E_4358) ) ),
    inference(resolution,[status(thm)],[c_58,c_123158])).

tff(c_153387,plain,(
    ! [A_5204,B_5205,E_5206] :
      ( k1_partfun1(A_5204,B_5205,'#skF_3','#skF_1',E_5206,'#skF_5') = k5_relat_1(E_5206,'#skF_5')
      | ~ m1_subset_1(E_5206,k1_zfmisc_1(k2_zfmisc_1(A_5204,B_5205)))
      | ~ v1_funct_1(E_5206) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_123168])).

tff(c_153398,plain,
    ( k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_1','#skF_4','#skF_5') = k5_relat_1('#skF_4','#skF_5')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_62,c_153387])).

tff(c_153410,plain,(
    k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_1','#skF_4','#skF_5') = k5_relat_1('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_153398])).

tff(c_479,plain,(
    ! [A_123,B_124] : k1_relset_1(A_123,B_124,k1_xboole_0) = k1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_6,c_456])).

tff(c_716,plain,(
    ! [C_141,B_142] :
      ( v1_funct_2(C_141,k1_xboole_0,B_142)
      | k1_relset_1(k1_xboole_0,B_142,C_141) != k1_xboole_0
      | ~ m1_subset_1(C_141,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_142))) ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_728,plain,(
    ! [B_142] :
      ( v1_funct_2(k1_xboole_0,k1_xboole_0,B_142)
      | k1_relset_1(k1_xboole_0,B_142,k1_xboole_0) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_6,c_716])).

tff(c_732,plain,(
    ! [B_142] :
      ( v1_funct_2(k1_xboole_0,k1_xboole_0,B_142)
      | k1_relat_1(k1_xboole_0) != k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_479,c_728])).

tff(c_736,plain,(
    k1_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_732])).

tff(c_124,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_6,c_101])).

tff(c_213,plain,(
    ! [A_83] : v4_relat_1(k1_xboole_0,A_83) ),
    inference(resolution,[status(thm)],[c_6,c_190])).

tff(c_3673,plain,(
    ! [B_355,B_356] :
      ( r1_tarski(k1_relat_1(B_355),B_356)
      | ~ v4_relat_1(B_355,o_1_1_funct_2(k1_zfmisc_1(B_356)))
      | ~ v1_relat_1(B_355) ) ),
    inference(resolution,[status(thm)],[c_18,c_596])).

tff(c_3756,plain,(
    ! [B_356] :
      ( r1_tarski(k1_relat_1(k1_xboole_0),B_356)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_213,c_3673])).

tff(c_3815,plain,(
    ! [B_357] : r1_tarski(k1_relat_1(k1_xboole_0),B_357) ),
    inference(demodulation,[status(thm),theory(equality)],[c_124,c_3756])).

tff(c_3942,plain,(
    ! [B_357] :
      ( v1_xboole_0(k1_relat_1(k1_xboole_0))
      | ~ m1_subset_1(B_357,k1_relat_1(k1_xboole_0)) ) ),
    inference(resolution,[status(thm)],[c_3815,c_130])).

tff(c_4504,plain,(
    ! [B_374] : ~ m1_subset_1(B_374,k1_relat_1(k1_xboole_0)) ),
    inference(splitLeft,[status(thm)],[c_3942])).

tff(c_4509,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_46,c_4504])).

tff(c_4510,plain,(
    v1_xboole_0(k1_relat_1(k1_xboole_0)) ),
    inference(splitRight,[status(thm)],[c_3942])).

tff(c_4513,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_4510,c_2])).

tff(c_4517,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_736,c_4513])).

tff(c_4518,plain,(
    ! [B_142] : v1_funct_2(k1_xboole_0,k1_xboole_0,B_142) ),
    inference(splitRight,[status(thm)],[c_732])).

tff(c_122965,plain,(
    ! [B_142] : v1_funct_2('#skF_1','#skF_1',B_142) ),
    inference(demodulation,[status(thm),theory(equality)],[c_122955,c_122955,c_4518])).

tff(c_91,plain,(
    r1_tarski('#skF_5',k2_zfmisc_1('#skF_3','#skF_1')) ),
    inference(resolution,[status(thm)],[c_58,c_76])).

tff(c_331,plain,(
    ! [A_104] :
      ( r1_tarski(A_104,k2_zfmisc_1('#skF_3','#skF_1'))
      | ~ r1_tarski(A_104,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_91,c_314])).

tff(c_553,plain,(
    ! [C_132,A_133] :
      ( k1_xboole_0 = C_132
      | ~ v1_funct_2(C_132,A_133,k1_xboole_0)
      | k1_xboole_0 = A_133
      | ~ m1_subset_1(C_132,k1_zfmisc_1(k2_zfmisc_1(A_133,k1_xboole_0))) ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_566,plain,(
    ! [A_8,A_133] :
      ( k1_xboole_0 = A_8
      | ~ v1_funct_2(A_8,A_133,k1_xboole_0)
      | k1_xboole_0 = A_133
      | ~ r1_tarski(A_8,k2_zfmisc_1(A_133,k1_xboole_0)) ) ),
    inference(resolution,[status(thm)],[c_12,c_553])).

tff(c_153559,plain,(
    ! [A_5214,A_5215] :
      ( A_5214 = '#skF_1'
      | ~ v1_funct_2(A_5214,A_5215,'#skF_1')
      | A_5215 = '#skF_1'
      | ~ r1_tarski(A_5214,k2_zfmisc_1(A_5215,'#skF_1')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_122955,c_122955,c_122955,c_122955,c_566])).

tff(c_153594,plain,(
    ! [A_104] :
      ( A_104 = '#skF_1'
      | ~ v1_funct_2(A_104,'#skF_3','#skF_1')
      | '#skF_3' = '#skF_1'
      | ~ r1_tarski(A_104,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_331,c_153559])).

tff(c_181076,plain,(
    '#skF_3' = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_153594])).

tff(c_123004,plain,(
    ! [A_13] :
      ( v4_relat_1('#skF_5',A_13)
      | ~ r1_tarski('#skF_3',A_13)
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_122956,c_16])).

tff(c_123325,plain,(
    ! [A_4381] :
      ( v4_relat_1('#skF_5',A_4381)
      | ~ r1_tarski('#skF_3',A_4381) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_122,c_123004])).

tff(c_408,plain,(
    ! [A_121] :
      ( r1_tarski(A_121,k2_zfmisc_1('#skF_3','#skF_1'))
      | ~ r1_tarski(A_121,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_91,c_314])).

tff(c_120,plain,(
    ! [A_8,A_70,B_71] :
      ( v1_relat_1(A_8)
      | ~ r1_tarski(A_8,k2_zfmisc_1(A_70,B_71)) ) ),
    inference(resolution,[status(thm)],[c_12,c_101])).

tff(c_433,plain,(
    ! [A_122] :
      ( v1_relat_1(A_122)
      | ~ r1_tarski(A_122,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_408,c_120])).

tff(c_452,plain,(
    ! [B_14] :
      ( v1_relat_1(k1_relat_1(B_14))
      | ~ v4_relat_1(B_14,'#skF_5')
      | ~ v1_relat_1(B_14) ) ),
    inference(resolution,[status(thm)],[c_18,c_433])).

tff(c_122998,plain,
    ( v1_relat_1('#skF_3')
    | ~ v4_relat_1('#skF_5','#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_122956,c_452])).

tff(c_123011,plain,
    ( v1_relat_1('#skF_3')
    | ~ v4_relat_1('#skF_5','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_122,c_122998])).

tff(c_123235,plain,(
    ~ v4_relat_1('#skF_5','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_123011])).

tff(c_123333,plain,(
    ~ r1_tarski('#skF_3','#skF_5') ),
    inference(resolution,[status(thm)],[c_123325,c_123235])).

tff(c_127038,plain,(
    ! [B_4561,C_4562,A_4563] :
      ( k1_funct_1(k5_relat_1(B_4561,C_4562),A_4563) = k1_funct_1(C_4562,k1_funct_1(B_4561,A_4563))
      | ~ v1_funct_1(C_4562)
      | ~ v1_relat_1(C_4562)
      | ~ v1_funct_1(B_4561)
      | ~ v1_relat_1(B_4561)
      | v1_xboole_0(k1_relat_1(B_4561))
      | ~ m1_subset_1(A_4563,k1_relat_1(B_4561)) ) ),
    inference(resolution,[status(thm)],[c_8,c_123044])).

tff(c_127044,plain,(
    ! [C_4562,A_4563] :
      ( k1_funct_1(k5_relat_1('#skF_4',C_4562),A_4563) = k1_funct_1(C_4562,k1_funct_1('#skF_4',A_4563))
      | ~ v1_funct_1(C_4562)
      | ~ v1_relat_1(C_4562)
      | ~ v1_funct_1('#skF_4')
      | ~ v1_relat_1('#skF_4')
      | v1_xboole_0(k1_relat_1('#skF_4'))
      | ~ m1_subset_1(A_4563,'#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4705,c_127038])).

tff(c_127054,plain,(
    ! [C_4562,A_4563] :
      ( k1_funct_1(k5_relat_1('#skF_4',C_4562),A_4563) = k1_funct_1(C_4562,k1_funct_1('#skF_4',A_4563))
      | ~ v1_funct_1(C_4562)
      | ~ v1_relat_1(C_4562)
      | v1_xboole_0('#skF_2')
      | ~ m1_subset_1(A_4563,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4705,c_121,c_66,c_127044])).

tff(c_147281,plain,(
    v1_xboole_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_127054])).

tff(c_147284,plain,(
    '#skF_2' = '#skF_1' ),
    inference(resolution,[status(thm)],[c_147281,c_122984])).

tff(c_147288,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_122985,c_147284])).

tff(c_147289,plain,(
    ! [C_4562,A_4563] :
      ( k1_funct_1(k5_relat_1('#skF_4',C_4562),A_4563) = k1_funct_1(C_4562,k1_funct_1('#skF_4',A_4563))
      | ~ v1_funct_1(C_4562)
      | ~ v1_relat_1(C_4562)
      | ~ m1_subset_1(A_4563,'#skF_2') ) ),
    inference(splitRight,[status(thm)],[c_127054])).

tff(c_123453,plain,(
    ! [A_4389,B_4390,E_4391] :
      ( k1_partfun1(A_4389,B_4390,'#skF_3','#skF_1',E_4391,'#skF_5') = k5_relat_1(E_4391,'#skF_5')
      | ~ m1_subset_1(E_4391,k1_zfmisc_1(k2_zfmisc_1(A_4389,B_4390)))
      | ~ v1_funct_1(E_4391) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_123168])).

tff(c_123464,plain,
    ( k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_1','#skF_4','#skF_5') = k5_relat_1('#skF_4','#skF_5')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_62,c_123453])).

tff(c_123476,plain,(
    k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_1','#skF_4','#skF_5') = k5_relat_1('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_123464])).

tff(c_123717,plain,(
    ! [A_4406,A_4407] :
      ( A_4406 = '#skF_1'
      | ~ v1_funct_2(A_4406,A_4407,'#skF_1')
      | A_4407 = '#skF_1'
      | ~ r1_tarski(A_4406,k2_zfmisc_1(A_4407,'#skF_1')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_122955,c_122955,c_122955,c_122955,c_566])).

tff(c_123752,plain,(
    ! [A_104] :
      ( A_104 = '#skF_1'
      | ~ v1_funct_2(A_104,'#skF_3','#skF_1')
      | '#skF_3' = '#skF_1'
      | ~ r1_tarski(A_104,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_331,c_123717])).

tff(c_126703,plain,(
    '#skF_3' = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_123752])).

tff(c_123015,plain,(
    ! [A_13] :
      ( v4_relat_1('#skF_5',A_13)
      | ~ r1_tarski('#skF_3',A_13) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_122,c_123004])).

tff(c_123603,plain,(
    ! [A_4398,A_4399,B_4400] :
      ( r1_tarski(A_4398,A_4399)
      | ~ r1_tarski(A_4398,k1_relat_1(B_4400))
      | ~ v4_relat_1(B_4400,A_4399)
      | ~ v1_relat_1(B_4400) ) ),
    inference(resolution,[status(thm)],[c_18,c_314])).

tff(c_123616,plain,(
    ! [A_4398,A_4399] :
      ( r1_tarski(A_4398,A_4399)
      | ~ r1_tarski(A_4398,'#skF_3')
      | ~ v4_relat_1('#skF_5',A_4399)
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_122956,c_123603])).

tff(c_123904,plain,(
    ! [A_4415,A_4416] :
      ( r1_tarski(A_4415,A_4416)
      | ~ r1_tarski(A_4415,'#skF_3')
      | ~ v4_relat_1('#skF_5',A_4416) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_122,c_123616])).

tff(c_123945,plain,(
    ! [A_4417] :
      ( r1_tarski(o_1_1_funct_2(k1_zfmisc_1('#skF_3')),A_4417)
      | ~ v4_relat_1('#skF_5',A_4417) ) ),
    inference(resolution,[status(thm)],[c_92,c_123904])).

tff(c_329,plain,(
    ! [A_104,B_64] :
      ( r1_tarski(A_104,B_64)
      | ~ r1_tarski(A_104,o_1_1_funct_2(k1_zfmisc_1(B_64))) ) ),
    inference(resolution,[status(thm)],[c_92,c_314])).

tff(c_125005,plain,(
    ! [B_4469] :
      ( r1_tarski(o_1_1_funct_2(k1_zfmisc_1('#skF_3')),B_4469)
      | ~ v4_relat_1('#skF_5',o_1_1_funct_2(k1_zfmisc_1(B_4469))) ) ),
    inference(resolution,[status(thm)],[c_123945,c_329])).

tff(c_125392,plain,(
    ! [B_4481] :
      ( r1_tarski(o_1_1_funct_2(k1_zfmisc_1('#skF_3')),B_4481)
      | ~ r1_tarski('#skF_3',o_1_1_funct_2(k1_zfmisc_1(B_4481))) ) ),
    inference(resolution,[status(thm)],[c_123015,c_125005])).

tff(c_432,plain,(
    ! [A_121] :
      ( v1_relat_1(A_121)
      | ~ r1_tarski(A_121,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_408,c_120])).

tff(c_125492,plain,
    ( v1_relat_1(o_1_1_funct_2(k1_zfmisc_1('#skF_3')))
    | ~ r1_tarski('#skF_3',o_1_1_funct_2(k1_zfmisc_1('#skF_5'))) ),
    inference(resolution,[status(thm)],[c_125392,c_432])).

tff(c_125499,plain,(
    ~ r1_tarski('#skF_3',o_1_1_funct_2(k1_zfmisc_1('#skF_5'))) ),
    inference(splitLeft,[status(thm)],[c_125492])).

tff(c_126716,plain,(
    ~ r1_tarski('#skF_1',o_1_1_funct_2(k1_zfmisc_1('#skF_5'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_126703,c_125499])).

tff(c_126779,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_122981,c_126716])).

tff(c_126781,plain,(
    '#skF_3' != '#skF_1' ),
    inference(splitRight,[status(thm)],[c_123752])).

tff(c_122994,plain,(
    k1_relset_1('#skF_3','#skF_1','#skF_5') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_122956,c_477])).

tff(c_32,plain,(
    ! [D_33,E_35,A_30,C_32,B_31] :
      ( k1_partfun1(A_30,B_31,B_31,C_32,D_33,E_35) = k8_funct_2(A_30,B_31,C_32,D_33,E_35)
      | k1_xboole_0 = B_31
      | ~ r1_tarski(k2_relset_1(A_30,B_31,D_33),k1_relset_1(B_31,C_32,E_35))
      | ~ m1_subset_1(E_35,k1_zfmisc_1(k2_zfmisc_1(B_31,C_32)))
      | ~ v1_funct_1(E_35)
      | ~ m1_subset_1(D_33,k1_zfmisc_1(k2_zfmisc_1(A_30,B_31)))
      | ~ v1_funct_2(D_33,A_30,B_31)
      | ~ v1_funct_1(D_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_123237,plain,(
    ! [B_4369,E_4367,D_4371,C_4368,A_4370] :
      ( k1_partfun1(A_4370,B_4369,B_4369,C_4368,D_4371,E_4367) = k8_funct_2(A_4370,B_4369,C_4368,D_4371,E_4367)
      | B_4369 = '#skF_1'
      | ~ r1_tarski(k2_relset_1(A_4370,B_4369,D_4371),k1_relset_1(B_4369,C_4368,E_4367))
      | ~ m1_subset_1(E_4367,k1_zfmisc_1(k2_zfmisc_1(B_4369,C_4368)))
      | ~ v1_funct_1(E_4367)
      | ~ m1_subset_1(D_4371,k1_zfmisc_1(k2_zfmisc_1(A_4370,B_4369)))
      | ~ v1_funct_2(D_4371,A_4370,B_4369)
      | ~ v1_funct_1(D_4371) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_122955,c_32])).

tff(c_123243,plain,(
    ! [A_4370,D_4371] :
      ( k1_partfun1(A_4370,'#skF_3','#skF_3','#skF_1',D_4371,'#skF_5') = k8_funct_2(A_4370,'#skF_3','#skF_1',D_4371,'#skF_5')
      | '#skF_3' = '#skF_1'
      | ~ r1_tarski(k2_relset_1(A_4370,'#skF_3',D_4371),'#skF_3')
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_1')))
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1(D_4371,k1_zfmisc_1(k2_zfmisc_1(A_4370,'#skF_3')))
      | ~ v1_funct_2(D_4371,A_4370,'#skF_3')
      | ~ v1_funct_1(D_4371) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_122994,c_123237])).

tff(c_123250,plain,(
    ! [A_4370,D_4371] :
      ( k1_partfun1(A_4370,'#skF_3','#skF_3','#skF_1',D_4371,'#skF_5') = k8_funct_2(A_4370,'#skF_3','#skF_1',D_4371,'#skF_5')
      | '#skF_3' = '#skF_1'
      | ~ r1_tarski(k2_relset_1(A_4370,'#skF_3',D_4371),'#skF_3')
      | ~ m1_subset_1(D_4371,k1_zfmisc_1(k2_zfmisc_1(A_4370,'#skF_3')))
      | ~ v1_funct_2(D_4371,A_4370,'#skF_3')
      | ~ v1_funct_1(D_4371) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_123243])).

tff(c_152976,plain,(
    ! [A_5175,D_5176] :
      ( k1_partfun1(A_5175,'#skF_3','#skF_3','#skF_1',D_5176,'#skF_5') = k8_funct_2(A_5175,'#skF_3','#skF_1',D_5176,'#skF_5')
      | ~ r1_tarski(k2_relset_1(A_5175,'#skF_3',D_5176),'#skF_3')
      | ~ m1_subset_1(D_5176,k1_zfmisc_1(k2_zfmisc_1(A_5175,'#skF_3')))
      | ~ v1_funct_2(D_5176,A_5175,'#skF_3')
      | ~ v1_funct_1(D_5176) ) ),
    inference(negUnitSimplification,[status(thm)],[c_126781,c_123250])).

tff(c_152991,plain,
    ( k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_1','#skF_4','#skF_5') = k8_funct_2('#skF_2','#skF_3','#skF_1','#skF_4','#skF_5')
    | ~ r1_tarski(k2_relset_1('#skF_2','#skF_3','#skF_4'),'#skF_3')
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_3')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_62,c_152976])).

tff(c_153001,plain,(
    k8_funct_2('#skF_2','#skF_3','#skF_1','#skF_4','#skF_5') = k5_relat_1('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_122993,c_123476,c_152991])).

tff(c_153019,plain,(
    k1_funct_1(k5_relat_1('#skF_4','#skF_5'),'#skF_6') != k1_funct_1('#skF_5',k1_funct_1('#skF_4','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_153001,c_50])).

tff(c_153026,plain,
    ( ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5')
    | ~ m1_subset_1('#skF_6','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_147289,c_153019])).

tff(c_153033,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_122,c_60,c_153026])).

tff(c_153035,plain,(
    r1_tarski('#skF_3',o_1_1_funct_2(k1_zfmisc_1('#skF_5'))) ),
    inference(splitRight,[status(thm)],[c_125492])).

tff(c_153038,plain,(
    r1_tarski('#skF_3','#skF_5') ),
    inference(resolution,[status(thm)],[c_153035,c_329])).

tff(c_153047,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_123333,c_153038])).

tff(c_153049,plain,(
    v4_relat_1('#skF_5','#skF_5') ),
    inference(splitRight,[status(thm)],[c_123011])).

tff(c_123007,plain,(
    ! [A_13] :
      ( r1_tarski('#skF_3',A_13)
      | ~ v4_relat_1('#skF_5',A_13)
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_122956,c_18])).

tff(c_153153,plain,(
    ! [A_5193] :
      ( r1_tarski('#skF_3',A_5193)
      | ~ v4_relat_1('#skF_5',A_5193) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_122,c_123007])).

tff(c_153172,plain,(
    r1_tarski('#skF_3','#skF_5') ),
    inference(resolution,[status(thm)],[c_153049,c_153153])).

tff(c_155762,plain,(
    ! [B_5305] :
      ( v4_relat_1(B_5305,k2_zfmisc_1('#skF_3','#skF_1'))
      | ~ v1_relat_1(B_5305)
      | ~ r1_tarski(k1_relat_1(B_5305),'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_408,c_16])).

tff(c_123017,plain,(
    ! [A_13] :
      ( r1_tarski('#skF_3',A_13)
      | ~ v4_relat_1('#skF_5',A_13) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_122,c_123007])).

tff(c_155779,plain,
    ( r1_tarski('#skF_3',k2_zfmisc_1('#skF_3','#skF_1'))
    | ~ v1_relat_1('#skF_5')
    | ~ r1_tarski(k1_relat_1('#skF_5'),'#skF_5') ),
    inference(resolution,[status(thm)],[c_155762,c_123017])).

tff(c_155796,plain,(
    r1_tarski('#skF_3',k2_zfmisc_1('#skF_3','#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_153172,c_122956,c_122,c_155779])).

tff(c_153558,plain,(
    ! [A_8,A_133] :
      ( A_8 = '#skF_1'
      | ~ v1_funct_2(A_8,A_133,'#skF_1')
      | A_133 = '#skF_1'
      | ~ r1_tarski(A_8,k2_zfmisc_1(A_133,'#skF_1')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_122955,c_122955,c_122955,c_122955,c_566])).

tff(c_155837,plain,
    ( ~ v1_funct_2('#skF_3','#skF_3','#skF_1')
    | '#skF_3' = '#skF_1' ),
    inference(resolution,[status(thm)],[c_155796,c_153558])).

tff(c_155860,plain,(
    ~ v1_funct_2('#skF_3','#skF_3','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_155837])).

tff(c_181144,plain,(
    ~ v1_funct_2('#skF_1','#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_181076,c_181076,c_155860])).

tff(c_181264,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_122965,c_181144])).

tff(c_181266,plain,(
    '#skF_3' != '#skF_1' ),
    inference(splitRight,[status(thm)],[c_153594])).

tff(c_153052,plain,(
    ! [A_5180,B_5179,C_5178,E_5177,D_5181] :
      ( k1_partfun1(A_5180,B_5179,B_5179,C_5178,D_5181,E_5177) = k8_funct_2(A_5180,B_5179,C_5178,D_5181,E_5177)
      | B_5179 = '#skF_1'
      | ~ r1_tarski(k2_relset_1(A_5180,B_5179,D_5181),k1_relset_1(B_5179,C_5178,E_5177))
      | ~ m1_subset_1(E_5177,k1_zfmisc_1(k2_zfmisc_1(B_5179,C_5178)))
      | ~ v1_funct_1(E_5177)
      | ~ m1_subset_1(D_5181,k1_zfmisc_1(k2_zfmisc_1(A_5180,B_5179)))
      | ~ v1_funct_2(D_5181,A_5180,B_5179)
      | ~ v1_funct_1(D_5181) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_122955,c_32])).

tff(c_153058,plain,(
    ! [A_5180,D_5181] :
      ( k1_partfun1(A_5180,'#skF_3','#skF_3','#skF_1',D_5181,'#skF_5') = k8_funct_2(A_5180,'#skF_3','#skF_1',D_5181,'#skF_5')
      | '#skF_3' = '#skF_1'
      | ~ r1_tarski(k2_relset_1(A_5180,'#skF_3',D_5181),'#skF_3')
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_1')))
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1(D_5181,k1_zfmisc_1(k2_zfmisc_1(A_5180,'#skF_3')))
      | ~ v1_funct_2(D_5181,A_5180,'#skF_3')
      | ~ v1_funct_1(D_5181) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_122994,c_153052])).

tff(c_153065,plain,(
    ! [A_5180,D_5181] :
      ( k1_partfun1(A_5180,'#skF_3','#skF_3','#skF_1',D_5181,'#skF_5') = k8_funct_2(A_5180,'#skF_3','#skF_1',D_5181,'#skF_5')
      | '#skF_3' = '#skF_1'
      | ~ r1_tarski(k2_relset_1(A_5180,'#skF_3',D_5181),'#skF_3')
      | ~ m1_subset_1(D_5181,k1_zfmisc_1(k2_zfmisc_1(A_5180,'#skF_3')))
      | ~ v1_funct_2(D_5181,A_5180,'#skF_3')
      | ~ v1_funct_1(D_5181) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_153058])).

tff(c_199686,plain,(
    ! [A_6395,D_6396] :
      ( k1_partfun1(A_6395,'#skF_3','#skF_3','#skF_1',D_6396,'#skF_5') = k8_funct_2(A_6395,'#skF_3','#skF_1',D_6396,'#skF_5')
      | ~ r1_tarski(k2_relset_1(A_6395,'#skF_3',D_6396),'#skF_3')
      | ~ m1_subset_1(D_6396,k1_zfmisc_1(k2_zfmisc_1(A_6395,'#skF_3')))
      | ~ v1_funct_2(D_6396,A_6395,'#skF_3')
      | ~ v1_funct_1(D_6396) ) ),
    inference(negUnitSimplification,[status(thm)],[c_181266,c_153065])).

tff(c_199701,plain,
    ( k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_1','#skF_4','#skF_5') = k8_funct_2('#skF_2','#skF_3','#skF_1','#skF_4','#skF_5')
    | ~ r1_tarski(k2_relset_1('#skF_2','#skF_3','#skF_4'),'#skF_3')
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_3')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_62,c_199686])).

tff(c_199711,plain,(
    k8_funct_2('#skF_2','#skF_3','#skF_1','#skF_4','#skF_5') = k5_relat_1('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_122993,c_153410,c_199701])).

tff(c_199731,plain,(
    k1_funct_1(k5_relat_1('#skF_4','#skF_5'),'#skF_6') != k1_funct_1('#skF_5',k1_funct_1('#skF_4','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_199711,c_50])).

tff(c_199955,plain,
    ( ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5')
    | ~ m1_subset_1('#skF_6','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_194525,c_199731])).

tff(c_199962,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_122,c_60,c_199955])).

tff(c_199963,plain,(
    '#skF_3' = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_155837])).

tff(c_153600,plain,(
    ! [B_5216,A_5217] :
      ( v4_relat_1(B_5216,A_5217)
      | ~ v4_relat_1(B_5216,'#skF_1')
      | ~ v1_relat_1(B_5216) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_122955,c_4671])).

tff(c_153606,plain,(
    ! [A_5217] :
      ( v4_relat_1('#skF_5',A_5217)
      | ~ v1_relat_1('#skF_5')
      | ~ r1_tarski('#skF_3','#skF_1') ) ),
    inference(resolution,[status(thm)],[c_123015,c_153600])).

tff(c_153624,plain,(
    ! [A_5217] :
      ( v4_relat_1('#skF_5',A_5217)
      | ~ r1_tarski('#skF_3','#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_122,c_153606])).

tff(c_153637,plain,(
    ~ r1_tarski('#skF_3','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_153624])).

tff(c_200011,plain,(
    ~ r1_tarski('#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_199963,c_153637])).

tff(c_200073,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_122981,c_200011])).

tff(c_200074,plain,(
    ! [A_5217] : v4_relat_1('#skF_5',A_5217) ),
    inference(splitRight,[status(thm)],[c_153624])).

tff(c_200094,plain,(
    ! [A_6400] : r1_tarski('#skF_3',A_6400) ),
    inference(demodulation,[status(thm),theory(equality)],[c_200074,c_123017])).

tff(c_200141,plain,(
    ! [A_6400] :
      ( v1_xboole_0('#skF_3')
      | ~ m1_subset_1(A_6400,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_200094,c_130])).

tff(c_200179,plain,(
    ! [A_6403] : ~ m1_subset_1(A_6403,'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_200141])).

tff(c_200184,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_46,c_200179])).

tff(c_200185,plain,
    ( k1_relat_1('#skF_5') = '#skF_3'
    | k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_4701])).

tff(c_200215,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_200185])).

tff(c_200239,plain,(
    v1_relat_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_200215,c_124])).

tff(c_154,plain,(
    ! [B_79,A_80] :
      ( ~ r1_tarski(B_79,A_80)
      | v1_xboole_0(B_79)
      | ~ m1_subset_1(A_80,B_79) ) ),
    inference(resolution,[status(thm)],[c_126,c_22])).

tff(c_174,plain,(
    ! [A_5] :
      ( v1_xboole_0(k1_xboole_0)
      | ~ m1_subset_1(A_5,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_93,c_154])).

tff(c_176,plain,(
    ! [A_81] : ~ m1_subset_1(A_81,k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_174])).

tff(c_181,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_46,c_176])).

tff(c_182,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_174])).

tff(c_200238,plain,(
    v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_200215,c_182])).

tff(c_200186,plain,(
    v1_funct_2('#skF_5','#skF_3','#skF_1') ),
    inference(splitRight,[status(thm)],[c_4701])).

tff(c_201307,plain,(
    ! [A_6478,A_6479] :
      ( A_6478 = '#skF_1'
      | ~ v1_funct_2(A_6478,A_6479,'#skF_1')
      | A_6479 = '#skF_1'
      | ~ r1_tarski(A_6478,k2_zfmisc_1(A_6479,'#skF_1')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_200215,c_200215,c_200215,c_200215,c_566])).

tff(c_201341,plain,
    ( '#skF_5' = '#skF_1'
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_1')
    | '#skF_3' = '#skF_1' ),
    inference(resolution,[status(thm)],[c_91,c_201307])).

tff(c_201352,plain,
    ( '#skF_5' = '#skF_1'
    | '#skF_3' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_200186,c_201341])).

tff(c_201353,plain,(
    '#skF_3' = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_201352])).

tff(c_201385,plain,(
    ~ v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_201353,c_68])).

tff(c_201388,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_200238,c_201385])).

tff(c_201389,plain,(
    '#skF_5' = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_201352])).

tff(c_201437,plain,(
    v1_funct_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_201389,c_60])).

tff(c_200244,plain,(
    '#skF_2' != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_200215,c_52])).

tff(c_200323,plain,(
    ! [B_6409,C_6410,A_6411] :
      ( k1_funct_1(k5_relat_1(B_6409,C_6410),A_6411) = k1_funct_1(C_6410,k1_funct_1(B_6409,A_6411))
      | ~ r2_hidden(A_6411,k1_relat_1(B_6409))
      | ~ v1_funct_1(C_6410)
      | ~ v1_relat_1(C_6410)
      | ~ v1_funct_1(B_6409)
      | ~ v1_relat_1(B_6409) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_203932,plain,(
    ! [B_6629,C_6630,A_6631] :
      ( k1_funct_1(k5_relat_1(B_6629,C_6630),A_6631) = k1_funct_1(C_6630,k1_funct_1(B_6629,A_6631))
      | ~ v1_funct_1(C_6630)
      | ~ v1_relat_1(C_6630)
      | ~ v1_funct_1(B_6629)
      | ~ v1_relat_1(B_6629)
      | v1_xboole_0(k1_relat_1(B_6629))
      | ~ m1_subset_1(A_6631,k1_relat_1(B_6629)) ) ),
    inference(resolution,[status(thm)],[c_8,c_200323])).

tff(c_203936,plain,(
    ! [C_6630,A_6631] :
      ( k1_funct_1(k5_relat_1('#skF_4',C_6630),A_6631) = k1_funct_1(C_6630,k1_funct_1('#skF_4',A_6631))
      | ~ v1_funct_1(C_6630)
      | ~ v1_relat_1(C_6630)
      | ~ v1_funct_1('#skF_4')
      | ~ v1_relat_1('#skF_4')
      | v1_xboole_0(k1_relat_1('#skF_4'))
      | ~ m1_subset_1(A_6631,'#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4705,c_203932])).

tff(c_203943,plain,(
    ! [C_6630,A_6631] :
      ( k1_funct_1(k5_relat_1('#skF_4',C_6630),A_6631) = k1_funct_1(C_6630,k1_funct_1('#skF_4',A_6631))
      | ~ v1_funct_1(C_6630)
      | ~ v1_relat_1(C_6630)
      | v1_xboole_0('#skF_2')
      | ~ m1_subset_1(A_6631,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4705,c_121,c_66,c_203936])).

tff(c_211589,plain,(
    v1_xboole_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_203943])).

tff(c_200243,plain,(
    ! [A_1] :
      ( A_1 = '#skF_1'
      | ~ v1_xboole_0(A_1) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_200215,c_2])).

tff(c_211592,plain,(
    '#skF_2' = '#skF_1' ),
    inference(resolution,[status(thm)],[c_211589,c_200243])).

tff(c_211596,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_200244,c_211592])).

tff(c_211597,plain,(
    ! [C_6630,A_6631] :
      ( k1_funct_1(k5_relat_1('#skF_4',C_6630),A_6631) = k1_funct_1(C_6630,k1_funct_1('#skF_4',A_6631))
      | ~ v1_funct_1(C_6630)
      | ~ v1_relat_1(C_6630)
      | ~ m1_subset_1(A_6631,'#skF_2') ) ),
    inference(splitRight,[status(thm)],[c_203943])).

tff(c_200240,plain,(
    ! [A_5] : r1_tarski('#skF_1',A_5) ),
    inference(demodulation,[status(thm),theory(equality)],[c_200215,c_93])).

tff(c_200237,plain,(
    ! [A_83] : v4_relat_1('#skF_1',A_83) ),
    inference(demodulation,[status(thm),theory(equality)],[c_200215,c_213])).

tff(c_200771,plain,(
    ! [A_6456,A_6457,B_6458] :
      ( r1_tarski(A_6456,A_6457)
      | ~ r1_tarski(A_6456,k1_relat_1(B_6458))
      | ~ v4_relat_1(B_6458,A_6457)
      | ~ v1_relat_1(B_6458) ) ),
    inference(resolution,[status(thm)],[c_18,c_314])).

tff(c_200791,plain,(
    ! [A_6457] :
      ( r1_tarski(k2_relset_1('#skF_2','#skF_3','#skF_4'),A_6457)
      | ~ v4_relat_1('#skF_5',A_6457)
      | ~ v1_relat_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_484,c_200771])).

tff(c_200814,plain,(
    ! [A_6457] :
      ( r1_tarski(k2_relset_1('#skF_2','#skF_3','#skF_4'),A_6457)
      | ~ v4_relat_1('#skF_5',A_6457) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_122,c_200791])).

tff(c_201408,plain,(
    ! [A_6457] :
      ( r1_tarski(k2_relset_1('#skF_2','#skF_3','#skF_4'),A_6457)
      | ~ v4_relat_1('#skF_1',A_6457) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_201389,c_200814])).

tff(c_201514,plain,(
    ! [A_6485] : r1_tarski(k2_relset_1('#skF_2','#skF_3','#skF_4'),A_6485) ),
    inference(demodulation,[status(thm),theory(equality)],[c_200237,c_201408])).

tff(c_201591,plain,(
    ! [A_6485] :
      ( v1_xboole_0(k2_relset_1('#skF_2','#skF_3','#skF_4'))
      | ~ m1_subset_1(A_6485,k2_relset_1('#skF_2','#skF_3','#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_201514,c_130])).

tff(c_207388,plain,(
    ! [A_6719] : ~ m1_subset_1(A_6719,k2_relset_1('#skF_2','#skF_3','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_201591])).

tff(c_207398,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_46,c_207388])).

tff(c_207399,plain,(
    v1_xboole_0(k2_relset_1('#skF_2','#skF_3','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_201591])).

tff(c_207403,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_4') = '#skF_1' ),
    inference(resolution,[status(thm)],[c_207399,c_200243])).

tff(c_200387,plain,(
    ! [A_6419,E_6418,F_6421,C_6422,D_6420,B_6423] :
      ( k1_partfun1(A_6419,B_6423,C_6422,D_6420,E_6418,F_6421) = k5_relat_1(E_6418,F_6421)
      | ~ m1_subset_1(F_6421,k1_zfmisc_1(k2_zfmisc_1(C_6422,D_6420)))
      | ~ v1_funct_1(F_6421)
      | ~ m1_subset_1(E_6418,k1_zfmisc_1(k2_zfmisc_1(A_6419,B_6423)))
      | ~ v1_funct_1(E_6418) ) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_204557,plain,(
    ! [A_6651,C_6652,B_6653,A_6650,E_6654,D_6655] :
      ( k1_partfun1(A_6651,B_6653,C_6652,D_6655,E_6654,A_6650) = k5_relat_1(E_6654,A_6650)
      | ~ v1_funct_1(A_6650)
      | ~ m1_subset_1(E_6654,k1_zfmisc_1(k2_zfmisc_1(A_6651,B_6653)))
      | ~ v1_funct_1(E_6654)
      | ~ r1_tarski(A_6650,k2_zfmisc_1(C_6652,D_6655)) ) ),
    inference(resolution,[status(thm)],[c_12,c_200387])).

tff(c_204565,plain,(
    ! [C_6652,D_6655,A_6650] :
      ( k1_partfun1('#skF_2','#skF_3',C_6652,D_6655,'#skF_4',A_6650) = k5_relat_1('#skF_4',A_6650)
      | ~ v1_funct_1(A_6650)
      | ~ v1_funct_1('#skF_4')
      | ~ r1_tarski(A_6650,k2_zfmisc_1(C_6652,D_6655)) ) ),
    inference(resolution,[status(thm)],[c_62,c_204557])).

tff(c_204958,plain,(
    ! [C_6660,D_6661,A_6662] :
      ( k1_partfun1('#skF_2','#skF_3',C_6660,D_6661,'#skF_4',A_6662) = k5_relat_1('#skF_4',A_6662)
      | ~ v1_funct_1(A_6662)
      | ~ r1_tarski(A_6662,k2_zfmisc_1(C_6660,D_6661)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_204565])).

tff(c_205020,plain,(
    ! [C_6660,D_6661] :
      ( k1_partfun1('#skF_2','#skF_3',C_6660,D_6661,'#skF_4','#skF_1') = k5_relat_1('#skF_4','#skF_1')
      | ~ v1_funct_1('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_200240,c_204958])).

tff(c_205056,plain,(
    ! [C_6660,D_6661] : k1_partfun1('#skF_2','#skF_3',C_6660,D_6661,'#skF_4','#skF_1') = k5_relat_1('#skF_4','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_201437,c_205020])).

tff(c_201390,plain,(
    '#skF_3' != '#skF_1' ),
    inference(splitRight,[status(thm)],[c_201352])).

tff(c_4519,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_732])).

tff(c_200225,plain,(
    k1_relat_1('#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_200215,c_200215,c_4519])).

tff(c_200493,plain,(
    ! [C_6431,A_6433,B_6432,E_6430,D_6434] :
      ( k1_partfun1(A_6433,B_6432,B_6432,C_6431,D_6434,E_6430) = k8_funct_2(A_6433,B_6432,C_6431,D_6434,E_6430)
      | B_6432 = '#skF_1'
      | ~ r1_tarski(k2_relset_1(A_6433,B_6432,D_6434),k1_relset_1(B_6432,C_6431,E_6430))
      | ~ m1_subset_1(E_6430,k1_zfmisc_1(k2_zfmisc_1(B_6432,C_6431)))
      | ~ v1_funct_1(E_6430)
      | ~ m1_subset_1(D_6434,k1_zfmisc_1(k2_zfmisc_1(A_6433,B_6432)))
      | ~ v1_funct_2(D_6434,A_6433,B_6432)
      | ~ v1_funct_1(D_6434) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_200215,c_32])).

tff(c_200502,plain,(
    ! [A_6433,D_6434] :
      ( k1_partfun1(A_6433,'#skF_3','#skF_3','#skF_1',D_6434,'#skF_5') = k8_funct_2(A_6433,'#skF_3','#skF_1',D_6434,'#skF_5')
      | '#skF_3' = '#skF_1'
      | ~ r1_tarski(k2_relset_1(A_6433,'#skF_3',D_6434),k1_relat_1('#skF_5'))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_1')))
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1(D_6434,k1_zfmisc_1(k2_zfmisc_1(A_6433,'#skF_3')))
      | ~ v1_funct_2(D_6434,A_6433,'#skF_3')
      | ~ v1_funct_1(D_6434) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_477,c_200493])).

tff(c_200509,plain,(
    ! [A_6433,D_6434] :
      ( k1_partfun1(A_6433,'#skF_3','#skF_3','#skF_1',D_6434,'#skF_5') = k8_funct_2(A_6433,'#skF_3','#skF_1',D_6434,'#skF_5')
      | '#skF_3' = '#skF_1'
      | ~ r1_tarski(k2_relset_1(A_6433,'#skF_3',D_6434),k1_relat_1('#skF_5'))
      | ~ m1_subset_1(D_6434,k1_zfmisc_1(k2_zfmisc_1(A_6433,'#skF_3')))
      | ~ v1_funct_2(D_6434,A_6433,'#skF_3')
      | ~ v1_funct_1(D_6434) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_200502])).

tff(c_215052,plain,(
    ! [A_6433,D_6434] :
      ( k1_partfun1(A_6433,'#skF_3','#skF_3','#skF_1',D_6434,'#skF_1') = k8_funct_2(A_6433,'#skF_3','#skF_1',D_6434,'#skF_1')
      | '#skF_3' = '#skF_1'
      | ~ r1_tarski(k2_relset_1(A_6433,'#skF_3',D_6434),'#skF_1')
      | ~ m1_subset_1(D_6434,k1_zfmisc_1(k2_zfmisc_1(A_6433,'#skF_3')))
      | ~ v1_funct_2(D_6434,A_6433,'#skF_3')
      | ~ v1_funct_1(D_6434) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_200225,c_201389,c_201389,c_201389,c_200509])).

tff(c_215054,plain,(
    ! [A_6975,D_6976] :
      ( k1_partfun1(A_6975,'#skF_3','#skF_3','#skF_1',D_6976,'#skF_1') = k8_funct_2(A_6975,'#skF_3','#skF_1',D_6976,'#skF_1')
      | ~ r1_tarski(k2_relset_1(A_6975,'#skF_3',D_6976),'#skF_1')
      | ~ m1_subset_1(D_6976,k1_zfmisc_1(k2_zfmisc_1(A_6975,'#skF_3')))
      | ~ v1_funct_2(D_6976,A_6975,'#skF_3')
      | ~ v1_funct_1(D_6976) ) ),
    inference(negUnitSimplification,[status(thm)],[c_201390,c_215052])).

tff(c_215069,plain,
    ( k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_1','#skF_4','#skF_1') = k8_funct_2('#skF_2','#skF_3','#skF_1','#skF_4','#skF_1')
    | ~ r1_tarski(k2_relset_1('#skF_2','#skF_3','#skF_4'),'#skF_1')
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_3')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_62,c_215054])).

tff(c_215081,plain,(
    k8_funct_2('#skF_2','#skF_3','#skF_1','#skF_4','#skF_1') = k5_relat_1('#skF_4','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_200240,c_207403,c_205056,c_215069])).

tff(c_201432,plain,(
    k1_funct_1(k8_funct_2('#skF_2','#skF_3','#skF_1','#skF_4','#skF_1'),'#skF_6') != k1_funct_1('#skF_1',k1_funct_1('#skF_4','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_201389,c_201389,c_50])).

tff(c_215083,plain,(
    k1_funct_1(k5_relat_1('#skF_4','#skF_1'),'#skF_6') != k1_funct_1('#skF_1',k1_funct_1('#skF_4','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_215081,c_201432])).

tff(c_215090,plain,
    ( ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1')
    | ~ m1_subset_1('#skF_6','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_211597,c_215083])).

tff(c_215097,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_200239,c_201437,c_215090])).

tff(c_215098,plain,(
    k1_relat_1('#skF_5') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_200185])).

tff(c_215105,plain,(
    r1_tarski(k2_relset_1('#skF_2','#skF_3','#skF_4'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_215098,c_484])).

tff(c_238479,plain,(
    ! [E_7653,B_7658,A_7654,F_7656,D_7655,C_7657] :
      ( k1_partfun1(A_7654,B_7658,C_7657,D_7655,E_7653,F_7656) = k5_relat_1(E_7653,F_7656)
      | ~ m1_subset_1(F_7656,k1_zfmisc_1(k2_zfmisc_1(C_7657,D_7655)))
      | ~ v1_funct_1(F_7656)
      | ~ m1_subset_1(E_7653,k1_zfmisc_1(k2_zfmisc_1(A_7654,B_7658)))
      | ~ v1_funct_1(E_7653) ) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_238486,plain,(
    ! [A_7654,B_7658,E_7653] :
      ( k1_partfun1(A_7654,B_7658,'#skF_3','#skF_1',E_7653,'#skF_5') = k5_relat_1(E_7653,'#skF_5')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1(E_7653,k1_zfmisc_1(k2_zfmisc_1(A_7654,B_7658)))
      | ~ v1_funct_1(E_7653) ) ),
    inference(resolution,[status(thm)],[c_58,c_238479])).

tff(c_239132,plain,(
    ! [A_7695,B_7696,E_7697] :
      ( k1_partfun1(A_7695,B_7696,'#skF_3','#skF_1',E_7697,'#skF_5') = k5_relat_1(E_7697,'#skF_5')
      | ~ m1_subset_1(E_7697,k1_zfmisc_1(k2_zfmisc_1(A_7695,B_7696)))
      | ~ v1_funct_1(E_7697) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_238486])).

tff(c_239139,plain,
    ( k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_1','#skF_4','#skF_5') = k5_relat_1('#skF_4','#skF_5')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_62,c_239132])).

tff(c_239154,plain,(
    k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_1','#skF_4','#skF_5') = k5_relat_1('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_239139])).

tff(c_215122,plain,(
    ! [A_13] :
      ( r1_tarski('#skF_3',A_13)
      | ~ v4_relat_1('#skF_5',A_13)
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_215098,c_18])).

tff(c_238502,plain,(
    ! [A_7659] :
      ( r1_tarski('#skF_3',A_7659)
      | ~ v4_relat_1('#skF_5',A_7659) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_122,c_215122])).

tff(c_238520,plain,(
    r1_tarski('#skF_3','#skF_3') ),
    inference(resolution,[status(thm)],[c_211,c_238502])).

tff(c_200187,plain,(
    ! [B_6404,C_6405,A_6406] :
      ( k1_xboole_0 = B_6404
      | v1_funct_2(C_6405,A_6406,B_6404)
      | k1_relset_1(A_6406,B_6404,C_6405) != A_6406
      | ~ m1_subset_1(C_6405,k1_zfmisc_1(k2_zfmisc_1(A_6406,B_6404))) ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_240395,plain,(
    ! [B_7755,A_7756,A_7757] :
      ( k1_xboole_0 = B_7755
      | v1_funct_2(A_7756,A_7757,B_7755)
      | k1_relset_1(A_7757,B_7755,A_7756) != A_7757
      | ~ r1_tarski(A_7756,k2_zfmisc_1(A_7757,B_7755)) ) ),
    inference(resolution,[status(thm)],[c_12,c_200187])).

tff(c_240450,plain,(
    ! [A_104] :
      ( k1_xboole_0 = '#skF_3'
      | v1_funct_2(A_104,'#skF_2','#skF_3')
      | k1_relset_1('#skF_2','#skF_3',A_104) != '#skF_2'
      | ~ r1_tarski(A_104,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_330,c_240395])).

tff(c_248291,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_240450])).

tff(c_215119,plain,(
    ! [A_13] :
      ( v4_relat_1('#skF_5',A_13)
      | ~ r1_tarski('#skF_3',A_13)
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_215098,c_16])).

tff(c_215132,plain,(
    ! [A_13] :
      ( v4_relat_1('#skF_5',A_13)
      | ~ r1_tarski('#skF_3',A_13) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_122,c_215119])).

tff(c_343,plain,(
    ! [B_14,A_108] :
      ( r1_tarski(k1_relat_1(B_14),A_108)
      | ~ v4_relat_1(B_14,k1_xboole_0)
      | ~ v1_relat_1(B_14) ) ),
    inference(resolution,[status(thm)],[c_18,c_333])).

tff(c_215110,plain,(
    ! [A_108] :
      ( r1_tarski('#skF_3',A_108)
      | ~ v4_relat_1('#skF_5',k1_xboole_0)
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_215098,c_343])).

tff(c_215126,plain,(
    ! [A_108] :
      ( r1_tarski('#skF_3',A_108)
      | ~ v4_relat_1('#skF_5',k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_122,c_215110])).

tff(c_238568,plain,(
    ~ v4_relat_1('#skF_5',k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_215126])).

tff(c_238588,plain,(
    ~ r1_tarski('#skF_3',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_215132,c_238568])).

tff(c_248327,plain,(
    ~ r1_tarski('#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_248291,c_238588])).

tff(c_248353,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_238520,c_248327])).

tff(c_248355,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_240450])).

tff(c_215106,plain,(
    k1_relset_1('#skF_3','#skF_1','#skF_5') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_215098,c_477])).

tff(c_238550,plain,(
    ! [C_7662,E_7661,D_7665,A_7664,B_7663] :
      ( k1_partfun1(A_7664,B_7663,B_7663,C_7662,D_7665,E_7661) = k8_funct_2(A_7664,B_7663,C_7662,D_7665,E_7661)
      | k1_xboole_0 = B_7663
      | ~ r1_tarski(k2_relset_1(A_7664,B_7663,D_7665),k1_relset_1(B_7663,C_7662,E_7661))
      | ~ m1_subset_1(E_7661,k1_zfmisc_1(k2_zfmisc_1(B_7663,C_7662)))
      | ~ v1_funct_1(E_7661)
      | ~ m1_subset_1(D_7665,k1_zfmisc_1(k2_zfmisc_1(A_7664,B_7663)))
      | ~ v1_funct_2(D_7665,A_7664,B_7663)
      | ~ v1_funct_1(D_7665) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_238553,plain,(
    ! [A_7664,D_7665] :
      ( k1_partfun1(A_7664,'#skF_3','#skF_3','#skF_1',D_7665,'#skF_5') = k8_funct_2(A_7664,'#skF_3','#skF_1',D_7665,'#skF_5')
      | k1_xboole_0 = '#skF_3'
      | ~ r1_tarski(k2_relset_1(A_7664,'#skF_3',D_7665),'#skF_3')
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_1')))
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1(D_7665,k1_zfmisc_1(k2_zfmisc_1(A_7664,'#skF_3')))
      | ~ v1_funct_2(D_7665,A_7664,'#skF_3')
      | ~ v1_funct_1(D_7665) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_215106,c_238550])).

tff(c_238561,plain,(
    ! [A_7664,D_7665] :
      ( k1_partfun1(A_7664,'#skF_3','#skF_3','#skF_1',D_7665,'#skF_5') = k8_funct_2(A_7664,'#skF_3','#skF_1',D_7665,'#skF_5')
      | k1_xboole_0 = '#skF_3'
      | ~ r1_tarski(k2_relset_1(A_7664,'#skF_3',D_7665),'#skF_3')
      | ~ m1_subset_1(D_7665,k1_zfmisc_1(k2_zfmisc_1(A_7664,'#skF_3')))
      | ~ v1_funct_2(D_7665,A_7664,'#skF_3')
      | ~ v1_funct_1(D_7665) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_238553])).

tff(c_254245,plain,(
    ! [A_8164,D_8165] :
      ( k1_partfun1(A_8164,'#skF_3','#skF_3','#skF_1',D_8165,'#skF_5') = k8_funct_2(A_8164,'#skF_3','#skF_1',D_8165,'#skF_5')
      | ~ r1_tarski(k2_relset_1(A_8164,'#skF_3',D_8165),'#skF_3')
      | ~ m1_subset_1(D_8165,k1_zfmisc_1(k2_zfmisc_1(A_8164,'#skF_3')))
      | ~ v1_funct_2(D_8165,A_8164,'#skF_3')
      | ~ v1_funct_1(D_8165) ) ),
    inference(negUnitSimplification,[status(thm)],[c_248355,c_238561])).

tff(c_254256,plain,
    ( k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_1','#skF_4','#skF_5') = k8_funct_2('#skF_2','#skF_3','#skF_1','#skF_4','#skF_5')
    | ~ r1_tarski(k2_relset_1('#skF_2','#skF_3','#skF_4'),'#skF_3')
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_3')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_62,c_254245])).

tff(c_254269,plain,(
    k8_funct_2('#skF_2','#skF_3','#skF_1','#skF_4','#skF_5') = k5_relat_1('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_215105,c_239154,c_254256])).

tff(c_254272,plain,(
    k1_funct_1(k5_relat_1('#skF_4','#skF_5'),'#skF_6') != k1_funct_1('#skF_5',k1_funct_1('#skF_4','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_254269,c_50])).

tff(c_254279,plain,
    ( ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5')
    | ~ m1_subset_1('#skF_6','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_248364,c_254272])).

tff(c_254286,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_122,c_60,c_254279])).

tff(c_254294,plain,(
    ! [A_8166] : r1_tarski('#skF_3',A_8166) ),
    inference(splitRight,[status(thm)],[c_215126])).

tff(c_254329,plain,(
    ! [A_8166] :
      ( v1_xboole_0('#skF_3')
      | ~ m1_subset_1(A_8166,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_254294,c_130])).

tff(c_254354,plain,(
    ! [A_8167] : ~ m1_subset_1(A_8167,'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_254329])).

tff(c_254359,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_46,c_254354])).

tff(c_254360,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_4699])).

tff(c_254383,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_254360,c_182])).

tff(c_254391,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_254383])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n022.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 14:10:56 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 48.55/37.58  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 48.76/37.65  
% 48.76/37.65  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 48.76/37.65  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k8_funct_2 > k2_relset_1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > o_1_1_funct_2 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 48.76/37.65  
% 48.76/37.65  %Foreground sorts:
% 48.76/37.65  
% 48.76/37.65  
% 48.76/37.65  %Background operators:
% 48.76/37.65  
% 48.76/37.65  
% 48.76/37.65  %Foreground operators:
% 48.76/37.65  tff(o_1_1_funct_2, type, o_1_1_funct_2: $i > $i).
% 48.76/37.65  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 48.76/37.65  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 48.76/37.65  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 48.76/37.65  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 48.76/37.65  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 48.76/37.65  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 48.76/37.65  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 48.76/37.65  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 48.76/37.65  tff('#skF_5', type, '#skF_5': $i).
% 48.76/37.65  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 48.76/37.65  tff(k8_funct_2, type, k8_funct_2: ($i * $i * $i * $i * $i) > $i).
% 48.76/37.65  tff('#skF_6', type, '#skF_6': $i).
% 48.76/37.65  tff('#skF_2', type, '#skF_2': $i).
% 48.76/37.65  tff('#skF_3', type, '#skF_3': $i).
% 48.76/37.65  tff('#skF_1', type, '#skF_1': $i).
% 48.76/37.65  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 48.76/37.65  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 48.76/37.65  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 48.76/37.65  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 48.76/37.65  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 48.76/37.65  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 48.76/37.65  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 48.76/37.65  tff('#skF_4', type, '#skF_4': $i).
% 48.76/37.65  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 48.76/37.65  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 48.76/37.65  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 48.76/37.65  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 48.76/37.65  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 48.76/37.65  
% 48.76/37.70  tff(f_163, negated_conjecture, ~(![A, B, C]: (~v1_xboole_0(C) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, C)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (![E]: ((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(C, A)))) => (![F]: (m1_subset_1(F, B) => (r1_tarski(k2_relset_1(B, C, D), k1_relset_1(C, A, E)) => ((B = k1_xboole_0) | (k1_funct_1(k8_funct_2(B, C, A, D, E), F) = k1_funct_1(E, k1_funct_1(D, F))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t185_funct_2)).
% 48.76/37.70  tff(f_128, axiom, (![A]: m1_subset_1(o_1_1_funct_2(A), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_o_1_1_funct_2)).
% 48.76/37.70  tff(f_81, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 48.76/37.70  tff(f_91, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 48.76/37.70  tff(f_126, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 48.76/37.70  tff(f_43, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 48.76/37.70  tff(f_72, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (![C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(A, k1_relat_1(B)) => (k1_funct_1(k5_relat_1(B, C), A) = k1_funct_1(C, k1_funct_1(B, A)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t23_funct_1)).
% 48.76/37.70  tff(f_29, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 48.76/37.70  tff(f_37, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 48.76/37.70  tff(f_47, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 48.76/37.70  tff(f_138, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 48.76/37.70  tff(f_87, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 48.76/37.70  tff(f_35, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 48.76/37.70  tff(f_59, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d18_relat_1)).
% 48.76/37.70  tff(f_108, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: ((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (r1_tarski(k2_relset_1(A, B, D), k1_relset_1(B, C, E)) => ((B = k1_xboole_0) | (k8_funct_2(A, B, C, D, E) = k1_partfun1(A, B, B, C, D, E)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d12_funct_2)).
% 48.76/37.70  tff(f_77, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 48.76/37.70  tff(c_68, plain, (~v1_xboole_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_163])).
% 48.76/37.70  tff(c_46, plain, (![A_39]: (m1_subset_1(o_1_1_funct_2(A_39), A_39))), inference(cnfTransformation, [status(thm)], [f_128])).
% 48.76/37.70  tff(c_56, plain, (m1_subset_1('#skF_6', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_163])).
% 48.76/37.70  tff(c_58, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_163])).
% 48.76/37.70  tff(c_101, plain, (![C_69, A_70, B_71]: (v1_relat_1(C_69) | ~m1_subset_1(C_69, k1_zfmisc_1(k2_zfmisc_1(A_70, B_71))))), inference(cnfTransformation, [status(thm)], [f_81])).
% 48.76/37.70  tff(c_122, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_58, c_101])).
% 48.76/37.70  tff(c_60, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_163])).
% 48.76/37.70  tff(c_52, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_163])).
% 48.76/37.70  tff(c_64, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_163])).
% 48.76/37.70  tff(c_62, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_163])).
% 48.76/37.70  tff(c_456, plain, (![A_123, B_124, C_125]: (k1_relset_1(A_123, B_124, C_125)=k1_relat_1(C_125) | ~m1_subset_1(C_125, k1_zfmisc_1(k2_zfmisc_1(A_123, B_124))))), inference(cnfTransformation, [status(thm)], [f_91])).
% 48.76/37.70  tff(c_476, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_62, c_456])).
% 48.76/37.70  tff(c_4677, plain, (![B_394, A_395, C_396]: (k1_xboole_0=B_394 | k1_relset_1(A_395, B_394, C_396)=A_395 | ~v1_funct_2(C_396, A_395, B_394) | ~m1_subset_1(C_396, k1_zfmisc_1(k2_zfmisc_1(A_395, B_394))))), inference(cnfTransformation, [status(thm)], [f_126])).
% 48.76/37.70  tff(c_4684, plain, (k1_xboole_0='#skF_3' | k1_relset_1('#skF_2', '#skF_3', '#skF_4')='#skF_2' | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_62, c_4677])).
% 48.76/37.70  tff(c_4699, plain, (k1_xboole_0='#skF_3' | k1_relat_1('#skF_4')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_64, c_476, c_4684])).
% 48.76/37.70  tff(c_4705, plain, (k1_relat_1('#skF_4')='#skF_2'), inference(splitLeft, [status(thm)], [c_4699])).
% 48.76/37.70  tff(c_121, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_62, c_101])).
% 48.76/37.70  tff(c_66, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_163])).
% 48.76/37.70  tff(c_8, plain, (![A_6, B_7]: (r2_hidden(A_6, B_7) | v1_xboole_0(B_7) | ~m1_subset_1(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_43])).
% 48.76/37.70  tff(c_238386, plain, (![B_7647, C_7648, A_7649]: (k1_funct_1(k5_relat_1(B_7647, C_7648), A_7649)=k1_funct_1(C_7648, k1_funct_1(B_7647, A_7649)) | ~r2_hidden(A_7649, k1_relat_1(B_7647)) | ~v1_funct_1(C_7648) | ~v1_relat_1(C_7648) | ~v1_funct_1(B_7647) | ~v1_relat_1(B_7647))), inference(cnfTransformation, [status(thm)], [f_72])).
% 48.76/37.70  tff(c_241582, plain, (![B_7821, C_7822, A_7823]: (k1_funct_1(k5_relat_1(B_7821, C_7822), A_7823)=k1_funct_1(C_7822, k1_funct_1(B_7821, A_7823)) | ~v1_funct_1(C_7822) | ~v1_relat_1(C_7822) | ~v1_funct_1(B_7821) | ~v1_relat_1(B_7821) | v1_xboole_0(k1_relat_1(B_7821)) | ~m1_subset_1(A_7823, k1_relat_1(B_7821)))), inference(resolution, [status(thm)], [c_8, c_238386])).
% 48.76/37.70  tff(c_241586, plain, (![C_7822, A_7823]: (k1_funct_1(k5_relat_1('#skF_4', C_7822), A_7823)=k1_funct_1(C_7822, k1_funct_1('#skF_4', A_7823)) | ~v1_funct_1(C_7822) | ~v1_relat_1(C_7822) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4') | v1_xboole_0(k1_relat_1('#skF_4')) | ~m1_subset_1(A_7823, '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_4705, c_241582])).
% 48.76/37.70  tff(c_241596, plain, (![C_7822, A_7823]: (k1_funct_1(k5_relat_1('#skF_4', C_7822), A_7823)=k1_funct_1(C_7822, k1_funct_1('#skF_4', A_7823)) | ~v1_funct_1(C_7822) | ~v1_relat_1(C_7822) | v1_xboole_0('#skF_2') | ~m1_subset_1(A_7823, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_4705, c_121, c_66, c_241586])).
% 48.76/37.70  tff(c_248356, plain, (v1_xboole_0('#skF_2')), inference(splitLeft, [status(thm)], [c_241596])).
% 48.76/37.70  tff(c_2, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_29])).
% 48.76/37.70  tff(c_248359, plain, (k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_248356, c_2])).
% 48.76/37.70  tff(c_248363, plain, $false, inference(negUnitSimplification, [status(thm)], [c_52, c_248359])).
% 48.76/37.70  tff(c_248364, plain, (![C_7822, A_7823]: (k1_funct_1(k5_relat_1('#skF_4', C_7822), A_7823)=k1_funct_1(C_7822, k1_funct_1('#skF_4', A_7823)) | ~v1_funct_1(C_7822) | ~v1_relat_1(C_7822) | ~m1_subset_1(A_7823, '#skF_2'))), inference(splitRight, [status(thm)], [c_241596])).
% 48.76/37.70  tff(c_4825, plain, (![B_403, C_404, A_405]: (k1_funct_1(k5_relat_1(B_403, C_404), A_405)=k1_funct_1(C_404, k1_funct_1(B_403, A_405)) | ~r2_hidden(A_405, k1_relat_1(B_403)) | ~v1_funct_1(C_404) | ~v1_relat_1(C_404) | ~v1_funct_1(B_403) | ~v1_relat_1(B_403))), inference(cnfTransformation, [status(thm)], [f_72])).
% 48.76/37.70  tff(c_110749, plain, (![B_3974, C_3975, A_3976]: (k1_funct_1(k5_relat_1(B_3974, C_3975), A_3976)=k1_funct_1(C_3975, k1_funct_1(B_3974, A_3976)) | ~v1_funct_1(C_3975) | ~v1_relat_1(C_3975) | ~v1_funct_1(B_3974) | ~v1_relat_1(B_3974) | v1_xboole_0(k1_relat_1(B_3974)) | ~m1_subset_1(A_3976, k1_relat_1(B_3974)))), inference(resolution, [status(thm)], [c_8, c_4825])).
% 48.76/37.70  tff(c_110751, plain, (![C_3975, A_3976]: (k1_funct_1(k5_relat_1('#skF_4', C_3975), A_3976)=k1_funct_1(C_3975, k1_funct_1('#skF_4', A_3976)) | ~v1_funct_1(C_3975) | ~v1_relat_1(C_3975) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4') | v1_xboole_0(k1_relat_1('#skF_4')) | ~m1_subset_1(A_3976, '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_4705, c_110749])).
% 48.76/37.70  tff(c_110758, plain, (![C_3975, A_3976]: (k1_funct_1(k5_relat_1('#skF_4', C_3975), A_3976)=k1_funct_1(C_3975, k1_funct_1('#skF_4', A_3976)) | ~v1_funct_1(C_3975) | ~v1_relat_1(C_3975) | v1_xboole_0('#skF_2') | ~m1_subset_1(A_3976, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_4705, c_121, c_66, c_110751])).
% 48.76/37.70  tff(c_119301, plain, (v1_xboole_0('#skF_2')), inference(splitLeft, [status(thm)], [c_110758])).
% 48.76/37.70  tff(c_119304, plain, (k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_119301, c_2])).
% 48.76/37.70  tff(c_119308, plain, $false, inference(negUnitSimplification, [status(thm)], [c_52, c_119304])).
% 48.76/37.70  tff(c_119309, plain, (![C_3975, A_3976]: (k1_funct_1(k5_relat_1('#skF_4', C_3975), A_3976)=k1_funct_1(C_3975, k1_funct_1('#skF_4', A_3976)) | ~v1_funct_1(C_3975) | ~v1_relat_1(C_3975) | ~m1_subset_1(A_3976, '#skF_2'))), inference(splitRight, [status(thm)], [c_110758])).
% 48.76/37.70  tff(c_6, plain, (![A_5]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_5)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 48.76/37.70  tff(c_76, plain, (![A_63, B_64]: (r1_tarski(A_63, B_64) | ~m1_subset_1(A_63, k1_zfmisc_1(B_64)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 48.76/37.70  tff(c_93, plain, (![A_5]: (r1_tarski(k1_xboole_0, A_5))), inference(resolution, [status(thm)], [c_6, c_76])).
% 48.76/37.70  tff(c_86936, plain, (![B_3141, C_3142, A_3143]: (k1_funct_1(k5_relat_1(B_3141, C_3142), A_3143)=k1_funct_1(C_3142, k1_funct_1(B_3141, A_3143)) | ~v1_funct_1(C_3142) | ~v1_relat_1(C_3142) | ~v1_funct_1(B_3141) | ~v1_relat_1(B_3141) | v1_xboole_0(k1_relat_1(B_3141)) | ~m1_subset_1(A_3143, k1_relat_1(B_3141)))), inference(resolution, [status(thm)], [c_8, c_4825])).
% 48.76/37.70  tff(c_86940, plain, (![C_3142, A_3143]: (k1_funct_1(k5_relat_1('#skF_4', C_3142), A_3143)=k1_funct_1(C_3142, k1_funct_1('#skF_4', A_3143)) | ~v1_funct_1(C_3142) | ~v1_relat_1(C_3142) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4') | v1_xboole_0(k1_relat_1('#skF_4')) | ~m1_subset_1(A_3143, '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_4705, c_86936])).
% 48.76/37.70  tff(c_86950, plain, (![C_3142, A_3143]: (k1_funct_1(k5_relat_1('#skF_4', C_3142), A_3143)=k1_funct_1(C_3142, k1_funct_1('#skF_4', A_3143)) | ~v1_funct_1(C_3142) | ~v1_relat_1(C_3142) | v1_xboole_0('#skF_2') | ~m1_subset_1(A_3143, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_4705, c_121, c_66, c_86940])).
% 48.76/37.70  tff(c_95402, plain, (v1_xboole_0('#skF_2')), inference(splitLeft, [status(thm)], [c_86950])).
% 48.76/37.70  tff(c_95405, plain, (k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_95402, c_2])).
% 48.76/37.70  tff(c_95409, plain, $false, inference(negUnitSimplification, [status(thm)], [c_52, c_95405])).
% 48.76/37.70  tff(c_95410, plain, (![C_3142, A_3143]: (k1_funct_1(k5_relat_1('#skF_4', C_3142), A_3143)=k1_funct_1(C_3142, k1_funct_1('#skF_4', A_3143)) | ~v1_funct_1(C_3142) | ~v1_relat_1(C_3142) | ~m1_subset_1(A_3143, '#skF_2'))), inference(splitRight, [status(thm)], [c_86950])).
% 48.76/37.70  tff(c_4850, plain, (![C_410, F_409, B_411, A_407, D_408, E_406]: (k1_partfun1(A_407, B_411, C_410, D_408, E_406, F_409)=k5_relat_1(E_406, F_409) | ~m1_subset_1(F_409, k1_zfmisc_1(k2_zfmisc_1(C_410, D_408))) | ~v1_funct_1(F_409) | ~m1_subset_1(E_406, k1_zfmisc_1(k2_zfmisc_1(A_407, B_411))) | ~v1_funct_1(E_406))), inference(cnfTransformation, [status(thm)], [f_138])).
% 48.76/37.70  tff(c_4857, plain, (![A_407, B_411, E_406]: (k1_partfun1(A_407, B_411, '#skF_3', '#skF_1', E_406, '#skF_5')=k5_relat_1(E_406, '#skF_5') | ~v1_funct_1('#skF_5') | ~m1_subset_1(E_406, k1_zfmisc_1(k2_zfmisc_1(A_407, B_411))) | ~v1_funct_1(E_406))), inference(resolution, [status(thm)], [c_58, c_4850])).
% 48.76/37.70  tff(c_85865, plain, (![A_3072, B_3073, E_3074]: (k1_partfun1(A_3072, B_3073, '#skF_3', '#skF_1', E_3074, '#skF_5')=k5_relat_1(E_3074, '#skF_5') | ~m1_subset_1(E_3074, k1_zfmisc_1(k2_zfmisc_1(A_3072, B_3073))) | ~v1_funct_1(E_3074))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_4857])).
% 48.76/37.70  tff(c_85872, plain, (k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_1', '#skF_4', '#skF_5')=k5_relat_1('#skF_4', '#skF_5') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_62, c_85865])).
% 48.76/37.70  tff(c_85887, plain, (k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_1', '#skF_4', '#skF_5')=k5_relat_1('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_85872])).
% 48.76/37.70  tff(c_477, plain, (k1_relset_1('#skF_3', '#skF_1', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_58, c_456])).
% 48.76/37.70  tff(c_54, plain, (r1_tarski(k2_relset_1('#skF_2', '#skF_3', '#skF_4'), k1_relset_1('#skF_3', '#skF_1', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_163])).
% 48.76/37.70  tff(c_484, plain, (r1_tarski(k2_relset_1('#skF_2', '#skF_3', '#skF_4'), k1_relat_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_477, c_54])).
% 48.76/37.70  tff(c_190, plain, (![C_82, A_83, B_84]: (v4_relat_1(C_82, A_83) | ~m1_subset_1(C_82, k1_zfmisc_1(k2_zfmisc_1(A_83, B_84))))), inference(cnfTransformation, [status(thm)], [f_87])).
% 48.76/37.70  tff(c_211, plain, (v4_relat_1('#skF_5', '#skF_3')), inference(resolution, [status(thm)], [c_58, c_190])).
% 48.76/37.70  tff(c_90, plain, (r1_tarski('#skF_4', k2_zfmisc_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_62, c_76])).
% 48.76/37.70  tff(c_314, plain, (![A_104, C_105, B_106]: (r1_tarski(A_104, C_105) | ~r1_tarski(B_106, C_105) | ~r1_tarski(A_104, B_106))), inference(cnfTransformation, [status(thm)], [f_35])).
% 48.76/37.70  tff(c_330, plain, (![A_104]: (r1_tarski(A_104, k2_zfmisc_1('#skF_2', '#skF_3')) | ~r1_tarski(A_104, '#skF_4'))), inference(resolution, [status(thm)], [c_90, c_314])).
% 48.76/37.70  tff(c_12, plain, (![A_8, B_9]: (m1_subset_1(A_8, k1_zfmisc_1(B_9)) | ~r1_tarski(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_47])).
% 48.76/37.70  tff(c_4743, plain, (![B_397, C_398, A_399]: (k1_xboole_0=B_397 | v1_funct_2(C_398, A_399, B_397) | k1_relset_1(A_399, B_397, C_398)!=A_399 | ~m1_subset_1(C_398, k1_zfmisc_1(k2_zfmisc_1(A_399, B_397))))), inference(cnfTransformation, [status(thm)], [f_126])).
% 48.76/37.70  tff(c_85923, plain, (![B_3077, A_3078, A_3079]: (k1_xboole_0=B_3077 | v1_funct_2(A_3078, A_3079, B_3077) | k1_relset_1(A_3079, B_3077, A_3078)!=A_3079 | ~r1_tarski(A_3078, k2_zfmisc_1(A_3079, B_3077)))), inference(resolution, [status(thm)], [c_12, c_4743])).
% 48.76/37.70  tff(c_85988, plain, (![A_104]: (k1_xboole_0='#skF_3' | v1_funct_2(A_104, '#skF_2', '#skF_3') | k1_relset_1('#skF_2', '#skF_3', A_104)!='#skF_2' | ~r1_tarski(A_104, '#skF_4'))), inference(resolution, [status(thm)], [c_330, c_85923])).
% 48.76/37.70  tff(c_92555, plain, (k1_xboole_0='#skF_3'), inference(splitLeft, [status(thm)], [c_85988])).
% 48.76/37.70  tff(c_18, plain, (![B_14, A_13]: (r1_tarski(k1_relat_1(B_14), A_13) | ~v4_relat_1(B_14, A_13) | ~v1_relat_1(B_14))), inference(cnfTransformation, [status(thm)], [f_59])).
% 48.76/37.70  tff(c_5297, plain, (![A_446, A_447, B_448]: (r1_tarski(A_446, A_447) | ~r1_tarski(A_446, k1_relat_1(B_448)) | ~v4_relat_1(B_448, A_447) | ~v1_relat_1(B_448))), inference(resolution, [status(thm)], [c_18, c_314])).
% 48.76/37.70  tff(c_5314, plain, (![A_447]: (r1_tarski(k2_relset_1('#skF_2', '#skF_3', '#skF_4'), A_447) | ~v4_relat_1('#skF_5', A_447) | ~v1_relat_1('#skF_5'))), inference(resolution, [status(thm)], [c_484, c_5297])).
% 48.76/37.70  tff(c_5341, plain, (![A_449]: (r1_tarski(k2_relset_1('#skF_2', '#skF_3', '#skF_4'), A_449) | ~v4_relat_1('#skF_5', A_449))), inference(demodulation, [status(thm), theory('equality')], [c_122, c_5314])).
% 48.76/37.70  tff(c_332, plain, (![A_104, A_5]: (r1_tarski(A_104, A_5) | ~r1_tarski(A_104, k1_xboole_0))), inference(resolution, [status(thm)], [c_93, c_314])).
% 48.76/37.70  tff(c_5409, plain, (![A_5]: (r1_tarski(k2_relset_1('#skF_2', '#skF_3', '#skF_4'), A_5) | ~v4_relat_1('#skF_5', k1_xboole_0))), inference(resolution, [status(thm)], [c_5341, c_332])).
% 48.76/37.70  tff(c_69800, plain, (~v4_relat_1('#skF_5', k1_xboole_0)), inference(splitLeft, [status(thm)], [c_5409])).
% 48.76/37.70  tff(c_92582, plain, (~v4_relat_1('#skF_5', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_92555, c_69800])).
% 48.76/37.70  tff(c_92617, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_211, c_92582])).
% 48.76/37.70  tff(c_92619, plain, (k1_xboole_0!='#skF_3'), inference(splitRight, [status(thm)], [c_85988])).
% 48.76/37.70  tff(c_4907, plain, (![A_420, B_419, C_418, D_421, E_417]: (k1_partfun1(A_420, B_419, B_419, C_418, D_421, E_417)=k8_funct_2(A_420, B_419, C_418, D_421, E_417) | k1_xboole_0=B_419 | ~r1_tarski(k2_relset_1(A_420, B_419, D_421), k1_relset_1(B_419, C_418, E_417)) | ~m1_subset_1(E_417, k1_zfmisc_1(k2_zfmisc_1(B_419, C_418))) | ~v1_funct_1(E_417) | ~m1_subset_1(D_421, k1_zfmisc_1(k2_zfmisc_1(A_420, B_419))) | ~v1_funct_2(D_421, A_420, B_419) | ~v1_funct_1(D_421))), inference(cnfTransformation, [status(thm)], [f_108])).
% 48.76/37.70  tff(c_4916, plain, (![A_420, D_421]: (k1_partfun1(A_420, '#skF_3', '#skF_3', '#skF_1', D_421, '#skF_5')=k8_funct_2(A_420, '#skF_3', '#skF_1', D_421, '#skF_5') | k1_xboole_0='#skF_3' | ~r1_tarski(k2_relset_1(A_420, '#skF_3', D_421), k1_relat_1('#skF_5')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_1'))) | ~v1_funct_1('#skF_5') | ~m1_subset_1(D_421, k1_zfmisc_1(k2_zfmisc_1(A_420, '#skF_3'))) | ~v1_funct_2(D_421, A_420, '#skF_3') | ~v1_funct_1(D_421))), inference(superposition, [status(thm), theory('equality')], [c_477, c_4907])).
% 48.76/37.70  tff(c_4923, plain, (![A_420, D_421]: (k1_partfun1(A_420, '#skF_3', '#skF_3', '#skF_1', D_421, '#skF_5')=k8_funct_2(A_420, '#skF_3', '#skF_1', D_421, '#skF_5') | k1_xboole_0='#skF_3' | ~r1_tarski(k2_relset_1(A_420, '#skF_3', D_421), k1_relat_1('#skF_5')) | ~m1_subset_1(D_421, k1_zfmisc_1(k2_zfmisc_1(A_420, '#skF_3'))) | ~v1_funct_2(D_421, A_420, '#skF_3') | ~v1_funct_1(D_421))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_4916])).
% 48.76/37.70  tff(c_99401, plain, (![A_3483, D_3484]: (k1_partfun1(A_3483, '#skF_3', '#skF_3', '#skF_1', D_3484, '#skF_5')=k8_funct_2(A_3483, '#skF_3', '#skF_1', D_3484, '#skF_5') | ~r1_tarski(k2_relset_1(A_3483, '#skF_3', D_3484), k1_relat_1('#skF_5')) | ~m1_subset_1(D_3484, k1_zfmisc_1(k2_zfmisc_1(A_3483, '#skF_3'))) | ~v1_funct_2(D_3484, A_3483, '#skF_3') | ~v1_funct_1(D_3484))), inference(negUnitSimplification, [status(thm)], [c_92619, c_4923])).
% 48.76/37.70  tff(c_99408, plain, (k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_1', '#skF_4', '#skF_5')=k8_funct_2('#skF_2', '#skF_3', '#skF_1', '#skF_4', '#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_484, c_99401])).
% 48.76/37.70  tff(c_99414, plain, (k8_funct_2('#skF_2', '#skF_3', '#skF_1', '#skF_4', '#skF_5')=k5_relat_1('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_62, c_85887, c_99408])).
% 48.76/37.70  tff(c_50, plain, (k1_funct_1(k8_funct_2('#skF_2', '#skF_3', '#skF_1', '#skF_4', '#skF_5'), '#skF_6')!=k1_funct_1('#skF_5', k1_funct_1('#skF_4', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_163])).
% 48.76/37.70  tff(c_99671, plain, (k1_funct_1(k5_relat_1('#skF_4', '#skF_5'), '#skF_6')!=k1_funct_1('#skF_5', k1_funct_1('#skF_4', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_99414, c_50])).
% 48.76/37.70  tff(c_99678, plain, (~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5') | ~m1_subset_1('#skF_6', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_95410, c_99671])).
% 48.76/37.70  tff(c_99685, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_56, c_122, c_60, c_99678])).
% 48.76/37.70  tff(c_99706, plain, (![A_3486]: (r1_tarski(k2_relset_1('#skF_2', '#skF_3', '#skF_4'), A_3486))), inference(splitRight, [status(thm)], [c_5409])).
% 48.76/37.70  tff(c_126, plain, (![A_74, B_75]: (r2_hidden(A_74, B_75) | v1_xboole_0(B_75) | ~m1_subset_1(A_74, B_75))), inference(cnfTransformation, [status(thm)], [f_43])).
% 48.76/37.70  tff(c_22, plain, (![B_20, A_19]: (~r1_tarski(B_20, A_19) | ~r2_hidden(A_19, B_20))), inference(cnfTransformation, [status(thm)], [f_77])).
% 48.76/37.70  tff(c_130, plain, (![B_75, A_74]: (~r1_tarski(B_75, A_74) | v1_xboole_0(B_75) | ~m1_subset_1(A_74, B_75))), inference(resolution, [status(thm)], [c_126, c_22])).
% 48.76/37.70  tff(c_99793, plain, (![A_3486]: (v1_xboole_0(k2_relset_1('#skF_2', '#skF_3', '#skF_4')) | ~m1_subset_1(A_3486, k2_relset_1('#skF_2', '#skF_3', '#skF_4')))), inference(resolution, [status(thm)], [c_99706, c_130])).
% 48.76/37.70  tff(c_115670, plain, (![A_4106]: (~m1_subset_1(A_4106, k2_relset_1('#skF_2', '#skF_3', '#skF_4')))), inference(splitLeft, [status(thm)], [c_99793])).
% 48.76/37.70  tff(c_115680, plain, $false, inference(resolution, [status(thm)], [c_46, c_115670])).
% 48.76/37.70  tff(c_115681, plain, (v1_xboole_0(k2_relset_1('#skF_2', '#skF_3', '#skF_4'))), inference(splitRight, [status(thm)], [c_99793])).
% 48.76/37.70  tff(c_115685, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_115681, c_2])).
% 48.76/37.70  tff(c_99854, plain, (![A_3493, B_3494, E_3495]: (k1_partfun1(A_3493, B_3494, '#skF_3', '#skF_1', E_3495, '#skF_5')=k5_relat_1(E_3495, '#skF_5') | ~m1_subset_1(E_3495, k1_zfmisc_1(k2_zfmisc_1(A_3493, B_3494))) | ~v1_funct_1(E_3495))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_4857])).
% 48.76/37.70  tff(c_99861, plain, (k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_1', '#skF_4', '#skF_5')=k5_relat_1('#skF_4', '#skF_5') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_62, c_99854])).
% 48.76/37.70  tff(c_99876, plain, (k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_1', '#skF_4', '#skF_5')=k5_relat_1('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_99861])).
% 48.76/37.70  tff(c_99687, plain, (v4_relat_1('#skF_5', k1_xboole_0)), inference(splitRight, [status(thm)], [c_5409])).
% 48.76/37.70  tff(c_333, plain, (![A_107, A_108]: (r1_tarski(A_107, A_108) | ~r1_tarski(A_107, k1_xboole_0))), inference(resolution, [status(thm)], [c_93, c_314])).
% 48.76/37.70  tff(c_4617, plain, (![B_392, A_393]: (r1_tarski(k1_relat_1(B_392), A_393) | ~v4_relat_1(B_392, k1_xboole_0) | ~v1_relat_1(B_392))), inference(resolution, [status(thm)], [c_18, c_333])).
% 48.76/37.70  tff(c_16, plain, (![B_14, A_13]: (v4_relat_1(B_14, A_13) | ~r1_tarski(k1_relat_1(B_14), A_13) | ~v1_relat_1(B_14))), inference(cnfTransformation, [status(thm)], [f_59])).
% 48.76/37.70  tff(c_4671, plain, (![B_392, A_393]: (v4_relat_1(B_392, A_393) | ~v4_relat_1(B_392, k1_xboole_0) | ~v1_relat_1(B_392))), inference(resolution, [status(thm)], [c_4617, c_16])).
% 48.76/37.70  tff(c_99689, plain, (![A_393]: (v4_relat_1('#skF_5', A_393) | ~v1_relat_1('#skF_5'))), inference(resolution, [status(thm)], [c_99687, c_4671])).
% 48.76/37.70  tff(c_99692, plain, (![A_393]: (v4_relat_1('#skF_5', A_393))), inference(demodulation, [status(thm), theory('equality')], [c_122, c_99689])).
% 48.76/37.70  tff(c_92, plain, (![B_64]: (r1_tarski(o_1_1_funct_2(k1_zfmisc_1(B_64)), B_64))), inference(resolution, [status(thm)], [c_46, c_76])).
% 48.76/37.70  tff(c_596, plain, (![A_137, B_138]: (r1_tarski(A_137, B_138) | ~r1_tarski(A_137, o_1_1_funct_2(k1_zfmisc_1(B_138))))), inference(resolution, [status(thm)], [c_92, c_314])).
% 48.76/37.70  tff(c_111846, plain, (![B_4044, B_4045]: (r1_tarski(k1_relat_1(B_4044), B_4045) | ~v4_relat_1(B_4044, o_1_1_funct_2(k1_zfmisc_1(B_4045))) | ~v1_relat_1(B_4044))), inference(resolution, [status(thm)], [c_18, c_596])).
% 48.76/37.70  tff(c_111942, plain, (![B_4045]: (r1_tarski(k1_relat_1('#skF_5'), B_4045) | ~v1_relat_1('#skF_5'))), inference(resolution, [status(thm)], [c_99692, c_111846])).
% 48.76/37.70  tff(c_112058, plain, (![B_4046]: (r1_tarski(k1_relat_1('#skF_5'), B_4046))), inference(demodulation, [status(thm), theory('equality')], [c_122, c_111942])).
% 48.76/37.70  tff(c_112192, plain, (![B_4046]: (v1_xboole_0(k1_relat_1('#skF_5')) | ~m1_subset_1(B_4046, k1_relat_1('#skF_5')))), inference(resolution, [status(thm)], [c_112058, c_130])).
% 48.76/37.70  tff(c_112629, plain, (![B_4052]: (~m1_subset_1(B_4052, k1_relat_1('#skF_5')))), inference(splitLeft, [status(thm)], [c_112192])).
% 48.76/37.70  tff(c_112639, plain, $false, inference(resolution, [status(thm)], [c_46, c_112629])).
% 48.76/37.70  tff(c_112640, plain, (v1_xboole_0(k1_relat_1('#skF_5'))), inference(splitRight, [status(thm)], [c_112192])).
% 48.76/37.70  tff(c_112644, plain, (k1_relat_1('#skF_5')=k1_xboole_0), inference(resolution, [status(thm)], [c_112640, c_2])).
% 48.76/37.70  tff(c_4687, plain, (k1_xboole_0='#skF_1' | k1_relset_1('#skF_3', '#skF_1', '#skF_5')='#skF_3' | ~v1_funct_2('#skF_5', '#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_58, c_4677])).
% 48.76/37.70  tff(c_4701, plain, (k1_xboole_0='#skF_1' | k1_relat_1('#skF_5')='#skF_3' | ~v1_funct_2('#skF_5', '#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_477, c_4687])).
% 48.76/37.70  tff(c_4740, plain, (~v1_funct_2('#skF_5', '#skF_3', '#skF_1')), inference(splitLeft, [status(thm)], [c_4701])).
% 48.76/37.70  tff(c_4753, plain, (k1_xboole_0='#skF_1' | v1_funct_2('#skF_5', '#skF_3', '#skF_1') | k1_relset_1('#skF_3', '#skF_1', '#skF_5')!='#skF_3'), inference(resolution, [status(thm)], [c_58, c_4743])).
% 48.76/37.70  tff(c_4767, plain, (k1_xboole_0='#skF_1' | v1_funct_2('#skF_5', '#skF_3', '#skF_1') | k1_relat_1('#skF_5')!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_477, c_4753])).
% 48.76/37.70  tff(c_4768, plain, (k1_xboole_0='#skF_1' | k1_relat_1('#skF_5')!='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_4740, c_4767])).
% 48.76/37.70  tff(c_4772, plain, (k1_relat_1('#skF_5')!='#skF_3'), inference(splitLeft, [status(thm)], [c_4768])).
% 48.76/37.70  tff(c_112671, plain, (k1_xboole_0!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_112644, c_4772])).
% 48.76/37.70  tff(c_122911, plain, (![A_420, D_421]: (k1_partfun1(A_420, '#skF_3', '#skF_3', '#skF_1', D_421, '#skF_5')=k8_funct_2(A_420, '#skF_3', '#skF_1', D_421, '#skF_5') | k1_xboole_0='#skF_3' | ~r1_tarski(k2_relset_1(A_420, '#skF_3', D_421), k1_xboole_0) | ~m1_subset_1(D_421, k1_zfmisc_1(k2_zfmisc_1(A_420, '#skF_3'))) | ~v1_funct_2(D_421, A_420, '#skF_3') | ~v1_funct_1(D_421))), inference(demodulation, [status(thm), theory('equality')], [c_112644, c_4923])).
% 48.76/37.70  tff(c_122913, plain, (![A_4345, D_4346]: (k1_partfun1(A_4345, '#skF_3', '#skF_3', '#skF_1', D_4346, '#skF_5')=k8_funct_2(A_4345, '#skF_3', '#skF_1', D_4346, '#skF_5') | ~r1_tarski(k2_relset_1(A_4345, '#skF_3', D_4346), k1_xboole_0) | ~m1_subset_1(D_4346, k1_zfmisc_1(k2_zfmisc_1(A_4345, '#skF_3'))) | ~v1_funct_2(D_4346, A_4345, '#skF_3') | ~v1_funct_1(D_4346))), inference(negUnitSimplification, [status(thm)], [c_112671, c_122911])).
% 48.76/37.70  tff(c_122924, plain, (k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_1', '#skF_4', '#skF_5')=k8_funct_2('#skF_2', '#skF_3', '#skF_1', '#skF_4', '#skF_5') | ~r1_tarski(k2_relset_1('#skF_2', '#skF_3', '#skF_4'), k1_xboole_0) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_62, c_122913])).
% 48.76/37.70  tff(c_122937, plain, (k8_funct_2('#skF_2', '#skF_3', '#skF_1', '#skF_4', '#skF_5')=k5_relat_1('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_93, c_115685, c_99876, c_122924])).
% 48.76/37.70  tff(c_122940, plain, (k1_funct_1(k5_relat_1('#skF_4', '#skF_5'), '#skF_6')!=k1_funct_1('#skF_5', k1_funct_1('#skF_4', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_122937, c_50])).
% 48.76/37.70  tff(c_122947, plain, (~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5') | ~m1_subset_1('#skF_6', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_119309, c_122940])).
% 48.76/37.70  tff(c_122954, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_56, c_122, c_60, c_122947])).
% 48.76/37.70  tff(c_122955, plain, (k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_4768])).
% 48.76/37.70  tff(c_122981, plain, (![A_5]: (r1_tarski('#skF_1', A_5))), inference(demodulation, [status(thm), theory('equality')], [c_122955, c_93])).
% 48.76/37.70  tff(c_122985, plain, ('#skF_2'!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_122955, c_52])).
% 48.76/37.70  tff(c_123044, plain, (![B_4348, C_4349, A_4350]: (k1_funct_1(k5_relat_1(B_4348, C_4349), A_4350)=k1_funct_1(C_4349, k1_funct_1(B_4348, A_4350)) | ~r2_hidden(A_4350, k1_relat_1(B_4348)) | ~v1_funct_1(C_4349) | ~v1_relat_1(C_4349) | ~v1_funct_1(B_4348) | ~v1_relat_1(B_4348))), inference(cnfTransformation, [status(thm)], [f_72])).
% 48.76/37.70  tff(c_179217, plain, (![B_5873, C_5874, A_5875]: (k1_funct_1(k5_relat_1(B_5873, C_5874), A_5875)=k1_funct_1(C_5874, k1_funct_1(B_5873, A_5875)) | ~v1_funct_1(C_5874) | ~v1_relat_1(C_5874) | ~v1_funct_1(B_5873) | ~v1_relat_1(B_5873) | v1_xboole_0(k1_relat_1(B_5873)) | ~m1_subset_1(A_5875, k1_relat_1(B_5873)))), inference(resolution, [status(thm)], [c_8, c_123044])).
% 48.76/37.70  tff(c_179223, plain, (![C_5874, A_5875]: (k1_funct_1(k5_relat_1('#skF_4', C_5874), A_5875)=k1_funct_1(C_5874, k1_funct_1('#skF_4', A_5875)) | ~v1_funct_1(C_5874) | ~v1_relat_1(C_5874) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4') | v1_xboole_0(k1_relat_1('#skF_4')) | ~m1_subset_1(A_5875, '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_4705, c_179217])).
% 48.76/37.70  tff(c_179233, plain, (![C_5874, A_5875]: (k1_funct_1(k5_relat_1('#skF_4', C_5874), A_5875)=k1_funct_1(C_5874, k1_funct_1('#skF_4', A_5875)) | ~v1_funct_1(C_5874) | ~v1_relat_1(C_5874) | v1_xboole_0('#skF_2') | ~m1_subset_1(A_5875, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_4705, c_121, c_66, c_179223])).
% 48.76/37.70  tff(c_194517, plain, (v1_xboole_0('#skF_2')), inference(splitLeft, [status(thm)], [c_179233])).
% 48.76/37.70  tff(c_122984, plain, (![A_1]: (A_1='#skF_1' | ~v1_xboole_0(A_1))), inference(demodulation, [status(thm), theory('equality')], [c_122955, c_2])).
% 48.76/37.70  tff(c_194520, plain, ('#skF_2'='#skF_1'), inference(resolution, [status(thm)], [c_194517, c_122984])).
% 48.76/37.70  tff(c_194524, plain, $false, inference(negUnitSimplification, [status(thm)], [c_122985, c_194520])).
% 48.76/37.70  tff(c_194525, plain, (![C_5874, A_5875]: (k1_funct_1(k5_relat_1('#skF_4', C_5874), A_5875)=k1_funct_1(C_5874, k1_funct_1('#skF_4', A_5875)) | ~v1_funct_1(C_5874) | ~v1_relat_1(C_5874) | ~m1_subset_1(A_5875, '#skF_2'))), inference(splitRight, [status(thm)], [c_179233])).
% 48.76/37.70  tff(c_122956, plain, (k1_relat_1('#skF_5')='#skF_3'), inference(splitRight, [status(thm)], [c_4768])).
% 48.76/37.70  tff(c_122993, plain, (r1_tarski(k2_relset_1('#skF_2', '#skF_3', '#skF_4'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_122956, c_484])).
% 48.76/37.70  tff(c_123158, plain, (![B_4363, F_4361, E_4358, D_4360, A_4359, C_4362]: (k1_partfun1(A_4359, B_4363, C_4362, D_4360, E_4358, F_4361)=k5_relat_1(E_4358, F_4361) | ~m1_subset_1(F_4361, k1_zfmisc_1(k2_zfmisc_1(C_4362, D_4360))) | ~v1_funct_1(F_4361) | ~m1_subset_1(E_4358, k1_zfmisc_1(k2_zfmisc_1(A_4359, B_4363))) | ~v1_funct_1(E_4358))), inference(cnfTransformation, [status(thm)], [f_138])).
% 48.76/37.70  tff(c_123168, plain, (![A_4359, B_4363, E_4358]: (k1_partfun1(A_4359, B_4363, '#skF_3', '#skF_1', E_4358, '#skF_5')=k5_relat_1(E_4358, '#skF_5') | ~v1_funct_1('#skF_5') | ~m1_subset_1(E_4358, k1_zfmisc_1(k2_zfmisc_1(A_4359, B_4363))) | ~v1_funct_1(E_4358))), inference(resolution, [status(thm)], [c_58, c_123158])).
% 48.76/37.70  tff(c_153387, plain, (![A_5204, B_5205, E_5206]: (k1_partfun1(A_5204, B_5205, '#skF_3', '#skF_1', E_5206, '#skF_5')=k5_relat_1(E_5206, '#skF_5') | ~m1_subset_1(E_5206, k1_zfmisc_1(k2_zfmisc_1(A_5204, B_5205))) | ~v1_funct_1(E_5206))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_123168])).
% 48.76/37.70  tff(c_153398, plain, (k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_1', '#skF_4', '#skF_5')=k5_relat_1('#skF_4', '#skF_5') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_62, c_153387])).
% 48.76/37.70  tff(c_153410, plain, (k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_1', '#skF_4', '#skF_5')=k5_relat_1('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_153398])).
% 48.76/37.70  tff(c_479, plain, (![A_123, B_124]: (k1_relset_1(A_123, B_124, k1_xboole_0)=k1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_6, c_456])).
% 48.76/37.70  tff(c_716, plain, (![C_141, B_142]: (v1_funct_2(C_141, k1_xboole_0, B_142) | k1_relset_1(k1_xboole_0, B_142, C_141)!=k1_xboole_0 | ~m1_subset_1(C_141, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_142))))), inference(cnfTransformation, [status(thm)], [f_126])).
% 48.76/37.70  tff(c_728, plain, (![B_142]: (v1_funct_2(k1_xboole_0, k1_xboole_0, B_142) | k1_relset_1(k1_xboole_0, B_142, k1_xboole_0)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_716])).
% 48.76/37.70  tff(c_732, plain, (![B_142]: (v1_funct_2(k1_xboole_0, k1_xboole_0, B_142) | k1_relat_1(k1_xboole_0)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_479, c_728])).
% 48.76/37.70  tff(c_736, plain, (k1_relat_1(k1_xboole_0)!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_732])).
% 48.76/37.70  tff(c_124, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_101])).
% 48.76/37.70  tff(c_213, plain, (![A_83]: (v4_relat_1(k1_xboole_0, A_83))), inference(resolution, [status(thm)], [c_6, c_190])).
% 48.76/37.70  tff(c_3673, plain, (![B_355, B_356]: (r1_tarski(k1_relat_1(B_355), B_356) | ~v4_relat_1(B_355, o_1_1_funct_2(k1_zfmisc_1(B_356))) | ~v1_relat_1(B_355))), inference(resolution, [status(thm)], [c_18, c_596])).
% 48.76/37.70  tff(c_3756, plain, (![B_356]: (r1_tarski(k1_relat_1(k1_xboole_0), B_356) | ~v1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_213, c_3673])).
% 48.76/37.70  tff(c_3815, plain, (![B_357]: (r1_tarski(k1_relat_1(k1_xboole_0), B_357))), inference(demodulation, [status(thm), theory('equality')], [c_124, c_3756])).
% 48.76/37.70  tff(c_3942, plain, (![B_357]: (v1_xboole_0(k1_relat_1(k1_xboole_0)) | ~m1_subset_1(B_357, k1_relat_1(k1_xboole_0)))), inference(resolution, [status(thm)], [c_3815, c_130])).
% 48.76/37.70  tff(c_4504, plain, (![B_374]: (~m1_subset_1(B_374, k1_relat_1(k1_xboole_0)))), inference(splitLeft, [status(thm)], [c_3942])).
% 48.76/37.70  tff(c_4509, plain, $false, inference(resolution, [status(thm)], [c_46, c_4504])).
% 48.76/37.70  tff(c_4510, plain, (v1_xboole_0(k1_relat_1(k1_xboole_0))), inference(splitRight, [status(thm)], [c_3942])).
% 48.76/37.70  tff(c_4513, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_4510, c_2])).
% 48.76/37.70  tff(c_4517, plain, $false, inference(negUnitSimplification, [status(thm)], [c_736, c_4513])).
% 48.76/37.70  tff(c_4518, plain, (![B_142]: (v1_funct_2(k1_xboole_0, k1_xboole_0, B_142))), inference(splitRight, [status(thm)], [c_732])).
% 48.76/37.70  tff(c_122965, plain, (![B_142]: (v1_funct_2('#skF_1', '#skF_1', B_142))), inference(demodulation, [status(thm), theory('equality')], [c_122955, c_122955, c_4518])).
% 48.76/37.70  tff(c_91, plain, (r1_tarski('#skF_5', k2_zfmisc_1('#skF_3', '#skF_1'))), inference(resolution, [status(thm)], [c_58, c_76])).
% 48.76/37.70  tff(c_331, plain, (![A_104]: (r1_tarski(A_104, k2_zfmisc_1('#skF_3', '#skF_1')) | ~r1_tarski(A_104, '#skF_5'))), inference(resolution, [status(thm)], [c_91, c_314])).
% 48.76/37.70  tff(c_553, plain, (![C_132, A_133]: (k1_xboole_0=C_132 | ~v1_funct_2(C_132, A_133, k1_xboole_0) | k1_xboole_0=A_133 | ~m1_subset_1(C_132, k1_zfmisc_1(k2_zfmisc_1(A_133, k1_xboole_0))))), inference(cnfTransformation, [status(thm)], [f_126])).
% 48.76/37.70  tff(c_566, plain, (![A_8, A_133]: (k1_xboole_0=A_8 | ~v1_funct_2(A_8, A_133, k1_xboole_0) | k1_xboole_0=A_133 | ~r1_tarski(A_8, k2_zfmisc_1(A_133, k1_xboole_0)))), inference(resolution, [status(thm)], [c_12, c_553])).
% 48.76/37.70  tff(c_153559, plain, (![A_5214, A_5215]: (A_5214='#skF_1' | ~v1_funct_2(A_5214, A_5215, '#skF_1') | A_5215='#skF_1' | ~r1_tarski(A_5214, k2_zfmisc_1(A_5215, '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_122955, c_122955, c_122955, c_122955, c_566])).
% 48.76/37.70  tff(c_153594, plain, (![A_104]: (A_104='#skF_1' | ~v1_funct_2(A_104, '#skF_3', '#skF_1') | '#skF_3'='#skF_1' | ~r1_tarski(A_104, '#skF_5'))), inference(resolution, [status(thm)], [c_331, c_153559])).
% 48.76/37.70  tff(c_181076, plain, ('#skF_3'='#skF_1'), inference(splitLeft, [status(thm)], [c_153594])).
% 48.76/37.70  tff(c_123004, plain, (![A_13]: (v4_relat_1('#skF_5', A_13) | ~r1_tarski('#skF_3', A_13) | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_122956, c_16])).
% 48.76/37.70  tff(c_123325, plain, (![A_4381]: (v4_relat_1('#skF_5', A_4381) | ~r1_tarski('#skF_3', A_4381))), inference(demodulation, [status(thm), theory('equality')], [c_122, c_123004])).
% 48.76/37.70  tff(c_408, plain, (![A_121]: (r1_tarski(A_121, k2_zfmisc_1('#skF_3', '#skF_1')) | ~r1_tarski(A_121, '#skF_5'))), inference(resolution, [status(thm)], [c_91, c_314])).
% 48.76/37.70  tff(c_120, plain, (![A_8, A_70, B_71]: (v1_relat_1(A_8) | ~r1_tarski(A_8, k2_zfmisc_1(A_70, B_71)))), inference(resolution, [status(thm)], [c_12, c_101])).
% 48.76/37.70  tff(c_433, plain, (![A_122]: (v1_relat_1(A_122) | ~r1_tarski(A_122, '#skF_5'))), inference(resolution, [status(thm)], [c_408, c_120])).
% 48.76/37.70  tff(c_452, plain, (![B_14]: (v1_relat_1(k1_relat_1(B_14)) | ~v4_relat_1(B_14, '#skF_5') | ~v1_relat_1(B_14))), inference(resolution, [status(thm)], [c_18, c_433])).
% 48.76/37.70  tff(c_122998, plain, (v1_relat_1('#skF_3') | ~v4_relat_1('#skF_5', '#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_122956, c_452])).
% 48.76/37.70  tff(c_123011, plain, (v1_relat_1('#skF_3') | ~v4_relat_1('#skF_5', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_122, c_122998])).
% 48.76/37.70  tff(c_123235, plain, (~v4_relat_1('#skF_5', '#skF_5')), inference(splitLeft, [status(thm)], [c_123011])).
% 48.76/37.70  tff(c_123333, plain, (~r1_tarski('#skF_3', '#skF_5')), inference(resolution, [status(thm)], [c_123325, c_123235])).
% 48.76/37.70  tff(c_127038, plain, (![B_4561, C_4562, A_4563]: (k1_funct_1(k5_relat_1(B_4561, C_4562), A_4563)=k1_funct_1(C_4562, k1_funct_1(B_4561, A_4563)) | ~v1_funct_1(C_4562) | ~v1_relat_1(C_4562) | ~v1_funct_1(B_4561) | ~v1_relat_1(B_4561) | v1_xboole_0(k1_relat_1(B_4561)) | ~m1_subset_1(A_4563, k1_relat_1(B_4561)))), inference(resolution, [status(thm)], [c_8, c_123044])).
% 48.76/37.70  tff(c_127044, plain, (![C_4562, A_4563]: (k1_funct_1(k5_relat_1('#skF_4', C_4562), A_4563)=k1_funct_1(C_4562, k1_funct_1('#skF_4', A_4563)) | ~v1_funct_1(C_4562) | ~v1_relat_1(C_4562) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4') | v1_xboole_0(k1_relat_1('#skF_4')) | ~m1_subset_1(A_4563, '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_4705, c_127038])).
% 48.76/37.70  tff(c_127054, plain, (![C_4562, A_4563]: (k1_funct_1(k5_relat_1('#skF_4', C_4562), A_4563)=k1_funct_1(C_4562, k1_funct_1('#skF_4', A_4563)) | ~v1_funct_1(C_4562) | ~v1_relat_1(C_4562) | v1_xboole_0('#skF_2') | ~m1_subset_1(A_4563, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_4705, c_121, c_66, c_127044])).
% 48.76/37.70  tff(c_147281, plain, (v1_xboole_0('#skF_2')), inference(splitLeft, [status(thm)], [c_127054])).
% 48.76/37.70  tff(c_147284, plain, ('#skF_2'='#skF_1'), inference(resolution, [status(thm)], [c_147281, c_122984])).
% 48.76/37.70  tff(c_147288, plain, $false, inference(negUnitSimplification, [status(thm)], [c_122985, c_147284])).
% 48.76/37.70  tff(c_147289, plain, (![C_4562, A_4563]: (k1_funct_1(k5_relat_1('#skF_4', C_4562), A_4563)=k1_funct_1(C_4562, k1_funct_1('#skF_4', A_4563)) | ~v1_funct_1(C_4562) | ~v1_relat_1(C_4562) | ~m1_subset_1(A_4563, '#skF_2'))), inference(splitRight, [status(thm)], [c_127054])).
% 48.76/37.70  tff(c_123453, plain, (![A_4389, B_4390, E_4391]: (k1_partfun1(A_4389, B_4390, '#skF_3', '#skF_1', E_4391, '#skF_5')=k5_relat_1(E_4391, '#skF_5') | ~m1_subset_1(E_4391, k1_zfmisc_1(k2_zfmisc_1(A_4389, B_4390))) | ~v1_funct_1(E_4391))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_123168])).
% 48.76/37.70  tff(c_123464, plain, (k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_1', '#skF_4', '#skF_5')=k5_relat_1('#skF_4', '#skF_5') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_62, c_123453])).
% 48.76/37.70  tff(c_123476, plain, (k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_1', '#skF_4', '#skF_5')=k5_relat_1('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_123464])).
% 48.76/37.70  tff(c_123717, plain, (![A_4406, A_4407]: (A_4406='#skF_1' | ~v1_funct_2(A_4406, A_4407, '#skF_1') | A_4407='#skF_1' | ~r1_tarski(A_4406, k2_zfmisc_1(A_4407, '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_122955, c_122955, c_122955, c_122955, c_566])).
% 48.76/37.70  tff(c_123752, plain, (![A_104]: (A_104='#skF_1' | ~v1_funct_2(A_104, '#skF_3', '#skF_1') | '#skF_3'='#skF_1' | ~r1_tarski(A_104, '#skF_5'))), inference(resolution, [status(thm)], [c_331, c_123717])).
% 48.76/37.70  tff(c_126703, plain, ('#skF_3'='#skF_1'), inference(splitLeft, [status(thm)], [c_123752])).
% 48.76/37.70  tff(c_123015, plain, (![A_13]: (v4_relat_1('#skF_5', A_13) | ~r1_tarski('#skF_3', A_13))), inference(demodulation, [status(thm), theory('equality')], [c_122, c_123004])).
% 48.76/37.70  tff(c_123603, plain, (![A_4398, A_4399, B_4400]: (r1_tarski(A_4398, A_4399) | ~r1_tarski(A_4398, k1_relat_1(B_4400)) | ~v4_relat_1(B_4400, A_4399) | ~v1_relat_1(B_4400))), inference(resolution, [status(thm)], [c_18, c_314])).
% 48.76/37.70  tff(c_123616, plain, (![A_4398, A_4399]: (r1_tarski(A_4398, A_4399) | ~r1_tarski(A_4398, '#skF_3') | ~v4_relat_1('#skF_5', A_4399) | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_122956, c_123603])).
% 48.76/37.70  tff(c_123904, plain, (![A_4415, A_4416]: (r1_tarski(A_4415, A_4416) | ~r1_tarski(A_4415, '#skF_3') | ~v4_relat_1('#skF_5', A_4416))), inference(demodulation, [status(thm), theory('equality')], [c_122, c_123616])).
% 48.76/37.70  tff(c_123945, plain, (![A_4417]: (r1_tarski(o_1_1_funct_2(k1_zfmisc_1('#skF_3')), A_4417) | ~v4_relat_1('#skF_5', A_4417))), inference(resolution, [status(thm)], [c_92, c_123904])).
% 48.76/37.70  tff(c_329, plain, (![A_104, B_64]: (r1_tarski(A_104, B_64) | ~r1_tarski(A_104, o_1_1_funct_2(k1_zfmisc_1(B_64))))), inference(resolution, [status(thm)], [c_92, c_314])).
% 48.76/37.70  tff(c_125005, plain, (![B_4469]: (r1_tarski(o_1_1_funct_2(k1_zfmisc_1('#skF_3')), B_4469) | ~v4_relat_1('#skF_5', o_1_1_funct_2(k1_zfmisc_1(B_4469))))), inference(resolution, [status(thm)], [c_123945, c_329])).
% 48.76/37.70  tff(c_125392, plain, (![B_4481]: (r1_tarski(o_1_1_funct_2(k1_zfmisc_1('#skF_3')), B_4481) | ~r1_tarski('#skF_3', o_1_1_funct_2(k1_zfmisc_1(B_4481))))), inference(resolution, [status(thm)], [c_123015, c_125005])).
% 48.76/37.70  tff(c_432, plain, (![A_121]: (v1_relat_1(A_121) | ~r1_tarski(A_121, '#skF_5'))), inference(resolution, [status(thm)], [c_408, c_120])).
% 48.76/37.70  tff(c_125492, plain, (v1_relat_1(o_1_1_funct_2(k1_zfmisc_1('#skF_3'))) | ~r1_tarski('#skF_3', o_1_1_funct_2(k1_zfmisc_1('#skF_5')))), inference(resolution, [status(thm)], [c_125392, c_432])).
% 48.76/37.70  tff(c_125499, plain, (~r1_tarski('#skF_3', o_1_1_funct_2(k1_zfmisc_1('#skF_5')))), inference(splitLeft, [status(thm)], [c_125492])).
% 48.76/37.70  tff(c_126716, plain, (~r1_tarski('#skF_1', o_1_1_funct_2(k1_zfmisc_1('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_126703, c_125499])).
% 48.76/37.70  tff(c_126779, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_122981, c_126716])).
% 48.76/37.70  tff(c_126781, plain, ('#skF_3'!='#skF_1'), inference(splitRight, [status(thm)], [c_123752])).
% 48.76/37.70  tff(c_122994, plain, (k1_relset_1('#skF_3', '#skF_1', '#skF_5')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_122956, c_477])).
% 48.76/37.70  tff(c_32, plain, (![D_33, E_35, A_30, C_32, B_31]: (k1_partfun1(A_30, B_31, B_31, C_32, D_33, E_35)=k8_funct_2(A_30, B_31, C_32, D_33, E_35) | k1_xboole_0=B_31 | ~r1_tarski(k2_relset_1(A_30, B_31, D_33), k1_relset_1(B_31, C_32, E_35)) | ~m1_subset_1(E_35, k1_zfmisc_1(k2_zfmisc_1(B_31, C_32))) | ~v1_funct_1(E_35) | ~m1_subset_1(D_33, k1_zfmisc_1(k2_zfmisc_1(A_30, B_31))) | ~v1_funct_2(D_33, A_30, B_31) | ~v1_funct_1(D_33))), inference(cnfTransformation, [status(thm)], [f_108])).
% 48.76/37.70  tff(c_123237, plain, (![B_4369, E_4367, D_4371, C_4368, A_4370]: (k1_partfun1(A_4370, B_4369, B_4369, C_4368, D_4371, E_4367)=k8_funct_2(A_4370, B_4369, C_4368, D_4371, E_4367) | B_4369='#skF_1' | ~r1_tarski(k2_relset_1(A_4370, B_4369, D_4371), k1_relset_1(B_4369, C_4368, E_4367)) | ~m1_subset_1(E_4367, k1_zfmisc_1(k2_zfmisc_1(B_4369, C_4368))) | ~v1_funct_1(E_4367) | ~m1_subset_1(D_4371, k1_zfmisc_1(k2_zfmisc_1(A_4370, B_4369))) | ~v1_funct_2(D_4371, A_4370, B_4369) | ~v1_funct_1(D_4371))), inference(demodulation, [status(thm), theory('equality')], [c_122955, c_32])).
% 48.76/37.70  tff(c_123243, plain, (![A_4370, D_4371]: (k1_partfun1(A_4370, '#skF_3', '#skF_3', '#skF_1', D_4371, '#skF_5')=k8_funct_2(A_4370, '#skF_3', '#skF_1', D_4371, '#skF_5') | '#skF_3'='#skF_1' | ~r1_tarski(k2_relset_1(A_4370, '#skF_3', D_4371), '#skF_3') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_1'))) | ~v1_funct_1('#skF_5') | ~m1_subset_1(D_4371, k1_zfmisc_1(k2_zfmisc_1(A_4370, '#skF_3'))) | ~v1_funct_2(D_4371, A_4370, '#skF_3') | ~v1_funct_1(D_4371))), inference(superposition, [status(thm), theory('equality')], [c_122994, c_123237])).
% 48.76/37.70  tff(c_123250, plain, (![A_4370, D_4371]: (k1_partfun1(A_4370, '#skF_3', '#skF_3', '#skF_1', D_4371, '#skF_5')=k8_funct_2(A_4370, '#skF_3', '#skF_1', D_4371, '#skF_5') | '#skF_3'='#skF_1' | ~r1_tarski(k2_relset_1(A_4370, '#skF_3', D_4371), '#skF_3') | ~m1_subset_1(D_4371, k1_zfmisc_1(k2_zfmisc_1(A_4370, '#skF_3'))) | ~v1_funct_2(D_4371, A_4370, '#skF_3') | ~v1_funct_1(D_4371))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_123243])).
% 48.76/37.70  tff(c_152976, plain, (![A_5175, D_5176]: (k1_partfun1(A_5175, '#skF_3', '#skF_3', '#skF_1', D_5176, '#skF_5')=k8_funct_2(A_5175, '#skF_3', '#skF_1', D_5176, '#skF_5') | ~r1_tarski(k2_relset_1(A_5175, '#skF_3', D_5176), '#skF_3') | ~m1_subset_1(D_5176, k1_zfmisc_1(k2_zfmisc_1(A_5175, '#skF_3'))) | ~v1_funct_2(D_5176, A_5175, '#skF_3') | ~v1_funct_1(D_5176))), inference(negUnitSimplification, [status(thm)], [c_126781, c_123250])).
% 48.76/37.70  tff(c_152991, plain, (k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_1', '#skF_4', '#skF_5')=k8_funct_2('#skF_2', '#skF_3', '#skF_1', '#skF_4', '#skF_5') | ~r1_tarski(k2_relset_1('#skF_2', '#skF_3', '#skF_4'), '#skF_3') | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_62, c_152976])).
% 48.76/37.70  tff(c_153001, plain, (k8_funct_2('#skF_2', '#skF_3', '#skF_1', '#skF_4', '#skF_5')=k5_relat_1('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_122993, c_123476, c_152991])).
% 48.76/37.70  tff(c_153019, plain, (k1_funct_1(k5_relat_1('#skF_4', '#skF_5'), '#skF_6')!=k1_funct_1('#skF_5', k1_funct_1('#skF_4', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_153001, c_50])).
% 48.76/37.70  tff(c_153026, plain, (~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5') | ~m1_subset_1('#skF_6', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_147289, c_153019])).
% 48.76/37.70  tff(c_153033, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_56, c_122, c_60, c_153026])).
% 48.76/37.70  tff(c_153035, plain, (r1_tarski('#skF_3', o_1_1_funct_2(k1_zfmisc_1('#skF_5')))), inference(splitRight, [status(thm)], [c_125492])).
% 48.76/37.70  tff(c_153038, plain, (r1_tarski('#skF_3', '#skF_5')), inference(resolution, [status(thm)], [c_153035, c_329])).
% 48.76/37.70  tff(c_153047, plain, $false, inference(negUnitSimplification, [status(thm)], [c_123333, c_153038])).
% 48.76/37.70  tff(c_153049, plain, (v4_relat_1('#skF_5', '#skF_5')), inference(splitRight, [status(thm)], [c_123011])).
% 48.76/37.70  tff(c_123007, plain, (![A_13]: (r1_tarski('#skF_3', A_13) | ~v4_relat_1('#skF_5', A_13) | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_122956, c_18])).
% 48.76/37.70  tff(c_153153, plain, (![A_5193]: (r1_tarski('#skF_3', A_5193) | ~v4_relat_1('#skF_5', A_5193))), inference(demodulation, [status(thm), theory('equality')], [c_122, c_123007])).
% 48.76/37.70  tff(c_153172, plain, (r1_tarski('#skF_3', '#skF_5')), inference(resolution, [status(thm)], [c_153049, c_153153])).
% 48.76/37.70  tff(c_155762, plain, (![B_5305]: (v4_relat_1(B_5305, k2_zfmisc_1('#skF_3', '#skF_1')) | ~v1_relat_1(B_5305) | ~r1_tarski(k1_relat_1(B_5305), '#skF_5'))), inference(resolution, [status(thm)], [c_408, c_16])).
% 48.76/37.70  tff(c_123017, plain, (![A_13]: (r1_tarski('#skF_3', A_13) | ~v4_relat_1('#skF_5', A_13))), inference(demodulation, [status(thm), theory('equality')], [c_122, c_123007])).
% 48.76/37.70  tff(c_155779, plain, (r1_tarski('#skF_3', k2_zfmisc_1('#skF_3', '#skF_1')) | ~v1_relat_1('#skF_5') | ~r1_tarski(k1_relat_1('#skF_5'), '#skF_5')), inference(resolution, [status(thm)], [c_155762, c_123017])).
% 48.76/37.70  tff(c_155796, plain, (r1_tarski('#skF_3', k2_zfmisc_1('#skF_3', '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_153172, c_122956, c_122, c_155779])).
% 48.76/37.70  tff(c_153558, plain, (![A_8, A_133]: (A_8='#skF_1' | ~v1_funct_2(A_8, A_133, '#skF_1') | A_133='#skF_1' | ~r1_tarski(A_8, k2_zfmisc_1(A_133, '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_122955, c_122955, c_122955, c_122955, c_566])).
% 48.76/37.70  tff(c_155837, plain, (~v1_funct_2('#skF_3', '#skF_3', '#skF_1') | '#skF_3'='#skF_1'), inference(resolution, [status(thm)], [c_155796, c_153558])).
% 48.76/37.70  tff(c_155860, plain, (~v1_funct_2('#skF_3', '#skF_3', '#skF_1')), inference(splitLeft, [status(thm)], [c_155837])).
% 48.76/37.70  tff(c_181144, plain, (~v1_funct_2('#skF_1', '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_181076, c_181076, c_155860])).
% 48.76/37.70  tff(c_181264, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_122965, c_181144])).
% 48.76/37.70  tff(c_181266, plain, ('#skF_3'!='#skF_1'), inference(splitRight, [status(thm)], [c_153594])).
% 48.76/37.70  tff(c_153052, plain, (![A_5180, B_5179, C_5178, E_5177, D_5181]: (k1_partfun1(A_5180, B_5179, B_5179, C_5178, D_5181, E_5177)=k8_funct_2(A_5180, B_5179, C_5178, D_5181, E_5177) | B_5179='#skF_1' | ~r1_tarski(k2_relset_1(A_5180, B_5179, D_5181), k1_relset_1(B_5179, C_5178, E_5177)) | ~m1_subset_1(E_5177, k1_zfmisc_1(k2_zfmisc_1(B_5179, C_5178))) | ~v1_funct_1(E_5177) | ~m1_subset_1(D_5181, k1_zfmisc_1(k2_zfmisc_1(A_5180, B_5179))) | ~v1_funct_2(D_5181, A_5180, B_5179) | ~v1_funct_1(D_5181))), inference(demodulation, [status(thm), theory('equality')], [c_122955, c_32])).
% 48.76/37.70  tff(c_153058, plain, (![A_5180, D_5181]: (k1_partfun1(A_5180, '#skF_3', '#skF_3', '#skF_1', D_5181, '#skF_5')=k8_funct_2(A_5180, '#skF_3', '#skF_1', D_5181, '#skF_5') | '#skF_3'='#skF_1' | ~r1_tarski(k2_relset_1(A_5180, '#skF_3', D_5181), '#skF_3') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_1'))) | ~v1_funct_1('#skF_5') | ~m1_subset_1(D_5181, k1_zfmisc_1(k2_zfmisc_1(A_5180, '#skF_3'))) | ~v1_funct_2(D_5181, A_5180, '#skF_3') | ~v1_funct_1(D_5181))), inference(superposition, [status(thm), theory('equality')], [c_122994, c_153052])).
% 48.76/37.70  tff(c_153065, plain, (![A_5180, D_5181]: (k1_partfun1(A_5180, '#skF_3', '#skF_3', '#skF_1', D_5181, '#skF_5')=k8_funct_2(A_5180, '#skF_3', '#skF_1', D_5181, '#skF_5') | '#skF_3'='#skF_1' | ~r1_tarski(k2_relset_1(A_5180, '#skF_3', D_5181), '#skF_3') | ~m1_subset_1(D_5181, k1_zfmisc_1(k2_zfmisc_1(A_5180, '#skF_3'))) | ~v1_funct_2(D_5181, A_5180, '#skF_3') | ~v1_funct_1(D_5181))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_153058])).
% 48.76/37.70  tff(c_199686, plain, (![A_6395, D_6396]: (k1_partfun1(A_6395, '#skF_3', '#skF_3', '#skF_1', D_6396, '#skF_5')=k8_funct_2(A_6395, '#skF_3', '#skF_1', D_6396, '#skF_5') | ~r1_tarski(k2_relset_1(A_6395, '#skF_3', D_6396), '#skF_3') | ~m1_subset_1(D_6396, k1_zfmisc_1(k2_zfmisc_1(A_6395, '#skF_3'))) | ~v1_funct_2(D_6396, A_6395, '#skF_3') | ~v1_funct_1(D_6396))), inference(negUnitSimplification, [status(thm)], [c_181266, c_153065])).
% 48.76/37.70  tff(c_199701, plain, (k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_1', '#skF_4', '#skF_5')=k8_funct_2('#skF_2', '#skF_3', '#skF_1', '#skF_4', '#skF_5') | ~r1_tarski(k2_relset_1('#skF_2', '#skF_3', '#skF_4'), '#skF_3') | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_62, c_199686])).
% 48.76/37.70  tff(c_199711, plain, (k8_funct_2('#skF_2', '#skF_3', '#skF_1', '#skF_4', '#skF_5')=k5_relat_1('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_122993, c_153410, c_199701])).
% 48.76/37.70  tff(c_199731, plain, (k1_funct_1(k5_relat_1('#skF_4', '#skF_5'), '#skF_6')!=k1_funct_1('#skF_5', k1_funct_1('#skF_4', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_199711, c_50])).
% 48.76/37.70  tff(c_199955, plain, (~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5') | ~m1_subset_1('#skF_6', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_194525, c_199731])).
% 48.76/37.70  tff(c_199962, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_56, c_122, c_60, c_199955])).
% 48.76/37.70  tff(c_199963, plain, ('#skF_3'='#skF_1'), inference(splitRight, [status(thm)], [c_155837])).
% 48.76/37.70  tff(c_153600, plain, (![B_5216, A_5217]: (v4_relat_1(B_5216, A_5217) | ~v4_relat_1(B_5216, '#skF_1') | ~v1_relat_1(B_5216))), inference(demodulation, [status(thm), theory('equality')], [c_122955, c_4671])).
% 48.76/37.70  tff(c_153606, plain, (![A_5217]: (v4_relat_1('#skF_5', A_5217) | ~v1_relat_1('#skF_5') | ~r1_tarski('#skF_3', '#skF_1'))), inference(resolution, [status(thm)], [c_123015, c_153600])).
% 48.76/37.70  tff(c_153624, plain, (![A_5217]: (v4_relat_1('#skF_5', A_5217) | ~r1_tarski('#skF_3', '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_122, c_153606])).
% 48.76/37.70  tff(c_153637, plain, (~r1_tarski('#skF_3', '#skF_1')), inference(splitLeft, [status(thm)], [c_153624])).
% 48.76/37.70  tff(c_200011, plain, (~r1_tarski('#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_199963, c_153637])).
% 48.76/37.70  tff(c_200073, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_122981, c_200011])).
% 48.76/37.70  tff(c_200074, plain, (![A_5217]: (v4_relat_1('#skF_5', A_5217))), inference(splitRight, [status(thm)], [c_153624])).
% 48.76/37.70  tff(c_200094, plain, (![A_6400]: (r1_tarski('#skF_3', A_6400))), inference(demodulation, [status(thm), theory('equality')], [c_200074, c_123017])).
% 48.76/37.70  tff(c_200141, plain, (![A_6400]: (v1_xboole_0('#skF_3') | ~m1_subset_1(A_6400, '#skF_3'))), inference(resolution, [status(thm)], [c_200094, c_130])).
% 48.76/37.70  tff(c_200179, plain, (![A_6403]: (~m1_subset_1(A_6403, '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_68, c_200141])).
% 48.76/37.70  tff(c_200184, plain, $false, inference(resolution, [status(thm)], [c_46, c_200179])).
% 48.76/37.70  tff(c_200185, plain, (k1_relat_1('#skF_5')='#skF_3' | k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_4701])).
% 48.76/37.70  tff(c_200215, plain, (k1_xboole_0='#skF_1'), inference(splitLeft, [status(thm)], [c_200185])).
% 48.76/37.70  tff(c_200239, plain, (v1_relat_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_200215, c_124])).
% 48.76/37.70  tff(c_154, plain, (![B_79, A_80]: (~r1_tarski(B_79, A_80) | v1_xboole_0(B_79) | ~m1_subset_1(A_80, B_79))), inference(resolution, [status(thm)], [c_126, c_22])).
% 48.76/37.70  tff(c_174, plain, (![A_5]: (v1_xboole_0(k1_xboole_0) | ~m1_subset_1(A_5, k1_xboole_0))), inference(resolution, [status(thm)], [c_93, c_154])).
% 48.76/37.70  tff(c_176, plain, (![A_81]: (~m1_subset_1(A_81, k1_xboole_0))), inference(splitLeft, [status(thm)], [c_174])).
% 48.76/37.70  tff(c_181, plain, $false, inference(resolution, [status(thm)], [c_46, c_176])).
% 48.76/37.70  tff(c_182, plain, (v1_xboole_0(k1_xboole_0)), inference(splitRight, [status(thm)], [c_174])).
% 48.76/37.70  tff(c_200238, plain, (v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_200215, c_182])).
% 48.76/37.70  tff(c_200186, plain, (v1_funct_2('#skF_5', '#skF_3', '#skF_1')), inference(splitRight, [status(thm)], [c_4701])).
% 48.76/37.70  tff(c_201307, plain, (![A_6478, A_6479]: (A_6478='#skF_1' | ~v1_funct_2(A_6478, A_6479, '#skF_1') | A_6479='#skF_1' | ~r1_tarski(A_6478, k2_zfmisc_1(A_6479, '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_200215, c_200215, c_200215, c_200215, c_566])).
% 48.76/37.70  tff(c_201341, plain, ('#skF_5'='#skF_1' | ~v1_funct_2('#skF_5', '#skF_3', '#skF_1') | '#skF_3'='#skF_1'), inference(resolution, [status(thm)], [c_91, c_201307])).
% 48.76/37.70  tff(c_201352, plain, ('#skF_5'='#skF_1' | '#skF_3'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_200186, c_201341])).
% 48.76/37.70  tff(c_201353, plain, ('#skF_3'='#skF_1'), inference(splitLeft, [status(thm)], [c_201352])).
% 48.76/37.70  tff(c_201385, plain, (~v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_201353, c_68])).
% 48.76/37.70  tff(c_201388, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_200238, c_201385])).
% 48.76/37.70  tff(c_201389, plain, ('#skF_5'='#skF_1'), inference(splitRight, [status(thm)], [c_201352])).
% 48.76/37.70  tff(c_201437, plain, (v1_funct_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_201389, c_60])).
% 48.76/37.70  tff(c_200244, plain, ('#skF_2'!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_200215, c_52])).
% 48.76/37.70  tff(c_200323, plain, (![B_6409, C_6410, A_6411]: (k1_funct_1(k5_relat_1(B_6409, C_6410), A_6411)=k1_funct_1(C_6410, k1_funct_1(B_6409, A_6411)) | ~r2_hidden(A_6411, k1_relat_1(B_6409)) | ~v1_funct_1(C_6410) | ~v1_relat_1(C_6410) | ~v1_funct_1(B_6409) | ~v1_relat_1(B_6409))), inference(cnfTransformation, [status(thm)], [f_72])).
% 48.76/37.70  tff(c_203932, plain, (![B_6629, C_6630, A_6631]: (k1_funct_1(k5_relat_1(B_6629, C_6630), A_6631)=k1_funct_1(C_6630, k1_funct_1(B_6629, A_6631)) | ~v1_funct_1(C_6630) | ~v1_relat_1(C_6630) | ~v1_funct_1(B_6629) | ~v1_relat_1(B_6629) | v1_xboole_0(k1_relat_1(B_6629)) | ~m1_subset_1(A_6631, k1_relat_1(B_6629)))), inference(resolution, [status(thm)], [c_8, c_200323])).
% 48.76/37.70  tff(c_203936, plain, (![C_6630, A_6631]: (k1_funct_1(k5_relat_1('#skF_4', C_6630), A_6631)=k1_funct_1(C_6630, k1_funct_1('#skF_4', A_6631)) | ~v1_funct_1(C_6630) | ~v1_relat_1(C_6630) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4') | v1_xboole_0(k1_relat_1('#skF_4')) | ~m1_subset_1(A_6631, '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_4705, c_203932])).
% 48.76/37.70  tff(c_203943, plain, (![C_6630, A_6631]: (k1_funct_1(k5_relat_1('#skF_4', C_6630), A_6631)=k1_funct_1(C_6630, k1_funct_1('#skF_4', A_6631)) | ~v1_funct_1(C_6630) | ~v1_relat_1(C_6630) | v1_xboole_0('#skF_2') | ~m1_subset_1(A_6631, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_4705, c_121, c_66, c_203936])).
% 48.76/37.70  tff(c_211589, plain, (v1_xboole_0('#skF_2')), inference(splitLeft, [status(thm)], [c_203943])).
% 48.76/37.70  tff(c_200243, plain, (![A_1]: (A_1='#skF_1' | ~v1_xboole_0(A_1))), inference(demodulation, [status(thm), theory('equality')], [c_200215, c_2])).
% 48.76/37.70  tff(c_211592, plain, ('#skF_2'='#skF_1'), inference(resolution, [status(thm)], [c_211589, c_200243])).
% 48.76/37.70  tff(c_211596, plain, $false, inference(negUnitSimplification, [status(thm)], [c_200244, c_211592])).
% 48.76/37.70  tff(c_211597, plain, (![C_6630, A_6631]: (k1_funct_1(k5_relat_1('#skF_4', C_6630), A_6631)=k1_funct_1(C_6630, k1_funct_1('#skF_4', A_6631)) | ~v1_funct_1(C_6630) | ~v1_relat_1(C_6630) | ~m1_subset_1(A_6631, '#skF_2'))), inference(splitRight, [status(thm)], [c_203943])).
% 48.76/37.70  tff(c_200240, plain, (![A_5]: (r1_tarski('#skF_1', A_5))), inference(demodulation, [status(thm), theory('equality')], [c_200215, c_93])).
% 48.76/37.70  tff(c_200237, plain, (![A_83]: (v4_relat_1('#skF_1', A_83))), inference(demodulation, [status(thm), theory('equality')], [c_200215, c_213])).
% 48.76/37.70  tff(c_200771, plain, (![A_6456, A_6457, B_6458]: (r1_tarski(A_6456, A_6457) | ~r1_tarski(A_6456, k1_relat_1(B_6458)) | ~v4_relat_1(B_6458, A_6457) | ~v1_relat_1(B_6458))), inference(resolution, [status(thm)], [c_18, c_314])).
% 48.76/37.70  tff(c_200791, plain, (![A_6457]: (r1_tarski(k2_relset_1('#skF_2', '#skF_3', '#skF_4'), A_6457) | ~v4_relat_1('#skF_5', A_6457) | ~v1_relat_1('#skF_5'))), inference(resolution, [status(thm)], [c_484, c_200771])).
% 48.76/37.70  tff(c_200814, plain, (![A_6457]: (r1_tarski(k2_relset_1('#skF_2', '#skF_3', '#skF_4'), A_6457) | ~v4_relat_1('#skF_5', A_6457))), inference(demodulation, [status(thm), theory('equality')], [c_122, c_200791])).
% 48.76/37.70  tff(c_201408, plain, (![A_6457]: (r1_tarski(k2_relset_1('#skF_2', '#skF_3', '#skF_4'), A_6457) | ~v4_relat_1('#skF_1', A_6457))), inference(demodulation, [status(thm), theory('equality')], [c_201389, c_200814])).
% 48.76/37.70  tff(c_201514, plain, (![A_6485]: (r1_tarski(k2_relset_1('#skF_2', '#skF_3', '#skF_4'), A_6485))), inference(demodulation, [status(thm), theory('equality')], [c_200237, c_201408])).
% 48.76/37.70  tff(c_201591, plain, (![A_6485]: (v1_xboole_0(k2_relset_1('#skF_2', '#skF_3', '#skF_4')) | ~m1_subset_1(A_6485, k2_relset_1('#skF_2', '#skF_3', '#skF_4')))), inference(resolution, [status(thm)], [c_201514, c_130])).
% 48.76/37.70  tff(c_207388, plain, (![A_6719]: (~m1_subset_1(A_6719, k2_relset_1('#skF_2', '#skF_3', '#skF_4')))), inference(splitLeft, [status(thm)], [c_201591])).
% 48.76/37.70  tff(c_207398, plain, $false, inference(resolution, [status(thm)], [c_46, c_207388])).
% 48.76/37.70  tff(c_207399, plain, (v1_xboole_0(k2_relset_1('#skF_2', '#skF_3', '#skF_4'))), inference(splitRight, [status(thm)], [c_201591])).
% 48.76/37.70  tff(c_207403, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_4')='#skF_1'), inference(resolution, [status(thm)], [c_207399, c_200243])).
% 48.76/37.70  tff(c_200387, plain, (![A_6419, E_6418, F_6421, C_6422, D_6420, B_6423]: (k1_partfun1(A_6419, B_6423, C_6422, D_6420, E_6418, F_6421)=k5_relat_1(E_6418, F_6421) | ~m1_subset_1(F_6421, k1_zfmisc_1(k2_zfmisc_1(C_6422, D_6420))) | ~v1_funct_1(F_6421) | ~m1_subset_1(E_6418, k1_zfmisc_1(k2_zfmisc_1(A_6419, B_6423))) | ~v1_funct_1(E_6418))), inference(cnfTransformation, [status(thm)], [f_138])).
% 48.76/37.70  tff(c_204557, plain, (![A_6651, C_6652, B_6653, A_6650, E_6654, D_6655]: (k1_partfun1(A_6651, B_6653, C_6652, D_6655, E_6654, A_6650)=k5_relat_1(E_6654, A_6650) | ~v1_funct_1(A_6650) | ~m1_subset_1(E_6654, k1_zfmisc_1(k2_zfmisc_1(A_6651, B_6653))) | ~v1_funct_1(E_6654) | ~r1_tarski(A_6650, k2_zfmisc_1(C_6652, D_6655)))), inference(resolution, [status(thm)], [c_12, c_200387])).
% 48.76/37.70  tff(c_204565, plain, (![C_6652, D_6655, A_6650]: (k1_partfun1('#skF_2', '#skF_3', C_6652, D_6655, '#skF_4', A_6650)=k5_relat_1('#skF_4', A_6650) | ~v1_funct_1(A_6650) | ~v1_funct_1('#skF_4') | ~r1_tarski(A_6650, k2_zfmisc_1(C_6652, D_6655)))), inference(resolution, [status(thm)], [c_62, c_204557])).
% 48.76/37.70  tff(c_204958, plain, (![C_6660, D_6661, A_6662]: (k1_partfun1('#skF_2', '#skF_3', C_6660, D_6661, '#skF_4', A_6662)=k5_relat_1('#skF_4', A_6662) | ~v1_funct_1(A_6662) | ~r1_tarski(A_6662, k2_zfmisc_1(C_6660, D_6661)))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_204565])).
% 48.76/37.70  tff(c_205020, plain, (![C_6660, D_6661]: (k1_partfun1('#skF_2', '#skF_3', C_6660, D_6661, '#skF_4', '#skF_1')=k5_relat_1('#skF_4', '#skF_1') | ~v1_funct_1('#skF_1'))), inference(resolution, [status(thm)], [c_200240, c_204958])).
% 48.76/37.70  tff(c_205056, plain, (![C_6660, D_6661]: (k1_partfun1('#skF_2', '#skF_3', C_6660, D_6661, '#skF_4', '#skF_1')=k5_relat_1('#skF_4', '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_201437, c_205020])).
% 48.76/37.70  tff(c_201390, plain, ('#skF_3'!='#skF_1'), inference(splitRight, [status(thm)], [c_201352])).
% 48.76/37.70  tff(c_4519, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(splitRight, [status(thm)], [c_732])).
% 48.76/37.70  tff(c_200225, plain, (k1_relat_1('#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_200215, c_200215, c_4519])).
% 48.76/37.70  tff(c_200493, plain, (![C_6431, A_6433, B_6432, E_6430, D_6434]: (k1_partfun1(A_6433, B_6432, B_6432, C_6431, D_6434, E_6430)=k8_funct_2(A_6433, B_6432, C_6431, D_6434, E_6430) | B_6432='#skF_1' | ~r1_tarski(k2_relset_1(A_6433, B_6432, D_6434), k1_relset_1(B_6432, C_6431, E_6430)) | ~m1_subset_1(E_6430, k1_zfmisc_1(k2_zfmisc_1(B_6432, C_6431))) | ~v1_funct_1(E_6430) | ~m1_subset_1(D_6434, k1_zfmisc_1(k2_zfmisc_1(A_6433, B_6432))) | ~v1_funct_2(D_6434, A_6433, B_6432) | ~v1_funct_1(D_6434))), inference(demodulation, [status(thm), theory('equality')], [c_200215, c_32])).
% 48.76/37.70  tff(c_200502, plain, (![A_6433, D_6434]: (k1_partfun1(A_6433, '#skF_3', '#skF_3', '#skF_1', D_6434, '#skF_5')=k8_funct_2(A_6433, '#skF_3', '#skF_1', D_6434, '#skF_5') | '#skF_3'='#skF_1' | ~r1_tarski(k2_relset_1(A_6433, '#skF_3', D_6434), k1_relat_1('#skF_5')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_1'))) | ~v1_funct_1('#skF_5') | ~m1_subset_1(D_6434, k1_zfmisc_1(k2_zfmisc_1(A_6433, '#skF_3'))) | ~v1_funct_2(D_6434, A_6433, '#skF_3') | ~v1_funct_1(D_6434))), inference(superposition, [status(thm), theory('equality')], [c_477, c_200493])).
% 48.76/37.70  tff(c_200509, plain, (![A_6433, D_6434]: (k1_partfun1(A_6433, '#skF_3', '#skF_3', '#skF_1', D_6434, '#skF_5')=k8_funct_2(A_6433, '#skF_3', '#skF_1', D_6434, '#skF_5') | '#skF_3'='#skF_1' | ~r1_tarski(k2_relset_1(A_6433, '#skF_3', D_6434), k1_relat_1('#skF_5')) | ~m1_subset_1(D_6434, k1_zfmisc_1(k2_zfmisc_1(A_6433, '#skF_3'))) | ~v1_funct_2(D_6434, A_6433, '#skF_3') | ~v1_funct_1(D_6434))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_200502])).
% 48.76/37.70  tff(c_215052, plain, (![A_6433, D_6434]: (k1_partfun1(A_6433, '#skF_3', '#skF_3', '#skF_1', D_6434, '#skF_1')=k8_funct_2(A_6433, '#skF_3', '#skF_1', D_6434, '#skF_1') | '#skF_3'='#skF_1' | ~r1_tarski(k2_relset_1(A_6433, '#skF_3', D_6434), '#skF_1') | ~m1_subset_1(D_6434, k1_zfmisc_1(k2_zfmisc_1(A_6433, '#skF_3'))) | ~v1_funct_2(D_6434, A_6433, '#skF_3') | ~v1_funct_1(D_6434))), inference(demodulation, [status(thm), theory('equality')], [c_200225, c_201389, c_201389, c_201389, c_200509])).
% 48.76/37.70  tff(c_215054, plain, (![A_6975, D_6976]: (k1_partfun1(A_6975, '#skF_3', '#skF_3', '#skF_1', D_6976, '#skF_1')=k8_funct_2(A_6975, '#skF_3', '#skF_1', D_6976, '#skF_1') | ~r1_tarski(k2_relset_1(A_6975, '#skF_3', D_6976), '#skF_1') | ~m1_subset_1(D_6976, k1_zfmisc_1(k2_zfmisc_1(A_6975, '#skF_3'))) | ~v1_funct_2(D_6976, A_6975, '#skF_3') | ~v1_funct_1(D_6976))), inference(negUnitSimplification, [status(thm)], [c_201390, c_215052])).
% 48.76/37.70  tff(c_215069, plain, (k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_1', '#skF_4', '#skF_1')=k8_funct_2('#skF_2', '#skF_3', '#skF_1', '#skF_4', '#skF_1') | ~r1_tarski(k2_relset_1('#skF_2', '#skF_3', '#skF_4'), '#skF_1') | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_62, c_215054])).
% 48.76/37.70  tff(c_215081, plain, (k8_funct_2('#skF_2', '#skF_3', '#skF_1', '#skF_4', '#skF_1')=k5_relat_1('#skF_4', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_200240, c_207403, c_205056, c_215069])).
% 48.76/37.70  tff(c_201432, plain, (k1_funct_1(k8_funct_2('#skF_2', '#skF_3', '#skF_1', '#skF_4', '#skF_1'), '#skF_6')!=k1_funct_1('#skF_1', k1_funct_1('#skF_4', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_201389, c_201389, c_50])).
% 48.76/37.70  tff(c_215083, plain, (k1_funct_1(k5_relat_1('#skF_4', '#skF_1'), '#skF_6')!=k1_funct_1('#skF_1', k1_funct_1('#skF_4', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_215081, c_201432])).
% 48.76/37.70  tff(c_215090, plain, (~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1') | ~m1_subset_1('#skF_6', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_211597, c_215083])).
% 48.76/37.70  tff(c_215097, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_56, c_200239, c_201437, c_215090])).
% 48.76/37.70  tff(c_215098, plain, (k1_relat_1('#skF_5')='#skF_3'), inference(splitRight, [status(thm)], [c_200185])).
% 48.76/37.70  tff(c_215105, plain, (r1_tarski(k2_relset_1('#skF_2', '#skF_3', '#skF_4'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_215098, c_484])).
% 48.76/37.70  tff(c_238479, plain, (![E_7653, B_7658, A_7654, F_7656, D_7655, C_7657]: (k1_partfun1(A_7654, B_7658, C_7657, D_7655, E_7653, F_7656)=k5_relat_1(E_7653, F_7656) | ~m1_subset_1(F_7656, k1_zfmisc_1(k2_zfmisc_1(C_7657, D_7655))) | ~v1_funct_1(F_7656) | ~m1_subset_1(E_7653, k1_zfmisc_1(k2_zfmisc_1(A_7654, B_7658))) | ~v1_funct_1(E_7653))), inference(cnfTransformation, [status(thm)], [f_138])).
% 48.76/37.70  tff(c_238486, plain, (![A_7654, B_7658, E_7653]: (k1_partfun1(A_7654, B_7658, '#skF_3', '#skF_1', E_7653, '#skF_5')=k5_relat_1(E_7653, '#skF_5') | ~v1_funct_1('#skF_5') | ~m1_subset_1(E_7653, k1_zfmisc_1(k2_zfmisc_1(A_7654, B_7658))) | ~v1_funct_1(E_7653))), inference(resolution, [status(thm)], [c_58, c_238479])).
% 48.76/37.70  tff(c_239132, plain, (![A_7695, B_7696, E_7697]: (k1_partfun1(A_7695, B_7696, '#skF_3', '#skF_1', E_7697, '#skF_5')=k5_relat_1(E_7697, '#skF_5') | ~m1_subset_1(E_7697, k1_zfmisc_1(k2_zfmisc_1(A_7695, B_7696))) | ~v1_funct_1(E_7697))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_238486])).
% 48.76/37.70  tff(c_239139, plain, (k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_1', '#skF_4', '#skF_5')=k5_relat_1('#skF_4', '#skF_5') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_62, c_239132])).
% 48.76/37.70  tff(c_239154, plain, (k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_1', '#skF_4', '#skF_5')=k5_relat_1('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_239139])).
% 48.76/37.70  tff(c_215122, plain, (![A_13]: (r1_tarski('#skF_3', A_13) | ~v4_relat_1('#skF_5', A_13) | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_215098, c_18])).
% 48.76/37.70  tff(c_238502, plain, (![A_7659]: (r1_tarski('#skF_3', A_7659) | ~v4_relat_1('#skF_5', A_7659))), inference(demodulation, [status(thm), theory('equality')], [c_122, c_215122])).
% 48.76/37.70  tff(c_238520, plain, (r1_tarski('#skF_3', '#skF_3')), inference(resolution, [status(thm)], [c_211, c_238502])).
% 48.76/37.70  tff(c_200187, plain, (![B_6404, C_6405, A_6406]: (k1_xboole_0=B_6404 | v1_funct_2(C_6405, A_6406, B_6404) | k1_relset_1(A_6406, B_6404, C_6405)!=A_6406 | ~m1_subset_1(C_6405, k1_zfmisc_1(k2_zfmisc_1(A_6406, B_6404))))), inference(cnfTransformation, [status(thm)], [f_126])).
% 48.76/37.70  tff(c_240395, plain, (![B_7755, A_7756, A_7757]: (k1_xboole_0=B_7755 | v1_funct_2(A_7756, A_7757, B_7755) | k1_relset_1(A_7757, B_7755, A_7756)!=A_7757 | ~r1_tarski(A_7756, k2_zfmisc_1(A_7757, B_7755)))), inference(resolution, [status(thm)], [c_12, c_200187])).
% 48.76/37.70  tff(c_240450, plain, (![A_104]: (k1_xboole_0='#skF_3' | v1_funct_2(A_104, '#skF_2', '#skF_3') | k1_relset_1('#skF_2', '#skF_3', A_104)!='#skF_2' | ~r1_tarski(A_104, '#skF_4'))), inference(resolution, [status(thm)], [c_330, c_240395])).
% 48.76/37.70  tff(c_248291, plain, (k1_xboole_0='#skF_3'), inference(splitLeft, [status(thm)], [c_240450])).
% 48.76/37.70  tff(c_215119, plain, (![A_13]: (v4_relat_1('#skF_5', A_13) | ~r1_tarski('#skF_3', A_13) | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_215098, c_16])).
% 48.76/37.70  tff(c_215132, plain, (![A_13]: (v4_relat_1('#skF_5', A_13) | ~r1_tarski('#skF_3', A_13))), inference(demodulation, [status(thm), theory('equality')], [c_122, c_215119])).
% 48.76/37.70  tff(c_343, plain, (![B_14, A_108]: (r1_tarski(k1_relat_1(B_14), A_108) | ~v4_relat_1(B_14, k1_xboole_0) | ~v1_relat_1(B_14))), inference(resolution, [status(thm)], [c_18, c_333])).
% 48.76/37.70  tff(c_215110, plain, (![A_108]: (r1_tarski('#skF_3', A_108) | ~v4_relat_1('#skF_5', k1_xboole_0) | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_215098, c_343])).
% 48.76/37.70  tff(c_215126, plain, (![A_108]: (r1_tarski('#skF_3', A_108) | ~v4_relat_1('#skF_5', k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_122, c_215110])).
% 48.76/37.70  tff(c_238568, plain, (~v4_relat_1('#skF_5', k1_xboole_0)), inference(splitLeft, [status(thm)], [c_215126])).
% 48.76/37.70  tff(c_238588, plain, (~r1_tarski('#skF_3', k1_xboole_0)), inference(resolution, [status(thm)], [c_215132, c_238568])).
% 48.76/37.70  tff(c_248327, plain, (~r1_tarski('#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_248291, c_238588])).
% 48.76/37.70  tff(c_248353, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_238520, c_248327])).
% 48.76/37.70  tff(c_248355, plain, (k1_xboole_0!='#skF_3'), inference(splitRight, [status(thm)], [c_240450])).
% 48.76/37.70  tff(c_215106, plain, (k1_relset_1('#skF_3', '#skF_1', '#skF_5')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_215098, c_477])).
% 48.76/37.70  tff(c_238550, plain, (![C_7662, E_7661, D_7665, A_7664, B_7663]: (k1_partfun1(A_7664, B_7663, B_7663, C_7662, D_7665, E_7661)=k8_funct_2(A_7664, B_7663, C_7662, D_7665, E_7661) | k1_xboole_0=B_7663 | ~r1_tarski(k2_relset_1(A_7664, B_7663, D_7665), k1_relset_1(B_7663, C_7662, E_7661)) | ~m1_subset_1(E_7661, k1_zfmisc_1(k2_zfmisc_1(B_7663, C_7662))) | ~v1_funct_1(E_7661) | ~m1_subset_1(D_7665, k1_zfmisc_1(k2_zfmisc_1(A_7664, B_7663))) | ~v1_funct_2(D_7665, A_7664, B_7663) | ~v1_funct_1(D_7665))), inference(cnfTransformation, [status(thm)], [f_108])).
% 48.76/37.70  tff(c_238553, plain, (![A_7664, D_7665]: (k1_partfun1(A_7664, '#skF_3', '#skF_3', '#skF_1', D_7665, '#skF_5')=k8_funct_2(A_7664, '#skF_3', '#skF_1', D_7665, '#skF_5') | k1_xboole_0='#skF_3' | ~r1_tarski(k2_relset_1(A_7664, '#skF_3', D_7665), '#skF_3') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_1'))) | ~v1_funct_1('#skF_5') | ~m1_subset_1(D_7665, k1_zfmisc_1(k2_zfmisc_1(A_7664, '#skF_3'))) | ~v1_funct_2(D_7665, A_7664, '#skF_3') | ~v1_funct_1(D_7665))), inference(superposition, [status(thm), theory('equality')], [c_215106, c_238550])).
% 48.76/37.70  tff(c_238561, plain, (![A_7664, D_7665]: (k1_partfun1(A_7664, '#skF_3', '#skF_3', '#skF_1', D_7665, '#skF_5')=k8_funct_2(A_7664, '#skF_3', '#skF_1', D_7665, '#skF_5') | k1_xboole_0='#skF_3' | ~r1_tarski(k2_relset_1(A_7664, '#skF_3', D_7665), '#skF_3') | ~m1_subset_1(D_7665, k1_zfmisc_1(k2_zfmisc_1(A_7664, '#skF_3'))) | ~v1_funct_2(D_7665, A_7664, '#skF_3') | ~v1_funct_1(D_7665))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_238553])).
% 48.76/37.70  tff(c_254245, plain, (![A_8164, D_8165]: (k1_partfun1(A_8164, '#skF_3', '#skF_3', '#skF_1', D_8165, '#skF_5')=k8_funct_2(A_8164, '#skF_3', '#skF_1', D_8165, '#skF_5') | ~r1_tarski(k2_relset_1(A_8164, '#skF_3', D_8165), '#skF_3') | ~m1_subset_1(D_8165, k1_zfmisc_1(k2_zfmisc_1(A_8164, '#skF_3'))) | ~v1_funct_2(D_8165, A_8164, '#skF_3') | ~v1_funct_1(D_8165))), inference(negUnitSimplification, [status(thm)], [c_248355, c_238561])).
% 48.76/37.70  tff(c_254256, plain, (k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_1', '#skF_4', '#skF_5')=k8_funct_2('#skF_2', '#skF_3', '#skF_1', '#skF_4', '#skF_5') | ~r1_tarski(k2_relset_1('#skF_2', '#skF_3', '#skF_4'), '#skF_3') | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_62, c_254245])).
% 48.76/37.70  tff(c_254269, plain, (k8_funct_2('#skF_2', '#skF_3', '#skF_1', '#skF_4', '#skF_5')=k5_relat_1('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_215105, c_239154, c_254256])).
% 48.76/37.70  tff(c_254272, plain, (k1_funct_1(k5_relat_1('#skF_4', '#skF_5'), '#skF_6')!=k1_funct_1('#skF_5', k1_funct_1('#skF_4', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_254269, c_50])).
% 48.76/37.70  tff(c_254279, plain, (~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5') | ~m1_subset_1('#skF_6', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_248364, c_254272])).
% 48.76/37.70  tff(c_254286, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_56, c_122, c_60, c_254279])).
% 48.76/37.70  tff(c_254294, plain, (![A_8166]: (r1_tarski('#skF_3', A_8166))), inference(splitRight, [status(thm)], [c_215126])).
% 48.76/37.70  tff(c_254329, plain, (![A_8166]: (v1_xboole_0('#skF_3') | ~m1_subset_1(A_8166, '#skF_3'))), inference(resolution, [status(thm)], [c_254294, c_130])).
% 48.76/37.70  tff(c_254354, plain, (![A_8167]: (~m1_subset_1(A_8167, '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_68, c_254329])).
% 48.76/37.70  tff(c_254359, plain, $false, inference(resolution, [status(thm)], [c_46, c_254354])).
% 48.76/37.70  tff(c_254360, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_4699])).
% 48.76/37.70  tff(c_254383, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_254360, c_182])).
% 48.76/37.70  tff(c_254391, plain, $false, inference(negUnitSimplification, [status(thm)], [c_68, c_254383])).
% 48.76/37.70  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 48.76/37.70  
% 48.76/37.70  Inference rules
% 48.76/37.70  ----------------------
% 48.76/37.70  #Ref     : 0
% 48.76/37.70  #Sup     : 49964
% 48.76/37.70  #Fact    : 0
% 48.76/37.70  #Define  : 0
% 48.76/37.70  #Split   : 683
% 48.76/37.70  #Chain   : 0
% 48.76/37.70  #Close   : 0
% 48.76/37.70  
% 48.76/37.70  Ordering : KBO
% 48.76/37.70  
% 48.76/37.70  Simplification rules
% 48.76/37.70  ----------------------
% 48.76/37.70  #Subsume      : 13774
% 48.76/37.70  #Demod        : 58917
% 48.76/37.70  #Tautology    : 15357
% 48.76/37.70  #SimpNegUnit  : 1034
% 48.76/37.70  #BackRed      : 4465
% 48.76/37.70  
% 48.76/37.70  #Partial instantiations: 0
% 48.76/37.70  #Strategies tried      : 1
% 48.76/37.70  
% 48.76/37.70  Timing (in seconds)
% 48.76/37.70  ----------------------
% 48.76/37.70  Preprocessing        : 0.36
% 48.76/37.70  Parsing              : 0.19
% 48.76/37.70  CNF conversion       : 0.03
% 48.76/37.70  Main loop            : 36.33
% 48.76/37.70  Inferencing          : 6.92
% 48.76/37.70  Reduction            : 17.59
% 48.76/37.70  Demodulation         : 13.57
% 48.76/37.70  BG Simplification    : 0.58
% 48.76/37.70  Subsumption          : 8.98
% 48.76/37.70  Abstraction          : 1.11
% 48.76/37.70  MUC search           : 0.00
% 48.76/37.70  Cooper               : 0.00
% 48.76/37.70  Total                : 36.82
% 48.76/37.70  Index Insertion      : 0.00
% 48.76/37.70  Index Deletion       : 0.00
% 48.76/37.70  Index Matching       : 0.00
% 48.76/37.70  BG Taut test         : 0.00
%------------------------------------------------------------------------------
