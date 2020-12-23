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
% DateTime   : Thu Dec  3 10:17:43 EST 2020

% Result     : Theorem 3.07s
% Output     : CNFRefutation 3.07s
% Verified   : 
% Statistics : Number of formulae       :   95 ( 229 expanded)
%              Number of leaves         :   39 (  98 expanded)
%              Depth                    :   10
%              Number of atoms          :  184 ( 813 expanded)
%              Number of equality atoms :   50 ( 214 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k8_funct_2 > k2_relset_1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_142,negated_conjecture,(
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

tff(f_68,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_72,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_107,axiom,(
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

tff(f_47,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_64,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ! [C] :
          ( ( v1_relat_1(C)
            & v1_funct_1(C) )
         => ( r2_hidden(A,k1_relat_1(B))
           => k1_funct_1(k5_relat_1(B,C),A) = k1_funct_1(C,k1_funct_1(B,A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_funct_1)).

tff(f_29,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_117,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_89,axiom,(
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

tff(f_31,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_33,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ~ ( r1_tarski(B,A)
          & r1_xboole_0(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_xboole_1)).

tff(c_56,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_44,plain,(
    m1_subset_1('#skF_6','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_46,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_74,plain,(
    ! [C_53,A_54,B_55] :
      ( v1_relat_1(C_53)
      | ~ m1_subset_1(C_53,k1_zfmisc_1(k2_zfmisc_1(A_54,B_55))) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_86,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_46,c_74])).

tff(c_48,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_40,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_52,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_50,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_129,plain,(
    ! [A_66,B_67,C_68] :
      ( k1_relset_1(A_66,B_67,C_68) = k1_relat_1(C_68)
      | ~ m1_subset_1(C_68,k1_zfmisc_1(k2_zfmisc_1(A_66,B_67))) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_142,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_50,c_129])).

tff(c_223,plain,(
    ! [B_87,A_88,C_89] :
      ( k1_xboole_0 = B_87
      | k1_relset_1(A_88,B_87,C_89) = A_88
      | ~ v1_funct_2(C_89,A_88,B_87)
      | ~ m1_subset_1(C_89,k1_zfmisc_1(k2_zfmisc_1(A_88,B_87))) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_233,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relset_1('#skF_2','#skF_3','#skF_4') = '#skF_2'
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_50,c_223])).

tff(c_239,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relat_1('#skF_4') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_142,c_233])).

tff(c_240,plain,(
    k1_relat_1('#skF_4') = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_239])).

tff(c_87,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_50,c_74])).

tff(c_54,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_10,plain,(
    ! [A_6,B_7] :
      ( r2_hidden(A_6,B_7)
      | v1_xboole_0(B_7)
      | ~ m1_subset_1(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_312,plain,(
    ! [B_101,C_102,A_103] :
      ( k1_funct_1(k5_relat_1(B_101,C_102),A_103) = k1_funct_1(C_102,k1_funct_1(B_101,A_103))
      | ~ r2_hidden(A_103,k1_relat_1(B_101))
      | ~ v1_funct_1(C_102)
      | ~ v1_relat_1(C_102)
      | ~ v1_funct_1(B_101)
      | ~ v1_relat_1(B_101) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_341,plain,(
    ! [B_108,C_109,A_110] :
      ( k1_funct_1(k5_relat_1(B_108,C_109),A_110) = k1_funct_1(C_109,k1_funct_1(B_108,A_110))
      | ~ v1_funct_1(C_109)
      | ~ v1_relat_1(C_109)
      | ~ v1_funct_1(B_108)
      | ~ v1_relat_1(B_108)
      | v1_xboole_0(k1_relat_1(B_108))
      | ~ m1_subset_1(A_110,k1_relat_1(B_108)) ) ),
    inference(resolution,[status(thm)],[c_10,c_312])).

tff(c_343,plain,(
    ! [C_109,A_110] :
      ( k1_funct_1(k5_relat_1('#skF_4',C_109),A_110) = k1_funct_1(C_109,k1_funct_1('#skF_4',A_110))
      | ~ v1_funct_1(C_109)
      | ~ v1_relat_1(C_109)
      | ~ v1_funct_1('#skF_4')
      | ~ v1_relat_1('#skF_4')
      | v1_xboole_0(k1_relat_1('#skF_4'))
      | ~ m1_subset_1(A_110,'#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_240,c_341])).

tff(c_345,plain,(
    ! [C_109,A_110] :
      ( k1_funct_1(k5_relat_1('#skF_4',C_109),A_110) = k1_funct_1(C_109,k1_funct_1('#skF_4',A_110))
      | ~ v1_funct_1(C_109)
      | ~ v1_relat_1(C_109)
      | v1_xboole_0('#skF_2')
      | ~ m1_subset_1(A_110,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_240,c_87,c_54,c_343])).

tff(c_346,plain,(
    v1_xboole_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_345])).

tff(c_2,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_349,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_346,c_2])).

tff(c_353,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_349])).

tff(c_354,plain,(
    ! [C_109,A_110] :
      ( k1_funct_1(k5_relat_1('#skF_4',C_109),A_110) = k1_funct_1(C_109,k1_funct_1('#skF_4',A_110))
      | ~ v1_funct_1(C_109)
      | ~ v1_relat_1(C_109)
      | ~ m1_subset_1(A_110,'#skF_2') ) ),
    inference(splitRight,[status(thm)],[c_345])).

tff(c_373,plain,(
    ! [B_114,F_116,E_117,A_115,D_113,C_118] :
      ( k1_partfun1(A_115,B_114,C_118,D_113,E_117,F_116) = k5_relat_1(E_117,F_116)
      | ~ m1_subset_1(F_116,k1_zfmisc_1(k2_zfmisc_1(C_118,D_113)))
      | ~ v1_funct_1(F_116)
      | ~ m1_subset_1(E_117,k1_zfmisc_1(k2_zfmisc_1(A_115,B_114)))
      | ~ v1_funct_1(E_117) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_378,plain,(
    ! [A_115,B_114,E_117] :
      ( k1_partfun1(A_115,B_114,'#skF_3','#skF_1',E_117,'#skF_5') = k5_relat_1(E_117,'#skF_5')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1(E_117,k1_zfmisc_1(k2_zfmisc_1(A_115,B_114)))
      | ~ v1_funct_1(E_117) ) ),
    inference(resolution,[status(thm)],[c_46,c_373])).

tff(c_388,plain,(
    ! [A_119,B_120,E_121] :
      ( k1_partfun1(A_119,B_120,'#skF_3','#skF_1',E_121,'#skF_5') = k5_relat_1(E_121,'#skF_5')
      | ~ m1_subset_1(E_121,k1_zfmisc_1(k2_zfmisc_1(A_119,B_120)))
      | ~ v1_funct_1(E_121) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_378])).

tff(c_398,plain,
    ( k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_1','#skF_4','#skF_5') = k5_relat_1('#skF_4','#skF_5')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_50,c_388])).

tff(c_405,plain,(
    k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_1','#skF_4','#skF_5') = k5_relat_1('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_398])).

tff(c_141,plain,(
    k1_relset_1('#skF_3','#skF_1','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_46,c_129])).

tff(c_42,plain,(
    r1_tarski(k2_relset_1('#skF_2','#skF_3','#skF_4'),k1_relset_1('#skF_3','#skF_1','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_143,plain,(
    r1_tarski(k2_relset_1('#skF_2','#skF_3','#skF_4'),k1_relat_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_141,c_42])).

tff(c_406,plain,(
    ! [E_126,C_122,D_124,A_125,B_123] :
      ( k1_partfun1(A_125,B_123,B_123,C_122,D_124,E_126) = k8_funct_2(A_125,B_123,C_122,D_124,E_126)
      | k1_xboole_0 = B_123
      | ~ r1_tarski(k2_relset_1(A_125,B_123,D_124),k1_relset_1(B_123,C_122,E_126))
      | ~ m1_subset_1(E_126,k1_zfmisc_1(k2_zfmisc_1(B_123,C_122)))
      | ~ v1_funct_1(E_126)
      | ~ m1_subset_1(D_124,k1_zfmisc_1(k2_zfmisc_1(A_125,B_123)))
      | ~ v1_funct_2(D_124,A_125,B_123)
      | ~ v1_funct_1(D_124) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_415,plain,(
    ! [A_125,D_124] :
      ( k1_partfun1(A_125,'#skF_3','#skF_3','#skF_1',D_124,'#skF_5') = k8_funct_2(A_125,'#skF_3','#skF_1',D_124,'#skF_5')
      | k1_xboole_0 = '#skF_3'
      | ~ r1_tarski(k2_relset_1(A_125,'#skF_3',D_124),k1_relat_1('#skF_5'))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_1')))
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1(D_124,k1_zfmisc_1(k2_zfmisc_1(A_125,'#skF_3')))
      | ~ v1_funct_2(D_124,A_125,'#skF_3')
      | ~ v1_funct_1(D_124) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_141,c_406])).

tff(c_420,plain,(
    ! [A_125,D_124] :
      ( k1_partfun1(A_125,'#skF_3','#skF_3','#skF_1',D_124,'#skF_5') = k8_funct_2(A_125,'#skF_3','#skF_1',D_124,'#skF_5')
      | k1_xboole_0 = '#skF_3'
      | ~ r1_tarski(k2_relset_1(A_125,'#skF_3',D_124),k1_relat_1('#skF_5'))
      | ~ m1_subset_1(D_124,k1_zfmisc_1(k2_zfmisc_1(A_125,'#skF_3')))
      | ~ v1_funct_2(D_124,A_125,'#skF_3')
      | ~ v1_funct_1(D_124) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_415])).

tff(c_565,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_420])).

tff(c_4,plain,(
    ! [A_2] : r1_tarski(k1_xboole_0,A_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_6,plain,(
    ! [A_3] : r1_xboole_0(A_3,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_104,plain,(
    ! [B_59,A_60] :
      ( ~ r1_xboole_0(B_59,A_60)
      | ~ r1_tarski(B_59,A_60)
      | v1_xboole_0(B_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_109,plain,(
    ! [A_61] :
      ( ~ r1_tarski(A_61,k1_xboole_0)
      | v1_xboole_0(A_61) ) ),
    inference(resolution,[status(thm)],[c_6,c_104])).

tff(c_114,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_4,c_109])).

tff(c_584,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_565,c_114])).

tff(c_592,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_584])).

tff(c_595,plain,(
    ! [A_158,D_159] :
      ( k1_partfun1(A_158,'#skF_3','#skF_3','#skF_1',D_159,'#skF_5') = k8_funct_2(A_158,'#skF_3','#skF_1',D_159,'#skF_5')
      | ~ r1_tarski(k2_relset_1(A_158,'#skF_3',D_159),k1_relat_1('#skF_5'))
      | ~ m1_subset_1(D_159,k1_zfmisc_1(k2_zfmisc_1(A_158,'#skF_3')))
      | ~ v1_funct_2(D_159,A_158,'#skF_3')
      | ~ v1_funct_1(D_159) ) ),
    inference(splitRight,[status(thm)],[c_420])).

tff(c_598,plain,
    ( k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_1','#skF_4','#skF_5') = k8_funct_2('#skF_2','#skF_3','#skF_1','#skF_4','#skF_5')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_3')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_143,c_595])).

tff(c_601,plain,(
    k8_funct_2('#skF_2','#skF_3','#skF_1','#skF_4','#skF_5') = k5_relat_1('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_50,c_405,c_598])).

tff(c_38,plain,(
    k1_funct_1(k8_funct_2('#skF_2','#skF_3','#skF_1','#skF_4','#skF_5'),'#skF_6') != k1_funct_1('#skF_5',k1_funct_1('#skF_4','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_602,plain,(
    k1_funct_1(k5_relat_1('#skF_4','#skF_5'),'#skF_6') != k1_funct_1('#skF_5',k1_funct_1('#skF_4','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_601,c_38])).

tff(c_609,plain,
    ( ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5')
    | ~ m1_subset_1('#skF_6','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_354,c_602])).

tff(c_616,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_86,c_48,c_609])).

tff(c_617,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_239])).

tff(c_630,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_617,c_114])).

tff(c_638,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_630])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:26:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.07/1.51  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.07/1.52  
% 3.07/1.52  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.07/1.52  %$ v1_funct_2 > r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k8_funct_2 > k2_relset_1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 3.07/1.52  
% 3.07/1.52  %Foreground sorts:
% 3.07/1.52  
% 3.07/1.52  
% 3.07/1.52  %Background operators:
% 3.07/1.52  
% 3.07/1.52  
% 3.07/1.52  %Foreground operators:
% 3.07/1.52  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 3.07/1.52  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.07/1.52  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.07/1.52  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.07/1.52  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.07/1.52  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 3.07/1.52  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.07/1.52  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.07/1.52  tff('#skF_5', type, '#skF_5': $i).
% 3.07/1.52  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.07/1.52  tff(k8_funct_2, type, k8_funct_2: ($i * $i * $i * $i * $i) > $i).
% 3.07/1.52  tff('#skF_6', type, '#skF_6': $i).
% 3.07/1.52  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.07/1.52  tff('#skF_2', type, '#skF_2': $i).
% 3.07/1.52  tff('#skF_3', type, '#skF_3': $i).
% 3.07/1.52  tff('#skF_1', type, '#skF_1': $i).
% 3.07/1.52  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.07/1.52  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.07/1.52  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.07/1.52  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.07/1.52  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.07/1.52  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.07/1.52  tff('#skF_4', type, '#skF_4': $i).
% 3.07/1.52  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.07/1.52  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.07/1.52  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.07/1.52  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.07/1.52  
% 3.07/1.53  tff(f_142, negated_conjecture, ~(![A, B, C]: (~v1_xboole_0(C) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, C)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (![E]: ((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(C, A)))) => (![F]: (m1_subset_1(F, B) => (r1_tarski(k2_relset_1(B, C, D), k1_relset_1(C, A, E)) => ((B = k1_xboole_0) | (k1_funct_1(k8_funct_2(B, C, A, D, E), F) = k1_funct_1(E, k1_funct_1(D, F))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t185_funct_2)).
% 3.07/1.53  tff(f_68, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.07/1.53  tff(f_72, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.07/1.53  tff(f_107, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 3.07/1.53  tff(f_47, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 3.07/1.53  tff(f_64, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (![C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(A, k1_relat_1(B)) => (k1_funct_1(k5_relat_1(B, C), A) = k1_funct_1(C, k1_funct_1(B, A)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t23_funct_1)).
% 3.07/1.53  tff(f_29, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 3.07/1.53  tff(f_117, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 3.07/1.53  tff(f_89, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: ((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (r1_tarski(k2_relset_1(A, B, D), k1_relset_1(B, C, E)) => ((B = k1_xboole_0) | (k8_funct_2(A, B, C, D, E) = k1_partfun1(A, B, B, C, D, E)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d12_funct_2)).
% 3.07/1.53  tff(f_31, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 3.07/1.53  tff(f_33, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 3.07/1.53  tff(f_41, axiom, (![A, B]: (~v1_xboole_0(B) => ~(r1_tarski(B, A) & r1_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_xboole_1)).
% 3.07/1.53  tff(c_56, plain, (~v1_xboole_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_142])).
% 3.07/1.53  tff(c_44, plain, (m1_subset_1('#skF_6', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_142])).
% 3.07/1.53  tff(c_46, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_142])).
% 3.07/1.53  tff(c_74, plain, (![C_53, A_54, B_55]: (v1_relat_1(C_53) | ~m1_subset_1(C_53, k1_zfmisc_1(k2_zfmisc_1(A_54, B_55))))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.07/1.53  tff(c_86, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_46, c_74])).
% 3.07/1.53  tff(c_48, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_142])).
% 3.07/1.53  tff(c_40, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_142])).
% 3.07/1.53  tff(c_52, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_142])).
% 3.07/1.53  tff(c_50, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_142])).
% 3.07/1.53  tff(c_129, plain, (![A_66, B_67, C_68]: (k1_relset_1(A_66, B_67, C_68)=k1_relat_1(C_68) | ~m1_subset_1(C_68, k1_zfmisc_1(k2_zfmisc_1(A_66, B_67))))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.07/1.53  tff(c_142, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_50, c_129])).
% 3.07/1.53  tff(c_223, plain, (![B_87, A_88, C_89]: (k1_xboole_0=B_87 | k1_relset_1(A_88, B_87, C_89)=A_88 | ~v1_funct_2(C_89, A_88, B_87) | ~m1_subset_1(C_89, k1_zfmisc_1(k2_zfmisc_1(A_88, B_87))))), inference(cnfTransformation, [status(thm)], [f_107])).
% 3.07/1.53  tff(c_233, plain, (k1_xboole_0='#skF_3' | k1_relset_1('#skF_2', '#skF_3', '#skF_4')='#skF_2' | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_50, c_223])).
% 3.07/1.53  tff(c_239, plain, (k1_xboole_0='#skF_3' | k1_relat_1('#skF_4')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_52, c_142, c_233])).
% 3.07/1.53  tff(c_240, plain, (k1_relat_1('#skF_4')='#skF_2'), inference(splitLeft, [status(thm)], [c_239])).
% 3.07/1.53  tff(c_87, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_50, c_74])).
% 3.07/1.54  tff(c_54, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_142])).
% 3.07/1.54  tff(c_10, plain, (![A_6, B_7]: (r2_hidden(A_6, B_7) | v1_xboole_0(B_7) | ~m1_subset_1(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.07/1.54  tff(c_312, plain, (![B_101, C_102, A_103]: (k1_funct_1(k5_relat_1(B_101, C_102), A_103)=k1_funct_1(C_102, k1_funct_1(B_101, A_103)) | ~r2_hidden(A_103, k1_relat_1(B_101)) | ~v1_funct_1(C_102) | ~v1_relat_1(C_102) | ~v1_funct_1(B_101) | ~v1_relat_1(B_101))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.07/1.54  tff(c_341, plain, (![B_108, C_109, A_110]: (k1_funct_1(k5_relat_1(B_108, C_109), A_110)=k1_funct_1(C_109, k1_funct_1(B_108, A_110)) | ~v1_funct_1(C_109) | ~v1_relat_1(C_109) | ~v1_funct_1(B_108) | ~v1_relat_1(B_108) | v1_xboole_0(k1_relat_1(B_108)) | ~m1_subset_1(A_110, k1_relat_1(B_108)))), inference(resolution, [status(thm)], [c_10, c_312])).
% 3.07/1.54  tff(c_343, plain, (![C_109, A_110]: (k1_funct_1(k5_relat_1('#skF_4', C_109), A_110)=k1_funct_1(C_109, k1_funct_1('#skF_4', A_110)) | ~v1_funct_1(C_109) | ~v1_relat_1(C_109) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4') | v1_xboole_0(k1_relat_1('#skF_4')) | ~m1_subset_1(A_110, '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_240, c_341])).
% 3.07/1.54  tff(c_345, plain, (![C_109, A_110]: (k1_funct_1(k5_relat_1('#skF_4', C_109), A_110)=k1_funct_1(C_109, k1_funct_1('#skF_4', A_110)) | ~v1_funct_1(C_109) | ~v1_relat_1(C_109) | v1_xboole_0('#skF_2') | ~m1_subset_1(A_110, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_240, c_87, c_54, c_343])).
% 3.07/1.54  tff(c_346, plain, (v1_xboole_0('#skF_2')), inference(splitLeft, [status(thm)], [c_345])).
% 3.07/1.54  tff(c_2, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.07/1.54  tff(c_349, plain, (k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_346, c_2])).
% 3.07/1.54  tff(c_353, plain, $false, inference(negUnitSimplification, [status(thm)], [c_40, c_349])).
% 3.07/1.54  tff(c_354, plain, (![C_109, A_110]: (k1_funct_1(k5_relat_1('#skF_4', C_109), A_110)=k1_funct_1(C_109, k1_funct_1('#skF_4', A_110)) | ~v1_funct_1(C_109) | ~v1_relat_1(C_109) | ~m1_subset_1(A_110, '#skF_2'))), inference(splitRight, [status(thm)], [c_345])).
% 3.07/1.54  tff(c_373, plain, (![B_114, F_116, E_117, A_115, D_113, C_118]: (k1_partfun1(A_115, B_114, C_118, D_113, E_117, F_116)=k5_relat_1(E_117, F_116) | ~m1_subset_1(F_116, k1_zfmisc_1(k2_zfmisc_1(C_118, D_113))) | ~v1_funct_1(F_116) | ~m1_subset_1(E_117, k1_zfmisc_1(k2_zfmisc_1(A_115, B_114))) | ~v1_funct_1(E_117))), inference(cnfTransformation, [status(thm)], [f_117])).
% 3.07/1.54  tff(c_378, plain, (![A_115, B_114, E_117]: (k1_partfun1(A_115, B_114, '#skF_3', '#skF_1', E_117, '#skF_5')=k5_relat_1(E_117, '#skF_5') | ~v1_funct_1('#skF_5') | ~m1_subset_1(E_117, k1_zfmisc_1(k2_zfmisc_1(A_115, B_114))) | ~v1_funct_1(E_117))), inference(resolution, [status(thm)], [c_46, c_373])).
% 3.07/1.54  tff(c_388, plain, (![A_119, B_120, E_121]: (k1_partfun1(A_119, B_120, '#skF_3', '#skF_1', E_121, '#skF_5')=k5_relat_1(E_121, '#skF_5') | ~m1_subset_1(E_121, k1_zfmisc_1(k2_zfmisc_1(A_119, B_120))) | ~v1_funct_1(E_121))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_378])).
% 3.07/1.54  tff(c_398, plain, (k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_1', '#skF_4', '#skF_5')=k5_relat_1('#skF_4', '#skF_5') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_50, c_388])).
% 3.07/1.54  tff(c_405, plain, (k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_1', '#skF_4', '#skF_5')=k5_relat_1('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_398])).
% 3.07/1.54  tff(c_141, plain, (k1_relset_1('#skF_3', '#skF_1', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_46, c_129])).
% 3.07/1.54  tff(c_42, plain, (r1_tarski(k2_relset_1('#skF_2', '#skF_3', '#skF_4'), k1_relset_1('#skF_3', '#skF_1', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_142])).
% 3.07/1.54  tff(c_143, plain, (r1_tarski(k2_relset_1('#skF_2', '#skF_3', '#skF_4'), k1_relat_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_141, c_42])).
% 3.07/1.54  tff(c_406, plain, (![E_126, C_122, D_124, A_125, B_123]: (k1_partfun1(A_125, B_123, B_123, C_122, D_124, E_126)=k8_funct_2(A_125, B_123, C_122, D_124, E_126) | k1_xboole_0=B_123 | ~r1_tarski(k2_relset_1(A_125, B_123, D_124), k1_relset_1(B_123, C_122, E_126)) | ~m1_subset_1(E_126, k1_zfmisc_1(k2_zfmisc_1(B_123, C_122))) | ~v1_funct_1(E_126) | ~m1_subset_1(D_124, k1_zfmisc_1(k2_zfmisc_1(A_125, B_123))) | ~v1_funct_2(D_124, A_125, B_123) | ~v1_funct_1(D_124))), inference(cnfTransformation, [status(thm)], [f_89])).
% 3.07/1.54  tff(c_415, plain, (![A_125, D_124]: (k1_partfun1(A_125, '#skF_3', '#skF_3', '#skF_1', D_124, '#skF_5')=k8_funct_2(A_125, '#skF_3', '#skF_1', D_124, '#skF_5') | k1_xboole_0='#skF_3' | ~r1_tarski(k2_relset_1(A_125, '#skF_3', D_124), k1_relat_1('#skF_5')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_1'))) | ~v1_funct_1('#skF_5') | ~m1_subset_1(D_124, k1_zfmisc_1(k2_zfmisc_1(A_125, '#skF_3'))) | ~v1_funct_2(D_124, A_125, '#skF_3') | ~v1_funct_1(D_124))), inference(superposition, [status(thm), theory('equality')], [c_141, c_406])).
% 3.07/1.54  tff(c_420, plain, (![A_125, D_124]: (k1_partfun1(A_125, '#skF_3', '#skF_3', '#skF_1', D_124, '#skF_5')=k8_funct_2(A_125, '#skF_3', '#skF_1', D_124, '#skF_5') | k1_xboole_0='#skF_3' | ~r1_tarski(k2_relset_1(A_125, '#skF_3', D_124), k1_relat_1('#skF_5')) | ~m1_subset_1(D_124, k1_zfmisc_1(k2_zfmisc_1(A_125, '#skF_3'))) | ~v1_funct_2(D_124, A_125, '#skF_3') | ~v1_funct_1(D_124))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_415])).
% 3.07/1.54  tff(c_565, plain, (k1_xboole_0='#skF_3'), inference(splitLeft, [status(thm)], [c_420])).
% 3.07/1.54  tff(c_4, plain, (![A_2]: (r1_tarski(k1_xboole_0, A_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.07/1.54  tff(c_6, plain, (![A_3]: (r1_xboole_0(A_3, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.07/1.54  tff(c_104, plain, (![B_59, A_60]: (~r1_xboole_0(B_59, A_60) | ~r1_tarski(B_59, A_60) | v1_xboole_0(B_59))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.07/1.54  tff(c_109, plain, (![A_61]: (~r1_tarski(A_61, k1_xboole_0) | v1_xboole_0(A_61))), inference(resolution, [status(thm)], [c_6, c_104])).
% 3.07/1.54  tff(c_114, plain, (v1_xboole_0(k1_xboole_0)), inference(resolution, [status(thm)], [c_4, c_109])).
% 3.07/1.54  tff(c_584, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_565, c_114])).
% 3.07/1.54  tff(c_592, plain, $false, inference(negUnitSimplification, [status(thm)], [c_56, c_584])).
% 3.07/1.54  tff(c_595, plain, (![A_158, D_159]: (k1_partfun1(A_158, '#skF_3', '#skF_3', '#skF_1', D_159, '#skF_5')=k8_funct_2(A_158, '#skF_3', '#skF_1', D_159, '#skF_5') | ~r1_tarski(k2_relset_1(A_158, '#skF_3', D_159), k1_relat_1('#skF_5')) | ~m1_subset_1(D_159, k1_zfmisc_1(k2_zfmisc_1(A_158, '#skF_3'))) | ~v1_funct_2(D_159, A_158, '#skF_3') | ~v1_funct_1(D_159))), inference(splitRight, [status(thm)], [c_420])).
% 3.07/1.54  tff(c_598, plain, (k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_1', '#skF_4', '#skF_5')=k8_funct_2('#skF_2', '#skF_3', '#skF_1', '#skF_4', '#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_143, c_595])).
% 3.07/1.54  tff(c_601, plain, (k8_funct_2('#skF_2', '#skF_3', '#skF_1', '#skF_4', '#skF_5')=k5_relat_1('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_50, c_405, c_598])).
% 3.07/1.54  tff(c_38, plain, (k1_funct_1(k8_funct_2('#skF_2', '#skF_3', '#skF_1', '#skF_4', '#skF_5'), '#skF_6')!=k1_funct_1('#skF_5', k1_funct_1('#skF_4', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_142])).
% 3.07/1.54  tff(c_602, plain, (k1_funct_1(k5_relat_1('#skF_4', '#skF_5'), '#skF_6')!=k1_funct_1('#skF_5', k1_funct_1('#skF_4', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_601, c_38])).
% 3.07/1.54  tff(c_609, plain, (~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5') | ~m1_subset_1('#skF_6', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_354, c_602])).
% 3.07/1.54  tff(c_616, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_44, c_86, c_48, c_609])).
% 3.07/1.54  tff(c_617, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_239])).
% 3.07/1.54  tff(c_630, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_617, c_114])).
% 3.07/1.54  tff(c_638, plain, $false, inference(negUnitSimplification, [status(thm)], [c_56, c_630])).
% 3.07/1.54  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.07/1.54  
% 3.07/1.54  Inference rules
% 3.07/1.54  ----------------------
% 3.07/1.54  #Ref     : 0
% 3.07/1.54  #Sup     : 105
% 3.07/1.54  #Fact    : 0
% 3.07/1.54  #Define  : 0
% 3.07/1.54  #Split   : 7
% 3.07/1.54  #Chain   : 0
% 3.07/1.54  #Close   : 0
% 3.07/1.54  
% 3.07/1.54  Ordering : KBO
% 3.07/1.54  
% 3.07/1.54  Simplification rules
% 3.07/1.54  ----------------------
% 3.07/1.54  #Subsume      : 10
% 3.07/1.54  #Demod        : 159
% 3.07/1.54  #Tautology    : 47
% 3.07/1.54  #SimpNegUnit  : 7
% 3.07/1.54  #BackRed      : 46
% 3.07/1.54  
% 3.07/1.54  #Partial instantiations: 0
% 3.07/1.54  #Strategies tried      : 1
% 3.07/1.54  
% 3.07/1.54  Timing (in seconds)
% 3.07/1.54  ----------------------
% 3.07/1.54  Preprocessing        : 0.38
% 3.07/1.54  Parsing              : 0.20
% 3.07/1.54  CNF conversion       : 0.03
% 3.07/1.54  Main loop            : 0.34
% 3.07/1.54  Inferencing          : 0.12
% 3.07/1.54  Reduction            : 0.11
% 3.07/1.54  Demodulation         : 0.08
% 3.07/1.54  BG Simplification    : 0.02
% 3.07/1.54  Subsumption          : 0.06
% 3.07/1.54  Abstraction          : 0.02
% 3.07/1.54  MUC search           : 0.00
% 3.07/1.54  Cooper               : 0.00
% 3.07/1.54  Total                : 0.75
% 3.07/1.54  Index Insertion      : 0.00
% 3.07/1.54  Index Deletion       : 0.00
% 3.07/1.54  Index Matching       : 0.00
% 3.07/1.54  BG Taut test         : 0.00
%------------------------------------------------------------------------------
