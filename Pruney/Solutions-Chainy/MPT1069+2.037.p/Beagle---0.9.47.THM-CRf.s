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
% DateTime   : Thu Dec  3 10:17:50 EST 2020

% Result     : Theorem 9.05s
% Output     : CNFRefutation 9.23s
% Verified   : 
% Statistics : Number of formulae       :  121 ( 322 expanded)
%              Number of leaves         :   47 ( 132 expanded)
%              Depth                    :   14
%              Number of atoms          :  244 (1105 expanded)
%              Number of equality atoms :   57 ( 266 expanded)
%              Maximal formula depth    :   17 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k8_funct_2 > k7_partfun1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_9 > #skF_8 > #skF_4 > #skF_3 > #skF_2

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

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k7_partfun1,type,(
    k7_partfun1: ( $i * $i * $i ) > $i )).

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

tff('#skF_9',type,(
    '#skF_9': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

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

tff('#skF_3',type,(
    '#skF_3': $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_203,negated_conjecture,(
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
                        | k1_funct_1(k8_funct_2(B,C,A,D,E),F) = k7_partfun1(A,E,k1_funct_1(D,F)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t186_funct_2)).

tff(f_115,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_119,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_178,axiom,(
    ! [A,B,C] :
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

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_105,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_143,axiom,(
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

tff(f_154,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A)
        & v1_funct_1(B) )
     => ! [C] :
          ( r2_hidden(C,k1_relat_1(B))
         => k7_partfun1(A,B,C) = k1_funct_1(B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_partfun1)).

tff(f_57,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_75,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_111,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_125,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(C,A)))
     => ( r1_tarski(k2_relat_1(D),B)
       => m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(C,B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_relset_1)).

tff(f_96,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A)
        & v1_funct_1(B) )
     => ! [C] :
          ( r2_hidden(C,k1_relat_1(B))
         => r2_hidden(k1_funct_1(B,C),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t172_funct_1)).

tff(f_59,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_101,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

tff(c_78,plain,(
    ~ v1_xboole_0('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_203])).

tff(c_66,plain,(
    m1_subset_1('#skF_9','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_203])).

tff(c_62,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_203])).

tff(c_76,plain,(
    v1_funct_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_203])).

tff(c_74,plain,(
    v1_funct_2('#skF_7','#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_203])).

tff(c_72,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_6'))) ),
    inference(cnfTransformation,[status(thm)],[f_203])).

tff(c_68,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_203])).

tff(c_647,plain,(
    ! [A_171,B_172,C_173] :
      ( k1_relset_1(A_171,B_172,C_173) = k1_relat_1(C_173)
      | ~ m1_subset_1(C_173,k1_zfmisc_1(k2_zfmisc_1(A_171,B_172))) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_674,plain,(
    k1_relset_1('#skF_6','#skF_4','#skF_8') = k1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_68,c_647])).

tff(c_527,plain,(
    ! [A_159,B_160,C_161] :
      ( k2_relset_1(A_159,B_160,C_161) = k2_relat_1(C_161)
      | ~ m1_subset_1(C_161,k1_zfmisc_1(k2_zfmisc_1(A_159,B_160))) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_543,plain,(
    k2_relset_1('#skF_5','#skF_6','#skF_7') = k2_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_72,c_527])).

tff(c_64,plain,(
    r1_tarski(k2_relset_1('#skF_5','#skF_6','#skF_7'),k1_relset_1('#skF_6','#skF_4','#skF_8')) ),
    inference(cnfTransformation,[status(thm)],[f_203])).

tff(c_546,plain,(
    r1_tarski(k2_relat_1('#skF_7'),k1_relset_1('#skF_6','#skF_4','#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_543,c_64])).

tff(c_688,plain,(
    r1_tarski(k2_relat_1('#skF_7'),k1_relat_1('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_674,c_546])).

tff(c_70,plain,(
    v1_funct_1('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_203])).

tff(c_3562,plain,(
    ! [C_410,F_409,B_407,D_408,A_406,E_405] :
      ( k1_funct_1(k8_funct_2(B_407,C_410,A_406,D_408,E_405),F_409) = k1_funct_1(E_405,k1_funct_1(D_408,F_409))
      | k1_xboole_0 = B_407
      | ~ r1_tarski(k2_relset_1(B_407,C_410,D_408),k1_relset_1(C_410,A_406,E_405))
      | ~ m1_subset_1(F_409,B_407)
      | ~ m1_subset_1(E_405,k1_zfmisc_1(k2_zfmisc_1(C_410,A_406)))
      | ~ v1_funct_1(E_405)
      | ~ m1_subset_1(D_408,k1_zfmisc_1(k2_zfmisc_1(B_407,C_410)))
      | ~ v1_funct_2(D_408,B_407,C_410)
      | ~ v1_funct_1(D_408)
      | v1_xboole_0(C_410) ) ),
    inference(cnfTransformation,[status(thm)],[f_178])).

tff(c_3570,plain,(
    ! [B_407,D_408,F_409] :
      ( k1_funct_1(k8_funct_2(B_407,'#skF_6','#skF_4',D_408,'#skF_8'),F_409) = k1_funct_1('#skF_8',k1_funct_1(D_408,F_409))
      | k1_xboole_0 = B_407
      | ~ r1_tarski(k2_relset_1(B_407,'#skF_6',D_408),k1_relat_1('#skF_8'))
      | ~ m1_subset_1(F_409,B_407)
      | ~ m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_4')))
      | ~ v1_funct_1('#skF_8')
      | ~ m1_subset_1(D_408,k1_zfmisc_1(k2_zfmisc_1(B_407,'#skF_6')))
      | ~ v1_funct_2(D_408,B_407,'#skF_6')
      | ~ v1_funct_1(D_408)
      | v1_xboole_0('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_674,c_3562])).

tff(c_3587,plain,(
    ! [B_407,D_408,F_409] :
      ( k1_funct_1(k8_funct_2(B_407,'#skF_6','#skF_4',D_408,'#skF_8'),F_409) = k1_funct_1('#skF_8',k1_funct_1(D_408,F_409))
      | k1_xboole_0 = B_407
      | ~ r1_tarski(k2_relset_1(B_407,'#skF_6',D_408),k1_relat_1('#skF_8'))
      | ~ m1_subset_1(F_409,B_407)
      | ~ m1_subset_1(D_408,k1_zfmisc_1(k2_zfmisc_1(B_407,'#skF_6')))
      | ~ v1_funct_2(D_408,B_407,'#skF_6')
      | ~ v1_funct_1(D_408)
      | v1_xboole_0('#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_3570])).

tff(c_3735,plain,(
    ! [B_427,D_428,F_429] :
      ( k1_funct_1(k8_funct_2(B_427,'#skF_6','#skF_4',D_428,'#skF_8'),F_429) = k1_funct_1('#skF_8',k1_funct_1(D_428,F_429))
      | k1_xboole_0 = B_427
      | ~ r1_tarski(k2_relset_1(B_427,'#skF_6',D_428),k1_relat_1('#skF_8'))
      | ~ m1_subset_1(F_429,B_427)
      | ~ m1_subset_1(D_428,k1_zfmisc_1(k2_zfmisc_1(B_427,'#skF_6')))
      | ~ v1_funct_2(D_428,B_427,'#skF_6')
      | ~ v1_funct_1(D_428) ) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_3587])).

tff(c_3740,plain,(
    ! [F_429] :
      ( k1_funct_1(k8_funct_2('#skF_5','#skF_6','#skF_4','#skF_7','#skF_8'),F_429) = k1_funct_1('#skF_8',k1_funct_1('#skF_7',F_429))
      | k1_xboole_0 = '#skF_5'
      | ~ r1_tarski(k2_relat_1('#skF_7'),k1_relat_1('#skF_8'))
      | ~ m1_subset_1(F_429,'#skF_5')
      | ~ m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_6')))
      | ~ v1_funct_2('#skF_7','#skF_5','#skF_6')
      | ~ v1_funct_1('#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_543,c_3735])).

tff(c_3744,plain,(
    ! [F_429] :
      ( k1_funct_1(k8_funct_2('#skF_5','#skF_6','#skF_4','#skF_7','#skF_8'),F_429) = k1_funct_1('#skF_8',k1_funct_1('#skF_7',F_429))
      | k1_xboole_0 = '#skF_5'
      | ~ m1_subset_1(F_429,'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_72,c_688,c_3740])).

tff(c_3745,plain,(
    ! [F_429] :
      ( k1_funct_1(k8_funct_2('#skF_5','#skF_6','#skF_4','#skF_7','#skF_8'),F_429) = k1_funct_1('#skF_8',k1_funct_1('#skF_7',F_429))
      | ~ m1_subset_1(F_429,'#skF_5') ) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_3744])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_171,plain,(
    ! [C_106,A_107,B_108] :
      ( v1_relat_1(C_106)
      | ~ m1_subset_1(C_106,k1_zfmisc_1(k2_zfmisc_1(A_107,B_108))) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_187,plain,(
    v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_72,c_171])).

tff(c_673,plain,(
    k1_relset_1('#skF_5','#skF_6','#skF_7') = k1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_72,c_647])).

tff(c_2757,plain,(
    ! [B_333,A_334,C_335] :
      ( k1_xboole_0 = B_333
      | k1_relset_1(A_334,B_333,C_335) = A_334
      | ~ v1_funct_2(C_335,A_334,B_333)
      | ~ m1_subset_1(C_335,k1_zfmisc_1(k2_zfmisc_1(A_334,B_333))) ) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_2782,plain,
    ( k1_xboole_0 = '#skF_6'
    | k1_relset_1('#skF_5','#skF_6','#skF_7') = '#skF_5'
    | ~ v1_funct_2('#skF_7','#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_72,c_2757])).

tff(c_2798,plain,
    ( k1_xboole_0 = '#skF_6'
    | k1_relat_1('#skF_7') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_673,c_2782])).

tff(c_2803,plain,(
    k1_relat_1('#skF_7') = '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_2798])).

tff(c_3447,plain,(
    ! [A_394,B_395,C_396] :
      ( k7_partfun1(A_394,B_395,C_396) = k1_funct_1(B_395,C_396)
      | ~ r2_hidden(C_396,k1_relat_1(B_395))
      | ~ v1_funct_1(B_395)
      | ~ v5_relat_1(B_395,A_394)
      | ~ v1_relat_1(B_395) ) ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_3449,plain,(
    ! [A_394,C_396] :
      ( k7_partfun1(A_394,'#skF_7',C_396) = k1_funct_1('#skF_7',C_396)
      | ~ r2_hidden(C_396,'#skF_5')
      | ~ v1_funct_1('#skF_7')
      | ~ v5_relat_1('#skF_7',A_394)
      | ~ v1_relat_1('#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2803,c_3447])).

tff(c_4985,plain,(
    ! [A_548,C_549] :
      ( k7_partfun1(A_548,'#skF_7',C_549) = k1_funct_1('#skF_7',C_549)
      | ~ r2_hidden(C_549,'#skF_5')
      | ~ v5_relat_1('#skF_7',A_548) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_187,c_76,c_3449])).

tff(c_5008,plain,(
    ! [A_548] :
      ( k7_partfun1(A_548,'#skF_7','#skF_1'('#skF_5')) = k1_funct_1('#skF_7','#skF_1'('#skF_5'))
      | ~ v5_relat_1('#skF_7',A_548)
      | v1_xboole_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_4,c_4985])).

tff(c_5540,plain,(
    v1_xboole_0('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_5008])).

tff(c_84,plain,(
    ! [A_84] :
      ( r2_hidden('#skF_3'(A_84),A_84)
      | k1_xboole_0 = A_84 ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_88,plain,(
    ! [A_84] :
      ( ~ v1_xboole_0(A_84)
      | k1_xboole_0 = A_84 ) ),
    inference(resolution,[status(thm)],[c_84,c_2])).

tff(c_5543,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_5540,c_88])).

tff(c_5547,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_5543])).

tff(c_5549,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(splitRight,[status(thm)],[c_5008])).

tff(c_20,plain,(
    ! [A_16,B_17] :
      ( r2_hidden(A_16,B_17)
      | v1_xboole_0(B_17)
      | ~ m1_subset_1(A_16,B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_355,plain,(
    ! [C_135,B_136,A_137] :
      ( v5_relat_1(C_135,B_136)
      | ~ m1_subset_1(C_135,k1_zfmisc_1(k2_zfmisc_1(A_137,B_136))) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_372,plain,(
    v5_relat_1('#skF_8','#skF_4') ),
    inference(resolution,[status(thm)],[c_68,c_355])).

tff(c_188,plain,(
    v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_68,c_171])).

tff(c_2569,plain,(
    ! [D_319,C_320,B_321,A_322] :
      ( m1_subset_1(D_319,k1_zfmisc_1(k2_zfmisc_1(C_320,B_321)))
      | ~ r1_tarski(k2_relat_1(D_319),B_321)
      | ~ m1_subset_1(D_319,k1_zfmisc_1(k2_zfmisc_1(C_320,A_322))) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_2598,plain,(
    ! [B_324] :
      ( m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_5',B_324)))
      | ~ r1_tarski(k2_relat_1('#skF_7'),B_324) ) ),
    inference(resolution,[status(thm)],[c_72,c_2569])).

tff(c_34,plain,(
    ! [C_34,B_33,A_32] :
      ( v5_relat_1(C_34,B_33)
      | ~ m1_subset_1(C_34,k1_zfmisc_1(k2_zfmisc_1(A_32,B_33))) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_2676,plain,(
    ! [B_326] :
      ( v5_relat_1('#skF_7',B_326)
      | ~ r1_tarski(k2_relat_1('#skF_7'),B_326) ) ),
    inference(resolution,[status(thm)],[c_2598,c_34])).

tff(c_2680,plain,(
    v5_relat_1('#skF_7',k1_relat_1('#skF_8')) ),
    inference(resolution,[status(thm)],[c_688,c_2676])).

tff(c_28,plain,(
    ! [B_24,C_26,A_23] :
      ( r2_hidden(k1_funct_1(B_24,C_26),A_23)
      | ~ r2_hidden(C_26,k1_relat_1(B_24))
      | ~ v1_funct_1(B_24)
      | ~ v5_relat_1(B_24,A_23)
      | ~ v1_relat_1(B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_7996,plain,(
    ! [A_689,B_690,B_691,C_692] :
      ( k7_partfun1(A_689,B_690,k1_funct_1(B_691,C_692)) = k1_funct_1(B_690,k1_funct_1(B_691,C_692))
      | ~ v1_funct_1(B_690)
      | ~ v5_relat_1(B_690,A_689)
      | ~ v1_relat_1(B_690)
      | ~ r2_hidden(C_692,k1_relat_1(B_691))
      | ~ v1_funct_1(B_691)
      | ~ v5_relat_1(B_691,k1_relat_1(B_690))
      | ~ v1_relat_1(B_691) ) ),
    inference(resolution,[status(thm)],[c_28,c_3447])).

tff(c_7998,plain,(
    ! [A_689,B_690,C_692] :
      ( k7_partfun1(A_689,B_690,k1_funct_1('#skF_7',C_692)) = k1_funct_1(B_690,k1_funct_1('#skF_7',C_692))
      | ~ v1_funct_1(B_690)
      | ~ v5_relat_1(B_690,A_689)
      | ~ v1_relat_1(B_690)
      | ~ r2_hidden(C_692,'#skF_5')
      | ~ v1_funct_1('#skF_7')
      | ~ v5_relat_1('#skF_7',k1_relat_1(B_690))
      | ~ v1_relat_1('#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2803,c_7996])).

tff(c_9582,plain,(
    ! [A_786,B_787,C_788] :
      ( k7_partfun1(A_786,B_787,k1_funct_1('#skF_7',C_788)) = k1_funct_1(B_787,k1_funct_1('#skF_7',C_788))
      | ~ v1_funct_1(B_787)
      | ~ v5_relat_1(B_787,A_786)
      | ~ v1_relat_1(B_787)
      | ~ r2_hidden(C_788,'#skF_5')
      | ~ v5_relat_1('#skF_7',k1_relat_1(B_787)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_187,c_76,c_7998])).

tff(c_9586,plain,(
    ! [A_786,C_788] :
      ( k7_partfun1(A_786,'#skF_8',k1_funct_1('#skF_7',C_788)) = k1_funct_1('#skF_8',k1_funct_1('#skF_7',C_788))
      | ~ v1_funct_1('#skF_8')
      | ~ v5_relat_1('#skF_8',A_786)
      | ~ v1_relat_1('#skF_8')
      | ~ r2_hidden(C_788,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_2680,c_9582])).

tff(c_10772,plain,(
    ! [A_859,C_860] :
      ( k7_partfun1(A_859,'#skF_8',k1_funct_1('#skF_7',C_860)) = k1_funct_1('#skF_8',k1_funct_1('#skF_7',C_860))
      | ~ v5_relat_1('#skF_8',A_859)
      | ~ r2_hidden(C_860,'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_188,c_70,c_9586])).

tff(c_60,plain,(
    k7_partfun1('#skF_4','#skF_8',k1_funct_1('#skF_7','#skF_9')) != k1_funct_1(k8_funct_2('#skF_5','#skF_6','#skF_4','#skF_7','#skF_8'),'#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_203])).

tff(c_10794,plain,
    ( k1_funct_1(k8_funct_2('#skF_5','#skF_6','#skF_4','#skF_7','#skF_8'),'#skF_9') != k1_funct_1('#skF_8',k1_funct_1('#skF_7','#skF_9'))
    | ~ v5_relat_1('#skF_8','#skF_4')
    | ~ r2_hidden('#skF_9','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_10772,c_60])).

tff(c_10827,plain,
    ( k1_funct_1(k8_funct_2('#skF_5','#skF_6','#skF_4','#skF_7','#skF_8'),'#skF_9') != k1_funct_1('#skF_8',k1_funct_1('#skF_7','#skF_9'))
    | ~ r2_hidden('#skF_9','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_372,c_10794])).

tff(c_10840,plain,(
    ~ r2_hidden('#skF_9','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_10827])).

tff(c_10843,plain,
    ( v1_xboole_0('#skF_5')
    | ~ m1_subset_1('#skF_9','#skF_5') ),
    inference(resolution,[status(thm)],[c_20,c_10840])).

tff(c_10846,plain,(
    v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_10843])).

tff(c_10848,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_5549,c_10846])).

tff(c_10849,plain,(
    k1_funct_1(k8_funct_2('#skF_5','#skF_6','#skF_4','#skF_7','#skF_8'),'#skF_9') != k1_funct_1('#skF_8',k1_funct_1('#skF_7','#skF_9')) ),
    inference(splitRight,[status(thm)],[c_10827])).

tff(c_10894,plain,(
    ~ m1_subset_1('#skF_9','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_3745,c_10849])).

tff(c_10898,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_10894])).

tff(c_10899,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_2798])).

tff(c_14,plain,(
    ! [A_12] : r1_tarski(k1_xboole_0,A_12) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_95,plain,(
    ! [A_88] :
      ( v1_xboole_0(A_88)
      | r2_hidden('#skF_1'(A_88),A_88) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_30,plain,(
    ! [B_28,A_27] :
      ( ~ r1_tarski(B_28,A_27)
      | ~ r2_hidden(A_27,B_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_105,plain,(
    ! [A_90] :
      ( ~ r1_tarski(A_90,'#skF_1'(A_90))
      | v1_xboole_0(A_90) ) ),
    inference(resolution,[status(thm)],[c_95,c_30])).

tff(c_110,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_14,c_105])).

tff(c_10973,plain,(
    v1_xboole_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10899,c_110])).

tff(c_10981,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_10973])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n019.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 16:33:22 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 9.05/3.28  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.05/3.29  
% 9.05/3.29  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.05/3.29  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k8_funct_2 > k7_partfun1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_9 > #skF_8 > #skF_4 > #skF_3 > #skF_2
% 9.05/3.29  
% 9.05/3.29  %Foreground sorts:
% 9.05/3.29  
% 9.05/3.29  
% 9.05/3.29  %Background operators:
% 9.05/3.29  
% 9.05/3.29  
% 9.05/3.29  %Foreground operators:
% 9.05/3.29  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 9.05/3.29  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 9.05/3.29  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 9.05/3.29  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 9.05/3.29  tff('#skF_1', type, '#skF_1': $i > $i).
% 9.05/3.29  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 9.05/3.29  tff('#skF_7', type, '#skF_7': $i).
% 9.05/3.29  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 9.05/3.29  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 9.05/3.29  tff(k7_partfun1, type, k7_partfun1: ($i * $i * $i) > $i).
% 9.05/3.29  tff('#skF_5', type, '#skF_5': $i).
% 9.05/3.29  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 9.05/3.29  tff(k8_funct_2, type, k8_funct_2: ($i * $i * $i * $i * $i) > $i).
% 9.05/3.29  tff('#skF_6', type, '#skF_6': $i).
% 9.05/3.29  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 9.05/3.29  tff('#skF_9', type, '#skF_9': $i).
% 9.05/3.29  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 9.05/3.29  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 9.05/3.29  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 9.05/3.29  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 9.05/3.29  tff('#skF_8', type, '#skF_8': $i).
% 9.05/3.29  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 9.05/3.29  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 9.05/3.29  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 9.05/3.29  tff('#skF_4', type, '#skF_4': $i).
% 9.05/3.29  tff('#skF_3', type, '#skF_3': $i > $i).
% 9.05/3.29  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 9.05/3.29  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 9.05/3.29  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 9.05/3.29  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 9.05/3.29  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 9.05/3.29  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 9.05/3.29  
% 9.23/3.31  tff(f_203, negated_conjecture, ~(![A, B, C]: (~v1_xboole_0(C) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, C)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (![E]: ((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(C, A)))) => (![F]: (m1_subset_1(F, B) => (r1_tarski(k2_relset_1(B, C, D), k1_relset_1(C, A, E)) => ((B = k1_xboole_0) | (k1_funct_1(k8_funct_2(B, C, A, D, E), F) = k7_partfun1(A, E, k1_funct_1(D, F))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t186_funct_2)).
% 9.23/3.31  tff(f_115, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 9.23/3.31  tff(f_119, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 9.23/3.31  tff(f_178, axiom, (![A, B, C]: (~v1_xboole_0(C) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, C)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (![E]: ((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(C, A)))) => (![F]: (m1_subset_1(F, B) => (r1_tarski(k2_relset_1(B, C, D), k1_relset_1(C, A, E)) => ((B = k1_xboole_0) | (k1_funct_1(k8_funct_2(B, C, A, D, E), F) = k1_funct_1(E, k1_funct_1(D, F))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t185_funct_2)).
% 9.23/3.31  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 9.23/3.31  tff(f_105, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 9.23/3.31  tff(f_143, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 9.23/3.31  tff(f_154, axiom, (![A, B]: (((v1_relat_1(B) & v5_relat_1(B, A)) & v1_funct_1(B)) => (![C]: (r2_hidden(C, k1_relat_1(B)) => (k7_partfun1(A, B, C) = k1_funct_1(B, C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_partfun1)).
% 9.23/3.31  tff(f_57, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 9.23/3.31  tff(f_75, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 9.23/3.31  tff(f_111, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 9.23/3.31  tff(f_125, axiom, (![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(C, A))) => (r1_tarski(k2_relat_1(D), B) => m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(C, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t14_relset_1)).
% 9.23/3.31  tff(f_96, axiom, (![A, B]: (((v1_relat_1(B) & v5_relat_1(B, A)) & v1_funct_1(B)) => (![C]: (r2_hidden(C, k1_relat_1(B)) => r2_hidden(k1_funct_1(B, C), A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t172_funct_1)).
% 9.23/3.31  tff(f_59, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 9.23/3.31  tff(f_101, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 9.23/3.31  tff(c_78, plain, (~v1_xboole_0('#skF_6')), inference(cnfTransformation, [status(thm)], [f_203])).
% 9.23/3.31  tff(c_66, plain, (m1_subset_1('#skF_9', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_203])).
% 9.23/3.31  tff(c_62, plain, (k1_xboole_0!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_203])).
% 9.23/3.31  tff(c_76, plain, (v1_funct_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_203])).
% 9.23/3.31  tff(c_74, plain, (v1_funct_2('#skF_7', '#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_203])).
% 9.23/3.31  tff(c_72, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_6')))), inference(cnfTransformation, [status(thm)], [f_203])).
% 9.23/3.31  tff(c_68, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_6', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_203])).
% 9.23/3.31  tff(c_647, plain, (![A_171, B_172, C_173]: (k1_relset_1(A_171, B_172, C_173)=k1_relat_1(C_173) | ~m1_subset_1(C_173, k1_zfmisc_1(k2_zfmisc_1(A_171, B_172))))), inference(cnfTransformation, [status(thm)], [f_115])).
% 9.23/3.31  tff(c_674, plain, (k1_relset_1('#skF_6', '#skF_4', '#skF_8')=k1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_68, c_647])).
% 9.23/3.31  tff(c_527, plain, (![A_159, B_160, C_161]: (k2_relset_1(A_159, B_160, C_161)=k2_relat_1(C_161) | ~m1_subset_1(C_161, k1_zfmisc_1(k2_zfmisc_1(A_159, B_160))))), inference(cnfTransformation, [status(thm)], [f_119])).
% 9.23/3.31  tff(c_543, plain, (k2_relset_1('#skF_5', '#skF_6', '#skF_7')=k2_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_72, c_527])).
% 9.23/3.31  tff(c_64, plain, (r1_tarski(k2_relset_1('#skF_5', '#skF_6', '#skF_7'), k1_relset_1('#skF_6', '#skF_4', '#skF_8'))), inference(cnfTransformation, [status(thm)], [f_203])).
% 9.23/3.31  tff(c_546, plain, (r1_tarski(k2_relat_1('#skF_7'), k1_relset_1('#skF_6', '#skF_4', '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_543, c_64])).
% 9.23/3.31  tff(c_688, plain, (r1_tarski(k2_relat_1('#skF_7'), k1_relat_1('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_674, c_546])).
% 9.23/3.31  tff(c_70, plain, (v1_funct_1('#skF_8')), inference(cnfTransformation, [status(thm)], [f_203])).
% 9.23/3.31  tff(c_3562, plain, (![C_410, F_409, B_407, D_408, A_406, E_405]: (k1_funct_1(k8_funct_2(B_407, C_410, A_406, D_408, E_405), F_409)=k1_funct_1(E_405, k1_funct_1(D_408, F_409)) | k1_xboole_0=B_407 | ~r1_tarski(k2_relset_1(B_407, C_410, D_408), k1_relset_1(C_410, A_406, E_405)) | ~m1_subset_1(F_409, B_407) | ~m1_subset_1(E_405, k1_zfmisc_1(k2_zfmisc_1(C_410, A_406))) | ~v1_funct_1(E_405) | ~m1_subset_1(D_408, k1_zfmisc_1(k2_zfmisc_1(B_407, C_410))) | ~v1_funct_2(D_408, B_407, C_410) | ~v1_funct_1(D_408) | v1_xboole_0(C_410))), inference(cnfTransformation, [status(thm)], [f_178])).
% 9.23/3.31  tff(c_3570, plain, (![B_407, D_408, F_409]: (k1_funct_1(k8_funct_2(B_407, '#skF_6', '#skF_4', D_408, '#skF_8'), F_409)=k1_funct_1('#skF_8', k1_funct_1(D_408, F_409)) | k1_xboole_0=B_407 | ~r1_tarski(k2_relset_1(B_407, '#skF_6', D_408), k1_relat_1('#skF_8')) | ~m1_subset_1(F_409, B_407) | ~m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_6', '#skF_4'))) | ~v1_funct_1('#skF_8') | ~m1_subset_1(D_408, k1_zfmisc_1(k2_zfmisc_1(B_407, '#skF_6'))) | ~v1_funct_2(D_408, B_407, '#skF_6') | ~v1_funct_1(D_408) | v1_xboole_0('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_674, c_3562])).
% 9.23/3.31  tff(c_3587, plain, (![B_407, D_408, F_409]: (k1_funct_1(k8_funct_2(B_407, '#skF_6', '#skF_4', D_408, '#skF_8'), F_409)=k1_funct_1('#skF_8', k1_funct_1(D_408, F_409)) | k1_xboole_0=B_407 | ~r1_tarski(k2_relset_1(B_407, '#skF_6', D_408), k1_relat_1('#skF_8')) | ~m1_subset_1(F_409, B_407) | ~m1_subset_1(D_408, k1_zfmisc_1(k2_zfmisc_1(B_407, '#skF_6'))) | ~v1_funct_2(D_408, B_407, '#skF_6') | ~v1_funct_1(D_408) | v1_xboole_0('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_3570])).
% 9.23/3.31  tff(c_3735, plain, (![B_427, D_428, F_429]: (k1_funct_1(k8_funct_2(B_427, '#skF_6', '#skF_4', D_428, '#skF_8'), F_429)=k1_funct_1('#skF_8', k1_funct_1(D_428, F_429)) | k1_xboole_0=B_427 | ~r1_tarski(k2_relset_1(B_427, '#skF_6', D_428), k1_relat_1('#skF_8')) | ~m1_subset_1(F_429, B_427) | ~m1_subset_1(D_428, k1_zfmisc_1(k2_zfmisc_1(B_427, '#skF_6'))) | ~v1_funct_2(D_428, B_427, '#skF_6') | ~v1_funct_1(D_428))), inference(negUnitSimplification, [status(thm)], [c_78, c_3587])).
% 9.23/3.31  tff(c_3740, plain, (![F_429]: (k1_funct_1(k8_funct_2('#skF_5', '#skF_6', '#skF_4', '#skF_7', '#skF_8'), F_429)=k1_funct_1('#skF_8', k1_funct_1('#skF_7', F_429)) | k1_xboole_0='#skF_5' | ~r1_tarski(k2_relat_1('#skF_7'), k1_relat_1('#skF_8')) | ~m1_subset_1(F_429, '#skF_5') | ~m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_6'))) | ~v1_funct_2('#skF_7', '#skF_5', '#skF_6') | ~v1_funct_1('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_543, c_3735])).
% 9.23/3.31  tff(c_3744, plain, (![F_429]: (k1_funct_1(k8_funct_2('#skF_5', '#skF_6', '#skF_4', '#skF_7', '#skF_8'), F_429)=k1_funct_1('#skF_8', k1_funct_1('#skF_7', F_429)) | k1_xboole_0='#skF_5' | ~m1_subset_1(F_429, '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_74, c_72, c_688, c_3740])).
% 9.23/3.31  tff(c_3745, plain, (![F_429]: (k1_funct_1(k8_funct_2('#skF_5', '#skF_6', '#skF_4', '#skF_7', '#skF_8'), F_429)=k1_funct_1('#skF_8', k1_funct_1('#skF_7', F_429)) | ~m1_subset_1(F_429, '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_62, c_3744])).
% 9.23/3.31  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 9.23/3.31  tff(c_171, plain, (![C_106, A_107, B_108]: (v1_relat_1(C_106) | ~m1_subset_1(C_106, k1_zfmisc_1(k2_zfmisc_1(A_107, B_108))))), inference(cnfTransformation, [status(thm)], [f_105])).
% 9.23/3.31  tff(c_187, plain, (v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_72, c_171])).
% 9.23/3.31  tff(c_673, plain, (k1_relset_1('#skF_5', '#skF_6', '#skF_7')=k1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_72, c_647])).
% 9.23/3.31  tff(c_2757, plain, (![B_333, A_334, C_335]: (k1_xboole_0=B_333 | k1_relset_1(A_334, B_333, C_335)=A_334 | ~v1_funct_2(C_335, A_334, B_333) | ~m1_subset_1(C_335, k1_zfmisc_1(k2_zfmisc_1(A_334, B_333))))), inference(cnfTransformation, [status(thm)], [f_143])).
% 9.23/3.31  tff(c_2782, plain, (k1_xboole_0='#skF_6' | k1_relset_1('#skF_5', '#skF_6', '#skF_7')='#skF_5' | ~v1_funct_2('#skF_7', '#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_72, c_2757])).
% 9.23/3.31  tff(c_2798, plain, (k1_xboole_0='#skF_6' | k1_relat_1('#skF_7')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_74, c_673, c_2782])).
% 9.23/3.31  tff(c_2803, plain, (k1_relat_1('#skF_7')='#skF_5'), inference(splitLeft, [status(thm)], [c_2798])).
% 9.23/3.31  tff(c_3447, plain, (![A_394, B_395, C_396]: (k7_partfun1(A_394, B_395, C_396)=k1_funct_1(B_395, C_396) | ~r2_hidden(C_396, k1_relat_1(B_395)) | ~v1_funct_1(B_395) | ~v5_relat_1(B_395, A_394) | ~v1_relat_1(B_395))), inference(cnfTransformation, [status(thm)], [f_154])).
% 9.23/3.31  tff(c_3449, plain, (![A_394, C_396]: (k7_partfun1(A_394, '#skF_7', C_396)=k1_funct_1('#skF_7', C_396) | ~r2_hidden(C_396, '#skF_5') | ~v1_funct_1('#skF_7') | ~v5_relat_1('#skF_7', A_394) | ~v1_relat_1('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_2803, c_3447])).
% 9.23/3.31  tff(c_4985, plain, (![A_548, C_549]: (k7_partfun1(A_548, '#skF_7', C_549)=k1_funct_1('#skF_7', C_549) | ~r2_hidden(C_549, '#skF_5') | ~v5_relat_1('#skF_7', A_548))), inference(demodulation, [status(thm), theory('equality')], [c_187, c_76, c_3449])).
% 9.23/3.31  tff(c_5008, plain, (![A_548]: (k7_partfun1(A_548, '#skF_7', '#skF_1'('#skF_5'))=k1_funct_1('#skF_7', '#skF_1'('#skF_5')) | ~v5_relat_1('#skF_7', A_548) | v1_xboole_0('#skF_5'))), inference(resolution, [status(thm)], [c_4, c_4985])).
% 9.23/3.31  tff(c_5540, plain, (v1_xboole_0('#skF_5')), inference(splitLeft, [status(thm)], [c_5008])).
% 9.23/3.31  tff(c_84, plain, (![A_84]: (r2_hidden('#skF_3'(A_84), A_84) | k1_xboole_0=A_84)), inference(cnfTransformation, [status(thm)], [f_57])).
% 9.23/3.31  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 9.23/3.31  tff(c_88, plain, (![A_84]: (~v1_xboole_0(A_84) | k1_xboole_0=A_84)), inference(resolution, [status(thm)], [c_84, c_2])).
% 9.23/3.31  tff(c_5543, plain, (k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_5540, c_88])).
% 9.23/3.31  tff(c_5547, plain, $false, inference(negUnitSimplification, [status(thm)], [c_62, c_5543])).
% 9.23/3.31  tff(c_5549, plain, (~v1_xboole_0('#skF_5')), inference(splitRight, [status(thm)], [c_5008])).
% 9.23/3.31  tff(c_20, plain, (![A_16, B_17]: (r2_hidden(A_16, B_17) | v1_xboole_0(B_17) | ~m1_subset_1(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_75])).
% 9.23/3.31  tff(c_355, plain, (![C_135, B_136, A_137]: (v5_relat_1(C_135, B_136) | ~m1_subset_1(C_135, k1_zfmisc_1(k2_zfmisc_1(A_137, B_136))))), inference(cnfTransformation, [status(thm)], [f_111])).
% 9.23/3.31  tff(c_372, plain, (v5_relat_1('#skF_8', '#skF_4')), inference(resolution, [status(thm)], [c_68, c_355])).
% 9.23/3.31  tff(c_188, plain, (v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_68, c_171])).
% 9.23/3.31  tff(c_2569, plain, (![D_319, C_320, B_321, A_322]: (m1_subset_1(D_319, k1_zfmisc_1(k2_zfmisc_1(C_320, B_321))) | ~r1_tarski(k2_relat_1(D_319), B_321) | ~m1_subset_1(D_319, k1_zfmisc_1(k2_zfmisc_1(C_320, A_322))))), inference(cnfTransformation, [status(thm)], [f_125])).
% 9.23/3.31  tff(c_2598, plain, (![B_324]: (m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1('#skF_5', B_324))) | ~r1_tarski(k2_relat_1('#skF_7'), B_324))), inference(resolution, [status(thm)], [c_72, c_2569])).
% 9.23/3.31  tff(c_34, plain, (![C_34, B_33, A_32]: (v5_relat_1(C_34, B_33) | ~m1_subset_1(C_34, k1_zfmisc_1(k2_zfmisc_1(A_32, B_33))))), inference(cnfTransformation, [status(thm)], [f_111])).
% 9.23/3.31  tff(c_2676, plain, (![B_326]: (v5_relat_1('#skF_7', B_326) | ~r1_tarski(k2_relat_1('#skF_7'), B_326))), inference(resolution, [status(thm)], [c_2598, c_34])).
% 9.23/3.31  tff(c_2680, plain, (v5_relat_1('#skF_7', k1_relat_1('#skF_8'))), inference(resolution, [status(thm)], [c_688, c_2676])).
% 9.23/3.31  tff(c_28, plain, (![B_24, C_26, A_23]: (r2_hidden(k1_funct_1(B_24, C_26), A_23) | ~r2_hidden(C_26, k1_relat_1(B_24)) | ~v1_funct_1(B_24) | ~v5_relat_1(B_24, A_23) | ~v1_relat_1(B_24))), inference(cnfTransformation, [status(thm)], [f_96])).
% 9.23/3.31  tff(c_7996, plain, (![A_689, B_690, B_691, C_692]: (k7_partfun1(A_689, B_690, k1_funct_1(B_691, C_692))=k1_funct_1(B_690, k1_funct_1(B_691, C_692)) | ~v1_funct_1(B_690) | ~v5_relat_1(B_690, A_689) | ~v1_relat_1(B_690) | ~r2_hidden(C_692, k1_relat_1(B_691)) | ~v1_funct_1(B_691) | ~v5_relat_1(B_691, k1_relat_1(B_690)) | ~v1_relat_1(B_691))), inference(resolution, [status(thm)], [c_28, c_3447])).
% 9.23/3.31  tff(c_7998, plain, (![A_689, B_690, C_692]: (k7_partfun1(A_689, B_690, k1_funct_1('#skF_7', C_692))=k1_funct_1(B_690, k1_funct_1('#skF_7', C_692)) | ~v1_funct_1(B_690) | ~v5_relat_1(B_690, A_689) | ~v1_relat_1(B_690) | ~r2_hidden(C_692, '#skF_5') | ~v1_funct_1('#skF_7') | ~v5_relat_1('#skF_7', k1_relat_1(B_690)) | ~v1_relat_1('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_2803, c_7996])).
% 9.23/3.31  tff(c_9582, plain, (![A_786, B_787, C_788]: (k7_partfun1(A_786, B_787, k1_funct_1('#skF_7', C_788))=k1_funct_1(B_787, k1_funct_1('#skF_7', C_788)) | ~v1_funct_1(B_787) | ~v5_relat_1(B_787, A_786) | ~v1_relat_1(B_787) | ~r2_hidden(C_788, '#skF_5') | ~v5_relat_1('#skF_7', k1_relat_1(B_787)))), inference(demodulation, [status(thm), theory('equality')], [c_187, c_76, c_7998])).
% 9.23/3.31  tff(c_9586, plain, (![A_786, C_788]: (k7_partfun1(A_786, '#skF_8', k1_funct_1('#skF_7', C_788))=k1_funct_1('#skF_8', k1_funct_1('#skF_7', C_788)) | ~v1_funct_1('#skF_8') | ~v5_relat_1('#skF_8', A_786) | ~v1_relat_1('#skF_8') | ~r2_hidden(C_788, '#skF_5'))), inference(resolution, [status(thm)], [c_2680, c_9582])).
% 9.23/3.31  tff(c_10772, plain, (![A_859, C_860]: (k7_partfun1(A_859, '#skF_8', k1_funct_1('#skF_7', C_860))=k1_funct_1('#skF_8', k1_funct_1('#skF_7', C_860)) | ~v5_relat_1('#skF_8', A_859) | ~r2_hidden(C_860, '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_188, c_70, c_9586])).
% 9.23/3.31  tff(c_60, plain, (k7_partfun1('#skF_4', '#skF_8', k1_funct_1('#skF_7', '#skF_9'))!=k1_funct_1(k8_funct_2('#skF_5', '#skF_6', '#skF_4', '#skF_7', '#skF_8'), '#skF_9')), inference(cnfTransformation, [status(thm)], [f_203])).
% 9.23/3.31  tff(c_10794, plain, (k1_funct_1(k8_funct_2('#skF_5', '#skF_6', '#skF_4', '#skF_7', '#skF_8'), '#skF_9')!=k1_funct_1('#skF_8', k1_funct_1('#skF_7', '#skF_9')) | ~v5_relat_1('#skF_8', '#skF_4') | ~r2_hidden('#skF_9', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_10772, c_60])).
% 9.23/3.31  tff(c_10827, plain, (k1_funct_1(k8_funct_2('#skF_5', '#skF_6', '#skF_4', '#skF_7', '#skF_8'), '#skF_9')!=k1_funct_1('#skF_8', k1_funct_1('#skF_7', '#skF_9')) | ~r2_hidden('#skF_9', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_372, c_10794])).
% 9.23/3.31  tff(c_10840, plain, (~r2_hidden('#skF_9', '#skF_5')), inference(splitLeft, [status(thm)], [c_10827])).
% 9.23/3.31  tff(c_10843, plain, (v1_xboole_0('#skF_5') | ~m1_subset_1('#skF_9', '#skF_5')), inference(resolution, [status(thm)], [c_20, c_10840])).
% 9.23/3.31  tff(c_10846, plain, (v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_10843])).
% 9.23/3.31  tff(c_10848, plain, $false, inference(negUnitSimplification, [status(thm)], [c_5549, c_10846])).
% 9.23/3.31  tff(c_10849, plain, (k1_funct_1(k8_funct_2('#skF_5', '#skF_6', '#skF_4', '#skF_7', '#skF_8'), '#skF_9')!=k1_funct_1('#skF_8', k1_funct_1('#skF_7', '#skF_9'))), inference(splitRight, [status(thm)], [c_10827])).
% 9.23/3.31  tff(c_10894, plain, (~m1_subset_1('#skF_9', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_3745, c_10849])).
% 9.23/3.31  tff(c_10898, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_66, c_10894])).
% 9.23/3.31  tff(c_10899, plain, (k1_xboole_0='#skF_6'), inference(splitRight, [status(thm)], [c_2798])).
% 9.23/3.31  tff(c_14, plain, (![A_12]: (r1_tarski(k1_xboole_0, A_12))), inference(cnfTransformation, [status(thm)], [f_59])).
% 9.23/3.31  tff(c_95, plain, (![A_88]: (v1_xboole_0(A_88) | r2_hidden('#skF_1'(A_88), A_88))), inference(cnfTransformation, [status(thm)], [f_31])).
% 9.23/3.31  tff(c_30, plain, (![B_28, A_27]: (~r1_tarski(B_28, A_27) | ~r2_hidden(A_27, B_28))), inference(cnfTransformation, [status(thm)], [f_101])).
% 9.23/3.31  tff(c_105, plain, (![A_90]: (~r1_tarski(A_90, '#skF_1'(A_90)) | v1_xboole_0(A_90))), inference(resolution, [status(thm)], [c_95, c_30])).
% 9.23/3.31  tff(c_110, plain, (v1_xboole_0(k1_xboole_0)), inference(resolution, [status(thm)], [c_14, c_105])).
% 9.23/3.31  tff(c_10973, plain, (v1_xboole_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_10899, c_110])).
% 9.23/3.31  tff(c_10981, plain, $false, inference(negUnitSimplification, [status(thm)], [c_78, c_10973])).
% 9.23/3.31  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.23/3.31  
% 9.23/3.31  Inference rules
% 9.23/3.31  ----------------------
% 9.23/3.31  #Ref     : 0
% 9.23/3.31  #Sup     : 2143
% 9.23/3.31  #Fact    : 0
% 9.23/3.31  #Define  : 0
% 9.23/3.31  #Split   : 40
% 9.23/3.31  #Chain   : 0
% 9.23/3.31  #Close   : 0
% 9.23/3.31  
% 9.23/3.31  Ordering : KBO
% 9.23/3.31  
% 9.23/3.31  Simplification rules
% 9.23/3.31  ----------------------
% 9.23/3.31  #Subsume      : 214
% 9.23/3.31  #Demod        : 1153
% 9.23/3.31  #Tautology    : 490
% 9.23/3.31  #SimpNegUnit  : 120
% 9.23/3.31  #BackRed      : 248
% 9.23/3.31  
% 9.23/3.31  #Partial instantiations: 0
% 9.23/3.31  #Strategies tried      : 1
% 9.23/3.31  
% 9.23/3.31  Timing (in seconds)
% 9.23/3.31  ----------------------
% 9.23/3.31  Preprocessing        : 0.39
% 9.23/3.31  Parsing              : 0.21
% 9.23/3.31  CNF conversion       : 0.03
% 9.23/3.31  Main loop            : 2.16
% 9.23/3.31  Inferencing          : 0.63
% 9.23/3.31  Reduction            : 0.65
% 9.23/3.31  Demodulation         : 0.43
% 9.23/3.31  BG Simplification    : 0.08
% 9.23/3.31  Subsumption          : 0.61
% 9.23/3.31  Abstraction          : 0.10
% 9.23/3.31  MUC search           : 0.00
% 9.23/3.31  Cooper               : 0.00
% 9.23/3.31  Total                : 2.59
% 9.23/3.31  Index Insertion      : 0.00
% 9.23/3.31  Index Deletion       : 0.00
% 9.23/3.31  Index Matching       : 0.00
% 9.23/3.31  BG Taut test         : 0.00
%------------------------------------------------------------------------------
