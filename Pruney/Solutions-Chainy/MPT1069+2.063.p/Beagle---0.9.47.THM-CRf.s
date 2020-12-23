%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:17:54 EST 2020

% Result     : Theorem 6.45s
% Output     : CNFRefutation 6.45s
% Verified   : 
% Statistics : Number of formulae       :  130 ( 509 expanded)
%              Number of leaves         :   47 ( 200 expanded)
%              Depth                    :   23
%              Number of atoms          :  282 (1746 expanded)
%              Number of equality atoms :   53 ( 381 expanded)
%              Maximal formula depth    :   17 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k8_funct_2 > k7_partfun1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_11 > #skF_7 > #skF_3 > #skF_10 > #skF_6 > #skF_5 > #skF_9 > #skF_8 > #skF_2 > #skF_1 > #skF_4

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

tff('#skF_11',type,(
    '#skF_11': $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k7_partfun1,type,(
    k7_partfun1: ( $i * $i * $i ) > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff(k8_funct_2,type,(
    k8_funct_2: ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

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

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_159,negated_conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t186_funct_2)).

tff(f_77,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_81,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_134,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t185_funct_2)).

tff(f_43,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(f_52,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_50,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_99,axiom,(
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

tff(f_110,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A)
        & v1_funct_1(B) )
     => ! [C] :
          ( r2_hidden(C,k1_relat_1(B))
         => k7_partfun1(A,B,C) = k1_funct_1(B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_partfun1)).

tff(f_37,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_73,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_67,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( B = k2_relat_1(A)
        <=> ! [C] :
              ( r2_hidden(C,B)
            <=> ? [D] :
                  ( r2_hidden(D,k1_relat_1(A))
                  & C = k1_funct_1(A,D) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_funct_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_33,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(c_78,plain,(
    ~ v1_xboole_0('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_66,plain,(
    m1_subset_1('#skF_11','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_70,plain,(
    v1_funct_1('#skF_10') ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_68,plain,(
    m1_subset_1('#skF_10',k1_zfmisc_1(k2_zfmisc_1('#skF_8','#skF_6'))) ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_173,plain,(
    ! [A_130,B_131,C_132] :
      ( k1_relset_1(A_130,B_131,C_132) = k1_relat_1(C_132)
      | ~ m1_subset_1(C_132,k1_zfmisc_1(k2_zfmisc_1(A_130,B_131))) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_181,plain,(
    k1_relset_1('#skF_8','#skF_6','#skF_10') = k1_relat_1('#skF_10') ),
    inference(resolution,[status(thm)],[c_68,c_173])).

tff(c_72,plain,(
    m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1('#skF_7','#skF_8'))) ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_138,plain,(
    ! [A_119,B_120,C_121] :
      ( k2_relset_1(A_119,B_120,C_121) = k2_relat_1(C_121)
      | ~ m1_subset_1(C_121,k1_zfmisc_1(k2_zfmisc_1(A_119,B_120))) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_145,plain,(
    k2_relset_1('#skF_7','#skF_8','#skF_9') = k2_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_72,c_138])).

tff(c_64,plain,(
    r1_tarski(k2_relset_1('#skF_7','#skF_8','#skF_9'),k1_relset_1('#skF_8','#skF_6','#skF_10')) ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_147,plain,(
    r1_tarski(k2_relat_1('#skF_9'),k1_relset_1('#skF_8','#skF_6','#skF_10')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_145,c_64])).

tff(c_187,plain,(
    r1_tarski(k2_relat_1('#skF_9'),k1_relat_1('#skF_10')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_181,c_147])).

tff(c_62,plain,(
    k1_xboole_0 != '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_76,plain,(
    v1_funct_1('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_74,plain,(
    v1_funct_2('#skF_9','#skF_7','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_3873,plain,(
    ! [B_557,A_555,E_558,F_554,C_556,D_553] :
      ( k1_funct_1(k8_funct_2(B_557,C_556,A_555,D_553,E_558),F_554) = k1_funct_1(E_558,k1_funct_1(D_553,F_554))
      | k1_xboole_0 = B_557
      | ~ r1_tarski(k2_relset_1(B_557,C_556,D_553),k1_relset_1(C_556,A_555,E_558))
      | ~ m1_subset_1(F_554,B_557)
      | ~ m1_subset_1(E_558,k1_zfmisc_1(k2_zfmisc_1(C_556,A_555)))
      | ~ v1_funct_1(E_558)
      | ~ m1_subset_1(D_553,k1_zfmisc_1(k2_zfmisc_1(B_557,C_556)))
      | ~ v1_funct_2(D_553,B_557,C_556)
      | ~ v1_funct_1(D_553)
      | v1_xboole_0(C_556) ) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_3881,plain,(
    ! [A_555,E_558,F_554] :
      ( k1_funct_1(k8_funct_2('#skF_7','#skF_8',A_555,'#skF_9',E_558),F_554) = k1_funct_1(E_558,k1_funct_1('#skF_9',F_554))
      | k1_xboole_0 = '#skF_7'
      | ~ r1_tarski(k2_relat_1('#skF_9'),k1_relset_1('#skF_8',A_555,E_558))
      | ~ m1_subset_1(F_554,'#skF_7')
      | ~ m1_subset_1(E_558,k1_zfmisc_1(k2_zfmisc_1('#skF_8',A_555)))
      | ~ v1_funct_1(E_558)
      | ~ m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1('#skF_7','#skF_8')))
      | ~ v1_funct_2('#skF_9','#skF_7','#skF_8')
      | ~ v1_funct_1('#skF_9')
      | v1_xboole_0('#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_145,c_3873])).

tff(c_3891,plain,(
    ! [A_555,E_558,F_554] :
      ( k1_funct_1(k8_funct_2('#skF_7','#skF_8',A_555,'#skF_9',E_558),F_554) = k1_funct_1(E_558,k1_funct_1('#skF_9',F_554))
      | k1_xboole_0 = '#skF_7'
      | ~ r1_tarski(k2_relat_1('#skF_9'),k1_relset_1('#skF_8',A_555,E_558))
      | ~ m1_subset_1(F_554,'#skF_7')
      | ~ m1_subset_1(E_558,k1_zfmisc_1(k2_zfmisc_1('#skF_8',A_555)))
      | ~ v1_funct_1(E_558)
      | v1_xboole_0('#skF_8') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_72,c_3881])).

tff(c_3931,plain,(
    ! [A_563,E_564,F_565] :
      ( k1_funct_1(k8_funct_2('#skF_7','#skF_8',A_563,'#skF_9',E_564),F_565) = k1_funct_1(E_564,k1_funct_1('#skF_9',F_565))
      | ~ r1_tarski(k2_relat_1('#skF_9'),k1_relset_1('#skF_8',A_563,E_564))
      | ~ m1_subset_1(F_565,'#skF_7')
      | ~ m1_subset_1(E_564,k1_zfmisc_1(k2_zfmisc_1('#skF_8',A_563)))
      | ~ v1_funct_1(E_564) ) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_62,c_3891])).

tff(c_3936,plain,(
    ! [F_565] :
      ( k1_funct_1(k8_funct_2('#skF_7','#skF_8','#skF_6','#skF_9','#skF_10'),F_565) = k1_funct_1('#skF_10',k1_funct_1('#skF_9',F_565))
      | ~ r1_tarski(k2_relat_1('#skF_9'),k1_relat_1('#skF_10'))
      | ~ m1_subset_1(F_565,'#skF_7')
      | ~ m1_subset_1('#skF_10',k1_zfmisc_1(k2_zfmisc_1('#skF_8','#skF_6')))
      | ~ v1_funct_1('#skF_10') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_181,c_3931])).

tff(c_3939,plain,(
    ! [F_565] :
      ( k1_funct_1(k8_funct_2('#skF_7','#skF_8','#skF_6','#skF_9','#skF_10'),F_565) = k1_funct_1('#skF_10',k1_funct_1('#skF_9',F_565))
      | ~ m1_subset_1(F_565,'#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_187,c_3936])).

tff(c_12,plain,(
    ! [A_7,B_8] :
      ( r2_hidden(A_7,B_8)
      | v1_xboole_0(B_8)
      | ~ m1_subset_1(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_16,plain,(
    ! [A_12,B_13] : v1_relat_1(k2_zfmisc_1(A_12,B_13)) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_94,plain,(
    ! [B_106,A_107] :
      ( v1_relat_1(B_106)
      | ~ m1_subset_1(B_106,k1_zfmisc_1(A_107))
      | ~ v1_relat_1(A_107) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_97,plain,
    ( v1_relat_1('#skF_9')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_7','#skF_8')) ),
    inference(resolution,[status(thm)],[c_72,c_94])).

tff(c_103,plain,(
    v1_relat_1('#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_97])).

tff(c_180,plain,(
    k1_relset_1('#skF_7','#skF_8','#skF_9') = k1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_72,c_173])).

tff(c_1750,plain,(
    ! [B_332,A_333,C_334] :
      ( k1_xboole_0 = B_332
      | k1_relset_1(A_333,B_332,C_334) = A_333
      | ~ v1_funct_2(C_334,A_333,B_332)
      | ~ m1_subset_1(C_334,k1_zfmisc_1(k2_zfmisc_1(A_333,B_332))) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_1753,plain,
    ( k1_xboole_0 = '#skF_8'
    | k1_relset_1('#skF_7','#skF_8','#skF_9') = '#skF_7'
    | ~ v1_funct_2('#skF_9','#skF_7','#skF_8') ),
    inference(resolution,[status(thm)],[c_72,c_1750])).

tff(c_1759,plain,
    ( k1_xboole_0 = '#skF_8'
    | k1_relat_1('#skF_9') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_180,c_1753])).

tff(c_1762,plain,(
    k1_relat_1('#skF_9') = '#skF_7' ),
    inference(splitLeft,[status(thm)],[c_1759])).

tff(c_1838,plain,(
    ! [A_351,B_352,C_353] :
      ( k7_partfun1(A_351,B_352,C_353) = k1_funct_1(B_352,C_353)
      | ~ r2_hidden(C_353,k1_relat_1(B_352))
      | ~ v1_funct_1(B_352)
      | ~ v5_relat_1(B_352,A_351)
      | ~ v1_relat_1(B_352) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_1851,plain,(
    ! [A_351,C_353] :
      ( k7_partfun1(A_351,'#skF_9',C_353) = k1_funct_1('#skF_9',C_353)
      | ~ r2_hidden(C_353,'#skF_7')
      | ~ v1_funct_1('#skF_9')
      | ~ v5_relat_1('#skF_9',A_351)
      | ~ v1_relat_1('#skF_9') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1762,c_1838])).

tff(c_1898,plain,(
    ! [A_355,C_356] :
      ( k7_partfun1(A_355,'#skF_9',C_356) = k1_funct_1('#skF_9',C_356)
      | ~ r2_hidden(C_356,'#skF_7')
      | ~ v5_relat_1('#skF_9',A_355) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_103,c_76,c_1851])).

tff(c_1931,plain,(
    ! [A_355,A_7] :
      ( k7_partfun1(A_355,'#skF_9',A_7) = k1_funct_1('#skF_9',A_7)
      | ~ v5_relat_1('#skF_9',A_355)
      | v1_xboole_0('#skF_7')
      | ~ m1_subset_1(A_7,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_12,c_1898])).

tff(c_1938,plain,(
    v1_xboole_0('#skF_7') ),
    inference(splitLeft,[status(thm)],[c_1931])).

tff(c_10,plain,(
    ! [A_6] :
      ( k1_xboole_0 = A_6
      | ~ v1_xboole_0(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_1941,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(resolution,[status(thm)],[c_1938,c_10])).

tff(c_1945,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_1941])).

tff(c_1947,plain,(
    ~ v1_xboole_0('#skF_7') ),
    inference(splitRight,[status(thm)],[c_1931])).

tff(c_120,plain,(
    ! [C_113,B_114,A_115] :
      ( v5_relat_1(C_113,B_114)
      | ~ m1_subset_1(C_113,k1_zfmisc_1(k2_zfmisc_1(A_115,B_114))) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_128,plain,(
    v5_relat_1('#skF_10','#skF_6') ),
    inference(resolution,[status(thm)],[c_68,c_120])).

tff(c_100,plain,
    ( v1_relat_1('#skF_10')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_8','#skF_6')) ),
    inference(resolution,[status(thm)],[c_68,c_94])).

tff(c_106,plain,(
    v1_relat_1('#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_100])).

tff(c_18,plain,(
    ! [A_14,D_53] :
      ( r2_hidden(k1_funct_1(A_14,D_53),k2_relat_1(A_14))
      | ~ r2_hidden(D_53,k1_relat_1(A_14))
      | ~ v1_funct_1(A_14)
      | ~ v1_relat_1(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_87,plain,(
    ! [A_103,B_104] :
      ( r2_hidden('#skF_1'(A_103,B_104),A_103)
      | r1_tarski(A_103,B_104) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_92,plain,(
    ! [A_103] : r1_tarski(A_103,A_103) ),
    inference(resolution,[status(thm)],[c_87,c_4])).

tff(c_1720,plain,(
    ! [A_323,C_324] :
      ( r2_hidden('#skF_5'(A_323,k2_relat_1(A_323),C_324),k1_relat_1(A_323))
      | ~ r2_hidden(C_324,k2_relat_1(A_323))
      | ~ v1_funct_1(A_323)
      | ~ v1_relat_1(A_323) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_1723,plain,(
    ! [A_323,C_324,B_2] :
      ( r2_hidden('#skF_5'(A_323,k2_relat_1(A_323),C_324),B_2)
      | ~ r1_tarski(k1_relat_1(A_323),B_2)
      | ~ r2_hidden(C_324,k2_relat_1(A_323))
      | ~ v1_funct_1(A_323)
      | ~ v1_relat_1(A_323) ) ),
    inference(resolution,[status(thm)],[c_1720,c_2])).

tff(c_20,plain,(
    ! [A_14,C_50] :
      ( k1_funct_1(A_14,'#skF_5'(A_14,k2_relat_1(A_14),C_50)) = C_50
      | ~ r2_hidden(C_50,k2_relat_1(A_14))
      | ~ v1_funct_1(A_14)
      | ~ v1_relat_1(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_1684,plain,(
    ! [A_305,D_306] :
      ( r2_hidden(k1_funct_1(A_305,D_306),k2_relat_1(A_305))
      | ~ r2_hidden(D_306,k1_relat_1(A_305))
      | ~ v1_funct_1(A_305)
      | ~ v1_relat_1(A_305) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_1811,plain,(
    ! [A_343,D_344,B_345] :
      ( r2_hidden(k1_funct_1(A_343,D_344),B_345)
      | ~ r1_tarski(k2_relat_1(A_343),B_345)
      | ~ r2_hidden(D_344,k1_relat_1(A_343))
      | ~ v1_funct_1(A_343)
      | ~ v1_relat_1(A_343) ) ),
    inference(resolution,[status(thm)],[c_1684,c_2])).

tff(c_2135,plain,(
    ! [A_395,D_396,B_397,B_398] :
      ( r2_hidden(k1_funct_1(A_395,D_396),B_397)
      | ~ r1_tarski(B_398,B_397)
      | ~ r1_tarski(k2_relat_1(A_395),B_398)
      | ~ r2_hidden(D_396,k1_relat_1(A_395))
      | ~ v1_funct_1(A_395)
      | ~ v1_relat_1(A_395) ) ),
    inference(resolution,[status(thm)],[c_1811,c_2])).

tff(c_2142,plain,(
    ! [A_399,D_400] :
      ( r2_hidden(k1_funct_1(A_399,D_400),k1_relat_1('#skF_10'))
      | ~ r1_tarski(k2_relat_1(A_399),k2_relat_1('#skF_9'))
      | ~ r2_hidden(D_400,k1_relat_1(A_399))
      | ~ v1_funct_1(A_399)
      | ~ v1_relat_1(A_399) ) ),
    inference(resolution,[status(thm)],[c_187,c_2135])).

tff(c_3446,plain,(
    ! [A_523,D_524,B_525] :
      ( r2_hidden(k1_funct_1(A_523,D_524),B_525)
      | ~ r1_tarski(k1_relat_1('#skF_10'),B_525)
      | ~ r1_tarski(k2_relat_1(A_523),k2_relat_1('#skF_9'))
      | ~ r2_hidden(D_524,k1_relat_1(A_523))
      | ~ v1_funct_1(A_523)
      | ~ v1_relat_1(A_523) ) ),
    inference(resolution,[status(thm)],[c_2142,c_2])).

tff(c_3449,plain,(
    ! [D_524,B_525] :
      ( r2_hidden(k1_funct_1('#skF_9',D_524),B_525)
      | ~ r1_tarski(k1_relat_1('#skF_10'),B_525)
      | ~ r2_hidden(D_524,k1_relat_1('#skF_9'))
      | ~ v1_funct_1('#skF_9')
      | ~ v1_relat_1('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_92,c_3446])).

tff(c_3453,plain,(
    ! [D_526,B_527] :
      ( r2_hidden(k1_funct_1('#skF_9',D_526),B_527)
      | ~ r1_tarski(k1_relat_1('#skF_10'),B_527)
      | ~ r2_hidden(D_526,'#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_103,c_76,c_1762,c_3449])).

tff(c_3467,plain,(
    ! [C_50,B_527] :
      ( r2_hidden(C_50,B_527)
      | ~ r1_tarski(k1_relat_1('#skF_10'),B_527)
      | ~ r2_hidden('#skF_5'('#skF_9',k2_relat_1('#skF_9'),C_50),'#skF_7')
      | ~ r2_hidden(C_50,k2_relat_1('#skF_9'))
      | ~ v1_funct_1('#skF_9')
      | ~ v1_relat_1('#skF_9') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_3453])).

tff(c_3481,plain,(
    ! [C_531,B_532] :
      ( r2_hidden(C_531,B_532)
      | ~ r1_tarski(k1_relat_1('#skF_10'),B_532)
      | ~ r2_hidden('#skF_5'('#skF_9',k2_relat_1('#skF_9'),C_531),'#skF_7')
      | ~ r2_hidden(C_531,k2_relat_1('#skF_9')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_103,c_76,c_3467])).

tff(c_3491,plain,(
    ! [C_536] :
      ( r2_hidden(C_536,k1_relat_1('#skF_10'))
      | ~ r2_hidden('#skF_5'('#skF_9',k2_relat_1('#skF_9'),C_536),'#skF_7')
      | ~ r2_hidden(C_536,k2_relat_1('#skF_9')) ) ),
    inference(resolution,[status(thm)],[c_92,c_3481])).

tff(c_3495,plain,(
    ! [C_324] :
      ( r2_hidden(C_324,k1_relat_1('#skF_10'))
      | ~ r1_tarski(k1_relat_1('#skF_9'),'#skF_7')
      | ~ r2_hidden(C_324,k2_relat_1('#skF_9'))
      | ~ v1_funct_1('#skF_9')
      | ~ v1_relat_1('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_1723,c_3491])).

tff(c_3516,plain,(
    ! [C_537] :
      ( r2_hidden(C_537,k1_relat_1('#skF_10'))
      | ~ r2_hidden(C_537,k2_relat_1('#skF_9')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_103,c_76,c_92,c_1762,c_3495])).

tff(c_3578,plain,(
    ! [D_53] :
      ( r2_hidden(k1_funct_1('#skF_9',D_53),k1_relat_1('#skF_10'))
      | ~ r2_hidden(D_53,k1_relat_1('#skF_9'))
      | ~ v1_funct_1('#skF_9')
      | ~ v1_relat_1('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_18,c_3516])).

tff(c_3651,plain,(
    ! [D_540] :
      ( r2_hidden(k1_funct_1('#skF_9',D_540),k1_relat_1('#skF_10'))
      | ~ r2_hidden(D_540,'#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_103,c_76,c_1762,c_3578])).

tff(c_56,plain,(
    ! [A_66,B_67,C_69] :
      ( k7_partfun1(A_66,B_67,C_69) = k1_funct_1(B_67,C_69)
      | ~ r2_hidden(C_69,k1_relat_1(B_67))
      | ~ v1_funct_1(B_67)
      | ~ v5_relat_1(B_67,A_66)
      | ~ v1_relat_1(B_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_3653,plain,(
    ! [A_66,D_540] :
      ( k7_partfun1(A_66,'#skF_10',k1_funct_1('#skF_9',D_540)) = k1_funct_1('#skF_10',k1_funct_1('#skF_9',D_540))
      | ~ v1_funct_1('#skF_10')
      | ~ v5_relat_1('#skF_10',A_66)
      | ~ v1_relat_1('#skF_10')
      | ~ r2_hidden(D_540,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_3651,c_56])).

tff(c_4124,plain,(
    ! [A_578,D_579] :
      ( k7_partfun1(A_578,'#skF_10',k1_funct_1('#skF_9',D_579)) = k1_funct_1('#skF_10',k1_funct_1('#skF_9',D_579))
      | ~ v5_relat_1('#skF_10',A_578)
      | ~ r2_hidden(D_579,'#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_106,c_70,c_3653])).

tff(c_60,plain,(
    k7_partfun1('#skF_6','#skF_10',k1_funct_1('#skF_9','#skF_11')) != k1_funct_1(k8_funct_2('#skF_7','#skF_8','#skF_6','#skF_9','#skF_10'),'#skF_11') ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_4130,plain,
    ( k1_funct_1(k8_funct_2('#skF_7','#skF_8','#skF_6','#skF_9','#skF_10'),'#skF_11') != k1_funct_1('#skF_10',k1_funct_1('#skF_9','#skF_11'))
    | ~ v5_relat_1('#skF_10','#skF_6')
    | ~ r2_hidden('#skF_11','#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_4124,c_60])).

tff(c_4142,plain,
    ( k1_funct_1(k8_funct_2('#skF_7','#skF_8','#skF_6','#skF_9','#skF_10'),'#skF_11') != k1_funct_1('#skF_10',k1_funct_1('#skF_9','#skF_11'))
    | ~ r2_hidden('#skF_11','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_128,c_4130])).

tff(c_4146,plain,(
    ~ r2_hidden('#skF_11','#skF_7') ),
    inference(splitLeft,[status(thm)],[c_4142])).

tff(c_4155,plain,
    ( v1_xboole_0('#skF_7')
    | ~ m1_subset_1('#skF_11','#skF_7') ),
    inference(resolution,[status(thm)],[c_12,c_4146])).

tff(c_4158,plain,(
    v1_xboole_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_4155])).

tff(c_4160,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1947,c_4158])).

tff(c_4161,plain,(
    k1_funct_1(k8_funct_2('#skF_7','#skF_8','#skF_6','#skF_9','#skF_10'),'#skF_11') != k1_funct_1('#skF_10',k1_funct_1('#skF_9','#skF_11')) ),
    inference(splitRight,[status(thm)],[c_4142])).

tff(c_4242,plain,(
    ~ m1_subset_1('#skF_11','#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_3939,c_4161])).

tff(c_4246,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_4242])).

tff(c_4247,plain,(
    k1_xboole_0 = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_1759])).

tff(c_8,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_4255,plain,(
    v1_xboole_0('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4247,c_8])).

tff(c_4258,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_4255])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:29:35 EST 2020
% 0.19/0.34  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.45/2.25  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.45/2.26  
% 6.45/2.26  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.45/2.26  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k8_funct_2 > k7_partfun1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_11 > #skF_7 > #skF_3 > #skF_10 > #skF_6 > #skF_5 > #skF_9 > #skF_8 > #skF_2 > #skF_1 > #skF_4
% 6.45/2.26  
% 6.45/2.26  %Foreground sorts:
% 6.45/2.26  
% 6.45/2.26  
% 6.45/2.26  %Background operators:
% 6.45/2.26  
% 6.45/2.26  
% 6.45/2.26  %Foreground operators:
% 6.45/2.26  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 6.45/2.26  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 6.45/2.26  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.45/2.26  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 6.45/2.26  tff('#skF_11', type, '#skF_11': $i).
% 6.45/2.26  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 6.45/2.26  tff('#skF_7', type, '#skF_7': $i).
% 6.45/2.26  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 6.45/2.26  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.45/2.26  tff('#skF_10', type, '#skF_10': $i).
% 6.45/2.26  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 6.45/2.26  tff(k7_partfun1, type, k7_partfun1: ($i * $i * $i) > $i).
% 6.45/2.26  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 6.45/2.26  tff(k8_funct_2, type, k8_funct_2: ($i * $i * $i * $i * $i) > $i).
% 6.45/2.26  tff('#skF_6', type, '#skF_6': $i).
% 6.45/2.26  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 6.45/2.26  tff('#skF_9', type, '#skF_9': $i).
% 6.45/2.26  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 6.45/2.26  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 6.45/2.26  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 6.45/2.26  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 6.45/2.26  tff('#skF_8', type, '#skF_8': $i).
% 6.45/2.26  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.45/2.26  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 6.45/2.26  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 6.45/2.26  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.45/2.26  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 6.45/2.26  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 6.45/2.26  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 6.45/2.26  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 6.45/2.26  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 6.45/2.26  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 6.45/2.26  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 6.45/2.26  
% 6.45/2.28  tff(f_159, negated_conjecture, ~(![A, B, C]: (~v1_xboole_0(C) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, C)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (![E]: ((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(C, A)))) => (![F]: (m1_subset_1(F, B) => (r1_tarski(k2_relset_1(B, C, D), k1_relset_1(C, A, E)) => ((B = k1_xboole_0) | (k1_funct_1(k8_funct_2(B, C, A, D, E), F) = k7_partfun1(A, E, k1_funct_1(D, F))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t186_funct_2)).
% 6.45/2.28  tff(f_77, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 6.45/2.28  tff(f_81, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 6.45/2.28  tff(f_134, axiom, (![A, B, C]: (~v1_xboole_0(C) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, C)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (![E]: ((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(C, A)))) => (![F]: (m1_subset_1(F, B) => (r1_tarski(k2_relset_1(B, C, D), k1_relset_1(C, A, E)) => ((B = k1_xboole_0) | (k1_funct_1(k8_funct_2(B, C, A, D, E), F) = k1_funct_1(E, k1_funct_1(D, F))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t185_funct_2)).
% 6.45/2.28  tff(f_43, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 6.45/2.28  tff(f_52, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 6.45/2.28  tff(f_50, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 6.45/2.28  tff(f_99, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 6.45/2.28  tff(f_110, axiom, (![A, B]: (((v1_relat_1(B) & v5_relat_1(B, A)) & v1_funct_1(B)) => (![C]: (r2_hidden(C, k1_relat_1(B)) => (k7_partfun1(A, B, C) = k1_funct_1(B, C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_partfun1)).
% 6.45/2.28  tff(f_37, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 6.45/2.28  tff(f_73, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 6.45/2.28  tff(f_67, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((B = k2_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: (r2_hidden(D, k1_relat_1(A)) & (C = k1_funct_1(A, D)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_funct_1)).
% 6.45/2.28  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 6.45/2.28  tff(f_33, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 6.45/2.28  tff(c_78, plain, (~v1_xboole_0('#skF_8')), inference(cnfTransformation, [status(thm)], [f_159])).
% 6.45/2.28  tff(c_66, plain, (m1_subset_1('#skF_11', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_159])).
% 6.45/2.28  tff(c_70, plain, (v1_funct_1('#skF_10')), inference(cnfTransformation, [status(thm)], [f_159])).
% 6.45/2.28  tff(c_68, plain, (m1_subset_1('#skF_10', k1_zfmisc_1(k2_zfmisc_1('#skF_8', '#skF_6')))), inference(cnfTransformation, [status(thm)], [f_159])).
% 6.45/2.28  tff(c_173, plain, (![A_130, B_131, C_132]: (k1_relset_1(A_130, B_131, C_132)=k1_relat_1(C_132) | ~m1_subset_1(C_132, k1_zfmisc_1(k2_zfmisc_1(A_130, B_131))))), inference(cnfTransformation, [status(thm)], [f_77])).
% 6.45/2.28  tff(c_181, plain, (k1_relset_1('#skF_8', '#skF_6', '#skF_10')=k1_relat_1('#skF_10')), inference(resolution, [status(thm)], [c_68, c_173])).
% 6.45/2.28  tff(c_72, plain, (m1_subset_1('#skF_9', k1_zfmisc_1(k2_zfmisc_1('#skF_7', '#skF_8')))), inference(cnfTransformation, [status(thm)], [f_159])).
% 6.45/2.28  tff(c_138, plain, (![A_119, B_120, C_121]: (k2_relset_1(A_119, B_120, C_121)=k2_relat_1(C_121) | ~m1_subset_1(C_121, k1_zfmisc_1(k2_zfmisc_1(A_119, B_120))))), inference(cnfTransformation, [status(thm)], [f_81])).
% 6.45/2.28  tff(c_145, plain, (k2_relset_1('#skF_7', '#skF_8', '#skF_9')=k2_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_72, c_138])).
% 6.45/2.28  tff(c_64, plain, (r1_tarski(k2_relset_1('#skF_7', '#skF_8', '#skF_9'), k1_relset_1('#skF_8', '#skF_6', '#skF_10'))), inference(cnfTransformation, [status(thm)], [f_159])).
% 6.45/2.28  tff(c_147, plain, (r1_tarski(k2_relat_1('#skF_9'), k1_relset_1('#skF_8', '#skF_6', '#skF_10'))), inference(demodulation, [status(thm), theory('equality')], [c_145, c_64])).
% 6.45/2.28  tff(c_187, plain, (r1_tarski(k2_relat_1('#skF_9'), k1_relat_1('#skF_10'))), inference(demodulation, [status(thm), theory('equality')], [c_181, c_147])).
% 6.45/2.28  tff(c_62, plain, (k1_xboole_0!='#skF_7'), inference(cnfTransformation, [status(thm)], [f_159])).
% 6.45/2.28  tff(c_76, plain, (v1_funct_1('#skF_9')), inference(cnfTransformation, [status(thm)], [f_159])).
% 6.45/2.28  tff(c_74, plain, (v1_funct_2('#skF_9', '#skF_7', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_159])).
% 6.45/2.28  tff(c_3873, plain, (![B_557, A_555, E_558, F_554, C_556, D_553]: (k1_funct_1(k8_funct_2(B_557, C_556, A_555, D_553, E_558), F_554)=k1_funct_1(E_558, k1_funct_1(D_553, F_554)) | k1_xboole_0=B_557 | ~r1_tarski(k2_relset_1(B_557, C_556, D_553), k1_relset_1(C_556, A_555, E_558)) | ~m1_subset_1(F_554, B_557) | ~m1_subset_1(E_558, k1_zfmisc_1(k2_zfmisc_1(C_556, A_555))) | ~v1_funct_1(E_558) | ~m1_subset_1(D_553, k1_zfmisc_1(k2_zfmisc_1(B_557, C_556))) | ~v1_funct_2(D_553, B_557, C_556) | ~v1_funct_1(D_553) | v1_xboole_0(C_556))), inference(cnfTransformation, [status(thm)], [f_134])).
% 6.45/2.28  tff(c_3881, plain, (![A_555, E_558, F_554]: (k1_funct_1(k8_funct_2('#skF_7', '#skF_8', A_555, '#skF_9', E_558), F_554)=k1_funct_1(E_558, k1_funct_1('#skF_9', F_554)) | k1_xboole_0='#skF_7' | ~r1_tarski(k2_relat_1('#skF_9'), k1_relset_1('#skF_8', A_555, E_558)) | ~m1_subset_1(F_554, '#skF_7') | ~m1_subset_1(E_558, k1_zfmisc_1(k2_zfmisc_1('#skF_8', A_555))) | ~v1_funct_1(E_558) | ~m1_subset_1('#skF_9', k1_zfmisc_1(k2_zfmisc_1('#skF_7', '#skF_8'))) | ~v1_funct_2('#skF_9', '#skF_7', '#skF_8') | ~v1_funct_1('#skF_9') | v1_xboole_0('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_145, c_3873])).
% 6.45/2.28  tff(c_3891, plain, (![A_555, E_558, F_554]: (k1_funct_1(k8_funct_2('#skF_7', '#skF_8', A_555, '#skF_9', E_558), F_554)=k1_funct_1(E_558, k1_funct_1('#skF_9', F_554)) | k1_xboole_0='#skF_7' | ~r1_tarski(k2_relat_1('#skF_9'), k1_relset_1('#skF_8', A_555, E_558)) | ~m1_subset_1(F_554, '#skF_7') | ~m1_subset_1(E_558, k1_zfmisc_1(k2_zfmisc_1('#skF_8', A_555))) | ~v1_funct_1(E_558) | v1_xboole_0('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_74, c_72, c_3881])).
% 6.45/2.28  tff(c_3931, plain, (![A_563, E_564, F_565]: (k1_funct_1(k8_funct_2('#skF_7', '#skF_8', A_563, '#skF_9', E_564), F_565)=k1_funct_1(E_564, k1_funct_1('#skF_9', F_565)) | ~r1_tarski(k2_relat_1('#skF_9'), k1_relset_1('#skF_8', A_563, E_564)) | ~m1_subset_1(F_565, '#skF_7') | ~m1_subset_1(E_564, k1_zfmisc_1(k2_zfmisc_1('#skF_8', A_563))) | ~v1_funct_1(E_564))), inference(negUnitSimplification, [status(thm)], [c_78, c_62, c_3891])).
% 6.45/2.28  tff(c_3936, plain, (![F_565]: (k1_funct_1(k8_funct_2('#skF_7', '#skF_8', '#skF_6', '#skF_9', '#skF_10'), F_565)=k1_funct_1('#skF_10', k1_funct_1('#skF_9', F_565)) | ~r1_tarski(k2_relat_1('#skF_9'), k1_relat_1('#skF_10')) | ~m1_subset_1(F_565, '#skF_7') | ~m1_subset_1('#skF_10', k1_zfmisc_1(k2_zfmisc_1('#skF_8', '#skF_6'))) | ~v1_funct_1('#skF_10'))), inference(superposition, [status(thm), theory('equality')], [c_181, c_3931])).
% 6.45/2.28  tff(c_3939, plain, (![F_565]: (k1_funct_1(k8_funct_2('#skF_7', '#skF_8', '#skF_6', '#skF_9', '#skF_10'), F_565)=k1_funct_1('#skF_10', k1_funct_1('#skF_9', F_565)) | ~m1_subset_1(F_565, '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_187, c_3936])).
% 6.45/2.28  tff(c_12, plain, (![A_7, B_8]: (r2_hidden(A_7, B_8) | v1_xboole_0(B_8) | ~m1_subset_1(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_43])).
% 6.45/2.28  tff(c_16, plain, (![A_12, B_13]: (v1_relat_1(k2_zfmisc_1(A_12, B_13)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 6.45/2.28  tff(c_94, plain, (![B_106, A_107]: (v1_relat_1(B_106) | ~m1_subset_1(B_106, k1_zfmisc_1(A_107)) | ~v1_relat_1(A_107))), inference(cnfTransformation, [status(thm)], [f_50])).
% 6.45/2.28  tff(c_97, plain, (v1_relat_1('#skF_9') | ~v1_relat_1(k2_zfmisc_1('#skF_7', '#skF_8'))), inference(resolution, [status(thm)], [c_72, c_94])).
% 6.45/2.28  tff(c_103, plain, (v1_relat_1('#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_16, c_97])).
% 6.45/2.28  tff(c_180, plain, (k1_relset_1('#skF_7', '#skF_8', '#skF_9')=k1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_72, c_173])).
% 6.45/2.28  tff(c_1750, plain, (![B_332, A_333, C_334]: (k1_xboole_0=B_332 | k1_relset_1(A_333, B_332, C_334)=A_333 | ~v1_funct_2(C_334, A_333, B_332) | ~m1_subset_1(C_334, k1_zfmisc_1(k2_zfmisc_1(A_333, B_332))))), inference(cnfTransformation, [status(thm)], [f_99])).
% 6.45/2.28  tff(c_1753, plain, (k1_xboole_0='#skF_8' | k1_relset_1('#skF_7', '#skF_8', '#skF_9')='#skF_7' | ~v1_funct_2('#skF_9', '#skF_7', '#skF_8')), inference(resolution, [status(thm)], [c_72, c_1750])).
% 6.45/2.28  tff(c_1759, plain, (k1_xboole_0='#skF_8' | k1_relat_1('#skF_9')='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_74, c_180, c_1753])).
% 6.45/2.28  tff(c_1762, plain, (k1_relat_1('#skF_9')='#skF_7'), inference(splitLeft, [status(thm)], [c_1759])).
% 6.45/2.28  tff(c_1838, plain, (![A_351, B_352, C_353]: (k7_partfun1(A_351, B_352, C_353)=k1_funct_1(B_352, C_353) | ~r2_hidden(C_353, k1_relat_1(B_352)) | ~v1_funct_1(B_352) | ~v5_relat_1(B_352, A_351) | ~v1_relat_1(B_352))), inference(cnfTransformation, [status(thm)], [f_110])).
% 6.45/2.28  tff(c_1851, plain, (![A_351, C_353]: (k7_partfun1(A_351, '#skF_9', C_353)=k1_funct_1('#skF_9', C_353) | ~r2_hidden(C_353, '#skF_7') | ~v1_funct_1('#skF_9') | ~v5_relat_1('#skF_9', A_351) | ~v1_relat_1('#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_1762, c_1838])).
% 6.45/2.28  tff(c_1898, plain, (![A_355, C_356]: (k7_partfun1(A_355, '#skF_9', C_356)=k1_funct_1('#skF_9', C_356) | ~r2_hidden(C_356, '#skF_7') | ~v5_relat_1('#skF_9', A_355))), inference(demodulation, [status(thm), theory('equality')], [c_103, c_76, c_1851])).
% 6.45/2.28  tff(c_1931, plain, (![A_355, A_7]: (k7_partfun1(A_355, '#skF_9', A_7)=k1_funct_1('#skF_9', A_7) | ~v5_relat_1('#skF_9', A_355) | v1_xboole_0('#skF_7') | ~m1_subset_1(A_7, '#skF_7'))), inference(resolution, [status(thm)], [c_12, c_1898])).
% 6.45/2.28  tff(c_1938, plain, (v1_xboole_0('#skF_7')), inference(splitLeft, [status(thm)], [c_1931])).
% 6.45/2.28  tff(c_10, plain, (![A_6]: (k1_xboole_0=A_6 | ~v1_xboole_0(A_6))), inference(cnfTransformation, [status(thm)], [f_37])).
% 6.45/2.28  tff(c_1941, plain, (k1_xboole_0='#skF_7'), inference(resolution, [status(thm)], [c_1938, c_10])).
% 6.45/2.28  tff(c_1945, plain, $false, inference(negUnitSimplification, [status(thm)], [c_62, c_1941])).
% 6.45/2.28  tff(c_1947, plain, (~v1_xboole_0('#skF_7')), inference(splitRight, [status(thm)], [c_1931])).
% 6.45/2.28  tff(c_120, plain, (![C_113, B_114, A_115]: (v5_relat_1(C_113, B_114) | ~m1_subset_1(C_113, k1_zfmisc_1(k2_zfmisc_1(A_115, B_114))))), inference(cnfTransformation, [status(thm)], [f_73])).
% 6.45/2.28  tff(c_128, plain, (v5_relat_1('#skF_10', '#skF_6')), inference(resolution, [status(thm)], [c_68, c_120])).
% 6.45/2.28  tff(c_100, plain, (v1_relat_1('#skF_10') | ~v1_relat_1(k2_zfmisc_1('#skF_8', '#skF_6'))), inference(resolution, [status(thm)], [c_68, c_94])).
% 6.45/2.28  tff(c_106, plain, (v1_relat_1('#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_16, c_100])).
% 6.45/2.28  tff(c_18, plain, (![A_14, D_53]: (r2_hidden(k1_funct_1(A_14, D_53), k2_relat_1(A_14)) | ~r2_hidden(D_53, k1_relat_1(A_14)) | ~v1_funct_1(A_14) | ~v1_relat_1(A_14))), inference(cnfTransformation, [status(thm)], [f_67])).
% 6.45/2.28  tff(c_87, plain, (![A_103, B_104]: (r2_hidden('#skF_1'(A_103, B_104), A_103) | r1_tarski(A_103, B_104))), inference(cnfTransformation, [status(thm)], [f_32])).
% 6.45/2.28  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 6.45/2.28  tff(c_92, plain, (![A_103]: (r1_tarski(A_103, A_103))), inference(resolution, [status(thm)], [c_87, c_4])).
% 6.45/2.28  tff(c_1720, plain, (![A_323, C_324]: (r2_hidden('#skF_5'(A_323, k2_relat_1(A_323), C_324), k1_relat_1(A_323)) | ~r2_hidden(C_324, k2_relat_1(A_323)) | ~v1_funct_1(A_323) | ~v1_relat_1(A_323))), inference(cnfTransformation, [status(thm)], [f_67])).
% 6.45/2.28  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 6.45/2.28  tff(c_1723, plain, (![A_323, C_324, B_2]: (r2_hidden('#skF_5'(A_323, k2_relat_1(A_323), C_324), B_2) | ~r1_tarski(k1_relat_1(A_323), B_2) | ~r2_hidden(C_324, k2_relat_1(A_323)) | ~v1_funct_1(A_323) | ~v1_relat_1(A_323))), inference(resolution, [status(thm)], [c_1720, c_2])).
% 6.45/2.28  tff(c_20, plain, (![A_14, C_50]: (k1_funct_1(A_14, '#skF_5'(A_14, k2_relat_1(A_14), C_50))=C_50 | ~r2_hidden(C_50, k2_relat_1(A_14)) | ~v1_funct_1(A_14) | ~v1_relat_1(A_14))), inference(cnfTransformation, [status(thm)], [f_67])).
% 6.45/2.28  tff(c_1684, plain, (![A_305, D_306]: (r2_hidden(k1_funct_1(A_305, D_306), k2_relat_1(A_305)) | ~r2_hidden(D_306, k1_relat_1(A_305)) | ~v1_funct_1(A_305) | ~v1_relat_1(A_305))), inference(cnfTransformation, [status(thm)], [f_67])).
% 6.45/2.28  tff(c_1811, plain, (![A_343, D_344, B_345]: (r2_hidden(k1_funct_1(A_343, D_344), B_345) | ~r1_tarski(k2_relat_1(A_343), B_345) | ~r2_hidden(D_344, k1_relat_1(A_343)) | ~v1_funct_1(A_343) | ~v1_relat_1(A_343))), inference(resolution, [status(thm)], [c_1684, c_2])).
% 6.45/2.28  tff(c_2135, plain, (![A_395, D_396, B_397, B_398]: (r2_hidden(k1_funct_1(A_395, D_396), B_397) | ~r1_tarski(B_398, B_397) | ~r1_tarski(k2_relat_1(A_395), B_398) | ~r2_hidden(D_396, k1_relat_1(A_395)) | ~v1_funct_1(A_395) | ~v1_relat_1(A_395))), inference(resolution, [status(thm)], [c_1811, c_2])).
% 6.45/2.28  tff(c_2142, plain, (![A_399, D_400]: (r2_hidden(k1_funct_1(A_399, D_400), k1_relat_1('#skF_10')) | ~r1_tarski(k2_relat_1(A_399), k2_relat_1('#skF_9')) | ~r2_hidden(D_400, k1_relat_1(A_399)) | ~v1_funct_1(A_399) | ~v1_relat_1(A_399))), inference(resolution, [status(thm)], [c_187, c_2135])).
% 6.45/2.28  tff(c_3446, plain, (![A_523, D_524, B_525]: (r2_hidden(k1_funct_1(A_523, D_524), B_525) | ~r1_tarski(k1_relat_1('#skF_10'), B_525) | ~r1_tarski(k2_relat_1(A_523), k2_relat_1('#skF_9')) | ~r2_hidden(D_524, k1_relat_1(A_523)) | ~v1_funct_1(A_523) | ~v1_relat_1(A_523))), inference(resolution, [status(thm)], [c_2142, c_2])).
% 6.45/2.28  tff(c_3449, plain, (![D_524, B_525]: (r2_hidden(k1_funct_1('#skF_9', D_524), B_525) | ~r1_tarski(k1_relat_1('#skF_10'), B_525) | ~r2_hidden(D_524, k1_relat_1('#skF_9')) | ~v1_funct_1('#skF_9') | ~v1_relat_1('#skF_9'))), inference(resolution, [status(thm)], [c_92, c_3446])).
% 6.45/2.28  tff(c_3453, plain, (![D_526, B_527]: (r2_hidden(k1_funct_1('#skF_9', D_526), B_527) | ~r1_tarski(k1_relat_1('#skF_10'), B_527) | ~r2_hidden(D_526, '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_103, c_76, c_1762, c_3449])).
% 6.45/2.28  tff(c_3467, plain, (![C_50, B_527]: (r2_hidden(C_50, B_527) | ~r1_tarski(k1_relat_1('#skF_10'), B_527) | ~r2_hidden('#skF_5'('#skF_9', k2_relat_1('#skF_9'), C_50), '#skF_7') | ~r2_hidden(C_50, k2_relat_1('#skF_9')) | ~v1_funct_1('#skF_9') | ~v1_relat_1('#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_20, c_3453])).
% 6.45/2.28  tff(c_3481, plain, (![C_531, B_532]: (r2_hidden(C_531, B_532) | ~r1_tarski(k1_relat_1('#skF_10'), B_532) | ~r2_hidden('#skF_5'('#skF_9', k2_relat_1('#skF_9'), C_531), '#skF_7') | ~r2_hidden(C_531, k2_relat_1('#skF_9')))), inference(demodulation, [status(thm), theory('equality')], [c_103, c_76, c_3467])).
% 6.45/2.28  tff(c_3491, plain, (![C_536]: (r2_hidden(C_536, k1_relat_1('#skF_10')) | ~r2_hidden('#skF_5'('#skF_9', k2_relat_1('#skF_9'), C_536), '#skF_7') | ~r2_hidden(C_536, k2_relat_1('#skF_9')))), inference(resolution, [status(thm)], [c_92, c_3481])).
% 6.45/2.28  tff(c_3495, plain, (![C_324]: (r2_hidden(C_324, k1_relat_1('#skF_10')) | ~r1_tarski(k1_relat_1('#skF_9'), '#skF_7') | ~r2_hidden(C_324, k2_relat_1('#skF_9')) | ~v1_funct_1('#skF_9') | ~v1_relat_1('#skF_9'))), inference(resolution, [status(thm)], [c_1723, c_3491])).
% 6.45/2.28  tff(c_3516, plain, (![C_537]: (r2_hidden(C_537, k1_relat_1('#skF_10')) | ~r2_hidden(C_537, k2_relat_1('#skF_9')))), inference(demodulation, [status(thm), theory('equality')], [c_103, c_76, c_92, c_1762, c_3495])).
% 6.45/2.28  tff(c_3578, plain, (![D_53]: (r2_hidden(k1_funct_1('#skF_9', D_53), k1_relat_1('#skF_10')) | ~r2_hidden(D_53, k1_relat_1('#skF_9')) | ~v1_funct_1('#skF_9') | ~v1_relat_1('#skF_9'))), inference(resolution, [status(thm)], [c_18, c_3516])).
% 6.45/2.28  tff(c_3651, plain, (![D_540]: (r2_hidden(k1_funct_1('#skF_9', D_540), k1_relat_1('#skF_10')) | ~r2_hidden(D_540, '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_103, c_76, c_1762, c_3578])).
% 6.45/2.28  tff(c_56, plain, (![A_66, B_67, C_69]: (k7_partfun1(A_66, B_67, C_69)=k1_funct_1(B_67, C_69) | ~r2_hidden(C_69, k1_relat_1(B_67)) | ~v1_funct_1(B_67) | ~v5_relat_1(B_67, A_66) | ~v1_relat_1(B_67))), inference(cnfTransformation, [status(thm)], [f_110])).
% 6.45/2.28  tff(c_3653, plain, (![A_66, D_540]: (k7_partfun1(A_66, '#skF_10', k1_funct_1('#skF_9', D_540))=k1_funct_1('#skF_10', k1_funct_1('#skF_9', D_540)) | ~v1_funct_1('#skF_10') | ~v5_relat_1('#skF_10', A_66) | ~v1_relat_1('#skF_10') | ~r2_hidden(D_540, '#skF_7'))), inference(resolution, [status(thm)], [c_3651, c_56])).
% 6.45/2.28  tff(c_4124, plain, (![A_578, D_579]: (k7_partfun1(A_578, '#skF_10', k1_funct_1('#skF_9', D_579))=k1_funct_1('#skF_10', k1_funct_1('#skF_9', D_579)) | ~v5_relat_1('#skF_10', A_578) | ~r2_hidden(D_579, '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_106, c_70, c_3653])).
% 6.45/2.28  tff(c_60, plain, (k7_partfun1('#skF_6', '#skF_10', k1_funct_1('#skF_9', '#skF_11'))!=k1_funct_1(k8_funct_2('#skF_7', '#skF_8', '#skF_6', '#skF_9', '#skF_10'), '#skF_11')), inference(cnfTransformation, [status(thm)], [f_159])).
% 6.45/2.28  tff(c_4130, plain, (k1_funct_1(k8_funct_2('#skF_7', '#skF_8', '#skF_6', '#skF_9', '#skF_10'), '#skF_11')!=k1_funct_1('#skF_10', k1_funct_1('#skF_9', '#skF_11')) | ~v5_relat_1('#skF_10', '#skF_6') | ~r2_hidden('#skF_11', '#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_4124, c_60])).
% 6.45/2.28  tff(c_4142, plain, (k1_funct_1(k8_funct_2('#skF_7', '#skF_8', '#skF_6', '#skF_9', '#skF_10'), '#skF_11')!=k1_funct_1('#skF_10', k1_funct_1('#skF_9', '#skF_11')) | ~r2_hidden('#skF_11', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_128, c_4130])).
% 6.45/2.28  tff(c_4146, plain, (~r2_hidden('#skF_11', '#skF_7')), inference(splitLeft, [status(thm)], [c_4142])).
% 6.45/2.28  tff(c_4155, plain, (v1_xboole_0('#skF_7') | ~m1_subset_1('#skF_11', '#skF_7')), inference(resolution, [status(thm)], [c_12, c_4146])).
% 6.45/2.28  tff(c_4158, plain, (v1_xboole_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_4155])).
% 6.45/2.28  tff(c_4160, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1947, c_4158])).
% 6.45/2.28  tff(c_4161, plain, (k1_funct_1(k8_funct_2('#skF_7', '#skF_8', '#skF_6', '#skF_9', '#skF_10'), '#skF_11')!=k1_funct_1('#skF_10', k1_funct_1('#skF_9', '#skF_11'))), inference(splitRight, [status(thm)], [c_4142])).
% 6.45/2.28  tff(c_4242, plain, (~m1_subset_1('#skF_11', '#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_3939, c_4161])).
% 6.45/2.28  tff(c_4246, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_66, c_4242])).
% 6.45/2.28  tff(c_4247, plain, (k1_xboole_0='#skF_8'), inference(splitRight, [status(thm)], [c_1759])).
% 6.45/2.28  tff(c_8, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 6.45/2.28  tff(c_4255, plain, (v1_xboole_0('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_4247, c_8])).
% 6.45/2.28  tff(c_4258, plain, $false, inference(negUnitSimplification, [status(thm)], [c_78, c_4255])).
% 6.45/2.28  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.45/2.28  
% 6.45/2.28  Inference rules
% 6.45/2.28  ----------------------
% 6.45/2.28  #Ref     : 0
% 6.45/2.28  #Sup     : 897
% 6.45/2.28  #Fact    : 0
% 6.45/2.28  #Define  : 0
% 6.45/2.28  #Split   : 24
% 6.45/2.28  #Chain   : 0
% 6.45/2.28  #Close   : 0
% 6.45/2.28  
% 6.45/2.28  Ordering : KBO
% 6.45/2.28  
% 6.45/2.28  Simplification rules
% 6.45/2.28  ----------------------
% 6.45/2.28  #Subsume      : 222
% 6.45/2.28  #Demod        : 639
% 6.45/2.28  #Tautology    : 148
% 6.45/2.28  #SimpNegUnit  : 38
% 6.45/2.28  #BackRed      : 106
% 6.45/2.28  
% 6.45/2.28  #Partial instantiations: 0
% 6.45/2.28  #Strategies tried      : 1
% 6.45/2.28  
% 6.45/2.28  Timing (in seconds)
% 6.45/2.28  ----------------------
% 6.45/2.29  Preprocessing        : 0.38
% 6.45/2.29  Parsing              : 0.19
% 6.45/2.29  CNF conversion       : 0.04
% 6.45/2.29  Main loop            : 1.13
% 6.45/2.29  Inferencing          : 0.42
% 6.45/2.29  Reduction            : 0.33
% 6.45/2.29  Demodulation         : 0.23
% 6.45/2.29  BG Simplification    : 0.05
% 6.45/2.29  Subsumption          : 0.24
% 6.45/2.29  Abstraction          : 0.06
% 6.45/2.29  MUC search           : 0.00
% 6.45/2.29  Cooper               : 0.00
% 6.45/2.29  Total                : 1.56
% 6.45/2.29  Index Insertion      : 0.00
% 6.45/2.29  Index Deletion       : 0.00
% 6.45/2.29  Index Matching       : 0.00
% 6.45/2.29  BG Taut test         : 0.00
%------------------------------------------------------------------------------
