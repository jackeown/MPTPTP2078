%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:17:49 EST 2020

% Result     : Theorem 11.82s
% Output     : CNFRefutation 11.82s
% Verified   : 
% Statistics : Number of formulae       :  147 ( 707 expanded)
%              Number of leaves         :   50 ( 272 expanded)
%              Depth                    :   23
%              Number of atoms          :  333 (2573 expanded)
%              Number of equality atoms :   71 ( 584 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k8_funct_2 > k7_partfun1 > k2_relset_1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_11 > #skF_7 > #skF_3 > #skF_10 > #skF_6 > #skF_5 > #skF_9 > #skF_8 > #skF_2 > #skF_1 > #skF_4

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

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

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

tff(k1_partfun1,type,(
    k1_partfun1: ( $i * $i * $i * $i * $i * $i ) > $i )).

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

tff(f_174,negated_conjecture,(
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

tff(f_79,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_89,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_128,axiom,(
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

tff(f_139,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A)
        & v1_funct_1(B) )
     => ! [C] :
          ( r2_hidden(C,k1_relat_1(B))
         => k7_partfun1(A,B,C) = k1_funct_1(B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_partfun1)).

tff(f_33,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_41,axiom,(
    ! [A,B] :
      ~ ( v1_xboole_0(A)
        & A != B
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_boole)).

tff(f_85,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_62,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_funct_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_93,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_75,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ! [C] :
          ( ( v1_relat_1(C)
            & v1_funct_1(C) )
         => ( r2_hidden(A,k1_relat_1(B))
           => k1_funct_1(k5_relat_1(B,C),A) = k1_funct_1(C,k1_funct_1(B,A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_funct_1)).

tff(f_149,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_110,axiom,(
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

tff(c_80,plain,(
    ~ v1_xboole_0('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_174])).

tff(c_70,plain,(
    m1_subset_1('#skF_10',k1_zfmisc_1(k2_zfmisc_1('#skF_8','#skF_6'))) ),
    inference(cnfTransformation,[status(thm)],[f_174])).

tff(c_105,plain,(
    ! [C_106,A_107,B_108] :
      ( v1_relat_1(C_106)
      | ~ m1_subset_1(C_106,k1_zfmisc_1(k2_zfmisc_1(A_107,B_108))) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_113,plain,(
    v1_relat_1('#skF_10') ),
    inference(resolution,[status(thm)],[c_70,c_105])).

tff(c_72,plain,(
    v1_funct_1('#skF_10') ),
    inference(cnfTransformation,[status(thm)],[f_174])).

tff(c_64,plain,(
    k1_xboole_0 != '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_174])).

tff(c_12,plain,(
    ! [A_8,B_9] :
      ( r2_hidden(A_8,B_9)
      | v1_xboole_0(B_9)
      | ~ m1_subset_1(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_74,plain,(
    m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1('#skF_7','#skF_8'))) ),
    inference(cnfTransformation,[status(thm)],[f_174])).

tff(c_112,plain,(
    v1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_74,c_105])).

tff(c_78,plain,(
    v1_funct_1('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_174])).

tff(c_76,plain,(
    v1_funct_2('#skF_9','#skF_7','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_174])).

tff(c_157,plain,(
    ! [A_127,B_128,C_129] :
      ( k1_relset_1(A_127,B_128,C_129) = k1_relat_1(C_129)
      | ~ m1_subset_1(C_129,k1_zfmisc_1(k2_zfmisc_1(A_127,B_128))) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_164,plain,(
    k1_relset_1('#skF_7','#skF_8','#skF_9') = k1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_74,c_157])).

tff(c_13703,plain,(
    ! [B_964,A_965,C_966] :
      ( k1_xboole_0 = B_964
      | k1_relset_1(A_965,B_964,C_966) = A_965
      | ~ v1_funct_2(C_966,A_965,B_964)
      | ~ m1_subset_1(C_966,k1_zfmisc_1(k2_zfmisc_1(A_965,B_964))) ) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_13706,plain,
    ( k1_xboole_0 = '#skF_8'
    | k1_relset_1('#skF_7','#skF_8','#skF_9') = '#skF_7'
    | ~ v1_funct_2('#skF_9','#skF_7','#skF_8') ),
    inference(resolution,[status(thm)],[c_74,c_13703])).

tff(c_13712,plain,
    ( k1_xboole_0 = '#skF_8'
    | k1_relat_1('#skF_9') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_164,c_13706])).

tff(c_13715,plain,(
    k1_relat_1('#skF_9') = '#skF_7' ),
    inference(splitLeft,[status(thm)],[c_13712])).

tff(c_13768,plain,(
    ! [A_979,B_980,C_981] :
      ( k7_partfun1(A_979,B_980,C_981) = k1_funct_1(B_980,C_981)
      | ~ r2_hidden(C_981,k1_relat_1(B_980))
      | ~ v1_funct_1(B_980)
      | ~ v5_relat_1(B_980,A_979)
      | ~ v1_relat_1(B_980) ) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_13776,plain,(
    ! [A_979,C_981] :
      ( k7_partfun1(A_979,'#skF_9',C_981) = k1_funct_1('#skF_9',C_981)
      | ~ r2_hidden(C_981,'#skF_7')
      | ~ v1_funct_1('#skF_9')
      | ~ v5_relat_1('#skF_9',A_979)
      | ~ v1_relat_1('#skF_9') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_13715,c_13768])).

tff(c_13810,plain,(
    ! [A_982,C_983] :
      ( k7_partfun1(A_982,'#skF_9',C_983) = k1_funct_1('#skF_9',C_983)
      | ~ r2_hidden(C_983,'#skF_7')
      | ~ v5_relat_1('#skF_9',A_982) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_112,c_78,c_13776])).

tff(c_13839,plain,(
    ! [A_982,A_8] :
      ( k7_partfun1(A_982,'#skF_9',A_8) = k1_funct_1('#skF_9',A_8)
      | ~ v5_relat_1('#skF_9',A_982)
      | v1_xboole_0('#skF_7')
      | ~ m1_subset_1(A_8,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_12,c_13810])).

tff(c_13845,plain,(
    v1_xboole_0('#skF_7') ),
    inference(splitLeft,[status(thm)],[c_13839])).

tff(c_8,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_81,plain,(
    ! [B_96,A_97] :
      ( ~ v1_xboole_0(B_96)
      | B_96 = A_97
      | ~ v1_xboole_0(A_97) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_84,plain,(
    ! [A_97] :
      ( k1_xboole_0 = A_97
      | ~ v1_xboole_0(A_97) ) ),
    inference(resolution,[status(thm)],[c_8,c_81])).

tff(c_13848,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(resolution,[status(thm)],[c_13845,c_84])).

tff(c_13854,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_13848])).

tff(c_13856,plain,(
    ~ v1_xboole_0('#skF_7') ),
    inference(splitRight,[status(thm)],[c_13839])).

tff(c_68,plain,(
    m1_subset_1('#skF_11','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_174])).

tff(c_130,plain,(
    ! [C_115,B_116,A_117] :
      ( v5_relat_1(C_115,B_116)
      | ~ m1_subset_1(C_115,k1_zfmisc_1(k2_zfmisc_1(A_117,B_116))) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_138,plain,(
    v5_relat_1('#skF_10','#skF_6') ),
    inference(resolution,[status(thm)],[c_70,c_130])).

tff(c_14,plain,(
    ! [A_10,D_49] :
      ( r2_hidden(k1_funct_1(A_10,D_49),k2_relat_1(A_10))
      | ~ r2_hidden(D_49,k1_relat_1(A_10))
      | ~ v1_funct_1(A_10)
      | ~ v1_relat_1(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_98,plain,(
    ! [A_103,B_104] :
      ( r2_hidden('#skF_1'(A_103,B_104),A_103)
      | r1_tarski(A_103,B_104) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_103,plain,(
    ! [A_103] : r1_tarski(A_103,A_103) ),
    inference(resolution,[status(thm)],[c_98,c_4])).

tff(c_13674,plain,(
    ! [A_955,C_956] :
      ( r2_hidden('#skF_5'(A_955,k2_relat_1(A_955),C_956),k1_relat_1(A_955))
      | ~ r2_hidden(C_956,k2_relat_1(A_955))
      | ~ v1_funct_1(A_955)
      | ~ v1_relat_1(A_955) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_13677,plain,(
    ! [A_955,C_956,B_2] :
      ( r2_hidden('#skF_5'(A_955,k2_relat_1(A_955),C_956),B_2)
      | ~ r1_tarski(k1_relat_1(A_955),B_2)
      | ~ r2_hidden(C_956,k2_relat_1(A_955))
      | ~ v1_funct_1(A_955)
      | ~ v1_relat_1(A_955) ) ),
    inference(resolution,[status(thm)],[c_13674,c_2])).

tff(c_16,plain,(
    ! [A_10,C_46] :
      ( k1_funct_1(A_10,'#skF_5'(A_10,k2_relat_1(A_10),C_46)) = C_46
      | ~ r2_hidden(C_46,k2_relat_1(A_10))
      | ~ v1_funct_1(A_10)
      | ~ v1_relat_1(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_178,plain,(
    ! [A_130,B_131,C_132] :
      ( k2_relset_1(A_130,B_131,C_132) = k2_relat_1(C_132)
      | ~ m1_subset_1(C_132,k1_zfmisc_1(k2_zfmisc_1(A_130,B_131))) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_185,plain,(
    k2_relset_1('#skF_7','#skF_8','#skF_9') = k2_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_74,c_178])).

tff(c_165,plain,(
    k1_relset_1('#skF_8','#skF_6','#skF_10') = k1_relat_1('#skF_10') ),
    inference(resolution,[status(thm)],[c_70,c_157])).

tff(c_66,plain,(
    r1_tarski(k2_relset_1('#skF_7','#skF_8','#skF_9'),k1_relset_1('#skF_8','#skF_6','#skF_10')) ),
    inference(cnfTransformation,[status(thm)],[f_174])).

tff(c_170,plain,(
    r1_tarski(k2_relset_1('#skF_7','#skF_8','#skF_9'),k1_relat_1('#skF_10')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_165,c_66])).

tff(c_187,plain,(
    r1_tarski(k2_relat_1('#skF_9'),k1_relat_1('#skF_10')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_185,c_170])).

tff(c_13633,plain,(
    ! [A_940,D_941] :
      ( r2_hidden(k1_funct_1(A_940,D_941),k2_relat_1(A_940))
      | ~ r2_hidden(D_941,k1_relat_1(A_940))
      | ~ v1_funct_1(A_940)
      | ~ v1_relat_1(A_940) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_13753,plain,(
    ! [A_973,D_974,B_975] :
      ( r2_hidden(k1_funct_1(A_973,D_974),B_975)
      | ~ r1_tarski(k2_relat_1(A_973),B_975)
      | ~ r2_hidden(D_974,k1_relat_1(A_973))
      | ~ v1_funct_1(A_973)
      | ~ v1_relat_1(A_973) ) ),
    inference(resolution,[status(thm)],[c_13633,c_2])).

tff(c_14064,plain,(
    ! [A_1021,D_1022,B_1023,B_1024] :
      ( r2_hidden(k1_funct_1(A_1021,D_1022),B_1023)
      | ~ r1_tarski(B_1024,B_1023)
      | ~ r1_tarski(k2_relat_1(A_1021),B_1024)
      | ~ r2_hidden(D_1022,k1_relat_1(A_1021))
      | ~ v1_funct_1(A_1021)
      | ~ v1_relat_1(A_1021) ) ),
    inference(resolution,[status(thm)],[c_13753,c_2])).

tff(c_14071,plain,(
    ! [A_1025,D_1026] :
      ( r2_hidden(k1_funct_1(A_1025,D_1026),k1_relat_1('#skF_10'))
      | ~ r1_tarski(k2_relat_1(A_1025),k2_relat_1('#skF_9'))
      | ~ r2_hidden(D_1026,k1_relat_1(A_1025))
      | ~ v1_funct_1(A_1025)
      | ~ v1_relat_1(A_1025) ) ),
    inference(resolution,[status(thm)],[c_187,c_14064])).

tff(c_16535,plain,(
    ! [A_1241,D_1242,B_1243] :
      ( r2_hidden(k1_funct_1(A_1241,D_1242),B_1243)
      | ~ r1_tarski(k1_relat_1('#skF_10'),B_1243)
      | ~ r1_tarski(k2_relat_1(A_1241),k2_relat_1('#skF_9'))
      | ~ r2_hidden(D_1242,k1_relat_1(A_1241))
      | ~ v1_funct_1(A_1241)
      | ~ v1_relat_1(A_1241) ) ),
    inference(resolution,[status(thm)],[c_14071,c_2])).

tff(c_16538,plain,(
    ! [D_1242,B_1243] :
      ( r2_hidden(k1_funct_1('#skF_9',D_1242),B_1243)
      | ~ r1_tarski(k1_relat_1('#skF_10'),B_1243)
      | ~ r2_hidden(D_1242,k1_relat_1('#skF_9'))
      | ~ v1_funct_1('#skF_9')
      | ~ v1_relat_1('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_103,c_16535])).

tff(c_16558,plain,(
    ! [D_1247,B_1248] :
      ( r2_hidden(k1_funct_1('#skF_9',D_1247),B_1248)
      | ~ r1_tarski(k1_relat_1('#skF_10'),B_1248)
      | ~ r2_hidden(D_1247,'#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_112,c_78,c_13715,c_16538])).

tff(c_16575,plain,(
    ! [C_46,B_1248] :
      ( r2_hidden(C_46,B_1248)
      | ~ r1_tarski(k1_relat_1('#skF_10'),B_1248)
      | ~ r2_hidden('#skF_5'('#skF_9',k2_relat_1('#skF_9'),C_46),'#skF_7')
      | ~ r2_hidden(C_46,k2_relat_1('#skF_9'))
      | ~ v1_funct_1('#skF_9')
      | ~ v1_relat_1('#skF_9') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_16558])).

tff(c_16590,plain,(
    ! [C_1252,B_1253] :
      ( r2_hidden(C_1252,B_1253)
      | ~ r1_tarski(k1_relat_1('#skF_10'),B_1253)
      | ~ r2_hidden('#skF_5'('#skF_9',k2_relat_1('#skF_9'),C_1252),'#skF_7')
      | ~ r2_hidden(C_1252,k2_relat_1('#skF_9')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_112,c_78,c_16575])).

tff(c_16602,plain,(
    ! [C_1257] :
      ( r2_hidden(C_1257,k1_relat_1('#skF_10'))
      | ~ r2_hidden('#skF_5'('#skF_9',k2_relat_1('#skF_9'),C_1257),'#skF_7')
      | ~ r2_hidden(C_1257,k2_relat_1('#skF_9')) ) ),
    inference(resolution,[status(thm)],[c_103,c_16590])).

tff(c_16610,plain,(
    ! [C_956] :
      ( r2_hidden(C_956,k1_relat_1('#skF_10'))
      | ~ r1_tarski(k1_relat_1('#skF_9'),'#skF_7')
      | ~ r2_hidden(C_956,k2_relat_1('#skF_9'))
      | ~ v1_funct_1('#skF_9')
      | ~ v1_relat_1('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_13677,c_16602])).

tff(c_16634,plain,(
    ! [C_1258] :
      ( r2_hidden(C_1258,k1_relat_1('#skF_10'))
      | ~ r2_hidden(C_1258,k2_relat_1('#skF_9')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_112,c_78,c_103,c_13715,c_16610])).

tff(c_16714,plain,(
    ! [D_49] :
      ( r2_hidden(k1_funct_1('#skF_9',D_49),k1_relat_1('#skF_10'))
      | ~ r2_hidden(D_49,k1_relat_1('#skF_9'))
      | ~ v1_funct_1('#skF_9')
      | ~ v1_relat_1('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_14,c_16634])).

tff(c_16771,plain,(
    ! [D_1260] :
      ( r2_hidden(k1_funct_1('#skF_9',D_1260),k1_relat_1('#skF_10'))
      | ~ r2_hidden(D_1260,'#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_112,c_78,c_13715,c_16714])).

tff(c_58,plain,(
    ! [A_75,B_76,C_78] :
      ( k7_partfun1(A_75,B_76,C_78) = k1_funct_1(B_76,C_78)
      | ~ r2_hidden(C_78,k1_relat_1(B_76))
      | ~ v1_funct_1(B_76)
      | ~ v5_relat_1(B_76,A_75)
      | ~ v1_relat_1(B_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_16775,plain,(
    ! [A_75,D_1260] :
      ( k7_partfun1(A_75,'#skF_10',k1_funct_1('#skF_9',D_1260)) = k1_funct_1('#skF_10',k1_funct_1('#skF_9',D_1260))
      | ~ v1_funct_1('#skF_10')
      | ~ v5_relat_1('#skF_10',A_75)
      | ~ v1_relat_1('#skF_10')
      | ~ r2_hidden(D_1260,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_16771,c_58])).

tff(c_16895,plain,(
    ! [A_1271,D_1272] :
      ( k7_partfun1(A_1271,'#skF_10',k1_funct_1('#skF_9',D_1272)) = k1_funct_1('#skF_10',k1_funct_1('#skF_9',D_1272))
      | ~ v5_relat_1('#skF_10',A_1271)
      | ~ r2_hidden(D_1272,'#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_113,c_72,c_16775])).

tff(c_62,plain,(
    k7_partfun1('#skF_6','#skF_10',k1_funct_1('#skF_9','#skF_11')) != k1_funct_1(k8_funct_2('#skF_7','#skF_8','#skF_6','#skF_9','#skF_10'),'#skF_11') ),
    inference(cnfTransformation,[status(thm)],[f_174])).

tff(c_16901,plain,
    ( k1_funct_1(k8_funct_2('#skF_7','#skF_8','#skF_6','#skF_9','#skF_10'),'#skF_11') != k1_funct_1('#skF_10',k1_funct_1('#skF_9','#skF_11'))
    | ~ v5_relat_1('#skF_10','#skF_6')
    | ~ r2_hidden('#skF_11','#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_16895,c_62])).

tff(c_16913,plain,
    ( k1_funct_1(k8_funct_2('#skF_7','#skF_8','#skF_6','#skF_9','#skF_10'),'#skF_11') != k1_funct_1('#skF_10',k1_funct_1('#skF_9','#skF_11'))
    | ~ r2_hidden('#skF_11','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_138,c_16901])).

tff(c_16917,plain,(
    ~ r2_hidden('#skF_11','#skF_7') ),
    inference(splitLeft,[status(thm)],[c_16913])).

tff(c_16933,plain,
    ( v1_xboole_0('#skF_7')
    | ~ m1_subset_1('#skF_11','#skF_7') ),
    inference(resolution,[status(thm)],[c_12,c_16917])).

tff(c_16936,plain,(
    v1_xboole_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_16933])).

tff(c_16938,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_13856,c_16936])).

tff(c_16940,plain,(
    r2_hidden('#skF_11','#skF_7') ),
    inference(splitRight,[status(thm)],[c_16913])).

tff(c_16270,plain,(
    ! [B_1208,C_1209,A_1210] :
      ( k1_funct_1(k5_relat_1(B_1208,C_1209),A_1210) = k1_funct_1(C_1209,k1_funct_1(B_1208,A_1210))
      | ~ r2_hidden(A_1210,k1_relat_1(B_1208))
      | ~ v1_funct_1(C_1209)
      | ~ v1_relat_1(C_1209)
      | ~ v1_funct_1(B_1208)
      | ~ v1_relat_1(B_1208) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_16321,plain,(
    ! [C_1209,A_1210] :
      ( k1_funct_1(k5_relat_1('#skF_9',C_1209),A_1210) = k1_funct_1(C_1209,k1_funct_1('#skF_9',A_1210))
      | ~ r2_hidden(A_1210,'#skF_7')
      | ~ v1_funct_1(C_1209)
      | ~ v1_relat_1(C_1209)
      | ~ v1_funct_1('#skF_9')
      | ~ v1_relat_1('#skF_9') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_13715,c_16270])).

tff(c_16365,plain,(
    ! [C_1209,A_1210] :
      ( k1_funct_1(k5_relat_1('#skF_9',C_1209),A_1210) = k1_funct_1(C_1209,k1_funct_1('#skF_9',A_1210))
      | ~ r2_hidden(A_1210,'#skF_7')
      | ~ v1_funct_1(C_1209)
      | ~ v1_relat_1(C_1209) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_112,c_78,c_16321])).

tff(c_16884,plain,(
    ! [A_1266,E_1270,B_1269,F_1268,D_1265,C_1267] :
      ( k1_partfun1(A_1266,B_1269,C_1267,D_1265,E_1270,F_1268) = k5_relat_1(E_1270,F_1268)
      | ~ m1_subset_1(F_1268,k1_zfmisc_1(k2_zfmisc_1(C_1267,D_1265)))
      | ~ v1_funct_1(F_1268)
      | ~ m1_subset_1(E_1270,k1_zfmisc_1(k2_zfmisc_1(A_1266,B_1269)))
      | ~ v1_funct_1(E_1270) ) ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_16888,plain,(
    ! [A_1266,B_1269,E_1270] :
      ( k1_partfun1(A_1266,B_1269,'#skF_8','#skF_6',E_1270,'#skF_10') = k5_relat_1(E_1270,'#skF_10')
      | ~ v1_funct_1('#skF_10')
      | ~ m1_subset_1(E_1270,k1_zfmisc_1(k2_zfmisc_1(A_1266,B_1269)))
      | ~ v1_funct_1(E_1270) ) ),
    inference(resolution,[status(thm)],[c_70,c_16884])).

tff(c_17040,plain,(
    ! [A_1293,B_1294,E_1295] :
      ( k1_partfun1(A_1293,B_1294,'#skF_8','#skF_6',E_1295,'#skF_10') = k5_relat_1(E_1295,'#skF_10')
      | ~ m1_subset_1(E_1295,k1_zfmisc_1(k2_zfmisc_1(A_1293,B_1294)))
      | ~ v1_funct_1(E_1295) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_16888])).

tff(c_17043,plain,
    ( k1_partfun1('#skF_7','#skF_8','#skF_8','#skF_6','#skF_9','#skF_10') = k5_relat_1('#skF_9','#skF_10')
    | ~ v1_funct_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_74,c_17040])).

tff(c_17049,plain,(
    k1_partfun1('#skF_7','#skF_8','#skF_8','#skF_6','#skF_9','#skF_10') = k5_relat_1('#skF_9','#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_17043])).

tff(c_16986,plain,(
    ! [D_1284,E_1280,A_1281,C_1283,B_1282] :
      ( k1_partfun1(A_1281,B_1282,B_1282,C_1283,D_1284,E_1280) = k8_funct_2(A_1281,B_1282,C_1283,D_1284,E_1280)
      | k1_xboole_0 = B_1282
      | ~ r1_tarski(k2_relset_1(A_1281,B_1282,D_1284),k1_relset_1(B_1282,C_1283,E_1280))
      | ~ m1_subset_1(E_1280,k1_zfmisc_1(k2_zfmisc_1(B_1282,C_1283)))
      | ~ v1_funct_1(E_1280)
      | ~ m1_subset_1(D_1284,k1_zfmisc_1(k2_zfmisc_1(A_1281,B_1282)))
      | ~ v1_funct_2(D_1284,A_1281,B_1282)
      | ~ v1_funct_1(D_1284) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_16995,plain,(
    ! [C_1283,E_1280] :
      ( k1_partfun1('#skF_7','#skF_8','#skF_8',C_1283,'#skF_9',E_1280) = k8_funct_2('#skF_7','#skF_8',C_1283,'#skF_9',E_1280)
      | k1_xboole_0 = '#skF_8'
      | ~ r1_tarski(k2_relat_1('#skF_9'),k1_relset_1('#skF_8',C_1283,E_1280))
      | ~ m1_subset_1(E_1280,k1_zfmisc_1(k2_zfmisc_1('#skF_8',C_1283)))
      | ~ v1_funct_1(E_1280)
      | ~ m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1('#skF_7','#skF_8')))
      | ~ v1_funct_2('#skF_9','#skF_7','#skF_8')
      | ~ v1_funct_1('#skF_9') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_185,c_16986])).

tff(c_17005,plain,(
    ! [C_1283,E_1280] :
      ( k1_partfun1('#skF_7','#skF_8','#skF_8',C_1283,'#skF_9',E_1280) = k8_funct_2('#skF_7','#skF_8',C_1283,'#skF_9',E_1280)
      | k1_xboole_0 = '#skF_8'
      | ~ r1_tarski(k2_relat_1('#skF_9'),k1_relset_1('#skF_8',C_1283,E_1280))
      | ~ m1_subset_1(E_1280,k1_zfmisc_1(k2_zfmisc_1('#skF_8',C_1283)))
      | ~ v1_funct_1(E_1280) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_74,c_16995])).

tff(c_17137,plain,(
    k1_xboole_0 = '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_17005])).

tff(c_17146,plain,(
    v1_xboole_0('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_17137,c_8])).

tff(c_17149,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_17146])).

tff(c_17151,plain,(
    k1_xboole_0 != '#skF_8' ),
    inference(splitRight,[status(thm)],[c_17005])).

tff(c_16998,plain,(
    ! [A_1281,D_1284] :
      ( k1_partfun1(A_1281,'#skF_8','#skF_8','#skF_6',D_1284,'#skF_10') = k8_funct_2(A_1281,'#skF_8','#skF_6',D_1284,'#skF_10')
      | k1_xboole_0 = '#skF_8'
      | ~ r1_tarski(k2_relset_1(A_1281,'#skF_8',D_1284),k1_relat_1('#skF_10'))
      | ~ m1_subset_1('#skF_10',k1_zfmisc_1(k2_zfmisc_1('#skF_8','#skF_6')))
      | ~ v1_funct_1('#skF_10')
      | ~ m1_subset_1(D_1284,k1_zfmisc_1(k2_zfmisc_1(A_1281,'#skF_8')))
      | ~ v1_funct_2(D_1284,A_1281,'#skF_8')
      | ~ v1_funct_1(D_1284) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_165,c_16986])).

tff(c_17007,plain,(
    ! [A_1281,D_1284] :
      ( k1_partfun1(A_1281,'#skF_8','#skF_8','#skF_6',D_1284,'#skF_10') = k8_funct_2(A_1281,'#skF_8','#skF_6',D_1284,'#skF_10')
      | k1_xboole_0 = '#skF_8'
      | ~ r1_tarski(k2_relset_1(A_1281,'#skF_8',D_1284),k1_relat_1('#skF_10'))
      | ~ m1_subset_1(D_1284,k1_zfmisc_1(k2_zfmisc_1(A_1281,'#skF_8')))
      | ~ v1_funct_2(D_1284,A_1281,'#skF_8')
      | ~ v1_funct_1(D_1284) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_16998])).

tff(c_17243,plain,(
    ! [A_1308,D_1309] :
      ( k1_partfun1(A_1308,'#skF_8','#skF_8','#skF_6',D_1309,'#skF_10') = k8_funct_2(A_1308,'#skF_8','#skF_6',D_1309,'#skF_10')
      | ~ r1_tarski(k2_relset_1(A_1308,'#skF_8',D_1309),k1_relat_1('#skF_10'))
      | ~ m1_subset_1(D_1309,k1_zfmisc_1(k2_zfmisc_1(A_1308,'#skF_8')))
      | ~ v1_funct_2(D_1309,A_1308,'#skF_8')
      | ~ v1_funct_1(D_1309) ) ),
    inference(negUnitSimplification,[status(thm)],[c_17151,c_17007])).

tff(c_17246,plain,
    ( k1_partfun1('#skF_7','#skF_8','#skF_8','#skF_6','#skF_9','#skF_10') = k8_funct_2('#skF_7','#skF_8','#skF_6','#skF_9','#skF_10')
    | ~ r1_tarski(k2_relat_1('#skF_9'),k1_relat_1('#skF_10'))
    | ~ m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1('#skF_7','#skF_8')))
    | ~ v1_funct_2('#skF_9','#skF_7','#skF_8')
    | ~ v1_funct_1('#skF_9') ),
    inference(superposition,[status(thm),theory(equality)],[c_185,c_17243])).

tff(c_17248,plain,(
    k8_funct_2('#skF_7','#skF_8','#skF_6','#skF_9','#skF_10') = k5_relat_1('#skF_9','#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_74,c_187,c_17049,c_17246])).

tff(c_16939,plain,(
    k1_funct_1(k8_funct_2('#skF_7','#skF_8','#skF_6','#skF_9','#skF_10'),'#skF_11') != k1_funct_1('#skF_10',k1_funct_1('#skF_9','#skF_11')) ),
    inference(splitRight,[status(thm)],[c_16913])).

tff(c_17249,plain,(
    k1_funct_1(k5_relat_1('#skF_9','#skF_10'),'#skF_11') != k1_funct_1('#skF_10',k1_funct_1('#skF_9','#skF_11')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_17248,c_16939])).

tff(c_17257,plain,
    ( ~ r2_hidden('#skF_11','#skF_7')
    | ~ v1_funct_1('#skF_10')
    | ~ v1_relat_1('#skF_10') ),
    inference(superposition,[status(thm),theory(equality)],[c_16365,c_17249])).

tff(c_17261,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_113,c_72,c_16940,c_17257])).

tff(c_17262,plain,(
    k1_xboole_0 = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_13712])).

tff(c_17270,plain,(
    v1_xboole_0('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_17262,c_8])).

tff(c_17273,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_17270])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:04:22 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 11.82/5.02  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.82/5.03  
% 11.82/5.03  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.82/5.03  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k8_funct_2 > k7_partfun1 > k2_relset_1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_11 > #skF_7 > #skF_3 > #skF_10 > #skF_6 > #skF_5 > #skF_9 > #skF_8 > #skF_2 > #skF_1 > #skF_4
% 11.82/5.03  
% 11.82/5.03  %Foreground sorts:
% 11.82/5.03  
% 11.82/5.03  
% 11.82/5.03  %Background operators:
% 11.82/5.03  
% 11.82/5.03  
% 11.82/5.03  %Foreground operators:
% 11.82/5.03  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 11.82/5.03  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 11.82/5.03  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 11.82/5.03  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 11.82/5.03  tff('#skF_11', type, '#skF_11': $i).
% 11.82/5.03  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 11.82/5.03  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 11.82/5.03  tff('#skF_7', type, '#skF_7': $i).
% 11.82/5.03  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 11.82/5.03  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 11.82/5.03  tff('#skF_10', type, '#skF_10': $i).
% 11.82/5.03  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 11.82/5.03  tff(k7_partfun1, type, k7_partfun1: ($i * $i * $i) > $i).
% 11.82/5.03  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 11.82/5.03  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 11.82/5.03  tff(k8_funct_2, type, k8_funct_2: ($i * $i * $i * $i * $i) > $i).
% 11.82/5.03  tff('#skF_6', type, '#skF_6': $i).
% 11.82/5.03  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 11.82/5.03  tff('#skF_9', type, '#skF_9': $i).
% 11.82/5.03  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 11.82/5.03  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 11.82/5.03  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 11.82/5.03  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 11.82/5.03  tff('#skF_8', type, '#skF_8': $i).
% 11.82/5.03  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 11.82/5.03  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 11.82/5.03  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 11.82/5.03  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 11.82/5.03  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 11.82/5.03  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 11.82/5.03  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 11.82/5.03  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 11.82/5.03  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 11.82/5.03  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 11.82/5.03  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 11.82/5.03  
% 11.82/5.05  tff(f_174, negated_conjecture, ~(![A, B, C]: (~v1_xboole_0(C) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, C)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (![E]: ((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(C, A)))) => (![F]: (m1_subset_1(F, B) => (r1_tarski(k2_relset_1(B, C, D), k1_relset_1(C, A, E)) => ((B = k1_xboole_0) | (k1_funct_1(k8_funct_2(B, C, A, D, E), F) = k7_partfun1(A, E, k1_funct_1(D, F))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t186_funct_2)).
% 11.82/5.05  tff(f_79, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 11.82/5.05  tff(f_47, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 11.82/5.05  tff(f_89, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 11.82/5.05  tff(f_128, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 11.82/5.05  tff(f_139, axiom, (![A, B]: (((v1_relat_1(B) & v5_relat_1(B, A)) & v1_funct_1(B)) => (![C]: (r2_hidden(C, k1_relat_1(B)) => (k7_partfun1(A, B, C) = k1_funct_1(B, C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_partfun1)).
% 11.82/5.05  tff(f_33, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 11.82/5.05  tff(f_41, axiom, (![A, B]: ~((v1_xboole_0(A) & ~(A = B)) & v1_xboole_0(B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_boole)).
% 11.82/5.05  tff(f_85, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 11.82/5.05  tff(f_62, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((B = k2_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: (r2_hidden(D, k1_relat_1(A)) & (C = k1_funct_1(A, D)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_funct_1)).
% 11.82/5.05  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 11.82/5.05  tff(f_93, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 11.82/5.05  tff(f_75, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (![C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(A, k1_relat_1(B)) => (k1_funct_1(k5_relat_1(B, C), A) = k1_funct_1(C, k1_funct_1(B, A)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t23_funct_1)).
% 11.82/5.05  tff(f_149, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 11.82/5.05  tff(f_110, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: ((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (r1_tarski(k2_relset_1(A, B, D), k1_relset_1(B, C, E)) => ((B = k1_xboole_0) | (k8_funct_2(A, B, C, D, E) = k1_partfun1(A, B, B, C, D, E)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d12_funct_2)).
% 11.82/5.05  tff(c_80, plain, (~v1_xboole_0('#skF_8')), inference(cnfTransformation, [status(thm)], [f_174])).
% 11.82/5.05  tff(c_70, plain, (m1_subset_1('#skF_10', k1_zfmisc_1(k2_zfmisc_1('#skF_8', '#skF_6')))), inference(cnfTransformation, [status(thm)], [f_174])).
% 11.82/5.05  tff(c_105, plain, (![C_106, A_107, B_108]: (v1_relat_1(C_106) | ~m1_subset_1(C_106, k1_zfmisc_1(k2_zfmisc_1(A_107, B_108))))), inference(cnfTransformation, [status(thm)], [f_79])).
% 11.82/5.05  tff(c_113, plain, (v1_relat_1('#skF_10')), inference(resolution, [status(thm)], [c_70, c_105])).
% 11.82/5.05  tff(c_72, plain, (v1_funct_1('#skF_10')), inference(cnfTransformation, [status(thm)], [f_174])).
% 11.82/5.05  tff(c_64, plain, (k1_xboole_0!='#skF_7'), inference(cnfTransformation, [status(thm)], [f_174])).
% 11.82/5.05  tff(c_12, plain, (![A_8, B_9]: (r2_hidden(A_8, B_9) | v1_xboole_0(B_9) | ~m1_subset_1(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_47])).
% 11.82/5.05  tff(c_74, plain, (m1_subset_1('#skF_9', k1_zfmisc_1(k2_zfmisc_1('#skF_7', '#skF_8')))), inference(cnfTransformation, [status(thm)], [f_174])).
% 11.82/5.05  tff(c_112, plain, (v1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_74, c_105])).
% 11.82/5.05  tff(c_78, plain, (v1_funct_1('#skF_9')), inference(cnfTransformation, [status(thm)], [f_174])).
% 11.82/5.05  tff(c_76, plain, (v1_funct_2('#skF_9', '#skF_7', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_174])).
% 11.82/5.05  tff(c_157, plain, (![A_127, B_128, C_129]: (k1_relset_1(A_127, B_128, C_129)=k1_relat_1(C_129) | ~m1_subset_1(C_129, k1_zfmisc_1(k2_zfmisc_1(A_127, B_128))))), inference(cnfTransformation, [status(thm)], [f_89])).
% 11.82/5.05  tff(c_164, plain, (k1_relset_1('#skF_7', '#skF_8', '#skF_9')=k1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_74, c_157])).
% 11.82/5.05  tff(c_13703, plain, (![B_964, A_965, C_966]: (k1_xboole_0=B_964 | k1_relset_1(A_965, B_964, C_966)=A_965 | ~v1_funct_2(C_966, A_965, B_964) | ~m1_subset_1(C_966, k1_zfmisc_1(k2_zfmisc_1(A_965, B_964))))), inference(cnfTransformation, [status(thm)], [f_128])).
% 11.82/5.05  tff(c_13706, plain, (k1_xboole_0='#skF_8' | k1_relset_1('#skF_7', '#skF_8', '#skF_9')='#skF_7' | ~v1_funct_2('#skF_9', '#skF_7', '#skF_8')), inference(resolution, [status(thm)], [c_74, c_13703])).
% 11.82/5.05  tff(c_13712, plain, (k1_xboole_0='#skF_8' | k1_relat_1('#skF_9')='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_76, c_164, c_13706])).
% 11.82/5.05  tff(c_13715, plain, (k1_relat_1('#skF_9')='#skF_7'), inference(splitLeft, [status(thm)], [c_13712])).
% 11.82/5.05  tff(c_13768, plain, (![A_979, B_980, C_981]: (k7_partfun1(A_979, B_980, C_981)=k1_funct_1(B_980, C_981) | ~r2_hidden(C_981, k1_relat_1(B_980)) | ~v1_funct_1(B_980) | ~v5_relat_1(B_980, A_979) | ~v1_relat_1(B_980))), inference(cnfTransformation, [status(thm)], [f_139])).
% 11.82/5.05  tff(c_13776, plain, (![A_979, C_981]: (k7_partfun1(A_979, '#skF_9', C_981)=k1_funct_1('#skF_9', C_981) | ~r2_hidden(C_981, '#skF_7') | ~v1_funct_1('#skF_9') | ~v5_relat_1('#skF_9', A_979) | ~v1_relat_1('#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_13715, c_13768])).
% 11.82/5.05  tff(c_13810, plain, (![A_982, C_983]: (k7_partfun1(A_982, '#skF_9', C_983)=k1_funct_1('#skF_9', C_983) | ~r2_hidden(C_983, '#skF_7') | ~v5_relat_1('#skF_9', A_982))), inference(demodulation, [status(thm), theory('equality')], [c_112, c_78, c_13776])).
% 11.82/5.05  tff(c_13839, plain, (![A_982, A_8]: (k7_partfun1(A_982, '#skF_9', A_8)=k1_funct_1('#skF_9', A_8) | ~v5_relat_1('#skF_9', A_982) | v1_xboole_0('#skF_7') | ~m1_subset_1(A_8, '#skF_7'))), inference(resolution, [status(thm)], [c_12, c_13810])).
% 11.82/5.05  tff(c_13845, plain, (v1_xboole_0('#skF_7')), inference(splitLeft, [status(thm)], [c_13839])).
% 11.82/5.05  tff(c_8, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 11.82/5.05  tff(c_81, plain, (![B_96, A_97]: (~v1_xboole_0(B_96) | B_96=A_97 | ~v1_xboole_0(A_97))), inference(cnfTransformation, [status(thm)], [f_41])).
% 11.82/5.05  tff(c_84, plain, (![A_97]: (k1_xboole_0=A_97 | ~v1_xboole_0(A_97))), inference(resolution, [status(thm)], [c_8, c_81])).
% 11.82/5.05  tff(c_13848, plain, (k1_xboole_0='#skF_7'), inference(resolution, [status(thm)], [c_13845, c_84])).
% 11.82/5.05  tff(c_13854, plain, $false, inference(negUnitSimplification, [status(thm)], [c_64, c_13848])).
% 11.82/5.05  tff(c_13856, plain, (~v1_xboole_0('#skF_7')), inference(splitRight, [status(thm)], [c_13839])).
% 11.82/5.05  tff(c_68, plain, (m1_subset_1('#skF_11', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_174])).
% 11.82/5.05  tff(c_130, plain, (![C_115, B_116, A_117]: (v5_relat_1(C_115, B_116) | ~m1_subset_1(C_115, k1_zfmisc_1(k2_zfmisc_1(A_117, B_116))))), inference(cnfTransformation, [status(thm)], [f_85])).
% 11.82/5.05  tff(c_138, plain, (v5_relat_1('#skF_10', '#skF_6')), inference(resolution, [status(thm)], [c_70, c_130])).
% 11.82/5.05  tff(c_14, plain, (![A_10, D_49]: (r2_hidden(k1_funct_1(A_10, D_49), k2_relat_1(A_10)) | ~r2_hidden(D_49, k1_relat_1(A_10)) | ~v1_funct_1(A_10) | ~v1_relat_1(A_10))), inference(cnfTransformation, [status(thm)], [f_62])).
% 11.82/5.05  tff(c_98, plain, (![A_103, B_104]: (r2_hidden('#skF_1'(A_103, B_104), A_103) | r1_tarski(A_103, B_104))), inference(cnfTransformation, [status(thm)], [f_32])).
% 11.82/5.05  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 11.82/5.05  tff(c_103, plain, (![A_103]: (r1_tarski(A_103, A_103))), inference(resolution, [status(thm)], [c_98, c_4])).
% 11.82/5.05  tff(c_13674, plain, (![A_955, C_956]: (r2_hidden('#skF_5'(A_955, k2_relat_1(A_955), C_956), k1_relat_1(A_955)) | ~r2_hidden(C_956, k2_relat_1(A_955)) | ~v1_funct_1(A_955) | ~v1_relat_1(A_955))), inference(cnfTransformation, [status(thm)], [f_62])).
% 11.82/5.05  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 11.82/5.05  tff(c_13677, plain, (![A_955, C_956, B_2]: (r2_hidden('#skF_5'(A_955, k2_relat_1(A_955), C_956), B_2) | ~r1_tarski(k1_relat_1(A_955), B_2) | ~r2_hidden(C_956, k2_relat_1(A_955)) | ~v1_funct_1(A_955) | ~v1_relat_1(A_955))), inference(resolution, [status(thm)], [c_13674, c_2])).
% 11.82/5.05  tff(c_16, plain, (![A_10, C_46]: (k1_funct_1(A_10, '#skF_5'(A_10, k2_relat_1(A_10), C_46))=C_46 | ~r2_hidden(C_46, k2_relat_1(A_10)) | ~v1_funct_1(A_10) | ~v1_relat_1(A_10))), inference(cnfTransformation, [status(thm)], [f_62])).
% 11.82/5.05  tff(c_178, plain, (![A_130, B_131, C_132]: (k2_relset_1(A_130, B_131, C_132)=k2_relat_1(C_132) | ~m1_subset_1(C_132, k1_zfmisc_1(k2_zfmisc_1(A_130, B_131))))), inference(cnfTransformation, [status(thm)], [f_93])).
% 11.82/5.05  tff(c_185, plain, (k2_relset_1('#skF_7', '#skF_8', '#skF_9')=k2_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_74, c_178])).
% 11.82/5.05  tff(c_165, plain, (k1_relset_1('#skF_8', '#skF_6', '#skF_10')=k1_relat_1('#skF_10')), inference(resolution, [status(thm)], [c_70, c_157])).
% 11.82/5.05  tff(c_66, plain, (r1_tarski(k2_relset_1('#skF_7', '#skF_8', '#skF_9'), k1_relset_1('#skF_8', '#skF_6', '#skF_10'))), inference(cnfTransformation, [status(thm)], [f_174])).
% 11.82/5.05  tff(c_170, plain, (r1_tarski(k2_relset_1('#skF_7', '#skF_8', '#skF_9'), k1_relat_1('#skF_10'))), inference(demodulation, [status(thm), theory('equality')], [c_165, c_66])).
% 11.82/5.05  tff(c_187, plain, (r1_tarski(k2_relat_1('#skF_9'), k1_relat_1('#skF_10'))), inference(demodulation, [status(thm), theory('equality')], [c_185, c_170])).
% 11.82/5.05  tff(c_13633, plain, (![A_940, D_941]: (r2_hidden(k1_funct_1(A_940, D_941), k2_relat_1(A_940)) | ~r2_hidden(D_941, k1_relat_1(A_940)) | ~v1_funct_1(A_940) | ~v1_relat_1(A_940))), inference(cnfTransformation, [status(thm)], [f_62])).
% 11.82/5.05  tff(c_13753, plain, (![A_973, D_974, B_975]: (r2_hidden(k1_funct_1(A_973, D_974), B_975) | ~r1_tarski(k2_relat_1(A_973), B_975) | ~r2_hidden(D_974, k1_relat_1(A_973)) | ~v1_funct_1(A_973) | ~v1_relat_1(A_973))), inference(resolution, [status(thm)], [c_13633, c_2])).
% 11.82/5.05  tff(c_14064, plain, (![A_1021, D_1022, B_1023, B_1024]: (r2_hidden(k1_funct_1(A_1021, D_1022), B_1023) | ~r1_tarski(B_1024, B_1023) | ~r1_tarski(k2_relat_1(A_1021), B_1024) | ~r2_hidden(D_1022, k1_relat_1(A_1021)) | ~v1_funct_1(A_1021) | ~v1_relat_1(A_1021))), inference(resolution, [status(thm)], [c_13753, c_2])).
% 11.82/5.05  tff(c_14071, plain, (![A_1025, D_1026]: (r2_hidden(k1_funct_1(A_1025, D_1026), k1_relat_1('#skF_10')) | ~r1_tarski(k2_relat_1(A_1025), k2_relat_1('#skF_9')) | ~r2_hidden(D_1026, k1_relat_1(A_1025)) | ~v1_funct_1(A_1025) | ~v1_relat_1(A_1025))), inference(resolution, [status(thm)], [c_187, c_14064])).
% 11.82/5.05  tff(c_16535, plain, (![A_1241, D_1242, B_1243]: (r2_hidden(k1_funct_1(A_1241, D_1242), B_1243) | ~r1_tarski(k1_relat_1('#skF_10'), B_1243) | ~r1_tarski(k2_relat_1(A_1241), k2_relat_1('#skF_9')) | ~r2_hidden(D_1242, k1_relat_1(A_1241)) | ~v1_funct_1(A_1241) | ~v1_relat_1(A_1241))), inference(resolution, [status(thm)], [c_14071, c_2])).
% 11.82/5.05  tff(c_16538, plain, (![D_1242, B_1243]: (r2_hidden(k1_funct_1('#skF_9', D_1242), B_1243) | ~r1_tarski(k1_relat_1('#skF_10'), B_1243) | ~r2_hidden(D_1242, k1_relat_1('#skF_9')) | ~v1_funct_1('#skF_9') | ~v1_relat_1('#skF_9'))), inference(resolution, [status(thm)], [c_103, c_16535])).
% 11.82/5.05  tff(c_16558, plain, (![D_1247, B_1248]: (r2_hidden(k1_funct_1('#skF_9', D_1247), B_1248) | ~r1_tarski(k1_relat_1('#skF_10'), B_1248) | ~r2_hidden(D_1247, '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_112, c_78, c_13715, c_16538])).
% 11.82/5.05  tff(c_16575, plain, (![C_46, B_1248]: (r2_hidden(C_46, B_1248) | ~r1_tarski(k1_relat_1('#skF_10'), B_1248) | ~r2_hidden('#skF_5'('#skF_9', k2_relat_1('#skF_9'), C_46), '#skF_7') | ~r2_hidden(C_46, k2_relat_1('#skF_9')) | ~v1_funct_1('#skF_9') | ~v1_relat_1('#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_16, c_16558])).
% 11.82/5.05  tff(c_16590, plain, (![C_1252, B_1253]: (r2_hidden(C_1252, B_1253) | ~r1_tarski(k1_relat_1('#skF_10'), B_1253) | ~r2_hidden('#skF_5'('#skF_9', k2_relat_1('#skF_9'), C_1252), '#skF_7') | ~r2_hidden(C_1252, k2_relat_1('#skF_9')))), inference(demodulation, [status(thm), theory('equality')], [c_112, c_78, c_16575])).
% 11.82/5.05  tff(c_16602, plain, (![C_1257]: (r2_hidden(C_1257, k1_relat_1('#skF_10')) | ~r2_hidden('#skF_5'('#skF_9', k2_relat_1('#skF_9'), C_1257), '#skF_7') | ~r2_hidden(C_1257, k2_relat_1('#skF_9')))), inference(resolution, [status(thm)], [c_103, c_16590])).
% 11.82/5.05  tff(c_16610, plain, (![C_956]: (r2_hidden(C_956, k1_relat_1('#skF_10')) | ~r1_tarski(k1_relat_1('#skF_9'), '#skF_7') | ~r2_hidden(C_956, k2_relat_1('#skF_9')) | ~v1_funct_1('#skF_9') | ~v1_relat_1('#skF_9'))), inference(resolution, [status(thm)], [c_13677, c_16602])).
% 11.82/5.05  tff(c_16634, plain, (![C_1258]: (r2_hidden(C_1258, k1_relat_1('#skF_10')) | ~r2_hidden(C_1258, k2_relat_1('#skF_9')))), inference(demodulation, [status(thm), theory('equality')], [c_112, c_78, c_103, c_13715, c_16610])).
% 11.82/5.05  tff(c_16714, plain, (![D_49]: (r2_hidden(k1_funct_1('#skF_9', D_49), k1_relat_1('#skF_10')) | ~r2_hidden(D_49, k1_relat_1('#skF_9')) | ~v1_funct_1('#skF_9') | ~v1_relat_1('#skF_9'))), inference(resolution, [status(thm)], [c_14, c_16634])).
% 11.82/5.05  tff(c_16771, plain, (![D_1260]: (r2_hidden(k1_funct_1('#skF_9', D_1260), k1_relat_1('#skF_10')) | ~r2_hidden(D_1260, '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_112, c_78, c_13715, c_16714])).
% 11.82/5.05  tff(c_58, plain, (![A_75, B_76, C_78]: (k7_partfun1(A_75, B_76, C_78)=k1_funct_1(B_76, C_78) | ~r2_hidden(C_78, k1_relat_1(B_76)) | ~v1_funct_1(B_76) | ~v5_relat_1(B_76, A_75) | ~v1_relat_1(B_76))), inference(cnfTransformation, [status(thm)], [f_139])).
% 11.82/5.05  tff(c_16775, plain, (![A_75, D_1260]: (k7_partfun1(A_75, '#skF_10', k1_funct_1('#skF_9', D_1260))=k1_funct_1('#skF_10', k1_funct_1('#skF_9', D_1260)) | ~v1_funct_1('#skF_10') | ~v5_relat_1('#skF_10', A_75) | ~v1_relat_1('#skF_10') | ~r2_hidden(D_1260, '#skF_7'))), inference(resolution, [status(thm)], [c_16771, c_58])).
% 11.82/5.05  tff(c_16895, plain, (![A_1271, D_1272]: (k7_partfun1(A_1271, '#skF_10', k1_funct_1('#skF_9', D_1272))=k1_funct_1('#skF_10', k1_funct_1('#skF_9', D_1272)) | ~v5_relat_1('#skF_10', A_1271) | ~r2_hidden(D_1272, '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_113, c_72, c_16775])).
% 11.82/5.05  tff(c_62, plain, (k7_partfun1('#skF_6', '#skF_10', k1_funct_1('#skF_9', '#skF_11'))!=k1_funct_1(k8_funct_2('#skF_7', '#skF_8', '#skF_6', '#skF_9', '#skF_10'), '#skF_11')), inference(cnfTransformation, [status(thm)], [f_174])).
% 11.82/5.05  tff(c_16901, plain, (k1_funct_1(k8_funct_2('#skF_7', '#skF_8', '#skF_6', '#skF_9', '#skF_10'), '#skF_11')!=k1_funct_1('#skF_10', k1_funct_1('#skF_9', '#skF_11')) | ~v5_relat_1('#skF_10', '#skF_6') | ~r2_hidden('#skF_11', '#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_16895, c_62])).
% 11.82/5.05  tff(c_16913, plain, (k1_funct_1(k8_funct_2('#skF_7', '#skF_8', '#skF_6', '#skF_9', '#skF_10'), '#skF_11')!=k1_funct_1('#skF_10', k1_funct_1('#skF_9', '#skF_11')) | ~r2_hidden('#skF_11', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_138, c_16901])).
% 11.82/5.05  tff(c_16917, plain, (~r2_hidden('#skF_11', '#skF_7')), inference(splitLeft, [status(thm)], [c_16913])).
% 11.82/5.05  tff(c_16933, plain, (v1_xboole_0('#skF_7') | ~m1_subset_1('#skF_11', '#skF_7')), inference(resolution, [status(thm)], [c_12, c_16917])).
% 11.82/5.05  tff(c_16936, plain, (v1_xboole_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_16933])).
% 11.82/5.05  tff(c_16938, plain, $false, inference(negUnitSimplification, [status(thm)], [c_13856, c_16936])).
% 11.82/5.05  tff(c_16940, plain, (r2_hidden('#skF_11', '#skF_7')), inference(splitRight, [status(thm)], [c_16913])).
% 11.82/5.05  tff(c_16270, plain, (![B_1208, C_1209, A_1210]: (k1_funct_1(k5_relat_1(B_1208, C_1209), A_1210)=k1_funct_1(C_1209, k1_funct_1(B_1208, A_1210)) | ~r2_hidden(A_1210, k1_relat_1(B_1208)) | ~v1_funct_1(C_1209) | ~v1_relat_1(C_1209) | ~v1_funct_1(B_1208) | ~v1_relat_1(B_1208))), inference(cnfTransformation, [status(thm)], [f_75])).
% 11.82/5.05  tff(c_16321, plain, (![C_1209, A_1210]: (k1_funct_1(k5_relat_1('#skF_9', C_1209), A_1210)=k1_funct_1(C_1209, k1_funct_1('#skF_9', A_1210)) | ~r2_hidden(A_1210, '#skF_7') | ~v1_funct_1(C_1209) | ~v1_relat_1(C_1209) | ~v1_funct_1('#skF_9') | ~v1_relat_1('#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_13715, c_16270])).
% 11.82/5.05  tff(c_16365, plain, (![C_1209, A_1210]: (k1_funct_1(k5_relat_1('#skF_9', C_1209), A_1210)=k1_funct_1(C_1209, k1_funct_1('#skF_9', A_1210)) | ~r2_hidden(A_1210, '#skF_7') | ~v1_funct_1(C_1209) | ~v1_relat_1(C_1209))), inference(demodulation, [status(thm), theory('equality')], [c_112, c_78, c_16321])).
% 11.82/5.05  tff(c_16884, plain, (![A_1266, E_1270, B_1269, F_1268, D_1265, C_1267]: (k1_partfun1(A_1266, B_1269, C_1267, D_1265, E_1270, F_1268)=k5_relat_1(E_1270, F_1268) | ~m1_subset_1(F_1268, k1_zfmisc_1(k2_zfmisc_1(C_1267, D_1265))) | ~v1_funct_1(F_1268) | ~m1_subset_1(E_1270, k1_zfmisc_1(k2_zfmisc_1(A_1266, B_1269))) | ~v1_funct_1(E_1270))), inference(cnfTransformation, [status(thm)], [f_149])).
% 11.82/5.05  tff(c_16888, plain, (![A_1266, B_1269, E_1270]: (k1_partfun1(A_1266, B_1269, '#skF_8', '#skF_6', E_1270, '#skF_10')=k5_relat_1(E_1270, '#skF_10') | ~v1_funct_1('#skF_10') | ~m1_subset_1(E_1270, k1_zfmisc_1(k2_zfmisc_1(A_1266, B_1269))) | ~v1_funct_1(E_1270))), inference(resolution, [status(thm)], [c_70, c_16884])).
% 11.82/5.05  tff(c_17040, plain, (![A_1293, B_1294, E_1295]: (k1_partfun1(A_1293, B_1294, '#skF_8', '#skF_6', E_1295, '#skF_10')=k5_relat_1(E_1295, '#skF_10') | ~m1_subset_1(E_1295, k1_zfmisc_1(k2_zfmisc_1(A_1293, B_1294))) | ~v1_funct_1(E_1295))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_16888])).
% 11.82/5.05  tff(c_17043, plain, (k1_partfun1('#skF_7', '#skF_8', '#skF_8', '#skF_6', '#skF_9', '#skF_10')=k5_relat_1('#skF_9', '#skF_10') | ~v1_funct_1('#skF_9')), inference(resolution, [status(thm)], [c_74, c_17040])).
% 11.82/5.05  tff(c_17049, plain, (k1_partfun1('#skF_7', '#skF_8', '#skF_8', '#skF_6', '#skF_9', '#skF_10')=k5_relat_1('#skF_9', '#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_17043])).
% 11.82/5.05  tff(c_16986, plain, (![D_1284, E_1280, A_1281, C_1283, B_1282]: (k1_partfun1(A_1281, B_1282, B_1282, C_1283, D_1284, E_1280)=k8_funct_2(A_1281, B_1282, C_1283, D_1284, E_1280) | k1_xboole_0=B_1282 | ~r1_tarski(k2_relset_1(A_1281, B_1282, D_1284), k1_relset_1(B_1282, C_1283, E_1280)) | ~m1_subset_1(E_1280, k1_zfmisc_1(k2_zfmisc_1(B_1282, C_1283))) | ~v1_funct_1(E_1280) | ~m1_subset_1(D_1284, k1_zfmisc_1(k2_zfmisc_1(A_1281, B_1282))) | ~v1_funct_2(D_1284, A_1281, B_1282) | ~v1_funct_1(D_1284))), inference(cnfTransformation, [status(thm)], [f_110])).
% 11.82/5.05  tff(c_16995, plain, (![C_1283, E_1280]: (k1_partfun1('#skF_7', '#skF_8', '#skF_8', C_1283, '#skF_9', E_1280)=k8_funct_2('#skF_7', '#skF_8', C_1283, '#skF_9', E_1280) | k1_xboole_0='#skF_8' | ~r1_tarski(k2_relat_1('#skF_9'), k1_relset_1('#skF_8', C_1283, E_1280)) | ~m1_subset_1(E_1280, k1_zfmisc_1(k2_zfmisc_1('#skF_8', C_1283))) | ~v1_funct_1(E_1280) | ~m1_subset_1('#skF_9', k1_zfmisc_1(k2_zfmisc_1('#skF_7', '#skF_8'))) | ~v1_funct_2('#skF_9', '#skF_7', '#skF_8') | ~v1_funct_1('#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_185, c_16986])).
% 11.82/5.05  tff(c_17005, plain, (![C_1283, E_1280]: (k1_partfun1('#skF_7', '#skF_8', '#skF_8', C_1283, '#skF_9', E_1280)=k8_funct_2('#skF_7', '#skF_8', C_1283, '#skF_9', E_1280) | k1_xboole_0='#skF_8' | ~r1_tarski(k2_relat_1('#skF_9'), k1_relset_1('#skF_8', C_1283, E_1280)) | ~m1_subset_1(E_1280, k1_zfmisc_1(k2_zfmisc_1('#skF_8', C_1283))) | ~v1_funct_1(E_1280))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_74, c_16995])).
% 11.82/5.05  tff(c_17137, plain, (k1_xboole_0='#skF_8'), inference(splitLeft, [status(thm)], [c_17005])).
% 11.82/5.05  tff(c_17146, plain, (v1_xboole_0('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_17137, c_8])).
% 11.82/5.05  tff(c_17149, plain, $false, inference(negUnitSimplification, [status(thm)], [c_80, c_17146])).
% 11.82/5.05  tff(c_17151, plain, (k1_xboole_0!='#skF_8'), inference(splitRight, [status(thm)], [c_17005])).
% 11.82/5.05  tff(c_16998, plain, (![A_1281, D_1284]: (k1_partfun1(A_1281, '#skF_8', '#skF_8', '#skF_6', D_1284, '#skF_10')=k8_funct_2(A_1281, '#skF_8', '#skF_6', D_1284, '#skF_10') | k1_xboole_0='#skF_8' | ~r1_tarski(k2_relset_1(A_1281, '#skF_8', D_1284), k1_relat_1('#skF_10')) | ~m1_subset_1('#skF_10', k1_zfmisc_1(k2_zfmisc_1('#skF_8', '#skF_6'))) | ~v1_funct_1('#skF_10') | ~m1_subset_1(D_1284, k1_zfmisc_1(k2_zfmisc_1(A_1281, '#skF_8'))) | ~v1_funct_2(D_1284, A_1281, '#skF_8') | ~v1_funct_1(D_1284))), inference(superposition, [status(thm), theory('equality')], [c_165, c_16986])).
% 11.82/5.05  tff(c_17007, plain, (![A_1281, D_1284]: (k1_partfun1(A_1281, '#skF_8', '#skF_8', '#skF_6', D_1284, '#skF_10')=k8_funct_2(A_1281, '#skF_8', '#skF_6', D_1284, '#skF_10') | k1_xboole_0='#skF_8' | ~r1_tarski(k2_relset_1(A_1281, '#skF_8', D_1284), k1_relat_1('#skF_10')) | ~m1_subset_1(D_1284, k1_zfmisc_1(k2_zfmisc_1(A_1281, '#skF_8'))) | ~v1_funct_2(D_1284, A_1281, '#skF_8') | ~v1_funct_1(D_1284))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_16998])).
% 11.82/5.05  tff(c_17243, plain, (![A_1308, D_1309]: (k1_partfun1(A_1308, '#skF_8', '#skF_8', '#skF_6', D_1309, '#skF_10')=k8_funct_2(A_1308, '#skF_8', '#skF_6', D_1309, '#skF_10') | ~r1_tarski(k2_relset_1(A_1308, '#skF_8', D_1309), k1_relat_1('#skF_10')) | ~m1_subset_1(D_1309, k1_zfmisc_1(k2_zfmisc_1(A_1308, '#skF_8'))) | ~v1_funct_2(D_1309, A_1308, '#skF_8') | ~v1_funct_1(D_1309))), inference(negUnitSimplification, [status(thm)], [c_17151, c_17007])).
% 11.82/5.05  tff(c_17246, plain, (k1_partfun1('#skF_7', '#skF_8', '#skF_8', '#skF_6', '#skF_9', '#skF_10')=k8_funct_2('#skF_7', '#skF_8', '#skF_6', '#skF_9', '#skF_10') | ~r1_tarski(k2_relat_1('#skF_9'), k1_relat_1('#skF_10')) | ~m1_subset_1('#skF_9', k1_zfmisc_1(k2_zfmisc_1('#skF_7', '#skF_8'))) | ~v1_funct_2('#skF_9', '#skF_7', '#skF_8') | ~v1_funct_1('#skF_9')), inference(superposition, [status(thm), theory('equality')], [c_185, c_17243])).
% 11.82/5.05  tff(c_17248, plain, (k8_funct_2('#skF_7', '#skF_8', '#skF_6', '#skF_9', '#skF_10')=k5_relat_1('#skF_9', '#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_74, c_187, c_17049, c_17246])).
% 11.82/5.05  tff(c_16939, plain, (k1_funct_1(k8_funct_2('#skF_7', '#skF_8', '#skF_6', '#skF_9', '#skF_10'), '#skF_11')!=k1_funct_1('#skF_10', k1_funct_1('#skF_9', '#skF_11'))), inference(splitRight, [status(thm)], [c_16913])).
% 11.82/5.05  tff(c_17249, plain, (k1_funct_1(k5_relat_1('#skF_9', '#skF_10'), '#skF_11')!=k1_funct_1('#skF_10', k1_funct_1('#skF_9', '#skF_11'))), inference(demodulation, [status(thm), theory('equality')], [c_17248, c_16939])).
% 11.82/5.05  tff(c_17257, plain, (~r2_hidden('#skF_11', '#skF_7') | ~v1_funct_1('#skF_10') | ~v1_relat_1('#skF_10')), inference(superposition, [status(thm), theory('equality')], [c_16365, c_17249])).
% 11.82/5.05  tff(c_17261, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_113, c_72, c_16940, c_17257])).
% 11.82/5.05  tff(c_17262, plain, (k1_xboole_0='#skF_8'), inference(splitRight, [status(thm)], [c_13712])).
% 11.82/5.05  tff(c_17270, plain, (v1_xboole_0('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_17262, c_8])).
% 11.82/5.05  tff(c_17273, plain, $false, inference(negUnitSimplification, [status(thm)], [c_80, c_17270])).
% 11.82/5.05  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.82/5.05  
% 11.82/5.05  Inference rules
% 11.82/5.05  ----------------------
% 11.82/5.05  #Ref     : 5
% 11.82/5.05  #Sup     : 3557
% 11.82/5.05  #Fact    : 0
% 11.82/5.05  #Define  : 0
% 11.82/5.05  #Split   : 48
% 11.82/5.05  #Chain   : 0
% 11.82/5.05  #Close   : 0
% 11.82/5.05  
% 11.82/5.05  Ordering : KBO
% 11.82/5.05  
% 11.82/5.05  Simplification rules
% 11.82/5.05  ----------------------
% 11.82/5.05  #Subsume      : 1018
% 11.82/5.05  #Demod        : 3302
% 11.82/5.05  #Tautology    : 737
% 11.82/5.05  #SimpNegUnit  : 261
% 11.82/5.05  #BackRed      : 239
% 11.82/5.05  
% 11.82/5.05  #Partial instantiations: 0
% 11.82/5.05  #Strategies tried      : 1
% 11.82/5.05  
% 11.82/5.05  Timing (in seconds)
% 11.82/5.05  ----------------------
% 12.06/5.05  Preprocessing        : 0.36
% 12.06/5.05  Parsing              : 0.18
% 12.06/5.05  CNF conversion       : 0.03
% 12.06/5.05  Main loop            : 3.87
% 12.06/5.05  Inferencing          : 1.25
% 12.06/5.05  Reduction            : 1.10
% 12.06/5.05  Demodulation         : 0.76
% 12.06/5.05  BG Simplification    : 0.12
% 12.06/5.05  Subsumption          : 1.13
% 12.06/5.06  Abstraction          : 0.19
% 12.06/5.06  MUC search           : 0.00
% 12.06/5.06  Cooper               : 0.00
% 12.06/5.06  Total                : 4.27
% 12.06/5.06  Index Insertion      : 0.00
% 12.06/5.06  Index Deletion       : 0.00
% 12.06/5.06  Index Matching       : 0.00
% 12.06/5.06  BG Taut test         : 0.00
%------------------------------------------------------------------------------
