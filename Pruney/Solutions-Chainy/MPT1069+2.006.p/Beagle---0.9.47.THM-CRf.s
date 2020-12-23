%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:17:46 EST 2020

% Result     : Theorem 3.33s
% Output     : CNFRefutation 3.33s
% Verified   : 
% Statistics : Number of formulae       :  119 ( 388 expanded)
%              Number of leaves         :   41 ( 153 expanded)
%              Depth                    :   17
%              Number of atoms          :  275 (1597 expanded)
%              Number of equality atoms :   58 ( 308 expanded)
%              Maximal formula depth    :   17 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k8_funct_2 > k7_partfun1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff(f_178,negated_conjecture,(
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

tff(f_67,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_122,axiom,(
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

tff(f_63,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_57,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_36,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_134,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_hidden(C,A)
       => ( B = k1_xboole_0
          | r2_hidden(k1_funct_1(D,C),B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_funct_2)).

tff(f_30,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_153,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r1_tarski(k2_relset_1(A,B,D),C)
       => ( ( B = k1_xboole_0
            & A != k1_xboole_0 )
          | ( v1_funct_1(D)
            & v1_funct_2(D,A,C)
            & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,C))) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_funct_2)).

tff(f_87,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & ~ v1_xboole_0(B) )
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => ( ( v1_funct_1(C)
              & v1_funct_2(C,A,B) )
           => ( v1_funct_1(C)
              & ~ v1_xboole_0(C)
              & v1_funct_2(C,A,B) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc6_funct_2)).

tff(f_43,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_xboole_0(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_subset_1)).

tff(f_98,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A)
        & v1_funct_1(B) )
     => ! [C] :
          ( r2_hidden(C,k1_relat_1(B))
         => k7_partfun1(A,B,C) = k1_funct_1(B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_partfun1)).

tff(c_52,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_178])).

tff(c_68,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_178])).

tff(c_56,plain,(
    m1_subset_1('#skF_6','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_178])).

tff(c_66,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_178])).

tff(c_64,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_178])).

tff(c_62,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_178])).

tff(c_58,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_178])).

tff(c_173,plain,(
    ! [A_86,B_87,C_88] :
      ( k1_relset_1(A_86,B_87,C_88) = k1_relat_1(C_88)
      | ~ m1_subset_1(C_88,k1_zfmisc_1(k2_zfmisc_1(A_86,B_87))) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_186,plain,(
    k1_relset_1('#skF_3','#skF_1','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_58,c_173])).

tff(c_54,plain,(
    r1_tarski(k2_relset_1('#skF_2','#skF_3','#skF_4'),k1_relset_1('#skF_3','#skF_1','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_178])).

tff(c_188,plain,(
    r1_tarski(k2_relset_1('#skF_2','#skF_3','#skF_4'),k1_relat_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_186,c_54])).

tff(c_60,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_178])).

tff(c_527,plain,(
    ! [E_140,D_138,F_141,A_143,B_142,C_139] :
      ( k1_funct_1(k8_funct_2(B_142,C_139,A_143,D_138,E_140),F_141) = k1_funct_1(E_140,k1_funct_1(D_138,F_141))
      | k1_xboole_0 = B_142
      | ~ r1_tarski(k2_relset_1(B_142,C_139,D_138),k1_relset_1(C_139,A_143,E_140))
      | ~ m1_subset_1(F_141,B_142)
      | ~ m1_subset_1(E_140,k1_zfmisc_1(k2_zfmisc_1(C_139,A_143)))
      | ~ v1_funct_1(E_140)
      | ~ m1_subset_1(D_138,k1_zfmisc_1(k2_zfmisc_1(B_142,C_139)))
      | ~ v1_funct_2(D_138,B_142,C_139)
      | ~ v1_funct_1(D_138)
      | v1_xboole_0(C_139) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_533,plain,(
    ! [B_142,D_138,F_141] :
      ( k1_funct_1(k8_funct_2(B_142,'#skF_3','#skF_1',D_138,'#skF_5'),F_141) = k1_funct_1('#skF_5',k1_funct_1(D_138,F_141))
      | k1_xboole_0 = B_142
      | ~ r1_tarski(k2_relset_1(B_142,'#skF_3',D_138),k1_relat_1('#skF_5'))
      | ~ m1_subset_1(F_141,B_142)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_1')))
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1(D_138,k1_zfmisc_1(k2_zfmisc_1(B_142,'#skF_3')))
      | ~ v1_funct_2(D_138,B_142,'#skF_3')
      | ~ v1_funct_1(D_138)
      | v1_xboole_0('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_186,c_527])).

tff(c_541,plain,(
    ! [B_142,D_138,F_141] :
      ( k1_funct_1(k8_funct_2(B_142,'#skF_3','#skF_1',D_138,'#skF_5'),F_141) = k1_funct_1('#skF_5',k1_funct_1(D_138,F_141))
      | k1_xboole_0 = B_142
      | ~ r1_tarski(k2_relset_1(B_142,'#skF_3',D_138),k1_relat_1('#skF_5'))
      | ~ m1_subset_1(F_141,B_142)
      | ~ m1_subset_1(D_138,k1_zfmisc_1(k2_zfmisc_1(B_142,'#skF_3')))
      | ~ v1_funct_2(D_138,B_142,'#skF_3')
      | ~ v1_funct_1(D_138)
      | v1_xboole_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_533])).

tff(c_571,plain,(
    ! [B_149,D_150,F_151] :
      ( k1_funct_1(k8_funct_2(B_149,'#skF_3','#skF_1',D_150,'#skF_5'),F_151) = k1_funct_1('#skF_5',k1_funct_1(D_150,F_151))
      | k1_xboole_0 = B_149
      | ~ r1_tarski(k2_relset_1(B_149,'#skF_3',D_150),k1_relat_1('#skF_5'))
      | ~ m1_subset_1(F_151,B_149)
      | ~ m1_subset_1(D_150,k1_zfmisc_1(k2_zfmisc_1(B_149,'#skF_3')))
      | ~ v1_funct_2(D_150,B_149,'#skF_3')
      | ~ v1_funct_1(D_150) ) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_541])).

tff(c_573,plain,(
    ! [F_151] :
      ( k1_funct_1(k8_funct_2('#skF_2','#skF_3','#skF_1','#skF_4','#skF_5'),F_151) = k1_funct_1('#skF_5',k1_funct_1('#skF_4',F_151))
      | k1_xboole_0 = '#skF_2'
      | ~ m1_subset_1(F_151,'#skF_2')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
      | ~ v1_funct_2('#skF_4','#skF_2','#skF_3')
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_188,c_571])).

tff(c_576,plain,(
    ! [F_151] :
      ( k1_funct_1(k8_funct_2('#skF_2','#skF_3','#skF_1','#skF_4','#skF_5'),F_151) = k1_funct_1('#skF_5',k1_funct_1('#skF_4',F_151))
      | k1_xboole_0 = '#skF_2'
      | ~ m1_subset_1(F_151,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_62,c_573])).

tff(c_578,plain,(
    ! [F_152] :
      ( k1_funct_1(k8_funct_2('#skF_2','#skF_3','#skF_1','#skF_4','#skF_5'),F_152) = k1_funct_1('#skF_5',k1_funct_1('#skF_4',F_152))
      | ~ m1_subset_1(F_152,'#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_576])).

tff(c_141,plain,(
    ! [C_77,B_78,A_79] :
      ( v5_relat_1(C_77,B_78)
      | ~ m1_subset_1(C_77,k1_zfmisc_1(k2_zfmisc_1(A_79,B_78))) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_154,plain,(
    v5_relat_1('#skF_5','#skF_1') ),
    inference(resolution,[status(thm)],[c_58,c_141])).

tff(c_104,plain,(
    ! [C_67,A_68,B_69] :
      ( v1_relat_1(C_67)
      | ~ m1_subset_1(C_67,k1_zfmisc_1(k2_zfmisc_1(A_68,B_69))) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_115,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_58,c_104])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_8,plain,(
    ! [A_2] : k2_zfmisc_1(A_2,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_14,plain,(
    ! [A_7,B_8] :
      ( r2_hidden(A_7,B_8)
      | v1_xboole_0(B_8)
      | ~ m1_subset_1(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_251,plain,(
    ! [D_107,C_108,B_109,A_110] :
      ( r2_hidden(k1_funct_1(D_107,C_108),B_109)
      | k1_xboole_0 = B_109
      | ~ r2_hidden(C_108,A_110)
      | ~ m1_subset_1(D_107,k1_zfmisc_1(k2_zfmisc_1(A_110,B_109)))
      | ~ v1_funct_2(D_107,A_110,B_109)
      | ~ v1_funct_1(D_107) ) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_389,plain,(
    ! [D_128,A_129,B_130,B_131] :
      ( r2_hidden(k1_funct_1(D_128,A_129),B_130)
      | k1_xboole_0 = B_130
      | ~ m1_subset_1(D_128,k1_zfmisc_1(k2_zfmisc_1(B_131,B_130)))
      | ~ v1_funct_2(D_128,B_131,B_130)
      | ~ v1_funct_1(D_128)
      | v1_xboole_0(B_131)
      | ~ m1_subset_1(A_129,B_131) ) ),
    inference(resolution,[status(thm)],[c_14,c_251])).

tff(c_395,plain,(
    ! [A_129] :
      ( r2_hidden(k1_funct_1('#skF_4',A_129),'#skF_3')
      | k1_xboole_0 = '#skF_3'
      | ~ v1_funct_2('#skF_4','#skF_2','#skF_3')
      | ~ v1_funct_1('#skF_4')
      | v1_xboole_0('#skF_2')
      | ~ m1_subset_1(A_129,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_62,c_389])).

tff(c_405,plain,(
    ! [A_129] :
      ( r2_hidden(k1_funct_1('#skF_4',A_129),'#skF_3')
      | k1_xboole_0 = '#skF_3'
      | v1_xboole_0('#skF_2')
      | ~ m1_subset_1(A_129,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_395])).

tff(c_407,plain,(
    v1_xboole_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_405])).

tff(c_4,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_413,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_407,c_4])).

tff(c_418,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_413])).

tff(c_420,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_405])).

tff(c_382,plain,(
    ! [B_124,D_125,A_126,C_127] :
      ( k1_xboole_0 = B_124
      | v1_funct_2(D_125,A_126,C_127)
      | ~ r1_tarski(k2_relset_1(A_126,B_124,D_125),C_127)
      | ~ m1_subset_1(D_125,k1_zfmisc_1(k2_zfmisc_1(A_126,B_124)))
      | ~ v1_funct_2(D_125,A_126,B_124)
      | ~ v1_funct_1(D_125) ) ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_384,plain,
    ( k1_xboole_0 = '#skF_3'
    | v1_funct_2('#skF_4','#skF_2',k1_relat_1('#skF_5'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_3')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_188,c_382])).

tff(c_387,plain,
    ( k1_xboole_0 = '#skF_3'
    | v1_funct_2('#skF_4','#skF_2',k1_relat_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_62,c_384])).

tff(c_388,plain,(
    v1_funct_2('#skF_4','#skF_2',k1_relat_1('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_387])).

tff(c_419,plain,(
    ! [A_129] :
      ( k1_xboole_0 = '#skF_3'
      | r2_hidden(k1_funct_1('#skF_4',A_129),'#skF_3')
      | ~ m1_subset_1(A_129,'#skF_2') ) ),
    inference(splitRight,[status(thm)],[c_405])).

tff(c_421,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_419])).

tff(c_439,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_421,c_2])).

tff(c_442,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_439])).

tff(c_444,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_419])).

tff(c_445,plain,(
    ! [B_132,D_133,A_134,C_135] :
      ( k1_xboole_0 = B_132
      | m1_subset_1(D_133,k1_zfmisc_1(k2_zfmisc_1(A_134,C_135)))
      | ~ r1_tarski(k2_relset_1(A_134,B_132,D_133),C_135)
      | ~ m1_subset_1(D_133,k1_zfmisc_1(k2_zfmisc_1(A_134,B_132)))
      | ~ v1_funct_2(D_133,A_134,B_132)
      | ~ v1_funct_1(D_133) ) ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_447,plain,
    ( k1_xboole_0 = '#skF_3'
    | m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2',k1_relat_1('#skF_5'))))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_3')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_188,c_445])).

tff(c_450,plain,
    ( k1_xboole_0 = '#skF_3'
    | m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2',k1_relat_1('#skF_5')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_62,c_447])).

tff(c_451,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2',k1_relat_1('#skF_5')))) ),
    inference(negUnitSimplification,[status(thm)],[c_444,c_450])).

tff(c_254,plain,(
    ! [D_107,A_7,B_109,B_8] :
      ( r2_hidden(k1_funct_1(D_107,A_7),B_109)
      | k1_xboole_0 = B_109
      | ~ m1_subset_1(D_107,k1_zfmisc_1(k2_zfmisc_1(B_8,B_109)))
      | ~ v1_funct_2(D_107,B_8,B_109)
      | ~ v1_funct_1(D_107)
      | v1_xboole_0(B_8)
      | ~ m1_subset_1(A_7,B_8) ) ),
    inference(resolution,[status(thm)],[c_14,c_251])).

tff(c_453,plain,(
    ! [A_7] :
      ( r2_hidden(k1_funct_1('#skF_4',A_7),k1_relat_1('#skF_5'))
      | k1_relat_1('#skF_5') = k1_xboole_0
      | ~ v1_funct_2('#skF_4','#skF_2',k1_relat_1('#skF_5'))
      | ~ v1_funct_1('#skF_4')
      | v1_xboole_0('#skF_2')
      | ~ m1_subset_1(A_7,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_451,c_254])).

tff(c_474,plain,(
    ! [A_7] :
      ( r2_hidden(k1_funct_1('#skF_4',A_7),k1_relat_1('#skF_5'))
      | k1_relat_1('#skF_5') = k1_xboole_0
      | v1_xboole_0('#skF_2')
      | ~ m1_subset_1(A_7,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_388,c_453])).

tff(c_475,plain,(
    ! [A_7] :
      ( r2_hidden(k1_funct_1('#skF_4',A_7),k1_relat_1('#skF_5'))
      | k1_relat_1('#skF_5') = k1_xboole_0
      | ~ m1_subset_1(A_7,'#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_420,c_474])).

tff(c_503,plain,(
    k1_relat_1('#skF_5') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_475])).

tff(c_200,plain,(
    ! [C_95,A_96,B_97] :
      ( ~ v1_xboole_0(C_95)
      | ~ v1_funct_2(C_95,A_96,B_97)
      | ~ v1_funct_1(C_95)
      | ~ m1_subset_1(C_95,k1_zfmisc_1(k2_zfmisc_1(A_96,B_97)))
      | v1_xboole_0(B_97)
      | v1_xboole_0(A_96) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_209,plain,
    ( ~ v1_xboole_0('#skF_4')
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_3')
    | ~ v1_funct_1('#skF_4')
    | v1_xboole_0('#skF_3')
    | v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_62,c_200])).

tff(c_220,plain,
    ( ~ v1_xboole_0('#skF_4')
    | v1_xboole_0('#skF_3')
    | v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_209])).

tff(c_221,plain,
    ( ~ v1_xboole_0('#skF_4')
    | v1_xboole_0('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_220])).

tff(c_228,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_221])).

tff(c_12,plain,(
    ! [B_6,A_4] :
      ( v1_xboole_0(B_6)
      | ~ m1_subset_1(B_6,k1_zfmisc_1(A_4))
      | ~ v1_xboole_0(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_468,plain,
    ( v1_xboole_0('#skF_4')
    | ~ v1_xboole_0(k2_zfmisc_1('#skF_2',k1_relat_1('#skF_5'))) ),
    inference(resolution,[status(thm)],[c_451,c_12])).

tff(c_487,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_2',k1_relat_1('#skF_5'))) ),
    inference(negUnitSimplification,[status(thm)],[c_228,c_468])).

tff(c_505,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_2',k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_503,c_487])).

tff(c_515,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_8,c_505])).

tff(c_518,plain,(
    ! [A_137] :
      ( r2_hidden(k1_funct_1('#skF_4',A_137),k1_relat_1('#skF_5'))
      | ~ m1_subset_1(A_137,'#skF_2') ) ),
    inference(splitRight,[status(thm)],[c_475])).

tff(c_32,plain,(
    ! [A_23,B_24,C_26] :
      ( k7_partfun1(A_23,B_24,C_26) = k1_funct_1(B_24,C_26)
      | ~ r2_hidden(C_26,k1_relat_1(B_24))
      | ~ v1_funct_1(B_24)
      | ~ v5_relat_1(B_24,A_23)
      | ~ v1_relat_1(B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_522,plain,(
    ! [A_23,A_137] :
      ( k7_partfun1(A_23,'#skF_5',k1_funct_1('#skF_4',A_137)) = k1_funct_1('#skF_5',k1_funct_1('#skF_4',A_137))
      | ~ v1_funct_1('#skF_5')
      | ~ v5_relat_1('#skF_5',A_23)
      | ~ v1_relat_1('#skF_5')
      | ~ m1_subset_1(A_137,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_518,c_32])).

tff(c_543,plain,(
    ! [A_144,A_145] :
      ( k7_partfun1(A_144,'#skF_5',k1_funct_1('#skF_4',A_145)) = k1_funct_1('#skF_5',k1_funct_1('#skF_4',A_145))
      | ~ v5_relat_1('#skF_5',A_144)
      | ~ m1_subset_1(A_145,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_115,c_60,c_522])).

tff(c_50,plain,(
    k7_partfun1('#skF_1','#skF_5',k1_funct_1('#skF_4','#skF_6')) != k1_funct_1(k8_funct_2('#skF_2','#skF_3','#skF_1','#skF_4','#skF_5'),'#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_178])).

tff(c_549,plain,
    ( k1_funct_1(k8_funct_2('#skF_2','#skF_3','#skF_1','#skF_4','#skF_5'),'#skF_6') != k1_funct_1('#skF_5',k1_funct_1('#skF_4','#skF_6'))
    | ~ v5_relat_1('#skF_5','#skF_1')
    | ~ m1_subset_1('#skF_6','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_543,c_50])).

tff(c_555,plain,(
    k1_funct_1(k8_funct_2('#skF_2','#skF_3','#skF_1','#skF_4','#skF_5'),'#skF_6') != k1_funct_1('#skF_5',k1_funct_1('#skF_4','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_154,c_549])).

tff(c_588,plain,(
    ~ m1_subset_1('#skF_6','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_578,c_555])).

tff(c_596,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_588])).

tff(c_597,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_387])).

tff(c_615,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_597,c_2])).

tff(c_618,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_615])).

tff(c_619,plain,(
    v1_xboole_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_221])).

tff(c_626,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_619,c_4])).

tff(c_631,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_626])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n013.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 16:34:09 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.33/1.49  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.33/1.51  
% 3.33/1.51  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.33/1.51  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k8_funct_2 > k7_partfun1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 3.33/1.51  
% 3.33/1.51  %Foreground sorts:
% 3.33/1.51  
% 3.33/1.51  
% 3.33/1.51  %Background operators:
% 3.33/1.51  
% 3.33/1.51  
% 3.33/1.51  %Foreground operators:
% 3.33/1.51  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 3.33/1.51  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.33/1.51  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.33/1.51  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.33/1.51  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.33/1.51  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.33/1.51  tff(k7_partfun1, type, k7_partfun1: ($i * $i * $i) > $i).
% 3.33/1.51  tff('#skF_5', type, '#skF_5': $i).
% 3.33/1.51  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.33/1.51  tff(k8_funct_2, type, k8_funct_2: ($i * $i * $i * $i * $i) > $i).
% 3.33/1.51  tff('#skF_6', type, '#skF_6': $i).
% 3.33/1.51  tff('#skF_2', type, '#skF_2': $i).
% 3.33/1.51  tff('#skF_3', type, '#skF_3': $i).
% 3.33/1.51  tff('#skF_1', type, '#skF_1': $i).
% 3.33/1.51  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.33/1.51  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.33/1.51  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.33/1.51  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.33/1.51  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.33/1.51  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.33/1.51  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.33/1.51  tff('#skF_4', type, '#skF_4': $i).
% 3.33/1.51  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.33/1.51  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.33/1.51  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.33/1.51  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.33/1.51  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.33/1.51  
% 3.33/1.53  tff(f_178, negated_conjecture, ~(![A, B, C]: (~v1_xboole_0(C) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, C)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (![E]: ((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(C, A)))) => (![F]: (m1_subset_1(F, B) => (r1_tarski(k2_relset_1(B, C, D), k1_relset_1(C, A, E)) => ((B = k1_xboole_0) | (k1_funct_1(k8_funct_2(B, C, A, D, E), F) = k7_partfun1(A, E, k1_funct_1(D, F))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t186_funct_2)).
% 3.33/1.53  tff(f_67, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.33/1.53  tff(f_122, axiom, (![A, B, C]: (~v1_xboole_0(C) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, C)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (![E]: ((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(C, A)))) => (![F]: (m1_subset_1(F, B) => (r1_tarski(k2_relset_1(B, C, D), k1_relset_1(C, A, E)) => ((B = k1_xboole_0) | (k1_funct_1(k8_funct_2(B, C, A, D, E), F) = k1_funct_1(E, k1_funct_1(D, F))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t185_funct_2)).
% 3.33/1.53  tff(f_63, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.33/1.53  tff(f_57, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.33/1.53  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 3.33/1.53  tff(f_36, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 3.33/1.53  tff(f_49, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 3.33/1.53  tff(f_134, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_hidden(C, A) => ((B = k1_xboole_0) | r2_hidden(k1_funct_1(D, C), B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_funct_2)).
% 3.33/1.53  tff(f_30, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 3.33/1.53  tff(f_153, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r1_tarski(k2_relset_1(A, B, D), C) => (((B = k1_xboole_0) & ~(A = k1_xboole_0)) | ((v1_funct_1(D) & v1_funct_2(D, A, C)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_funct_2)).
% 3.33/1.53  tff(f_87, axiom, (![A, B]: ((~v1_xboole_0(A) & ~v1_xboole_0(B)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) => ((v1_funct_1(C) & ~v1_xboole_0(C)) & v1_funct_2(C, A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc6_funct_2)).
% 3.33/1.53  tff(f_43, axiom, (![A]: (v1_xboole_0(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_subset_1)).
% 3.33/1.53  tff(f_98, axiom, (![A, B]: (((v1_relat_1(B) & v5_relat_1(B, A)) & v1_funct_1(B)) => (![C]: (r2_hidden(C, k1_relat_1(B)) => (k7_partfun1(A, B, C) = k1_funct_1(B, C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_partfun1)).
% 3.33/1.53  tff(c_52, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_178])).
% 3.33/1.53  tff(c_68, plain, (~v1_xboole_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_178])).
% 3.33/1.53  tff(c_56, plain, (m1_subset_1('#skF_6', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_178])).
% 3.33/1.53  tff(c_66, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_178])).
% 3.33/1.53  tff(c_64, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_178])).
% 3.33/1.53  tff(c_62, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_178])).
% 3.33/1.53  tff(c_58, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_178])).
% 3.33/1.53  tff(c_173, plain, (![A_86, B_87, C_88]: (k1_relset_1(A_86, B_87, C_88)=k1_relat_1(C_88) | ~m1_subset_1(C_88, k1_zfmisc_1(k2_zfmisc_1(A_86, B_87))))), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.33/1.53  tff(c_186, plain, (k1_relset_1('#skF_3', '#skF_1', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_58, c_173])).
% 3.33/1.53  tff(c_54, plain, (r1_tarski(k2_relset_1('#skF_2', '#skF_3', '#skF_4'), k1_relset_1('#skF_3', '#skF_1', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_178])).
% 3.33/1.53  tff(c_188, plain, (r1_tarski(k2_relset_1('#skF_2', '#skF_3', '#skF_4'), k1_relat_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_186, c_54])).
% 3.33/1.53  tff(c_60, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_178])).
% 3.33/1.53  tff(c_527, plain, (![E_140, D_138, F_141, A_143, B_142, C_139]: (k1_funct_1(k8_funct_2(B_142, C_139, A_143, D_138, E_140), F_141)=k1_funct_1(E_140, k1_funct_1(D_138, F_141)) | k1_xboole_0=B_142 | ~r1_tarski(k2_relset_1(B_142, C_139, D_138), k1_relset_1(C_139, A_143, E_140)) | ~m1_subset_1(F_141, B_142) | ~m1_subset_1(E_140, k1_zfmisc_1(k2_zfmisc_1(C_139, A_143))) | ~v1_funct_1(E_140) | ~m1_subset_1(D_138, k1_zfmisc_1(k2_zfmisc_1(B_142, C_139))) | ~v1_funct_2(D_138, B_142, C_139) | ~v1_funct_1(D_138) | v1_xboole_0(C_139))), inference(cnfTransformation, [status(thm)], [f_122])).
% 3.33/1.53  tff(c_533, plain, (![B_142, D_138, F_141]: (k1_funct_1(k8_funct_2(B_142, '#skF_3', '#skF_1', D_138, '#skF_5'), F_141)=k1_funct_1('#skF_5', k1_funct_1(D_138, F_141)) | k1_xboole_0=B_142 | ~r1_tarski(k2_relset_1(B_142, '#skF_3', D_138), k1_relat_1('#skF_5')) | ~m1_subset_1(F_141, B_142) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_1'))) | ~v1_funct_1('#skF_5') | ~m1_subset_1(D_138, k1_zfmisc_1(k2_zfmisc_1(B_142, '#skF_3'))) | ~v1_funct_2(D_138, B_142, '#skF_3') | ~v1_funct_1(D_138) | v1_xboole_0('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_186, c_527])).
% 3.33/1.53  tff(c_541, plain, (![B_142, D_138, F_141]: (k1_funct_1(k8_funct_2(B_142, '#skF_3', '#skF_1', D_138, '#skF_5'), F_141)=k1_funct_1('#skF_5', k1_funct_1(D_138, F_141)) | k1_xboole_0=B_142 | ~r1_tarski(k2_relset_1(B_142, '#skF_3', D_138), k1_relat_1('#skF_5')) | ~m1_subset_1(F_141, B_142) | ~m1_subset_1(D_138, k1_zfmisc_1(k2_zfmisc_1(B_142, '#skF_3'))) | ~v1_funct_2(D_138, B_142, '#skF_3') | ~v1_funct_1(D_138) | v1_xboole_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_533])).
% 3.33/1.53  tff(c_571, plain, (![B_149, D_150, F_151]: (k1_funct_1(k8_funct_2(B_149, '#skF_3', '#skF_1', D_150, '#skF_5'), F_151)=k1_funct_1('#skF_5', k1_funct_1(D_150, F_151)) | k1_xboole_0=B_149 | ~r1_tarski(k2_relset_1(B_149, '#skF_3', D_150), k1_relat_1('#skF_5')) | ~m1_subset_1(F_151, B_149) | ~m1_subset_1(D_150, k1_zfmisc_1(k2_zfmisc_1(B_149, '#skF_3'))) | ~v1_funct_2(D_150, B_149, '#skF_3') | ~v1_funct_1(D_150))), inference(negUnitSimplification, [status(thm)], [c_68, c_541])).
% 3.33/1.53  tff(c_573, plain, (![F_151]: (k1_funct_1(k8_funct_2('#skF_2', '#skF_3', '#skF_1', '#skF_4', '#skF_5'), F_151)=k1_funct_1('#skF_5', k1_funct_1('#skF_4', F_151)) | k1_xboole_0='#skF_2' | ~m1_subset_1(F_151, '#skF_2') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3') | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_188, c_571])).
% 3.33/1.53  tff(c_576, plain, (![F_151]: (k1_funct_1(k8_funct_2('#skF_2', '#skF_3', '#skF_1', '#skF_4', '#skF_5'), F_151)=k1_funct_1('#skF_5', k1_funct_1('#skF_4', F_151)) | k1_xboole_0='#skF_2' | ~m1_subset_1(F_151, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_62, c_573])).
% 3.33/1.53  tff(c_578, plain, (![F_152]: (k1_funct_1(k8_funct_2('#skF_2', '#skF_3', '#skF_1', '#skF_4', '#skF_5'), F_152)=k1_funct_1('#skF_5', k1_funct_1('#skF_4', F_152)) | ~m1_subset_1(F_152, '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_52, c_576])).
% 3.33/1.53  tff(c_141, plain, (![C_77, B_78, A_79]: (v5_relat_1(C_77, B_78) | ~m1_subset_1(C_77, k1_zfmisc_1(k2_zfmisc_1(A_79, B_78))))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.33/1.53  tff(c_154, plain, (v5_relat_1('#skF_5', '#skF_1')), inference(resolution, [status(thm)], [c_58, c_141])).
% 3.33/1.53  tff(c_104, plain, (![C_67, A_68, B_69]: (v1_relat_1(C_67) | ~m1_subset_1(C_67, k1_zfmisc_1(k2_zfmisc_1(A_68, B_69))))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.33/1.53  tff(c_115, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_58, c_104])).
% 3.33/1.53  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 3.33/1.53  tff(c_8, plain, (![A_2]: (k2_zfmisc_1(A_2, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.33/1.53  tff(c_14, plain, (![A_7, B_8]: (r2_hidden(A_7, B_8) | v1_xboole_0(B_8) | ~m1_subset_1(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.33/1.53  tff(c_251, plain, (![D_107, C_108, B_109, A_110]: (r2_hidden(k1_funct_1(D_107, C_108), B_109) | k1_xboole_0=B_109 | ~r2_hidden(C_108, A_110) | ~m1_subset_1(D_107, k1_zfmisc_1(k2_zfmisc_1(A_110, B_109))) | ~v1_funct_2(D_107, A_110, B_109) | ~v1_funct_1(D_107))), inference(cnfTransformation, [status(thm)], [f_134])).
% 3.33/1.53  tff(c_389, plain, (![D_128, A_129, B_130, B_131]: (r2_hidden(k1_funct_1(D_128, A_129), B_130) | k1_xboole_0=B_130 | ~m1_subset_1(D_128, k1_zfmisc_1(k2_zfmisc_1(B_131, B_130))) | ~v1_funct_2(D_128, B_131, B_130) | ~v1_funct_1(D_128) | v1_xboole_0(B_131) | ~m1_subset_1(A_129, B_131))), inference(resolution, [status(thm)], [c_14, c_251])).
% 3.33/1.53  tff(c_395, plain, (![A_129]: (r2_hidden(k1_funct_1('#skF_4', A_129), '#skF_3') | k1_xboole_0='#skF_3' | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3') | ~v1_funct_1('#skF_4') | v1_xboole_0('#skF_2') | ~m1_subset_1(A_129, '#skF_2'))), inference(resolution, [status(thm)], [c_62, c_389])).
% 3.33/1.53  tff(c_405, plain, (![A_129]: (r2_hidden(k1_funct_1('#skF_4', A_129), '#skF_3') | k1_xboole_0='#skF_3' | v1_xboole_0('#skF_2') | ~m1_subset_1(A_129, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_395])).
% 3.33/1.53  tff(c_407, plain, (v1_xboole_0('#skF_2')), inference(splitLeft, [status(thm)], [c_405])).
% 3.33/1.53  tff(c_4, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_30])).
% 3.33/1.53  tff(c_413, plain, (k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_407, c_4])).
% 3.33/1.53  tff(c_418, plain, $false, inference(negUnitSimplification, [status(thm)], [c_52, c_413])).
% 3.33/1.53  tff(c_420, plain, (~v1_xboole_0('#skF_2')), inference(splitRight, [status(thm)], [c_405])).
% 3.33/1.53  tff(c_382, plain, (![B_124, D_125, A_126, C_127]: (k1_xboole_0=B_124 | v1_funct_2(D_125, A_126, C_127) | ~r1_tarski(k2_relset_1(A_126, B_124, D_125), C_127) | ~m1_subset_1(D_125, k1_zfmisc_1(k2_zfmisc_1(A_126, B_124))) | ~v1_funct_2(D_125, A_126, B_124) | ~v1_funct_1(D_125))), inference(cnfTransformation, [status(thm)], [f_153])).
% 3.33/1.53  tff(c_384, plain, (k1_xboole_0='#skF_3' | v1_funct_2('#skF_4', '#skF_2', k1_relat_1('#skF_5')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_188, c_382])).
% 3.33/1.53  tff(c_387, plain, (k1_xboole_0='#skF_3' | v1_funct_2('#skF_4', '#skF_2', k1_relat_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_62, c_384])).
% 3.33/1.53  tff(c_388, plain, (v1_funct_2('#skF_4', '#skF_2', k1_relat_1('#skF_5'))), inference(splitLeft, [status(thm)], [c_387])).
% 3.33/1.53  tff(c_419, plain, (![A_129]: (k1_xboole_0='#skF_3' | r2_hidden(k1_funct_1('#skF_4', A_129), '#skF_3') | ~m1_subset_1(A_129, '#skF_2'))), inference(splitRight, [status(thm)], [c_405])).
% 3.33/1.53  tff(c_421, plain, (k1_xboole_0='#skF_3'), inference(splitLeft, [status(thm)], [c_419])).
% 3.33/1.53  tff(c_439, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_421, c_2])).
% 3.33/1.53  tff(c_442, plain, $false, inference(negUnitSimplification, [status(thm)], [c_68, c_439])).
% 3.33/1.53  tff(c_444, plain, (k1_xboole_0!='#skF_3'), inference(splitRight, [status(thm)], [c_419])).
% 3.33/1.53  tff(c_445, plain, (![B_132, D_133, A_134, C_135]: (k1_xboole_0=B_132 | m1_subset_1(D_133, k1_zfmisc_1(k2_zfmisc_1(A_134, C_135))) | ~r1_tarski(k2_relset_1(A_134, B_132, D_133), C_135) | ~m1_subset_1(D_133, k1_zfmisc_1(k2_zfmisc_1(A_134, B_132))) | ~v1_funct_2(D_133, A_134, B_132) | ~v1_funct_1(D_133))), inference(cnfTransformation, [status(thm)], [f_153])).
% 3.33/1.53  tff(c_447, plain, (k1_xboole_0='#skF_3' | m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', k1_relat_1('#skF_5')))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_188, c_445])).
% 3.33/1.53  tff(c_450, plain, (k1_xboole_0='#skF_3' | m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', k1_relat_1('#skF_5'))))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_62, c_447])).
% 3.33/1.53  tff(c_451, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', k1_relat_1('#skF_5'))))), inference(negUnitSimplification, [status(thm)], [c_444, c_450])).
% 3.33/1.53  tff(c_254, plain, (![D_107, A_7, B_109, B_8]: (r2_hidden(k1_funct_1(D_107, A_7), B_109) | k1_xboole_0=B_109 | ~m1_subset_1(D_107, k1_zfmisc_1(k2_zfmisc_1(B_8, B_109))) | ~v1_funct_2(D_107, B_8, B_109) | ~v1_funct_1(D_107) | v1_xboole_0(B_8) | ~m1_subset_1(A_7, B_8))), inference(resolution, [status(thm)], [c_14, c_251])).
% 3.33/1.53  tff(c_453, plain, (![A_7]: (r2_hidden(k1_funct_1('#skF_4', A_7), k1_relat_1('#skF_5')) | k1_relat_1('#skF_5')=k1_xboole_0 | ~v1_funct_2('#skF_4', '#skF_2', k1_relat_1('#skF_5')) | ~v1_funct_1('#skF_4') | v1_xboole_0('#skF_2') | ~m1_subset_1(A_7, '#skF_2'))), inference(resolution, [status(thm)], [c_451, c_254])).
% 3.33/1.53  tff(c_474, plain, (![A_7]: (r2_hidden(k1_funct_1('#skF_4', A_7), k1_relat_1('#skF_5')) | k1_relat_1('#skF_5')=k1_xboole_0 | v1_xboole_0('#skF_2') | ~m1_subset_1(A_7, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_388, c_453])).
% 3.33/1.53  tff(c_475, plain, (![A_7]: (r2_hidden(k1_funct_1('#skF_4', A_7), k1_relat_1('#skF_5')) | k1_relat_1('#skF_5')=k1_xboole_0 | ~m1_subset_1(A_7, '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_420, c_474])).
% 3.33/1.53  tff(c_503, plain, (k1_relat_1('#skF_5')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_475])).
% 3.33/1.53  tff(c_200, plain, (![C_95, A_96, B_97]: (~v1_xboole_0(C_95) | ~v1_funct_2(C_95, A_96, B_97) | ~v1_funct_1(C_95) | ~m1_subset_1(C_95, k1_zfmisc_1(k2_zfmisc_1(A_96, B_97))) | v1_xboole_0(B_97) | v1_xboole_0(A_96))), inference(cnfTransformation, [status(thm)], [f_87])).
% 3.33/1.53  tff(c_209, plain, (~v1_xboole_0('#skF_4') | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3') | ~v1_funct_1('#skF_4') | v1_xboole_0('#skF_3') | v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_62, c_200])).
% 3.33/1.53  tff(c_220, plain, (~v1_xboole_0('#skF_4') | v1_xboole_0('#skF_3') | v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_209])).
% 3.33/1.53  tff(c_221, plain, (~v1_xboole_0('#skF_4') | v1_xboole_0('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_68, c_220])).
% 3.33/1.53  tff(c_228, plain, (~v1_xboole_0('#skF_4')), inference(splitLeft, [status(thm)], [c_221])).
% 3.33/1.53  tff(c_12, plain, (![B_6, A_4]: (v1_xboole_0(B_6) | ~m1_subset_1(B_6, k1_zfmisc_1(A_4)) | ~v1_xboole_0(A_4))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.33/1.53  tff(c_468, plain, (v1_xboole_0('#skF_4') | ~v1_xboole_0(k2_zfmisc_1('#skF_2', k1_relat_1('#skF_5')))), inference(resolution, [status(thm)], [c_451, c_12])).
% 3.33/1.53  tff(c_487, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_2', k1_relat_1('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_228, c_468])).
% 3.33/1.53  tff(c_505, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_2', k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_503, c_487])).
% 3.33/1.53  tff(c_515, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2, c_8, c_505])).
% 3.33/1.53  tff(c_518, plain, (![A_137]: (r2_hidden(k1_funct_1('#skF_4', A_137), k1_relat_1('#skF_5')) | ~m1_subset_1(A_137, '#skF_2'))), inference(splitRight, [status(thm)], [c_475])).
% 3.33/1.53  tff(c_32, plain, (![A_23, B_24, C_26]: (k7_partfun1(A_23, B_24, C_26)=k1_funct_1(B_24, C_26) | ~r2_hidden(C_26, k1_relat_1(B_24)) | ~v1_funct_1(B_24) | ~v5_relat_1(B_24, A_23) | ~v1_relat_1(B_24))), inference(cnfTransformation, [status(thm)], [f_98])).
% 3.33/1.53  tff(c_522, plain, (![A_23, A_137]: (k7_partfun1(A_23, '#skF_5', k1_funct_1('#skF_4', A_137))=k1_funct_1('#skF_5', k1_funct_1('#skF_4', A_137)) | ~v1_funct_1('#skF_5') | ~v5_relat_1('#skF_5', A_23) | ~v1_relat_1('#skF_5') | ~m1_subset_1(A_137, '#skF_2'))), inference(resolution, [status(thm)], [c_518, c_32])).
% 3.33/1.53  tff(c_543, plain, (![A_144, A_145]: (k7_partfun1(A_144, '#skF_5', k1_funct_1('#skF_4', A_145))=k1_funct_1('#skF_5', k1_funct_1('#skF_4', A_145)) | ~v5_relat_1('#skF_5', A_144) | ~m1_subset_1(A_145, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_115, c_60, c_522])).
% 3.33/1.53  tff(c_50, plain, (k7_partfun1('#skF_1', '#skF_5', k1_funct_1('#skF_4', '#skF_6'))!=k1_funct_1(k8_funct_2('#skF_2', '#skF_3', '#skF_1', '#skF_4', '#skF_5'), '#skF_6')), inference(cnfTransformation, [status(thm)], [f_178])).
% 3.33/1.53  tff(c_549, plain, (k1_funct_1(k8_funct_2('#skF_2', '#skF_3', '#skF_1', '#skF_4', '#skF_5'), '#skF_6')!=k1_funct_1('#skF_5', k1_funct_1('#skF_4', '#skF_6')) | ~v5_relat_1('#skF_5', '#skF_1') | ~m1_subset_1('#skF_6', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_543, c_50])).
% 3.33/1.53  tff(c_555, plain, (k1_funct_1(k8_funct_2('#skF_2', '#skF_3', '#skF_1', '#skF_4', '#skF_5'), '#skF_6')!=k1_funct_1('#skF_5', k1_funct_1('#skF_4', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_154, c_549])).
% 3.33/1.53  tff(c_588, plain, (~m1_subset_1('#skF_6', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_578, c_555])).
% 3.33/1.53  tff(c_596, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_56, c_588])).
% 3.33/1.53  tff(c_597, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_387])).
% 3.33/1.53  tff(c_615, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_597, c_2])).
% 3.33/1.53  tff(c_618, plain, $false, inference(negUnitSimplification, [status(thm)], [c_68, c_615])).
% 3.33/1.53  tff(c_619, plain, (v1_xboole_0('#skF_2')), inference(splitRight, [status(thm)], [c_221])).
% 3.33/1.53  tff(c_626, plain, (k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_619, c_4])).
% 3.33/1.53  tff(c_631, plain, $false, inference(negUnitSimplification, [status(thm)], [c_52, c_626])).
% 3.33/1.53  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.33/1.53  
% 3.33/1.53  Inference rules
% 3.33/1.53  ----------------------
% 3.33/1.53  #Ref     : 0
% 3.33/1.53  #Sup     : 101
% 3.33/1.53  #Fact    : 0
% 3.33/1.53  #Define  : 0
% 3.33/1.53  #Split   : 12
% 3.33/1.53  #Chain   : 0
% 3.33/1.53  #Close   : 0
% 3.33/1.53  
% 3.33/1.53  Ordering : KBO
% 3.33/1.53  
% 3.33/1.53  Simplification rules
% 3.33/1.53  ----------------------
% 3.33/1.53  #Subsume      : 5
% 3.33/1.53  #Demod        : 177
% 3.33/1.53  #Tautology    : 46
% 3.33/1.53  #SimpNegUnit  : 17
% 3.33/1.53  #BackRed      : 78
% 3.33/1.53  
% 3.33/1.53  #Partial instantiations: 0
% 3.33/1.53  #Strategies tried      : 1
% 3.33/1.53  
% 3.33/1.53  Timing (in seconds)
% 3.33/1.53  ----------------------
% 3.59/1.53  Preprocessing        : 0.38
% 3.59/1.53  Parsing              : 0.20
% 3.59/1.53  CNF conversion       : 0.03
% 3.59/1.53  Main loop            : 0.37
% 3.59/1.53  Inferencing          : 0.12
% 3.59/1.54  Reduction            : 0.13
% 3.59/1.54  Demodulation         : 0.09
% 3.59/1.54  BG Simplification    : 0.03
% 3.59/1.54  Subsumption          : 0.08
% 3.59/1.54  Abstraction          : 0.02
% 3.59/1.54  MUC search           : 0.00
% 3.59/1.54  Cooper               : 0.00
% 3.59/1.54  Total                : 0.80
% 3.59/1.54  Index Insertion      : 0.00
% 3.59/1.54  Index Deletion       : 0.00
% 3.59/1.54  Index Matching       : 0.00
% 3.59/1.54  BG Taut test         : 0.00
%------------------------------------------------------------------------------
