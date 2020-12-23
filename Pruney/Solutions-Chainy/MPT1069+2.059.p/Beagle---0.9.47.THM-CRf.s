%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:17:53 EST 2020

% Result     : Theorem 2.75s
% Output     : CNFRefutation 3.15s
% Verified   : 
% Statistics : Number of formulae       :  109 ( 332 expanded)
%              Number of leaves         :   42 ( 133 expanded)
%              Depth                    :   14
%              Number of atoms          :  224 (1130 expanded)
%              Number of equality atoms :   52 ( 261 expanded)
%              Maximal formula depth    :   17 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k8_funct_2 > k7_partfun1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(f_154,negated_conjecture,(
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

tff(f_76,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_72,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_129,axiom,(
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

tff(f_36,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(f_51,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_43,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_94,axiom,(
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

tff(f_105,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A)
        & v1_funct_1(B) )
     => ! [C] :
          ( r2_hidden(C,k1_relat_1(B))
         => k7_partfun1(A,B,C) = k1_funct_1(B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_partfun1)).

tff(f_30,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_68,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_62,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A)
        & v1_funct_1(B) )
     => ! [C] :
          ( r2_hidden(C,k1_relat_1(B))
         => r2_hidden(k1_funct_1(B,C),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t172_funct_1)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(c_60,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_48,plain,(
    m1_subset_1('#skF_6','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_52,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_50,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_54,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_125,plain,(
    ! [A_80,B_81,C_82] :
      ( k2_relset_1(A_80,B_81,C_82) = k2_relat_1(C_82)
      | ~ m1_subset_1(C_82,k1_zfmisc_1(k2_zfmisc_1(A_80,B_81))) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_132,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_54,c_125])).

tff(c_107,plain,(
    ! [A_77,B_78,C_79] :
      ( k1_relset_1(A_77,B_78,C_79) = k1_relat_1(C_79)
      | ~ m1_subset_1(C_79,k1_zfmisc_1(k2_zfmisc_1(A_77,B_78))) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_115,plain,(
    k1_relset_1('#skF_3','#skF_1','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_50,c_107])).

tff(c_46,plain,(
    r1_tarski(k2_relset_1('#skF_2','#skF_3','#skF_4'),k1_relset_1('#skF_3','#skF_1','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_120,plain,(
    r1_tarski(k2_relset_1('#skF_2','#skF_3','#skF_4'),k1_relat_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_115,c_46])).

tff(c_134,plain,(
    r1_tarski(k2_relat_1('#skF_4'),k1_relat_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_132,c_120])).

tff(c_44,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_58,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_56,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_234,plain,(
    ! [A_108,C_109,D_110,E_107,F_111,B_106] :
      ( k1_funct_1(k8_funct_2(B_106,C_109,A_108,D_110,E_107),F_111) = k1_funct_1(E_107,k1_funct_1(D_110,F_111))
      | k1_xboole_0 = B_106
      | ~ r1_tarski(k2_relset_1(B_106,C_109,D_110),k1_relset_1(C_109,A_108,E_107))
      | ~ m1_subset_1(F_111,B_106)
      | ~ m1_subset_1(E_107,k1_zfmisc_1(k2_zfmisc_1(C_109,A_108)))
      | ~ v1_funct_1(E_107)
      | ~ m1_subset_1(D_110,k1_zfmisc_1(k2_zfmisc_1(B_106,C_109)))
      | ~ v1_funct_2(D_110,B_106,C_109)
      | ~ v1_funct_1(D_110)
      | v1_xboole_0(C_109) ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_240,plain,(
    ! [A_108,E_107,F_111] :
      ( k1_funct_1(k8_funct_2('#skF_2','#skF_3',A_108,'#skF_4',E_107),F_111) = k1_funct_1(E_107,k1_funct_1('#skF_4',F_111))
      | k1_xboole_0 = '#skF_2'
      | ~ r1_tarski(k2_relat_1('#skF_4'),k1_relset_1('#skF_3',A_108,E_107))
      | ~ m1_subset_1(F_111,'#skF_2')
      | ~ m1_subset_1(E_107,k1_zfmisc_1(k2_zfmisc_1('#skF_3',A_108)))
      | ~ v1_funct_1(E_107)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
      | ~ v1_funct_2('#skF_4','#skF_2','#skF_3')
      | ~ v1_funct_1('#skF_4')
      | v1_xboole_0('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_132,c_234])).

tff(c_249,plain,(
    ! [A_108,E_107,F_111] :
      ( k1_funct_1(k8_funct_2('#skF_2','#skF_3',A_108,'#skF_4',E_107),F_111) = k1_funct_1(E_107,k1_funct_1('#skF_4',F_111))
      | k1_xboole_0 = '#skF_2'
      | ~ r1_tarski(k2_relat_1('#skF_4'),k1_relset_1('#skF_3',A_108,E_107))
      | ~ m1_subset_1(F_111,'#skF_2')
      | ~ m1_subset_1(E_107,k1_zfmisc_1(k2_zfmisc_1('#skF_3',A_108)))
      | ~ v1_funct_1(E_107)
      | v1_xboole_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_54,c_240])).

tff(c_285,plain,(
    ! [A_116,E_117,F_118] :
      ( k1_funct_1(k8_funct_2('#skF_2','#skF_3',A_116,'#skF_4',E_117),F_118) = k1_funct_1(E_117,k1_funct_1('#skF_4',F_118))
      | ~ r1_tarski(k2_relat_1('#skF_4'),k1_relset_1('#skF_3',A_116,E_117))
      | ~ m1_subset_1(F_118,'#skF_2')
      | ~ m1_subset_1(E_117,k1_zfmisc_1(k2_zfmisc_1('#skF_3',A_116)))
      | ~ v1_funct_1(E_117) ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_44,c_249])).

tff(c_287,plain,(
    ! [F_118] :
      ( k1_funct_1(k8_funct_2('#skF_2','#skF_3','#skF_1','#skF_4','#skF_5'),F_118) = k1_funct_1('#skF_5',k1_funct_1('#skF_4',F_118))
      | ~ r1_tarski(k2_relat_1('#skF_4'),k1_relat_1('#skF_5'))
      | ~ m1_subset_1(F_118,'#skF_2')
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_1')))
      | ~ v1_funct_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_115,c_285])).

tff(c_292,plain,(
    ! [F_118] :
      ( k1_funct_1(k8_funct_2('#skF_2','#skF_3','#skF_1','#skF_4','#skF_5'),F_118) = k1_funct_1('#skF_5',k1_funct_1('#skF_4',F_118))
      | ~ m1_subset_1(F_118,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_134,c_287])).

tff(c_6,plain,(
    ! [A_2,B_3] :
      ( r2_hidden(A_2,B_3)
      | v1_xboole_0(B_3)
      | ~ m1_subset_1(A_2,B_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_14,plain,(
    ! [A_9,B_10] : v1_relat_1(k2_zfmisc_1(A_9,B_10)) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_68,plain,(
    ! [B_62,A_63] :
      ( v1_relat_1(B_62)
      | ~ m1_subset_1(B_62,k1_zfmisc_1(A_63))
      | ~ v1_relat_1(A_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_71,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_54,c_68])).

tff(c_77,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_71])).

tff(c_114,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_54,c_107])).

tff(c_153,plain,(
    ! [B_92,A_93,C_94] :
      ( k1_xboole_0 = B_92
      | k1_relset_1(A_93,B_92,C_94) = A_93
      | ~ v1_funct_2(C_94,A_93,B_92)
      | ~ m1_subset_1(C_94,k1_zfmisc_1(k2_zfmisc_1(A_93,B_92))) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_156,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relset_1('#skF_2','#skF_3','#skF_4') = '#skF_2'
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_54,c_153])).

tff(c_162,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relat_1('#skF_4') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_114,c_156])).

tff(c_165,plain,(
    k1_relat_1('#skF_4') = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_162])).

tff(c_190,plain,(
    ! [A_98,B_99,C_100] :
      ( k7_partfun1(A_98,B_99,C_100) = k1_funct_1(B_99,C_100)
      | ~ r2_hidden(C_100,k1_relat_1(B_99))
      | ~ v1_funct_1(B_99)
      | ~ v5_relat_1(B_99,A_98)
      | ~ v1_relat_1(B_99) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_192,plain,(
    ! [A_98,C_100] :
      ( k7_partfun1(A_98,'#skF_4',C_100) = k1_funct_1('#skF_4',C_100)
      | ~ r2_hidden(C_100,'#skF_2')
      | ~ v1_funct_1('#skF_4')
      | ~ v5_relat_1('#skF_4',A_98)
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_165,c_190])).

tff(c_203,plain,(
    ! [A_101,C_102] :
      ( k7_partfun1(A_101,'#skF_4',C_102) = k1_funct_1('#skF_4',C_102)
      | ~ r2_hidden(C_102,'#skF_2')
      | ~ v5_relat_1('#skF_4',A_101) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_77,c_58,c_192])).

tff(c_211,plain,(
    ! [A_101,A_2] :
      ( k7_partfun1(A_101,'#skF_4',A_2) = k1_funct_1('#skF_4',A_2)
      | ~ v5_relat_1('#skF_4',A_101)
      | v1_xboole_0('#skF_2')
      | ~ m1_subset_1(A_2,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_6,c_203])).

tff(c_212,plain,(
    v1_xboole_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_211])).

tff(c_4,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_215,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_212,c_4])).

tff(c_219,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_215])).

tff(c_221,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_211])).

tff(c_92,plain,(
    ! [C_71,B_72,A_73] :
      ( v5_relat_1(C_71,B_72)
      | ~ m1_subset_1(C_71,k1_zfmisc_1(k2_zfmisc_1(A_73,B_72))) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_100,plain,(
    v5_relat_1('#skF_5','#skF_1') ),
    inference(resolution,[status(thm)],[c_50,c_92])).

tff(c_74,plain,
    ( v1_relat_1('#skF_5')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_3','#skF_1')) ),
    inference(resolution,[status(thm)],[c_50,c_68])).

tff(c_80,plain,(
    v1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_74])).

tff(c_10,plain,(
    ! [B_8,A_7] :
      ( v5_relat_1(B_8,A_7)
      | ~ r1_tarski(k2_relat_1(B_8),A_7)
      | ~ v1_relat_1(B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_141,plain,
    ( v5_relat_1('#skF_4',k1_relat_1('#skF_5'))
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_134,c_10])).

tff(c_144,plain,(
    v5_relat_1('#skF_4',k1_relat_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_77,c_141])).

tff(c_16,plain,(
    ! [B_12,C_14,A_11] :
      ( r2_hidden(k1_funct_1(B_12,C_14),A_11)
      | ~ r2_hidden(C_14,k1_relat_1(B_12))
      | ~ v1_funct_1(B_12)
      | ~ v5_relat_1(B_12,A_11)
      | ~ v1_relat_1(B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_457,plain,(
    ! [A_137,B_138,B_139,C_140] :
      ( k7_partfun1(A_137,B_138,k1_funct_1(B_139,C_140)) = k1_funct_1(B_138,k1_funct_1(B_139,C_140))
      | ~ v1_funct_1(B_138)
      | ~ v5_relat_1(B_138,A_137)
      | ~ v1_relat_1(B_138)
      | ~ r2_hidden(C_140,k1_relat_1(B_139))
      | ~ v1_funct_1(B_139)
      | ~ v5_relat_1(B_139,k1_relat_1(B_138))
      | ~ v1_relat_1(B_139) ) ),
    inference(resolution,[status(thm)],[c_16,c_190])).

tff(c_459,plain,(
    ! [A_137,B_138,C_140] :
      ( k7_partfun1(A_137,B_138,k1_funct_1('#skF_4',C_140)) = k1_funct_1(B_138,k1_funct_1('#skF_4',C_140))
      | ~ v1_funct_1(B_138)
      | ~ v5_relat_1(B_138,A_137)
      | ~ v1_relat_1(B_138)
      | ~ r2_hidden(C_140,'#skF_2')
      | ~ v1_funct_1('#skF_4')
      | ~ v5_relat_1('#skF_4',k1_relat_1(B_138))
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_165,c_457])).

tff(c_482,plain,(
    ! [A_142,B_143,C_144] :
      ( k7_partfun1(A_142,B_143,k1_funct_1('#skF_4',C_144)) = k1_funct_1(B_143,k1_funct_1('#skF_4',C_144))
      | ~ v1_funct_1(B_143)
      | ~ v5_relat_1(B_143,A_142)
      | ~ v1_relat_1(B_143)
      | ~ r2_hidden(C_144,'#skF_2')
      | ~ v5_relat_1('#skF_4',k1_relat_1(B_143)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_77,c_58,c_459])).

tff(c_486,plain,(
    ! [A_142,C_144] :
      ( k7_partfun1(A_142,'#skF_5',k1_funct_1('#skF_4',C_144)) = k1_funct_1('#skF_5',k1_funct_1('#skF_4',C_144))
      | ~ v1_funct_1('#skF_5')
      | ~ v5_relat_1('#skF_5',A_142)
      | ~ v1_relat_1('#skF_5')
      | ~ r2_hidden(C_144,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_144,c_482])).

tff(c_492,plain,(
    ! [A_145,C_146] :
      ( k7_partfun1(A_145,'#skF_5',k1_funct_1('#skF_4',C_146)) = k1_funct_1('#skF_5',k1_funct_1('#skF_4',C_146))
      | ~ v5_relat_1('#skF_5',A_145)
      | ~ r2_hidden(C_146,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_52,c_486])).

tff(c_42,plain,(
    k7_partfun1('#skF_1','#skF_5',k1_funct_1('#skF_4','#skF_6')) != k1_funct_1(k8_funct_2('#skF_2','#skF_3','#skF_1','#skF_4','#skF_5'),'#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_498,plain,
    ( k1_funct_1(k8_funct_2('#skF_2','#skF_3','#skF_1','#skF_4','#skF_5'),'#skF_6') != k1_funct_1('#skF_5',k1_funct_1('#skF_4','#skF_6'))
    | ~ v5_relat_1('#skF_5','#skF_1')
    | ~ r2_hidden('#skF_6','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_492,c_42])).

tff(c_504,plain,
    ( k1_funct_1(k8_funct_2('#skF_2','#skF_3','#skF_1','#skF_4','#skF_5'),'#skF_6') != k1_funct_1('#skF_5',k1_funct_1('#skF_4','#skF_6'))
    | ~ r2_hidden('#skF_6','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_498])).

tff(c_512,plain,(
    ~ r2_hidden('#skF_6','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_504])).

tff(c_515,plain,
    ( v1_xboole_0('#skF_2')
    | ~ m1_subset_1('#skF_6','#skF_2') ),
    inference(resolution,[status(thm)],[c_6,c_512])).

tff(c_518,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_515])).

tff(c_520,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_221,c_518])).

tff(c_521,plain,(
    k1_funct_1(k8_funct_2('#skF_2','#skF_3','#skF_1','#skF_4','#skF_5'),'#skF_6') != k1_funct_1('#skF_5',k1_funct_1('#skF_4','#skF_6')) ),
    inference(splitRight,[status(thm)],[c_504])).

tff(c_565,plain,(
    ~ m1_subset_1('#skF_6','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_292,c_521])).

tff(c_569,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_565])).

tff(c_570,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_162])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_578,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_570,c_2])).

tff(c_581,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_578])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n003.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 17:48:27 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.75/1.36  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.75/1.37  
% 2.75/1.37  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.75/1.37  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k8_funct_2 > k7_partfun1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.75/1.37  
% 2.75/1.37  %Foreground sorts:
% 2.75/1.37  
% 2.75/1.37  
% 2.75/1.37  %Background operators:
% 2.75/1.37  
% 2.75/1.37  
% 2.75/1.37  %Foreground operators:
% 2.75/1.37  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 2.75/1.37  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.75/1.37  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.75/1.37  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.75/1.37  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.75/1.37  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.75/1.37  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.75/1.37  tff(k7_partfun1, type, k7_partfun1: ($i * $i * $i) > $i).
% 2.75/1.37  tff('#skF_5', type, '#skF_5': $i).
% 2.75/1.37  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.75/1.37  tff(k8_funct_2, type, k8_funct_2: ($i * $i * $i * $i * $i) > $i).
% 2.75/1.37  tff('#skF_6', type, '#skF_6': $i).
% 2.75/1.37  tff('#skF_2', type, '#skF_2': $i).
% 2.75/1.37  tff('#skF_3', type, '#skF_3': $i).
% 2.75/1.37  tff('#skF_1', type, '#skF_1': $i).
% 2.75/1.37  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.75/1.37  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.75/1.37  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.75/1.37  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.75/1.37  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.75/1.37  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.75/1.37  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.75/1.37  tff('#skF_4', type, '#skF_4': $i).
% 2.75/1.37  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.75/1.37  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.75/1.37  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.75/1.37  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.75/1.37  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.75/1.37  
% 3.15/1.39  tff(f_154, negated_conjecture, ~(![A, B, C]: (~v1_xboole_0(C) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, C)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (![E]: ((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(C, A)))) => (![F]: (m1_subset_1(F, B) => (r1_tarski(k2_relset_1(B, C, D), k1_relset_1(C, A, E)) => ((B = k1_xboole_0) | (k1_funct_1(k8_funct_2(B, C, A, D, E), F) = k7_partfun1(A, E, k1_funct_1(D, F))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t186_funct_2)).
% 3.15/1.39  tff(f_76, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 3.15/1.39  tff(f_72, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.15/1.39  tff(f_129, axiom, (![A, B, C]: (~v1_xboole_0(C) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, C)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (![E]: ((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(C, A)))) => (![F]: (m1_subset_1(F, B) => (r1_tarski(k2_relset_1(B, C, D), k1_relset_1(C, A, E)) => ((B = k1_xboole_0) | (k1_funct_1(k8_funct_2(B, C, A, D, E), F) = k1_funct_1(E, k1_funct_1(D, F))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t185_funct_2)).
% 3.15/1.39  tff(f_36, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 3.15/1.39  tff(f_51, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 3.15/1.39  tff(f_43, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 3.15/1.39  tff(f_94, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 3.15/1.39  tff(f_105, axiom, (![A, B]: (((v1_relat_1(B) & v5_relat_1(B, A)) & v1_funct_1(B)) => (![C]: (r2_hidden(C, k1_relat_1(B)) => (k7_partfun1(A, B, C) = k1_funct_1(B, C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_partfun1)).
% 3.15/1.39  tff(f_30, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 3.15/1.39  tff(f_68, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.15/1.39  tff(f_49, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 3.15/1.39  tff(f_62, axiom, (![A, B]: (((v1_relat_1(B) & v5_relat_1(B, A)) & v1_funct_1(B)) => (![C]: (r2_hidden(C, k1_relat_1(B)) => r2_hidden(k1_funct_1(B, C), A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t172_funct_1)).
% 3.15/1.39  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 3.15/1.39  tff(c_60, plain, (~v1_xboole_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_154])).
% 3.15/1.39  tff(c_48, plain, (m1_subset_1('#skF_6', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_154])).
% 3.15/1.39  tff(c_52, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_154])).
% 3.15/1.39  tff(c_50, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_154])).
% 3.15/1.39  tff(c_54, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_154])).
% 3.15/1.39  tff(c_125, plain, (![A_80, B_81, C_82]: (k2_relset_1(A_80, B_81, C_82)=k2_relat_1(C_82) | ~m1_subset_1(C_82, k1_zfmisc_1(k2_zfmisc_1(A_80, B_81))))), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.15/1.39  tff(c_132, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_54, c_125])).
% 3.15/1.39  tff(c_107, plain, (![A_77, B_78, C_79]: (k1_relset_1(A_77, B_78, C_79)=k1_relat_1(C_79) | ~m1_subset_1(C_79, k1_zfmisc_1(k2_zfmisc_1(A_77, B_78))))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.15/1.39  tff(c_115, plain, (k1_relset_1('#skF_3', '#skF_1', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_50, c_107])).
% 3.15/1.39  tff(c_46, plain, (r1_tarski(k2_relset_1('#skF_2', '#skF_3', '#skF_4'), k1_relset_1('#skF_3', '#skF_1', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_154])).
% 3.15/1.39  tff(c_120, plain, (r1_tarski(k2_relset_1('#skF_2', '#skF_3', '#skF_4'), k1_relat_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_115, c_46])).
% 3.15/1.39  tff(c_134, plain, (r1_tarski(k2_relat_1('#skF_4'), k1_relat_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_132, c_120])).
% 3.15/1.39  tff(c_44, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_154])).
% 3.15/1.39  tff(c_58, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_154])).
% 3.15/1.39  tff(c_56, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_154])).
% 3.15/1.39  tff(c_234, plain, (![A_108, C_109, D_110, E_107, F_111, B_106]: (k1_funct_1(k8_funct_2(B_106, C_109, A_108, D_110, E_107), F_111)=k1_funct_1(E_107, k1_funct_1(D_110, F_111)) | k1_xboole_0=B_106 | ~r1_tarski(k2_relset_1(B_106, C_109, D_110), k1_relset_1(C_109, A_108, E_107)) | ~m1_subset_1(F_111, B_106) | ~m1_subset_1(E_107, k1_zfmisc_1(k2_zfmisc_1(C_109, A_108))) | ~v1_funct_1(E_107) | ~m1_subset_1(D_110, k1_zfmisc_1(k2_zfmisc_1(B_106, C_109))) | ~v1_funct_2(D_110, B_106, C_109) | ~v1_funct_1(D_110) | v1_xboole_0(C_109))), inference(cnfTransformation, [status(thm)], [f_129])).
% 3.15/1.39  tff(c_240, plain, (![A_108, E_107, F_111]: (k1_funct_1(k8_funct_2('#skF_2', '#skF_3', A_108, '#skF_4', E_107), F_111)=k1_funct_1(E_107, k1_funct_1('#skF_4', F_111)) | k1_xboole_0='#skF_2' | ~r1_tarski(k2_relat_1('#skF_4'), k1_relset_1('#skF_3', A_108, E_107)) | ~m1_subset_1(F_111, '#skF_2') | ~m1_subset_1(E_107, k1_zfmisc_1(k2_zfmisc_1('#skF_3', A_108))) | ~v1_funct_1(E_107) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3') | ~v1_funct_1('#skF_4') | v1_xboole_0('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_132, c_234])).
% 3.15/1.39  tff(c_249, plain, (![A_108, E_107, F_111]: (k1_funct_1(k8_funct_2('#skF_2', '#skF_3', A_108, '#skF_4', E_107), F_111)=k1_funct_1(E_107, k1_funct_1('#skF_4', F_111)) | k1_xboole_0='#skF_2' | ~r1_tarski(k2_relat_1('#skF_4'), k1_relset_1('#skF_3', A_108, E_107)) | ~m1_subset_1(F_111, '#skF_2') | ~m1_subset_1(E_107, k1_zfmisc_1(k2_zfmisc_1('#skF_3', A_108))) | ~v1_funct_1(E_107) | v1_xboole_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_54, c_240])).
% 3.15/1.39  tff(c_285, plain, (![A_116, E_117, F_118]: (k1_funct_1(k8_funct_2('#skF_2', '#skF_3', A_116, '#skF_4', E_117), F_118)=k1_funct_1(E_117, k1_funct_1('#skF_4', F_118)) | ~r1_tarski(k2_relat_1('#skF_4'), k1_relset_1('#skF_3', A_116, E_117)) | ~m1_subset_1(F_118, '#skF_2') | ~m1_subset_1(E_117, k1_zfmisc_1(k2_zfmisc_1('#skF_3', A_116))) | ~v1_funct_1(E_117))), inference(negUnitSimplification, [status(thm)], [c_60, c_44, c_249])).
% 3.15/1.39  tff(c_287, plain, (![F_118]: (k1_funct_1(k8_funct_2('#skF_2', '#skF_3', '#skF_1', '#skF_4', '#skF_5'), F_118)=k1_funct_1('#skF_5', k1_funct_1('#skF_4', F_118)) | ~r1_tarski(k2_relat_1('#skF_4'), k1_relat_1('#skF_5')) | ~m1_subset_1(F_118, '#skF_2') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_1'))) | ~v1_funct_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_115, c_285])).
% 3.15/1.39  tff(c_292, plain, (![F_118]: (k1_funct_1(k8_funct_2('#skF_2', '#skF_3', '#skF_1', '#skF_4', '#skF_5'), F_118)=k1_funct_1('#skF_5', k1_funct_1('#skF_4', F_118)) | ~m1_subset_1(F_118, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_134, c_287])).
% 3.15/1.39  tff(c_6, plain, (![A_2, B_3]: (r2_hidden(A_2, B_3) | v1_xboole_0(B_3) | ~m1_subset_1(A_2, B_3))), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.15/1.39  tff(c_14, plain, (![A_9, B_10]: (v1_relat_1(k2_zfmisc_1(A_9, B_10)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.15/1.39  tff(c_68, plain, (![B_62, A_63]: (v1_relat_1(B_62) | ~m1_subset_1(B_62, k1_zfmisc_1(A_63)) | ~v1_relat_1(A_63))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.15/1.39  tff(c_71, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_54, c_68])).
% 3.15/1.39  tff(c_77, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_14, c_71])).
% 3.15/1.39  tff(c_114, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_54, c_107])).
% 3.15/1.39  tff(c_153, plain, (![B_92, A_93, C_94]: (k1_xboole_0=B_92 | k1_relset_1(A_93, B_92, C_94)=A_93 | ~v1_funct_2(C_94, A_93, B_92) | ~m1_subset_1(C_94, k1_zfmisc_1(k2_zfmisc_1(A_93, B_92))))), inference(cnfTransformation, [status(thm)], [f_94])).
% 3.15/1.39  tff(c_156, plain, (k1_xboole_0='#skF_3' | k1_relset_1('#skF_2', '#skF_3', '#skF_4')='#skF_2' | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_54, c_153])).
% 3.15/1.39  tff(c_162, plain, (k1_xboole_0='#skF_3' | k1_relat_1('#skF_4')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_56, c_114, c_156])).
% 3.15/1.39  tff(c_165, plain, (k1_relat_1('#skF_4')='#skF_2'), inference(splitLeft, [status(thm)], [c_162])).
% 3.15/1.39  tff(c_190, plain, (![A_98, B_99, C_100]: (k7_partfun1(A_98, B_99, C_100)=k1_funct_1(B_99, C_100) | ~r2_hidden(C_100, k1_relat_1(B_99)) | ~v1_funct_1(B_99) | ~v5_relat_1(B_99, A_98) | ~v1_relat_1(B_99))), inference(cnfTransformation, [status(thm)], [f_105])).
% 3.15/1.39  tff(c_192, plain, (![A_98, C_100]: (k7_partfun1(A_98, '#skF_4', C_100)=k1_funct_1('#skF_4', C_100) | ~r2_hidden(C_100, '#skF_2') | ~v1_funct_1('#skF_4') | ~v5_relat_1('#skF_4', A_98) | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_165, c_190])).
% 3.15/1.39  tff(c_203, plain, (![A_101, C_102]: (k7_partfun1(A_101, '#skF_4', C_102)=k1_funct_1('#skF_4', C_102) | ~r2_hidden(C_102, '#skF_2') | ~v5_relat_1('#skF_4', A_101))), inference(demodulation, [status(thm), theory('equality')], [c_77, c_58, c_192])).
% 3.15/1.39  tff(c_211, plain, (![A_101, A_2]: (k7_partfun1(A_101, '#skF_4', A_2)=k1_funct_1('#skF_4', A_2) | ~v5_relat_1('#skF_4', A_101) | v1_xboole_0('#skF_2') | ~m1_subset_1(A_2, '#skF_2'))), inference(resolution, [status(thm)], [c_6, c_203])).
% 3.15/1.39  tff(c_212, plain, (v1_xboole_0('#skF_2')), inference(splitLeft, [status(thm)], [c_211])).
% 3.15/1.39  tff(c_4, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_30])).
% 3.15/1.39  tff(c_215, plain, (k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_212, c_4])).
% 3.15/1.39  tff(c_219, plain, $false, inference(negUnitSimplification, [status(thm)], [c_44, c_215])).
% 3.15/1.39  tff(c_221, plain, (~v1_xboole_0('#skF_2')), inference(splitRight, [status(thm)], [c_211])).
% 3.15/1.39  tff(c_92, plain, (![C_71, B_72, A_73]: (v5_relat_1(C_71, B_72) | ~m1_subset_1(C_71, k1_zfmisc_1(k2_zfmisc_1(A_73, B_72))))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.15/1.39  tff(c_100, plain, (v5_relat_1('#skF_5', '#skF_1')), inference(resolution, [status(thm)], [c_50, c_92])).
% 3.15/1.39  tff(c_74, plain, (v1_relat_1('#skF_5') | ~v1_relat_1(k2_zfmisc_1('#skF_3', '#skF_1'))), inference(resolution, [status(thm)], [c_50, c_68])).
% 3.15/1.39  tff(c_80, plain, (v1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_14, c_74])).
% 3.15/1.39  tff(c_10, plain, (![B_8, A_7]: (v5_relat_1(B_8, A_7) | ~r1_tarski(k2_relat_1(B_8), A_7) | ~v1_relat_1(B_8))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.15/1.39  tff(c_141, plain, (v5_relat_1('#skF_4', k1_relat_1('#skF_5')) | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_134, c_10])).
% 3.15/1.39  tff(c_144, plain, (v5_relat_1('#skF_4', k1_relat_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_77, c_141])).
% 3.15/1.39  tff(c_16, plain, (![B_12, C_14, A_11]: (r2_hidden(k1_funct_1(B_12, C_14), A_11) | ~r2_hidden(C_14, k1_relat_1(B_12)) | ~v1_funct_1(B_12) | ~v5_relat_1(B_12, A_11) | ~v1_relat_1(B_12))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.15/1.39  tff(c_457, plain, (![A_137, B_138, B_139, C_140]: (k7_partfun1(A_137, B_138, k1_funct_1(B_139, C_140))=k1_funct_1(B_138, k1_funct_1(B_139, C_140)) | ~v1_funct_1(B_138) | ~v5_relat_1(B_138, A_137) | ~v1_relat_1(B_138) | ~r2_hidden(C_140, k1_relat_1(B_139)) | ~v1_funct_1(B_139) | ~v5_relat_1(B_139, k1_relat_1(B_138)) | ~v1_relat_1(B_139))), inference(resolution, [status(thm)], [c_16, c_190])).
% 3.15/1.39  tff(c_459, plain, (![A_137, B_138, C_140]: (k7_partfun1(A_137, B_138, k1_funct_1('#skF_4', C_140))=k1_funct_1(B_138, k1_funct_1('#skF_4', C_140)) | ~v1_funct_1(B_138) | ~v5_relat_1(B_138, A_137) | ~v1_relat_1(B_138) | ~r2_hidden(C_140, '#skF_2') | ~v1_funct_1('#skF_4') | ~v5_relat_1('#skF_4', k1_relat_1(B_138)) | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_165, c_457])).
% 3.15/1.39  tff(c_482, plain, (![A_142, B_143, C_144]: (k7_partfun1(A_142, B_143, k1_funct_1('#skF_4', C_144))=k1_funct_1(B_143, k1_funct_1('#skF_4', C_144)) | ~v1_funct_1(B_143) | ~v5_relat_1(B_143, A_142) | ~v1_relat_1(B_143) | ~r2_hidden(C_144, '#skF_2') | ~v5_relat_1('#skF_4', k1_relat_1(B_143)))), inference(demodulation, [status(thm), theory('equality')], [c_77, c_58, c_459])).
% 3.15/1.39  tff(c_486, plain, (![A_142, C_144]: (k7_partfun1(A_142, '#skF_5', k1_funct_1('#skF_4', C_144))=k1_funct_1('#skF_5', k1_funct_1('#skF_4', C_144)) | ~v1_funct_1('#skF_5') | ~v5_relat_1('#skF_5', A_142) | ~v1_relat_1('#skF_5') | ~r2_hidden(C_144, '#skF_2'))), inference(resolution, [status(thm)], [c_144, c_482])).
% 3.15/1.39  tff(c_492, plain, (![A_145, C_146]: (k7_partfun1(A_145, '#skF_5', k1_funct_1('#skF_4', C_146))=k1_funct_1('#skF_5', k1_funct_1('#skF_4', C_146)) | ~v5_relat_1('#skF_5', A_145) | ~r2_hidden(C_146, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_52, c_486])).
% 3.15/1.39  tff(c_42, plain, (k7_partfun1('#skF_1', '#skF_5', k1_funct_1('#skF_4', '#skF_6'))!=k1_funct_1(k8_funct_2('#skF_2', '#skF_3', '#skF_1', '#skF_4', '#skF_5'), '#skF_6')), inference(cnfTransformation, [status(thm)], [f_154])).
% 3.15/1.39  tff(c_498, plain, (k1_funct_1(k8_funct_2('#skF_2', '#skF_3', '#skF_1', '#skF_4', '#skF_5'), '#skF_6')!=k1_funct_1('#skF_5', k1_funct_1('#skF_4', '#skF_6')) | ~v5_relat_1('#skF_5', '#skF_1') | ~r2_hidden('#skF_6', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_492, c_42])).
% 3.15/1.39  tff(c_504, plain, (k1_funct_1(k8_funct_2('#skF_2', '#skF_3', '#skF_1', '#skF_4', '#skF_5'), '#skF_6')!=k1_funct_1('#skF_5', k1_funct_1('#skF_4', '#skF_6')) | ~r2_hidden('#skF_6', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_100, c_498])).
% 3.15/1.39  tff(c_512, plain, (~r2_hidden('#skF_6', '#skF_2')), inference(splitLeft, [status(thm)], [c_504])).
% 3.15/1.39  tff(c_515, plain, (v1_xboole_0('#skF_2') | ~m1_subset_1('#skF_6', '#skF_2')), inference(resolution, [status(thm)], [c_6, c_512])).
% 3.15/1.39  tff(c_518, plain, (v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_515])).
% 3.15/1.39  tff(c_520, plain, $false, inference(negUnitSimplification, [status(thm)], [c_221, c_518])).
% 3.15/1.39  tff(c_521, plain, (k1_funct_1(k8_funct_2('#skF_2', '#skF_3', '#skF_1', '#skF_4', '#skF_5'), '#skF_6')!=k1_funct_1('#skF_5', k1_funct_1('#skF_4', '#skF_6'))), inference(splitRight, [status(thm)], [c_504])).
% 3.15/1.39  tff(c_565, plain, (~m1_subset_1('#skF_6', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_292, c_521])).
% 3.15/1.39  tff(c_569, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_48, c_565])).
% 3.15/1.39  tff(c_570, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_162])).
% 3.15/1.39  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 3.15/1.39  tff(c_578, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_570, c_2])).
% 3.15/1.39  tff(c_581, plain, $false, inference(negUnitSimplification, [status(thm)], [c_60, c_578])).
% 3.15/1.39  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.15/1.39  
% 3.15/1.39  Inference rules
% 3.15/1.39  ----------------------
% 3.15/1.39  #Ref     : 0
% 3.15/1.39  #Sup     : 108
% 3.15/1.39  #Fact    : 0
% 3.15/1.39  #Define  : 0
% 3.15/1.39  #Split   : 7
% 3.15/1.39  #Chain   : 0
% 3.15/1.39  #Close   : 0
% 3.15/1.39  
% 3.15/1.39  Ordering : KBO
% 3.15/1.39  
% 3.15/1.39  Simplification rules
% 3.15/1.39  ----------------------
% 3.15/1.39  #Subsume      : 8
% 3.15/1.39  #Demod        : 121
% 3.15/1.39  #Tautology    : 43
% 3.15/1.39  #SimpNegUnit  : 15
% 3.15/1.39  #BackRed      : 17
% 3.15/1.39  
% 3.15/1.39  #Partial instantiations: 0
% 3.15/1.39  #Strategies tried      : 1
% 3.15/1.39  
% 3.15/1.39  Timing (in seconds)
% 3.15/1.39  ----------------------
% 3.21/1.40  Preprocessing        : 0.34
% 3.21/1.40  Parsing              : 0.18
% 3.21/1.40  CNF conversion       : 0.03
% 3.21/1.40  Main loop            : 0.33
% 3.21/1.40  Inferencing          : 0.12
% 3.21/1.40  Reduction            : 0.11
% 3.21/1.40  Demodulation         : 0.07
% 3.21/1.40  BG Simplification    : 0.02
% 3.21/1.40  Subsumption          : 0.06
% 3.21/1.40  Abstraction          : 0.02
% 3.21/1.40  MUC search           : 0.00
% 3.21/1.40  Cooper               : 0.00
% 3.21/1.40  Total                : 0.71
% 3.21/1.40  Index Insertion      : 0.00
% 3.21/1.40  Index Deletion       : 0.00
% 3.21/1.40  Index Matching       : 0.00
% 3.21/1.40  BG Taut test         : 0.00
%------------------------------------------------------------------------------
