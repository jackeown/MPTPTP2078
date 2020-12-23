%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:17:50 EST 2020

% Result     : Theorem 3.11s
% Output     : CNFRefutation 3.25s
% Verified   : 
% Statistics : Number of formulae       :  105 ( 308 expanded)
%              Number of leaves         :   41 ( 125 expanded)
%              Depth                    :   14
%              Number of atoms          :  216 (1082 expanded)
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

tff(f_149,negated_conjecture,(
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

tff(f_71,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_124,axiom,(
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

tff(f_36,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_57,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_89,axiom,(
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

tff(f_100,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A)
        & v1_funct_1(B) )
     => ! [C] :
          ( r2_hidden(C,k1_relat_1(B))
         => k7_partfun1(A,B,C) = k1_funct_1(B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_partfun1)).

tff(f_30,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_63,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_42,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A)
        & v1_funct_1(B) )
     => ! [C] :
          ( r2_hidden(C,k1_relat_1(B))
         => r2_hidden(k1_funct_1(B,C),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t172_funct_1)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(c_58,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_46,plain,(
    m1_subset_1('#skF_6','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_50,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_48,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_108,plain,(
    ! [A_76,B_77,C_78] :
      ( k1_relset_1(A_76,B_77,C_78) = k1_relat_1(C_78)
      | ~ m1_subset_1(C_78,k1_zfmisc_1(k2_zfmisc_1(A_76,B_77))) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_116,plain,(
    k1_relset_1('#skF_3','#skF_1','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_48,c_108])).

tff(c_52,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_99,plain,(
    ! [A_73,B_74,C_75] :
      ( k2_relset_1(A_73,B_74,C_75) = k2_relat_1(C_75)
      | ~ m1_subset_1(C_75,k1_zfmisc_1(k2_zfmisc_1(A_73,B_74))) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_106,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_52,c_99])).

tff(c_44,plain,(
    r1_tarski(k2_relset_1('#skF_2','#skF_3','#skF_4'),k1_relset_1('#skF_3','#skF_1','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_117,plain,(
    r1_tarski(k2_relat_1('#skF_4'),k1_relset_1('#skF_3','#skF_1','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_106,c_44])).

tff(c_134,plain,(
    r1_tarski(k2_relat_1('#skF_4'),k1_relat_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_116,c_117])).

tff(c_42,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_56,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_54,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_243,plain,(
    ! [C_110,A_108,D_109,B_107,E_111,F_106] :
      ( k1_funct_1(k8_funct_2(B_107,C_110,A_108,D_109,E_111),F_106) = k1_funct_1(E_111,k1_funct_1(D_109,F_106))
      | k1_xboole_0 = B_107
      | ~ r1_tarski(k2_relset_1(B_107,C_110,D_109),k1_relset_1(C_110,A_108,E_111))
      | ~ m1_subset_1(F_106,B_107)
      | ~ m1_subset_1(E_111,k1_zfmisc_1(k2_zfmisc_1(C_110,A_108)))
      | ~ v1_funct_1(E_111)
      | ~ m1_subset_1(D_109,k1_zfmisc_1(k2_zfmisc_1(B_107,C_110)))
      | ~ v1_funct_2(D_109,B_107,C_110)
      | ~ v1_funct_1(D_109)
      | v1_xboole_0(C_110) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_251,plain,(
    ! [A_108,E_111,F_106] :
      ( k1_funct_1(k8_funct_2('#skF_2','#skF_3',A_108,'#skF_4',E_111),F_106) = k1_funct_1(E_111,k1_funct_1('#skF_4',F_106))
      | k1_xboole_0 = '#skF_2'
      | ~ r1_tarski(k2_relat_1('#skF_4'),k1_relset_1('#skF_3',A_108,E_111))
      | ~ m1_subset_1(F_106,'#skF_2')
      | ~ m1_subset_1(E_111,k1_zfmisc_1(k2_zfmisc_1('#skF_3',A_108)))
      | ~ v1_funct_1(E_111)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
      | ~ v1_funct_2('#skF_4','#skF_2','#skF_3')
      | ~ v1_funct_1('#skF_4')
      | v1_xboole_0('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_106,c_243])).

tff(c_261,plain,(
    ! [A_108,E_111,F_106] :
      ( k1_funct_1(k8_funct_2('#skF_2','#skF_3',A_108,'#skF_4',E_111),F_106) = k1_funct_1(E_111,k1_funct_1('#skF_4',F_106))
      | k1_xboole_0 = '#skF_2'
      | ~ r1_tarski(k2_relat_1('#skF_4'),k1_relset_1('#skF_3',A_108,E_111))
      | ~ m1_subset_1(F_106,'#skF_2')
      | ~ m1_subset_1(E_111,k1_zfmisc_1(k2_zfmisc_1('#skF_3',A_108)))
      | ~ v1_funct_1(E_111)
      | v1_xboole_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_52,c_251])).

tff(c_500,plain,(
    ! [A_146,E_147,F_148] :
      ( k1_funct_1(k8_funct_2('#skF_2','#skF_3',A_146,'#skF_4',E_147),F_148) = k1_funct_1(E_147,k1_funct_1('#skF_4',F_148))
      | ~ r1_tarski(k2_relat_1('#skF_4'),k1_relset_1('#skF_3',A_146,E_147))
      | ~ m1_subset_1(F_148,'#skF_2')
      | ~ m1_subset_1(E_147,k1_zfmisc_1(k2_zfmisc_1('#skF_3',A_146)))
      | ~ v1_funct_1(E_147) ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_42,c_261])).

tff(c_502,plain,(
    ! [F_148] :
      ( k1_funct_1(k8_funct_2('#skF_2','#skF_3','#skF_1','#skF_4','#skF_5'),F_148) = k1_funct_1('#skF_5',k1_funct_1('#skF_4',F_148))
      | ~ r1_tarski(k2_relat_1('#skF_4'),k1_relat_1('#skF_5'))
      | ~ m1_subset_1(F_148,'#skF_2')
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_1')))
      | ~ v1_funct_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_116,c_500])).

tff(c_507,plain,(
    ! [F_148] :
      ( k1_funct_1(k8_funct_2('#skF_2','#skF_3','#skF_1','#skF_4','#skF_5'),F_148) = k1_funct_1('#skF_5',k1_funct_1('#skF_4',F_148))
      | ~ m1_subset_1(F_148,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_134,c_502])).

tff(c_6,plain,(
    ! [A_2,B_3] :
      ( r2_hidden(A_2,B_3)
      | v1_xboole_0(B_3)
      | ~ m1_subset_1(A_2,B_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_66,plain,(
    ! [C_60,A_61,B_62] :
      ( v1_relat_1(C_60)
      | ~ m1_subset_1(C_60,k1_zfmisc_1(k2_zfmisc_1(A_61,B_62))) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_73,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_52,c_66])).

tff(c_115,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_52,c_108])).

tff(c_158,plain,(
    ! [B_92,A_93,C_94] :
      ( k1_xboole_0 = B_92
      | k1_relset_1(A_93,B_92,C_94) = A_93
      | ~ v1_funct_2(C_94,A_93,B_92)
      | ~ m1_subset_1(C_94,k1_zfmisc_1(k2_zfmisc_1(A_93,B_92))) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_161,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relset_1('#skF_2','#skF_3','#skF_4') = '#skF_2'
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_52,c_158])).

tff(c_167,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relat_1('#skF_4') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_115,c_161])).

tff(c_171,plain,(
    k1_relat_1('#skF_4') = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_167])).

tff(c_182,plain,(
    ! [A_95,B_96,C_97] :
      ( k7_partfun1(A_95,B_96,C_97) = k1_funct_1(B_96,C_97)
      | ~ r2_hidden(C_97,k1_relat_1(B_96))
      | ~ v1_funct_1(B_96)
      | ~ v5_relat_1(B_96,A_95)
      | ~ v1_relat_1(B_96) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_184,plain,(
    ! [A_95,C_97] :
      ( k7_partfun1(A_95,'#skF_4',C_97) = k1_funct_1('#skF_4',C_97)
      | ~ r2_hidden(C_97,'#skF_2')
      | ~ v1_funct_1('#skF_4')
      | ~ v5_relat_1('#skF_4',A_95)
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_171,c_182])).

tff(c_195,plain,(
    ! [A_98,C_99] :
      ( k7_partfun1(A_98,'#skF_4',C_99) = k1_funct_1('#skF_4',C_99)
      | ~ r2_hidden(C_99,'#skF_2')
      | ~ v5_relat_1('#skF_4',A_98) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_73,c_56,c_184])).

tff(c_203,plain,(
    ! [A_98,A_2] :
      ( k7_partfun1(A_98,'#skF_4',A_2) = k1_funct_1('#skF_4',A_2)
      | ~ v5_relat_1('#skF_4',A_98)
      | v1_xboole_0('#skF_2')
      | ~ m1_subset_1(A_2,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_6,c_195])).

tff(c_204,plain,(
    v1_xboole_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_203])).

tff(c_4,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_220,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_204,c_4])).

tff(c_224,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_220])).

tff(c_226,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_203])).

tff(c_81,plain,(
    ! [C_67,B_68,A_69] :
      ( v5_relat_1(C_67,B_68)
      | ~ m1_subset_1(C_67,k1_zfmisc_1(k2_zfmisc_1(A_69,B_68))) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_89,plain,(
    v5_relat_1('#skF_5','#skF_1') ),
    inference(resolution,[status(thm)],[c_48,c_81])).

tff(c_74,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_48,c_66])).

tff(c_8,plain,(
    ! [B_5,A_4] :
      ( v5_relat_1(B_5,A_4)
      | ~ r1_tarski(k2_relat_1(B_5),A_4)
      | ~ v1_relat_1(B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_137,plain,
    ( v5_relat_1('#skF_4',k1_relat_1('#skF_5'))
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_134,c_8])).

tff(c_140,plain,(
    v5_relat_1('#skF_4',k1_relat_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_73,c_137])).

tff(c_12,plain,(
    ! [B_7,C_9,A_6] :
      ( r2_hidden(k1_funct_1(B_7,C_9),A_6)
      | ~ r2_hidden(C_9,k1_relat_1(B_7))
      | ~ v1_funct_1(B_7)
      | ~ v5_relat_1(B_7,A_6)
      | ~ v1_relat_1(B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_462,plain,(
    ! [A_136,B_137,B_138,C_139] :
      ( k7_partfun1(A_136,B_137,k1_funct_1(B_138,C_139)) = k1_funct_1(B_137,k1_funct_1(B_138,C_139))
      | ~ v1_funct_1(B_137)
      | ~ v5_relat_1(B_137,A_136)
      | ~ v1_relat_1(B_137)
      | ~ r2_hidden(C_139,k1_relat_1(B_138))
      | ~ v1_funct_1(B_138)
      | ~ v5_relat_1(B_138,k1_relat_1(B_137))
      | ~ v1_relat_1(B_138) ) ),
    inference(resolution,[status(thm)],[c_12,c_182])).

tff(c_464,plain,(
    ! [A_136,B_137,C_139] :
      ( k7_partfun1(A_136,B_137,k1_funct_1('#skF_4',C_139)) = k1_funct_1(B_137,k1_funct_1('#skF_4',C_139))
      | ~ v1_funct_1(B_137)
      | ~ v5_relat_1(B_137,A_136)
      | ~ v1_relat_1(B_137)
      | ~ r2_hidden(C_139,'#skF_2')
      | ~ v1_funct_1('#skF_4')
      | ~ v5_relat_1('#skF_4',k1_relat_1(B_137))
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_171,c_462])).

tff(c_476,plain,(
    ! [A_141,B_142,C_143] :
      ( k7_partfun1(A_141,B_142,k1_funct_1('#skF_4',C_143)) = k1_funct_1(B_142,k1_funct_1('#skF_4',C_143))
      | ~ v1_funct_1(B_142)
      | ~ v5_relat_1(B_142,A_141)
      | ~ v1_relat_1(B_142)
      | ~ r2_hidden(C_143,'#skF_2')
      | ~ v5_relat_1('#skF_4',k1_relat_1(B_142)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_73,c_56,c_464])).

tff(c_480,plain,(
    ! [A_141,C_143] :
      ( k7_partfun1(A_141,'#skF_5',k1_funct_1('#skF_4',C_143)) = k1_funct_1('#skF_5',k1_funct_1('#skF_4',C_143))
      | ~ v1_funct_1('#skF_5')
      | ~ v5_relat_1('#skF_5',A_141)
      | ~ v1_relat_1('#skF_5')
      | ~ r2_hidden(C_143,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_140,c_476])).

tff(c_486,plain,(
    ! [A_144,C_145] :
      ( k7_partfun1(A_144,'#skF_5',k1_funct_1('#skF_4',C_145)) = k1_funct_1('#skF_5',k1_funct_1('#skF_4',C_145))
      | ~ v5_relat_1('#skF_5',A_144)
      | ~ r2_hidden(C_145,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_50,c_480])).

tff(c_40,plain,(
    k7_partfun1('#skF_1','#skF_5',k1_funct_1('#skF_4','#skF_6')) != k1_funct_1(k8_funct_2('#skF_2','#skF_3','#skF_1','#skF_4','#skF_5'),'#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_492,plain,
    ( k1_funct_1(k8_funct_2('#skF_2','#skF_3','#skF_1','#skF_4','#skF_5'),'#skF_6') != k1_funct_1('#skF_5',k1_funct_1('#skF_4','#skF_6'))
    | ~ v5_relat_1('#skF_5','#skF_1')
    | ~ r2_hidden('#skF_6','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_486,c_40])).

tff(c_498,plain,
    ( k1_funct_1(k8_funct_2('#skF_2','#skF_3','#skF_1','#skF_4','#skF_5'),'#skF_6') != k1_funct_1('#skF_5',k1_funct_1('#skF_4','#skF_6'))
    | ~ r2_hidden('#skF_6','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_89,c_492])).

tff(c_523,plain,(
    ~ r2_hidden('#skF_6','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_498])).

tff(c_526,plain,
    ( v1_xboole_0('#skF_2')
    | ~ m1_subset_1('#skF_6','#skF_2') ),
    inference(resolution,[status(thm)],[c_6,c_523])).

tff(c_529,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_526])).

tff(c_531,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_226,c_529])).

tff(c_532,plain,(
    k1_funct_1(k8_funct_2('#skF_2','#skF_3','#skF_1','#skF_4','#skF_5'),'#skF_6') != k1_funct_1('#skF_5',k1_funct_1('#skF_4','#skF_6')) ),
    inference(splitRight,[status(thm)],[c_498])).

tff(c_576,plain,(
    ~ m1_subset_1('#skF_6','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_507,c_532])).

tff(c_580,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_576])).

tff(c_581,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_167])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_590,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_581,c_2])).

tff(c_593,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_590])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:53:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.11/1.46  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.11/1.47  
% 3.11/1.47  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.11/1.47  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k8_funct_2 > k7_partfun1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 3.11/1.47  
% 3.11/1.47  %Foreground sorts:
% 3.11/1.47  
% 3.11/1.47  
% 3.11/1.47  %Background operators:
% 3.11/1.47  
% 3.11/1.47  
% 3.11/1.47  %Foreground operators:
% 3.11/1.47  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 3.11/1.47  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.11/1.47  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.11/1.47  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.11/1.47  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.11/1.47  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.11/1.47  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.11/1.47  tff(k7_partfun1, type, k7_partfun1: ($i * $i * $i) > $i).
% 3.11/1.47  tff('#skF_5', type, '#skF_5': $i).
% 3.11/1.47  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.11/1.47  tff(k8_funct_2, type, k8_funct_2: ($i * $i * $i * $i * $i) > $i).
% 3.11/1.47  tff('#skF_6', type, '#skF_6': $i).
% 3.11/1.47  tff('#skF_2', type, '#skF_2': $i).
% 3.11/1.47  tff('#skF_3', type, '#skF_3': $i).
% 3.11/1.47  tff('#skF_1', type, '#skF_1': $i).
% 3.11/1.47  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.11/1.47  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.11/1.47  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.11/1.47  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.11/1.47  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.11/1.47  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.11/1.47  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.11/1.47  tff('#skF_4', type, '#skF_4': $i).
% 3.11/1.47  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.11/1.47  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.11/1.47  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.11/1.47  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.11/1.47  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.11/1.47  
% 3.25/1.49  tff(f_149, negated_conjecture, ~(![A, B, C]: (~v1_xboole_0(C) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, C)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (![E]: ((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(C, A)))) => (![F]: (m1_subset_1(F, B) => (r1_tarski(k2_relset_1(B, C, D), k1_relset_1(C, A, E)) => ((B = k1_xboole_0) | (k1_funct_1(k8_funct_2(B, C, A, D, E), F) = k7_partfun1(A, E, k1_funct_1(D, F))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t186_funct_2)).
% 3.25/1.49  tff(f_67, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.25/1.49  tff(f_71, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 3.25/1.49  tff(f_124, axiom, (![A, B, C]: (~v1_xboole_0(C) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, C)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (![E]: ((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(C, A)))) => (![F]: (m1_subset_1(F, B) => (r1_tarski(k2_relset_1(B, C, D), k1_relset_1(C, A, E)) => ((B = k1_xboole_0) | (k1_funct_1(k8_funct_2(B, C, A, D, E), F) = k1_funct_1(E, k1_funct_1(D, F))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t185_funct_2)).
% 3.25/1.49  tff(f_36, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 3.25/1.49  tff(f_57, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.25/1.49  tff(f_89, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 3.25/1.49  tff(f_100, axiom, (![A, B]: (((v1_relat_1(B) & v5_relat_1(B, A)) & v1_funct_1(B)) => (![C]: (r2_hidden(C, k1_relat_1(B)) => (k7_partfun1(A, B, C) = k1_funct_1(B, C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_partfun1)).
% 3.25/1.49  tff(f_30, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 3.25/1.49  tff(f_63, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.25/1.49  tff(f_42, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 3.25/1.49  tff(f_53, axiom, (![A, B]: (((v1_relat_1(B) & v5_relat_1(B, A)) & v1_funct_1(B)) => (![C]: (r2_hidden(C, k1_relat_1(B)) => r2_hidden(k1_funct_1(B, C), A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t172_funct_1)).
% 3.25/1.49  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 3.25/1.49  tff(c_58, plain, (~v1_xboole_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_149])).
% 3.25/1.49  tff(c_46, plain, (m1_subset_1('#skF_6', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_149])).
% 3.25/1.49  tff(c_50, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_149])).
% 3.25/1.49  tff(c_48, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_149])).
% 3.25/1.49  tff(c_108, plain, (![A_76, B_77, C_78]: (k1_relset_1(A_76, B_77, C_78)=k1_relat_1(C_78) | ~m1_subset_1(C_78, k1_zfmisc_1(k2_zfmisc_1(A_76, B_77))))), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.25/1.49  tff(c_116, plain, (k1_relset_1('#skF_3', '#skF_1', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_48, c_108])).
% 3.25/1.49  tff(c_52, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_149])).
% 3.25/1.49  tff(c_99, plain, (![A_73, B_74, C_75]: (k2_relset_1(A_73, B_74, C_75)=k2_relat_1(C_75) | ~m1_subset_1(C_75, k1_zfmisc_1(k2_zfmisc_1(A_73, B_74))))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.25/1.49  tff(c_106, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_52, c_99])).
% 3.25/1.49  tff(c_44, plain, (r1_tarski(k2_relset_1('#skF_2', '#skF_3', '#skF_4'), k1_relset_1('#skF_3', '#skF_1', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_149])).
% 3.25/1.49  tff(c_117, plain, (r1_tarski(k2_relat_1('#skF_4'), k1_relset_1('#skF_3', '#skF_1', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_106, c_44])).
% 3.25/1.49  tff(c_134, plain, (r1_tarski(k2_relat_1('#skF_4'), k1_relat_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_116, c_117])).
% 3.25/1.49  tff(c_42, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_149])).
% 3.25/1.49  tff(c_56, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_149])).
% 3.25/1.49  tff(c_54, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_149])).
% 3.25/1.49  tff(c_243, plain, (![C_110, A_108, D_109, B_107, E_111, F_106]: (k1_funct_1(k8_funct_2(B_107, C_110, A_108, D_109, E_111), F_106)=k1_funct_1(E_111, k1_funct_1(D_109, F_106)) | k1_xboole_0=B_107 | ~r1_tarski(k2_relset_1(B_107, C_110, D_109), k1_relset_1(C_110, A_108, E_111)) | ~m1_subset_1(F_106, B_107) | ~m1_subset_1(E_111, k1_zfmisc_1(k2_zfmisc_1(C_110, A_108))) | ~v1_funct_1(E_111) | ~m1_subset_1(D_109, k1_zfmisc_1(k2_zfmisc_1(B_107, C_110))) | ~v1_funct_2(D_109, B_107, C_110) | ~v1_funct_1(D_109) | v1_xboole_0(C_110))), inference(cnfTransformation, [status(thm)], [f_124])).
% 3.25/1.49  tff(c_251, plain, (![A_108, E_111, F_106]: (k1_funct_1(k8_funct_2('#skF_2', '#skF_3', A_108, '#skF_4', E_111), F_106)=k1_funct_1(E_111, k1_funct_1('#skF_4', F_106)) | k1_xboole_0='#skF_2' | ~r1_tarski(k2_relat_1('#skF_4'), k1_relset_1('#skF_3', A_108, E_111)) | ~m1_subset_1(F_106, '#skF_2') | ~m1_subset_1(E_111, k1_zfmisc_1(k2_zfmisc_1('#skF_3', A_108))) | ~v1_funct_1(E_111) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3') | ~v1_funct_1('#skF_4') | v1_xboole_0('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_106, c_243])).
% 3.25/1.49  tff(c_261, plain, (![A_108, E_111, F_106]: (k1_funct_1(k8_funct_2('#skF_2', '#skF_3', A_108, '#skF_4', E_111), F_106)=k1_funct_1(E_111, k1_funct_1('#skF_4', F_106)) | k1_xboole_0='#skF_2' | ~r1_tarski(k2_relat_1('#skF_4'), k1_relset_1('#skF_3', A_108, E_111)) | ~m1_subset_1(F_106, '#skF_2') | ~m1_subset_1(E_111, k1_zfmisc_1(k2_zfmisc_1('#skF_3', A_108))) | ~v1_funct_1(E_111) | v1_xboole_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_52, c_251])).
% 3.25/1.49  tff(c_500, plain, (![A_146, E_147, F_148]: (k1_funct_1(k8_funct_2('#skF_2', '#skF_3', A_146, '#skF_4', E_147), F_148)=k1_funct_1(E_147, k1_funct_1('#skF_4', F_148)) | ~r1_tarski(k2_relat_1('#skF_4'), k1_relset_1('#skF_3', A_146, E_147)) | ~m1_subset_1(F_148, '#skF_2') | ~m1_subset_1(E_147, k1_zfmisc_1(k2_zfmisc_1('#skF_3', A_146))) | ~v1_funct_1(E_147))), inference(negUnitSimplification, [status(thm)], [c_58, c_42, c_261])).
% 3.25/1.49  tff(c_502, plain, (![F_148]: (k1_funct_1(k8_funct_2('#skF_2', '#skF_3', '#skF_1', '#skF_4', '#skF_5'), F_148)=k1_funct_1('#skF_5', k1_funct_1('#skF_4', F_148)) | ~r1_tarski(k2_relat_1('#skF_4'), k1_relat_1('#skF_5')) | ~m1_subset_1(F_148, '#skF_2') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_1'))) | ~v1_funct_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_116, c_500])).
% 3.25/1.49  tff(c_507, plain, (![F_148]: (k1_funct_1(k8_funct_2('#skF_2', '#skF_3', '#skF_1', '#skF_4', '#skF_5'), F_148)=k1_funct_1('#skF_5', k1_funct_1('#skF_4', F_148)) | ~m1_subset_1(F_148, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_134, c_502])).
% 3.25/1.49  tff(c_6, plain, (![A_2, B_3]: (r2_hidden(A_2, B_3) | v1_xboole_0(B_3) | ~m1_subset_1(A_2, B_3))), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.25/1.49  tff(c_66, plain, (![C_60, A_61, B_62]: (v1_relat_1(C_60) | ~m1_subset_1(C_60, k1_zfmisc_1(k2_zfmisc_1(A_61, B_62))))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.25/1.49  tff(c_73, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_52, c_66])).
% 3.25/1.49  tff(c_115, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_52, c_108])).
% 3.25/1.49  tff(c_158, plain, (![B_92, A_93, C_94]: (k1_xboole_0=B_92 | k1_relset_1(A_93, B_92, C_94)=A_93 | ~v1_funct_2(C_94, A_93, B_92) | ~m1_subset_1(C_94, k1_zfmisc_1(k2_zfmisc_1(A_93, B_92))))), inference(cnfTransformation, [status(thm)], [f_89])).
% 3.25/1.49  tff(c_161, plain, (k1_xboole_0='#skF_3' | k1_relset_1('#skF_2', '#skF_3', '#skF_4')='#skF_2' | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_52, c_158])).
% 3.25/1.49  tff(c_167, plain, (k1_xboole_0='#skF_3' | k1_relat_1('#skF_4')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_54, c_115, c_161])).
% 3.25/1.49  tff(c_171, plain, (k1_relat_1('#skF_4')='#skF_2'), inference(splitLeft, [status(thm)], [c_167])).
% 3.25/1.49  tff(c_182, plain, (![A_95, B_96, C_97]: (k7_partfun1(A_95, B_96, C_97)=k1_funct_1(B_96, C_97) | ~r2_hidden(C_97, k1_relat_1(B_96)) | ~v1_funct_1(B_96) | ~v5_relat_1(B_96, A_95) | ~v1_relat_1(B_96))), inference(cnfTransformation, [status(thm)], [f_100])).
% 3.25/1.49  tff(c_184, plain, (![A_95, C_97]: (k7_partfun1(A_95, '#skF_4', C_97)=k1_funct_1('#skF_4', C_97) | ~r2_hidden(C_97, '#skF_2') | ~v1_funct_1('#skF_4') | ~v5_relat_1('#skF_4', A_95) | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_171, c_182])).
% 3.25/1.49  tff(c_195, plain, (![A_98, C_99]: (k7_partfun1(A_98, '#skF_4', C_99)=k1_funct_1('#skF_4', C_99) | ~r2_hidden(C_99, '#skF_2') | ~v5_relat_1('#skF_4', A_98))), inference(demodulation, [status(thm), theory('equality')], [c_73, c_56, c_184])).
% 3.25/1.49  tff(c_203, plain, (![A_98, A_2]: (k7_partfun1(A_98, '#skF_4', A_2)=k1_funct_1('#skF_4', A_2) | ~v5_relat_1('#skF_4', A_98) | v1_xboole_0('#skF_2') | ~m1_subset_1(A_2, '#skF_2'))), inference(resolution, [status(thm)], [c_6, c_195])).
% 3.25/1.49  tff(c_204, plain, (v1_xboole_0('#skF_2')), inference(splitLeft, [status(thm)], [c_203])).
% 3.25/1.49  tff(c_4, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_30])).
% 3.25/1.49  tff(c_220, plain, (k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_204, c_4])).
% 3.25/1.49  tff(c_224, plain, $false, inference(negUnitSimplification, [status(thm)], [c_42, c_220])).
% 3.25/1.49  tff(c_226, plain, (~v1_xboole_0('#skF_2')), inference(splitRight, [status(thm)], [c_203])).
% 3.25/1.49  tff(c_81, plain, (![C_67, B_68, A_69]: (v5_relat_1(C_67, B_68) | ~m1_subset_1(C_67, k1_zfmisc_1(k2_zfmisc_1(A_69, B_68))))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.25/1.49  tff(c_89, plain, (v5_relat_1('#skF_5', '#skF_1')), inference(resolution, [status(thm)], [c_48, c_81])).
% 3.25/1.49  tff(c_74, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_48, c_66])).
% 3.25/1.49  tff(c_8, plain, (![B_5, A_4]: (v5_relat_1(B_5, A_4) | ~r1_tarski(k2_relat_1(B_5), A_4) | ~v1_relat_1(B_5))), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.25/1.49  tff(c_137, plain, (v5_relat_1('#skF_4', k1_relat_1('#skF_5')) | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_134, c_8])).
% 3.25/1.49  tff(c_140, plain, (v5_relat_1('#skF_4', k1_relat_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_73, c_137])).
% 3.25/1.49  tff(c_12, plain, (![B_7, C_9, A_6]: (r2_hidden(k1_funct_1(B_7, C_9), A_6) | ~r2_hidden(C_9, k1_relat_1(B_7)) | ~v1_funct_1(B_7) | ~v5_relat_1(B_7, A_6) | ~v1_relat_1(B_7))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.25/1.49  tff(c_462, plain, (![A_136, B_137, B_138, C_139]: (k7_partfun1(A_136, B_137, k1_funct_1(B_138, C_139))=k1_funct_1(B_137, k1_funct_1(B_138, C_139)) | ~v1_funct_1(B_137) | ~v5_relat_1(B_137, A_136) | ~v1_relat_1(B_137) | ~r2_hidden(C_139, k1_relat_1(B_138)) | ~v1_funct_1(B_138) | ~v5_relat_1(B_138, k1_relat_1(B_137)) | ~v1_relat_1(B_138))), inference(resolution, [status(thm)], [c_12, c_182])).
% 3.25/1.49  tff(c_464, plain, (![A_136, B_137, C_139]: (k7_partfun1(A_136, B_137, k1_funct_1('#skF_4', C_139))=k1_funct_1(B_137, k1_funct_1('#skF_4', C_139)) | ~v1_funct_1(B_137) | ~v5_relat_1(B_137, A_136) | ~v1_relat_1(B_137) | ~r2_hidden(C_139, '#skF_2') | ~v1_funct_1('#skF_4') | ~v5_relat_1('#skF_4', k1_relat_1(B_137)) | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_171, c_462])).
% 3.25/1.49  tff(c_476, plain, (![A_141, B_142, C_143]: (k7_partfun1(A_141, B_142, k1_funct_1('#skF_4', C_143))=k1_funct_1(B_142, k1_funct_1('#skF_4', C_143)) | ~v1_funct_1(B_142) | ~v5_relat_1(B_142, A_141) | ~v1_relat_1(B_142) | ~r2_hidden(C_143, '#skF_2') | ~v5_relat_1('#skF_4', k1_relat_1(B_142)))), inference(demodulation, [status(thm), theory('equality')], [c_73, c_56, c_464])).
% 3.25/1.49  tff(c_480, plain, (![A_141, C_143]: (k7_partfun1(A_141, '#skF_5', k1_funct_1('#skF_4', C_143))=k1_funct_1('#skF_5', k1_funct_1('#skF_4', C_143)) | ~v1_funct_1('#skF_5') | ~v5_relat_1('#skF_5', A_141) | ~v1_relat_1('#skF_5') | ~r2_hidden(C_143, '#skF_2'))), inference(resolution, [status(thm)], [c_140, c_476])).
% 3.25/1.49  tff(c_486, plain, (![A_144, C_145]: (k7_partfun1(A_144, '#skF_5', k1_funct_1('#skF_4', C_145))=k1_funct_1('#skF_5', k1_funct_1('#skF_4', C_145)) | ~v5_relat_1('#skF_5', A_144) | ~r2_hidden(C_145, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_50, c_480])).
% 3.25/1.49  tff(c_40, plain, (k7_partfun1('#skF_1', '#skF_5', k1_funct_1('#skF_4', '#skF_6'))!=k1_funct_1(k8_funct_2('#skF_2', '#skF_3', '#skF_1', '#skF_4', '#skF_5'), '#skF_6')), inference(cnfTransformation, [status(thm)], [f_149])).
% 3.25/1.49  tff(c_492, plain, (k1_funct_1(k8_funct_2('#skF_2', '#skF_3', '#skF_1', '#skF_4', '#skF_5'), '#skF_6')!=k1_funct_1('#skF_5', k1_funct_1('#skF_4', '#skF_6')) | ~v5_relat_1('#skF_5', '#skF_1') | ~r2_hidden('#skF_6', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_486, c_40])).
% 3.25/1.49  tff(c_498, plain, (k1_funct_1(k8_funct_2('#skF_2', '#skF_3', '#skF_1', '#skF_4', '#skF_5'), '#skF_6')!=k1_funct_1('#skF_5', k1_funct_1('#skF_4', '#skF_6')) | ~r2_hidden('#skF_6', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_89, c_492])).
% 3.25/1.49  tff(c_523, plain, (~r2_hidden('#skF_6', '#skF_2')), inference(splitLeft, [status(thm)], [c_498])).
% 3.25/1.49  tff(c_526, plain, (v1_xboole_0('#skF_2') | ~m1_subset_1('#skF_6', '#skF_2')), inference(resolution, [status(thm)], [c_6, c_523])).
% 3.25/1.49  tff(c_529, plain, (v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_526])).
% 3.25/1.49  tff(c_531, plain, $false, inference(negUnitSimplification, [status(thm)], [c_226, c_529])).
% 3.25/1.49  tff(c_532, plain, (k1_funct_1(k8_funct_2('#skF_2', '#skF_3', '#skF_1', '#skF_4', '#skF_5'), '#skF_6')!=k1_funct_1('#skF_5', k1_funct_1('#skF_4', '#skF_6'))), inference(splitRight, [status(thm)], [c_498])).
% 3.25/1.49  tff(c_576, plain, (~m1_subset_1('#skF_6', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_507, c_532])).
% 3.25/1.49  tff(c_580, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_46, c_576])).
% 3.25/1.49  tff(c_581, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_167])).
% 3.25/1.49  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 3.25/1.49  tff(c_590, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_581, c_2])).
% 3.25/1.49  tff(c_593, plain, $false, inference(negUnitSimplification, [status(thm)], [c_58, c_590])).
% 3.25/1.49  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.25/1.49  
% 3.25/1.49  Inference rules
% 3.25/1.49  ----------------------
% 3.25/1.49  #Ref     : 0
% 3.25/1.49  #Sup     : 112
% 3.25/1.49  #Fact    : 0
% 3.25/1.49  #Define  : 0
% 3.25/1.49  #Split   : 7
% 3.25/1.49  #Chain   : 0
% 3.25/1.49  #Close   : 0
% 3.25/1.49  
% 3.25/1.49  Ordering : KBO
% 3.25/1.49  
% 3.25/1.49  Simplification rules
% 3.25/1.49  ----------------------
% 3.25/1.49  #Subsume      : 8
% 3.25/1.49  #Demod        : 123
% 3.25/1.49  #Tautology    : 43
% 3.25/1.49  #SimpNegUnit  : 14
% 3.25/1.49  #BackRed      : 17
% 3.25/1.49  
% 3.25/1.49  #Partial instantiations: 0
% 3.25/1.49  #Strategies tried      : 1
% 3.25/1.49  
% 3.25/1.49  Timing (in seconds)
% 3.25/1.49  ----------------------
% 3.25/1.50  Preprocessing        : 0.36
% 3.25/1.50  Parsing              : 0.19
% 3.25/1.50  CNF conversion       : 0.03
% 3.25/1.50  Main loop            : 0.36
% 3.25/1.50  Inferencing          : 0.13
% 3.25/1.50  Reduction            : 0.12
% 3.25/1.50  Demodulation         : 0.08
% 3.25/1.50  BG Simplification    : 0.02
% 3.25/1.50  Subsumption          : 0.06
% 3.25/1.50  Abstraction          : 0.02
% 3.25/1.50  MUC search           : 0.00
% 3.25/1.50  Cooper               : 0.00
% 3.25/1.50  Total                : 0.76
% 3.25/1.50  Index Insertion      : 0.00
% 3.25/1.50  Index Deletion       : 0.00
% 3.25/1.50  Index Matching       : 0.00
% 3.25/1.50  BG Taut test         : 0.00
%------------------------------------------------------------------------------
