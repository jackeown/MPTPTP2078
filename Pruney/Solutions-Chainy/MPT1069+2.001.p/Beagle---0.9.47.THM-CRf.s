%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:17:45 EST 2020

% Result     : Theorem 3.01s
% Output     : CNFRefutation 3.21s
% Verified   : 
% Statistics : Number of formulae       :  123 ( 383 expanded)
%              Number of leaves         :   45 ( 151 expanded)
%              Depth                    :   14
%              Number of atoms          :  284 (1410 expanded)
%              Number of equality atoms :   48 ( 258 expanded)
%              Maximal formula depth    :   17 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k8_funct_2 > k7_partfun1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(v1_partfun1,type,(
    v1_partfun1: ( $i * $i ) > $o )).

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

tff(f_187,negated_conjecture,(
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

tff(f_65,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_61,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_150,axiom,(
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

tff(f_50,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_95,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => ( ( v1_funct_1(C)
              & v1_funct_2(C,A,B) )
           => ( v1_funct_1(C)
              & v1_partfun1(C,A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc5_funct_2)).

tff(f_71,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(C,A)))
     => ( r1_tarski(k2_relat_1(D),B)
       => m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(C,B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_relset_1)).

tff(f_81,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( ( v1_funct_1(C)
          & v1_partfun1(C,A) )
       => ( v1_funct_1(C)
          & v1_funct_2(C,A,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_funct_2)).

tff(f_44,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_36,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_162,axiom,(
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

tff(f_126,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A)
        & v1_funct_1(B) )
     => ! [C] :
          ( r2_hidden(C,k1_relat_1(B))
         => k7_partfun1(A,B,C) = k1_funct_1(B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_partfun1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(B,A)))
         => v1_xboole_0(C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc4_relset_1)).

tff(f_115,axiom,(
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

tff(c_50,plain,(
    m1_subset_1('#skF_6','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_187])).

tff(c_54,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_187])).

tff(c_52,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_187])).

tff(c_56,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_187])).

tff(c_130,plain,(
    ! [A_91,B_92,C_93] :
      ( k2_relset_1(A_91,B_92,C_93) = k2_relat_1(C_93)
      | ~ m1_subset_1(C_93,k1_zfmisc_1(k2_zfmisc_1(A_91,B_92))) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_138,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_56,c_130])).

tff(c_112,plain,(
    ! [A_88,B_89,C_90] :
      ( k1_relset_1(A_88,B_89,C_90) = k1_relat_1(C_90)
      | ~ m1_subset_1(C_90,k1_zfmisc_1(k2_zfmisc_1(A_88,B_89))) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_119,plain,(
    k1_relset_1('#skF_3','#skF_1','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_52,c_112])).

tff(c_48,plain,(
    r1_tarski(k2_relset_1('#skF_2','#skF_3','#skF_4'),k1_relset_1('#skF_3','#skF_1','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_187])).

tff(c_121,plain,(
    r1_tarski(k2_relset_1('#skF_2','#skF_3','#skF_4'),k1_relat_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_119,c_48])).

tff(c_143,plain,(
    r1_tarski(k2_relat_1('#skF_4'),k1_relat_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_138,c_121])).

tff(c_62,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_187])).

tff(c_46,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_187])).

tff(c_60,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_187])).

tff(c_58,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_187])).

tff(c_398,plain,(
    ! [C_132,E_130,A_131,D_129,F_133,B_134] :
      ( k1_funct_1(k8_funct_2(B_134,C_132,A_131,D_129,E_130),F_133) = k1_funct_1(E_130,k1_funct_1(D_129,F_133))
      | k1_xboole_0 = B_134
      | ~ r1_tarski(k2_relset_1(B_134,C_132,D_129),k1_relset_1(C_132,A_131,E_130))
      | ~ m1_subset_1(F_133,B_134)
      | ~ m1_subset_1(E_130,k1_zfmisc_1(k2_zfmisc_1(C_132,A_131)))
      | ~ v1_funct_1(E_130)
      | ~ m1_subset_1(D_129,k1_zfmisc_1(k2_zfmisc_1(B_134,C_132)))
      | ~ v1_funct_2(D_129,B_134,C_132)
      | ~ v1_funct_1(D_129)
      | v1_xboole_0(C_132) ) ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_406,plain,(
    ! [A_131,E_130,F_133] :
      ( k1_funct_1(k8_funct_2('#skF_2','#skF_3',A_131,'#skF_4',E_130),F_133) = k1_funct_1(E_130,k1_funct_1('#skF_4',F_133))
      | k1_xboole_0 = '#skF_2'
      | ~ r1_tarski(k2_relat_1('#skF_4'),k1_relset_1('#skF_3',A_131,E_130))
      | ~ m1_subset_1(F_133,'#skF_2')
      | ~ m1_subset_1(E_130,k1_zfmisc_1(k2_zfmisc_1('#skF_3',A_131)))
      | ~ v1_funct_1(E_130)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
      | ~ v1_funct_2('#skF_4','#skF_2','#skF_3')
      | ~ v1_funct_1('#skF_4')
      | v1_xboole_0('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_138,c_398])).

tff(c_419,plain,(
    ! [A_131,E_130,F_133] :
      ( k1_funct_1(k8_funct_2('#skF_2','#skF_3',A_131,'#skF_4',E_130),F_133) = k1_funct_1(E_130,k1_funct_1('#skF_4',F_133))
      | k1_xboole_0 = '#skF_2'
      | ~ r1_tarski(k2_relat_1('#skF_4'),k1_relset_1('#skF_3',A_131,E_130))
      | ~ m1_subset_1(F_133,'#skF_2')
      | ~ m1_subset_1(E_130,k1_zfmisc_1(k2_zfmisc_1('#skF_3',A_131)))
      | ~ v1_funct_1(E_130)
      | v1_xboole_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_56,c_406])).

tff(c_440,plain,(
    ! [A_139,E_140,F_141] :
      ( k1_funct_1(k8_funct_2('#skF_2','#skF_3',A_139,'#skF_4',E_140),F_141) = k1_funct_1(E_140,k1_funct_1('#skF_4',F_141))
      | ~ r1_tarski(k2_relat_1('#skF_4'),k1_relset_1('#skF_3',A_139,E_140))
      | ~ m1_subset_1(F_141,'#skF_2')
      | ~ m1_subset_1(E_140,k1_zfmisc_1(k2_zfmisc_1('#skF_3',A_139)))
      | ~ v1_funct_1(E_140) ) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_46,c_419])).

tff(c_442,plain,(
    ! [F_141] :
      ( k1_funct_1(k8_funct_2('#skF_2','#skF_3','#skF_1','#skF_4','#skF_5'),F_141) = k1_funct_1('#skF_5',k1_funct_1('#skF_4',F_141))
      | ~ r1_tarski(k2_relat_1('#skF_4'),k1_relat_1('#skF_5'))
      | ~ m1_subset_1(F_141,'#skF_2')
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_1')))
      | ~ v1_funct_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_119,c_440])).

tff(c_444,plain,(
    ! [F_141] :
      ( k1_funct_1(k8_funct_2('#skF_2','#skF_3','#skF_1','#skF_4','#skF_5'),F_141) = k1_funct_1('#skF_5',k1_funct_1('#skF_4',F_141))
      | ~ m1_subset_1(F_141,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_143,c_442])).

tff(c_84,plain,(
    ! [C_79,B_80,A_81] :
      ( v5_relat_1(C_79,B_80)
      | ~ m1_subset_1(C_79,k1_zfmisc_1(k2_zfmisc_1(A_81,B_80))) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_91,plain,(
    v5_relat_1('#skF_5','#skF_1') ),
    inference(resolution,[status(thm)],[c_52,c_84])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_249,plain,(
    ! [C_106,A_107,B_108] :
      ( v1_partfun1(C_106,A_107)
      | ~ v1_funct_2(C_106,A_107,B_108)
      | ~ v1_funct_1(C_106)
      | ~ m1_subset_1(C_106,k1_zfmisc_1(k2_zfmisc_1(A_107,B_108)))
      | v1_xboole_0(B_108) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_261,plain,
    ( v1_partfun1('#skF_4','#skF_2')
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_3')
    | ~ v1_funct_1('#skF_4')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_56,c_249])).

tff(c_275,plain,
    ( v1_partfun1('#skF_4','#skF_2')
    | v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_261])).

tff(c_276,plain,(
    v1_partfun1('#skF_4','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_275])).

tff(c_162,plain,(
    ! [D_97,C_98,B_99,A_100] :
      ( m1_subset_1(D_97,k1_zfmisc_1(k2_zfmisc_1(C_98,B_99)))
      | ~ r1_tarski(k2_relat_1(D_97),B_99)
      | ~ m1_subset_1(D_97,k1_zfmisc_1(k2_zfmisc_1(C_98,A_100))) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_208,plain,(
    ! [B_104] :
      ( m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2',B_104)))
      | ~ r1_tarski(k2_relat_1('#skF_4'),B_104) ) ),
    inference(resolution,[status(thm)],[c_56,c_162])).

tff(c_24,plain,(
    ! [C_27,A_25,B_26] :
      ( v1_funct_2(C_27,A_25,B_26)
      | ~ v1_partfun1(C_27,A_25)
      | ~ v1_funct_1(C_27)
      | ~ m1_subset_1(C_27,k1_zfmisc_1(k2_zfmisc_1(A_25,B_26))) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_213,plain,(
    ! [B_104] :
      ( v1_funct_2('#skF_4','#skF_2',B_104)
      | ~ v1_partfun1('#skF_4','#skF_2')
      | ~ v1_funct_1('#skF_4')
      | ~ r1_tarski(k2_relat_1('#skF_4'),B_104) ) ),
    inference(resolution,[status(thm)],[c_208,c_24])).

tff(c_235,plain,(
    ! [B_104] :
      ( v1_funct_2('#skF_4','#skF_2',B_104)
      | ~ v1_partfun1('#skF_4','#skF_2')
      | ~ r1_tarski(k2_relat_1('#skF_4'),B_104) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_213])).

tff(c_310,plain,(
    ! [B_117] :
      ( v1_funct_2('#skF_4','#skF_2',B_117)
      | ~ r1_tarski(k2_relat_1('#skF_4'),B_117) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_276,c_235])).

tff(c_314,plain,(
    v1_funct_2('#skF_4','#skF_2',k1_relat_1('#skF_5')) ),
    inference(resolution,[status(thm)],[c_143,c_310])).

tff(c_75,plain,(
    ! [C_76,A_77,B_78] :
      ( v1_relat_1(C_76)
      | ~ m1_subset_1(C_76,k1_zfmisc_1(k2_zfmisc_1(A_77,B_78))) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_82,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_52,c_75])).

tff(c_6,plain,(
    ! [A_2,B_3] :
      ( r2_hidden(A_2,B_3)
      | v1_xboole_0(B_3)
      | ~ m1_subset_1(A_2,B_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_346,plain,(
    ! [D_122,C_123,B_124,A_125] :
      ( r2_hidden(k1_funct_1(D_122,C_123),B_124)
      | k1_xboole_0 = B_124
      | ~ r2_hidden(C_123,A_125)
      | ~ m1_subset_1(D_122,k1_zfmisc_1(k2_zfmisc_1(A_125,B_124)))
      | ~ v1_funct_2(D_122,A_125,B_124)
      | ~ v1_funct_1(D_122) ) ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_455,plain,(
    ! [D_143,A_144,B_145,B_146] :
      ( r2_hidden(k1_funct_1(D_143,A_144),B_145)
      | k1_xboole_0 = B_145
      | ~ m1_subset_1(D_143,k1_zfmisc_1(k2_zfmisc_1(B_146,B_145)))
      | ~ v1_funct_2(D_143,B_146,B_145)
      | ~ v1_funct_1(D_143)
      | v1_xboole_0(B_146)
      | ~ m1_subset_1(A_144,B_146) ) ),
    inference(resolution,[status(thm)],[c_6,c_346])).

tff(c_463,plain,(
    ! [A_144] :
      ( r2_hidden(k1_funct_1('#skF_4',A_144),'#skF_3')
      | k1_xboole_0 = '#skF_3'
      | ~ v1_funct_2('#skF_4','#skF_2','#skF_3')
      | ~ v1_funct_1('#skF_4')
      | v1_xboole_0('#skF_2')
      | ~ m1_subset_1(A_144,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_56,c_455])).

tff(c_477,plain,(
    ! [A_144] :
      ( r2_hidden(k1_funct_1('#skF_4',A_144),'#skF_3')
      | k1_xboole_0 = '#skF_3'
      | v1_xboole_0('#skF_2')
      | ~ m1_subset_1(A_144,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_463])).

tff(c_478,plain,(
    v1_xboole_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_477])).

tff(c_4,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_481,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_478,c_4])).

tff(c_488,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_481])).

tff(c_490,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_477])).

tff(c_168,plain,(
    ! [B_99] :
      ( m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2',B_99)))
      | ~ r1_tarski(k2_relat_1('#skF_4'),B_99) ) ),
    inference(resolution,[status(thm)],[c_56,c_162])).

tff(c_457,plain,(
    ! [A_144,B_99] :
      ( r2_hidden(k1_funct_1('#skF_4',A_144),B_99)
      | k1_xboole_0 = B_99
      | ~ v1_funct_2('#skF_4','#skF_2',B_99)
      | ~ v1_funct_1('#skF_4')
      | v1_xboole_0('#skF_2')
      | ~ m1_subset_1(A_144,'#skF_2')
      | ~ r1_tarski(k2_relat_1('#skF_4'),B_99) ) ),
    inference(resolution,[status(thm)],[c_168,c_455])).

tff(c_466,plain,(
    ! [A_144,B_99] :
      ( r2_hidden(k1_funct_1('#skF_4',A_144),B_99)
      | k1_xboole_0 = B_99
      | ~ v1_funct_2('#skF_4','#skF_2',B_99)
      | v1_xboole_0('#skF_2')
      | ~ m1_subset_1(A_144,'#skF_2')
      | ~ r1_tarski(k2_relat_1('#skF_4'),B_99) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_457])).

tff(c_526,plain,(
    ! [A_150,B_151] :
      ( r2_hidden(k1_funct_1('#skF_4',A_150),B_151)
      | k1_xboole_0 = B_151
      | ~ v1_funct_2('#skF_4','#skF_2',B_151)
      | ~ m1_subset_1(A_150,'#skF_2')
      | ~ r1_tarski(k2_relat_1('#skF_4'),B_151) ) ),
    inference(negUnitSimplification,[status(thm)],[c_490,c_466])).

tff(c_38,plain,(
    ! [A_36,B_37,C_39] :
      ( k7_partfun1(A_36,B_37,C_39) = k1_funct_1(B_37,C_39)
      | ~ r2_hidden(C_39,k1_relat_1(B_37))
      | ~ v1_funct_1(B_37)
      | ~ v5_relat_1(B_37,A_36)
      | ~ v1_relat_1(B_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_556,plain,(
    ! [A_155,B_156,A_157] :
      ( k7_partfun1(A_155,B_156,k1_funct_1('#skF_4',A_157)) = k1_funct_1(B_156,k1_funct_1('#skF_4',A_157))
      | ~ v1_funct_1(B_156)
      | ~ v5_relat_1(B_156,A_155)
      | ~ v1_relat_1(B_156)
      | k1_relat_1(B_156) = k1_xboole_0
      | ~ v1_funct_2('#skF_4','#skF_2',k1_relat_1(B_156))
      | ~ m1_subset_1(A_157,'#skF_2')
      | ~ r1_tarski(k2_relat_1('#skF_4'),k1_relat_1(B_156)) ) ),
    inference(resolution,[status(thm)],[c_526,c_38])).

tff(c_560,plain,(
    ! [A_155,A_157] :
      ( k7_partfun1(A_155,'#skF_5',k1_funct_1('#skF_4',A_157)) = k1_funct_1('#skF_5',k1_funct_1('#skF_4',A_157))
      | ~ v1_funct_1('#skF_5')
      | ~ v5_relat_1('#skF_5',A_155)
      | ~ v1_relat_1('#skF_5')
      | k1_relat_1('#skF_5') = k1_xboole_0
      | ~ v1_funct_2('#skF_4','#skF_2',k1_relat_1('#skF_5'))
      | ~ m1_subset_1(A_157,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_143,c_556])).

tff(c_565,plain,(
    ! [A_155,A_157] :
      ( k7_partfun1(A_155,'#skF_5',k1_funct_1('#skF_4',A_157)) = k1_funct_1('#skF_5',k1_funct_1('#skF_4',A_157))
      | ~ v5_relat_1('#skF_5',A_155)
      | k1_relat_1('#skF_5') = k1_xboole_0
      | ~ m1_subset_1(A_157,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_314,c_82,c_54,c_560])).

tff(c_566,plain,(
    k1_relat_1('#skF_5') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_565])).

tff(c_16,plain,(
    ! [C_14,B_12,A_11] :
      ( v1_xboole_0(C_14)
      | ~ m1_subset_1(C_14,k1_zfmisc_1(k2_zfmisc_1(B_12,A_11)))
      | ~ v1_xboole_0(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_238,plain,(
    ! [B_104] :
      ( v1_xboole_0('#skF_4')
      | ~ v1_xboole_0(B_104)
      | ~ r1_tarski(k2_relat_1('#skF_4'),B_104) ) ),
    inference(resolution,[status(thm)],[c_208,c_16])).

tff(c_278,plain,(
    ! [B_109] :
      ( ~ v1_xboole_0(B_109)
      | ~ r1_tarski(k2_relat_1('#skF_4'),B_109) ) ),
    inference(splitLeft,[status(thm)],[c_238])).

tff(c_282,plain,(
    ~ v1_xboole_0(k1_relat_1('#skF_5')) ),
    inference(resolution,[status(thm)],[c_143,c_278])).

tff(c_579,plain,(
    ~ v1_xboole_0(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_566,c_282])).

tff(c_585,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_579])).

tff(c_588,plain,(
    ! [A_161,A_162] :
      ( k7_partfun1(A_161,'#skF_5',k1_funct_1('#skF_4',A_162)) = k1_funct_1('#skF_5',k1_funct_1('#skF_4',A_162))
      | ~ v5_relat_1('#skF_5',A_161)
      | ~ m1_subset_1(A_162,'#skF_2') ) ),
    inference(splitRight,[status(thm)],[c_565])).

tff(c_44,plain,(
    k7_partfun1('#skF_1','#skF_5',k1_funct_1('#skF_4','#skF_6')) != k1_funct_1(k8_funct_2('#skF_2','#skF_3','#skF_1','#skF_4','#skF_5'),'#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_187])).

tff(c_594,plain,
    ( k1_funct_1(k8_funct_2('#skF_2','#skF_3','#skF_1','#skF_4','#skF_5'),'#skF_6') != k1_funct_1('#skF_5',k1_funct_1('#skF_4','#skF_6'))
    | ~ v5_relat_1('#skF_5','#skF_1')
    | ~ m1_subset_1('#skF_6','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_588,c_44])).

tff(c_600,plain,(
    k1_funct_1(k8_funct_2('#skF_2','#skF_3','#skF_1','#skF_4','#skF_5'),'#skF_6') != k1_funct_1('#skF_5',k1_funct_1('#skF_4','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_91,c_594])).

tff(c_610,plain,(
    ~ m1_subset_1('#skF_6','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_444,c_600])).

tff(c_614,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_610])).

tff(c_615,plain,(
    v1_xboole_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_238])).

tff(c_622,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_615,c_4])).

tff(c_628,plain,(
    '#skF_2' != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_622,c_46])).

tff(c_674,plain,(
    ! [C_176,A_177,B_178] :
      ( ~ v1_xboole_0(C_176)
      | ~ v1_funct_2(C_176,A_177,B_178)
      | ~ v1_funct_1(C_176)
      | ~ m1_subset_1(C_176,k1_zfmisc_1(k2_zfmisc_1(A_177,B_178)))
      | v1_xboole_0(B_178)
      | v1_xboole_0(A_177) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_686,plain,
    ( ~ v1_xboole_0('#skF_4')
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_3')
    | ~ v1_funct_1('#skF_4')
    | v1_xboole_0('#skF_3')
    | v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_56,c_674])).

tff(c_700,plain,
    ( v1_xboole_0('#skF_3')
    | v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_615,c_686])).

tff(c_701,plain,(
    v1_xboole_0('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_700])).

tff(c_625,plain,(
    ! [A_1] :
      ( A_1 = '#skF_4'
      | ~ v1_xboole_0(A_1) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_622,c_4])).

tff(c_704,plain,(
    '#skF_2' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_701,c_625])).

tff(c_711,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_628,c_704])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n022.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 11:13:41 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.01/1.46  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.21/1.47  
% 3.21/1.47  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.21/1.47  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k8_funct_2 > k7_partfun1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 3.21/1.47  
% 3.21/1.47  %Foreground sorts:
% 3.21/1.47  
% 3.21/1.47  
% 3.21/1.47  %Background operators:
% 3.21/1.47  
% 3.21/1.47  
% 3.21/1.47  %Foreground operators:
% 3.21/1.47  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 3.21/1.47  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.21/1.47  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.21/1.47  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.21/1.47  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.21/1.47  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.21/1.47  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.21/1.47  tff(k7_partfun1, type, k7_partfun1: ($i * $i * $i) > $i).
% 3.21/1.47  tff('#skF_5', type, '#skF_5': $i).
% 3.21/1.47  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.21/1.47  tff(k8_funct_2, type, k8_funct_2: ($i * $i * $i * $i * $i) > $i).
% 3.21/1.47  tff('#skF_6', type, '#skF_6': $i).
% 3.21/1.47  tff('#skF_2', type, '#skF_2': $i).
% 3.21/1.47  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 3.21/1.47  tff('#skF_3', type, '#skF_3': $i).
% 3.21/1.47  tff('#skF_1', type, '#skF_1': $i).
% 3.21/1.47  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.21/1.47  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.21/1.47  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.21/1.47  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.21/1.47  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.21/1.47  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.21/1.47  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.21/1.47  tff('#skF_4', type, '#skF_4': $i).
% 3.21/1.47  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.21/1.47  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.21/1.47  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.21/1.47  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.21/1.47  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.21/1.47  
% 3.21/1.50  tff(f_187, negated_conjecture, ~(![A, B, C]: (~v1_xboole_0(C) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, C)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (![E]: ((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(C, A)))) => (![F]: (m1_subset_1(F, B) => (r1_tarski(k2_relset_1(B, C, D), k1_relset_1(C, A, E)) => ((B = k1_xboole_0) | (k1_funct_1(k8_funct_2(B, C, A, D, E), F) = k7_partfun1(A, E, k1_funct_1(D, F))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t186_funct_2)).
% 3.21/1.50  tff(f_65, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 3.21/1.50  tff(f_61, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.21/1.50  tff(f_150, axiom, (![A, B, C]: (~v1_xboole_0(C) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, C)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (![E]: ((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(C, A)))) => (![F]: (m1_subset_1(F, B) => (r1_tarski(k2_relset_1(B, C, D), k1_relset_1(C, A, E)) => ((B = k1_xboole_0) | (k1_funct_1(k8_funct_2(B, C, A, D, E), F) = k1_funct_1(E, k1_funct_1(D, F))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t185_funct_2)).
% 3.21/1.50  tff(f_50, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.21/1.50  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 3.21/1.50  tff(f_95, axiom, (![A, B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) => (v1_funct_1(C) & v1_partfun1(C, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc5_funct_2)).
% 3.21/1.50  tff(f_71, axiom, (![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(C, A))) => (r1_tarski(k2_relat_1(D), B) => m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(C, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t14_relset_1)).
% 3.21/1.50  tff(f_81, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v1_partfun1(C, A)) => (v1_funct_1(C) & v1_funct_2(C, A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_funct_2)).
% 3.21/1.50  tff(f_44, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.21/1.50  tff(f_36, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 3.21/1.50  tff(f_162, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_hidden(C, A) => ((B = k1_xboole_0) | r2_hidden(k1_funct_1(D, C), B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_funct_2)).
% 3.21/1.50  tff(f_30, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 3.21/1.50  tff(f_126, axiom, (![A, B]: (((v1_relat_1(B) & v5_relat_1(B, A)) & v1_funct_1(B)) => (![C]: (r2_hidden(C, k1_relat_1(B)) => (k7_partfun1(A, B, C) = k1_funct_1(B, C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_partfun1)).
% 3.21/1.50  tff(f_57, axiom, (![A, B]: (v1_xboole_0(A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => v1_xboole_0(C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc4_relset_1)).
% 3.21/1.50  tff(f_115, axiom, (![A, B]: ((~v1_xboole_0(A) & ~v1_xboole_0(B)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) => ((v1_funct_1(C) & ~v1_xboole_0(C)) & v1_funct_2(C, A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc6_funct_2)).
% 3.21/1.50  tff(c_50, plain, (m1_subset_1('#skF_6', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_187])).
% 3.21/1.50  tff(c_54, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_187])).
% 3.21/1.50  tff(c_52, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_187])).
% 3.21/1.50  tff(c_56, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_187])).
% 3.21/1.50  tff(c_130, plain, (![A_91, B_92, C_93]: (k2_relset_1(A_91, B_92, C_93)=k2_relat_1(C_93) | ~m1_subset_1(C_93, k1_zfmisc_1(k2_zfmisc_1(A_91, B_92))))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.21/1.50  tff(c_138, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_56, c_130])).
% 3.21/1.50  tff(c_112, plain, (![A_88, B_89, C_90]: (k1_relset_1(A_88, B_89, C_90)=k1_relat_1(C_90) | ~m1_subset_1(C_90, k1_zfmisc_1(k2_zfmisc_1(A_88, B_89))))), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.21/1.50  tff(c_119, plain, (k1_relset_1('#skF_3', '#skF_1', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_52, c_112])).
% 3.21/1.50  tff(c_48, plain, (r1_tarski(k2_relset_1('#skF_2', '#skF_3', '#skF_4'), k1_relset_1('#skF_3', '#skF_1', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_187])).
% 3.21/1.50  tff(c_121, plain, (r1_tarski(k2_relset_1('#skF_2', '#skF_3', '#skF_4'), k1_relat_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_119, c_48])).
% 3.21/1.50  tff(c_143, plain, (r1_tarski(k2_relat_1('#skF_4'), k1_relat_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_138, c_121])).
% 3.21/1.50  tff(c_62, plain, (~v1_xboole_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_187])).
% 3.21/1.50  tff(c_46, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_187])).
% 3.21/1.50  tff(c_60, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_187])).
% 3.21/1.50  tff(c_58, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_187])).
% 3.21/1.50  tff(c_398, plain, (![C_132, E_130, A_131, D_129, F_133, B_134]: (k1_funct_1(k8_funct_2(B_134, C_132, A_131, D_129, E_130), F_133)=k1_funct_1(E_130, k1_funct_1(D_129, F_133)) | k1_xboole_0=B_134 | ~r1_tarski(k2_relset_1(B_134, C_132, D_129), k1_relset_1(C_132, A_131, E_130)) | ~m1_subset_1(F_133, B_134) | ~m1_subset_1(E_130, k1_zfmisc_1(k2_zfmisc_1(C_132, A_131))) | ~v1_funct_1(E_130) | ~m1_subset_1(D_129, k1_zfmisc_1(k2_zfmisc_1(B_134, C_132))) | ~v1_funct_2(D_129, B_134, C_132) | ~v1_funct_1(D_129) | v1_xboole_0(C_132))), inference(cnfTransformation, [status(thm)], [f_150])).
% 3.21/1.50  tff(c_406, plain, (![A_131, E_130, F_133]: (k1_funct_1(k8_funct_2('#skF_2', '#skF_3', A_131, '#skF_4', E_130), F_133)=k1_funct_1(E_130, k1_funct_1('#skF_4', F_133)) | k1_xboole_0='#skF_2' | ~r1_tarski(k2_relat_1('#skF_4'), k1_relset_1('#skF_3', A_131, E_130)) | ~m1_subset_1(F_133, '#skF_2') | ~m1_subset_1(E_130, k1_zfmisc_1(k2_zfmisc_1('#skF_3', A_131))) | ~v1_funct_1(E_130) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3') | ~v1_funct_1('#skF_4') | v1_xboole_0('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_138, c_398])).
% 3.21/1.50  tff(c_419, plain, (![A_131, E_130, F_133]: (k1_funct_1(k8_funct_2('#skF_2', '#skF_3', A_131, '#skF_4', E_130), F_133)=k1_funct_1(E_130, k1_funct_1('#skF_4', F_133)) | k1_xboole_0='#skF_2' | ~r1_tarski(k2_relat_1('#skF_4'), k1_relset_1('#skF_3', A_131, E_130)) | ~m1_subset_1(F_133, '#skF_2') | ~m1_subset_1(E_130, k1_zfmisc_1(k2_zfmisc_1('#skF_3', A_131))) | ~v1_funct_1(E_130) | v1_xboole_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_56, c_406])).
% 3.21/1.50  tff(c_440, plain, (![A_139, E_140, F_141]: (k1_funct_1(k8_funct_2('#skF_2', '#skF_3', A_139, '#skF_4', E_140), F_141)=k1_funct_1(E_140, k1_funct_1('#skF_4', F_141)) | ~r1_tarski(k2_relat_1('#skF_4'), k1_relset_1('#skF_3', A_139, E_140)) | ~m1_subset_1(F_141, '#skF_2') | ~m1_subset_1(E_140, k1_zfmisc_1(k2_zfmisc_1('#skF_3', A_139))) | ~v1_funct_1(E_140))), inference(negUnitSimplification, [status(thm)], [c_62, c_46, c_419])).
% 3.21/1.50  tff(c_442, plain, (![F_141]: (k1_funct_1(k8_funct_2('#skF_2', '#skF_3', '#skF_1', '#skF_4', '#skF_5'), F_141)=k1_funct_1('#skF_5', k1_funct_1('#skF_4', F_141)) | ~r1_tarski(k2_relat_1('#skF_4'), k1_relat_1('#skF_5')) | ~m1_subset_1(F_141, '#skF_2') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_1'))) | ~v1_funct_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_119, c_440])).
% 3.21/1.50  tff(c_444, plain, (![F_141]: (k1_funct_1(k8_funct_2('#skF_2', '#skF_3', '#skF_1', '#skF_4', '#skF_5'), F_141)=k1_funct_1('#skF_5', k1_funct_1('#skF_4', F_141)) | ~m1_subset_1(F_141, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_143, c_442])).
% 3.21/1.50  tff(c_84, plain, (![C_79, B_80, A_81]: (v5_relat_1(C_79, B_80) | ~m1_subset_1(C_79, k1_zfmisc_1(k2_zfmisc_1(A_81, B_80))))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.21/1.50  tff(c_91, plain, (v5_relat_1('#skF_5', '#skF_1')), inference(resolution, [status(thm)], [c_52, c_84])).
% 3.21/1.50  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 3.21/1.50  tff(c_249, plain, (![C_106, A_107, B_108]: (v1_partfun1(C_106, A_107) | ~v1_funct_2(C_106, A_107, B_108) | ~v1_funct_1(C_106) | ~m1_subset_1(C_106, k1_zfmisc_1(k2_zfmisc_1(A_107, B_108))) | v1_xboole_0(B_108))), inference(cnfTransformation, [status(thm)], [f_95])).
% 3.21/1.50  tff(c_261, plain, (v1_partfun1('#skF_4', '#skF_2') | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3') | ~v1_funct_1('#skF_4') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_56, c_249])).
% 3.21/1.50  tff(c_275, plain, (v1_partfun1('#skF_4', '#skF_2') | v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_261])).
% 3.21/1.50  tff(c_276, plain, (v1_partfun1('#skF_4', '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_62, c_275])).
% 3.21/1.50  tff(c_162, plain, (![D_97, C_98, B_99, A_100]: (m1_subset_1(D_97, k1_zfmisc_1(k2_zfmisc_1(C_98, B_99))) | ~r1_tarski(k2_relat_1(D_97), B_99) | ~m1_subset_1(D_97, k1_zfmisc_1(k2_zfmisc_1(C_98, A_100))))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.21/1.50  tff(c_208, plain, (![B_104]: (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', B_104))) | ~r1_tarski(k2_relat_1('#skF_4'), B_104))), inference(resolution, [status(thm)], [c_56, c_162])).
% 3.21/1.50  tff(c_24, plain, (![C_27, A_25, B_26]: (v1_funct_2(C_27, A_25, B_26) | ~v1_partfun1(C_27, A_25) | ~v1_funct_1(C_27) | ~m1_subset_1(C_27, k1_zfmisc_1(k2_zfmisc_1(A_25, B_26))))), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.21/1.50  tff(c_213, plain, (![B_104]: (v1_funct_2('#skF_4', '#skF_2', B_104) | ~v1_partfun1('#skF_4', '#skF_2') | ~v1_funct_1('#skF_4') | ~r1_tarski(k2_relat_1('#skF_4'), B_104))), inference(resolution, [status(thm)], [c_208, c_24])).
% 3.21/1.50  tff(c_235, plain, (![B_104]: (v1_funct_2('#skF_4', '#skF_2', B_104) | ~v1_partfun1('#skF_4', '#skF_2') | ~r1_tarski(k2_relat_1('#skF_4'), B_104))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_213])).
% 3.21/1.50  tff(c_310, plain, (![B_117]: (v1_funct_2('#skF_4', '#skF_2', B_117) | ~r1_tarski(k2_relat_1('#skF_4'), B_117))), inference(demodulation, [status(thm), theory('equality')], [c_276, c_235])).
% 3.21/1.50  tff(c_314, plain, (v1_funct_2('#skF_4', '#skF_2', k1_relat_1('#skF_5'))), inference(resolution, [status(thm)], [c_143, c_310])).
% 3.21/1.50  tff(c_75, plain, (![C_76, A_77, B_78]: (v1_relat_1(C_76) | ~m1_subset_1(C_76, k1_zfmisc_1(k2_zfmisc_1(A_77, B_78))))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.21/1.50  tff(c_82, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_52, c_75])).
% 3.21/1.50  tff(c_6, plain, (![A_2, B_3]: (r2_hidden(A_2, B_3) | v1_xboole_0(B_3) | ~m1_subset_1(A_2, B_3))), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.21/1.50  tff(c_346, plain, (![D_122, C_123, B_124, A_125]: (r2_hidden(k1_funct_1(D_122, C_123), B_124) | k1_xboole_0=B_124 | ~r2_hidden(C_123, A_125) | ~m1_subset_1(D_122, k1_zfmisc_1(k2_zfmisc_1(A_125, B_124))) | ~v1_funct_2(D_122, A_125, B_124) | ~v1_funct_1(D_122))), inference(cnfTransformation, [status(thm)], [f_162])).
% 3.21/1.50  tff(c_455, plain, (![D_143, A_144, B_145, B_146]: (r2_hidden(k1_funct_1(D_143, A_144), B_145) | k1_xboole_0=B_145 | ~m1_subset_1(D_143, k1_zfmisc_1(k2_zfmisc_1(B_146, B_145))) | ~v1_funct_2(D_143, B_146, B_145) | ~v1_funct_1(D_143) | v1_xboole_0(B_146) | ~m1_subset_1(A_144, B_146))), inference(resolution, [status(thm)], [c_6, c_346])).
% 3.21/1.50  tff(c_463, plain, (![A_144]: (r2_hidden(k1_funct_1('#skF_4', A_144), '#skF_3') | k1_xboole_0='#skF_3' | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3') | ~v1_funct_1('#skF_4') | v1_xboole_0('#skF_2') | ~m1_subset_1(A_144, '#skF_2'))), inference(resolution, [status(thm)], [c_56, c_455])).
% 3.21/1.50  tff(c_477, plain, (![A_144]: (r2_hidden(k1_funct_1('#skF_4', A_144), '#skF_3') | k1_xboole_0='#skF_3' | v1_xboole_0('#skF_2') | ~m1_subset_1(A_144, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_463])).
% 3.21/1.50  tff(c_478, plain, (v1_xboole_0('#skF_2')), inference(splitLeft, [status(thm)], [c_477])).
% 3.21/1.50  tff(c_4, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_30])).
% 3.21/1.50  tff(c_481, plain, (k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_478, c_4])).
% 3.21/1.50  tff(c_488, plain, $false, inference(negUnitSimplification, [status(thm)], [c_46, c_481])).
% 3.21/1.50  tff(c_490, plain, (~v1_xboole_0('#skF_2')), inference(splitRight, [status(thm)], [c_477])).
% 3.21/1.50  tff(c_168, plain, (![B_99]: (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', B_99))) | ~r1_tarski(k2_relat_1('#skF_4'), B_99))), inference(resolution, [status(thm)], [c_56, c_162])).
% 3.21/1.50  tff(c_457, plain, (![A_144, B_99]: (r2_hidden(k1_funct_1('#skF_4', A_144), B_99) | k1_xboole_0=B_99 | ~v1_funct_2('#skF_4', '#skF_2', B_99) | ~v1_funct_1('#skF_4') | v1_xboole_0('#skF_2') | ~m1_subset_1(A_144, '#skF_2') | ~r1_tarski(k2_relat_1('#skF_4'), B_99))), inference(resolution, [status(thm)], [c_168, c_455])).
% 3.21/1.50  tff(c_466, plain, (![A_144, B_99]: (r2_hidden(k1_funct_1('#skF_4', A_144), B_99) | k1_xboole_0=B_99 | ~v1_funct_2('#skF_4', '#skF_2', B_99) | v1_xboole_0('#skF_2') | ~m1_subset_1(A_144, '#skF_2') | ~r1_tarski(k2_relat_1('#skF_4'), B_99))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_457])).
% 3.21/1.50  tff(c_526, plain, (![A_150, B_151]: (r2_hidden(k1_funct_1('#skF_4', A_150), B_151) | k1_xboole_0=B_151 | ~v1_funct_2('#skF_4', '#skF_2', B_151) | ~m1_subset_1(A_150, '#skF_2') | ~r1_tarski(k2_relat_1('#skF_4'), B_151))), inference(negUnitSimplification, [status(thm)], [c_490, c_466])).
% 3.21/1.50  tff(c_38, plain, (![A_36, B_37, C_39]: (k7_partfun1(A_36, B_37, C_39)=k1_funct_1(B_37, C_39) | ~r2_hidden(C_39, k1_relat_1(B_37)) | ~v1_funct_1(B_37) | ~v5_relat_1(B_37, A_36) | ~v1_relat_1(B_37))), inference(cnfTransformation, [status(thm)], [f_126])).
% 3.21/1.50  tff(c_556, plain, (![A_155, B_156, A_157]: (k7_partfun1(A_155, B_156, k1_funct_1('#skF_4', A_157))=k1_funct_1(B_156, k1_funct_1('#skF_4', A_157)) | ~v1_funct_1(B_156) | ~v5_relat_1(B_156, A_155) | ~v1_relat_1(B_156) | k1_relat_1(B_156)=k1_xboole_0 | ~v1_funct_2('#skF_4', '#skF_2', k1_relat_1(B_156)) | ~m1_subset_1(A_157, '#skF_2') | ~r1_tarski(k2_relat_1('#skF_4'), k1_relat_1(B_156)))), inference(resolution, [status(thm)], [c_526, c_38])).
% 3.21/1.50  tff(c_560, plain, (![A_155, A_157]: (k7_partfun1(A_155, '#skF_5', k1_funct_1('#skF_4', A_157))=k1_funct_1('#skF_5', k1_funct_1('#skF_4', A_157)) | ~v1_funct_1('#skF_5') | ~v5_relat_1('#skF_5', A_155) | ~v1_relat_1('#skF_5') | k1_relat_1('#skF_5')=k1_xboole_0 | ~v1_funct_2('#skF_4', '#skF_2', k1_relat_1('#skF_5')) | ~m1_subset_1(A_157, '#skF_2'))), inference(resolution, [status(thm)], [c_143, c_556])).
% 3.21/1.50  tff(c_565, plain, (![A_155, A_157]: (k7_partfun1(A_155, '#skF_5', k1_funct_1('#skF_4', A_157))=k1_funct_1('#skF_5', k1_funct_1('#skF_4', A_157)) | ~v5_relat_1('#skF_5', A_155) | k1_relat_1('#skF_5')=k1_xboole_0 | ~m1_subset_1(A_157, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_314, c_82, c_54, c_560])).
% 3.21/1.50  tff(c_566, plain, (k1_relat_1('#skF_5')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_565])).
% 3.21/1.50  tff(c_16, plain, (![C_14, B_12, A_11]: (v1_xboole_0(C_14) | ~m1_subset_1(C_14, k1_zfmisc_1(k2_zfmisc_1(B_12, A_11))) | ~v1_xboole_0(A_11))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.21/1.50  tff(c_238, plain, (![B_104]: (v1_xboole_0('#skF_4') | ~v1_xboole_0(B_104) | ~r1_tarski(k2_relat_1('#skF_4'), B_104))), inference(resolution, [status(thm)], [c_208, c_16])).
% 3.21/1.50  tff(c_278, plain, (![B_109]: (~v1_xboole_0(B_109) | ~r1_tarski(k2_relat_1('#skF_4'), B_109))), inference(splitLeft, [status(thm)], [c_238])).
% 3.21/1.50  tff(c_282, plain, (~v1_xboole_0(k1_relat_1('#skF_5'))), inference(resolution, [status(thm)], [c_143, c_278])).
% 3.21/1.50  tff(c_579, plain, (~v1_xboole_0(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_566, c_282])).
% 3.21/1.50  tff(c_585, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2, c_579])).
% 3.21/1.50  tff(c_588, plain, (![A_161, A_162]: (k7_partfun1(A_161, '#skF_5', k1_funct_1('#skF_4', A_162))=k1_funct_1('#skF_5', k1_funct_1('#skF_4', A_162)) | ~v5_relat_1('#skF_5', A_161) | ~m1_subset_1(A_162, '#skF_2'))), inference(splitRight, [status(thm)], [c_565])).
% 3.21/1.50  tff(c_44, plain, (k7_partfun1('#skF_1', '#skF_5', k1_funct_1('#skF_4', '#skF_6'))!=k1_funct_1(k8_funct_2('#skF_2', '#skF_3', '#skF_1', '#skF_4', '#skF_5'), '#skF_6')), inference(cnfTransformation, [status(thm)], [f_187])).
% 3.21/1.50  tff(c_594, plain, (k1_funct_1(k8_funct_2('#skF_2', '#skF_3', '#skF_1', '#skF_4', '#skF_5'), '#skF_6')!=k1_funct_1('#skF_5', k1_funct_1('#skF_4', '#skF_6')) | ~v5_relat_1('#skF_5', '#skF_1') | ~m1_subset_1('#skF_6', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_588, c_44])).
% 3.21/1.50  tff(c_600, plain, (k1_funct_1(k8_funct_2('#skF_2', '#skF_3', '#skF_1', '#skF_4', '#skF_5'), '#skF_6')!=k1_funct_1('#skF_5', k1_funct_1('#skF_4', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_91, c_594])).
% 3.21/1.50  tff(c_610, plain, (~m1_subset_1('#skF_6', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_444, c_600])).
% 3.21/1.50  tff(c_614, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_50, c_610])).
% 3.21/1.50  tff(c_615, plain, (v1_xboole_0('#skF_4')), inference(splitRight, [status(thm)], [c_238])).
% 3.21/1.50  tff(c_622, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_615, c_4])).
% 3.21/1.50  tff(c_628, plain, ('#skF_2'!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_622, c_46])).
% 3.21/1.50  tff(c_674, plain, (![C_176, A_177, B_178]: (~v1_xboole_0(C_176) | ~v1_funct_2(C_176, A_177, B_178) | ~v1_funct_1(C_176) | ~m1_subset_1(C_176, k1_zfmisc_1(k2_zfmisc_1(A_177, B_178))) | v1_xboole_0(B_178) | v1_xboole_0(A_177))), inference(cnfTransformation, [status(thm)], [f_115])).
% 3.21/1.50  tff(c_686, plain, (~v1_xboole_0('#skF_4') | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3') | ~v1_funct_1('#skF_4') | v1_xboole_0('#skF_3') | v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_56, c_674])).
% 3.21/1.50  tff(c_700, plain, (v1_xboole_0('#skF_3') | v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_615, c_686])).
% 3.21/1.50  tff(c_701, plain, (v1_xboole_0('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_62, c_700])).
% 3.21/1.50  tff(c_625, plain, (![A_1]: (A_1='#skF_4' | ~v1_xboole_0(A_1))), inference(demodulation, [status(thm), theory('equality')], [c_622, c_4])).
% 3.21/1.50  tff(c_704, plain, ('#skF_2'='#skF_4'), inference(resolution, [status(thm)], [c_701, c_625])).
% 3.21/1.50  tff(c_711, plain, $false, inference(negUnitSimplification, [status(thm)], [c_628, c_704])).
% 3.21/1.50  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.21/1.50  
% 3.21/1.50  Inference rules
% 3.21/1.50  ----------------------
% 3.21/1.50  #Ref     : 0
% 3.21/1.50  #Sup     : 128
% 3.21/1.50  #Fact    : 0
% 3.21/1.50  #Define  : 0
% 3.21/1.50  #Split   : 9
% 3.21/1.50  #Chain   : 0
% 3.21/1.50  #Close   : 0
% 3.21/1.50  
% 3.21/1.50  Ordering : KBO
% 3.21/1.50  
% 3.21/1.50  Simplification rules
% 3.21/1.50  ----------------------
% 3.21/1.50  #Subsume      : 13
% 3.21/1.50  #Demod        : 119
% 3.21/1.50  #Tautology    : 52
% 3.21/1.50  #SimpNegUnit  : 22
% 3.21/1.50  #BackRed      : 32
% 3.21/1.50  
% 3.21/1.50  #Partial instantiations: 0
% 3.21/1.50  #Strategies tried      : 1
% 3.21/1.50  
% 3.21/1.50  Timing (in seconds)
% 3.21/1.50  ----------------------
% 3.21/1.50  Preprocessing        : 0.34
% 3.21/1.50  Parsing              : 0.18
% 3.21/1.50  CNF conversion       : 0.03
% 3.21/1.50  Main loop            : 0.36
% 3.21/1.50  Inferencing          : 0.13
% 3.21/1.50  Reduction            : 0.12
% 3.21/1.50  Demodulation         : 0.08
% 3.21/1.50  BG Simplification    : 0.02
% 3.21/1.50  Subsumption          : 0.06
% 3.21/1.50  Abstraction          : 0.02
% 3.21/1.50  MUC search           : 0.00
% 3.21/1.50  Cooper               : 0.00
% 3.21/1.50  Total                : 0.75
% 3.21/1.50  Index Insertion      : 0.00
% 3.21/1.50  Index Deletion       : 0.00
% 3.21/1.50  Index Matching       : 0.00
% 3.21/1.50  BG Taut test         : 0.00
%------------------------------------------------------------------------------
