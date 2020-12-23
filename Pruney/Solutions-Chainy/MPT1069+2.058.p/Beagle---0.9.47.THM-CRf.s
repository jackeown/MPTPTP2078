%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:17:53 EST 2020

% Result     : Theorem 4.72s
% Output     : CNFRefutation 4.72s
% Verified   : 
% Statistics : Number of formulae       :  112 ( 334 expanded)
%              Number of leaves         :   43 ( 135 expanded)
%              Depth                    :   14
%              Number of atoms          :  229 (1128 expanded)
%              Number of equality atoms :   51 ( 257 expanded)
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

tff(f_160,negated_conjecture,(
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

tff(f_78,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_82,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_135,axiom,(
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

tff(f_51,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_43,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_100,axiom,(
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

tff(f_111,axiom,(
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

tff(f_74,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_68,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r2_hidden(A,k1_relat_1(B))
       => r2_hidden(k1_funct_1(B,A),k2_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_funct_1)).

tff(f_60,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A) )
     => ! [C] :
          ( r2_hidden(C,k2_relat_1(B))
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t202_relat_1)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(c_62,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_50,plain,(
    m1_subset_1('#skF_6','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_54,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_52,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_138,plain,(
    ! [A_85,B_86,C_87] :
      ( k1_relset_1(A_85,B_86,C_87) = k1_relat_1(C_87)
      | ~ m1_subset_1(C_87,k1_zfmisc_1(k2_zfmisc_1(A_85,B_86))) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_146,plain,(
    k1_relset_1('#skF_3','#skF_1','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_52,c_138])).

tff(c_56,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_109,plain,(
    ! [A_79,B_80,C_81] :
      ( k2_relset_1(A_79,B_80,C_81) = k2_relat_1(C_81)
      | ~ m1_subset_1(C_81,k1_zfmisc_1(k2_zfmisc_1(A_79,B_80))) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_116,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_56,c_109])).

tff(c_48,plain,(
    r1_tarski(k2_relset_1('#skF_2','#skF_3','#skF_4'),k1_relset_1('#skF_3','#skF_1','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_118,plain,(
    r1_tarski(k2_relat_1('#skF_4'),k1_relset_1('#skF_3','#skF_1','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_116,c_48])).

tff(c_152,plain,(
    r1_tarski(k2_relat_1('#skF_4'),k1_relat_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_146,c_118])).

tff(c_46,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_60,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_58,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_951,plain,(
    ! [B_204,C_201,E_203,D_202,A_199,F_200] :
      ( k1_funct_1(k8_funct_2(B_204,C_201,A_199,D_202,E_203),F_200) = k1_funct_1(E_203,k1_funct_1(D_202,F_200))
      | k1_xboole_0 = B_204
      | ~ r1_tarski(k2_relset_1(B_204,C_201,D_202),k1_relset_1(C_201,A_199,E_203))
      | ~ m1_subset_1(F_200,B_204)
      | ~ m1_subset_1(E_203,k1_zfmisc_1(k2_zfmisc_1(C_201,A_199)))
      | ~ v1_funct_1(E_203)
      | ~ m1_subset_1(D_202,k1_zfmisc_1(k2_zfmisc_1(B_204,C_201)))
      | ~ v1_funct_2(D_202,B_204,C_201)
      | ~ v1_funct_1(D_202)
      | v1_xboole_0(C_201) ) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_959,plain,(
    ! [A_199,E_203,F_200] :
      ( k1_funct_1(k8_funct_2('#skF_2','#skF_3',A_199,'#skF_4',E_203),F_200) = k1_funct_1(E_203,k1_funct_1('#skF_4',F_200))
      | k1_xboole_0 = '#skF_2'
      | ~ r1_tarski(k2_relat_1('#skF_4'),k1_relset_1('#skF_3',A_199,E_203))
      | ~ m1_subset_1(F_200,'#skF_2')
      | ~ m1_subset_1(E_203,k1_zfmisc_1(k2_zfmisc_1('#skF_3',A_199)))
      | ~ v1_funct_1(E_203)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
      | ~ v1_funct_2('#skF_4','#skF_2','#skF_3')
      | ~ v1_funct_1('#skF_4')
      | v1_xboole_0('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_116,c_951])).

tff(c_969,plain,(
    ! [A_199,E_203,F_200] :
      ( k1_funct_1(k8_funct_2('#skF_2','#skF_3',A_199,'#skF_4',E_203),F_200) = k1_funct_1(E_203,k1_funct_1('#skF_4',F_200))
      | k1_xboole_0 = '#skF_2'
      | ~ r1_tarski(k2_relat_1('#skF_4'),k1_relset_1('#skF_3',A_199,E_203))
      | ~ m1_subset_1(F_200,'#skF_2')
      | ~ m1_subset_1(E_203,k1_zfmisc_1(k2_zfmisc_1('#skF_3',A_199)))
      | ~ v1_funct_1(E_203)
      | v1_xboole_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_56,c_959])).

tff(c_988,plain,(
    ! [A_209,E_210,F_211] :
      ( k1_funct_1(k8_funct_2('#skF_2','#skF_3',A_209,'#skF_4',E_210),F_211) = k1_funct_1(E_210,k1_funct_1('#skF_4',F_211))
      | ~ r1_tarski(k2_relat_1('#skF_4'),k1_relset_1('#skF_3',A_209,E_210))
      | ~ m1_subset_1(F_211,'#skF_2')
      | ~ m1_subset_1(E_210,k1_zfmisc_1(k2_zfmisc_1('#skF_3',A_209)))
      | ~ v1_funct_1(E_210) ) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_46,c_969])).

tff(c_990,plain,(
    ! [F_211] :
      ( k1_funct_1(k8_funct_2('#skF_2','#skF_3','#skF_1','#skF_4','#skF_5'),F_211) = k1_funct_1('#skF_5',k1_funct_1('#skF_4',F_211))
      | ~ r1_tarski(k2_relat_1('#skF_4'),k1_relat_1('#skF_5'))
      | ~ m1_subset_1(F_211,'#skF_2')
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_1')))
      | ~ v1_funct_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_146,c_988])).

tff(c_995,plain,(
    ! [F_211] :
      ( k1_funct_1(k8_funct_2('#skF_2','#skF_3','#skF_1','#skF_4','#skF_5'),F_211) = k1_funct_1('#skF_5',k1_funct_1('#skF_4',F_211))
      | ~ m1_subset_1(F_211,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_152,c_990])).

tff(c_6,plain,(
    ! [A_2,B_3] :
      ( r2_hidden(A_2,B_3)
      | v1_xboole_0(B_3)
      | ~ m1_subset_1(A_2,B_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_14,plain,(
    ! [A_9,B_10] : v1_relat_1(k2_zfmisc_1(A_9,B_10)) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_70,plain,(
    ! [B_64,A_65] :
      ( v1_relat_1(B_64)
      | ~ m1_subset_1(B_64,k1_zfmisc_1(A_65))
      | ~ v1_relat_1(A_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_73,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_56,c_70])).

tff(c_79,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_73])).

tff(c_145,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_56,c_138])).

tff(c_217,plain,(
    ! [B_99,A_100,C_101] :
      ( k1_xboole_0 = B_99
      | k1_relset_1(A_100,B_99,C_101) = A_100
      | ~ v1_funct_2(C_101,A_100,B_99)
      | ~ m1_subset_1(C_101,k1_zfmisc_1(k2_zfmisc_1(A_100,B_99))) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_220,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relset_1('#skF_2','#skF_3','#skF_4') = '#skF_2'
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_56,c_217])).

tff(c_226,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relat_1('#skF_4') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_145,c_220])).

tff(c_229,plain,(
    k1_relat_1('#skF_4') = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_226])).

tff(c_887,plain,(
    ! [A_188,B_189,C_190] :
      ( k7_partfun1(A_188,B_189,C_190) = k1_funct_1(B_189,C_190)
      | ~ r2_hidden(C_190,k1_relat_1(B_189))
      | ~ v1_funct_1(B_189)
      | ~ v5_relat_1(B_189,A_188)
      | ~ v1_relat_1(B_189) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_889,plain,(
    ! [A_188,C_190] :
      ( k7_partfun1(A_188,'#skF_4',C_190) = k1_funct_1('#skF_4',C_190)
      | ~ r2_hidden(C_190,'#skF_2')
      | ~ v1_funct_1('#skF_4')
      | ~ v5_relat_1('#skF_4',A_188)
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_229,c_887])).

tff(c_916,plain,(
    ! [A_194,C_195] :
      ( k7_partfun1(A_194,'#skF_4',C_195) = k1_funct_1('#skF_4',C_195)
      | ~ r2_hidden(C_195,'#skF_2')
      | ~ v5_relat_1('#skF_4',A_194) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_79,c_60,c_889])).

tff(c_924,plain,(
    ! [A_194,A_2] :
      ( k7_partfun1(A_194,'#skF_4',A_2) = k1_funct_1('#skF_4',A_2)
      | ~ v5_relat_1('#skF_4',A_194)
      | v1_xboole_0('#skF_2')
      | ~ m1_subset_1(A_2,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_6,c_916])).

tff(c_925,plain,(
    v1_xboole_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_924])).

tff(c_4,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_928,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_925,c_4])).

tff(c_932,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_928])).

tff(c_934,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_924])).

tff(c_93,plain,(
    ! [C_71,B_72,A_73] :
      ( v5_relat_1(C_71,B_72)
      | ~ m1_subset_1(C_71,k1_zfmisc_1(k2_zfmisc_1(A_73,B_72))) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_101,plain,(
    v5_relat_1('#skF_5','#skF_1') ),
    inference(resolution,[status(thm)],[c_52,c_93])).

tff(c_76,plain,
    ( v1_relat_1('#skF_5')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_3','#skF_1')) ),
    inference(resolution,[status(thm)],[c_52,c_70])).

tff(c_82,plain,(
    v1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_76])).

tff(c_10,plain,(
    ! [B_8,A_7] :
      ( v5_relat_1(B_8,A_7)
      | ~ r1_tarski(k2_relat_1(B_8),A_7)
      | ~ v1_relat_1(B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_129,plain,
    ( v5_relat_1('#skF_4',k1_relset_1('#skF_3','#skF_1','#skF_5'))
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_118,c_10])).

tff(c_132,plain,(
    v5_relat_1('#skF_4',k1_relset_1('#skF_3','#skF_1','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_79,c_129])).

tff(c_151,plain,(
    v5_relat_1('#skF_4',k1_relat_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_146,c_132])).

tff(c_157,plain,(
    ! [B_88,A_89] :
      ( r2_hidden(k1_funct_1(B_88,A_89),k2_relat_1(B_88))
      | ~ r2_hidden(A_89,k1_relat_1(B_88))
      | ~ v1_funct_1(B_88)
      | ~ v1_relat_1(B_88) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_16,plain,(
    ! [C_14,A_11,B_12] :
      ( r2_hidden(C_14,A_11)
      | ~ r2_hidden(C_14,k2_relat_1(B_12))
      | ~ v5_relat_1(B_12,A_11)
      | ~ v1_relat_1(B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_1000,plain,(
    ! [B_214,A_215,A_216] :
      ( r2_hidden(k1_funct_1(B_214,A_215),A_216)
      | ~ v5_relat_1(B_214,A_216)
      | ~ r2_hidden(A_215,k1_relat_1(B_214))
      | ~ v1_funct_1(B_214)
      | ~ v1_relat_1(B_214) ) ),
    inference(resolution,[status(thm)],[c_157,c_16])).

tff(c_40,plain,(
    ! [A_29,B_30,C_32] :
      ( k7_partfun1(A_29,B_30,C_32) = k1_funct_1(B_30,C_32)
      | ~ r2_hidden(C_32,k1_relat_1(B_30))
      | ~ v1_funct_1(B_30)
      | ~ v5_relat_1(B_30,A_29)
      | ~ v1_relat_1(B_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_1552,plain,(
    ! [A_299,B_300,B_301,A_302] :
      ( k7_partfun1(A_299,B_300,k1_funct_1(B_301,A_302)) = k1_funct_1(B_300,k1_funct_1(B_301,A_302))
      | ~ v1_funct_1(B_300)
      | ~ v5_relat_1(B_300,A_299)
      | ~ v1_relat_1(B_300)
      | ~ v5_relat_1(B_301,k1_relat_1(B_300))
      | ~ r2_hidden(A_302,k1_relat_1(B_301))
      | ~ v1_funct_1(B_301)
      | ~ v1_relat_1(B_301) ) ),
    inference(resolution,[status(thm)],[c_1000,c_40])).

tff(c_1559,plain,(
    ! [A_299,A_302] :
      ( k7_partfun1(A_299,'#skF_5',k1_funct_1('#skF_4',A_302)) = k1_funct_1('#skF_5',k1_funct_1('#skF_4',A_302))
      | ~ v1_funct_1('#skF_5')
      | ~ v5_relat_1('#skF_5',A_299)
      | ~ v1_relat_1('#skF_5')
      | ~ r2_hidden(A_302,k1_relat_1('#skF_4'))
      | ~ v1_funct_1('#skF_4')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_151,c_1552])).

tff(c_1572,plain,(
    ! [A_303,A_304] :
      ( k7_partfun1(A_303,'#skF_5',k1_funct_1('#skF_4',A_304)) = k1_funct_1('#skF_5',k1_funct_1('#skF_4',A_304))
      | ~ v5_relat_1('#skF_5',A_303)
      | ~ r2_hidden(A_304,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_79,c_60,c_229,c_82,c_54,c_1559])).

tff(c_44,plain,(
    k7_partfun1('#skF_1','#skF_5',k1_funct_1('#skF_4','#skF_6')) != k1_funct_1(k8_funct_2('#skF_2','#skF_3','#skF_1','#skF_4','#skF_5'),'#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_1578,plain,
    ( k1_funct_1(k8_funct_2('#skF_2','#skF_3','#skF_1','#skF_4','#skF_5'),'#skF_6') != k1_funct_1('#skF_5',k1_funct_1('#skF_4','#skF_6'))
    | ~ v5_relat_1('#skF_5','#skF_1')
    | ~ r2_hidden('#skF_6','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_1572,c_44])).

tff(c_1584,plain,
    ( k1_funct_1(k8_funct_2('#skF_2','#skF_3','#skF_1','#skF_4','#skF_5'),'#skF_6') != k1_funct_1('#skF_5',k1_funct_1('#skF_4','#skF_6'))
    | ~ r2_hidden('#skF_6','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_101,c_1578])).

tff(c_1586,plain,(
    ~ r2_hidden('#skF_6','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_1584])).

tff(c_1589,plain,
    ( v1_xboole_0('#skF_2')
    | ~ m1_subset_1('#skF_6','#skF_2') ),
    inference(resolution,[status(thm)],[c_6,c_1586])).

tff(c_1592,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_1589])).

tff(c_1594,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_934,c_1592])).

tff(c_1595,plain,(
    k1_funct_1(k8_funct_2('#skF_2','#skF_3','#skF_1','#skF_4','#skF_5'),'#skF_6') != k1_funct_1('#skF_5',k1_funct_1('#skF_4','#skF_6')) ),
    inference(splitRight,[status(thm)],[c_1584])).

tff(c_1628,plain,(
    ~ m1_subset_1('#skF_6','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_995,c_1595])).

tff(c_1632,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_1628])).

tff(c_1633,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_226])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_1654,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1633,c_2])).

tff(c_1657,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_1654])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n011.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 13:08:27 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.72/1.83  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.72/1.83  
% 4.72/1.83  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.72/1.84  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k8_funct_2 > k7_partfun1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 4.72/1.84  
% 4.72/1.84  %Foreground sorts:
% 4.72/1.84  
% 4.72/1.84  
% 4.72/1.84  %Background operators:
% 4.72/1.84  
% 4.72/1.84  
% 4.72/1.84  %Foreground operators:
% 4.72/1.84  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 4.72/1.84  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.72/1.84  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.72/1.84  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.72/1.84  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.72/1.84  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.72/1.84  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 4.72/1.84  tff(k7_partfun1, type, k7_partfun1: ($i * $i * $i) > $i).
% 4.72/1.84  tff('#skF_5', type, '#skF_5': $i).
% 4.72/1.84  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.72/1.84  tff(k8_funct_2, type, k8_funct_2: ($i * $i * $i * $i * $i) > $i).
% 4.72/1.84  tff('#skF_6', type, '#skF_6': $i).
% 4.72/1.84  tff('#skF_2', type, '#skF_2': $i).
% 4.72/1.84  tff('#skF_3', type, '#skF_3': $i).
% 4.72/1.84  tff('#skF_1', type, '#skF_1': $i).
% 4.72/1.84  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 4.72/1.84  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 4.72/1.84  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.72/1.84  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 4.72/1.84  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.72/1.84  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.72/1.84  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.72/1.84  tff('#skF_4', type, '#skF_4': $i).
% 4.72/1.84  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.72/1.84  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 4.72/1.84  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.72/1.84  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.72/1.84  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.72/1.84  
% 4.72/1.86  tff(f_160, negated_conjecture, ~(![A, B, C]: (~v1_xboole_0(C) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, C)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (![E]: ((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(C, A)))) => (![F]: (m1_subset_1(F, B) => (r1_tarski(k2_relset_1(B, C, D), k1_relset_1(C, A, E)) => ((B = k1_xboole_0) | (k1_funct_1(k8_funct_2(B, C, A, D, E), F) = k7_partfun1(A, E, k1_funct_1(D, F))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t186_funct_2)).
% 4.72/1.86  tff(f_78, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 4.72/1.86  tff(f_82, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 4.72/1.86  tff(f_135, axiom, (![A, B, C]: (~v1_xboole_0(C) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, C)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (![E]: ((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(C, A)))) => (![F]: (m1_subset_1(F, B) => (r1_tarski(k2_relset_1(B, C, D), k1_relset_1(C, A, E)) => ((B = k1_xboole_0) | (k1_funct_1(k8_funct_2(B, C, A, D, E), F) = k1_funct_1(E, k1_funct_1(D, F))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t185_funct_2)).
% 4.72/1.86  tff(f_36, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 4.72/1.86  tff(f_51, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 4.72/1.86  tff(f_43, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 4.72/1.86  tff(f_100, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 4.72/1.86  tff(f_111, axiom, (![A, B]: (((v1_relat_1(B) & v5_relat_1(B, A)) & v1_funct_1(B)) => (![C]: (r2_hidden(C, k1_relat_1(B)) => (k7_partfun1(A, B, C) = k1_funct_1(B, C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_partfun1)).
% 4.72/1.86  tff(f_30, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 4.72/1.86  tff(f_74, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 4.72/1.86  tff(f_49, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 4.72/1.86  tff(f_68, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r2_hidden(A, k1_relat_1(B)) => r2_hidden(k1_funct_1(B, A), k2_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_funct_1)).
% 4.72/1.86  tff(f_60, axiom, (![A, B]: ((v1_relat_1(B) & v5_relat_1(B, A)) => (![C]: (r2_hidden(C, k2_relat_1(B)) => r2_hidden(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t202_relat_1)).
% 4.72/1.86  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 4.72/1.86  tff(c_62, plain, (~v1_xboole_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_160])).
% 4.72/1.86  tff(c_50, plain, (m1_subset_1('#skF_6', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_160])).
% 4.72/1.86  tff(c_54, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_160])).
% 4.72/1.86  tff(c_52, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_160])).
% 4.72/1.86  tff(c_138, plain, (![A_85, B_86, C_87]: (k1_relset_1(A_85, B_86, C_87)=k1_relat_1(C_87) | ~m1_subset_1(C_87, k1_zfmisc_1(k2_zfmisc_1(A_85, B_86))))), inference(cnfTransformation, [status(thm)], [f_78])).
% 4.72/1.86  tff(c_146, plain, (k1_relset_1('#skF_3', '#skF_1', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_52, c_138])).
% 4.72/1.86  tff(c_56, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_160])).
% 4.72/1.86  tff(c_109, plain, (![A_79, B_80, C_81]: (k2_relset_1(A_79, B_80, C_81)=k2_relat_1(C_81) | ~m1_subset_1(C_81, k1_zfmisc_1(k2_zfmisc_1(A_79, B_80))))), inference(cnfTransformation, [status(thm)], [f_82])).
% 4.72/1.86  tff(c_116, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_56, c_109])).
% 4.72/1.86  tff(c_48, plain, (r1_tarski(k2_relset_1('#skF_2', '#skF_3', '#skF_4'), k1_relset_1('#skF_3', '#skF_1', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_160])).
% 4.72/1.86  tff(c_118, plain, (r1_tarski(k2_relat_1('#skF_4'), k1_relset_1('#skF_3', '#skF_1', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_116, c_48])).
% 4.72/1.86  tff(c_152, plain, (r1_tarski(k2_relat_1('#skF_4'), k1_relat_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_146, c_118])).
% 4.72/1.86  tff(c_46, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_160])).
% 4.72/1.86  tff(c_60, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_160])).
% 4.72/1.86  tff(c_58, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_160])).
% 4.72/1.86  tff(c_951, plain, (![B_204, C_201, E_203, D_202, A_199, F_200]: (k1_funct_1(k8_funct_2(B_204, C_201, A_199, D_202, E_203), F_200)=k1_funct_1(E_203, k1_funct_1(D_202, F_200)) | k1_xboole_0=B_204 | ~r1_tarski(k2_relset_1(B_204, C_201, D_202), k1_relset_1(C_201, A_199, E_203)) | ~m1_subset_1(F_200, B_204) | ~m1_subset_1(E_203, k1_zfmisc_1(k2_zfmisc_1(C_201, A_199))) | ~v1_funct_1(E_203) | ~m1_subset_1(D_202, k1_zfmisc_1(k2_zfmisc_1(B_204, C_201))) | ~v1_funct_2(D_202, B_204, C_201) | ~v1_funct_1(D_202) | v1_xboole_0(C_201))), inference(cnfTransformation, [status(thm)], [f_135])).
% 4.72/1.86  tff(c_959, plain, (![A_199, E_203, F_200]: (k1_funct_1(k8_funct_2('#skF_2', '#skF_3', A_199, '#skF_4', E_203), F_200)=k1_funct_1(E_203, k1_funct_1('#skF_4', F_200)) | k1_xboole_0='#skF_2' | ~r1_tarski(k2_relat_1('#skF_4'), k1_relset_1('#skF_3', A_199, E_203)) | ~m1_subset_1(F_200, '#skF_2') | ~m1_subset_1(E_203, k1_zfmisc_1(k2_zfmisc_1('#skF_3', A_199))) | ~v1_funct_1(E_203) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3') | ~v1_funct_1('#skF_4') | v1_xboole_0('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_116, c_951])).
% 4.72/1.86  tff(c_969, plain, (![A_199, E_203, F_200]: (k1_funct_1(k8_funct_2('#skF_2', '#skF_3', A_199, '#skF_4', E_203), F_200)=k1_funct_1(E_203, k1_funct_1('#skF_4', F_200)) | k1_xboole_0='#skF_2' | ~r1_tarski(k2_relat_1('#skF_4'), k1_relset_1('#skF_3', A_199, E_203)) | ~m1_subset_1(F_200, '#skF_2') | ~m1_subset_1(E_203, k1_zfmisc_1(k2_zfmisc_1('#skF_3', A_199))) | ~v1_funct_1(E_203) | v1_xboole_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_56, c_959])).
% 4.72/1.86  tff(c_988, plain, (![A_209, E_210, F_211]: (k1_funct_1(k8_funct_2('#skF_2', '#skF_3', A_209, '#skF_4', E_210), F_211)=k1_funct_1(E_210, k1_funct_1('#skF_4', F_211)) | ~r1_tarski(k2_relat_1('#skF_4'), k1_relset_1('#skF_3', A_209, E_210)) | ~m1_subset_1(F_211, '#skF_2') | ~m1_subset_1(E_210, k1_zfmisc_1(k2_zfmisc_1('#skF_3', A_209))) | ~v1_funct_1(E_210))), inference(negUnitSimplification, [status(thm)], [c_62, c_46, c_969])).
% 4.72/1.86  tff(c_990, plain, (![F_211]: (k1_funct_1(k8_funct_2('#skF_2', '#skF_3', '#skF_1', '#skF_4', '#skF_5'), F_211)=k1_funct_1('#skF_5', k1_funct_1('#skF_4', F_211)) | ~r1_tarski(k2_relat_1('#skF_4'), k1_relat_1('#skF_5')) | ~m1_subset_1(F_211, '#skF_2') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_1'))) | ~v1_funct_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_146, c_988])).
% 4.72/1.86  tff(c_995, plain, (![F_211]: (k1_funct_1(k8_funct_2('#skF_2', '#skF_3', '#skF_1', '#skF_4', '#skF_5'), F_211)=k1_funct_1('#skF_5', k1_funct_1('#skF_4', F_211)) | ~m1_subset_1(F_211, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_152, c_990])).
% 4.72/1.86  tff(c_6, plain, (![A_2, B_3]: (r2_hidden(A_2, B_3) | v1_xboole_0(B_3) | ~m1_subset_1(A_2, B_3))), inference(cnfTransformation, [status(thm)], [f_36])).
% 4.72/1.86  tff(c_14, plain, (![A_9, B_10]: (v1_relat_1(k2_zfmisc_1(A_9, B_10)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 4.72/1.86  tff(c_70, plain, (![B_64, A_65]: (v1_relat_1(B_64) | ~m1_subset_1(B_64, k1_zfmisc_1(A_65)) | ~v1_relat_1(A_65))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.72/1.86  tff(c_73, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_56, c_70])).
% 4.72/1.86  tff(c_79, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_14, c_73])).
% 4.72/1.86  tff(c_145, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_56, c_138])).
% 4.72/1.86  tff(c_217, plain, (![B_99, A_100, C_101]: (k1_xboole_0=B_99 | k1_relset_1(A_100, B_99, C_101)=A_100 | ~v1_funct_2(C_101, A_100, B_99) | ~m1_subset_1(C_101, k1_zfmisc_1(k2_zfmisc_1(A_100, B_99))))), inference(cnfTransformation, [status(thm)], [f_100])).
% 4.72/1.86  tff(c_220, plain, (k1_xboole_0='#skF_3' | k1_relset_1('#skF_2', '#skF_3', '#skF_4')='#skF_2' | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_56, c_217])).
% 4.72/1.86  tff(c_226, plain, (k1_xboole_0='#skF_3' | k1_relat_1('#skF_4')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_58, c_145, c_220])).
% 4.72/1.86  tff(c_229, plain, (k1_relat_1('#skF_4')='#skF_2'), inference(splitLeft, [status(thm)], [c_226])).
% 4.72/1.86  tff(c_887, plain, (![A_188, B_189, C_190]: (k7_partfun1(A_188, B_189, C_190)=k1_funct_1(B_189, C_190) | ~r2_hidden(C_190, k1_relat_1(B_189)) | ~v1_funct_1(B_189) | ~v5_relat_1(B_189, A_188) | ~v1_relat_1(B_189))), inference(cnfTransformation, [status(thm)], [f_111])).
% 4.72/1.86  tff(c_889, plain, (![A_188, C_190]: (k7_partfun1(A_188, '#skF_4', C_190)=k1_funct_1('#skF_4', C_190) | ~r2_hidden(C_190, '#skF_2') | ~v1_funct_1('#skF_4') | ~v5_relat_1('#skF_4', A_188) | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_229, c_887])).
% 4.72/1.86  tff(c_916, plain, (![A_194, C_195]: (k7_partfun1(A_194, '#skF_4', C_195)=k1_funct_1('#skF_4', C_195) | ~r2_hidden(C_195, '#skF_2') | ~v5_relat_1('#skF_4', A_194))), inference(demodulation, [status(thm), theory('equality')], [c_79, c_60, c_889])).
% 4.72/1.86  tff(c_924, plain, (![A_194, A_2]: (k7_partfun1(A_194, '#skF_4', A_2)=k1_funct_1('#skF_4', A_2) | ~v5_relat_1('#skF_4', A_194) | v1_xboole_0('#skF_2') | ~m1_subset_1(A_2, '#skF_2'))), inference(resolution, [status(thm)], [c_6, c_916])).
% 4.72/1.86  tff(c_925, plain, (v1_xboole_0('#skF_2')), inference(splitLeft, [status(thm)], [c_924])).
% 4.72/1.86  tff(c_4, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_30])).
% 4.72/1.86  tff(c_928, plain, (k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_925, c_4])).
% 4.72/1.86  tff(c_932, plain, $false, inference(negUnitSimplification, [status(thm)], [c_46, c_928])).
% 4.72/1.86  tff(c_934, plain, (~v1_xboole_0('#skF_2')), inference(splitRight, [status(thm)], [c_924])).
% 4.72/1.86  tff(c_93, plain, (![C_71, B_72, A_73]: (v5_relat_1(C_71, B_72) | ~m1_subset_1(C_71, k1_zfmisc_1(k2_zfmisc_1(A_73, B_72))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 4.72/1.86  tff(c_101, plain, (v5_relat_1('#skF_5', '#skF_1')), inference(resolution, [status(thm)], [c_52, c_93])).
% 4.72/1.86  tff(c_76, plain, (v1_relat_1('#skF_5') | ~v1_relat_1(k2_zfmisc_1('#skF_3', '#skF_1'))), inference(resolution, [status(thm)], [c_52, c_70])).
% 4.72/1.86  tff(c_82, plain, (v1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_14, c_76])).
% 4.72/1.86  tff(c_10, plain, (![B_8, A_7]: (v5_relat_1(B_8, A_7) | ~r1_tarski(k2_relat_1(B_8), A_7) | ~v1_relat_1(B_8))), inference(cnfTransformation, [status(thm)], [f_49])).
% 4.72/1.86  tff(c_129, plain, (v5_relat_1('#skF_4', k1_relset_1('#skF_3', '#skF_1', '#skF_5')) | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_118, c_10])).
% 4.72/1.86  tff(c_132, plain, (v5_relat_1('#skF_4', k1_relset_1('#skF_3', '#skF_1', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_79, c_129])).
% 4.72/1.86  tff(c_151, plain, (v5_relat_1('#skF_4', k1_relat_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_146, c_132])).
% 4.72/1.86  tff(c_157, plain, (![B_88, A_89]: (r2_hidden(k1_funct_1(B_88, A_89), k2_relat_1(B_88)) | ~r2_hidden(A_89, k1_relat_1(B_88)) | ~v1_funct_1(B_88) | ~v1_relat_1(B_88))), inference(cnfTransformation, [status(thm)], [f_68])).
% 4.72/1.86  tff(c_16, plain, (![C_14, A_11, B_12]: (r2_hidden(C_14, A_11) | ~r2_hidden(C_14, k2_relat_1(B_12)) | ~v5_relat_1(B_12, A_11) | ~v1_relat_1(B_12))), inference(cnfTransformation, [status(thm)], [f_60])).
% 4.72/1.86  tff(c_1000, plain, (![B_214, A_215, A_216]: (r2_hidden(k1_funct_1(B_214, A_215), A_216) | ~v5_relat_1(B_214, A_216) | ~r2_hidden(A_215, k1_relat_1(B_214)) | ~v1_funct_1(B_214) | ~v1_relat_1(B_214))), inference(resolution, [status(thm)], [c_157, c_16])).
% 4.72/1.86  tff(c_40, plain, (![A_29, B_30, C_32]: (k7_partfun1(A_29, B_30, C_32)=k1_funct_1(B_30, C_32) | ~r2_hidden(C_32, k1_relat_1(B_30)) | ~v1_funct_1(B_30) | ~v5_relat_1(B_30, A_29) | ~v1_relat_1(B_30))), inference(cnfTransformation, [status(thm)], [f_111])).
% 4.72/1.86  tff(c_1552, plain, (![A_299, B_300, B_301, A_302]: (k7_partfun1(A_299, B_300, k1_funct_1(B_301, A_302))=k1_funct_1(B_300, k1_funct_1(B_301, A_302)) | ~v1_funct_1(B_300) | ~v5_relat_1(B_300, A_299) | ~v1_relat_1(B_300) | ~v5_relat_1(B_301, k1_relat_1(B_300)) | ~r2_hidden(A_302, k1_relat_1(B_301)) | ~v1_funct_1(B_301) | ~v1_relat_1(B_301))), inference(resolution, [status(thm)], [c_1000, c_40])).
% 4.72/1.86  tff(c_1559, plain, (![A_299, A_302]: (k7_partfun1(A_299, '#skF_5', k1_funct_1('#skF_4', A_302))=k1_funct_1('#skF_5', k1_funct_1('#skF_4', A_302)) | ~v1_funct_1('#skF_5') | ~v5_relat_1('#skF_5', A_299) | ~v1_relat_1('#skF_5') | ~r2_hidden(A_302, k1_relat_1('#skF_4')) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_151, c_1552])).
% 4.72/1.86  tff(c_1572, plain, (![A_303, A_304]: (k7_partfun1(A_303, '#skF_5', k1_funct_1('#skF_4', A_304))=k1_funct_1('#skF_5', k1_funct_1('#skF_4', A_304)) | ~v5_relat_1('#skF_5', A_303) | ~r2_hidden(A_304, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_79, c_60, c_229, c_82, c_54, c_1559])).
% 4.72/1.86  tff(c_44, plain, (k7_partfun1('#skF_1', '#skF_5', k1_funct_1('#skF_4', '#skF_6'))!=k1_funct_1(k8_funct_2('#skF_2', '#skF_3', '#skF_1', '#skF_4', '#skF_5'), '#skF_6')), inference(cnfTransformation, [status(thm)], [f_160])).
% 4.72/1.86  tff(c_1578, plain, (k1_funct_1(k8_funct_2('#skF_2', '#skF_3', '#skF_1', '#skF_4', '#skF_5'), '#skF_6')!=k1_funct_1('#skF_5', k1_funct_1('#skF_4', '#skF_6')) | ~v5_relat_1('#skF_5', '#skF_1') | ~r2_hidden('#skF_6', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_1572, c_44])).
% 4.72/1.86  tff(c_1584, plain, (k1_funct_1(k8_funct_2('#skF_2', '#skF_3', '#skF_1', '#skF_4', '#skF_5'), '#skF_6')!=k1_funct_1('#skF_5', k1_funct_1('#skF_4', '#skF_6')) | ~r2_hidden('#skF_6', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_101, c_1578])).
% 4.72/1.86  tff(c_1586, plain, (~r2_hidden('#skF_6', '#skF_2')), inference(splitLeft, [status(thm)], [c_1584])).
% 4.72/1.86  tff(c_1589, plain, (v1_xboole_0('#skF_2') | ~m1_subset_1('#skF_6', '#skF_2')), inference(resolution, [status(thm)], [c_6, c_1586])).
% 4.72/1.86  tff(c_1592, plain, (v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_1589])).
% 4.72/1.86  tff(c_1594, plain, $false, inference(negUnitSimplification, [status(thm)], [c_934, c_1592])).
% 4.72/1.86  tff(c_1595, plain, (k1_funct_1(k8_funct_2('#skF_2', '#skF_3', '#skF_1', '#skF_4', '#skF_5'), '#skF_6')!=k1_funct_1('#skF_5', k1_funct_1('#skF_4', '#skF_6'))), inference(splitRight, [status(thm)], [c_1584])).
% 4.72/1.86  tff(c_1628, plain, (~m1_subset_1('#skF_6', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_995, c_1595])).
% 4.72/1.86  tff(c_1632, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_50, c_1628])).
% 4.72/1.86  tff(c_1633, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_226])).
% 4.72/1.86  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 4.72/1.86  tff(c_1654, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1633, c_2])).
% 4.72/1.86  tff(c_1657, plain, $false, inference(negUnitSimplification, [status(thm)], [c_62, c_1654])).
% 4.72/1.86  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.72/1.86  
% 4.72/1.86  Inference rules
% 4.72/1.86  ----------------------
% 4.72/1.86  #Ref     : 0
% 4.72/1.86  #Sup     : 331
% 4.72/1.86  #Fact    : 0
% 4.72/1.86  #Define  : 0
% 4.72/1.86  #Split   : 20
% 4.72/1.86  #Chain   : 0
% 4.72/1.86  #Close   : 0
% 4.72/1.86  
% 4.72/1.86  Ordering : KBO
% 4.72/1.86  
% 4.72/1.86  Simplification rules
% 4.72/1.86  ----------------------
% 4.72/1.86  #Subsume      : 74
% 4.72/1.86  #Demod        : 341
% 4.72/1.86  #Tautology    : 82
% 4.72/1.86  #SimpNegUnit  : 27
% 4.72/1.86  #BackRed      : 41
% 4.72/1.86  
% 4.72/1.86  #Partial instantiations: 0
% 4.72/1.86  #Strategies tried      : 1
% 4.72/1.86  
% 4.72/1.86  Timing (in seconds)
% 4.72/1.86  ----------------------
% 4.72/1.86  Preprocessing        : 0.37
% 4.72/1.86  Parsing              : 0.20
% 4.72/1.86  CNF conversion       : 0.03
% 4.72/1.86  Main loop            : 0.69
% 4.72/1.86  Inferencing          : 0.25
% 4.72/1.86  Reduction            : 0.22
% 4.72/1.86  Demodulation         : 0.15
% 4.72/1.86  BG Simplification    : 0.03
% 4.72/1.86  Subsumption          : 0.13
% 4.72/1.86  Abstraction          : 0.03
% 4.72/1.86  MUC search           : 0.00
% 4.72/1.86  Cooper               : 0.00
% 4.72/1.86  Total                : 1.11
% 4.72/1.86  Index Insertion      : 0.00
% 4.72/1.86  Index Deletion       : 0.00
% 4.72/1.86  Index Matching       : 0.00
% 4.72/1.86  BG Taut test         : 0.00
%------------------------------------------------------------------------------
