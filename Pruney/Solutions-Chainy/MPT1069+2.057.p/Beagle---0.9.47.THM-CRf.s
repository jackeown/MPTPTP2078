%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:17:53 EST 2020

% Result     : Theorem 3.28s
% Output     : CNFRefutation 3.28s
% Verified   : 
% Statistics : Number of formulae       :  127 ( 428 expanded)
%              Number of leaves         :   45 ( 166 expanded)
%              Depth                    :   14
%              Number of atoms          :  266 (1490 expanded)
%              Number of equality atoms :   55 ( 351 expanded)
%              Maximal formula depth    :   17 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k8_funct_2 > k3_funct_2 > k7_partfun1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(k3_funct_2,type,(
    k3_funct_2: ( $i * $i * $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_173,negated_conjecture,(
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

tff(f_82,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_78,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_148,axiom,(
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

tff(f_37,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(f_52,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_44,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).

tff(f_111,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A)
        & v1_funct_1(B) )
     => ! [C] :
          ( r2_hidden(C,k1_relat_1(B))
         => k7_partfun1(A,B,C) = k1_funct_1(B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_partfun1)).

tff(f_29,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_74,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_63,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A)
        & v1_funct_1(B) )
     => ! [C] :
          ( r2_hidden(C,k1_relat_1(B))
         => r2_hidden(k1_funct_1(B,C),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t172_funct_1)).

tff(f_31,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_68,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

tff(f_124,axiom,(
    ! [A,B,C,D] :
      ( ( ~ v1_xboole_0(A)
        & v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,A) )
     => m1_subset_1(k3_funct_2(A,B,C,D),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_funct_2)).

tff(c_52,plain,(
    m1_subset_1('#skF_6','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_173])).

tff(c_56,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_173])).

tff(c_54,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_173])).

tff(c_58,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_173])).

tff(c_149,plain,(
    ! [A_93,B_94,C_95] :
      ( k2_relset_1(A_93,B_94,C_95) = k2_relat_1(C_95)
      | ~ m1_subset_1(C_95,k1_zfmisc_1(k2_zfmisc_1(A_93,B_94))) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_157,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_58,c_149])).

tff(c_126,plain,(
    ! [A_89,B_90,C_91] :
      ( k1_relset_1(A_89,B_90,C_91) = k1_relat_1(C_91)
      | ~ m1_subset_1(C_91,k1_zfmisc_1(k2_zfmisc_1(A_89,B_90))) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_133,plain,(
    k1_relset_1('#skF_3','#skF_1','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_54,c_126])).

tff(c_50,plain,(
    r1_tarski(k2_relset_1('#skF_2','#skF_3','#skF_4'),k1_relset_1('#skF_3','#skF_1','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_173])).

tff(c_135,plain,(
    r1_tarski(k2_relset_1('#skF_2','#skF_3','#skF_4'),k1_relat_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_133,c_50])).

tff(c_163,plain,(
    r1_tarski(k2_relat_1('#skF_4'),k1_relat_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_157,c_135])).

tff(c_64,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_173])).

tff(c_48,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_173])).

tff(c_62,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_173])).

tff(c_60,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_173])).

tff(c_501,plain,(
    ! [C_182,F_181,B_178,A_177,D_180,E_179] :
      ( k1_funct_1(k8_funct_2(B_178,C_182,A_177,D_180,E_179),F_181) = k1_funct_1(E_179,k1_funct_1(D_180,F_181))
      | k1_xboole_0 = B_178
      | ~ r1_tarski(k2_relset_1(B_178,C_182,D_180),k1_relset_1(C_182,A_177,E_179))
      | ~ m1_subset_1(F_181,B_178)
      | ~ m1_subset_1(E_179,k1_zfmisc_1(k2_zfmisc_1(C_182,A_177)))
      | ~ v1_funct_1(E_179)
      | ~ m1_subset_1(D_180,k1_zfmisc_1(k2_zfmisc_1(B_178,C_182)))
      | ~ v1_funct_2(D_180,B_178,C_182)
      | ~ v1_funct_1(D_180)
      | v1_xboole_0(C_182) ) ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_505,plain,(
    ! [A_177,E_179,F_181] :
      ( k1_funct_1(k8_funct_2('#skF_2','#skF_3',A_177,'#skF_4',E_179),F_181) = k1_funct_1(E_179,k1_funct_1('#skF_4',F_181))
      | k1_xboole_0 = '#skF_2'
      | ~ r1_tarski(k2_relat_1('#skF_4'),k1_relset_1('#skF_3',A_177,E_179))
      | ~ m1_subset_1(F_181,'#skF_2')
      | ~ m1_subset_1(E_179,k1_zfmisc_1(k2_zfmisc_1('#skF_3',A_177)))
      | ~ v1_funct_1(E_179)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
      | ~ v1_funct_2('#skF_4','#skF_2','#skF_3')
      | ~ v1_funct_1('#skF_4')
      | v1_xboole_0('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_157,c_501])).

tff(c_514,plain,(
    ! [A_177,E_179,F_181] :
      ( k1_funct_1(k8_funct_2('#skF_2','#skF_3',A_177,'#skF_4',E_179),F_181) = k1_funct_1(E_179,k1_funct_1('#skF_4',F_181))
      | k1_xboole_0 = '#skF_2'
      | ~ r1_tarski(k2_relat_1('#skF_4'),k1_relset_1('#skF_3',A_177,E_179))
      | ~ m1_subset_1(F_181,'#skF_2')
      | ~ m1_subset_1(E_179,k1_zfmisc_1(k2_zfmisc_1('#skF_3',A_177)))
      | ~ v1_funct_1(E_179)
      | v1_xboole_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_58,c_505])).

tff(c_539,plain,(
    ! [A_183,E_184,F_185] :
      ( k1_funct_1(k8_funct_2('#skF_2','#skF_3',A_183,'#skF_4',E_184),F_185) = k1_funct_1(E_184,k1_funct_1('#skF_4',F_185))
      | ~ r1_tarski(k2_relat_1('#skF_4'),k1_relset_1('#skF_3',A_183,E_184))
      | ~ m1_subset_1(F_185,'#skF_2')
      | ~ m1_subset_1(E_184,k1_zfmisc_1(k2_zfmisc_1('#skF_3',A_183)))
      | ~ v1_funct_1(E_184) ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_48,c_514])).

tff(c_541,plain,(
    ! [F_185] :
      ( k1_funct_1(k8_funct_2('#skF_2','#skF_3','#skF_1','#skF_4','#skF_5'),F_185) = k1_funct_1('#skF_5',k1_funct_1('#skF_4',F_185))
      | ~ r1_tarski(k2_relat_1('#skF_4'),k1_relat_1('#skF_5'))
      | ~ m1_subset_1(F_185,'#skF_2')
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_1')))
      | ~ v1_funct_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_133,c_539])).

tff(c_576,plain,(
    ! [F_187] :
      ( k1_funct_1(k8_funct_2('#skF_2','#skF_3','#skF_1','#skF_4','#skF_5'),F_187) = k1_funct_1('#skF_5',k1_funct_1('#skF_4',F_187))
      | ~ m1_subset_1(F_187,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_163,c_541])).

tff(c_6,plain,(
    ! [A_3,B_4] :
      ( r2_hidden(A_3,B_4)
      | v1_xboole_0(B_4)
      | ~ m1_subset_1(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_14,plain,(
    ! [A_10,B_11] : v1_relat_1(k2_zfmisc_1(A_10,B_11)) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_74,plain,(
    ! [B_74,A_75] :
      ( v1_relat_1(B_74)
      | ~ m1_subset_1(B_74,k1_zfmisc_1(A_75))
      | ~ v1_relat_1(A_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_80,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_58,c_74])).

tff(c_86,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_80])).

tff(c_134,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_58,c_126])).

tff(c_198,plain,(
    ! [B_110,A_111,C_112] :
      ( k1_xboole_0 = B_110
      | k1_relset_1(A_111,B_110,C_112) = A_111
      | ~ v1_funct_2(C_112,A_111,B_110)
      | ~ m1_subset_1(C_112,k1_zfmisc_1(k2_zfmisc_1(A_111,B_110))) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_204,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relset_1('#skF_2','#skF_3','#skF_4') = '#skF_2'
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_58,c_198])).

tff(c_209,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relat_1('#skF_4') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_134,c_204])).

tff(c_210,plain,(
    k1_relat_1('#skF_4') = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_209])).

tff(c_258,plain,(
    ! [A_120,B_121,C_122] :
      ( k7_partfun1(A_120,B_121,C_122) = k1_funct_1(B_121,C_122)
      | ~ r2_hidden(C_122,k1_relat_1(B_121))
      | ~ v1_funct_1(B_121)
      | ~ v5_relat_1(B_121,A_120)
      | ~ v1_relat_1(B_121) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_260,plain,(
    ! [A_120,C_122] :
      ( k7_partfun1(A_120,'#skF_4',C_122) = k1_funct_1('#skF_4',C_122)
      | ~ r2_hidden(C_122,'#skF_2')
      | ~ v1_funct_1('#skF_4')
      | ~ v5_relat_1('#skF_4',A_120)
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_210,c_258])).

tff(c_271,plain,(
    ! [A_123,C_124] :
      ( k7_partfun1(A_123,'#skF_4',C_124) = k1_funct_1('#skF_4',C_124)
      | ~ r2_hidden(C_124,'#skF_2')
      | ~ v5_relat_1('#skF_4',A_123) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_62,c_260])).

tff(c_279,plain,(
    ! [A_123,A_3] :
      ( k7_partfun1(A_123,'#skF_4',A_3) = k1_funct_1('#skF_4',A_3)
      | ~ v5_relat_1('#skF_4',A_123)
      | v1_xboole_0('#skF_2')
      | ~ m1_subset_1(A_3,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_6,c_271])).

tff(c_280,plain,(
    v1_xboole_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_279])).

tff(c_2,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_295,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_280,c_2])).

tff(c_299,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_295])).

tff(c_301,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_279])).

tff(c_87,plain,(
    ! [C_76,B_77,A_78] :
      ( v5_relat_1(C_76,B_77)
      | ~ m1_subset_1(C_76,k1_zfmisc_1(k2_zfmisc_1(A_78,B_77))) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_94,plain,(
    v5_relat_1('#skF_5','#skF_1') ),
    inference(resolution,[status(thm)],[c_54,c_87])).

tff(c_77,plain,
    ( v1_relat_1('#skF_5')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_3','#skF_1')) ),
    inference(resolution,[status(thm)],[c_54,c_74])).

tff(c_83,plain,(
    v1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_77])).

tff(c_10,plain,(
    ! [B_9,A_8] :
      ( v5_relat_1(B_9,A_8)
      | ~ r1_tarski(k2_relat_1(B_9),A_8)
      | ~ v1_relat_1(B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_170,plain,
    ( v5_relat_1('#skF_4',k1_relat_1('#skF_5'))
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_163,c_10])).

tff(c_176,plain,(
    v5_relat_1('#skF_4',k1_relat_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_170])).

tff(c_16,plain,(
    ! [B_13,C_15,A_12] :
      ( r2_hidden(k1_funct_1(B_13,C_15),A_12)
      | ~ r2_hidden(C_15,k1_relat_1(B_13))
      | ~ v1_funct_1(B_13)
      | ~ v5_relat_1(B_13,A_12)
      | ~ v1_relat_1(B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_464,plain,(
    ! [A_168,B_169,B_170,C_171] :
      ( k7_partfun1(A_168,B_169,k1_funct_1(B_170,C_171)) = k1_funct_1(B_169,k1_funct_1(B_170,C_171))
      | ~ v1_funct_1(B_169)
      | ~ v5_relat_1(B_169,A_168)
      | ~ v1_relat_1(B_169)
      | ~ r2_hidden(C_171,k1_relat_1(B_170))
      | ~ v1_funct_1(B_170)
      | ~ v5_relat_1(B_170,k1_relat_1(B_169))
      | ~ v1_relat_1(B_170) ) ),
    inference(resolution,[status(thm)],[c_16,c_258])).

tff(c_466,plain,(
    ! [A_168,B_169,C_171] :
      ( k7_partfun1(A_168,B_169,k1_funct_1('#skF_4',C_171)) = k1_funct_1(B_169,k1_funct_1('#skF_4',C_171))
      | ~ v1_funct_1(B_169)
      | ~ v5_relat_1(B_169,A_168)
      | ~ v1_relat_1(B_169)
      | ~ r2_hidden(C_171,'#skF_2')
      | ~ v1_funct_1('#skF_4')
      | ~ v5_relat_1('#skF_4',k1_relat_1(B_169))
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_210,c_464])).

tff(c_477,plain,(
    ! [A_172,B_173,C_174] :
      ( k7_partfun1(A_172,B_173,k1_funct_1('#skF_4',C_174)) = k1_funct_1(B_173,k1_funct_1('#skF_4',C_174))
      | ~ v1_funct_1(B_173)
      | ~ v5_relat_1(B_173,A_172)
      | ~ v1_relat_1(B_173)
      | ~ r2_hidden(C_174,'#skF_2')
      | ~ v5_relat_1('#skF_4',k1_relat_1(B_173)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_62,c_466])).

tff(c_481,plain,(
    ! [A_172,C_174] :
      ( k7_partfun1(A_172,'#skF_5',k1_funct_1('#skF_4',C_174)) = k1_funct_1('#skF_5',k1_funct_1('#skF_4',C_174))
      | ~ v1_funct_1('#skF_5')
      | ~ v5_relat_1('#skF_5',A_172)
      | ~ v1_relat_1('#skF_5')
      | ~ r2_hidden(C_174,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_176,c_477])).

tff(c_487,plain,(
    ! [A_175,C_176] :
      ( k7_partfun1(A_175,'#skF_5',k1_funct_1('#skF_4',C_176)) = k1_funct_1('#skF_5',k1_funct_1('#skF_4',C_176))
      | ~ v5_relat_1('#skF_5',A_175)
      | ~ r2_hidden(C_176,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_83,c_56,c_481])).

tff(c_46,plain,(
    k7_partfun1('#skF_1','#skF_5',k1_funct_1('#skF_4','#skF_6')) != k1_funct_1(k8_funct_2('#skF_2','#skF_3','#skF_1','#skF_4','#skF_5'),'#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_173])).

tff(c_493,plain,
    ( k1_funct_1(k8_funct_2('#skF_2','#skF_3','#skF_1','#skF_4','#skF_5'),'#skF_6') != k1_funct_1('#skF_5',k1_funct_1('#skF_4','#skF_6'))
    | ~ v5_relat_1('#skF_5','#skF_1')
    | ~ r2_hidden('#skF_6','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_487,c_46])).

tff(c_499,plain,
    ( k1_funct_1(k8_funct_2('#skF_2','#skF_3','#skF_1','#skF_4','#skF_5'),'#skF_6') != k1_funct_1('#skF_5',k1_funct_1('#skF_4','#skF_6'))
    | ~ r2_hidden('#skF_6','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_493])).

tff(c_521,plain,(
    ~ r2_hidden('#skF_6','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_499])).

tff(c_524,plain,
    ( v1_xboole_0('#skF_2')
    | ~ m1_subset_1('#skF_6','#skF_2') ),
    inference(resolution,[status(thm)],[c_6,c_521])).

tff(c_527,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_524])).

tff(c_529,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_301,c_527])).

tff(c_530,plain,(
    k1_funct_1(k8_funct_2('#skF_2','#skF_3','#skF_1','#skF_4','#skF_5'),'#skF_6') != k1_funct_1('#skF_5',k1_funct_1('#skF_4','#skF_6')) ),
    inference(splitRight,[status(thm)],[c_499])).

tff(c_582,plain,(
    ~ m1_subset_1('#skF_6','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_576,c_530])).

tff(c_595,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_582])).

tff(c_596,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_209])).

tff(c_618,plain,(
    '#skF_2' != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_596,c_48])).

tff(c_4,plain,(
    ! [A_2] : r1_tarski(k1_xboole_0,A_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_625,plain,(
    ! [A_191] : r1_tarski('#skF_3',A_191) ),
    inference(demodulation,[status(thm),theory(equality)],[c_596,c_4])).

tff(c_69,plain,(
    ! [A_72,B_73] :
      ( r2_hidden(A_72,B_73)
      | v1_xboole_0(B_73)
      | ~ m1_subset_1(A_72,B_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_18,plain,(
    ! [B_17,A_16] :
      ( ~ r1_tarski(B_17,A_16)
      | ~ r2_hidden(A_16,B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_73,plain,(
    ! [B_73,A_72] :
      ( ~ r1_tarski(B_73,A_72)
      | v1_xboole_0(B_73)
      | ~ m1_subset_1(A_72,B_73) ) ),
    inference(resolution,[status(thm)],[c_69,c_18])).

tff(c_631,plain,(
    ! [A_191] :
      ( v1_xboole_0('#skF_3')
      | ~ m1_subset_1(A_191,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_625,c_73])).

tff(c_635,plain,(
    ! [A_191] : ~ m1_subset_1(A_191,'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_631])).

tff(c_662,plain,(
    ! [A_199,B_200,C_201,D_202] :
      ( m1_subset_1(k3_funct_2(A_199,B_200,C_201,D_202),B_200)
      | ~ m1_subset_1(D_202,A_199)
      | ~ m1_subset_1(C_201,k1_zfmisc_1(k2_zfmisc_1(A_199,B_200)))
      | ~ v1_funct_2(C_201,A_199,B_200)
      | ~ v1_funct_1(C_201)
      | v1_xboole_0(A_199) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_666,plain,(
    ! [D_202] :
      ( m1_subset_1(k3_funct_2('#skF_2','#skF_3','#skF_4',D_202),'#skF_3')
      | ~ m1_subset_1(D_202,'#skF_2')
      | ~ v1_funct_2('#skF_4','#skF_2','#skF_3')
      | ~ v1_funct_1('#skF_4')
      | v1_xboole_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_58,c_662])).

tff(c_673,plain,(
    ! [D_202] :
      ( m1_subset_1(k3_funct_2('#skF_2','#skF_3','#skF_4',D_202),'#skF_3')
      | ~ m1_subset_1(D_202,'#skF_2')
      | v1_xboole_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_666])).

tff(c_674,plain,(
    ! [D_202] :
      ( ~ m1_subset_1(D_202,'#skF_2')
      | v1_xboole_0('#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_635,c_673])).

tff(c_675,plain,(
    ! [D_202] : ~ m1_subset_1(D_202,'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_674])).

tff(c_677,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_675,c_52])).

tff(c_678,plain,(
    v1_xboole_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_674])).

tff(c_616,plain,(
    ! [A_1] :
      ( A_1 = '#skF_3'
      | ~ v1_xboole_0(A_1) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_596,c_2])).

tff(c_681,plain,(
    '#skF_2' = '#skF_3' ),
    inference(resolution,[status(thm)],[c_678,c_616])).

tff(c_685,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_618,c_681])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n002.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 14:09:07 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.28/1.57  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.28/1.58  
% 3.28/1.58  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.28/1.58  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k8_funct_2 > k3_funct_2 > k7_partfun1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 3.28/1.58  
% 3.28/1.58  %Foreground sorts:
% 3.28/1.58  
% 3.28/1.58  
% 3.28/1.58  %Background operators:
% 3.28/1.58  
% 3.28/1.58  
% 3.28/1.58  %Foreground operators:
% 3.28/1.58  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 3.28/1.58  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.28/1.58  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.28/1.58  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.28/1.58  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.28/1.58  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.28/1.58  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.28/1.58  tff(k7_partfun1, type, k7_partfun1: ($i * $i * $i) > $i).
% 3.28/1.58  tff('#skF_5', type, '#skF_5': $i).
% 3.28/1.58  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.28/1.58  tff(k8_funct_2, type, k8_funct_2: ($i * $i * $i * $i * $i) > $i).
% 3.28/1.58  tff('#skF_6', type, '#skF_6': $i).
% 3.28/1.58  tff('#skF_2', type, '#skF_2': $i).
% 3.28/1.58  tff('#skF_3', type, '#skF_3': $i).
% 3.28/1.58  tff('#skF_1', type, '#skF_1': $i).
% 3.28/1.58  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.28/1.58  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.28/1.58  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.28/1.58  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.28/1.58  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.28/1.58  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.28/1.58  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.28/1.58  tff('#skF_4', type, '#skF_4': $i).
% 3.28/1.58  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.28/1.58  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.28/1.58  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.28/1.58  tff(k3_funct_2, type, k3_funct_2: ($i * $i * $i * $i) > $i).
% 3.28/1.58  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.28/1.58  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.28/1.58  
% 3.28/1.60  tff(f_173, negated_conjecture, ~(![A, B, C]: (~v1_xboole_0(C) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, C)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (![E]: ((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(C, A)))) => (![F]: (m1_subset_1(F, B) => (r1_tarski(k2_relset_1(B, C, D), k1_relset_1(C, A, E)) => ((B = k1_xboole_0) | (k1_funct_1(k8_funct_2(B, C, A, D, E), F) = k7_partfun1(A, E, k1_funct_1(D, F))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t186_funct_2)).
% 3.28/1.60  tff(f_82, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 3.28/1.60  tff(f_78, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.28/1.60  tff(f_148, axiom, (![A, B, C]: (~v1_xboole_0(C) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, C)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (![E]: ((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(C, A)))) => (![F]: (m1_subset_1(F, B) => (r1_tarski(k2_relset_1(B, C, D), k1_relset_1(C, A, E)) => ((B = k1_xboole_0) | (k1_funct_1(k8_funct_2(B, C, A, D, E), F) = k1_funct_1(E, k1_funct_1(D, F))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t185_funct_2)).
% 3.28/1.60  tff(f_37, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 3.28/1.60  tff(f_52, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 3.28/1.60  tff(f_44, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 3.28/1.60  tff(f_100, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 3.28/1.60  tff(f_111, axiom, (![A, B]: (((v1_relat_1(B) & v5_relat_1(B, A)) & v1_funct_1(B)) => (![C]: (r2_hidden(C, k1_relat_1(B)) => (k7_partfun1(A, B, C) = k1_funct_1(B, C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_partfun1)).
% 3.28/1.60  tff(f_29, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 3.28/1.60  tff(f_74, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.28/1.60  tff(f_50, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 3.28/1.60  tff(f_63, axiom, (![A, B]: (((v1_relat_1(B) & v5_relat_1(B, A)) & v1_funct_1(B)) => (![C]: (r2_hidden(C, k1_relat_1(B)) => r2_hidden(k1_funct_1(B, C), A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t172_funct_1)).
% 3.28/1.60  tff(f_31, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 3.28/1.60  tff(f_68, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 3.28/1.60  tff(f_124, axiom, (![A, B, C, D]: (((((~v1_xboole_0(A) & v1_funct_1(C)) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & m1_subset_1(D, A)) => m1_subset_1(k3_funct_2(A, B, C, D), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k3_funct_2)).
% 3.28/1.60  tff(c_52, plain, (m1_subset_1('#skF_6', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_173])).
% 3.28/1.60  tff(c_56, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_173])).
% 3.28/1.60  tff(c_54, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_173])).
% 3.28/1.60  tff(c_58, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_173])).
% 3.28/1.60  tff(c_149, plain, (![A_93, B_94, C_95]: (k2_relset_1(A_93, B_94, C_95)=k2_relat_1(C_95) | ~m1_subset_1(C_95, k1_zfmisc_1(k2_zfmisc_1(A_93, B_94))))), inference(cnfTransformation, [status(thm)], [f_82])).
% 3.28/1.60  tff(c_157, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_58, c_149])).
% 3.28/1.60  tff(c_126, plain, (![A_89, B_90, C_91]: (k1_relset_1(A_89, B_90, C_91)=k1_relat_1(C_91) | ~m1_subset_1(C_91, k1_zfmisc_1(k2_zfmisc_1(A_89, B_90))))), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.28/1.60  tff(c_133, plain, (k1_relset_1('#skF_3', '#skF_1', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_54, c_126])).
% 3.28/1.60  tff(c_50, plain, (r1_tarski(k2_relset_1('#skF_2', '#skF_3', '#skF_4'), k1_relset_1('#skF_3', '#skF_1', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_173])).
% 3.28/1.60  tff(c_135, plain, (r1_tarski(k2_relset_1('#skF_2', '#skF_3', '#skF_4'), k1_relat_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_133, c_50])).
% 3.28/1.60  tff(c_163, plain, (r1_tarski(k2_relat_1('#skF_4'), k1_relat_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_157, c_135])).
% 3.28/1.60  tff(c_64, plain, (~v1_xboole_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_173])).
% 3.28/1.60  tff(c_48, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_173])).
% 3.28/1.60  tff(c_62, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_173])).
% 3.28/1.60  tff(c_60, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_173])).
% 3.28/1.60  tff(c_501, plain, (![C_182, F_181, B_178, A_177, D_180, E_179]: (k1_funct_1(k8_funct_2(B_178, C_182, A_177, D_180, E_179), F_181)=k1_funct_1(E_179, k1_funct_1(D_180, F_181)) | k1_xboole_0=B_178 | ~r1_tarski(k2_relset_1(B_178, C_182, D_180), k1_relset_1(C_182, A_177, E_179)) | ~m1_subset_1(F_181, B_178) | ~m1_subset_1(E_179, k1_zfmisc_1(k2_zfmisc_1(C_182, A_177))) | ~v1_funct_1(E_179) | ~m1_subset_1(D_180, k1_zfmisc_1(k2_zfmisc_1(B_178, C_182))) | ~v1_funct_2(D_180, B_178, C_182) | ~v1_funct_1(D_180) | v1_xboole_0(C_182))), inference(cnfTransformation, [status(thm)], [f_148])).
% 3.28/1.60  tff(c_505, plain, (![A_177, E_179, F_181]: (k1_funct_1(k8_funct_2('#skF_2', '#skF_3', A_177, '#skF_4', E_179), F_181)=k1_funct_1(E_179, k1_funct_1('#skF_4', F_181)) | k1_xboole_0='#skF_2' | ~r1_tarski(k2_relat_1('#skF_4'), k1_relset_1('#skF_3', A_177, E_179)) | ~m1_subset_1(F_181, '#skF_2') | ~m1_subset_1(E_179, k1_zfmisc_1(k2_zfmisc_1('#skF_3', A_177))) | ~v1_funct_1(E_179) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3') | ~v1_funct_1('#skF_4') | v1_xboole_0('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_157, c_501])).
% 3.28/1.60  tff(c_514, plain, (![A_177, E_179, F_181]: (k1_funct_1(k8_funct_2('#skF_2', '#skF_3', A_177, '#skF_4', E_179), F_181)=k1_funct_1(E_179, k1_funct_1('#skF_4', F_181)) | k1_xboole_0='#skF_2' | ~r1_tarski(k2_relat_1('#skF_4'), k1_relset_1('#skF_3', A_177, E_179)) | ~m1_subset_1(F_181, '#skF_2') | ~m1_subset_1(E_179, k1_zfmisc_1(k2_zfmisc_1('#skF_3', A_177))) | ~v1_funct_1(E_179) | v1_xboole_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_58, c_505])).
% 3.28/1.60  tff(c_539, plain, (![A_183, E_184, F_185]: (k1_funct_1(k8_funct_2('#skF_2', '#skF_3', A_183, '#skF_4', E_184), F_185)=k1_funct_1(E_184, k1_funct_1('#skF_4', F_185)) | ~r1_tarski(k2_relat_1('#skF_4'), k1_relset_1('#skF_3', A_183, E_184)) | ~m1_subset_1(F_185, '#skF_2') | ~m1_subset_1(E_184, k1_zfmisc_1(k2_zfmisc_1('#skF_3', A_183))) | ~v1_funct_1(E_184))), inference(negUnitSimplification, [status(thm)], [c_64, c_48, c_514])).
% 3.28/1.60  tff(c_541, plain, (![F_185]: (k1_funct_1(k8_funct_2('#skF_2', '#skF_3', '#skF_1', '#skF_4', '#skF_5'), F_185)=k1_funct_1('#skF_5', k1_funct_1('#skF_4', F_185)) | ~r1_tarski(k2_relat_1('#skF_4'), k1_relat_1('#skF_5')) | ~m1_subset_1(F_185, '#skF_2') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_1'))) | ~v1_funct_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_133, c_539])).
% 3.28/1.60  tff(c_576, plain, (![F_187]: (k1_funct_1(k8_funct_2('#skF_2', '#skF_3', '#skF_1', '#skF_4', '#skF_5'), F_187)=k1_funct_1('#skF_5', k1_funct_1('#skF_4', F_187)) | ~m1_subset_1(F_187, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_163, c_541])).
% 3.28/1.60  tff(c_6, plain, (![A_3, B_4]: (r2_hidden(A_3, B_4) | v1_xboole_0(B_4) | ~m1_subset_1(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.28/1.60  tff(c_14, plain, (![A_10, B_11]: (v1_relat_1(k2_zfmisc_1(A_10, B_11)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.28/1.60  tff(c_74, plain, (![B_74, A_75]: (v1_relat_1(B_74) | ~m1_subset_1(B_74, k1_zfmisc_1(A_75)) | ~v1_relat_1(A_75))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.28/1.60  tff(c_80, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_58, c_74])).
% 3.28/1.60  tff(c_86, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_14, c_80])).
% 3.28/1.60  tff(c_134, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_58, c_126])).
% 3.28/1.60  tff(c_198, plain, (![B_110, A_111, C_112]: (k1_xboole_0=B_110 | k1_relset_1(A_111, B_110, C_112)=A_111 | ~v1_funct_2(C_112, A_111, B_110) | ~m1_subset_1(C_112, k1_zfmisc_1(k2_zfmisc_1(A_111, B_110))))), inference(cnfTransformation, [status(thm)], [f_100])).
% 3.28/1.60  tff(c_204, plain, (k1_xboole_0='#skF_3' | k1_relset_1('#skF_2', '#skF_3', '#skF_4')='#skF_2' | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_58, c_198])).
% 3.28/1.60  tff(c_209, plain, (k1_xboole_0='#skF_3' | k1_relat_1('#skF_4')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_60, c_134, c_204])).
% 3.28/1.60  tff(c_210, plain, (k1_relat_1('#skF_4')='#skF_2'), inference(splitLeft, [status(thm)], [c_209])).
% 3.28/1.60  tff(c_258, plain, (![A_120, B_121, C_122]: (k7_partfun1(A_120, B_121, C_122)=k1_funct_1(B_121, C_122) | ~r2_hidden(C_122, k1_relat_1(B_121)) | ~v1_funct_1(B_121) | ~v5_relat_1(B_121, A_120) | ~v1_relat_1(B_121))), inference(cnfTransformation, [status(thm)], [f_111])).
% 3.28/1.60  tff(c_260, plain, (![A_120, C_122]: (k7_partfun1(A_120, '#skF_4', C_122)=k1_funct_1('#skF_4', C_122) | ~r2_hidden(C_122, '#skF_2') | ~v1_funct_1('#skF_4') | ~v5_relat_1('#skF_4', A_120) | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_210, c_258])).
% 3.28/1.60  tff(c_271, plain, (![A_123, C_124]: (k7_partfun1(A_123, '#skF_4', C_124)=k1_funct_1('#skF_4', C_124) | ~r2_hidden(C_124, '#skF_2') | ~v5_relat_1('#skF_4', A_123))), inference(demodulation, [status(thm), theory('equality')], [c_86, c_62, c_260])).
% 3.28/1.60  tff(c_279, plain, (![A_123, A_3]: (k7_partfun1(A_123, '#skF_4', A_3)=k1_funct_1('#skF_4', A_3) | ~v5_relat_1('#skF_4', A_123) | v1_xboole_0('#skF_2') | ~m1_subset_1(A_3, '#skF_2'))), inference(resolution, [status(thm)], [c_6, c_271])).
% 3.28/1.60  tff(c_280, plain, (v1_xboole_0('#skF_2')), inference(splitLeft, [status(thm)], [c_279])).
% 3.28/1.60  tff(c_2, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.28/1.60  tff(c_295, plain, (k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_280, c_2])).
% 3.28/1.60  tff(c_299, plain, $false, inference(negUnitSimplification, [status(thm)], [c_48, c_295])).
% 3.28/1.60  tff(c_301, plain, (~v1_xboole_0('#skF_2')), inference(splitRight, [status(thm)], [c_279])).
% 3.28/1.60  tff(c_87, plain, (![C_76, B_77, A_78]: (v5_relat_1(C_76, B_77) | ~m1_subset_1(C_76, k1_zfmisc_1(k2_zfmisc_1(A_78, B_77))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.28/1.60  tff(c_94, plain, (v5_relat_1('#skF_5', '#skF_1')), inference(resolution, [status(thm)], [c_54, c_87])).
% 3.28/1.60  tff(c_77, plain, (v1_relat_1('#skF_5') | ~v1_relat_1(k2_zfmisc_1('#skF_3', '#skF_1'))), inference(resolution, [status(thm)], [c_54, c_74])).
% 3.28/1.60  tff(c_83, plain, (v1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_14, c_77])).
% 3.28/1.60  tff(c_10, plain, (![B_9, A_8]: (v5_relat_1(B_9, A_8) | ~r1_tarski(k2_relat_1(B_9), A_8) | ~v1_relat_1(B_9))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.28/1.60  tff(c_170, plain, (v5_relat_1('#skF_4', k1_relat_1('#skF_5')) | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_163, c_10])).
% 3.28/1.60  tff(c_176, plain, (v5_relat_1('#skF_4', k1_relat_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_86, c_170])).
% 3.28/1.60  tff(c_16, plain, (![B_13, C_15, A_12]: (r2_hidden(k1_funct_1(B_13, C_15), A_12) | ~r2_hidden(C_15, k1_relat_1(B_13)) | ~v1_funct_1(B_13) | ~v5_relat_1(B_13, A_12) | ~v1_relat_1(B_13))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.28/1.60  tff(c_464, plain, (![A_168, B_169, B_170, C_171]: (k7_partfun1(A_168, B_169, k1_funct_1(B_170, C_171))=k1_funct_1(B_169, k1_funct_1(B_170, C_171)) | ~v1_funct_1(B_169) | ~v5_relat_1(B_169, A_168) | ~v1_relat_1(B_169) | ~r2_hidden(C_171, k1_relat_1(B_170)) | ~v1_funct_1(B_170) | ~v5_relat_1(B_170, k1_relat_1(B_169)) | ~v1_relat_1(B_170))), inference(resolution, [status(thm)], [c_16, c_258])).
% 3.28/1.60  tff(c_466, plain, (![A_168, B_169, C_171]: (k7_partfun1(A_168, B_169, k1_funct_1('#skF_4', C_171))=k1_funct_1(B_169, k1_funct_1('#skF_4', C_171)) | ~v1_funct_1(B_169) | ~v5_relat_1(B_169, A_168) | ~v1_relat_1(B_169) | ~r2_hidden(C_171, '#skF_2') | ~v1_funct_1('#skF_4') | ~v5_relat_1('#skF_4', k1_relat_1(B_169)) | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_210, c_464])).
% 3.28/1.60  tff(c_477, plain, (![A_172, B_173, C_174]: (k7_partfun1(A_172, B_173, k1_funct_1('#skF_4', C_174))=k1_funct_1(B_173, k1_funct_1('#skF_4', C_174)) | ~v1_funct_1(B_173) | ~v5_relat_1(B_173, A_172) | ~v1_relat_1(B_173) | ~r2_hidden(C_174, '#skF_2') | ~v5_relat_1('#skF_4', k1_relat_1(B_173)))), inference(demodulation, [status(thm), theory('equality')], [c_86, c_62, c_466])).
% 3.28/1.60  tff(c_481, plain, (![A_172, C_174]: (k7_partfun1(A_172, '#skF_5', k1_funct_1('#skF_4', C_174))=k1_funct_1('#skF_5', k1_funct_1('#skF_4', C_174)) | ~v1_funct_1('#skF_5') | ~v5_relat_1('#skF_5', A_172) | ~v1_relat_1('#skF_5') | ~r2_hidden(C_174, '#skF_2'))), inference(resolution, [status(thm)], [c_176, c_477])).
% 3.28/1.60  tff(c_487, plain, (![A_175, C_176]: (k7_partfun1(A_175, '#skF_5', k1_funct_1('#skF_4', C_176))=k1_funct_1('#skF_5', k1_funct_1('#skF_4', C_176)) | ~v5_relat_1('#skF_5', A_175) | ~r2_hidden(C_176, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_83, c_56, c_481])).
% 3.28/1.60  tff(c_46, plain, (k7_partfun1('#skF_1', '#skF_5', k1_funct_1('#skF_4', '#skF_6'))!=k1_funct_1(k8_funct_2('#skF_2', '#skF_3', '#skF_1', '#skF_4', '#skF_5'), '#skF_6')), inference(cnfTransformation, [status(thm)], [f_173])).
% 3.28/1.60  tff(c_493, plain, (k1_funct_1(k8_funct_2('#skF_2', '#skF_3', '#skF_1', '#skF_4', '#skF_5'), '#skF_6')!=k1_funct_1('#skF_5', k1_funct_1('#skF_4', '#skF_6')) | ~v5_relat_1('#skF_5', '#skF_1') | ~r2_hidden('#skF_6', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_487, c_46])).
% 3.28/1.60  tff(c_499, plain, (k1_funct_1(k8_funct_2('#skF_2', '#skF_3', '#skF_1', '#skF_4', '#skF_5'), '#skF_6')!=k1_funct_1('#skF_5', k1_funct_1('#skF_4', '#skF_6')) | ~r2_hidden('#skF_6', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_94, c_493])).
% 3.28/1.60  tff(c_521, plain, (~r2_hidden('#skF_6', '#skF_2')), inference(splitLeft, [status(thm)], [c_499])).
% 3.28/1.60  tff(c_524, plain, (v1_xboole_0('#skF_2') | ~m1_subset_1('#skF_6', '#skF_2')), inference(resolution, [status(thm)], [c_6, c_521])).
% 3.28/1.60  tff(c_527, plain, (v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_524])).
% 3.28/1.60  tff(c_529, plain, $false, inference(negUnitSimplification, [status(thm)], [c_301, c_527])).
% 3.28/1.60  tff(c_530, plain, (k1_funct_1(k8_funct_2('#skF_2', '#skF_3', '#skF_1', '#skF_4', '#skF_5'), '#skF_6')!=k1_funct_1('#skF_5', k1_funct_1('#skF_4', '#skF_6'))), inference(splitRight, [status(thm)], [c_499])).
% 3.28/1.60  tff(c_582, plain, (~m1_subset_1('#skF_6', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_576, c_530])).
% 3.28/1.60  tff(c_595, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_52, c_582])).
% 3.28/1.60  tff(c_596, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_209])).
% 3.28/1.60  tff(c_618, plain, ('#skF_2'!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_596, c_48])).
% 3.28/1.60  tff(c_4, plain, (![A_2]: (r1_tarski(k1_xboole_0, A_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.28/1.60  tff(c_625, plain, (![A_191]: (r1_tarski('#skF_3', A_191))), inference(demodulation, [status(thm), theory('equality')], [c_596, c_4])).
% 3.28/1.60  tff(c_69, plain, (![A_72, B_73]: (r2_hidden(A_72, B_73) | v1_xboole_0(B_73) | ~m1_subset_1(A_72, B_73))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.28/1.60  tff(c_18, plain, (![B_17, A_16]: (~r1_tarski(B_17, A_16) | ~r2_hidden(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.28/1.60  tff(c_73, plain, (![B_73, A_72]: (~r1_tarski(B_73, A_72) | v1_xboole_0(B_73) | ~m1_subset_1(A_72, B_73))), inference(resolution, [status(thm)], [c_69, c_18])).
% 3.28/1.60  tff(c_631, plain, (![A_191]: (v1_xboole_0('#skF_3') | ~m1_subset_1(A_191, '#skF_3'))), inference(resolution, [status(thm)], [c_625, c_73])).
% 3.28/1.60  tff(c_635, plain, (![A_191]: (~m1_subset_1(A_191, '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_64, c_631])).
% 3.28/1.60  tff(c_662, plain, (![A_199, B_200, C_201, D_202]: (m1_subset_1(k3_funct_2(A_199, B_200, C_201, D_202), B_200) | ~m1_subset_1(D_202, A_199) | ~m1_subset_1(C_201, k1_zfmisc_1(k2_zfmisc_1(A_199, B_200))) | ~v1_funct_2(C_201, A_199, B_200) | ~v1_funct_1(C_201) | v1_xboole_0(A_199))), inference(cnfTransformation, [status(thm)], [f_124])).
% 3.28/1.60  tff(c_666, plain, (![D_202]: (m1_subset_1(k3_funct_2('#skF_2', '#skF_3', '#skF_4', D_202), '#skF_3') | ~m1_subset_1(D_202, '#skF_2') | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3') | ~v1_funct_1('#skF_4') | v1_xboole_0('#skF_2'))), inference(resolution, [status(thm)], [c_58, c_662])).
% 3.28/1.60  tff(c_673, plain, (![D_202]: (m1_subset_1(k3_funct_2('#skF_2', '#skF_3', '#skF_4', D_202), '#skF_3') | ~m1_subset_1(D_202, '#skF_2') | v1_xboole_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_666])).
% 3.28/1.60  tff(c_674, plain, (![D_202]: (~m1_subset_1(D_202, '#skF_2') | v1_xboole_0('#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_635, c_673])).
% 3.28/1.60  tff(c_675, plain, (![D_202]: (~m1_subset_1(D_202, '#skF_2'))), inference(splitLeft, [status(thm)], [c_674])).
% 3.28/1.60  tff(c_677, plain, $false, inference(negUnitSimplification, [status(thm)], [c_675, c_52])).
% 3.28/1.60  tff(c_678, plain, (v1_xboole_0('#skF_2')), inference(splitRight, [status(thm)], [c_674])).
% 3.28/1.60  tff(c_616, plain, (![A_1]: (A_1='#skF_3' | ~v1_xboole_0(A_1))), inference(demodulation, [status(thm), theory('equality')], [c_596, c_2])).
% 3.28/1.60  tff(c_681, plain, ('#skF_2'='#skF_3'), inference(resolution, [status(thm)], [c_678, c_616])).
% 3.28/1.60  tff(c_685, plain, $false, inference(negUnitSimplification, [status(thm)], [c_618, c_681])).
% 3.28/1.60  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.28/1.60  
% 3.28/1.60  Inference rules
% 3.28/1.60  ----------------------
% 3.28/1.60  #Ref     : 0
% 3.28/1.60  #Sup     : 120
% 3.28/1.60  #Fact    : 0
% 3.28/1.60  #Define  : 0
% 3.28/1.60  #Split   : 14
% 3.28/1.60  #Chain   : 0
% 3.28/1.60  #Close   : 0
% 3.28/1.60  
% 3.28/1.60  Ordering : KBO
% 3.28/1.60  
% 3.28/1.60  Simplification rules
% 3.28/1.60  ----------------------
% 3.28/1.60  #Subsume      : 18
% 3.28/1.60  #Demod        : 139
% 3.28/1.60  #Tautology    : 29
% 3.28/1.60  #SimpNegUnit  : 23
% 3.28/1.60  #BackRed      : 21
% 3.28/1.60  
% 3.28/1.60  #Partial instantiations: 0
% 3.28/1.60  #Strategies tried      : 1
% 3.28/1.60  
% 3.28/1.60  Timing (in seconds)
% 3.28/1.60  ----------------------
% 3.28/1.61  Preprocessing        : 0.41
% 3.28/1.61  Parsing              : 0.22
% 3.28/1.61  CNF conversion       : 0.03
% 3.28/1.61  Main loop            : 0.39
% 3.28/1.61  Inferencing          : 0.13
% 3.28/1.61  Reduction            : 0.14
% 3.28/1.61  Demodulation         : 0.09
% 3.28/1.61  BG Simplification    : 0.02
% 3.28/1.61  Subsumption          : 0.08
% 3.28/1.61  Abstraction          : 0.02
% 3.28/1.61  MUC search           : 0.00
% 3.28/1.61  Cooper               : 0.00
% 3.28/1.61  Total                : 0.85
% 3.28/1.61  Index Insertion      : 0.00
% 3.28/1.61  Index Deletion       : 0.00
% 3.28/1.61  Index Matching       : 0.00
% 3.28/1.61  BG Taut test         : 0.00
%------------------------------------------------------------------------------
