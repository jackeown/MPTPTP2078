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
% DateTime   : Thu Dec  3 10:18:14 EST 2020

% Result     : Theorem 3.58s
% Output     : CNFRefutation 3.58s
% Verified   : 
% Statistics : Number of formulae       :  126 ( 384 expanded)
%              Number of leaves         :   41 ( 155 expanded)
%              Depth                    :   17
%              Number of atoms          :  327 (1766 expanded)
%              Number of equality atoms :   62 ( 244 expanded)
%              Maximal formula depth    :   17 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k8_funct_2 > k3_funct_2 > k7_partfun1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

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

tff(k3_funct_2,type,(
    k3_funct_2: ( $i * $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_172,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B] :
            ( ~ v1_xboole_0(B)
           => ! [C,D] :
                ( ( v1_funct_1(D)
                  & v1_funct_2(D,B,A)
                  & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,A))) )
               => ! [E] :
                    ( ( v1_funct_1(E)
                      & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,C))) )
                   => ! [F] :
                        ( m1_subset_1(F,B)
                       => ( v1_partfun1(E,A)
                         => k3_funct_2(B,C,k8_funct_2(B,A,C,D,E),F) = k7_partfun1(C,E,k3_funct_2(B,A,D,F)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t193_funct_2)).

tff(f_62,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & v1_xboole_0(B) )
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => ~ v1_partfun1(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_partfun1)).

tff(f_41,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_33,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_47,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_121,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( v1_partfun1(C,A)
       => ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t131_funct_2)).

tff(f_80,axiom,(
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

tff(f_51,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_145,axiom,(
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
                      | k1_funct_1(k8_funct_2(B,C,A,D,E),F) = k7_partfun1(A,E,k1_funct_1(D,F)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t186_funct_2)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_96,axiom,(
    ! [A,B,C,D,E] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(B,C))) )
     => ( v1_funct_1(k8_funct_2(A,B,C,D,E))
        & v1_funct_2(k8_funct_2(A,B,C,D,E),A,C)
        & m1_subset_1(k8_funct_2(A,B,C,D,E),k1_zfmisc_1(k2_zfmisc_1(A,C))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k8_funct_2)).

tff(f_109,axiom,(
    ! [A,B,C,D] :
      ( ( ~ v1_xboole_0(A)
        & v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,A) )
     => k3_funct_2(A,B,C,D) = k1_funct_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k3_funct_2)).

tff(c_66,plain,(
    ~ v1_xboole_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_172])).

tff(c_50,plain,(
    v1_partfun1('#skF_5','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_172])).

tff(c_54,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_172])).

tff(c_115,plain,(
    ! [C_97,A_98,B_99] :
      ( ~ v1_partfun1(C_97,A_98)
      | ~ m1_subset_1(C_97,k1_zfmisc_1(k2_zfmisc_1(A_98,B_99)))
      | ~ v1_xboole_0(B_99)
      | v1_xboole_0(A_98) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_121,plain,
    ( ~ v1_partfun1('#skF_5','#skF_1')
    | ~ v1_xboole_0('#skF_3')
    | v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_54,c_115])).

tff(c_126,plain,
    ( ~ v1_xboole_0('#skF_3')
    | v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_121])).

tff(c_127,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_126])).

tff(c_52,plain,(
    m1_subset_1('#skF_6','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_172])).

tff(c_10,plain,(
    ! [A_6,B_7] : v1_relat_1(k2_zfmisc_1(A_6,B_7)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_58,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_172])).

tff(c_68,plain,(
    ! [B_81,A_82] :
      ( v1_relat_1(B_81)
      | ~ m1_subset_1(B_81,k1_zfmisc_1(A_82))
      | ~ v1_relat_1(A_82) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_71,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_1')) ),
    inference(resolution,[status(thm)],[c_58,c_68])).

tff(c_77,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_71])).

tff(c_87,plain,(
    ! [C_87,B_88,A_89] :
      ( v5_relat_1(C_87,B_88)
      | ~ m1_subset_1(C_87,k1_zfmisc_1(k2_zfmisc_1(A_89,B_88))) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_94,plain,(
    v5_relat_1('#skF_4','#skF_1') ),
    inference(resolution,[status(thm)],[c_58,c_87])).

tff(c_8,plain,(
    ! [B_5,A_4] :
      ( r1_tarski(k2_relat_1(B_5),A_4)
      | ~ v5_relat_1(B_5,A_4)
      | ~ v1_relat_1(B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_56,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_172])).

tff(c_137,plain,(
    ! [C_102,A_103,B_104] :
      ( v1_funct_2(C_102,A_103,B_104)
      | ~ v1_partfun1(C_102,A_103)
      | ~ m1_subset_1(C_102,k1_zfmisc_1(k2_zfmisc_1(A_103,B_104)))
      | ~ v1_funct_1(C_102) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_143,plain,
    ( v1_funct_2('#skF_5','#skF_1','#skF_3')
    | ~ v1_partfun1('#skF_5','#skF_1')
    | ~ v1_funct_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_54,c_137])).

tff(c_149,plain,(
    v1_funct_2('#skF_5','#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_50,c_143])).

tff(c_152,plain,(
    ! [B_109,A_110,C_111] :
      ( k1_xboole_0 = B_109
      | k1_relset_1(A_110,B_109,C_111) = A_110
      | ~ v1_funct_2(C_111,A_110,B_109)
      | ~ m1_subset_1(C_111,k1_zfmisc_1(k2_zfmisc_1(A_110,B_109))) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_158,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relset_1('#skF_1','#skF_3','#skF_5') = '#skF_1'
    | ~ v1_funct_2('#skF_5','#skF_1','#skF_3') ),
    inference(resolution,[status(thm)],[c_54,c_152])).

tff(c_164,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relset_1('#skF_1','#skF_3','#skF_5') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_149,c_158])).

tff(c_181,plain,(
    k1_relset_1('#skF_1','#skF_3','#skF_5') = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_164])).

tff(c_64,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_172])).

tff(c_62,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_172])).

tff(c_60,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_172])).

tff(c_106,plain,(
    ! [A_94,B_95,C_96] :
      ( k2_relset_1(A_94,B_95,C_96) = k2_relat_1(C_96)
      | ~ m1_subset_1(C_96,k1_zfmisc_1(k2_zfmisc_1(A_94,B_95))) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_113,plain,(
    k2_relset_1('#skF_2','#skF_1','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_58,c_106])).

tff(c_330,plain,(
    ! [E_148,F_145,A_144,D_147,B_149,C_146] :
      ( k7_partfun1(A_144,E_148,k1_funct_1(D_147,F_145)) = k1_funct_1(k8_funct_2(B_149,C_146,A_144,D_147,E_148),F_145)
      | k1_xboole_0 = B_149
      | ~ r1_tarski(k2_relset_1(B_149,C_146,D_147),k1_relset_1(C_146,A_144,E_148))
      | ~ m1_subset_1(F_145,B_149)
      | ~ m1_subset_1(E_148,k1_zfmisc_1(k2_zfmisc_1(C_146,A_144)))
      | ~ v1_funct_1(E_148)
      | ~ m1_subset_1(D_147,k1_zfmisc_1(k2_zfmisc_1(B_149,C_146)))
      | ~ v1_funct_2(D_147,B_149,C_146)
      | ~ v1_funct_1(D_147)
      | v1_xboole_0(C_146) ) ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_338,plain,(
    ! [A_144,E_148,F_145] :
      ( k7_partfun1(A_144,E_148,k1_funct_1('#skF_4',F_145)) = k1_funct_1(k8_funct_2('#skF_2','#skF_1',A_144,'#skF_4',E_148),F_145)
      | k1_xboole_0 = '#skF_2'
      | ~ r1_tarski(k2_relat_1('#skF_4'),k1_relset_1('#skF_1',A_144,E_148))
      | ~ m1_subset_1(F_145,'#skF_2')
      | ~ m1_subset_1(E_148,k1_zfmisc_1(k2_zfmisc_1('#skF_1',A_144)))
      | ~ v1_funct_1(E_148)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
      | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
      | ~ v1_funct_1('#skF_4')
      | v1_xboole_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_113,c_330])).

tff(c_349,plain,(
    ! [A_144,E_148,F_145] :
      ( k7_partfun1(A_144,E_148,k1_funct_1('#skF_4',F_145)) = k1_funct_1(k8_funct_2('#skF_2','#skF_1',A_144,'#skF_4',E_148),F_145)
      | k1_xboole_0 = '#skF_2'
      | ~ r1_tarski(k2_relat_1('#skF_4'),k1_relset_1('#skF_1',A_144,E_148))
      | ~ m1_subset_1(F_145,'#skF_2')
      | ~ m1_subset_1(E_148,k1_zfmisc_1(k2_zfmisc_1('#skF_1',A_144)))
      | ~ v1_funct_1(E_148)
      | v1_xboole_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_58,c_338])).

tff(c_350,plain,(
    ! [A_144,E_148,F_145] :
      ( k7_partfun1(A_144,E_148,k1_funct_1('#skF_4',F_145)) = k1_funct_1(k8_funct_2('#skF_2','#skF_1',A_144,'#skF_4',E_148),F_145)
      | k1_xboole_0 = '#skF_2'
      | ~ r1_tarski(k2_relat_1('#skF_4'),k1_relset_1('#skF_1',A_144,E_148))
      | ~ m1_subset_1(F_145,'#skF_2')
      | ~ m1_subset_1(E_148,k1_zfmisc_1(k2_zfmisc_1('#skF_1',A_144)))
      | ~ v1_funct_1(E_148) ) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_349])).

tff(c_445,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_350])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_453,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_445,c_2])).

tff(c_455,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_453])).

tff(c_459,plain,(
    ! [A_182,E_183,F_184] :
      ( k7_partfun1(A_182,E_183,k1_funct_1('#skF_4',F_184)) = k1_funct_1(k8_funct_2('#skF_2','#skF_1',A_182,'#skF_4',E_183),F_184)
      | ~ r1_tarski(k2_relat_1('#skF_4'),k1_relset_1('#skF_1',A_182,E_183))
      | ~ m1_subset_1(F_184,'#skF_2')
      | ~ m1_subset_1(E_183,k1_zfmisc_1(k2_zfmisc_1('#skF_1',A_182)))
      | ~ v1_funct_1(E_183) ) ),
    inference(splitRight,[status(thm)],[c_350])).

tff(c_461,plain,(
    ! [F_184] :
      ( k7_partfun1('#skF_3','#skF_5',k1_funct_1('#skF_4',F_184)) = k1_funct_1(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),F_184)
      | ~ r1_tarski(k2_relat_1('#skF_4'),'#skF_1')
      | ~ m1_subset_1(F_184,'#skF_2')
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3')))
      | ~ v1_funct_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_181,c_459])).

tff(c_466,plain,(
    ! [F_184] :
      ( k7_partfun1('#skF_3','#skF_5',k1_funct_1('#skF_4',F_184)) = k1_funct_1(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),F_184)
      | ~ r1_tarski(k2_relat_1('#skF_4'),'#skF_1')
      | ~ m1_subset_1(F_184,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_461])).

tff(c_484,plain,(
    ~ r1_tarski(k2_relat_1('#skF_4'),'#skF_1') ),
    inference(splitLeft,[status(thm)],[c_466])).

tff(c_487,plain,
    ( ~ v5_relat_1('#skF_4','#skF_1')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_8,c_484])).

tff(c_491,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_77,c_94,c_487])).

tff(c_492,plain,(
    ! [F_184] :
      ( k7_partfun1('#skF_3','#skF_5',k1_funct_1('#skF_4',F_184)) = k1_funct_1(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),F_184)
      | ~ m1_subset_1(F_184,'#skF_2') ) ),
    inference(splitRight,[status(thm)],[c_466])).

tff(c_210,plain,(
    ! [D_122,A_121,E_125,B_124,C_123] :
      ( v1_funct_1(k8_funct_2(A_121,B_124,C_123,D_122,E_125))
      | ~ m1_subset_1(E_125,k1_zfmisc_1(k2_zfmisc_1(B_124,C_123)))
      | ~ v1_funct_1(E_125)
      | ~ m1_subset_1(D_122,k1_zfmisc_1(k2_zfmisc_1(A_121,B_124)))
      | ~ v1_funct_2(D_122,A_121,B_124)
      | ~ v1_funct_1(D_122) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_214,plain,(
    ! [A_121,D_122] :
      ( v1_funct_1(k8_funct_2(A_121,'#skF_1','#skF_3',D_122,'#skF_5'))
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1(D_122,k1_zfmisc_1(k2_zfmisc_1(A_121,'#skF_1')))
      | ~ v1_funct_2(D_122,A_121,'#skF_1')
      | ~ v1_funct_1(D_122) ) ),
    inference(resolution,[status(thm)],[c_54,c_210])).

tff(c_233,plain,(
    ! [A_133,D_134] :
      ( v1_funct_1(k8_funct_2(A_133,'#skF_1','#skF_3',D_134,'#skF_5'))
      | ~ m1_subset_1(D_134,k1_zfmisc_1(k2_zfmisc_1(A_133,'#skF_1')))
      | ~ v1_funct_2(D_134,A_133,'#skF_1')
      | ~ v1_funct_1(D_134) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_214])).

tff(c_236,plain,
    ( v1_funct_1(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_58,c_233])).

tff(c_239,plain,(
    v1_funct_1(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_236])).

tff(c_221,plain,(
    ! [D_127,C_128,B_129,E_130,A_126] :
      ( v1_funct_2(k8_funct_2(A_126,B_129,C_128,D_127,E_130),A_126,C_128)
      | ~ m1_subset_1(E_130,k1_zfmisc_1(k2_zfmisc_1(B_129,C_128)))
      | ~ v1_funct_1(E_130)
      | ~ m1_subset_1(D_127,k1_zfmisc_1(k2_zfmisc_1(A_126,B_129)))
      | ~ v1_funct_2(D_127,A_126,B_129)
      | ~ v1_funct_1(D_127) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_225,plain,(
    ! [A_126,D_127] :
      ( v1_funct_2(k8_funct_2(A_126,'#skF_1','#skF_3',D_127,'#skF_5'),A_126,'#skF_3')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1(D_127,k1_zfmisc_1(k2_zfmisc_1(A_126,'#skF_1')))
      | ~ v1_funct_2(D_127,A_126,'#skF_1')
      | ~ v1_funct_1(D_127) ) ),
    inference(resolution,[status(thm)],[c_54,c_221])).

tff(c_241,plain,(
    ! [A_135,D_136] :
      ( v1_funct_2(k8_funct_2(A_135,'#skF_1','#skF_3',D_136,'#skF_5'),A_135,'#skF_3')
      | ~ m1_subset_1(D_136,k1_zfmisc_1(k2_zfmisc_1(A_135,'#skF_1')))
      | ~ v1_funct_2(D_136,A_135,'#skF_1')
      | ~ v1_funct_1(D_136) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_225])).

tff(c_243,plain,
    ( v1_funct_2(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),'#skF_2','#skF_3')
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_58,c_241])).

tff(c_246,plain,(
    v1_funct_2(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),'#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_243])).

tff(c_32,plain,(
    ! [A_21,B_22,D_24,C_23,E_25] :
      ( m1_subset_1(k8_funct_2(A_21,B_22,C_23,D_24,E_25),k1_zfmisc_1(k2_zfmisc_1(A_21,C_23)))
      | ~ m1_subset_1(E_25,k1_zfmisc_1(k2_zfmisc_1(B_22,C_23)))
      | ~ v1_funct_1(E_25)
      | ~ m1_subset_1(D_24,k1_zfmisc_1(k2_zfmisc_1(A_21,B_22)))
      | ~ v1_funct_2(D_24,A_21,B_22)
      | ~ v1_funct_1(D_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_248,plain,(
    ! [E_143,A_139,C_141,B_142,D_140] :
      ( m1_subset_1(k8_funct_2(A_139,B_142,C_141,D_140,E_143),k1_zfmisc_1(k2_zfmisc_1(A_139,C_141)))
      | ~ m1_subset_1(E_143,k1_zfmisc_1(k2_zfmisc_1(B_142,C_141)))
      | ~ v1_funct_1(E_143)
      | ~ m1_subset_1(D_140,k1_zfmisc_1(k2_zfmisc_1(A_139,B_142)))
      | ~ v1_funct_2(D_140,A_139,B_142)
      | ~ v1_funct_1(D_140) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_30,plain,(
    ! [B_19,A_18,C_20] :
      ( k1_xboole_0 = B_19
      | k1_relset_1(A_18,B_19,C_20) = A_18
      | ~ v1_funct_2(C_20,A_18,B_19)
      | ~ m1_subset_1(C_20,k1_zfmisc_1(k2_zfmisc_1(A_18,B_19))) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_589,plain,(
    ! [B_219,C_222,A_218,D_221,E_220] :
      ( k1_xboole_0 = C_222
      | k1_relset_1(A_218,C_222,k8_funct_2(A_218,B_219,C_222,D_221,E_220)) = A_218
      | ~ v1_funct_2(k8_funct_2(A_218,B_219,C_222,D_221,E_220),A_218,C_222)
      | ~ m1_subset_1(E_220,k1_zfmisc_1(k2_zfmisc_1(B_219,C_222)))
      | ~ v1_funct_1(E_220)
      | ~ m1_subset_1(D_221,k1_zfmisc_1(k2_zfmisc_1(A_218,B_219)))
      | ~ v1_funct_2(D_221,A_218,B_219)
      | ~ v1_funct_1(D_221) ) ),
    inference(resolution,[status(thm)],[c_248,c_30])).

tff(c_591,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relset_1('#skF_2','#skF_3',k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5')) = '#skF_2'
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3')))
    | ~ v1_funct_1('#skF_5')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_246,c_589])).

tff(c_594,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relset_1('#skF_2','#skF_3',k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_58,c_56,c_54,c_591])).

tff(c_595,plain,(
    k1_relset_1('#skF_2','#skF_3',k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5')) = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_594])).

tff(c_46,plain,(
    ! [F_49,E_47,A_33,B_34,D_43,C_35] :
      ( k7_partfun1(A_33,E_47,k1_funct_1(D_43,F_49)) = k1_funct_1(k8_funct_2(B_34,C_35,A_33,D_43,E_47),F_49)
      | k1_xboole_0 = B_34
      | ~ r1_tarski(k2_relset_1(B_34,C_35,D_43),k1_relset_1(C_35,A_33,E_47))
      | ~ m1_subset_1(F_49,B_34)
      | ~ m1_subset_1(E_47,k1_zfmisc_1(k2_zfmisc_1(C_35,A_33)))
      | ~ v1_funct_1(E_47)
      | ~ m1_subset_1(D_43,k1_zfmisc_1(k2_zfmisc_1(B_34,C_35)))
      | ~ v1_funct_2(D_43,B_34,C_35)
      | ~ v1_funct_1(D_43)
      | v1_xboole_0(C_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_612,plain,(
    ! [D_43,F_49,B_34] :
      ( k7_partfun1('#skF_3',k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),k1_funct_1(D_43,F_49)) = k1_funct_1(k8_funct_2(B_34,'#skF_2','#skF_3',D_43,k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5')),F_49)
      | k1_xboole_0 = B_34
      | ~ r1_tarski(k2_relset_1(B_34,'#skF_2',D_43),'#skF_2')
      | ~ m1_subset_1(F_49,B_34)
      | ~ m1_subset_1(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
      | ~ v1_funct_1(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'))
      | ~ m1_subset_1(D_43,k1_zfmisc_1(k2_zfmisc_1(B_34,'#skF_2')))
      | ~ v1_funct_2(D_43,B_34,'#skF_2')
      | ~ v1_funct_1(D_43)
      | v1_xboole_0('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_595,c_46])).

tff(c_616,plain,(
    ! [D_43,F_49,B_34] :
      ( k7_partfun1('#skF_3',k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),k1_funct_1(D_43,F_49)) = k1_funct_1(k8_funct_2(B_34,'#skF_2','#skF_3',D_43,k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5')),F_49)
      | k1_xboole_0 = B_34
      | ~ r1_tarski(k2_relset_1(B_34,'#skF_2',D_43),'#skF_2')
      | ~ m1_subset_1(F_49,B_34)
      | ~ m1_subset_1(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
      | ~ m1_subset_1(D_43,k1_zfmisc_1(k2_zfmisc_1(B_34,'#skF_2')))
      | ~ v1_funct_2(D_43,B_34,'#skF_2')
      | ~ v1_funct_1(D_43)
      | v1_xboole_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_239,c_612])).

tff(c_617,plain,(
    ! [D_43,F_49,B_34] :
      ( k7_partfun1('#skF_3',k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),k1_funct_1(D_43,F_49)) = k1_funct_1(k8_funct_2(B_34,'#skF_2','#skF_3',D_43,k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5')),F_49)
      | k1_xboole_0 = B_34
      | ~ r1_tarski(k2_relset_1(B_34,'#skF_2',D_43),'#skF_2')
      | ~ m1_subset_1(F_49,B_34)
      | ~ m1_subset_1(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
      | ~ m1_subset_1(D_43,k1_zfmisc_1(k2_zfmisc_1(B_34,'#skF_2')))
      | ~ v1_funct_2(D_43,B_34,'#skF_2')
      | ~ v1_funct_1(D_43) ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_616])).

tff(c_639,plain,(
    ~ m1_subset_1(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_617])).

tff(c_642,plain,
    ( ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3')))
    | ~ v1_funct_1('#skF_5')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_32,c_639])).

tff(c_646,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_58,c_56,c_54,c_642])).

tff(c_648,plain,(
    m1_subset_1(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_617])).

tff(c_186,plain,(
    ! [A_115,B_116,C_117,D_118] :
      ( k3_funct_2(A_115,B_116,C_117,D_118) = k1_funct_1(C_117,D_118)
      | ~ m1_subset_1(D_118,A_115)
      | ~ m1_subset_1(C_117,k1_zfmisc_1(k2_zfmisc_1(A_115,B_116)))
      | ~ v1_funct_2(C_117,A_115,B_116)
      | ~ v1_funct_1(C_117)
      | v1_xboole_0(A_115) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_192,plain,(
    ! [B_116,C_117] :
      ( k3_funct_2('#skF_2',B_116,C_117,'#skF_6') = k1_funct_1(C_117,'#skF_6')
      | ~ m1_subset_1(C_117,k1_zfmisc_1(k2_zfmisc_1('#skF_2',B_116)))
      | ~ v1_funct_2(C_117,'#skF_2',B_116)
      | ~ v1_funct_1(C_117)
      | v1_xboole_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_52,c_186])).

tff(c_197,plain,(
    ! [B_116,C_117] :
      ( k3_funct_2('#skF_2',B_116,C_117,'#skF_6') = k1_funct_1(C_117,'#skF_6')
      | ~ m1_subset_1(C_117,k1_zfmisc_1(k2_zfmisc_1('#skF_2',B_116)))
      | ~ v1_funct_2(C_117,'#skF_2',B_116)
      | ~ v1_funct_1(C_117) ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_192])).

tff(c_667,plain,
    ( k3_funct_2('#skF_2','#skF_3',k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),'#skF_6') = k1_funct_1(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),'#skF_6')
    | ~ v1_funct_2(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),'#skF_2','#skF_3')
    | ~ v1_funct_1(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_648,c_197])).

tff(c_720,plain,(
    k3_funct_2('#skF_2','#skF_3',k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),'#skF_6') = k1_funct_1(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_239,c_246,c_667])).

tff(c_198,plain,(
    ! [B_119,C_120] :
      ( k3_funct_2('#skF_2',B_119,C_120,'#skF_6') = k1_funct_1(C_120,'#skF_6')
      | ~ m1_subset_1(C_120,k1_zfmisc_1(k2_zfmisc_1('#skF_2',B_119)))
      | ~ v1_funct_2(C_120,'#skF_2',B_119)
      | ~ v1_funct_1(C_120) ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_192])).

tff(c_201,plain,
    ( k3_funct_2('#skF_2','#skF_1','#skF_4','#skF_6') = k1_funct_1('#skF_4','#skF_6')
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_58,c_198])).

tff(c_204,plain,(
    k3_funct_2('#skF_2','#skF_1','#skF_4','#skF_6') = k1_funct_1('#skF_4','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_201])).

tff(c_48,plain,(
    k3_funct_2('#skF_2','#skF_3',k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),'#skF_6') != k7_partfun1('#skF_3','#skF_5',k3_funct_2('#skF_2','#skF_1','#skF_4','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_172])).

tff(c_205,plain,(
    k3_funct_2('#skF_2','#skF_3',k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),'#skF_6') != k7_partfun1('#skF_3','#skF_5',k1_funct_1('#skF_4','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_204,c_48])).

tff(c_742,plain,(
    k7_partfun1('#skF_3','#skF_5',k1_funct_1('#skF_4','#skF_6')) != k1_funct_1(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_720,c_205])).

tff(c_749,plain,(
    ~ m1_subset_1('#skF_6','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_492,c_742])).

tff(c_753,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_749])).

tff(c_754,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_164])).

tff(c_762,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_754,c_2])).

tff(c_764,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_127,c_762])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 21:07:51 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.58/1.61  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.58/1.62  
% 3.58/1.62  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.58/1.62  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k8_funct_2 > k3_funct_2 > k7_partfun1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 3.58/1.62  
% 3.58/1.62  %Foreground sorts:
% 3.58/1.62  
% 3.58/1.62  
% 3.58/1.62  %Background operators:
% 3.58/1.62  
% 3.58/1.62  
% 3.58/1.62  %Foreground operators:
% 3.58/1.62  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 3.58/1.62  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.58/1.62  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.58/1.62  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.58/1.62  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.58/1.62  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.58/1.62  tff(k7_partfun1, type, k7_partfun1: ($i * $i * $i) > $i).
% 3.58/1.62  tff('#skF_5', type, '#skF_5': $i).
% 3.58/1.62  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.58/1.62  tff(k8_funct_2, type, k8_funct_2: ($i * $i * $i * $i * $i) > $i).
% 3.58/1.62  tff('#skF_6', type, '#skF_6': $i).
% 3.58/1.62  tff('#skF_2', type, '#skF_2': $i).
% 3.58/1.62  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 3.58/1.62  tff('#skF_3', type, '#skF_3': $i).
% 3.58/1.62  tff('#skF_1', type, '#skF_1': $i).
% 3.58/1.62  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.58/1.62  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.58/1.62  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.58/1.62  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.58/1.62  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.58/1.62  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.58/1.62  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.58/1.62  tff('#skF_4', type, '#skF_4': $i).
% 3.58/1.62  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.58/1.62  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.58/1.62  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.58/1.62  tff(k3_funct_2, type, k3_funct_2: ($i * $i * $i * $i) > $i).
% 3.58/1.62  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.58/1.62  
% 3.58/1.64  tff(f_172, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C, D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (![E]: ((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, C)))) => (![F]: (m1_subset_1(F, B) => (v1_partfun1(E, A) => (k3_funct_2(B, C, k8_funct_2(B, A, C, D, E), F) = k7_partfun1(C, E, k3_funct_2(B, A, D, F)))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t193_funct_2)).
% 3.58/1.64  tff(f_62, axiom, (![A, B]: ((~v1_xboole_0(A) & v1_xboole_0(B)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ~v1_partfun1(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_partfun1)).
% 3.58/1.64  tff(f_41, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 3.58/1.64  tff(f_33, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 3.58/1.64  tff(f_47, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.58/1.64  tff(f_39, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 3.58/1.64  tff(f_121, axiom, (![A, B, C]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (v1_partfun1(C, A) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t131_funct_2)).
% 3.58/1.64  tff(f_80, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 3.58/1.64  tff(f_51, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 3.58/1.64  tff(f_145, axiom, (![A, B, C]: (~v1_xboole_0(C) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, C)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (![E]: ((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(C, A)))) => (![F]: (m1_subset_1(F, B) => (r1_tarski(k2_relset_1(B, C, D), k1_relset_1(C, A, E)) => ((B = k1_xboole_0) | (k1_funct_1(k8_funct_2(B, C, A, D, E), F) = k7_partfun1(A, E, k1_funct_1(D, F))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t186_funct_2)).
% 3.58/1.64  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 3.58/1.64  tff(f_96, axiom, (![A, B, C, D, E]: (((((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(E)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => ((v1_funct_1(k8_funct_2(A, B, C, D, E)) & v1_funct_2(k8_funct_2(A, B, C, D, E), A, C)) & m1_subset_1(k8_funct_2(A, B, C, D, E), k1_zfmisc_1(k2_zfmisc_1(A, C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k8_funct_2)).
% 3.58/1.64  tff(f_109, axiom, (![A, B, C, D]: (((((~v1_xboole_0(A) & v1_funct_1(C)) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & m1_subset_1(D, A)) => (k3_funct_2(A, B, C, D) = k1_funct_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k3_funct_2)).
% 3.58/1.64  tff(c_66, plain, (~v1_xboole_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_172])).
% 3.58/1.64  tff(c_50, plain, (v1_partfun1('#skF_5', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_172])).
% 3.58/1.64  tff(c_54, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_172])).
% 3.58/1.64  tff(c_115, plain, (![C_97, A_98, B_99]: (~v1_partfun1(C_97, A_98) | ~m1_subset_1(C_97, k1_zfmisc_1(k2_zfmisc_1(A_98, B_99))) | ~v1_xboole_0(B_99) | v1_xboole_0(A_98))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.58/1.64  tff(c_121, plain, (~v1_partfun1('#skF_5', '#skF_1') | ~v1_xboole_0('#skF_3') | v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_54, c_115])).
% 3.58/1.64  tff(c_126, plain, (~v1_xboole_0('#skF_3') | v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_121])).
% 3.58/1.64  tff(c_127, plain, (~v1_xboole_0('#skF_3')), inference(negUnitSimplification, [status(thm)], [c_66, c_126])).
% 3.58/1.64  tff(c_52, plain, (m1_subset_1('#skF_6', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_172])).
% 3.58/1.64  tff(c_10, plain, (![A_6, B_7]: (v1_relat_1(k2_zfmisc_1(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.58/1.64  tff(c_58, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_172])).
% 3.58/1.64  tff(c_68, plain, (![B_81, A_82]: (v1_relat_1(B_81) | ~m1_subset_1(B_81, k1_zfmisc_1(A_82)) | ~v1_relat_1(A_82))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.58/1.64  tff(c_71, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_1'))), inference(resolution, [status(thm)], [c_58, c_68])).
% 3.58/1.64  tff(c_77, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_10, c_71])).
% 3.58/1.64  tff(c_87, plain, (![C_87, B_88, A_89]: (v5_relat_1(C_87, B_88) | ~m1_subset_1(C_87, k1_zfmisc_1(k2_zfmisc_1(A_89, B_88))))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.58/1.64  tff(c_94, plain, (v5_relat_1('#skF_4', '#skF_1')), inference(resolution, [status(thm)], [c_58, c_87])).
% 3.58/1.64  tff(c_8, plain, (![B_5, A_4]: (r1_tarski(k2_relat_1(B_5), A_4) | ~v5_relat_1(B_5, A_4) | ~v1_relat_1(B_5))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.58/1.64  tff(c_56, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_172])).
% 3.58/1.64  tff(c_137, plain, (![C_102, A_103, B_104]: (v1_funct_2(C_102, A_103, B_104) | ~v1_partfun1(C_102, A_103) | ~m1_subset_1(C_102, k1_zfmisc_1(k2_zfmisc_1(A_103, B_104))) | ~v1_funct_1(C_102))), inference(cnfTransformation, [status(thm)], [f_121])).
% 3.58/1.64  tff(c_143, plain, (v1_funct_2('#skF_5', '#skF_1', '#skF_3') | ~v1_partfun1('#skF_5', '#skF_1') | ~v1_funct_1('#skF_5')), inference(resolution, [status(thm)], [c_54, c_137])).
% 3.58/1.64  tff(c_149, plain, (v1_funct_2('#skF_5', '#skF_1', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_50, c_143])).
% 3.58/1.64  tff(c_152, plain, (![B_109, A_110, C_111]: (k1_xboole_0=B_109 | k1_relset_1(A_110, B_109, C_111)=A_110 | ~v1_funct_2(C_111, A_110, B_109) | ~m1_subset_1(C_111, k1_zfmisc_1(k2_zfmisc_1(A_110, B_109))))), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.58/1.64  tff(c_158, plain, (k1_xboole_0='#skF_3' | k1_relset_1('#skF_1', '#skF_3', '#skF_5')='#skF_1' | ~v1_funct_2('#skF_5', '#skF_1', '#skF_3')), inference(resolution, [status(thm)], [c_54, c_152])).
% 3.58/1.64  tff(c_164, plain, (k1_xboole_0='#skF_3' | k1_relset_1('#skF_1', '#skF_3', '#skF_5')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_149, c_158])).
% 3.58/1.64  tff(c_181, plain, (k1_relset_1('#skF_1', '#skF_3', '#skF_5')='#skF_1'), inference(splitLeft, [status(thm)], [c_164])).
% 3.58/1.64  tff(c_64, plain, (~v1_xboole_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_172])).
% 3.58/1.64  tff(c_62, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_172])).
% 3.58/1.64  tff(c_60, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_172])).
% 3.58/1.64  tff(c_106, plain, (![A_94, B_95, C_96]: (k2_relset_1(A_94, B_95, C_96)=k2_relat_1(C_96) | ~m1_subset_1(C_96, k1_zfmisc_1(k2_zfmisc_1(A_94, B_95))))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.58/1.64  tff(c_113, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_58, c_106])).
% 3.58/1.64  tff(c_330, plain, (![E_148, F_145, A_144, D_147, B_149, C_146]: (k7_partfun1(A_144, E_148, k1_funct_1(D_147, F_145))=k1_funct_1(k8_funct_2(B_149, C_146, A_144, D_147, E_148), F_145) | k1_xboole_0=B_149 | ~r1_tarski(k2_relset_1(B_149, C_146, D_147), k1_relset_1(C_146, A_144, E_148)) | ~m1_subset_1(F_145, B_149) | ~m1_subset_1(E_148, k1_zfmisc_1(k2_zfmisc_1(C_146, A_144))) | ~v1_funct_1(E_148) | ~m1_subset_1(D_147, k1_zfmisc_1(k2_zfmisc_1(B_149, C_146))) | ~v1_funct_2(D_147, B_149, C_146) | ~v1_funct_1(D_147) | v1_xboole_0(C_146))), inference(cnfTransformation, [status(thm)], [f_145])).
% 3.58/1.64  tff(c_338, plain, (![A_144, E_148, F_145]: (k7_partfun1(A_144, E_148, k1_funct_1('#skF_4', F_145))=k1_funct_1(k8_funct_2('#skF_2', '#skF_1', A_144, '#skF_4', E_148), F_145) | k1_xboole_0='#skF_2' | ~r1_tarski(k2_relat_1('#skF_4'), k1_relset_1('#skF_1', A_144, E_148)) | ~m1_subset_1(F_145, '#skF_2') | ~m1_subset_1(E_148, k1_zfmisc_1(k2_zfmisc_1('#skF_1', A_144))) | ~v1_funct_1(E_148) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4') | v1_xboole_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_113, c_330])).
% 3.58/1.64  tff(c_349, plain, (![A_144, E_148, F_145]: (k7_partfun1(A_144, E_148, k1_funct_1('#skF_4', F_145))=k1_funct_1(k8_funct_2('#skF_2', '#skF_1', A_144, '#skF_4', E_148), F_145) | k1_xboole_0='#skF_2' | ~r1_tarski(k2_relat_1('#skF_4'), k1_relset_1('#skF_1', A_144, E_148)) | ~m1_subset_1(F_145, '#skF_2') | ~m1_subset_1(E_148, k1_zfmisc_1(k2_zfmisc_1('#skF_1', A_144))) | ~v1_funct_1(E_148) | v1_xboole_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_58, c_338])).
% 3.58/1.64  tff(c_350, plain, (![A_144, E_148, F_145]: (k7_partfun1(A_144, E_148, k1_funct_1('#skF_4', F_145))=k1_funct_1(k8_funct_2('#skF_2', '#skF_1', A_144, '#skF_4', E_148), F_145) | k1_xboole_0='#skF_2' | ~r1_tarski(k2_relat_1('#skF_4'), k1_relset_1('#skF_1', A_144, E_148)) | ~m1_subset_1(F_145, '#skF_2') | ~m1_subset_1(E_148, k1_zfmisc_1(k2_zfmisc_1('#skF_1', A_144))) | ~v1_funct_1(E_148))), inference(negUnitSimplification, [status(thm)], [c_66, c_349])).
% 3.58/1.64  tff(c_445, plain, (k1_xboole_0='#skF_2'), inference(splitLeft, [status(thm)], [c_350])).
% 3.58/1.64  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 3.58/1.64  tff(c_453, plain, (v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_445, c_2])).
% 3.58/1.64  tff(c_455, plain, $false, inference(negUnitSimplification, [status(thm)], [c_64, c_453])).
% 3.58/1.64  tff(c_459, plain, (![A_182, E_183, F_184]: (k7_partfun1(A_182, E_183, k1_funct_1('#skF_4', F_184))=k1_funct_1(k8_funct_2('#skF_2', '#skF_1', A_182, '#skF_4', E_183), F_184) | ~r1_tarski(k2_relat_1('#skF_4'), k1_relset_1('#skF_1', A_182, E_183)) | ~m1_subset_1(F_184, '#skF_2') | ~m1_subset_1(E_183, k1_zfmisc_1(k2_zfmisc_1('#skF_1', A_182))) | ~v1_funct_1(E_183))), inference(splitRight, [status(thm)], [c_350])).
% 3.58/1.64  tff(c_461, plain, (![F_184]: (k7_partfun1('#skF_3', '#skF_5', k1_funct_1('#skF_4', F_184))=k1_funct_1(k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), F_184) | ~r1_tarski(k2_relat_1('#skF_4'), '#skF_1') | ~m1_subset_1(F_184, '#skF_2') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3'))) | ~v1_funct_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_181, c_459])).
% 3.58/1.64  tff(c_466, plain, (![F_184]: (k7_partfun1('#skF_3', '#skF_5', k1_funct_1('#skF_4', F_184))=k1_funct_1(k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), F_184) | ~r1_tarski(k2_relat_1('#skF_4'), '#skF_1') | ~m1_subset_1(F_184, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_461])).
% 3.58/1.64  tff(c_484, plain, (~r1_tarski(k2_relat_1('#skF_4'), '#skF_1')), inference(splitLeft, [status(thm)], [c_466])).
% 3.58/1.64  tff(c_487, plain, (~v5_relat_1('#skF_4', '#skF_1') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_8, c_484])).
% 3.58/1.64  tff(c_491, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_77, c_94, c_487])).
% 3.58/1.64  tff(c_492, plain, (![F_184]: (k7_partfun1('#skF_3', '#skF_5', k1_funct_1('#skF_4', F_184))=k1_funct_1(k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), F_184) | ~m1_subset_1(F_184, '#skF_2'))), inference(splitRight, [status(thm)], [c_466])).
% 3.58/1.64  tff(c_210, plain, (![D_122, A_121, E_125, B_124, C_123]: (v1_funct_1(k8_funct_2(A_121, B_124, C_123, D_122, E_125)) | ~m1_subset_1(E_125, k1_zfmisc_1(k2_zfmisc_1(B_124, C_123))) | ~v1_funct_1(E_125) | ~m1_subset_1(D_122, k1_zfmisc_1(k2_zfmisc_1(A_121, B_124))) | ~v1_funct_2(D_122, A_121, B_124) | ~v1_funct_1(D_122))), inference(cnfTransformation, [status(thm)], [f_96])).
% 3.58/1.64  tff(c_214, plain, (![A_121, D_122]: (v1_funct_1(k8_funct_2(A_121, '#skF_1', '#skF_3', D_122, '#skF_5')) | ~v1_funct_1('#skF_5') | ~m1_subset_1(D_122, k1_zfmisc_1(k2_zfmisc_1(A_121, '#skF_1'))) | ~v1_funct_2(D_122, A_121, '#skF_1') | ~v1_funct_1(D_122))), inference(resolution, [status(thm)], [c_54, c_210])).
% 3.58/1.64  tff(c_233, plain, (![A_133, D_134]: (v1_funct_1(k8_funct_2(A_133, '#skF_1', '#skF_3', D_134, '#skF_5')) | ~m1_subset_1(D_134, k1_zfmisc_1(k2_zfmisc_1(A_133, '#skF_1'))) | ~v1_funct_2(D_134, A_133, '#skF_1') | ~v1_funct_1(D_134))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_214])).
% 3.58/1.64  tff(c_236, plain, (v1_funct_1(k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5')) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_58, c_233])).
% 3.58/1.64  tff(c_239, plain, (v1_funct_1(k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_236])).
% 3.58/1.64  tff(c_221, plain, (![D_127, C_128, B_129, E_130, A_126]: (v1_funct_2(k8_funct_2(A_126, B_129, C_128, D_127, E_130), A_126, C_128) | ~m1_subset_1(E_130, k1_zfmisc_1(k2_zfmisc_1(B_129, C_128))) | ~v1_funct_1(E_130) | ~m1_subset_1(D_127, k1_zfmisc_1(k2_zfmisc_1(A_126, B_129))) | ~v1_funct_2(D_127, A_126, B_129) | ~v1_funct_1(D_127))), inference(cnfTransformation, [status(thm)], [f_96])).
% 3.58/1.64  tff(c_225, plain, (![A_126, D_127]: (v1_funct_2(k8_funct_2(A_126, '#skF_1', '#skF_3', D_127, '#skF_5'), A_126, '#skF_3') | ~v1_funct_1('#skF_5') | ~m1_subset_1(D_127, k1_zfmisc_1(k2_zfmisc_1(A_126, '#skF_1'))) | ~v1_funct_2(D_127, A_126, '#skF_1') | ~v1_funct_1(D_127))), inference(resolution, [status(thm)], [c_54, c_221])).
% 3.58/1.64  tff(c_241, plain, (![A_135, D_136]: (v1_funct_2(k8_funct_2(A_135, '#skF_1', '#skF_3', D_136, '#skF_5'), A_135, '#skF_3') | ~m1_subset_1(D_136, k1_zfmisc_1(k2_zfmisc_1(A_135, '#skF_1'))) | ~v1_funct_2(D_136, A_135, '#skF_1') | ~v1_funct_1(D_136))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_225])).
% 3.58/1.64  tff(c_243, plain, (v1_funct_2(k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), '#skF_2', '#skF_3') | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_58, c_241])).
% 3.58/1.64  tff(c_246, plain, (v1_funct_2(k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), '#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_243])).
% 3.58/1.64  tff(c_32, plain, (![A_21, B_22, D_24, C_23, E_25]: (m1_subset_1(k8_funct_2(A_21, B_22, C_23, D_24, E_25), k1_zfmisc_1(k2_zfmisc_1(A_21, C_23))) | ~m1_subset_1(E_25, k1_zfmisc_1(k2_zfmisc_1(B_22, C_23))) | ~v1_funct_1(E_25) | ~m1_subset_1(D_24, k1_zfmisc_1(k2_zfmisc_1(A_21, B_22))) | ~v1_funct_2(D_24, A_21, B_22) | ~v1_funct_1(D_24))), inference(cnfTransformation, [status(thm)], [f_96])).
% 3.58/1.64  tff(c_248, plain, (![E_143, A_139, C_141, B_142, D_140]: (m1_subset_1(k8_funct_2(A_139, B_142, C_141, D_140, E_143), k1_zfmisc_1(k2_zfmisc_1(A_139, C_141))) | ~m1_subset_1(E_143, k1_zfmisc_1(k2_zfmisc_1(B_142, C_141))) | ~v1_funct_1(E_143) | ~m1_subset_1(D_140, k1_zfmisc_1(k2_zfmisc_1(A_139, B_142))) | ~v1_funct_2(D_140, A_139, B_142) | ~v1_funct_1(D_140))), inference(cnfTransformation, [status(thm)], [f_96])).
% 3.58/1.64  tff(c_30, plain, (![B_19, A_18, C_20]: (k1_xboole_0=B_19 | k1_relset_1(A_18, B_19, C_20)=A_18 | ~v1_funct_2(C_20, A_18, B_19) | ~m1_subset_1(C_20, k1_zfmisc_1(k2_zfmisc_1(A_18, B_19))))), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.58/1.64  tff(c_589, plain, (![B_219, C_222, A_218, D_221, E_220]: (k1_xboole_0=C_222 | k1_relset_1(A_218, C_222, k8_funct_2(A_218, B_219, C_222, D_221, E_220))=A_218 | ~v1_funct_2(k8_funct_2(A_218, B_219, C_222, D_221, E_220), A_218, C_222) | ~m1_subset_1(E_220, k1_zfmisc_1(k2_zfmisc_1(B_219, C_222))) | ~v1_funct_1(E_220) | ~m1_subset_1(D_221, k1_zfmisc_1(k2_zfmisc_1(A_218, B_219))) | ~v1_funct_2(D_221, A_218, B_219) | ~v1_funct_1(D_221))), inference(resolution, [status(thm)], [c_248, c_30])).
% 3.58/1.64  tff(c_591, plain, (k1_xboole_0='#skF_3' | k1_relset_1('#skF_2', '#skF_3', k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'))='#skF_2' | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3'))) | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_246, c_589])).
% 3.58/1.64  tff(c_594, plain, (k1_xboole_0='#skF_3' | k1_relset_1('#skF_2', '#skF_3', k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_58, c_56, c_54, c_591])).
% 3.58/1.64  tff(c_595, plain, (k1_relset_1('#skF_2', '#skF_3', k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'))='#skF_2'), inference(splitLeft, [status(thm)], [c_594])).
% 3.58/1.64  tff(c_46, plain, (![F_49, E_47, A_33, B_34, D_43, C_35]: (k7_partfun1(A_33, E_47, k1_funct_1(D_43, F_49))=k1_funct_1(k8_funct_2(B_34, C_35, A_33, D_43, E_47), F_49) | k1_xboole_0=B_34 | ~r1_tarski(k2_relset_1(B_34, C_35, D_43), k1_relset_1(C_35, A_33, E_47)) | ~m1_subset_1(F_49, B_34) | ~m1_subset_1(E_47, k1_zfmisc_1(k2_zfmisc_1(C_35, A_33))) | ~v1_funct_1(E_47) | ~m1_subset_1(D_43, k1_zfmisc_1(k2_zfmisc_1(B_34, C_35))) | ~v1_funct_2(D_43, B_34, C_35) | ~v1_funct_1(D_43) | v1_xboole_0(C_35))), inference(cnfTransformation, [status(thm)], [f_145])).
% 3.58/1.64  tff(c_612, plain, (![D_43, F_49, B_34]: (k7_partfun1('#skF_3', k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), k1_funct_1(D_43, F_49))=k1_funct_1(k8_funct_2(B_34, '#skF_2', '#skF_3', D_43, k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5')), F_49) | k1_xboole_0=B_34 | ~r1_tarski(k2_relset_1(B_34, '#skF_2', D_43), '#skF_2') | ~m1_subset_1(F_49, B_34) | ~m1_subset_1(k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~v1_funct_1(k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5')) | ~m1_subset_1(D_43, k1_zfmisc_1(k2_zfmisc_1(B_34, '#skF_2'))) | ~v1_funct_2(D_43, B_34, '#skF_2') | ~v1_funct_1(D_43) | v1_xboole_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_595, c_46])).
% 3.58/1.64  tff(c_616, plain, (![D_43, F_49, B_34]: (k7_partfun1('#skF_3', k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), k1_funct_1(D_43, F_49))=k1_funct_1(k8_funct_2(B_34, '#skF_2', '#skF_3', D_43, k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5')), F_49) | k1_xboole_0=B_34 | ~r1_tarski(k2_relset_1(B_34, '#skF_2', D_43), '#skF_2') | ~m1_subset_1(F_49, B_34) | ~m1_subset_1(k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~m1_subset_1(D_43, k1_zfmisc_1(k2_zfmisc_1(B_34, '#skF_2'))) | ~v1_funct_2(D_43, B_34, '#skF_2') | ~v1_funct_1(D_43) | v1_xboole_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_239, c_612])).
% 3.58/1.64  tff(c_617, plain, (![D_43, F_49, B_34]: (k7_partfun1('#skF_3', k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), k1_funct_1(D_43, F_49))=k1_funct_1(k8_funct_2(B_34, '#skF_2', '#skF_3', D_43, k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5')), F_49) | k1_xboole_0=B_34 | ~r1_tarski(k2_relset_1(B_34, '#skF_2', D_43), '#skF_2') | ~m1_subset_1(F_49, B_34) | ~m1_subset_1(k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~m1_subset_1(D_43, k1_zfmisc_1(k2_zfmisc_1(B_34, '#skF_2'))) | ~v1_funct_2(D_43, B_34, '#skF_2') | ~v1_funct_1(D_43))), inference(negUnitSimplification, [status(thm)], [c_64, c_616])).
% 3.58/1.64  tff(c_639, plain, (~m1_subset_1(k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(splitLeft, [status(thm)], [c_617])).
% 3.58/1.64  tff(c_642, plain, (~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3'))) | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_32, c_639])).
% 3.58/1.64  tff(c_646, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_58, c_56, c_54, c_642])).
% 3.58/1.64  tff(c_648, plain, (m1_subset_1(k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(splitRight, [status(thm)], [c_617])).
% 3.58/1.64  tff(c_186, plain, (![A_115, B_116, C_117, D_118]: (k3_funct_2(A_115, B_116, C_117, D_118)=k1_funct_1(C_117, D_118) | ~m1_subset_1(D_118, A_115) | ~m1_subset_1(C_117, k1_zfmisc_1(k2_zfmisc_1(A_115, B_116))) | ~v1_funct_2(C_117, A_115, B_116) | ~v1_funct_1(C_117) | v1_xboole_0(A_115))), inference(cnfTransformation, [status(thm)], [f_109])).
% 3.58/1.64  tff(c_192, plain, (![B_116, C_117]: (k3_funct_2('#skF_2', B_116, C_117, '#skF_6')=k1_funct_1(C_117, '#skF_6') | ~m1_subset_1(C_117, k1_zfmisc_1(k2_zfmisc_1('#skF_2', B_116))) | ~v1_funct_2(C_117, '#skF_2', B_116) | ~v1_funct_1(C_117) | v1_xboole_0('#skF_2'))), inference(resolution, [status(thm)], [c_52, c_186])).
% 3.58/1.64  tff(c_197, plain, (![B_116, C_117]: (k3_funct_2('#skF_2', B_116, C_117, '#skF_6')=k1_funct_1(C_117, '#skF_6') | ~m1_subset_1(C_117, k1_zfmisc_1(k2_zfmisc_1('#skF_2', B_116))) | ~v1_funct_2(C_117, '#skF_2', B_116) | ~v1_funct_1(C_117))), inference(negUnitSimplification, [status(thm)], [c_64, c_192])).
% 3.58/1.64  tff(c_667, plain, (k3_funct_2('#skF_2', '#skF_3', k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), '#skF_6')=k1_funct_1(k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), '#skF_6') | ~v1_funct_2(k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), '#skF_2', '#skF_3') | ~v1_funct_1(k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_648, c_197])).
% 3.58/1.64  tff(c_720, plain, (k3_funct_2('#skF_2', '#skF_3', k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), '#skF_6')=k1_funct_1(k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_239, c_246, c_667])).
% 3.58/1.64  tff(c_198, plain, (![B_119, C_120]: (k3_funct_2('#skF_2', B_119, C_120, '#skF_6')=k1_funct_1(C_120, '#skF_6') | ~m1_subset_1(C_120, k1_zfmisc_1(k2_zfmisc_1('#skF_2', B_119))) | ~v1_funct_2(C_120, '#skF_2', B_119) | ~v1_funct_1(C_120))), inference(negUnitSimplification, [status(thm)], [c_64, c_192])).
% 3.58/1.64  tff(c_201, plain, (k3_funct_2('#skF_2', '#skF_1', '#skF_4', '#skF_6')=k1_funct_1('#skF_4', '#skF_6') | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_58, c_198])).
% 3.58/1.64  tff(c_204, plain, (k3_funct_2('#skF_2', '#skF_1', '#skF_4', '#skF_6')=k1_funct_1('#skF_4', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_201])).
% 3.58/1.64  tff(c_48, plain, (k3_funct_2('#skF_2', '#skF_3', k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), '#skF_6')!=k7_partfun1('#skF_3', '#skF_5', k3_funct_2('#skF_2', '#skF_1', '#skF_4', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_172])).
% 3.58/1.64  tff(c_205, plain, (k3_funct_2('#skF_2', '#skF_3', k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), '#skF_6')!=k7_partfun1('#skF_3', '#skF_5', k1_funct_1('#skF_4', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_204, c_48])).
% 3.58/1.64  tff(c_742, plain, (k7_partfun1('#skF_3', '#skF_5', k1_funct_1('#skF_4', '#skF_6'))!=k1_funct_1(k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_720, c_205])).
% 3.58/1.64  tff(c_749, plain, (~m1_subset_1('#skF_6', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_492, c_742])).
% 3.58/1.64  tff(c_753, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_52, c_749])).
% 3.58/1.64  tff(c_754, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_164])).
% 3.58/1.64  tff(c_762, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_754, c_2])).
% 3.58/1.64  tff(c_764, plain, $false, inference(negUnitSimplification, [status(thm)], [c_127, c_762])).
% 3.58/1.64  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.58/1.64  
% 3.58/1.64  Inference rules
% 3.58/1.64  ----------------------
% 3.58/1.64  #Ref     : 0
% 3.58/1.64  #Sup     : 133
% 3.58/1.64  #Fact    : 0
% 3.58/1.64  #Define  : 0
% 3.58/1.64  #Split   : 9
% 3.58/1.64  #Chain   : 0
% 3.58/1.64  #Close   : 0
% 3.58/1.64  
% 3.58/1.64  Ordering : KBO
% 3.58/1.64  
% 3.58/1.64  Simplification rules
% 3.58/1.64  ----------------------
% 3.58/1.64  #Subsume      : 7
% 3.58/1.64  #Demod        : 177
% 3.58/1.64  #Tautology    : 32
% 3.58/1.64  #SimpNegUnit  : 14
% 3.58/1.64  #BackRed      : 28
% 3.58/1.64  
% 3.58/1.64  #Partial instantiations: 0
% 3.58/1.64  #Strategies tried      : 1
% 3.58/1.64  
% 3.58/1.64  Timing (in seconds)
% 3.58/1.64  ----------------------
% 3.58/1.65  Preprocessing        : 0.37
% 3.58/1.65  Parsing              : 0.20
% 3.58/1.65  CNF conversion       : 0.03
% 3.58/1.65  Main loop            : 0.42
% 3.58/1.65  Inferencing          : 0.14
% 3.58/1.65  Reduction            : 0.14
% 3.58/1.65  Demodulation         : 0.10
% 3.58/1.65  BG Simplification    : 0.03
% 3.58/1.65  Subsumption          : 0.08
% 3.58/1.65  Abstraction          : 0.02
% 3.58/1.65  MUC search           : 0.00
% 3.58/1.65  Cooper               : 0.00
% 3.58/1.65  Total                : 0.83
% 3.58/1.65  Index Insertion      : 0.00
% 3.58/1.65  Index Deletion       : 0.00
% 3.58/1.65  Index Matching       : 0.00
% 3.58/1.65  BG Taut test         : 0.00
%------------------------------------------------------------------------------
