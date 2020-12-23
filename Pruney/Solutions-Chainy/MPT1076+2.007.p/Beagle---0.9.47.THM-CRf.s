%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:18:13 EST 2020

% Result     : Theorem 4.47s
% Output     : CNFRefutation 4.84s
% Verified   : 
% Statistics : Number of formulae       :  152 ( 462 expanded)
%              Number of leaves         :   45 ( 183 expanded)
%              Depth                    :   17
%              Number of atoms          :  404 (2045 expanded)
%              Number of equality atoms :   66 ( 249 expanded)
%              Maximal formula depth    :   17 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k8_funct_2 > k3_funct_2 > k7_partfun1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_196,negated_conjecture,(
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

tff(f_84,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => ( v1_partfun1(B,A)
      <=> k1_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_partfun1)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_55,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_169,axiom,(
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

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_113,axiom,(
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

tff(f_126,axiom,(
    ! [A,B,C,D] :
      ( ( ~ v1_xboole_0(A)
        & v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,A) )
     => k3_funct_2(A,B,C,D) = k1_funct_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k3_funct_2)).

tff(f_76,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & v1_xboole_0(B) )
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => ~ v1_partfun1(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_partfun1)).

tff(f_65,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( ( v1_funct_1(C)
          & v1_partfun1(C,A) )
       => ( v1_funct_1(C)
          & v1_funct_2(C,A,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_funct_2)).

tff(f_97,axiom,(
    ! [A,B,C,D] :
      ( ( ~ v1_xboole_0(A)
        & v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,A) )
     => m1_subset_1(k3_funct_2(A,B,C,D),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_funct_2)).

tff(f_145,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ! [B] :
          ( ~ v1_xboole_0(B)
         => ! [C] :
              ( ( v1_funct_1(C)
                & v1_funct_2(C,A,B)
                & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
             => ! [D] :
                  ( m1_subset_1(D,A)
                 => k7_partfun1(B,C,D) = k3_funct_2(A,B,C,D) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t176_funct_2)).

tff(c_48,plain,(
    m1_subset_1('#skF_6','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_196])).

tff(c_10,plain,(
    ! [A_6,B_7] : v1_relat_1(k2_zfmisc_1(A_6,B_7)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_54,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_196])).

tff(c_64,plain,(
    ! [B_102,A_103] :
      ( v1_relat_1(B_102)
      | ~ m1_subset_1(B_102,k1_zfmisc_1(A_103))
      | ~ v1_relat_1(A_103) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_67,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_1')) ),
    inference(resolution,[status(thm)],[c_54,c_64])).

tff(c_73,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_67])).

tff(c_92,plain,(
    ! [C_111,B_112,A_113] :
      ( v5_relat_1(C_111,B_112)
      | ~ m1_subset_1(C_111,k1_zfmisc_1(k2_zfmisc_1(A_113,B_112))) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_99,plain,(
    v5_relat_1('#skF_4','#skF_1') ),
    inference(resolution,[status(thm)],[c_54,c_92])).

tff(c_8,plain,(
    ! [B_5,A_4] :
      ( r1_tarski(k2_relat_1(B_5),A_4)
      | ~ v5_relat_1(B_5,A_4)
      | ~ v1_relat_1(B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_52,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_196])).

tff(c_50,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_196])).

tff(c_70,plain,
    ( v1_relat_1('#skF_5')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_3')) ),
    inference(resolution,[status(thm)],[c_50,c_64])).

tff(c_76,plain,(
    v1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_70])).

tff(c_46,plain,(
    v1_partfun1('#skF_5','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_196])).

tff(c_78,plain,(
    ! [C_106,A_107,B_108] :
      ( v4_relat_1(C_106,A_107)
      | ~ m1_subset_1(C_106,k1_zfmisc_1(k2_zfmisc_1(A_107,B_108))) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_86,plain,(
    v4_relat_1('#skF_5','#skF_1') ),
    inference(resolution,[status(thm)],[c_50,c_78])).

tff(c_102,plain,(
    ! [B_115,A_116] :
      ( k1_relat_1(B_115) = A_116
      | ~ v1_partfun1(B_115,A_116)
      | ~ v4_relat_1(B_115,A_116)
      | ~ v1_relat_1(B_115) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_105,plain,
    ( k1_relat_1('#skF_5') = '#skF_1'
    | ~ v1_partfun1('#skF_5','#skF_1')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_86,c_102])).

tff(c_111,plain,(
    k1_relat_1('#skF_5') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_46,c_105])).

tff(c_142,plain,(
    ! [A_120,B_121,C_122] :
      ( k1_relset_1(A_120,B_121,C_122) = k1_relat_1(C_122)
      | ~ m1_subset_1(C_122,k1_zfmisc_1(k2_zfmisc_1(A_120,B_121))) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_148,plain,(
    k1_relset_1('#skF_1','#skF_3','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_50,c_142])).

tff(c_151,plain,(
    k1_relset_1('#skF_1','#skF_3','#skF_5') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_111,c_148])).

tff(c_60,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_196])).

tff(c_62,plain,(
    ~ v1_xboole_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_196])).

tff(c_58,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_196])).

tff(c_56,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_196])).

tff(c_115,plain,(
    ! [A_117,B_118,C_119] :
      ( k2_relset_1(A_117,B_118,C_119) = k2_relat_1(C_119)
      | ~ m1_subset_1(C_119,k1_zfmisc_1(k2_zfmisc_1(A_117,B_118))) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_122,plain,(
    k2_relset_1('#skF_2','#skF_1','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_54,c_115])).

tff(c_450,plain,(
    ! [C_176,D_179,E_181,B_178,A_177,F_180] :
      ( k1_funct_1(k8_funct_2(B_178,C_176,A_177,D_179,E_181),F_180) = k1_funct_1(E_181,k1_funct_1(D_179,F_180))
      | k1_xboole_0 = B_178
      | ~ r1_tarski(k2_relset_1(B_178,C_176,D_179),k1_relset_1(C_176,A_177,E_181))
      | ~ m1_subset_1(F_180,B_178)
      | ~ m1_subset_1(E_181,k1_zfmisc_1(k2_zfmisc_1(C_176,A_177)))
      | ~ v1_funct_1(E_181)
      | ~ m1_subset_1(D_179,k1_zfmisc_1(k2_zfmisc_1(B_178,C_176)))
      | ~ v1_funct_2(D_179,B_178,C_176)
      | ~ v1_funct_1(D_179)
      | v1_xboole_0(C_176) ) ),
    inference(cnfTransformation,[status(thm)],[f_169])).

tff(c_458,plain,(
    ! [A_177,E_181,F_180] :
      ( k1_funct_1(k8_funct_2('#skF_2','#skF_1',A_177,'#skF_4',E_181),F_180) = k1_funct_1(E_181,k1_funct_1('#skF_4',F_180))
      | k1_xboole_0 = '#skF_2'
      | ~ r1_tarski(k2_relat_1('#skF_4'),k1_relset_1('#skF_1',A_177,E_181))
      | ~ m1_subset_1(F_180,'#skF_2')
      | ~ m1_subset_1(E_181,k1_zfmisc_1(k2_zfmisc_1('#skF_1',A_177)))
      | ~ v1_funct_1(E_181)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
      | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
      | ~ v1_funct_1('#skF_4')
      | v1_xboole_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_122,c_450])).

tff(c_469,plain,(
    ! [A_177,E_181,F_180] :
      ( k1_funct_1(k8_funct_2('#skF_2','#skF_1',A_177,'#skF_4',E_181),F_180) = k1_funct_1(E_181,k1_funct_1('#skF_4',F_180))
      | k1_xboole_0 = '#skF_2'
      | ~ r1_tarski(k2_relat_1('#skF_4'),k1_relset_1('#skF_1',A_177,E_181))
      | ~ m1_subset_1(F_180,'#skF_2')
      | ~ m1_subset_1(E_181,k1_zfmisc_1(k2_zfmisc_1('#skF_1',A_177)))
      | ~ v1_funct_1(E_181)
      | v1_xboole_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_54,c_458])).

tff(c_470,plain,(
    ! [A_177,E_181,F_180] :
      ( k1_funct_1(k8_funct_2('#skF_2','#skF_1',A_177,'#skF_4',E_181),F_180) = k1_funct_1(E_181,k1_funct_1('#skF_4',F_180))
      | k1_xboole_0 = '#skF_2'
      | ~ r1_tarski(k2_relat_1('#skF_4'),k1_relset_1('#skF_1',A_177,E_181))
      | ~ m1_subset_1(F_180,'#skF_2')
      | ~ m1_subset_1(E_181,k1_zfmisc_1(k2_zfmisc_1('#skF_1',A_177)))
      | ~ v1_funct_1(E_181) ) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_469])).

tff(c_597,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_470])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_599,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_597,c_2])).

tff(c_601,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_599])).

tff(c_627,plain,(
    ! [A_222,E_223,F_224] :
      ( k1_funct_1(k8_funct_2('#skF_2','#skF_1',A_222,'#skF_4',E_223),F_224) = k1_funct_1(E_223,k1_funct_1('#skF_4',F_224))
      | ~ r1_tarski(k2_relat_1('#skF_4'),k1_relset_1('#skF_1',A_222,E_223))
      | ~ m1_subset_1(F_224,'#skF_2')
      | ~ m1_subset_1(E_223,k1_zfmisc_1(k2_zfmisc_1('#skF_1',A_222)))
      | ~ v1_funct_1(E_223) ) ),
    inference(splitRight,[status(thm)],[c_470])).

tff(c_629,plain,(
    ! [F_224] :
      ( k1_funct_1(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),F_224) = k1_funct_1('#skF_5',k1_funct_1('#skF_4',F_224))
      | ~ r1_tarski(k2_relat_1('#skF_4'),'#skF_1')
      | ~ m1_subset_1(F_224,'#skF_2')
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3')))
      | ~ v1_funct_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_151,c_627])).

tff(c_634,plain,(
    ! [F_224] :
      ( k1_funct_1(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),F_224) = k1_funct_1('#skF_5',k1_funct_1('#skF_4',F_224))
      | ~ r1_tarski(k2_relat_1('#skF_4'),'#skF_1')
      | ~ m1_subset_1(F_224,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_629])).

tff(c_639,plain,(
    ~ r1_tarski(k2_relat_1('#skF_4'),'#skF_1') ),
    inference(splitLeft,[status(thm)],[c_634])).

tff(c_642,plain,
    ( ~ v5_relat_1('#skF_4','#skF_1')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_8,c_639])).

tff(c_646,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_73,c_99,c_642])).

tff(c_647,plain,(
    ! [F_224] :
      ( k1_funct_1(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),F_224) = k1_funct_1('#skF_5',k1_funct_1('#skF_4',F_224))
      | ~ m1_subset_1(F_224,'#skF_2') ) ),
    inference(splitRight,[status(thm)],[c_634])).

tff(c_245,plain,(
    ! [A_143,E_144,C_141,D_145,B_142] :
      ( v1_funct_1(k8_funct_2(A_143,B_142,C_141,D_145,E_144))
      | ~ m1_subset_1(E_144,k1_zfmisc_1(k2_zfmisc_1(B_142,C_141)))
      | ~ v1_funct_1(E_144)
      | ~ m1_subset_1(D_145,k1_zfmisc_1(k2_zfmisc_1(A_143,B_142)))
      | ~ v1_funct_2(D_145,A_143,B_142)
      | ~ v1_funct_1(D_145) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_249,plain,(
    ! [A_143,D_145] :
      ( v1_funct_1(k8_funct_2(A_143,'#skF_1','#skF_3',D_145,'#skF_5'))
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1(D_145,k1_zfmisc_1(k2_zfmisc_1(A_143,'#skF_1')))
      | ~ v1_funct_2(D_145,A_143,'#skF_1')
      | ~ v1_funct_1(D_145) ) ),
    inference(resolution,[status(thm)],[c_50,c_245])).

tff(c_257,plain,(
    ! [A_148,D_149] :
      ( v1_funct_1(k8_funct_2(A_148,'#skF_1','#skF_3',D_149,'#skF_5'))
      | ~ m1_subset_1(D_149,k1_zfmisc_1(k2_zfmisc_1(A_148,'#skF_1')))
      | ~ v1_funct_2(D_149,A_148,'#skF_1')
      | ~ v1_funct_1(D_149) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_249])).

tff(c_260,plain,
    ( v1_funct_1(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_54,c_257])).

tff(c_263,plain,(
    v1_funct_1(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_260])).

tff(c_325,plain,(
    ! [C_158,D_162,B_159,A_160,E_161] :
      ( v1_funct_2(k8_funct_2(A_160,B_159,C_158,D_162,E_161),A_160,C_158)
      | ~ m1_subset_1(E_161,k1_zfmisc_1(k2_zfmisc_1(B_159,C_158)))
      | ~ v1_funct_1(E_161)
      | ~ m1_subset_1(D_162,k1_zfmisc_1(k2_zfmisc_1(A_160,B_159)))
      | ~ v1_funct_2(D_162,A_160,B_159)
      | ~ v1_funct_1(D_162) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_329,plain,(
    ! [A_160,D_162] :
      ( v1_funct_2(k8_funct_2(A_160,'#skF_1','#skF_3',D_162,'#skF_5'),A_160,'#skF_3')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1(D_162,k1_zfmisc_1(k2_zfmisc_1(A_160,'#skF_1')))
      | ~ v1_funct_2(D_162,A_160,'#skF_1')
      | ~ v1_funct_1(D_162) ) ),
    inference(resolution,[status(thm)],[c_50,c_325])).

tff(c_340,plain,(
    ! [A_163,D_164] :
      ( v1_funct_2(k8_funct_2(A_163,'#skF_1','#skF_3',D_164,'#skF_5'),A_163,'#skF_3')
      | ~ m1_subset_1(D_164,k1_zfmisc_1(k2_zfmisc_1(A_163,'#skF_1')))
      | ~ v1_funct_2(D_164,A_163,'#skF_1')
      | ~ v1_funct_1(D_164) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_329])).

tff(c_342,plain,
    ( v1_funct_2(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),'#skF_2','#skF_3')
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_54,c_340])).

tff(c_345,plain,(
    v1_funct_2(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),'#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_342])).

tff(c_32,plain,(
    ! [D_33,A_30,C_32,B_31,E_34] :
      ( m1_subset_1(k8_funct_2(A_30,B_31,C_32,D_33,E_34),k1_zfmisc_1(k2_zfmisc_1(A_30,C_32)))
      | ~ m1_subset_1(E_34,k1_zfmisc_1(k2_zfmisc_1(B_31,C_32)))
      | ~ v1_funct_1(E_34)
      | ~ m1_subset_1(D_33,k1_zfmisc_1(k2_zfmisc_1(A_30,B_31)))
      | ~ v1_funct_2(D_33,A_30,B_31)
      | ~ v1_funct_1(D_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_361,plain,(
    ! [C_171,B_172,E_174,D_175,A_173] :
      ( m1_subset_1(k8_funct_2(A_173,B_172,C_171,D_175,E_174),k1_zfmisc_1(k2_zfmisc_1(A_173,C_171)))
      | ~ m1_subset_1(E_174,k1_zfmisc_1(k2_zfmisc_1(B_172,C_171)))
      | ~ v1_funct_1(E_174)
      | ~ m1_subset_1(D_175,k1_zfmisc_1(k2_zfmisc_1(A_173,B_172)))
      | ~ v1_funct_2(D_175,A_173,B_172)
      | ~ v1_funct_1(D_175) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_16,plain,(
    ! [A_11,B_12,C_13] :
      ( k1_relset_1(A_11,B_12,C_13) = k1_relat_1(C_13)
      | ~ m1_subset_1(C_13,k1_zfmisc_1(k2_zfmisc_1(A_11,B_12))) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_798,plain,(
    ! [D_257,A_255,C_256,B_258,E_254] :
      ( k1_relset_1(A_255,C_256,k8_funct_2(A_255,B_258,C_256,D_257,E_254)) = k1_relat_1(k8_funct_2(A_255,B_258,C_256,D_257,E_254))
      | ~ m1_subset_1(E_254,k1_zfmisc_1(k2_zfmisc_1(B_258,C_256)))
      | ~ v1_funct_1(E_254)
      | ~ m1_subset_1(D_257,k1_zfmisc_1(k2_zfmisc_1(A_255,B_258)))
      | ~ v1_funct_2(D_257,A_255,B_258)
      | ~ v1_funct_1(D_257) ) ),
    inference(resolution,[status(thm)],[c_361,c_16])).

tff(c_804,plain,(
    ! [A_255,D_257] :
      ( k1_relset_1(A_255,'#skF_3',k8_funct_2(A_255,'#skF_1','#skF_3',D_257,'#skF_5')) = k1_relat_1(k8_funct_2(A_255,'#skF_1','#skF_3',D_257,'#skF_5'))
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1(D_257,k1_zfmisc_1(k2_zfmisc_1(A_255,'#skF_1')))
      | ~ v1_funct_2(D_257,A_255,'#skF_1')
      | ~ v1_funct_1(D_257) ) ),
    inference(resolution,[status(thm)],[c_50,c_798])).

tff(c_817,plain,(
    ! [A_261,D_262] :
      ( k1_relset_1(A_261,'#skF_3',k8_funct_2(A_261,'#skF_1','#skF_3',D_262,'#skF_5')) = k1_relat_1(k8_funct_2(A_261,'#skF_1','#skF_3',D_262,'#skF_5'))
      | ~ m1_subset_1(D_262,k1_zfmisc_1(k2_zfmisc_1(A_261,'#skF_1')))
      | ~ v1_funct_2(D_262,A_261,'#skF_1')
      | ~ v1_funct_1(D_262) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_804])).

tff(c_822,plain,
    ( k1_relset_1('#skF_2','#skF_3',k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5')) = k1_relat_1(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_54,c_817])).

tff(c_826,plain,(
    k1_relset_1('#skF_2','#skF_3',k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5')) = k1_relat_1(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_822])).

tff(c_42,plain,(
    ! [F_70,C_56,D_64,E_68,B_55,A_54] :
      ( k1_funct_1(k8_funct_2(B_55,C_56,A_54,D_64,E_68),F_70) = k1_funct_1(E_68,k1_funct_1(D_64,F_70))
      | k1_xboole_0 = B_55
      | ~ r1_tarski(k2_relset_1(B_55,C_56,D_64),k1_relset_1(C_56,A_54,E_68))
      | ~ m1_subset_1(F_70,B_55)
      | ~ m1_subset_1(E_68,k1_zfmisc_1(k2_zfmisc_1(C_56,A_54)))
      | ~ v1_funct_1(E_68)
      | ~ m1_subset_1(D_64,k1_zfmisc_1(k2_zfmisc_1(B_55,C_56)))
      | ~ v1_funct_2(D_64,B_55,C_56)
      | ~ v1_funct_1(D_64)
      | v1_xboole_0(C_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_169])).

tff(c_843,plain,(
    ! [B_55,D_64,F_70] :
      ( k1_funct_1(k8_funct_2(B_55,'#skF_2','#skF_3',D_64,k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5')),F_70) = k1_funct_1(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),k1_funct_1(D_64,F_70))
      | k1_xboole_0 = B_55
      | ~ r1_tarski(k2_relset_1(B_55,'#skF_2',D_64),k1_relat_1(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5')))
      | ~ m1_subset_1(F_70,B_55)
      | ~ m1_subset_1(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
      | ~ v1_funct_1(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'))
      | ~ m1_subset_1(D_64,k1_zfmisc_1(k2_zfmisc_1(B_55,'#skF_2')))
      | ~ v1_funct_2(D_64,B_55,'#skF_2')
      | ~ v1_funct_1(D_64)
      | v1_xboole_0('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_826,c_42])).

tff(c_847,plain,(
    ! [B_55,D_64,F_70] :
      ( k1_funct_1(k8_funct_2(B_55,'#skF_2','#skF_3',D_64,k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5')),F_70) = k1_funct_1(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),k1_funct_1(D_64,F_70))
      | k1_xboole_0 = B_55
      | ~ r1_tarski(k2_relset_1(B_55,'#skF_2',D_64),k1_relat_1(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5')))
      | ~ m1_subset_1(F_70,B_55)
      | ~ m1_subset_1(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
      | ~ m1_subset_1(D_64,k1_zfmisc_1(k2_zfmisc_1(B_55,'#skF_2')))
      | ~ v1_funct_2(D_64,B_55,'#skF_2')
      | ~ v1_funct_1(D_64)
      | v1_xboole_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_263,c_843])).

tff(c_848,plain,(
    ! [B_55,D_64,F_70] :
      ( k1_funct_1(k8_funct_2(B_55,'#skF_2','#skF_3',D_64,k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5')),F_70) = k1_funct_1(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),k1_funct_1(D_64,F_70))
      | k1_xboole_0 = B_55
      | ~ r1_tarski(k2_relset_1(B_55,'#skF_2',D_64),k1_relat_1(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5')))
      | ~ m1_subset_1(F_70,B_55)
      | ~ m1_subset_1(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
      | ~ m1_subset_1(D_64,k1_zfmisc_1(k2_zfmisc_1(B_55,'#skF_2')))
      | ~ v1_funct_2(D_64,B_55,'#skF_2')
      | ~ v1_funct_1(D_64) ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_847])).

tff(c_927,plain,(
    ~ m1_subset_1(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_848])).

tff(c_930,plain,
    ( ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3')))
    | ~ v1_funct_1('#skF_5')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_32,c_927])).

tff(c_934,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_54,c_52,c_50,c_930])).

tff(c_936,plain,(
    m1_subset_1(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_848])).

tff(c_201,plain,(
    ! [A_135,B_136,C_137,D_138] :
      ( k3_funct_2(A_135,B_136,C_137,D_138) = k1_funct_1(C_137,D_138)
      | ~ m1_subset_1(D_138,A_135)
      | ~ m1_subset_1(C_137,k1_zfmisc_1(k2_zfmisc_1(A_135,B_136)))
      | ~ v1_funct_2(C_137,A_135,B_136)
      | ~ v1_funct_1(C_137)
      | v1_xboole_0(A_135) ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_211,plain,(
    ! [B_136,C_137] :
      ( k3_funct_2('#skF_2',B_136,C_137,'#skF_6') = k1_funct_1(C_137,'#skF_6')
      | ~ m1_subset_1(C_137,k1_zfmisc_1(k2_zfmisc_1('#skF_2',B_136)))
      | ~ v1_funct_2(C_137,'#skF_2',B_136)
      | ~ v1_funct_1(C_137)
      | v1_xboole_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_48,c_201])).

tff(c_222,plain,(
    ! [B_136,C_137] :
      ( k3_funct_2('#skF_2',B_136,C_137,'#skF_6') = k1_funct_1(C_137,'#skF_6')
      | ~ m1_subset_1(C_137,k1_zfmisc_1(k2_zfmisc_1('#skF_2',B_136)))
      | ~ v1_funct_2(C_137,'#skF_2',B_136)
      | ~ v1_funct_1(C_137) ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_211])).

tff(c_962,plain,
    ( k3_funct_2('#skF_2','#skF_3',k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),'#skF_6') = k1_funct_1(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),'#skF_6')
    | ~ v1_funct_2(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),'#skF_2','#skF_3')
    | ~ v1_funct_1(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_936,c_222])).

tff(c_1022,plain,(
    k3_funct_2('#skF_2','#skF_3',k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),'#skF_6') = k1_funct_1(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_263,c_345,c_962])).

tff(c_160,plain,(
    ! [C_123,A_124,B_125] :
      ( ~ v1_partfun1(C_123,A_124)
      | ~ m1_subset_1(C_123,k1_zfmisc_1(k2_zfmisc_1(A_124,B_125)))
      | ~ v1_xboole_0(B_125)
      | v1_xboole_0(A_124) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_166,plain,
    ( ~ v1_partfun1('#skF_5','#skF_1')
    | ~ v1_xboole_0('#skF_3')
    | v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_50,c_160])).

tff(c_171,plain,
    ( ~ v1_xboole_0('#skF_3')
    | v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_166])).

tff(c_172,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_171])).

tff(c_173,plain,(
    ! [C_126,A_127,B_128] :
      ( v1_funct_2(C_126,A_127,B_128)
      | ~ v1_partfun1(C_126,A_127)
      | ~ v1_funct_1(C_126)
      | ~ m1_subset_1(C_126,k1_zfmisc_1(k2_zfmisc_1(A_127,B_128))) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_179,plain,
    ( v1_funct_2('#skF_5','#skF_1','#skF_3')
    | ~ v1_partfun1('#skF_5','#skF_1')
    | ~ v1_funct_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_50,c_173])).

tff(c_185,plain,(
    v1_funct_2('#skF_5','#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_46,c_179])).

tff(c_223,plain,(
    ! [B_139,C_140] :
      ( k3_funct_2('#skF_2',B_139,C_140,'#skF_6') = k1_funct_1(C_140,'#skF_6')
      | ~ m1_subset_1(C_140,k1_zfmisc_1(k2_zfmisc_1('#skF_2',B_139)))
      | ~ v1_funct_2(C_140,'#skF_2',B_139)
      | ~ v1_funct_1(C_140) ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_211])).

tff(c_226,plain,
    ( k3_funct_2('#skF_2','#skF_1','#skF_4','#skF_6') = k1_funct_1('#skF_4','#skF_6')
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_54,c_223])).

tff(c_229,plain,(
    k3_funct_2('#skF_2','#skF_1','#skF_4','#skF_6') = k1_funct_1('#skF_4','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_226])).

tff(c_186,plain,(
    ! [A_129,B_130,C_131,D_132] :
      ( m1_subset_1(k3_funct_2(A_129,B_130,C_131,D_132),B_130)
      | ~ m1_subset_1(D_132,A_129)
      | ~ m1_subset_1(C_131,k1_zfmisc_1(k2_zfmisc_1(A_129,B_130)))
      | ~ v1_funct_2(C_131,A_129,B_130)
      | ~ v1_funct_1(C_131)
      | v1_xboole_0(A_129) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_188,plain,(
    ! [D_132] :
      ( m1_subset_1(k3_funct_2('#skF_2','#skF_1','#skF_4',D_132),'#skF_1')
      | ~ m1_subset_1(D_132,'#skF_2')
      | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
      | ~ v1_funct_1('#skF_4')
      | v1_xboole_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_54,c_186])).

tff(c_193,plain,(
    ! [D_132] :
      ( m1_subset_1(k3_funct_2('#skF_2','#skF_1','#skF_4',D_132),'#skF_1')
      | ~ m1_subset_1(D_132,'#skF_2')
      | v1_xboole_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_188])).

tff(c_194,plain,(
    ! [D_132] :
      ( m1_subset_1(k3_funct_2('#skF_2','#skF_1','#skF_4',D_132),'#skF_1')
      | ~ m1_subset_1(D_132,'#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_193])).

tff(c_234,plain,
    ( m1_subset_1(k1_funct_1('#skF_4','#skF_6'),'#skF_1')
    | ~ m1_subset_1('#skF_6','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_229,c_194])).

tff(c_238,plain,(
    m1_subset_1(k1_funct_1('#skF_4','#skF_6'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_234])).

tff(c_38,plain,(
    ! [A_35,B_36,C_37,D_38] :
      ( k3_funct_2(A_35,B_36,C_37,D_38) = k1_funct_1(C_37,D_38)
      | ~ m1_subset_1(D_38,A_35)
      | ~ m1_subset_1(C_37,k1_zfmisc_1(k2_zfmisc_1(A_35,B_36)))
      | ~ v1_funct_2(C_37,A_35,B_36)
      | ~ v1_funct_1(C_37)
      | v1_xboole_0(A_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_241,plain,(
    ! [B_36,C_37] :
      ( k3_funct_2('#skF_1',B_36,C_37,k1_funct_1('#skF_4','#skF_6')) = k1_funct_1(C_37,k1_funct_1('#skF_4','#skF_6'))
      | ~ m1_subset_1(C_37,k1_zfmisc_1(k2_zfmisc_1('#skF_1',B_36)))
      | ~ v1_funct_2(C_37,'#skF_1',B_36)
      | ~ v1_funct_1(C_37)
      | v1_xboole_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_238,c_38])).

tff(c_264,plain,(
    ! [B_150,C_151] :
      ( k3_funct_2('#skF_1',B_150,C_151,k1_funct_1('#skF_4','#skF_6')) = k1_funct_1(C_151,k1_funct_1('#skF_4','#skF_6'))
      | ~ m1_subset_1(C_151,k1_zfmisc_1(k2_zfmisc_1('#skF_1',B_150)))
      | ~ v1_funct_2(C_151,'#skF_1',B_150)
      | ~ v1_funct_1(C_151) ) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_241])).

tff(c_267,plain,
    ( k3_funct_2('#skF_1','#skF_3','#skF_5',k1_funct_1('#skF_4','#skF_6')) = k1_funct_1('#skF_5',k1_funct_1('#skF_4','#skF_6'))
    | ~ v1_funct_2('#skF_5','#skF_1','#skF_3')
    | ~ v1_funct_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_50,c_264])).

tff(c_270,plain,(
    k3_funct_2('#skF_1','#skF_3','#skF_5',k1_funct_1('#skF_4','#skF_6')) = k1_funct_1('#skF_5',k1_funct_1('#skF_4','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_185,c_267])).

tff(c_285,plain,(
    ! [A_152,B_153,C_154,D_155] :
      ( k3_funct_2(A_152,B_153,C_154,D_155) = k7_partfun1(B_153,C_154,D_155)
      | ~ m1_subset_1(D_155,A_152)
      | ~ m1_subset_1(C_154,k1_zfmisc_1(k2_zfmisc_1(A_152,B_153)))
      | ~ v1_funct_2(C_154,A_152,B_153)
      | ~ v1_funct_1(C_154)
      | v1_xboole_0(B_153)
      | v1_xboole_0(A_152) ) ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_289,plain,(
    ! [B_153,C_154] :
      ( k3_funct_2('#skF_1',B_153,C_154,k1_funct_1('#skF_4','#skF_6')) = k7_partfun1(B_153,C_154,k1_funct_1('#skF_4','#skF_6'))
      | ~ m1_subset_1(C_154,k1_zfmisc_1(k2_zfmisc_1('#skF_1',B_153)))
      | ~ v1_funct_2(C_154,'#skF_1',B_153)
      | ~ v1_funct_1(C_154)
      | v1_xboole_0(B_153)
      | v1_xboole_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_238,c_285])).

tff(c_346,plain,(
    ! [B_165,C_166] :
      ( k3_funct_2('#skF_1',B_165,C_166,k1_funct_1('#skF_4','#skF_6')) = k7_partfun1(B_165,C_166,k1_funct_1('#skF_4','#skF_6'))
      | ~ m1_subset_1(C_166,k1_zfmisc_1(k2_zfmisc_1('#skF_1',B_165)))
      | ~ v1_funct_2(C_166,'#skF_1',B_165)
      | ~ v1_funct_1(C_166)
      | v1_xboole_0(B_165) ) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_289])).

tff(c_349,plain,
    ( k3_funct_2('#skF_1','#skF_3','#skF_5',k1_funct_1('#skF_4','#skF_6')) = k7_partfun1('#skF_3','#skF_5',k1_funct_1('#skF_4','#skF_6'))
    | ~ v1_funct_2('#skF_5','#skF_1','#skF_3')
    | ~ v1_funct_1('#skF_5')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_50,c_346])).

tff(c_352,plain,
    ( k7_partfun1('#skF_3','#skF_5',k1_funct_1('#skF_4','#skF_6')) = k1_funct_1('#skF_5',k1_funct_1('#skF_4','#skF_6'))
    | v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_185,c_270,c_349])).

tff(c_353,plain,(
    k7_partfun1('#skF_3','#skF_5',k1_funct_1('#skF_4','#skF_6')) = k1_funct_1('#skF_5',k1_funct_1('#skF_4','#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_172,c_352])).

tff(c_44,plain,(
    k3_funct_2('#skF_2','#skF_3',k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),'#skF_6') != k7_partfun1('#skF_3','#skF_5',k3_funct_2('#skF_2','#skF_1','#skF_4','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_196])).

tff(c_230,plain,(
    k3_funct_2('#skF_2','#skF_3',k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),'#skF_6') != k7_partfun1('#skF_3','#skF_5',k1_funct_1('#skF_4','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_229,c_44])).

tff(c_354,plain,(
    k3_funct_2('#skF_2','#skF_3',k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),'#skF_6') != k1_funct_1('#skF_5',k1_funct_1('#skF_4','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_353,c_230])).

tff(c_1055,plain,(
    k1_funct_1(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),'#skF_6') != k1_funct_1('#skF_5',k1_funct_1('#skF_4','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1022,c_354])).

tff(c_1308,plain,(
    ~ m1_subset_1('#skF_6','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_647,c_1055])).

tff(c_1312,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_1308])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:34:04 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.47/1.90  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.47/1.91  
% 4.47/1.91  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.47/1.91  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k8_funct_2 > k3_funct_2 > k7_partfun1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 4.47/1.91  
% 4.47/1.91  %Foreground sorts:
% 4.47/1.91  
% 4.47/1.91  
% 4.47/1.91  %Background operators:
% 4.47/1.91  
% 4.47/1.91  
% 4.47/1.91  %Foreground operators:
% 4.47/1.91  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 4.47/1.91  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.47/1.91  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.47/1.91  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.47/1.91  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.47/1.91  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 4.47/1.91  tff(k7_partfun1, type, k7_partfun1: ($i * $i * $i) > $i).
% 4.47/1.91  tff('#skF_5', type, '#skF_5': $i).
% 4.47/1.91  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.47/1.91  tff(k8_funct_2, type, k8_funct_2: ($i * $i * $i * $i * $i) > $i).
% 4.47/1.91  tff('#skF_6', type, '#skF_6': $i).
% 4.47/1.91  tff('#skF_2', type, '#skF_2': $i).
% 4.47/1.91  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 4.47/1.91  tff('#skF_3', type, '#skF_3': $i).
% 4.47/1.91  tff('#skF_1', type, '#skF_1': $i).
% 4.47/1.91  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 4.47/1.91  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 4.47/1.91  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.47/1.91  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 4.47/1.91  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.47/1.91  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.47/1.91  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.47/1.91  tff('#skF_4', type, '#skF_4': $i).
% 4.47/1.91  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.47/1.91  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 4.47/1.91  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.47/1.91  tff(k3_funct_2, type, k3_funct_2: ($i * $i * $i * $i) > $i).
% 4.47/1.91  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.47/1.91  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.47/1.91  
% 4.84/1.94  tff(f_196, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C, D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (![E]: ((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, C)))) => (![F]: (m1_subset_1(F, B) => (v1_partfun1(E, A) => (k3_funct_2(B, C, k8_funct_2(B, A, C, D, E), F) = k7_partfun1(C, E, k3_funct_2(B, A, D, F)))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t193_funct_2)).
% 4.84/1.94  tff(f_41, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 4.84/1.94  tff(f_33, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 4.84/1.94  tff(f_47, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 4.84/1.94  tff(f_39, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 4.84/1.94  tff(f_84, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (v1_partfun1(B, A) <=> (k1_relat_1(B) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_partfun1)).
% 4.84/1.94  tff(f_51, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 4.84/1.94  tff(f_55, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 4.84/1.94  tff(f_169, axiom, (![A, B, C]: (~v1_xboole_0(C) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, C)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (![E]: ((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(C, A)))) => (![F]: (m1_subset_1(F, B) => (r1_tarski(k2_relset_1(B, C, D), k1_relset_1(C, A, E)) => ((B = k1_xboole_0) | (k1_funct_1(k8_funct_2(B, C, A, D, E), F) = k1_funct_1(E, k1_funct_1(D, F))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t185_funct_2)).
% 4.84/1.94  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 4.84/1.94  tff(f_113, axiom, (![A, B, C, D, E]: (((((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(E)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => ((v1_funct_1(k8_funct_2(A, B, C, D, E)) & v1_funct_2(k8_funct_2(A, B, C, D, E), A, C)) & m1_subset_1(k8_funct_2(A, B, C, D, E), k1_zfmisc_1(k2_zfmisc_1(A, C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k8_funct_2)).
% 4.84/1.94  tff(f_126, axiom, (![A, B, C, D]: (((((~v1_xboole_0(A) & v1_funct_1(C)) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & m1_subset_1(D, A)) => (k3_funct_2(A, B, C, D) = k1_funct_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k3_funct_2)).
% 4.84/1.94  tff(f_76, axiom, (![A, B]: ((~v1_xboole_0(A) & v1_xboole_0(B)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ~v1_partfun1(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_partfun1)).
% 4.84/1.94  tff(f_65, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v1_partfun1(C, A)) => (v1_funct_1(C) & v1_funct_2(C, A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_funct_2)).
% 4.84/1.94  tff(f_97, axiom, (![A, B, C, D]: (((((~v1_xboole_0(A) & v1_funct_1(C)) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & m1_subset_1(D, A)) => m1_subset_1(k3_funct_2(A, B, C, D), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k3_funct_2)).
% 4.84/1.94  tff(f_145, axiom, (![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (m1_subset_1(D, A) => (k7_partfun1(B, C, D) = k3_funct_2(A, B, C, D)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t176_funct_2)).
% 4.84/1.94  tff(c_48, plain, (m1_subset_1('#skF_6', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_196])).
% 4.84/1.94  tff(c_10, plain, (![A_6, B_7]: (v1_relat_1(k2_zfmisc_1(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.84/1.94  tff(c_54, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_196])).
% 4.84/1.94  tff(c_64, plain, (![B_102, A_103]: (v1_relat_1(B_102) | ~m1_subset_1(B_102, k1_zfmisc_1(A_103)) | ~v1_relat_1(A_103))), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.84/1.94  tff(c_67, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_1'))), inference(resolution, [status(thm)], [c_54, c_64])).
% 4.84/1.94  tff(c_73, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_10, c_67])).
% 4.84/1.94  tff(c_92, plain, (![C_111, B_112, A_113]: (v5_relat_1(C_111, B_112) | ~m1_subset_1(C_111, k1_zfmisc_1(k2_zfmisc_1(A_113, B_112))))), inference(cnfTransformation, [status(thm)], [f_47])).
% 4.84/1.94  tff(c_99, plain, (v5_relat_1('#skF_4', '#skF_1')), inference(resolution, [status(thm)], [c_54, c_92])).
% 4.84/1.94  tff(c_8, plain, (![B_5, A_4]: (r1_tarski(k2_relat_1(B_5), A_4) | ~v5_relat_1(B_5, A_4) | ~v1_relat_1(B_5))), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.84/1.94  tff(c_52, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_196])).
% 4.84/1.94  tff(c_50, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_196])).
% 4.84/1.94  tff(c_70, plain, (v1_relat_1('#skF_5') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_3'))), inference(resolution, [status(thm)], [c_50, c_64])).
% 4.84/1.94  tff(c_76, plain, (v1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_10, c_70])).
% 4.84/1.94  tff(c_46, plain, (v1_partfun1('#skF_5', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_196])).
% 4.84/1.94  tff(c_78, plain, (![C_106, A_107, B_108]: (v4_relat_1(C_106, A_107) | ~m1_subset_1(C_106, k1_zfmisc_1(k2_zfmisc_1(A_107, B_108))))), inference(cnfTransformation, [status(thm)], [f_47])).
% 4.84/1.94  tff(c_86, plain, (v4_relat_1('#skF_5', '#skF_1')), inference(resolution, [status(thm)], [c_50, c_78])).
% 4.84/1.94  tff(c_102, plain, (![B_115, A_116]: (k1_relat_1(B_115)=A_116 | ~v1_partfun1(B_115, A_116) | ~v4_relat_1(B_115, A_116) | ~v1_relat_1(B_115))), inference(cnfTransformation, [status(thm)], [f_84])).
% 4.84/1.94  tff(c_105, plain, (k1_relat_1('#skF_5')='#skF_1' | ~v1_partfun1('#skF_5', '#skF_1') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_86, c_102])).
% 4.84/1.94  tff(c_111, plain, (k1_relat_1('#skF_5')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_76, c_46, c_105])).
% 4.84/1.94  tff(c_142, plain, (![A_120, B_121, C_122]: (k1_relset_1(A_120, B_121, C_122)=k1_relat_1(C_122) | ~m1_subset_1(C_122, k1_zfmisc_1(k2_zfmisc_1(A_120, B_121))))), inference(cnfTransformation, [status(thm)], [f_51])).
% 4.84/1.94  tff(c_148, plain, (k1_relset_1('#skF_1', '#skF_3', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_50, c_142])).
% 4.84/1.94  tff(c_151, plain, (k1_relset_1('#skF_1', '#skF_3', '#skF_5')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_111, c_148])).
% 4.84/1.94  tff(c_60, plain, (~v1_xboole_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_196])).
% 4.84/1.94  tff(c_62, plain, (~v1_xboole_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_196])).
% 4.84/1.94  tff(c_58, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_196])).
% 4.84/1.94  tff(c_56, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_196])).
% 4.84/1.94  tff(c_115, plain, (![A_117, B_118, C_119]: (k2_relset_1(A_117, B_118, C_119)=k2_relat_1(C_119) | ~m1_subset_1(C_119, k1_zfmisc_1(k2_zfmisc_1(A_117, B_118))))), inference(cnfTransformation, [status(thm)], [f_55])).
% 4.84/1.94  tff(c_122, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_54, c_115])).
% 4.84/1.94  tff(c_450, plain, (![C_176, D_179, E_181, B_178, A_177, F_180]: (k1_funct_1(k8_funct_2(B_178, C_176, A_177, D_179, E_181), F_180)=k1_funct_1(E_181, k1_funct_1(D_179, F_180)) | k1_xboole_0=B_178 | ~r1_tarski(k2_relset_1(B_178, C_176, D_179), k1_relset_1(C_176, A_177, E_181)) | ~m1_subset_1(F_180, B_178) | ~m1_subset_1(E_181, k1_zfmisc_1(k2_zfmisc_1(C_176, A_177))) | ~v1_funct_1(E_181) | ~m1_subset_1(D_179, k1_zfmisc_1(k2_zfmisc_1(B_178, C_176))) | ~v1_funct_2(D_179, B_178, C_176) | ~v1_funct_1(D_179) | v1_xboole_0(C_176))), inference(cnfTransformation, [status(thm)], [f_169])).
% 4.84/1.94  tff(c_458, plain, (![A_177, E_181, F_180]: (k1_funct_1(k8_funct_2('#skF_2', '#skF_1', A_177, '#skF_4', E_181), F_180)=k1_funct_1(E_181, k1_funct_1('#skF_4', F_180)) | k1_xboole_0='#skF_2' | ~r1_tarski(k2_relat_1('#skF_4'), k1_relset_1('#skF_1', A_177, E_181)) | ~m1_subset_1(F_180, '#skF_2') | ~m1_subset_1(E_181, k1_zfmisc_1(k2_zfmisc_1('#skF_1', A_177))) | ~v1_funct_1(E_181) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4') | v1_xboole_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_122, c_450])).
% 4.84/1.94  tff(c_469, plain, (![A_177, E_181, F_180]: (k1_funct_1(k8_funct_2('#skF_2', '#skF_1', A_177, '#skF_4', E_181), F_180)=k1_funct_1(E_181, k1_funct_1('#skF_4', F_180)) | k1_xboole_0='#skF_2' | ~r1_tarski(k2_relat_1('#skF_4'), k1_relset_1('#skF_1', A_177, E_181)) | ~m1_subset_1(F_180, '#skF_2') | ~m1_subset_1(E_181, k1_zfmisc_1(k2_zfmisc_1('#skF_1', A_177))) | ~v1_funct_1(E_181) | v1_xboole_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_54, c_458])).
% 4.84/1.94  tff(c_470, plain, (![A_177, E_181, F_180]: (k1_funct_1(k8_funct_2('#skF_2', '#skF_1', A_177, '#skF_4', E_181), F_180)=k1_funct_1(E_181, k1_funct_1('#skF_4', F_180)) | k1_xboole_0='#skF_2' | ~r1_tarski(k2_relat_1('#skF_4'), k1_relset_1('#skF_1', A_177, E_181)) | ~m1_subset_1(F_180, '#skF_2') | ~m1_subset_1(E_181, k1_zfmisc_1(k2_zfmisc_1('#skF_1', A_177))) | ~v1_funct_1(E_181))), inference(negUnitSimplification, [status(thm)], [c_62, c_469])).
% 4.84/1.94  tff(c_597, plain, (k1_xboole_0='#skF_2'), inference(splitLeft, [status(thm)], [c_470])).
% 4.84/1.94  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 4.84/1.94  tff(c_599, plain, (v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_597, c_2])).
% 4.84/1.94  tff(c_601, plain, $false, inference(negUnitSimplification, [status(thm)], [c_60, c_599])).
% 4.84/1.94  tff(c_627, plain, (![A_222, E_223, F_224]: (k1_funct_1(k8_funct_2('#skF_2', '#skF_1', A_222, '#skF_4', E_223), F_224)=k1_funct_1(E_223, k1_funct_1('#skF_4', F_224)) | ~r1_tarski(k2_relat_1('#skF_4'), k1_relset_1('#skF_1', A_222, E_223)) | ~m1_subset_1(F_224, '#skF_2') | ~m1_subset_1(E_223, k1_zfmisc_1(k2_zfmisc_1('#skF_1', A_222))) | ~v1_funct_1(E_223))), inference(splitRight, [status(thm)], [c_470])).
% 4.84/1.94  tff(c_629, plain, (![F_224]: (k1_funct_1(k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), F_224)=k1_funct_1('#skF_5', k1_funct_1('#skF_4', F_224)) | ~r1_tarski(k2_relat_1('#skF_4'), '#skF_1') | ~m1_subset_1(F_224, '#skF_2') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3'))) | ~v1_funct_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_151, c_627])).
% 4.84/1.94  tff(c_634, plain, (![F_224]: (k1_funct_1(k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), F_224)=k1_funct_1('#skF_5', k1_funct_1('#skF_4', F_224)) | ~r1_tarski(k2_relat_1('#skF_4'), '#skF_1') | ~m1_subset_1(F_224, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_629])).
% 4.84/1.94  tff(c_639, plain, (~r1_tarski(k2_relat_1('#skF_4'), '#skF_1')), inference(splitLeft, [status(thm)], [c_634])).
% 4.84/1.94  tff(c_642, plain, (~v5_relat_1('#skF_4', '#skF_1') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_8, c_639])).
% 4.84/1.94  tff(c_646, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_73, c_99, c_642])).
% 4.84/1.94  tff(c_647, plain, (![F_224]: (k1_funct_1(k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), F_224)=k1_funct_1('#skF_5', k1_funct_1('#skF_4', F_224)) | ~m1_subset_1(F_224, '#skF_2'))), inference(splitRight, [status(thm)], [c_634])).
% 4.84/1.94  tff(c_245, plain, (![A_143, E_144, C_141, D_145, B_142]: (v1_funct_1(k8_funct_2(A_143, B_142, C_141, D_145, E_144)) | ~m1_subset_1(E_144, k1_zfmisc_1(k2_zfmisc_1(B_142, C_141))) | ~v1_funct_1(E_144) | ~m1_subset_1(D_145, k1_zfmisc_1(k2_zfmisc_1(A_143, B_142))) | ~v1_funct_2(D_145, A_143, B_142) | ~v1_funct_1(D_145))), inference(cnfTransformation, [status(thm)], [f_113])).
% 4.84/1.94  tff(c_249, plain, (![A_143, D_145]: (v1_funct_1(k8_funct_2(A_143, '#skF_1', '#skF_3', D_145, '#skF_5')) | ~v1_funct_1('#skF_5') | ~m1_subset_1(D_145, k1_zfmisc_1(k2_zfmisc_1(A_143, '#skF_1'))) | ~v1_funct_2(D_145, A_143, '#skF_1') | ~v1_funct_1(D_145))), inference(resolution, [status(thm)], [c_50, c_245])).
% 4.84/1.94  tff(c_257, plain, (![A_148, D_149]: (v1_funct_1(k8_funct_2(A_148, '#skF_1', '#skF_3', D_149, '#skF_5')) | ~m1_subset_1(D_149, k1_zfmisc_1(k2_zfmisc_1(A_148, '#skF_1'))) | ~v1_funct_2(D_149, A_148, '#skF_1') | ~v1_funct_1(D_149))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_249])).
% 4.84/1.94  tff(c_260, plain, (v1_funct_1(k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5')) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_54, c_257])).
% 4.84/1.94  tff(c_263, plain, (v1_funct_1(k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_260])).
% 4.84/1.94  tff(c_325, plain, (![C_158, D_162, B_159, A_160, E_161]: (v1_funct_2(k8_funct_2(A_160, B_159, C_158, D_162, E_161), A_160, C_158) | ~m1_subset_1(E_161, k1_zfmisc_1(k2_zfmisc_1(B_159, C_158))) | ~v1_funct_1(E_161) | ~m1_subset_1(D_162, k1_zfmisc_1(k2_zfmisc_1(A_160, B_159))) | ~v1_funct_2(D_162, A_160, B_159) | ~v1_funct_1(D_162))), inference(cnfTransformation, [status(thm)], [f_113])).
% 4.84/1.94  tff(c_329, plain, (![A_160, D_162]: (v1_funct_2(k8_funct_2(A_160, '#skF_1', '#skF_3', D_162, '#skF_5'), A_160, '#skF_3') | ~v1_funct_1('#skF_5') | ~m1_subset_1(D_162, k1_zfmisc_1(k2_zfmisc_1(A_160, '#skF_1'))) | ~v1_funct_2(D_162, A_160, '#skF_1') | ~v1_funct_1(D_162))), inference(resolution, [status(thm)], [c_50, c_325])).
% 4.84/1.94  tff(c_340, plain, (![A_163, D_164]: (v1_funct_2(k8_funct_2(A_163, '#skF_1', '#skF_3', D_164, '#skF_5'), A_163, '#skF_3') | ~m1_subset_1(D_164, k1_zfmisc_1(k2_zfmisc_1(A_163, '#skF_1'))) | ~v1_funct_2(D_164, A_163, '#skF_1') | ~v1_funct_1(D_164))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_329])).
% 4.84/1.94  tff(c_342, plain, (v1_funct_2(k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), '#skF_2', '#skF_3') | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_54, c_340])).
% 4.84/1.94  tff(c_345, plain, (v1_funct_2(k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), '#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_342])).
% 4.84/1.94  tff(c_32, plain, (![D_33, A_30, C_32, B_31, E_34]: (m1_subset_1(k8_funct_2(A_30, B_31, C_32, D_33, E_34), k1_zfmisc_1(k2_zfmisc_1(A_30, C_32))) | ~m1_subset_1(E_34, k1_zfmisc_1(k2_zfmisc_1(B_31, C_32))) | ~v1_funct_1(E_34) | ~m1_subset_1(D_33, k1_zfmisc_1(k2_zfmisc_1(A_30, B_31))) | ~v1_funct_2(D_33, A_30, B_31) | ~v1_funct_1(D_33))), inference(cnfTransformation, [status(thm)], [f_113])).
% 4.84/1.94  tff(c_361, plain, (![C_171, B_172, E_174, D_175, A_173]: (m1_subset_1(k8_funct_2(A_173, B_172, C_171, D_175, E_174), k1_zfmisc_1(k2_zfmisc_1(A_173, C_171))) | ~m1_subset_1(E_174, k1_zfmisc_1(k2_zfmisc_1(B_172, C_171))) | ~v1_funct_1(E_174) | ~m1_subset_1(D_175, k1_zfmisc_1(k2_zfmisc_1(A_173, B_172))) | ~v1_funct_2(D_175, A_173, B_172) | ~v1_funct_1(D_175))), inference(cnfTransformation, [status(thm)], [f_113])).
% 4.84/1.94  tff(c_16, plain, (![A_11, B_12, C_13]: (k1_relset_1(A_11, B_12, C_13)=k1_relat_1(C_13) | ~m1_subset_1(C_13, k1_zfmisc_1(k2_zfmisc_1(A_11, B_12))))), inference(cnfTransformation, [status(thm)], [f_51])).
% 4.84/1.94  tff(c_798, plain, (![D_257, A_255, C_256, B_258, E_254]: (k1_relset_1(A_255, C_256, k8_funct_2(A_255, B_258, C_256, D_257, E_254))=k1_relat_1(k8_funct_2(A_255, B_258, C_256, D_257, E_254)) | ~m1_subset_1(E_254, k1_zfmisc_1(k2_zfmisc_1(B_258, C_256))) | ~v1_funct_1(E_254) | ~m1_subset_1(D_257, k1_zfmisc_1(k2_zfmisc_1(A_255, B_258))) | ~v1_funct_2(D_257, A_255, B_258) | ~v1_funct_1(D_257))), inference(resolution, [status(thm)], [c_361, c_16])).
% 4.84/1.94  tff(c_804, plain, (![A_255, D_257]: (k1_relset_1(A_255, '#skF_3', k8_funct_2(A_255, '#skF_1', '#skF_3', D_257, '#skF_5'))=k1_relat_1(k8_funct_2(A_255, '#skF_1', '#skF_3', D_257, '#skF_5')) | ~v1_funct_1('#skF_5') | ~m1_subset_1(D_257, k1_zfmisc_1(k2_zfmisc_1(A_255, '#skF_1'))) | ~v1_funct_2(D_257, A_255, '#skF_1') | ~v1_funct_1(D_257))), inference(resolution, [status(thm)], [c_50, c_798])).
% 4.84/1.94  tff(c_817, plain, (![A_261, D_262]: (k1_relset_1(A_261, '#skF_3', k8_funct_2(A_261, '#skF_1', '#skF_3', D_262, '#skF_5'))=k1_relat_1(k8_funct_2(A_261, '#skF_1', '#skF_3', D_262, '#skF_5')) | ~m1_subset_1(D_262, k1_zfmisc_1(k2_zfmisc_1(A_261, '#skF_1'))) | ~v1_funct_2(D_262, A_261, '#skF_1') | ~v1_funct_1(D_262))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_804])).
% 4.84/1.94  tff(c_822, plain, (k1_relset_1('#skF_2', '#skF_3', k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'))=k1_relat_1(k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5')) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_54, c_817])).
% 4.84/1.94  tff(c_826, plain, (k1_relset_1('#skF_2', '#skF_3', k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'))=k1_relat_1(k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_822])).
% 4.84/1.94  tff(c_42, plain, (![F_70, C_56, D_64, E_68, B_55, A_54]: (k1_funct_1(k8_funct_2(B_55, C_56, A_54, D_64, E_68), F_70)=k1_funct_1(E_68, k1_funct_1(D_64, F_70)) | k1_xboole_0=B_55 | ~r1_tarski(k2_relset_1(B_55, C_56, D_64), k1_relset_1(C_56, A_54, E_68)) | ~m1_subset_1(F_70, B_55) | ~m1_subset_1(E_68, k1_zfmisc_1(k2_zfmisc_1(C_56, A_54))) | ~v1_funct_1(E_68) | ~m1_subset_1(D_64, k1_zfmisc_1(k2_zfmisc_1(B_55, C_56))) | ~v1_funct_2(D_64, B_55, C_56) | ~v1_funct_1(D_64) | v1_xboole_0(C_56))), inference(cnfTransformation, [status(thm)], [f_169])).
% 4.84/1.94  tff(c_843, plain, (![B_55, D_64, F_70]: (k1_funct_1(k8_funct_2(B_55, '#skF_2', '#skF_3', D_64, k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5')), F_70)=k1_funct_1(k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), k1_funct_1(D_64, F_70)) | k1_xboole_0=B_55 | ~r1_tarski(k2_relset_1(B_55, '#skF_2', D_64), k1_relat_1(k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'))) | ~m1_subset_1(F_70, B_55) | ~m1_subset_1(k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~v1_funct_1(k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5')) | ~m1_subset_1(D_64, k1_zfmisc_1(k2_zfmisc_1(B_55, '#skF_2'))) | ~v1_funct_2(D_64, B_55, '#skF_2') | ~v1_funct_1(D_64) | v1_xboole_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_826, c_42])).
% 4.84/1.94  tff(c_847, plain, (![B_55, D_64, F_70]: (k1_funct_1(k8_funct_2(B_55, '#skF_2', '#skF_3', D_64, k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5')), F_70)=k1_funct_1(k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), k1_funct_1(D_64, F_70)) | k1_xboole_0=B_55 | ~r1_tarski(k2_relset_1(B_55, '#skF_2', D_64), k1_relat_1(k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'))) | ~m1_subset_1(F_70, B_55) | ~m1_subset_1(k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~m1_subset_1(D_64, k1_zfmisc_1(k2_zfmisc_1(B_55, '#skF_2'))) | ~v1_funct_2(D_64, B_55, '#skF_2') | ~v1_funct_1(D_64) | v1_xboole_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_263, c_843])).
% 4.84/1.94  tff(c_848, plain, (![B_55, D_64, F_70]: (k1_funct_1(k8_funct_2(B_55, '#skF_2', '#skF_3', D_64, k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5')), F_70)=k1_funct_1(k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), k1_funct_1(D_64, F_70)) | k1_xboole_0=B_55 | ~r1_tarski(k2_relset_1(B_55, '#skF_2', D_64), k1_relat_1(k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'))) | ~m1_subset_1(F_70, B_55) | ~m1_subset_1(k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~m1_subset_1(D_64, k1_zfmisc_1(k2_zfmisc_1(B_55, '#skF_2'))) | ~v1_funct_2(D_64, B_55, '#skF_2') | ~v1_funct_1(D_64))), inference(negUnitSimplification, [status(thm)], [c_60, c_847])).
% 4.84/1.94  tff(c_927, plain, (~m1_subset_1(k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(splitLeft, [status(thm)], [c_848])).
% 4.84/1.94  tff(c_930, plain, (~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3'))) | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_32, c_927])).
% 4.84/1.94  tff(c_934, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_54, c_52, c_50, c_930])).
% 4.84/1.94  tff(c_936, plain, (m1_subset_1(k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(splitRight, [status(thm)], [c_848])).
% 4.84/1.94  tff(c_201, plain, (![A_135, B_136, C_137, D_138]: (k3_funct_2(A_135, B_136, C_137, D_138)=k1_funct_1(C_137, D_138) | ~m1_subset_1(D_138, A_135) | ~m1_subset_1(C_137, k1_zfmisc_1(k2_zfmisc_1(A_135, B_136))) | ~v1_funct_2(C_137, A_135, B_136) | ~v1_funct_1(C_137) | v1_xboole_0(A_135))), inference(cnfTransformation, [status(thm)], [f_126])).
% 4.84/1.94  tff(c_211, plain, (![B_136, C_137]: (k3_funct_2('#skF_2', B_136, C_137, '#skF_6')=k1_funct_1(C_137, '#skF_6') | ~m1_subset_1(C_137, k1_zfmisc_1(k2_zfmisc_1('#skF_2', B_136))) | ~v1_funct_2(C_137, '#skF_2', B_136) | ~v1_funct_1(C_137) | v1_xboole_0('#skF_2'))), inference(resolution, [status(thm)], [c_48, c_201])).
% 4.84/1.94  tff(c_222, plain, (![B_136, C_137]: (k3_funct_2('#skF_2', B_136, C_137, '#skF_6')=k1_funct_1(C_137, '#skF_6') | ~m1_subset_1(C_137, k1_zfmisc_1(k2_zfmisc_1('#skF_2', B_136))) | ~v1_funct_2(C_137, '#skF_2', B_136) | ~v1_funct_1(C_137))), inference(negUnitSimplification, [status(thm)], [c_60, c_211])).
% 4.84/1.94  tff(c_962, plain, (k3_funct_2('#skF_2', '#skF_3', k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), '#skF_6')=k1_funct_1(k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), '#skF_6') | ~v1_funct_2(k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), '#skF_2', '#skF_3') | ~v1_funct_1(k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_936, c_222])).
% 4.84/1.94  tff(c_1022, plain, (k3_funct_2('#skF_2', '#skF_3', k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), '#skF_6')=k1_funct_1(k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_263, c_345, c_962])).
% 4.84/1.94  tff(c_160, plain, (![C_123, A_124, B_125]: (~v1_partfun1(C_123, A_124) | ~m1_subset_1(C_123, k1_zfmisc_1(k2_zfmisc_1(A_124, B_125))) | ~v1_xboole_0(B_125) | v1_xboole_0(A_124))), inference(cnfTransformation, [status(thm)], [f_76])).
% 4.84/1.94  tff(c_166, plain, (~v1_partfun1('#skF_5', '#skF_1') | ~v1_xboole_0('#skF_3') | v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_50, c_160])).
% 4.84/1.94  tff(c_171, plain, (~v1_xboole_0('#skF_3') | v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_166])).
% 4.84/1.94  tff(c_172, plain, (~v1_xboole_0('#skF_3')), inference(negUnitSimplification, [status(thm)], [c_62, c_171])).
% 4.84/1.94  tff(c_173, plain, (![C_126, A_127, B_128]: (v1_funct_2(C_126, A_127, B_128) | ~v1_partfun1(C_126, A_127) | ~v1_funct_1(C_126) | ~m1_subset_1(C_126, k1_zfmisc_1(k2_zfmisc_1(A_127, B_128))))), inference(cnfTransformation, [status(thm)], [f_65])).
% 4.84/1.94  tff(c_179, plain, (v1_funct_2('#skF_5', '#skF_1', '#skF_3') | ~v1_partfun1('#skF_5', '#skF_1') | ~v1_funct_1('#skF_5')), inference(resolution, [status(thm)], [c_50, c_173])).
% 4.84/1.94  tff(c_185, plain, (v1_funct_2('#skF_5', '#skF_1', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_46, c_179])).
% 4.84/1.94  tff(c_223, plain, (![B_139, C_140]: (k3_funct_2('#skF_2', B_139, C_140, '#skF_6')=k1_funct_1(C_140, '#skF_6') | ~m1_subset_1(C_140, k1_zfmisc_1(k2_zfmisc_1('#skF_2', B_139))) | ~v1_funct_2(C_140, '#skF_2', B_139) | ~v1_funct_1(C_140))), inference(negUnitSimplification, [status(thm)], [c_60, c_211])).
% 4.84/1.94  tff(c_226, plain, (k3_funct_2('#skF_2', '#skF_1', '#skF_4', '#skF_6')=k1_funct_1('#skF_4', '#skF_6') | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_54, c_223])).
% 4.84/1.94  tff(c_229, plain, (k3_funct_2('#skF_2', '#skF_1', '#skF_4', '#skF_6')=k1_funct_1('#skF_4', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_226])).
% 4.84/1.94  tff(c_186, plain, (![A_129, B_130, C_131, D_132]: (m1_subset_1(k3_funct_2(A_129, B_130, C_131, D_132), B_130) | ~m1_subset_1(D_132, A_129) | ~m1_subset_1(C_131, k1_zfmisc_1(k2_zfmisc_1(A_129, B_130))) | ~v1_funct_2(C_131, A_129, B_130) | ~v1_funct_1(C_131) | v1_xboole_0(A_129))), inference(cnfTransformation, [status(thm)], [f_97])).
% 4.84/1.94  tff(c_188, plain, (![D_132]: (m1_subset_1(k3_funct_2('#skF_2', '#skF_1', '#skF_4', D_132), '#skF_1') | ~m1_subset_1(D_132, '#skF_2') | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4') | v1_xboole_0('#skF_2'))), inference(resolution, [status(thm)], [c_54, c_186])).
% 4.84/1.94  tff(c_193, plain, (![D_132]: (m1_subset_1(k3_funct_2('#skF_2', '#skF_1', '#skF_4', D_132), '#skF_1') | ~m1_subset_1(D_132, '#skF_2') | v1_xboole_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_188])).
% 4.84/1.94  tff(c_194, plain, (![D_132]: (m1_subset_1(k3_funct_2('#skF_2', '#skF_1', '#skF_4', D_132), '#skF_1') | ~m1_subset_1(D_132, '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_60, c_193])).
% 4.84/1.94  tff(c_234, plain, (m1_subset_1(k1_funct_1('#skF_4', '#skF_6'), '#skF_1') | ~m1_subset_1('#skF_6', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_229, c_194])).
% 4.84/1.94  tff(c_238, plain, (m1_subset_1(k1_funct_1('#skF_4', '#skF_6'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_234])).
% 4.84/1.94  tff(c_38, plain, (![A_35, B_36, C_37, D_38]: (k3_funct_2(A_35, B_36, C_37, D_38)=k1_funct_1(C_37, D_38) | ~m1_subset_1(D_38, A_35) | ~m1_subset_1(C_37, k1_zfmisc_1(k2_zfmisc_1(A_35, B_36))) | ~v1_funct_2(C_37, A_35, B_36) | ~v1_funct_1(C_37) | v1_xboole_0(A_35))), inference(cnfTransformation, [status(thm)], [f_126])).
% 4.84/1.94  tff(c_241, plain, (![B_36, C_37]: (k3_funct_2('#skF_1', B_36, C_37, k1_funct_1('#skF_4', '#skF_6'))=k1_funct_1(C_37, k1_funct_1('#skF_4', '#skF_6')) | ~m1_subset_1(C_37, k1_zfmisc_1(k2_zfmisc_1('#skF_1', B_36))) | ~v1_funct_2(C_37, '#skF_1', B_36) | ~v1_funct_1(C_37) | v1_xboole_0('#skF_1'))), inference(resolution, [status(thm)], [c_238, c_38])).
% 4.84/1.94  tff(c_264, plain, (![B_150, C_151]: (k3_funct_2('#skF_1', B_150, C_151, k1_funct_1('#skF_4', '#skF_6'))=k1_funct_1(C_151, k1_funct_1('#skF_4', '#skF_6')) | ~m1_subset_1(C_151, k1_zfmisc_1(k2_zfmisc_1('#skF_1', B_150))) | ~v1_funct_2(C_151, '#skF_1', B_150) | ~v1_funct_1(C_151))), inference(negUnitSimplification, [status(thm)], [c_62, c_241])).
% 4.84/1.94  tff(c_267, plain, (k3_funct_2('#skF_1', '#skF_3', '#skF_5', k1_funct_1('#skF_4', '#skF_6'))=k1_funct_1('#skF_5', k1_funct_1('#skF_4', '#skF_6')) | ~v1_funct_2('#skF_5', '#skF_1', '#skF_3') | ~v1_funct_1('#skF_5')), inference(resolution, [status(thm)], [c_50, c_264])).
% 4.84/1.94  tff(c_270, plain, (k3_funct_2('#skF_1', '#skF_3', '#skF_5', k1_funct_1('#skF_4', '#skF_6'))=k1_funct_1('#skF_5', k1_funct_1('#skF_4', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_185, c_267])).
% 4.84/1.94  tff(c_285, plain, (![A_152, B_153, C_154, D_155]: (k3_funct_2(A_152, B_153, C_154, D_155)=k7_partfun1(B_153, C_154, D_155) | ~m1_subset_1(D_155, A_152) | ~m1_subset_1(C_154, k1_zfmisc_1(k2_zfmisc_1(A_152, B_153))) | ~v1_funct_2(C_154, A_152, B_153) | ~v1_funct_1(C_154) | v1_xboole_0(B_153) | v1_xboole_0(A_152))), inference(cnfTransformation, [status(thm)], [f_145])).
% 4.84/1.94  tff(c_289, plain, (![B_153, C_154]: (k3_funct_2('#skF_1', B_153, C_154, k1_funct_1('#skF_4', '#skF_6'))=k7_partfun1(B_153, C_154, k1_funct_1('#skF_4', '#skF_6')) | ~m1_subset_1(C_154, k1_zfmisc_1(k2_zfmisc_1('#skF_1', B_153))) | ~v1_funct_2(C_154, '#skF_1', B_153) | ~v1_funct_1(C_154) | v1_xboole_0(B_153) | v1_xboole_0('#skF_1'))), inference(resolution, [status(thm)], [c_238, c_285])).
% 4.84/1.94  tff(c_346, plain, (![B_165, C_166]: (k3_funct_2('#skF_1', B_165, C_166, k1_funct_1('#skF_4', '#skF_6'))=k7_partfun1(B_165, C_166, k1_funct_1('#skF_4', '#skF_6')) | ~m1_subset_1(C_166, k1_zfmisc_1(k2_zfmisc_1('#skF_1', B_165))) | ~v1_funct_2(C_166, '#skF_1', B_165) | ~v1_funct_1(C_166) | v1_xboole_0(B_165))), inference(negUnitSimplification, [status(thm)], [c_62, c_289])).
% 4.84/1.94  tff(c_349, plain, (k3_funct_2('#skF_1', '#skF_3', '#skF_5', k1_funct_1('#skF_4', '#skF_6'))=k7_partfun1('#skF_3', '#skF_5', k1_funct_1('#skF_4', '#skF_6')) | ~v1_funct_2('#skF_5', '#skF_1', '#skF_3') | ~v1_funct_1('#skF_5') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_50, c_346])).
% 4.84/1.94  tff(c_352, plain, (k7_partfun1('#skF_3', '#skF_5', k1_funct_1('#skF_4', '#skF_6'))=k1_funct_1('#skF_5', k1_funct_1('#skF_4', '#skF_6')) | v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_185, c_270, c_349])).
% 4.84/1.94  tff(c_353, plain, (k7_partfun1('#skF_3', '#skF_5', k1_funct_1('#skF_4', '#skF_6'))=k1_funct_1('#skF_5', k1_funct_1('#skF_4', '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_172, c_352])).
% 4.84/1.94  tff(c_44, plain, (k3_funct_2('#skF_2', '#skF_3', k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), '#skF_6')!=k7_partfun1('#skF_3', '#skF_5', k3_funct_2('#skF_2', '#skF_1', '#skF_4', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_196])).
% 4.84/1.94  tff(c_230, plain, (k3_funct_2('#skF_2', '#skF_3', k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), '#skF_6')!=k7_partfun1('#skF_3', '#skF_5', k1_funct_1('#skF_4', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_229, c_44])).
% 4.84/1.94  tff(c_354, plain, (k3_funct_2('#skF_2', '#skF_3', k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), '#skF_6')!=k1_funct_1('#skF_5', k1_funct_1('#skF_4', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_353, c_230])).
% 4.84/1.94  tff(c_1055, plain, (k1_funct_1(k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), '#skF_6')!=k1_funct_1('#skF_5', k1_funct_1('#skF_4', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_1022, c_354])).
% 4.84/1.94  tff(c_1308, plain, (~m1_subset_1('#skF_6', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_647, c_1055])).
% 4.84/1.94  tff(c_1312, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_48, c_1308])).
% 4.84/1.94  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.84/1.94  
% 4.84/1.94  Inference rules
% 4.84/1.94  ----------------------
% 4.84/1.94  #Ref     : 0
% 4.84/1.94  #Sup     : 260
% 4.84/1.94  #Fact    : 0
% 4.84/1.94  #Define  : 0
% 4.84/1.94  #Split   : 8
% 4.84/1.94  #Chain   : 0
% 4.84/1.94  #Close   : 0
% 4.84/1.94  
% 4.84/1.94  Ordering : KBO
% 4.84/1.94  
% 4.84/1.94  Simplification rules
% 4.84/1.94  ----------------------
% 4.84/1.94  #Subsume      : 9
% 4.84/1.94  #Demod        : 173
% 4.84/1.94  #Tautology    : 50
% 4.84/1.94  #SimpNegUnit  : 38
% 4.84/1.94  #BackRed      : 8
% 4.84/1.94  
% 4.84/1.94  #Partial instantiations: 0
% 4.84/1.94  #Strategies tried      : 1
% 4.84/1.94  
% 4.84/1.94  Timing (in seconds)
% 4.84/1.94  ----------------------
% 4.84/1.95  Preprocessing        : 0.37
% 4.84/1.95  Parsing              : 0.20
% 4.84/1.95  CNF conversion       : 0.03
% 4.84/1.95  Main loop            : 0.71
% 4.84/1.95  Inferencing          : 0.26
% 4.84/1.95  Reduction            : 0.22
% 4.84/1.95  Demodulation         : 0.16
% 4.84/1.95  BG Simplification    : 0.04
% 4.84/1.95  Subsumption          : 0.13
% 4.84/1.95  Abstraction          : 0.05
% 4.84/1.95  MUC search           : 0.00
% 4.84/1.95  Cooper               : 0.00
% 4.84/1.95  Total                : 1.13
% 4.84/1.95  Index Insertion      : 0.00
% 4.84/1.95  Index Deletion       : 0.00
% 4.84/1.95  Index Matching       : 0.00
% 4.84/1.95  BG Taut test         : 0.00
%------------------------------------------------------------------------------
