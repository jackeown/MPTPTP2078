%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:18:12 EST 2020

% Result     : Theorem 4.46s
% Output     : CNFRefutation 4.73s
% Verified   : 
% Statistics : Number of formulae       :  148 ( 453 expanded)
%              Number of leaves         :   44 ( 180 expanded)
%              Depth                    :   17
%              Number of atoms          :  396 (2027 expanded)
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

tff(f_191,negated_conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t193_funct_2)).

tff(f_36,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_42,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_79,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => ( v1_partfun1(B,A)
      <=> k1_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_partfun1)).

tff(f_46,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_50,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_164,axiom,(
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

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_108,axiom,(
    ! [A,B,C,D,E] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(B,C))) )
     => ( v1_funct_1(k8_funct_2(A,B,C,D,E))
        & v1_funct_2(k8_funct_2(A,B,C,D,E),A,C)
        & m1_subset_1(k8_funct_2(A,B,C,D,E),k1_zfmisc_1(k2_zfmisc_1(A,C))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k8_funct_2)).

tff(f_121,axiom,(
    ! [A,B,C,D] :
      ( ( ~ v1_xboole_0(A)
        & v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,A) )
     => k3_funct_2(A,B,C,D) = k1_funct_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k3_funct_2)).

tff(f_71,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & v1_xboole_0(B) )
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => ~ v1_partfun1(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_partfun1)).

tff(f_60,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( ( v1_funct_1(C)
          & v1_partfun1(C,A) )
       => ( v1_funct_1(C)
          & v1_funct_2(C,A,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_funct_2)).

tff(f_92,axiom,(
    ! [A,B,C,D] :
      ( ( ~ v1_xboole_0(A)
        & v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,A) )
     => m1_subset_1(k3_funct_2(A,B,C,D),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_funct_2)).

tff(f_140,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t176_funct_2)).

tff(c_46,plain,(
    m1_subset_1('#skF_6','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_191])).

tff(c_52,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_191])).

tff(c_61,plain,(
    ! [C_98,A_99,B_100] :
      ( v1_relat_1(C_98)
      | ~ m1_subset_1(C_98,k1_zfmisc_1(k2_zfmisc_1(A_99,B_100))) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_68,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_52,c_61])).

tff(c_71,plain,(
    ! [C_103,B_104,A_105] :
      ( v5_relat_1(C_103,B_104)
      | ~ m1_subset_1(C_103,k1_zfmisc_1(k2_zfmisc_1(A_105,B_104))) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_78,plain,(
    v5_relat_1('#skF_4','#skF_1') ),
    inference(resolution,[status(thm)],[c_52,c_71])).

tff(c_6,plain,(
    ! [B_2,A_1] :
      ( r1_tarski(k2_relat_1(B_2),A_1)
      | ~ v5_relat_1(B_2,A_1)
      | ~ v1_relat_1(B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_50,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_191])).

tff(c_48,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_191])).

tff(c_69,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_48,c_61])).

tff(c_44,plain,(
    v1_partfun1('#skF_5','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_191])).

tff(c_85,plain,(
    ! [C_108,A_109,B_110] :
      ( v4_relat_1(C_108,A_109)
      | ~ m1_subset_1(C_108,k1_zfmisc_1(k2_zfmisc_1(A_109,B_110))) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_93,plain,(
    v4_relat_1('#skF_5','#skF_1') ),
    inference(resolution,[status(thm)],[c_48,c_85])).

tff(c_95,plain,(
    ! [B_112,A_113] :
      ( k1_relat_1(B_112) = A_113
      | ~ v1_partfun1(B_112,A_113)
      | ~ v4_relat_1(B_112,A_113)
      | ~ v1_relat_1(B_112) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_98,plain,
    ( k1_relat_1('#skF_5') = '#skF_1'
    | ~ v1_partfun1('#skF_5','#skF_1')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_93,c_95])).

tff(c_104,plain,(
    k1_relat_1('#skF_5') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_69,c_44,c_98])).

tff(c_117,plain,(
    ! [A_114,B_115,C_116] :
      ( k1_relset_1(A_114,B_115,C_116) = k1_relat_1(C_116)
      | ~ m1_subset_1(C_116,k1_zfmisc_1(k2_zfmisc_1(A_114,B_115))) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_123,plain,(
    k1_relset_1('#skF_1','#skF_3','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_48,c_117])).

tff(c_126,plain,(
    k1_relset_1('#skF_1','#skF_3','#skF_5') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_123])).

tff(c_58,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_191])).

tff(c_60,plain,(
    ~ v1_xboole_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_191])).

tff(c_56,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_191])).

tff(c_54,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_191])).

tff(c_136,plain,(
    ! [A_117,B_118,C_119] :
      ( k2_relset_1(A_117,B_118,C_119) = k2_relat_1(C_119)
      | ~ m1_subset_1(C_119,k1_zfmisc_1(k2_zfmisc_1(A_117,B_118))) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_143,plain,(
    k2_relset_1('#skF_2','#skF_1','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_52,c_136])).

tff(c_455,plain,(
    ! [B_180,D_181,E_178,C_183,A_179,F_182] :
      ( k1_funct_1(k8_funct_2(B_180,C_183,A_179,D_181,E_178),F_182) = k1_funct_1(E_178,k1_funct_1(D_181,F_182))
      | k1_xboole_0 = B_180
      | ~ r1_tarski(k2_relset_1(B_180,C_183,D_181),k1_relset_1(C_183,A_179,E_178))
      | ~ m1_subset_1(F_182,B_180)
      | ~ m1_subset_1(E_178,k1_zfmisc_1(k2_zfmisc_1(C_183,A_179)))
      | ~ v1_funct_1(E_178)
      | ~ m1_subset_1(D_181,k1_zfmisc_1(k2_zfmisc_1(B_180,C_183)))
      | ~ v1_funct_2(D_181,B_180,C_183)
      | ~ v1_funct_1(D_181)
      | v1_xboole_0(C_183) ) ),
    inference(cnfTransformation,[status(thm)],[f_164])).

tff(c_459,plain,(
    ! [A_179,E_178,F_182] :
      ( k1_funct_1(k8_funct_2('#skF_2','#skF_1',A_179,'#skF_4',E_178),F_182) = k1_funct_1(E_178,k1_funct_1('#skF_4',F_182))
      | k1_xboole_0 = '#skF_2'
      | ~ r1_tarski(k2_relat_1('#skF_4'),k1_relset_1('#skF_1',A_179,E_178))
      | ~ m1_subset_1(F_182,'#skF_2')
      | ~ m1_subset_1(E_178,k1_zfmisc_1(k2_zfmisc_1('#skF_1',A_179)))
      | ~ v1_funct_1(E_178)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
      | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
      | ~ v1_funct_1('#skF_4')
      | v1_xboole_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_143,c_455])).

tff(c_468,plain,(
    ! [A_179,E_178,F_182] :
      ( k1_funct_1(k8_funct_2('#skF_2','#skF_1',A_179,'#skF_4',E_178),F_182) = k1_funct_1(E_178,k1_funct_1('#skF_4',F_182))
      | k1_xboole_0 = '#skF_2'
      | ~ r1_tarski(k2_relat_1('#skF_4'),k1_relset_1('#skF_1',A_179,E_178))
      | ~ m1_subset_1(F_182,'#skF_2')
      | ~ m1_subset_1(E_178,k1_zfmisc_1(k2_zfmisc_1('#skF_1',A_179)))
      | ~ v1_funct_1(E_178)
      | v1_xboole_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_52,c_459])).

tff(c_469,plain,(
    ! [A_179,E_178,F_182] :
      ( k1_funct_1(k8_funct_2('#skF_2','#skF_1',A_179,'#skF_4',E_178),F_182) = k1_funct_1(E_178,k1_funct_1('#skF_4',F_182))
      | k1_xboole_0 = '#skF_2'
      | ~ r1_tarski(k2_relat_1('#skF_4'),k1_relset_1('#skF_1',A_179,E_178))
      | ~ m1_subset_1(F_182,'#skF_2')
      | ~ m1_subset_1(E_178,k1_zfmisc_1(k2_zfmisc_1('#skF_1',A_179)))
      | ~ v1_funct_1(E_178) ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_468])).

tff(c_587,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_469])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_589,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_587,c_2])).

tff(c_591,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_589])).

tff(c_618,plain,(
    ! [A_219,E_220,F_221] :
      ( k1_funct_1(k8_funct_2('#skF_2','#skF_1',A_219,'#skF_4',E_220),F_221) = k1_funct_1(E_220,k1_funct_1('#skF_4',F_221))
      | ~ r1_tarski(k2_relat_1('#skF_4'),k1_relset_1('#skF_1',A_219,E_220))
      | ~ m1_subset_1(F_221,'#skF_2')
      | ~ m1_subset_1(E_220,k1_zfmisc_1(k2_zfmisc_1('#skF_1',A_219)))
      | ~ v1_funct_1(E_220) ) ),
    inference(splitRight,[status(thm)],[c_469])).

tff(c_620,plain,(
    ! [F_221] :
      ( k1_funct_1(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),F_221) = k1_funct_1('#skF_5',k1_funct_1('#skF_4',F_221))
      | ~ r1_tarski(k2_relat_1('#skF_4'),'#skF_1')
      | ~ m1_subset_1(F_221,'#skF_2')
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3')))
      | ~ v1_funct_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_126,c_618])).

tff(c_625,plain,(
    ! [F_221] :
      ( k1_funct_1(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),F_221) = k1_funct_1('#skF_5',k1_funct_1('#skF_4',F_221))
      | ~ r1_tarski(k2_relat_1('#skF_4'),'#skF_1')
      | ~ m1_subset_1(F_221,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_620])).

tff(c_629,plain,(
    ~ r1_tarski(k2_relat_1('#skF_4'),'#skF_1') ),
    inference(splitLeft,[status(thm)],[c_625])).

tff(c_633,plain,
    ( ~ v5_relat_1('#skF_4','#skF_1')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_6,c_629])).

tff(c_637,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_78,c_633])).

tff(c_638,plain,(
    ! [F_221] :
      ( k1_funct_1(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),F_221) = k1_funct_1('#skF_5',k1_funct_1('#skF_4',F_221))
      | ~ m1_subset_1(F_221,'#skF_2') ) ),
    inference(splitRight,[status(thm)],[c_625])).

tff(c_238,plain,(
    ! [E_138,C_140,D_142,A_139,B_141] :
      ( v1_funct_1(k8_funct_2(A_139,B_141,C_140,D_142,E_138))
      | ~ m1_subset_1(E_138,k1_zfmisc_1(k2_zfmisc_1(B_141,C_140)))
      | ~ v1_funct_1(E_138)
      | ~ m1_subset_1(D_142,k1_zfmisc_1(k2_zfmisc_1(A_139,B_141)))
      | ~ v1_funct_2(D_142,A_139,B_141)
      | ~ v1_funct_1(D_142) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_242,plain,(
    ! [A_139,D_142] :
      ( v1_funct_1(k8_funct_2(A_139,'#skF_1','#skF_3',D_142,'#skF_5'))
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1(D_142,k1_zfmisc_1(k2_zfmisc_1(A_139,'#skF_1')))
      | ~ v1_funct_2(D_142,A_139,'#skF_1')
      | ~ v1_funct_1(D_142) ) ),
    inference(resolution,[status(thm)],[c_48,c_238])).

tff(c_250,plain,(
    ! [A_145,D_146] :
      ( v1_funct_1(k8_funct_2(A_145,'#skF_1','#skF_3',D_146,'#skF_5'))
      | ~ m1_subset_1(D_146,k1_zfmisc_1(k2_zfmisc_1(A_145,'#skF_1')))
      | ~ v1_funct_2(D_146,A_145,'#skF_1')
      | ~ v1_funct_1(D_146) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_242])).

tff(c_253,plain,
    ( v1_funct_1(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_52,c_250])).

tff(c_256,plain,(
    v1_funct_1(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_253])).

tff(c_322,plain,(
    ! [A_156,E_155,D_159,B_158,C_157] :
      ( v1_funct_2(k8_funct_2(A_156,B_158,C_157,D_159,E_155),A_156,C_157)
      | ~ m1_subset_1(E_155,k1_zfmisc_1(k2_zfmisc_1(B_158,C_157)))
      | ~ v1_funct_1(E_155)
      | ~ m1_subset_1(D_159,k1_zfmisc_1(k2_zfmisc_1(A_156,B_158)))
      | ~ v1_funct_2(D_159,A_156,B_158)
      | ~ v1_funct_1(D_159) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_326,plain,(
    ! [A_156,D_159] :
      ( v1_funct_2(k8_funct_2(A_156,'#skF_1','#skF_3',D_159,'#skF_5'),A_156,'#skF_3')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1(D_159,k1_zfmisc_1(k2_zfmisc_1(A_156,'#skF_1')))
      | ~ v1_funct_2(D_159,A_156,'#skF_1')
      | ~ v1_funct_1(D_159) ) ),
    inference(resolution,[status(thm)],[c_48,c_322])).

tff(c_334,plain,(
    ! [A_162,D_163] :
      ( v1_funct_2(k8_funct_2(A_162,'#skF_1','#skF_3',D_163,'#skF_5'),A_162,'#skF_3')
      | ~ m1_subset_1(D_163,k1_zfmisc_1(k2_zfmisc_1(A_162,'#skF_1')))
      | ~ v1_funct_2(D_163,A_162,'#skF_1')
      | ~ v1_funct_1(D_163) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_326])).

tff(c_336,plain,
    ( v1_funct_2(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),'#skF_2','#skF_3')
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_52,c_334])).

tff(c_339,plain,(
    v1_funct_2(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),'#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_336])).

tff(c_30,plain,(
    ! [C_30,E_32,D_31,B_29,A_28] :
      ( m1_subset_1(k8_funct_2(A_28,B_29,C_30,D_31,E_32),k1_zfmisc_1(k2_zfmisc_1(A_28,C_30)))
      | ~ m1_subset_1(E_32,k1_zfmisc_1(k2_zfmisc_1(B_29,C_30)))
      | ~ v1_funct_1(E_32)
      | ~ m1_subset_1(D_31,k1_zfmisc_1(k2_zfmisc_1(A_28,B_29)))
      | ~ v1_funct_2(D_31,A_28,B_29)
      | ~ v1_funct_1(D_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_354,plain,(
    ! [C_170,D_172,E_168,A_169,B_171] :
      ( m1_subset_1(k8_funct_2(A_169,B_171,C_170,D_172,E_168),k1_zfmisc_1(k2_zfmisc_1(A_169,C_170)))
      | ~ m1_subset_1(E_168,k1_zfmisc_1(k2_zfmisc_1(B_171,C_170)))
      | ~ v1_funct_1(E_168)
      | ~ m1_subset_1(D_172,k1_zfmisc_1(k2_zfmisc_1(A_169,B_171)))
      | ~ v1_funct_2(D_172,A_169,B_171)
      | ~ v1_funct_1(D_172) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_14,plain,(
    ! [A_9,B_10,C_11] :
      ( k1_relset_1(A_9,B_10,C_11) = k1_relat_1(C_11)
      | ~ m1_subset_1(C_11,k1_zfmisc_1(k2_zfmisc_1(A_9,B_10))) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_698,plain,(
    ! [E_239,D_238,A_237,B_241,C_240] :
      ( k1_relset_1(A_237,C_240,k8_funct_2(A_237,B_241,C_240,D_238,E_239)) = k1_relat_1(k8_funct_2(A_237,B_241,C_240,D_238,E_239))
      | ~ m1_subset_1(E_239,k1_zfmisc_1(k2_zfmisc_1(B_241,C_240)))
      | ~ v1_funct_1(E_239)
      | ~ m1_subset_1(D_238,k1_zfmisc_1(k2_zfmisc_1(A_237,B_241)))
      | ~ v1_funct_2(D_238,A_237,B_241)
      | ~ v1_funct_1(D_238) ) ),
    inference(resolution,[status(thm)],[c_354,c_14])).

tff(c_704,plain,(
    ! [A_237,D_238] :
      ( k1_relset_1(A_237,'#skF_3',k8_funct_2(A_237,'#skF_1','#skF_3',D_238,'#skF_5')) = k1_relat_1(k8_funct_2(A_237,'#skF_1','#skF_3',D_238,'#skF_5'))
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1(D_238,k1_zfmisc_1(k2_zfmisc_1(A_237,'#skF_1')))
      | ~ v1_funct_2(D_238,A_237,'#skF_1')
      | ~ v1_funct_1(D_238) ) ),
    inference(resolution,[status(thm)],[c_48,c_698])).

tff(c_717,plain,(
    ! [A_244,D_245] :
      ( k1_relset_1(A_244,'#skF_3',k8_funct_2(A_244,'#skF_1','#skF_3',D_245,'#skF_5')) = k1_relat_1(k8_funct_2(A_244,'#skF_1','#skF_3',D_245,'#skF_5'))
      | ~ m1_subset_1(D_245,k1_zfmisc_1(k2_zfmisc_1(A_244,'#skF_1')))
      | ~ v1_funct_2(D_245,A_244,'#skF_1')
      | ~ v1_funct_1(D_245) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_704])).

tff(c_722,plain,
    ( k1_relset_1('#skF_2','#skF_3',k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5')) = k1_relat_1(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_52,c_717])).

tff(c_726,plain,(
    k1_relset_1('#skF_2','#skF_3',k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5')) = k1_relat_1(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_722])).

tff(c_40,plain,(
    ! [F_68,E_66,D_62,B_53,A_52,C_54] :
      ( k1_funct_1(k8_funct_2(B_53,C_54,A_52,D_62,E_66),F_68) = k1_funct_1(E_66,k1_funct_1(D_62,F_68))
      | k1_xboole_0 = B_53
      | ~ r1_tarski(k2_relset_1(B_53,C_54,D_62),k1_relset_1(C_54,A_52,E_66))
      | ~ m1_subset_1(F_68,B_53)
      | ~ m1_subset_1(E_66,k1_zfmisc_1(k2_zfmisc_1(C_54,A_52)))
      | ~ v1_funct_1(E_66)
      | ~ m1_subset_1(D_62,k1_zfmisc_1(k2_zfmisc_1(B_53,C_54)))
      | ~ v1_funct_2(D_62,B_53,C_54)
      | ~ v1_funct_1(D_62)
      | v1_xboole_0(C_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_164])).

tff(c_729,plain,(
    ! [B_53,D_62,F_68] :
      ( k1_funct_1(k8_funct_2(B_53,'#skF_2','#skF_3',D_62,k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5')),F_68) = k1_funct_1(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),k1_funct_1(D_62,F_68))
      | k1_xboole_0 = B_53
      | ~ r1_tarski(k2_relset_1(B_53,'#skF_2',D_62),k1_relat_1(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5')))
      | ~ m1_subset_1(F_68,B_53)
      | ~ m1_subset_1(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
      | ~ v1_funct_1(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'))
      | ~ m1_subset_1(D_62,k1_zfmisc_1(k2_zfmisc_1(B_53,'#skF_2')))
      | ~ v1_funct_2(D_62,B_53,'#skF_2')
      | ~ v1_funct_1(D_62)
      | v1_xboole_0('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_726,c_40])).

tff(c_733,plain,(
    ! [B_53,D_62,F_68] :
      ( k1_funct_1(k8_funct_2(B_53,'#skF_2','#skF_3',D_62,k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5')),F_68) = k1_funct_1(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),k1_funct_1(D_62,F_68))
      | k1_xboole_0 = B_53
      | ~ r1_tarski(k2_relset_1(B_53,'#skF_2',D_62),k1_relat_1(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5')))
      | ~ m1_subset_1(F_68,B_53)
      | ~ m1_subset_1(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
      | ~ m1_subset_1(D_62,k1_zfmisc_1(k2_zfmisc_1(B_53,'#skF_2')))
      | ~ v1_funct_2(D_62,B_53,'#skF_2')
      | ~ v1_funct_1(D_62)
      | v1_xboole_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_256,c_729])).

tff(c_734,plain,(
    ! [B_53,D_62,F_68] :
      ( k1_funct_1(k8_funct_2(B_53,'#skF_2','#skF_3',D_62,k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5')),F_68) = k1_funct_1(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),k1_funct_1(D_62,F_68))
      | k1_xboole_0 = B_53
      | ~ r1_tarski(k2_relset_1(B_53,'#skF_2',D_62),k1_relat_1(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5')))
      | ~ m1_subset_1(F_68,B_53)
      | ~ m1_subset_1(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
      | ~ m1_subset_1(D_62,k1_zfmisc_1(k2_zfmisc_1(B_53,'#skF_2')))
      | ~ v1_funct_2(D_62,B_53,'#skF_2')
      | ~ v1_funct_1(D_62) ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_733])).

tff(c_910,plain,(
    ~ m1_subset_1(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_734])).

tff(c_913,plain,
    ( ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3')))
    | ~ v1_funct_1('#skF_5')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_30,c_910])).

tff(c_917,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_52,c_50,c_48,c_913])).

tff(c_919,plain,(
    m1_subset_1(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_734])).

tff(c_194,plain,(
    ! [A_132,B_133,C_134,D_135] :
      ( k3_funct_2(A_132,B_133,C_134,D_135) = k1_funct_1(C_134,D_135)
      | ~ m1_subset_1(D_135,A_132)
      | ~ m1_subset_1(C_134,k1_zfmisc_1(k2_zfmisc_1(A_132,B_133)))
      | ~ v1_funct_2(C_134,A_132,B_133)
      | ~ v1_funct_1(C_134)
      | v1_xboole_0(A_132) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_204,plain,(
    ! [B_133,C_134] :
      ( k3_funct_2('#skF_2',B_133,C_134,'#skF_6') = k1_funct_1(C_134,'#skF_6')
      | ~ m1_subset_1(C_134,k1_zfmisc_1(k2_zfmisc_1('#skF_2',B_133)))
      | ~ v1_funct_2(C_134,'#skF_2',B_133)
      | ~ v1_funct_1(C_134)
      | v1_xboole_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_46,c_194])).

tff(c_215,plain,(
    ! [B_133,C_134] :
      ( k3_funct_2('#skF_2',B_133,C_134,'#skF_6') = k1_funct_1(C_134,'#skF_6')
      | ~ m1_subset_1(C_134,k1_zfmisc_1(k2_zfmisc_1('#skF_2',B_133)))
      | ~ v1_funct_2(C_134,'#skF_2',B_133)
      | ~ v1_funct_1(C_134) ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_204])).

tff(c_945,plain,
    ( k3_funct_2('#skF_2','#skF_3',k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),'#skF_6') = k1_funct_1(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),'#skF_6')
    | ~ v1_funct_2(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),'#skF_2','#skF_3')
    | ~ v1_funct_1(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_919,c_215])).

tff(c_1005,plain,(
    k3_funct_2('#skF_2','#skF_3',k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),'#skF_6') = k1_funct_1(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_256,c_339,c_945])).

tff(c_153,plain,(
    ! [C_120,A_121,B_122] :
      ( ~ v1_partfun1(C_120,A_121)
      | ~ m1_subset_1(C_120,k1_zfmisc_1(k2_zfmisc_1(A_121,B_122)))
      | ~ v1_xboole_0(B_122)
      | v1_xboole_0(A_121) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_159,plain,
    ( ~ v1_partfun1('#skF_5','#skF_1')
    | ~ v1_xboole_0('#skF_3')
    | v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_48,c_153])).

tff(c_164,plain,
    ( ~ v1_xboole_0('#skF_3')
    | v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_159])).

tff(c_165,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_164])).

tff(c_166,plain,(
    ! [C_123,A_124,B_125] :
      ( v1_funct_2(C_123,A_124,B_125)
      | ~ v1_partfun1(C_123,A_124)
      | ~ v1_funct_1(C_123)
      | ~ m1_subset_1(C_123,k1_zfmisc_1(k2_zfmisc_1(A_124,B_125))) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_172,plain,
    ( v1_funct_2('#skF_5','#skF_1','#skF_3')
    | ~ v1_partfun1('#skF_5','#skF_1')
    | ~ v1_funct_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_48,c_166])).

tff(c_178,plain,(
    v1_funct_2('#skF_5','#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_44,c_172])).

tff(c_216,plain,(
    ! [B_136,C_137] :
      ( k3_funct_2('#skF_2',B_136,C_137,'#skF_6') = k1_funct_1(C_137,'#skF_6')
      | ~ m1_subset_1(C_137,k1_zfmisc_1(k2_zfmisc_1('#skF_2',B_136)))
      | ~ v1_funct_2(C_137,'#skF_2',B_136)
      | ~ v1_funct_1(C_137) ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_204])).

tff(c_219,plain,
    ( k3_funct_2('#skF_2','#skF_1','#skF_4','#skF_6') = k1_funct_1('#skF_4','#skF_6')
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_52,c_216])).

tff(c_222,plain,(
    k3_funct_2('#skF_2','#skF_1','#skF_4','#skF_6') = k1_funct_1('#skF_4','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_219])).

tff(c_179,plain,(
    ! [A_126,B_127,C_128,D_129] :
      ( m1_subset_1(k3_funct_2(A_126,B_127,C_128,D_129),B_127)
      | ~ m1_subset_1(D_129,A_126)
      | ~ m1_subset_1(C_128,k1_zfmisc_1(k2_zfmisc_1(A_126,B_127)))
      | ~ v1_funct_2(C_128,A_126,B_127)
      | ~ v1_funct_1(C_128)
      | v1_xboole_0(A_126) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_181,plain,(
    ! [D_129] :
      ( m1_subset_1(k3_funct_2('#skF_2','#skF_1','#skF_4',D_129),'#skF_1')
      | ~ m1_subset_1(D_129,'#skF_2')
      | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
      | ~ v1_funct_1('#skF_4')
      | v1_xboole_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_52,c_179])).

tff(c_186,plain,(
    ! [D_129] :
      ( m1_subset_1(k3_funct_2('#skF_2','#skF_1','#skF_4',D_129),'#skF_1')
      | ~ m1_subset_1(D_129,'#skF_2')
      | v1_xboole_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_181])).

tff(c_187,plain,(
    ! [D_129] :
      ( m1_subset_1(k3_funct_2('#skF_2','#skF_1','#skF_4',D_129),'#skF_1')
      | ~ m1_subset_1(D_129,'#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_186])).

tff(c_227,plain,
    ( m1_subset_1(k1_funct_1('#skF_4','#skF_6'),'#skF_1')
    | ~ m1_subset_1('#skF_6','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_222,c_187])).

tff(c_231,plain,(
    m1_subset_1(k1_funct_1('#skF_4','#skF_6'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_227])).

tff(c_36,plain,(
    ! [A_33,B_34,C_35,D_36] :
      ( k3_funct_2(A_33,B_34,C_35,D_36) = k1_funct_1(C_35,D_36)
      | ~ m1_subset_1(D_36,A_33)
      | ~ m1_subset_1(C_35,k1_zfmisc_1(k2_zfmisc_1(A_33,B_34)))
      | ~ v1_funct_2(C_35,A_33,B_34)
      | ~ v1_funct_1(C_35)
      | v1_xboole_0(A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_234,plain,(
    ! [B_34,C_35] :
      ( k3_funct_2('#skF_1',B_34,C_35,k1_funct_1('#skF_4','#skF_6')) = k1_funct_1(C_35,k1_funct_1('#skF_4','#skF_6'))
      | ~ m1_subset_1(C_35,k1_zfmisc_1(k2_zfmisc_1('#skF_1',B_34)))
      | ~ v1_funct_2(C_35,'#skF_1',B_34)
      | ~ v1_funct_1(C_35)
      | v1_xboole_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_231,c_36])).

tff(c_257,plain,(
    ! [B_147,C_148] :
      ( k3_funct_2('#skF_1',B_147,C_148,k1_funct_1('#skF_4','#skF_6')) = k1_funct_1(C_148,k1_funct_1('#skF_4','#skF_6'))
      | ~ m1_subset_1(C_148,k1_zfmisc_1(k2_zfmisc_1('#skF_1',B_147)))
      | ~ v1_funct_2(C_148,'#skF_1',B_147)
      | ~ v1_funct_1(C_148) ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_234])).

tff(c_260,plain,
    ( k3_funct_2('#skF_1','#skF_3','#skF_5',k1_funct_1('#skF_4','#skF_6')) = k1_funct_1('#skF_5',k1_funct_1('#skF_4','#skF_6'))
    | ~ v1_funct_2('#skF_5','#skF_1','#skF_3')
    | ~ v1_funct_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_48,c_257])).

tff(c_263,plain,(
    k3_funct_2('#skF_1','#skF_3','#skF_5',k1_funct_1('#skF_4','#skF_6')) = k1_funct_1('#skF_5',k1_funct_1('#skF_4','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_178,c_260])).

tff(c_278,plain,(
    ! [A_149,B_150,C_151,D_152] :
      ( k3_funct_2(A_149,B_150,C_151,D_152) = k7_partfun1(B_150,C_151,D_152)
      | ~ m1_subset_1(D_152,A_149)
      | ~ m1_subset_1(C_151,k1_zfmisc_1(k2_zfmisc_1(A_149,B_150)))
      | ~ v1_funct_2(C_151,A_149,B_150)
      | ~ v1_funct_1(C_151)
      | v1_xboole_0(B_150)
      | v1_xboole_0(A_149) ) ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_282,plain,(
    ! [B_150,C_151] :
      ( k3_funct_2('#skF_1',B_150,C_151,k1_funct_1('#skF_4','#skF_6')) = k7_partfun1(B_150,C_151,k1_funct_1('#skF_4','#skF_6'))
      | ~ m1_subset_1(C_151,k1_zfmisc_1(k2_zfmisc_1('#skF_1',B_150)))
      | ~ v1_funct_2(C_151,'#skF_1',B_150)
      | ~ v1_funct_1(C_151)
      | v1_xboole_0(B_150)
      | v1_xboole_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_231,c_278])).

tff(c_340,plain,(
    ! [B_164,C_165] :
      ( k3_funct_2('#skF_1',B_164,C_165,k1_funct_1('#skF_4','#skF_6')) = k7_partfun1(B_164,C_165,k1_funct_1('#skF_4','#skF_6'))
      | ~ m1_subset_1(C_165,k1_zfmisc_1(k2_zfmisc_1('#skF_1',B_164)))
      | ~ v1_funct_2(C_165,'#skF_1',B_164)
      | ~ v1_funct_1(C_165)
      | v1_xboole_0(B_164) ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_282])).

tff(c_343,plain,
    ( k3_funct_2('#skF_1','#skF_3','#skF_5',k1_funct_1('#skF_4','#skF_6')) = k7_partfun1('#skF_3','#skF_5',k1_funct_1('#skF_4','#skF_6'))
    | ~ v1_funct_2('#skF_5','#skF_1','#skF_3')
    | ~ v1_funct_1('#skF_5')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_48,c_340])).

tff(c_346,plain,
    ( k7_partfun1('#skF_3','#skF_5',k1_funct_1('#skF_4','#skF_6')) = k1_funct_1('#skF_5',k1_funct_1('#skF_4','#skF_6'))
    | v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_178,c_263,c_343])).

tff(c_347,plain,(
    k7_partfun1('#skF_3','#skF_5',k1_funct_1('#skF_4','#skF_6')) = k1_funct_1('#skF_5',k1_funct_1('#skF_4','#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_165,c_346])).

tff(c_42,plain,(
    k3_funct_2('#skF_2','#skF_3',k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),'#skF_6') != k7_partfun1('#skF_3','#skF_5',k3_funct_2('#skF_2','#skF_1','#skF_4','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_191])).

tff(c_223,plain,(
    k3_funct_2('#skF_2','#skF_3',k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),'#skF_6') != k7_partfun1('#skF_3','#skF_5',k1_funct_1('#skF_4','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_222,c_42])).

tff(c_348,plain,(
    k3_funct_2('#skF_2','#skF_3',k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),'#skF_6') != k1_funct_1('#skF_5',k1_funct_1('#skF_4','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_347,c_223])).

tff(c_1037,plain,(
    k1_funct_1(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),'#skF_6') != k1_funct_1('#skF_5',k1_funct_1('#skF_4','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1005,c_348])).

tff(c_1065,plain,(
    ~ m1_subset_1('#skF_6','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_638,c_1037])).

tff(c_1069,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_1065])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n024.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 12:36:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.46/1.78  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.53/1.81  
% 4.53/1.81  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.53/1.81  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k8_funct_2 > k3_funct_2 > k7_partfun1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 4.53/1.81  
% 4.53/1.81  %Foreground sorts:
% 4.53/1.81  
% 4.53/1.81  
% 4.53/1.81  %Background operators:
% 4.53/1.81  
% 4.53/1.81  
% 4.53/1.81  %Foreground operators:
% 4.53/1.81  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 4.53/1.81  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.53/1.81  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.53/1.81  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.53/1.81  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.53/1.81  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 4.53/1.81  tff(k7_partfun1, type, k7_partfun1: ($i * $i * $i) > $i).
% 4.53/1.81  tff('#skF_5', type, '#skF_5': $i).
% 4.53/1.81  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.53/1.81  tff(k8_funct_2, type, k8_funct_2: ($i * $i * $i * $i * $i) > $i).
% 4.53/1.81  tff('#skF_6', type, '#skF_6': $i).
% 4.53/1.81  tff('#skF_2', type, '#skF_2': $i).
% 4.53/1.81  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 4.53/1.81  tff('#skF_3', type, '#skF_3': $i).
% 4.53/1.81  tff('#skF_1', type, '#skF_1': $i).
% 4.53/1.81  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 4.53/1.81  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 4.53/1.81  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.53/1.81  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 4.53/1.81  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.53/1.81  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.53/1.81  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.53/1.81  tff('#skF_4', type, '#skF_4': $i).
% 4.53/1.81  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.53/1.81  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 4.53/1.81  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.53/1.81  tff(k3_funct_2, type, k3_funct_2: ($i * $i * $i * $i) > $i).
% 4.53/1.81  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.53/1.81  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.53/1.81  
% 4.73/1.84  tff(f_191, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C, D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (![E]: ((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, C)))) => (![F]: (m1_subset_1(F, B) => (v1_partfun1(E, A) => (k3_funct_2(B, C, k8_funct_2(B, A, C, D, E), F) = k7_partfun1(C, E, k3_funct_2(B, A, D, F)))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t193_funct_2)).
% 4.73/1.84  tff(f_36, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 4.73/1.84  tff(f_42, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 4.73/1.84  tff(f_32, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 4.73/1.84  tff(f_79, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (v1_partfun1(B, A) <=> (k1_relat_1(B) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_partfun1)).
% 4.73/1.84  tff(f_46, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 4.73/1.84  tff(f_50, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 4.73/1.84  tff(f_164, axiom, (![A, B, C]: (~v1_xboole_0(C) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, C)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (![E]: ((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(C, A)))) => (![F]: (m1_subset_1(F, B) => (r1_tarski(k2_relset_1(B, C, D), k1_relset_1(C, A, E)) => ((B = k1_xboole_0) | (k1_funct_1(k8_funct_2(B, C, A, D, E), F) = k1_funct_1(E, k1_funct_1(D, F))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t185_funct_2)).
% 4.73/1.84  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 4.73/1.84  tff(f_108, axiom, (![A, B, C, D, E]: (((((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(E)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => ((v1_funct_1(k8_funct_2(A, B, C, D, E)) & v1_funct_2(k8_funct_2(A, B, C, D, E), A, C)) & m1_subset_1(k8_funct_2(A, B, C, D, E), k1_zfmisc_1(k2_zfmisc_1(A, C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k8_funct_2)).
% 4.73/1.84  tff(f_121, axiom, (![A, B, C, D]: (((((~v1_xboole_0(A) & v1_funct_1(C)) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & m1_subset_1(D, A)) => (k3_funct_2(A, B, C, D) = k1_funct_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k3_funct_2)).
% 4.73/1.84  tff(f_71, axiom, (![A, B]: ((~v1_xboole_0(A) & v1_xboole_0(B)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ~v1_partfun1(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_partfun1)).
% 4.73/1.84  tff(f_60, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v1_partfun1(C, A)) => (v1_funct_1(C) & v1_funct_2(C, A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_funct_2)).
% 4.73/1.84  tff(f_92, axiom, (![A, B, C, D]: (((((~v1_xboole_0(A) & v1_funct_1(C)) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & m1_subset_1(D, A)) => m1_subset_1(k3_funct_2(A, B, C, D), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k3_funct_2)).
% 4.73/1.84  tff(f_140, axiom, (![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (m1_subset_1(D, A) => (k7_partfun1(B, C, D) = k3_funct_2(A, B, C, D)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t176_funct_2)).
% 4.73/1.84  tff(c_46, plain, (m1_subset_1('#skF_6', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_191])).
% 4.73/1.84  tff(c_52, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_191])).
% 4.73/1.84  tff(c_61, plain, (![C_98, A_99, B_100]: (v1_relat_1(C_98) | ~m1_subset_1(C_98, k1_zfmisc_1(k2_zfmisc_1(A_99, B_100))))), inference(cnfTransformation, [status(thm)], [f_36])).
% 4.73/1.84  tff(c_68, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_52, c_61])).
% 4.73/1.84  tff(c_71, plain, (![C_103, B_104, A_105]: (v5_relat_1(C_103, B_104) | ~m1_subset_1(C_103, k1_zfmisc_1(k2_zfmisc_1(A_105, B_104))))), inference(cnfTransformation, [status(thm)], [f_42])).
% 4.73/1.84  tff(c_78, plain, (v5_relat_1('#skF_4', '#skF_1')), inference(resolution, [status(thm)], [c_52, c_71])).
% 4.73/1.84  tff(c_6, plain, (![B_2, A_1]: (r1_tarski(k2_relat_1(B_2), A_1) | ~v5_relat_1(B_2, A_1) | ~v1_relat_1(B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.73/1.84  tff(c_50, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_191])).
% 4.73/1.84  tff(c_48, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_191])).
% 4.73/1.84  tff(c_69, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_48, c_61])).
% 4.73/1.84  tff(c_44, plain, (v1_partfun1('#skF_5', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_191])).
% 4.73/1.84  tff(c_85, plain, (![C_108, A_109, B_110]: (v4_relat_1(C_108, A_109) | ~m1_subset_1(C_108, k1_zfmisc_1(k2_zfmisc_1(A_109, B_110))))), inference(cnfTransformation, [status(thm)], [f_42])).
% 4.73/1.84  tff(c_93, plain, (v4_relat_1('#skF_5', '#skF_1')), inference(resolution, [status(thm)], [c_48, c_85])).
% 4.73/1.84  tff(c_95, plain, (![B_112, A_113]: (k1_relat_1(B_112)=A_113 | ~v1_partfun1(B_112, A_113) | ~v4_relat_1(B_112, A_113) | ~v1_relat_1(B_112))), inference(cnfTransformation, [status(thm)], [f_79])).
% 4.73/1.84  tff(c_98, plain, (k1_relat_1('#skF_5')='#skF_1' | ~v1_partfun1('#skF_5', '#skF_1') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_93, c_95])).
% 4.73/1.84  tff(c_104, plain, (k1_relat_1('#skF_5')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_69, c_44, c_98])).
% 4.73/1.84  tff(c_117, plain, (![A_114, B_115, C_116]: (k1_relset_1(A_114, B_115, C_116)=k1_relat_1(C_116) | ~m1_subset_1(C_116, k1_zfmisc_1(k2_zfmisc_1(A_114, B_115))))), inference(cnfTransformation, [status(thm)], [f_46])).
% 4.73/1.84  tff(c_123, plain, (k1_relset_1('#skF_1', '#skF_3', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_48, c_117])).
% 4.73/1.84  tff(c_126, plain, (k1_relset_1('#skF_1', '#skF_3', '#skF_5')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_104, c_123])).
% 4.73/1.84  tff(c_58, plain, (~v1_xboole_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_191])).
% 4.73/1.84  tff(c_60, plain, (~v1_xboole_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_191])).
% 4.73/1.84  tff(c_56, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_191])).
% 4.73/1.84  tff(c_54, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_191])).
% 4.73/1.84  tff(c_136, plain, (![A_117, B_118, C_119]: (k2_relset_1(A_117, B_118, C_119)=k2_relat_1(C_119) | ~m1_subset_1(C_119, k1_zfmisc_1(k2_zfmisc_1(A_117, B_118))))), inference(cnfTransformation, [status(thm)], [f_50])).
% 4.73/1.84  tff(c_143, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_52, c_136])).
% 4.73/1.84  tff(c_455, plain, (![B_180, D_181, E_178, C_183, A_179, F_182]: (k1_funct_1(k8_funct_2(B_180, C_183, A_179, D_181, E_178), F_182)=k1_funct_1(E_178, k1_funct_1(D_181, F_182)) | k1_xboole_0=B_180 | ~r1_tarski(k2_relset_1(B_180, C_183, D_181), k1_relset_1(C_183, A_179, E_178)) | ~m1_subset_1(F_182, B_180) | ~m1_subset_1(E_178, k1_zfmisc_1(k2_zfmisc_1(C_183, A_179))) | ~v1_funct_1(E_178) | ~m1_subset_1(D_181, k1_zfmisc_1(k2_zfmisc_1(B_180, C_183))) | ~v1_funct_2(D_181, B_180, C_183) | ~v1_funct_1(D_181) | v1_xboole_0(C_183))), inference(cnfTransformation, [status(thm)], [f_164])).
% 4.73/1.84  tff(c_459, plain, (![A_179, E_178, F_182]: (k1_funct_1(k8_funct_2('#skF_2', '#skF_1', A_179, '#skF_4', E_178), F_182)=k1_funct_1(E_178, k1_funct_1('#skF_4', F_182)) | k1_xboole_0='#skF_2' | ~r1_tarski(k2_relat_1('#skF_4'), k1_relset_1('#skF_1', A_179, E_178)) | ~m1_subset_1(F_182, '#skF_2') | ~m1_subset_1(E_178, k1_zfmisc_1(k2_zfmisc_1('#skF_1', A_179))) | ~v1_funct_1(E_178) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4') | v1_xboole_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_143, c_455])).
% 4.73/1.84  tff(c_468, plain, (![A_179, E_178, F_182]: (k1_funct_1(k8_funct_2('#skF_2', '#skF_1', A_179, '#skF_4', E_178), F_182)=k1_funct_1(E_178, k1_funct_1('#skF_4', F_182)) | k1_xboole_0='#skF_2' | ~r1_tarski(k2_relat_1('#skF_4'), k1_relset_1('#skF_1', A_179, E_178)) | ~m1_subset_1(F_182, '#skF_2') | ~m1_subset_1(E_178, k1_zfmisc_1(k2_zfmisc_1('#skF_1', A_179))) | ~v1_funct_1(E_178) | v1_xboole_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_52, c_459])).
% 4.73/1.84  tff(c_469, plain, (![A_179, E_178, F_182]: (k1_funct_1(k8_funct_2('#skF_2', '#skF_1', A_179, '#skF_4', E_178), F_182)=k1_funct_1(E_178, k1_funct_1('#skF_4', F_182)) | k1_xboole_0='#skF_2' | ~r1_tarski(k2_relat_1('#skF_4'), k1_relset_1('#skF_1', A_179, E_178)) | ~m1_subset_1(F_182, '#skF_2') | ~m1_subset_1(E_178, k1_zfmisc_1(k2_zfmisc_1('#skF_1', A_179))) | ~v1_funct_1(E_178))), inference(negUnitSimplification, [status(thm)], [c_60, c_468])).
% 4.73/1.84  tff(c_587, plain, (k1_xboole_0='#skF_2'), inference(splitLeft, [status(thm)], [c_469])).
% 4.73/1.84  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 4.73/1.84  tff(c_589, plain, (v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_587, c_2])).
% 4.73/1.84  tff(c_591, plain, $false, inference(negUnitSimplification, [status(thm)], [c_58, c_589])).
% 4.73/1.84  tff(c_618, plain, (![A_219, E_220, F_221]: (k1_funct_1(k8_funct_2('#skF_2', '#skF_1', A_219, '#skF_4', E_220), F_221)=k1_funct_1(E_220, k1_funct_1('#skF_4', F_221)) | ~r1_tarski(k2_relat_1('#skF_4'), k1_relset_1('#skF_1', A_219, E_220)) | ~m1_subset_1(F_221, '#skF_2') | ~m1_subset_1(E_220, k1_zfmisc_1(k2_zfmisc_1('#skF_1', A_219))) | ~v1_funct_1(E_220))), inference(splitRight, [status(thm)], [c_469])).
% 4.73/1.84  tff(c_620, plain, (![F_221]: (k1_funct_1(k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), F_221)=k1_funct_1('#skF_5', k1_funct_1('#skF_4', F_221)) | ~r1_tarski(k2_relat_1('#skF_4'), '#skF_1') | ~m1_subset_1(F_221, '#skF_2') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3'))) | ~v1_funct_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_126, c_618])).
% 4.73/1.84  tff(c_625, plain, (![F_221]: (k1_funct_1(k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), F_221)=k1_funct_1('#skF_5', k1_funct_1('#skF_4', F_221)) | ~r1_tarski(k2_relat_1('#skF_4'), '#skF_1') | ~m1_subset_1(F_221, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_620])).
% 4.73/1.84  tff(c_629, plain, (~r1_tarski(k2_relat_1('#skF_4'), '#skF_1')), inference(splitLeft, [status(thm)], [c_625])).
% 4.73/1.84  tff(c_633, plain, (~v5_relat_1('#skF_4', '#skF_1') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_6, c_629])).
% 4.73/1.84  tff(c_637, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_68, c_78, c_633])).
% 4.73/1.84  tff(c_638, plain, (![F_221]: (k1_funct_1(k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), F_221)=k1_funct_1('#skF_5', k1_funct_1('#skF_4', F_221)) | ~m1_subset_1(F_221, '#skF_2'))), inference(splitRight, [status(thm)], [c_625])).
% 4.73/1.84  tff(c_238, plain, (![E_138, C_140, D_142, A_139, B_141]: (v1_funct_1(k8_funct_2(A_139, B_141, C_140, D_142, E_138)) | ~m1_subset_1(E_138, k1_zfmisc_1(k2_zfmisc_1(B_141, C_140))) | ~v1_funct_1(E_138) | ~m1_subset_1(D_142, k1_zfmisc_1(k2_zfmisc_1(A_139, B_141))) | ~v1_funct_2(D_142, A_139, B_141) | ~v1_funct_1(D_142))), inference(cnfTransformation, [status(thm)], [f_108])).
% 4.73/1.84  tff(c_242, plain, (![A_139, D_142]: (v1_funct_1(k8_funct_2(A_139, '#skF_1', '#skF_3', D_142, '#skF_5')) | ~v1_funct_1('#skF_5') | ~m1_subset_1(D_142, k1_zfmisc_1(k2_zfmisc_1(A_139, '#skF_1'))) | ~v1_funct_2(D_142, A_139, '#skF_1') | ~v1_funct_1(D_142))), inference(resolution, [status(thm)], [c_48, c_238])).
% 4.73/1.84  tff(c_250, plain, (![A_145, D_146]: (v1_funct_1(k8_funct_2(A_145, '#skF_1', '#skF_3', D_146, '#skF_5')) | ~m1_subset_1(D_146, k1_zfmisc_1(k2_zfmisc_1(A_145, '#skF_1'))) | ~v1_funct_2(D_146, A_145, '#skF_1') | ~v1_funct_1(D_146))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_242])).
% 4.73/1.84  tff(c_253, plain, (v1_funct_1(k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5')) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_52, c_250])).
% 4.73/1.84  tff(c_256, plain, (v1_funct_1(k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_253])).
% 4.73/1.84  tff(c_322, plain, (![A_156, E_155, D_159, B_158, C_157]: (v1_funct_2(k8_funct_2(A_156, B_158, C_157, D_159, E_155), A_156, C_157) | ~m1_subset_1(E_155, k1_zfmisc_1(k2_zfmisc_1(B_158, C_157))) | ~v1_funct_1(E_155) | ~m1_subset_1(D_159, k1_zfmisc_1(k2_zfmisc_1(A_156, B_158))) | ~v1_funct_2(D_159, A_156, B_158) | ~v1_funct_1(D_159))), inference(cnfTransformation, [status(thm)], [f_108])).
% 4.73/1.84  tff(c_326, plain, (![A_156, D_159]: (v1_funct_2(k8_funct_2(A_156, '#skF_1', '#skF_3', D_159, '#skF_5'), A_156, '#skF_3') | ~v1_funct_1('#skF_5') | ~m1_subset_1(D_159, k1_zfmisc_1(k2_zfmisc_1(A_156, '#skF_1'))) | ~v1_funct_2(D_159, A_156, '#skF_1') | ~v1_funct_1(D_159))), inference(resolution, [status(thm)], [c_48, c_322])).
% 4.73/1.84  tff(c_334, plain, (![A_162, D_163]: (v1_funct_2(k8_funct_2(A_162, '#skF_1', '#skF_3', D_163, '#skF_5'), A_162, '#skF_3') | ~m1_subset_1(D_163, k1_zfmisc_1(k2_zfmisc_1(A_162, '#skF_1'))) | ~v1_funct_2(D_163, A_162, '#skF_1') | ~v1_funct_1(D_163))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_326])).
% 4.73/1.84  tff(c_336, plain, (v1_funct_2(k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), '#skF_2', '#skF_3') | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_52, c_334])).
% 4.73/1.84  tff(c_339, plain, (v1_funct_2(k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), '#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_336])).
% 4.73/1.84  tff(c_30, plain, (![C_30, E_32, D_31, B_29, A_28]: (m1_subset_1(k8_funct_2(A_28, B_29, C_30, D_31, E_32), k1_zfmisc_1(k2_zfmisc_1(A_28, C_30))) | ~m1_subset_1(E_32, k1_zfmisc_1(k2_zfmisc_1(B_29, C_30))) | ~v1_funct_1(E_32) | ~m1_subset_1(D_31, k1_zfmisc_1(k2_zfmisc_1(A_28, B_29))) | ~v1_funct_2(D_31, A_28, B_29) | ~v1_funct_1(D_31))), inference(cnfTransformation, [status(thm)], [f_108])).
% 4.73/1.84  tff(c_354, plain, (![C_170, D_172, E_168, A_169, B_171]: (m1_subset_1(k8_funct_2(A_169, B_171, C_170, D_172, E_168), k1_zfmisc_1(k2_zfmisc_1(A_169, C_170))) | ~m1_subset_1(E_168, k1_zfmisc_1(k2_zfmisc_1(B_171, C_170))) | ~v1_funct_1(E_168) | ~m1_subset_1(D_172, k1_zfmisc_1(k2_zfmisc_1(A_169, B_171))) | ~v1_funct_2(D_172, A_169, B_171) | ~v1_funct_1(D_172))), inference(cnfTransformation, [status(thm)], [f_108])).
% 4.73/1.84  tff(c_14, plain, (![A_9, B_10, C_11]: (k1_relset_1(A_9, B_10, C_11)=k1_relat_1(C_11) | ~m1_subset_1(C_11, k1_zfmisc_1(k2_zfmisc_1(A_9, B_10))))), inference(cnfTransformation, [status(thm)], [f_46])).
% 4.73/1.84  tff(c_698, plain, (![E_239, D_238, A_237, B_241, C_240]: (k1_relset_1(A_237, C_240, k8_funct_2(A_237, B_241, C_240, D_238, E_239))=k1_relat_1(k8_funct_2(A_237, B_241, C_240, D_238, E_239)) | ~m1_subset_1(E_239, k1_zfmisc_1(k2_zfmisc_1(B_241, C_240))) | ~v1_funct_1(E_239) | ~m1_subset_1(D_238, k1_zfmisc_1(k2_zfmisc_1(A_237, B_241))) | ~v1_funct_2(D_238, A_237, B_241) | ~v1_funct_1(D_238))), inference(resolution, [status(thm)], [c_354, c_14])).
% 4.73/1.84  tff(c_704, plain, (![A_237, D_238]: (k1_relset_1(A_237, '#skF_3', k8_funct_2(A_237, '#skF_1', '#skF_3', D_238, '#skF_5'))=k1_relat_1(k8_funct_2(A_237, '#skF_1', '#skF_3', D_238, '#skF_5')) | ~v1_funct_1('#skF_5') | ~m1_subset_1(D_238, k1_zfmisc_1(k2_zfmisc_1(A_237, '#skF_1'))) | ~v1_funct_2(D_238, A_237, '#skF_1') | ~v1_funct_1(D_238))), inference(resolution, [status(thm)], [c_48, c_698])).
% 4.73/1.84  tff(c_717, plain, (![A_244, D_245]: (k1_relset_1(A_244, '#skF_3', k8_funct_2(A_244, '#skF_1', '#skF_3', D_245, '#skF_5'))=k1_relat_1(k8_funct_2(A_244, '#skF_1', '#skF_3', D_245, '#skF_5')) | ~m1_subset_1(D_245, k1_zfmisc_1(k2_zfmisc_1(A_244, '#skF_1'))) | ~v1_funct_2(D_245, A_244, '#skF_1') | ~v1_funct_1(D_245))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_704])).
% 4.73/1.84  tff(c_722, plain, (k1_relset_1('#skF_2', '#skF_3', k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'))=k1_relat_1(k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5')) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_52, c_717])).
% 4.73/1.84  tff(c_726, plain, (k1_relset_1('#skF_2', '#skF_3', k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'))=k1_relat_1(k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_722])).
% 4.73/1.84  tff(c_40, plain, (![F_68, E_66, D_62, B_53, A_52, C_54]: (k1_funct_1(k8_funct_2(B_53, C_54, A_52, D_62, E_66), F_68)=k1_funct_1(E_66, k1_funct_1(D_62, F_68)) | k1_xboole_0=B_53 | ~r1_tarski(k2_relset_1(B_53, C_54, D_62), k1_relset_1(C_54, A_52, E_66)) | ~m1_subset_1(F_68, B_53) | ~m1_subset_1(E_66, k1_zfmisc_1(k2_zfmisc_1(C_54, A_52))) | ~v1_funct_1(E_66) | ~m1_subset_1(D_62, k1_zfmisc_1(k2_zfmisc_1(B_53, C_54))) | ~v1_funct_2(D_62, B_53, C_54) | ~v1_funct_1(D_62) | v1_xboole_0(C_54))), inference(cnfTransformation, [status(thm)], [f_164])).
% 4.73/1.84  tff(c_729, plain, (![B_53, D_62, F_68]: (k1_funct_1(k8_funct_2(B_53, '#skF_2', '#skF_3', D_62, k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5')), F_68)=k1_funct_1(k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), k1_funct_1(D_62, F_68)) | k1_xboole_0=B_53 | ~r1_tarski(k2_relset_1(B_53, '#skF_2', D_62), k1_relat_1(k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'))) | ~m1_subset_1(F_68, B_53) | ~m1_subset_1(k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~v1_funct_1(k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5')) | ~m1_subset_1(D_62, k1_zfmisc_1(k2_zfmisc_1(B_53, '#skF_2'))) | ~v1_funct_2(D_62, B_53, '#skF_2') | ~v1_funct_1(D_62) | v1_xboole_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_726, c_40])).
% 4.73/1.84  tff(c_733, plain, (![B_53, D_62, F_68]: (k1_funct_1(k8_funct_2(B_53, '#skF_2', '#skF_3', D_62, k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5')), F_68)=k1_funct_1(k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), k1_funct_1(D_62, F_68)) | k1_xboole_0=B_53 | ~r1_tarski(k2_relset_1(B_53, '#skF_2', D_62), k1_relat_1(k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'))) | ~m1_subset_1(F_68, B_53) | ~m1_subset_1(k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~m1_subset_1(D_62, k1_zfmisc_1(k2_zfmisc_1(B_53, '#skF_2'))) | ~v1_funct_2(D_62, B_53, '#skF_2') | ~v1_funct_1(D_62) | v1_xboole_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_256, c_729])).
% 4.73/1.84  tff(c_734, plain, (![B_53, D_62, F_68]: (k1_funct_1(k8_funct_2(B_53, '#skF_2', '#skF_3', D_62, k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5')), F_68)=k1_funct_1(k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), k1_funct_1(D_62, F_68)) | k1_xboole_0=B_53 | ~r1_tarski(k2_relset_1(B_53, '#skF_2', D_62), k1_relat_1(k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'))) | ~m1_subset_1(F_68, B_53) | ~m1_subset_1(k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~m1_subset_1(D_62, k1_zfmisc_1(k2_zfmisc_1(B_53, '#skF_2'))) | ~v1_funct_2(D_62, B_53, '#skF_2') | ~v1_funct_1(D_62))), inference(negUnitSimplification, [status(thm)], [c_58, c_733])).
% 4.73/1.84  tff(c_910, plain, (~m1_subset_1(k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(splitLeft, [status(thm)], [c_734])).
% 4.73/1.84  tff(c_913, plain, (~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3'))) | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_30, c_910])).
% 4.73/1.84  tff(c_917, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_52, c_50, c_48, c_913])).
% 4.73/1.84  tff(c_919, plain, (m1_subset_1(k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(splitRight, [status(thm)], [c_734])).
% 4.73/1.84  tff(c_194, plain, (![A_132, B_133, C_134, D_135]: (k3_funct_2(A_132, B_133, C_134, D_135)=k1_funct_1(C_134, D_135) | ~m1_subset_1(D_135, A_132) | ~m1_subset_1(C_134, k1_zfmisc_1(k2_zfmisc_1(A_132, B_133))) | ~v1_funct_2(C_134, A_132, B_133) | ~v1_funct_1(C_134) | v1_xboole_0(A_132))), inference(cnfTransformation, [status(thm)], [f_121])).
% 4.73/1.84  tff(c_204, plain, (![B_133, C_134]: (k3_funct_2('#skF_2', B_133, C_134, '#skF_6')=k1_funct_1(C_134, '#skF_6') | ~m1_subset_1(C_134, k1_zfmisc_1(k2_zfmisc_1('#skF_2', B_133))) | ~v1_funct_2(C_134, '#skF_2', B_133) | ~v1_funct_1(C_134) | v1_xboole_0('#skF_2'))), inference(resolution, [status(thm)], [c_46, c_194])).
% 4.73/1.84  tff(c_215, plain, (![B_133, C_134]: (k3_funct_2('#skF_2', B_133, C_134, '#skF_6')=k1_funct_1(C_134, '#skF_6') | ~m1_subset_1(C_134, k1_zfmisc_1(k2_zfmisc_1('#skF_2', B_133))) | ~v1_funct_2(C_134, '#skF_2', B_133) | ~v1_funct_1(C_134))), inference(negUnitSimplification, [status(thm)], [c_58, c_204])).
% 4.73/1.84  tff(c_945, plain, (k3_funct_2('#skF_2', '#skF_3', k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), '#skF_6')=k1_funct_1(k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), '#skF_6') | ~v1_funct_2(k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), '#skF_2', '#skF_3') | ~v1_funct_1(k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_919, c_215])).
% 4.73/1.84  tff(c_1005, plain, (k3_funct_2('#skF_2', '#skF_3', k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), '#skF_6')=k1_funct_1(k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_256, c_339, c_945])).
% 4.73/1.84  tff(c_153, plain, (![C_120, A_121, B_122]: (~v1_partfun1(C_120, A_121) | ~m1_subset_1(C_120, k1_zfmisc_1(k2_zfmisc_1(A_121, B_122))) | ~v1_xboole_0(B_122) | v1_xboole_0(A_121))), inference(cnfTransformation, [status(thm)], [f_71])).
% 4.73/1.84  tff(c_159, plain, (~v1_partfun1('#skF_5', '#skF_1') | ~v1_xboole_0('#skF_3') | v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_48, c_153])).
% 4.73/1.84  tff(c_164, plain, (~v1_xboole_0('#skF_3') | v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_159])).
% 4.73/1.84  tff(c_165, plain, (~v1_xboole_0('#skF_3')), inference(negUnitSimplification, [status(thm)], [c_60, c_164])).
% 4.73/1.84  tff(c_166, plain, (![C_123, A_124, B_125]: (v1_funct_2(C_123, A_124, B_125) | ~v1_partfun1(C_123, A_124) | ~v1_funct_1(C_123) | ~m1_subset_1(C_123, k1_zfmisc_1(k2_zfmisc_1(A_124, B_125))))), inference(cnfTransformation, [status(thm)], [f_60])).
% 4.73/1.84  tff(c_172, plain, (v1_funct_2('#skF_5', '#skF_1', '#skF_3') | ~v1_partfun1('#skF_5', '#skF_1') | ~v1_funct_1('#skF_5')), inference(resolution, [status(thm)], [c_48, c_166])).
% 4.73/1.84  tff(c_178, plain, (v1_funct_2('#skF_5', '#skF_1', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_44, c_172])).
% 4.73/1.84  tff(c_216, plain, (![B_136, C_137]: (k3_funct_2('#skF_2', B_136, C_137, '#skF_6')=k1_funct_1(C_137, '#skF_6') | ~m1_subset_1(C_137, k1_zfmisc_1(k2_zfmisc_1('#skF_2', B_136))) | ~v1_funct_2(C_137, '#skF_2', B_136) | ~v1_funct_1(C_137))), inference(negUnitSimplification, [status(thm)], [c_58, c_204])).
% 4.73/1.84  tff(c_219, plain, (k3_funct_2('#skF_2', '#skF_1', '#skF_4', '#skF_6')=k1_funct_1('#skF_4', '#skF_6') | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_52, c_216])).
% 4.73/1.84  tff(c_222, plain, (k3_funct_2('#skF_2', '#skF_1', '#skF_4', '#skF_6')=k1_funct_1('#skF_4', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_219])).
% 4.73/1.84  tff(c_179, plain, (![A_126, B_127, C_128, D_129]: (m1_subset_1(k3_funct_2(A_126, B_127, C_128, D_129), B_127) | ~m1_subset_1(D_129, A_126) | ~m1_subset_1(C_128, k1_zfmisc_1(k2_zfmisc_1(A_126, B_127))) | ~v1_funct_2(C_128, A_126, B_127) | ~v1_funct_1(C_128) | v1_xboole_0(A_126))), inference(cnfTransformation, [status(thm)], [f_92])).
% 4.73/1.84  tff(c_181, plain, (![D_129]: (m1_subset_1(k3_funct_2('#skF_2', '#skF_1', '#skF_4', D_129), '#skF_1') | ~m1_subset_1(D_129, '#skF_2') | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4') | v1_xboole_0('#skF_2'))), inference(resolution, [status(thm)], [c_52, c_179])).
% 4.73/1.84  tff(c_186, plain, (![D_129]: (m1_subset_1(k3_funct_2('#skF_2', '#skF_1', '#skF_4', D_129), '#skF_1') | ~m1_subset_1(D_129, '#skF_2') | v1_xboole_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_181])).
% 4.73/1.84  tff(c_187, plain, (![D_129]: (m1_subset_1(k3_funct_2('#skF_2', '#skF_1', '#skF_4', D_129), '#skF_1') | ~m1_subset_1(D_129, '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_58, c_186])).
% 4.73/1.84  tff(c_227, plain, (m1_subset_1(k1_funct_1('#skF_4', '#skF_6'), '#skF_1') | ~m1_subset_1('#skF_6', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_222, c_187])).
% 4.73/1.84  tff(c_231, plain, (m1_subset_1(k1_funct_1('#skF_4', '#skF_6'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_227])).
% 4.73/1.84  tff(c_36, plain, (![A_33, B_34, C_35, D_36]: (k3_funct_2(A_33, B_34, C_35, D_36)=k1_funct_1(C_35, D_36) | ~m1_subset_1(D_36, A_33) | ~m1_subset_1(C_35, k1_zfmisc_1(k2_zfmisc_1(A_33, B_34))) | ~v1_funct_2(C_35, A_33, B_34) | ~v1_funct_1(C_35) | v1_xboole_0(A_33))), inference(cnfTransformation, [status(thm)], [f_121])).
% 4.73/1.84  tff(c_234, plain, (![B_34, C_35]: (k3_funct_2('#skF_1', B_34, C_35, k1_funct_1('#skF_4', '#skF_6'))=k1_funct_1(C_35, k1_funct_1('#skF_4', '#skF_6')) | ~m1_subset_1(C_35, k1_zfmisc_1(k2_zfmisc_1('#skF_1', B_34))) | ~v1_funct_2(C_35, '#skF_1', B_34) | ~v1_funct_1(C_35) | v1_xboole_0('#skF_1'))), inference(resolution, [status(thm)], [c_231, c_36])).
% 4.73/1.84  tff(c_257, plain, (![B_147, C_148]: (k3_funct_2('#skF_1', B_147, C_148, k1_funct_1('#skF_4', '#skF_6'))=k1_funct_1(C_148, k1_funct_1('#skF_4', '#skF_6')) | ~m1_subset_1(C_148, k1_zfmisc_1(k2_zfmisc_1('#skF_1', B_147))) | ~v1_funct_2(C_148, '#skF_1', B_147) | ~v1_funct_1(C_148))), inference(negUnitSimplification, [status(thm)], [c_60, c_234])).
% 4.73/1.84  tff(c_260, plain, (k3_funct_2('#skF_1', '#skF_3', '#skF_5', k1_funct_1('#skF_4', '#skF_6'))=k1_funct_1('#skF_5', k1_funct_1('#skF_4', '#skF_6')) | ~v1_funct_2('#skF_5', '#skF_1', '#skF_3') | ~v1_funct_1('#skF_5')), inference(resolution, [status(thm)], [c_48, c_257])).
% 4.73/1.84  tff(c_263, plain, (k3_funct_2('#skF_1', '#skF_3', '#skF_5', k1_funct_1('#skF_4', '#skF_6'))=k1_funct_1('#skF_5', k1_funct_1('#skF_4', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_178, c_260])).
% 4.73/1.84  tff(c_278, plain, (![A_149, B_150, C_151, D_152]: (k3_funct_2(A_149, B_150, C_151, D_152)=k7_partfun1(B_150, C_151, D_152) | ~m1_subset_1(D_152, A_149) | ~m1_subset_1(C_151, k1_zfmisc_1(k2_zfmisc_1(A_149, B_150))) | ~v1_funct_2(C_151, A_149, B_150) | ~v1_funct_1(C_151) | v1_xboole_0(B_150) | v1_xboole_0(A_149))), inference(cnfTransformation, [status(thm)], [f_140])).
% 4.73/1.84  tff(c_282, plain, (![B_150, C_151]: (k3_funct_2('#skF_1', B_150, C_151, k1_funct_1('#skF_4', '#skF_6'))=k7_partfun1(B_150, C_151, k1_funct_1('#skF_4', '#skF_6')) | ~m1_subset_1(C_151, k1_zfmisc_1(k2_zfmisc_1('#skF_1', B_150))) | ~v1_funct_2(C_151, '#skF_1', B_150) | ~v1_funct_1(C_151) | v1_xboole_0(B_150) | v1_xboole_0('#skF_1'))), inference(resolution, [status(thm)], [c_231, c_278])).
% 4.73/1.84  tff(c_340, plain, (![B_164, C_165]: (k3_funct_2('#skF_1', B_164, C_165, k1_funct_1('#skF_4', '#skF_6'))=k7_partfun1(B_164, C_165, k1_funct_1('#skF_4', '#skF_6')) | ~m1_subset_1(C_165, k1_zfmisc_1(k2_zfmisc_1('#skF_1', B_164))) | ~v1_funct_2(C_165, '#skF_1', B_164) | ~v1_funct_1(C_165) | v1_xboole_0(B_164))), inference(negUnitSimplification, [status(thm)], [c_60, c_282])).
% 4.73/1.84  tff(c_343, plain, (k3_funct_2('#skF_1', '#skF_3', '#skF_5', k1_funct_1('#skF_4', '#skF_6'))=k7_partfun1('#skF_3', '#skF_5', k1_funct_1('#skF_4', '#skF_6')) | ~v1_funct_2('#skF_5', '#skF_1', '#skF_3') | ~v1_funct_1('#skF_5') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_48, c_340])).
% 4.73/1.84  tff(c_346, plain, (k7_partfun1('#skF_3', '#skF_5', k1_funct_1('#skF_4', '#skF_6'))=k1_funct_1('#skF_5', k1_funct_1('#skF_4', '#skF_6')) | v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_178, c_263, c_343])).
% 4.73/1.84  tff(c_347, plain, (k7_partfun1('#skF_3', '#skF_5', k1_funct_1('#skF_4', '#skF_6'))=k1_funct_1('#skF_5', k1_funct_1('#skF_4', '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_165, c_346])).
% 4.73/1.84  tff(c_42, plain, (k3_funct_2('#skF_2', '#skF_3', k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), '#skF_6')!=k7_partfun1('#skF_3', '#skF_5', k3_funct_2('#skF_2', '#skF_1', '#skF_4', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_191])).
% 4.73/1.84  tff(c_223, plain, (k3_funct_2('#skF_2', '#skF_3', k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), '#skF_6')!=k7_partfun1('#skF_3', '#skF_5', k1_funct_1('#skF_4', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_222, c_42])).
% 4.73/1.84  tff(c_348, plain, (k3_funct_2('#skF_2', '#skF_3', k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), '#skF_6')!=k1_funct_1('#skF_5', k1_funct_1('#skF_4', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_347, c_223])).
% 4.73/1.84  tff(c_1037, plain, (k1_funct_1(k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), '#skF_6')!=k1_funct_1('#skF_5', k1_funct_1('#skF_4', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_1005, c_348])).
% 4.73/1.84  tff(c_1065, plain, (~m1_subset_1('#skF_6', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_638, c_1037])).
% 4.73/1.84  tff(c_1069, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_46, c_1065])).
% 4.73/1.84  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.73/1.84  
% 4.73/1.84  Inference rules
% 4.73/1.84  ----------------------
% 4.73/1.84  #Ref     : 0
% 4.73/1.84  #Sup     : 207
% 4.73/1.84  #Fact    : 0
% 4.73/1.84  #Define  : 0
% 4.73/1.84  #Split   : 9
% 4.73/1.84  #Chain   : 0
% 4.73/1.84  #Close   : 0
% 4.73/1.84  
% 4.73/1.84  Ordering : KBO
% 4.73/1.84  
% 4.73/1.84  Simplification rules
% 4.73/1.84  ----------------------
% 4.73/1.84  #Subsume      : 9
% 4.73/1.84  #Demod        : 158
% 4.73/1.84  #Tautology    : 49
% 4.73/1.84  #SimpNegUnit  : 37
% 4.73/1.84  #BackRed      : 8
% 4.73/1.84  
% 4.73/1.84  #Partial instantiations: 0
% 4.73/1.84  #Strategies tried      : 1
% 4.73/1.84  
% 4.73/1.84  Timing (in seconds)
% 4.73/1.84  ----------------------
% 4.73/1.85  Preprocessing        : 0.41
% 4.73/1.85  Parsing              : 0.22
% 4.73/1.85  CNF conversion       : 0.04
% 4.73/1.85  Main loop            : 0.55
% 4.73/1.85  Inferencing          : 0.19
% 4.73/1.85  Reduction            : 0.18
% 4.73/1.85  Demodulation         : 0.13
% 4.73/1.85  BG Simplification    : 0.03
% 4.73/1.85  Subsumption          : 0.10
% 4.73/1.85  Abstraction          : 0.03
% 4.73/1.85  MUC search           : 0.00
% 4.73/1.85  Cooper               : 0.00
% 4.73/1.85  Total                : 1.03
% 4.73/1.85  Index Insertion      : 0.00
% 4.73/1.85  Index Deletion       : 0.00
% 4.73/1.85  Index Matching       : 0.00
% 4.73/1.85  BG Taut test         : 0.00
%------------------------------------------------------------------------------
