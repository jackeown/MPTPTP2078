%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:18:12 EST 2020

% Result     : Theorem 7.32s
% Output     : CNFRefutation 7.55s
% Verified   : 
% Statistics : Number of formulae       :  209 (1421 expanded)
%              Number of leaves         :   49 ( 519 expanded)
%              Depth                    :   22
%              Number of atoms          :  607 (6328 expanded)
%              Number of equality atoms :   94 ( 661 expanded)
%              Maximal formula depth    :   17 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k8_funct_2 > k3_funct_2 > k7_partfun1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(k3_funct_2,type,(
    k3_funct_2: ( $i * $i * $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_218,negated_conjecture,(
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

tff(f_76,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_191,axiom,(
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

tff(f_119,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => ( v1_partfun1(B,A)
      <=> k1_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_partfun1)).

tff(f_72,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_36,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(f_97,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & v1_xboole_0(B) )
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => ~ v1_partfun1(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_partfun1)).

tff(f_86,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( ( v1_funct_1(C)
          & v1_partfun1(C,A) )
       => ( v1_funct_1(C)
          & v1_funct_2(C,A,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_funct_2)).

tff(f_111,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => ( ( v1_funct_1(C)
              & v1_funct_2(C,A,B) )
           => ( v1_funct_1(C)
              & v1_partfun1(C,A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc5_funct_2)).

tff(f_62,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A)
        & v1_funct_1(B) )
     => ! [C] :
          ( r2_hidden(C,k1_relat_1(B))
         => r2_hidden(k1_funct_1(B,C),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t172_funct_1)).

tff(f_30,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

tff(f_167,axiom,(
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

tff(f_148,axiom,(
    ! [A,B,C,D] :
      ( ( ~ v1_xboole_0(A)
        & v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,A) )
     => k3_funct_2(A,B,C,D) = k1_funct_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k3_funct_2)).

tff(f_135,axiom,(
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

tff(c_56,plain,(
    m1_subset_1('#skF_6','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_218])).

tff(c_14,plain,(
    ! [A_10,B_11] : v1_relat_1(k2_zfmisc_1(A_10,B_11)) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_62,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_218])).

tff(c_78,plain,(
    ! [B_114,A_115] :
      ( v1_relat_1(B_114)
      | ~ m1_subset_1(B_114,k1_zfmisc_1(A_115))
      | ~ v1_relat_1(A_115) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_84,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_1')) ),
    inference(resolution,[status(thm)],[c_62,c_78])).

tff(c_90,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_84])).

tff(c_100,plain,(
    ! [C_119,B_120,A_121] :
      ( v5_relat_1(C_119,B_120)
      | ~ m1_subset_1(C_119,k1_zfmisc_1(k2_zfmisc_1(A_121,B_120))) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_108,plain,(
    v5_relat_1('#skF_4','#skF_1') ),
    inference(resolution,[status(thm)],[c_62,c_100])).

tff(c_12,plain,(
    ! [B_9,A_8] :
      ( r1_tarski(k2_relat_1(B_9),A_8)
      | ~ v5_relat_1(B_9,A_8)
      | ~ v1_relat_1(B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_68,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_218])).

tff(c_70,plain,(
    ~ v1_xboole_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_218])).

tff(c_66,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_218])).

tff(c_64,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_218])).

tff(c_289,plain,(
    ! [A_153,B_154,C_155] :
      ( k2_relset_1(A_153,B_154,C_155) = k2_relat_1(C_155)
      | ~ m1_subset_1(C_155,k1_zfmisc_1(k2_zfmisc_1(A_153,B_154))) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_297,plain,(
    k2_relset_1('#skF_2','#skF_1','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_62,c_289])).

tff(c_1593,plain,(
    ! [D_392,F_388,A_390,C_389,E_393,B_391] :
      ( k1_funct_1(k8_funct_2(B_391,C_389,A_390,D_392,E_393),F_388) = k1_funct_1(E_393,k1_funct_1(D_392,F_388))
      | k1_xboole_0 = B_391
      | ~ r1_tarski(k2_relset_1(B_391,C_389,D_392),k1_relset_1(C_389,A_390,E_393))
      | ~ m1_subset_1(F_388,B_391)
      | ~ m1_subset_1(E_393,k1_zfmisc_1(k2_zfmisc_1(C_389,A_390)))
      | ~ v1_funct_1(E_393)
      | ~ m1_subset_1(D_392,k1_zfmisc_1(k2_zfmisc_1(B_391,C_389)))
      | ~ v1_funct_2(D_392,B_391,C_389)
      | ~ v1_funct_1(D_392)
      | v1_xboole_0(C_389) ) ),
    inference(cnfTransformation,[status(thm)],[f_191])).

tff(c_1599,plain,(
    ! [A_390,E_393,F_388] :
      ( k1_funct_1(k8_funct_2('#skF_2','#skF_1',A_390,'#skF_4',E_393),F_388) = k1_funct_1(E_393,k1_funct_1('#skF_4',F_388))
      | k1_xboole_0 = '#skF_2'
      | ~ r1_tarski(k2_relat_1('#skF_4'),k1_relset_1('#skF_1',A_390,E_393))
      | ~ m1_subset_1(F_388,'#skF_2')
      | ~ m1_subset_1(E_393,k1_zfmisc_1(k2_zfmisc_1('#skF_1',A_390)))
      | ~ v1_funct_1(E_393)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
      | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
      | ~ v1_funct_1('#skF_4')
      | v1_xboole_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_297,c_1593])).

tff(c_1609,plain,(
    ! [A_390,E_393,F_388] :
      ( k1_funct_1(k8_funct_2('#skF_2','#skF_1',A_390,'#skF_4',E_393),F_388) = k1_funct_1(E_393,k1_funct_1('#skF_4',F_388))
      | k1_xboole_0 = '#skF_2'
      | ~ r1_tarski(k2_relat_1('#skF_4'),k1_relset_1('#skF_1',A_390,E_393))
      | ~ m1_subset_1(F_388,'#skF_2')
      | ~ m1_subset_1(E_393,k1_zfmisc_1(k2_zfmisc_1('#skF_1',A_390)))
      | ~ v1_funct_1(E_393)
      | v1_xboole_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_62,c_1599])).

tff(c_1610,plain,(
    ! [A_390,E_393,F_388] :
      ( k1_funct_1(k8_funct_2('#skF_2','#skF_1',A_390,'#skF_4',E_393),F_388) = k1_funct_1(E_393,k1_funct_1('#skF_4',F_388))
      | k1_xboole_0 = '#skF_2'
      | ~ r1_tarski(k2_relat_1('#skF_4'),k1_relset_1('#skF_1',A_390,E_393))
      | ~ m1_subset_1(F_388,'#skF_2')
      | ~ m1_subset_1(E_393,k1_zfmisc_1(k2_zfmisc_1('#skF_1',A_390)))
      | ~ v1_funct_1(E_393) ) ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_1609])).

tff(c_1745,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_1610])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_1747,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1745,c_2])).

tff(c_1749,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_1747])).

tff(c_1751,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(splitRight,[status(thm)],[c_1610])).

tff(c_60,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_218])).

tff(c_58,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_218])).

tff(c_81,plain,
    ( v1_relat_1('#skF_5')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_3')) ),
    inference(resolution,[status(thm)],[c_58,c_78])).

tff(c_87,plain,(
    v1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_81])).

tff(c_54,plain,(
    v1_partfun1('#skF_5','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_218])).

tff(c_91,plain,(
    ! [C_116,A_117,B_118] :
      ( v4_relat_1(C_116,A_117)
      | ~ m1_subset_1(C_116,k1_zfmisc_1(k2_zfmisc_1(A_117,B_118))) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_98,plain,(
    v4_relat_1('#skF_5','#skF_1') ),
    inference(resolution,[status(thm)],[c_58,c_91])).

tff(c_116,plain,(
    ! [B_127,A_128] :
      ( k1_relat_1(B_127) = A_128
      | ~ v1_partfun1(B_127,A_128)
      | ~ v4_relat_1(B_127,A_128)
      | ~ v1_relat_1(B_127) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_122,plain,
    ( k1_relat_1('#skF_5') = '#skF_1'
    | ~ v1_partfun1('#skF_5','#skF_1')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_98,c_116])).

tff(c_128,plain,(
    k1_relat_1('#skF_5') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_87,c_54,c_122])).

tff(c_306,plain,(
    ! [A_156,B_157,C_158] :
      ( k1_relset_1(A_156,B_157,C_158) = k1_relat_1(C_158)
      | ~ m1_subset_1(C_158,k1_zfmisc_1(k2_zfmisc_1(A_156,B_157))) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_309,plain,(
    k1_relset_1('#skF_1','#skF_3','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_58,c_306])).

tff(c_314,plain,(
    k1_relset_1('#skF_1','#skF_3','#skF_5') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_128,c_309])).

tff(c_1597,plain,(
    ! [B_391,D_392,F_388] :
      ( k1_funct_1(k8_funct_2(B_391,'#skF_1','#skF_3',D_392,'#skF_5'),F_388) = k1_funct_1('#skF_5',k1_funct_1(D_392,F_388))
      | k1_xboole_0 = B_391
      | ~ r1_tarski(k2_relset_1(B_391,'#skF_1',D_392),'#skF_1')
      | ~ m1_subset_1(F_388,B_391)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3')))
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1(D_392,k1_zfmisc_1(k2_zfmisc_1(B_391,'#skF_1')))
      | ~ v1_funct_2(D_392,B_391,'#skF_1')
      | ~ v1_funct_1(D_392)
      | v1_xboole_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_314,c_1593])).

tff(c_1606,plain,(
    ! [B_391,D_392,F_388] :
      ( k1_funct_1(k8_funct_2(B_391,'#skF_1','#skF_3',D_392,'#skF_5'),F_388) = k1_funct_1('#skF_5',k1_funct_1(D_392,F_388))
      | k1_xboole_0 = B_391
      | ~ r1_tarski(k2_relset_1(B_391,'#skF_1',D_392),'#skF_1')
      | ~ m1_subset_1(F_388,B_391)
      | ~ m1_subset_1(D_392,k1_zfmisc_1(k2_zfmisc_1(B_391,'#skF_1')))
      | ~ v1_funct_2(D_392,B_391,'#skF_1')
      | ~ v1_funct_1(D_392)
      | v1_xboole_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_1597])).

tff(c_1857,plain,(
    ! [B_414,D_415,F_416] :
      ( k1_funct_1(k8_funct_2(B_414,'#skF_1','#skF_3',D_415,'#skF_5'),F_416) = k1_funct_1('#skF_5',k1_funct_1(D_415,F_416))
      | k1_xboole_0 = B_414
      | ~ r1_tarski(k2_relset_1(B_414,'#skF_1',D_415),'#skF_1')
      | ~ m1_subset_1(F_416,B_414)
      | ~ m1_subset_1(D_415,k1_zfmisc_1(k2_zfmisc_1(B_414,'#skF_1')))
      | ~ v1_funct_2(D_415,B_414,'#skF_1')
      | ~ v1_funct_1(D_415) ) ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_1606])).

tff(c_1877,plain,(
    ! [F_416] :
      ( k1_funct_1(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),F_416) = k1_funct_1('#skF_5',k1_funct_1('#skF_4',F_416))
      | k1_xboole_0 = '#skF_2'
      | ~ r1_tarski(k2_relset_1('#skF_2','#skF_1','#skF_4'),'#skF_1')
      | ~ m1_subset_1(F_416,'#skF_2')
      | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_62,c_1857])).

tff(c_1886,plain,(
    ! [F_416] :
      ( k1_funct_1(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),F_416) = k1_funct_1('#skF_5',k1_funct_1('#skF_4',F_416))
      | k1_xboole_0 = '#skF_2'
      | ~ r1_tarski(k2_relat_1('#skF_4'),'#skF_1')
      | ~ m1_subset_1(F_416,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_297,c_1877])).

tff(c_1887,plain,(
    ! [F_416] :
      ( k1_funct_1(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),F_416) = k1_funct_1('#skF_5',k1_funct_1('#skF_4',F_416))
      | ~ r1_tarski(k2_relat_1('#skF_4'),'#skF_1')
      | ~ m1_subset_1(F_416,'#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_1751,c_1886])).

tff(c_1888,plain,(
    ~ r1_tarski(k2_relat_1('#skF_4'),'#skF_1') ),
    inference(splitLeft,[status(thm)],[c_1887])).

tff(c_1891,plain,
    ( ~ v5_relat_1('#skF_4','#skF_1')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_12,c_1888])).

tff(c_1895,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_108,c_1891])).

tff(c_1896,plain,(
    ! [F_416] :
      ( k1_funct_1(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),F_416) = k1_funct_1('#skF_5',k1_funct_1('#skF_4',F_416))
      | ~ m1_subset_1(F_416,'#skF_2') ) ),
    inference(splitRight,[status(thm)],[c_1887])).

tff(c_6,plain,(
    ! [A_3,B_4] :
      ( r2_hidden(A_3,B_4)
      | v1_xboole_0(B_4)
      | ~ m1_subset_1(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_325,plain,(
    ! [C_159,A_160,B_161] :
      ( ~ v1_partfun1(C_159,A_160)
      | ~ m1_subset_1(C_159,k1_zfmisc_1(k2_zfmisc_1(A_160,B_161)))
      | ~ v1_xboole_0(B_161)
      | v1_xboole_0(A_160) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_328,plain,
    ( ~ v1_partfun1('#skF_5','#skF_1')
    | ~ v1_xboole_0('#skF_3')
    | v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_58,c_325])).

tff(c_334,plain,
    ( ~ v1_xboole_0('#skF_3')
    | v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_328])).

tff(c_335,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_334])).

tff(c_340,plain,(
    ! [C_162,A_163,B_164] :
      ( v1_funct_2(C_162,A_163,B_164)
      | ~ v1_partfun1(C_162,A_163)
      | ~ v1_funct_1(C_162)
      | ~ m1_subset_1(C_162,k1_zfmisc_1(k2_zfmisc_1(A_163,B_164))) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_343,plain,
    ( v1_funct_2('#skF_5','#skF_1','#skF_3')
    | ~ v1_partfun1('#skF_5','#skF_1')
    | ~ v1_funct_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_58,c_340])).

tff(c_349,plain,(
    v1_funct_2('#skF_5','#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_54,c_343])).

tff(c_99,plain,(
    v4_relat_1('#skF_4','#skF_2') ),
    inference(resolution,[status(thm)],[c_62,c_91])).

tff(c_119,plain,
    ( k1_relat_1('#skF_4') = '#skF_2'
    | ~ v1_partfun1('#skF_4','#skF_2')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_99,c_116])).

tff(c_125,plain,
    ( k1_relat_1('#skF_4') = '#skF_2'
    | ~ v1_partfun1('#skF_4','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_119])).

tff(c_138,plain,(
    ~ v1_partfun1('#skF_4','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_125])).

tff(c_256,plain,(
    ! [C_150,A_151,B_152] :
      ( v1_partfun1(C_150,A_151)
      | ~ v1_funct_2(C_150,A_151,B_152)
      | ~ v1_funct_1(C_150)
      | ~ m1_subset_1(C_150,k1_zfmisc_1(k2_zfmisc_1(A_151,B_152)))
      | v1_xboole_0(B_152) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_266,plain,
    ( v1_partfun1('#skF_4','#skF_2')
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4')
    | v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_62,c_256])).

tff(c_274,plain,
    ( v1_partfun1('#skF_4','#skF_2')
    | v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_266])).

tff(c_276,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_138,c_274])).

tff(c_277,plain,(
    k1_relat_1('#skF_4') = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_125])).

tff(c_353,plain,(
    ! [B_165,C_166,A_167] :
      ( r2_hidden(k1_funct_1(B_165,C_166),A_167)
      | ~ r2_hidden(C_166,k1_relat_1(B_165))
      | ~ v1_funct_1(B_165)
      | ~ v5_relat_1(B_165,A_167)
      | ~ v1_relat_1(B_165) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( m1_subset_1(A_1,B_2)
      | ~ r2_hidden(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_358,plain,(
    ! [B_168,C_169,A_170] :
      ( m1_subset_1(k1_funct_1(B_168,C_169),A_170)
      | ~ r2_hidden(C_169,k1_relat_1(B_168))
      | ~ v1_funct_1(B_168)
      | ~ v5_relat_1(B_168,A_170)
      | ~ v1_relat_1(B_168) ) ),
    inference(resolution,[status(thm)],[c_353,c_4])).

tff(c_363,plain,(
    ! [C_169,A_170] :
      ( m1_subset_1(k1_funct_1('#skF_4',C_169),A_170)
      | ~ r2_hidden(C_169,'#skF_2')
      | ~ v1_funct_1('#skF_4')
      | ~ v5_relat_1('#skF_4',A_170)
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_277,c_358])).

tff(c_371,plain,(
    ! [C_169,A_170] :
      ( m1_subset_1(k1_funct_1('#skF_4',C_169),A_170)
      | ~ r2_hidden(C_169,'#skF_2')
      | ~ v5_relat_1('#skF_4',A_170) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_66,c_363])).

tff(c_705,plain,(
    ! [A_249,B_250,C_251,D_252] :
      ( k3_funct_2(A_249,B_250,C_251,D_252) = k7_partfun1(B_250,C_251,D_252)
      | ~ m1_subset_1(D_252,A_249)
      | ~ m1_subset_1(C_251,k1_zfmisc_1(k2_zfmisc_1(A_249,B_250)))
      | ~ v1_funct_2(C_251,A_249,B_250)
      | ~ v1_funct_1(C_251)
      | v1_xboole_0(B_250)
      | v1_xboole_0(A_249) ) ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_3870,plain,(
    ! [A_729,B_730,C_731,C_732] :
      ( k3_funct_2(A_729,B_730,C_731,k1_funct_1('#skF_4',C_732)) = k7_partfun1(B_730,C_731,k1_funct_1('#skF_4',C_732))
      | ~ m1_subset_1(C_731,k1_zfmisc_1(k2_zfmisc_1(A_729,B_730)))
      | ~ v1_funct_2(C_731,A_729,B_730)
      | ~ v1_funct_1(C_731)
      | v1_xboole_0(B_730)
      | v1_xboole_0(A_729)
      | ~ r2_hidden(C_732,'#skF_2')
      | ~ v5_relat_1('#skF_4',A_729) ) ),
    inference(resolution,[status(thm)],[c_371,c_705])).

tff(c_3897,plain,(
    ! [C_732] :
      ( k3_funct_2('#skF_1','#skF_3','#skF_5',k1_funct_1('#skF_4',C_732)) = k7_partfun1('#skF_3','#skF_5',k1_funct_1('#skF_4',C_732))
      | ~ v1_funct_2('#skF_5','#skF_1','#skF_3')
      | ~ v1_funct_1('#skF_5')
      | v1_xboole_0('#skF_3')
      | v1_xboole_0('#skF_1')
      | ~ r2_hidden(C_732,'#skF_2')
      | ~ v5_relat_1('#skF_4','#skF_1') ) ),
    inference(resolution,[status(thm)],[c_58,c_3870])).

tff(c_3914,plain,(
    ! [C_732] :
      ( k3_funct_2('#skF_1','#skF_3','#skF_5',k1_funct_1('#skF_4',C_732)) = k7_partfun1('#skF_3','#skF_5',k1_funct_1('#skF_4',C_732))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0('#skF_1')
      | ~ r2_hidden(C_732,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_108,c_60,c_349,c_3897])).

tff(c_3920,plain,(
    ! [C_733] :
      ( k3_funct_2('#skF_1','#skF_3','#skF_5',k1_funct_1('#skF_4',C_733)) = k7_partfun1('#skF_3','#skF_5',k1_funct_1('#skF_4',C_733))
      | ~ r2_hidden(C_733,'#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_335,c_3914])).

tff(c_523,plain,(
    ! [A_201,B_202,C_203,D_204] :
      ( k3_funct_2(A_201,B_202,C_203,D_204) = k1_funct_1(C_203,D_204)
      | ~ m1_subset_1(D_204,A_201)
      | ~ m1_subset_1(C_203,k1_zfmisc_1(k2_zfmisc_1(A_201,B_202)))
      | ~ v1_funct_2(C_203,A_201,B_202)
      | ~ v1_funct_1(C_203)
      | v1_xboole_0(A_201) ) ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_2985,plain,(
    ! [A_567,B_568,C_569,C_570] :
      ( k3_funct_2(A_567,B_568,C_569,k1_funct_1('#skF_4',C_570)) = k1_funct_1(C_569,k1_funct_1('#skF_4',C_570))
      | ~ m1_subset_1(C_569,k1_zfmisc_1(k2_zfmisc_1(A_567,B_568)))
      | ~ v1_funct_2(C_569,A_567,B_568)
      | ~ v1_funct_1(C_569)
      | v1_xboole_0(A_567)
      | ~ r2_hidden(C_570,'#skF_2')
      | ~ v5_relat_1('#skF_4',A_567) ) ),
    inference(resolution,[status(thm)],[c_371,c_523])).

tff(c_3012,plain,(
    ! [C_570] :
      ( k3_funct_2('#skF_1','#skF_3','#skF_5',k1_funct_1('#skF_4',C_570)) = k1_funct_1('#skF_5',k1_funct_1('#skF_4',C_570))
      | ~ v1_funct_2('#skF_5','#skF_1','#skF_3')
      | ~ v1_funct_1('#skF_5')
      | v1_xboole_0('#skF_1')
      | ~ r2_hidden(C_570,'#skF_2')
      | ~ v5_relat_1('#skF_4','#skF_1') ) ),
    inference(resolution,[status(thm)],[c_58,c_2985])).

tff(c_3029,plain,(
    ! [C_570] :
      ( k3_funct_2('#skF_1','#skF_3','#skF_5',k1_funct_1('#skF_4',C_570)) = k1_funct_1('#skF_5',k1_funct_1('#skF_4',C_570))
      | v1_xboole_0('#skF_1')
      | ~ r2_hidden(C_570,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_108,c_60,c_349,c_3012])).

tff(c_3030,plain,(
    ! [C_570] :
      ( k3_funct_2('#skF_1','#skF_3','#skF_5',k1_funct_1('#skF_4',C_570)) = k1_funct_1('#skF_5',k1_funct_1('#skF_4',C_570))
      | ~ r2_hidden(C_570,'#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_3029])).

tff(c_3942,plain,(
    ! [C_738] :
      ( k7_partfun1('#skF_3','#skF_5',k1_funct_1('#skF_4',C_738)) = k1_funct_1('#skF_5',k1_funct_1('#skF_4',C_738))
      | ~ r2_hidden(C_738,'#skF_2')
      | ~ r2_hidden(C_738,'#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3920,c_3030])).

tff(c_577,plain,(
    ! [E_228,B_227,C_229,D_230,A_226] :
      ( v1_funct_1(k8_funct_2(A_226,B_227,C_229,D_230,E_228))
      | ~ m1_subset_1(E_228,k1_zfmisc_1(k2_zfmisc_1(B_227,C_229)))
      | ~ v1_funct_1(E_228)
      | ~ m1_subset_1(D_230,k1_zfmisc_1(k2_zfmisc_1(A_226,B_227)))
      | ~ v1_funct_2(D_230,A_226,B_227)
      | ~ v1_funct_1(D_230) ) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_588,plain,(
    ! [A_226,D_230] :
      ( v1_funct_1(k8_funct_2(A_226,'#skF_1','#skF_3',D_230,'#skF_5'))
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1(D_230,k1_zfmisc_1(k2_zfmisc_1(A_226,'#skF_1')))
      | ~ v1_funct_2(D_230,A_226,'#skF_1')
      | ~ v1_funct_1(D_230) ) ),
    inference(resolution,[status(thm)],[c_58,c_577])).

tff(c_600,plain,(
    ! [A_231,D_232] :
      ( v1_funct_1(k8_funct_2(A_231,'#skF_1','#skF_3',D_232,'#skF_5'))
      | ~ m1_subset_1(D_232,k1_zfmisc_1(k2_zfmisc_1(A_231,'#skF_1')))
      | ~ v1_funct_2(D_232,A_231,'#skF_1')
      | ~ v1_funct_1(D_232) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_588])).

tff(c_615,plain,
    ( v1_funct_1(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_62,c_600])).

tff(c_621,plain,(
    v1_funct_1(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_615])).

tff(c_768,plain,(
    ! [B_274,E_275,A_273,D_277,C_276] :
      ( v1_funct_2(k8_funct_2(A_273,B_274,C_276,D_277,E_275),A_273,C_276)
      | ~ m1_subset_1(E_275,k1_zfmisc_1(k2_zfmisc_1(B_274,C_276)))
      | ~ v1_funct_1(E_275)
      | ~ m1_subset_1(D_277,k1_zfmisc_1(k2_zfmisc_1(A_273,B_274)))
      | ~ v1_funct_2(D_277,A_273,B_274)
      | ~ v1_funct_1(D_277) ) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_782,plain,(
    ! [A_273,D_277] :
      ( v1_funct_2(k8_funct_2(A_273,'#skF_1','#skF_3',D_277,'#skF_5'),A_273,'#skF_3')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1(D_277,k1_zfmisc_1(k2_zfmisc_1(A_273,'#skF_1')))
      | ~ v1_funct_2(D_277,A_273,'#skF_1')
      | ~ v1_funct_1(D_277) ) ),
    inference(resolution,[status(thm)],[c_58,c_768])).

tff(c_795,plain,(
    ! [A_278,D_279] :
      ( v1_funct_2(k8_funct_2(A_278,'#skF_1','#skF_3',D_279,'#skF_5'),A_278,'#skF_3')
      | ~ m1_subset_1(D_279,k1_zfmisc_1(k2_zfmisc_1(A_278,'#skF_1')))
      | ~ v1_funct_2(D_279,A_278,'#skF_1')
      | ~ v1_funct_1(D_279) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_782])).

tff(c_809,plain,
    ( v1_funct_2(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),'#skF_2','#skF_3')
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_62,c_795])).

tff(c_816,plain,(
    v1_funct_2(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),'#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_809])).

tff(c_40,plain,(
    ! [D_41,B_39,A_38,E_42,C_40] :
      ( m1_subset_1(k8_funct_2(A_38,B_39,C_40,D_41,E_42),k1_zfmisc_1(k2_zfmisc_1(A_38,C_40)))
      | ~ m1_subset_1(E_42,k1_zfmisc_1(k2_zfmisc_1(B_39,C_40)))
      | ~ v1_funct_1(E_42)
      | ~ m1_subset_1(D_41,k1_zfmisc_1(k2_zfmisc_1(A_38,B_39)))
      | ~ v1_funct_2(D_41,A_38,B_39)
      | ~ v1_funct_1(D_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_840,plain,(
    ! [E_296,C_297,A_294,D_298,B_295] :
      ( m1_subset_1(k8_funct_2(A_294,B_295,C_297,D_298,E_296),k1_zfmisc_1(k2_zfmisc_1(A_294,C_297)))
      | ~ m1_subset_1(E_296,k1_zfmisc_1(k2_zfmisc_1(B_295,C_297)))
      | ~ v1_funct_1(E_296)
      | ~ m1_subset_1(D_298,k1_zfmisc_1(k2_zfmisc_1(A_294,B_295)))
      | ~ v1_funct_2(D_298,A_294,B_295)
      | ~ v1_funct_1(D_298) ) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_8,plain,(
    ! [B_7,A_5] :
      ( v1_relat_1(B_7)
      | ~ m1_subset_1(B_7,k1_zfmisc_1(A_5))
      | ~ v1_relat_1(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_894,plain,(
    ! [E_296,C_297,A_294,D_298,B_295] :
      ( v1_relat_1(k8_funct_2(A_294,B_295,C_297,D_298,E_296))
      | ~ v1_relat_1(k2_zfmisc_1(A_294,C_297))
      | ~ m1_subset_1(E_296,k1_zfmisc_1(k2_zfmisc_1(B_295,C_297)))
      | ~ v1_funct_1(E_296)
      | ~ m1_subset_1(D_298,k1_zfmisc_1(k2_zfmisc_1(A_294,B_295)))
      | ~ v1_funct_2(D_298,A_294,B_295)
      | ~ v1_funct_1(D_298) ) ),
    inference(resolution,[status(thm)],[c_840,c_8])).

tff(c_915,plain,(
    ! [B_301,D_299,C_303,E_300,A_302] :
      ( v1_relat_1(k8_funct_2(A_302,B_301,C_303,D_299,E_300))
      | ~ m1_subset_1(E_300,k1_zfmisc_1(k2_zfmisc_1(B_301,C_303)))
      | ~ v1_funct_1(E_300)
      | ~ m1_subset_1(D_299,k1_zfmisc_1(k2_zfmisc_1(A_302,B_301)))
      | ~ v1_funct_2(D_299,A_302,B_301)
      | ~ v1_funct_1(D_299) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_894])).

tff(c_931,plain,(
    ! [A_302,D_299] :
      ( v1_relat_1(k8_funct_2(A_302,'#skF_1','#skF_3',D_299,'#skF_5'))
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1(D_299,k1_zfmisc_1(k2_zfmisc_1(A_302,'#skF_1')))
      | ~ v1_funct_2(D_299,A_302,'#skF_1')
      | ~ v1_funct_1(D_299) ) ),
    inference(resolution,[status(thm)],[c_58,c_915])).

tff(c_945,plain,(
    ! [A_304,D_305] :
      ( v1_relat_1(k8_funct_2(A_304,'#skF_1','#skF_3',D_305,'#skF_5'))
      | ~ m1_subset_1(D_305,k1_zfmisc_1(k2_zfmisc_1(A_304,'#skF_1')))
      | ~ v1_funct_2(D_305,A_304,'#skF_1')
      | ~ v1_funct_1(D_305) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_931])).

tff(c_968,plain,
    ( v1_relat_1(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_62,c_945])).

tff(c_976,plain,(
    v1_relat_1(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_968])).

tff(c_20,plain,(
    ! [C_18,A_16,B_17] :
      ( v4_relat_1(C_18,A_16)
      | ~ m1_subset_1(C_18,k1_zfmisc_1(k2_zfmisc_1(A_16,B_17))) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_1003,plain,(
    ! [C_312,E_309,D_308,B_310,A_311] :
      ( v4_relat_1(k8_funct_2(A_311,B_310,C_312,D_308,E_309),A_311)
      | ~ m1_subset_1(E_309,k1_zfmisc_1(k2_zfmisc_1(B_310,C_312)))
      | ~ v1_funct_1(E_309)
      | ~ m1_subset_1(D_308,k1_zfmisc_1(k2_zfmisc_1(A_311,B_310)))
      | ~ v1_funct_2(D_308,A_311,B_310)
      | ~ v1_funct_1(D_308) ) ),
    inference(resolution,[status(thm)],[c_840,c_20])).

tff(c_1019,plain,(
    ! [A_311,D_308] :
      ( v4_relat_1(k8_funct_2(A_311,'#skF_1','#skF_3',D_308,'#skF_5'),A_311)
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1(D_308,k1_zfmisc_1(k2_zfmisc_1(A_311,'#skF_1')))
      | ~ v1_funct_2(D_308,A_311,'#skF_1')
      | ~ v1_funct_1(D_308) ) ),
    inference(resolution,[status(thm)],[c_58,c_1003])).

tff(c_1033,plain,(
    ! [A_313,D_314] :
      ( v4_relat_1(k8_funct_2(A_313,'#skF_1','#skF_3',D_314,'#skF_5'),A_313)
      | ~ m1_subset_1(D_314,k1_zfmisc_1(k2_zfmisc_1(A_313,'#skF_1')))
      | ~ v1_funct_2(D_314,A_313,'#skF_1')
      | ~ v1_funct_1(D_314) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_1019])).

tff(c_1050,plain,
    ( v4_relat_1(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),'#skF_2')
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_62,c_1033])).

tff(c_1058,plain,(
    v4_relat_1(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_1050])).

tff(c_38,plain,(
    ! [B_37,A_36] :
      ( k1_relat_1(B_37) = A_36
      | ~ v1_partfun1(B_37,A_36)
      | ~ v4_relat_1(B_37,A_36)
      | ~ v1_relat_1(B_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_1061,plain,
    ( k1_relat_1(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5')) = '#skF_2'
    | ~ v1_partfun1(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),'#skF_2')
    | ~ v1_relat_1(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_1058,c_38])).

tff(c_1064,plain,
    ( k1_relat_1(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5')) = '#skF_2'
    | ~ v1_partfun1(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_976,c_1061])).

tff(c_1065,plain,(
    ~ v1_partfun1(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_1064])).

tff(c_22,plain,(
    ! [A_19,B_20,C_21] :
      ( k1_relset_1(A_19,B_20,C_21) = k1_relat_1(C_21)
      | ~ m1_subset_1(C_21,k1_zfmisc_1(k2_zfmisc_1(A_19,B_20))) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_1406,plain,(
    ! [D_379,B_381,C_383,E_380,A_382] :
      ( k1_relset_1(A_382,C_383,k8_funct_2(A_382,B_381,C_383,D_379,E_380)) = k1_relat_1(k8_funct_2(A_382,B_381,C_383,D_379,E_380))
      | ~ m1_subset_1(E_380,k1_zfmisc_1(k2_zfmisc_1(B_381,C_383)))
      | ~ v1_funct_1(E_380)
      | ~ m1_subset_1(D_379,k1_zfmisc_1(k2_zfmisc_1(A_382,B_381)))
      | ~ v1_funct_2(D_379,A_382,B_381)
      | ~ v1_funct_1(D_379) ) ),
    inference(resolution,[status(thm)],[c_840,c_22])).

tff(c_1422,plain,(
    ! [A_382,D_379] :
      ( k1_relset_1(A_382,'#skF_3',k8_funct_2(A_382,'#skF_1','#skF_3',D_379,'#skF_5')) = k1_relat_1(k8_funct_2(A_382,'#skF_1','#skF_3',D_379,'#skF_5'))
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1(D_379,k1_zfmisc_1(k2_zfmisc_1(A_382,'#skF_1')))
      | ~ v1_funct_2(D_379,A_382,'#skF_1')
      | ~ v1_funct_1(D_379) ) ),
    inference(resolution,[status(thm)],[c_58,c_1406])).

tff(c_1449,plain,(
    ! [A_386,D_387] :
      ( k1_relset_1(A_386,'#skF_3',k8_funct_2(A_386,'#skF_1','#skF_3',D_387,'#skF_5')) = k1_relat_1(k8_funct_2(A_386,'#skF_1','#skF_3',D_387,'#skF_5'))
      | ~ m1_subset_1(D_387,k1_zfmisc_1(k2_zfmisc_1(A_386,'#skF_1')))
      | ~ v1_funct_2(D_387,A_386,'#skF_1')
      | ~ v1_funct_1(D_387) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_1422])).

tff(c_1466,plain,
    ( k1_relset_1('#skF_2','#skF_3',k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5')) = k1_relat_1(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_62,c_1449])).

tff(c_1474,plain,(
    k1_relset_1('#skF_2','#skF_3',k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5')) = k1_relat_1(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_1466])).

tff(c_50,plain,(
    ! [B_63,E_76,F_78,C_64,D_72,A_62] :
      ( k1_funct_1(k8_funct_2(B_63,C_64,A_62,D_72,E_76),F_78) = k1_funct_1(E_76,k1_funct_1(D_72,F_78))
      | k1_xboole_0 = B_63
      | ~ r1_tarski(k2_relset_1(B_63,C_64,D_72),k1_relset_1(C_64,A_62,E_76))
      | ~ m1_subset_1(F_78,B_63)
      | ~ m1_subset_1(E_76,k1_zfmisc_1(k2_zfmisc_1(C_64,A_62)))
      | ~ v1_funct_1(E_76)
      | ~ m1_subset_1(D_72,k1_zfmisc_1(k2_zfmisc_1(B_63,C_64)))
      | ~ v1_funct_2(D_72,B_63,C_64)
      | ~ v1_funct_1(D_72)
      | v1_xboole_0(C_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_191])).

tff(c_1477,plain,(
    ! [B_63,D_72,F_78] :
      ( k1_funct_1(k8_funct_2(B_63,'#skF_2','#skF_3',D_72,k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5')),F_78) = k1_funct_1(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),k1_funct_1(D_72,F_78))
      | k1_xboole_0 = B_63
      | ~ r1_tarski(k2_relset_1(B_63,'#skF_2',D_72),k1_relat_1(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5')))
      | ~ m1_subset_1(F_78,B_63)
      | ~ m1_subset_1(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
      | ~ v1_funct_1(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'))
      | ~ m1_subset_1(D_72,k1_zfmisc_1(k2_zfmisc_1(B_63,'#skF_2')))
      | ~ v1_funct_2(D_72,B_63,'#skF_2')
      | ~ v1_funct_1(D_72)
      | v1_xboole_0('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1474,c_50])).

tff(c_1481,plain,(
    ! [B_63,D_72,F_78] :
      ( k1_funct_1(k8_funct_2(B_63,'#skF_2','#skF_3',D_72,k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5')),F_78) = k1_funct_1(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),k1_funct_1(D_72,F_78))
      | k1_xboole_0 = B_63
      | ~ r1_tarski(k2_relset_1(B_63,'#skF_2',D_72),k1_relat_1(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5')))
      | ~ m1_subset_1(F_78,B_63)
      | ~ m1_subset_1(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
      | ~ m1_subset_1(D_72,k1_zfmisc_1(k2_zfmisc_1(B_63,'#skF_2')))
      | ~ v1_funct_2(D_72,B_63,'#skF_2')
      | ~ v1_funct_1(D_72)
      | v1_xboole_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_621,c_1477])).

tff(c_1482,plain,(
    ! [B_63,D_72,F_78] :
      ( k1_funct_1(k8_funct_2(B_63,'#skF_2','#skF_3',D_72,k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5')),F_78) = k1_funct_1(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),k1_funct_1(D_72,F_78))
      | k1_xboole_0 = B_63
      | ~ r1_tarski(k2_relset_1(B_63,'#skF_2',D_72),k1_relat_1(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5')))
      | ~ m1_subset_1(F_78,B_63)
      | ~ m1_subset_1(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
      | ~ m1_subset_1(D_72,k1_zfmisc_1(k2_zfmisc_1(B_63,'#skF_2')))
      | ~ v1_funct_2(D_72,B_63,'#skF_2')
      | ~ v1_funct_1(D_72) ) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_1481])).

tff(c_1484,plain,(
    ~ m1_subset_1(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_1482])).

tff(c_1487,plain,
    ( ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3')))
    | ~ v1_funct_1('#skF_5')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_40,c_1484])).

tff(c_1491,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_62,c_60,c_58,c_1487])).

tff(c_1493,plain,(
    m1_subset_1(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_1482])).

tff(c_32,plain,(
    ! [C_35,A_32,B_33] :
      ( v1_partfun1(C_35,A_32)
      | ~ v1_funct_2(C_35,A_32,B_33)
      | ~ v1_funct_1(C_35)
      | ~ m1_subset_1(C_35,k1_zfmisc_1(k2_zfmisc_1(A_32,B_33)))
      | v1_xboole_0(B_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_1520,plain,
    ( v1_partfun1(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),'#skF_2')
    | ~ v1_funct_2(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),'#skF_2','#skF_3')
    | ~ v1_funct_1(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'))
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_1493,c_32])).

tff(c_1574,plain,
    ( v1_partfun1(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),'#skF_2')
    | v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_621,c_816,c_1520])).

tff(c_1576,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_335,c_1065,c_1574])).

tff(c_1577,plain,(
    k1_relat_1(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5')) = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_1064])).

tff(c_2238,plain,(
    ! [D_470,B_472,E_471,C_474,A_473] :
      ( k1_relset_1(A_473,C_474,k8_funct_2(A_473,B_472,C_474,D_470,E_471)) = k1_relat_1(k8_funct_2(A_473,B_472,C_474,D_470,E_471))
      | ~ m1_subset_1(E_471,k1_zfmisc_1(k2_zfmisc_1(B_472,C_474)))
      | ~ v1_funct_1(E_471)
      | ~ m1_subset_1(D_470,k1_zfmisc_1(k2_zfmisc_1(A_473,B_472)))
      | ~ v1_funct_2(D_470,A_473,B_472)
      | ~ v1_funct_1(D_470) ) ),
    inference(resolution,[status(thm)],[c_840,c_22])).

tff(c_2260,plain,(
    ! [A_473,D_470] :
      ( k1_relset_1(A_473,'#skF_3',k8_funct_2(A_473,'#skF_1','#skF_3',D_470,'#skF_5')) = k1_relat_1(k8_funct_2(A_473,'#skF_1','#skF_3',D_470,'#skF_5'))
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1(D_470,k1_zfmisc_1(k2_zfmisc_1(A_473,'#skF_1')))
      | ~ v1_funct_2(D_470,A_473,'#skF_1')
      | ~ v1_funct_1(D_470) ) ),
    inference(resolution,[status(thm)],[c_58,c_2238])).

tff(c_2276,plain,(
    ! [A_475,D_476] :
      ( k1_relset_1(A_475,'#skF_3',k8_funct_2(A_475,'#skF_1','#skF_3',D_476,'#skF_5')) = k1_relat_1(k8_funct_2(A_475,'#skF_1','#skF_3',D_476,'#skF_5'))
      | ~ m1_subset_1(D_476,k1_zfmisc_1(k2_zfmisc_1(A_475,'#skF_1')))
      | ~ v1_funct_2(D_476,A_475,'#skF_1')
      | ~ v1_funct_1(D_476) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_2260])).

tff(c_2299,plain,
    ( k1_relset_1('#skF_2','#skF_3',k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5')) = k1_relat_1(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_62,c_2276])).

tff(c_2309,plain,(
    k1_relset_1('#skF_2','#skF_3',k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_1577,c_2299])).

tff(c_2312,plain,(
    ! [B_63,D_72,F_78] :
      ( k1_funct_1(k8_funct_2(B_63,'#skF_2','#skF_3',D_72,k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5')),F_78) = k1_funct_1(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),k1_funct_1(D_72,F_78))
      | k1_xboole_0 = B_63
      | ~ r1_tarski(k2_relset_1(B_63,'#skF_2',D_72),'#skF_2')
      | ~ m1_subset_1(F_78,B_63)
      | ~ m1_subset_1(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
      | ~ v1_funct_1(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'))
      | ~ m1_subset_1(D_72,k1_zfmisc_1(k2_zfmisc_1(B_63,'#skF_2')))
      | ~ v1_funct_2(D_72,B_63,'#skF_2')
      | ~ v1_funct_1(D_72)
      | v1_xboole_0('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2309,c_50])).

tff(c_2316,plain,(
    ! [B_63,D_72,F_78] :
      ( k1_funct_1(k8_funct_2(B_63,'#skF_2','#skF_3',D_72,k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5')),F_78) = k1_funct_1(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),k1_funct_1(D_72,F_78))
      | k1_xboole_0 = B_63
      | ~ r1_tarski(k2_relset_1(B_63,'#skF_2',D_72),'#skF_2')
      | ~ m1_subset_1(F_78,B_63)
      | ~ m1_subset_1(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
      | ~ m1_subset_1(D_72,k1_zfmisc_1(k2_zfmisc_1(B_63,'#skF_2')))
      | ~ v1_funct_2(D_72,B_63,'#skF_2')
      | ~ v1_funct_1(D_72)
      | v1_xboole_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_621,c_2312])).

tff(c_2317,plain,(
    ! [B_63,D_72,F_78] :
      ( k1_funct_1(k8_funct_2(B_63,'#skF_2','#skF_3',D_72,k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5')),F_78) = k1_funct_1(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),k1_funct_1(D_72,F_78))
      | k1_xboole_0 = B_63
      | ~ r1_tarski(k2_relset_1(B_63,'#skF_2',D_72),'#skF_2')
      | ~ m1_subset_1(F_78,B_63)
      | ~ m1_subset_1(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
      | ~ m1_subset_1(D_72,k1_zfmisc_1(k2_zfmisc_1(B_63,'#skF_2')))
      | ~ v1_funct_2(D_72,B_63,'#skF_2')
      | ~ v1_funct_1(D_72) ) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_2316])).

tff(c_2348,plain,(
    ~ m1_subset_1(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_2317])).

tff(c_2351,plain,
    ( ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3')))
    | ~ v1_funct_1('#skF_5')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_40,c_2348])).

tff(c_2355,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_62,c_60,c_58,c_2351])).

tff(c_2357,plain,(
    m1_subset_1(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_2317])).

tff(c_535,plain,(
    ! [B_202,C_203] :
      ( k3_funct_2('#skF_2',B_202,C_203,'#skF_6') = k1_funct_1(C_203,'#skF_6')
      | ~ m1_subset_1(C_203,k1_zfmisc_1(k2_zfmisc_1('#skF_2',B_202)))
      | ~ v1_funct_2(C_203,'#skF_2',B_202)
      | ~ v1_funct_1(C_203)
      | v1_xboole_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_56,c_523])).

tff(c_543,plain,(
    ! [B_202,C_203] :
      ( k3_funct_2('#skF_2',B_202,C_203,'#skF_6') = k1_funct_1(C_203,'#skF_6')
      | ~ m1_subset_1(C_203,k1_zfmisc_1(k2_zfmisc_1('#skF_2',B_202)))
      | ~ v1_funct_2(C_203,'#skF_2',B_202)
      | ~ v1_funct_1(C_203) ) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_535])).

tff(c_2379,plain,
    ( k3_funct_2('#skF_2','#skF_3',k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),'#skF_6') = k1_funct_1(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),'#skF_6')
    | ~ v1_funct_2(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),'#skF_2','#skF_3')
    | ~ v1_funct_1(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_2357,c_543])).

tff(c_2434,plain,(
    k3_funct_2('#skF_2','#skF_3',k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),'#skF_6') = k1_funct_1(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_621,c_816,c_2379])).

tff(c_547,plain,(
    ! [B_214,C_215] :
      ( k3_funct_2('#skF_2',B_214,C_215,'#skF_6') = k1_funct_1(C_215,'#skF_6')
      | ~ m1_subset_1(C_215,k1_zfmisc_1(k2_zfmisc_1('#skF_2',B_214)))
      | ~ v1_funct_2(C_215,'#skF_2',B_214)
      | ~ v1_funct_1(C_215) ) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_535])).

tff(c_562,plain,
    ( k3_funct_2('#skF_2','#skF_1','#skF_4','#skF_6') = k1_funct_1('#skF_4','#skF_6')
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_62,c_547])).

tff(c_568,plain,(
    k3_funct_2('#skF_2','#skF_1','#skF_4','#skF_6') = k1_funct_1('#skF_4','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_562])).

tff(c_52,plain,(
    k3_funct_2('#skF_2','#skF_3',k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),'#skF_6') != k7_partfun1('#skF_3','#skF_5',k3_funct_2('#skF_2','#skF_1','#skF_4','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_218])).

tff(c_569,plain,(
    k3_funct_2('#skF_2','#skF_3',k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),'#skF_6') != k7_partfun1('#skF_3','#skF_5',k1_funct_1('#skF_4','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_568,c_52])).

tff(c_2458,plain,(
    k7_partfun1('#skF_3','#skF_5',k1_funct_1('#skF_4','#skF_6')) != k1_funct_1(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2434,c_569])).

tff(c_3948,plain,
    ( k1_funct_1(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),'#skF_6') != k1_funct_1('#skF_5',k1_funct_1('#skF_4','#skF_6'))
    | ~ r2_hidden('#skF_6','#skF_2')
    | ~ r2_hidden('#skF_6','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_3942,c_2458])).

tff(c_3954,plain,(
    ~ r2_hidden('#skF_6','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_3948])).

tff(c_3962,plain,
    ( v1_xboole_0('#skF_2')
    | ~ m1_subset_1('#skF_6','#skF_2') ),
    inference(resolution,[status(thm)],[c_6,c_3954])).

tff(c_3965,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_3962])).

tff(c_3967,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_3965])).

tff(c_3969,plain,(
    r2_hidden('#skF_6','#skF_2') ),
    inference(splitRight,[status(thm)],[c_3948])).

tff(c_3968,plain,
    ( ~ r2_hidden('#skF_6','#skF_2')
    | k1_funct_1(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),'#skF_6') != k1_funct_1('#skF_5',k1_funct_1('#skF_4','#skF_6')) ),
    inference(splitRight,[status(thm)],[c_3948])).

tff(c_3976,plain,(
    k1_funct_1(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),'#skF_6') != k1_funct_1('#skF_5',k1_funct_1('#skF_4','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3969,c_3968])).

tff(c_3979,plain,(
    ~ m1_subset_1('#skF_6','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_1896,c_3976])).

tff(c_3983,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_3979])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n011.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:29:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.32/2.50  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.55/2.52  
% 7.55/2.52  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.55/2.52  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k8_funct_2 > k3_funct_2 > k7_partfun1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 7.55/2.52  
% 7.55/2.52  %Foreground sorts:
% 7.55/2.52  
% 7.55/2.52  
% 7.55/2.52  %Background operators:
% 7.55/2.52  
% 7.55/2.52  
% 7.55/2.52  %Foreground operators:
% 7.55/2.52  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 7.55/2.52  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 7.55/2.52  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.55/2.52  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 7.55/2.52  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 7.55/2.52  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.55/2.52  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 7.55/2.52  tff(k7_partfun1, type, k7_partfun1: ($i * $i * $i) > $i).
% 7.55/2.52  tff('#skF_5', type, '#skF_5': $i).
% 7.55/2.52  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 7.55/2.52  tff(k8_funct_2, type, k8_funct_2: ($i * $i * $i * $i * $i) > $i).
% 7.55/2.52  tff('#skF_6', type, '#skF_6': $i).
% 7.55/2.52  tff('#skF_2', type, '#skF_2': $i).
% 7.55/2.52  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 7.55/2.52  tff('#skF_3', type, '#skF_3': $i).
% 7.55/2.52  tff('#skF_1', type, '#skF_1': $i).
% 7.55/2.52  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 7.55/2.52  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 7.55/2.52  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 7.55/2.52  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 7.55/2.52  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.55/2.52  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 7.55/2.52  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 7.55/2.52  tff('#skF_4', type, '#skF_4': $i).
% 7.55/2.52  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.55/2.52  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 7.55/2.52  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 7.55/2.52  tff(k3_funct_2, type, k3_funct_2: ($i * $i * $i * $i) > $i).
% 7.55/2.52  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 7.55/2.52  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 7.55/2.52  
% 7.55/2.55  tff(f_218, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C, D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (![E]: ((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, C)))) => (![F]: (m1_subset_1(F, B) => (v1_partfun1(E, A) => (k3_funct_2(B, C, k8_funct_2(B, A, C, D, E), F) = k7_partfun1(C, E, k3_funct_2(B, A, D, F)))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t193_funct_2)).
% 7.55/2.55  tff(f_51, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 7.55/2.55  tff(f_43, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 7.55/2.55  tff(f_68, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 7.55/2.55  tff(f_49, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 7.55/2.55  tff(f_76, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 7.55/2.55  tff(f_191, axiom, (![A, B, C]: (~v1_xboole_0(C) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, C)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (![E]: ((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(C, A)))) => (![F]: (m1_subset_1(F, B) => (r1_tarski(k2_relset_1(B, C, D), k1_relset_1(C, A, E)) => ((B = k1_xboole_0) | (k1_funct_1(k8_funct_2(B, C, A, D, E), F) = k1_funct_1(E, k1_funct_1(D, F))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t185_funct_2)).
% 7.55/2.55  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 7.55/2.55  tff(f_119, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (v1_partfun1(B, A) <=> (k1_relat_1(B) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_partfun1)).
% 7.55/2.55  tff(f_72, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 7.55/2.55  tff(f_36, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 7.55/2.55  tff(f_97, axiom, (![A, B]: ((~v1_xboole_0(A) & v1_xboole_0(B)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ~v1_partfun1(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_partfun1)).
% 7.55/2.55  tff(f_86, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v1_partfun1(C, A)) => (v1_funct_1(C) & v1_funct_2(C, A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_funct_2)).
% 7.55/2.55  tff(f_111, axiom, (![A, B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) => (v1_funct_1(C) & v1_partfun1(C, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc5_funct_2)).
% 7.55/2.55  tff(f_62, axiom, (![A, B]: (((v1_relat_1(B) & v5_relat_1(B, A)) & v1_funct_1(B)) => (![C]: (r2_hidden(C, k1_relat_1(B)) => r2_hidden(k1_funct_1(B, C), A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t172_funct_1)).
% 7.55/2.55  tff(f_30, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_subset)).
% 7.55/2.55  tff(f_167, axiom, (![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (m1_subset_1(D, A) => (k7_partfun1(B, C, D) = k3_funct_2(A, B, C, D)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t176_funct_2)).
% 7.55/2.55  tff(f_148, axiom, (![A, B, C, D]: (((((~v1_xboole_0(A) & v1_funct_1(C)) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & m1_subset_1(D, A)) => (k3_funct_2(A, B, C, D) = k1_funct_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k3_funct_2)).
% 7.55/2.55  tff(f_135, axiom, (![A, B, C, D, E]: (((((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(E)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => ((v1_funct_1(k8_funct_2(A, B, C, D, E)) & v1_funct_2(k8_funct_2(A, B, C, D, E), A, C)) & m1_subset_1(k8_funct_2(A, B, C, D, E), k1_zfmisc_1(k2_zfmisc_1(A, C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k8_funct_2)).
% 7.55/2.55  tff(c_56, plain, (m1_subset_1('#skF_6', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_218])).
% 7.55/2.55  tff(c_14, plain, (![A_10, B_11]: (v1_relat_1(k2_zfmisc_1(A_10, B_11)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 7.55/2.55  tff(c_62, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_218])).
% 7.55/2.55  tff(c_78, plain, (![B_114, A_115]: (v1_relat_1(B_114) | ~m1_subset_1(B_114, k1_zfmisc_1(A_115)) | ~v1_relat_1(A_115))), inference(cnfTransformation, [status(thm)], [f_43])).
% 7.55/2.55  tff(c_84, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_1'))), inference(resolution, [status(thm)], [c_62, c_78])).
% 7.55/2.55  tff(c_90, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_14, c_84])).
% 7.55/2.55  tff(c_100, plain, (![C_119, B_120, A_121]: (v5_relat_1(C_119, B_120) | ~m1_subset_1(C_119, k1_zfmisc_1(k2_zfmisc_1(A_121, B_120))))), inference(cnfTransformation, [status(thm)], [f_68])).
% 7.55/2.55  tff(c_108, plain, (v5_relat_1('#skF_4', '#skF_1')), inference(resolution, [status(thm)], [c_62, c_100])).
% 7.55/2.55  tff(c_12, plain, (![B_9, A_8]: (r1_tarski(k2_relat_1(B_9), A_8) | ~v5_relat_1(B_9, A_8) | ~v1_relat_1(B_9))), inference(cnfTransformation, [status(thm)], [f_49])).
% 7.55/2.55  tff(c_68, plain, (~v1_xboole_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_218])).
% 7.55/2.55  tff(c_70, plain, (~v1_xboole_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_218])).
% 7.55/2.55  tff(c_66, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_218])).
% 7.55/2.55  tff(c_64, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_218])).
% 7.55/2.55  tff(c_289, plain, (![A_153, B_154, C_155]: (k2_relset_1(A_153, B_154, C_155)=k2_relat_1(C_155) | ~m1_subset_1(C_155, k1_zfmisc_1(k2_zfmisc_1(A_153, B_154))))), inference(cnfTransformation, [status(thm)], [f_76])).
% 7.55/2.55  tff(c_297, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_62, c_289])).
% 7.55/2.55  tff(c_1593, plain, (![D_392, F_388, A_390, C_389, E_393, B_391]: (k1_funct_1(k8_funct_2(B_391, C_389, A_390, D_392, E_393), F_388)=k1_funct_1(E_393, k1_funct_1(D_392, F_388)) | k1_xboole_0=B_391 | ~r1_tarski(k2_relset_1(B_391, C_389, D_392), k1_relset_1(C_389, A_390, E_393)) | ~m1_subset_1(F_388, B_391) | ~m1_subset_1(E_393, k1_zfmisc_1(k2_zfmisc_1(C_389, A_390))) | ~v1_funct_1(E_393) | ~m1_subset_1(D_392, k1_zfmisc_1(k2_zfmisc_1(B_391, C_389))) | ~v1_funct_2(D_392, B_391, C_389) | ~v1_funct_1(D_392) | v1_xboole_0(C_389))), inference(cnfTransformation, [status(thm)], [f_191])).
% 7.55/2.55  tff(c_1599, plain, (![A_390, E_393, F_388]: (k1_funct_1(k8_funct_2('#skF_2', '#skF_1', A_390, '#skF_4', E_393), F_388)=k1_funct_1(E_393, k1_funct_1('#skF_4', F_388)) | k1_xboole_0='#skF_2' | ~r1_tarski(k2_relat_1('#skF_4'), k1_relset_1('#skF_1', A_390, E_393)) | ~m1_subset_1(F_388, '#skF_2') | ~m1_subset_1(E_393, k1_zfmisc_1(k2_zfmisc_1('#skF_1', A_390))) | ~v1_funct_1(E_393) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4') | v1_xboole_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_297, c_1593])).
% 7.55/2.55  tff(c_1609, plain, (![A_390, E_393, F_388]: (k1_funct_1(k8_funct_2('#skF_2', '#skF_1', A_390, '#skF_4', E_393), F_388)=k1_funct_1(E_393, k1_funct_1('#skF_4', F_388)) | k1_xboole_0='#skF_2' | ~r1_tarski(k2_relat_1('#skF_4'), k1_relset_1('#skF_1', A_390, E_393)) | ~m1_subset_1(F_388, '#skF_2') | ~m1_subset_1(E_393, k1_zfmisc_1(k2_zfmisc_1('#skF_1', A_390))) | ~v1_funct_1(E_393) | v1_xboole_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_62, c_1599])).
% 7.55/2.55  tff(c_1610, plain, (![A_390, E_393, F_388]: (k1_funct_1(k8_funct_2('#skF_2', '#skF_1', A_390, '#skF_4', E_393), F_388)=k1_funct_1(E_393, k1_funct_1('#skF_4', F_388)) | k1_xboole_0='#skF_2' | ~r1_tarski(k2_relat_1('#skF_4'), k1_relset_1('#skF_1', A_390, E_393)) | ~m1_subset_1(F_388, '#skF_2') | ~m1_subset_1(E_393, k1_zfmisc_1(k2_zfmisc_1('#skF_1', A_390))) | ~v1_funct_1(E_393))), inference(negUnitSimplification, [status(thm)], [c_70, c_1609])).
% 7.55/2.55  tff(c_1745, plain, (k1_xboole_0='#skF_2'), inference(splitLeft, [status(thm)], [c_1610])).
% 7.55/2.55  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 7.55/2.55  tff(c_1747, plain, (v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1745, c_2])).
% 7.55/2.55  tff(c_1749, plain, $false, inference(negUnitSimplification, [status(thm)], [c_68, c_1747])).
% 7.55/2.55  tff(c_1751, plain, (k1_xboole_0!='#skF_2'), inference(splitRight, [status(thm)], [c_1610])).
% 7.55/2.55  tff(c_60, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_218])).
% 7.55/2.55  tff(c_58, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_218])).
% 7.55/2.55  tff(c_81, plain, (v1_relat_1('#skF_5') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_3'))), inference(resolution, [status(thm)], [c_58, c_78])).
% 7.55/2.55  tff(c_87, plain, (v1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_14, c_81])).
% 7.55/2.55  tff(c_54, plain, (v1_partfun1('#skF_5', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_218])).
% 7.55/2.55  tff(c_91, plain, (![C_116, A_117, B_118]: (v4_relat_1(C_116, A_117) | ~m1_subset_1(C_116, k1_zfmisc_1(k2_zfmisc_1(A_117, B_118))))), inference(cnfTransformation, [status(thm)], [f_68])).
% 7.55/2.55  tff(c_98, plain, (v4_relat_1('#skF_5', '#skF_1')), inference(resolution, [status(thm)], [c_58, c_91])).
% 7.55/2.55  tff(c_116, plain, (![B_127, A_128]: (k1_relat_1(B_127)=A_128 | ~v1_partfun1(B_127, A_128) | ~v4_relat_1(B_127, A_128) | ~v1_relat_1(B_127))), inference(cnfTransformation, [status(thm)], [f_119])).
% 7.55/2.55  tff(c_122, plain, (k1_relat_1('#skF_5')='#skF_1' | ~v1_partfun1('#skF_5', '#skF_1') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_98, c_116])).
% 7.55/2.55  tff(c_128, plain, (k1_relat_1('#skF_5')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_87, c_54, c_122])).
% 7.55/2.55  tff(c_306, plain, (![A_156, B_157, C_158]: (k1_relset_1(A_156, B_157, C_158)=k1_relat_1(C_158) | ~m1_subset_1(C_158, k1_zfmisc_1(k2_zfmisc_1(A_156, B_157))))), inference(cnfTransformation, [status(thm)], [f_72])).
% 7.55/2.55  tff(c_309, plain, (k1_relset_1('#skF_1', '#skF_3', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_58, c_306])).
% 7.55/2.55  tff(c_314, plain, (k1_relset_1('#skF_1', '#skF_3', '#skF_5')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_128, c_309])).
% 7.55/2.55  tff(c_1597, plain, (![B_391, D_392, F_388]: (k1_funct_1(k8_funct_2(B_391, '#skF_1', '#skF_3', D_392, '#skF_5'), F_388)=k1_funct_1('#skF_5', k1_funct_1(D_392, F_388)) | k1_xboole_0=B_391 | ~r1_tarski(k2_relset_1(B_391, '#skF_1', D_392), '#skF_1') | ~m1_subset_1(F_388, B_391) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3'))) | ~v1_funct_1('#skF_5') | ~m1_subset_1(D_392, k1_zfmisc_1(k2_zfmisc_1(B_391, '#skF_1'))) | ~v1_funct_2(D_392, B_391, '#skF_1') | ~v1_funct_1(D_392) | v1_xboole_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_314, c_1593])).
% 7.55/2.55  tff(c_1606, plain, (![B_391, D_392, F_388]: (k1_funct_1(k8_funct_2(B_391, '#skF_1', '#skF_3', D_392, '#skF_5'), F_388)=k1_funct_1('#skF_5', k1_funct_1(D_392, F_388)) | k1_xboole_0=B_391 | ~r1_tarski(k2_relset_1(B_391, '#skF_1', D_392), '#skF_1') | ~m1_subset_1(F_388, B_391) | ~m1_subset_1(D_392, k1_zfmisc_1(k2_zfmisc_1(B_391, '#skF_1'))) | ~v1_funct_2(D_392, B_391, '#skF_1') | ~v1_funct_1(D_392) | v1_xboole_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_1597])).
% 7.55/2.55  tff(c_1857, plain, (![B_414, D_415, F_416]: (k1_funct_1(k8_funct_2(B_414, '#skF_1', '#skF_3', D_415, '#skF_5'), F_416)=k1_funct_1('#skF_5', k1_funct_1(D_415, F_416)) | k1_xboole_0=B_414 | ~r1_tarski(k2_relset_1(B_414, '#skF_1', D_415), '#skF_1') | ~m1_subset_1(F_416, B_414) | ~m1_subset_1(D_415, k1_zfmisc_1(k2_zfmisc_1(B_414, '#skF_1'))) | ~v1_funct_2(D_415, B_414, '#skF_1') | ~v1_funct_1(D_415))), inference(negUnitSimplification, [status(thm)], [c_70, c_1606])).
% 7.55/2.55  tff(c_1877, plain, (![F_416]: (k1_funct_1(k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), F_416)=k1_funct_1('#skF_5', k1_funct_1('#skF_4', F_416)) | k1_xboole_0='#skF_2' | ~r1_tarski(k2_relset_1('#skF_2', '#skF_1', '#skF_4'), '#skF_1') | ~m1_subset_1(F_416, '#skF_2') | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_62, c_1857])).
% 7.55/2.55  tff(c_1886, plain, (![F_416]: (k1_funct_1(k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), F_416)=k1_funct_1('#skF_5', k1_funct_1('#skF_4', F_416)) | k1_xboole_0='#skF_2' | ~r1_tarski(k2_relat_1('#skF_4'), '#skF_1') | ~m1_subset_1(F_416, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_297, c_1877])).
% 7.55/2.55  tff(c_1887, plain, (![F_416]: (k1_funct_1(k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), F_416)=k1_funct_1('#skF_5', k1_funct_1('#skF_4', F_416)) | ~r1_tarski(k2_relat_1('#skF_4'), '#skF_1') | ~m1_subset_1(F_416, '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_1751, c_1886])).
% 7.55/2.55  tff(c_1888, plain, (~r1_tarski(k2_relat_1('#skF_4'), '#skF_1')), inference(splitLeft, [status(thm)], [c_1887])).
% 7.55/2.55  tff(c_1891, plain, (~v5_relat_1('#skF_4', '#skF_1') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_12, c_1888])).
% 7.55/2.55  tff(c_1895, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_90, c_108, c_1891])).
% 7.55/2.55  tff(c_1896, plain, (![F_416]: (k1_funct_1(k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), F_416)=k1_funct_1('#skF_5', k1_funct_1('#skF_4', F_416)) | ~m1_subset_1(F_416, '#skF_2'))), inference(splitRight, [status(thm)], [c_1887])).
% 7.55/2.55  tff(c_6, plain, (![A_3, B_4]: (r2_hidden(A_3, B_4) | v1_xboole_0(B_4) | ~m1_subset_1(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_36])).
% 7.55/2.55  tff(c_325, plain, (![C_159, A_160, B_161]: (~v1_partfun1(C_159, A_160) | ~m1_subset_1(C_159, k1_zfmisc_1(k2_zfmisc_1(A_160, B_161))) | ~v1_xboole_0(B_161) | v1_xboole_0(A_160))), inference(cnfTransformation, [status(thm)], [f_97])).
% 7.55/2.55  tff(c_328, plain, (~v1_partfun1('#skF_5', '#skF_1') | ~v1_xboole_0('#skF_3') | v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_58, c_325])).
% 7.55/2.55  tff(c_334, plain, (~v1_xboole_0('#skF_3') | v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_328])).
% 7.55/2.55  tff(c_335, plain, (~v1_xboole_0('#skF_3')), inference(negUnitSimplification, [status(thm)], [c_70, c_334])).
% 7.55/2.55  tff(c_340, plain, (![C_162, A_163, B_164]: (v1_funct_2(C_162, A_163, B_164) | ~v1_partfun1(C_162, A_163) | ~v1_funct_1(C_162) | ~m1_subset_1(C_162, k1_zfmisc_1(k2_zfmisc_1(A_163, B_164))))), inference(cnfTransformation, [status(thm)], [f_86])).
% 7.55/2.55  tff(c_343, plain, (v1_funct_2('#skF_5', '#skF_1', '#skF_3') | ~v1_partfun1('#skF_5', '#skF_1') | ~v1_funct_1('#skF_5')), inference(resolution, [status(thm)], [c_58, c_340])).
% 7.55/2.55  tff(c_349, plain, (v1_funct_2('#skF_5', '#skF_1', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_54, c_343])).
% 7.55/2.55  tff(c_99, plain, (v4_relat_1('#skF_4', '#skF_2')), inference(resolution, [status(thm)], [c_62, c_91])).
% 7.55/2.55  tff(c_119, plain, (k1_relat_1('#skF_4')='#skF_2' | ~v1_partfun1('#skF_4', '#skF_2') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_99, c_116])).
% 7.55/2.55  tff(c_125, plain, (k1_relat_1('#skF_4')='#skF_2' | ~v1_partfun1('#skF_4', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_90, c_119])).
% 7.55/2.55  tff(c_138, plain, (~v1_partfun1('#skF_4', '#skF_2')), inference(splitLeft, [status(thm)], [c_125])).
% 7.55/2.55  tff(c_256, plain, (![C_150, A_151, B_152]: (v1_partfun1(C_150, A_151) | ~v1_funct_2(C_150, A_151, B_152) | ~v1_funct_1(C_150) | ~m1_subset_1(C_150, k1_zfmisc_1(k2_zfmisc_1(A_151, B_152))) | v1_xboole_0(B_152))), inference(cnfTransformation, [status(thm)], [f_111])).
% 7.55/2.55  tff(c_266, plain, (v1_partfun1('#skF_4', '#skF_2') | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4') | v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_62, c_256])).
% 7.55/2.55  tff(c_274, plain, (v1_partfun1('#skF_4', '#skF_2') | v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_266])).
% 7.55/2.55  tff(c_276, plain, $false, inference(negUnitSimplification, [status(thm)], [c_70, c_138, c_274])).
% 7.55/2.55  tff(c_277, plain, (k1_relat_1('#skF_4')='#skF_2'), inference(splitRight, [status(thm)], [c_125])).
% 7.55/2.55  tff(c_353, plain, (![B_165, C_166, A_167]: (r2_hidden(k1_funct_1(B_165, C_166), A_167) | ~r2_hidden(C_166, k1_relat_1(B_165)) | ~v1_funct_1(B_165) | ~v5_relat_1(B_165, A_167) | ~v1_relat_1(B_165))), inference(cnfTransformation, [status(thm)], [f_62])).
% 7.55/2.55  tff(c_4, plain, (![A_1, B_2]: (m1_subset_1(A_1, B_2) | ~r2_hidden(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_30])).
% 7.55/2.55  tff(c_358, plain, (![B_168, C_169, A_170]: (m1_subset_1(k1_funct_1(B_168, C_169), A_170) | ~r2_hidden(C_169, k1_relat_1(B_168)) | ~v1_funct_1(B_168) | ~v5_relat_1(B_168, A_170) | ~v1_relat_1(B_168))), inference(resolution, [status(thm)], [c_353, c_4])).
% 7.55/2.55  tff(c_363, plain, (![C_169, A_170]: (m1_subset_1(k1_funct_1('#skF_4', C_169), A_170) | ~r2_hidden(C_169, '#skF_2') | ~v1_funct_1('#skF_4') | ~v5_relat_1('#skF_4', A_170) | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_277, c_358])).
% 7.55/2.55  tff(c_371, plain, (![C_169, A_170]: (m1_subset_1(k1_funct_1('#skF_4', C_169), A_170) | ~r2_hidden(C_169, '#skF_2') | ~v5_relat_1('#skF_4', A_170))), inference(demodulation, [status(thm), theory('equality')], [c_90, c_66, c_363])).
% 7.55/2.55  tff(c_705, plain, (![A_249, B_250, C_251, D_252]: (k3_funct_2(A_249, B_250, C_251, D_252)=k7_partfun1(B_250, C_251, D_252) | ~m1_subset_1(D_252, A_249) | ~m1_subset_1(C_251, k1_zfmisc_1(k2_zfmisc_1(A_249, B_250))) | ~v1_funct_2(C_251, A_249, B_250) | ~v1_funct_1(C_251) | v1_xboole_0(B_250) | v1_xboole_0(A_249))), inference(cnfTransformation, [status(thm)], [f_167])).
% 7.55/2.55  tff(c_3870, plain, (![A_729, B_730, C_731, C_732]: (k3_funct_2(A_729, B_730, C_731, k1_funct_1('#skF_4', C_732))=k7_partfun1(B_730, C_731, k1_funct_1('#skF_4', C_732)) | ~m1_subset_1(C_731, k1_zfmisc_1(k2_zfmisc_1(A_729, B_730))) | ~v1_funct_2(C_731, A_729, B_730) | ~v1_funct_1(C_731) | v1_xboole_0(B_730) | v1_xboole_0(A_729) | ~r2_hidden(C_732, '#skF_2') | ~v5_relat_1('#skF_4', A_729))), inference(resolution, [status(thm)], [c_371, c_705])).
% 7.55/2.55  tff(c_3897, plain, (![C_732]: (k3_funct_2('#skF_1', '#skF_3', '#skF_5', k1_funct_1('#skF_4', C_732))=k7_partfun1('#skF_3', '#skF_5', k1_funct_1('#skF_4', C_732)) | ~v1_funct_2('#skF_5', '#skF_1', '#skF_3') | ~v1_funct_1('#skF_5') | v1_xboole_0('#skF_3') | v1_xboole_0('#skF_1') | ~r2_hidden(C_732, '#skF_2') | ~v5_relat_1('#skF_4', '#skF_1'))), inference(resolution, [status(thm)], [c_58, c_3870])).
% 7.55/2.55  tff(c_3914, plain, (![C_732]: (k3_funct_2('#skF_1', '#skF_3', '#skF_5', k1_funct_1('#skF_4', C_732))=k7_partfun1('#skF_3', '#skF_5', k1_funct_1('#skF_4', C_732)) | v1_xboole_0('#skF_3') | v1_xboole_0('#skF_1') | ~r2_hidden(C_732, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_108, c_60, c_349, c_3897])).
% 7.55/2.55  tff(c_3920, plain, (![C_733]: (k3_funct_2('#skF_1', '#skF_3', '#skF_5', k1_funct_1('#skF_4', C_733))=k7_partfun1('#skF_3', '#skF_5', k1_funct_1('#skF_4', C_733)) | ~r2_hidden(C_733, '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_70, c_335, c_3914])).
% 7.55/2.55  tff(c_523, plain, (![A_201, B_202, C_203, D_204]: (k3_funct_2(A_201, B_202, C_203, D_204)=k1_funct_1(C_203, D_204) | ~m1_subset_1(D_204, A_201) | ~m1_subset_1(C_203, k1_zfmisc_1(k2_zfmisc_1(A_201, B_202))) | ~v1_funct_2(C_203, A_201, B_202) | ~v1_funct_1(C_203) | v1_xboole_0(A_201))), inference(cnfTransformation, [status(thm)], [f_148])).
% 7.55/2.55  tff(c_2985, plain, (![A_567, B_568, C_569, C_570]: (k3_funct_2(A_567, B_568, C_569, k1_funct_1('#skF_4', C_570))=k1_funct_1(C_569, k1_funct_1('#skF_4', C_570)) | ~m1_subset_1(C_569, k1_zfmisc_1(k2_zfmisc_1(A_567, B_568))) | ~v1_funct_2(C_569, A_567, B_568) | ~v1_funct_1(C_569) | v1_xboole_0(A_567) | ~r2_hidden(C_570, '#skF_2') | ~v5_relat_1('#skF_4', A_567))), inference(resolution, [status(thm)], [c_371, c_523])).
% 7.55/2.55  tff(c_3012, plain, (![C_570]: (k3_funct_2('#skF_1', '#skF_3', '#skF_5', k1_funct_1('#skF_4', C_570))=k1_funct_1('#skF_5', k1_funct_1('#skF_4', C_570)) | ~v1_funct_2('#skF_5', '#skF_1', '#skF_3') | ~v1_funct_1('#skF_5') | v1_xboole_0('#skF_1') | ~r2_hidden(C_570, '#skF_2') | ~v5_relat_1('#skF_4', '#skF_1'))), inference(resolution, [status(thm)], [c_58, c_2985])).
% 7.55/2.55  tff(c_3029, plain, (![C_570]: (k3_funct_2('#skF_1', '#skF_3', '#skF_5', k1_funct_1('#skF_4', C_570))=k1_funct_1('#skF_5', k1_funct_1('#skF_4', C_570)) | v1_xboole_0('#skF_1') | ~r2_hidden(C_570, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_108, c_60, c_349, c_3012])).
% 7.55/2.55  tff(c_3030, plain, (![C_570]: (k3_funct_2('#skF_1', '#skF_3', '#skF_5', k1_funct_1('#skF_4', C_570))=k1_funct_1('#skF_5', k1_funct_1('#skF_4', C_570)) | ~r2_hidden(C_570, '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_70, c_3029])).
% 7.55/2.55  tff(c_3942, plain, (![C_738]: (k7_partfun1('#skF_3', '#skF_5', k1_funct_1('#skF_4', C_738))=k1_funct_1('#skF_5', k1_funct_1('#skF_4', C_738)) | ~r2_hidden(C_738, '#skF_2') | ~r2_hidden(C_738, '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_3920, c_3030])).
% 7.55/2.55  tff(c_577, plain, (![E_228, B_227, C_229, D_230, A_226]: (v1_funct_1(k8_funct_2(A_226, B_227, C_229, D_230, E_228)) | ~m1_subset_1(E_228, k1_zfmisc_1(k2_zfmisc_1(B_227, C_229))) | ~v1_funct_1(E_228) | ~m1_subset_1(D_230, k1_zfmisc_1(k2_zfmisc_1(A_226, B_227))) | ~v1_funct_2(D_230, A_226, B_227) | ~v1_funct_1(D_230))), inference(cnfTransformation, [status(thm)], [f_135])).
% 7.55/2.55  tff(c_588, plain, (![A_226, D_230]: (v1_funct_1(k8_funct_2(A_226, '#skF_1', '#skF_3', D_230, '#skF_5')) | ~v1_funct_1('#skF_5') | ~m1_subset_1(D_230, k1_zfmisc_1(k2_zfmisc_1(A_226, '#skF_1'))) | ~v1_funct_2(D_230, A_226, '#skF_1') | ~v1_funct_1(D_230))), inference(resolution, [status(thm)], [c_58, c_577])).
% 7.55/2.55  tff(c_600, plain, (![A_231, D_232]: (v1_funct_1(k8_funct_2(A_231, '#skF_1', '#skF_3', D_232, '#skF_5')) | ~m1_subset_1(D_232, k1_zfmisc_1(k2_zfmisc_1(A_231, '#skF_1'))) | ~v1_funct_2(D_232, A_231, '#skF_1') | ~v1_funct_1(D_232))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_588])).
% 7.55/2.55  tff(c_615, plain, (v1_funct_1(k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5')) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_62, c_600])).
% 7.55/2.55  tff(c_621, plain, (v1_funct_1(k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_615])).
% 7.55/2.55  tff(c_768, plain, (![B_274, E_275, A_273, D_277, C_276]: (v1_funct_2(k8_funct_2(A_273, B_274, C_276, D_277, E_275), A_273, C_276) | ~m1_subset_1(E_275, k1_zfmisc_1(k2_zfmisc_1(B_274, C_276))) | ~v1_funct_1(E_275) | ~m1_subset_1(D_277, k1_zfmisc_1(k2_zfmisc_1(A_273, B_274))) | ~v1_funct_2(D_277, A_273, B_274) | ~v1_funct_1(D_277))), inference(cnfTransformation, [status(thm)], [f_135])).
% 7.55/2.55  tff(c_782, plain, (![A_273, D_277]: (v1_funct_2(k8_funct_2(A_273, '#skF_1', '#skF_3', D_277, '#skF_5'), A_273, '#skF_3') | ~v1_funct_1('#skF_5') | ~m1_subset_1(D_277, k1_zfmisc_1(k2_zfmisc_1(A_273, '#skF_1'))) | ~v1_funct_2(D_277, A_273, '#skF_1') | ~v1_funct_1(D_277))), inference(resolution, [status(thm)], [c_58, c_768])).
% 7.55/2.55  tff(c_795, plain, (![A_278, D_279]: (v1_funct_2(k8_funct_2(A_278, '#skF_1', '#skF_3', D_279, '#skF_5'), A_278, '#skF_3') | ~m1_subset_1(D_279, k1_zfmisc_1(k2_zfmisc_1(A_278, '#skF_1'))) | ~v1_funct_2(D_279, A_278, '#skF_1') | ~v1_funct_1(D_279))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_782])).
% 7.55/2.55  tff(c_809, plain, (v1_funct_2(k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), '#skF_2', '#skF_3') | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_62, c_795])).
% 7.55/2.55  tff(c_816, plain, (v1_funct_2(k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), '#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_809])).
% 7.55/2.55  tff(c_40, plain, (![D_41, B_39, A_38, E_42, C_40]: (m1_subset_1(k8_funct_2(A_38, B_39, C_40, D_41, E_42), k1_zfmisc_1(k2_zfmisc_1(A_38, C_40))) | ~m1_subset_1(E_42, k1_zfmisc_1(k2_zfmisc_1(B_39, C_40))) | ~v1_funct_1(E_42) | ~m1_subset_1(D_41, k1_zfmisc_1(k2_zfmisc_1(A_38, B_39))) | ~v1_funct_2(D_41, A_38, B_39) | ~v1_funct_1(D_41))), inference(cnfTransformation, [status(thm)], [f_135])).
% 7.55/2.55  tff(c_840, plain, (![E_296, C_297, A_294, D_298, B_295]: (m1_subset_1(k8_funct_2(A_294, B_295, C_297, D_298, E_296), k1_zfmisc_1(k2_zfmisc_1(A_294, C_297))) | ~m1_subset_1(E_296, k1_zfmisc_1(k2_zfmisc_1(B_295, C_297))) | ~v1_funct_1(E_296) | ~m1_subset_1(D_298, k1_zfmisc_1(k2_zfmisc_1(A_294, B_295))) | ~v1_funct_2(D_298, A_294, B_295) | ~v1_funct_1(D_298))), inference(cnfTransformation, [status(thm)], [f_135])).
% 7.55/2.55  tff(c_8, plain, (![B_7, A_5]: (v1_relat_1(B_7) | ~m1_subset_1(B_7, k1_zfmisc_1(A_5)) | ~v1_relat_1(A_5))), inference(cnfTransformation, [status(thm)], [f_43])).
% 7.55/2.55  tff(c_894, plain, (![E_296, C_297, A_294, D_298, B_295]: (v1_relat_1(k8_funct_2(A_294, B_295, C_297, D_298, E_296)) | ~v1_relat_1(k2_zfmisc_1(A_294, C_297)) | ~m1_subset_1(E_296, k1_zfmisc_1(k2_zfmisc_1(B_295, C_297))) | ~v1_funct_1(E_296) | ~m1_subset_1(D_298, k1_zfmisc_1(k2_zfmisc_1(A_294, B_295))) | ~v1_funct_2(D_298, A_294, B_295) | ~v1_funct_1(D_298))), inference(resolution, [status(thm)], [c_840, c_8])).
% 7.55/2.55  tff(c_915, plain, (![B_301, D_299, C_303, E_300, A_302]: (v1_relat_1(k8_funct_2(A_302, B_301, C_303, D_299, E_300)) | ~m1_subset_1(E_300, k1_zfmisc_1(k2_zfmisc_1(B_301, C_303))) | ~v1_funct_1(E_300) | ~m1_subset_1(D_299, k1_zfmisc_1(k2_zfmisc_1(A_302, B_301))) | ~v1_funct_2(D_299, A_302, B_301) | ~v1_funct_1(D_299))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_894])).
% 7.55/2.55  tff(c_931, plain, (![A_302, D_299]: (v1_relat_1(k8_funct_2(A_302, '#skF_1', '#skF_3', D_299, '#skF_5')) | ~v1_funct_1('#skF_5') | ~m1_subset_1(D_299, k1_zfmisc_1(k2_zfmisc_1(A_302, '#skF_1'))) | ~v1_funct_2(D_299, A_302, '#skF_1') | ~v1_funct_1(D_299))), inference(resolution, [status(thm)], [c_58, c_915])).
% 7.55/2.55  tff(c_945, plain, (![A_304, D_305]: (v1_relat_1(k8_funct_2(A_304, '#skF_1', '#skF_3', D_305, '#skF_5')) | ~m1_subset_1(D_305, k1_zfmisc_1(k2_zfmisc_1(A_304, '#skF_1'))) | ~v1_funct_2(D_305, A_304, '#skF_1') | ~v1_funct_1(D_305))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_931])).
% 7.55/2.55  tff(c_968, plain, (v1_relat_1(k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5')) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_62, c_945])).
% 7.55/2.55  tff(c_976, plain, (v1_relat_1(k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_968])).
% 7.55/2.55  tff(c_20, plain, (![C_18, A_16, B_17]: (v4_relat_1(C_18, A_16) | ~m1_subset_1(C_18, k1_zfmisc_1(k2_zfmisc_1(A_16, B_17))))), inference(cnfTransformation, [status(thm)], [f_68])).
% 7.55/2.55  tff(c_1003, plain, (![C_312, E_309, D_308, B_310, A_311]: (v4_relat_1(k8_funct_2(A_311, B_310, C_312, D_308, E_309), A_311) | ~m1_subset_1(E_309, k1_zfmisc_1(k2_zfmisc_1(B_310, C_312))) | ~v1_funct_1(E_309) | ~m1_subset_1(D_308, k1_zfmisc_1(k2_zfmisc_1(A_311, B_310))) | ~v1_funct_2(D_308, A_311, B_310) | ~v1_funct_1(D_308))), inference(resolution, [status(thm)], [c_840, c_20])).
% 7.55/2.55  tff(c_1019, plain, (![A_311, D_308]: (v4_relat_1(k8_funct_2(A_311, '#skF_1', '#skF_3', D_308, '#skF_5'), A_311) | ~v1_funct_1('#skF_5') | ~m1_subset_1(D_308, k1_zfmisc_1(k2_zfmisc_1(A_311, '#skF_1'))) | ~v1_funct_2(D_308, A_311, '#skF_1') | ~v1_funct_1(D_308))), inference(resolution, [status(thm)], [c_58, c_1003])).
% 7.55/2.55  tff(c_1033, plain, (![A_313, D_314]: (v4_relat_1(k8_funct_2(A_313, '#skF_1', '#skF_3', D_314, '#skF_5'), A_313) | ~m1_subset_1(D_314, k1_zfmisc_1(k2_zfmisc_1(A_313, '#skF_1'))) | ~v1_funct_2(D_314, A_313, '#skF_1') | ~v1_funct_1(D_314))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_1019])).
% 7.55/2.55  tff(c_1050, plain, (v4_relat_1(k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), '#skF_2') | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_62, c_1033])).
% 7.55/2.55  tff(c_1058, plain, (v4_relat_1(k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_1050])).
% 7.55/2.55  tff(c_38, plain, (![B_37, A_36]: (k1_relat_1(B_37)=A_36 | ~v1_partfun1(B_37, A_36) | ~v4_relat_1(B_37, A_36) | ~v1_relat_1(B_37))), inference(cnfTransformation, [status(thm)], [f_119])).
% 7.55/2.55  tff(c_1061, plain, (k1_relat_1(k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'))='#skF_2' | ~v1_partfun1(k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), '#skF_2') | ~v1_relat_1(k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_1058, c_38])).
% 7.55/2.55  tff(c_1064, plain, (k1_relat_1(k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'))='#skF_2' | ~v1_partfun1(k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_976, c_1061])).
% 7.55/2.55  tff(c_1065, plain, (~v1_partfun1(k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), '#skF_2')), inference(splitLeft, [status(thm)], [c_1064])).
% 7.55/2.55  tff(c_22, plain, (![A_19, B_20, C_21]: (k1_relset_1(A_19, B_20, C_21)=k1_relat_1(C_21) | ~m1_subset_1(C_21, k1_zfmisc_1(k2_zfmisc_1(A_19, B_20))))), inference(cnfTransformation, [status(thm)], [f_72])).
% 7.55/2.55  tff(c_1406, plain, (![D_379, B_381, C_383, E_380, A_382]: (k1_relset_1(A_382, C_383, k8_funct_2(A_382, B_381, C_383, D_379, E_380))=k1_relat_1(k8_funct_2(A_382, B_381, C_383, D_379, E_380)) | ~m1_subset_1(E_380, k1_zfmisc_1(k2_zfmisc_1(B_381, C_383))) | ~v1_funct_1(E_380) | ~m1_subset_1(D_379, k1_zfmisc_1(k2_zfmisc_1(A_382, B_381))) | ~v1_funct_2(D_379, A_382, B_381) | ~v1_funct_1(D_379))), inference(resolution, [status(thm)], [c_840, c_22])).
% 7.55/2.55  tff(c_1422, plain, (![A_382, D_379]: (k1_relset_1(A_382, '#skF_3', k8_funct_2(A_382, '#skF_1', '#skF_3', D_379, '#skF_5'))=k1_relat_1(k8_funct_2(A_382, '#skF_1', '#skF_3', D_379, '#skF_5')) | ~v1_funct_1('#skF_5') | ~m1_subset_1(D_379, k1_zfmisc_1(k2_zfmisc_1(A_382, '#skF_1'))) | ~v1_funct_2(D_379, A_382, '#skF_1') | ~v1_funct_1(D_379))), inference(resolution, [status(thm)], [c_58, c_1406])).
% 7.55/2.55  tff(c_1449, plain, (![A_386, D_387]: (k1_relset_1(A_386, '#skF_3', k8_funct_2(A_386, '#skF_1', '#skF_3', D_387, '#skF_5'))=k1_relat_1(k8_funct_2(A_386, '#skF_1', '#skF_3', D_387, '#skF_5')) | ~m1_subset_1(D_387, k1_zfmisc_1(k2_zfmisc_1(A_386, '#skF_1'))) | ~v1_funct_2(D_387, A_386, '#skF_1') | ~v1_funct_1(D_387))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_1422])).
% 7.55/2.55  tff(c_1466, plain, (k1_relset_1('#skF_2', '#skF_3', k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'))=k1_relat_1(k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5')) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_62, c_1449])).
% 7.55/2.55  tff(c_1474, plain, (k1_relset_1('#skF_2', '#skF_3', k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'))=k1_relat_1(k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_1466])).
% 7.55/2.55  tff(c_50, plain, (![B_63, E_76, F_78, C_64, D_72, A_62]: (k1_funct_1(k8_funct_2(B_63, C_64, A_62, D_72, E_76), F_78)=k1_funct_1(E_76, k1_funct_1(D_72, F_78)) | k1_xboole_0=B_63 | ~r1_tarski(k2_relset_1(B_63, C_64, D_72), k1_relset_1(C_64, A_62, E_76)) | ~m1_subset_1(F_78, B_63) | ~m1_subset_1(E_76, k1_zfmisc_1(k2_zfmisc_1(C_64, A_62))) | ~v1_funct_1(E_76) | ~m1_subset_1(D_72, k1_zfmisc_1(k2_zfmisc_1(B_63, C_64))) | ~v1_funct_2(D_72, B_63, C_64) | ~v1_funct_1(D_72) | v1_xboole_0(C_64))), inference(cnfTransformation, [status(thm)], [f_191])).
% 7.55/2.55  tff(c_1477, plain, (![B_63, D_72, F_78]: (k1_funct_1(k8_funct_2(B_63, '#skF_2', '#skF_3', D_72, k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5')), F_78)=k1_funct_1(k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), k1_funct_1(D_72, F_78)) | k1_xboole_0=B_63 | ~r1_tarski(k2_relset_1(B_63, '#skF_2', D_72), k1_relat_1(k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'))) | ~m1_subset_1(F_78, B_63) | ~m1_subset_1(k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~v1_funct_1(k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5')) | ~m1_subset_1(D_72, k1_zfmisc_1(k2_zfmisc_1(B_63, '#skF_2'))) | ~v1_funct_2(D_72, B_63, '#skF_2') | ~v1_funct_1(D_72) | v1_xboole_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_1474, c_50])).
% 7.55/2.55  tff(c_1481, plain, (![B_63, D_72, F_78]: (k1_funct_1(k8_funct_2(B_63, '#skF_2', '#skF_3', D_72, k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5')), F_78)=k1_funct_1(k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), k1_funct_1(D_72, F_78)) | k1_xboole_0=B_63 | ~r1_tarski(k2_relset_1(B_63, '#skF_2', D_72), k1_relat_1(k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'))) | ~m1_subset_1(F_78, B_63) | ~m1_subset_1(k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~m1_subset_1(D_72, k1_zfmisc_1(k2_zfmisc_1(B_63, '#skF_2'))) | ~v1_funct_2(D_72, B_63, '#skF_2') | ~v1_funct_1(D_72) | v1_xboole_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_621, c_1477])).
% 7.55/2.55  tff(c_1482, plain, (![B_63, D_72, F_78]: (k1_funct_1(k8_funct_2(B_63, '#skF_2', '#skF_3', D_72, k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5')), F_78)=k1_funct_1(k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), k1_funct_1(D_72, F_78)) | k1_xboole_0=B_63 | ~r1_tarski(k2_relset_1(B_63, '#skF_2', D_72), k1_relat_1(k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'))) | ~m1_subset_1(F_78, B_63) | ~m1_subset_1(k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~m1_subset_1(D_72, k1_zfmisc_1(k2_zfmisc_1(B_63, '#skF_2'))) | ~v1_funct_2(D_72, B_63, '#skF_2') | ~v1_funct_1(D_72))), inference(negUnitSimplification, [status(thm)], [c_68, c_1481])).
% 7.55/2.55  tff(c_1484, plain, (~m1_subset_1(k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(splitLeft, [status(thm)], [c_1482])).
% 7.55/2.55  tff(c_1487, plain, (~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3'))) | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_40, c_1484])).
% 7.55/2.55  tff(c_1491, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_62, c_60, c_58, c_1487])).
% 7.55/2.55  tff(c_1493, plain, (m1_subset_1(k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(splitRight, [status(thm)], [c_1482])).
% 7.55/2.55  tff(c_32, plain, (![C_35, A_32, B_33]: (v1_partfun1(C_35, A_32) | ~v1_funct_2(C_35, A_32, B_33) | ~v1_funct_1(C_35) | ~m1_subset_1(C_35, k1_zfmisc_1(k2_zfmisc_1(A_32, B_33))) | v1_xboole_0(B_33))), inference(cnfTransformation, [status(thm)], [f_111])).
% 7.55/2.55  tff(c_1520, plain, (v1_partfun1(k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), '#skF_2') | ~v1_funct_2(k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), '#skF_2', '#skF_3') | ~v1_funct_1(k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5')) | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_1493, c_32])).
% 7.55/2.55  tff(c_1574, plain, (v1_partfun1(k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), '#skF_2') | v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_621, c_816, c_1520])).
% 7.55/2.55  tff(c_1576, plain, $false, inference(negUnitSimplification, [status(thm)], [c_335, c_1065, c_1574])).
% 7.55/2.55  tff(c_1577, plain, (k1_relat_1(k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'))='#skF_2'), inference(splitRight, [status(thm)], [c_1064])).
% 7.55/2.55  tff(c_2238, plain, (![D_470, B_472, E_471, C_474, A_473]: (k1_relset_1(A_473, C_474, k8_funct_2(A_473, B_472, C_474, D_470, E_471))=k1_relat_1(k8_funct_2(A_473, B_472, C_474, D_470, E_471)) | ~m1_subset_1(E_471, k1_zfmisc_1(k2_zfmisc_1(B_472, C_474))) | ~v1_funct_1(E_471) | ~m1_subset_1(D_470, k1_zfmisc_1(k2_zfmisc_1(A_473, B_472))) | ~v1_funct_2(D_470, A_473, B_472) | ~v1_funct_1(D_470))), inference(resolution, [status(thm)], [c_840, c_22])).
% 7.55/2.55  tff(c_2260, plain, (![A_473, D_470]: (k1_relset_1(A_473, '#skF_3', k8_funct_2(A_473, '#skF_1', '#skF_3', D_470, '#skF_5'))=k1_relat_1(k8_funct_2(A_473, '#skF_1', '#skF_3', D_470, '#skF_5')) | ~v1_funct_1('#skF_5') | ~m1_subset_1(D_470, k1_zfmisc_1(k2_zfmisc_1(A_473, '#skF_1'))) | ~v1_funct_2(D_470, A_473, '#skF_1') | ~v1_funct_1(D_470))), inference(resolution, [status(thm)], [c_58, c_2238])).
% 7.55/2.55  tff(c_2276, plain, (![A_475, D_476]: (k1_relset_1(A_475, '#skF_3', k8_funct_2(A_475, '#skF_1', '#skF_3', D_476, '#skF_5'))=k1_relat_1(k8_funct_2(A_475, '#skF_1', '#skF_3', D_476, '#skF_5')) | ~m1_subset_1(D_476, k1_zfmisc_1(k2_zfmisc_1(A_475, '#skF_1'))) | ~v1_funct_2(D_476, A_475, '#skF_1') | ~v1_funct_1(D_476))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_2260])).
% 7.55/2.55  tff(c_2299, plain, (k1_relset_1('#skF_2', '#skF_3', k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'))=k1_relat_1(k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5')) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_62, c_2276])).
% 7.55/2.55  tff(c_2309, plain, (k1_relset_1('#skF_2', '#skF_3', k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_1577, c_2299])).
% 7.55/2.55  tff(c_2312, plain, (![B_63, D_72, F_78]: (k1_funct_1(k8_funct_2(B_63, '#skF_2', '#skF_3', D_72, k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5')), F_78)=k1_funct_1(k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), k1_funct_1(D_72, F_78)) | k1_xboole_0=B_63 | ~r1_tarski(k2_relset_1(B_63, '#skF_2', D_72), '#skF_2') | ~m1_subset_1(F_78, B_63) | ~m1_subset_1(k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~v1_funct_1(k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5')) | ~m1_subset_1(D_72, k1_zfmisc_1(k2_zfmisc_1(B_63, '#skF_2'))) | ~v1_funct_2(D_72, B_63, '#skF_2') | ~v1_funct_1(D_72) | v1_xboole_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_2309, c_50])).
% 7.55/2.55  tff(c_2316, plain, (![B_63, D_72, F_78]: (k1_funct_1(k8_funct_2(B_63, '#skF_2', '#skF_3', D_72, k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5')), F_78)=k1_funct_1(k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), k1_funct_1(D_72, F_78)) | k1_xboole_0=B_63 | ~r1_tarski(k2_relset_1(B_63, '#skF_2', D_72), '#skF_2') | ~m1_subset_1(F_78, B_63) | ~m1_subset_1(k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~m1_subset_1(D_72, k1_zfmisc_1(k2_zfmisc_1(B_63, '#skF_2'))) | ~v1_funct_2(D_72, B_63, '#skF_2') | ~v1_funct_1(D_72) | v1_xboole_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_621, c_2312])).
% 7.55/2.55  tff(c_2317, plain, (![B_63, D_72, F_78]: (k1_funct_1(k8_funct_2(B_63, '#skF_2', '#skF_3', D_72, k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5')), F_78)=k1_funct_1(k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), k1_funct_1(D_72, F_78)) | k1_xboole_0=B_63 | ~r1_tarski(k2_relset_1(B_63, '#skF_2', D_72), '#skF_2') | ~m1_subset_1(F_78, B_63) | ~m1_subset_1(k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~m1_subset_1(D_72, k1_zfmisc_1(k2_zfmisc_1(B_63, '#skF_2'))) | ~v1_funct_2(D_72, B_63, '#skF_2') | ~v1_funct_1(D_72))), inference(negUnitSimplification, [status(thm)], [c_68, c_2316])).
% 7.55/2.55  tff(c_2348, plain, (~m1_subset_1(k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(splitLeft, [status(thm)], [c_2317])).
% 7.55/2.55  tff(c_2351, plain, (~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3'))) | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_40, c_2348])).
% 7.55/2.55  tff(c_2355, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_62, c_60, c_58, c_2351])).
% 7.55/2.55  tff(c_2357, plain, (m1_subset_1(k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(splitRight, [status(thm)], [c_2317])).
% 7.55/2.55  tff(c_535, plain, (![B_202, C_203]: (k3_funct_2('#skF_2', B_202, C_203, '#skF_6')=k1_funct_1(C_203, '#skF_6') | ~m1_subset_1(C_203, k1_zfmisc_1(k2_zfmisc_1('#skF_2', B_202))) | ~v1_funct_2(C_203, '#skF_2', B_202) | ~v1_funct_1(C_203) | v1_xboole_0('#skF_2'))), inference(resolution, [status(thm)], [c_56, c_523])).
% 7.55/2.55  tff(c_543, plain, (![B_202, C_203]: (k3_funct_2('#skF_2', B_202, C_203, '#skF_6')=k1_funct_1(C_203, '#skF_6') | ~m1_subset_1(C_203, k1_zfmisc_1(k2_zfmisc_1('#skF_2', B_202))) | ~v1_funct_2(C_203, '#skF_2', B_202) | ~v1_funct_1(C_203))), inference(negUnitSimplification, [status(thm)], [c_68, c_535])).
% 7.55/2.55  tff(c_2379, plain, (k3_funct_2('#skF_2', '#skF_3', k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), '#skF_6')=k1_funct_1(k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), '#skF_6') | ~v1_funct_2(k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), '#skF_2', '#skF_3') | ~v1_funct_1(k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_2357, c_543])).
% 7.55/2.55  tff(c_2434, plain, (k3_funct_2('#skF_2', '#skF_3', k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), '#skF_6')=k1_funct_1(k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_621, c_816, c_2379])).
% 7.55/2.55  tff(c_547, plain, (![B_214, C_215]: (k3_funct_2('#skF_2', B_214, C_215, '#skF_6')=k1_funct_1(C_215, '#skF_6') | ~m1_subset_1(C_215, k1_zfmisc_1(k2_zfmisc_1('#skF_2', B_214))) | ~v1_funct_2(C_215, '#skF_2', B_214) | ~v1_funct_1(C_215))), inference(negUnitSimplification, [status(thm)], [c_68, c_535])).
% 7.55/2.55  tff(c_562, plain, (k3_funct_2('#skF_2', '#skF_1', '#skF_4', '#skF_6')=k1_funct_1('#skF_4', '#skF_6') | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_62, c_547])).
% 7.55/2.55  tff(c_568, plain, (k3_funct_2('#skF_2', '#skF_1', '#skF_4', '#skF_6')=k1_funct_1('#skF_4', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_562])).
% 7.55/2.55  tff(c_52, plain, (k3_funct_2('#skF_2', '#skF_3', k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), '#skF_6')!=k7_partfun1('#skF_3', '#skF_5', k3_funct_2('#skF_2', '#skF_1', '#skF_4', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_218])).
% 7.55/2.55  tff(c_569, plain, (k3_funct_2('#skF_2', '#skF_3', k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), '#skF_6')!=k7_partfun1('#skF_3', '#skF_5', k1_funct_1('#skF_4', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_568, c_52])).
% 7.55/2.55  tff(c_2458, plain, (k7_partfun1('#skF_3', '#skF_5', k1_funct_1('#skF_4', '#skF_6'))!=k1_funct_1(k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_2434, c_569])).
% 7.55/2.55  tff(c_3948, plain, (k1_funct_1(k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), '#skF_6')!=k1_funct_1('#skF_5', k1_funct_1('#skF_4', '#skF_6')) | ~r2_hidden('#skF_6', '#skF_2') | ~r2_hidden('#skF_6', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_3942, c_2458])).
% 7.55/2.55  tff(c_3954, plain, (~r2_hidden('#skF_6', '#skF_2')), inference(splitLeft, [status(thm)], [c_3948])).
% 7.55/2.55  tff(c_3962, plain, (v1_xboole_0('#skF_2') | ~m1_subset_1('#skF_6', '#skF_2')), inference(resolution, [status(thm)], [c_6, c_3954])).
% 7.55/2.55  tff(c_3965, plain, (v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_3962])).
% 7.55/2.55  tff(c_3967, plain, $false, inference(negUnitSimplification, [status(thm)], [c_68, c_3965])).
% 7.55/2.55  tff(c_3969, plain, (r2_hidden('#skF_6', '#skF_2')), inference(splitRight, [status(thm)], [c_3948])).
% 7.55/2.55  tff(c_3968, plain, (~r2_hidden('#skF_6', '#skF_2') | k1_funct_1(k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), '#skF_6')!=k1_funct_1('#skF_5', k1_funct_1('#skF_4', '#skF_6'))), inference(splitRight, [status(thm)], [c_3948])).
% 7.55/2.55  tff(c_3976, plain, (k1_funct_1(k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), '#skF_6')!=k1_funct_1('#skF_5', k1_funct_1('#skF_4', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_3969, c_3968])).
% 7.55/2.55  tff(c_3979, plain, (~m1_subset_1('#skF_6', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_1896, c_3976])).
% 7.55/2.55  tff(c_3983, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_56, c_3979])).
% 7.55/2.55  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.55/2.55  
% 7.55/2.55  Inference rules
% 7.55/2.55  ----------------------
% 7.55/2.55  #Ref     : 0
% 7.55/2.55  #Sup     : 827
% 7.55/2.55  #Fact    : 0
% 7.55/2.55  #Define  : 0
% 7.55/2.55  #Split   : 20
% 7.55/2.55  #Chain   : 0
% 7.55/2.55  #Close   : 0
% 7.55/2.55  
% 7.55/2.55  Ordering : KBO
% 7.55/2.55  
% 7.55/2.55  Simplification rules
% 7.55/2.55  ----------------------
% 7.55/2.55  #Subsume      : 25
% 7.55/2.55  #Demod        : 362
% 7.55/2.55  #Tautology    : 72
% 7.55/2.55  #SimpNegUnit  : 60
% 7.55/2.55  #BackRed      : 11
% 7.55/2.55  
% 7.55/2.55  #Partial instantiations: 0
% 7.55/2.55  #Strategies tried      : 1
% 7.55/2.55  
% 7.55/2.55  Timing (in seconds)
% 7.55/2.55  ----------------------
% 7.55/2.56  Preprocessing        : 0.39
% 7.55/2.56  Parsing              : 0.21
% 7.55/2.56  CNF conversion       : 0.03
% 7.55/2.56  Main loop            : 1.44
% 7.55/2.56  Inferencing          : 0.45
% 7.55/2.56  Reduction            : 0.44
% 7.55/2.56  Demodulation         : 0.32
% 7.55/2.56  BG Simplification    : 0.06
% 7.55/2.56  Subsumption          : 0.37
% 7.55/2.56  Abstraction          : 0.08
% 7.55/2.56  MUC search           : 0.00
% 7.55/2.56  Cooper               : 0.00
% 7.55/2.56  Total                : 1.90
% 7.55/2.56  Index Insertion      : 0.00
% 7.55/2.56  Index Deletion       : 0.00
% 7.55/2.56  Index Matching       : 0.00
% 7.55/2.56  BG Taut test         : 0.00
%------------------------------------------------------------------------------
