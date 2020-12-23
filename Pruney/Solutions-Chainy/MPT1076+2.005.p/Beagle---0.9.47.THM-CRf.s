%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:18:12 EST 2020

% Result     : Theorem 9.97s
% Output     : CNFRefutation 9.97s
% Verified   : 
% Statistics : Number of formulae       :  157 ( 506 expanded)
%              Number of leaves         :   48 ( 199 expanded)
%              Depth                    :   14
%              Number of atoms          :  451 (2056 expanded)
%              Number of equality atoms :   71 ( 259 expanded)
%              Maximal formula depth    :   17 (   5 average)
%              Maximal term depth       :    3 (   1 average)

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

tff(f_213,negated_conjecture,(
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

tff(f_47,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_39,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_63,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_71,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_186,axiom,(
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

tff(f_114,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => ( v1_partfun1(B,A)
      <=> k1_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_partfun1)).

tff(f_67,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_106,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => ( ( v1_funct_1(C)
              & v1_funct_2(C,A,B) )
           => ( v1_funct_1(C)
              & v1_partfun1(C,A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc5_funct_2)).

tff(f_92,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & v1_xboole_0(B) )
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => ~ v1_partfun1(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_partfun1)).

tff(f_81,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( ( v1_funct_1(C)
          & v1_partfun1(C,A) )
       => ( v1_funct_1(C)
          & v1_funct_2(C,A,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_funct_2)).

tff(f_32,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_57,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v5_relat_1(C,A)
        & v1_funct_1(C) )
     => ( r2_hidden(B,k1_relat_1(C))
       => m1_subset_1(k1_funct_1(C,B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t176_funct_1)).

tff(f_162,axiom,(
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

tff(f_143,axiom,(
    ! [A,B,C,D] :
      ( ( ~ v1_xboole_0(A)
        & v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,A) )
     => k3_funct_2(A,B,C,D) = k1_funct_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k3_funct_2)).

tff(f_130,axiom,(
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

tff(c_54,plain,(
    m1_subset_1('#skF_6','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_213])).

tff(c_12,plain,(
    ! [A_8,B_9] : v1_relat_1(k2_zfmisc_1(A_8,B_9)) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_60,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_213])).

tff(c_71,plain,(
    ! [B_109,A_110] :
      ( v1_relat_1(B_109)
      | ~ m1_subset_1(B_109,k1_zfmisc_1(A_110))
      | ~ v1_relat_1(A_110) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_77,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_1')) ),
    inference(resolution,[status(thm)],[c_60,c_71])).

tff(c_83,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_77])).

tff(c_85,plain,(
    ! [C_113,B_114,A_115] :
      ( v5_relat_1(C_113,B_114)
      | ~ m1_subset_1(C_113,k1_zfmisc_1(k2_zfmisc_1(A_115,B_114))) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_93,plain,(
    v5_relat_1('#skF_4','#skF_1') ),
    inference(resolution,[status(thm)],[c_60,c_85])).

tff(c_10,plain,(
    ! [B_7,A_6] :
      ( r1_tarski(k2_relat_1(B_7),A_6)
      | ~ v5_relat_1(B_7,A_6)
      | ~ v1_relat_1(B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_66,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_213])).

tff(c_68,plain,(
    ~ v1_xboole_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_213])).

tff(c_64,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_213])).

tff(c_62,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_213])).

tff(c_275,plain,(
    ! [A_151,B_152,C_153] :
      ( k2_relset_1(A_151,B_152,C_153) = k2_relat_1(C_153)
      | ~ m1_subset_1(C_153,k1_zfmisc_1(k2_zfmisc_1(A_151,B_152))) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_283,plain,(
    k2_relset_1('#skF_2','#skF_1','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_60,c_275])).

tff(c_985,plain,(
    ! [C_315,E_319,B_317,D_320,A_316,F_318] :
      ( k1_funct_1(k8_funct_2(B_317,C_315,A_316,D_320,E_319),F_318) = k1_funct_1(E_319,k1_funct_1(D_320,F_318))
      | k1_xboole_0 = B_317
      | ~ r1_tarski(k2_relset_1(B_317,C_315,D_320),k1_relset_1(C_315,A_316,E_319))
      | ~ m1_subset_1(F_318,B_317)
      | ~ m1_subset_1(E_319,k1_zfmisc_1(k2_zfmisc_1(C_315,A_316)))
      | ~ v1_funct_1(E_319)
      | ~ m1_subset_1(D_320,k1_zfmisc_1(k2_zfmisc_1(B_317,C_315)))
      | ~ v1_funct_2(D_320,B_317,C_315)
      | ~ v1_funct_1(D_320)
      | v1_xboole_0(C_315) ) ),
    inference(cnfTransformation,[status(thm)],[f_186])).

tff(c_991,plain,(
    ! [A_316,E_319,F_318] :
      ( k1_funct_1(k8_funct_2('#skF_2','#skF_1',A_316,'#skF_4',E_319),F_318) = k1_funct_1(E_319,k1_funct_1('#skF_4',F_318))
      | k1_xboole_0 = '#skF_2'
      | ~ r1_tarski(k2_relat_1('#skF_4'),k1_relset_1('#skF_1',A_316,E_319))
      | ~ m1_subset_1(F_318,'#skF_2')
      | ~ m1_subset_1(E_319,k1_zfmisc_1(k2_zfmisc_1('#skF_1',A_316)))
      | ~ v1_funct_1(E_319)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
      | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
      | ~ v1_funct_1('#skF_4')
      | v1_xboole_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_283,c_985])).

tff(c_1001,plain,(
    ! [A_316,E_319,F_318] :
      ( k1_funct_1(k8_funct_2('#skF_2','#skF_1',A_316,'#skF_4',E_319),F_318) = k1_funct_1(E_319,k1_funct_1('#skF_4',F_318))
      | k1_xboole_0 = '#skF_2'
      | ~ r1_tarski(k2_relat_1('#skF_4'),k1_relset_1('#skF_1',A_316,E_319))
      | ~ m1_subset_1(F_318,'#skF_2')
      | ~ m1_subset_1(E_319,k1_zfmisc_1(k2_zfmisc_1('#skF_1',A_316)))
      | ~ v1_funct_1(E_319)
      | v1_xboole_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_60,c_991])).

tff(c_1002,plain,(
    ! [A_316,E_319,F_318] :
      ( k1_funct_1(k8_funct_2('#skF_2','#skF_1',A_316,'#skF_4',E_319),F_318) = k1_funct_1(E_319,k1_funct_1('#skF_4',F_318))
      | k1_xboole_0 = '#skF_2'
      | ~ r1_tarski(k2_relat_1('#skF_4'),k1_relset_1('#skF_1',A_316,E_319))
      | ~ m1_subset_1(F_318,'#skF_2')
      | ~ m1_subset_1(E_319,k1_zfmisc_1(k2_zfmisc_1('#skF_1',A_316)))
      | ~ v1_funct_1(E_319) ) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_1001])).

tff(c_1549,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_1002])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_1551,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1549,c_2])).

tff(c_1553,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_1551])).

tff(c_1555,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(splitRight,[status(thm)],[c_1002])).

tff(c_58,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_213])).

tff(c_56,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_213])).

tff(c_74,plain,
    ( v1_relat_1('#skF_5')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_3')) ),
    inference(resolution,[status(thm)],[c_56,c_71])).

tff(c_80,plain,(
    v1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_74])).

tff(c_52,plain,(
    v1_partfun1('#skF_5','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_213])).

tff(c_94,plain,(
    ! [C_116,A_117,B_118] :
      ( v4_relat_1(C_116,A_117)
      | ~ m1_subset_1(C_116,k1_zfmisc_1(k2_zfmisc_1(A_117,B_118))) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_101,plain,(
    v4_relat_1('#skF_5','#skF_1') ),
    inference(resolution,[status(thm)],[c_56,c_94])).

tff(c_109,plain,(
    ! [B_122,A_123] :
      ( k1_relat_1(B_122) = A_123
      | ~ v1_partfun1(B_122,A_123)
      | ~ v4_relat_1(B_122,A_123)
      | ~ v1_relat_1(B_122) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_115,plain,
    ( k1_relat_1('#skF_5') = '#skF_1'
    | ~ v1_partfun1('#skF_5','#skF_1')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_101,c_109])).

tff(c_121,plain,(
    k1_relat_1('#skF_5') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_52,c_115])).

tff(c_292,plain,(
    ! [A_154,B_155,C_156] :
      ( k1_relset_1(A_154,B_155,C_156) = k1_relat_1(C_156)
      | ~ m1_subset_1(C_156,k1_zfmisc_1(k2_zfmisc_1(A_154,B_155))) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_295,plain,(
    k1_relset_1('#skF_1','#skF_3','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_56,c_292])).

tff(c_300,plain,(
    k1_relset_1('#skF_1','#skF_3','#skF_5') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_121,c_295])).

tff(c_989,plain,(
    ! [B_317,D_320,F_318] :
      ( k1_funct_1(k8_funct_2(B_317,'#skF_1','#skF_3',D_320,'#skF_5'),F_318) = k1_funct_1('#skF_5',k1_funct_1(D_320,F_318))
      | k1_xboole_0 = B_317
      | ~ r1_tarski(k2_relset_1(B_317,'#skF_1',D_320),'#skF_1')
      | ~ m1_subset_1(F_318,B_317)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3')))
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1(D_320,k1_zfmisc_1(k2_zfmisc_1(B_317,'#skF_1')))
      | ~ v1_funct_2(D_320,B_317,'#skF_1')
      | ~ v1_funct_1(D_320)
      | v1_xboole_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_300,c_985])).

tff(c_998,plain,(
    ! [B_317,D_320,F_318] :
      ( k1_funct_1(k8_funct_2(B_317,'#skF_1','#skF_3',D_320,'#skF_5'),F_318) = k1_funct_1('#skF_5',k1_funct_1(D_320,F_318))
      | k1_xboole_0 = B_317
      | ~ r1_tarski(k2_relset_1(B_317,'#skF_1',D_320),'#skF_1')
      | ~ m1_subset_1(F_318,B_317)
      | ~ m1_subset_1(D_320,k1_zfmisc_1(k2_zfmisc_1(B_317,'#skF_1')))
      | ~ v1_funct_2(D_320,B_317,'#skF_1')
      | ~ v1_funct_1(D_320)
      | v1_xboole_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_989])).

tff(c_1757,plain,(
    ! [B_423,D_424,F_425] :
      ( k1_funct_1(k8_funct_2(B_423,'#skF_1','#skF_3',D_424,'#skF_5'),F_425) = k1_funct_1('#skF_5',k1_funct_1(D_424,F_425))
      | k1_xboole_0 = B_423
      | ~ r1_tarski(k2_relset_1(B_423,'#skF_1',D_424),'#skF_1')
      | ~ m1_subset_1(F_425,B_423)
      | ~ m1_subset_1(D_424,k1_zfmisc_1(k2_zfmisc_1(B_423,'#skF_1')))
      | ~ v1_funct_2(D_424,B_423,'#skF_1')
      | ~ v1_funct_1(D_424) ) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_998])).

tff(c_1774,plain,(
    ! [F_425] :
      ( k1_funct_1(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),F_425) = k1_funct_1('#skF_5',k1_funct_1('#skF_4',F_425))
      | k1_xboole_0 = '#skF_2'
      | ~ r1_tarski(k2_relset_1('#skF_2','#skF_1','#skF_4'),'#skF_1')
      | ~ m1_subset_1(F_425,'#skF_2')
      | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_60,c_1757])).

tff(c_1782,plain,(
    ! [F_425] :
      ( k1_funct_1(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),F_425) = k1_funct_1('#skF_5',k1_funct_1('#skF_4',F_425))
      | k1_xboole_0 = '#skF_2'
      | ~ r1_tarski(k2_relat_1('#skF_4'),'#skF_1')
      | ~ m1_subset_1(F_425,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_283,c_1774])).

tff(c_1783,plain,(
    ! [F_425] :
      ( k1_funct_1(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),F_425) = k1_funct_1('#skF_5',k1_funct_1('#skF_4',F_425))
      | ~ r1_tarski(k2_relat_1('#skF_4'),'#skF_1')
      | ~ m1_subset_1(F_425,'#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_1555,c_1782])).

tff(c_1784,plain,(
    ~ r1_tarski(k2_relat_1('#skF_4'),'#skF_1') ),
    inference(splitLeft,[status(thm)],[c_1783])).

tff(c_1787,plain,
    ( ~ v5_relat_1('#skF_4','#skF_1')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_10,c_1784])).

tff(c_1791,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_83,c_93,c_1787])).

tff(c_1792,plain,(
    ! [F_425] :
      ( k1_funct_1(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),F_425) = k1_funct_1('#skF_5',k1_funct_1('#skF_4',F_425))
      | ~ m1_subset_1(F_425,'#skF_2') ) ),
    inference(splitRight,[status(thm)],[c_1783])).

tff(c_102,plain,(
    v4_relat_1('#skF_4','#skF_2') ),
    inference(resolution,[status(thm)],[c_60,c_94])).

tff(c_112,plain,
    ( k1_relat_1('#skF_4') = '#skF_2'
    | ~ v1_partfun1('#skF_4','#skF_2')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_102,c_109])).

tff(c_118,plain,
    ( k1_relat_1('#skF_4') = '#skF_2'
    | ~ v1_partfun1('#skF_4','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_83,c_112])).

tff(c_131,plain,(
    ~ v1_partfun1('#skF_4','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_118])).

tff(c_242,plain,(
    ! [C_148,A_149,B_150] :
      ( v1_partfun1(C_148,A_149)
      | ~ v1_funct_2(C_148,A_149,B_150)
      | ~ v1_funct_1(C_148)
      | ~ m1_subset_1(C_148,k1_zfmisc_1(k2_zfmisc_1(A_149,B_150)))
      | v1_xboole_0(B_150) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_252,plain,
    ( v1_partfun1('#skF_4','#skF_2')
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4')
    | v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_60,c_242])).

tff(c_260,plain,
    ( v1_partfun1('#skF_4','#skF_2')
    | v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_252])).

tff(c_262,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_131,c_260])).

tff(c_263,plain,(
    k1_relat_1('#skF_4') = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_118])).

tff(c_311,plain,(
    ! [C_157,A_158,B_159] :
      ( ~ v1_partfun1(C_157,A_158)
      | ~ m1_subset_1(C_157,k1_zfmisc_1(k2_zfmisc_1(A_158,B_159)))
      | ~ v1_xboole_0(B_159)
      | v1_xboole_0(A_158) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_314,plain,
    ( ~ v1_partfun1('#skF_5','#skF_1')
    | ~ v1_xboole_0('#skF_3')
    | v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_56,c_311])).

tff(c_320,plain,
    ( ~ v1_xboole_0('#skF_3')
    | v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_314])).

tff(c_321,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_320])).

tff(c_326,plain,(
    ! [C_160,A_161,B_162] :
      ( v1_funct_2(C_160,A_161,B_162)
      | ~ v1_partfun1(C_160,A_161)
      | ~ v1_funct_1(C_160)
      | ~ m1_subset_1(C_160,k1_zfmisc_1(k2_zfmisc_1(A_161,B_162))) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_329,plain,
    ( v1_funct_2('#skF_5','#skF_1','#skF_3')
    | ~ v1_partfun1('#skF_5','#skF_1')
    | ~ v1_funct_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_56,c_326])).

tff(c_335,plain,(
    v1_funct_2('#skF_5','#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_52,c_329])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( r2_hidden(A_1,B_2)
      | v1_xboole_0(B_2)
      | ~ m1_subset_1(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_339,plain,(
    ! [C_163,B_164,A_165] :
      ( m1_subset_1(k1_funct_1(C_163,B_164),A_165)
      | ~ r2_hidden(B_164,k1_relat_1(C_163))
      | ~ v1_funct_1(C_163)
      | ~ v5_relat_1(C_163,A_165)
      | ~ v1_relat_1(C_163) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_351,plain,(
    ! [C_163,A_1,A_165] :
      ( m1_subset_1(k1_funct_1(C_163,A_1),A_165)
      | ~ v1_funct_1(C_163)
      | ~ v5_relat_1(C_163,A_165)
      | ~ v1_relat_1(C_163)
      | v1_xboole_0(k1_relat_1(C_163))
      | ~ m1_subset_1(A_1,k1_relat_1(C_163)) ) ),
    inference(resolution,[status(thm)],[c_4,c_339])).

tff(c_621,plain,(
    ! [A_247,B_248,C_249,D_250] :
      ( k3_funct_2(A_247,B_248,C_249,D_250) = k7_partfun1(B_248,C_249,D_250)
      | ~ m1_subset_1(D_250,A_247)
      | ~ m1_subset_1(C_249,k1_zfmisc_1(k2_zfmisc_1(A_247,B_248)))
      | ~ v1_funct_2(C_249,A_247,B_248)
      | ~ v1_funct_1(C_249)
      | v1_xboole_0(B_248)
      | v1_xboole_0(A_247) ) ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_3417,plain,(
    ! [C_778,B_779,A_780,C_777,A_781] :
      ( k3_funct_2(A_780,B_779,C_777,k1_funct_1(C_778,A_781)) = k7_partfun1(B_779,C_777,k1_funct_1(C_778,A_781))
      | ~ m1_subset_1(C_777,k1_zfmisc_1(k2_zfmisc_1(A_780,B_779)))
      | ~ v1_funct_2(C_777,A_780,B_779)
      | ~ v1_funct_1(C_777)
      | v1_xboole_0(B_779)
      | v1_xboole_0(A_780)
      | ~ v1_funct_1(C_778)
      | ~ v5_relat_1(C_778,A_780)
      | ~ v1_relat_1(C_778)
      | v1_xboole_0(k1_relat_1(C_778))
      | ~ m1_subset_1(A_781,k1_relat_1(C_778)) ) ),
    inference(resolution,[status(thm)],[c_351,c_621])).

tff(c_3436,plain,(
    ! [C_778,A_781] :
      ( k3_funct_2('#skF_1','#skF_3','#skF_5',k1_funct_1(C_778,A_781)) = k7_partfun1('#skF_3','#skF_5',k1_funct_1(C_778,A_781))
      | ~ v1_funct_2('#skF_5','#skF_1','#skF_3')
      | ~ v1_funct_1('#skF_5')
      | v1_xboole_0('#skF_3')
      | v1_xboole_0('#skF_1')
      | ~ v1_funct_1(C_778)
      | ~ v5_relat_1(C_778,'#skF_1')
      | ~ v1_relat_1(C_778)
      | v1_xboole_0(k1_relat_1(C_778))
      | ~ m1_subset_1(A_781,k1_relat_1(C_778)) ) ),
    inference(resolution,[status(thm)],[c_56,c_3417])).

tff(c_3447,plain,(
    ! [C_778,A_781] :
      ( k3_funct_2('#skF_1','#skF_3','#skF_5',k1_funct_1(C_778,A_781)) = k7_partfun1('#skF_3','#skF_5',k1_funct_1(C_778,A_781))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0('#skF_1')
      | ~ v1_funct_1(C_778)
      | ~ v5_relat_1(C_778,'#skF_1')
      | ~ v1_relat_1(C_778)
      | v1_xboole_0(k1_relat_1(C_778))
      | ~ m1_subset_1(A_781,k1_relat_1(C_778)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_335,c_3436])).

tff(c_3453,plain,(
    ! [C_782,A_783] :
      ( k3_funct_2('#skF_1','#skF_3','#skF_5',k1_funct_1(C_782,A_783)) = k7_partfun1('#skF_3','#skF_5',k1_funct_1(C_782,A_783))
      | ~ v1_funct_1(C_782)
      | ~ v5_relat_1(C_782,'#skF_1')
      | ~ v1_relat_1(C_782)
      | v1_xboole_0(k1_relat_1(C_782))
      | ~ m1_subset_1(A_783,k1_relat_1(C_782)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_321,c_3447])).

tff(c_3479,plain,(
    ! [A_783] :
      ( k3_funct_2('#skF_1','#skF_3','#skF_5',k1_funct_1('#skF_4',A_783)) = k7_partfun1('#skF_3','#skF_5',k1_funct_1('#skF_4',A_783))
      | ~ v1_funct_1('#skF_4')
      | ~ v5_relat_1('#skF_4','#skF_1')
      | ~ v1_relat_1('#skF_4')
      | v1_xboole_0(k1_relat_1('#skF_4'))
      | ~ m1_subset_1(A_783,'#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_263,c_3453])).

tff(c_3492,plain,(
    ! [A_783] :
      ( k3_funct_2('#skF_1','#skF_3','#skF_5',k1_funct_1('#skF_4',A_783)) = k7_partfun1('#skF_3','#skF_5',k1_funct_1('#skF_4',A_783))
      | v1_xboole_0('#skF_2')
      | ~ m1_subset_1(A_783,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_263,c_83,c_93,c_64,c_3479])).

tff(c_3497,plain,(
    ! [A_784] :
      ( k3_funct_2('#skF_1','#skF_3','#skF_5',k1_funct_1('#skF_4',A_784)) = k7_partfun1('#skF_3','#skF_5',k1_funct_1('#skF_4',A_784))
      | ~ m1_subset_1(A_784,'#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_3492])).

tff(c_501,plain,(
    ! [A_199,B_200,C_201,D_202] :
      ( k3_funct_2(A_199,B_200,C_201,D_202) = k1_funct_1(C_201,D_202)
      | ~ m1_subset_1(D_202,A_199)
      | ~ m1_subset_1(C_201,k1_zfmisc_1(k2_zfmisc_1(A_199,B_200)))
      | ~ v1_funct_2(C_201,A_199,B_200)
      | ~ v1_funct_1(C_201)
      | v1_xboole_0(A_199) ) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_2931,plain,(
    ! [A_692,B_690,A_693,C_691,C_694] :
      ( k3_funct_2(A_692,B_690,C_694,k1_funct_1(C_691,A_693)) = k1_funct_1(C_694,k1_funct_1(C_691,A_693))
      | ~ m1_subset_1(C_694,k1_zfmisc_1(k2_zfmisc_1(A_692,B_690)))
      | ~ v1_funct_2(C_694,A_692,B_690)
      | ~ v1_funct_1(C_694)
      | v1_xboole_0(A_692)
      | ~ v1_funct_1(C_691)
      | ~ v5_relat_1(C_691,A_692)
      | ~ v1_relat_1(C_691)
      | v1_xboole_0(k1_relat_1(C_691))
      | ~ m1_subset_1(A_693,k1_relat_1(C_691)) ) ),
    inference(resolution,[status(thm)],[c_351,c_501])).

tff(c_2950,plain,(
    ! [C_691,A_693] :
      ( k3_funct_2('#skF_1','#skF_3','#skF_5',k1_funct_1(C_691,A_693)) = k1_funct_1('#skF_5',k1_funct_1(C_691,A_693))
      | ~ v1_funct_2('#skF_5','#skF_1','#skF_3')
      | ~ v1_funct_1('#skF_5')
      | v1_xboole_0('#skF_1')
      | ~ v1_funct_1(C_691)
      | ~ v5_relat_1(C_691,'#skF_1')
      | ~ v1_relat_1(C_691)
      | v1_xboole_0(k1_relat_1(C_691))
      | ~ m1_subset_1(A_693,k1_relat_1(C_691)) ) ),
    inference(resolution,[status(thm)],[c_56,c_2931])).

tff(c_2961,plain,(
    ! [C_691,A_693] :
      ( k3_funct_2('#skF_1','#skF_3','#skF_5',k1_funct_1(C_691,A_693)) = k1_funct_1('#skF_5',k1_funct_1(C_691,A_693))
      | v1_xboole_0('#skF_1')
      | ~ v1_funct_1(C_691)
      | ~ v5_relat_1(C_691,'#skF_1')
      | ~ v1_relat_1(C_691)
      | v1_xboole_0(k1_relat_1(C_691))
      | ~ m1_subset_1(A_693,k1_relat_1(C_691)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_335,c_2950])).

tff(c_2967,plain,(
    ! [C_695,A_696] :
      ( k3_funct_2('#skF_1','#skF_3','#skF_5',k1_funct_1(C_695,A_696)) = k1_funct_1('#skF_5',k1_funct_1(C_695,A_696))
      | ~ v1_funct_1(C_695)
      | ~ v5_relat_1(C_695,'#skF_1')
      | ~ v1_relat_1(C_695)
      | v1_xboole_0(k1_relat_1(C_695))
      | ~ m1_subset_1(A_696,k1_relat_1(C_695)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_2961])).

tff(c_2993,plain,(
    ! [A_696] :
      ( k3_funct_2('#skF_1','#skF_3','#skF_5',k1_funct_1('#skF_4',A_696)) = k1_funct_1('#skF_5',k1_funct_1('#skF_4',A_696))
      | ~ v1_funct_1('#skF_4')
      | ~ v5_relat_1('#skF_4','#skF_1')
      | ~ v1_relat_1('#skF_4')
      | v1_xboole_0(k1_relat_1('#skF_4'))
      | ~ m1_subset_1(A_696,'#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_263,c_2967])).

tff(c_3006,plain,(
    ! [A_696] :
      ( k3_funct_2('#skF_1','#skF_3','#skF_5',k1_funct_1('#skF_4',A_696)) = k1_funct_1('#skF_5',k1_funct_1('#skF_4',A_696))
      | v1_xboole_0('#skF_2')
      | ~ m1_subset_1(A_696,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_263,c_83,c_93,c_64,c_2993])).

tff(c_3007,plain,(
    ! [A_696] :
      ( k3_funct_2('#skF_1','#skF_3','#skF_5',k1_funct_1('#skF_4',A_696)) = k1_funct_1('#skF_5',k1_funct_1('#skF_4',A_696))
      | ~ m1_subset_1(A_696,'#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_3006])).

tff(c_3511,plain,(
    ! [A_784] :
      ( k7_partfun1('#skF_3','#skF_5',k1_funct_1('#skF_4',A_784)) = k1_funct_1('#skF_5',k1_funct_1('#skF_4',A_784))
      | ~ m1_subset_1(A_784,'#skF_2')
      | ~ m1_subset_1(A_784,'#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3497,c_3007])).

tff(c_555,plain,(
    ! [E_227,D_228,C_226,A_225,B_229] :
      ( v1_funct_1(k8_funct_2(A_225,B_229,C_226,D_228,E_227))
      | ~ m1_subset_1(E_227,k1_zfmisc_1(k2_zfmisc_1(B_229,C_226)))
      | ~ v1_funct_1(E_227)
      | ~ m1_subset_1(D_228,k1_zfmisc_1(k2_zfmisc_1(A_225,B_229)))
      | ~ v1_funct_2(D_228,A_225,B_229)
      | ~ v1_funct_1(D_228) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_566,plain,(
    ! [A_225,D_228] :
      ( v1_funct_1(k8_funct_2(A_225,'#skF_1','#skF_3',D_228,'#skF_5'))
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1(D_228,k1_zfmisc_1(k2_zfmisc_1(A_225,'#skF_1')))
      | ~ v1_funct_2(D_228,A_225,'#skF_1')
      | ~ v1_funct_1(D_228) ) ),
    inference(resolution,[status(thm)],[c_56,c_555])).

tff(c_578,plain,(
    ! [A_230,D_231] :
      ( v1_funct_1(k8_funct_2(A_230,'#skF_1','#skF_3',D_231,'#skF_5'))
      | ~ m1_subset_1(D_231,k1_zfmisc_1(k2_zfmisc_1(A_230,'#skF_1')))
      | ~ v1_funct_2(D_231,A_230,'#skF_1')
      | ~ v1_funct_1(D_231) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_566])).

tff(c_593,plain,
    ( v1_funct_1(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_60,c_578])).

tff(c_599,plain,(
    v1_funct_1(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_593])).

tff(c_676,plain,(
    ! [A_268,E_270,C_269,D_271,B_272] :
      ( v1_funct_2(k8_funct_2(A_268,B_272,C_269,D_271,E_270),A_268,C_269)
      | ~ m1_subset_1(E_270,k1_zfmisc_1(k2_zfmisc_1(B_272,C_269)))
      | ~ v1_funct_1(E_270)
      | ~ m1_subset_1(D_271,k1_zfmisc_1(k2_zfmisc_1(A_268,B_272)))
      | ~ v1_funct_2(D_271,A_268,B_272)
      | ~ v1_funct_1(D_271) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_687,plain,(
    ! [A_268,D_271] :
      ( v1_funct_2(k8_funct_2(A_268,'#skF_1','#skF_3',D_271,'#skF_5'),A_268,'#skF_3')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1(D_271,k1_zfmisc_1(k2_zfmisc_1(A_268,'#skF_1')))
      | ~ v1_funct_2(D_271,A_268,'#skF_1')
      | ~ v1_funct_1(D_271) ) ),
    inference(resolution,[status(thm)],[c_56,c_676])).

tff(c_699,plain,(
    ! [A_273,D_274] :
      ( v1_funct_2(k8_funct_2(A_273,'#skF_1','#skF_3',D_274,'#skF_5'),A_273,'#skF_3')
      | ~ m1_subset_1(D_274,k1_zfmisc_1(k2_zfmisc_1(A_273,'#skF_1')))
      | ~ v1_funct_2(D_274,A_273,'#skF_1')
      | ~ v1_funct_1(D_274) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_687])).

tff(c_710,plain,
    ( v1_funct_2(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),'#skF_2','#skF_3')
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_60,c_699])).

tff(c_716,plain,(
    v1_funct_2(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),'#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_710])).

tff(c_736,plain,(
    ! [C_288,E_289,B_291,D_290,A_287] :
      ( m1_subset_1(k8_funct_2(A_287,B_291,C_288,D_290,E_289),k1_zfmisc_1(k2_zfmisc_1(A_287,C_288)))
      | ~ m1_subset_1(E_289,k1_zfmisc_1(k2_zfmisc_1(B_291,C_288)))
      | ~ v1_funct_1(E_289)
      | ~ m1_subset_1(D_290,k1_zfmisc_1(k2_zfmisc_1(A_287,B_291)))
      | ~ v1_funct_2(D_290,A_287,B_291)
      | ~ v1_funct_1(D_290) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_513,plain,(
    ! [B_200,C_201] :
      ( k3_funct_2('#skF_2',B_200,C_201,'#skF_6') = k1_funct_1(C_201,'#skF_6')
      | ~ m1_subset_1(C_201,k1_zfmisc_1(k2_zfmisc_1('#skF_2',B_200)))
      | ~ v1_funct_2(C_201,'#skF_2',B_200)
      | ~ v1_funct_1(C_201)
      | v1_xboole_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_54,c_501])).

tff(c_521,plain,(
    ! [B_200,C_201] :
      ( k3_funct_2('#skF_2',B_200,C_201,'#skF_6') = k1_funct_1(C_201,'#skF_6')
      | ~ m1_subset_1(C_201,k1_zfmisc_1(k2_zfmisc_1('#skF_2',B_200)))
      | ~ v1_funct_2(C_201,'#skF_2',B_200)
      | ~ v1_funct_1(C_201) ) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_513])).

tff(c_6608,plain,(
    ! [C_1119,B_1120,D_1121,E_1122] :
      ( k3_funct_2('#skF_2',C_1119,k8_funct_2('#skF_2',B_1120,C_1119,D_1121,E_1122),'#skF_6') = k1_funct_1(k8_funct_2('#skF_2',B_1120,C_1119,D_1121,E_1122),'#skF_6')
      | ~ v1_funct_2(k8_funct_2('#skF_2',B_1120,C_1119,D_1121,E_1122),'#skF_2',C_1119)
      | ~ v1_funct_1(k8_funct_2('#skF_2',B_1120,C_1119,D_1121,E_1122))
      | ~ m1_subset_1(E_1122,k1_zfmisc_1(k2_zfmisc_1(B_1120,C_1119)))
      | ~ v1_funct_1(E_1122)
      | ~ m1_subset_1(D_1121,k1_zfmisc_1(k2_zfmisc_1('#skF_2',B_1120)))
      | ~ v1_funct_2(D_1121,'#skF_2',B_1120)
      | ~ v1_funct_1(D_1121) ) ),
    inference(resolution,[status(thm)],[c_736,c_521])).

tff(c_6664,plain,
    ( k3_funct_2('#skF_2','#skF_3',k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),'#skF_6') = k1_funct_1(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),'#skF_6')
    | ~ v1_funct_1(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3')))
    | ~ v1_funct_1('#skF_5')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_716,c_6608])).

tff(c_6709,plain,(
    k3_funct_2('#skF_2','#skF_3',k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),'#skF_6') = k1_funct_1(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_60,c_58,c_56,c_599,c_6664])).

tff(c_525,plain,(
    ! [B_212,C_213] :
      ( k3_funct_2('#skF_2',B_212,C_213,'#skF_6') = k1_funct_1(C_213,'#skF_6')
      | ~ m1_subset_1(C_213,k1_zfmisc_1(k2_zfmisc_1('#skF_2',B_212)))
      | ~ v1_funct_2(C_213,'#skF_2',B_212)
      | ~ v1_funct_1(C_213) ) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_513])).

tff(c_540,plain,
    ( k3_funct_2('#skF_2','#skF_1','#skF_4','#skF_6') = k1_funct_1('#skF_4','#skF_6')
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_60,c_525])).

tff(c_546,plain,(
    k3_funct_2('#skF_2','#skF_1','#skF_4','#skF_6') = k1_funct_1('#skF_4','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_540])).

tff(c_50,plain,(
    k3_funct_2('#skF_2','#skF_3',k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),'#skF_6') != k7_partfun1('#skF_3','#skF_5',k3_funct_2('#skF_2','#skF_1','#skF_4','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_213])).

tff(c_547,plain,(
    k3_funct_2('#skF_2','#skF_3',k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),'#skF_6') != k7_partfun1('#skF_3','#skF_5',k1_funct_1('#skF_4','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_546,c_50])).

tff(c_6710,plain,(
    k7_partfun1('#skF_3','#skF_5',k1_funct_1('#skF_4','#skF_6')) != k1_funct_1(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6709,c_547])).

tff(c_6717,plain,
    ( k1_funct_1(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),'#skF_6') != k1_funct_1('#skF_5',k1_funct_1('#skF_4','#skF_6'))
    | ~ m1_subset_1('#skF_6','#skF_2')
    | ~ m1_subset_1('#skF_6','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_3511,c_6710])).

tff(c_6725,plain,(
    k1_funct_1(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),'#skF_6') != k1_funct_1('#skF_5',k1_funct_1('#skF_4','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_54,c_6717])).

tff(c_6730,plain,(
    ~ m1_subset_1('#skF_6','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_1792,c_6725])).

tff(c_6734,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_6730])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n023.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 15:13:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 9.97/3.90  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.97/3.91  
% 9.97/3.91  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.97/3.91  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k8_funct_2 > k3_funct_2 > k7_partfun1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 9.97/3.91  
% 9.97/3.91  %Foreground sorts:
% 9.97/3.91  
% 9.97/3.91  
% 9.97/3.91  %Background operators:
% 9.97/3.91  
% 9.97/3.91  
% 9.97/3.91  %Foreground operators:
% 9.97/3.91  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 9.97/3.91  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 9.97/3.91  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 9.97/3.91  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 9.97/3.91  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 9.97/3.91  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 9.97/3.91  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 9.97/3.91  tff(k7_partfun1, type, k7_partfun1: ($i * $i * $i) > $i).
% 9.97/3.91  tff('#skF_5', type, '#skF_5': $i).
% 9.97/3.91  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 9.97/3.91  tff(k8_funct_2, type, k8_funct_2: ($i * $i * $i * $i * $i) > $i).
% 9.97/3.91  tff('#skF_6', type, '#skF_6': $i).
% 9.97/3.91  tff('#skF_2', type, '#skF_2': $i).
% 9.97/3.91  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 9.97/3.91  tff('#skF_3', type, '#skF_3': $i).
% 9.97/3.91  tff('#skF_1', type, '#skF_1': $i).
% 9.97/3.91  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 9.97/3.91  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 9.97/3.91  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 9.97/3.91  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 9.97/3.91  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 9.97/3.91  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 9.97/3.91  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 9.97/3.91  tff('#skF_4', type, '#skF_4': $i).
% 9.97/3.91  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 9.97/3.91  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 9.97/3.91  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 9.97/3.91  tff(k3_funct_2, type, k3_funct_2: ($i * $i * $i * $i) > $i).
% 9.97/3.91  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 9.97/3.91  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 9.97/3.91  
% 9.97/3.94  tff(f_213, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C, D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (![E]: ((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, C)))) => (![F]: (m1_subset_1(F, B) => (v1_partfun1(E, A) => (k3_funct_2(B, C, k8_funct_2(B, A, C, D, E), F) = k7_partfun1(C, E, k3_funct_2(B, A, D, F)))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t193_funct_2)).
% 9.97/3.94  tff(f_47, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 9.97/3.94  tff(f_39, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 9.97/3.94  tff(f_63, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 9.97/3.94  tff(f_45, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 9.97/3.94  tff(f_71, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 9.97/3.94  tff(f_186, axiom, (![A, B, C]: (~v1_xboole_0(C) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, C)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (![E]: ((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(C, A)))) => (![F]: (m1_subset_1(F, B) => (r1_tarski(k2_relset_1(B, C, D), k1_relset_1(C, A, E)) => ((B = k1_xboole_0) | (k1_funct_1(k8_funct_2(B, C, A, D, E), F) = k1_funct_1(E, k1_funct_1(D, F))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t185_funct_2)).
% 9.97/3.94  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 9.97/3.94  tff(f_114, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (v1_partfun1(B, A) <=> (k1_relat_1(B) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_partfun1)).
% 9.97/3.94  tff(f_67, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 9.97/3.94  tff(f_106, axiom, (![A, B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) => (v1_funct_1(C) & v1_partfun1(C, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc5_funct_2)).
% 9.97/3.94  tff(f_92, axiom, (![A, B]: ((~v1_xboole_0(A) & v1_xboole_0(B)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ~v1_partfun1(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_partfun1)).
% 9.97/3.94  tff(f_81, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v1_partfun1(C, A)) => (v1_funct_1(C) & v1_funct_2(C, A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_funct_2)).
% 9.97/3.94  tff(f_32, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 9.97/3.94  tff(f_57, axiom, (![A, B, C]: (((v1_relat_1(C) & v5_relat_1(C, A)) & v1_funct_1(C)) => (r2_hidden(B, k1_relat_1(C)) => m1_subset_1(k1_funct_1(C, B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t176_funct_1)).
% 9.97/3.94  tff(f_162, axiom, (![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (m1_subset_1(D, A) => (k7_partfun1(B, C, D) = k3_funct_2(A, B, C, D)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t176_funct_2)).
% 9.97/3.94  tff(f_143, axiom, (![A, B, C, D]: (((((~v1_xboole_0(A) & v1_funct_1(C)) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & m1_subset_1(D, A)) => (k3_funct_2(A, B, C, D) = k1_funct_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k3_funct_2)).
% 9.97/3.94  tff(f_130, axiom, (![A, B, C, D, E]: (((((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(E)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => ((v1_funct_1(k8_funct_2(A, B, C, D, E)) & v1_funct_2(k8_funct_2(A, B, C, D, E), A, C)) & m1_subset_1(k8_funct_2(A, B, C, D, E), k1_zfmisc_1(k2_zfmisc_1(A, C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k8_funct_2)).
% 9.97/3.94  tff(c_54, plain, (m1_subset_1('#skF_6', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_213])).
% 9.97/3.94  tff(c_12, plain, (![A_8, B_9]: (v1_relat_1(k2_zfmisc_1(A_8, B_9)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 9.97/3.94  tff(c_60, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_213])).
% 9.97/3.94  tff(c_71, plain, (![B_109, A_110]: (v1_relat_1(B_109) | ~m1_subset_1(B_109, k1_zfmisc_1(A_110)) | ~v1_relat_1(A_110))), inference(cnfTransformation, [status(thm)], [f_39])).
% 9.97/3.94  tff(c_77, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_1'))), inference(resolution, [status(thm)], [c_60, c_71])).
% 9.97/3.94  tff(c_83, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_12, c_77])).
% 9.97/3.94  tff(c_85, plain, (![C_113, B_114, A_115]: (v5_relat_1(C_113, B_114) | ~m1_subset_1(C_113, k1_zfmisc_1(k2_zfmisc_1(A_115, B_114))))), inference(cnfTransformation, [status(thm)], [f_63])).
% 9.97/3.94  tff(c_93, plain, (v5_relat_1('#skF_4', '#skF_1')), inference(resolution, [status(thm)], [c_60, c_85])).
% 9.97/3.94  tff(c_10, plain, (![B_7, A_6]: (r1_tarski(k2_relat_1(B_7), A_6) | ~v5_relat_1(B_7, A_6) | ~v1_relat_1(B_7))), inference(cnfTransformation, [status(thm)], [f_45])).
% 9.97/3.94  tff(c_66, plain, (~v1_xboole_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_213])).
% 9.97/3.94  tff(c_68, plain, (~v1_xboole_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_213])).
% 9.97/3.94  tff(c_64, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_213])).
% 9.97/3.94  tff(c_62, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_213])).
% 9.97/3.94  tff(c_275, plain, (![A_151, B_152, C_153]: (k2_relset_1(A_151, B_152, C_153)=k2_relat_1(C_153) | ~m1_subset_1(C_153, k1_zfmisc_1(k2_zfmisc_1(A_151, B_152))))), inference(cnfTransformation, [status(thm)], [f_71])).
% 9.97/3.94  tff(c_283, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_60, c_275])).
% 9.97/3.94  tff(c_985, plain, (![C_315, E_319, B_317, D_320, A_316, F_318]: (k1_funct_1(k8_funct_2(B_317, C_315, A_316, D_320, E_319), F_318)=k1_funct_1(E_319, k1_funct_1(D_320, F_318)) | k1_xboole_0=B_317 | ~r1_tarski(k2_relset_1(B_317, C_315, D_320), k1_relset_1(C_315, A_316, E_319)) | ~m1_subset_1(F_318, B_317) | ~m1_subset_1(E_319, k1_zfmisc_1(k2_zfmisc_1(C_315, A_316))) | ~v1_funct_1(E_319) | ~m1_subset_1(D_320, k1_zfmisc_1(k2_zfmisc_1(B_317, C_315))) | ~v1_funct_2(D_320, B_317, C_315) | ~v1_funct_1(D_320) | v1_xboole_0(C_315))), inference(cnfTransformation, [status(thm)], [f_186])).
% 9.97/3.94  tff(c_991, plain, (![A_316, E_319, F_318]: (k1_funct_1(k8_funct_2('#skF_2', '#skF_1', A_316, '#skF_4', E_319), F_318)=k1_funct_1(E_319, k1_funct_1('#skF_4', F_318)) | k1_xboole_0='#skF_2' | ~r1_tarski(k2_relat_1('#skF_4'), k1_relset_1('#skF_1', A_316, E_319)) | ~m1_subset_1(F_318, '#skF_2') | ~m1_subset_1(E_319, k1_zfmisc_1(k2_zfmisc_1('#skF_1', A_316))) | ~v1_funct_1(E_319) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4') | v1_xboole_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_283, c_985])).
% 9.97/3.94  tff(c_1001, plain, (![A_316, E_319, F_318]: (k1_funct_1(k8_funct_2('#skF_2', '#skF_1', A_316, '#skF_4', E_319), F_318)=k1_funct_1(E_319, k1_funct_1('#skF_4', F_318)) | k1_xboole_0='#skF_2' | ~r1_tarski(k2_relat_1('#skF_4'), k1_relset_1('#skF_1', A_316, E_319)) | ~m1_subset_1(F_318, '#skF_2') | ~m1_subset_1(E_319, k1_zfmisc_1(k2_zfmisc_1('#skF_1', A_316))) | ~v1_funct_1(E_319) | v1_xboole_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_60, c_991])).
% 9.97/3.94  tff(c_1002, plain, (![A_316, E_319, F_318]: (k1_funct_1(k8_funct_2('#skF_2', '#skF_1', A_316, '#skF_4', E_319), F_318)=k1_funct_1(E_319, k1_funct_1('#skF_4', F_318)) | k1_xboole_0='#skF_2' | ~r1_tarski(k2_relat_1('#skF_4'), k1_relset_1('#skF_1', A_316, E_319)) | ~m1_subset_1(F_318, '#skF_2') | ~m1_subset_1(E_319, k1_zfmisc_1(k2_zfmisc_1('#skF_1', A_316))) | ~v1_funct_1(E_319))), inference(negUnitSimplification, [status(thm)], [c_68, c_1001])).
% 9.97/3.94  tff(c_1549, plain, (k1_xboole_0='#skF_2'), inference(splitLeft, [status(thm)], [c_1002])).
% 9.97/3.94  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 9.97/3.94  tff(c_1551, plain, (v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1549, c_2])).
% 9.97/3.94  tff(c_1553, plain, $false, inference(negUnitSimplification, [status(thm)], [c_66, c_1551])).
% 9.97/3.94  tff(c_1555, plain, (k1_xboole_0!='#skF_2'), inference(splitRight, [status(thm)], [c_1002])).
% 9.97/3.94  tff(c_58, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_213])).
% 9.97/3.94  tff(c_56, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_213])).
% 9.97/3.94  tff(c_74, plain, (v1_relat_1('#skF_5') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_3'))), inference(resolution, [status(thm)], [c_56, c_71])).
% 9.97/3.94  tff(c_80, plain, (v1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_12, c_74])).
% 9.97/3.94  tff(c_52, plain, (v1_partfun1('#skF_5', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_213])).
% 9.97/3.94  tff(c_94, plain, (![C_116, A_117, B_118]: (v4_relat_1(C_116, A_117) | ~m1_subset_1(C_116, k1_zfmisc_1(k2_zfmisc_1(A_117, B_118))))), inference(cnfTransformation, [status(thm)], [f_63])).
% 9.97/3.94  tff(c_101, plain, (v4_relat_1('#skF_5', '#skF_1')), inference(resolution, [status(thm)], [c_56, c_94])).
% 9.97/3.94  tff(c_109, plain, (![B_122, A_123]: (k1_relat_1(B_122)=A_123 | ~v1_partfun1(B_122, A_123) | ~v4_relat_1(B_122, A_123) | ~v1_relat_1(B_122))), inference(cnfTransformation, [status(thm)], [f_114])).
% 9.97/3.94  tff(c_115, plain, (k1_relat_1('#skF_5')='#skF_1' | ~v1_partfun1('#skF_5', '#skF_1') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_101, c_109])).
% 9.97/3.94  tff(c_121, plain, (k1_relat_1('#skF_5')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_80, c_52, c_115])).
% 9.97/3.94  tff(c_292, plain, (![A_154, B_155, C_156]: (k1_relset_1(A_154, B_155, C_156)=k1_relat_1(C_156) | ~m1_subset_1(C_156, k1_zfmisc_1(k2_zfmisc_1(A_154, B_155))))), inference(cnfTransformation, [status(thm)], [f_67])).
% 9.97/3.94  tff(c_295, plain, (k1_relset_1('#skF_1', '#skF_3', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_56, c_292])).
% 9.97/3.94  tff(c_300, plain, (k1_relset_1('#skF_1', '#skF_3', '#skF_5')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_121, c_295])).
% 9.97/3.94  tff(c_989, plain, (![B_317, D_320, F_318]: (k1_funct_1(k8_funct_2(B_317, '#skF_1', '#skF_3', D_320, '#skF_5'), F_318)=k1_funct_1('#skF_5', k1_funct_1(D_320, F_318)) | k1_xboole_0=B_317 | ~r1_tarski(k2_relset_1(B_317, '#skF_1', D_320), '#skF_1') | ~m1_subset_1(F_318, B_317) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3'))) | ~v1_funct_1('#skF_5') | ~m1_subset_1(D_320, k1_zfmisc_1(k2_zfmisc_1(B_317, '#skF_1'))) | ~v1_funct_2(D_320, B_317, '#skF_1') | ~v1_funct_1(D_320) | v1_xboole_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_300, c_985])).
% 9.97/3.94  tff(c_998, plain, (![B_317, D_320, F_318]: (k1_funct_1(k8_funct_2(B_317, '#skF_1', '#skF_3', D_320, '#skF_5'), F_318)=k1_funct_1('#skF_5', k1_funct_1(D_320, F_318)) | k1_xboole_0=B_317 | ~r1_tarski(k2_relset_1(B_317, '#skF_1', D_320), '#skF_1') | ~m1_subset_1(F_318, B_317) | ~m1_subset_1(D_320, k1_zfmisc_1(k2_zfmisc_1(B_317, '#skF_1'))) | ~v1_funct_2(D_320, B_317, '#skF_1') | ~v1_funct_1(D_320) | v1_xboole_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_989])).
% 9.97/3.94  tff(c_1757, plain, (![B_423, D_424, F_425]: (k1_funct_1(k8_funct_2(B_423, '#skF_1', '#skF_3', D_424, '#skF_5'), F_425)=k1_funct_1('#skF_5', k1_funct_1(D_424, F_425)) | k1_xboole_0=B_423 | ~r1_tarski(k2_relset_1(B_423, '#skF_1', D_424), '#skF_1') | ~m1_subset_1(F_425, B_423) | ~m1_subset_1(D_424, k1_zfmisc_1(k2_zfmisc_1(B_423, '#skF_1'))) | ~v1_funct_2(D_424, B_423, '#skF_1') | ~v1_funct_1(D_424))), inference(negUnitSimplification, [status(thm)], [c_68, c_998])).
% 9.97/3.94  tff(c_1774, plain, (![F_425]: (k1_funct_1(k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), F_425)=k1_funct_1('#skF_5', k1_funct_1('#skF_4', F_425)) | k1_xboole_0='#skF_2' | ~r1_tarski(k2_relset_1('#skF_2', '#skF_1', '#skF_4'), '#skF_1') | ~m1_subset_1(F_425, '#skF_2') | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_60, c_1757])).
% 9.97/3.94  tff(c_1782, plain, (![F_425]: (k1_funct_1(k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), F_425)=k1_funct_1('#skF_5', k1_funct_1('#skF_4', F_425)) | k1_xboole_0='#skF_2' | ~r1_tarski(k2_relat_1('#skF_4'), '#skF_1') | ~m1_subset_1(F_425, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_283, c_1774])).
% 9.97/3.94  tff(c_1783, plain, (![F_425]: (k1_funct_1(k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), F_425)=k1_funct_1('#skF_5', k1_funct_1('#skF_4', F_425)) | ~r1_tarski(k2_relat_1('#skF_4'), '#skF_1') | ~m1_subset_1(F_425, '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_1555, c_1782])).
% 9.97/3.94  tff(c_1784, plain, (~r1_tarski(k2_relat_1('#skF_4'), '#skF_1')), inference(splitLeft, [status(thm)], [c_1783])).
% 9.97/3.94  tff(c_1787, plain, (~v5_relat_1('#skF_4', '#skF_1') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_10, c_1784])).
% 9.97/3.94  tff(c_1791, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_83, c_93, c_1787])).
% 9.97/3.94  tff(c_1792, plain, (![F_425]: (k1_funct_1(k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), F_425)=k1_funct_1('#skF_5', k1_funct_1('#skF_4', F_425)) | ~m1_subset_1(F_425, '#skF_2'))), inference(splitRight, [status(thm)], [c_1783])).
% 9.97/3.94  tff(c_102, plain, (v4_relat_1('#skF_4', '#skF_2')), inference(resolution, [status(thm)], [c_60, c_94])).
% 9.97/3.94  tff(c_112, plain, (k1_relat_1('#skF_4')='#skF_2' | ~v1_partfun1('#skF_4', '#skF_2') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_102, c_109])).
% 9.97/3.94  tff(c_118, plain, (k1_relat_1('#skF_4')='#skF_2' | ~v1_partfun1('#skF_4', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_83, c_112])).
% 9.97/3.94  tff(c_131, plain, (~v1_partfun1('#skF_4', '#skF_2')), inference(splitLeft, [status(thm)], [c_118])).
% 9.97/3.94  tff(c_242, plain, (![C_148, A_149, B_150]: (v1_partfun1(C_148, A_149) | ~v1_funct_2(C_148, A_149, B_150) | ~v1_funct_1(C_148) | ~m1_subset_1(C_148, k1_zfmisc_1(k2_zfmisc_1(A_149, B_150))) | v1_xboole_0(B_150))), inference(cnfTransformation, [status(thm)], [f_106])).
% 9.97/3.94  tff(c_252, plain, (v1_partfun1('#skF_4', '#skF_2') | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4') | v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_60, c_242])).
% 9.97/3.94  tff(c_260, plain, (v1_partfun1('#skF_4', '#skF_2') | v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_252])).
% 9.97/3.94  tff(c_262, plain, $false, inference(negUnitSimplification, [status(thm)], [c_68, c_131, c_260])).
% 9.97/3.94  tff(c_263, plain, (k1_relat_1('#skF_4')='#skF_2'), inference(splitRight, [status(thm)], [c_118])).
% 9.97/3.94  tff(c_311, plain, (![C_157, A_158, B_159]: (~v1_partfun1(C_157, A_158) | ~m1_subset_1(C_157, k1_zfmisc_1(k2_zfmisc_1(A_158, B_159))) | ~v1_xboole_0(B_159) | v1_xboole_0(A_158))), inference(cnfTransformation, [status(thm)], [f_92])).
% 9.97/3.94  tff(c_314, plain, (~v1_partfun1('#skF_5', '#skF_1') | ~v1_xboole_0('#skF_3') | v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_56, c_311])).
% 9.97/3.94  tff(c_320, plain, (~v1_xboole_0('#skF_3') | v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_314])).
% 9.97/3.94  tff(c_321, plain, (~v1_xboole_0('#skF_3')), inference(negUnitSimplification, [status(thm)], [c_68, c_320])).
% 9.97/3.94  tff(c_326, plain, (![C_160, A_161, B_162]: (v1_funct_2(C_160, A_161, B_162) | ~v1_partfun1(C_160, A_161) | ~v1_funct_1(C_160) | ~m1_subset_1(C_160, k1_zfmisc_1(k2_zfmisc_1(A_161, B_162))))), inference(cnfTransformation, [status(thm)], [f_81])).
% 9.97/3.94  tff(c_329, plain, (v1_funct_2('#skF_5', '#skF_1', '#skF_3') | ~v1_partfun1('#skF_5', '#skF_1') | ~v1_funct_1('#skF_5')), inference(resolution, [status(thm)], [c_56, c_326])).
% 9.97/3.94  tff(c_335, plain, (v1_funct_2('#skF_5', '#skF_1', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_52, c_329])).
% 9.97/3.94  tff(c_4, plain, (![A_1, B_2]: (r2_hidden(A_1, B_2) | v1_xboole_0(B_2) | ~m1_subset_1(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 9.97/3.94  tff(c_339, plain, (![C_163, B_164, A_165]: (m1_subset_1(k1_funct_1(C_163, B_164), A_165) | ~r2_hidden(B_164, k1_relat_1(C_163)) | ~v1_funct_1(C_163) | ~v5_relat_1(C_163, A_165) | ~v1_relat_1(C_163))), inference(cnfTransformation, [status(thm)], [f_57])).
% 9.97/3.94  tff(c_351, plain, (![C_163, A_1, A_165]: (m1_subset_1(k1_funct_1(C_163, A_1), A_165) | ~v1_funct_1(C_163) | ~v5_relat_1(C_163, A_165) | ~v1_relat_1(C_163) | v1_xboole_0(k1_relat_1(C_163)) | ~m1_subset_1(A_1, k1_relat_1(C_163)))), inference(resolution, [status(thm)], [c_4, c_339])).
% 9.97/3.94  tff(c_621, plain, (![A_247, B_248, C_249, D_250]: (k3_funct_2(A_247, B_248, C_249, D_250)=k7_partfun1(B_248, C_249, D_250) | ~m1_subset_1(D_250, A_247) | ~m1_subset_1(C_249, k1_zfmisc_1(k2_zfmisc_1(A_247, B_248))) | ~v1_funct_2(C_249, A_247, B_248) | ~v1_funct_1(C_249) | v1_xboole_0(B_248) | v1_xboole_0(A_247))), inference(cnfTransformation, [status(thm)], [f_162])).
% 9.97/3.94  tff(c_3417, plain, (![C_778, B_779, A_780, C_777, A_781]: (k3_funct_2(A_780, B_779, C_777, k1_funct_1(C_778, A_781))=k7_partfun1(B_779, C_777, k1_funct_1(C_778, A_781)) | ~m1_subset_1(C_777, k1_zfmisc_1(k2_zfmisc_1(A_780, B_779))) | ~v1_funct_2(C_777, A_780, B_779) | ~v1_funct_1(C_777) | v1_xboole_0(B_779) | v1_xboole_0(A_780) | ~v1_funct_1(C_778) | ~v5_relat_1(C_778, A_780) | ~v1_relat_1(C_778) | v1_xboole_0(k1_relat_1(C_778)) | ~m1_subset_1(A_781, k1_relat_1(C_778)))), inference(resolution, [status(thm)], [c_351, c_621])).
% 9.97/3.94  tff(c_3436, plain, (![C_778, A_781]: (k3_funct_2('#skF_1', '#skF_3', '#skF_5', k1_funct_1(C_778, A_781))=k7_partfun1('#skF_3', '#skF_5', k1_funct_1(C_778, A_781)) | ~v1_funct_2('#skF_5', '#skF_1', '#skF_3') | ~v1_funct_1('#skF_5') | v1_xboole_0('#skF_3') | v1_xboole_0('#skF_1') | ~v1_funct_1(C_778) | ~v5_relat_1(C_778, '#skF_1') | ~v1_relat_1(C_778) | v1_xboole_0(k1_relat_1(C_778)) | ~m1_subset_1(A_781, k1_relat_1(C_778)))), inference(resolution, [status(thm)], [c_56, c_3417])).
% 9.97/3.94  tff(c_3447, plain, (![C_778, A_781]: (k3_funct_2('#skF_1', '#skF_3', '#skF_5', k1_funct_1(C_778, A_781))=k7_partfun1('#skF_3', '#skF_5', k1_funct_1(C_778, A_781)) | v1_xboole_0('#skF_3') | v1_xboole_0('#skF_1') | ~v1_funct_1(C_778) | ~v5_relat_1(C_778, '#skF_1') | ~v1_relat_1(C_778) | v1_xboole_0(k1_relat_1(C_778)) | ~m1_subset_1(A_781, k1_relat_1(C_778)))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_335, c_3436])).
% 9.97/3.94  tff(c_3453, plain, (![C_782, A_783]: (k3_funct_2('#skF_1', '#skF_3', '#skF_5', k1_funct_1(C_782, A_783))=k7_partfun1('#skF_3', '#skF_5', k1_funct_1(C_782, A_783)) | ~v1_funct_1(C_782) | ~v5_relat_1(C_782, '#skF_1') | ~v1_relat_1(C_782) | v1_xboole_0(k1_relat_1(C_782)) | ~m1_subset_1(A_783, k1_relat_1(C_782)))), inference(negUnitSimplification, [status(thm)], [c_68, c_321, c_3447])).
% 9.97/3.94  tff(c_3479, plain, (![A_783]: (k3_funct_2('#skF_1', '#skF_3', '#skF_5', k1_funct_1('#skF_4', A_783))=k7_partfun1('#skF_3', '#skF_5', k1_funct_1('#skF_4', A_783)) | ~v1_funct_1('#skF_4') | ~v5_relat_1('#skF_4', '#skF_1') | ~v1_relat_1('#skF_4') | v1_xboole_0(k1_relat_1('#skF_4')) | ~m1_subset_1(A_783, '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_263, c_3453])).
% 9.97/3.94  tff(c_3492, plain, (![A_783]: (k3_funct_2('#skF_1', '#skF_3', '#skF_5', k1_funct_1('#skF_4', A_783))=k7_partfun1('#skF_3', '#skF_5', k1_funct_1('#skF_4', A_783)) | v1_xboole_0('#skF_2') | ~m1_subset_1(A_783, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_263, c_83, c_93, c_64, c_3479])).
% 9.97/3.94  tff(c_3497, plain, (![A_784]: (k3_funct_2('#skF_1', '#skF_3', '#skF_5', k1_funct_1('#skF_4', A_784))=k7_partfun1('#skF_3', '#skF_5', k1_funct_1('#skF_4', A_784)) | ~m1_subset_1(A_784, '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_66, c_3492])).
% 9.97/3.94  tff(c_501, plain, (![A_199, B_200, C_201, D_202]: (k3_funct_2(A_199, B_200, C_201, D_202)=k1_funct_1(C_201, D_202) | ~m1_subset_1(D_202, A_199) | ~m1_subset_1(C_201, k1_zfmisc_1(k2_zfmisc_1(A_199, B_200))) | ~v1_funct_2(C_201, A_199, B_200) | ~v1_funct_1(C_201) | v1_xboole_0(A_199))), inference(cnfTransformation, [status(thm)], [f_143])).
% 9.97/3.94  tff(c_2931, plain, (![A_692, B_690, A_693, C_691, C_694]: (k3_funct_2(A_692, B_690, C_694, k1_funct_1(C_691, A_693))=k1_funct_1(C_694, k1_funct_1(C_691, A_693)) | ~m1_subset_1(C_694, k1_zfmisc_1(k2_zfmisc_1(A_692, B_690))) | ~v1_funct_2(C_694, A_692, B_690) | ~v1_funct_1(C_694) | v1_xboole_0(A_692) | ~v1_funct_1(C_691) | ~v5_relat_1(C_691, A_692) | ~v1_relat_1(C_691) | v1_xboole_0(k1_relat_1(C_691)) | ~m1_subset_1(A_693, k1_relat_1(C_691)))), inference(resolution, [status(thm)], [c_351, c_501])).
% 9.97/3.94  tff(c_2950, plain, (![C_691, A_693]: (k3_funct_2('#skF_1', '#skF_3', '#skF_5', k1_funct_1(C_691, A_693))=k1_funct_1('#skF_5', k1_funct_1(C_691, A_693)) | ~v1_funct_2('#skF_5', '#skF_1', '#skF_3') | ~v1_funct_1('#skF_5') | v1_xboole_0('#skF_1') | ~v1_funct_1(C_691) | ~v5_relat_1(C_691, '#skF_1') | ~v1_relat_1(C_691) | v1_xboole_0(k1_relat_1(C_691)) | ~m1_subset_1(A_693, k1_relat_1(C_691)))), inference(resolution, [status(thm)], [c_56, c_2931])).
% 9.97/3.94  tff(c_2961, plain, (![C_691, A_693]: (k3_funct_2('#skF_1', '#skF_3', '#skF_5', k1_funct_1(C_691, A_693))=k1_funct_1('#skF_5', k1_funct_1(C_691, A_693)) | v1_xboole_0('#skF_1') | ~v1_funct_1(C_691) | ~v5_relat_1(C_691, '#skF_1') | ~v1_relat_1(C_691) | v1_xboole_0(k1_relat_1(C_691)) | ~m1_subset_1(A_693, k1_relat_1(C_691)))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_335, c_2950])).
% 9.97/3.94  tff(c_2967, plain, (![C_695, A_696]: (k3_funct_2('#skF_1', '#skF_3', '#skF_5', k1_funct_1(C_695, A_696))=k1_funct_1('#skF_5', k1_funct_1(C_695, A_696)) | ~v1_funct_1(C_695) | ~v5_relat_1(C_695, '#skF_1') | ~v1_relat_1(C_695) | v1_xboole_0(k1_relat_1(C_695)) | ~m1_subset_1(A_696, k1_relat_1(C_695)))), inference(negUnitSimplification, [status(thm)], [c_68, c_2961])).
% 9.97/3.94  tff(c_2993, plain, (![A_696]: (k3_funct_2('#skF_1', '#skF_3', '#skF_5', k1_funct_1('#skF_4', A_696))=k1_funct_1('#skF_5', k1_funct_1('#skF_4', A_696)) | ~v1_funct_1('#skF_4') | ~v5_relat_1('#skF_4', '#skF_1') | ~v1_relat_1('#skF_4') | v1_xboole_0(k1_relat_1('#skF_4')) | ~m1_subset_1(A_696, '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_263, c_2967])).
% 9.97/3.94  tff(c_3006, plain, (![A_696]: (k3_funct_2('#skF_1', '#skF_3', '#skF_5', k1_funct_1('#skF_4', A_696))=k1_funct_1('#skF_5', k1_funct_1('#skF_4', A_696)) | v1_xboole_0('#skF_2') | ~m1_subset_1(A_696, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_263, c_83, c_93, c_64, c_2993])).
% 9.97/3.94  tff(c_3007, plain, (![A_696]: (k3_funct_2('#skF_1', '#skF_3', '#skF_5', k1_funct_1('#skF_4', A_696))=k1_funct_1('#skF_5', k1_funct_1('#skF_4', A_696)) | ~m1_subset_1(A_696, '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_66, c_3006])).
% 9.97/3.94  tff(c_3511, plain, (![A_784]: (k7_partfun1('#skF_3', '#skF_5', k1_funct_1('#skF_4', A_784))=k1_funct_1('#skF_5', k1_funct_1('#skF_4', A_784)) | ~m1_subset_1(A_784, '#skF_2') | ~m1_subset_1(A_784, '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_3497, c_3007])).
% 9.97/3.94  tff(c_555, plain, (![E_227, D_228, C_226, A_225, B_229]: (v1_funct_1(k8_funct_2(A_225, B_229, C_226, D_228, E_227)) | ~m1_subset_1(E_227, k1_zfmisc_1(k2_zfmisc_1(B_229, C_226))) | ~v1_funct_1(E_227) | ~m1_subset_1(D_228, k1_zfmisc_1(k2_zfmisc_1(A_225, B_229))) | ~v1_funct_2(D_228, A_225, B_229) | ~v1_funct_1(D_228))), inference(cnfTransformation, [status(thm)], [f_130])).
% 9.97/3.94  tff(c_566, plain, (![A_225, D_228]: (v1_funct_1(k8_funct_2(A_225, '#skF_1', '#skF_3', D_228, '#skF_5')) | ~v1_funct_1('#skF_5') | ~m1_subset_1(D_228, k1_zfmisc_1(k2_zfmisc_1(A_225, '#skF_1'))) | ~v1_funct_2(D_228, A_225, '#skF_1') | ~v1_funct_1(D_228))), inference(resolution, [status(thm)], [c_56, c_555])).
% 9.97/3.94  tff(c_578, plain, (![A_230, D_231]: (v1_funct_1(k8_funct_2(A_230, '#skF_1', '#skF_3', D_231, '#skF_5')) | ~m1_subset_1(D_231, k1_zfmisc_1(k2_zfmisc_1(A_230, '#skF_1'))) | ~v1_funct_2(D_231, A_230, '#skF_1') | ~v1_funct_1(D_231))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_566])).
% 9.97/3.94  tff(c_593, plain, (v1_funct_1(k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5')) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_60, c_578])).
% 9.97/3.94  tff(c_599, plain, (v1_funct_1(k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_593])).
% 9.97/3.94  tff(c_676, plain, (![A_268, E_270, C_269, D_271, B_272]: (v1_funct_2(k8_funct_2(A_268, B_272, C_269, D_271, E_270), A_268, C_269) | ~m1_subset_1(E_270, k1_zfmisc_1(k2_zfmisc_1(B_272, C_269))) | ~v1_funct_1(E_270) | ~m1_subset_1(D_271, k1_zfmisc_1(k2_zfmisc_1(A_268, B_272))) | ~v1_funct_2(D_271, A_268, B_272) | ~v1_funct_1(D_271))), inference(cnfTransformation, [status(thm)], [f_130])).
% 9.97/3.94  tff(c_687, plain, (![A_268, D_271]: (v1_funct_2(k8_funct_2(A_268, '#skF_1', '#skF_3', D_271, '#skF_5'), A_268, '#skF_3') | ~v1_funct_1('#skF_5') | ~m1_subset_1(D_271, k1_zfmisc_1(k2_zfmisc_1(A_268, '#skF_1'))) | ~v1_funct_2(D_271, A_268, '#skF_1') | ~v1_funct_1(D_271))), inference(resolution, [status(thm)], [c_56, c_676])).
% 9.97/3.94  tff(c_699, plain, (![A_273, D_274]: (v1_funct_2(k8_funct_2(A_273, '#skF_1', '#skF_3', D_274, '#skF_5'), A_273, '#skF_3') | ~m1_subset_1(D_274, k1_zfmisc_1(k2_zfmisc_1(A_273, '#skF_1'))) | ~v1_funct_2(D_274, A_273, '#skF_1') | ~v1_funct_1(D_274))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_687])).
% 9.97/3.94  tff(c_710, plain, (v1_funct_2(k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), '#skF_2', '#skF_3') | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_60, c_699])).
% 9.97/3.94  tff(c_716, plain, (v1_funct_2(k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), '#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_710])).
% 9.97/3.94  tff(c_736, plain, (![C_288, E_289, B_291, D_290, A_287]: (m1_subset_1(k8_funct_2(A_287, B_291, C_288, D_290, E_289), k1_zfmisc_1(k2_zfmisc_1(A_287, C_288))) | ~m1_subset_1(E_289, k1_zfmisc_1(k2_zfmisc_1(B_291, C_288))) | ~v1_funct_1(E_289) | ~m1_subset_1(D_290, k1_zfmisc_1(k2_zfmisc_1(A_287, B_291))) | ~v1_funct_2(D_290, A_287, B_291) | ~v1_funct_1(D_290))), inference(cnfTransformation, [status(thm)], [f_130])).
% 9.97/3.94  tff(c_513, plain, (![B_200, C_201]: (k3_funct_2('#skF_2', B_200, C_201, '#skF_6')=k1_funct_1(C_201, '#skF_6') | ~m1_subset_1(C_201, k1_zfmisc_1(k2_zfmisc_1('#skF_2', B_200))) | ~v1_funct_2(C_201, '#skF_2', B_200) | ~v1_funct_1(C_201) | v1_xboole_0('#skF_2'))), inference(resolution, [status(thm)], [c_54, c_501])).
% 9.97/3.94  tff(c_521, plain, (![B_200, C_201]: (k3_funct_2('#skF_2', B_200, C_201, '#skF_6')=k1_funct_1(C_201, '#skF_6') | ~m1_subset_1(C_201, k1_zfmisc_1(k2_zfmisc_1('#skF_2', B_200))) | ~v1_funct_2(C_201, '#skF_2', B_200) | ~v1_funct_1(C_201))), inference(negUnitSimplification, [status(thm)], [c_66, c_513])).
% 9.97/3.94  tff(c_6608, plain, (![C_1119, B_1120, D_1121, E_1122]: (k3_funct_2('#skF_2', C_1119, k8_funct_2('#skF_2', B_1120, C_1119, D_1121, E_1122), '#skF_6')=k1_funct_1(k8_funct_2('#skF_2', B_1120, C_1119, D_1121, E_1122), '#skF_6') | ~v1_funct_2(k8_funct_2('#skF_2', B_1120, C_1119, D_1121, E_1122), '#skF_2', C_1119) | ~v1_funct_1(k8_funct_2('#skF_2', B_1120, C_1119, D_1121, E_1122)) | ~m1_subset_1(E_1122, k1_zfmisc_1(k2_zfmisc_1(B_1120, C_1119))) | ~v1_funct_1(E_1122) | ~m1_subset_1(D_1121, k1_zfmisc_1(k2_zfmisc_1('#skF_2', B_1120))) | ~v1_funct_2(D_1121, '#skF_2', B_1120) | ~v1_funct_1(D_1121))), inference(resolution, [status(thm)], [c_736, c_521])).
% 9.97/3.94  tff(c_6664, plain, (k3_funct_2('#skF_2', '#skF_3', k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), '#skF_6')=k1_funct_1(k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), '#skF_6') | ~v1_funct_1(k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3'))) | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_716, c_6608])).
% 9.97/3.94  tff(c_6709, plain, (k3_funct_2('#skF_2', '#skF_3', k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), '#skF_6')=k1_funct_1(k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_60, c_58, c_56, c_599, c_6664])).
% 9.97/3.94  tff(c_525, plain, (![B_212, C_213]: (k3_funct_2('#skF_2', B_212, C_213, '#skF_6')=k1_funct_1(C_213, '#skF_6') | ~m1_subset_1(C_213, k1_zfmisc_1(k2_zfmisc_1('#skF_2', B_212))) | ~v1_funct_2(C_213, '#skF_2', B_212) | ~v1_funct_1(C_213))), inference(negUnitSimplification, [status(thm)], [c_66, c_513])).
% 9.97/3.94  tff(c_540, plain, (k3_funct_2('#skF_2', '#skF_1', '#skF_4', '#skF_6')=k1_funct_1('#skF_4', '#skF_6') | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_60, c_525])).
% 9.97/3.94  tff(c_546, plain, (k3_funct_2('#skF_2', '#skF_1', '#skF_4', '#skF_6')=k1_funct_1('#skF_4', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_540])).
% 9.97/3.94  tff(c_50, plain, (k3_funct_2('#skF_2', '#skF_3', k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), '#skF_6')!=k7_partfun1('#skF_3', '#skF_5', k3_funct_2('#skF_2', '#skF_1', '#skF_4', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_213])).
% 9.97/3.94  tff(c_547, plain, (k3_funct_2('#skF_2', '#skF_3', k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), '#skF_6')!=k7_partfun1('#skF_3', '#skF_5', k1_funct_1('#skF_4', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_546, c_50])).
% 9.97/3.94  tff(c_6710, plain, (k7_partfun1('#skF_3', '#skF_5', k1_funct_1('#skF_4', '#skF_6'))!=k1_funct_1(k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_6709, c_547])).
% 9.97/3.94  tff(c_6717, plain, (k1_funct_1(k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), '#skF_6')!=k1_funct_1('#skF_5', k1_funct_1('#skF_4', '#skF_6')) | ~m1_subset_1('#skF_6', '#skF_2') | ~m1_subset_1('#skF_6', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_3511, c_6710])).
% 9.97/3.94  tff(c_6725, plain, (k1_funct_1(k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), '#skF_6')!=k1_funct_1('#skF_5', k1_funct_1('#skF_4', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_54, c_6717])).
% 9.97/3.94  tff(c_6730, plain, (~m1_subset_1('#skF_6', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_1792, c_6725])).
% 9.97/3.94  tff(c_6734, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_54, c_6730])).
% 9.97/3.94  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.97/3.94  
% 9.97/3.94  Inference rules
% 9.97/3.94  ----------------------
% 9.97/3.94  #Ref     : 0
% 9.97/3.94  #Sup     : 1337
% 9.97/3.94  #Fact    : 0
% 9.97/3.94  #Define  : 0
% 9.97/3.94  #Split   : 27
% 9.97/3.94  #Chain   : 0
% 9.97/3.94  #Close   : 0
% 9.97/3.94  
% 9.97/3.94  Ordering : KBO
% 9.97/3.94  
% 9.97/3.94  Simplification rules
% 9.97/3.94  ----------------------
% 9.97/3.94  #Subsume      : 193
% 9.97/3.94  #Demod        : 1449
% 9.97/3.94  #Tautology    : 193
% 9.97/3.94  #SimpNegUnit  : 294
% 9.97/3.94  #BackRed      : 11
% 9.97/3.94  
% 9.97/3.94  #Partial instantiations: 0
% 9.97/3.94  #Strategies tried      : 1
% 9.97/3.94  
% 9.97/3.94  Timing (in seconds)
% 9.97/3.94  ----------------------
% 9.97/3.94  Preprocessing        : 0.40
% 9.97/3.94  Parsing              : 0.20
% 9.97/3.94  CNF conversion       : 0.04
% 9.97/3.94  Main loop            : 2.75
% 9.97/3.94  Inferencing          : 0.85
% 9.97/3.94  Reduction            : 0.85
% 9.97/3.94  Demodulation         : 0.61
% 9.97/3.94  BG Simplification    : 0.09
% 9.97/3.94  Subsumption          : 0.78
% 9.97/3.94  Abstraction          : 0.16
% 9.97/3.94  MUC search           : 0.00
% 9.97/3.94  Cooper               : 0.00
% 9.97/3.94  Total                : 3.20
% 9.97/3.94  Index Insertion      : 0.00
% 9.97/3.94  Index Deletion       : 0.00
% 9.97/3.94  Index Matching       : 0.00
% 9.97/3.94  BG Taut test         : 0.00
%------------------------------------------------------------------------------
