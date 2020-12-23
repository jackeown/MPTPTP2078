%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:13:11 EST 2020

% Result     : Theorem 11.68s
% Output     : CNFRefutation 11.68s
% Verified   : 
% Statistics : Number of formulae       :  175 (1307 expanded)
%              Number of leaves         :   52 ( 465 expanded)
%              Depth                    :   26
%              Number of atoms          :  351 (3915 expanded)
%              Number of equality atoms :   78 (1021 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k4_relat_1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff(k2_funct_1,type,(
    k2_funct_1: $i > $i )).

tff(v2_funct_1,type,(
    v2_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_relset_1,type,(
    r2_relset_1: ( $i * $i * $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k1_partfun1,type,(
    k1_partfun1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k6_partfun1,type,(
    k6_partfun1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k4_relat_1,type,(
    k4_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_194,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ! [D] :
            ( ( v1_funct_1(D)
              & v1_funct_2(D,B,A)
              & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,A))) )
           => ( ( k2_relset_1(A,B,C) = B
                & r2_relset_1(A,A,k1_partfun1(A,B,B,A,C,D),k6_partfun1(A))
                & v2_funct_1(C) )
             => ( A = k1_xboole_0
                | B = k1_xboole_0
                | D = k2_funct_1(C) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_funct_2)).

tff(f_50,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_38,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_130,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_104,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_168,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_84,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_134,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_124,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k5_relat_1(A,k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))
          & k5_relat_1(k2_funct_1(A),A) = k6_relat_1(k2_relat_1(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_funct_1)).

tff(f_63,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => r1_tarski(k2_relat_1(k5_relat_1(A,B)),k2_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_relat_1)).

tff(f_48,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => v1_relat_1(k4_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_relat_1)).

tff(f_56,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( k2_relat_1(A) = k1_relat_1(k4_relat_1(A))
        & k1_relat_1(A) = k2_relat_1(k4_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_relat_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_86,axiom,(
    ! [A] : k4_relat_1(k6_relat_1(A)) = k6_relat_1(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_relat_1)).

tff(f_144,axiom,(
    ! [A] : m1_subset_1(k6_relat_1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_relset_1)).

tff(f_92,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k1_relat_1(B),A)
       => k5_relat_1(k6_relat_1(A),B) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_relat_1)).

tff(f_156,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( v1_funct_1(k1_partfun1(A,B,C,D,E,F))
        & m1_subset_1(k1_partfun1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).

tff(f_142,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_166,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_70,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k4_relat_1(k5_relat_1(A,B)) = k5_relat_1(k4_relat_1(B),k4_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t54_relat_1)).

tff(f_114,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k2_relat_1(A) = k1_relat_1(k2_funct_1(A))
          & k1_relat_1(A) = k2_relat_1(k2_funct_1(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).

tff(f_96,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k5_relat_1(A,k6_relat_1(k2_relat_1(A))) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t80_relat_1)).

tff(f_80,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ! [C] :
              ( v1_relat_1(C)
             => k5_relat_1(k5_relat_1(A,B),C) = k5_relat_1(A,k5_relat_1(B,C)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_relat_1)).

tff(c_70,plain,(
    k2_funct_1('#skF_3') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_194])).

tff(c_16,plain,(
    ! [A_9,B_10] : v1_relat_1(k2_zfmisc_1(A_9,B_10)) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_82,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_194])).

tff(c_184,plain,(
    ! [B_73,A_74] :
      ( v1_relat_1(B_73)
      | ~ m1_subset_1(B_73,k1_zfmisc_1(A_74))
      | ~ v1_relat_1(A_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_190,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_1')) ),
    inference(resolution,[status(thm)],[c_82,c_184])).

tff(c_199,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_190])).

tff(c_291,plain,(
    ! [C_89,A_90,B_91] :
      ( v4_relat_1(C_89,A_90)
      | ~ m1_subset_1(C_89,k1_zfmisc_1(k2_zfmisc_1(A_90,B_91))) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_302,plain,(
    v4_relat_1('#skF_4','#skF_2') ),
    inference(resolution,[status(thm)],[c_82,c_291])).

tff(c_88,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_194])).

tff(c_193,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_88,c_184])).

tff(c_202,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_193])).

tff(c_92,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_194])).

tff(c_76,plain,(
    v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_194])).

tff(c_40,plain,(
    ! [A_30] :
      ( v1_relat_1(k2_funct_1(A_30))
      | ~ v1_funct_1(A_30)
      | ~ v1_relat_1(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_68,plain,(
    ! [A_56] : k6_relat_1(A_56) = k6_partfun1(A_56) ),
    inference(cnfTransformation,[status(thm)],[f_168])).

tff(c_30,plain,(
    ! [A_25] : k2_relat_1(k6_relat_1(A_25)) = A_25 ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_99,plain,(
    ! [A_25] : k2_relat_1(k6_partfun1(A_25)) = A_25 ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_30])).

tff(c_80,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_194])).

tff(c_589,plain,(
    ! [A_113,B_114,C_115] :
      ( k2_relset_1(A_113,B_114,C_115) = k2_relat_1(C_115)
      | ~ m1_subset_1(C_115,k1_zfmisc_1(k2_zfmisc_1(A_113,B_114))) ) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_598,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_88,c_589])).

tff(c_603,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_598])).

tff(c_46,plain,(
    ! [A_32] :
      ( k5_relat_1(k2_funct_1(A_32),A_32) = k6_relat_1(k2_relat_1(A_32))
      | ~ v2_funct_1(A_32)
      | ~ v1_funct_1(A_32)
      | ~ v1_relat_1(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_95,plain,(
    ! [A_32] :
      ( k5_relat_1(k2_funct_1(A_32),A_32) = k6_partfun1(k2_relat_1(A_32))
      | ~ v2_funct_1(A_32)
      | ~ v1_funct_1(A_32)
      | ~ v1_relat_1(A_32) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_46])).

tff(c_22,plain,(
    ! [A_12,B_14] :
      ( r1_tarski(k2_relat_1(k5_relat_1(A_12,B_14)),k2_relat_1(B_14))
      | ~ v1_relat_1(B_14)
      | ~ v1_relat_1(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_611,plain,(
    ! [A_12] :
      ( r1_tarski(k2_relat_1(k5_relat_1(A_12,'#skF_3')),'#skF_2')
      | ~ v1_relat_1('#skF_3')
      | ~ v1_relat_1(A_12) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_603,c_22])).

tff(c_679,plain,(
    ! [A_118] :
      ( r1_tarski(k2_relat_1(k5_relat_1(A_118,'#skF_3')),'#skF_2')
      | ~ v1_relat_1(A_118) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_202,c_611])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_701,plain,(
    ! [A_119] :
      ( k2_relat_1(k5_relat_1(A_119,'#skF_3')) = '#skF_2'
      | ~ r1_tarski('#skF_2',k2_relat_1(k5_relat_1(A_119,'#skF_3')))
      | ~ v1_relat_1(A_119) ) ),
    inference(resolution,[status(thm)],[c_679,c_2])).

tff(c_705,plain,
    ( k2_relat_1(k5_relat_1(k2_funct_1('#skF_3'),'#skF_3')) = '#skF_2'
    | ~ r1_tarski('#skF_2',k2_relat_1(k6_partfun1(k2_relat_1('#skF_3'))))
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_95,c_701])).

tff(c_715,plain,
    ( k2_relat_1(k5_relat_1(k2_funct_1('#skF_3'),'#skF_3')) = '#skF_2'
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_202,c_92,c_76,c_6,c_99,c_603,c_705])).

tff(c_758,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_715])).

tff(c_761,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_40,c_758])).

tff(c_765,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_202,c_92,c_761])).

tff(c_767,plain,(
    v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_715])).

tff(c_303,plain,(
    v4_relat_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_88,c_291])).

tff(c_14,plain,(
    ! [A_8] :
      ( v1_relat_1(k4_relat_1(A_8))
      | ~ v1_relat_1(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_20,plain,(
    ! [A_11] :
      ( k1_relat_1(k4_relat_1(A_11)) = k2_relat_1(A_11)
      | ~ v1_relat_1(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_243,plain,(
    ! [B_82,A_83] :
      ( v4_relat_1(B_82,A_83)
      | ~ r1_tarski(k1_relat_1(B_82),A_83)
      | ~ v1_relat_1(B_82) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_261,plain,(
    ! [B_84] :
      ( v4_relat_1(B_84,k1_relat_1(B_84))
      | ~ v1_relat_1(B_84) ) ),
    inference(resolution,[status(thm)],[c_6,c_243])).

tff(c_268,plain,(
    ! [A_11] :
      ( v4_relat_1(k4_relat_1(A_11),k2_relat_1(A_11))
      | ~ v1_relat_1(k4_relat_1(A_11))
      | ~ v1_relat_1(A_11) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_261])).

tff(c_614,plain,
    ( v4_relat_1(k4_relat_1('#skF_3'),'#skF_2')
    | ~ v1_relat_1(k4_relat_1('#skF_3'))
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_603,c_268])).

tff(c_623,plain,
    ( v4_relat_1(k4_relat_1('#skF_3'),'#skF_2')
    | ~ v1_relat_1(k4_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_202,c_614])).

tff(c_650,plain,(
    ~ v1_relat_1(k4_relat_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_623])).

tff(c_653,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_14,c_650])).

tff(c_657,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_202,c_653])).

tff(c_659,plain,(
    v1_relat_1(k4_relat_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_623])).

tff(c_32,plain,(
    ! [A_26] : k4_relat_1(k6_relat_1(A_26)) = k6_relat_1(A_26) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_98,plain,(
    ! [A_26] : k4_relat_1(k6_partfun1(A_26)) = k6_partfun1(A_26) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_68,c_32])).

tff(c_260,plain,(
    ! [B_82] :
      ( v4_relat_1(B_82,k1_relat_1(B_82))
      | ~ v1_relat_1(B_82) ) ),
    inference(resolution,[status(thm)],[c_6,c_243])).

tff(c_18,plain,(
    ! [A_11] :
      ( k2_relat_1(k4_relat_1(A_11)) = k1_relat_1(A_11)
      | ~ v1_relat_1(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_60,plain,(
    ! [A_43] : m1_subset_1(k6_relat_1(A_43),k1_zfmisc_1(k2_zfmisc_1(A_43,A_43))) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_93,plain,(
    ! [A_43] : m1_subset_1(k6_partfun1(A_43),k1_zfmisc_1(k2_zfmisc_1(A_43,A_43))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_60])).

tff(c_187,plain,(
    ! [A_43] :
      ( v1_relat_1(k6_partfun1(A_43))
      | ~ v1_relat_1(k2_zfmisc_1(A_43,A_43)) ) ),
    inference(resolution,[status(thm)],[c_93,c_184])).

tff(c_196,plain,(
    ! [A_43] : v1_relat_1(k6_partfun1(A_43)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_187])).

tff(c_658,plain,(
    v4_relat_1(k4_relat_1('#skF_3'),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_623])).

tff(c_204,plain,(
    ! [B_76,A_77] :
      ( r1_tarski(k1_relat_1(B_76),A_77)
      | ~ v4_relat_1(B_76,A_77)
      | ~ v1_relat_1(B_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_3122,plain,(
    ! [A_244,A_245] :
      ( r1_tarski(k2_relat_1(A_244),A_245)
      | ~ v4_relat_1(k4_relat_1(A_244),A_245)
      | ~ v1_relat_1(k4_relat_1(A_244))
      | ~ v1_relat_1(A_244) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_204])).

tff(c_3148,plain,(
    ! [A_246] :
      ( r1_tarski(k2_relat_1(A_246),k1_relat_1(k4_relat_1(A_246)))
      | ~ v1_relat_1(A_246)
      | ~ v1_relat_1(k4_relat_1(A_246)) ) ),
    inference(resolution,[status(thm)],[c_260,c_3122])).

tff(c_3170,plain,
    ( r1_tarski('#skF_2',k1_relat_1(k4_relat_1('#skF_3')))
    | ~ v1_relat_1('#skF_3')
    | ~ v1_relat_1(k4_relat_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_603,c_3148])).

tff(c_3193,plain,(
    r1_tarski('#skF_2',k1_relat_1(k4_relat_1('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_659,c_202,c_3170])).

tff(c_213,plain,(
    ! [B_76,A_77] :
      ( k1_relat_1(B_76) = A_77
      | ~ r1_tarski(A_77,k1_relat_1(B_76))
      | ~ v4_relat_1(B_76,A_77)
      | ~ v1_relat_1(B_76) ) ),
    inference(resolution,[status(thm)],[c_204,c_2])).

tff(c_3222,plain,
    ( k1_relat_1(k4_relat_1('#skF_3')) = '#skF_2'
    | ~ v4_relat_1(k4_relat_1('#skF_3'),'#skF_2')
    | ~ v1_relat_1(k4_relat_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_3193,c_213])).

tff(c_3232,plain,(
    k1_relat_1(k4_relat_1('#skF_3')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_659,c_658,c_3222])).

tff(c_34,plain,(
    ! [A_27,B_28] :
      ( k5_relat_1(k6_relat_1(A_27),B_28) = B_28
      | ~ r1_tarski(k1_relat_1(B_28),A_27)
      | ~ v1_relat_1(B_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_374,plain,(
    ! [A_102,B_103] :
      ( k5_relat_1(k6_partfun1(A_102),B_103) = B_103
      | ~ r1_tarski(k1_relat_1(B_103),A_102)
      | ~ v1_relat_1(B_103) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_34])).

tff(c_394,plain,(
    ! [B_103] :
      ( k5_relat_1(k6_partfun1(k1_relat_1(B_103)),B_103) = B_103
      | ~ v1_relat_1(B_103) ) ),
    inference(resolution,[status(thm)],[c_6,c_374])).

tff(c_3248,plain,
    ( k5_relat_1(k6_partfun1('#skF_2'),k4_relat_1('#skF_3')) = k4_relat_1('#skF_3')
    | ~ v1_relat_1(k4_relat_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_3232,c_394])).

tff(c_3274,plain,(
    k5_relat_1(k6_partfun1('#skF_2'),k4_relat_1('#skF_3')) = k4_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_659,c_3248])).

tff(c_458,plain,(
    ! [A_107,B_108] :
      ( r1_tarski(k2_relat_1(k5_relat_1(A_107,B_108)),k2_relat_1(B_108))
      | ~ v1_relat_1(B_108)
      | ~ v1_relat_1(A_107) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_3863,plain,(
    ! [A_261,A_262] :
      ( r1_tarski(k2_relat_1(k5_relat_1(A_261,k4_relat_1(A_262))),k1_relat_1(A_262))
      | ~ v1_relat_1(k4_relat_1(A_262))
      | ~ v1_relat_1(A_261)
      | ~ v1_relat_1(A_262) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_458])).

tff(c_3873,plain,
    ( r1_tarski(k2_relat_1(k4_relat_1('#skF_3')),k1_relat_1('#skF_3'))
    | ~ v1_relat_1(k4_relat_1('#skF_3'))
    | ~ v1_relat_1(k6_partfun1('#skF_2'))
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_3274,c_3863])).

tff(c_3921,plain,(
    r1_tarski(k2_relat_1(k4_relat_1('#skF_3')),k1_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_202,c_196,c_659,c_3873])).

tff(c_3940,plain,
    ( k2_relat_1(k4_relat_1('#skF_3')) = k1_relat_1('#skF_3')
    | ~ v4_relat_1('#skF_3',k2_relat_1(k4_relat_1('#skF_3')))
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_3921,c_213])).

tff(c_3950,plain,
    ( k2_relat_1(k4_relat_1('#skF_3')) = k1_relat_1('#skF_3')
    | ~ v4_relat_1('#skF_3',k2_relat_1(k4_relat_1('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_202,c_3940])).

tff(c_4355,plain,(
    ~ v4_relat_1('#skF_3',k2_relat_1(k4_relat_1('#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_3950])).

tff(c_4358,plain,
    ( ~ v4_relat_1('#skF_3',k1_relat_1('#skF_3'))
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_4355])).

tff(c_4360,plain,(
    ~ v4_relat_1('#skF_3',k1_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_202,c_4358])).

tff(c_4401,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_260,c_4360])).

tff(c_4405,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_202,c_4401])).

tff(c_4406,plain,(
    k2_relat_1(k4_relat_1('#skF_3')) = k1_relat_1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_3950])).

tff(c_86,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_194])).

tff(c_2400,plain,(
    ! [D_196,F_195,C_197,E_194,B_198,A_199] :
      ( m1_subset_1(k1_partfun1(A_199,B_198,C_197,D_196,E_194,F_195),k1_zfmisc_1(k2_zfmisc_1(A_199,D_196)))
      | ~ m1_subset_1(F_195,k1_zfmisc_1(k2_zfmisc_1(C_197,D_196)))
      | ~ v1_funct_1(F_195)
      | ~ m1_subset_1(E_194,k1_zfmisc_1(k2_zfmisc_1(A_199,B_198)))
      | ~ v1_funct_1(E_194) ) ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_78,plain,(
    r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k6_partfun1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_194])).

tff(c_1870,plain,(
    ! [D_150,C_151,A_152,B_153] :
      ( D_150 = C_151
      | ~ r2_relset_1(A_152,B_153,C_151,D_150)
      | ~ m1_subset_1(D_150,k1_zfmisc_1(k2_zfmisc_1(A_152,B_153)))
      | ~ m1_subset_1(C_151,k1_zfmisc_1(k2_zfmisc_1(A_152,B_153))) ) ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_1878,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_78,c_1870])).

tff(c_1893,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_93,c_1878])).

tff(c_1990,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_1893])).

tff(c_2413,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_2400,c_1990])).

tff(c_2435,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_88,c_86,c_82,c_2413])).

tff(c_2436,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_1893])).

tff(c_2946,plain,(
    ! [D_231,C_228,F_230,B_229,A_227,E_226] :
      ( k1_partfun1(A_227,B_229,C_228,D_231,E_226,F_230) = k5_relat_1(E_226,F_230)
      | ~ m1_subset_1(F_230,k1_zfmisc_1(k2_zfmisc_1(C_228,D_231)))
      | ~ v1_funct_1(F_230)
      | ~ m1_subset_1(E_226,k1_zfmisc_1(k2_zfmisc_1(A_227,B_229)))
      | ~ v1_funct_1(E_226) ) ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_2950,plain,(
    ! [A_227,B_229,E_226] :
      ( k1_partfun1(A_227,B_229,'#skF_2','#skF_1',E_226,'#skF_4') = k5_relat_1(E_226,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_226,k1_zfmisc_1(k2_zfmisc_1(A_227,B_229)))
      | ~ v1_funct_1(E_226) ) ),
    inference(resolution,[status(thm)],[c_82,c_2946])).

tff(c_3589,plain,(
    ! [A_256,B_257,E_258] :
      ( k1_partfun1(A_256,B_257,'#skF_2','#skF_1',E_258,'#skF_4') = k5_relat_1(E_258,'#skF_4')
      | ~ m1_subset_1(E_258,k1_zfmisc_1(k2_zfmisc_1(A_256,B_257)))
      | ~ v1_funct_1(E_258) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_2950])).

tff(c_3607,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_88,c_3589])).

tff(c_3621,plain,(
    k5_relat_1('#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_2436,c_3607])).

tff(c_801,plain,(
    ! [B_120,A_121] :
      ( k5_relat_1(k4_relat_1(B_120),k4_relat_1(A_121)) = k4_relat_1(k5_relat_1(A_121,B_120))
      | ~ v1_relat_1(B_120)
      | ~ v1_relat_1(A_121) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_5829,plain,(
    ! [A_295,B_296] :
      ( r1_tarski(k2_relat_1(k4_relat_1(k5_relat_1(A_295,B_296))),k2_relat_1(k4_relat_1(A_295)))
      | ~ v1_relat_1(k4_relat_1(A_295))
      | ~ v1_relat_1(k4_relat_1(B_296))
      | ~ v1_relat_1(B_296)
      | ~ v1_relat_1(A_295) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_801,c_22])).

tff(c_5872,plain,
    ( r1_tarski(k2_relat_1(k4_relat_1(k6_partfun1('#skF_1'))),k2_relat_1(k4_relat_1('#skF_3')))
    | ~ v1_relat_1(k4_relat_1('#skF_3'))
    | ~ v1_relat_1(k4_relat_1('#skF_4'))
    | ~ v1_relat_1('#skF_4')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_3621,c_5829])).

tff(c_5978,plain,
    ( r1_tarski('#skF_1',k1_relat_1('#skF_3'))
    | ~ v1_relat_1(k4_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_202,c_199,c_659,c_99,c_98,c_4406,c_5872])).

tff(c_6022,plain,(
    ~ v1_relat_1(k4_relat_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_5978])).

tff(c_6025,plain,(
    ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_14,c_6022])).

tff(c_6029,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_199,c_6025])).

tff(c_6030,plain,(
    r1_tarski('#skF_1',k1_relat_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_5978])).

tff(c_6043,plain,
    ( k1_relat_1('#skF_3') = '#skF_1'
    | ~ v4_relat_1('#skF_3','#skF_1')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_6030,c_213])).

tff(c_6050,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_202,c_303,c_6043])).

tff(c_359,plain,(
    ! [A_101] :
      ( k2_relat_1(k2_funct_1(A_101)) = k1_relat_1(A_101)
      | ~ v2_funct_1(A_101)
      | ~ v1_funct_1(A_101)
      | ~ v1_relat_1(A_101) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_36,plain,(
    ! [A_29] :
      ( k5_relat_1(A_29,k6_relat_1(k2_relat_1(A_29))) = A_29
      | ~ v1_relat_1(A_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_96,plain,(
    ! [A_29] :
      ( k5_relat_1(A_29,k6_partfun1(k2_relat_1(A_29))) = A_29
      | ~ v1_relat_1(A_29) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_36])).

tff(c_368,plain,(
    ! [A_101] :
      ( k5_relat_1(k2_funct_1(A_101),k6_partfun1(k1_relat_1(A_101))) = k2_funct_1(A_101)
      | ~ v1_relat_1(k2_funct_1(A_101))
      | ~ v2_funct_1(A_101)
      | ~ v1_funct_1(A_101)
      | ~ v1_relat_1(A_101) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_359,c_96])).

tff(c_6076,plain,
    ( k5_relat_1(k2_funct_1('#skF_3'),k6_partfun1('#skF_1')) = k2_funct_1('#skF_3')
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_6050,c_368])).

tff(c_6109,plain,(
    k5_relat_1(k2_funct_1('#skF_3'),k6_partfun1('#skF_1')) = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_202,c_92,c_76,c_767,c_6076])).

tff(c_1479,plain,(
    ! [A_140,B_141,C_142] :
      ( k5_relat_1(k5_relat_1(A_140,B_141),C_142) = k5_relat_1(A_140,k5_relat_1(B_141,C_142))
      | ~ v1_relat_1(C_142)
      | ~ v1_relat_1(B_141)
      | ~ v1_relat_1(A_140) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_8511,plain,(
    ! [A_349,C_350] :
      ( k5_relat_1(k6_partfun1(k2_relat_1(A_349)),C_350) = k5_relat_1(k2_funct_1(A_349),k5_relat_1(A_349,C_350))
      | ~ v1_relat_1(C_350)
      | ~ v1_relat_1(A_349)
      | ~ v1_relat_1(k2_funct_1(A_349))
      | ~ v2_funct_1(A_349)
      | ~ v1_funct_1(A_349)
      | ~ v1_relat_1(A_349) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_95,c_1479])).

tff(c_8874,plain,(
    ! [C_350] :
      ( k5_relat_1(k2_funct_1('#skF_3'),k5_relat_1('#skF_3',C_350)) = k5_relat_1(k6_partfun1('#skF_2'),C_350)
      | ~ v1_relat_1(C_350)
      | ~ v1_relat_1('#skF_3')
      | ~ v1_relat_1(k2_funct_1('#skF_3'))
      | ~ v2_funct_1('#skF_3')
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_603,c_8511])).

tff(c_19331,plain,(
    ! [C_524] :
      ( k5_relat_1(k2_funct_1('#skF_3'),k5_relat_1('#skF_3',C_524)) = k5_relat_1(k6_partfun1('#skF_2'),C_524)
      | ~ v1_relat_1(C_524) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_202,c_92,c_76,c_767,c_202,c_8874])).

tff(c_19429,plain,
    ( k5_relat_1(k2_funct_1('#skF_3'),k6_partfun1('#skF_1')) = k5_relat_1(k6_partfun1('#skF_2'),'#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_3621,c_19331])).

tff(c_19505,plain,(
    k5_relat_1(k6_partfun1('#skF_2'),'#skF_4') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_199,c_6109,c_19429])).

tff(c_12,plain,(
    ! [B_7,A_6] :
      ( r1_tarski(k1_relat_1(B_7),A_6)
      | ~ v4_relat_1(B_7,A_6)
      | ~ v1_relat_1(B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_391,plain,(
    ! [A_6,B_7] :
      ( k5_relat_1(k6_partfun1(A_6),B_7) = B_7
      | ~ v4_relat_1(B_7,A_6)
      | ~ v1_relat_1(B_7) ) ),
    inference(resolution,[status(thm)],[c_12,c_374])).

tff(c_19663,plain,
    ( k2_funct_1('#skF_3') = '#skF_4'
    | ~ v4_relat_1('#skF_4','#skF_2')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_19505,c_391])).

tff(c_19698,plain,(
    k2_funct_1('#skF_3') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_199,c_302,c_19663])).

tff(c_19700,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_19698])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n001.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 19:33:30 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 11.68/5.01  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.68/5.02  
% 11.68/5.02  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.68/5.02  %$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k4_relat_1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 11.68/5.02  
% 11.68/5.02  %Foreground sorts:
% 11.68/5.02  
% 11.68/5.02  
% 11.68/5.02  %Background operators:
% 11.68/5.02  
% 11.68/5.02  
% 11.68/5.02  %Foreground operators:
% 11.68/5.02  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 11.68/5.02  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 11.68/5.02  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 11.68/5.02  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 11.68/5.02  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 11.68/5.02  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 11.68/5.02  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 11.68/5.02  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 11.68/5.02  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 11.68/5.02  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 11.68/5.02  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 11.68/5.02  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 11.68/5.02  tff('#skF_2', type, '#skF_2': $i).
% 11.68/5.02  tff('#skF_3', type, '#skF_3': $i).
% 11.68/5.02  tff('#skF_1', type, '#skF_1': $i).
% 11.68/5.02  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 11.68/5.02  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 11.68/5.02  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 11.68/5.02  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 11.68/5.02  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 11.68/5.02  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 11.68/5.02  tff('#skF_4', type, '#skF_4': $i).
% 11.68/5.02  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 11.68/5.02  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 11.68/5.02  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 11.68/5.02  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 11.68/5.02  tff(k4_relat_1, type, k4_relat_1: $i > $i).
% 11.68/5.02  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 11.68/5.02  
% 11.68/5.05  tff(f_194, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => ((((k2_relset_1(A, B, C) = B) & r2_relset_1(A, A, k1_partfun1(A, B, B, A, C, D), k6_partfun1(A))) & v2_funct_1(C)) => (((A = k1_xboole_0) | (B = k1_xboole_0)) | (D = k2_funct_1(C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_funct_2)).
% 11.68/5.05  tff(f_50, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 11.68/5.05  tff(f_38, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 11.68/5.05  tff(f_130, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 11.68/5.05  tff(f_104, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 11.68/5.05  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 11.68/5.05  tff(f_168, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 11.68/5.05  tff(f_84, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 11.68/5.05  tff(f_134, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 11.68/5.05  tff(f_124, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k5_relat_1(A, k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))) & (k5_relat_1(k2_funct_1(A), A) = k6_relat_1(k2_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t61_funct_1)).
% 11.68/5.05  tff(f_63, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => r1_tarski(k2_relat_1(k5_relat_1(A, B)), k2_relat_1(B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t45_relat_1)).
% 11.68/5.05  tff(f_48, axiom, (![A]: (v1_relat_1(A) => v1_relat_1(k4_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k4_relat_1)).
% 11.68/5.05  tff(f_56, axiom, (![A]: (v1_relat_1(A) => ((k2_relat_1(A) = k1_relat_1(k4_relat_1(A))) & (k1_relat_1(A) = k2_relat_1(k4_relat_1(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t37_relat_1)).
% 11.68/5.05  tff(f_44, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d18_relat_1)).
% 11.68/5.05  tff(f_86, axiom, (![A]: (k4_relat_1(k6_relat_1(A)) = k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_relat_1)).
% 11.68/5.05  tff(f_144, axiom, (![A]: m1_subset_1(k6_relat_1(A), k1_zfmisc_1(k2_zfmisc_1(A, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_relset_1)).
% 11.68/5.05  tff(f_92, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(B), A) => (k5_relat_1(k6_relat_1(A), B) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t77_relat_1)).
% 11.68/5.05  tff(f_156, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (v1_funct_1(k1_partfun1(A, B, C, D, E, F)) & m1_subset_1(k1_partfun1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 11.68/5.05  tff(f_142, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 11.68/5.05  tff(f_166, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 11.68/5.05  tff(f_70, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k4_relat_1(k5_relat_1(A, B)) = k5_relat_1(k4_relat_1(B), k4_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t54_relat_1)).
% 11.68/5.05  tff(f_114, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k2_relat_1(A) = k1_relat_1(k2_funct_1(A))) & (k1_relat_1(A) = k2_relat_1(k2_funct_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_funct_1)).
% 11.68/5.05  tff(f_96, axiom, (![A]: (v1_relat_1(A) => (k5_relat_1(A, k6_relat_1(k2_relat_1(A))) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t80_relat_1)).
% 11.68/5.05  tff(f_80, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (k5_relat_1(k5_relat_1(A, B), C) = k5_relat_1(A, k5_relat_1(B, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_relat_1)).
% 11.68/5.05  tff(c_70, plain, (k2_funct_1('#skF_3')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_194])).
% 11.68/5.05  tff(c_16, plain, (![A_9, B_10]: (v1_relat_1(k2_zfmisc_1(A_9, B_10)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 11.68/5.05  tff(c_82, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_194])).
% 11.68/5.05  tff(c_184, plain, (![B_73, A_74]: (v1_relat_1(B_73) | ~m1_subset_1(B_73, k1_zfmisc_1(A_74)) | ~v1_relat_1(A_74))), inference(cnfTransformation, [status(thm)], [f_38])).
% 11.68/5.05  tff(c_190, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_1'))), inference(resolution, [status(thm)], [c_82, c_184])).
% 11.68/5.05  tff(c_199, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_16, c_190])).
% 11.68/5.05  tff(c_291, plain, (![C_89, A_90, B_91]: (v4_relat_1(C_89, A_90) | ~m1_subset_1(C_89, k1_zfmisc_1(k2_zfmisc_1(A_90, B_91))))), inference(cnfTransformation, [status(thm)], [f_130])).
% 11.68/5.05  tff(c_302, plain, (v4_relat_1('#skF_4', '#skF_2')), inference(resolution, [status(thm)], [c_82, c_291])).
% 11.68/5.05  tff(c_88, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_194])).
% 11.68/5.05  tff(c_193, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_88, c_184])).
% 11.68/5.05  tff(c_202, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_16, c_193])).
% 11.68/5.05  tff(c_92, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_194])).
% 11.68/5.05  tff(c_76, plain, (v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_194])).
% 11.68/5.05  tff(c_40, plain, (![A_30]: (v1_relat_1(k2_funct_1(A_30)) | ~v1_funct_1(A_30) | ~v1_relat_1(A_30))), inference(cnfTransformation, [status(thm)], [f_104])).
% 11.68/5.05  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 11.68/5.05  tff(c_68, plain, (![A_56]: (k6_relat_1(A_56)=k6_partfun1(A_56))), inference(cnfTransformation, [status(thm)], [f_168])).
% 11.68/5.05  tff(c_30, plain, (![A_25]: (k2_relat_1(k6_relat_1(A_25))=A_25)), inference(cnfTransformation, [status(thm)], [f_84])).
% 11.68/5.05  tff(c_99, plain, (![A_25]: (k2_relat_1(k6_partfun1(A_25))=A_25)), inference(demodulation, [status(thm), theory('equality')], [c_68, c_30])).
% 11.68/5.05  tff(c_80, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_2'), inference(cnfTransformation, [status(thm)], [f_194])).
% 11.68/5.05  tff(c_589, plain, (![A_113, B_114, C_115]: (k2_relset_1(A_113, B_114, C_115)=k2_relat_1(C_115) | ~m1_subset_1(C_115, k1_zfmisc_1(k2_zfmisc_1(A_113, B_114))))), inference(cnfTransformation, [status(thm)], [f_134])).
% 11.68/5.05  tff(c_598, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_88, c_589])).
% 11.68/5.05  tff(c_603, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_80, c_598])).
% 11.68/5.05  tff(c_46, plain, (![A_32]: (k5_relat_1(k2_funct_1(A_32), A_32)=k6_relat_1(k2_relat_1(A_32)) | ~v2_funct_1(A_32) | ~v1_funct_1(A_32) | ~v1_relat_1(A_32))), inference(cnfTransformation, [status(thm)], [f_124])).
% 11.68/5.05  tff(c_95, plain, (![A_32]: (k5_relat_1(k2_funct_1(A_32), A_32)=k6_partfun1(k2_relat_1(A_32)) | ~v2_funct_1(A_32) | ~v1_funct_1(A_32) | ~v1_relat_1(A_32))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_46])).
% 11.68/5.05  tff(c_22, plain, (![A_12, B_14]: (r1_tarski(k2_relat_1(k5_relat_1(A_12, B_14)), k2_relat_1(B_14)) | ~v1_relat_1(B_14) | ~v1_relat_1(A_12))), inference(cnfTransformation, [status(thm)], [f_63])).
% 11.68/5.05  tff(c_611, plain, (![A_12]: (r1_tarski(k2_relat_1(k5_relat_1(A_12, '#skF_3')), '#skF_2') | ~v1_relat_1('#skF_3') | ~v1_relat_1(A_12))), inference(superposition, [status(thm), theory('equality')], [c_603, c_22])).
% 11.68/5.05  tff(c_679, plain, (![A_118]: (r1_tarski(k2_relat_1(k5_relat_1(A_118, '#skF_3')), '#skF_2') | ~v1_relat_1(A_118))), inference(demodulation, [status(thm), theory('equality')], [c_202, c_611])).
% 11.68/5.05  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 11.68/5.05  tff(c_701, plain, (![A_119]: (k2_relat_1(k5_relat_1(A_119, '#skF_3'))='#skF_2' | ~r1_tarski('#skF_2', k2_relat_1(k5_relat_1(A_119, '#skF_3'))) | ~v1_relat_1(A_119))), inference(resolution, [status(thm)], [c_679, c_2])).
% 11.68/5.05  tff(c_705, plain, (k2_relat_1(k5_relat_1(k2_funct_1('#skF_3'), '#skF_3'))='#skF_2' | ~r1_tarski('#skF_2', k2_relat_1(k6_partfun1(k2_relat_1('#skF_3')))) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_95, c_701])).
% 11.68/5.05  tff(c_715, plain, (k2_relat_1(k5_relat_1(k2_funct_1('#skF_3'), '#skF_3'))='#skF_2' | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_202, c_92, c_76, c_6, c_99, c_603, c_705])).
% 11.68/5.05  tff(c_758, plain, (~v1_relat_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_715])).
% 11.68/5.05  tff(c_761, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_40, c_758])).
% 11.68/5.05  tff(c_765, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_202, c_92, c_761])).
% 11.68/5.05  tff(c_767, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_715])).
% 11.68/5.05  tff(c_303, plain, (v4_relat_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_88, c_291])).
% 11.68/5.05  tff(c_14, plain, (![A_8]: (v1_relat_1(k4_relat_1(A_8)) | ~v1_relat_1(A_8))), inference(cnfTransformation, [status(thm)], [f_48])).
% 11.68/5.05  tff(c_20, plain, (![A_11]: (k1_relat_1(k4_relat_1(A_11))=k2_relat_1(A_11) | ~v1_relat_1(A_11))), inference(cnfTransformation, [status(thm)], [f_56])).
% 11.68/5.05  tff(c_243, plain, (![B_82, A_83]: (v4_relat_1(B_82, A_83) | ~r1_tarski(k1_relat_1(B_82), A_83) | ~v1_relat_1(B_82))), inference(cnfTransformation, [status(thm)], [f_44])).
% 11.68/5.05  tff(c_261, plain, (![B_84]: (v4_relat_1(B_84, k1_relat_1(B_84)) | ~v1_relat_1(B_84))), inference(resolution, [status(thm)], [c_6, c_243])).
% 11.68/5.05  tff(c_268, plain, (![A_11]: (v4_relat_1(k4_relat_1(A_11), k2_relat_1(A_11)) | ~v1_relat_1(k4_relat_1(A_11)) | ~v1_relat_1(A_11))), inference(superposition, [status(thm), theory('equality')], [c_20, c_261])).
% 11.68/5.05  tff(c_614, plain, (v4_relat_1(k4_relat_1('#skF_3'), '#skF_2') | ~v1_relat_1(k4_relat_1('#skF_3')) | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_603, c_268])).
% 11.68/5.05  tff(c_623, plain, (v4_relat_1(k4_relat_1('#skF_3'), '#skF_2') | ~v1_relat_1(k4_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_202, c_614])).
% 11.68/5.05  tff(c_650, plain, (~v1_relat_1(k4_relat_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_623])).
% 11.68/5.05  tff(c_653, plain, (~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_14, c_650])).
% 11.68/5.05  tff(c_657, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_202, c_653])).
% 11.68/5.05  tff(c_659, plain, (v1_relat_1(k4_relat_1('#skF_3'))), inference(splitRight, [status(thm)], [c_623])).
% 11.68/5.05  tff(c_32, plain, (![A_26]: (k4_relat_1(k6_relat_1(A_26))=k6_relat_1(A_26))), inference(cnfTransformation, [status(thm)], [f_86])).
% 11.68/5.05  tff(c_98, plain, (![A_26]: (k4_relat_1(k6_partfun1(A_26))=k6_partfun1(A_26))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_68, c_32])).
% 11.68/5.05  tff(c_260, plain, (![B_82]: (v4_relat_1(B_82, k1_relat_1(B_82)) | ~v1_relat_1(B_82))), inference(resolution, [status(thm)], [c_6, c_243])).
% 11.68/5.05  tff(c_18, plain, (![A_11]: (k2_relat_1(k4_relat_1(A_11))=k1_relat_1(A_11) | ~v1_relat_1(A_11))), inference(cnfTransformation, [status(thm)], [f_56])).
% 11.68/5.05  tff(c_60, plain, (![A_43]: (m1_subset_1(k6_relat_1(A_43), k1_zfmisc_1(k2_zfmisc_1(A_43, A_43))))), inference(cnfTransformation, [status(thm)], [f_144])).
% 11.68/5.05  tff(c_93, plain, (![A_43]: (m1_subset_1(k6_partfun1(A_43), k1_zfmisc_1(k2_zfmisc_1(A_43, A_43))))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_60])).
% 11.68/5.05  tff(c_187, plain, (![A_43]: (v1_relat_1(k6_partfun1(A_43)) | ~v1_relat_1(k2_zfmisc_1(A_43, A_43)))), inference(resolution, [status(thm)], [c_93, c_184])).
% 11.68/5.05  tff(c_196, plain, (![A_43]: (v1_relat_1(k6_partfun1(A_43)))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_187])).
% 11.68/5.05  tff(c_658, plain, (v4_relat_1(k4_relat_1('#skF_3'), '#skF_2')), inference(splitRight, [status(thm)], [c_623])).
% 11.68/5.05  tff(c_204, plain, (![B_76, A_77]: (r1_tarski(k1_relat_1(B_76), A_77) | ~v4_relat_1(B_76, A_77) | ~v1_relat_1(B_76))), inference(cnfTransformation, [status(thm)], [f_44])).
% 11.68/5.05  tff(c_3122, plain, (![A_244, A_245]: (r1_tarski(k2_relat_1(A_244), A_245) | ~v4_relat_1(k4_relat_1(A_244), A_245) | ~v1_relat_1(k4_relat_1(A_244)) | ~v1_relat_1(A_244))), inference(superposition, [status(thm), theory('equality')], [c_20, c_204])).
% 11.68/5.05  tff(c_3148, plain, (![A_246]: (r1_tarski(k2_relat_1(A_246), k1_relat_1(k4_relat_1(A_246))) | ~v1_relat_1(A_246) | ~v1_relat_1(k4_relat_1(A_246)))), inference(resolution, [status(thm)], [c_260, c_3122])).
% 11.68/5.05  tff(c_3170, plain, (r1_tarski('#skF_2', k1_relat_1(k4_relat_1('#skF_3'))) | ~v1_relat_1('#skF_3') | ~v1_relat_1(k4_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_603, c_3148])).
% 11.68/5.05  tff(c_3193, plain, (r1_tarski('#skF_2', k1_relat_1(k4_relat_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_659, c_202, c_3170])).
% 11.68/5.05  tff(c_213, plain, (![B_76, A_77]: (k1_relat_1(B_76)=A_77 | ~r1_tarski(A_77, k1_relat_1(B_76)) | ~v4_relat_1(B_76, A_77) | ~v1_relat_1(B_76))), inference(resolution, [status(thm)], [c_204, c_2])).
% 11.68/5.05  tff(c_3222, plain, (k1_relat_1(k4_relat_1('#skF_3'))='#skF_2' | ~v4_relat_1(k4_relat_1('#skF_3'), '#skF_2') | ~v1_relat_1(k4_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_3193, c_213])).
% 11.68/5.05  tff(c_3232, plain, (k1_relat_1(k4_relat_1('#skF_3'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_659, c_658, c_3222])).
% 11.68/5.05  tff(c_34, plain, (![A_27, B_28]: (k5_relat_1(k6_relat_1(A_27), B_28)=B_28 | ~r1_tarski(k1_relat_1(B_28), A_27) | ~v1_relat_1(B_28))), inference(cnfTransformation, [status(thm)], [f_92])).
% 11.68/5.05  tff(c_374, plain, (![A_102, B_103]: (k5_relat_1(k6_partfun1(A_102), B_103)=B_103 | ~r1_tarski(k1_relat_1(B_103), A_102) | ~v1_relat_1(B_103))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_34])).
% 11.68/5.05  tff(c_394, plain, (![B_103]: (k5_relat_1(k6_partfun1(k1_relat_1(B_103)), B_103)=B_103 | ~v1_relat_1(B_103))), inference(resolution, [status(thm)], [c_6, c_374])).
% 11.68/5.05  tff(c_3248, plain, (k5_relat_1(k6_partfun1('#skF_2'), k4_relat_1('#skF_3'))=k4_relat_1('#skF_3') | ~v1_relat_1(k4_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_3232, c_394])).
% 11.68/5.05  tff(c_3274, plain, (k5_relat_1(k6_partfun1('#skF_2'), k4_relat_1('#skF_3'))=k4_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_659, c_3248])).
% 11.68/5.05  tff(c_458, plain, (![A_107, B_108]: (r1_tarski(k2_relat_1(k5_relat_1(A_107, B_108)), k2_relat_1(B_108)) | ~v1_relat_1(B_108) | ~v1_relat_1(A_107))), inference(cnfTransformation, [status(thm)], [f_63])).
% 11.68/5.05  tff(c_3863, plain, (![A_261, A_262]: (r1_tarski(k2_relat_1(k5_relat_1(A_261, k4_relat_1(A_262))), k1_relat_1(A_262)) | ~v1_relat_1(k4_relat_1(A_262)) | ~v1_relat_1(A_261) | ~v1_relat_1(A_262))), inference(superposition, [status(thm), theory('equality')], [c_18, c_458])).
% 11.68/5.05  tff(c_3873, plain, (r1_tarski(k2_relat_1(k4_relat_1('#skF_3')), k1_relat_1('#skF_3')) | ~v1_relat_1(k4_relat_1('#skF_3')) | ~v1_relat_1(k6_partfun1('#skF_2')) | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_3274, c_3863])).
% 11.68/5.05  tff(c_3921, plain, (r1_tarski(k2_relat_1(k4_relat_1('#skF_3')), k1_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_202, c_196, c_659, c_3873])).
% 11.68/5.05  tff(c_3940, plain, (k2_relat_1(k4_relat_1('#skF_3'))=k1_relat_1('#skF_3') | ~v4_relat_1('#skF_3', k2_relat_1(k4_relat_1('#skF_3'))) | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_3921, c_213])).
% 11.68/5.05  tff(c_3950, plain, (k2_relat_1(k4_relat_1('#skF_3'))=k1_relat_1('#skF_3') | ~v4_relat_1('#skF_3', k2_relat_1(k4_relat_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_202, c_3940])).
% 11.68/5.05  tff(c_4355, plain, (~v4_relat_1('#skF_3', k2_relat_1(k4_relat_1('#skF_3')))), inference(splitLeft, [status(thm)], [c_3950])).
% 11.68/5.05  tff(c_4358, plain, (~v4_relat_1('#skF_3', k1_relat_1('#skF_3')) | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_18, c_4355])).
% 11.68/5.05  tff(c_4360, plain, (~v4_relat_1('#skF_3', k1_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_202, c_4358])).
% 11.68/5.05  tff(c_4401, plain, (~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_260, c_4360])).
% 11.68/5.05  tff(c_4405, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_202, c_4401])).
% 11.68/5.05  tff(c_4406, plain, (k2_relat_1(k4_relat_1('#skF_3'))=k1_relat_1('#skF_3')), inference(splitRight, [status(thm)], [c_3950])).
% 11.68/5.05  tff(c_86, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_194])).
% 11.68/5.05  tff(c_2400, plain, (![D_196, F_195, C_197, E_194, B_198, A_199]: (m1_subset_1(k1_partfun1(A_199, B_198, C_197, D_196, E_194, F_195), k1_zfmisc_1(k2_zfmisc_1(A_199, D_196))) | ~m1_subset_1(F_195, k1_zfmisc_1(k2_zfmisc_1(C_197, D_196))) | ~v1_funct_1(F_195) | ~m1_subset_1(E_194, k1_zfmisc_1(k2_zfmisc_1(A_199, B_198))) | ~v1_funct_1(E_194))), inference(cnfTransformation, [status(thm)], [f_156])).
% 11.68/5.05  tff(c_78, plain, (r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k6_partfun1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_194])).
% 11.68/5.05  tff(c_1870, plain, (![D_150, C_151, A_152, B_153]: (D_150=C_151 | ~r2_relset_1(A_152, B_153, C_151, D_150) | ~m1_subset_1(D_150, k1_zfmisc_1(k2_zfmisc_1(A_152, B_153))) | ~m1_subset_1(C_151, k1_zfmisc_1(k2_zfmisc_1(A_152, B_153))))), inference(cnfTransformation, [status(thm)], [f_142])).
% 11.68/5.05  tff(c_1878, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_78, c_1870])).
% 11.68/5.05  tff(c_1893, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_93, c_1878])).
% 11.68/5.05  tff(c_1990, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_1893])).
% 11.68/5.05  tff(c_2413, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_2400, c_1990])).
% 11.68/5.05  tff(c_2435, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_92, c_88, c_86, c_82, c_2413])).
% 11.68/5.05  tff(c_2436, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_1893])).
% 11.68/5.05  tff(c_2946, plain, (![D_231, C_228, F_230, B_229, A_227, E_226]: (k1_partfun1(A_227, B_229, C_228, D_231, E_226, F_230)=k5_relat_1(E_226, F_230) | ~m1_subset_1(F_230, k1_zfmisc_1(k2_zfmisc_1(C_228, D_231))) | ~v1_funct_1(F_230) | ~m1_subset_1(E_226, k1_zfmisc_1(k2_zfmisc_1(A_227, B_229))) | ~v1_funct_1(E_226))), inference(cnfTransformation, [status(thm)], [f_166])).
% 11.68/5.05  tff(c_2950, plain, (![A_227, B_229, E_226]: (k1_partfun1(A_227, B_229, '#skF_2', '#skF_1', E_226, '#skF_4')=k5_relat_1(E_226, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_226, k1_zfmisc_1(k2_zfmisc_1(A_227, B_229))) | ~v1_funct_1(E_226))), inference(resolution, [status(thm)], [c_82, c_2946])).
% 11.68/5.05  tff(c_3589, plain, (![A_256, B_257, E_258]: (k1_partfun1(A_256, B_257, '#skF_2', '#skF_1', E_258, '#skF_4')=k5_relat_1(E_258, '#skF_4') | ~m1_subset_1(E_258, k1_zfmisc_1(k2_zfmisc_1(A_256, B_257))) | ~v1_funct_1(E_258))), inference(demodulation, [status(thm), theory('equality')], [c_86, c_2950])).
% 11.68/5.05  tff(c_3607, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_88, c_3589])).
% 11.68/5.05  tff(c_3621, plain, (k5_relat_1('#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_92, c_2436, c_3607])).
% 11.68/5.05  tff(c_801, plain, (![B_120, A_121]: (k5_relat_1(k4_relat_1(B_120), k4_relat_1(A_121))=k4_relat_1(k5_relat_1(A_121, B_120)) | ~v1_relat_1(B_120) | ~v1_relat_1(A_121))), inference(cnfTransformation, [status(thm)], [f_70])).
% 11.68/5.05  tff(c_5829, plain, (![A_295, B_296]: (r1_tarski(k2_relat_1(k4_relat_1(k5_relat_1(A_295, B_296))), k2_relat_1(k4_relat_1(A_295))) | ~v1_relat_1(k4_relat_1(A_295)) | ~v1_relat_1(k4_relat_1(B_296)) | ~v1_relat_1(B_296) | ~v1_relat_1(A_295))), inference(superposition, [status(thm), theory('equality')], [c_801, c_22])).
% 11.68/5.05  tff(c_5872, plain, (r1_tarski(k2_relat_1(k4_relat_1(k6_partfun1('#skF_1'))), k2_relat_1(k4_relat_1('#skF_3'))) | ~v1_relat_1(k4_relat_1('#skF_3')) | ~v1_relat_1(k4_relat_1('#skF_4')) | ~v1_relat_1('#skF_4') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_3621, c_5829])).
% 11.68/5.05  tff(c_5978, plain, (r1_tarski('#skF_1', k1_relat_1('#skF_3')) | ~v1_relat_1(k4_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_202, c_199, c_659, c_99, c_98, c_4406, c_5872])).
% 11.68/5.05  tff(c_6022, plain, (~v1_relat_1(k4_relat_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_5978])).
% 11.68/5.05  tff(c_6025, plain, (~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_14, c_6022])).
% 11.68/5.05  tff(c_6029, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_199, c_6025])).
% 11.68/5.05  tff(c_6030, plain, (r1_tarski('#skF_1', k1_relat_1('#skF_3'))), inference(splitRight, [status(thm)], [c_5978])).
% 11.68/5.05  tff(c_6043, plain, (k1_relat_1('#skF_3')='#skF_1' | ~v4_relat_1('#skF_3', '#skF_1') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_6030, c_213])).
% 11.68/5.05  tff(c_6050, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_202, c_303, c_6043])).
% 11.68/5.05  tff(c_359, plain, (![A_101]: (k2_relat_1(k2_funct_1(A_101))=k1_relat_1(A_101) | ~v2_funct_1(A_101) | ~v1_funct_1(A_101) | ~v1_relat_1(A_101))), inference(cnfTransformation, [status(thm)], [f_114])).
% 11.68/5.05  tff(c_36, plain, (![A_29]: (k5_relat_1(A_29, k6_relat_1(k2_relat_1(A_29)))=A_29 | ~v1_relat_1(A_29))), inference(cnfTransformation, [status(thm)], [f_96])).
% 11.68/5.05  tff(c_96, plain, (![A_29]: (k5_relat_1(A_29, k6_partfun1(k2_relat_1(A_29)))=A_29 | ~v1_relat_1(A_29))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_36])).
% 11.68/5.05  tff(c_368, plain, (![A_101]: (k5_relat_1(k2_funct_1(A_101), k6_partfun1(k1_relat_1(A_101)))=k2_funct_1(A_101) | ~v1_relat_1(k2_funct_1(A_101)) | ~v2_funct_1(A_101) | ~v1_funct_1(A_101) | ~v1_relat_1(A_101))), inference(superposition, [status(thm), theory('equality')], [c_359, c_96])).
% 11.68/5.05  tff(c_6076, plain, (k5_relat_1(k2_funct_1('#skF_3'), k6_partfun1('#skF_1'))=k2_funct_1('#skF_3') | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_6050, c_368])).
% 11.68/5.05  tff(c_6109, plain, (k5_relat_1(k2_funct_1('#skF_3'), k6_partfun1('#skF_1'))=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_202, c_92, c_76, c_767, c_6076])).
% 11.68/5.05  tff(c_1479, plain, (![A_140, B_141, C_142]: (k5_relat_1(k5_relat_1(A_140, B_141), C_142)=k5_relat_1(A_140, k5_relat_1(B_141, C_142)) | ~v1_relat_1(C_142) | ~v1_relat_1(B_141) | ~v1_relat_1(A_140))), inference(cnfTransformation, [status(thm)], [f_80])).
% 11.68/5.05  tff(c_8511, plain, (![A_349, C_350]: (k5_relat_1(k6_partfun1(k2_relat_1(A_349)), C_350)=k5_relat_1(k2_funct_1(A_349), k5_relat_1(A_349, C_350)) | ~v1_relat_1(C_350) | ~v1_relat_1(A_349) | ~v1_relat_1(k2_funct_1(A_349)) | ~v2_funct_1(A_349) | ~v1_funct_1(A_349) | ~v1_relat_1(A_349))), inference(superposition, [status(thm), theory('equality')], [c_95, c_1479])).
% 11.68/5.05  tff(c_8874, plain, (![C_350]: (k5_relat_1(k2_funct_1('#skF_3'), k5_relat_1('#skF_3', C_350))=k5_relat_1(k6_partfun1('#skF_2'), C_350) | ~v1_relat_1(C_350) | ~v1_relat_1('#skF_3') | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_603, c_8511])).
% 11.68/5.05  tff(c_19331, plain, (![C_524]: (k5_relat_1(k2_funct_1('#skF_3'), k5_relat_1('#skF_3', C_524))=k5_relat_1(k6_partfun1('#skF_2'), C_524) | ~v1_relat_1(C_524))), inference(demodulation, [status(thm), theory('equality')], [c_202, c_92, c_76, c_767, c_202, c_8874])).
% 11.68/5.05  tff(c_19429, plain, (k5_relat_1(k2_funct_1('#skF_3'), k6_partfun1('#skF_1'))=k5_relat_1(k6_partfun1('#skF_2'), '#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_3621, c_19331])).
% 11.68/5.05  tff(c_19505, plain, (k5_relat_1(k6_partfun1('#skF_2'), '#skF_4')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_199, c_6109, c_19429])).
% 11.68/5.05  tff(c_12, plain, (![B_7, A_6]: (r1_tarski(k1_relat_1(B_7), A_6) | ~v4_relat_1(B_7, A_6) | ~v1_relat_1(B_7))), inference(cnfTransformation, [status(thm)], [f_44])).
% 11.68/5.05  tff(c_391, plain, (![A_6, B_7]: (k5_relat_1(k6_partfun1(A_6), B_7)=B_7 | ~v4_relat_1(B_7, A_6) | ~v1_relat_1(B_7))), inference(resolution, [status(thm)], [c_12, c_374])).
% 11.68/5.05  tff(c_19663, plain, (k2_funct_1('#skF_3')='#skF_4' | ~v4_relat_1('#skF_4', '#skF_2') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_19505, c_391])).
% 11.68/5.05  tff(c_19698, plain, (k2_funct_1('#skF_3')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_199, c_302, c_19663])).
% 11.68/5.05  tff(c_19700, plain, $false, inference(negUnitSimplification, [status(thm)], [c_70, c_19698])).
% 11.68/5.05  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.68/5.05  
% 11.68/5.05  Inference rules
% 11.68/5.05  ----------------------
% 11.68/5.05  #Ref     : 0
% 11.68/5.05  #Sup     : 4158
% 11.68/5.05  #Fact    : 0
% 11.68/5.05  #Define  : 0
% 11.68/5.05  #Split   : 18
% 11.68/5.05  #Chain   : 0
% 11.68/5.05  #Close   : 0
% 11.68/5.05  
% 11.68/5.05  Ordering : KBO
% 11.68/5.05  
% 11.68/5.05  Simplification rules
% 11.68/5.05  ----------------------
% 11.68/5.05  #Subsume      : 244
% 11.68/5.05  #Demod        : 7457
% 11.68/5.05  #Tautology    : 1636
% 11.68/5.05  #SimpNegUnit  : 1
% 11.68/5.05  #BackRed      : 42
% 11.68/5.05  
% 11.68/5.05  #Partial instantiations: 0
% 11.68/5.05  #Strategies tried      : 1
% 11.68/5.05  
% 11.68/5.05  Timing (in seconds)
% 11.68/5.05  ----------------------
% 11.68/5.05  Preprocessing        : 0.37
% 11.68/5.05  Parsing              : 0.20
% 11.68/5.05  CNF conversion       : 0.03
% 11.68/5.05  Main loop            : 3.91
% 11.68/5.05  Inferencing          : 0.92
% 11.68/5.05  Reduction            : 1.95
% 11.68/5.05  Demodulation         : 1.64
% 11.68/5.05  BG Simplification    : 0.10
% 11.68/5.05  Subsumption          : 0.76
% 11.68/5.05  Abstraction          : 0.13
% 11.68/5.05  MUC search           : 0.00
% 11.68/5.05  Cooper               : 0.00
% 11.68/5.05  Total                : 4.33
% 11.68/5.05  Index Insertion      : 0.00
% 11.68/5.05  Index Deletion       : 0.00
% 11.68/5.05  Index Matching       : 0.00
% 11.68/5.05  BG Taut test         : 0.00
%------------------------------------------------------------------------------
