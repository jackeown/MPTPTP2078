%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:13:14 EST 2020

% Result     : Theorem 5.91s
% Output     : CNFRefutation 5.91s
% Verified   : 
% Statistics : Number of formulae       :  115 ( 421 expanded)
%              Number of leaves         :   47 ( 166 expanded)
%              Depth                    :   14
%              Number of atoms          :  214 (1377 expanded)
%              Number of equality atoms :   56 ( 354 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k4_relat_1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(v1_partfun1,type,(
    v1_partfun1: ( $i * $i ) > $o )).

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

tff(f_170,negated_conjecture,(
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

tff(f_44,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_32,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_104,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_128,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( v1_funct_1(k1_partfun1(A,B,C,D,E,F))
        & m1_subset_1(k1_partfun1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).

tff(f_132,axiom,(
    ! [A] :
      ( v1_partfun1(k6_partfun1(A),A)
      & m1_subset_1(k6_partfun1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_partfun1)).

tff(f_116,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_142,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_80,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => k2_funct_1(A) = k4_relat_1(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_funct_1)).

tff(f_42,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => v1_relat_1(k4_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_relat_1)).

tff(f_108,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_144,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_98,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k5_relat_1(A,k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))
          & k5_relat_1(k2_funct_1(A),A) = k6_relat_1(k2_relat_1(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_funct_1)).

tff(f_60,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ! [C] :
              ( v1_relat_1(C)
             => k5_relat_1(k5_relat_1(A,B),C) = k5_relat_1(A,k5_relat_1(B,C)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_relat_1)).

tff(f_50,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( k2_relat_1(A) = k1_relat_1(k4_relat_1(A))
        & k1_relat_1(A) = k2_relat_1(k4_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_relat_1)).

tff(f_72,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k2_relat_1(B),A)
       => k5_relat_1(B,k6_relat_1(A)) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_relat_1)).

tff(f_66,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k1_relat_1(B),A)
       => k5_relat_1(k6_relat_1(A),B) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_relat_1)).

tff(c_54,plain,(
    k2_funct_1('#skF_3') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_10,plain,(
    ! [A_7,B_8] : v1_relat_1(k2_zfmisc_1(A_7,B_8)) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_66,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_118,plain,(
    ! [B_59,A_60] :
      ( v1_relat_1(B_59)
      | ~ m1_subset_1(B_59,k1_zfmisc_1(A_60))
      | ~ v1_relat_1(A_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_127,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_1')) ),
    inference(resolution,[status(thm)],[c_66,c_118])).

tff(c_136,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_127])).

tff(c_164,plain,(
    ! [C_70,A_71,B_72] :
      ( v4_relat_1(C_70,A_71)
      | ~ m1_subset_1(C_70,k1_zfmisc_1(k2_zfmisc_1(A_71,B_72))) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_176,plain,(
    v4_relat_1('#skF_4','#skF_2') ),
    inference(resolution,[status(thm)],[c_66,c_164])).

tff(c_72,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_124,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_72,c_118])).

tff(c_133,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_124])).

tff(c_175,plain,(
    v4_relat_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_72,c_164])).

tff(c_6,plain,(
    ! [B_5,A_4] :
      ( r1_tarski(k1_relat_1(B_5),A_4)
      | ~ v4_relat_1(B_5,A_4)
      | ~ v1_relat_1(B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_76,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_70,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_989,plain,(
    ! [A_156,F_158,C_161,D_157,E_159,B_160] :
      ( m1_subset_1(k1_partfun1(A_156,B_160,C_161,D_157,E_159,F_158),k1_zfmisc_1(k2_zfmisc_1(A_156,D_157)))
      | ~ m1_subset_1(F_158,k1_zfmisc_1(k2_zfmisc_1(C_161,D_157)))
      | ~ v1_funct_1(F_158)
      | ~ m1_subset_1(E_159,k1_zfmisc_1(k2_zfmisc_1(A_156,B_160)))
      | ~ v1_funct_1(E_159) ) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_48,plain,(
    ! [A_40] : m1_subset_1(k6_partfun1(A_40),k1_zfmisc_1(k2_zfmisc_1(A_40,A_40))) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_62,plain,(
    r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k6_partfun1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_758,plain,(
    ! [D_119,C_120,A_121,B_122] :
      ( D_119 = C_120
      | ~ r2_relset_1(A_121,B_122,C_120,D_119)
      | ~ m1_subset_1(D_119,k1_zfmisc_1(k2_zfmisc_1(A_121,B_122)))
      | ~ m1_subset_1(C_120,k1_zfmisc_1(k2_zfmisc_1(A_121,B_122))) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_766,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_62,c_758])).

tff(c_781,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_766])).

tff(c_849,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_781])).

tff(c_1005,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_989,c_849])).

tff(c_1034,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_72,c_70,c_66,c_1005])).

tff(c_1035,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_781])).

tff(c_1144,plain,(
    ! [C_181,D_182,F_183,A_180,B_184,E_179] :
      ( k1_partfun1(A_180,B_184,C_181,D_182,E_179,F_183) = k5_relat_1(E_179,F_183)
      | ~ m1_subset_1(F_183,k1_zfmisc_1(k2_zfmisc_1(C_181,D_182)))
      | ~ v1_funct_1(F_183)
      | ~ m1_subset_1(E_179,k1_zfmisc_1(k2_zfmisc_1(A_180,B_184)))
      | ~ v1_funct_1(E_179) ) ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_1150,plain,(
    ! [A_180,B_184,E_179] :
      ( k1_partfun1(A_180,B_184,'#skF_2','#skF_1',E_179,'#skF_4') = k5_relat_1(E_179,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_179,k1_zfmisc_1(k2_zfmisc_1(A_180,B_184)))
      | ~ v1_funct_1(E_179) ) ),
    inference(resolution,[status(thm)],[c_66,c_1144])).

tff(c_1299,plain,(
    ! [A_199,B_200,E_201] :
      ( k1_partfun1(A_199,B_200,'#skF_2','#skF_1',E_201,'#skF_4') = k5_relat_1(E_201,'#skF_4')
      | ~ m1_subset_1(E_201,k1_zfmisc_1(k2_zfmisc_1(A_199,B_200)))
      | ~ v1_funct_1(E_201) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_1150])).

tff(c_1311,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_72,c_1299])).

tff(c_1322,plain,(
    k5_relat_1('#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_1035,c_1311])).

tff(c_60,plain,(
    v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_178,plain,(
    ! [A_74] :
      ( k4_relat_1(A_74) = k2_funct_1(A_74)
      | ~ v2_funct_1(A_74)
      | ~ v1_funct_1(A_74)
      | ~ v1_relat_1(A_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_181,plain,
    ( k4_relat_1('#skF_3') = k2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_60,c_178])).

tff(c_184,plain,(
    k4_relat_1('#skF_3') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_133,c_76,c_181])).

tff(c_8,plain,(
    ! [A_6] :
      ( v1_relat_1(k4_relat_1(A_6))
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_194,plain,
    ( v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_184,c_8])).

tff(c_202,plain,(
    v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_133,c_194])).

tff(c_64,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_301,plain,(
    ! [A_89,B_90,C_91] :
      ( k2_relset_1(A_89,B_90,C_91) = k2_relat_1(C_91)
      | ~ m1_subset_1(C_91,k1_zfmisc_1(k2_zfmisc_1(A_89,B_90))) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_307,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_72,c_301])).

tff(c_313,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_307])).

tff(c_52,plain,(
    ! [A_47] : k6_relat_1(A_47) = k6_partfun1(A_47) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_28,plain,(
    ! [A_23] :
      ( k5_relat_1(k2_funct_1(A_23),A_23) = k6_relat_1(k2_relat_1(A_23))
      | ~ v2_funct_1(A_23)
      | ~ v1_funct_1(A_23)
      | ~ v1_relat_1(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_78,plain,(
    ! [A_23] :
      ( k5_relat_1(k2_funct_1(A_23),A_23) = k6_partfun1(k2_relat_1(A_23))
      | ~ v2_funct_1(A_23)
      | ~ v1_funct_1(A_23)
      | ~ v1_relat_1(A_23) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_28])).

tff(c_427,plain,(
    ! [A_99,B_100,C_101] :
      ( k5_relat_1(k5_relat_1(A_99,B_100),C_101) = k5_relat_1(A_99,k5_relat_1(B_100,C_101))
      | ~ v1_relat_1(C_101)
      | ~ v1_relat_1(B_100)
      | ~ v1_relat_1(A_99) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_2028,plain,(
    ! [A_225,C_226] :
      ( k5_relat_1(k6_partfun1(k2_relat_1(A_225)),C_226) = k5_relat_1(k2_funct_1(A_225),k5_relat_1(A_225,C_226))
      | ~ v1_relat_1(C_226)
      | ~ v1_relat_1(A_225)
      | ~ v1_relat_1(k2_funct_1(A_225))
      | ~ v2_funct_1(A_225)
      | ~ v1_funct_1(A_225)
      | ~ v1_relat_1(A_225) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_78,c_427])).

tff(c_2149,plain,(
    ! [C_226] :
      ( k5_relat_1(k2_funct_1('#skF_3'),k5_relat_1('#skF_3',C_226)) = k5_relat_1(k6_partfun1('#skF_2'),C_226)
      | ~ v1_relat_1(C_226)
      | ~ v1_relat_1('#skF_3')
      | ~ v1_relat_1(k2_funct_1('#skF_3'))
      | ~ v2_funct_1('#skF_3')
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_313,c_2028])).

tff(c_3445,plain,(
    ! [C_268] :
      ( k5_relat_1(k2_funct_1('#skF_3'),k5_relat_1('#skF_3',C_268)) = k5_relat_1(k6_partfun1('#skF_2'),C_268)
      | ~ v1_relat_1(C_268) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_133,c_76,c_60,c_202,c_133,c_2149])).

tff(c_3478,plain,
    ( k5_relat_1(k2_funct_1('#skF_3'),k6_partfun1('#skF_1')) = k5_relat_1(k6_partfun1('#skF_2'),'#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1322,c_3445])).

tff(c_3498,plain,(
    k5_relat_1(k2_funct_1('#skF_3'),k6_partfun1('#skF_1')) = k5_relat_1(k6_partfun1('#skF_2'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_136,c_3478])).

tff(c_12,plain,(
    ! [A_9] :
      ( k2_relat_1(k4_relat_1(A_9)) = k1_relat_1(A_9)
      | ~ v1_relat_1(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_188,plain,
    ( k2_relat_1(k2_funct_1('#skF_3')) = k1_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_184,c_12])).

tff(c_198,plain,(
    k2_relat_1(k2_funct_1('#skF_3')) = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_133,c_188])).

tff(c_20,plain,(
    ! [B_20,A_19] :
      ( k5_relat_1(B_20,k6_relat_1(A_19)) = B_20
      | ~ r1_tarski(k2_relat_1(B_20),A_19)
      | ~ v1_relat_1(B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_228,plain,(
    ! [B_77,A_78] :
      ( k5_relat_1(B_77,k6_partfun1(A_78)) = B_77
      | ~ r1_tarski(k2_relat_1(B_77),A_78)
      | ~ v1_relat_1(B_77) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_20])).

tff(c_231,plain,(
    ! [A_78] :
      ( k5_relat_1(k2_funct_1('#skF_3'),k6_partfun1(A_78)) = k2_funct_1('#skF_3')
      | ~ r1_tarski(k1_relat_1('#skF_3'),A_78)
      | ~ v1_relat_1(k2_funct_1('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_198,c_228])).

tff(c_236,plain,(
    ! [A_78] :
      ( k5_relat_1(k2_funct_1('#skF_3'),k6_partfun1(A_78)) = k2_funct_1('#skF_3')
      | ~ r1_tarski(k1_relat_1('#skF_3'),A_78) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_202,c_231])).

tff(c_3516,plain,
    ( k5_relat_1(k6_partfun1('#skF_2'),'#skF_4') = k2_funct_1('#skF_3')
    | ~ r1_tarski(k1_relat_1('#skF_3'),'#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_3498,c_236])).

tff(c_3531,plain,(
    ~ r1_tarski(k1_relat_1('#skF_3'),'#skF_1') ),
    inference(splitLeft,[status(thm)],[c_3516])).

tff(c_3540,plain,
    ( ~ v4_relat_1('#skF_3','#skF_1')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_6,c_3531])).

tff(c_3544,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_133,c_175,c_3540])).

tff(c_3545,plain,(
    k5_relat_1(k6_partfun1('#skF_2'),'#skF_4') = k2_funct_1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_3516])).

tff(c_18,plain,(
    ! [A_17,B_18] :
      ( k5_relat_1(k6_relat_1(A_17),B_18) = B_18
      | ~ r1_tarski(k1_relat_1(B_18),A_17)
      | ~ v1_relat_1(B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_237,plain,(
    ! [A_79,B_80] :
      ( k5_relat_1(k6_partfun1(A_79),B_80) = B_80
      | ~ r1_tarski(k1_relat_1(B_80),A_79)
      | ~ v1_relat_1(B_80) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_18])).

tff(c_249,plain,(
    ! [A_4,B_5] :
      ( k5_relat_1(k6_partfun1(A_4),B_5) = B_5
      | ~ v4_relat_1(B_5,A_4)
      | ~ v1_relat_1(B_5) ) ),
    inference(resolution,[status(thm)],[c_6,c_237])).

tff(c_3578,plain,
    ( k2_funct_1('#skF_3') = '#skF_4'
    | ~ v4_relat_1('#skF_4','#skF_2')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_3545,c_249])).

tff(c_3595,plain,(
    k2_funct_1('#skF_3') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_136,c_176,c_3578])).

tff(c_3597,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_3595])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.35  % Computer   : n006.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 11:38:07 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.91/2.17  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.91/2.17  
% 5.91/2.17  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.91/2.18  %$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k4_relat_1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 5.91/2.18  
% 5.91/2.18  %Foreground sorts:
% 5.91/2.18  
% 5.91/2.18  
% 5.91/2.18  %Background operators:
% 5.91/2.18  
% 5.91/2.18  
% 5.91/2.18  %Foreground operators:
% 5.91/2.18  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 5.91/2.18  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 5.91/2.18  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 5.91/2.18  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 5.91/2.18  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.91/2.18  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 5.91/2.18  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.91/2.18  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 5.91/2.18  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.91/2.18  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 5.91/2.18  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 5.91/2.18  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 5.91/2.18  tff('#skF_2', type, '#skF_2': $i).
% 5.91/2.18  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 5.91/2.18  tff('#skF_3', type, '#skF_3': $i).
% 5.91/2.18  tff('#skF_1', type, '#skF_1': $i).
% 5.91/2.18  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 5.91/2.18  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.91/2.18  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 5.91/2.18  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.91/2.18  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.91/2.18  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 5.91/2.18  tff('#skF_4', type, '#skF_4': $i).
% 5.91/2.18  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 5.91/2.18  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.91/2.18  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 5.91/2.18  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 5.91/2.18  tff(k4_relat_1, type, k4_relat_1: $i > $i).
% 5.91/2.18  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.91/2.18  
% 5.91/2.19  tff(f_170, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => ((((k2_relset_1(A, B, C) = B) & r2_relset_1(A, A, k1_partfun1(A, B, B, A, C, D), k6_partfun1(A))) & v2_funct_1(C)) => (((A = k1_xboole_0) | (B = k1_xboole_0)) | (D = k2_funct_1(C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_funct_2)).
% 5.91/2.19  tff(f_44, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 5.91/2.19  tff(f_32, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 5.91/2.19  tff(f_104, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 5.91/2.19  tff(f_38, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d18_relat_1)).
% 5.91/2.19  tff(f_128, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (v1_funct_1(k1_partfun1(A, B, C, D, E, F)) & m1_subset_1(k1_partfun1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 5.91/2.19  tff(f_132, axiom, (![A]: (v1_partfun1(k6_partfun1(A), A) & m1_subset_1(k6_partfun1(A), k1_zfmisc_1(k2_zfmisc_1(A, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_partfun1)).
% 5.91/2.19  tff(f_116, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 5.91/2.19  tff(f_142, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 5.91/2.19  tff(f_80, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => (k2_funct_1(A) = k4_relat_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d9_funct_1)).
% 5.91/2.19  tff(f_42, axiom, (![A]: (v1_relat_1(A) => v1_relat_1(k4_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k4_relat_1)).
% 5.91/2.19  tff(f_108, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 5.91/2.19  tff(f_144, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 5.91/2.19  tff(f_98, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k5_relat_1(A, k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))) & (k5_relat_1(k2_funct_1(A), A) = k6_relat_1(k2_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t61_funct_1)).
% 5.91/2.19  tff(f_60, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (k5_relat_1(k5_relat_1(A, B), C) = k5_relat_1(A, k5_relat_1(B, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_relat_1)).
% 5.91/2.19  tff(f_50, axiom, (![A]: (v1_relat_1(A) => ((k2_relat_1(A) = k1_relat_1(k4_relat_1(A))) & (k1_relat_1(A) = k2_relat_1(k4_relat_1(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t37_relat_1)).
% 5.91/2.19  tff(f_72, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(B), A) => (k5_relat_1(B, k6_relat_1(A)) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_relat_1)).
% 5.91/2.19  tff(f_66, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(B), A) => (k5_relat_1(k6_relat_1(A), B) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t77_relat_1)).
% 5.91/2.19  tff(c_54, plain, (k2_funct_1('#skF_3')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_170])).
% 5.91/2.19  tff(c_10, plain, (![A_7, B_8]: (v1_relat_1(k2_zfmisc_1(A_7, B_8)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 5.91/2.19  tff(c_66, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_170])).
% 5.91/2.19  tff(c_118, plain, (![B_59, A_60]: (v1_relat_1(B_59) | ~m1_subset_1(B_59, k1_zfmisc_1(A_60)) | ~v1_relat_1(A_60))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.91/2.19  tff(c_127, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_1'))), inference(resolution, [status(thm)], [c_66, c_118])).
% 5.91/2.19  tff(c_136, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_10, c_127])).
% 5.91/2.19  tff(c_164, plain, (![C_70, A_71, B_72]: (v4_relat_1(C_70, A_71) | ~m1_subset_1(C_70, k1_zfmisc_1(k2_zfmisc_1(A_71, B_72))))), inference(cnfTransformation, [status(thm)], [f_104])).
% 5.91/2.19  tff(c_176, plain, (v4_relat_1('#skF_4', '#skF_2')), inference(resolution, [status(thm)], [c_66, c_164])).
% 5.91/2.19  tff(c_72, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_170])).
% 5.91/2.19  tff(c_124, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_72, c_118])).
% 5.91/2.19  tff(c_133, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_10, c_124])).
% 5.91/2.19  tff(c_175, plain, (v4_relat_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_72, c_164])).
% 5.91/2.19  tff(c_6, plain, (![B_5, A_4]: (r1_tarski(k1_relat_1(B_5), A_4) | ~v4_relat_1(B_5, A_4) | ~v1_relat_1(B_5))), inference(cnfTransformation, [status(thm)], [f_38])).
% 5.91/2.19  tff(c_76, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_170])).
% 5.91/2.19  tff(c_70, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_170])).
% 5.91/2.19  tff(c_989, plain, (![A_156, F_158, C_161, D_157, E_159, B_160]: (m1_subset_1(k1_partfun1(A_156, B_160, C_161, D_157, E_159, F_158), k1_zfmisc_1(k2_zfmisc_1(A_156, D_157))) | ~m1_subset_1(F_158, k1_zfmisc_1(k2_zfmisc_1(C_161, D_157))) | ~v1_funct_1(F_158) | ~m1_subset_1(E_159, k1_zfmisc_1(k2_zfmisc_1(A_156, B_160))) | ~v1_funct_1(E_159))), inference(cnfTransformation, [status(thm)], [f_128])).
% 5.91/2.19  tff(c_48, plain, (![A_40]: (m1_subset_1(k6_partfun1(A_40), k1_zfmisc_1(k2_zfmisc_1(A_40, A_40))))), inference(cnfTransformation, [status(thm)], [f_132])).
% 5.91/2.19  tff(c_62, plain, (r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k6_partfun1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_170])).
% 5.91/2.19  tff(c_758, plain, (![D_119, C_120, A_121, B_122]: (D_119=C_120 | ~r2_relset_1(A_121, B_122, C_120, D_119) | ~m1_subset_1(D_119, k1_zfmisc_1(k2_zfmisc_1(A_121, B_122))) | ~m1_subset_1(C_120, k1_zfmisc_1(k2_zfmisc_1(A_121, B_122))))), inference(cnfTransformation, [status(thm)], [f_116])).
% 5.91/2.19  tff(c_766, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_62, c_758])).
% 5.91/2.19  tff(c_781, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_766])).
% 5.91/2.19  tff(c_849, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_781])).
% 5.91/2.19  tff(c_1005, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_989, c_849])).
% 5.91/2.19  tff(c_1034, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_76, c_72, c_70, c_66, c_1005])).
% 5.91/2.19  tff(c_1035, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_781])).
% 5.91/2.19  tff(c_1144, plain, (![C_181, D_182, F_183, A_180, B_184, E_179]: (k1_partfun1(A_180, B_184, C_181, D_182, E_179, F_183)=k5_relat_1(E_179, F_183) | ~m1_subset_1(F_183, k1_zfmisc_1(k2_zfmisc_1(C_181, D_182))) | ~v1_funct_1(F_183) | ~m1_subset_1(E_179, k1_zfmisc_1(k2_zfmisc_1(A_180, B_184))) | ~v1_funct_1(E_179))), inference(cnfTransformation, [status(thm)], [f_142])).
% 5.91/2.19  tff(c_1150, plain, (![A_180, B_184, E_179]: (k1_partfun1(A_180, B_184, '#skF_2', '#skF_1', E_179, '#skF_4')=k5_relat_1(E_179, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_179, k1_zfmisc_1(k2_zfmisc_1(A_180, B_184))) | ~v1_funct_1(E_179))), inference(resolution, [status(thm)], [c_66, c_1144])).
% 5.91/2.19  tff(c_1299, plain, (![A_199, B_200, E_201]: (k1_partfun1(A_199, B_200, '#skF_2', '#skF_1', E_201, '#skF_4')=k5_relat_1(E_201, '#skF_4') | ~m1_subset_1(E_201, k1_zfmisc_1(k2_zfmisc_1(A_199, B_200))) | ~v1_funct_1(E_201))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_1150])).
% 5.91/2.19  tff(c_1311, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_72, c_1299])).
% 5.91/2.19  tff(c_1322, plain, (k5_relat_1('#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_1035, c_1311])).
% 5.91/2.19  tff(c_60, plain, (v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_170])).
% 5.91/2.19  tff(c_178, plain, (![A_74]: (k4_relat_1(A_74)=k2_funct_1(A_74) | ~v2_funct_1(A_74) | ~v1_funct_1(A_74) | ~v1_relat_1(A_74))), inference(cnfTransformation, [status(thm)], [f_80])).
% 5.91/2.19  tff(c_181, plain, (k4_relat_1('#skF_3')=k2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_60, c_178])).
% 5.91/2.19  tff(c_184, plain, (k4_relat_1('#skF_3')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_133, c_76, c_181])).
% 5.91/2.19  tff(c_8, plain, (![A_6]: (v1_relat_1(k4_relat_1(A_6)) | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_42])).
% 5.91/2.19  tff(c_194, plain, (v1_relat_1(k2_funct_1('#skF_3')) | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_184, c_8])).
% 5.91/2.19  tff(c_202, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_133, c_194])).
% 5.91/2.19  tff(c_64, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_2'), inference(cnfTransformation, [status(thm)], [f_170])).
% 5.91/2.19  tff(c_301, plain, (![A_89, B_90, C_91]: (k2_relset_1(A_89, B_90, C_91)=k2_relat_1(C_91) | ~m1_subset_1(C_91, k1_zfmisc_1(k2_zfmisc_1(A_89, B_90))))), inference(cnfTransformation, [status(thm)], [f_108])).
% 5.91/2.19  tff(c_307, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_72, c_301])).
% 5.91/2.19  tff(c_313, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_64, c_307])).
% 5.91/2.19  tff(c_52, plain, (![A_47]: (k6_relat_1(A_47)=k6_partfun1(A_47))), inference(cnfTransformation, [status(thm)], [f_144])).
% 5.91/2.19  tff(c_28, plain, (![A_23]: (k5_relat_1(k2_funct_1(A_23), A_23)=k6_relat_1(k2_relat_1(A_23)) | ~v2_funct_1(A_23) | ~v1_funct_1(A_23) | ~v1_relat_1(A_23))), inference(cnfTransformation, [status(thm)], [f_98])).
% 5.91/2.19  tff(c_78, plain, (![A_23]: (k5_relat_1(k2_funct_1(A_23), A_23)=k6_partfun1(k2_relat_1(A_23)) | ~v2_funct_1(A_23) | ~v1_funct_1(A_23) | ~v1_relat_1(A_23))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_28])).
% 5.91/2.19  tff(c_427, plain, (![A_99, B_100, C_101]: (k5_relat_1(k5_relat_1(A_99, B_100), C_101)=k5_relat_1(A_99, k5_relat_1(B_100, C_101)) | ~v1_relat_1(C_101) | ~v1_relat_1(B_100) | ~v1_relat_1(A_99))), inference(cnfTransformation, [status(thm)], [f_60])).
% 5.91/2.19  tff(c_2028, plain, (![A_225, C_226]: (k5_relat_1(k6_partfun1(k2_relat_1(A_225)), C_226)=k5_relat_1(k2_funct_1(A_225), k5_relat_1(A_225, C_226)) | ~v1_relat_1(C_226) | ~v1_relat_1(A_225) | ~v1_relat_1(k2_funct_1(A_225)) | ~v2_funct_1(A_225) | ~v1_funct_1(A_225) | ~v1_relat_1(A_225))), inference(superposition, [status(thm), theory('equality')], [c_78, c_427])).
% 5.91/2.19  tff(c_2149, plain, (![C_226]: (k5_relat_1(k2_funct_1('#skF_3'), k5_relat_1('#skF_3', C_226))=k5_relat_1(k6_partfun1('#skF_2'), C_226) | ~v1_relat_1(C_226) | ~v1_relat_1('#skF_3') | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_313, c_2028])).
% 5.91/2.19  tff(c_3445, plain, (![C_268]: (k5_relat_1(k2_funct_1('#skF_3'), k5_relat_1('#skF_3', C_268))=k5_relat_1(k6_partfun1('#skF_2'), C_268) | ~v1_relat_1(C_268))), inference(demodulation, [status(thm), theory('equality')], [c_133, c_76, c_60, c_202, c_133, c_2149])).
% 5.91/2.19  tff(c_3478, plain, (k5_relat_1(k2_funct_1('#skF_3'), k6_partfun1('#skF_1'))=k5_relat_1(k6_partfun1('#skF_2'), '#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1322, c_3445])).
% 5.91/2.19  tff(c_3498, plain, (k5_relat_1(k2_funct_1('#skF_3'), k6_partfun1('#skF_1'))=k5_relat_1(k6_partfun1('#skF_2'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_136, c_3478])).
% 5.91/2.19  tff(c_12, plain, (![A_9]: (k2_relat_1(k4_relat_1(A_9))=k1_relat_1(A_9) | ~v1_relat_1(A_9))), inference(cnfTransformation, [status(thm)], [f_50])).
% 5.91/2.19  tff(c_188, plain, (k2_relat_1(k2_funct_1('#skF_3'))=k1_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_184, c_12])).
% 5.91/2.19  tff(c_198, plain, (k2_relat_1(k2_funct_1('#skF_3'))=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_133, c_188])).
% 5.91/2.19  tff(c_20, plain, (![B_20, A_19]: (k5_relat_1(B_20, k6_relat_1(A_19))=B_20 | ~r1_tarski(k2_relat_1(B_20), A_19) | ~v1_relat_1(B_20))), inference(cnfTransformation, [status(thm)], [f_72])).
% 5.91/2.19  tff(c_228, plain, (![B_77, A_78]: (k5_relat_1(B_77, k6_partfun1(A_78))=B_77 | ~r1_tarski(k2_relat_1(B_77), A_78) | ~v1_relat_1(B_77))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_20])).
% 5.91/2.19  tff(c_231, plain, (![A_78]: (k5_relat_1(k2_funct_1('#skF_3'), k6_partfun1(A_78))=k2_funct_1('#skF_3') | ~r1_tarski(k1_relat_1('#skF_3'), A_78) | ~v1_relat_1(k2_funct_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_198, c_228])).
% 5.91/2.19  tff(c_236, plain, (![A_78]: (k5_relat_1(k2_funct_1('#skF_3'), k6_partfun1(A_78))=k2_funct_1('#skF_3') | ~r1_tarski(k1_relat_1('#skF_3'), A_78))), inference(demodulation, [status(thm), theory('equality')], [c_202, c_231])).
% 5.91/2.19  tff(c_3516, plain, (k5_relat_1(k6_partfun1('#skF_2'), '#skF_4')=k2_funct_1('#skF_3') | ~r1_tarski(k1_relat_1('#skF_3'), '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_3498, c_236])).
% 5.91/2.19  tff(c_3531, plain, (~r1_tarski(k1_relat_1('#skF_3'), '#skF_1')), inference(splitLeft, [status(thm)], [c_3516])).
% 5.91/2.19  tff(c_3540, plain, (~v4_relat_1('#skF_3', '#skF_1') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_6, c_3531])).
% 5.91/2.19  tff(c_3544, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_133, c_175, c_3540])).
% 5.91/2.19  tff(c_3545, plain, (k5_relat_1(k6_partfun1('#skF_2'), '#skF_4')=k2_funct_1('#skF_3')), inference(splitRight, [status(thm)], [c_3516])).
% 5.91/2.19  tff(c_18, plain, (![A_17, B_18]: (k5_relat_1(k6_relat_1(A_17), B_18)=B_18 | ~r1_tarski(k1_relat_1(B_18), A_17) | ~v1_relat_1(B_18))), inference(cnfTransformation, [status(thm)], [f_66])).
% 5.91/2.19  tff(c_237, plain, (![A_79, B_80]: (k5_relat_1(k6_partfun1(A_79), B_80)=B_80 | ~r1_tarski(k1_relat_1(B_80), A_79) | ~v1_relat_1(B_80))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_18])).
% 5.91/2.19  tff(c_249, plain, (![A_4, B_5]: (k5_relat_1(k6_partfun1(A_4), B_5)=B_5 | ~v4_relat_1(B_5, A_4) | ~v1_relat_1(B_5))), inference(resolution, [status(thm)], [c_6, c_237])).
% 5.91/2.19  tff(c_3578, plain, (k2_funct_1('#skF_3')='#skF_4' | ~v4_relat_1('#skF_4', '#skF_2') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_3545, c_249])).
% 5.91/2.19  tff(c_3595, plain, (k2_funct_1('#skF_3')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_136, c_176, c_3578])).
% 5.91/2.19  tff(c_3597, plain, $false, inference(negUnitSimplification, [status(thm)], [c_54, c_3595])).
% 5.91/2.19  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.91/2.19  
% 5.91/2.19  Inference rules
% 5.91/2.19  ----------------------
% 5.91/2.19  #Ref     : 0
% 5.91/2.19  #Sup     : 740
% 5.91/2.19  #Fact    : 0
% 5.91/2.19  #Define  : 0
% 5.91/2.19  #Split   : 6
% 5.91/2.19  #Chain   : 0
% 5.91/2.19  #Close   : 0
% 5.91/2.19  
% 5.91/2.19  Ordering : KBO
% 5.91/2.19  
% 5.91/2.19  Simplification rules
% 5.91/2.19  ----------------------
% 5.91/2.19  #Subsume      : 45
% 5.91/2.19  #Demod        : 816
% 5.91/2.19  #Tautology    : 244
% 5.91/2.19  #SimpNegUnit  : 3
% 5.91/2.19  #BackRed      : 30
% 5.91/2.19  
% 5.91/2.19  #Partial instantiations: 0
% 5.91/2.19  #Strategies tried      : 1
% 5.91/2.19  
% 5.91/2.19  Timing (in seconds)
% 5.91/2.19  ----------------------
% 5.91/2.20  Preprocessing        : 0.38
% 5.91/2.20  Parsing              : 0.21
% 5.91/2.20  CNF conversion       : 0.02
% 5.91/2.20  Main loop            : 0.98
% 5.91/2.20  Inferencing          : 0.32
% 5.91/2.20  Reduction            : 0.38
% 5.91/2.20  Demodulation         : 0.30
% 5.91/2.20  BG Simplification    : 0.04
% 5.91/2.20  Subsumption          : 0.16
% 5.91/2.20  Abstraction          : 0.05
% 5.91/2.20  MUC search           : 0.00
% 5.91/2.20  Cooper               : 0.00
% 5.91/2.20  Total                : 1.39
% 5.91/2.20  Index Insertion      : 0.00
% 5.91/2.20  Index Deletion       : 0.00
% 5.91/2.20  Index Matching       : 0.00
% 5.91/2.20  BG Taut test         : 0.00
%------------------------------------------------------------------------------
