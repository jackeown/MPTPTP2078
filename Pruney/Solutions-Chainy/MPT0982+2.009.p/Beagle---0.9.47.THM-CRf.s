%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:11:56 EST 2020

% Result     : Theorem 19.20s
% Output     : CNFRefutation 19.32s
% Verified   : 
% Statistics : Number of formulae       :  136 ( 803 expanded)
%              Number of leaves         :   45 ( 307 expanded)
%              Depth                    :   22
%              Number of atoms          :  296 (3042 expanded)
%              Number of equality atoms :   73 ( 866 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k5_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

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

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_179,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ! [E] :
            ( ( v1_funct_1(E)
              & v1_funct_2(E,B,C)
              & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(B,C))) )
           => ( ( k2_relset_1(A,C,k1_partfun1(A,B,B,C,D,E)) = C
                & v2_funct_1(E) )
             => ( C = k1_xboole_0
                | k2_relset_1(A,B,D) = B ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_funct_2)).

tff(f_103,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_109,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_117,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_63,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A)
        & v2_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A))
        & v2_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_funct_1)).

tff(f_113,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_135,axiom,(
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

tff(f_89,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k2_relat_1(A) = k1_relat_1(k2_funct_1(A))
          & k1_relat_1(A) = k2_relat_1(k2_funct_1(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_157,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_147,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( v1_funct_1(k1_partfun1(A,B,C,D,E,F))
        & m1_subset_1(k1_partfun1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).

tff(f_51,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => r1_tarski(k2_relat_1(k5_relat_1(A,B)),k2_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_relat_1)).

tff(f_44,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k2_relat_1(k5_relat_1(A,B)) = k9_relat_1(B,k2_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t160_relat_1)).

tff(f_99,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k1_relat_1(k5_relat_1(A,k2_funct_1(A))) = k1_relat_1(A)
          & k2_relat_1(k5_relat_1(A,k2_funct_1(A))) = k1_relat_1(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t58_funct_1)).

tff(f_79,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( v2_funct_1(B)
       => k9_relat_1(B,A) = k10_relat_1(k2_funct_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t154_funct_1)).

tff(f_71,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r1_tarski(A,k2_relat_1(B))
       => k9_relat_1(B,k10_relat_1(B,A)) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t147_funct_1)).

tff(c_76,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_90,plain,(
    ! [C_49,A_50,B_51] :
      ( v1_relat_1(C_49)
      | ~ m1_subset_1(C_49,k1_zfmisc_1(k2_zfmisc_1(A_50,B_51))) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_97,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_76,c_90])).

tff(c_105,plain,(
    ! [C_54,B_55,A_56] :
      ( v5_relat_1(C_54,B_55)
      | ~ m1_subset_1(C_54,k1_zfmisc_1(k2_zfmisc_1(A_56,B_55))) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_112,plain,(
    v5_relat_1('#skF_4','#skF_2') ),
    inference(resolution,[status(thm)],[c_76,c_105])).

tff(c_10,plain,(
    ! [B_4,A_3] :
      ( r1_tarski(k2_relat_1(B_4),A_3)
      | ~ v5_relat_1(B_4,A_3)
      | ~ v1_relat_1(B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_207,plain,(
    ! [A_76,B_77,C_78] :
      ( k2_relset_1(A_76,B_77,C_78) = k2_relat_1(C_78)
      | ~ m1_subset_1(C_78,k1_zfmisc_1(k2_zfmisc_1(A_76,B_77))) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_214,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_76,c_207])).

tff(c_62,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_4') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_216,plain,(
    k2_relat_1('#skF_4') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_214,c_62])).

tff(c_70,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_98,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_70,c_90])).

tff(c_74,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_66,plain,(
    v2_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_20,plain,(
    ! [A_11] :
      ( v1_relat_1(k2_funct_1(A_11))
      | ~ v2_funct_1(A_11)
      | ~ v1_funct_1(A_11)
      | ~ v1_relat_1(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_64,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_72,plain,(
    v1_funct_2('#skF_5','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_178,plain,(
    ! [A_71,B_72,C_73] :
      ( k1_relset_1(A_71,B_72,C_73) = k1_relat_1(C_73)
      | ~ m1_subset_1(C_73,k1_zfmisc_1(k2_zfmisc_1(A_71,B_72))) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_186,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_70,c_178])).

tff(c_372,plain,(
    ! [B_104,A_105,C_106] :
      ( k1_xboole_0 = B_104
      | k1_relset_1(A_105,B_104,C_106) = A_105
      | ~ v1_funct_2(C_106,A_105,B_104)
      | ~ m1_subset_1(C_106,k1_zfmisc_1(k2_zfmisc_1(A_105,B_104))) ) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_378,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relset_1('#skF_2','#skF_3','#skF_5') = '#skF_2'
    | ~ v1_funct_2('#skF_5','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_70,c_372])).

tff(c_384,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relat_1('#skF_5') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_186,c_378])).

tff(c_385,plain,(
    k1_relat_1('#skF_5') = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_384])).

tff(c_156,plain,(
    ! [A_69] :
      ( k2_relat_1(k2_funct_1(A_69)) = k1_relat_1(A_69)
      | ~ v2_funct_1(A_69)
      | ~ v1_funct_1(A_69)
      | ~ v1_relat_1(A_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_99,plain,(
    ! [B_52,A_53] :
      ( v5_relat_1(B_52,A_53)
      | ~ r1_tarski(k2_relat_1(B_52),A_53)
      | ~ v1_relat_1(B_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_104,plain,(
    ! [B_52] :
      ( v5_relat_1(B_52,k2_relat_1(B_52))
      | ~ v1_relat_1(B_52) ) ),
    inference(resolution,[status(thm)],[c_6,c_99])).

tff(c_168,plain,(
    ! [A_69] :
      ( v5_relat_1(k2_funct_1(A_69),k1_relat_1(A_69))
      | ~ v1_relat_1(k2_funct_1(A_69))
      | ~ v2_funct_1(A_69)
      | ~ v1_funct_1(A_69)
      | ~ v1_relat_1(A_69) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_156,c_104])).

tff(c_390,plain,
    ( v5_relat_1(k2_funct_1('#skF_5'),'#skF_2')
    | ~ v1_relat_1(k2_funct_1('#skF_5'))
    | ~ v2_funct_1('#skF_5')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_385,c_168])).

tff(c_394,plain,
    ( v5_relat_1(k2_funct_1('#skF_5'),'#skF_2')
    | ~ v1_relat_1(k2_funct_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_74,c_66,c_390])).

tff(c_426,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_394])).

tff(c_429,plain,
    ( ~ v2_funct_1('#skF_5')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_20,c_426])).

tff(c_433,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_74,c_66,c_429])).

tff(c_435,plain,(
    v1_relat_1(k2_funct_1('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_394])).

tff(c_113,plain,(
    v5_relat_1('#skF_5','#skF_3') ),
    inference(resolution,[status(thm)],[c_70,c_105])).

tff(c_80,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_437,plain,(
    ! [C_115,A_113,D_116,F_117,B_114,E_118] :
      ( k1_partfun1(A_113,B_114,C_115,D_116,E_118,F_117) = k5_relat_1(E_118,F_117)
      | ~ m1_subset_1(F_117,k1_zfmisc_1(k2_zfmisc_1(C_115,D_116)))
      | ~ v1_funct_1(F_117)
      | ~ m1_subset_1(E_118,k1_zfmisc_1(k2_zfmisc_1(A_113,B_114)))
      | ~ v1_funct_1(E_118) ) ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_441,plain,(
    ! [A_113,B_114,E_118] :
      ( k1_partfun1(A_113,B_114,'#skF_2','#skF_3',E_118,'#skF_5') = k5_relat_1(E_118,'#skF_5')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1(E_118,k1_zfmisc_1(k2_zfmisc_1(A_113,B_114)))
      | ~ v1_funct_1(E_118) ) ),
    inference(resolution,[status(thm)],[c_70,c_437])).

tff(c_928,plain,(
    ! [A_143,B_144,E_145] :
      ( k1_partfun1(A_143,B_144,'#skF_2','#skF_3',E_145,'#skF_5') = k5_relat_1(E_145,'#skF_5')
      | ~ m1_subset_1(E_145,k1_zfmisc_1(k2_zfmisc_1(A_143,B_144)))
      | ~ v1_funct_1(E_145) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_441])).

tff(c_940,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_3','#skF_4','#skF_5') = k5_relat_1('#skF_4','#skF_5')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_76,c_928])).

tff(c_953,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_3','#skF_4','#skF_5') = k5_relat_1('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_940])).

tff(c_68,plain,(
    k2_relset_1('#skF_1','#skF_3',k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_3','#skF_4','#skF_5')) = '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_958,plain,(
    k2_relset_1('#skF_1','#skF_3',k5_relat_1('#skF_4','#skF_5')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_953,c_68])).

tff(c_56,plain,(
    ! [D_36,F_38,E_37,A_33,B_34,C_35] :
      ( m1_subset_1(k1_partfun1(A_33,B_34,C_35,D_36,E_37,F_38),k1_zfmisc_1(k2_zfmisc_1(A_33,D_36)))
      | ~ m1_subset_1(F_38,k1_zfmisc_1(k2_zfmisc_1(C_35,D_36)))
      | ~ v1_funct_1(F_38)
      | ~ m1_subset_1(E_37,k1_zfmisc_1(k2_zfmisc_1(A_33,B_34)))
      | ~ v1_funct_1(E_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_962,plain,
    ( m1_subset_1(k5_relat_1('#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3')))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
    | ~ v1_funct_1('#skF_5')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_953,c_56])).

tff(c_966,plain,(
    m1_subset_1(k5_relat_1('#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_76,c_74,c_70,c_962])).

tff(c_42,plain,(
    ! [A_27,B_28,C_29] :
      ( k2_relset_1(A_27,B_28,C_29) = k2_relat_1(C_29)
      | ~ m1_subset_1(C_29,k1_zfmisc_1(k2_zfmisc_1(A_27,B_28))) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_996,plain,(
    k2_relset_1('#skF_1','#skF_3',k5_relat_1('#skF_4','#skF_5')) = k2_relat_1(k5_relat_1('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_966,c_42])).

tff(c_1034,plain,(
    k2_relat_1(k5_relat_1('#skF_4','#skF_5')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_958,c_996])).

tff(c_14,plain,(
    ! [A_8,B_10] :
      ( r1_tarski(k2_relat_1(k5_relat_1(A_8,B_10)),k2_relat_1(B_10))
      | ~ v1_relat_1(B_10)
      | ~ v1_relat_1(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_119,plain,(
    ! [B_58,A_59] :
      ( r1_tarski(k2_relat_1(B_58),A_59)
      | ~ v5_relat_1(B_58,A_59)
      | ~ v1_relat_1(B_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_234,plain,(
    ! [B_80,A_81] :
      ( k2_relat_1(B_80) = A_81
      | ~ r1_tarski(A_81,k2_relat_1(B_80))
      | ~ v5_relat_1(B_80,A_81)
      | ~ v1_relat_1(B_80) ) ),
    inference(resolution,[status(thm)],[c_119,c_2])).

tff(c_249,plain,(
    ! [A_8,B_10] :
      ( k2_relat_1(k5_relat_1(A_8,B_10)) = k2_relat_1(B_10)
      | ~ v5_relat_1(B_10,k2_relat_1(k5_relat_1(A_8,B_10)))
      | ~ v1_relat_1(B_10)
      | ~ v1_relat_1(A_8) ) ),
    inference(resolution,[status(thm)],[c_14,c_234])).

tff(c_1077,plain,
    ( k2_relat_1(k5_relat_1('#skF_4','#skF_5')) = k2_relat_1('#skF_5')
    | ~ v5_relat_1('#skF_5','#skF_3')
    | ~ v1_relat_1('#skF_5')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1034,c_249])).

tff(c_1116,plain,(
    k2_relat_1('#skF_5') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_97,c_98,c_113,c_1034,c_1077])).

tff(c_12,plain,(
    ! [B_7,A_5] :
      ( k9_relat_1(B_7,k2_relat_1(A_5)) = k2_relat_1(k5_relat_1(A_5,B_7))
      | ~ v1_relat_1(B_7)
      | ~ v1_relat_1(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_1158,plain,(
    ! [B_7] :
      ( k2_relat_1(k5_relat_1('#skF_5',B_7)) = k9_relat_1(B_7,'#skF_3')
      | ~ v1_relat_1(B_7)
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1116,c_12])).

tff(c_1550,plain,(
    ! [B_161] :
      ( k2_relat_1(k5_relat_1('#skF_5',B_161)) = k9_relat_1(B_161,'#skF_3')
      | ~ v1_relat_1(B_161) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_1158])).

tff(c_30,plain,(
    ! [A_17] :
      ( k2_relat_1(k5_relat_1(A_17,k2_funct_1(A_17))) = k1_relat_1(A_17)
      | ~ v2_funct_1(A_17)
      | ~ v1_funct_1(A_17)
      | ~ v1_relat_1(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_1594,plain,
    ( k9_relat_1(k2_funct_1('#skF_5'),'#skF_3') = k1_relat_1('#skF_5')
    | ~ v2_funct_1('#skF_5')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5')
    | ~ v1_relat_1(k2_funct_1('#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1550,c_30])).

tff(c_1637,plain,(
    k9_relat_1(k2_funct_1('#skF_5'),'#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_435,c_98,c_74,c_66,c_385,c_1594])).

tff(c_24,plain,(
    ! [B_15,A_14] :
      ( k10_relat_1(k2_funct_1(B_15),A_14) = k9_relat_1(B_15,A_14)
      | ~ v2_funct_1(B_15)
      | ~ v1_funct_1(B_15)
      | ~ v1_relat_1(B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_18,plain,(
    ! [A_11] :
      ( v1_funct_1(k2_funct_1(A_11))
      | ~ v2_funct_1(A_11)
      | ~ v1_funct_1(A_11)
      | ~ v1_relat_1(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_262,plain,(
    ! [A_84] :
      ( k2_relat_1(k5_relat_1(A_84,k2_funct_1(A_84))) = k1_relat_1(A_84)
      | ~ v2_funct_1(A_84)
      | ~ v1_funct_1(A_84)
      | ~ v1_relat_1(A_84) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_474,plain,(
    ! [A_125] :
      ( r1_tarski(k1_relat_1(A_125),k2_relat_1(k2_funct_1(A_125)))
      | ~ v1_relat_1(k2_funct_1(A_125))
      | ~ v1_relat_1(A_125)
      | ~ v2_funct_1(A_125)
      | ~ v1_funct_1(A_125)
      | ~ v1_relat_1(A_125) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_262,c_14])).

tff(c_487,plain,
    ( r1_tarski('#skF_2',k2_relat_1(k2_funct_1('#skF_5')))
    | ~ v1_relat_1(k2_funct_1('#skF_5'))
    | ~ v1_relat_1('#skF_5')
    | ~ v2_funct_1('#skF_5')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_385,c_474])).

tff(c_503,plain,(
    r1_tarski('#skF_2',k2_relat_1(k2_funct_1('#skF_5'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_74,c_66,c_98,c_435,c_487])).

tff(c_22,plain,(
    ! [B_13,A_12] :
      ( k9_relat_1(B_13,k10_relat_1(B_13,A_12)) = A_12
      | ~ r1_tarski(A_12,k2_relat_1(B_13))
      | ~ v1_funct_1(B_13)
      | ~ v1_relat_1(B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_506,plain,
    ( k9_relat_1(k2_funct_1('#skF_5'),k10_relat_1(k2_funct_1('#skF_5'),'#skF_2')) = '#skF_2'
    | ~ v1_funct_1(k2_funct_1('#skF_5'))
    | ~ v1_relat_1(k2_funct_1('#skF_5')) ),
    inference(resolution,[status(thm)],[c_503,c_22])).

tff(c_517,plain,
    ( k9_relat_1(k2_funct_1('#skF_5'),k10_relat_1(k2_funct_1('#skF_5'),'#skF_2')) = '#skF_2'
    | ~ v1_funct_1(k2_funct_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_435,c_506])).

tff(c_2119,plain,(
    ~ v1_funct_1(k2_funct_1('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_517])).

tff(c_2156,plain,
    ( ~ v2_funct_1('#skF_5')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_18,c_2119])).

tff(c_2160,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_74,c_66,c_2156])).

tff(c_2162,plain,(
    v1_funct_1(k2_funct_1('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_517])).

tff(c_434,plain,(
    v5_relat_1(k2_funct_1('#skF_5'),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_394])).

tff(c_126,plain,(
    ! [B_58,A_59] :
      ( k2_relat_1(B_58) = A_59
      | ~ r1_tarski(A_59,k2_relat_1(B_58))
      | ~ v5_relat_1(B_58,A_59)
      | ~ v1_relat_1(B_58) ) ),
    inference(resolution,[status(thm)],[c_119,c_2])).

tff(c_509,plain,
    ( k2_relat_1(k2_funct_1('#skF_5')) = '#skF_2'
    | ~ v5_relat_1(k2_funct_1('#skF_5'),'#skF_2')
    | ~ v1_relat_1(k2_funct_1('#skF_5')) ),
    inference(resolution,[status(thm)],[c_503,c_126])).

tff(c_520,plain,(
    k2_relat_1(k2_funct_1('#skF_5')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_435,c_434,c_509])).

tff(c_597,plain,(
    ! [A_12] :
      ( k9_relat_1(k2_funct_1('#skF_5'),k10_relat_1(k2_funct_1('#skF_5'),A_12)) = A_12
      | ~ r1_tarski(A_12,'#skF_2')
      | ~ v1_funct_1(k2_funct_1('#skF_5'))
      | ~ v1_relat_1(k2_funct_1('#skF_5')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_520,c_22])).

tff(c_633,plain,(
    ! [A_12] :
      ( k9_relat_1(k2_funct_1('#skF_5'),k10_relat_1(k2_funct_1('#skF_5'),A_12)) = A_12
      | ~ r1_tarski(A_12,'#skF_2')
      | ~ v1_funct_1(k2_funct_1('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_435,c_597])).

tff(c_5787,plain,(
    ! [A_332] :
      ( k9_relat_1(k2_funct_1('#skF_5'),k10_relat_1(k2_funct_1('#skF_5'),A_332)) = A_332
      | ~ r1_tarski(A_332,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2162,c_633])).

tff(c_5850,plain,(
    ! [A_14] :
      ( k9_relat_1(k2_funct_1('#skF_5'),k9_relat_1('#skF_5',A_14)) = A_14
      | ~ r1_tarski(A_14,'#skF_2')
      | ~ v2_funct_1('#skF_5')
      | ~ v1_funct_1('#skF_5')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_5787])).

tff(c_5904,plain,(
    ! [A_336] :
      ( k9_relat_1(k2_funct_1('#skF_5'),k9_relat_1('#skF_5',A_336)) = A_336
      | ~ r1_tarski(A_336,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_74,c_66,c_5850])).

tff(c_5938,plain,(
    ! [A_5] :
      ( k9_relat_1(k2_funct_1('#skF_5'),k2_relat_1(k5_relat_1(A_5,'#skF_5'))) = k2_relat_1(A_5)
      | ~ r1_tarski(k2_relat_1(A_5),'#skF_2')
      | ~ v1_relat_1('#skF_5')
      | ~ v1_relat_1(A_5) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_5904])).

tff(c_31250,plain,(
    ! [A_979] :
      ( k9_relat_1(k2_funct_1('#skF_5'),k2_relat_1(k5_relat_1(A_979,'#skF_5'))) = k2_relat_1(A_979)
      | ~ r1_tarski(k2_relat_1(A_979),'#skF_2')
      | ~ v1_relat_1(A_979) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_5938])).

tff(c_31292,plain,
    ( k9_relat_1(k2_funct_1('#skF_5'),'#skF_3') = k2_relat_1('#skF_4')
    | ~ r1_tarski(k2_relat_1('#skF_4'),'#skF_2')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1034,c_31250])).

tff(c_31317,plain,
    ( k2_relat_1('#skF_4') = '#skF_2'
    | ~ r1_tarski(k2_relat_1('#skF_4'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_97,c_1637,c_31292])).

tff(c_31318,plain,(
    ~ r1_tarski(k2_relat_1('#skF_4'),'#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_216,c_31317])).

tff(c_31323,plain,
    ( ~ v5_relat_1('#skF_4','#skF_2')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_10,c_31318])).

tff(c_31327,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_97,c_112,c_31323])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n001.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 18:29:45 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 19.20/10.18  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 19.20/10.19  
% 19.20/10.19  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 19.20/10.20  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k5_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 19.20/10.20  
% 19.20/10.20  %Foreground sorts:
% 19.20/10.20  
% 19.20/10.20  
% 19.20/10.20  %Background operators:
% 19.20/10.20  
% 19.20/10.20  
% 19.20/10.20  %Foreground operators:
% 19.20/10.20  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 19.20/10.20  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 19.20/10.20  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 19.20/10.20  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 19.20/10.20  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 19.20/10.20  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 19.20/10.20  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 19.20/10.20  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 19.20/10.20  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 19.20/10.20  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 19.20/10.20  tff('#skF_5', type, '#skF_5': $i).
% 19.20/10.20  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 19.20/10.20  tff('#skF_2', type, '#skF_2': $i).
% 19.20/10.20  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 19.20/10.20  tff('#skF_3', type, '#skF_3': $i).
% 19.20/10.20  tff('#skF_1', type, '#skF_1': $i).
% 19.20/10.20  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 19.20/10.20  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 19.20/10.20  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 19.20/10.20  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 19.20/10.20  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 19.20/10.20  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 19.20/10.20  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 19.20/10.20  tff('#skF_4', type, '#skF_4': $i).
% 19.20/10.20  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 19.20/10.20  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 19.20/10.20  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 19.20/10.20  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 19.20/10.20  
% 19.32/10.22  tff(f_179, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, B, C)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (((k2_relset_1(A, C, k1_partfun1(A, B, B, C, D, E)) = C) & v2_funct_1(E)) => ((C = k1_xboole_0) | (k2_relset_1(A, B, D) = B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_funct_2)).
% 19.32/10.22  tff(f_103, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 19.32/10.22  tff(f_109, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 19.32/10.22  tff(f_37, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 19.32/10.22  tff(f_117, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 19.32/10.22  tff(f_63, axiom, (![A]: (((v1_relat_1(A) & v1_funct_1(A)) & v2_funct_1(A)) => ((v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))) & v2_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_funct_1)).
% 19.32/10.22  tff(f_113, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 19.32/10.22  tff(f_135, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 19.32/10.22  tff(f_89, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k2_relat_1(A) = k1_relat_1(k2_funct_1(A))) & (k1_relat_1(A) = k2_relat_1(k2_funct_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_funct_1)).
% 19.32/10.22  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 19.32/10.22  tff(f_157, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 19.32/10.22  tff(f_147, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (v1_funct_1(k1_partfun1(A, B, C, D, E, F)) & m1_subset_1(k1_partfun1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 19.32/10.22  tff(f_51, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => r1_tarski(k2_relat_1(k5_relat_1(A, B)), k2_relat_1(B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t45_relat_1)).
% 19.32/10.22  tff(f_44, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k2_relat_1(k5_relat_1(A, B)) = k9_relat_1(B, k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t160_relat_1)).
% 19.32/10.22  tff(f_99, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k1_relat_1(k5_relat_1(A, k2_funct_1(A))) = k1_relat_1(A)) & (k2_relat_1(k5_relat_1(A, k2_funct_1(A))) = k1_relat_1(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t58_funct_1)).
% 19.32/10.22  tff(f_79, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (v2_funct_1(B) => (k9_relat_1(B, A) = k10_relat_1(k2_funct_1(B), A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t154_funct_1)).
% 19.32/10.22  tff(f_71, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r1_tarski(A, k2_relat_1(B)) => (k9_relat_1(B, k10_relat_1(B, A)) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t147_funct_1)).
% 19.32/10.22  tff(c_76, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_179])).
% 19.32/10.22  tff(c_90, plain, (![C_49, A_50, B_51]: (v1_relat_1(C_49) | ~m1_subset_1(C_49, k1_zfmisc_1(k2_zfmisc_1(A_50, B_51))))), inference(cnfTransformation, [status(thm)], [f_103])).
% 19.32/10.22  tff(c_97, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_76, c_90])).
% 19.32/10.22  tff(c_105, plain, (![C_54, B_55, A_56]: (v5_relat_1(C_54, B_55) | ~m1_subset_1(C_54, k1_zfmisc_1(k2_zfmisc_1(A_56, B_55))))), inference(cnfTransformation, [status(thm)], [f_109])).
% 19.32/10.22  tff(c_112, plain, (v5_relat_1('#skF_4', '#skF_2')), inference(resolution, [status(thm)], [c_76, c_105])).
% 19.32/10.22  tff(c_10, plain, (![B_4, A_3]: (r1_tarski(k2_relat_1(B_4), A_3) | ~v5_relat_1(B_4, A_3) | ~v1_relat_1(B_4))), inference(cnfTransformation, [status(thm)], [f_37])).
% 19.32/10.22  tff(c_207, plain, (![A_76, B_77, C_78]: (k2_relset_1(A_76, B_77, C_78)=k2_relat_1(C_78) | ~m1_subset_1(C_78, k1_zfmisc_1(k2_zfmisc_1(A_76, B_77))))), inference(cnfTransformation, [status(thm)], [f_117])).
% 19.32/10.22  tff(c_214, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_76, c_207])).
% 19.32/10.22  tff(c_62, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_4')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_179])).
% 19.32/10.22  tff(c_216, plain, (k2_relat_1('#skF_4')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_214, c_62])).
% 19.32/10.22  tff(c_70, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_179])).
% 19.32/10.22  tff(c_98, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_70, c_90])).
% 19.32/10.22  tff(c_74, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_179])).
% 19.32/10.22  tff(c_66, plain, (v2_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_179])).
% 19.32/10.22  tff(c_20, plain, (![A_11]: (v1_relat_1(k2_funct_1(A_11)) | ~v2_funct_1(A_11) | ~v1_funct_1(A_11) | ~v1_relat_1(A_11))), inference(cnfTransformation, [status(thm)], [f_63])).
% 19.32/10.22  tff(c_64, plain, (k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_179])).
% 19.32/10.22  tff(c_72, plain, (v1_funct_2('#skF_5', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_179])).
% 19.32/10.22  tff(c_178, plain, (![A_71, B_72, C_73]: (k1_relset_1(A_71, B_72, C_73)=k1_relat_1(C_73) | ~m1_subset_1(C_73, k1_zfmisc_1(k2_zfmisc_1(A_71, B_72))))), inference(cnfTransformation, [status(thm)], [f_113])).
% 19.32/10.22  tff(c_186, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_70, c_178])).
% 19.32/10.22  tff(c_372, plain, (![B_104, A_105, C_106]: (k1_xboole_0=B_104 | k1_relset_1(A_105, B_104, C_106)=A_105 | ~v1_funct_2(C_106, A_105, B_104) | ~m1_subset_1(C_106, k1_zfmisc_1(k2_zfmisc_1(A_105, B_104))))), inference(cnfTransformation, [status(thm)], [f_135])).
% 19.32/10.22  tff(c_378, plain, (k1_xboole_0='#skF_3' | k1_relset_1('#skF_2', '#skF_3', '#skF_5')='#skF_2' | ~v1_funct_2('#skF_5', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_70, c_372])).
% 19.32/10.22  tff(c_384, plain, (k1_xboole_0='#skF_3' | k1_relat_1('#skF_5')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_72, c_186, c_378])).
% 19.32/10.22  tff(c_385, plain, (k1_relat_1('#skF_5')='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_64, c_384])).
% 19.32/10.22  tff(c_156, plain, (![A_69]: (k2_relat_1(k2_funct_1(A_69))=k1_relat_1(A_69) | ~v2_funct_1(A_69) | ~v1_funct_1(A_69) | ~v1_relat_1(A_69))), inference(cnfTransformation, [status(thm)], [f_89])).
% 19.32/10.22  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 19.32/10.22  tff(c_99, plain, (![B_52, A_53]: (v5_relat_1(B_52, A_53) | ~r1_tarski(k2_relat_1(B_52), A_53) | ~v1_relat_1(B_52))), inference(cnfTransformation, [status(thm)], [f_37])).
% 19.32/10.22  tff(c_104, plain, (![B_52]: (v5_relat_1(B_52, k2_relat_1(B_52)) | ~v1_relat_1(B_52))), inference(resolution, [status(thm)], [c_6, c_99])).
% 19.32/10.22  tff(c_168, plain, (![A_69]: (v5_relat_1(k2_funct_1(A_69), k1_relat_1(A_69)) | ~v1_relat_1(k2_funct_1(A_69)) | ~v2_funct_1(A_69) | ~v1_funct_1(A_69) | ~v1_relat_1(A_69))), inference(superposition, [status(thm), theory('equality')], [c_156, c_104])).
% 19.32/10.22  tff(c_390, plain, (v5_relat_1(k2_funct_1('#skF_5'), '#skF_2') | ~v1_relat_1(k2_funct_1('#skF_5')) | ~v2_funct_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_385, c_168])).
% 19.32/10.22  tff(c_394, plain, (v5_relat_1(k2_funct_1('#skF_5'), '#skF_2') | ~v1_relat_1(k2_funct_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_98, c_74, c_66, c_390])).
% 19.32/10.22  tff(c_426, plain, (~v1_relat_1(k2_funct_1('#skF_5'))), inference(splitLeft, [status(thm)], [c_394])).
% 19.32/10.22  tff(c_429, plain, (~v2_funct_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_20, c_426])).
% 19.32/10.22  tff(c_433, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_98, c_74, c_66, c_429])).
% 19.32/10.22  tff(c_435, plain, (v1_relat_1(k2_funct_1('#skF_5'))), inference(splitRight, [status(thm)], [c_394])).
% 19.32/10.22  tff(c_113, plain, (v5_relat_1('#skF_5', '#skF_3')), inference(resolution, [status(thm)], [c_70, c_105])).
% 19.32/10.22  tff(c_80, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_179])).
% 19.32/10.22  tff(c_437, plain, (![C_115, A_113, D_116, F_117, B_114, E_118]: (k1_partfun1(A_113, B_114, C_115, D_116, E_118, F_117)=k5_relat_1(E_118, F_117) | ~m1_subset_1(F_117, k1_zfmisc_1(k2_zfmisc_1(C_115, D_116))) | ~v1_funct_1(F_117) | ~m1_subset_1(E_118, k1_zfmisc_1(k2_zfmisc_1(A_113, B_114))) | ~v1_funct_1(E_118))), inference(cnfTransformation, [status(thm)], [f_157])).
% 19.32/10.22  tff(c_441, plain, (![A_113, B_114, E_118]: (k1_partfun1(A_113, B_114, '#skF_2', '#skF_3', E_118, '#skF_5')=k5_relat_1(E_118, '#skF_5') | ~v1_funct_1('#skF_5') | ~m1_subset_1(E_118, k1_zfmisc_1(k2_zfmisc_1(A_113, B_114))) | ~v1_funct_1(E_118))), inference(resolution, [status(thm)], [c_70, c_437])).
% 19.32/10.22  tff(c_928, plain, (![A_143, B_144, E_145]: (k1_partfun1(A_143, B_144, '#skF_2', '#skF_3', E_145, '#skF_5')=k5_relat_1(E_145, '#skF_5') | ~m1_subset_1(E_145, k1_zfmisc_1(k2_zfmisc_1(A_143, B_144))) | ~v1_funct_1(E_145))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_441])).
% 19.32/10.22  tff(c_940, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_3', '#skF_4', '#skF_5')=k5_relat_1('#skF_4', '#skF_5') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_76, c_928])).
% 19.32/10.22  tff(c_953, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_3', '#skF_4', '#skF_5')=k5_relat_1('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_80, c_940])).
% 19.32/10.22  tff(c_68, plain, (k2_relset_1('#skF_1', '#skF_3', k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_3', '#skF_4', '#skF_5'))='#skF_3'), inference(cnfTransformation, [status(thm)], [f_179])).
% 19.32/10.22  tff(c_958, plain, (k2_relset_1('#skF_1', '#skF_3', k5_relat_1('#skF_4', '#skF_5'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_953, c_68])).
% 19.32/10.22  tff(c_56, plain, (![D_36, F_38, E_37, A_33, B_34, C_35]: (m1_subset_1(k1_partfun1(A_33, B_34, C_35, D_36, E_37, F_38), k1_zfmisc_1(k2_zfmisc_1(A_33, D_36))) | ~m1_subset_1(F_38, k1_zfmisc_1(k2_zfmisc_1(C_35, D_36))) | ~v1_funct_1(F_38) | ~m1_subset_1(E_37, k1_zfmisc_1(k2_zfmisc_1(A_33, B_34))) | ~v1_funct_1(E_37))), inference(cnfTransformation, [status(thm)], [f_147])).
% 19.32/10.22  tff(c_962, plain, (m1_subset_1(k5_relat_1('#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3'))) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_953, c_56])).
% 19.32/10.22  tff(c_966, plain, (m1_subset_1(k5_relat_1('#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_76, c_74, c_70, c_962])).
% 19.32/10.22  tff(c_42, plain, (![A_27, B_28, C_29]: (k2_relset_1(A_27, B_28, C_29)=k2_relat_1(C_29) | ~m1_subset_1(C_29, k1_zfmisc_1(k2_zfmisc_1(A_27, B_28))))), inference(cnfTransformation, [status(thm)], [f_117])).
% 19.32/10.22  tff(c_996, plain, (k2_relset_1('#skF_1', '#skF_3', k5_relat_1('#skF_4', '#skF_5'))=k2_relat_1(k5_relat_1('#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_966, c_42])).
% 19.32/10.22  tff(c_1034, plain, (k2_relat_1(k5_relat_1('#skF_4', '#skF_5'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_958, c_996])).
% 19.32/10.22  tff(c_14, plain, (![A_8, B_10]: (r1_tarski(k2_relat_1(k5_relat_1(A_8, B_10)), k2_relat_1(B_10)) | ~v1_relat_1(B_10) | ~v1_relat_1(A_8))), inference(cnfTransformation, [status(thm)], [f_51])).
% 19.32/10.22  tff(c_119, plain, (![B_58, A_59]: (r1_tarski(k2_relat_1(B_58), A_59) | ~v5_relat_1(B_58, A_59) | ~v1_relat_1(B_58))), inference(cnfTransformation, [status(thm)], [f_37])).
% 19.32/10.22  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 19.32/10.22  tff(c_234, plain, (![B_80, A_81]: (k2_relat_1(B_80)=A_81 | ~r1_tarski(A_81, k2_relat_1(B_80)) | ~v5_relat_1(B_80, A_81) | ~v1_relat_1(B_80))), inference(resolution, [status(thm)], [c_119, c_2])).
% 19.32/10.22  tff(c_249, plain, (![A_8, B_10]: (k2_relat_1(k5_relat_1(A_8, B_10))=k2_relat_1(B_10) | ~v5_relat_1(B_10, k2_relat_1(k5_relat_1(A_8, B_10))) | ~v1_relat_1(B_10) | ~v1_relat_1(A_8))), inference(resolution, [status(thm)], [c_14, c_234])).
% 19.32/10.22  tff(c_1077, plain, (k2_relat_1(k5_relat_1('#skF_4', '#skF_5'))=k2_relat_1('#skF_5') | ~v5_relat_1('#skF_5', '#skF_3') | ~v1_relat_1('#skF_5') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1034, c_249])).
% 19.32/10.22  tff(c_1116, plain, (k2_relat_1('#skF_5')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_97, c_98, c_113, c_1034, c_1077])).
% 19.32/10.22  tff(c_12, plain, (![B_7, A_5]: (k9_relat_1(B_7, k2_relat_1(A_5))=k2_relat_1(k5_relat_1(A_5, B_7)) | ~v1_relat_1(B_7) | ~v1_relat_1(A_5))), inference(cnfTransformation, [status(thm)], [f_44])).
% 19.32/10.22  tff(c_1158, plain, (![B_7]: (k2_relat_1(k5_relat_1('#skF_5', B_7))=k9_relat_1(B_7, '#skF_3') | ~v1_relat_1(B_7) | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_1116, c_12])).
% 19.32/10.22  tff(c_1550, plain, (![B_161]: (k2_relat_1(k5_relat_1('#skF_5', B_161))=k9_relat_1(B_161, '#skF_3') | ~v1_relat_1(B_161))), inference(demodulation, [status(thm), theory('equality')], [c_98, c_1158])).
% 19.32/10.22  tff(c_30, plain, (![A_17]: (k2_relat_1(k5_relat_1(A_17, k2_funct_1(A_17)))=k1_relat_1(A_17) | ~v2_funct_1(A_17) | ~v1_funct_1(A_17) | ~v1_relat_1(A_17))), inference(cnfTransformation, [status(thm)], [f_99])).
% 19.32/10.22  tff(c_1594, plain, (k9_relat_1(k2_funct_1('#skF_5'), '#skF_3')=k1_relat_1('#skF_5') | ~v2_funct_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5') | ~v1_relat_1(k2_funct_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_1550, c_30])).
% 19.32/10.22  tff(c_1637, plain, (k9_relat_1(k2_funct_1('#skF_5'), '#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_435, c_98, c_74, c_66, c_385, c_1594])).
% 19.32/10.22  tff(c_24, plain, (![B_15, A_14]: (k10_relat_1(k2_funct_1(B_15), A_14)=k9_relat_1(B_15, A_14) | ~v2_funct_1(B_15) | ~v1_funct_1(B_15) | ~v1_relat_1(B_15))), inference(cnfTransformation, [status(thm)], [f_79])).
% 19.32/10.22  tff(c_18, plain, (![A_11]: (v1_funct_1(k2_funct_1(A_11)) | ~v2_funct_1(A_11) | ~v1_funct_1(A_11) | ~v1_relat_1(A_11))), inference(cnfTransformation, [status(thm)], [f_63])).
% 19.32/10.22  tff(c_262, plain, (![A_84]: (k2_relat_1(k5_relat_1(A_84, k2_funct_1(A_84)))=k1_relat_1(A_84) | ~v2_funct_1(A_84) | ~v1_funct_1(A_84) | ~v1_relat_1(A_84))), inference(cnfTransformation, [status(thm)], [f_99])).
% 19.32/10.22  tff(c_474, plain, (![A_125]: (r1_tarski(k1_relat_1(A_125), k2_relat_1(k2_funct_1(A_125))) | ~v1_relat_1(k2_funct_1(A_125)) | ~v1_relat_1(A_125) | ~v2_funct_1(A_125) | ~v1_funct_1(A_125) | ~v1_relat_1(A_125))), inference(superposition, [status(thm), theory('equality')], [c_262, c_14])).
% 19.32/10.22  tff(c_487, plain, (r1_tarski('#skF_2', k2_relat_1(k2_funct_1('#skF_5'))) | ~v1_relat_1(k2_funct_1('#skF_5')) | ~v1_relat_1('#skF_5') | ~v2_funct_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_385, c_474])).
% 19.32/10.22  tff(c_503, plain, (r1_tarski('#skF_2', k2_relat_1(k2_funct_1('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_98, c_74, c_66, c_98, c_435, c_487])).
% 19.32/10.22  tff(c_22, plain, (![B_13, A_12]: (k9_relat_1(B_13, k10_relat_1(B_13, A_12))=A_12 | ~r1_tarski(A_12, k2_relat_1(B_13)) | ~v1_funct_1(B_13) | ~v1_relat_1(B_13))), inference(cnfTransformation, [status(thm)], [f_71])).
% 19.32/10.22  tff(c_506, plain, (k9_relat_1(k2_funct_1('#skF_5'), k10_relat_1(k2_funct_1('#skF_5'), '#skF_2'))='#skF_2' | ~v1_funct_1(k2_funct_1('#skF_5')) | ~v1_relat_1(k2_funct_1('#skF_5'))), inference(resolution, [status(thm)], [c_503, c_22])).
% 19.32/10.22  tff(c_517, plain, (k9_relat_1(k2_funct_1('#skF_5'), k10_relat_1(k2_funct_1('#skF_5'), '#skF_2'))='#skF_2' | ~v1_funct_1(k2_funct_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_435, c_506])).
% 19.32/10.22  tff(c_2119, plain, (~v1_funct_1(k2_funct_1('#skF_5'))), inference(splitLeft, [status(thm)], [c_517])).
% 19.32/10.22  tff(c_2156, plain, (~v2_funct_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_18, c_2119])).
% 19.32/10.22  tff(c_2160, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_98, c_74, c_66, c_2156])).
% 19.32/10.22  tff(c_2162, plain, (v1_funct_1(k2_funct_1('#skF_5'))), inference(splitRight, [status(thm)], [c_517])).
% 19.32/10.22  tff(c_434, plain, (v5_relat_1(k2_funct_1('#skF_5'), '#skF_2')), inference(splitRight, [status(thm)], [c_394])).
% 19.32/10.22  tff(c_126, plain, (![B_58, A_59]: (k2_relat_1(B_58)=A_59 | ~r1_tarski(A_59, k2_relat_1(B_58)) | ~v5_relat_1(B_58, A_59) | ~v1_relat_1(B_58))), inference(resolution, [status(thm)], [c_119, c_2])).
% 19.32/10.22  tff(c_509, plain, (k2_relat_1(k2_funct_1('#skF_5'))='#skF_2' | ~v5_relat_1(k2_funct_1('#skF_5'), '#skF_2') | ~v1_relat_1(k2_funct_1('#skF_5'))), inference(resolution, [status(thm)], [c_503, c_126])).
% 19.32/10.22  tff(c_520, plain, (k2_relat_1(k2_funct_1('#skF_5'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_435, c_434, c_509])).
% 19.32/10.22  tff(c_597, plain, (![A_12]: (k9_relat_1(k2_funct_1('#skF_5'), k10_relat_1(k2_funct_1('#skF_5'), A_12))=A_12 | ~r1_tarski(A_12, '#skF_2') | ~v1_funct_1(k2_funct_1('#skF_5')) | ~v1_relat_1(k2_funct_1('#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_520, c_22])).
% 19.32/10.22  tff(c_633, plain, (![A_12]: (k9_relat_1(k2_funct_1('#skF_5'), k10_relat_1(k2_funct_1('#skF_5'), A_12))=A_12 | ~r1_tarski(A_12, '#skF_2') | ~v1_funct_1(k2_funct_1('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_435, c_597])).
% 19.32/10.22  tff(c_5787, plain, (![A_332]: (k9_relat_1(k2_funct_1('#skF_5'), k10_relat_1(k2_funct_1('#skF_5'), A_332))=A_332 | ~r1_tarski(A_332, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_2162, c_633])).
% 19.32/10.22  tff(c_5850, plain, (![A_14]: (k9_relat_1(k2_funct_1('#skF_5'), k9_relat_1('#skF_5', A_14))=A_14 | ~r1_tarski(A_14, '#skF_2') | ~v2_funct_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_24, c_5787])).
% 19.32/10.22  tff(c_5904, plain, (![A_336]: (k9_relat_1(k2_funct_1('#skF_5'), k9_relat_1('#skF_5', A_336))=A_336 | ~r1_tarski(A_336, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_98, c_74, c_66, c_5850])).
% 19.32/10.22  tff(c_5938, plain, (![A_5]: (k9_relat_1(k2_funct_1('#skF_5'), k2_relat_1(k5_relat_1(A_5, '#skF_5')))=k2_relat_1(A_5) | ~r1_tarski(k2_relat_1(A_5), '#skF_2') | ~v1_relat_1('#skF_5') | ~v1_relat_1(A_5))), inference(superposition, [status(thm), theory('equality')], [c_12, c_5904])).
% 19.32/10.22  tff(c_31250, plain, (![A_979]: (k9_relat_1(k2_funct_1('#skF_5'), k2_relat_1(k5_relat_1(A_979, '#skF_5')))=k2_relat_1(A_979) | ~r1_tarski(k2_relat_1(A_979), '#skF_2') | ~v1_relat_1(A_979))), inference(demodulation, [status(thm), theory('equality')], [c_98, c_5938])).
% 19.32/10.22  tff(c_31292, plain, (k9_relat_1(k2_funct_1('#skF_5'), '#skF_3')=k2_relat_1('#skF_4') | ~r1_tarski(k2_relat_1('#skF_4'), '#skF_2') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1034, c_31250])).
% 19.32/10.22  tff(c_31317, plain, (k2_relat_1('#skF_4')='#skF_2' | ~r1_tarski(k2_relat_1('#skF_4'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_97, c_1637, c_31292])).
% 19.32/10.22  tff(c_31318, plain, (~r1_tarski(k2_relat_1('#skF_4'), '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_216, c_31317])).
% 19.32/10.22  tff(c_31323, plain, (~v5_relat_1('#skF_4', '#skF_2') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_10, c_31318])).
% 19.32/10.22  tff(c_31327, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_97, c_112, c_31323])).
% 19.32/10.22  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 19.32/10.22  
% 19.32/10.22  Inference rules
% 19.32/10.22  ----------------------
% 19.32/10.22  #Ref     : 0
% 19.32/10.22  #Sup     : 6655
% 19.32/10.22  #Fact    : 0
% 19.32/10.22  #Define  : 0
% 19.32/10.22  #Split   : 74
% 19.32/10.22  #Chain   : 0
% 19.32/10.22  #Close   : 0
% 19.32/10.22  
% 19.32/10.22  Ordering : KBO
% 19.32/10.22  
% 19.32/10.22  Simplification rules
% 19.32/10.22  ----------------------
% 19.32/10.22  #Subsume      : 847
% 19.32/10.22  #Demod        : 11568
% 19.32/10.22  #Tautology    : 1884
% 19.32/10.22  #SimpNegUnit  : 217
% 19.32/10.22  #BackRed      : 542
% 19.32/10.22  
% 19.32/10.22  #Partial instantiations: 0
% 19.32/10.22  #Strategies tried      : 1
% 19.32/10.22  
% 19.32/10.22  Timing (in seconds)
% 19.32/10.22  ----------------------
% 19.32/10.22  Preprocessing        : 0.36
% 19.32/10.22  Parsing              : 0.19
% 19.32/10.22  CNF conversion       : 0.02
% 19.32/10.22  Main loop            : 9.09
% 19.32/10.22  Inferencing          : 1.93
% 19.32/10.22  Reduction            : 4.58
% 19.32/10.22  Demodulation         : 3.79
% 19.32/10.22  BG Simplification    : 0.16
% 19.32/10.22  Subsumption          : 1.88
% 19.32/10.22  Abstraction          : 0.22
% 19.32/10.22  MUC search           : 0.00
% 19.32/10.22  Cooper               : 0.00
% 19.32/10.22  Total                : 9.50
% 19.32/10.22  Index Insertion      : 0.00
% 19.32/10.22  Index Deletion       : 0.00
% 19.32/10.22  Index Matching       : 0.00
% 19.32/10.22  BG Taut test         : 0.00
%------------------------------------------------------------------------------
