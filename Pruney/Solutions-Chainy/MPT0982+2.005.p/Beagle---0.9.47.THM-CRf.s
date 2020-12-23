%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:11:55 EST 2020

% Result     : Theorem 13.83s
% Output     : CNFRefutation 13.97s
% Verified   : 
% Statistics : Number of formulae       :  217 (7450 expanded)
%              Number of leaves         :   46 (2695 expanded)
%              Depth                    :   36
%              Number of atoms          :  463 (27341 expanded)
%              Number of equality atoms :  123 (8861 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    5 (   2 average)

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

tff(f_172,negated_conjecture,(
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

tff(f_110,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_96,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_102,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_150,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_140,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( v1_funct_1(k1_partfun1(A,B,C,D,E,F))
        & m1_subset_1(k1_partfun1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).

tff(f_48,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k2_relat_1(k5_relat_1(A,B)) = k9_relat_1(B,k2_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t160_relat_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k9_relat_1(B,A),k2_relat_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t144_relat_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_106,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_128,axiom,(
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

tff(f_56,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k10_relat_1(A,k2_relat_1(A)) = k1_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_relat_1)).

tff(f_52,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k10_relat_1(B,A),k1_relat_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t167_relat_1)).

tff(f_68,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A)
        & v2_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A))
        & v2_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_funct_1)).

tff(f_92,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( v2_funct_1(B)
       => k10_relat_1(B,A) = k9_relat_1(k2_funct_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t155_funct_1)).

tff(f_76,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r1_tarski(A,k2_relat_1(B))
       => k9_relat_1(B,k10_relat_1(B,A)) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t147_funct_1)).

tff(f_84,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( v2_funct_1(B)
       => k9_relat_1(B,A) = k10_relat_1(k2_funct_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t154_funct_1)).

tff(c_74,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_172])).

tff(c_157,plain,(
    ! [A_72,B_73,C_74] :
      ( k2_relset_1(A_72,B_73,C_74) = k2_relat_1(C_74)
      | ~ m1_subset_1(C_74,k1_zfmisc_1(k2_zfmisc_1(A_72,B_73))) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_164,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_74,c_157])).

tff(c_60,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_4') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_172])).

tff(c_167,plain,(
    k2_relat_1('#skF_4') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_164,c_60])).

tff(c_95,plain,(
    ! [C_52,A_53,B_54] :
      ( v1_relat_1(C_52)
      | ~ m1_subset_1(C_52,k1_zfmisc_1(k2_zfmisc_1(A_53,B_54))) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_102,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_74,c_95])).

tff(c_127,plain,(
    ! [C_62,B_63,A_64] :
      ( v5_relat_1(C_62,B_63)
      | ~ m1_subset_1(C_62,k1_zfmisc_1(k2_zfmisc_1(A_64,B_63))) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_134,plain,(
    v5_relat_1('#skF_4','#skF_2') ),
    inference(resolution,[status(thm)],[c_74,c_127])).

tff(c_68,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_172])).

tff(c_103,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_68,c_95])).

tff(c_135,plain,(
    v5_relat_1('#skF_5','#skF_3') ),
    inference(resolution,[status(thm)],[c_68,c_127])).

tff(c_78,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_172])).

tff(c_72,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_172])).

tff(c_779,plain,(
    ! [C_136,D_137,F_138,E_134,B_139,A_135] :
      ( k1_partfun1(A_135,B_139,C_136,D_137,E_134,F_138) = k5_relat_1(E_134,F_138)
      | ~ m1_subset_1(F_138,k1_zfmisc_1(k2_zfmisc_1(C_136,D_137)))
      | ~ v1_funct_1(F_138)
      | ~ m1_subset_1(E_134,k1_zfmisc_1(k2_zfmisc_1(A_135,B_139)))
      | ~ v1_funct_1(E_134) ) ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_783,plain,(
    ! [A_135,B_139,E_134] :
      ( k1_partfun1(A_135,B_139,'#skF_2','#skF_3',E_134,'#skF_5') = k5_relat_1(E_134,'#skF_5')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1(E_134,k1_zfmisc_1(k2_zfmisc_1(A_135,B_139)))
      | ~ v1_funct_1(E_134) ) ),
    inference(resolution,[status(thm)],[c_68,c_779])).

tff(c_3754,plain,(
    ! [A_262,B_263,E_264] :
      ( k1_partfun1(A_262,B_263,'#skF_2','#skF_3',E_264,'#skF_5') = k5_relat_1(E_264,'#skF_5')
      | ~ m1_subset_1(E_264,k1_zfmisc_1(k2_zfmisc_1(A_262,B_263)))
      | ~ v1_funct_1(E_264) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_783])).

tff(c_3763,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_3','#skF_4','#skF_5') = k5_relat_1('#skF_4','#skF_5')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_74,c_3754])).

tff(c_3773,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_3','#skF_4','#skF_5') = k5_relat_1('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_3763])).

tff(c_66,plain,(
    k2_relset_1('#skF_1','#skF_3',k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_3','#skF_4','#skF_5')) = '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_172])).

tff(c_3840,plain,(
    k2_relset_1('#skF_1','#skF_3',k5_relat_1('#skF_4','#skF_5')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3773,c_66])).

tff(c_54,plain,(
    ! [A_35,F_40,B_36,C_37,D_38,E_39] :
      ( m1_subset_1(k1_partfun1(A_35,B_36,C_37,D_38,E_39,F_40),k1_zfmisc_1(k2_zfmisc_1(A_35,D_38)))
      | ~ m1_subset_1(F_40,k1_zfmisc_1(k2_zfmisc_1(C_37,D_38)))
      | ~ v1_funct_1(F_40)
      | ~ m1_subset_1(E_39,k1_zfmisc_1(k2_zfmisc_1(A_35,B_36)))
      | ~ v1_funct_1(E_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_3844,plain,
    ( m1_subset_1(k5_relat_1('#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3')))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
    | ~ v1_funct_1('#skF_5')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_3773,c_54])).

tff(c_3848,plain,(
    m1_subset_1(k5_relat_1('#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_74,c_72,c_68,c_3844])).

tff(c_40,plain,(
    ! [A_29,B_30,C_31] :
      ( k2_relset_1(A_29,B_30,C_31) = k2_relat_1(C_31)
      | ~ m1_subset_1(C_31,k1_zfmisc_1(k2_zfmisc_1(A_29,B_30))) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_3881,plain,(
    k2_relset_1('#skF_1','#skF_3',k5_relat_1('#skF_4','#skF_5')) = k2_relat_1(k5_relat_1('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_3848,c_40])).

tff(c_3917,plain,(
    k2_relat_1(k5_relat_1('#skF_4','#skF_5')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3840,c_3881])).

tff(c_194,plain,(
    ! [B_80,A_81] :
      ( k9_relat_1(B_80,k2_relat_1(A_81)) = k2_relat_1(k5_relat_1(A_81,B_80))
      | ~ v1_relat_1(B_80)
      | ~ v1_relat_1(A_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_12,plain,(
    ! [B_6,A_5] :
      ( r1_tarski(k9_relat_1(B_6,A_5),k2_relat_1(B_6))
      | ~ v1_relat_1(B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_200,plain,(
    ! [A_81,B_80] :
      ( r1_tarski(k2_relat_1(k5_relat_1(A_81,B_80)),k2_relat_1(B_80))
      | ~ v1_relat_1(B_80)
      | ~ v1_relat_1(B_80)
      | ~ v1_relat_1(A_81) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_194,c_12])).

tff(c_4005,plain,
    ( r1_tarski('#skF_3',k2_relat_1('#skF_5'))
    | ~ v1_relat_1('#skF_5')
    | ~ v1_relat_1('#skF_5')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_3917,c_200])).

tff(c_4046,plain,(
    r1_tarski('#skF_3',k2_relat_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_103,c_103,c_4005])).

tff(c_118,plain,(
    ! [B_59,A_60] :
      ( r1_tarski(k2_relat_1(B_59),A_60)
      | ~ v5_relat_1(B_59,A_60)
      | ~ v1_relat_1(B_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_121,plain,(
    ! [B_59,A_60] :
      ( k2_relat_1(B_59) = A_60
      | ~ r1_tarski(A_60,k2_relat_1(B_59))
      | ~ v5_relat_1(B_59,A_60)
      | ~ v1_relat_1(B_59) ) ),
    inference(resolution,[status(thm)],[c_118,c_2])).

tff(c_4070,plain,
    ( k2_relat_1('#skF_5') = '#skF_3'
    | ~ v5_relat_1('#skF_5','#skF_3')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_4046,c_121])).

tff(c_4078,plain,(
    k2_relat_1('#skF_5') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_103,c_135,c_4070])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_62,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_172])).

tff(c_70,plain,(
    v1_funct_2('#skF_5','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_172])).

tff(c_176,plain,(
    ! [A_76,B_77,C_78] :
      ( k1_relset_1(A_76,B_77,C_78) = k1_relat_1(C_78)
      | ~ m1_subset_1(C_78,k1_zfmisc_1(k2_zfmisc_1(A_76,B_77))) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_184,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_68,c_176])).

tff(c_522,plain,(
    ! [B_120,A_121,C_122] :
      ( k1_xboole_0 = B_120
      | k1_relset_1(A_121,B_120,C_122) = A_121
      | ~ v1_funct_2(C_122,A_121,B_120)
      | ~ m1_subset_1(C_122,k1_zfmisc_1(k2_zfmisc_1(A_121,B_120))) ) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_528,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relset_1('#skF_2','#skF_3','#skF_5') = '#skF_2'
    | ~ v1_funct_2('#skF_5','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_68,c_522])).

tff(c_534,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relat_1('#skF_5') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_184,c_528])).

tff(c_535,plain,(
    k1_relat_1('#skF_5') = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_534])).

tff(c_18,plain,(
    ! [A_12] :
      ( k10_relat_1(A_12,k2_relat_1(A_12)) = k1_relat_1(A_12)
      | ~ v1_relat_1(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_16,plain,(
    ! [B_11,A_10] :
      ( r1_tarski(k10_relat_1(B_11,A_10),k1_relat_1(B_11))
      | ~ v1_relat_1(B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_105,plain,(
    ! [B_57,A_58] :
      ( B_57 = A_58
      | ~ r1_tarski(B_57,A_58)
      | ~ r1_tarski(A_58,B_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_113,plain,(
    ! [B_11,A_10] :
      ( k10_relat_1(B_11,A_10) = k1_relat_1(B_11)
      | ~ r1_tarski(k1_relat_1(B_11),k10_relat_1(B_11,A_10))
      | ~ v1_relat_1(B_11) ) ),
    inference(resolution,[status(thm)],[c_16,c_105])).

tff(c_543,plain,(
    ! [A_10] :
      ( k10_relat_1('#skF_5',A_10) = k1_relat_1('#skF_5')
      | ~ r1_tarski('#skF_2',k10_relat_1('#skF_5',A_10))
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_535,c_113])).

tff(c_790,plain,(
    ! [A_140] :
      ( k10_relat_1('#skF_5',A_140) = '#skF_2'
      | ~ r1_tarski('#skF_2',k10_relat_1('#skF_5',A_140)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_103,c_535,c_543])).

tff(c_794,plain,
    ( k10_relat_1('#skF_5',k2_relat_1('#skF_5')) = '#skF_2'
    | ~ r1_tarski('#skF_2',k1_relat_1('#skF_5'))
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_790])).

tff(c_796,plain,(
    k10_relat_1('#skF_5',k2_relat_1('#skF_5')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_103,c_6,c_535,c_794])).

tff(c_4086,plain,(
    k10_relat_1('#skF_5','#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4078,c_796])).

tff(c_14,plain,(
    ! [B_9,A_7] :
      ( k9_relat_1(B_9,k2_relat_1(A_7)) = k2_relat_1(k5_relat_1(A_7,B_9))
      | ~ v1_relat_1(B_9)
      | ~ v1_relat_1(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_269,plain,(
    ! [B_90,A_91] :
      ( k9_relat_1(B_90,A_91) = k2_relat_1(B_90)
      | ~ r1_tarski(k2_relat_1(B_90),k9_relat_1(B_90,A_91))
      | ~ v1_relat_1(B_90) ) ),
    inference(resolution,[status(thm)],[c_12,c_105])).

tff(c_7615,plain,(
    ! [B_429,A_430] :
      ( k9_relat_1(B_429,k2_relat_1(A_430)) = k2_relat_1(B_429)
      | ~ r1_tarski(k2_relat_1(B_429),k2_relat_1(k5_relat_1(A_430,B_429)))
      | ~ v1_relat_1(B_429)
      | ~ v1_relat_1(B_429)
      | ~ v1_relat_1(A_430) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_269])).

tff(c_7648,plain,
    ( k9_relat_1('#skF_5',k2_relat_1('#skF_4')) = k2_relat_1('#skF_5')
    | ~ r1_tarski(k2_relat_1('#skF_5'),'#skF_3')
    | ~ v1_relat_1('#skF_5')
    | ~ v1_relat_1('#skF_5')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_3917,c_7615])).

tff(c_7682,plain,(
    k9_relat_1('#skF_5',k2_relat_1('#skF_4')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_103,c_103,c_6,c_4078,c_4078,c_7648])).

tff(c_64,plain,(
    v2_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_172])).

tff(c_24,plain,(
    ! [A_13] :
      ( v1_relat_1(k2_funct_1(A_13))
      | ~ v2_funct_1(A_13)
      | ~ v1_funct_1(A_13)
      | ~ v1_relat_1(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_206,plain,(
    ! [B_82,A_83] :
      ( k9_relat_1(k2_funct_1(B_82),A_83) = k10_relat_1(B_82,A_83)
      | ~ v2_funct_1(B_82)
      | ~ v1_funct_1(B_82)
      | ~ v1_relat_1(B_82) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_216,plain,(
    ! [B_82,A_83] :
      ( r1_tarski(k10_relat_1(B_82,A_83),k2_relat_1(k2_funct_1(B_82)))
      | ~ v1_relat_1(k2_funct_1(B_82))
      | ~ v2_funct_1(B_82)
      | ~ v1_funct_1(B_82)
      | ~ v1_relat_1(B_82) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_206,c_12])).

tff(c_807,plain,
    ( r1_tarski('#skF_2',k2_relat_1(k2_funct_1('#skF_5')))
    | ~ v1_relat_1(k2_funct_1('#skF_5'))
    | ~ v2_funct_1('#skF_5')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_796,c_216])).

tff(c_829,plain,
    ( r1_tarski('#skF_2',k2_relat_1(k2_funct_1('#skF_5')))
    | ~ v1_relat_1(k2_funct_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_103,c_72,c_64,c_807])).

tff(c_841,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_829])).

tff(c_857,plain,
    ( ~ v2_funct_1('#skF_5')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_24,c_841])).

tff(c_861,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_103,c_72,c_64,c_857])).

tff(c_863,plain,(
    v1_relat_1(k2_funct_1('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_829])).

tff(c_862,plain,(
    r1_tarski('#skF_2',k2_relat_1(k2_funct_1('#skF_5'))) ),
    inference(splitRight,[status(thm)],[c_829])).

tff(c_868,plain,
    ( k2_relat_1(k2_funct_1('#skF_5')) = '#skF_2'
    | ~ v5_relat_1(k2_funct_1('#skF_5'),'#skF_2')
    | ~ v1_relat_1(k2_funct_1('#skF_5')) ),
    inference(resolution,[status(thm)],[c_862,c_121])).

tff(c_876,plain,
    ( k2_relat_1(k2_funct_1('#skF_5')) = '#skF_2'
    | ~ v5_relat_1(k2_funct_1('#skF_5'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_863,c_868])).

tff(c_878,plain,(
    ~ v5_relat_1(k2_funct_1('#skF_5'),'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_876])).

tff(c_1154,plain,(
    ! [A_158,B_159,E_160] :
      ( k1_partfun1(A_158,B_159,'#skF_2','#skF_3',E_160,'#skF_5') = k5_relat_1(E_160,'#skF_5')
      | ~ m1_subset_1(E_160,k1_zfmisc_1(k2_zfmisc_1(A_158,B_159)))
      | ~ v1_funct_1(E_160) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_783])).

tff(c_1163,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_3','#skF_4','#skF_5') = k5_relat_1('#skF_4','#skF_5')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_74,c_1154])).

tff(c_1173,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_3','#skF_4','#skF_5') = k5_relat_1('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_1163])).

tff(c_1240,plain,(
    k2_relset_1('#skF_1','#skF_3',k5_relat_1('#skF_4','#skF_5')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1173,c_66])).

tff(c_1244,plain,
    ( m1_subset_1(k5_relat_1('#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3')))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
    | ~ v1_funct_1('#skF_5')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1173,c_54])).

tff(c_1248,plain,(
    m1_subset_1(k5_relat_1('#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_74,c_72,c_68,c_1244])).

tff(c_1340,plain,(
    k2_relset_1('#skF_1','#skF_3',k5_relat_1('#skF_4','#skF_5')) = k2_relat_1(k5_relat_1('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_1248,c_40])).

tff(c_1376,plain,(
    k2_relat_1(k5_relat_1('#skF_4','#skF_5')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1240,c_1340])).

tff(c_1397,plain,
    ( r1_tarski('#skF_3',k2_relat_1('#skF_5'))
    | ~ v1_relat_1('#skF_5')
    | ~ v1_relat_1('#skF_5')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1376,c_200])).

tff(c_1438,plain,(
    r1_tarski('#skF_3',k2_relat_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_103,c_103,c_1397])).

tff(c_1462,plain,
    ( k2_relat_1('#skF_5') = '#skF_3'
    | ~ v5_relat_1('#skF_5','#skF_3')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_1438,c_121])).

tff(c_1470,plain,(
    k2_relat_1('#skF_5') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_103,c_135,c_1462])).

tff(c_1526,plain,(
    k10_relat_1('#skF_5','#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1470,c_796])).

tff(c_22,plain,(
    ! [A_13] :
      ( v1_funct_1(k2_funct_1(A_13))
      | ~ v2_funct_1(A_13)
      | ~ v1_funct_1(A_13)
      | ~ v1_relat_1(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_303,plain,(
    ! [B_98,A_99] :
      ( k9_relat_1(B_98,k10_relat_1(B_98,A_99)) = A_99
      | ~ r1_tarski(A_99,k2_relat_1(B_98))
      | ~ v1_funct_1(B_98)
      | ~ v1_relat_1(B_98) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_318,plain,(
    ! [B_100] :
      ( k9_relat_1(B_100,k10_relat_1(B_100,k2_relat_1(B_100))) = k2_relat_1(B_100)
      | ~ v1_funct_1(B_100)
      | ~ v1_relat_1(B_100) ) ),
    inference(resolution,[status(thm)],[c_6,c_303])).

tff(c_355,plain,(
    ! [A_103] :
      ( k9_relat_1(A_103,k1_relat_1(A_103)) = k2_relat_1(A_103)
      | ~ v1_funct_1(A_103)
      | ~ v1_relat_1(A_103)
      | ~ v1_relat_1(A_103) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_318])).

tff(c_112,plain,(
    ! [B_6,A_5] :
      ( k9_relat_1(B_6,A_5) = k2_relat_1(B_6)
      | ~ r1_tarski(k2_relat_1(B_6),k9_relat_1(B_6,A_5))
      | ~ v1_relat_1(B_6) ) ),
    inference(resolution,[status(thm)],[c_12,c_105])).

tff(c_361,plain,(
    ! [A_103] :
      ( k9_relat_1(A_103,k1_relat_1(A_103)) = k2_relat_1(A_103)
      | ~ r1_tarski(k2_relat_1(A_103),k2_relat_1(A_103))
      | ~ v1_relat_1(A_103)
      | ~ v1_funct_1(A_103)
      | ~ v1_relat_1(A_103)
      | ~ v1_relat_1(A_103) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_355,c_112])).

tff(c_381,plain,(
    ! [A_103] :
      ( k9_relat_1(A_103,k1_relat_1(A_103)) = k2_relat_1(A_103)
      | ~ v1_funct_1(A_103)
      | ~ v1_relat_1(A_103) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_361])).

tff(c_540,plain,
    ( k9_relat_1('#skF_5','#skF_2') = k2_relat_1('#skF_5')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_535,c_381])).

tff(c_550,plain,(
    k9_relat_1('#skF_5','#skF_2') = k2_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_103,c_72,c_540])).

tff(c_249,plain,(
    ! [B_88,A_89] :
      ( k10_relat_1(k2_funct_1(B_88),A_89) = k9_relat_1(B_88,A_89)
      | ~ v2_funct_1(B_88)
      | ~ v1_funct_1(B_88)
      | ~ v1_relat_1(B_88) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_255,plain,(
    ! [B_88,A_89] :
      ( r1_tarski(k9_relat_1(B_88,A_89),k1_relat_1(k2_funct_1(B_88)))
      | ~ v1_relat_1(k2_funct_1(B_88))
      | ~ v2_funct_1(B_88)
      | ~ v1_funct_1(B_88)
      | ~ v1_relat_1(B_88) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_249,c_16])).

tff(c_619,plain,
    ( r1_tarski(k2_relat_1('#skF_5'),k1_relat_1(k2_funct_1('#skF_5')))
    | ~ v1_relat_1(k2_funct_1('#skF_5'))
    | ~ v2_funct_1('#skF_5')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_550,c_255])).

tff(c_635,plain,
    ( r1_tarski(k2_relat_1('#skF_5'),k1_relat_1(k2_funct_1('#skF_5')))
    | ~ v1_relat_1(k2_funct_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_103,c_72,c_64,c_619])).

tff(c_1002,plain,(
    r1_tarski(k2_relat_1('#skF_5'),k1_relat_1(k2_funct_1('#skF_5'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_863,c_635])).

tff(c_1525,plain,(
    r1_tarski('#skF_3',k1_relat_1(k2_funct_1('#skF_5'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1470,c_1002])).

tff(c_266,plain,(
    ! [B_88] :
      ( k9_relat_1(B_88,k2_relat_1(k2_funct_1(B_88))) = k1_relat_1(k2_funct_1(B_88))
      | ~ v2_funct_1(B_88)
      | ~ v1_funct_1(B_88)
      | ~ v1_relat_1(B_88)
      | ~ v1_relat_1(k2_funct_1(B_88)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_249])).

tff(c_1567,plain,(
    ! [A_5] :
      ( r1_tarski(k9_relat_1('#skF_5',A_5),'#skF_3')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1470,c_12])).

tff(c_1667,plain,(
    ! [A_165] : r1_tarski(k9_relat_1('#skF_5',A_165),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_103,c_1567])).

tff(c_1679,plain,
    ( r1_tarski(k1_relat_1(k2_funct_1('#skF_5')),'#skF_3')
    | ~ v2_funct_1('#skF_5')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5')
    | ~ v1_relat_1(k2_funct_1('#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_266,c_1667])).

tff(c_1701,plain,(
    r1_tarski(k1_relat_1(k2_funct_1('#skF_5')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_863,c_103,c_72,c_64,c_1679])).

tff(c_1712,plain,
    ( k1_relat_1(k2_funct_1('#skF_5')) = '#skF_3'
    | ~ r1_tarski('#skF_3',k1_relat_1(k2_funct_1('#skF_5'))) ),
    inference(resolution,[status(thm)],[c_1701,c_2])).

tff(c_1715,plain,(
    k1_relat_1(k2_funct_1('#skF_5')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1525,c_1712])).

tff(c_1728,plain,
    ( k9_relat_1(k2_funct_1('#skF_5'),'#skF_3') = k2_relat_1(k2_funct_1('#skF_5'))
    | ~ v1_funct_1(k2_funct_1('#skF_5'))
    | ~ v1_relat_1(k2_funct_1('#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1715,c_381])).

tff(c_1740,plain,
    ( k9_relat_1(k2_funct_1('#skF_5'),'#skF_3') = k2_relat_1(k2_funct_1('#skF_5'))
    | ~ v1_funct_1(k2_funct_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_863,c_1728])).

tff(c_2804,plain,(
    ~ v1_funct_1(k2_funct_1('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_1740])).

tff(c_2807,plain,
    ( ~ v2_funct_1('#skF_5')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_22,c_2804])).

tff(c_2811,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_103,c_72,c_64,c_2807])).

tff(c_2812,plain,(
    k9_relat_1(k2_funct_1('#skF_5'),'#skF_3') = k2_relat_1(k2_funct_1('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_1740])).

tff(c_30,plain,(
    ! [B_19,A_18] :
      ( k9_relat_1(k2_funct_1(B_19),A_18) = k10_relat_1(B_19,A_18)
      | ~ v2_funct_1(B_19)
      | ~ v1_funct_1(B_19)
      | ~ v1_relat_1(B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_2830,plain,
    ( k2_relat_1(k2_funct_1('#skF_5')) = k10_relat_1('#skF_5','#skF_3')
    | ~ v2_funct_1('#skF_5')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_2812,c_30])).

tff(c_2848,plain,(
    k2_relat_1(k2_funct_1('#skF_5')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_103,c_72,c_64,c_1526,c_2830])).

tff(c_877,plain,
    ( k2_relat_1(k2_funct_1('#skF_5')) = '#skF_2'
    | ~ r1_tarski(k2_relat_1(k2_funct_1('#skF_5')),'#skF_2') ),
    inference(resolution,[status(thm)],[c_862,c_2])).

tff(c_1052,plain,(
    ~ r1_tarski(k2_relat_1(k2_funct_1('#skF_5')),'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_877])).

tff(c_2856,plain,(
    ~ r1_tarski('#skF_2','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2848,c_1052])).

tff(c_2861,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_2856])).

tff(c_2862,plain,(
    k2_relat_1(k2_funct_1('#skF_5')) = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_877])).

tff(c_147,plain,(
    ! [B_70,A_71] :
      ( v5_relat_1(B_70,A_71)
      | ~ r1_tarski(k2_relat_1(B_70),A_71)
      | ~ v1_relat_1(B_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_156,plain,(
    ! [B_70] :
      ( v5_relat_1(B_70,k2_relat_1(B_70))
      | ~ v1_relat_1(B_70) ) ),
    inference(resolution,[status(thm)],[c_6,c_147])).

tff(c_2914,plain,
    ( v5_relat_1(k2_funct_1('#skF_5'),'#skF_2')
    | ~ v1_relat_1(k2_funct_1('#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_2862,c_156])).

tff(c_2950,plain,(
    v5_relat_1(k2_funct_1('#skF_5'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_863,c_2914])).

tff(c_2952,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_878,c_2950])).

tff(c_2953,plain,(
    k2_relat_1(k2_funct_1('#skF_5')) = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_876])).

tff(c_2997,plain,
    ( k10_relat_1(k2_funct_1('#skF_5'),'#skF_2') = k1_relat_1(k2_funct_1('#skF_5'))
    | ~ v1_relat_1(k2_funct_1('#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_2953,c_18])).

tff(c_3027,plain,(
    k10_relat_1(k2_funct_1('#skF_5'),'#skF_2') = k1_relat_1(k2_funct_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_863,c_2997])).

tff(c_28,plain,(
    ! [B_17,A_16] :
      ( k10_relat_1(k2_funct_1(B_17),A_16) = k9_relat_1(B_17,A_16)
      | ~ v2_funct_1(B_17)
      | ~ v1_funct_1(B_17)
      | ~ v1_relat_1(B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_3140,plain,
    ( k1_relat_1(k2_funct_1('#skF_5')) = k9_relat_1('#skF_5','#skF_2')
    | ~ v2_funct_1('#skF_5')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_3027,c_28])).

tff(c_3154,plain,(
    k1_relat_1(k2_funct_1('#skF_5')) = k2_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_103,c_72,c_64,c_550,c_3140])).

tff(c_3167,plain,
    ( k9_relat_1(k2_funct_1('#skF_5'),k2_relat_1('#skF_5')) = k2_relat_1(k2_funct_1('#skF_5'))
    | ~ v1_funct_1(k2_funct_1('#skF_5'))
    | ~ v1_relat_1(k2_funct_1('#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_3154,c_381])).

tff(c_3179,plain,
    ( k9_relat_1(k2_funct_1('#skF_5'),k2_relat_1('#skF_5')) = '#skF_2'
    | ~ v1_funct_1(k2_funct_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_863,c_2953,c_3167])).

tff(c_3622,plain,(
    ~ v1_funct_1(k2_funct_1('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_3179])).

tff(c_3625,plain,
    ( ~ v2_funct_1('#skF_5')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_22,c_3622])).

tff(c_3629,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_103,c_72,c_64,c_3625])).

tff(c_3631,plain,(
    v1_funct_1(k2_funct_1('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_3179])).

tff(c_4127,plain,(
    ! [A_5] :
      ( r1_tarski(k9_relat_1('#skF_5',A_5),'#skF_3')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4078,c_12])).

tff(c_4158,plain,(
    ! [A_5] : r1_tarski(k9_relat_1('#skF_5',A_5),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_103,c_4127])).

tff(c_3164,plain,(
    ! [A_89] :
      ( r1_tarski(k9_relat_1('#skF_5',A_89),k2_relat_1('#skF_5'))
      | ~ v1_relat_1(k2_funct_1('#skF_5'))
      | ~ v2_funct_1('#skF_5')
      | ~ v1_funct_1('#skF_5')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3154,c_255])).

tff(c_3232,plain,(
    ! [A_250] : r1_tarski(k9_relat_1('#skF_5',A_250),k2_relat_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_103,c_72,c_64,c_863,c_3164])).

tff(c_26,plain,(
    ! [B_15,A_14] :
      ( k9_relat_1(B_15,k10_relat_1(B_15,A_14)) = A_14
      | ~ r1_tarski(A_14,k2_relat_1(B_15))
      | ~ v1_funct_1(B_15)
      | ~ v1_relat_1(B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_3234,plain,(
    ! [A_250] :
      ( k9_relat_1('#skF_5',k10_relat_1('#skF_5',k9_relat_1('#skF_5',A_250))) = k9_relat_1('#skF_5',A_250)
      | ~ v1_funct_1('#skF_5')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_3232,c_26])).

tff(c_3260,plain,(
    ! [A_250] : k9_relat_1('#skF_5',k10_relat_1('#skF_5',k9_relat_1('#skF_5',A_250))) = k9_relat_1('#skF_5',A_250) ),
    inference(demodulation,[status(thm),theory(equality)],[c_103,c_72,c_3234])).

tff(c_3173,plain,(
    ! [A_10] :
      ( r1_tarski(k10_relat_1(k2_funct_1('#skF_5'),A_10),k2_relat_1('#skF_5'))
      | ~ v1_relat_1(k2_funct_1('#skF_5')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3154,c_16])).

tff(c_3292,plain,(
    ! [A_252] : r1_tarski(k10_relat_1(k2_funct_1('#skF_5'),A_252),k2_relat_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_863,c_3173])).

tff(c_3294,plain,(
    ! [A_252] :
      ( k9_relat_1('#skF_5',k10_relat_1('#skF_5',k10_relat_1(k2_funct_1('#skF_5'),A_252))) = k10_relat_1(k2_funct_1('#skF_5'),A_252)
      | ~ v1_funct_1('#skF_5')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_3292,c_26])).

tff(c_6631,plain,(
    ! [A_404] : k9_relat_1('#skF_5',k10_relat_1('#skF_5',k10_relat_1(k2_funct_1('#skF_5'),A_404))) = k10_relat_1(k2_funct_1('#skF_5'),A_404) ),
    inference(demodulation,[status(thm),theory(equality)],[c_103,c_72,c_3294])).

tff(c_6694,plain,(
    ! [A_16] :
      ( k9_relat_1('#skF_5',k10_relat_1('#skF_5',k9_relat_1('#skF_5',A_16))) = k10_relat_1(k2_funct_1('#skF_5'),A_16)
      | ~ v2_funct_1('#skF_5')
      | ~ v1_funct_1('#skF_5')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_6631])).

tff(c_6731,plain,(
    ! [A_16] : k10_relat_1(k2_funct_1('#skF_5'),A_16) = k9_relat_1('#skF_5',A_16) ),
    inference(demodulation,[status(thm),theory(equality)],[c_103,c_72,c_64,c_3260,c_6694])).

tff(c_10,plain,(
    ! [B_4,A_3] :
      ( r1_tarski(k2_relat_1(B_4),A_3)
      | ~ v5_relat_1(B_4,A_3)
      | ~ v1_relat_1(B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_315,plain,(
    ! [B_98,B_4] :
      ( k9_relat_1(B_98,k10_relat_1(B_98,k2_relat_1(B_4))) = k2_relat_1(B_4)
      | ~ v1_funct_1(B_98)
      | ~ v1_relat_1(B_98)
      | ~ v5_relat_1(B_4,k2_relat_1(B_98))
      | ~ v1_relat_1(B_4) ) ),
    inference(resolution,[status(thm)],[c_10,c_303])).

tff(c_4103,plain,(
    ! [A_14] :
      ( k9_relat_1('#skF_5',k10_relat_1('#skF_5',A_14)) = A_14
      | ~ r1_tarski(A_14,'#skF_3')
      | ~ v1_funct_1('#skF_5')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4078,c_26])).

tff(c_4142,plain,(
    ! [A_14] :
      ( k9_relat_1('#skF_5',k10_relat_1('#skF_5',A_14)) = A_14
      | ~ r1_tarski(A_14,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_103,c_72,c_4103])).

tff(c_6742,plain,(
    ! [A_405] : k10_relat_1(k2_funct_1('#skF_5'),A_405) = k9_relat_1('#skF_5',A_405) ),
    inference(demodulation,[status(thm),theory(equality)],[c_103,c_72,c_64,c_3260,c_6694])).

tff(c_316,plain,(
    ! [B_6,A_5] :
      ( k9_relat_1(B_6,k10_relat_1(B_6,k9_relat_1(B_6,A_5))) = k9_relat_1(B_6,A_5)
      | ~ v1_funct_1(B_6)
      | ~ v1_relat_1(B_6) ) ),
    inference(resolution,[status(thm)],[c_12,c_303])).

tff(c_6759,plain,(
    ! [A_5] :
      ( k9_relat_1(k2_funct_1('#skF_5'),k9_relat_1('#skF_5',k9_relat_1(k2_funct_1('#skF_5'),A_5))) = k9_relat_1(k2_funct_1('#skF_5'),A_5)
      | ~ v1_funct_1(k2_funct_1('#skF_5'))
      | ~ v1_relat_1(k2_funct_1('#skF_5')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6742,c_316])).

tff(c_22381,plain,(
    ! [A_809] : k9_relat_1(k2_funct_1('#skF_5'),k9_relat_1('#skF_5',k9_relat_1(k2_funct_1('#skF_5'),A_809))) = k9_relat_1(k2_funct_1('#skF_5'),A_809) ),
    inference(demodulation,[status(thm),theory(equality)],[c_863,c_3631,c_6759])).

tff(c_22412,plain,(
    ! [A_809] :
      ( k10_relat_1('#skF_5',k9_relat_1('#skF_5',k9_relat_1(k2_funct_1('#skF_5'),A_809))) = k9_relat_1(k2_funct_1('#skF_5'),A_809)
      | ~ v2_funct_1('#skF_5')
      | ~ v1_funct_1('#skF_5')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22381,c_30])).

tff(c_22589,plain,(
    ! [A_812] : k10_relat_1('#skF_5',k9_relat_1('#skF_5',k9_relat_1(k2_funct_1('#skF_5'),A_812))) = k9_relat_1(k2_funct_1('#skF_5'),A_812) ),
    inference(demodulation,[status(thm),theory(equality)],[c_103,c_72,c_64,c_22412])).

tff(c_22674,plain,(
    ! [A_18] :
      ( k10_relat_1('#skF_5',k9_relat_1('#skF_5',k10_relat_1('#skF_5',A_18))) = k9_relat_1(k2_funct_1('#skF_5'),A_18)
      | ~ v2_funct_1('#skF_5')
      | ~ v1_funct_1('#skF_5')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_22589])).

tff(c_22726,plain,(
    ! [A_813] : k10_relat_1('#skF_5',k9_relat_1('#skF_5',k10_relat_1('#skF_5',A_813))) = k9_relat_1(k2_funct_1('#skF_5'),A_813) ),
    inference(demodulation,[status(thm),theory(equality)],[c_103,c_72,c_64,c_22674])).

tff(c_22862,plain,(
    ! [A_814] :
      ( k9_relat_1(k2_funct_1('#skF_5'),A_814) = k10_relat_1('#skF_5',A_814)
      | ~ r1_tarski(A_814,'#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4142,c_22726])).

tff(c_22969,plain,(
    ! [B_4] :
      ( k10_relat_1('#skF_5',k10_relat_1(k2_funct_1('#skF_5'),k2_relat_1(B_4))) = k2_relat_1(B_4)
      | ~ r1_tarski(k10_relat_1(k2_funct_1('#skF_5'),k2_relat_1(B_4)),'#skF_3')
      | ~ v1_funct_1(k2_funct_1('#skF_5'))
      | ~ v1_relat_1(k2_funct_1('#skF_5'))
      | ~ v5_relat_1(B_4,k2_relat_1(k2_funct_1('#skF_5')))
      | ~ v1_relat_1(B_4) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_315,c_22862])).

tff(c_25144,plain,(
    ! [B_840] :
      ( k10_relat_1('#skF_5',k9_relat_1('#skF_5',k2_relat_1(B_840))) = k2_relat_1(B_840)
      | ~ v5_relat_1(B_840,'#skF_2')
      | ~ v1_relat_1(B_840) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2953,c_863,c_3631,c_4158,c_6731,c_6731,c_22969])).

tff(c_25218,plain,
    ( k10_relat_1('#skF_5','#skF_3') = k2_relat_1('#skF_4')
    | ~ v5_relat_1('#skF_4','#skF_2')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_7682,c_25144])).

tff(c_25288,plain,(
    k2_relat_1('#skF_4') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_134,c_4086,c_25218])).

tff(c_25290,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_167,c_25288])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:30:26 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 13.83/5.39  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 13.97/5.42  
% 13.97/5.42  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 13.97/5.42  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k5_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 13.97/5.42  
% 13.97/5.42  %Foreground sorts:
% 13.97/5.42  
% 13.97/5.42  
% 13.97/5.42  %Background operators:
% 13.97/5.42  
% 13.97/5.42  
% 13.97/5.42  %Foreground operators:
% 13.97/5.42  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 13.97/5.42  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 13.97/5.42  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 13.97/5.42  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 13.97/5.42  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 13.97/5.42  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 13.97/5.42  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 13.97/5.42  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 13.97/5.42  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 13.97/5.42  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 13.97/5.42  tff('#skF_5', type, '#skF_5': $i).
% 13.97/5.42  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 13.97/5.42  tff('#skF_2', type, '#skF_2': $i).
% 13.97/5.42  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 13.97/5.42  tff('#skF_3', type, '#skF_3': $i).
% 13.97/5.42  tff('#skF_1', type, '#skF_1': $i).
% 13.97/5.42  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 13.97/5.42  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 13.97/5.42  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 13.97/5.42  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 13.97/5.42  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 13.97/5.42  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 13.97/5.42  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 13.97/5.42  tff('#skF_4', type, '#skF_4': $i).
% 13.97/5.42  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 13.97/5.42  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 13.97/5.42  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 13.97/5.42  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 13.97/5.42  
% 13.97/5.45  tff(f_172, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, B, C)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (((k2_relset_1(A, C, k1_partfun1(A, B, B, C, D, E)) = C) & v2_funct_1(E)) => ((C = k1_xboole_0) | (k2_relset_1(A, B, D) = B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_funct_2)).
% 13.97/5.45  tff(f_110, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 13.97/5.45  tff(f_96, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 13.97/5.45  tff(f_102, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 13.97/5.45  tff(f_150, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 13.97/5.45  tff(f_140, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (v1_funct_1(k1_partfun1(A, B, C, D, E, F)) & m1_subset_1(k1_partfun1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 13.97/5.45  tff(f_48, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k2_relat_1(k5_relat_1(A, B)) = k9_relat_1(B, k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t160_relat_1)).
% 13.97/5.45  tff(f_41, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k9_relat_1(B, A), k2_relat_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t144_relat_1)).
% 13.97/5.45  tff(f_37, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 13.97/5.45  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 13.97/5.45  tff(f_106, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 13.97/5.45  tff(f_128, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 13.97/5.45  tff(f_56, axiom, (![A]: (v1_relat_1(A) => (k10_relat_1(A, k2_relat_1(A)) = k1_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t169_relat_1)).
% 13.97/5.45  tff(f_52, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k10_relat_1(B, A), k1_relat_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t167_relat_1)).
% 13.97/5.45  tff(f_68, axiom, (![A]: (((v1_relat_1(A) & v1_funct_1(A)) & v2_funct_1(A)) => ((v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))) & v2_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_funct_1)).
% 13.97/5.45  tff(f_92, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (v2_funct_1(B) => (k10_relat_1(B, A) = k9_relat_1(k2_funct_1(B), A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t155_funct_1)).
% 13.97/5.45  tff(f_76, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r1_tarski(A, k2_relat_1(B)) => (k9_relat_1(B, k10_relat_1(B, A)) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t147_funct_1)).
% 13.97/5.45  tff(f_84, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (v2_funct_1(B) => (k9_relat_1(B, A) = k10_relat_1(k2_funct_1(B), A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t154_funct_1)).
% 13.97/5.45  tff(c_74, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_172])).
% 13.97/5.45  tff(c_157, plain, (![A_72, B_73, C_74]: (k2_relset_1(A_72, B_73, C_74)=k2_relat_1(C_74) | ~m1_subset_1(C_74, k1_zfmisc_1(k2_zfmisc_1(A_72, B_73))))), inference(cnfTransformation, [status(thm)], [f_110])).
% 13.97/5.45  tff(c_164, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_74, c_157])).
% 13.97/5.45  tff(c_60, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_4')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_172])).
% 13.97/5.45  tff(c_167, plain, (k2_relat_1('#skF_4')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_164, c_60])).
% 13.97/5.45  tff(c_95, plain, (![C_52, A_53, B_54]: (v1_relat_1(C_52) | ~m1_subset_1(C_52, k1_zfmisc_1(k2_zfmisc_1(A_53, B_54))))), inference(cnfTransformation, [status(thm)], [f_96])).
% 13.97/5.45  tff(c_102, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_74, c_95])).
% 13.97/5.45  tff(c_127, plain, (![C_62, B_63, A_64]: (v5_relat_1(C_62, B_63) | ~m1_subset_1(C_62, k1_zfmisc_1(k2_zfmisc_1(A_64, B_63))))), inference(cnfTransformation, [status(thm)], [f_102])).
% 13.97/5.45  tff(c_134, plain, (v5_relat_1('#skF_4', '#skF_2')), inference(resolution, [status(thm)], [c_74, c_127])).
% 13.97/5.45  tff(c_68, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_172])).
% 13.97/5.45  tff(c_103, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_68, c_95])).
% 13.97/5.45  tff(c_135, plain, (v5_relat_1('#skF_5', '#skF_3')), inference(resolution, [status(thm)], [c_68, c_127])).
% 13.97/5.45  tff(c_78, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_172])).
% 13.97/5.45  tff(c_72, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_172])).
% 13.97/5.45  tff(c_779, plain, (![C_136, D_137, F_138, E_134, B_139, A_135]: (k1_partfun1(A_135, B_139, C_136, D_137, E_134, F_138)=k5_relat_1(E_134, F_138) | ~m1_subset_1(F_138, k1_zfmisc_1(k2_zfmisc_1(C_136, D_137))) | ~v1_funct_1(F_138) | ~m1_subset_1(E_134, k1_zfmisc_1(k2_zfmisc_1(A_135, B_139))) | ~v1_funct_1(E_134))), inference(cnfTransformation, [status(thm)], [f_150])).
% 13.97/5.45  tff(c_783, plain, (![A_135, B_139, E_134]: (k1_partfun1(A_135, B_139, '#skF_2', '#skF_3', E_134, '#skF_5')=k5_relat_1(E_134, '#skF_5') | ~v1_funct_1('#skF_5') | ~m1_subset_1(E_134, k1_zfmisc_1(k2_zfmisc_1(A_135, B_139))) | ~v1_funct_1(E_134))), inference(resolution, [status(thm)], [c_68, c_779])).
% 13.97/5.45  tff(c_3754, plain, (![A_262, B_263, E_264]: (k1_partfun1(A_262, B_263, '#skF_2', '#skF_3', E_264, '#skF_5')=k5_relat_1(E_264, '#skF_5') | ~m1_subset_1(E_264, k1_zfmisc_1(k2_zfmisc_1(A_262, B_263))) | ~v1_funct_1(E_264))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_783])).
% 13.97/5.45  tff(c_3763, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_3', '#skF_4', '#skF_5')=k5_relat_1('#skF_4', '#skF_5') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_74, c_3754])).
% 13.97/5.45  tff(c_3773, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_3', '#skF_4', '#skF_5')=k5_relat_1('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_3763])).
% 13.97/5.45  tff(c_66, plain, (k2_relset_1('#skF_1', '#skF_3', k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_3', '#skF_4', '#skF_5'))='#skF_3'), inference(cnfTransformation, [status(thm)], [f_172])).
% 13.97/5.45  tff(c_3840, plain, (k2_relset_1('#skF_1', '#skF_3', k5_relat_1('#skF_4', '#skF_5'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_3773, c_66])).
% 13.97/5.45  tff(c_54, plain, (![A_35, F_40, B_36, C_37, D_38, E_39]: (m1_subset_1(k1_partfun1(A_35, B_36, C_37, D_38, E_39, F_40), k1_zfmisc_1(k2_zfmisc_1(A_35, D_38))) | ~m1_subset_1(F_40, k1_zfmisc_1(k2_zfmisc_1(C_37, D_38))) | ~v1_funct_1(F_40) | ~m1_subset_1(E_39, k1_zfmisc_1(k2_zfmisc_1(A_35, B_36))) | ~v1_funct_1(E_39))), inference(cnfTransformation, [status(thm)], [f_140])).
% 13.97/5.45  tff(c_3844, plain, (m1_subset_1(k5_relat_1('#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3'))) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_3773, c_54])).
% 13.97/5.45  tff(c_3848, plain, (m1_subset_1(k5_relat_1('#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_74, c_72, c_68, c_3844])).
% 13.97/5.45  tff(c_40, plain, (![A_29, B_30, C_31]: (k2_relset_1(A_29, B_30, C_31)=k2_relat_1(C_31) | ~m1_subset_1(C_31, k1_zfmisc_1(k2_zfmisc_1(A_29, B_30))))), inference(cnfTransformation, [status(thm)], [f_110])).
% 13.97/5.45  tff(c_3881, plain, (k2_relset_1('#skF_1', '#skF_3', k5_relat_1('#skF_4', '#skF_5'))=k2_relat_1(k5_relat_1('#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_3848, c_40])).
% 13.97/5.45  tff(c_3917, plain, (k2_relat_1(k5_relat_1('#skF_4', '#skF_5'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_3840, c_3881])).
% 13.97/5.45  tff(c_194, plain, (![B_80, A_81]: (k9_relat_1(B_80, k2_relat_1(A_81))=k2_relat_1(k5_relat_1(A_81, B_80)) | ~v1_relat_1(B_80) | ~v1_relat_1(A_81))), inference(cnfTransformation, [status(thm)], [f_48])).
% 13.97/5.45  tff(c_12, plain, (![B_6, A_5]: (r1_tarski(k9_relat_1(B_6, A_5), k2_relat_1(B_6)) | ~v1_relat_1(B_6))), inference(cnfTransformation, [status(thm)], [f_41])).
% 13.97/5.45  tff(c_200, plain, (![A_81, B_80]: (r1_tarski(k2_relat_1(k5_relat_1(A_81, B_80)), k2_relat_1(B_80)) | ~v1_relat_1(B_80) | ~v1_relat_1(B_80) | ~v1_relat_1(A_81))), inference(superposition, [status(thm), theory('equality')], [c_194, c_12])).
% 13.97/5.45  tff(c_4005, plain, (r1_tarski('#skF_3', k2_relat_1('#skF_5')) | ~v1_relat_1('#skF_5') | ~v1_relat_1('#skF_5') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_3917, c_200])).
% 13.97/5.45  tff(c_4046, plain, (r1_tarski('#skF_3', k2_relat_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_102, c_103, c_103, c_4005])).
% 13.97/5.45  tff(c_118, plain, (![B_59, A_60]: (r1_tarski(k2_relat_1(B_59), A_60) | ~v5_relat_1(B_59, A_60) | ~v1_relat_1(B_59))), inference(cnfTransformation, [status(thm)], [f_37])).
% 13.97/5.45  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 13.97/5.45  tff(c_121, plain, (![B_59, A_60]: (k2_relat_1(B_59)=A_60 | ~r1_tarski(A_60, k2_relat_1(B_59)) | ~v5_relat_1(B_59, A_60) | ~v1_relat_1(B_59))), inference(resolution, [status(thm)], [c_118, c_2])).
% 13.97/5.45  tff(c_4070, plain, (k2_relat_1('#skF_5')='#skF_3' | ~v5_relat_1('#skF_5', '#skF_3') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_4046, c_121])).
% 13.97/5.45  tff(c_4078, plain, (k2_relat_1('#skF_5')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_103, c_135, c_4070])).
% 13.97/5.45  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 13.97/5.45  tff(c_62, plain, (k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_172])).
% 13.97/5.45  tff(c_70, plain, (v1_funct_2('#skF_5', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_172])).
% 13.97/5.45  tff(c_176, plain, (![A_76, B_77, C_78]: (k1_relset_1(A_76, B_77, C_78)=k1_relat_1(C_78) | ~m1_subset_1(C_78, k1_zfmisc_1(k2_zfmisc_1(A_76, B_77))))), inference(cnfTransformation, [status(thm)], [f_106])).
% 13.97/5.45  tff(c_184, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_68, c_176])).
% 13.97/5.45  tff(c_522, plain, (![B_120, A_121, C_122]: (k1_xboole_0=B_120 | k1_relset_1(A_121, B_120, C_122)=A_121 | ~v1_funct_2(C_122, A_121, B_120) | ~m1_subset_1(C_122, k1_zfmisc_1(k2_zfmisc_1(A_121, B_120))))), inference(cnfTransformation, [status(thm)], [f_128])).
% 13.97/5.45  tff(c_528, plain, (k1_xboole_0='#skF_3' | k1_relset_1('#skF_2', '#skF_3', '#skF_5')='#skF_2' | ~v1_funct_2('#skF_5', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_68, c_522])).
% 13.97/5.45  tff(c_534, plain, (k1_xboole_0='#skF_3' | k1_relat_1('#skF_5')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_70, c_184, c_528])).
% 13.97/5.45  tff(c_535, plain, (k1_relat_1('#skF_5')='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_62, c_534])).
% 13.97/5.45  tff(c_18, plain, (![A_12]: (k10_relat_1(A_12, k2_relat_1(A_12))=k1_relat_1(A_12) | ~v1_relat_1(A_12))), inference(cnfTransformation, [status(thm)], [f_56])).
% 13.97/5.45  tff(c_16, plain, (![B_11, A_10]: (r1_tarski(k10_relat_1(B_11, A_10), k1_relat_1(B_11)) | ~v1_relat_1(B_11))), inference(cnfTransformation, [status(thm)], [f_52])).
% 13.97/5.45  tff(c_105, plain, (![B_57, A_58]: (B_57=A_58 | ~r1_tarski(B_57, A_58) | ~r1_tarski(A_58, B_57))), inference(cnfTransformation, [status(thm)], [f_31])).
% 13.97/5.45  tff(c_113, plain, (![B_11, A_10]: (k10_relat_1(B_11, A_10)=k1_relat_1(B_11) | ~r1_tarski(k1_relat_1(B_11), k10_relat_1(B_11, A_10)) | ~v1_relat_1(B_11))), inference(resolution, [status(thm)], [c_16, c_105])).
% 13.97/5.45  tff(c_543, plain, (![A_10]: (k10_relat_1('#skF_5', A_10)=k1_relat_1('#skF_5') | ~r1_tarski('#skF_2', k10_relat_1('#skF_5', A_10)) | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_535, c_113])).
% 13.97/5.45  tff(c_790, plain, (![A_140]: (k10_relat_1('#skF_5', A_140)='#skF_2' | ~r1_tarski('#skF_2', k10_relat_1('#skF_5', A_140)))), inference(demodulation, [status(thm), theory('equality')], [c_103, c_535, c_543])).
% 13.97/5.45  tff(c_794, plain, (k10_relat_1('#skF_5', k2_relat_1('#skF_5'))='#skF_2' | ~r1_tarski('#skF_2', k1_relat_1('#skF_5')) | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_18, c_790])).
% 13.97/5.45  tff(c_796, plain, (k10_relat_1('#skF_5', k2_relat_1('#skF_5'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_103, c_6, c_535, c_794])).
% 13.97/5.45  tff(c_4086, plain, (k10_relat_1('#skF_5', '#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_4078, c_796])).
% 13.97/5.45  tff(c_14, plain, (![B_9, A_7]: (k9_relat_1(B_9, k2_relat_1(A_7))=k2_relat_1(k5_relat_1(A_7, B_9)) | ~v1_relat_1(B_9) | ~v1_relat_1(A_7))), inference(cnfTransformation, [status(thm)], [f_48])).
% 13.97/5.45  tff(c_269, plain, (![B_90, A_91]: (k9_relat_1(B_90, A_91)=k2_relat_1(B_90) | ~r1_tarski(k2_relat_1(B_90), k9_relat_1(B_90, A_91)) | ~v1_relat_1(B_90))), inference(resolution, [status(thm)], [c_12, c_105])).
% 13.97/5.45  tff(c_7615, plain, (![B_429, A_430]: (k9_relat_1(B_429, k2_relat_1(A_430))=k2_relat_1(B_429) | ~r1_tarski(k2_relat_1(B_429), k2_relat_1(k5_relat_1(A_430, B_429))) | ~v1_relat_1(B_429) | ~v1_relat_1(B_429) | ~v1_relat_1(A_430))), inference(superposition, [status(thm), theory('equality')], [c_14, c_269])).
% 13.97/5.45  tff(c_7648, plain, (k9_relat_1('#skF_5', k2_relat_1('#skF_4'))=k2_relat_1('#skF_5') | ~r1_tarski(k2_relat_1('#skF_5'), '#skF_3') | ~v1_relat_1('#skF_5') | ~v1_relat_1('#skF_5') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_3917, c_7615])).
% 13.97/5.45  tff(c_7682, plain, (k9_relat_1('#skF_5', k2_relat_1('#skF_4'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_102, c_103, c_103, c_6, c_4078, c_4078, c_7648])).
% 13.97/5.45  tff(c_64, plain, (v2_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_172])).
% 13.97/5.45  tff(c_24, plain, (![A_13]: (v1_relat_1(k2_funct_1(A_13)) | ~v2_funct_1(A_13) | ~v1_funct_1(A_13) | ~v1_relat_1(A_13))), inference(cnfTransformation, [status(thm)], [f_68])).
% 13.97/5.45  tff(c_206, plain, (![B_82, A_83]: (k9_relat_1(k2_funct_1(B_82), A_83)=k10_relat_1(B_82, A_83) | ~v2_funct_1(B_82) | ~v1_funct_1(B_82) | ~v1_relat_1(B_82))), inference(cnfTransformation, [status(thm)], [f_92])).
% 13.97/5.45  tff(c_216, plain, (![B_82, A_83]: (r1_tarski(k10_relat_1(B_82, A_83), k2_relat_1(k2_funct_1(B_82))) | ~v1_relat_1(k2_funct_1(B_82)) | ~v2_funct_1(B_82) | ~v1_funct_1(B_82) | ~v1_relat_1(B_82))), inference(superposition, [status(thm), theory('equality')], [c_206, c_12])).
% 13.97/5.45  tff(c_807, plain, (r1_tarski('#skF_2', k2_relat_1(k2_funct_1('#skF_5'))) | ~v1_relat_1(k2_funct_1('#skF_5')) | ~v2_funct_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_796, c_216])).
% 13.97/5.45  tff(c_829, plain, (r1_tarski('#skF_2', k2_relat_1(k2_funct_1('#skF_5'))) | ~v1_relat_1(k2_funct_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_103, c_72, c_64, c_807])).
% 13.97/5.45  tff(c_841, plain, (~v1_relat_1(k2_funct_1('#skF_5'))), inference(splitLeft, [status(thm)], [c_829])).
% 13.97/5.45  tff(c_857, plain, (~v2_funct_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_24, c_841])).
% 13.97/5.45  tff(c_861, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_103, c_72, c_64, c_857])).
% 13.97/5.45  tff(c_863, plain, (v1_relat_1(k2_funct_1('#skF_5'))), inference(splitRight, [status(thm)], [c_829])).
% 13.97/5.45  tff(c_862, plain, (r1_tarski('#skF_2', k2_relat_1(k2_funct_1('#skF_5')))), inference(splitRight, [status(thm)], [c_829])).
% 13.97/5.45  tff(c_868, plain, (k2_relat_1(k2_funct_1('#skF_5'))='#skF_2' | ~v5_relat_1(k2_funct_1('#skF_5'), '#skF_2') | ~v1_relat_1(k2_funct_1('#skF_5'))), inference(resolution, [status(thm)], [c_862, c_121])).
% 13.97/5.45  tff(c_876, plain, (k2_relat_1(k2_funct_1('#skF_5'))='#skF_2' | ~v5_relat_1(k2_funct_1('#skF_5'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_863, c_868])).
% 13.97/5.45  tff(c_878, plain, (~v5_relat_1(k2_funct_1('#skF_5'), '#skF_2')), inference(splitLeft, [status(thm)], [c_876])).
% 13.97/5.45  tff(c_1154, plain, (![A_158, B_159, E_160]: (k1_partfun1(A_158, B_159, '#skF_2', '#skF_3', E_160, '#skF_5')=k5_relat_1(E_160, '#skF_5') | ~m1_subset_1(E_160, k1_zfmisc_1(k2_zfmisc_1(A_158, B_159))) | ~v1_funct_1(E_160))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_783])).
% 13.97/5.45  tff(c_1163, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_3', '#skF_4', '#skF_5')=k5_relat_1('#skF_4', '#skF_5') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_74, c_1154])).
% 13.97/5.45  tff(c_1173, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_3', '#skF_4', '#skF_5')=k5_relat_1('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_1163])).
% 13.97/5.45  tff(c_1240, plain, (k2_relset_1('#skF_1', '#skF_3', k5_relat_1('#skF_4', '#skF_5'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1173, c_66])).
% 13.97/5.45  tff(c_1244, plain, (m1_subset_1(k5_relat_1('#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3'))) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1173, c_54])).
% 13.97/5.45  tff(c_1248, plain, (m1_subset_1(k5_relat_1('#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_74, c_72, c_68, c_1244])).
% 13.97/5.45  tff(c_1340, plain, (k2_relset_1('#skF_1', '#skF_3', k5_relat_1('#skF_4', '#skF_5'))=k2_relat_1(k5_relat_1('#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_1248, c_40])).
% 13.97/5.45  tff(c_1376, plain, (k2_relat_1(k5_relat_1('#skF_4', '#skF_5'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1240, c_1340])).
% 13.97/5.45  tff(c_1397, plain, (r1_tarski('#skF_3', k2_relat_1('#skF_5')) | ~v1_relat_1('#skF_5') | ~v1_relat_1('#skF_5') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1376, c_200])).
% 13.97/5.45  tff(c_1438, plain, (r1_tarski('#skF_3', k2_relat_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_102, c_103, c_103, c_1397])).
% 13.97/5.45  tff(c_1462, plain, (k2_relat_1('#skF_5')='#skF_3' | ~v5_relat_1('#skF_5', '#skF_3') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_1438, c_121])).
% 13.97/5.45  tff(c_1470, plain, (k2_relat_1('#skF_5')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_103, c_135, c_1462])).
% 13.97/5.45  tff(c_1526, plain, (k10_relat_1('#skF_5', '#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_1470, c_796])).
% 13.97/5.45  tff(c_22, plain, (![A_13]: (v1_funct_1(k2_funct_1(A_13)) | ~v2_funct_1(A_13) | ~v1_funct_1(A_13) | ~v1_relat_1(A_13))), inference(cnfTransformation, [status(thm)], [f_68])).
% 13.97/5.45  tff(c_303, plain, (![B_98, A_99]: (k9_relat_1(B_98, k10_relat_1(B_98, A_99))=A_99 | ~r1_tarski(A_99, k2_relat_1(B_98)) | ~v1_funct_1(B_98) | ~v1_relat_1(B_98))), inference(cnfTransformation, [status(thm)], [f_76])).
% 13.97/5.45  tff(c_318, plain, (![B_100]: (k9_relat_1(B_100, k10_relat_1(B_100, k2_relat_1(B_100)))=k2_relat_1(B_100) | ~v1_funct_1(B_100) | ~v1_relat_1(B_100))), inference(resolution, [status(thm)], [c_6, c_303])).
% 13.97/5.45  tff(c_355, plain, (![A_103]: (k9_relat_1(A_103, k1_relat_1(A_103))=k2_relat_1(A_103) | ~v1_funct_1(A_103) | ~v1_relat_1(A_103) | ~v1_relat_1(A_103))), inference(superposition, [status(thm), theory('equality')], [c_18, c_318])).
% 13.97/5.45  tff(c_112, plain, (![B_6, A_5]: (k9_relat_1(B_6, A_5)=k2_relat_1(B_6) | ~r1_tarski(k2_relat_1(B_6), k9_relat_1(B_6, A_5)) | ~v1_relat_1(B_6))), inference(resolution, [status(thm)], [c_12, c_105])).
% 13.97/5.45  tff(c_361, plain, (![A_103]: (k9_relat_1(A_103, k1_relat_1(A_103))=k2_relat_1(A_103) | ~r1_tarski(k2_relat_1(A_103), k2_relat_1(A_103)) | ~v1_relat_1(A_103) | ~v1_funct_1(A_103) | ~v1_relat_1(A_103) | ~v1_relat_1(A_103))), inference(superposition, [status(thm), theory('equality')], [c_355, c_112])).
% 13.97/5.45  tff(c_381, plain, (![A_103]: (k9_relat_1(A_103, k1_relat_1(A_103))=k2_relat_1(A_103) | ~v1_funct_1(A_103) | ~v1_relat_1(A_103))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_361])).
% 13.97/5.45  tff(c_540, plain, (k9_relat_1('#skF_5', '#skF_2')=k2_relat_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_535, c_381])).
% 13.97/5.45  tff(c_550, plain, (k9_relat_1('#skF_5', '#skF_2')=k2_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_103, c_72, c_540])).
% 13.97/5.45  tff(c_249, plain, (![B_88, A_89]: (k10_relat_1(k2_funct_1(B_88), A_89)=k9_relat_1(B_88, A_89) | ~v2_funct_1(B_88) | ~v1_funct_1(B_88) | ~v1_relat_1(B_88))), inference(cnfTransformation, [status(thm)], [f_84])).
% 13.97/5.45  tff(c_255, plain, (![B_88, A_89]: (r1_tarski(k9_relat_1(B_88, A_89), k1_relat_1(k2_funct_1(B_88))) | ~v1_relat_1(k2_funct_1(B_88)) | ~v2_funct_1(B_88) | ~v1_funct_1(B_88) | ~v1_relat_1(B_88))), inference(superposition, [status(thm), theory('equality')], [c_249, c_16])).
% 13.97/5.45  tff(c_619, plain, (r1_tarski(k2_relat_1('#skF_5'), k1_relat_1(k2_funct_1('#skF_5'))) | ~v1_relat_1(k2_funct_1('#skF_5')) | ~v2_funct_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_550, c_255])).
% 13.97/5.45  tff(c_635, plain, (r1_tarski(k2_relat_1('#skF_5'), k1_relat_1(k2_funct_1('#skF_5'))) | ~v1_relat_1(k2_funct_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_103, c_72, c_64, c_619])).
% 13.97/5.45  tff(c_1002, plain, (r1_tarski(k2_relat_1('#skF_5'), k1_relat_1(k2_funct_1('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_863, c_635])).
% 13.97/5.45  tff(c_1525, plain, (r1_tarski('#skF_3', k1_relat_1(k2_funct_1('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_1470, c_1002])).
% 13.97/5.45  tff(c_266, plain, (![B_88]: (k9_relat_1(B_88, k2_relat_1(k2_funct_1(B_88)))=k1_relat_1(k2_funct_1(B_88)) | ~v2_funct_1(B_88) | ~v1_funct_1(B_88) | ~v1_relat_1(B_88) | ~v1_relat_1(k2_funct_1(B_88)))), inference(superposition, [status(thm), theory('equality')], [c_18, c_249])).
% 13.97/5.45  tff(c_1567, plain, (![A_5]: (r1_tarski(k9_relat_1('#skF_5', A_5), '#skF_3') | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_1470, c_12])).
% 13.97/5.45  tff(c_1667, plain, (![A_165]: (r1_tarski(k9_relat_1('#skF_5', A_165), '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_103, c_1567])).
% 13.97/5.45  tff(c_1679, plain, (r1_tarski(k1_relat_1(k2_funct_1('#skF_5')), '#skF_3') | ~v2_funct_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5') | ~v1_relat_1(k2_funct_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_266, c_1667])).
% 13.97/5.45  tff(c_1701, plain, (r1_tarski(k1_relat_1(k2_funct_1('#skF_5')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_863, c_103, c_72, c_64, c_1679])).
% 13.97/5.45  tff(c_1712, plain, (k1_relat_1(k2_funct_1('#skF_5'))='#skF_3' | ~r1_tarski('#skF_3', k1_relat_1(k2_funct_1('#skF_5')))), inference(resolution, [status(thm)], [c_1701, c_2])).
% 13.97/5.45  tff(c_1715, plain, (k1_relat_1(k2_funct_1('#skF_5'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1525, c_1712])).
% 13.97/5.45  tff(c_1728, plain, (k9_relat_1(k2_funct_1('#skF_5'), '#skF_3')=k2_relat_1(k2_funct_1('#skF_5')) | ~v1_funct_1(k2_funct_1('#skF_5')) | ~v1_relat_1(k2_funct_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_1715, c_381])).
% 13.97/5.45  tff(c_1740, plain, (k9_relat_1(k2_funct_1('#skF_5'), '#skF_3')=k2_relat_1(k2_funct_1('#skF_5')) | ~v1_funct_1(k2_funct_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_863, c_1728])).
% 13.97/5.45  tff(c_2804, plain, (~v1_funct_1(k2_funct_1('#skF_5'))), inference(splitLeft, [status(thm)], [c_1740])).
% 13.97/5.45  tff(c_2807, plain, (~v2_funct_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_22, c_2804])).
% 13.97/5.45  tff(c_2811, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_103, c_72, c_64, c_2807])).
% 13.97/5.45  tff(c_2812, plain, (k9_relat_1(k2_funct_1('#skF_5'), '#skF_3')=k2_relat_1(k2_funct_1('#skF_5'))), inference(splitRight, [status(thm)], [c_1740])).
% 13.97/5.45  tff(c_30, plain, (![B_19, A_18]: (k9_relat_1(k2_funct_1(B_19), A_18)=k10_relat_1(B_19, A_18) | ~v2_funct_1(B_19) | ~v1_funct_1(B_19) | ~v1_relat_1(B_19))), inference(cnfTransformation, [status(thm)], [f_92])).
% 13.97/5.45  tff(c_2830, plain, (k2_relat_1(k2_funct_1('#skF_5'))=k10_relat_1('#skF_5', '#skF_3') | ~v2_funct_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_2812, c_30])).
% 13.97/5.45  tff(c_2848, plain, (k2_relat_1(k2_funct_1('#skF_5'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_103, c_72, c_64, c_1526, c_2830])).
% 13.97/5.45  tff(c_877, plain, (k2_relat_1(k2_funct_1('#skF_5'))='#skF_2' | ~r1_tarski(k2_relat_1(k2_funct_1('#skF_5')), '#skF_2')), inference(resolution, [status(thm)], [c_862, c_2])).
% 13.97/5.45  tff(c_1052, plain, (~r1_tarski(k2_relat_1(k2_funct_1('#skF_5')), '#skF_2')), inference(splitLeft, [status(thm)], [c_877])).
% 13.97/5.45  tff(c_2856, plain, (~r1_tarski('#skF_2', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2848, c_1052])).
% 13.97/5.45  tff(c_2861, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_2856])).
% 13.97/5.45  tff(c_2862, plain, (k2_relat_1(k2_funct_1('#skF_5'))='#skF_2'), inference(splitRight, [status(thm)], [c_877])).
% 13.97/5.45  tff(c_147, plain, (![B_70, A_71]: (v5_relat_1(B_70, A_71) | ~r1_tarski(k2_relat_1(B_70), A_71) | ~v1_relat_1(B_70))), inference(cnfTransformation, [status(thm)], [f_37])).
% 13.97/5.45  tff(c_156, plain, (![B_70]: (v5_relat_1(B_70, k2_relat_1(B_70)) | ~v1_relat_1(B_70))), inference(resolution, [status(thm)], [c_6, c_147])).
% 13.97/5.45  tff(c_2914, plain, (v5_relat_1(k2_funct_1('#skF_5'), '#skF_2') | ~v1_relat_1(k2_funct_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_2862, c_156])).
% 13.97/5.45  tff(c_2950, plain, (v5_relat_1(k2_funct_1('#skF_5'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_863, c_2914])).
% 13.97/5.45  tff(c_2952, plain, $false, inference(negUnitSimplification, [status(thm)], [c_878, c_2950])).
% 13.97/5.45  tff(c_2953, plain, (k2_relat_1(k2_funct_1('#skF_5'))='#skF_2'), inference(splitRight, [status(thm)], [c_876])).
% 13.97/5.45  tff(c_2997, plain, (k10_relat_1(k2_funct_1('#skF_5'), '#skF_2')=k1_relat_1(k2_funct_1('#skF_5')) | ~v1_relat_1(k2_funct_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_2953, c_18])).
% 13.97/5.45  tff(c_3027, plain, (k10_relat_1(k2_funct_1('#skF_5'), '#skF_2')=k1_relat_1(k2_funct_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_863, c_2997])).
% 13.97/5.45  tff(c_28, plain, (![B_17, A_16]: (k10_relat_1(k2_funct_1(B_17), A_16)=k9_relat_1(B_17, A_16) | ~v2_funct_1(B_17) | ~v1_funct_1(B_17) | ~v1_relat_1(B_17))), inference(cnfTransformation, [status(thm)], [f_84])).
% 13.97/5.45  tff(c_3140, plain, (k1_relat_1(k2_funct_1('#skF_5'))=k9_relat_1('#skF_5', '#skF_2') | ~v2_funct_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_3027, c_28])).
% 13.97/5.45  tff(c_3154, plain, (k1_relat_1(k2_funct_1('#skF_5'))=k2_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_103, c_72, c_64, c_550, c_3140])).
% 13.97/5.45  tff(c_3167, plain, (k9_relat_1(k2_funct_1('#skF_5'), k2_relat_1('#skF_5'))=k2_relat_1(k2_funct_1('#skF_5')) | ~v1_funct_1(k2_funct_1('#skF_5')) | ~v1_relat_1(k2_funct_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_3154, c_381])).
% 13.97/5.45  tff(c_3179, plain, (k9_relat_1(k2_funct_1('#skF_5'), k2_relat_1('#skF_5'))='#skF_2' | ~v1_funct_1(k2_funct_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_863, c_2953, c_3167])).
% 13.97/5.45  tff(c_3622, plain, (~v1_funct_1(k2_funct_1('#skF_5'))), inference(splitLeft, [status(thm)], [c_3179])).
% 13.97/5.45  tff(c_3625, plain, (~v2_funct_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_22, c_3622])).
% 13.97/5.45  tff(c_3629, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_103, c_72, c_64, c_3625])).
% 13.97/5.45  tff(c_3631, plain, (v1_funct_1(k2_funct_1('#skF_5'))), inference(splitRight, [status(thm)], [c_3179])).
% 13.97/5.45  tff(c_4127, plain, (![A_5]: (r1_tarski(k9_relat_1('#skF_5', A_5), '#skF_3') | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_4078, c_12])).
% 13.97/5.45  tff(c_4158, plain, (![A_5]: (r1_tarski(k9_relat_1('#skF_5', A_5), '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_103, c_4127])).
% 13.97/5.45  tff(c_3164, plain, (![A_89]: (r1_tarski(k9_relat_1('#skF_5', A_89), k2_relat_1('#skF_5')) | ~v1_relat_1(k2_funct_1('#skF_5')) | ~v2_funct_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_3154, c_255])).
% 13.97/5.45  tff(c_3232, plain, (![A_250]: (r1_tarski(k9_relat_1('#skF_5', A_250), k2_relat_1('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_103, c_72, c_64, c_863, c_3164])).
% 13.97/5.45  tff(c_26, plain, (![B_15, A_14]: (k9_relat_1(B_15, k10_relat_1(B_15, A_14))=A_14 | ~r1_tarski(A_14, k2_relat_1(B_15)) | ~v1_funct_1(B_15) | ~v1_relat_1(B_15))), inference(cnfTransformation, [status(thm)], [f_76])).
% 13.97/5.45  tff(c_3234, plain, (![A_250]: (k9_relat_1('#skF_5', k10_relat_1('#skF_5', k9_relat_1('#skF_5', A_250)))=k9_relat_1('#skF_5', A_250) | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5'))), inference(resolution, [status(thm)], [c_3232, c_26])).
% 13.97/5.45  tff(c_3260, plain, (![A_250]: (k9_relat_1('#skF_5', k10_relat_1('#skF_5', k9_relat_1('#skF_5', A_250)))=k9_relat_1('#skF_5', A_250))), inference(demodulation, [status(thm), theory('equality')], [c_103, c_72, c_3234])).
% 13.97/5.45  tff(c_3173, plain, (![A_10]: (r1_tarski(k10_relat_1(k2_funct_1('#skF_5'), A_10), k2_relat_1('#skF_5')) | ~v1_relat_1(k2_funct_1('#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_3154, c_16])).
% 13.97/5.45  tff(c_3292, plain, (![A_252]: (r1_tarski(k10_relat_1(k2_funct_1('#skF_5'), A_252), k2_relat_1('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_863, c_3173])).
% 13.97/5.45  tff(c_3294, plain, (![A_252]: (k9_relat_1('#skF_5', k10_relat_1('#skF_5', k10_relat_1(k2_funct_1('#skF_5'), A_252)))=k10_relat_1(k2_funct_1('#skF_5'), A_252) | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5'))), inference(resolution, [status(thm)], [c_3292, c_26])).
% 13.97/5.45  tff(c_6631, plain, (![A_404]: (k9_relat_1('#skF_5', k10_relat_1('#skF_5', k10_relat_1(k2_funct_1('#skF_5'), A_404)))=k10_relat_1(k2_funct_1('#skF_5'), A_404))), inference(demodulation, [status(thm), theory('equality')], [c_103, c_72, c_3294])).
% 13.97/5.45  tff(c_6694, plain, (![A_16]: (k9_relat_1('#skF_5', k10_relat_1('#skF_5', k9_relat_1('#skF_5', A_16)))=k10_relat_1(k2_funct_1('#skF_5'), A_16) | ~v2_funct_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_28, c_6631])).
% 13.97/5.45  tff(c_6731, plain, (![A_16]: (k10_relat_1(k2_funct_1('#skF_5'), A_16)=k9_relat_1('#skF_5', A_16))), inference(demodulation, [status(thm), theory('equality')], [c_103, c_72, c_64, c_3260, c_6694])).
% 13.97/5.45  tff(c_10, plain, (![B_4, A_3]: (r1_tarski(k2_relat_1(B_4), A_3) | ~v5_relat_1(B_4, A_3) | ~v1_relat_1(B_4))), inference(cnfTransformation, [status(thm)], [f_37])).
% 13.97/5.45  tff(c_315, plain, (![B_98, B_4]: (k9_relat_1(B_98, k10_relat_1(B_98, k2_relat_1(B_4)))=k2_relat_1(B_4) | ~v1_funct_1(B_98) | ~v1_relat_1(B_98) | ~v5_relat_1(B_4, k2_relat_1(B_98)) | ~v1_relat_1(B_4))), inference(resolution, [status(thm)], [c_10, c_303])).
% 13.97/5.45  tff(c_4103, plain, (![A_14]: (k9_relat_1('#skF_5', k10_relat_1('#skF_5', A_14))=A_14 | ~r1_tarski(A_14, '#skF_3') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_4078, c_26])).
% 13.97/5.45  tff(c_4142, plain, (![A_14]: (k9_relat_1('#skF_5', k10_relat_1('#skF_5', A_14))=A_14 | ~r1_tarski(A_14, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_103, c_72, c_4103])).
% 13.97/5.45  tff(c_6742, plain, (![A_405]: (k10_relat_1(k2_funct_1('#skF_5'), A_405)=k9_relat_1('#skF_5', A_405))), inference(demodulation, [status(thm), theory('equality')], [c_103, c_72, c_64, c_3260, c_6694])).
% 13.97/5.45  tff(c_316, plain, (![B_6, A_5]: (k9_relat_1(B_6, k10_relat_1(B_6, k9_relat_1(B_6, A_5)))=k9_relat_1(B_6, A_5) | ~v1_funct_1(B_6) | ~v1_relat_1(B_6))), inference(resolution, [status(thm)], [c_12, c_303])).
% 13.97/5.45  tff(c_6759, plain, (![A_5]: (k9_relat_1(k2_funct_1('#skF_5'), k9_relat_1('#skF_5', k9_relat_1(k2_funct_1('#skF_5'), A_5)))=k9_relat_1(k2_funct_1('#skF_5'), A_5) | ~v1_funct_1(k2_funct_1('#skF_5')) | ~v1_relat_1(k2_funct_1('#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_6742, c_316])).
% 13.97/5.45  tff(c_22381, plain, (![A_809]: (k9_relat_1(k2_funct_1('#skF_5'), k9_relat_1('#skF_5', k9_relat_1(k2_funct_1('#skF_5'), A_809)))=k9_relat_1(k2_funct_1('#skF_5'), A_809))), inference(demodulation, [status(thm), theory('equality')], [c_863, c_3631, c_6759])).
% 13.97/5.45  tff(c_22412, plain, (![A_809]: (k10_relat_1('#skF_5', k9_relat_1('#skF_5', k9_relat_1(k2_funct_1('#skF_5'), A_809)))=k9_relat_1(k2_funct_1('#skF_5'), A_809) | ~v2_funct_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_22381, c_30])).
% 13.97/5.45  tff(c_22589, plain, (![A_812]: (k10_relat_1('#skF_5', k9_relat_1('#skF_5', k9_relat_1(k2_funct_1('#skF_5'), A_812)))=k9_relat_1(k2_funct_1('#skF_5'), A_812))), inference(demodulation, [status(thm), theory('equality')], [c_103, c_72, c_64, c_22412])).
% 13.97/5.45  tff(c_22674, plain, (![A_18]: (k10_relat_1('#skF_5', k9_relat_1('#skF_5', k10_relat_1('#skF_5', A_18)))=k9_relat_1(k2_funct_1('#skF_5'), A_18) | ~v2_funct_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_30, c_22589])).
% 13.97/5.45  tff(c_22726, plain, (![A_813]: (k10_relat_1('#skF_5', k9_relat_1('#skF_5', k10_relat_1('#skF_5', A_813)))=k9_relat_1(k2_funct_1('#skF_5'), A_813))), inference(demodulation, [status(thm), theory('equality')], [c_103, c_72, c_64, c_22674])).
% 13.97/5.45  tff(c_22862, plain, (![A_814]: (k9_relat_1(k2_funct_1('#skF_5'), A_814)=k10_relat_1('#skF_5', A_814) | ~r1_tarski(A_814, '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_4142, c_22726])).
% 13.97/5.45  tff(c_22969, plain, (![B_4]: (k10_relat_1('#skF_5', k10_relat_1(k2_funct_1('#skF_5'), k2_relat_1(B_4)))=k2_relat_1(B_4) | ~r1_tarski(k10_relat_1(k2_funct_1('#skF_5'), k2_relat_1(B_4)), '#skF_3') | ~v1_funct_1(k2_funct_1('#skF_5')) | ~v1_relat_1(k2_funct_1('#skF_5')) | ~v5_relat_1(B_4, k2_relat_1(k2_funct_1('#skF_5'))) | ~v1_relat_1(B_4))), inference(superposition, [status(thm), theory('equality')], [c_315, c_22862])).
% 13.97/5.45  tff(c_25144, plain, (![B_840]: (k10_relat_1('#skF_5', k9_relat_1('#skF_5', k2_relat_1(B_840)))=k2_relat_1(B_840) | ~v5_relat_1(B_840, '#skF_2') | ~v1_relat_1(B_840))), inference(demodulation, [status(thm), theory('equality')], [c_2953, c_863, c_3631, c_4158, c_6731, c_6731, c_22969])).
% 13.97/5.45  tff(c_25218, plain, (k10_relat_1('#skF_5', '#skF_3')=k2_relat_1('#skF_4') | ~v5_relat_1('#skF_4', '#skF_2') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_7682, c_25144])).
% 13.97/5.45  tff(c_25288, plain, (k2_relat_1('#skF_4')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_102, c_134, c_4086, c_25218])).
% 13.97/5.45  tff(c_25290, plain, $false, inference(negUnitSimplification, [status(thm)], [c_167, c_25288])).
% 13.97/5.45  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 13.97/5.45  
% 13.97/5.45  Inference rules
% 13.97/5.45  ----------------------
% 13.97/5.45  #Ref     : 0
% 13.97/5.45  #Sup     : 5299
% 13.97/5.45  #Fact    : 0
% 13.97/5.45  #Define  : 0
% 13.97/5.45  #Split   : 37
% 13.97/5.45  #Chain   : 0
% 13.97/5.45  #Close   : 0
% 13.97/5.45  
% 13.97/5.45  Ordering : KBO
% 13.97/5.45  
% 13.97/5.45  Simplification rules
% 13.97/5.45  ----------------------
% 13.97/5.45  #Subsume      : 835
% 13.97/5.45  #Demod        : 12600
% 13.97/5.45  #Tautology    : 2194
% 13.97/5.45  #SimpNegUnit  : 84
% 13.97/5.45  #BackRed      : 537
% 13.97/5.45  
% 13.97/5.45  #Partial instantiations: 0
% 13.97/5.45  #Strategies tried      : 1
% 13.97/5.45  
% 13.97/5.45  Timing (in seconds)
% 13.97/5.45  ----------------------
% 13.97/5.45  Preprocessing        : 0.37
% 13.97/5.45  Parsing              : 0.19
% 13.97/5.45  CNF conversion       : 0.03
% 13.97/5.45  Main loop            : 4.27
% 13.97/5.45  Inferencing          : 1.07
% 13.97/5.45  Reduction            : 2.00
% 13.97/5.45  Demodulation         : 1.60
% 13.97/5.45  BG Simplification    : 0.10
% 13.97/5.45  Subsumption          : 0.80
% 13.97/5.45  Abstraction          : 0.14
% 13.97/5.45  MUC search           : 0.00
% 13.97/5.45  Cooper               : 0.00
% 13.97/5.45  Total                : 4.71
% 13.97/5.45  Index Insertion      : 0.00
% 13.97/5.45  Index Deletion       : 0.00
% 13.97/5.45  Index Matching       : 0.00
% 13.97/5.45  BG Taut test         : 0.00
%------------------------------------------------------------------------------
