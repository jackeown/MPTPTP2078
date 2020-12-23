%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:11:59 EST 2020

% Result     : Theorem 4.60s
% Output     : CNFRefutation 4.77s
% Verified   : 
% Statistics : Number of formulae       :  111 ( 200 expanded)
%              Number of leaves         :   42 (  88 expanded)
%              Depth                    :   11
%              Number of atoms          :  184 ( 616 expanded)
%              Number of equality atoms :   64 ( 193 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k4_relset_1 > k1_partfun1 > k8_relset_1 > k7_relset_1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k5_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff(v2_funct_1,type,(
    v2_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k8_relset_1,type,(
    k8_relset_1: ( $i * $i * $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(k4_relset_1,type,(
    k4_relset_1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k7_relset_1,type,(
    k7_relset_1: ( $i * $i * $i * $i ) > $i )).

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_134,negated_conjecture,(
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

tff(f_68,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_50,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_54,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k2_relset_1(A,B,C),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_relset_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_64,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_102,axiom,(
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

tff(f_78,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k8_relset_1(A,B,C,D) = k10_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

tff(f_84,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( k7_relset_1(A,B,C,A) = k2_relset_1(A,B,C)
        & k8_relset_1(A,B,C,B) = k1_relset_1(A,B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_relset_1)).

tff(f_112,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_74,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k4_relset_1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_relset_1)).

tff(f_60,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => m1_subset_1(k4_relset_1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_relset_1)).

tff(f_36,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k2_relat_1(k5_relat_1(A,B)) = k9_relat_1(B,k2_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t160_relat_1)).

tff(f_46,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( ( r1_tarski(A,k1_relat_1(B))
          & v2_funct_1(B) )
       => k10_relat_1(B,k9_relat_1(B,A)) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t164_funct_1)).

tff(c_56,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_137,plain,(
    ! [A_65,B_66,C_67] :
      ( k2_relset_1(A_65,B_66,C_67) = k2_relat_1(C_67)
      | ~ m1_subset_1(C_67,k1_zfmisc_1(k2_zfmisc_1(A_65,B_66))) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_150,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_56,c_137])).

tff(c_42,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_4') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_155,plain,(
    k2_relat_1('#skF_4') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_150,c_42])).

tff(c_79,plain,(
    ! [C_53,A_54,B_55] :
      ( v1_relat_1(C_53)
      | ~ m1_subset_1(C_53,k1_zfmisc_1(k2_zfmisc_1(A_54,B_55))) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_92,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_56,c_79])).

tff(c_186,plain,(
    ! [A_75,B_76,C_77] :
      ( m1_subset_1(k2_relset_1(A_75,B_76,C_77),k1_zfmisc_1(B_76))
      | ~ m1_subset_1(C_77,k1_zfmisc_1(k2_zfmisc_1(A_75,B_76))) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_204,plain,
    ( m1_subset_1(k2_relat_1('#skF_4'),k1_zfmisc_1('#skF_2'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_150,c_186])).

tff(c_216,plain,(
    m1_subset_1(k2_relat_1('#skF_4'),k1_zfmisc_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_204])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( r1_tarski(A_1,B_2)
      | ~ m1_subset_1(A_1,k1_zfmisc_1(B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_222,plain,(
    r1_tarski(k2_relat_1('#skF_4'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_216,c_2])).

tff(c_44,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_52,plain,(
    v1_funct_2('#skF_5','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_50,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_93,plain,(
    ! [A_56,B_57,C_58] :
      ( k1_relset_1(A_56,B_57,C_58) = k1_relat_1(C_58)
      | ~ m1_subset_1(C_58,k1_zfmisc_1(k2_zfmisc_1(A_56,B_57))) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_105,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_50,c_93])).

tff(c_1482,plain,(
    ! [B_210,A_211,C_212] :
      ( k1_xboole_0 = B_210
      | k1_relset_1(A_211,B_210,C_212) = A_211
      | ~ v1_funct_2(C_212,A_211,B_210)
      | ~ m1_subset_1(C_212,k1_zfmisc_1(k2_zfmisc_1(A_211,B_210))) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_1496,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relset_1('#skF_2','#skF_3','#skF_5') = '#skF_2'
    | ~ v1_funct_2('#skF_5','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_50,c_1482])).

tff(c_1507,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relat_1('#skF_5') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_105,c_1496])).

tff(c_1508,plain,(
    k1_relat_1('#skF_5') = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_1507])).

tff(c_227,plain,(
    ! [A_78,B_79,C_80,D_81] :
      ( k8_relset_1(A_78,B_79,C_80,D_81) = k10_relat_1(C_80,D_81)
      | ~ m1_subset_1(C_80,k1_zfmisc_1(k2_zfmisc_1(A_78,B_79))) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_240,plain,(
    ! [D_81] : k8_relset_1('#skF_2','#skF_3','#skF_5',D_81) = k10_relat_1('#skF_5',D_81) ),
    inference(resolution,[status(thm)],[c_50,c_227])).

tff(c_1324,plain,(
    ! [A_183,B_184,C_185] :
      ( k8_relset_1(A_183,B_184,C_185,B_184) = k1_relset_1(A_183,B_184,C_185)
      | ~ m1_subset_1(C_185,k1_zfmisc_1(k2_zfmisc_1(A_183,B_184))) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_1334,plain,(
    k8_relset_1('#skF_2','#skF_3','#skF_5','#skF_3') = k1_relset_1('#skF_2','#skF_3','#skF_5') ),
    inference(resolution,[status(thm)],[c_50,c_1324])).

tff(c_1342,plain,(
    k10_relat_1('#skF_5','#skF_3') = k1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_105,c_240,c_1334])).

tff(c_1512,plain,(
    k10_relat_1('#skF_5','#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1508,c_1342])).

tff(c_60,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_54,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_2100,plain,(
    ! [B_250,D_249,C_253,E_248,A_251,F_252] :
      ( k1_partfun1(A_251,B_250,C_253,D_249,E_248,F_252) = k5_relat_1(E_248,F_252)
      | ~ m1_subset_1(F_252,k1_zfmisc_1(k2_zfmisc_1(C_253,D_249)))
      | ~ v1_funct_1(F_252)
      | ~ m1_subset_1(E_248,k1_zfmisc_1(k2_zfmisc_1(A_251,B_250)))
      | ~ v1_funct_1(E_248) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_2118,plain,(
    ! [A_251,B_250,E_248] :
      ( k1_partfun1(A_251,B_250,'#skF_2','#skF_3',E_248,'#skF_5') = k5_relat_1(E_248,'#skF_5')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1(E_248,k1_zfmisc_1(k2_zfmisc_1(A_251,B_250)))
      | ~ v1_funct_1(E_248) ) ),
    inference(resolution,[status(thm)],[c_50,c_2100])).

tff(c_2348,plain,(
    ! [A_257,B_258,E_259] :
      ( k1_partfun1(A_257,B_258,'#skF_2','#skF_3',E_259,'#skF_5') = k5_relat_1(E_259,'#skF_5')
      | ~ m1_subset_1(E_259,k1_zfmisc_1(k2_zfmisc_1(A_257,B_258)))
      | ~ v1_funct_1(E_259) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_2118])).

tff(c_2380,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_3','#skF_4','#skF_5') = k5_relat_1('#skF_4','#skF_5')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_56,c_2348])).

tff(c_2394,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_3','#skF_4','#skF_5') = k5_relat_1('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_2380])).

tff(c_48,plain,(
    k2_relset_1('#skF_1','#skF_3',k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_3','#skF_4','#skF_5')) = '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_536,plain,(
    ! [D_137,A_139,C_141,B_138,E_142,F_140] :
      ( k4_relset_1(A_139,B_138,C_141,D_137,E_142,F_140) = k5_relat_1(E_142,F_140)
      | ~ m1_subset_1(F_140,k1_zfmisc_1(k2_zfmisc_1(C_141,D_137)))
      | ~ m1_subset_1(E_142,k1_zfmisc_1(k2_zfmisc_1(A_139,B_138))) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_885,plain,(
    ! [A_159,B_160,E_161] :
      ( k4_relset_1(A_159,B_160,'#skF_2','#skF_3',E_161,'#skF_5') = k5_relat_1(E_161,'#skF_5')
      | ~ m1_subset_1(E_161,k1_zfmisc_1(k2_zfmisc_1(A_159,B_160))) ) ),
    inference(resolution,[status(thm)],[c_50,c_536])).

tff(c_915,plain,(
    k4_relset_1('#skF_1','#skF_2','#skF_2','#skF_3','#skF_4','#skF_5') = k5_relat_1('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_56,c_885])).

tff(c_14,plain,(
    ! [E_18,C_16,D_17,F_19,A_14,B_15] :
      ( m1_subset_1(k4_relset_1(A_14,B_15,C_16,D_17,E_18,F_19),k1_zfmisc_1(k2_zfmisc_1(A_14,D_17)))
      | ~ m1_subset_1(F_19,k1_zfmisc_1(k2_zfmisc_1(C_16,D_17)))
      | ~ m1_subset_1(E_18,k1_zfmisc_1(k2_zfmisc_1(A_14,B_15))) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_1049,plain,
    ( m1_subset_1(k5_relat_1('#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3')))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_915,c_14])).

tff(c_1053,plain,(
    m1_subset_1(k5_relat_1('#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_50,c_1049])).

tff(c_1109,plain,(
    r1_tarski(k5_relat_1('#skF_4','#skF_5'),k2_zfmisc_1('#skF_1','#skF_3')) ),
    inference(resolution,[status(thm)],[c_1053,c_2])).

tff(c_842,plain,(
    ! [C_158,B_155,A_156,F_157,E_153,D_154] :
      ( k1_partfun1(A_156,B_155,C_158,D_154,E_153,F_157) = k5_relat_1(E_153,F_157)
      | ~ m1_subset_1(F_157,k1_zfmisc_1(k2_zfmisc_1(C_158,D_154)))
      | ~ v1_funct_1(F_157)
      | ~ m1_subset_1(E_153,k1_zfmisc_1(k2_zfmisc_1(A_156,B_155)))
      | ~ v1_funct_1(E_153) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_856,plain,(
    ! [A_156,B_155,E_153] :
      ( k1_partfun1(A_156,B_155,'#skF_2','#skF_3',E_153,'#skF_5') = k5_relat_1(E_153,'#skF_5')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1(E_153,k1_zfmisc_1(k2_zfmisc_1(A_156,B_155)))
      | ~ v1_funct_1(E_153) ) ),
    inference(resolution,[status(thm)],[c_50,c_842])).

tff(c_1144,plain,(
    ! [A_165,B_166,E_167] :
      ( k1_partfun1(A_165,B_166,'#skF_2','#skF_3',E_167,'#skF_5') = k5_relat_1(E_167,'#skF_5')
      | ~ m1_subset_1(E_167,k1_zfmisc_1(k2_zfmisc_1(A_165,B_166)))
      | ~ v1_funct_1(E_167) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_856])).

tff(c_1173,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_3','#skF_4','#skF_5') = k5_relat_1('#skF_4','#skF_5')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_56,c_1144])).

tff(c_1186,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_3','#skF_4','#skF_5') = k5_relat_1('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_1173])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( m1_subset_1(A_1,k1_zfmisc_1(B_2))
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_210,plain,
    ( m1_subset_1('#skF_3',k1_zfmisc_1('#skF_3'))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_3','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_186])).

tff(c_277,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_3','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_210])).

tff(c_310,plain,(
    ~ r1_tarski(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_3','#skF_4','#skF_5'),k2_zfmisc_1('#skF_1','#skF_3')) ),
    inference(resolution,[status(thm)],[c_4,c_277])).

tff(c_1191,plain,(
    ~ r1_tarski(k5_relat_1('#skF_4','#skF_5'),k2_zfmisc_1('#skF_1','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1186,c_310])).

tff(c_1196,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1109,c_1191])).

tff(c_1198,plain,(
    m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_3','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_210])).

tff(c_18,plain,(
    ! [A_23,B_24,C_25] :
      ( k2_relset_1(A_23,B_24,C_25) = k2_relat_1(C_25)
      | ~ m1_subset_1(C_25,k1_zfmisc_1(k2_zfmisc_1(A_23,B_24))) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_1209,plain,(
    k2_relset_1('#skF_1','#skF_3',k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_3','#skF_4','#skF_5')) = k2_relat_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_3','#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_1198,c_18])).

tff(c_1223,plain,(
    k2_relat_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_3','#skF_4','#skF_5')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_1209])).

tff(c_2410,plain,(
    k2_relat_1(k5_relat_1('#skF_4','#skF_5')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2394,c_1223])).

tff(c_91,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_50,c_79])).

tff(c_6,plain,(
    ! [B_5,A_3] :
      ( k9_relat_1(B_5,k2_relat_1(A_3)) = k2_relat_1(k5_relat_1(A_3,B_5))
      | ~ v1_relat_1(B_5)
      | ~ v1_relat_1(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_46,plain,(
    v2_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_8,plain,(
    ! [B_7,A_6] :
      ( k10_relat_1(B_7,k9_relat_1(B_7,A_6)) = A_6
      | ~ v2_funct_1(B_7)
      | ~ r1_tarski(A_6,k1_relat_1(B_7))
      | ~ v1_funct_1(B_7)
      | ~ v1_relat_1(B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_1516,plain,(
    ! [A_6] :
      ( k10_relat_1('#skF_5',k9_relat_1('#skF_5',A_6)) = A_6
      | ~ v2_funct_1('#skF_5')
      | ~ r1_tarski(A_6,'#skF_2')
      | ~ v1_funct_1('#skF_5')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1508,c_8])).

tff(c_1579,plain,(
    ! [A_216] :
      ( k10_relat_1('#skF_5',k9_relat_1('#skF_5',A_216)) = A_216
      | ~ r1_tarski(A_216,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_91,c_54,c_46,c_1516])).

tff(c_1589,plain,(
    ! [A_3] :
      ( k10_relat_1('#skF_5',k2_relat_1(k5_relat_1(A_3,'#skF_5'))) = k2_relat_1(A_3)
      | ~ r1_tarski(k2_relat_1(A_3),'#skF_2')
      | ~ v1_relat_1('#skF_5')
      | ~ v1_relat_1(A_3) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_1579])).

tff(c_1593,plain,(
    ! [A_3] :
      ( k10_relat_1('#skF_5',k2_relat_1(k5_relat_1(A_3,'#skF_5'))) = k2_relat_1(A_3)
      | ~ r1_tarski(k2_relat_1(A_3),'#skF_2')
      | ~ v1_relat_1(A_3) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_91,c_1589])).

tff(c_2440,plain,
    ( k10_relat_1('#skF_5','#skF_3') = k2_relat_1('#skF_4')
    | ~ r1_tarski(k2_relat_1('#skF_4'),'#skF_2')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_2410,c_1593])).

tff(c_2447,plain,(
    k2_relat_1('#skF_4') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_222,c_1512,c_2440])).

tff(c_2449,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_155,c_2447])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:02:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.60/1.80  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.60/1.81  
% 4.60/1.81  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.60/1.81  %$ v1_funct_2 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k4_relset_1 > k1_partfun1 > k8_relset_1 > k7_relset_1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k5_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 4.60/1.81  
% 4.60/1.81  %Foreground sorts:
% 4.60/1.81  
% 4.60/1.81  
% 4.60/1.81  %Background operators:
% 4.60/1.81  
% 4.60/1.81  
% 4.60/1.81  %Foreground operators:
% 4.60/1.81  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 4.60/1.81  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.60/1.81  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 4.60/1.81  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.60/1.81  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 4.60/1.81  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.60/1.81  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 4.60/1.81  tff(k4_relset_1, type, k4_relset_1: ($i * $i * $i * $i * $i * $i) > $i).
% 4.60/1.81  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.60/1.81  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 4.60/1.81  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 4.60/1.81  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 4.60/1.81  tff('#skF_5', type, '#skF_5': $i).
% 4.60/1.81  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.60/1.81  tff('#skF_2', type, '#skF_2': $i).
% 4.60/1.81  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 4.60/1.81  tff('#skF_3', type, '#skF_3': $i).
% 4.60/1.81  tff('#skF_1', type, '#skF_1': $i).
% 4.60/1.81  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 4.60/1.81  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.60/1.81  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.60/1.81  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 4.60/1.81  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.60/1.81  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.60/1.81  tff('#skF_4', type, '#skF_4': $i).
% 4.60/1.81  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.60/1.81  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.60/1.81  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.60/1.81  
% 4.77/1.83  tff(f_134, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, B, C)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (((k2_relset_1(A, C, k1_partfun1(A, B, B, C, D, E)) = C) & v2_funct_1(E)) => ((C = k1_xboole_0) | (k2_relset_1(A, B, D) = B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_funct_2)).
% 4.77/1.83  tff(f_68, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 4.77/1.83  tff(f_50, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 4.77/1.83  tff(f_54, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k2_relset_1(A, B, C), k1_zfmisc_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_relset_1)).
% 4.77/1.83  tff(f_29, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 4.77/1.83  tff(f_64, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 4.77/1.83  tff(f_102, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 4.77/1.83  tff(f_78, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k8_relset_1(A, B, C, D) = k10_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k8_relset_1)).
% 4.77/1.83  tff(f_84, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((k7_relset_1(A, B, C, A) = k2_relset_1(A, B, C)) & (k8_relset_1(A, B, C, B) = k1_relset_1(A, B, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_relset_1)).
% 4.77/1.83  tff(f_112, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 4.77/1.83  tff(f_74, axiom, (![A, B, C, D, E, F]: ((m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k4_relset_1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k4_relset_1)).
% 4.77/1.83  tff(f_60, axiom, (![A, B, C, D, E, F]: ((m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => m1_subset_1(k4_relset_1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k4_relset_1)).
% 4.77/1.83  tff(f_36, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k2_relat_1(k5_relat_1(A, B)) = k9_relat_1(B, k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t160_relat_1)).
% 4.77/1.83  tff(f_46, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((r1_tarski(A, k1_relat_1(B)) & v2_funct_1(B)) => (k10_relat_1(B, k9_relat_1(B, A)) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t164_funct_1)).
% 4.77/1.83  tff(c_56, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_134])).
% 4.77/1.83  tff(c_137, plain, (![A_65, B_66, C_67]: (k2_relset_1(A_65, B_66, C_67)=k2_relat_1(C_67) | ~m1_subset_1(C_67, k1_zfmisc_1(k2_zfmisc_1(A_65, B_66))))), inference(cnfTransformation, [status(thm)], [f_68])).
% 4.77/1.83  tff(c_150, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_56, c_137])).
% 4.77/1.83  tff(c_42, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_4')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_134])).
% 4.77/1.83  tff(c_155, plain, (k2_relat_1('#skF_4')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_150, c_42])).
% 4.77/1.83  tff(c_79, plain, (![C_53, A_54, B_55]: (v1_relat_1(C_53) | ~m1_subset_1(C_53, k1_zfmisc_1(k2_zfmisc_1(A_54, B_55))))), inference(cnfTransformation, [status(thm)], [f_50])).
% 4.77/1.83  tff(c_92, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_56, c_79])).
% 4.77/1.83  tff(c_186, plain, (![A_75, B_76, C_77]: (m1_subset_1(k2_relset_1(A_75, B_76, C_77), k1_zfmisc_1(B_76)) | ~m1_subset_1(C_77, k1_zfmisc_1(k2_zfmisc_1(A_75, B_76))))), inference(cnfTransformation, [status(thm)], [f_54])).
% 4.77/1.83  tff(c_204, plain, (m1_subset_1(k2_relat_1('#skF_4'), k1_zfmisc_1('#skF_2')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_150, c_186])).
% 4.77/1.83  tff(c_216, plain, (m1_subset_1(k2_relat_1('#skF_4'), k1_zfmisc_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_204])).
% 4.77/1.83  tff(c_2, plain, (![A_1, B_2]: (r1_tarski(A_1, B_2) | ~m1_subset_1(A_1, k1_zfmisc_1(B_2)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 4.77/1.83  tff(c_222, plain, (r1_tarski(k2_relat_1('#skF_4'), '#skF_2')), inference(resolution, [status(thm)], [c_216, c_2])).
% 4.77/1.83  tff(c_44, plain, (k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_134])).
% 4.77/1.83  tff(c_52, plain, (v1_funct_2('#skF_5', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_134])).
% 4.77/1.83  tff(c_50, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_134])).
% 4.77/1.83  tff(c_93, plain, (![A_56, B_57, C_58]: (k1_relset_1(A_56, B_57, C_58)=k1_relat_1(C_58) | ~m1_subset_1(C_58, k1_zfmisc_1(k2_zfmisc_1(A_56, B_57))))), inference(cnfTransformation, [status(thm)], [f_64])).
% 4.77/1.83  tff(c_105, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_50, c_93])).
% 4.77/1.83  tff(c_1482, plain, (![B_210, A_211, C_212]: (k1_xboole_0=B_210 | k1_relset_1(A_211, B_210, C_212)=A_211 | ~v1_funct_2(C_212, A_211, B_210) | ~m1_subset_1(C_212, k1_zfmisc_1(k2_zfmisc_1(A_211, B_210))))), inference(cnfTransformation, [status(thm)], [f_102])).
% 4.77/1.83  tff(c_1496, plain, (k1_xboole_0='#skF_3' | k1_relset_1('#skF_2', '#skF_3', '#skF_5')='#skF_2' | ~v1_funct_2('#skF_5', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_50, c_1482])).
% 4.77/1.83  tff(c_1507, plain, (k1_xboole_0='#skF_3' | k1_relat_1('#skF_5')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_52, c_105, c_1496])).
% 4.77/1.83  tff(c_1508, plain, (k1_relat_1('#skF_5')='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_44, c_1507])).
% 4.77/1.83  tff(c_227, plain, (![A_78, B_79, C_80, D_81]: (k8_relset_1(A_78, B_79, C_80, D_81)=k10_relat_1(C_80, D_81) | ~m1_subset_1(C_80, k1_zfmisc_1(k2_zfmisc_1(A_78, B_79))))), inference(cnfTransformation, [status(thm)], [f_78])).
% 4.77/1.83  tff(c_240, plain, (![D_81]: (k8_relset_1('#skF_2', '#skF_3', '#skF_5', D_81)=k10_relat_1('#skF_5', D_81))), inference(resolution, [status(thm)], [c_50, c_227])).
% 4.77/1.83  tff(c_1324, plain, (![A_183, B_184, C_185]: (k8_relset_1(A_183, B_184, C_185, B_184)=k1_relset_1(A_183, B_184, C_185) | ~m1_subset_1(C_185, k1_zfmisc_1(k2_zfmisc_1(A_183, B_184))))), inference(cnfTransformation, [status(thm)], [f_84])).
% 4.77/1.83  tff(c_1334, plain, (k8_relset_1('#skF_2', '#skF_3', '#skF_5', '#skF_3')=k1_relset_1('#skF_2', '#skF_3', '#skF_5')), inference(resolution, [status(thm)], [c_50, c_1324])).
% 4.77/1.83  tff(c_1342, plain, (k10_relat_1('#skF_5', '#skF_3')=k1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_105, c_240, c_1334])).
% 4.77/1.83  tff(c_1512, plain, (k10_relat_1('#skF_5', '#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_1508, c_1342])).
% 4.77/1.83  tff(c_60, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_134])).
% 4.77/1.83  tff(c_54, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_134])).
% 4.77/1.83  tff(c_2100, plain, (![B_250, D_249, C_253, E_248, A_251, F_252]: (k1_partfun1(A_251, B_250, C_253, D_249, E_248, F_252)=k5_relat_1(E_248, F_252) | ~m1_subset_1(F_252, k1_zfmisc_1(k2_zfmisc_1(C_253, D_249))) | ~v1_funct_1(F_252) | ~m1_subset_1(E_248, k1_zfmisc_1(k2_zfmisc_1(A_251, B_250))) | ~v1_funct_1(E_248))), inference(cnfTransformation, [status(thm)], [f_112])).
% 4.77/1.83  tff(c_2118, plain, (![A_251, B_250, E_248]: (k1_partfun1(A_251, B_250, '#skF_2', '#skF_3', E_248, '#skF_5')=k5_relat_1(E_248, '#skF_5') | ~v1_funct_1('#skF_5') | ~m1_subset_1(E_248, k1_zfmisc_1(k2_zfmisc_1(A_251, B_250))) | ~v1_funct_1(E_248))), inference(resolution, [status(thm)], [c_50, c_2100])).
% 4.77/1.83  tff(c_2348, plain, (![A_257, B_258, E_259]: (k1_partfun1(A_257, B_258, '#skF_2', '#skF_3', E_259, '#skF_5')=k5_relat_1(E_259, '#skF_5') | ~m1_subset_1(E_259, k1_zfmisc_1(k2_zfmisc_1(A_257, B_258))) | ~v1_funct_1(E_259))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_2118])).
% 4.77/1.83  tff(c_2380, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_3', '#skF_4', '#skF_5')=k5_relat_1('#skF_4', '#skF_5') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_56, c_2348])).
% 4.77/1.83  tff(c_2394, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_3', '#skF_4', '#skF_5')=k5_relat_1('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_2380])).
% 4.77/1.83  tff(c_48, plain, (k2_relset_1('#skF_1', '#skF_3', k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_3', '#skF_4', '#skF_5'))='#skF_3'), inference(cnfTransformation, [status(thm)], [f_134])).
% 4.77/1.83  tff(c_536, plain, (![D_137, A_139, C_141, B_138, E_142, F_140]: (k4_relset_1(A_139, B_138, C_141, D_137, E_142, F_140)=k5_relat_1(E_142, F_140) | ~m1_subset_1(F_140, k1_zfmisc_1(k2_zfmisc_1(C_141, D_137))) | ~m1_subset_1(E_142, k1_zfmisc_1(k2_zfmisc_1(A_139, B_138))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 4.77/1.83  tff(c_885, plain, (![A_159, B_160, E_161]: (k4_relset_1(A_159, B_160, '#skF_2', '#skF_3', E_161, '#skF_5')=k5_relat_1(E_161, '#skF_5') | ~m1_subset_1(E_161, k1_zfmisc_1(k2_zfmisc_1(A_159, B_160))))), inference(resolution, [status(thm)], [c_50, c_536])).
% 4.77/1.83  tff(c_915, plain, (k4_relset_1('#skF_1', '#skF_2', '#skF_2', '#skF_3', '#skF_4', '#skF_5')=k5_relat_1('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_56, c_885])).
% 4.77/1.83  tff(c_14, plain, (![E_18, C_16, D_17, F_19, A_14, B_15]: (m1_subset_1(k4_relset_1(A_14, B_15, C_16, D_17, E_18, F_19), k1_zfmisc_1(k2_zfmisc_1(A_14, D_17))) | ~m1_subset_1(F_19, k1_zfmisc_1(k2_zfmisc_1(C_16, D_17))) | ~m1_subset_1(E_18, k1_zfmisc_1(k2_zfmisc_1(A_14, B_15))))), inference(cnfTransformation, [status(thm)], [f_60])).
% 4.77/1.83  tff(c_1049, plain, (m1_subset_1(k5_relat_1('#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3'))) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_915, c_14])).
% 4.77/1.83  tff(c_1053, plain, (m1_subset_1(k5_relat_1('#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_50, c_1049])).
% 4.77/1.83  tff(c_1109, plain, (r1_tarski(k5_relat_1('#skF_4', '#skF_5'), k2_zfmisc_1('#skF_1', '#skF_3'))), inference(resolution, [status(thm)], [c_1053, c_2])).
% 4.77/1.83  tff(c_842, plain, (![C_158, B_155, A_156, F_157, E_153, D_154]: (k1_partfun1(A_156, B_155, C_158, D_154, E_153, F_157)=k5_relat_1(E_153, F_157) | ~m1_subset_1(F_157, k1_zfmisc_1(k2_zfmisc_1(C_158, D_154))) | ~v1_funct_1(F_157) | ~m1_subset_1(E_153, k1_zfmisc_1(k2_zfmisc_1(A_156, B_155))) | ~v1_funct_1(E_153))), inference(cnfTransformation, [status(thm)], [f_112])).
% 4.77/1.83  tff(c_856, plain, (![A_156, B_155, E_153]: (k1_partfun1(A_156, B_155, '#skF_2', '#skF_3', E_153, '#skF_5')=k5_relat_1(E_153, '#skF_5') | ~v1_funct_1('#skF_5') | ~m1_subset_1(E_153, k1_zfmisc_1(k2_zfmisc_1(A_156, B_155))) | ~v1_funct_1(E_153))), inference(resolution, [status(thm)], [c_50, c_842])).
% 4.77/1.83  tff(c_1144, plain, (![A_165, B_166, E_167]: (k1_partfun1(A_165, B_166, '#skF_2', '#skF_3', E_167, '#skF_5')=k5_relat_1(E_167, '#skF_5') | ~m1_subset_1(E_167, k1_zfmisc_1(k2_zfmisc_1(A_165, B_166))) | ~v1_funct_1(E_167))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_856])).
% 4.77/1.83  tff(c_1173, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_3', '#skF_4', '#skF_5')=k5_relat_1('#skF_4', '#skF_5') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_56, c_1144])).
% 4.77/1.83  tff(c_1186, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_3', '#skF_4', '#skF_5')=k5_relat_1('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_1173])).
% 4.77/1.83  tff(c_4, plain, (![A_1, B_2]: (m1_subset_1(A_1, k1_zfmisc_1(B_2)) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 4.77/1.83  tff(c_210, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_3')) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_3', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_48, c_186])).
% 4.77/1.83  tff(c_277, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_3', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3')))), inference(splitLeft, [status(thm)], [c_210])).
% 4.77/1.83  tff(c_310, plain, (~r1_tarski(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_3', '#skF_4', '#skF_5'), k2_zfmisc_1('#skF_1', '#skF_3'))), inference(resolution, [status(thm)], [c_4, c_277])).
% 4.77/1.83  tff(c_1191, plain, (~r1_tarski(k5_relat_1('#skF_4', '#skF_5'), k2_zfmisc_1('#skF_1', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_1186, c_310])).
% 4.77/1.83  tff(c_1196, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1109, c_1191])).
% 4.77/1.83  tff(c_1198, plain, (m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_3', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3')))), inference(splitRight, [status(thm)], [c_210])).
% 4.77/1.83  tff(c_18, plain, (![A_23, B_24, C_25]: (k2_relset_1(A_23, B_24, C_25)=k2_relat_1(C_25) | ~m1_subset_1(C_25, k1_zfmisc_1(k2_zfmisc_1(A_23, B_24))))), inference(cnfTransformation, [status(thm)], [f_68])).
% 4.77/1.83  tff(c_1209, plain, (k2_relset_1('#skF_1', '#skF_3', k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_3', '#skF_4', '#skF_5'))=k2_relat_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_3', '#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_1198, c_18])).
% 4.77/1.83  tff(c_1223, plain, (k2_relat_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_3', '#skF_4', '#skF_5'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_48, c_1209])).
% 4.77/1.83  tff(c_2410, plain, (k2_relat_1(k5_relat_1('#skF_4', '#skF_5'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_2394, c_1223])).
% 4.77/1.83  tff(c_91, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_50, c_79])).
% 4.77/1.83  tff(c_6, plain, (![B_5, A_3]: (k9_relat_1(B_5, k2_relat_1(A_3))=k2_relat_1(k5_relat_1(A_3, B_5)) | ~v1_relat_1(B_5) | ~v1_relat_1(A_3))), inference(cnfTransformation, [status(thm)], [f_36])).
% 4.77/1.83  tff(c_46, plain, (v2_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_134])).
% 4.77/1.83  tff(c_8, plain, (![B_7, A_6]: (k10_relat_1(B_7, k9_relat_1(B_7, A_6))=A_6 | ~v2_funct_1(B_7) | ~r1_tarski(A_6, k1_relat_1(B_7)) | ~v1_funct_1(B_7) | ~v1_relat_1(B_7))), inference(cnfTransformation, [status(thm)], [f_46])).
% 4.77/1.83  tff(c_1516, plain, (![A_6]: (k10_relat_1('#skF_5', k9_relat_1('#skF_5', A_6))=A_6 | ~v2_funct_1('#skF_5') | ~r1_tarski(A_6, '#skF_2') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_1508, c_8])).
% 4.77/1.83  tff(c_1579, plain, (![A_216]: (k10_relat_1('#skF_5', k9_relat_1('#skF_5', A_216))=A_216 | ~r1_tarski(A_216, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_91, c_54, c_46, c_1516])).
% 4.77/1.83  tff(c_1589, plain, (![A_3]: (k10_relat_1('#skF_5', k2_relat_1(k5_relat_1(A_3, '#skF_5')))=k2_relat_1(A_3) | ~r1_tarski(k2_relat_1(A_3), '#skF_2') | ~v1_relat_1('#skF_5') | ~v1_relat_1(A_3))), inference(superposition, [status(thm), theory('equality')], [c_6, c_1579])).
% 4.77/1.83  tff(c_1593, plain, (![A_3]: (k10_relat_1('#skF_5', k2_relat_1(k5_relat_1(A_3, '#skF_5')))=k2_relat_1(A_3) | ~r1_tarski(k2_relat_1(A_3), '#skF_2') | ~v1_relat_1(A_3))), inference(demodulation, [status(thm), theory('equality')], [c_91, c_1589])).
% 4.77/1.83  tff(c_2440, plain, (k10_relat_1('#skF_5', '#skF_3')=k2_relat_1('#skF_4') | ~r1_tarski(k2_relat_1('#skF_4'), '#skF_2') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_2410, c_1593])).
% 4.77/1.83  tff(c_2447, plain, (k2_relat_1('#skF_4')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_92, c_222, c_1512, c_2440])).
% 4.77/1.83  tff(c_2449, plain, $false, inference(negUnitSimplification, [status(thm)], [c_155, c_2447])).
% 4.77/1.83  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.77/1.83  
% 4.77/1.83  Inference rules
% 4.77/1.83  ----------------------
% 4.77/1.83  #Ref     : 0
% 4.77/1.83  #Sup     : 585
% 4.77/1.83  #Fact    : 0
% 4.77/1.83  #Define  : 0
% 4.77/1.83  #Split   : 7
% 4.77/1.83  #Chain   : 0
% 4.77/1.83  #Close   : 0
% 4.77/1.83  
% 4.77/1.83  Ordering : KBO
% 4.77/1.83  
% 4.77/1.83  Simplification rules
% 4.77/1.83  ----------------------
% 4.77/1.83  #Subsume      : 9
% 4.77/1.83  #Demod        : 207
% 4.77/1.83  #Tautology    : 172
% 4.77/1.83  #SimpNegUnit  : 31
% 4.77/1.83  #BackRed      : 25
% 4.77/1.83  
% 4.77/1.83  #Partial instantiations: 0
% 4.77/1.83  #Strategies tried      : 1
% 4.77/1.83  
% 4.77/1.83  Timing (in seconds)
% 4.77/1.83  ----------------------
% 4.77/1.83  Preprocessing        : 0.36
% 4.77/1.83  Parsing              : 0.20
% 4.77/1.84  CNF conversion       : 0.02
% 4.77/1.84  Main loop            : 0.68
% 4.77/1.84  Inferencing          : 0.25
% 4.77/1.84  Reduction            : 0.21
% 4.77/1.84  Demodulation         : 0.15
% 4.77/1.84  BG Simplification    : 0.04
% 4.77/1.84  Subsumption          : 0.11
% 4.77/1.84  Abstraction          : 0.04
% 4.77/1.84  MUC search           : 0.00
% 4.77/1.84  Cooper               : 0.00
% 4.77/1.84  Total                : 1.09
% 4.77/1.84  Index Insertion      : 0.00
% 4.77/1.84  Index Deletion       : 0.00
% 4.77/1.84  Index Matching       : 0.00
% 4.77/1.84  BG Taut test         : 0.00
%------------------------------------------------------------------------------
