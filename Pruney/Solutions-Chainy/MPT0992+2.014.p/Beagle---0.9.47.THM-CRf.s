%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:13:33 EST 2020

% Result     : Theorem 11.80s
% Output     : CNFRefutation 12.10s
% Verified   : 
% Statistics : Number of formulae       :  199 (3395 expanded)
%              Number of leaves         :   41 (1032 expanded)
%              Depth                    :   15
%              Number of atoms          :  329 (9645 expanded)
%              Number of equality atoms :   92 (3144 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_partfun1 > k1_relset_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

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

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_partfun1,type,(
    k2_partfun1: ( $i * $i * $i * $i ) > $i )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_159,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( r1_tarski(C,A)
         => ( ( B = k1_xboole_0
              & A != k1_xboole_0 )
            | ( v1_funct_1(k2_partfun1(A,B,D,C))
              & v1_funct_2(k2_partfun1(A,B,D,C),C,B)
              & m1_subset_1(k2_partfun1(A,B,D,C),k1_zfmisc_1(k2_zfmisc_1(C,B))) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_funct_2)).

tff(f_78,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_95,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_113,axiom,(
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

tff(f_65,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(A,k1_relat_1(B))
       => k1_relat_1(k7_relat_1(B,A)) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_relat_1)).

tff(f_127,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => k2_partfun1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

tff(f_121,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( v1_funct_1(k2_partfun1(A,B,C,D))
        & m1_subset_1(k2_partfun1(A,B,C,D),k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_partfun1)).

tff(f_84,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_139,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r1_tarski(k2_relat_1(B),A)
       => ( v1_funct_1(B)
          & v1_funct_2(B,k1_relat_1(B),A)
          & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B),A))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_funct_2)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_91,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => v1_xboole_0(C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc3_relset_1)).

tff(f_36,axiom,(
    ! [A,B] :
      ~ ( v1_xboole_0(A)
        & A != B
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_boole)).

tff(f_28,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_59,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_38,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_56,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).

tff(c_64,plain,(
    r1_tarski('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_66,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_95,plain,(
    ! [C_49,A_50,B_51] :
      ( v1_relat_1(C_49)
      | ~ m1_subset_1(C_49,k1_zfmisc_1(k2_zfmisc_1(A_50,B_51))) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_103,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_66,c_95])).

tff(c_62,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_83,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_62])).

tff(c_68,plain,(
    v1_funct_2('#skF_4','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_20929,plain,(
    ! [A_907,B_908,C_909] :
      ( k1_relset_1(A_907,B_908,C_909) = k1_relat_1(C_909)
      | ~ m1_subset_1(C_909,k1_zfmisc_1(k2_zfmisc_1(A_907,B_908))) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_20941,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_66,c_20929])).

tff(c_21261,plain,(
    ! [B_953,A_954,C_955] :
      ( k1_xboole_0 = B_953
      | k1_relset_1(A_954,B_953,C_955) = A_954
      | ~ v1_funct_2(C_955,A_954,B_953)
      | ~ m1_subset_1(C_955,k1_zfmisc_1(k2_zfmisc_1(A_954,B_953))) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_21270,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1('#skF_1','#skF_2','#skF_4') = '#skF_1'
    | ~ v1_funct_2('#skF_4','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_66,c_21261])).

tff(c_21280,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_20941,c_21270])).

tff(c_21281,plain,(
    k1_relat_1('#skF_4') = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_83,c_21280])).

tff(c_22,plain,(
    ! [B_13,A_12] :
      ( k1_relat_1(k7_relat_1(B_13,A_12)) = A_12
      | ~ r1_tarski(A_12,k1_relat_1(B_13))
      | ~ v1_relat_1(B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_21300,plain,(
    ! [A_12] :
      ( k1_relat_1(k7_relat_1('#skF_4',A_12)) = A_12
      | ~ r1_tarski(A_12,'#skF_1')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_21281,c_22])).

tff(c_21310,plain,(
    ! [A_12] :
      ( k1_relat_1(k7_relat_1('#skF_4',A_12)) = A_12
      | ~ r1_tarski(A_12,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_103,c_21300])).

tff(c_70,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_21152,plain,(
    ! [A_943,B_944,C_945,D_946] :
      ( k2_partfun1(A_943,B_944,C_945,D_946) = k7_relat_1(C_945,D_946)
      | ~ m1_subset_1(C_945,k1_zfmisc_1(k2_zfmisc_1(A_943,B_944)))
      | ~ v1_funct_1(C_945) ) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_21158,plain,(
    ! [D_946] :
      ( k2_partfun1('#skF_1','#skF_2','#skF_4',D_946) = k7_relat_1('#skF_4',D_946)
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_66,c_21152])).

tff(c_21168,plain,(
    ! [D_946] : k2_partfun1('#skF_1','#skF_2','#skF_4',D_946) = k7_relat_1('#skF_4',D_946) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_21158])).

tff(c_622,plain,(
    ! [A_155,B_156,C_157,D_158] :
      ( k2_partfun1(A_155,B_156,C_157,D_158) = k7_relat_1(C_157,D_158)
      | ~ m1_subset_1(C_157,k1_zfmisc_1(k2_zfmisc_1(A_155,B_156)))
      | ~ v1_funct_1(C_157) ) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_626,plain,(
    ! [D_158] :
      ( k2_partfun1('#skF_1','#skF_2','#skF_4',D_158) = k7_relat_1('#skF_4',D_158)
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_66,c_622])).

tff(c_633,plain,(
    ! [D_158] : k2_partfun1('#skF_1','#skF_2','#skF_4',D_158) = k7_relat_1('#skF_4',D_158) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_626])).

tff(c_996,plain,(
    ! [A_190,B_191,C_192,D_193] :
      ( m1_subset_1(k2_partfun1(A_190,B_191,C_192,D_193),k1_zfmisc_1(k2_zfmisc_1(A_190,B_191)))
      | ~ m1_subset_1(C_192,k1_zfmisc_1(k2_zfmisc_1(A_190,B_191)))
      | ~ v1_funct_1(C_192) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_1041,plain,(
    ! [D_158] :
      ( m1_subset_1(k7_relat_1('#skF_4',D_158),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
      | ~ v1_funct_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_633,c_996])).

tff(c_1063,plain,(
    ! [D_194] : m1_subset_1(k7_relat_1('#skF_4',D_194),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_66,c_1041])).

tff(c_26,plain,(
    ! [C_19,A_17,B_18] :
      ( v1_relat_1(C_19)
      | ~ m1_subset_1(C_19,k1_zfmisc_1(k2_zfmisc_1(A_17,B_18))) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_1115,plain,(
    ! [D_194] : v1_relat_1(k7_relat_1('#skF_4',D_194)) ),
    inference(resolution,[status(thm)],[c_1063,c_26])).

tff(c_28,plain,(
    ! [C_22,B_21,A_20] :
      ( v5_relat_1(C_22,B_21)
      | ~ m1_subset_1(C_22,k1_zfmisc_1(k2_zfmisc_1(A_20,B_21))) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_1113,plain,(
    ! [D_194] : v5_relat_1(k7_relat_1('#skF_4',D_194),'#skF_2') ),
    inference(resolution,[status(thm)],[c_1063,c_28])).

tff(c_14,plain,(
    ! [B_9,A_8] :
      ( r1_tarski(k2_relat_1(B_9),A_8)
      | ~ v5_relat_1(B_9,A_8)
      | ~ v1_relat_1(B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_501,plain,(
    ! [A_133,B_134,C_135,D_136] :
      ( v1_funct_1(k2_partfun1(A_133,B_134,C_135,D_136))
      | ~ m1_subset_1(C_135,k1_zfmisc_1(k2_zfmisc_1(A_133,B_134)))
      | ~ v1_funct_1(C_135) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_503,plain,(
    ! [D_136] :
      ( v1_funct_1(k2_partfun1('#skF_1','#skF_2','#skF_4',D_136))
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_66,c_501])).

tff(c_509,plain,(
    ! [D_136] : v1_funct_1(k2_partfun1('#skF_1','#skF_2','#skF_4',D_136)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_503])).

tff(c_646,plain,(
    ! [D_136] : v1_funct_1(k7_relat_1('#skF_4',D_136)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_633,c_509])).

tff(c_431,plain,(
    ! [A_122,B_123,C_124] :
      ( k1_relset_1(A_122,B_123,C_124) = k1_relat_1(C_124)
      | ~ m1_subset_1(C_124,k1_zfmisc_1(k2_zfmisc_1(A_122,B_123))) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_439,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_66,c_431])).

tff(c_837,plain,(
    ! [B_182,A_183,C_184] :
      ( k1_xboole_0 = B_182
      | k1_relset_1(A_183,B_182,C_184) = A_183
      | ~ v1_funct_2(C_184,A_183,B_182)
      | ~ m1_subset_1(C_184,k1_zfmisc_1(k2_zfmisc_1(A_183,B_182))) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_843,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1('#skF_1','#skF_2','#skF_4') = '#skF_1'
    | ~ v1_funct_2('#skF_4','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_66,c_837])).

tff(c_851,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_439,c_843])).

tff(c_852,plain,(
    k1_relat_1('#skF_4') = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_83,c_851])).

tff(c_877,plain,(
    ! [A_12] :
      ( k1_relat_1(k7_relat_1('#skF_4',A_12)) = A_12
      | ~ r1_tarski(A_12,'#skF_1')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_852,c_22])).

tff(c_928,plain,(
    ! [A_189] :
      ( k1_relat_1(k7_relat_1('#skF_4',A_189)) = A_189
      | ~ r1_tarski(A_189,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_103,c_877])).

tff(c_54,plain,(
    ! [B_42,A_41] :
      ( m1_subset_1(B_42,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B_42),A_41)))
      | ~ r1_tarski(k2_relat_1(B_42),A_41)
      | ~ v1_funct_1(B_42)
      | ~ v1_relat_1(B_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_946,plain,(
    ! [A_189,A_41] :
      ( m1_subset_1(k7_relat_1('#skF_4',A_189),k1_zfmisc_1(k2_zfmisc_1(A_189,A_41)))
      | ~ r1_tarski(k2_relat_1(k7_relat_1('#skF_4',A_189)),A_41)
      | ~ v1_funct_1(k7_relat_1('#skF_4',A_189))
      | ~ v1_relat_1(k7_relat_1('#skF_4',A_189))
      | ~ r1_tarski(A_189,'#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_928,c_54])).

tff(c_982,plain,(
    ! [A_189,A_41] :
      ( m1_subset_1(k7_relat_1('#skF_4',A_189),k1_zfmisc_1(k2_zfmisc_1(A_189,A_41)))
      | ~ r1_tarski(k2_relat_1(k7_relat_1('#skF_4',A_189)),A_41)
      | ~ v1_relat_1(k7_relat_1('#skF_4',A_189))
      | ~ r1_tarski(A_189,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_646,c_946])).

tff(c_20614,plain,(
    ! [A_885,A_886] :
      ( m1_subset_1(k7_relat_1('#skF_4',A_885),k1_zfmisc_1(k2_zfmisc_1(A_885,A_886)))
      | ~ r1_tarski(k2_relat_1(k7_relat_1('#skF_4',A_885)),A_886)
      | ~ r1_tarski(A_885,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1115,c_982])).

tff(c_299,plain,(
    ! [A_92,B_93,C_94,D_95] :
      ( v1_funct_1(k2_partfun1(A_92,B_93,C_94,D_95))
      | ~ m1_subset_1(C_94,k1_zfmisc_1(k2_zfmisc_1(A_92,B_93)))
      | ~ v1_funct_1(C_94) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_301,plain,(
    ! [D_95] :
      ( v1_funct_1(k2_partfun1('#skF_1','#skF_2','#skF_4',D_95))
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_66,c_299])).

tff(c_307,plain,(
    ! [D_95] : v1_funct_1(k2_partfun1('#skF_1','#skF_2','#skF_4',D_95)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_301])).

tff(c_60,plain,
    ( ~ m1_subset_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2')))
    | ~ v1_funct_2(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),'#skF_3','#skF_2')
    | ~ v1_funct_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_115,plain,(
    ~ v1_funct_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_60])).

tff(c_313,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_307,c_115])).

tff(c_314,plain,
    ( ~ v1_funct_2(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),'#skF_3','#skF_2')
    | ~ m1_subset_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_60])).

tff(c_345,plain,(
    ~ m1_subset_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_314])).

tff(c_647,plain,(
    ~ m1_subset_1(k7_relat_1('#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_633,c_345])).

tff(c_20655,plain,
    ( ~ r1_tarski(k2_relat_1(k7_relat_1('#skF_4','#skF_3')),'#skF_2')
    | ~ r1_tarski('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_20614,c_647])).

tff(c_20738,plain,(
    ~ r1_tarski(k2_relat_1(k7_relat_1('#skF_4','#skF_3')),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_20655])).

tff(c_20766,plain,
    ( ~ v5_relat_1(k7_relat_1('#skF_4','#skF_3'),'#skF_2')
    | ~ v1_relat_1(k7_relat_1('#skF_4','#skF_3')) ),
    inference(resolution,[status(thm)],[c_14,c_20738])).

tff(c_20770,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1115,c_1113,c_20766])).

tff(c_20772,plain,(
    m1_subset_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_314])).

tff(c_20940,plain,(
    k1_relset_1('#skF_3','#skF_2',k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3')) = k1_relat_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3')) ),
    inference(resolution,[status(thm)],[c_20772,c_20929])).

tff(c_21182,plain,(
    k1_relset_1('#skF_3','#skF_2',k7_relat_1('#skF_4','#skF_3')) = k1_relat_1(k7_relat_1('#skF_4','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_21168,c_21168,c_20940])).

tff(c_20771,plain,(
    ~ v1_funct_2(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),'#skF_3','#skF_2') ),
    inference(splitRight,[status(thm)],[c_314])).

tff(c_21191,plain,(
    ~ v1_funct_2(k7_relat_1('#skF_4','#skF_3'),'#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_21168,c_20771])).

tff(c_21190,plain,(
    m1_subset_1(k7_relat_1('#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_21168,c_20772])).

tff(c_21417,plain,(
    ! [B_961,C_962,A_963] :
      ( k1_xboole_0 = B_961
      | v1_funct_2(C_962,A_963,B_961)
      | k1_relset_1(A_963,B_961,C_962) != A_963
      | ~ m1_subset_1(C_962,k1_zfmisc_1(k2_zfmisc_1(A_963,B_961))) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_21420,plain,
    ( k1_xboole_0 = '#skF_2'
    | v1_funct_2(k7_relat_1('#skF_4','#skF_3'),'#skF_3','#skF_2')
    | k1_relset_1('#skF_3','#skF_2',k7_relat_1('#skF_4','#skF_3')) != '#skF_3' ),
    inference(resolution,[status(thm)],[c_21190,c_21417])).

tff(c_21433,plain,(
    k1_relset_1('#skF_3','#skF_2',k7_relat_1('#skF_4','#skF_3')) != '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_21191,c_83,c_21420])).

tff(c_21449,plain,(
    k1_relat_1(k7_relat_1('#skF_4','#skF_3')) != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_21182,c_21433])).

tff(c_21456,plain,(
    ~ r1_tarski('#skF_3','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_21310,c_21449])).

tff(c_21460,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_21456])).

tff(c_21461,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_62])).

tff(c_21462,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_62])).

tff(c_21472,plain,(
    '#skF_2' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_21461,c_21462])).

tff(c_21487,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_21472,c_66])).

tff(c_21501,plain,(
    ! [C_973,A_974,B_975] :
      ( v1_relat_1(C_973)
      | ~ m1_subset_1(C_973,k1_zfmisc_1(k2_zfmisc_1(A_974,B_975))) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_21510,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_21487,c_21501])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_21467,plain,(
    v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_21461,c_2])).

tff(c_22064,plain,(
    ! [C_1062,A_1063,B_1064] :
      ( v1_xboole_0(C_1062)
      | ~ m1_subset_1(C_1062,k1_zfmisc_1(k2_zfmisc_1(A_1063,B_1064)))
      | ~ v1_xboole_0(A_1063) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_22071,plain,
    ( v1_xboole_0('#skF_4')
    | ~ v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_21487,c_22064])).

tff(c_22076,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_21467,c_22071])).

tff(c_21489,plain,(
    ! [B_969,A_970] :
      ( ~ v1_xboole_0(B_969)
      | B_969 = A_970
      | ~ v1_xboole_0(A_970) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_21492,plain,(
    ! [A_970] :
      ( A_970 = '#skF_1'
      | ~ v1_xboole_0(A_970) ) ),
    inference(resolution,[status(thm)],[c_21467,c_21489])).

tff(c_22082,plain,(
    '#skF_1' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_22076,c_21492])).

tff(c_4,plain,(
    ! [A_1] : r1_tarski(k1_xboole_0,A_1) ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_21466,plain,(
    ! [A_1] : r1_tarski('#skF_1',A_1) ),
    inference(demodulation,[status(thm),theory(equality)],[c_21461,c_4])).

tff(c_22101,plain,(
    ! [A_1] : r1_tarski('#skF_4',A_1) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22082,c_21466])).

tff(c_18,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_21464,plain,(
    k2_relat_1('#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_21461,c_21461,c_18])).

tff(c_22102,plain,(
    k2_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_22082,c_22082,c_21464])).

tff(c_20,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_21465,plain,(
    k1_relat_1('#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_21461,c_21461,c_20])).

tff(c_22100,plain,(
    k1_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_22082,c_22082,c_21465])).

tff(c_22234,plain,(
    ! [B_1079,A_1080] :
      ( v1_funct_2(B_1079,k1_relat_1(B_1079),A_1080)
      | ~ r1_tarski(k2_relat_1(B_1079),A_1080)
      | ~ v1_funct_1(B_1079)
      | ~ v1_relat_1(B_1079) ) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_22237,plain,(
    ! [A_1080] :
      ( v1_funct_2('#skF_4','#skF_4',A_1080)
      | ~ r1_tarski(k2_relat_1('#skF_4'),A_1080)
      | ~ v1_funct_1('#skF_4')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22100,c_22234])).

tff(c_22239,plain,(
    ! [A_1080] : v1_funct_2('#skF_4','#skF_4',A_1080) ),
    inference(demodulation,[status(thm),theory(equality)],[c_21510,c_70,c_22101,c_22102,c_22237])).

tff(c_22106,plain,(
    r1_tarski('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22082,c_64])).

tff(c_8,plain,(
    ! [A_4] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_4)) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_21463,plain,(
    ! [A_4] : m1_subset_1('#skF_1',k1_zfmisc_1(A_4)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_21461,c_8])).

tff(c_21509,plain,(
    v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_21463,c_21501])).

tff(c_21991,plain,(
    ! [C_1045,A_1046,B_1047] :
      ( v4_relat_1(C_1045,A_1046)
      | ~ m1_subset_1(C_1045,k1_zfmisc_1(k2_zfmisc_1(A_1046,B_1047))) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_22007,plain,(
    ! [A_1048] : v4_relat_1('#skF_1',A_1048) ),
    inference(resolution,[status(thm)],[c_21463,c_21991])).

tff(c_16,plain,(
    ! [B_11,A_10] :
      ( k7_relat_1(B_11,A_10) = B_11
      | ~ v4_relat_1(B_11,A_10)
      | ~ v1_relat_1(B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_22010,plain,(
    ! [A_1048] :
      ( k7_relat_1('#skF_1',A_1048) = '#skF_1'
      | ~ v1_relat_1('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_22007,c_16])).

tff(c_22013,plain,(
    ! [A_1048] : k7_relat_1('#skF_1',A_1048) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_21509,c_22010])).

tff(c_22087,plain,(
    ! [A_1048] : k7_relat_1('#skF_4',A_1048) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_22082,c_22082,c_22013])).

tff(c_22153,plain,(
    ! [A_12] :
      ( k1_relat_1(k7_relat_1('#skF_4',A_12)) = A_12
      | ~ r1_tarski(A_12,'#skF_4')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22100,c_22])).

tff(c_22157,plain,(
    ! [A_12] :
      ( k1_relat_1(k7_relat_1('#skF_4',A_12)) = A_12
      | ~ r1_tarski(A_12,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_21510,c_22153])).

tff(c_22487,plain,(
    ! [A_1113] :
      ( A_1113 = '#skF_4'
      | ~ r1_tarski(A_1113,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22100,c_22087,c_22157])).

tff(c_22501,plain,(
    '#skF_3' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_22106,c_22487])).

tff(c_22097,plain,(
    ! [A_4] : m1_subset_1('#skF_4',k1_zfmisc_1(A_4)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22082,c_21463])).

tff(c_22397,plain,(
    ! [A_1106,B_1107,C_1108,D_1109] :
      ( k2_partfun1(A_1106,B_1107,C_1108,D_1109) = k7_relat_1(C_1108,D_1109)
      | ~ m1_subset_1(C_1108,k1_zfmisc_1(k2_zfmisc_1(A_1106,B_1107)))
      | ~ v1_funct_1(C_1108) ) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_22402,plain,(
    ! [A_1106,B_1107,D_1109] :
      ( k2_partfun1(A_1106,B_1107,'#skF_4',D_1109) = k7_relat_1('#skF_4',D_1109)
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_22097,c_22397])).

tff(c_22406,plain,(
    ! [A_1106,B_1107,D_1109] : k2_partfun1(A_1106,B_1107,'#skF_4',D_1109) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_22087,c_22402])).

tff(c_22280,plain,(
    ! [A_1087] :
      ( A_1087 = '#skF_4'
      | ~ r1_tarski(A_1087,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22100,c_22087,c_22157])).

tff(c_22294,plain,(
    '#skF_3' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_22106,c_22280])).

tff(c_21712,plain,(
    ! [C_1008,A_1009,B_1010] :
      ( v1_xboole_0(C_1008)
      | ~ m1_subset_1(C_1008,k1_zfmisc_1(k2_zfmisc_1(A_1009,B_1010)))
      | ~ v1_xboole_0(A_1009) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_21719,plain,
    ( v1_xboole_0('#skF_4')
    | ~ v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_21487,c_21712])).

tff(c_21724,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_21467,c_21719])).

tff(c_21730,plain,(
    '#skF_1' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_21724,c_21492])).

tff(c_21745,plain,(
    ! [A_4] : m1_subset_1('#skF_4',k1_zfmisc_1(A_4)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_21730,c_21463])).

tff(c_21957,plain,(
    ! [A_1035,B_1036,C_1037,D_1038] :
      ( v1_funct_1(k2_partfun1(A_1035,B_1036,C_1037,D_1038))
      | ~ m1_subset_1(C_1037,k1_zfmisc_1(k2_zfmisc_1(A_1035,B_1036)))
      | ~ v1_funct_1(C_1037) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_21960,plain,(
    ! [A_1035,B_1036,D_1038] :
      ( v1_funct_1(k2_partfun1(A_1035,B_1036,'#skF_4',D_1038))
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_21745,c_21957])).

tff(c_21963,plain,(
    ! [A_1035,B_1036,D_1038] : v1_funct_1(k2_partfun1(A_1035,B_1036,'#skF_4',D_1038)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_21960])).

tff(c_21754,plain,(
    r1_tarski('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_21730,c_64])).

tff(c_21748,plain,(
    k1_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_21730,c_21730,c_21465])).

tff(c_21532,plain,(
    ! [C_984,A_985,B_986] :
      ( v4_relat_1(C_984,A_985)
      | ~ m1_subset_1(C_984,k1_zfmisc_1(k2_zfmisc_1(A_985,B_986))) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_21552,plain,(
    ! [A_989] : v4_relat_1('#skF_1',A_989) ),
    inference(resolution,[status(thm)],[c_21463,c_21532])).

tff(c_21555,plain,(
    ! [A_989] :
      ( k7_relat_1('#skF_1',A_989) = '#skF_1'
      | ~ v1_relat_1('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_21552,c_16])).

tff(c_21558,plain,(
    ! [A_989] : k7_relat_1('#skF_1',A_989) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_21509,c_21555])).

tff(c_21736,plain,(
    ! [A_989] : k7_relat_1('#skF_4',A_989) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_21730,c_21730,c_21558])).

tff(c_21816,plain,(
    ! [A_12] :
      ( k1_relat_1(k7_relat_1('#skF_4',A_12)) = A_12
      | ~ r1_tarski(A_12,'#skF_4')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_21748,c_22])).

tff(c_21820,plain,(
    ! [A_12] :
      ( k1_relat_1(k7_relat_1('#skF_4',A_12)) = A_12
      | ~ r1_tarski(A_12,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_21510,c_21816])).

tff(c_21926,plain,(
    ! [A_1033] :
      ( A_1033 = '#skF_4'
      | ~ r1_tarski(A_1033,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_21748,c_21736,c_21820])).

tff(c_21938,plain,(
    '#skF_3' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_21754,c_21926])).

tff(c_21518,plain,
    ( ~ m1_subset_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_1')))
    | ~ v1_funct_2(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_3'),'#skF_3','#skF_1')
    | ~ v1_funct_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_21472,c_21472,c_21472,c_21472,c_21472,c_60])).

tff(c_21519,plain,(
    ~ v1_funct_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_21518])).

tff(c_21740,plain,(
    ~ v1_funct_1(k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_21730,c_21730,c_21519])).

tff(c_21942,plain,(
    ~ v1_funct_1(k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_21938,c_21740])).

tff(c_21966,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_21963,c_21942])).

tff(c_21967,plain,
    ( ~ v1_funct_2(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_3'),'#skF_3','#skF_1')
    | ~ m1_subset_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_21518])).

tff(c_22244,plain,
    ( ~ v1_funct_2(k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_3'),'#skF_3','#skF_4')
    | ~ m1_subset_1(k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22082,c_22082,c_22082,c_22082,c_22082,c_22082,c_21967])).

tff(c_22245,plain,(
    ~ m1_subset_1(k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(splitLeft,[status(thm)],[c_22244])).

tff(c_22311,plain,(
    ~ m1_subset_1(k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22294,c_22294,c_22245])).

tff(c_22408,plain,(
    ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22406,c_22311])).

tff(c_22412,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_22097,c_22408])).

tff(c_22414,plain,(
    m1_subset_1(k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(splitRight,[status(thm)],[c_22244])).

tff(c_32,plain,(
    ! [C_26,A_23,B_24] :
      ( v1_xboole_0(C_26)
      | ~ m1_subset_1(C_26,k1_zfmisc_1(k2_zfmisc_1(A_23,B_24)))
      | ~ v1_xboole_0(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_22473,plain,
    ( v1_xboole_0(k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_3'))
    | ~ v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_22414,c_32])).

tff(c_22525,plain,(
    v1_xboole_0(k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22076,c_22501,c_22501,c_22473])).

tff(c_6,plain,(
    ! [B_3,A_2] :
      ( ~ v1_xboole_0(B_3)
      | B_3 = A_2
      | ~ v1_xboole_0(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_22083,plain,(
    ! [A_2] :
      ( A_2 = '#skF_4'
      | ~ v1_xboole_0(A_2) ) ),
    inference(resolution,[status(thm)],[c_22076,c_6])).

tff(c_22531,plain,(
    k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_4') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_22525,c_22083])).

tff(c_22413,plain,(
    ~ v1_funct_2(k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_3'),'#skF_3','#skF_4') ),
    inference(splitRight,[status(thm)],[c_22244])).

tff(c_22507,plain,(
    ~ v1_funct_2(k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_4'),'#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22501,c_22501,c_22413])).

tff(c_22547,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_22239,c_22531,c_22507])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:55:22 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 11.80/4.78  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.80/4.82  
% 11.80/4.82  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.80/4.82  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_partfun1 > k1_relset_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 11.80/4.82  
% 11.80/4.82  %Foreground sorts:
% 11.80/4.82  
% 11.80/4.82  
% 11.80/4.82  %Background operators:
% 11.80/4.82  
% 11.80/4.82  
% 11.80/4.82  %Foreground operators:
% 11.80/4.82  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 11.80/4.82  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 11.80/4.82  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 11.80/4.82  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 11.80/4.82  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 11.80/4.82  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 11.80/4.82  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 11.80/4.82  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 11.80/4.82  tff('#skF_2', type, '#skF_2': $i).
% 11.80/4.82  tff('#skF_3', type, '#skF_3': $i).
% 11.80/4.82  tff('#skF_1', type, '#skF_1': $i).
% 11.80/4.82  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 11.80/4.82  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 11.80/4.82  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 11.80/4.82  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 11.80/4.82  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 11.80/4.82  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 11.80/4.82  tff('#skF_4', type, '#skF_4': $i).
% 11.80/4.82  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 11.80/4.82  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 11.80/4.82  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 11.80/4.82  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 11.80/4.82  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 11.80/4.82  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 11.80/4.82  
% 12.10/4.85  tff(f_159, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r1_tarski(C, A) => (((B = k1_xboole_0) & ~(A = k1_xboole_0)) | ((v1_funct_1(k2_partfun1(A, B, D, C)) & v1_funct_2(k2_partfun1(A, B, D, C), C, B)) & m1_subset_1(k2_partfun1(A, B, D, C), k1_zfmisc_1(k2_zfmisc_1(C, B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_funct_2)).
% 12.10/4.85  tff(f_78, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 12.10/4.85  tff(f_95, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 12.10/4.85  tff(f_113, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 12.10/4.85  tff(f_65, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(A, k1_relat_1(B)) => (k1_relat_1(k7_relat_1(B, A)) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_relat_1)).
% 12.10/4.85  tff(f_127, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (k2_partfun1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_partfun1)).
% 12.10/4.85  tff(f_121, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (v1_funct_1(k2_partfun1(A, B, C, D)) & m1_subset_1(k2_partfun1(A, B, C, D), k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_partfun1)).
% 12.10/4.85  tff(f_84, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 12.10/4.85  tff(f_50, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 12.10/4.85  tff(f_139, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r1_tarski(k2_relat_1(B), A) => ((v1_funct_1(B) & v1_funct_2(B, k1_relat_1(B), A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B), A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_funct_2)).
% 12.10/4.85  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 12.10/4.85  tff(f_91, axiom, (![A, B]: (v1_xboole_0(A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_xboole_0(C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc3_relset_1)).
% 12.10/4.85  tff(f_36, axiom, (![A, B]: ~((v1_xboole_0(A) & ~(A = B)) & v1_xboole_0(B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_boole)).
% 12.10/4.85  tff(f_28, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 12.10/4.85  tff(f_59, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 12.10/4.85  tff(f_38, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 12.10/4.85  tff(f_56, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t209_relat_1)).
% 12.10/4.85  tff(c_64, plain, (r1_tarski('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_159])).
% 12.10/4.85  tff(c_66, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_159])).
% 12.10/4.85  tff(c_95, plain, (![C_49, A_50, B_51]: (v1_relat_1(C_49) | ~m1_subset_1(C_49, k1_zfmisc_1(k2_zfmisc_1(A_50, B_51))))), inference(cnfTransformation, [status(thm)], [f_78])).
% 12.10/4.85  tff(c_103, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_66, c_95])).
% 12.10/4.85  tff(c_62, plain, (k1_xboole_0='#skF_1' | k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_159])).
% 12.10/4.85  tff(c_83, plain, (k1_xboole_0!='#skF_2'), inference(splitLeft, [status(thm)], [c_62])).
% 12.10/4.85  tff(c_68, plain, (v1_funct_2('#skF_4', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_159])).
% 12.10/4.85  tff(c_20929, plain, (![A_907, B_908, C_909]: (k1_relset_1(A_907, B_908, C_909)=k1_relat_1(C_909) | ~m1_subset_1(C_909, k1_zfmisc_1(k2_zfmisc_1(A_907, B_908))))), inference(cnfTransformation, [status(thm)], [f_95])).
% 12.10/4.85  tff(c_20941, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_66, c_20929])).
% 12.10/4.85  tff(c_21261, plain, (![B_953, A_954, C_955]: (k1_xboole_0=B_953 | k1_relset_1(A_954, B_953, C_955)=A_954 | ~v1_funct_2(C_955, A_954, B_953) | ~m1_subset_1(C_955, k1_zfmisc_1(k2_zfmisc_1(A_954, B_953))))), inference(cnfTransformation, [status(thm)], [f_113])).
% 12.10/4.85  tff(c_21270, plain, (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', '#skF_4')='#skF_1' | ~v1_funct_2('#skF_4', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_66, c_21261])).
% 12.10/4.85  tff(c_21280, plain, (k1_xboole_0='#skF_2' | k1_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_68, c_20941, c_21270])).
% 12.10/4.85  tff(c_21281, plain, (k1_relat_1('#skF_4')='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_83, c_21280])).
% 12.10/4.85  tff(c_22, plain, (![B_13, A_12]: (k1_relat_1(k7_relat_1(B_13, A_12))=A_12 | ~r1_tarski(A_12, k1_relat_1(B_13)) | ~v1_relat_1(B_13))), inference(cnfTransformation, [status(thm)], [f_65])).
% 12.10/4.85  tff(c_21300, plain, (![A_12]: (k1_relat_1(k7_relat_1('#skF_4', A_12))=A_12 | ~r1_tarski(A_12, '#skF_1') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_21281, c_22])).
% 12.10/4.85  tff(c_21310, plain, (![A_12]: (k1_relat_1(k7_relat_1('#skF_4', A_12))=A_12 | ~r1_tarski(A_12, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_103, c_21300])).
% 12.10/4.85  tff(c_70, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_159])).
% 12.10/4.85  tff(c_21152, plain, (![A_943, B_944, C_945, D_946]: (k2_partfun1(A_943, B_944, C_945, D_946)=k7_relat_1(C_945, D_946) | ~m1_subset_1(C_945, k1_zfmisc_1(k2_zfmisc_1(A_943, B_944))) | ~v1_funct_1(C_945))), inference(cnfTransformation, [status(thm)], [f_127])).
% 12.10/4.85  tff(c_21158, plain, (![D_946]: (k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_946)=k7_relat_1('#skF_4', D_946) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_66, c_21152])).
% 12.10/4.85  tff(c_21168, plain, (![D_946]: (k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_946)=k7_relat_1('#skF_4', D_946))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_21158])).
% 12.10/4.85  tff(c_622, plain, (![A_155, B_156, C_157, D_158]: (k2_partfun1(A_155, B_156, C_157, D_158)=k7_relat_1(C_157, D_158) | ~m1_subset_1(C_157, k1_zfmisc_1(k2_zfmisc_1(A_155, B_156))) | ~v1_funct_1(C_157))), inference(cnfTransformation, [status(thm)], [f_127])).
% 12.10/4.85  tff(c_626, plain, (![D_158]: (k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_158)=k7_relat_1('#skF_4', D_158) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_66, c_622])).
% 12.10/4.85  tff(c_633, plain, (![D_158]: (k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_158)=k7_relat_1('#skF_4', D_158))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_626])).
% 12.10/4.85  tff(c_996, plain, (![A_190, B_191, C_192, D_193]: (m1_subset_1(k2_partfun1(A_190, B_191, C_192, D_193), k1_zfmisc_1(k2_zfmisc_1(A_190, B_191))) | ~m1_subset_1(C_192, k1_zfmisc_1(k2_zfmisc_1(A_190, B_191))) | ~v1_funct_1(C_192))), inference(cnfTransformation, [status(thm)], [f_121])).
% 12.10/4.85  tff(c_1041, plain, (![D_158]: (m1_subset_1(k7_relat_1('#skF_4', D_158), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_633, c_996])).
% 12.10/4.85  tff(c_1063, plain, (![D_194]: (m1_subset_1(k7_relat_1('#skF_4', D_194), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_66, c_1041])).
% 12.10/4.85  tff(c_26, plain, (![C_19, A_17, B_18]: (v1_relat_1(C_19) | ~m1_subset_1(C_19, k1_zfmisc_1(k2_zfmisc_1(A_17, B_18))))), inference(cnfTransformation, [status(thm)], [f_78])).
% 12.10/4.85  tff(c_1115, plain, (![D_194]: (v1_relat_1(k7_relat_1('#skF_4', D_194)))), inference(resolution, [status(thm)], [c_1063, c_26])).
% 12.10/4.85  tff(c_28, plain, (![C_22, B_21, A_20]: (v5_relat_1(C_22, B_21) | ~m1_subset_1(C_22, k1_zfmisc_1(k2_zfmisc_1(A_20, B_21))))), inference(cnfTransformation, [status(thm)], [f_84])).
% 12.10/4.85  tff(c_1113, plain, (![D_194]: (v5_relat_1(k7_relat_1('#skF_4', D_194), '#skF_2'))), inference(resolution, [status(thm)], [c_1063, c_28])).
% 12.10/4.85  tff(c_14, plain, (![B_9, A_8]: (r1_tarski(k2_relat_1(B_9), A_8) | ~v5_relat_1(B_9, A_8) | ~v1_relat_1(B_9))), inference(cnfTransformation, [status(thm)], [f_50])).
% 12.10/4.85  tff(c_501, plain, (![A_133, B_134, C_135, D_136]: (v1_funct_1(k2_partfun1(A_133, B_134, C_135, D_136)) | ~m1_subset_1(C_135, k1_zfmisc_1(k2_zfmisc_1(A_133, B_134))) | ~v1_funct_1(C_135))), inference(cnfTransformation, [status(thm)], [f_121])).
% 12.10/4.85  tff(c_503, plain, (![D_136]: (v1_funct_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_136)) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_66, c_501])).
% 12.10/4.85  tff(c_509, plain, (![D_136]: (v1_funct_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_136)))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_503])).
% 12.10/4.85  tff(c_646, plain, (![D_136]: (v1_funct_1(k7_relat_1('#skF_4', D_136)))), inference(demodulation, [status(thm), theory('equality')], [c_633, c_509])).
% 12.10/4.85  tff(c_431, plain, (![A_122, B_123, C_124]: (k1_relset_1(A_122, B_123, C_124)=k1_relat_1(C_124) | ~m1_subset_1(C_124, k1_zfmisc_1(k2_zfmisc_1(A_122, B_123))))), inference(cnfTransformation, [status(thm)], [f_95])).
% 12.10/4.85  tff(c_439, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_66, c_431])).
% 12.10/4.85  tff(c_837, plain, (![B_182, A_183, C_184]: (k1_xboole_0=B_182 | k1_relset_1(A_183, B_182, C_184)=A_183 | ~v1_funct_2(C_184, A_183, B_182) | ~m1_subset_1(C_184, k1_zfmisc_1(k2_zfmisc_1(A_183, B_182))))), inference(cnfTransformation, [status(thm)], [f_113])).
% 12.10/4.85  tff(c_843, plain, (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', '#skF_4')='#skF_1' | ~v1_funct_2('#skF_4', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_66, c_837])).
% 12.10/4.85  tff(c_851, plain, (k1_xboole_0='#skF_2' | k1_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_68, c_439, c_843])).
% 12.10/4.85  tff(c_852, plain, (k1_relat_1('#skF_4')='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_83, c_851])).
% 12.10/4.85  tff(c_877, plain, (![A_12]: (k1_relat_1(k7_relat_1('#skF_4', A_12))=A_12 | ~r1_tarski(A_12, '#skF_1') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_852, c_22])).
% 12.10/4.85  tff(c_928, plain, (![A_189]: (k1_relat_1(k7_relat_1('#skF_4', A_189))=A_189 | ~r1_tarski(A_189, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_103, c_877])).
% 12.10/4.85  tff(c_54, plain, (![B_42, A_41]: (m1_subset_1(B_42, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B_42), A_41))) | ~r1_tarski(k2_relat_1(B_42), A_41) | ~v1_funct_1(B_42) | ~v1_relat_1(B_42))), inference(cnfTransformation, [status(thm)], [f_139])).
% 12.10/4.85  tff(c_946, plain, (![A_189, A_41]: (m1_subset_1(k7_relat_1('#skF_4', A_189), k1_zfmisc_1(k2_zfmisc_1(A_189, A_41))) | ~r1_tarski(k2_relat_1(k7_relat_1('#skF_4', A_189)), A_41) | ~v1_funct_1(k7_relat_1('#skF_4', A_189)) | ~v1_relat_1(k7_relat_1('#skF_4', A_189)) | ~r1_tarski(A_189, '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_928, c_54])).
% 12.10/4.85  tff(c_982, plain, (![A_189, A_41]: (m1_subset_1(k7_relat_1('#skF_4', A_189), k1_zfmisc_1(k2_zfmisc_1(A_189, A_41))) | ~r1_tarski(k2_relat_1(k7_relat_1('#skF_4', A_189)), A_41) | ~v1_relat_1(k7_relat_1('#skF_4', A_189)) | ~r1_tarski(A_189, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_646, c_946])).
% 12.10/4.85  tff(c_20614, plain, (![A_885, A_886]: (m1_subset_1(k7_relat_1('#skF_4', A_885), k1_zfmisc_1(k2_zfmisc_1(A_885, A_886))) | ~r1_tarski(k2_relat_1(k7_relat_1('#skF_4', A_885)), A_886) | ~r1_tarski(A_885, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_1115, c_982])).
% 12.10/4.85  tff(c_299, plain, (![A_92, B_93, C_94, D_95]: (v1_funct_1(k2_partfun1(A_92, B_93, C_94, D_95)) | ~m1_subset_1(C_94, k1_zfmisc_1(k2_zfmisc_1(A_92, B_93))) | ~v1_funct_1(C_94))), inference(cnfTransformation, [status(thm)], [f_121])).
% 12.10/4.85  tff(c_301, plain, (![D_95]: (v1_funct_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_95)) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_66, c_299])).
% 12.10/4.85  tff(c_307, plain, (![D_95]: (v1_funct_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_95)))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_301])).
% 12.10/4.85  tff(c_60, plain, (~m1_subset_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2'))) | ~v1_funct_2(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), '#skF_3', '#skF_2') | ~v1_funct_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_159])).
% 12.10/4.85  tff(c_115, plain, (~v1_funct_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'))), inference(splitLeft, [status(thm)], [c_60])).
% 12.10/4.85  tff(c_313, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_307, c_115])).
% 12.10/4.85  tff(c_314, plain, (~v1_funct_2(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), '#skF_3', '#skF_2') | ~m1_subset_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(splitRight, [status(thm)], [c_60])).
% 12.10/4.85  tff(c_345, plain, (~m1_subset_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(splitLeft, [status(thm)], [c_314])).
% 12.10/4.85  tff(c_647, plain, (~m1_subset_1(k7_relat_1('#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_633, c_345])).
% 12.10/4.85  tff(c_20655, plain, (~r1_tarski(k2_relat_1(k7_relat_1('#skF_4', '#skF_3')), '#skF_2') | ~r1_tarski('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_20614, c_647])).
% 12.10/4.85  tff(c_20738, plain, (~r1_tarski(k2_relat_1(k7_relat_1('#skF_4', '#skF_3')), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_20655])).
% 12.10/4.85  tff(c_20766, plain, (~v5_relat_1(k7_relat_1('#skF_4', '#skF_3'), '#skF_2') | ~v1_relat_1(k7_relat_1('#skF_4', '#skF_3'))), inference(resolution, [status(thm)], [c_14, c_20738])).
% 12.10/4.85  tff(c_20770, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1115, c_1113, c_20766])).
% 12.10/4.85  tff(c_20772, plain, (m1_subset_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(splitRight, [status(thm)], [c_314])).
% 12.10/4.85  tff(c_20940, plain, (k1_relset_1('#skF_3', '#skF_2', k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'))=k1_relat_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'))), inference(resolution, [status(thm)], [c_20772, c_20929])).
% 12.10/4.85  tff(c_21182, plain, (k1_relset_1('#skF_3', '#skF_2', k7_relat_1('#skF_4', '#skF_3'))=k1_relat_1(k7_relat_1('#skF_4', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_21168, c_21168, c_20940])).
% 12.10/4.85  tff(c_20771, plain, (~v1_funct_2(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), '#skF_3', '#skF_2')), inference(splitRight, [status(thm)], [c_314])).
% 12.10/4.85  tff(c_21191, plain, (~v1_funct_2(k7_relat_1('#skF_4', '#skF_3'), '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_21168, c_20771])).
% 12.10/4.85  tff(c_21190, plain, (m1_subset_1(k7_relat_1('#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_21168, c_20772])).
% 12.10/4.85  tff(c_21417, plain, (![B_961, C_962, A_963]: (k1_xboole_0=B_961 | v1_funct_2(C_962, A_963, B_961) | k1_relset_1(A_963, B_961, C_962)!=A_963 | ~m1_subset_1(C_962, k1_zfmisc_1(k2_zfmisc_1(A_963, B_961))))), inference(cnfTransformation, [status(thm)], [f_113])).
% 12.10/4.85  tff(c_21420, plain, (k1_xboole_0='#skF_2' | v1_funct_2(k7_relat_1('#skF_4', '#skF_3'), '#skF_3', '#skF_2') | k1_relset_1('#skF_3', '#skF_2', k7_relat_1('#skF_4', '#skF_3'))!='#skF_3'), inference(resolution, [status(thm)], [c_21190, c_21417])).
% 12.10/4.85  tff(c_21433, plain, (k1_relset_1('#skF_3', '#skF_2', k7_relat_1('#skF_4', '#skF_3'))!='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_21191, c_83, c_21420])).
% 12.10/4.85  tff(c_21449, plain, (k1_relat_1(k7_relat_1('#skF_4', '#skF_3'))!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_21182, c_21433])).
% 12.10/4.85  tff(c_21456, plain, (~r1_tarski('#skF_3', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_21310, c_21449])).
% 12.10/4.85  tff(c_21460, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_64, c_21456])).
% 12.10/4.85  tff(c_21461, plain, (k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_62])).
% 12.10/4.85  tff(c_21462, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_62])).
% 12.10/4.85  tff(c_21472, plain, ('#skF_2'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_21461, c_21462])).
% 12.10/4.85  tff(c_21487, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_21472, c_66])).
% 12.10/4.85  tff(c_21501, plain, (![C_973, A_974, B_975]: (v1_relat_1(C_973) | ~m1_subset_1(C_973, k1_zfmisc_1(k2_zfmisc_1(A_974, B_975))))), inference(cnfTransformation, [status(thm)], [f_78])).
% 12.10/4.85  tff(c_21510, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_21487, c_21501])).
% 12.10/4.85  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 12.10/4.85  tff(c_21467, plain, (v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_21461, c_2])).
% 12.10/4.85  tff(c_22064, plain, (![C_1062, A_1063, B_1064]: (v1_xboole_0(C_1062) | ~m1_subset_1(C_1062, k1_zfmisc_1(k2_zfmisc_1(A_1063, B_1064))) | ~v1_xboole_0(A_1063))), inference(cnfTransformation, [status(thm)], [f_91])).
% 12.10/4.85  tff(c_22071, plain, (v1_xboole_0('#skF_4') | ~v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_21487, c_22064])).
% 12.10/4.85  tff(c_22076, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_21467, c_22071])).
% 12.10/4.85  tff(c_21489, plain, (![B_969, A_970]: (~v1_xboole_0(B_969) | B_969=A_970 | ~v1_xboole_0(A_970))), inference(cnfTransformation, [status(thm)], [f_36])).
% 12.10/4.85  tff(c_21492, plain, (![A_970]: (A_970='#skF_1' | ~v1_xboole_0(A_970))), inference(resolution, [status(thm)], [c_21467, c_21489])).
% 12.10/4.85  tff(c_22082, plain, ('#skF_1'='#skF_4'), inference(resolution, [status(thm)], [c_22076, c_21492])).
% 12.10/4.85  tff(c_4, plain, (![A_1]: (r1_tarski(k1_xboole_0, A_1))), inference(cnfTransformation, [status(thm)], [f_28])).
% 12.10/4.85  tff(c_21466, plain, (![A_1]: (r1_tarski('#skF_1', A_1))), inference(demodulation, [status(thm), theory('equality')], [c_21461, c_4])).
% 12.10/4.85  tff(c_22101, plain, (![A_1]: (r1_tarski('#skF_4', A_1))), inference(demodulation, [status(thm), theory('equality')], [c_22082, c_21466])).
% 12.10/4.85  tff(c_18, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_59])).
% 12.10/4.85  tff(c_21464, plain, (k2_relat_1('#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_21461, c_21461, c_18])).
% 12.10/4.85  tff(c_22102, plain, (k2_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_22082, c_22082, c_21464])).
% 12.10/4.85  tff(c_20, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_59])).
% 12.10/4.85  tff(c_21465, plain, (k1_relat_1('#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_21461, c_21461, c_20])).
% 12.10/4.85  tff(c_22100, plain, (k1_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_22082, c_22082, c_21465])).
% 12.10/4.85  tff(c_22234, plain, (![B_1079, A_1080]: (v1_funct_2(B_1079, k1_relat_1(B_1079), A_1080) | ~r1_tarski(k2_relat_1(B_1079), A_1080) | ~v1_funct_1(B_1079) | ~v1_relat_1(B_1079))), inference(cnfTransformation, [status(thm)], [f_139])).
% 12.10/4.85  tff(c_22237, plain, (![A_1080]: (v1_funct_2('#skF_4', '#skF_4', A_1080) | ~r1_tarski(k2_relat_1('#skF_4'), A_1080) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_22100, c_22234])).
% 12.10/4.85  tff(c_22239, plain, (![A_1080]: (v1_funct_2('#skF_4', '#skF_4', A_1080))), inference(demodulation, [status(thm), theory('equality')], [c_21510, c_70, c_22101, c_22102, c_22237])).
% 12.10/4.85  tff(c_22106, plain, (r1_tarski('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_22082, c_64])).
% 12.10/4.85  tff(c_8, plain, (![A_4]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_4)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 12.10/4.85  tff(c_21463, plain, (![A_4]: (m1_subset_1('#skF_1', k1_zfmisc_1(A_4)))), inference(demodulation, [status(thm), theory('equality')], [c_21461, c_8])).
% 12.10/4.85  tff(c_21509, plain, (v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_21463, c_21501])).
% 12.10/4.85  tff(c_21991, plain, (![C_1045, A_1046, B_1047]: (v4_relat_1(C_1045, A_1046) | ~m1_subset_1(C_1045, k1_zfmisc_1(k2_zfmisc_1(A_1046, B_1047))))), inference(cnfTransformation, [status(thm)], [f_84])).
% 12.10/4.85  tff(c_22007, plain, (![A_1048]: (v4_relat_1('#skF_1', A_1048))), inference(resolution, [status(thm)], [c_21463, c_21991])).
% 12.10/4.85  tff(c_16, plain, (![B_11, A_10]: (k7_relat_1(B_11, A_10)=B_11 | ~v4_relat_1(B_11, A_10) | ~v1_relat_1(B_11))), inference(cnfTransformation, [status(thm)], [f_56])).
% 12.10/4.85  tff(c_22010, plain, (![A_1048]: (k7_relat_1('#skF_1', A_1048)='#skF_1' | ~v1_relat_1('#skF_1'))), inference(resolution, [status(thm)], [c_22007, c_16])).
% 12.10/4.85  tff(c_22013, plain, (![A_1048]: (k7_relat_1('#skF_1', A_1048)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_21509, c_22010])).
% 12.10/4.85  tff(c_22087, plain, (![A_1048]: (k7_relat_1('#skF_4', A_1048)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_22082, c_22082, c_22013])).
% 12.10/4.85  tff(c_22153, plain, (![A_12]: (k1_relat_1(k7_relat_1('#skF_4', A_12))=A_12 | ~r1_tarski(A_12, '#skF_4') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_22100, c_22])).
% 12.10/4.85  tff(c_22157, plain, (![A_12]: (k1_relat_1(k7_relat_1('#skF_4', A_12))=A_12 | ~r1_tarski(A_12, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_21510, c_22153])).
% 12.10/4.85  tff(c_22487, plain, (![A_1113]: (A_1113='#skF_4' | ~r1_tarski(A_1113, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_22100, c_22087, c_22157])).
% 12.10/4.85  tff(c_22501, plain, ('#skF_3'='#skF_4'), inference(resolution, [status(thm)], [c_22106, c_22487])).
% 12.10/4.85  tff(c_22097, plain, (![A_4]: (m1_subset_1('#skF_4', k1_zfmisc_1(A_4)))), inference(demodulation, [status(thm), theory('equality')], [c_22082, c_21463])).
% 12.10/4.85  tff(c_22397, plain, (![A_1106, B_1107, C_1108, D_1109]: (k2_partfun1(A_1106, B_1107, C_1108, D_1109)=k7_relat_1(C_1108, D_1109) | ~m1_subset_1(C_1108, k1_zfmisc_1(k2_zfmisc_1(A_1106, B_1107))) | ~v1_funct_1(C_1108))), inference(cnfTransformation, [status(thm)], [f_127])).
% 12.10/4.85  tff(c_22402, plain, (![A_1106, B_1107, D_1109]: (k2_partfun1(A_1106, B_1107, '#skF_4', D_1109)=k7_relat_1('#skF_4', D_1109) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_22097, c_22397])).
% 12.10/4.85  tff(c_22406, plain, (![A_1106, B_1107, D_1109]: (k2_partfun1(A_1106, B_1107, '#skF_4', D_1109)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_22087, c_22402])).
% 12.10/4.85  tff(c_22280, plain, (![A_1087]: (A_1087='#skF_4' | ~r1_tarski(A_1087, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_22100, c_22087, c_22157])).
% 12.10/4.85  tff(c_22294, plain, ('#skF_3'='#skF_4'), inference(resolution, [status(thm)], [c_22106, c_22280])).
% 12.10/4.85  tff(c_21712, plain, (![C_1008, A_1009, B_1010]: (v1_xboole_0(C_1008) | ~m1_subset_1(C_1008, k1_zfmisc_1(k2_zfmisc_1(A_1009, B_1010))) | ~v1_xboole_0(A_1009))), inference(cnfTransformation, [status(thm)], [f_91])).
% 12.10/4.85  tff(c_21719, plain, (v1_xboole_0('#skF_4') | ~v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_21487, c_21712])).
% 12.10/4.85  tff(c_21724, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_21467, c_21719])).
% 12.10/4.85  tff(c_21730, plain, ('#skF_1'='#skF_4'), inference(resolution, [status(thm)], [c_21724, c_21492])).
% 12.10/4.85  tff(c_21745, plain, (![A_4]: (m1_subset_1('#skF_4', k1_zfmisc_1(A_4)))), inference(demodulation, [status(thm), theory('equality')], [c_21730, c_21463])).
% 12.10/4.85  tff(c_21957, plain, (![A_1035, B_1036, C_1037, D_1038]: (v1_funct_1(k2_partfun1(A_1035, B_1036, C_1037, D_1038)) | ~m1_subset_1(C_1037, k1_zfmisc_1(k2_zfmisc_1(A_1035, B_1036))) | ~v1_funct_1(C_1037))), inference(cnfTransformation, [status(thm)], [f_121])).
% 12.10/4.85  tff(c_21960, plain, (![A_1035, B_1036, D_1038]: (v1_funct_1(k2_partfun1(A_1035, B_1036, '#skF_4', D_1038)) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_21745, c_21957])).
% 12.10/4.85  tff(c_21963, plain, (![A_1035, B_1036, D_1038]: (v1_funct_1(k2_partfun1(A_1035, B_1036, '#skF_4', D_1038)))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_21960])).
% 12.10/4.85  tff(c_21754, plain, (r1_tarski('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_21730, c_64])).
% 12.10/4.85  tff(c_21748, plain, (k1_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_21730, c_21730, c_21465])).
% 12.10/4.85  tff(c_21532, plain, (![C_984, A_985, B_986]: (v4_relat_1(C_984, A_985) | ~m1_subset_1(C_984, k1_zfmisc_1(k2_zfmisc_1(A_985, B_986))))), inference(cnfTransformation, [status(thm)], [f_84])).
% 12.10/4.85  tff(c_21552, plain, (![A_989]: (v4_relat_1('#skF_1', A_989))), inference(resolution, [status(thm)], [c_21463, c_21532])).
% 12.10/4.85  tff(c_21555, plain, (![A_989]: (k7_relat_1('#skF_1', A_989)='#skF_1' | ~v1_relat_1('#skF_1'))), inference(resolution, [status(thm)], [c_21552, c_16])).
% 12.10/4.85  tff(c_21558, plain, (![A_989]: (k7_relat_1('#skF_1', A_989)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_21509, c_21555])).
% 12.10/4.85  tff(c_21736, plain, (![A_989]: (k7_relat_1('#skF_4', A_989)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_21730, c_21730, c_21558])).
% 12.10/4.85  tff(c_21816, plain, (![A_12]: (k1_relat_1(k7_relat_1('#skF_4', A_12))=A_12 | ~r1_tarski(A_12, '#skF_4') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_21748, c_22])).
% 12.10/4.85  tff(c_21820, plain, (![A_12]: (k1_relat_1(k7_relat_1('#skF_4', A_12))=A_12 | ~r1_tarski(A_12, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_21510, c_21816])).
% 12.10/4.85  tff(c_21926, plain, (![A_1033]: (A_1033='#skF_4' | ~r1_tarski(A_1033, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_21748, c_21736, c_21820])).
% 12.10/4.85  tff(c_21938, plain, ('#skF_3'='#skF_4'), inference(resolution, [status(thm)], [c_21754, c_21926])).
% 12.10/4.85  tff(c_21518, plain, (~m1_subset_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_1'))) | ~v1_funct_2(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_3'), '#skF_3', '#skF_1') | ~v1_funct_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_21472, c_21472, c_21472, c_21472, c_21472, c_60])).
% 12.10/4.85  tff(c_21519, plain, (~v1_funct_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_3'))), inference(splitLeft, [status(thm)], [c_21518])).
% 12.10/4.85  tff(c_21740, plain, (~v1_funct_1(k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_21730, c_21730, c_21519])).
% 12.10/4.85  tff(c_21942, plain, (~v1_funct_1(k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_21938, c_21740])).
% 12.10/4.85  tff(c_21966, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_21963, c_21942])).
% 12.10/4.85  tff(c_21967, plain, (~v1_funct_2(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_3'), '#skF_3', '#skF_1') | ~m1_subset_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_1')))), inference(splitRight, [status(thm)], [c_21518])).
% 12.10/4.85  tff(c_22244, plain, (~v1_funct_2(k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_3'), '#skF_3', '#skF_4') | ~m1_subset_1(k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_22082, c_22082, c_22082, c_22082, c_22082, c_22082, c_21967])).
% 12.10/4.85  tff(c_22245, plain, (~m1_subset_1(k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4')))), inference(splitLeft, [status(thm)], [c_22244])).
% 12.10/4.85  tff(c_22311, plain, (~m1_subset_1(k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_22294, c_22294, c_22245])).
% 12.10/4.85  tff(c_22408, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_22406, c_22311])).
% 12.10/4.85  tff(c_22412, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_22097, c_22408])).
% 12.10/4.85  tff(c_22414, plain, (m1_subset_1(k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4')))), inference(splitRight, [status(thm)], [c_22244])).
% 12.10/4.85  tff(c_32, plain, (![C_26, A_23, B_24]: (v1_xboole_0(C_26) | ~m1_subset_1(C_26, k1_zfmisc_1(k2_zfmisc_1(A_23, B_24))) | ~v1_xboole_0(A_23))), inference(cnfTransformation, [status(thm)], [f_91])).
% 12.10/4.85  tff(c_22473, plain, (v1_xboole_0(k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_3')) | ~v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_22414, c_32])).
% 12.10/4.85  tff(c_22525, plain, (v1_xboole_0(k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_22076, c_22501, c_22501, c_22473])).
% 12.10/4.85  tff(c_6, plain, (![B_3, A_2]: (~v1_xboole_0(B_3) | B_3=A_2 | ~v1_xboole_0(A_2))), inference(cnfTransformation, [status(thm)], [f_36])).
% 12.10/4.85  tff(c_22083, plain, (![A_2]: (A_2='#skF_4' | ~v1_xboole_0(A_2))), inference(resolution, [status(thm)], [c_22076, c_6])).
% 12.10/4.85  tff(c_22531, plain, (k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_4')='#skF_4'), inference(resolution, [status(thm)], [c_22525, c_22083])).
% 12.10/4.85  tff(c_22413, plain, (~v1_funct_2(k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_3'), '#skF_3', '#skF_4')), inference(splitRight, [status(thm)], [c_22244])).
% 12.10/4.85  tff(c_22507, plain, (~v1_funct_2(k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_4'), '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_22501, c_22501, c_22413])).
% 12.10/4.85  tff(c_22547, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_22239, c_22531, c_22507])).
% 12.10/4.85  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 12.10/4.85  
% 12.10/4.85  Inference rules
% 12.10/4.85  ----------------------
% 12.10/4.85  #Ref     : 0
% 12.10/4.85  #Sup     : 5001
% 12.10/4.85  #Fact    : 0
% 12.10/4.85  #Define  : 0
% 12.10/4.85  #Split   : 22
% 12.10/4.85  #Chain   : 0
% 12.10/4.85  #Close   : 0
% 12.10/4.85  
% 12.10/4.85  Ordering : KBO
% 12.10/4.85  
% 12.10/4.85  Simplification rules
% 12.10/4.85  ----------------------
% 12.10/4.85  #Subsume      : 1233
% 12.10/4.85  #Demod        : 9932
% 12.10/4.85  #Tautology    : 2246
% 12.10/4.85  #SimpNegUnit  : 170
% 12.10/4.85  #BackRed      : 155
% 12.10/4.85  
% 12.10/4.85  #Partial instantiations: 0
% 12.10/4.85  #Strategies tried      : 1
% 12.10/4.85  
% 12.10/4.85  Timing (in seconds)
% 12.10/4.85  ----------------------
% 12.10/4.85  Preprocessing        : 0.32
% 12.10/4.85  Parsing              : 0.17
% 12.10/4.85  CNF conversion       : 0.02
% 12.10/4.85  Main loop            : 3.65
% 12.10/4.85  Inferencing          : 0.95
% 12.10/4.85  Reduction            : 1.66
% 12.10/4.85  Demodulation         : 1.34
% 12.10/4.85  BG Simplification    : 0.09
% 12.10/4.85  Subsumption          : 0.76
% 12.10/4.85  Abstraction          : 0.14
% 12.10/4.85  MUC search           : 0.00
% 12.10/4.85  Cooper               : 0.00
% 12.10/4.85  Total                : 4.05
% 12.10/4.85  Index Insertion      : 0.00
% 12.10/4.85  Index Deletion       : 0.00
% 12.10/4.85  Index Matching       : 0.00
% 12.10/4.85  BG Taut test         : 0.00
%------------------------------------------------------------------------------
