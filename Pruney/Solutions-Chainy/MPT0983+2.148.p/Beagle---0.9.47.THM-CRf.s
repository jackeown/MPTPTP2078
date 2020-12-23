%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:12:23 EST 2020

% Result     : Theorem 8.61s
% Output     : CNFRefutation 8.61s
% Verified   : 
% Statistics : Number of formulae       :  168 ( 707 expanded)
%              Number of leaves         :   46 ( 256 expanded)
%              Depth                    :   12
%              Number of atoms          :  316 (1832 expanded)
%              Number of equality atoms :   82 ( 456 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > v1_partfun1 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

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

tff(v2_funct_2,type,(
    v2_funct_2: ( $i * $i ) > $o )).

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

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_127,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_77,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v2_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_funct_1)).

tff(f_169,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ! [D] :
            ( ( v1_funct_1(D)
              & v1_funct_2(D,B,A)
              & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,A))) )
           => ( r2_relset_1(A,A,k1_partfun1(A,B,B,A,C,D),k6_partfun1(A))
             => ( v2_funct_1(C)
                & v2_funct_2(D,A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_funct_2)).

tff(f_125,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_111,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( v1_funct_1(k1_partfun1(A,B,C,D,E,F))
        & m1_subset_1(k1_partfun1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).

tff(f_115,axiom,(
    ! [A] :
      ( v1_partfun1(k6_partfun1(A),A)
      & m1_subset_1(k6_partfun1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_partfun1)).

tff(f_91,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_73,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_69,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ( k1_relat_1(A) = k1_xboole_0
          | k2_relat_1(A) = k1_xboole_0 )
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).

tff(f_149,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ! [E] :
          ( ( v1_funct_1(E)
            & v1_funct_2(E,B,C)
            & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(B,C))) )
         => ( v2_funct_1(k1_partfun1(A,B,B,C,D,E))
           => ( ( C = k1_xboole_0
                & B != k1_xboole_0 )
              | v2_funct_1(D) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_funct_2)).

tff(f_54,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_40,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_83,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_46,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_33,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_52,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_61,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => r1_tarski(k2_relat_1(k5_relat_1(A,B)),k2_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_relat_1)).

tff(f_99,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A) )
     => ( v2_funct_2(B,A)
      <=> k2_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_funct_2)).

tff(c_58,plain,(
    ! [A_41] : k6_relat_1(A_41) = k6_partfun1(A_41) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_34,plain,(
    ! [A_18] : v2_funct_1(k6_relat_1(A_18)) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_79,plain,(
    ! [A_18] : v2_funct_1(k6_partfun1(A_18)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_34])).

tff(c_78,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_169])).

tff(c_74,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_169])).

tff(c_72,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_169])).

tff(c_68,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_169])).

tff(c_967,plain,(
    ! [D_168,C_166,E_167,F_165,A_164,B_169] :
      ( k1_partfun1(A_164,B_169,C_166,D_168,E_167,F_165) = k5_relat_1(E_167,F_165)
      | ~ m1_subset_1(F_165,k1_zfmisc_1(k2_zfmisc_1(C_166,D_168)))
      | ~ v1_funct_1(F_165)
      | ~ m1_subset_1(E_167,k1_zfmisc_1(k2_zfmisc_1(A_164,B_169)))
      | ~ v1_funct_1(E_167) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_973,plain,(
    ! [A_164,B_169,E_167] :
      ( k1_partfun1(A_164,B_169,'#skF_2','#skF_1',E_167,'#skF_4') = k5_relat_1(E_167,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_167,k1_zfmisc_1(k2_zfmisc_1(A_164,B_169)))
      | ~ v1_funct_1(E_167) ) ),
    inference(resolution,[status(thm)],[c_68,c_967])).

tff(c_1169,plain,(
    ! [A_187,B_188,E_189] :
      ( k1_partfun1(A_187,B_188,'#skF_2','#skF_1',E_189,'#skF_4') = k5_relat_1(E_189,'#skF_4')
      | ~ m1_subset_1(E_189,k1_zfmisc_1(k2_zfmisc_1(A_187,B_188)))
      | ~ v1_funct_1(E_189) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_973])).

tff(c_1184,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_74,c_1169])).

tff(c_1193,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_1184])).

tff(c_48,plain,(
    ! [C_30,E_32,D_31,B_29,F_33,A_28] :
      ( m1_subset_1(k1_partfun1(A_28,B_29,C_30,D_31,E_32,F_33),k1_zfmisc_1(k2_zfmisc_1(A_28,D_31)))
      | ~ m1_subset_1(F_33,k1_zfmisc_1(k2_zfmisc_1(C_30,D_31)))
      | ~ v1_funct_1(F_33)
      | ~ m1_subset_1(E_32,k1_zfmisc_1(k2_zfmisc_1(A_28,B_29)))
      | ~ v1_funct_1(E_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_1288,plain,
    ( m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1193,c_48])).

tff(c_1292,plain,(
    m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_74,c_72,c_68,c_1288])).

tff(c_54,plain,(
    ! [A_34] : m1_subset_1(k6_partfun1(A_34),k1_zfmisc_1(k2_zfmisc_1(A_34,A_34))) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_66,plain,(
    r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k6_partfun1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_169])).

tff(c_751,plain,(
    ! [D_132,C_133,A_134,B_135] :
      ( D_132 = C_133
      | ~ r2_relset_1(A_134,B_135,C_133,D_132)
      | ~ m1_subset_1(D_132,k1_zfmisc_1(k2_zfmisc_1(A_134,B_135)))
      | ~ m1_subset_1(C_133,k1_zfmisc_1(k2_zfmisc_1(A_134,B_135))) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_761,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_66,c_751])).

tff(c_778,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_761])).

tff(c_1785,plain,(
    k5_relat_1('#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1292,c_1193,c_1193,c_778])).

tff(c_64,plain,
    ( ~ v2_funct_2('#skF_4','#skF_1')
    | ~ v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_169])).

tff(c_89,plain,(
    ~ v2_funct_1('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_64])).

tff(c_30,plain,(
    ! [A_17] : k2_relat_1(k6_relat_1(A_17)) = A_17 ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_81,plain,(
    ! [A_17] : k2_relat_1(k6_partfun1(A_17)) = A_17 ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_30])).

tff(c_32,plain,(
    ! [A_18] : v1_relat_1(k6_relat_1(A_18)) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_80,plain,(
    ! [A_18] : v1_relat_1(k6_partfun1(A_18)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_32])).

tff(c_118,plain,(
    ! [A_59] :
      ( k2_relat_1(A_59) != k1_xboole_0
      | k1_xboole_0 = A_59
      | ~ v1_relat_1(A_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_124,plain,(
    ! [A_18] :
      ( k2_relat_1(k6_partfun1(A_18)) != k1_xboole_0
      | k6_partfun1(A_18) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_80,c_118])).

tff(c_127,plain,(
    ! [A_18] :
      ( k1_xboole_0 != A_18
      | k6_partfun1(A_18) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_81,c_124])).

tff(c_153,plain,
    ( r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_xboole_0)
    | k1_xboole_0 != '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_127,c_66])).

tff(c_187,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_153])).

tff(c_76,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_169])).

tff(c_70,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_169])).

tff(c_1355,plain,(
    ! [E_197,D_194,C_198,A_196,B_195] :
      ( k1_xboole_0 = C_198
      | v2_funct_1(D_194)
      | ~ v2_funct_1(k1_partfun1(A_196,B_195,B_195,C_198,D_194,E_197))
      | ~ m1_subset_1(E_197,k1_zfmisc_1(k2_zfmisc_1(B_195,C_198)))
      | ~ v1_funct_2(E_197,B_195,C_198)
      | ~ v1_funct_1(E_197)
      | ~ m1_subset_1(D_194,k1_zfmisc_1(k2_zfmisc_1(A_196,B_195)))
      | ~ v1_funct_2(D_194,A_196,B_195)
      | ~ v1_funct_1(D_194) ) ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_1357,plain,
    ( k1_xboole_0 = '#skF_1'
    | v2_funct_1('#skF_3')
    | ~ v2_funct_1(k5_relat_1('#skF_3','#skF_4'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1193,c_1355])).

tff(c_1359,plain,
    ( k1_xboole_0 = '#skF_1'
    | v2_funct_1('#skF_3')
    | ~ v2_funct_1(k5_relat_1('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_74,c_72,c_70,c_68,c_1357])).

tff(c_1360,plain,(
    ~ v2_funct_1(k5_relat_1('#skF_3','#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_89,c_187,c_1359])).

tff(c_1791,plain,(
    ~ v2_funct_1(k6_partfun1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1785,c_1360])).

tff(c_1804,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_79,c_1791])).

tff(c_1806,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_153])).

tff(c_129,plain,(
    ! [A_60] :
      ( k1_xboole_0 != A_60
      | k6_partfun1(A_60) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_81,c_124])).

tff(c_145,plain,(
    ! [A_60] :
      ( v2_funct_1(k1_xboole_0)
      | k1_xboole_0 != A_60 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_129,c_79])).

tff(c_167,plain,(
    ! [A_60] : k1_xboole_0 != A_60 ),
    inference(splitLeft,[status(thm)],[c_145])).

tff(c_173,plain,(
    $false ),
    inference(reflexivity,[status(thm),theory(equality)],[c_167])).

tff(c_174,plain,(
    v2_funct_1(k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_145])).

tff(c_1809,plain,(
    v2_funct_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1806,c_174])).

tff(c_135,plain,(
    ! [A_60] :
      ( k2_relat_1(k1_xboole_0) = A_60
      | k1_xboole_0 != A_60 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_129,c_81])).

tff(c_1876,plain,(
    k2_relat_1('#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1806,c_1806,c_135])).

tff(c_20,plain,(
    ! [A_11,B_12] : v1_relat_1(k2_zfmisc_1(A_11,B_12)) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_1900,plain,(
    ! [B_219,A_220] :
      ( v1_relat_1(B_219)
      | ~ m1_subset_1(B_219,k1_zfmisc_1(A_220))
      | ~ v1_relat_1(A_220) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_1909,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_74,c_1900])).

tff(c_1918,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_1909])).

tff(c_26,plain,(
    ! [A_16] :
      ( k1_relat_1(A_16) != k1_xboole_0
      | k1_xboole_0 = A_16
      | ~ v1_relat_1(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_1826,plain,(
    ! [A_16] :
      ( k1_relat_1(A_16) != '#skF_1'
      | A_16 = '#skF_1'
      | ~ v1_relat_1(A_16) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1806,c_1806,c_26])).

tff(c_1944,plain,
    ( k1_relat_1('#skF_3') != '#skF_1'
    | '#skF_3' = '#skF_1' ),
    inference(resolution,[status(thm)],[c_1918,c_1826])).

tff(c_1973,plain,(
    k1_relat_1('#skF_3') != '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_1944])).

tff(c_1980,plain,(
    ! [C_227,A_228,B_229] :
      ( v4_relat_1(C_227,A_228)
      | ~ m1_subset_1(C_227,k1_zfmisc_1(k2_zfmisc_1(A_228,B_229))) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_1992,plain,(
    v4_relat_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_74,c_1980])).

tff(c_2136,plain,(
    ! [B_254,A_255] :
      ( r1_tarski(k1_relat_1(B_254),A_255)
      | ~ v4_relat_1(B_254,A_255)
      | ~ v1_relat_1(B_254) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_8,plain,(
    ! [A_3] : r1_tarski(k1_xboole_0,A_3) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_1813,plain,(
    ! [A_3] : r1_tarski('#skF_1',A_3) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1806,c_8])).

tff(c_1927,plain,(
    ! [B_221,A_222] :
      ( B_221 = A_222
      | ~ r1_tarski(B_221,A_222)
      | ~ r1_tarski(A_222,B_221) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_1932,plain,(
    ! [A_3] :
      ( A_3 = '#skF_1'
      | ~ r1_tarski(A_3,'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_1813,c_1927])).

tff(c_2302,plain,(
    ! [B_272] :
      ( k1_relat_1(B_272) = '#skF_1'
      | ~ v4_relat_1(B_272,'#skF_1')
      | ~ v1_relat_1(B_272) ) ),
    inference(resolution,[status(thm)],[c_2136,c_1932])).

tff(c_2317,plain,
    ( k1_relat_1('#skF_3') = '#skF_1'
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_1992,c_2302])).

tff(c_2329,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1918,c_2317])).

tff(c_2331,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1973,c_2329])).

tff(c_2332,plain,(
    '#skF_3' = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_1944])).

tff(c_24,plain,(
    ! [A_16] :
      ( k2_relat_1(A_16) != k1_xboole_0
      | k1_xboole_0 = A_16
      | ~ v1_relat_1(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_1812,plain,(
    ! [A_16] :
      ( k2_relat_1(A_16) != '#skF_1'
      | A_16 = '#skF_1'
      | ~ v1_relat_1(A_16) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1806,c_1806,c_24])).

tff(c_1943,plain,
    ( k2_relat_1('#skF_3') != '#skF_1'
    | '#skF_3' = '#skF_1' ),
    inference(resolution,[status(thm)],[c_1918,c_1812])).

tff(c_1947,plain,(
    k2_relat_1('#skF_3') != '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_1943])).

tff(c_2334,plain,(
    k2_relat_1('#skF_1') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2332,c_1947])).

tff(c_2343,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1876,c_2334])).

tff(c_2344,plain,(
    '#skF_3' = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_1943])).

tff(c_2349,plain,(
    ~ v2_funct_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2344,c_89])).

tff(c_2355,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1809,c_2349])).

tff(c_2356,plain,(
    ~ v2_funct_2('#skF_4','#skF_1') ),
    inference(splitRight,[status(thm)],[c_64])).

tff(c_2502,plain,(
    ! [B_287,A_288] :
      ( v1_relat_1(B_287)
      | ~ m1_subset_1(B_287,k1_zfmisc_1(A_288))
      | ~ v1_relat_1(A_288) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_2508,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_1')) ),
    inference(resolution,[status(thm)],[c_68,c_2502])).

tff(c_2517,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_2508])).

tff(c_2554,plain,(
    ! [C_292,B_293,A_294] :
      ( v5_relat_1(C_292,B_293)
      | ~ m1_subset_1(C_292,k1_zfmisc_1(k2_zfmisc_1(A_294,B_293))) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_2565,plain,(
    v5_relat_1('#skF_4','#skF_1') ),
    inference(resolution,[status(thm)],[c_68,c_2554])).

tff(c_18,plain,(
    ! [B_10,A_9] :
      ( r1_tarski(k2_relat_1(B_10),A_9)
      | ~ v5_relat_1(B_10,A_9)
      | ~ v1_relat_1(B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_2511,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_74,c_2502])).

tff(c_2520,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_2511])).

tff(c_3275,plain,(
    ! [E_385,F_383,C_384,D_386,B_387,A_382] :
      ( k1_partfun1(A_382,B_387,C_384,D_386,E_385,F_383) = k5_relat_1(E_385,F_383)
      | ~ m1_subset_1(F_383,k1_zfmisc_1(k2_zfmisc_1(C_384,D_386)))
      | ~ v1_funct_1(F_383)
      | ~ m1_subset_1(E_385,k1_zfmisc_1(k2_zfmisc_1(A_382,B_387)))
      | ~ v1_funct_1(E_385) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_3281,plain,(
    ! [A_382,B_387,E_385] :
      ( k1_partfun1(A_382,B_387,'#skF_2','#skF_1',E_385,'#skF_4') = k5_relat_1(E_385,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_385,k1_zfmisc_1(k2_zfmisc_1(A_382,B_387)))
      | ~ v1_funct_1(E_385) ) ),
    inference(resolution,[status(thm)],[c_68,c_3275])).

tff(c_3425,plain,(
    ! [A_405,B_406,E_407] :
      ( k1_partfun1(A_405,B_406,'#skF_2','#skF_1',E_407,'#skF_4') = k5_relat_1(E_407,'#skF_4')
      | ~ m1_subset_1(E_407,k1_zfmisc_1(k2_zfmisc_1(A_405,B_406)))
      | ~ v1_funct_1(E_407) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_3281])).

tff(c_3440,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_74,c_3425])).

tff(c_3449,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_3440])).

tff(c_3538,plain,
    ( m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_3449,c_48])).

tff(c_3542,plain,(
    m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_74,c_72,c_68,c_3538])).

tff(c_3022,plain,(
    ! [D_351,C_352,A_353,B_354] :
      ( D_351 = C_352
      | ~ r2_relset_1(A_353,B_354,C_352,D_351)
      | ~ m1_subset_1(D_351,k1_zfmisc_1(k2_zfmisc_1(A_353,B_354)))
      | ~ m1_subset_1(C_352,k1_zfmisc_1(k2_zfmisc_1(A_353,B_354))) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_3036,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_66,c_3022])).

tff(c_3059,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_3036])).

tff(c_3089,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_3059])).

tff(c_3879,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3542,c_3449,c_3089])).

tff(c_3880,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_3059])).

tff(c_4055,plain,(
    ! [A_449,E_452,F_450,D_453,B_454,C_451] :
      ( k1_partfun1(A_449,B_454,C_451,D_453,E_452,F_450) = k5_relat_1(E_452,F_450)
      | ~ m1_subset_1(F_450,k1_zfmisc_1(k2_zfmisc_1(C_451,D_453)))
      | ~ v1_funct_1(F_450)
      | ~ m1_subset_1(E_452,k1_zfmisc_1(k2_zfmisc_1(A_449,B_454)))
      | ~ v1_funct_1(E_452) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_4061,plain,(
    ! [A_449,B_454,E_452] :
      ( k1_partfun1(A_449,B_454,'#skF_2','#skF_1',E_452,'#skF_4') = k5_relat_1(E_452,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_452,k1_zfmisc_1(k2_zfmisc_1(A_449,B_454)))
      | ~ v1_funct_1(E_452) ) ),
    inference(resolution,[status(thm)],[c_68,c_4055])).

tff(c_4230,plain,(
    ! [A_474,B_475,E_476] :
      ( k1_partfun1(A_474,B_475,'#skF_2','#skF_1',E_476,'#skF_4') = k5_relat_1(E_476,'#skF_4')
      | ~ m1_subset_1(E_476,k1_zfmisc_1(k2_zfmisc_1(A_474,B_475)))
      | ~ v1_funct_1(E_476) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_4061])).

tff(c_4245,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_74,c_4230])).

tff(c_4254,plain,(
    k5_relat_1('#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_3880,c_4245])).

tff(c_22,plain,(
    ! [A_13,B_15] :
      ( r1_tarski(k2_relat_1(k5_relat_1(A_13,B_15)),k2_relat_1(B_15))
      | ~ v1_relat_1(B_15)
      | ~ v1_relat_1(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_4258,plain,
    ( r1_tarski(k2_relat_1(k6_partfun1('#skF_1')),k2_relat_1('#skF_4'))
    | ~ v1_relat_1('#skF_4')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_4254,c_22])).

tff(c_4262,plain,(
    r1_tarski('#skF_1',k2_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2520,c_2517,c_81,c_4258])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_4270,plain,
    ( k2_relat_1('#skF_4') = '#skF_1'
    | ~ r1_tarski(k2_relat_1('#skF_4'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_4262,c_2])).

tff(c_4271,plain,(
    ~ r1_tarski(k2_relat_1('#skF_4'),'#skF_1') ),
    inference(splitLeft,[status(thm)],[c_4270])).

tff(c_4277,plain,
    ( ~ v5_relat_1('#skF_4','#skF_1')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_18,c_4271])).

tff(c_4282,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2517,c_2565,c_4277])).

tff(c_4283,plain,(
    k2_relat_1('#skF_4') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_4270])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_2756,plain,(
    ! [B_320,A_321] :
      ( v5_relat_1(B_320,A_321)
      | ~ r1_tarski(k2_relat_1(B_320),A_321)
      | ~ v1_relat_1(B_320) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_2780,plain,(
    ! [B_320] :
      ( v5_relat_1(B_320,k2_relat_1(B_320))
      | ~ v1_relat_1(B_320) ) ),
    inference(resolution,[status(thm)],[c_6,c_2756])).

tff(c_2853,plain,(
    ! [B_330] :
      ( v2_funct_2(B_330,k2_relat_1(B_330))
      | ~ v5_relat_1(B_330,k2_relat_1(B_330))
      | ~ v1_relat_1(B_330) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_2871,plain,(
    ! [B_320] :
      ( v2_funct_2(B_320,k2_relat_1(B_320))
      | ~ v1_relat_1(B_320) ) ),
    inference(resolution,[status(thm)],[c_2780,c_2853])).

tff(c_4295,plain,
    ( v2_funct_2('#skF_4','#skF_1')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_4283,c_2871])).

tff(c_4310,plain,(
    v2_funct_2('#skF_4','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2517,c_4295])).

tff(c_4312,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2356,c_4310])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n012.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 20:55:37 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.61/3.26  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.61/3.28  
% 8.61/3.28  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.61/3.28  %$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > v1_partfun1 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 8.61/3.28  
% 8.61/3.28  %Foreground sorts:
% 8.61/3.28  
% 8.61/3.28  
% 8.61/3.28  %Background operators:
% 8.61/3.28  
% 8.61/3.28  
% 8.61/3.28  %Foreground operators:
% 8.61/3.28  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 8.61/3.28  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 8.61/3.28  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.61/3.28  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 8.61/3.28  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 8.61/3.28  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 8.61/3.28  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 8.61/3.28  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 8.61/3.28  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 8.61/3.28  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 8.61/3.28  tff('#skF_2', type, '#skF_2': $i).
% 8.61/3.28  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 8.61/3.28  tff('#skF_3', type, '#skF_3': $i).
% 8.61/3.28  tff('#skF_1', type, '#skF_1': $i).
% 8.61/3.28  tff(v2_funct_2, type, v2_funct_2: ($i * $i) > $o).
% 8.61/3.28  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 8.61/3.28  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 8.61/3.28  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 8.61/3.28  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.61/3.28  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 8.61/3.28  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 8.61/3.28  tff('#skF_4', type, '#skF_4': $i).
% 8.61/3.28  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 8.61/3.28  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.61/3.28  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 8.61/3.28  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 8.61/3.28  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 8.61/3.28  
% 8.61/3.32  tff(f_127, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 8.61/3.32  tff(f_77, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v2_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc4_funct_1)).
% 8.61/3.32  tff(f_169, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (r2_relset_1(A, A, k1_partfun1(A, B, B, A, C, D), k6_partfun1(A)) => (v2_funct_1(C) & v2_funct_2(D, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_funct_2)).
% 8.61/3.32  tff(f_125, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 8.61/3.32  tff(f_111, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (v1_funct_1(k1_partfun1(A, B, C, D, E, F)) & m1_subset_1(k1_partfun1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 8.61/3.32  tff(f_115, axiom, (![A]: (v1_partfun1(k6_partfun1(A), A) & m1_subset_1(k6_partfun1(A), k1_zfmisc_1(k2_zfmisc_1(A, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_partfun1)).
% 8.61/3.32  tff(f_91, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 8.61/3.32  tff(f_73, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 8.61/3.32  tff(f_69, axiom, (![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_relat_1)).
% 8.61/3.32  tff(f_149, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, B, C)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (v2_funct_1(k1_partfun1(A, B, B, C, D, E)) => (((C = k1_xboole_0) & ~(B = k1_xboole_0)) | v2_funct_1(D))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t26_funct_2)).
% 8.61/3.32  tff(f_54, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 8.61/3.32  tff(f_40, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 8.61/3.32  tff(f_83, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 8.61/3.32  tff(f_46, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d18_relat_1)).
% 8.61/3.32  tff(f_33, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 8.61/3.32  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 8.61/3.32  tff(f_52, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 8.61/3.32  tff(f_61, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => r1_tarski(k2_relat_1(k5_relat_1(A, B)), k2_relat_1(B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t45_relat_1)).
% 8.61/3.32  tff(f_99, axiom, (![A, B]: ((v1_relat_1(B) & v5_relat_1(B, A)) => (v2_funct_2(B, A) <=> (k2_relat_1(B) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_funct_2)).
% 8.61/3.32  tff(c_58, plain, (![A_41]: (k6_relat_1(A_41)=k6_partfun1(A_41))), inference(cnfTransformation, [status(thm)], [f_127])).
% 8.61/3.32  tff(c_34, plain, (![A_18]: (v2_funct_1(k6_relat_1(A_18)))), inference(cnfTransformation, [status(thm)], [f_77])).
% 8.61/3.32  tff(c_79, plain, (![A_18]: (v2_funct_1(k6_partfun1(A_18)))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_34])).
% 8.61/3.32  tff(c_78, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_169])).
% 8.61/3.32  tff(c_74, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_169])).
% 8.61/3.32  tff(c_72, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_169])).
% 8.61/3.32  tff(c_68, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_169])).
% 8.61/3.32  tff(c_967, plain, (![D_168, C_166, E_167, F_165, A_164, B_169]: (k1_partfun1(A_164, B_169, C_166, D_168, E_167, F_165)=k5_relat_1(E_167, F_165) | ~m1_subset_1(F_165, k1_zfmisc_1(k2_zfmisc_1(C_166, D_168))) | ~v1_funct_1(F_165) | ~m1_subset_1(E_167, k1_zfmisc_1(k2_zfmisc_1(A_164, B_169))) | ~v1_funct_1(E_167))), inference(cnfTransformation, [status(thm)], [f_125])).
% 8.61/3.32  tff(c_973, plain, (![A_164, B_169, E_167]: (k1_partfun1(A_164, B_169, '#skF_2', '#skF_1', E_167, '#skF_4')=k5_relat_1(E_167, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_167, k1_zfmisc_1(k2_zfmisc_1(A_164, B_169))) | ~v1_funct_1(E_167))), inference(resolution, [status(thm)], [c_68, c_967])).
% 8.61/3.32  tff(c_1169, plain, (![A_187, B_188, E_189]: (k1_partfun1(A_187, B_188, '#skF_2', '#skF_1', E_189, '#skF_4')=k5_relat_1(E_189, '#skF_4') | ~m1_subset_1(E_189, k1_zfmisc_1(k2_zfmisc_1(A_187, B_188))) | ~v1_funct_1(E_189))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_973])).
% 8.61/3.32  tff(c_1184, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_74, c_1169])).
% 8.61/3.32  tff(c_1193, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_1184])).
% 8.61/3.32  tff(c_48, plain, (![C_30, E_32, D_31, B_29, F_33, A_28]: (m1_subset_1(k1_partfun1(A_28, B_29, C_30, D_31, E_32, F_33), k1_zfmisc_1(k2_zfmisc_1(A_28, D_31))) | ~m1_subset_1(F_33, k1_zfmisc_1(k2_zfmisc_1(C_30, D_31))) | ~v1_funct_1(F_33) | ~m1_subset_1(E_32, k1_zfmisc_1(k2_zfmisc_1(A_28, B_29))) | ~v1_funct_1(E_32))), inference(cnfTransformation, [status(thm)], [f_111])).
% 8.61/3.32  tff(c_1288, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1193, c_48])).
% 8.61/3.32  tff(c_1292, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_74, c_72, c_68, c_1288])).
% 8.61/3.32  tff(c_54, plain, (![A_34]: (m1_subset_1(k6_partfun1(A_34), k1_zfmisc_1(k2_zfmisc_1(A_34, A_34))))), inference(cnfTransformation, [status(thm)], [f_115])).
% 8.61/3.32  tff(c_66, plain, (r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k6_partfun1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_169])).
% 8.61/3.32  tff(c_751, plain, (![D_132, C_133, A_134, B_135]: (D_132=C_133 | ~r2_relset_1(A_134, B_135, C_133, D_132) | ~m1_subset_1(D_132, k1_zfmisc_1(k2_zfmisc_1(A_134, B_135))) | ~m1_subset_1(C_133, k1_zfmisc_1(k2_zfmisc_1(A_134, B_135))))), inference(cnfTransformation, [status(thm)], [f_91])).
% 8.61/3.32  tff(c_761, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_66, c_751])).
% 8.61/3.32  tff(c_778, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_761])).
% 8.61/3.32  tff(c_1785, plain, (k5_relat_1('#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1292, c_1193, c_1193, c_778])).
% 8.61/3.32  tff(c_64, plain, (~v2_funct_2('#skF_4', '#skF_1') | ~v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_169])).
% 8.61/3.32  tff(c_89, plain, (~v2_funct_1('#skF_3')), inference(splitLeft, [status(thm)], [c_64])).
% 8.61/3.32  tff(c_30, plain, (![A_17]: (k2_relat_1(k6_relat_1(A_17))=A_17)), inference(cnfTransformation, [status(thm)], [f_73])).
% 8.61/3.32  tff(c_81, plain, (![A_17]: (k2_relat_1(k6_partfun1(A_17))=A_17)), inference(demodulation, [status(thm), theory('equality')], [c_58, c_30])).
% 8.61/3.32  tff(c_32, plain, (![A_18]: (v1_relat_1(k6_relat_1(A_18)))), inference(cnfTransformation, [status(thm)], [f_77])).
% 8.61/3.32  tff(c_80, plain, (![A_18]: (v1_relat_1(k6_partfun1(A_18)))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_32])).
% 8.61/3.32  tff(c_118, plain, (![A_59]: (k2_relat_1(A_59)!=k1_xboole_0 | k1_xboole_0=A_59 | ~v1_relat_1(A_59))), inference(cnfTransformation, [status(thm)], [f_69])).
% 8.61/3.32  tff(c_124, plain, (![A_18]: (k2_relat_1(k6_partfun1(A_18))!=k1_xboole_0 | k6_partfun1(A_18)=k1_xboole_0)), inference(resolution, [status(thm)], [c_80, c_118])).
% 8.61/3.32  tff(c_127, plain, (![A_18]: (k1_xboole_0!=A_18 | k6_partfun1(A_18)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_81, c_124])).
% 8.61/3.32  tff(c_153, plain, (r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_xboole_0) | k1_xboole_0!='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_127, c_66])).
% 8.61/3.32  tff(c_187, plain, (k1_xboole_0!='#skF_1'), inference(splitLeft, [status(thm)], [c_153])).
% 8.61/3.32  tff(c_76, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_169])).
% 8.61/3.32  tff(c_70, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_169])).
% 8.61/3.32  tff(c_1355, plain, (![E_197, D_194, C_198, A_196, B_195]: (k1_xboole_0=C_198 | v2_funct_1(D_194) | ~v2_funct_1(k1_partfun1(A_196, B_195, B_195, C_198, D_194, E_197)) | ~m1_subset_1(E_197, k1_zfmisc_1(k2_zfmisc_1(B_195, C_198))) | ~v1_funct_2(E_197, B_195, C_198) | ~v1_funct_1(E_197) | ~m1_subset_1(D_194, k1_zfmisc_1(k2_zfmisc_1(A_196, B_195))) | ~v1_funct_2(D_194, A_196, B_195) | ~v1_funct_1(D_194))), inference(cnfTransformation, [status(thm)], [f_149])).
% 8.61/3.32  tff(c_1357, plain, (k1_xboole_0='#skF_1' | v2_funct_1('#skF_3') | ~v2_funct_1(k5_relat_1('#skF_3', '#skF_4')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1193, c_1355])).
% 8.61/3.32  tff(c_1359, plain, (k1_xboole_0='#skF_1' | v2_funct_1('#skF_3') | ~v2_funct_1(k5_relat_1('#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_74, c_72, c_70, c_68, c_1357])).
% 8.61/3.32  tff(c_1360, plain, (~v2_funct_1(k5_relat_1('#skF_3', '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_89, c_187, c_1359])).
% 8.61/3.32  tff(c_1791, plain, (~v2_funct_1(k6_partfun1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_1785, c_1360])).
% 8.61/3.32  tff(c_1804, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_79, c_1791])).
% 8.61/3.32  tff(c_1806, plain, (k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_153])).
% 8.61/3.32  tff(c_129, plain, (![A_60]: (k1_xboole_0!=A_60 | k6_partfun1(A_60)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_81, c_124])).
% 8.61/3.32  tff(c_145, plain, (![A_60]: (v2_funct_1(k1_xboole_0) | k1_xboole_0!=A_60)), inference(superposition, [status(thm), theory('equality')], [c_129, c_79])).
% 8.61/3.32  tff(c_167, plain, (![A_60]: (k1_xboole_0!=A_60)), inference(splitLeft, [status(thm)], [c_145])).
% 8.61/3.32  tff(c_173, plain, $false, inference(reflexivity, [status(thm), theory('equality')], [c_167])).
% 8.61/3.32  tff(c_174, plain, (v2_funct_1(k1_xboole_0)), inference(splitRight, [status(thm)], [c_145])).
% 8.61/3.32  tff(c_1809, plain, (v2_funct_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1806, c_174])).
% 8.61/3.32  tff(c_135, plain, (![A_60]: (k2_relat_1(k1_xboole_0)=A_60 | k1_xboole_0!=A_60)), inference(superposition, [status(thm), theory('equality')], [c_129, c_81])).
% 8.61/3.32  tff(c_1876, plain, (k2_relat_1('#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_1806, c_1806, c_135])).
% 8.61/3.32  tff(c_20, plain, (![A_11, B_12]: (v1_relat_1(k2_zfmisc_1(A_11, B_12)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 8.61/3.32  tff(c_1900, plain, (![B_219, A_220]: (v1_relat_1(B_219) | ~m1_subset_1(B_219, k1_zfmisc_1(A_220)) | ~v1_relat_1(A_220))), inference(cnfTransformation, [status(thm)], [f_40])).
% 8.61/3.32  tff(c_1909, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_74, c_1900])).
% 8.61/3.32  tff(c_1918, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_20, c_1909])).
% 8.61/3.32  tff(c_26, plain, (![A_16]: (k1_relat_1(A_16)!=k1_xboole_0 | k1_xboole_0=A_16 | ~v1_relat_1(A_16))), inference(cnfTransformation, [status(thm)], [f_69])).
% 8.61/3.32  tff(c_1826, plain, (![A_16]: (k1_relat_1(A_16)!='#skF_1' | A_16='#skF_1' | ~v1_relat_1(A_16))), inference(demodulation, [status(thm), theory('equality')], [c_1806, c_1806, c_26])).
% 8.61/3.32  tff(c_1944, plain, (k1_relat_1('#skF_3')!='#skF_1' | '#skF_3'='#skF_1'), inference(resolution, [status(thm)], [c_1918, c_1826])).
% 8.61/3.32  tff(c_1973, plain, (k1_relat_1('#skF_3')!='#skF_1'), inference(splitLeft, [status(thm)], [c_1944])).
% 8.61/3.32  tff(c_1980, plain, (![C_227, A_228, B_229]: (v4_relat_1(C_227, A_228) | ~m1_subset_1(C_227, k1_zfmisc_1(k2_zfmisc_1(A_228, B_229))))), inference(cnfTransformation, [status(thm)], [f_83])).
% 8.61/3.32  tff(c_1992, plain, (v4_relat_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_74, c_1980])).
% 8.61/3.32  tff(c_2136, plain, (![B_254, A_255]: (r1_tarski(k1_relat_1(B_254), A_255) | ~v4_relat_1(B_254, A_255) | ~v1_relat_1(B_254))), inference(cnfTransformation, [status(thm)], [f_46])).
% 8.61/3.32  tff(c_8, plain, (![A_3]: (r1_tarski(k1_xboole_0, A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 8.61/3.32  tff(c_1813, plain, (![A_3]: (r1_tarski('#skF_1', A_3))), inference(demodulation, [status(thm), theory('equality')], [c_1806, c_8])).
% 8.61/3.32  tff(c_1927, plain, (![B_221, A_222]: (B_221=A_222 | ~r1_tarski(B_221, A_222) | ~r1_tarski(A_222, B_221))), inference(cnfTransformation, [status(thm)], [f_31])).
% 8.61/3.32  tff(c_1932, plain, (![A_3]: (A_3='#skF_1' | ~r1_tarski(A_3, '#skF_1'))), inference(resolution, [status(thm)], [c_1813, c_1927])).
% 8.61/3.32  tff(c_2302, plain, (![B_272]: (k1_relat_1(B_272)='#skF_1' | ~v4_relat_1(B_272, '#skF_1') | ~v1_relat_1(B_272))), inference(resolution, [status(thm)], [c_2136, c_1932])).
% 8.61/3.32  tff(c_2317, plain, (k1_relat_1('#skF_3')='#skF_1' | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_1992, c_2302])).
% 8.61/3.32  tff(c_2329, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_1918, c_2317])).
% 8.61/3.32  tff(c_2331, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1973, c_2329])).
% 8.61/3.32  tff(c_2332, plain, ('#skF_3'='#skF_1'), inference(splitRight, [status(thm)], [c_1944])).
% 8.61/3.32  tff(c_24, plain, (![A_16]: (k2_relat_1(A_16)!=k1_xboole_0 | k1_xboole_0=A_16 | ~v1_relat_1(A_16))), inference(cnfTransformation, [status(thm)], [f_69])).
% 8.61/3.32  tff(c_1812, plain, (![A_16]: (k2_relat_1(A_16)!='#skF_1' | A_16='#skF_1' | ~v1_relat_1(A_16))), inference(demodulation, [status(thm), theory('equality')], [c_1806, c_1806, c_24])).
% 8.61/3.32  tff(c_1943, plain, (k2_relat_1('#skF_3')!='#skF_1' | '#skF_3'='#skF_1'), inference(resolution, [status(thm)], [c_1918, c_1812])).
% 8.61/3.32  tff(c_1947, plain, (k2_relat_1('#skF_3')!='#skF_1'), inference(splitLeft, [status(thm)], [c_1943])).
% 8.61/3.32  tff(c_2334, plain, (k2_relat_1('#skF_1')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_2332, c_1947])).
% 8.61/3.32  tff(c_2343, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1876, c_2334])).
% 8.61/3.32  tff(c_2344, plain, ('#skF_3'='#skF_1'), inference(splitRight, [status(thm)], [c_1943])).
% 8.61/3.32  tff(c_2349, plain, (~v2_funct_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2344, c_89])).
% 8.61/3.32  tff(c_2355, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1809, c_2349])).
% 8.61/3.32  tff(c_2356, plain, (~v2_funct_2('#skF_4', '#skF_1')), inference(splitRight, [status(thm)], [c_64])).
% 8.61/3.32  tff(c_2502, plain, (![B_287, A_288]: (v1_relat_1(B_287) | ~m1_subset_1(B_287, k1_zfmisc_1(A_288)) | ~v1_relat_1(A_288))), inference(cnfTransformation, [status(thm)], [f_40])).
% 8.61/3.32  tff(c_2508, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_1'))), inference(resolution, [status(thm)], [c_68, c_2502])).
% 8.61/3.32  tff(c_2517, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_20, c_2508])).
% 8.61/3.32  tff(c_2554, plain, (![C_292, B_293, A_294]: (v5_relat_1(C_292, B_293) | ~m1_subset_1(C_292, k1_zfmisc_1(k2_zfmisc_1(A_294, B_293))))), inference(cnfTransformation, [status(thm)], [f_83])).
% 8.61/3.32  tff(c_2565, plain, (v5_relat_1('#skF_4', '#skF_1')), inference(resolution, [status(thm)], [c_68, c_2554])).
% 8.61/3.32  tff(c_18, plain, (![B_10, A_9]: (r1_tarski(k2_relat_1(B_10), A_9) | ~v5_relat_1(B_10, A_9) | ~v1_relat_1(B_10))), inference(cnfTransformation, [status(thm)], [f_52])).
% 8.61/3.32  tff(c_2511, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_74, c_2502])).
% 8.61/3.32  tff(c_2520, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_20, c_2511])).
% 8.61/3.32  tff(c_3275, plain, (![E_385, F_383, C_384, D_386, B_387, A_382]: (k1_partfun1(A_382, B_387, C_384, D_386, E_385, F_383)=k5_relat_1(E_385, F_383) | ~m1_subset_1(F_383, k1_zfmisc_1(k2_zfmisc_1(C_384, D_386))) | ~v1_funct_1(F_383) | ~m1_subset_1(E_385, k1_zfmisc_1(k2_zfmisc_1(A_382, B_387))) | ~v1_funct_1(E_385))), inference(cnfTransformation, [status(thm)], [f_125])).
% 8.61/3.32  tff(c_3281, plain, (![A_382, B_387, E_385]: (k1_partfun1(A_382, B_387, '#skF_2', '#skF_1', E_385, '#skF_4')=k5_relat_1(E_385, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_385, k1_zfmisc_1(k2_zfmisc_1(A_382, B_387))) | ~v1_funct_1(E_385))), inference(resolution, [status(thm)], [c_68, c_3275])).
% 8.61/3.32  tff(c_3425, plain, (![A_405, B_406, E_407]: (k1_partfun1(A_405, B_406, '#skF_2', '#skF_1', E_407, '#skF_4')=k5_relat_1(E_407, '#skF_4') | ~m1_subset_1(E_407, k1_zfmisc_1(k2_zfmisc_1(A_405, B_406))) | ~v1_funct_1(E_407))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_3281])).
% 8.61/3.32  tff(c_3440, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_74, c_3425])).
% 8.61/3.32  tff(c_3449, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_3440])).
% 8.61/3.32  tff(c_3538, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_3449, c_48])).
% 8.61/3.32  tff(c_3542, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_74, c_72, c_68, c_3538])).
% 8.61/3.32  tff(c_3022, plain, (![D_351, C_352, A_353, B_354]: (D_351=C_352 | ~r2_relset_1(A_353, B_354, C_352, D_351) | ~m1_subset_1(D_351, k1_zfmisc_1(k2_zfmisc_1(A_353, B_354))) | ~m1_subset_1(C_352, k1_zfmisc_1(k2_zfmisc_1(A_353, B_354))))), inference(cnfTransformation, [status(thm)], [f_91])).
% 8.61/3.32  tff(c_3036, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_66, c_3022])).
% 8.61/3.32  tff(c_3059, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_3036])).
% 8.61/3.32  tff(c_3089, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_3059])).
% 8.61/3.32  tff(c_3879, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3542, c_3449, c_3089])).
% 8.61/3.32  tff(c_3880, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_3059])).
% 8.61/3.32  tff(c_4055, plain, (![A_449, E_452, F_450, D_453, B_454, C_451]: (k1_partfun1(A_449, B_454, C_451, D_453, E_452, F_450)=k5_relat_1(E_452, F_450) | ~m1_subset_1(F_450, k1_zfmisc_1(k2_zfmisc_1(C_451, D_453))) | ~v1_funct_1(F_450) | ~m1_subset_1(E_452, k1_zfmisc_1(k2_zfmisc_1(A_449, B_454))) | ~v1_funct_1(E_452))), inference(cnfTransformation, [status(thm)], [f_125])).
% 8.61/3.32  tff(c_4061, plain, (![A_449, B_454, E_452]: (k1_partfun1(A_449, B_454, '#skF_2', '#skF_1', E_452, '#skF_4')=k5_relat_1(E_452, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_452, k1_zfmisc_1(k2_zfmisc_1(A_449, B_454))) | ~v1_funct_1(E_452))), inference(resolution, [status(thm)], [c_68, c_4055])).
% 8.61/3.32  tff(c_4230, plain, (![A_474, B_475, E_476]: (k1_partfun1(A_474, B_475, '#skF_2', '#skF_1', E_476, '#skF_4')=k5_relat_1(E_476, '#skF_4') | ~m1_subset_1(E_476, k1_zfmisc_1(k2_zfmisc_1(A_474, B_475))) | ~v1_funct_1(E_476))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_4061])).
% 8.61/3.32  tff(c_4245, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_74, c_4230])).
% 8.61/3.32  tff(c_4254, plain, (k5_relat_1('#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_3880, c_4245])).
% 8.61/3.32  tff(c_22, plain, (![A_13, B_15]: (r1_tarski(k2_relat_1(k5_relat_1(A_13, B_15)), k2_relat_1(B_15)) | ~v1_relat_1(B_15) | ~v1_relat_1(A_13))), inference(cnfTransformation, [status(thm)], [f_61])).
% 8.61/3.32  tff(c_4258, plain, (r1_tarski(k2_relat_1(k6_partfun1('#skF_1')), k2_relat_1('#skF_4')) | ~v1_relat_1('#skF_4') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_4254, c_22])).
% 8.61/3.32  tff(c_4262, plain, (r1_tarski('#skF_1', k2_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_2520, c_2517, c_81, c_4258])).
% 8.61/3.32  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 8.61/3.32  tff(c_4270, plain, (k2_relat_1('#skF_4')='#skF_1' | ~r1_tarski(k2_relat_1('#skF_4'), '#skF_1')), inference(resolution, [status(thm)], [c_4262, c_2])).
% 8.61/3.32  tff(c_4271, plain, (~r1_tarski(k2_relat_1('#skF_4'), '#skF_1')), inference(splitLeft, [status(thm)], [c_4270])).
% 8.61/3.32  tff(c_4277, plain, (~v5_relat_1('#skF_4', '#skF_1') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_18, c_4271])).
% 8.61/3.32  tff(c_4282, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2517, c_2565, c_4277])).
% 8.61/3.32  tff(c_4283, plain, (k2_relat_1('#skF_4')='#skF_1'), inference(splitRight, [status(thm)], [c_4270])).
% 8.61/3.32  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 8.61/3.32  tff(c_2756, plain, (![B_320, A_321]: (v5_relat_1(B_320, A_321) | ~r1_tarski(k2_relat_1(B_320), A_321) | ~v1_relat_1(B_320))), inference(cnfTransformation, [status(thm)], [f_52])).
% 8.61/3.32  tff(c_2780, plain, (![B_320]: (v5_relat_1(B_320, k2_relat_1(B_320)) | ~v1_relat_1(B_320))), inference(resolution, [status(thm)], [c_6, c_2756])).
% 8.61/3.32  tff(c_2853, plain, (![B_330]: (v2_funct_2(B_330, k2_relat_1(B_330)) | ~v5_relat_1(B_330, k2_relat_1(B_330)) | ~v1_relat_1(B_330))), inference(cnfTransformation, [status(thm)], [f_99])).
% 8.61/3.32  tff(c_2871, plain, (![B_320]: (v2_funct_2(B_320, k2_relat_1(B_320)) | ~v1_relat_1(B_320))), inference(resolution, [status(thm)], [c_2780, c_2853])).
% 8.61/3.32  tff(c_4295, plain, (v2_funct_2('#skF_4', '#skF_1') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_4283, c_2871])).
% 8.61/3.32  tff(c_4310, plain, (v2_funct_2('#skF_4', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2517, c_4295])).
% 8.61/3.32  tff(c_4312, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2356, c_4310])).
% 8.61/3.32  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.61/3.32  
% 8.61/3.32  Inference rules
% 8.61/3.32  ----------------------
% 8.61/3.32  #Ref     : 18
% 8.61/3.32  #Sup     : 804
% 8.61/3.32  #Fact    : 0
% 8.61/3.32  #Define  : 0
% 8.61/3.32  #Split   : 41
% 8.61/3.32  #Chain   : 0
% 8.61/3.32  #Close   : 0
% 8.61/3.32  
% 8.61/3.32  Ordering : KBO
% 8.61/3.32  
% 8.61/3.32  Simplification rules
% 8.61/3.32  ----------------------
% 8.61/3.32  #Subsume      : 189
% 8.61/3.32  #Demod        : 645
% 8.61/3.32  #Tautology    : 253
% 8.61/3.32  #SimpNegUnit  : 31
% 8.61/3.32  #BackRed      : 54
% 8.61/3.32  
% 8.61/3.32  #Partial instantiations: 0
% 8.61/3.32  #Strategies tried      : 1
% 8.61/3.32  
% 8.61/3.32  Timing (in seconds)
% 8.61/3.32  ----------------------
% 8.93/3.33  Preprocessing        : 0.58
% 8.93/3.33  Parsing              : 0.30
% 8.93/3.33  CNF conversion       : 0.04
% 8.93/3.33  Main loop            : 1.74
% 8.93/3.33  Inferencing          : 0.59
% 8.93/3.33  Reduction            : 0.61
% 8.93/3.33  Demodulation         : 0.44
% 8.93/3.33  BG Simplification    : 0.06
% 8.93/3.33  Subsumption          : 0.32
% 8.93/3.33  Abstraction          : 0.07
% 8.93/3.33  MUC search           : 0.00
% 8.93/3.33  Cooper               : 0.00
% 8.93/3.33  Total                : 2.41
% 8.93/3.33  Index Insertion      : 0.00
% 8.93/3.33  Index Deletion       : 0.00
% 8.93/3.33  Index Matching       : 0.00
% 8.93/3.33  BG Taut test         : 0.00
%------------------------------------------------------------------------------
