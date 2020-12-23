%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:12:16 EST 2020

% Result     : Theorem 8.28s
% Output     : CNFRefutation 8.28s
% Verified   : 
% Statistics : Number of formulae       :  155 ( 442 expanded)
%              Number of leaves         :   50 ( 173 expanded)
%              Depth                    :   13
%              Number of atoms          :  280 (1357 expanded)
%              Number of equality atoms :   51 ( 136 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k4_mcart_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4

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

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

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

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff(k4_mcart_1,type,(
    k4_mcart_1: ( $i * $i * $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_201,negated_conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_funct_2)).

tff(f_44,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => v1_xboole_0(k2_zfmisc_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_zfmisc_1)).

tff(f_51,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_xboole_0(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_subset_1)).

tff(f_159,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_88,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v2_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_funct_1)).

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

tff(f_111,axiom,(
    ! [A] : m1_subset_1(k6_relat_1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_relset_1)).

tff(f_109,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_181,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_funct_2)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_40,axiom,(
    ! [A,B] :
      ~ ( v1_xboole_0(A)
        & A != B
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_boole)).

tff(f_73,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_65,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_94,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_71,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_84,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_80,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => r1_tarski(k2_relat_1(k5_relat_1(A,B)),k2_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_relat_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_135,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A) )
     => ( v2_funct_2(B,A)
      <=> k2_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_funct_2)).

tff(c_70,plain,
    ( ~ v2_funct_2('#skF_5','#skF_2')
    | ~ v2_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_201])).

tff(c_122,plain,(
    ~ v2_funct_1('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_70])).

tff(c_12,plain,(
    ! [A_5,B_6] :
      ( v1_xboole_0(k2_zfmisc_1(A_5,B_6))
      | ~ v1_xboole_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_80,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_201])).

tff(c_200,plain,(
    ! [B_99,A_100] :
      ( v1_xboole_0(B_99)
      | ~ m1_subset_1(B_99,k1_zfmisc_1(A_100))
      | ~ v1_xboole_0(A_100) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_218,plain,
    ( v1_xboole_0('#skF_4')
    | ~ v1_xboole_0(k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_80,c_200])).

tff(c_293,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_218])).

tff(c_319,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_12,c_293])).

tff(c_64,plain,(
    ! [A_69] : k6_relat_1(A_69) = k6_partfun1(A_69) ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_34,plain,(
    ! [A_24] : v2_funct_1(k6_relat_1(A_24)) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_86,plain,(
    ! [A_24] : v2_funct_1(k6_partfun1(A_24)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_34])).

tff(c_84,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_201])).

tff(c_78,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_201])).

tff(c_74,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_201])).

tff(c_1499,plain,(
    ! [B_211,C_210,F_213,E_209,D_214,A_212] :
      ( k1_partfun1(A_212,B_211,C_210,D_214,E_209,F_213) = k5_relat_1(E_209,F_213)
      | ~ m1_subset_1(F_213,k1_zfmisc_1(k2_zfmisc_1(C_210,D_214)))
      | ~ v1_funct_1(F_213)
      | ~ m1_subset_1(E_209,k1_zfmisc_1(k2_zfmisc_1(A_212,B_211)))
      | ~ v1_funct_1(E_209) ) ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_1509,plain,(
    ! [A_212,B_211,E_209] :
      ( k1_partfun1(A_212,B_211,'#skF_3','#skF_2',E_209,'#skF_5') = k5_relat_1(E_209,'#skF_5')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1(E_209,k1_zfmisc_1(k2_zfmisc_1(A_212,B_211)))
      | ~ v1_funct_1(E_209) ) ),
    inference(resolution,[status(thm)],[c_74,c_1499])).

tff(c_2145,plain,(
    ! [A_240,B_241,E_242] :
      ( k1_partfun1(A_240,B_241,'#skF_3','#skF_2',E_242,'#skF_5') = k5_relat_1(E_242,'#skF_5')
      | ~ m1_subset_1(E_242,k1_zfmisc_1(k2_zfmisc_1(A_240,B_241)))
      | ~ v1_funct_1(E_242) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_1509])).

tff(c_2169,plain,
    ( k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5') = k5_relat_1('#skF_4','#skF_5')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_80,c_2145])).

tff(c_2177,plain,(
    k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5') = k5_relat_1('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_2169])).

tff(c_58,plain,(
    ! [A_57,E_61,B_58,D_60,C_59,F_62] :
      ( m1_subset_1(k1_partfun1(A_57,B_58,C_59,D_60,E_61,F_62),k1_zfmisc_1(k2_zfmisc_1(A_57,D_60)))
      | ~ m1_subset_1(F_62,k1_zfmisc_1(k2_zfmisc_1(C_59,D_60)))
      | ~ v1_funct_1(F_62)
      | ~ m1_subset_1(E_61,k1_zfmisc_1(k2_zfmisc_1(A_57,B_58)))
      | ~ v1_funct_1(E_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_2868,plain,
    ( m1_subset_1(k5_relat_1('#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2')))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2')))
    | ~ v1_funct_1('#skF_5')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
    | ~ v1_funct_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_2177,c_58])).

tff(c_2875,plain,(
    m1_subset_1(k5_relat_1('#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_80,c_78,c_74,c_2868])).

tff(c_46,plain,(
    ! [A_36] : m1_subset_1(k6_relat_1(A_36),k1_zfmisc_1(k2_zfmisc_1(A_36,A_36))) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_85,plain,(
    ! [A_36] : m1_subset_1(k6_partfun1(A_36),k1_zfmisc_1(k2_zfmisc_1(A_36,A_36))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_46])).

tff(c_72,plain,(
    r2_relset_1('#skF_2','#skF_2',k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5'),k6_partfun1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_201])).

tff(c_1169,plain,(
    ! [D_177,C_178,A_179,B_180] :
      ( D_177 = C_178
      | ~ r2_relset_1(A_179,B_180,C_178,D_177)
      | ~ m1_subset_1(D_177,k1_zfmisc_1(k2_zfmisc_1(A_179,B_180)))
      | ~ m1_subset_1(C_178,k1_zfmisc_1(k2_zfmisc_1(A_179,B_180))) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_1179,plain,
    ( k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5') = k6_partfun1('#skF_2')
    | ~ m1_subset_1(k6_partfun1('#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2')))
    | ~ m1_subset_1(k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(resolution,[status(thm)],[c_72,c_1169])).

tff(c_1198,plain,
    ( k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5') = k6_partfun1('#skF_2')
    | ~ m1_subset_1(k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_85,c_1179])).

tff(c_3415,plain,(
    k5_relat_1('#skF_4','#skF_5') = k6_partfun1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2875,c_2177,c_2177,c_1198])).

tff(c_82,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_201])).

tff(c_76,plain,(
    v1_funct_2('#skF_5','#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_201])).

tff(c_68,plain,(
    ! [D_73,A_70,C_72,E_75,B_71] :
      ( k1_xboole_0 = C_72
      | v2_funct_1(D_73)
      | ~ v2_funct_1(k1_partfun1(A_70,B_71,B_71,C_72,D_73,E_75))
      | ~ m1_subset_1(E_75,k1_zfmisc_1(k2_zfmisc_1(B_71,C_72)))
      | ~ v1_funct_2(E_75,B_71,C_72)
      | ~ v1_funct_1(E_75)
      | ~ m1_subset_1(D_73,k1_zfmisc_1(k2_zfmisc_1(A_70,B_71)))
      | ~ v1_funct_2(D_73,A_70,B_71)
      | ~ v1_funct_1(D_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_181])).

tff(c_2865,plain,
    ( k1_xboole_0 = '#skF_2'
    | v2_funct_1('#skF_4')
    | ~ v2_funct_1(k5_relat_1('#skF_4','#skF_5'))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2')))
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_2')
    | ~ v1_funct_1('#skF_5')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_3')
    | ~ v1_funct_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_2177,c_68])).

tff(c_2872,plain,
    ( k1_xboole_0 = '#skF_2'
    | v2_funct_1('#skF_4')
    | ~ v2_funct_1(k5_relat_1('#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_82,c_80,c_78,c_76,c_74,c_2865])).

tff(c_2873,plain,
    ( k1_xboole_0 = '#skF_2'
    | ~ v2_funct_1(k5_relat_1('#skF_4','#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_122,c_2872])).

tff(c_2877,plain,(
    ~ v2_funct_1(k5_relat_1('#skF_4','#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_2873])).

tff(c_3421,plain,(
    ~ v2_funct_1(k6_partfun1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3415,c_2877])).

tff(c_3431,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_3421])).

tff(c_3432,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_2873])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_3482,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3432,c_2])).

tff(c_3484,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_319,c_3482])).

tff(c_3485,plain,(
    v1_xboole_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_218])).

tff(c_124,plain,(
    ! [B_86,A_87] :
      ( ~ v1_xboole_0(B_86)
      | B_86 = A_87
      | ~ v1_xboole_0(A_87) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_127,plain,(
    ! [A_87] :
      ( k1_xboole_0 = A_87
      | ~ v1_xboole_0(A_87) ) ),
    inference(resolution,[status(thm)],[c_2,c_124])).

tff(c_3495,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_3485,c_127])).

tff(c_134,plain,(
    ! [A_89,B_90] :
      ( v1_xboole_0(k2_zfmisc_1(A_89,B_90))
      | ~ v1_xboole_0(A_89) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_142,plain,(
    ! [A_91,B_92] :
      ( k2_zfmisc_1(A_91,B_92) = k1_xboole_0
      | ~ v1_xboole_0(A_91) ) ),
    inference(resolution,[status(thm)],[c_134,c_127])).

tff(c_148,plain,(
    ! [B_92] : k2_zfmisc_1(k1_xboole_0,B_92) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2,c_142])).

tff(c_163,plain,(
    ! [A_94] : m1_subset_1(k6_partfun1(A_94),k1_zfmisc_1(k2_zfmisc_1(A_94,A_94))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_46])).

tff(c_167,plain,(
    m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) ),
    inference(superposition,[status(thm),theory(equality)],[c_148,c_163])).

tff(c_203,plain,
    ( v1_xboole_0(k6_partfun1(k1_xboole_0))
    | ~ v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_167,c_200])).

tff(c_215,plain,(
    v1_xboole_0(k6_partfun1(k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_203])).

tff(c_227,plain,(
    k6_partfun1(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_215,c_127])).

tff(c_245,plain,(
    v2_funct_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_227,c_86])).

tff(c_3500,plain,(
    v2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3495,c_245])).

tff(c_3509,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_122,c_3500])).

tff(c_3510,plain,(
    ~ v2_funct_2('#skF_5','#skF_2') ),
    inference(splitRight,[status(thm)],[c_70])).

tff(c_24,plain,(
    ! [A_18,B_19] : v1_relat_1(k2_zfmisc_1(A_18,B_19)) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_3629,plain,(
    ! [B_308,A_309] :
      ( v1_relat_1(B_308)
      | ~ m1_subset_1(B_308,k1_zfmisc_1(A_309))
      | ~ v1_relat_1(A_309) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_3638,plain,
    ( v1_relat_1('#skF_5')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_3','#skF_2')) ),
    inference(resolution,[status(thm)],[c_74,c_3629])).

tff(c_3650,plain,(
    v1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_3638])).

tff(c_3767,plain,(
    ! [C_323,B_324,A_325] :
      ( v5_relat_1(C_323,B_324)
      | ~ m1_subset_1(C_323,k1_zfmisc_1(k2_zfmisc_1(A_325,B_324))) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_3782,plain,(
    v5_relat_1('#skF_5','#skF_2') ),
    inference(resolution,[status(thm)],[c_74,c_3767])).

tff(c_22,plain,(
    ! [B_17,A_16] :
      ( r1_tarski(k2_relat_1(B_17),A_16)
      | ~ v5_relat_1(B_17,A_16)
      | ~ v1_relat_1(B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_3641,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_80,c_3629])).

tff(c_3653,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_3641])).

tff(c_30,plain,(
    ! [A_23] : k2_relat_1(k6_relat_1(A_23)) = A_23 ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_88,plain,(
    ! [A_23] : k2_relat_1(k6_partfun1(A_23)) = A_23 ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_30])).

tff(c_4883,plain,(
    ! [F_420,A_419,D_421,B_418,C_417,E_416] :
      ( k1_partfun1(A_419,B_418,C_417,D_421,E_416,F_420) = k5_relat_1(E_416,F_420)
      | ~ m1_subset_1(F_420,k1_zfmisc_1(k2_zfmisc_1(C_417,D_421)))
      | ~ v1_funct_1(F_420)
      | ~ m1_subset_1(E_416,k1_zfmisc_1(k2_zfmisc_1(A_419,B_418)))
      | ~ v1_funct_1(E_416) ) ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_4893,plain,(
    ! [A_419,B_418,E_416] :
      ( k1_partfun1(A_419,B_418,'#skF_3','#skF_2',E_416,'#skF_5') = k5_relat_1(E_416,'#skF_5')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1(E_416,k1_zfmisc_1(k2_zfmisc_1(A_419,B_418)))
      | ~ v1_funct_1(E_416) ) ),
    inference(resolution,[status(thm)],[c_74,c_4883])).

tff(c_6256,plain,(
    ! [A_476,B_477,E_478] :
      ( k1_partfun1(A_476,B_477,'#skF_3','#skF_2',E_478,'#skF_5') = k5_relat_1(E_478,'#skF_5')
      | ~ m1_subset_1(E_478,k1_zfmisc_1(k2_zfmisc_1(A_476,B_477)))
      | ~ v1_funct_1(E_478) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_4893])).

tff(c_6286,plain,
    ( k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5') = k5_relat_1('#skF_4','#skF_5')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_80,c_6256])).

tff(c_6300,plain,(
    k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5') = k5_relat_1('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_6286])).

tff(c_6604,plain,
    ( m1_subset_1(k5_relat_1('#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2')))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2')))
    | ~ v1_funct_1('#skF_5')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
    | ~ v1_funct_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_6300,c_58])).

tff(c_6610,plain,(
    m1_subset_1(k5_relat_1('#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_80,c_78,c_74,c_6604])).

tff(c_4392,plain,(
    ! [D_383,C_384,A_385,B_386] :
      ( D_383 = C_384
      | ~ r2_relset_1(A_385,B_386,C_384,D_383)
      | ~ m1_subset_1(D_383,k1_zfmisc_1(k2_zfmisc_1(A_385,B_386)))
      | ~ m1_subset_1(C_384,k1_zfmisc_1(k2_zfmisc_1(A_385,B_386))) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_4402,plain,
    ( k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5') = k6_partfun1('#skF_2')
    | ~ m1_subset_1(k6_partfun1('#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2')))
    | ~ m1_subset_1(k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(resolution,[status(thm)],[c_72,c_4392])).

tff(c_4421,plain,
    ( k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5') = k6_partfun1('#skF_2')
    | ~ m1_subset_1(k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_85,c_4402])).

tff(c_4573,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_4421])).

tff(c_6939,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6610,c_6300,c_4573])).

tff(c_6940,plain,(
    k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5') = k6_partfun1('#skF_2') ),
    inference(splitRight,[status(thm)],[c_4421])).

tff(c_7251,plain,(
    ! [E_537,A_540,F_541,B_539,D_542,C_538] :
      ( k1_partfun1(A_540,B_539,C_538,D_542,E_537,F_541) = k5_relat_1(E_537,F_541)
      | ~ m1_subset_1(F_541,k1_zfmisc_1(k2_zfmisc_1(C_538,D_542)))
      | ~ v1_funct_1(F_541)
      | ~ m1_subset_1(E_537,k1_zfmisc_1(k2_zfmisc_1(A_540,B_539)))
      | ~ v1_funct_1(E_537) ) ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_7261,plain,(
    ! [A_540,B_539,E_537] :
      ( k1_partfun1(A_540,B_539,'#skF_3','#skF_2',E_537,'#skF_5') = k5_relat_1(E_537,'#skF_5')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1(E_537,k1_zfmisc_1(k2_zfmisc_1(A_540,B_539)))
      | ~ v1_funct_1(E_537) ) ),
    inference(resolution,[status(thm)],[c_74,c_7251])).

tff(c_7720,plain,(
    ! [A_568,B_569,E_570] :
      ( k1_partfun1(A_568,B_569,'#skF_3','#skF_2',E_570,'#skF_5') = k5_relat_1(E_570,'#skF_5')
      | ~ m1_subset_1(E_570,k1_zfmisc_1(k2_zfmisc_1(A_568,B_569)))
      | ~ v1_funct_1(E_570) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_7261])).

tff(c_7744,plain,
    ( k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5') = k5_relat_1('#skF_4','#skF_5')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_80,c_7720])).

tff(c_7752,plain,(
    k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5') = k5_relat_1('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_7744])).

tff(c_8609,plain,(
    k5_relat_1('#skF_4','#skF_5') = k6_partfun1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6940,c_7752])).

tff(c_26,plain,(
    ! [A_20,B_22] :
      ( r1_tarski(k2_relat_1(k5_relat_1(A_20,B_22)),k2_relat_1(B_22))
      | ~ v1_relat_1(B_22)
      | ~ v1_relat_1(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_8637,plain,
    ( r1_tarski(k2_relat_1(k6_partfun1('#skF_2')),k2_relat_1('#skF_5'))
    | ~ v1_relat_1('#skF_5')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_8609,c_26])).

tff(c_8641,plain,(
    r1_tarski('#skF_2',k2_relat_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3653,c_3650,c_88,c_8637])).

tff(c_4,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_8645,plain,
    ( k2_relat_1('#skF_5') = '#skF_2'
    | ~ r1_tarski(k2_relat_1('#skF_5'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_8641,c_4])).

tff(c_8685,plain,(
    ~ r1_tarski(k2_relat_1('#skF_5'),'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_8645])).

tff(c_8688,plain,
    ( ~ v5_relat_1('#skF_5','#skF_2')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_22,c_8685])).

tff(c_8692,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3650,c_3782,c_8688])).

tff(c_8693,plain,(
    k2_relat_1('#skF_5') = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_8645])).

tff(c_8,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_3682,plain,(
    ! [B_313,A_314] :
      ( v5_relat_1(B_313,A_314)
      | ~ r1_tarski(k2_relat_1(B_313),A_314)
      | ~ v1_relat_1(B_313) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_3701,plain,(
    ! [B_313] :
      ( v5_relat_1(B_313,k2_relat_1(B_313))
      | ~ v1_relat_1(B_313) ) ),
    inference(resolution,[status(thm)],[c_8,c_3682])).

tff(c_3978,plain,(
    ! [B_345] :
      ( v2_funct_2(B_345,k2_relat_1(B_345))
      | ~ v5_relat_1(B_345,k2_relat_1(B_345))
      | ~ v1_relat_1(B_345) ) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_4002,plain,(
    ! [B_313] :
      ( v2_funct_2(B_313,k2_relat_1(B_313))
      | ~ v1_relat_1(B_313) ) ),
    inference(resolution,[status(thm)],[c_3701,c_3978])).

tff(c_8703,plain,
    ( v2_funct_2('#skF_5','#skF_2')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_8693,c_4002])).

tff(c_8718,plain,(
    v2_funct_2('#skF_5','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3650,c_8703])).

tff(c_8720,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3510,c_8718])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:03:53 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.28/2.74  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.28/2.76  
% 8.28/2.76  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.28/2.76  %$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k4_mcart_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4
% 8.28/2.76  
% 8.28/2.76  %Foreground sorts:
% 8.28/2.76  
% 8.28/2.76  
% 8.28/2.76  %Background operators:
% 8.28/2.76  
% 8.28/2.76  
% 8.28/2.76  %Foreground operators:
% 8.28/2.76  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 8.28/2.76  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 8.28/2.76  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.28/2.76  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 8.28/2.76  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 8.28/2.76  tff('#skF_1', type, '#skF_1': $i > $i).
% 8.28/2.76  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 8.28/2.76  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 8.28/2.76  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 8.28/2.76  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 8.28/2.76  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 8.28/2.76  tff('#skF_5', type, '#skF_5': $i).
% 8.28/2.76  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 8.28/2.76  tff('#skF_2', type, '#skF_2': $i).
% 8.28/2.76  tff('#skF_3', type, '#skF_3': $i).
% 8.28/2.76  tff(v2_funct_2, type, v2_funct_2: ($i * $i) > $o).
% 8.28/2.76  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 8.28/2.76  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 8.28/2.76  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 8.28/2.76  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.28/2.76  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 8.28/2.76  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 8.28/2.76  tff('#skF_4', type, '#skF_4': $i).
% 8.28/2.76  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 8.28/2.76  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.28/2.76  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 8.28/2.76  tff(k4_mcart_1, type, k4_mcart_1: ($i * $i * $i * $i) > $i).
% 8.28/2.76  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 8.28/2.76  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 8.28/2.76  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 8.28/2.76  
% 8.28/2.78  tff(f_201, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (r2_relset_1(A, A, k1_partfun1(A, B, B, A, C, D), k6_partfun1(A)) => (v2_funct_1(C) & v2_funct_2(D, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_funct_2)).
% 8.28/2.78  tff(f_44, axiom, (![A, B]: (v1_xboole_0(A) => v1_xboole_0(k2_zfmisc_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc4_zfmisc_1)).
% 8.28/2.78  tff(f_51, axiom, (![A]: (v1_xboole_0(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_subset_1)).
% 8.28/2.78  tff(f_159, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 8.28/2.78  tff(f_88, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v2_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc4_funct_1)).
% 8.28/2.78  tff(f_157, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 8.28/2.78  tff(f_147, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (v1_funct_1(k1_partfun1(A, B, C, D, E, F)) & m1_subset_1(k1_partfun1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 8.28/2.78  tff(f_111, axiom, (![A]: m1_subset_1(k6_relat_1(A), k1_zfmisc_1(k2_zfmisc_1(A, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_relset_1)).
% 8.28/2.78  tff(f_109, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 8.28/2.78  tff(f_181, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, B, C)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (v2_funct_1(k1_partfun1(A, B, B, C, D, E)) => (((C = k1_xboole_0) & ~(B = k1_xboole_0)) | v2_funct_1(D))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t26_funct_2)).
% 8.28/2.78  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 8.28/2.78  tff(f_40, axiom, (![A, B]: ~((v1_xboole_0(A) & ~(A = B)) & v1_xboole_0(B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_boole)).
% 8.28/2.78  tff(f_73, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 8.28/2.78  tff(f_65, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 8.28/2.78  tff(f_94, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 8.28/2.78  tff(f_71, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 8.28/2.78  tff(f_84, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 8.28/2.78  tff(f_80, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => r1_tarski(k2_relat_1(k5_relat_1(A, B)), k2_relat_1(B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t45_relat_1)).
% 8.28/2.78  tff(f_32, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 8.28/2.78  tff(f_135, axiom, (![A, B]: ((v1_relat_1(B) & v5_relat_1(B, A)) => (v2_funct_2(B, A) <=> (k2_relat_1(B) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_funct_2)).
% 8.28/2.78  tff(c_70, plain, (~v2_funct_2('#skF_5', '#skF_2') | ~v2_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_201])).
% 8.28/2.78  tff(c_122, plain, (~v2_funct_1('#skF_4')), inference(splitLeft, [status(thm)], [c_70])).
% 8.28/2.78  tff(c_12, plain, (![A_5, B_6]: (v1_xboole_0(k2_zfmisc_1(A_5, B_6)) | ~v1_xboole_0(A_5))), inference(cnfTransformation, [status(thm)], [f_44])).
% 8.28/2.78  tff(c_80, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_201])).
% 8.28/2.78  tff(c_200, plain, (![B_99, A_100]: (v1_xboole_0(B_99) | ~m1_subset_1(B_99, k1_zfmisc_1(A_100)) | ~v1_xboole_0(A_100))), inference(cnfTransformation, [status(thm)], [f_51])).
% 8.28/2.78  tff(c_218, plain, (v1_xboole_0('#skF_4') | ~v1_xboole_0(k2_zfmisc_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_80, c_200])).
% 8.28/2.78  tff(c_293, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_2', '#skF_3'))), inference(splitLeft, [status(thm)], [c_218])).
% 8.28/2.78  tff(c_319, plain, (~v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_12, c_293])).
% 8.28/2.78  tff(c_64, plain, (![A_69]: (k6_relat_1(A_69)=k6_partfun1(A_69))), inference(cnfTransformation, [status(thm)], [f_159])).
% 8.28/2.78  tff(c_34, plain, (![A_24]: (v2_funct_1(k6_relat_1(A_24)))), inference(cnfTransformation, [status(thm)], [f_88])).
% 8.28/2.78  tff(c_86, plain, (![A_24]: (v2_funct_1(k6_partfun1(A_24)))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_34])).
% 8.28/2.78  tff(c_84, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_201])).
% 8.28/2.78  tff(c_78, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_201])).
% 8.28/2.78  tff(c_74, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_201])).
% 8.28/2.78  tff(c_1499, plain, (![B_211, C_210, F_213, E_209, D_214, A_212]: (k1_partfun1(A_212, B_211, C_210, D_214, E_209, F_213)=k5_relat_1(E_209, F_213) | ~m1_subset_1(F_213, k1_zfmisc_1(k2_zfmisc_1(C_210, D_214))) | ~v1_funct_1(F_213) | ~m1_subset_1(E_209, k1_zfmisc_1(k2_zfmisc_1(A_212, B_211))) | ~v1_funct_1(E_209))), inference(cnfTransformation, [status(thm)], [f_157])).
% 8.28/2.78  tff(c_1509, plain, (![A_212, B_211, E_209]: (k1_partfun1(A_212, B_211, '#skF_3', '#skF_2', E_209, '#skF_5')=k5_relat_1(E_209, '#skF_5') | ~v1_funct_1('#skF_5') | ~m1_subset_1(E_209, k1_zfmisc_1(k2_zfmisc_1(A_212, B_211))) | ~v1_funct_1(E_209))), inference(resolution, [status(thm)], [c_74, c_1499])).
% 8.28/2.78  tff(c_2145, plain, (![A_240, B_241, E_242]: (k1_partfun1(A_240, B_241, '#skF_3', '#skF_2', E_242, '#skF_5')=k5_relat_1(E_242, '#skF_5') | ~m1_subset_1(E_242, k1_zfmisc_1(k2_zfmisc_1(A_240, B_241))) | ~v1_funct_1(E_242))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_1509])).
% 8.28/2.78  tff(c_2169, plain, (k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5')=k5_relat_1('#skF_4', '#skF_5') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_80, c_2145])).
% 8.28/2.78  tff(c_2177, plain, (k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5')=k5_relat_1('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_84, c_2169])).
% 8.28/2.78  tff(c_58, plain, (![A_57, E_61, B_58, D_60, C_59, F_62]: (m1_subset_1(k1_partfun1(A_57, B_58, C_59, D_60, E_61, F_62), k1_zfmisc_1(k2_zfmisc_1(A_57, D_60))) | ~m1_subset_1(F_62, k1_zfmisc_1(k2_zfmisc_1(C_59, D_60))) | ~v1_funct_1(F_62) | ~m1_subset_1(E_61, k1_zfmisc_1(k2_zfmisc_1(A_57, B_58))) | ~v1_funct_1(E_61))), inference(cnfTransformation, [status(thm)], [f_147])).
% 8.28/2.78  tff(c_2868, plain, (m1_subset_1(k5_relat_1('#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'))) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2'))) | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~v1_funct_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_2177, c_58])).
% 8.28/2.78  tff(c_2875, plain, (m1_subset_1(k5_relat_1('#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_84, c_80, c_78, c_74, c_2868])).
% 8.28/2.78  tff(c_46, plain, (![A_36]: (m1_subset_1(k6_relat_1(A_36), k1_zfmisc_1(k2_zfmisc_1(A_36, A_36))))), inference(cnfTransformation, [status(thm)], [f_111])).
% 8.28/2.78  tff(c_85, plain, (![A_36]: (m1_subset_1(k6_partfun1(A_36), k1_zfmisc_1(k2_zfmisc_1(A_36, A_36))))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_46])).
% 8.28/2.78  tff(c_72, plain, (r2_relset_1('#skF_2', '#skF_2', k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5'), k6_partfun1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_201])).
% 8.28/2.78  tff(c_1169, plain, (![D_177, C_178, A_179, B_180]: (D_177=C_178 | ~r2_relset_1(A_179, B_180, C_178, D_177) | ~m1_subset_1(D_177, k1_zfmisc_1(k2_zfmisc_1(A_179, B_180))) | ~m1_subset_1(C_178, k1_zfmisc_1(k2_zfmisc_1(A_179, B_180))))), inference(cnfTransformation, [status(thm)], [f_109])).
% 8.28/2.78  tff(c_1179, plain, (k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5')=k6_partfun1('#skF_2') | ~m1_subset_1(k6_partfun1('#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'))) | ~m1_subset_1(k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(resolution, [status(thm)], [c_72, c_1169])).
% 8.28/2.78  tff(c_1198, plain, (k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5')=k6_partfun1('#skF_2') | ~m1_subset_1(k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_85, c_1179])).
% 8.28/2.78  tff(c_3415, plain, (k5_relat_1('#skF_4', '#skF_5')=k6_partfun1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2875, c_2177, c_2177, c_1198])).
% 8.28/2.78  tff(c_82, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_201])).
% 8.28/2.78  tff(c_76, plain, (v1_funct_2('#skF_5', '#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_201])).
% 8.28/2.78  tff(c_68, plain, (![D_73, A_70, C_72, E_75, B_71]: (k1_xboole_0=C_72 | v2_funct_1(D_73) | ~v2_funct_1(k1_partfun1(A_70, B_71, B_71, C_72, D_73, E_75)) | ~m1_subset_1(E_75, k1_zfmisc_1(k2_zfmisc_1(B_71, C_72))) | ~v1_funct_2(E_75, B_71, C_72) | ~v1_funct_1(E_75) | ~m1_subset_1(D_73, k1_zfmisc_1(k2_zfmisc_1(A_70, B_71))) | ~v1_funct_2(D_73, A_70, B_71) | ~v1_funct_1(D_73))), inference(cnfTransformation, [status(thm)], [f_181])).
% 8.28/2.78  tff(c_2865, plain, (k1_xboole_0='#skF_2' | v2_funct_1('#skF_4') | ~v2_funct_1(k5_relat_1('#skF_4', '#skF_5')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2'))) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_2') | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3') | ~v1_funct_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_2177, c_68])).
% 8.28/2.78  tff(c_2872, plain, (k1_xboole_0='#skF_2' | v2_funct_1('#skF_4') | ~v2_funct_1(k5_relat_1('#skF_4', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_84, c_82, c_80, c_78, c_76, c_74, c_2865])).
% 8.28/2.78  tff(c_2873, plain, (k1_xboole_0='#skF_2' | ~v2_funct_1(k5_relat_1('#skF_4', '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_122, c_2872])).
% 8.28/2.78  tff(c_2877, plain, (~v2_funct_1(k5_relat_1('#skF_4', '#skF_5'))), inference(splitLeft, [status(thm)], [c_2873])).
% 8.28/2.78  tff(c_3421, plain, (~v2_funct_1(k6_partfun1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_3415, c_2877])).
% 8.28/2.78  tff(c_3431, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_86, c_3421])).
% 8.28/2.78  tff(c_3432, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_2873])).
% 8.28/2.78  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 8.28/2.78  tff(c_3482, plain, (v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_3432, c_2])).
% 8.28/2.78  tff(c_3484, plain, $false, inference(negUnitSimplification, [status(thm)], [c_319, c_3482])).
% 8.28/2.78  tff(c_3485, plain, (v1_xboole_0('#skF_4')), inference(splitRight, [status(thm)], [c_218])).
% 8.28/2.78  tff(c_124, plain, (![B_86, A_87]: (~v1_xboole_0(B_86) | B_86=A_87 | ~v1_xboole_0(A_87))), inference(cnfTransformation, [status(thm)], [f_40])).
% 8.28/2.78  tff(c_127, plain, (![A_87]: (k1_xboole_0=A_87 | ~v1_xboole_0(A_87))), inference(resolution, [status(thm)], [c_2, c_124])).
% 8.28/2.78  tff(c_3495, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_3485, c_127])).
% 8.28/2.78  tff(c_134, plain, (![A_89, B_90]: (v1_xboole_0(k2_zfmisc_1(A_89, B_90)) | ~v1_xboole_0(A_89))), inference(cnfTransformation, [status(thm)], [f_44])).
% 8.28/2.78  tff(c_142, plain, (![A_91, B_92]: (k2_zfmisc_1(A_91, B_92)=k1_xboole_0 | ~v1_xboole_0(A_91))), inference(resolution, [status(thm)], [c_134, c_127])).
% 8.28/2.78  tff(c_148, plain, (![B_92]: (k2_zfmisc_1(k1_xboole_0, B_92)=k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_142])).
% 8.28/2.78  tff(c_163, plain, (![A_94]: (m1_subset_1(k6_partfun1(A_94), k1_zfmisc_1(k2_zfmisc_1(A_94, A_94))))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_46])).
% 8.28/2.78  tff(c_167, plain, (m1_subset_1(k6_partfun1(k1_xboole_0), k1_zfmisc_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_148, c_163])).
% 8.28/2.78  tff(c_203, plain, (v1_xboole_0(k6_partfun1(k1_xboole_0)) | ~v1_xboole_0(k1_xboole_0)), inference(resolution, [status(thm)], [c_167, c_200])).
% 8.28/2.78  tff(c_215, plain, (v1_xboole_0(k6_partfun1(k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_203])).
% 8.28/2.78  tff(c_227, plain, (k6_partfun1(k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_215, c_127])).
% 8.28/2.78  tff(c_245, plain, (v2_funct_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_227, c_86])).
% 8.28/2.78  tff(c_3500, plain, (v2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_3495, c_245])).
% 8.28/2.78  tff(c_3509, plain, $false, inference(negUnitSimplification, [status(thm)], [c_122, c_3500])).
% 8.28/2.78  tff(c_3510, plain, (~v2_funct_2('#skF_5', '#skF_2')), inference(splitRight, [status(thm)], [c_70])).
% 8.28/2.78  tff(c_24, plain, (![A_18, B_19]: (v1_relat_1(k2_zfmisc_1(A_18, B_19)))), inference(cnfTransformation, [status(thm)], [f_73])).
% 8.28/2.78  tff(c_3629, plain, (![B_308, A_309]: (v1_relat_1(B_308) | ~m1_subset_1(B_308, k1_zfmisc_1(A_309)) | ~v1_relat_1(A_309))), inference(cnfTransformation, [status(thm)], [f_65])).
% 8.28/2.78  tff(c_3638, plain, (v1_relat_1('#skF_5') | ~v1_relat_1(k2_zfmisc_1('#skF_3', '#skF_2'))), inference(resolution, [status(thm)], [c_74, c_3629])).
% 8.28/2.78  tff(c_3650, plain, (v1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_24, c_3638])).
% 8.28/2.78  tff(c_3767, plain, (![C_323, B_324, A_325]: (v5_relat_1(C_323, B_324) | ~m1_subset_1(C_323, k1_zfmisc_1(k2_zfmisc_1(A_325, B_324))))), inference(cnfTransformation, [status(thm)], [f_94])).
% 8.28/2.78  tff(c_3782, plain, (v5_relat_1('#skF_5', '#skF_2')), inference(resolution, [status(thm)], [c_74, c_3767])).
% 8.28/2.78  tff(c_22, plain, (![B_17, A_16]: (r1_tarski(k2_relat_1(B_17), A_16) | ~v5_relat_1(B_17, A_16) | ~v1_relat_1(B_17))), inference(cnfTransformation, [status(thm)], [f_71])).
% 8.28/2.78  tff(c_3641, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_80, c_3629])).
% 8.28/2.78  tff(c_3653, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_24, c_3641])).
% 8.28/2.78  tff(c_30, plain, (![A_23]: (k2_relat_1(k6_relat_1(A_23))=A_23)), inference(cnfTransformation, [status(thm)], [f_84])).
% 8.28/2.78  tff(c_88, plain, (![A_23]: (k2_relat_1(k6_partfun1(A_23))=A_23)), inference(demodulation, [status(thm), theory('equality')], [c_64, c_30])).
% 8.28/2.78  tff(c_4883, plain, (![F_420, A_419, D_421, B_418, C_417, E_416]: (k1_partfun1(A_419, B_418, C_417, D_421, E_416, F_420)=k5_relat_1(E_416, F_420) | ~m1_subset_1(F_420, k1_zfmisc_1(k2_zfmisc_1(C_417, D_421))) | ~v1_funct_1(F_420) | ~m1_subset_1(E_416, k1_zfmisc_1(k2_zfmisc_1(A_419, B_418))) | ~v1_funct_1(E_416))), inference(cnfTransformation, [status(thm)], [f_157])).
% 8.28/2.78  tff(c_4893, plain, (![A_419, B_418, E_416]: (k1_partfun1(A_419, B_418, '#skF_3', '#skF_2', E_416, '#skF_5')=k5_relat_1(E_416, '#skF_5') | ~v1_funct_1('#skF_5') | ~m1_subset_1(E_416, k1_zfmisc_1(k2_zfmisc_1(A_419, B_418))) | ~v1_funct_1(E_416))), inference(resolution, [status(thm)], [c_74, c_4883])).
% 8.28/2.78  tff(c_6256, plain, (![A_476, B_477, E_478]: (k1_partfun1(A_476, B_477, '#skF_3', '#skF_2', E_478, '#skF_5')=k5_relat_1(E_478, '#skF_5') | ~m1_subset_1(E_478, k1_zfmisc_1(k2_zfmisc_1(A_476, B_477))) | ~v1_funct_1(E_478))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_4893])).
% 8.28/2.78  tff(c_6286, plain, (k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5')=k5_relat_1('#skF_4', '#skF_5') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_80, c_6256])).
% 8.28/2.78  tff(c_6300, plain, (k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5')=k5_relat_1('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_84, c_6286])).
% 8.28/2.78  tff(c_6604, plain, (m1_subset_1(k5_relat_1('#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'))) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2'))) | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~v1_funct_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_6300, c_58])).
% 8.28/2.78  tff(c_6610, plain, (m1_subset_1(k5_relat_1('#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_84, c_80, c_78, c_74, c_6604])).
% 8.28/2.78  tff(c_4392, plain, (![D_383, C_384, A_385, B_386]: (D_383=C_384 | ~r2_relset_1(A_385, B_386, C_384, D_383) | ~m1_subset_1(D_383, k1_zfmisc_1(k2_zfmisc_1(A_385, B_386))) | ~m1_subset_1(C_384, k1_zfmisc_1(k2_zfmisc_1(A_385, B_386))))), inference(cnfTransformation, [status(thm)], [f_109])).
% 8.28/2.78  tff(c_4402, plain, (k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5')=k6_partfun1('#skF_2') | ~m1_subset_1(k6_partfun1('#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'))) | ~m1_subset_1(k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(resolution, [status(thm)], [c_72, c_4392])).
% 8.28/2.78  tff(c_4421, plain, (k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5')=k6_partfun1('#skF_2') | ~m1_subset_1(k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_85, c_4402])).
% 8.28/2.78  tff(c_4573, plain, (~m1_subset_1(k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(splitLeft, [status(thm)], [c_4421])).
% 8.28/2.78  tff(c_6939, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6610, c_6300, c_4573])).
% 8.28/2.78  tff(c_6940, plain, (k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5')=k6_partfun1('#skF_2')), inference(splitRight, [status(thm)], [c_4421])).
% 8.28/2.78  tff(c_7251, plain, (![E_537, A_540, F_541, B_539, D_542, C_538]: (k1_partfun1(A_540, B_539, C_538, D_542, E_537, F_541)=k5_relat_1(E_537, F_541) | ~m1_subset_1(F_541, k1_zfmisc_1(k2_zfmisc_1(C_538, D_542))) | ~v1_funct_1(F_541) | ~m1_subset_1(E_537, k1_zfmisc_1(k2_zfmisc_1(A_540, B_539))) | ~v1_funct_1(E_537))), inference(cnfTransformation, [status(thm)], [f_157])).
% 8.28/2.78  tff(c_7261, plain, (![A_540, B_539, E_537]: (k1_partfun1(A_540, B_539, '#skF_3', '#skF_2', E_537, '#skF_5')=k5_relat_1(E_537, '#skF_5') | ~v1_funct_1('#skF_5') | ~m1_subset_1(E_537, k1_zfmisc_1(k2_zfmisc_1(A_540, B_539))) | ~v1_funct_1(E_537))), inference(resolution, [status(thm)], [c_74, c_7251])).
% 8.28/2.78  tff(c_7720, plain, (![A_568, B_569, E_570]: (k1_partfun1(A_568, B_569, '#skF_3', '#skF_2', E_570, '#skF_5')=k5_relat_1(E_570, '#skF_5') | ~m1_subset_1(E_570, k1_zfmisc_1(k2_zfmisc_1(A_568, B_569))) | ~v1_funct_1(E_570))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_7261])).
% 8.28/2.78  tff(c_7744, plain, (k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5')=k5_relat_1('#skF_4', '#skF_5') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_80, c_7720])).
% 8.28/2.78  tff(c_7752, plain, (k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5')=k5_relat_1('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_84, c_7744])).
% 8.28/2.78  tff(c_8609, plain, (k5_relat_1('#skF_4', '#skF_5')=k6_partfun1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_6940, c_7752])).
% 8.28/2.78  tff(c_26, plain, (![A_20, B_22]: (r1_tarski(k2_relat_1(k5_relat_1(A_20, B_22)), k2_relat_1(B_22)) | ~v1_relat_1(B_22) | ~v1_relat_1(A_20))), inference(cnfTransformation, [status(thm)], [f_80])).
% 8.28/2.78  tff(c_8637, plain, (r1_tarski(k2_relat_1(k6_partfun1('#skF_2')), k2_relat_1('#skF_5')) | ~v1_relat_1('#skF_5') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_8609, c_26])).
% 8.28/2.78  tff(c_8641, plain, (r1_tarski('#skF_2', k2_relat_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_3653, c_3650, c_88, c_8637])).
% 8.28/2.78  tff(c_4, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 8.28/2.78  tff(c_8645, plain, (k2_relat_1('#skF_5')='#skF_2' | ~r1_tarski(k2_relat_1('#skF_5'), '#skF_2')), inference(resolution, [status(thm)], [c_8641, c_4])).
% 8.28/2.78  tff(c_8685, plain, (~r1_tarski(k2_relat_1('#skF_5'), '#skF_2')), inference(splitLeft, [status(thm)], [c_8645])).
% 8.28/2.78  tff(c_8688, plain, (~v5_relat_1('#skF_5', '#skF_2') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_22, c_8685])).
% 8.28/2.78  tff(c_8692, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3650, c_3782, c_8688])).
% 8.28/2.78  tff(c_8693, plain, (k2_relat_1('#skF_5')='#skF_2'), inference(splitRight, [status(thm)], [c_8645])).
% 8.28/2.78  tff(c_8, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 8.28/2.78  tff(c_3682, plain, (![B_313, A_314]: (v5_relat_1(B_313, A_314) | ~r1_tarski(k2_relat_1(B_313), A_314) | ~v1_relat_1(B_313))), inference(cnfTransformation, [status(thm)], [f_71])).
% 8.28/2.78  tff(c_3701, plain, (![B_313]: (v5_relat_1(B_313, k2_relat_1(B_313)) | ~v1_relat_1(B_313))), inference(resolution, [status(thm)], [c_8, c_3682])).
% 8.28/2.78  tff(c_3978, plain, (![B_345]: (v2_funct_2(B_345, k2_relat_1(B_345)) | ~v5_relat_1(B_345, k2_relat_1(B_345)) | ~v1_relat_1(B_345))), inference(cnfTransformation, [status(thm)], [f_135])).
% 8.28/2.78  tff(c_4002, plain, (![B_313]: (v2_funct_2(B_313, k2_relat_1(B_313)) | ~v1_relat_1(B_313))), inference(resolution, [status(thm)], [c_3701, c_3978])).
% 8.28/2.78  tff(c_8703, plain, (v2_funct_2('#skF_5', '#skF_2') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_8693, c_4002])).
% 8.28/2.78  tff(c_8718, plain, (v2_funct_2('#skF_5', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_3650, c_8703])).
% 8.28/2.78  tff(c_8720, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3510, c_8718])).
% 8.28/2.78  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.28/2.78  
% 8.28/2.78  Inference rules
% 8.28/2.78  ----------------------
% 8.28/2.78  #Ref     : 0
% 8.28/2.78  #Sup     : 2027
% 8.28/2.78  #Fact    : 0
% 8.28/2.78  #Define  : 0
% 8.28/2.78  #Split   : 21
% 8.28/2.78  #Chain   : 0
% 8.28/2.78  #Close   : 0
% 8.28/2.78  
% 8.28/2.78  Ordering : KBO
% 8.28/2.78  
% 8.28/2.78  Simplification rules
% 8.28/2.78  ----------------------
% 8.28/2.78  #Subsume      : 378
% 8.28/2.78  #Demod        : 2071
% 8.28/2.78  #Tautology    : 998
% 8.28/2.78  #SimpNegUnit  : 28
% 8.28/2.78  #BackRed      : 98
% 8.28/2.78  
% 8.28/2.78  #Partial instantiations: 0
% 8.28/2.78  #Strategies tried      : 1
% 8.28/2.78  
% 8.28/2.79  Timing (in seconds)
% 8.28/2.79  ----------------------
% 8.28/2.79  Preprocessing        : 0.45
% 8.28/2.79  Parsing              : 0.23
% 8.28/2.79  CNF conversion       : 0.03
% 8.28/2.79  Main loop            : 1.52
% 8.28/2.79  Inferencing          : 0.47
% 8.28/2.79  Reduction            : 0.56
% 8.28/2.79  Demodulation         : 0.41
% 8.28/2.79  BG Simplification    : 0.06
% 8.28/2.79  Subsumption          : 0.32
% 8.28/2.79  Abstraction          : 0.06
% 8.28/2.79  MUC search           : 0.00
% 8.28/2.79  Cooper               : 0.00
% 8.28/2.79  Total                : 2.03
% 8.28/2.79  Index Insertion      : 0.00
% 8.28/2.79  Index Deletion       : 0.00
% 8.28/2.79  Index Matching       : 0.00
% 8.28/2.79  BG Taut test         : 0.00
%------------------------------------------------------------------------------
