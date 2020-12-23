%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:12:17 EST 2020

% Result     : Theorem 7.65s
% Output     : CNFRefutation 7.65s
% Verified   : 
% Statistics : Number of formulae       :  156 ( 445 expanded)
%              Number of leaves         :   52 ( 175 expanded)
%              Depth                    :   12
%              Number of atoms          :  290 (1406 expanded)
%              Number of equality atoms :   51 ( 125 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > v1_partfun1 > r2_hidden > r1_tarski > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_2

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

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(v1_partfun1,type,(
    v1_partfun1: ( $i * $i ) > $o )).

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_178,negated_conjecture,(
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

tff(f_49,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => v1_xboole_0(k2_zfmisc_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_zfmisc_1)).

tff(f_56,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_xboole_0(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_subset_1)).

tff(f_136,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_86,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v2_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_funct_1)).

tff(f_134,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_120,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( v1_funct_1(k1_partfun1(A,B,C,D,E,F))
        & m1_subset_1(k1_partfun1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).

tff(f_124,axiom,(
    ! [A] :
      ( v1_partfun1(k6_partfun1(A),A)
      & m1_subset_1(k6_partfun1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).

tff(f_100,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_158,axiom,(
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

tff(f_39,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_45,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_71,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_63,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_92,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_69,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_82,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_78,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => r1_tarski(k2_relat_1(k5_relat_1(A,B)),k2_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_relat_1)).

tff(f_108,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A) )
     => ( v2_funct_2(B,A)
      <=> k2_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_funct_2)).

tff(c_70,plain,
    ( ~ v2_funct_2('#skF_6','#skF_3')
    | ~ v2_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_178])).

tff(c_122,plain,(
    ~ v2_funct_1('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_70])).

tff(c_20,plain,(
    ! [A_12,B_13] :
      ( v1_xboole_0(k2_zfmisc_1(A_12,B_13))
      | ~ v1_xboole_0(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_80,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_178])).

tff(c_137,plain,(
    ! [B_78,A_79] :
      ( v1_xboole_0(B_78)
      | ~ m1_subset_1(B_78,k1_zfmisc_1(A_79))
      | ~ v1_xboole_0(A_79) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_149,plain,
    ( v1_xboole_0('#skF_5')
    | ~ v1_xboole_0(k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_80,c_137])).

tff(c_170,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_149])).

tff(c_178,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_20,c_170])).

tff(c_64,plain,(
    ! [A_51] : k6_relat_1(A_51) = k6_partfun1(A_51) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_40,plain,(
    ! [A_28] : v2_funct_1(k6_relat_1(A_28)) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_85,plain,(
    ! [A_28] : v2_funct_1(k6_partfun1(A_28)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_40])).

tff(c_84,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_178])).

tff(c_78,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_178])).

tff(c_74,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_178])).

tff(c_1053,plain,(
    ! [D_166,A_165,E_168,C_167,B_164,F_169] :
      ( k1_partfun1(A_165,B_164,C_167,D_166,E_168,F_169) = k5_relat_1(E_168,F_169)
      | ~ m1_subset_1(F_169,k1_zfmisc_1(k2_zfmisc_1(C_167,D_166)))
      | ~ v1_funct_1(F_169)
      | ~ m1_subset_1(E_168,k1_zfmisc_1(k2_zfmisc_1(A_165,B_164)))
      | ~ v1_funct_1(E_168) ) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_1061,plain,(
    ! [A_165,B_164,E_168] :
      ( k1_partfun1(A_165,B_164,'#skF_4','#skF_3',E_168,'#skF_6') = k5_relat_1(E_168,'#skF_6')
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1(E_168,k1_zfmisc_1(k2_zfmisc_1(A_165,B_164)))
      | ~ v1_funct_1(E_168) ) ),
    inference(resolution,[status(thm)],[c_74,c_1053])).

tff(c_2655,plain,(
    ! [A_255,B_256,E_257] :
      ( k1_partfun1(A_255,B_256,'#skF_4','#skF_3',E_257,'#skF_6') = k5_relat_1(E_257,'#skF_6')
      | ~ m1_subset_1(E_257,k1_zfmisc_1(k2_zfmisc_1(A_255,B_256)))
      | ~ v1_funct_1(E_257) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_1061])).

tff(c_2685,plain,
    ( k1_partfun1('#skF_3','#skF_4','#skF_4','#skF_3','#skF_5','#skF_6') = k5_relat_1('#skF_5','#skF_6')
    | ~ v1_funct_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_80,c_2655])).

tff(c_2699,plain,(
    k1_partfun1('#skF_3','#skF_4','#skF_4','#skF_3','#skF_5','#skF_6') = k5_relat_1('#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_2685])).

tff(c_54,plain,(
    ! [D_41,B_39,A_38,F_43,E_42,C_40] :
      ( m1_subset_1(k1_partfun1(A_38,B_39,C_40,D_41,E_42,F_43),k1_zfmisc_1(k2_zfmisc_1(A_38,D_41)))
      | ~ m1_subset_1(F_43,k1_zfmisc_1(k2_zfmisc_1(C_40,D_41)))
      | ~ v1_funct_1(F_43)
      | ~ m1_subset_1(E_42,k1_zfmisc_1(k2_zfmisc_1(A_38,B_39)))
      | ~ v1_funct_1(E_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_3258,plain,
    ( m1_subset_1(k5_relat_1('#skF_5','#skF_6'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3')))
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_3')))
    | ~ v1_funct_1('#skF_6')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4')))
    | ~ v1_funct_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_2699,c_54])).

tff(c_3265,plain,(
    m1_subset_1(k5_relat_1('#skF_5','#skF_6'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_80,c_78,c_74,c_3258])).

tff(c_60,plain,(
    ! [A_44] : m1_subset_1(k6_partfun1(A_44),k1_zfmisc_1(k2_zfmisc_1(A_44,A_44))) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_72,plain,(
    r2_relset_1('#skF_3','#skF_3',k1_partfun1('#skF_3','#skF_4','#skF_4','#skF_3','#skF_5','#skF_6'),k6_partfun1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_178])).

tff(c_712,plain,(
    ! [D_135,C_136,A_137,B_138] :
      ( D_135 = C_136
      | ~ r2_relset_1(A_137,B_138,C_136,D_135)
      | ~ m1_subset_1(D_135,k1_zfmisc_1(k2_zfmisc_1(A_137,B_138)))
      | ~ m1_subset_1(C_136,k1_zfmisc_1(k2_zfmisc_1(A_137,B_138))) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_718,plain,
    ( k1_partfun1('#skF_3','#skF_4','#skF_4','#skF_3','#skF_5','#skF_6') = k6_partfun1('#skF_3')
    | ~ m1_subset_1(k6_partfun1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3')))
    | ~ m1_subset_1(k1_partfun1('#skF_3','#skF_4','#skF_4','#skF_3','#skF_5','#skF_6'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3'))) ),
    inference(resolution,[status(thm)],[c_72,c_712])).

tff(c_729,plain,
    ( k1_partfun1('#skF_3','#skF_4','#skF_4','#skF_3','#skF_5','#skF_6') = k6_partfun1('#skF_3')
    | ~ m1_subset_1(k1_partfun1('#skF_3','#skF_4','#skF_4','#skF_3','#skF_5','#skF_6'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_718])).

tff(c_3522,plain,(
    k5_relat_1('#skF_5','#skF_6') = k6_partfun1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3265,c_2699,c_2699,c_729])).

tff(c_82,plain,(
    v1_funct_2('#skF_5','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_178])).

tff(c_76,plain,(
    v1_funct_2('#skF_6','#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_178])).

tff(c_68,plain,(
    ! [D_55,B_53,E_57,A_52,C_54] :
      ( k1_xboole_0 = C_54
      | v2_funct_1(D_55)
      | ~ v2_funct_1(k1_partfun1(A_52,B_53,B_53,C_54,D_55,E_57))
      | ~ m1_subset_1(E_57,k1_zfmisc_1(k2_zfmisc_1(B_53,C_54)))
      | ~ v1_funct_2(E_57,B_53,C_54)
      | ~ v1_funct_1(E_57)
      | ~ m1_subset_1(D_55,k1_zfmisc_1(k2_zfmisc_1(A_52,B_53)))
      | ~ v1_funct_2(D_55,A_52,B_53)
      | ~ v1_funct_1(D_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_3255,plain,
    ( k1_xboole_0 = '#skF_3'
    | v2_funct_1('#skF_5')
    | ~ v2_funct_1(k5_relat_1('#skF_5','#skF_6'))
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_3')))
    | ~ v1_funct_2('#skF_6','#skF_4','#skF_3')
    | ~ v1_funct_1('#skF_6')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4')))
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_2699,c_68])).

tff(c_3262,plain,
    ( k1_xboole_0 = '#skF_3'
    | v2_funct_1('#skF_5')
    | ~ v2_funct_1(k5_relat_1('#skF_5','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_82,c_80,c_78,c_76,c_74,c_3255])).

tff(c_3263,plain,
    ( k1_xboole_0 = '#skF_3'
    | ~ v2_funct_1(k5_relat_1('#skF_5','#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_122,c_3262])).

tff(c_3267,plain,(
    ~ v2_funct_1(k5_relat_1('#skF_5','#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_3263])).

tff(c_3528,plain,(
    ~ v2_funct_1(k6_partfun1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3522,c_3267])).

tff(c_3538,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_85,c_3528])).

tff(c_3539,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_3263])).

tff(c_12,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_3592,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3539,c_12])).

tff(c_3594,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_178,c_3592])).

tff(c_3595,plain,(
    v1_xboole_0('#skF_5') ),
    inference(splitRight,[status(thm)],[c_149])).

tff(c_131,plain,(
    ! [A_74,B_75] :
      ( r2_hidden('#skF_2'(A_74,B_75),A_74)
      | r1_tarski(A_74,B_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_135,plain,(
    ! [A_74,B_75] :
      ( ~ v1_xboole_0(A_74)
      | r1_tarski(A_74,B_75) ) ),
    inference(resolution,[status(thm)],[c_131,c_2])).

tff(c_3615,plain,(
    ! [B_276,A_277] :
      ( B_276 = A_277
      | ~ r1_tarski(B_276,A_277)
      | ~ r1_tarski(A_277,B_276) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_3639,plain,(
    ! [B_282,A_283] :
      ( B_282 = A_283
      | ~ r1_tarski(B_282,A_283)
      | ~ v1_xboole_0(A_283) ) ),
    inference(resolution,[status(thm)],[c_135,c_3615])).

tff(c_3649,plain,(
    ! [B_284,A_285] :
      ( B_284 = A_285
      | ~ v1_xboole_0(B_284)
      | ~ v1_xboole_0(A_285) ) ),
    inference(resolution,[status(thm)],[c_135,c_3639])).

tff(c_3681,plain,(
    ! [A_288] :
      ( k1_xboole_0 = A_288
      | ~ v1_xboole_0(A_288) ) ),
    inference(resolution,[status(thm)],[c_12,c_3649])).

tff(c_3699,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_3595,c_3681])).

tff(c_3608,plain,(
    ! [A_274] :
      ( v1_xboole_0(k6_partfun1(A_274))
      | ~ v1_xboole_0(k2_zfmisc_1(A_274,A_274)) ) ),
    inference(resolution,[status(thm)],[c_60,c_137])).

tff(c_3613,plain,(
    ! [B_13] :
      ( v1_xboole_0(k6_partfun1(B_13))
      | ~ v1_xboole_0(B_13) ) ),
    inference(resolution,[status(thm)],[c_20,c_3608])).

tff(c_3697,plain,(
    ! [B_13] :
      ( k6_partfun1(B_13) = k1_xboole_0
      | ~ v1_xboole_0(B_13) ) ),
    inference(resolution,[status(thm)],[c_3613,c_3681])).

tff(c_3760,plain,(
    ! [B_290] :
      ( k6_partfun1(B_290) = '#skF_5'
      | ~ v1_xboole_0(B_290) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3699,c_3697])).

tff(c_3771,plain,(
    k6_partfun1('#skF_5') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_3595,c_3760])).

tff(c_3795,plain,(
    v2_funct_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_3771,c_85])).

tff(c_3802,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_122,c_3795])).

tff(c_3803,plain,(
    ~ v2_funct_2('#skF_6','#skF_3') ),
    inference(splitRight,[status(thm)],[c_70])).

tff(c_30,plain,(
    ! [A_22,B_23] : v1_relat_1(k2_zfmisc_1(A_22,B_23)) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_3827,plain,(
    ! [B_301,A_302] :
      ( v1_relat_1(B_301)
      | ~ m1_subset_1(B_301,k1_zfmisc_1(A_302))
      | ~ v1_relat_1(A_302) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_3833,plain,
    ( v1_relat_1('#skF_6')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_4','#skF_3')) ),
    inference(resolution,[status(thm)],[c_74,c_3827])).

tff(c_3842,plain,(
    v1_relat_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_3833])).

tff(c_4043,plain,(
    ! [C_329,B_330,A_331] :
      ( v5_relat_1(C_329,B_330)
      | ~ m1_subset_1(C_329,k1_zfmisc_1(k2_zfmisc_1(A_331,B_330))) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_4054,plain,(
    v5_relat_1('#skF_6','#skF_3') ),
    inference(resolution,[status(thm)],[c_74,c_4043])).

tff(c_28,plain,(
    ! [B_21,A_20] :
      ( r1_tarski(k2_relat_1(B_21),A_20)
      | ~ v5_relat_1(B_21,A_20)
      | ~ v1_relat_1(B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_3836,plain,
    ( v1_relat_1('#skF_5')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_80,c_3827])).

tff(c_3845,plain,(
    v1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_3836])).

tff(c_36,plain,(
    ! [A_27] : k2_relat_1(k6_relat_1(A_27)) = A_27 ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_87,plain,(
    ! [A_27] : k2_relat_1(k6_partfun1(A_27)) = A_27 ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_36])).

tff(c_4693,plain,(
    ! [A_385,C_387,E_388,D_386,B_384,F_389] :
      ( k1_partfun1(A_385,B_384,C_387,D_386,E_388,F_389) = k5_relat_1(E_388,F_389)
      | ~ m1_subset_1(F_389,k1_zfmisc_1(k2_zfmisc_1(C_387,D_386)))
      | ~ v1_funct_1(F_389)
      | ~ m1_subset_1(E_388,k1_zfmisc_1(k2_zfmisc_1(A_385,B_384)))
      | ~ v1_funct_1(E_388) ) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_4701,plain,(
    ! [A_385,B_384,E_388] :
      ( k1_partfun1(A_385,B_384,'#skF_4','#skF_3',E_388,'#skF_6') = k5_relat_1(E_388,'#skF_6')
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1(E_388,k1_zfmisc_1(k2_zfmisc_1(A_385,B_384)))
      | ~ v1_funct_1(E_388) ) ),
    inference(resolution,[status(thm)],[c_74,c_4693])).

tff(c_5673,plain,(
    ! [A_449,B_450,E_451] :
      ( k1_partfun1(A_449,B_450,'#skF_4','#skF_3',E_451,'#skF_6') = k5_relat_1(E_451,'#skF_6')
      | ~ m1_subset_1(E_451,k1_zfmisc_1(k2_zfmisc_1(A_449,B_450)))
      | ~ v1_funct_1(E_451) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_4701])).

tff(c_5694,plain,
    ( k1_partfun1('#skF_3','#skF_4','#skF_4','#skF_3','#skF_5','#skF_6') = k5_relat_1('#skF_5','#skF_6')
    | ~ v1_funct_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_80,c_5673])).

tff(c_5702,plain,(
    k1_partfun1('#skF_3','#skF_4','#skF_4','#skF_3','#skF_5','#skF_6') = k5_relat_1('#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_5694])).

tff(c_6017,plain,
    ( m1_subset_1(k5_relat_1('#skF_5','#skF_6'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3')))
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_3')))
    | ~ v1_funct_1('#skF_6')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4')))
    | ~ v1_funct_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_5702,c_54])).

tff(c_6023,plain,(
    m1_subset_1(k5_relat_1('#skF_5','#skF_6'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_80,c_78,c_74,c_6017])).

tff(c_4314,plain,(
    ! [D_351,C_352,A_353,B_354] :
      ( D_351 = C_352
      | ~ r2_relset_1(A_353,B_354,C_352,D_351)
      | ~ m1_subset_1(D_351,k1_zfmisc_1(k2_zfmisc_1(A_353,B_354)))
      | ~ m1_subset_1(C_352,k1_zfmisc_1(k2_zfmisc_1(A_353,B_354))) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_4320,plain,
    ( k1_partfun1('#skF_3','#skF_4','#skF_4','#skF_3','#skF_5','#skF_6') = k6_partfun1('#skF_3')
    | ~ m1_subset_1(k6_partfun1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3')))
    | ~ m1_subset_1(k1_partfun1('#skF_3','#skF_4','#skF_4','#skF_3','#skF_5','#skF_6'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3'))) ),
    inference(resolution,[status(thm)],[c_72,c_4314])).

tff(c_4331,plain,
    ( k1_partfun1('#skF_3','#skF_4','#skF_4','#skF_3','#skF_5','#skF_6') = k6_partfun1('#skF_3')
    | ~ m1_subset_1(k1_partfun1('#skF_3','#skF_4','#skF_4','#skF_3','#skF_5','#skF_6'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_4320])).

tff(c_4377,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_3','#skF_4','#skF_4','#skF_3','#skF_5','#skF_6'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_4331])).

tff(c_7059,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6023,c_5702,c_4377])).

tff(c_7060,plain,(
    k1_partfun1('#skF_3','#skF_4','#skF_4','#skF_3','#skF_5','#skF_6') = k6_partfun1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_4331])).

tff(c_7427,plain,(
    ! [C_521,E_522,A_519,B_518,F_523,D_520] :
      ( k1_partfun1(A_519,B_518,C_521,D_520,E_522,F_523) = k5_relat_1(E_522,F_523)
      | ~ m1_subset_1(F_523,k1_zfmisc_1(k2_zfmisc_1(C_521,D_520)))
      | ~ v1_funct_1(F_523)
      | ~ m1_subset_1(E_522,k1_zfmisc_1(k2_zfmisc_1(A_519,B_518)))
      | ~ v1_funct_1(E_522) ) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_7435,plain,(
    ! [A_519,B_518,E_522] :
      ( k1_partfun1(A_519,B_518,'#skF_4','#skF_3',E_522,'#skF_6') = k5_relat_1(E_522,'#skF_6')
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1(E_522,k1_zfmisc_1(k2_zfmisc_1(A_519,B_518)))
      | ~ v1_funct_1(E_522) ) ),
    inference(resolution,[status(thm)],[c_74,c_7427])).

tff(c_8846,plain,(
    ! [A_593,B_594,E_595] :
      ( k1_partfun1(A_593,B_594,'#skF_4','#skF_3',E_595,'#skF_6') = k5_relat_1(E_595,'#skF_6')
      | ~ m1_subset_1(E_595,k1_zfmisc_1(k2_zfmisc_1(A_593,B_594)))
      | ~ v1_funct_1(E_595) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_7435])).

tff(c_8876,plain,
    ( k1_partfun1('#skF_3','#skF_4','#skF_4','#skF_3','#skF_5','#skF_6') = k5_relat_1('#skF_5','#skF_6')
    | ~ v1_funct_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_80,c_8846])).

tff(c_8890,plain,(
    k5_relat_1('#skF_5','#skF_6') = k6_partfun1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_7060,c_8876])).

tff(c_32,plain,(
    ! [A_24,B_26] :
      ( r1_tarski(k2_relat_1(k5_relat_1(A_24,B_26)),k2_relat_1(B_26))
      | ~ v1_relat_1(B_26)
      | ~ v1_relat_1(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_8894,plain,
    ( r1_tarski(k2_relat_1(k6_partfun1('#skF_3')),k2_relat_1('#skF_6'))
    | ~ v1_relat_1('#skF_6')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_8890,c_32])).

tff(c_8898,plain,(
    r1_tarski('#skF_3',k2_relat_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3845,c_3842,c_87,c_8894])).

tff(c_14,plain,(
    ! [B_11,A_10] :
      ( B_11 = A_10
      | ~ r1_tarski(B_11,A_10)
      | ~ r1_tarski(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_8912,plain,
    ( k2_relat_1('#skF_6') = '#skF_3'
    | ~ r1_tarski(k2_relat_1('#skF_6'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_8898,c_14])).

tff(c_8913,plain,(
    ~ r1_tarski(k2_relat_1('#skF_6'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_8912])).

tff(c_8929,plain,
    ( ~ v5_relat_1('#skF_6','#skF_3')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_28,c_8913])).

tff(c_8936,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3842,c_4054,c_8929])).

tff(c_8937,plain,(
    k2_relat_1('#skF_6') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_8912])).

tff(c_18,plain,(
    ! [B_11] : r1_tarski(B_11,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_3953,plain,(
    ! [B_324,A_325] :
      ( v5_relat_1(B_324,A_325)
      | ~ r1_tarski(k2_relat_1(B_324),A_325)
      | ~ v1_relat_1(B_324) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_3968,plain,(
    ! [B_324] :
      ( v5_relat_1(B_324,k2_relat_1(B_324))
      | ~ v1_relat_1(B_324) ) ),
    inference(resolution,[status(thm)],[c_18,c_3953])).

tff(c_4062,plain,(
    ! [B_333] :
      ( v2_funct_2(B_333,k2_relat_1(B_333))
      | ~ v5_relat_1(B_333,k2_relat_1(B_333))
      | ~ v1_relat_1(B_333) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_4072,plain,(
    ! [B_324] :
      ( v2_funct_2(B_324,k2_relat_1(B_324))
      | ~ v1_relat_1(B_324) ) ),
    inference(resolution,[status(thm)],[c_3968,c_4062])).

tff(c_8950,plain,
    ( v2_funct_2('#skF_6','#skF_3')
    | ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_8937,c_4072])).

tff(c_8967,plain,(
    v2_funct_2('#skF_6','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3842,c_8950])).

tff(c_8969,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3803,c_8967])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n003.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 19:19:57 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.65/2.62  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.65/2.63  
% 7.65/2.63  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.65/2.63  %$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > v1_partfun1 > r2_hidden > r1_tarski > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_2
% 7.65/2.63  
% 7.65/2.63  %Foreground sorts:
% 7.65/2.63  
% 7.65/2.63  
% 7.65/2.63  %Background operators:
% 7.65/2.63  
% 7.65/2.63  
% 7.65/2.63  %Foreground operators:
% 7.65/2.63  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 7.65/2.63  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 7.65/2.63  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.65/2.63  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 7.65/2.63  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 7.65/2.63  tff('#skF_1', type, '#skF_1': $i > $i).
% 7.65/2.63  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 7.65/2.63  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 7.65/2.63  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.65/2.63  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 7.65/2.63  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 7.65/2.63  tff('#skF_5', type, '#skF_5': $i).
% 7.65/2.63  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 7.65/2.63  tff('#skF_6', type, '#skF_6': $i).
% 7.65/2.63  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 7.65/2.63  tff('#skF_3', type, '#skF_3': $i).
% 7.65/2.63  tff(v2_funct_2, type, v2_funct_2: ($i * $i) > $o).
% 7.65/2.63  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 7.65/2.63  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 7.65/2.63  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 7.65/2.63  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.65/2.63  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 7.65/2.63  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 7.65/2.63  tff('#skF_4', type, '#skF_4': $i).
% 7.65/2.63  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 7.65/2.63  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.65/2.63  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 7.65/2.63  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 7.65/2.63  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 7.65/2.63  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 7.65/2.63  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 7.65/2.63  
% 7.65/2.66  tff(f_178, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (r2_relset_1(A, A, k1_partfun1(A, B, B, A, C, D), k6_partfun1(A)) => (v2_funct_1(C) & v2_funct_2(D, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_funct_2)).
% 7.65/2.66  tff(f_49, axiom, (![A, B]: (v1_xboole_0(A) => v1_xboole_0(k2_zfmisc_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc4_zfmisc_1)).
% 7.65/2.66  tff(f_56, axiom, (![A]: (v1_xboole_0(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_subset_1)).
% 7.65/2.66  tff(f_136, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 7.65/2.66  tff(f_86, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v2_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc4_funct_1)).
% 7.65/2.66  tff(f_134, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 7.65/2.66  tff(f_120, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (v1_funct_1(k1_partfun1(A, B, C, D, E, F)) & m1_subset_1(k1_partfun1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 7.65/2.66  tff(f_124, axiom, (![A]: (v1_partfun1(k6_partfun1(A), A) & m1_subset_1(k6_partfun1(A), k1_zfmisc_1(k2_zfmisc_1(A, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_partfun1)).
% 7.65/2.66  tff(f_100, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 7.65/2.66  tff(f_158, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, B, C)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (v2_funct_1(k1_partfun1(A, B, B, C, D, E)) => (((C = k1_xboole_0) & ~(B = k1_xboole_0)) | v2_funct_1(D))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t26_funct_2)).
% 7.65/2.66  tff(f_39, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 7.65/2.66  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 7.65/2.66  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 7.65/2.66  tff(f_45, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 7.65/2.66  tff(f_71, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 7.65/2.66  tff(f_63, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 7.65/2.66  tff(f_92, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 7.65/2.66  tff(f_69, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 7.65/2.66  tff(f_82, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 7.65/2.66  tff(f_78, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => r1_tarski(k2_relat_1(k5_relat_1(A, B)), k2_relat_1(B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t45_relat_1)).
% 7.65/2.66  tff(f_108, axiom, (![A, B]: ((v1_relat_1(B) & v5_relat_1(B, A)) => (v2_funct_2(B, A) <=> (k2_relat_1(B) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_funct_2)).
% 7.65/2.66  tff(c_70, plain, (~v2_funct_2('#skF_6', '#skF_3') | ~v2_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_178])).
% 7.65/2.66  tff(c_122, plain, (~v2_funct_1('#skF_5')), inference(splitLeft, [status(thm)], [c_70])).
% 7.65/2.66  tff(c_20, plain, (![A_12, B_13]: (v1_xboole_0(k2_zfmisc_1(A_12, B_13)) | ~v1_xboole_0(A_12))), inference(cnfTransformation, [status(thm)], [f_49])).
% 7.65/2.66  tff(c_80, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_178])).
% 7.65/2.66  tff(c_137, plain, (![B_78, A_79]: (v1_xboole_0(B_78) | ~m1_subset_1(B_78, k1_zfmisc_1(A_79)) | ~v1_xboole_0(A_79))), inference(cnfTransformation, [status(thm)], [f_56])).
% 7.65/2.66  tff(c_149, plain, (v1_xboole_0('#skF_5') | ~v1_xboole_0(k2_zfmisc_1('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_80, c_137])).
% 7.65/2.66  tff(c_170, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_3', '#skF_4'))), inference(splitLeft, [status(thm)], [c_149])).
% 7.65/2.66  tff(c_178, plain, (~v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_20, c_170])).
% 7.65/2.66  tff(c_64, plain, (![A_51]: (k6_relat_1(A_51)=k6_partfun1(A_51))), inference(cnfTransformation, [status(thm)], [f_136])).
% 7.65/2.66  tff(c_40, plain, (![A_28]: (v2_funct_1(k6_relat_1(A_28)))), inference(cnfTransformation, [status(thm)], [f_86])).
% 7.65/2.66  tff(c_85, plain, (![A_28]: (v2_funct_1(k6_partfun1(A_28)))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_40])).
% 7.65/2.66  tff(c_84, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_178])).
% 7.65/2.66  tff(c_78, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_178])).
% 7.65/2.66  tff(c_74, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_178])).
% 7.65/2.66  tff(c_1053, plain, (![D_166, A_165, E_168, C_167, B_164, F_169]: (k1_partfun1(A_165, B_164, C_167, D_166, E_168, F_169)=k5_relat_1(E_168, F_169) | ~m1_subset_1(F_169, k1_zfmisc_1(k2_zfmisc_1(C_167, D_166))) | ~v1_funct_1(F_169) | ~m1_subset_1(E_168, k1_zfmisc_1(k2_zfmisc_1(A_165, B_164))) | ~v1_funct_1(E_168))), inference(cnfTransformation, [status(thm)], [f_134])).
% 7.65/2.66  tff(c_1061, plain, (![A_165, B_164, E_168]: (k1_partfun1(A_165, B_164, '#skF_4', '#skF_3', E_168, '#skF_6')=k5_relat_1(E_168, '#skF_6') | ~v1_funct_1('#skF_6') | ~m1_subset_1(E_168, k1_zfmisc_1(k2_zfmisc_1(A_165, B_164))) | ~v1_funct_1(E_168))), inference(resolution, [status(thm)], [c_74, c_1053])).
% 7.65/2.66  tff(c_2655, plain, (![A_255, B_256, E_257]: (k1_partfun1(A_255, B_256, '#skF_4', '#skF_3', E_257, '#skF_6')=k5_relat_1(E_257, '#skF_6') | ~m1_subset_1(E_257, k1_zfmisc_1(k2_zfmisc_1(A_255, B_256))) | ~v1_funct_1(E_257))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_1061])).
% 7.65/2.66  tff(c_2685, plain, (k1_partfun1('#skF_3', '#skF_4', '#skF_4', '#skF_3', '#skF_5', '#skF_6')=k5_relat_1('#skF_5', '#skF_6') | ~v1_funct_1('#skF_5')), inference(resolution, [status(thm)], [c_80, c_2655])).
% 7.65/2.66  tff(c_2699, plain, (k1_partfun1('#skF_3', '#skF_4', '#skF_4', '#skF_3', '#skF_5', '#skF_6')=k5_relat_1('#skF_5', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_84, c_2685])).
% 7.65/2.66  tff(c_54, plain, (![D_41, B_39, A_38, F_43, E_42, C_40]: (m1_subset_1(k1_partfun1(A_38, B_39, C_40, D_41, E_42, F_43), k1_zfmisc_1(k2_zfmisc_1(A_38, D_41))) | ~m1_subset_1(F_43, k1_zfmisc_1(k2_zfmisc_1(C_40, D_41))) | ~v1_funct_1(F_43) | ~m1_subset_1(E_42, k1_zfmisc_1(k2_zfmisc_1(A_38, B_39))) | ~v1_funct_1(E_42))), inference(cnfTransformation, [status(thm)], [f_120])).
% 7.65/2.66  tff(c_3258, plain, (m1_subset_1(k5_relat_1('#skF_5', '#skF_6'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3'))) | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_3'))) | ~v1_funct_1('#skF_6') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4'))) | ~v1_funct_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_2699, c_54])).
% 7.65/2.66  tff(c_3265, plain, (m1_subset_1(k5_relat_1('#skF_5', '#skF_6'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_84, c_80, c_78, c_74, c_3258])).
% 7.65/2.66  tff(c_60, plain, (![A_44]: (m1_subset_1(k6_partfun1(A_44), k1_zfmisc_1(k2_zfmisc_1(A_44, A_44))))), inference(cnfTransformation, [status(thm)], [f_124])).
% 7.65/2.66  tff(c_72, plain, (r2_relset_1('#skF_3', '#skF_3', k1_partfun1('#skF_3', '#skF_4', '#skF_4', '#skF_3', '#skF_5', '#skF_6'), k6_partfun1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_178])).
% 7.65/2.66  tff(c_712, plain, (![D_135, C_136, A_137, B_138]: (D_135=C_136 | ~r2_relset_1(A_137, B_138, C_136, D_135) | ~m1_subset_1(D_135, k1_zfmisc_1(k2_zfmisc_1(A_137, B_138))) | ~m1_subset_1(C_136, k1_zfmisc_1(k2_zfmisc_1(A_137, B_138))))), inference(cnfTransformation, [status(thm)], [f_100])).
% 7.65/2.66  tff(c_718, plain, (k1_partfun1('#skF_3', '#skF_4', '#skF_4', '#skF_3', '#skF_5', '#skF_6')=k6_partfun1('#skF_3') | ~m1_subset_1(k6_partfun1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3'))) | ~m1_subset_1(k1_partfun1('#skF_3', '#skF_4', '#skF_4', '#skF_3', '#skF_5', '#skF_6'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3')))), inference(resolution, [status(thm)], [c_72, c_712])).
% 7.65/2.66  tff(c_729, plain, (k1_partfun1('#skF_3', '#skF_4', '#skF_4', '#skF_3', '#skF_5', '#skF_6')=k6_partfun1('#skF_3') | ~m1_subset_1(k1_partfun1('#skF_3', '#skF_4', '#skF_4', '#skF_3', '#skF_5', '#skF_6'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_718])).
% 7.65/2.66  tff(c_3522, plain, (k5_relat_1('#skF_5', '#skF_6')=k6_partfun1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_3265, c_2699, c_2699, c_729])).
% 7.65/2.66  tff(c_82, plain, (v1_funct_2('#skF_5', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_178])).
% 7.65/2.66  tff(c_76, plain, (v1_funct_2('#skF_6', '#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_178])).
% 7.65/2.66  tff(c_68, plain, (![D_55, B_53, E_57, A_52, C_54]: (k1_xboole_0=C_54 | v2_funct_1(D_55) | ~v2_funct_1(k1_partfun1(A_52, B_53, B_53, C_54, D_55, E_57)) | ~m1_subset_1(E_57, k1_zfmisc_1(k2_zfmisc_1(B_53, C_54))) | ~v1_funct_2(E_57, B_53, C_54) | ~v1_funct_1(E_57) | ~m1_subset_1(D_55, k1_zfmisc_1(k2_zfmisc_1(A_52, B_53))) | ~v1_funct_2(D_55, A_52, B_53) | ~v1_funct_1(D_55))), inference(cnfTransformation, [status(thm)], [f_158])).
% 7.65/2.66  tff(c_3255, plain, (k1_xboole_0='#skF_3' | v2_funct_1('#skF_5') | ~v2_funct_1(k5_relat_1('#skF_5', '#skF_6')) | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_3'))) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_3') | ~v1_funct_1('#skF_6') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4'))) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_4') | ~v1_funct_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_2699, c_68])).
% 7.65/2.66  tff(c_3262, plain, (k1_xboole_0='#skF_3' | v2_funct_1('#skF_5') | ~v2_funct_1(k5_relat_1('#skF_5', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_84, c_82, c_80, c_78, c_76, c_74, c_3255])).
% 7.65/2.66  tff(c_3263, plain, (k1_xboole_0='#skF_3' | ~v2_funct_1(k5_relat_1('#skF_5', '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_122, c_3262])).
% 7.65/2.66  tff(c_3267, plain, (~v2_funct_1(k5_relat_1('#skF_5', '#skF_6'))), inference(splitLeft, [status(thm)], [c_3263])).
% 7.65/2.66  tff(c_3528, plain, (~v2_funct_1(k6_partfun1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_3522, c_3267])).
% 7.65/2.66  tff(c_3538, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_85, c_3528])).
% 7.65/2.66  tff(c_3539, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_3263])).
% 7.65/2.66  tff(c_12, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 7.65/2.66  tff(c_3592, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_3539, c_12])).
% 7.65/2.66  tff(c_3594, plain, $false, inference(negUnitSimplification, [status(thm)], [c_178, c_3592])).
% 7.65/2.66  tff(c_3595, plain, (v1_xboole_0('#skF_5')), inference(splitRight, [status(thm)], [c_149])).
% 7.65/2.66  tff(c_131, plain, (![A_74, B_75]: (r2_hidden('#skF_2'(A_74, B_75), A_74) | r1_tarski(A_74, B_75))), inference(cnfTransformation, [status(thm)], [f_38])).
% 7.65/2.66  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 7.65/2.66  tff(c_135, plain, (![A_74, B_75]: (~v1_xboole_0(A_74) | r1_tarski(A_74, B_75))), inference(resolution, [status(thm)], [c_131, c_2])).
% 7.65/2.66  tff(c_3615, plain, (![B_276, A_277]: (B_276=A_277 | ~r1_tarski(B_276, A_277) | ~r1_tarski(A_277, B_276))), inference(cnfTransformation, [status(thm)], [f_45])).
% 7.65/2.66  tff(c_3639, plain, (![B_282, A_283]: (B_282=A_283 | ~r1_tarski(B_282, A_283) | ~v1_xboole_0(A_283))), inference(resolution, [status(thm)], [c_135, c_3615])).
% 7.65/2.66  tff(c_3649, plain, (![B_284, A_285]: (B_284=A_285 | ~v1_xboole_0(B_284) | ~v1_xboole_0(A_285))), inference(resolution, [status(thm)], [c_135, c_3639])).
% 7.65/2.66  tff(c_3681, plain, (![A_288]: (k1_xboole_0=A_288 | ~v1_xboole_0(A_288))), inference(resolution, [status(thm)], [c_12, c_3649])).
% 7.65/2.66  tff(c_3699, plain, (k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_3595, c_3681])).
% 7.65/2.66  tff(c_3608, plain, (![A_274]: (v1_xboole_0(k6_partfun1(A_274)) | ~v1_xboole_0(k2_zfmisc_1(A_274, A_274)))), inference(resolution, [status(thm)], [c_60, c_137])).
% 7.65/2.66  tff(c_3613, plain, (![B_13]: (v1_xboole_0(k6_partfun1(B_13)) | ~v1_xboole_0(B_13))), inference(resolution, [status(thm)], [c_20, c_3608])).
% 7.65/2.66  tff(c_3697, plain, (![B_13]: (k6_partfun1(B_13)=k1_xboole_0 | ~v1_xboole_0(B_13))), inference(resolution, [status(thm)], [c_3613, c_3681])).
% 7.65/2.66  tff(c_3760, plain, (![B_290]: (k6_partfun1(B_290)='#skF_5' | ~v1_xboole_0(B_290))), inference(demodulation, [status(thm), theory('equality')], [c_3699, c_3697])).
% 7.65/2.66  tff(c_3771, plain, (k6_partfun1('#skF_5')='#skF_5'), inference(resolution, [status(thm)], [c_3595, c_3760])).
% 7.65/2.66  tff(c_3795, plain, (v2_funct_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_3771, c_85])).
% 7.65/2.66  tff(c_3802, plain, $false, inference(negUnitSimplification, [status(thm)], [c_122, c_3795])).
% 7.65/2.66  tff(c_3803, plain, (~v2_funct_2('#skF_6', '#skF_3')), inference(splitRight, [status(thm)], [c_70])).
% 7.65/2.66  tff(c_30, plain, (![A_22, B_23]: (v1_relat_1(k2_zfmisc_1(A_22, B_23)))), inference(cnfTransformation, [status(thm)], [f_71])).
% 7.65/2.66  tff(c_3827, plain, (![B_301, A_302]: (v1_relat_1(B_301) | ~m1_subset_1(B_301, k1_zfmisc_1(A_302)) | ~v1_relat_1(A_302))), inference(cnfTransformation, [status(thm)], [f_63])).
% 7.65/2.66  tff(c_3833, plain, (v1_relat_1('#skF_6') | ~v1_relat_1(k2_zfmisc_1('#skF_4', '#skF_3'))), inference(resolution, [status(thm)], [c_74, c_3827])).
% 7.65/2.66  tff(c_3842, plain, (v1_relat_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_3833])).
% 7.65/2.66  tff(c_4043, plain, (![C_329, B_330, A_331]: (v5_relat_1(C_329, B_330) | ~m1_subset_1(C_329, k1_zfmisc_1(k2_zfmisc_1(A_331, B_330))))), inference(cnfTransformation, [status(thm)], [f_92])).
% 7.65/2.66  tff(c_4054, plain, (v5_relat_1('#skF_6', '#skF_3')), inference(resolution, [status(thm)], [c_74, c_4043])).
% 7.65/2.66  tff(c_28, plain, (![B_21, A_20]: (r1_tarski(k2_relat_1(B_21), A_20) | ~v5_relat_1(B_21, A_20) | ~v1_relat_1(B_21))), inference(cnfTransformation, [status(thm)], [f_69])).
% 7.65/2.66  tff(c_3836, plain, (v1_relat_1('#skF_5') | ~v1_relat_1(k2_zfmisc_1('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_80, c_3827])).
% 7.65/2.66  tff(c_3845, plain, (v1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_3836])).
% 7.65/2.66  tff(c_36, plain, (![A_27]: (k2_relat_1(k6_relat_1(A_27))=A_27)), inference(cnfTransformation, [status(thm)], [f_82])).
% 7.65/2.66  tff(c_87, plain, (![A_27]: (k2_relat_1(k6_partfun1(A_27))=A_27)), inference(demodulation, [status(thm), theory('equality')], [c_64, c_36])).
% 7.65/2.66  tff(c_4693, plain, (![A_385, C_387, E_388, D_386, B_384, F_389]: (k1_partfun1(A_385, B_384, C_387, D_386, E_388, F_389)=k5_relat_1(E_388, F_389) | ~m1_subset_1(F_389, k1_zfmisc_1(k2_zfmisc_1(C_387, D_386))) | ~v1_funct_1(F_389) | ~m1_subset_1(E_388, k1_zfmisc_1(k2_zfmisc_1(A_385, B_384))) | ~v1_funct_1(E_388))), inference(cnfTransformation, [status(thm)], [f_134])).
% 7.65/2.66  tff(c_4701, plain, (![A_385, B_384, E_388]: (k1_partfun1(A_385, B_384, '#skF_4', '#skF_3', E_388, '#skF_6')=k5_relat_1(E_388, '#skF_6') | ~v1_funct_1('#skF_6') | ~m1_subset_1(E_388, k1_zfmisc_1(k2_zfmisc_1(A_385, B_384))) | ~v1_funct_1(E_388))), inference(resolution, [status(thm)], [c_74, c_4693])).
% 7.65/2.66  tff(c_5673, plain, (![A_449, B_450, E_451]: (k1_partfun1(A_449, B_450, '#skF_4', '#skF_3', E_451, '#skF_6')=k5_relat_1(E_451, '#skF_6') | ~m1_subset_1(E_451, k1_zfmisc_1(k2_zfmisc_1(A_449, B_450))) | ~v1_funct_1(E_451))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_4701])).
% 7.65/2.66  tff(c_5694, plain, (k1_partfun1('#skF_3', '#skF_4', '#skF_4', '#skF_3', '#skF_5', '#skF_6')=k5_relat_1('#skF_5', '#skF_6') | ~v1_funct_1('#skF_5')), inference(resolution, [status(thm)], [c_80, c_5673])).
% 7.65/2.66  tff(c_5702, plain, (k1_partfun1('#skF_3', '#skF_4', '#skF_4', '#skF_3', '#skF_5', '#skF_6')=k5_relat_1('#skF_5', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_84, c_5694])).
% 7.65/2.66  tff(c_6017, plain, (m1_subset_1(k5_relat_1('#skF_5', '#skF_6'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3'))) | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_3'))) | ~v1_funct_1('#skF_6') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4'))) | ~v1_funct_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_5702, c_54])).
% 7.65/2.66  tff(c_6023, plain, (m1_subset_1(k5_relat_1('#skF_5', '#skF_6'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_84, c_80, c_78, c_74, c_6017])).
% 7.65/2.66  tff(c_4314, plain, (![D_351, C_352, A_353, B_354]: (D_351=C_352 | ~r2_relset_1(A_353, B_354, C_352, D_351) | ~m1_subset_1(D_351, k1_zfmisc_1(k2_zfmisc_1(A_353, B_354))) | ~m1_subset_1(C_352, k1_zfmisc_1(k2_zfmisc_1(A_353, B_354))))), inference(cnfTransformation, [status(thm)], [f_100])).
% 7.65/2.66  tff(c_4320, plain, (k1_partfun1('#skF_3', '#skF_4', '#skF_4', '#skF_3', '#skF_5', '#skF_6')=k6_partfun1('#skF_3') | ~m1_subset_1(k6_partfun1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3'))) | ~m1_subset_1(k1_partfun1('#skF_3', '#skF_4', '#skF_4', '#skF_3', '#skF_5', '#skF_6'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3')))), inference(resolution, [status(thm)], [c_72, c_4314])).
% 7.65/2.66  tff(c_4331, plain, (k1_partfun1('#skF_3', '#skF_4', '#skF_4', '#skF_3', '#skF_5', '#skF_6')=k6_partfun1('#skF_3') | ~m1_subset_1(k1_partfun1('#skF_3', '#skF_4', '#skF_4', '#skF_3', '#skF_5', '#skF_6'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_4320])).
% 7.65/2.66  tff(c_4377, plain, (~m1_subset_1(k1_partfun1('#skF_3', '#skF_4', '#skF_4', '#skF_3', '#skF_5', '#skF_6'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3')))), inference(splitLeft, [status(thm)], [c_4331])).
% 7.65/2.66  tff(c_7059, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6023, c_5702, c_4377])).
% 7.65/2.66  tff(c_7060, plain, (k1_partfun1('#skF_3', '#skF_4', '#skF_4', '#skF_3', '#skF_5', '#skF_6')=k6_partfun1('#skF_3')), inference(splitRight, [status(thm)], [c_4331])).
% 7.65/2.66  tff(c_7427, plain, (![C_521, E_522, A_519, B_518, F_523, D_520]: (k1_partfun1(A_519, B_518, C_521, D_520, E_522, F_523)=k5_relat_1(E_522, F_523) | ~m1_subset_1(F_523, k1_zfmisc_1(k2_zfmisc_1(C_521, D_520))) | ~v1_funct_1(F_523) | ~m1_subset_1(E_522, k1_zfmisc_1(k2_zfmisc_1(A_519, B_518))) | ~v1_funct_1(E_522))), inference(cnfTransformation, [status(thm)], [f_134])).
% 7.65/2.66  tff(c_7435, plain, (![A_519, B_518, E_522]: (k1_partfun1(A_519, B_518, '#skF_4', '#skF_3', E_522, '#skF_6')=k5_relat_1(E_522, '#skF_6') | ~v1_funct_1('#skF_6') | ~m1_subset_1(E_522, k1_zfmisc_1(k2_zfmisc_1(A_519, B_518))) | ~v1_funct_1(E_522))), inference(resolution, [status(thm)], [c_74, c_7427])).
% 7.65/2.66  tff(c_8846, plain, (![A_593, B_594, E_595]: (k1_partfun1(A_593, B_594, '#skF_4', '#skF_3', E_595, '#skF_6')=k5_relat_1(E_595, '#skF_6') | ~m1_subset_1(E_595, k1_zfmisc_1(k2_zfmisc_1(A_593, B_594))) | ~v1_funct_1(E_595))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_7435])).
% 7.65/2.66  tff(c_8876, plain, (k1_partfun1('#skF_3', '#skF_4', '#skF_4', '#skF_3', '#skF_5', '#skF_6')=k5_relat_1('#skF_5', '#skF_6') | ~v1_funct_1('#skF_5')), inference(resolution, [status(thm)], [c_80, c_8846])).
% 7.65/2.66  tff(c_8890, plain, (k5_relat_1('#skF_5', '#skF_6')=k6_partfun1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_84, c_7060, c_8876])).
% 7.65/2.66  tff(c_32, plain, (![A_24, B_26]: (r1_tarski(k2_relat_1(k5_relat_1(A_24, B_26)), k2_relat_1(B_26)) | ~v1_relat_1(B_26) | ~v1_relat_1(A_24))), inference(cnfTransformation, [status(thm)], [f_78])).
% 7.65/2.66  tff(c_8894, plain, (r1_tarski(k2_relat_1(k6_partfun1('#skF_3')), k2_relat_1('#skF_6')) | ~v1_relat_1('#skF_6') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_8890, c_32])).
% 7.65/2.66  tff(c_8898, plain, (r1_tarski('#skF_3', k2_relat_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_3845, c_3842, c_87, c_8894])).
% 7.65/2.66  tff(c_14, plain, (![B_11, A_10]: (B_11=A_10 | ~r1_tarski(B_11, A_10) | ~r1_tarski(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_45])).
% 7.65/2.66  tff(c_8912, plain, (k2_relat_1('#skF_6')='#skF_3' | ~r1_tarski(k2_relat_1('#skF_6'), '#skF_3')), inference(resolution, [status(thm)], [c_8898, c_14])).
% 7.65/2.66  tff(c_8913, plain, (~r1_tarski(k2_relat_1('#skF_6'), '#skF_3')), inference(splitLeft, [status(thm)], [c_8912])).
% 7.65/2.66  tff(c_8929, plain, (~v5_relat_1('#skF_6', '#skF_3') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_28, c_8913])).
% 7.65/2.66  tff(c_8936, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3842, c_4054, c_8929])).
% 7.65/2.66  tff(c_8937, plain, (k2_relat_1('#skF_6')='#skF_3'), inference(splitRight, [status(thm)], [c_8912])).
% 7.65/2.66  tff(c_18, plain, (![B_11]: (r1_tarski(B_11, B_11))), inference(cnfTransformation, [status(thm)], [f_45])).
% 7.65/2.66  tff(c_3953, plain, (![B_324, A_325]: (v5_relat_1(B_324, A_325) | ~r1_tarski(k2_relat_1(B_324), A_325) | ~v1_relat_1(B_324))), inference(cnfTransformation, [status(thm)], [f_69])).
% 7.65/2.66  tff(c_3968, plain, (![B_324]: (v5_relat_1(B_324, k2_relat_1(B_324)) | ~v1_relat_1(B_324))), inference(resolution, [status(thm)], [c_18, c_3953])).
% 7.65/2.66  tff(c_4062, plain, (![B_333]: (v2_funct_2(B_333, k2_relat_1(B_333)) | ~v5_relat_1(B_333, k2_relat_1(B_333)) | ~v1_relat_1(B_333))), inference(cnfTransformation, [status(thm)], [f_108])).
% 7.65/2.66  tff(c_4072, plain, (![B_324]: (v2_funct_2(B_324, k2_relat_1(B_324)) | ~v1_relat_1(B_324))), inference(resolution, [status(thm)], [c_3968, c_4062])).
% 7.65/2.66  tff(c_8950, plain, (v2_funct_2('#skF_6', '#skF_3') | ~v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_8937, c_4072])).
% 7.65/2.66  tff(c_8967, plain, (v2_funct_2('#skF_6', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_3842, c_8950])).
% 7.65/2.66  tff(c_8969, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3803, c_8967])).
% 7.65/2.66  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.65/2.66  
% 7.65/2.66  Inference rules
% 7.65/2.66  ----------------------
% 7.65/2.66  #Ref     : 0
% 7.65/2.66  #Sup     : 2110
% 7.65/2.66  #Fact    : 0
% 7.65/2.66  #Define  : 0
% 7.65/2.66  #Split   : 17
% 7.65/2.66  #Chain   : 0
% 7.65/2.66  #Close   : 0
% 7.65/2.66  
% 7.65/2.66  Ordering : KBO
% 7.65/2.66  
% 7.65/2.66  Simplification rules
% 7.65/2.66  ----------------------
% 7.65/2.66  #Subsume      : 182
% 7.65/2.66  #Demod        : 1934
% 7.65/2.66  #Tautology    : 1069
% 7.65/2.66  #SimpNegUnit  : 5
% 7.65/2.66  #BackRed      : 81
% 7.65/2.66  
% 7.65/2.66  #Partial instantiations: 0
% 7.65/2.66  #Strategies tried      : 1
% 7.65/2.66  
% 7.65/2.66  Timing (in seconds)
% 7.65/2.66  ----------------------
% 7.65/2.66  Preprocessing        : 0.38
% 7.65/2.66  Parsing              : 0.20
% 7.65/2.66  CNF conversion       : 0.03
% 7.65/2.66  Main loop            : 1.43
% 7.65/2.66  Inferencing          : 0.45
% 7.65/2.66  Reduction            : 0.51
% 7.65/2.66  Demodulation         : 0.38
% 7.65/2.66  BG Simplification    : 0.06
% 7.65/2.66  Subsumption          : 0.30
% 7.65/2.66  Abstraction          : 0.06
% 7.65/2.66  MUC search           : 0.00
% 7.65/2.66  Cooper               : 0.00
% 7.65/2.66  Total                : 1.86
% 7.65/2.66  Index Insertion      : 0.00
% 7.65/2.66  Index Deletion       : 0.00
% 7.65/2.66  Index Matching       : 0.00
% 7.65/2.66  BG Taut test         : 0.00
%------------------------------------------------------------------------------
