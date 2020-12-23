%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:12:01 EST 2020

% Result     : Theorem 6.20s
% Output     : CNFRefutation 6.20s
% Verified   : 
% Statistics : Number of formulae       :  150 ( 377 expanded)
%              Number of leaves         :   52 ( 151 expanded)
%              Depth                    :   12
%              Number of atoms          :  279 (1124 expanded)
%              Number of equality atoms :   52 ( 142 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > v1_partfun1 > r2_xboole_0 > r2_hidden > r1_tarski > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1

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

tff(r2_xboole_0,type,(
    r2_xboole_0: ( $i * $i ) > $o )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_226,negated_conjecture,(
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

tff(f_126,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_184,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_122,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v2_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_funct_1)).

tff(f_182,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_160,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( v1_funct_1(k1_partfun1(A,B,C,D,E,F))
        & m1_subset_1(k1_partfun1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).

tff(f_164,axiom,(
    ! [A] :
      ( v1_partfun1(k6_partfun1(A),A)
      & m1_subset_1(k6_partfun1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_partfun1)).

tff(f_140,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_102,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_98,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ( k1_relat_1(A) = k1_xboole_0
          | k2_relat_1(A) = k1_xboole_0 )
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).

tff(f_206,axiom,(
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

tff(f_33,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_172,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ( ~ v1_xboole_0(k6_relat_1(A))
        & v1_relat_1(k6_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc7_relset_1)).

tff(f_58,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => v1_xboole_0(k2_zfmisc_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_zfmisc_1)).

tff(f_118,axiom,(
    ! [A] :
      ( ( v1_xboole_0(A)
        & v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(A)
        & v1_funct_1(A)
        & v2_funct_1(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_funct_1)).

tff(f_65,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_xboole_0(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_subset_1)).

tff(f_132,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_75,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_90,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => r1_tarski(k2_relat_1(k5_relat_1(A,B)),k2_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_relat_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_148,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A) )
     => ( v2_funct_2(B,A)
      <=> k2_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_funct_2)).

tff(c_102,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_226])).

tff(c_2055,plain,(
    ! [C_270,A_271,B_272] :
      ( v1_relat_1(C_270)
      | ~ m1_subset_1(C_270,k1_zfmisc_1(k2_zfmisc_1(A_271,B_272))) ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_2067,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_102,c_2055])).

tff(c_86,plain,(
    ! [A_54] : k6_relat_1(A_54) = k6_partfun1(A_54) ),
    inference(cnfTransformation,[status(thm)],[f_184])).

tff(c_56,plain,(
    ! [A_27] : v2_funct_1(k6_relat_1(A_27)) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_109,plain,(
    ! [A_27] : v2_funct_1(k6_partfun1(A_27)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_56])).

tff(c_106,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_226])).

tff(c_100,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_226])).

tff(c_96,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_226])).

tff(c_1015,plain,(
    ! [A_195,E_197,C_196,B_194,F_192,D_193] :
      ( k1_partfun1(A_195,B_194,C_196,D_193,E_197,F_192) = k5_relat_1(E_197,F_192)
      | ~ m1_subset_1(F_192,k1_zfmisc_1(k2_zfmisc_1(C_196,D_193)))
      | ~ v1_funct_1(F_192)
      | ~ m1_subset_1(E_197,k1_zfmisc_1(k2_zfmisc_1(A_195,B_194)))
      | ~ v1_funct_1(E_197) ) ),
    inference(cnfTransformation,[status(thm)],[f_182])).

tff(c_1023,plain,(
    ! [A_195,B_194,E_197] :
      ( k1_partfun1(A_195,B_194,'#skF_3','#skF_2',E_197,'#skF_5') = k5_relat_1(E_197,'#skF_5')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1(E_197,k1_zfmisc_1(k2_zfmisc_1(A_195,B_194)))
      | ~ v1_funct_1(E_197) ) ),
    inference(resolution,[status(thm)],[c_96,c_1015])).

tff(c_1434,plain,(
    ! [A_233,B_234,E_235] :
      ( k1_partfun1(A_233,B_234,'#skF_3','#skF_2',E_235,'#skF_5') = k5_relat_1(E_235,'#skF_5')
      | ~ m1_subset_1(E_235,k1_zfmisc_1(k2_zfmisc_1(A_233,B_234)))
      | ~ v1_funct_1(E_235) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_1023])).

tff(c_1452,plain,
    ( k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5') = k5_relat_1('#skF_4','#skF_5')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_102,c_1434])).

tff(c_1469,plain,(
    k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5') = k5_relat_1('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_106,c_1452])).

tff(c_72,plain,(
    ! [E_44,C_42,F_45,A_40,D_43,B_41] :
      ( m1_subset_1(k1_partfun1(A_40,B_41,C_42,D_43,E_44,F_45),k1_zfmisc_1(k2_zfmisc_1(A_40,D_43)))
      | ~ m1_subset_1(F_45,k1_zfmisc_1(k2_zfmisc_1(C_42,D_43)))
      | ~ v1_funct_1(F_45)
      | ~ m1_subset_1(E_44,k1_zfmisc_1(k2_zfmisc_1(A_40,B_41)))
      | ~ v1_funct_1(E_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_1596,plain,
    ( m1_subset_1(k5_relat_1('#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2')))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2')))
    | ~ v1_funct_1('#skF_5')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
    | ~ v1_funct_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1469,c_72])).

tff(c_1603,plain,(
    m1_subset_1(k5_relat_1('#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_106,c_102,c_100,c_96,c_1596])).

tff(c_78,plain,(
    ! [A_46] : m1_subset_1(k6_partfun1(A_46),k1_zfmisc_1(k2_zfmisc_1(A_46,A_46))) ),
    inference(cnfTransformation,[status(thm)],[f_164])).

tff(c_94,plain,(
    r2_relset_1('#skF_2','#skF_2',k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5'),k6_partfun1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_226])).

tff(c_839,plain,(
    ! [D_166,C_167,A_168,B_169] :
      ( D_166 = C_167
      | ~ r2_relset_1(A_168,B_169,C_167,D_166)
      | ~ m1_subset_1(D_166,k1_zfmisc_1(k2_zfmisc_1(A_168,B_169)))
      | ~ m1_subset_1(C_167,k1_zfmisc_1(k2_zfmisc_1(A_168,B_169))) ) ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_851,plain,
    ( k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5') = k6_partfun1('#skF_2')
    | ~ m1_subset_1(k6_partfun1('#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2')))
    | ~ m1_subset_1(k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(resolution,[status(thm)],[c_94,c_839])).

tff(c_871,plain,
    ( k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5') = k6_partfun1('#skF_2')
    | ~ m1_subset_1(k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_851])).

tff(c_1798,plain,(
    k5_relat_1('#skF_4','#skF_5') = k6_partfun1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1603,c_1469,c_1469,c_871])).

tff(c_92,plain,
    ( ~ v2_funct_2('#skF_5','#skF_2')
    | ~ v2_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_226])).

tff(c_158,plain,(
    ~ v2_funct_1('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_92])).

tff(c_44,plain,(
    ! [A_24] : k2_relat_1(k6_relat_1(A_24)) = A_24 ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_112,plain,(
    ! [A_24] : k2_relat_1(k6_partfun1(A_24)) = A_24 ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_44])).

tff(c_54,plain,(
    ! [A_27] : v1_relat_1(k6_relat_1(A_27)) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_110,plain,(
    ! [A_27] : v1_relat_1(k6_partfun1(A_27)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_54])).

tff(c_170,plain,(
    ! [A_79] :
      ( k2_relat_1(A_79) != k1_xboole_0
      | k1_xboole_0 = A_79
      | ~ v1_relat_1(A_79) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_176,plain,(
    ! [A_27] :
      ( k2_relat_1(k6_partfun1(A_27)) != k1_xboole_0
      | k6_partfun1(A_27) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_110,c_170])).

tff(c_180,plain,(
    ! [A_27] :
      ( k1_xboole_0 != A_27
      | k6_partfun1(A_27) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_112,c_176])).

tff(c_285,plain,
    ( r2_relset_1('#skF_2','#skF_2',k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5'),k1_xboole_0)
    | k1_xboole_0 != '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_180,c_94])).

tff(c_351,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_285])).

tff(c_104,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_226])).

tff(c_98,plain,(
    v1_funct_2('#skF_5','#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_226])).

tff(c_90,plain,(
    ! [B_56,C_57,A_55,E_60,D_58] :
      ( k1_xboole_0 = C_57
      | v2_funct_1(D_58)
      | ~ v2_funct_1(k1_partfun1(A_55,B_56,B_56,C_57,D_58,E_60))
      | ~ m1_subset_1(E_60,k1_zfmisc_1(k2_zfmisc_1(B_56,C_57)))
      | ~ v1_funct_2(E_60,B_56,C_57)
      | ~ v1_funct_1(E_60)
      | ~ m1_subset_1(D_58,k1_zfmisc_1(k2_zfmisc_1(A_55,B_56)))
      | ~ v1_funct_2(D_58,A_55,B_56)
      | ~ v1_funct_1(D_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_206])).

tff(c_1593,plain,
    ( k1_xboole_0 = '#skF_2'
    | v2_funct_1('#skF_4')
    | ~ v2_funct_1(k5_relat_1('#skF_4','#skF_5'))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2')))
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_2')
    | ~ v1_funct_1('#skF_5')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_3')
    | ~ v1_funct_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1469,c_90])).

tff(c_1600,plain,
    ( k1_xboole_0 = '#skF_2'
    | v2_funct_1('#skF_4')
    | ~ v2_funct_1(k5_relat_1('#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_106,c_104,c_102,c_100,c_98,c_96,c_1593])).

tff(c_1601,plain,(
    ~ v2_funct_1(k5_relat_1('#skF_4','#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_158,c_351,c_1600])).

tff(c_1804,plain,(
    ~ v2_funct_1(k6_partfun1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1798,c_1601])).

tff(c_1814,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_109,c_1804])).

tff(c_1816,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_285])).

tff(c_8,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_182,plain,(
    ! [A_80] :
      ( k1_xboole_0 != A_80
      | k6_partfun1(A_80) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_112,c_176])).

tff(c_82,plain,(
    ! [A_47] :
      ( ~ v1_xboole_0(k6_relat_1(A_47))
      | v1_xboole_0(A_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_172])).

tff(c_107,plain,(
    ! [A_47] :
      ( ~ v1_xboole_0(k6_partfun1(A_47))
      | v1_xboole_0(A_47) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_82])).

tff(c_188,plain,(
    ! [A_80] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | v1_xboole_0(A_80)
      | k1_xboole_0 != A_80 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_182,c_107])).

tff(c_207,plain,(
    ! [A_80] :
      ( v1_xboole_0(A_80)
      | k1_xboole_0 != A_80 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_188])).

tff(c_1835,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1816,c_207])).

tff(c_22,plain,(
    ! [A_10,B_11] :
      ( v1_xboole_0(k2_zfmisc_1(A_10,B_11))
      | ~ v1_xboole_0(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_1953,plain,(
    ! [A_263] :
      ( v2_funct_1(A_263)
      | ~ v1_funct_1(A_263)
      | ~ v1_relat_1(A_263)
      | ~ v1_xboole_0(A_263) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_1956,plain,
    ( ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4')
    | ~ v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_1953,c_158])).

tff(c_1959,plain,
    ( ~ v1_relat_1('#skF_4')
    | ~ v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_106,c_1956])).

tff(c_1960,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_1959])).

tff(c_2023,plain,(
    ! [B_268,A_269] :
      ( v1_xboole_0(B_268)
      | ~ m1_subset_1(B_268,k1_zfmisc_1(A_269))
      | ~ v1_xboole_0(A_269) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_2029,plain,
    ( v1_xboole_0('#skF_4')
    | ~ v1_xboole_0(k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_102,c_2023])).

tff(c_2036,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_1960,c_2029])).

tff(c_2046,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_22,c_2036])).

tff(c_2052,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1835,c_2046])).

tff(c_2053,plain,(
    ~ v1_relat_1('#skF_4') ),
    inference(splitRight,[status(thm)],[c_1959])).

tff(c_2070,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2067,c_2053])).

tff(c_2071,plain,(
    ~ v2_funct_2('#skF_5','#skF_2') ),
    inference(splitRight,[status(thm)],[c_92])).

tff(c_2272,plain,(
    ! [C_307,A_308,B_309] :
      ( v1_relat_1(C_307)
      | ~ m1_subset_1(C_307,k1_zfmisc_1(k2_zfmisc_1(A_308,B_309))) ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_2285,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_96,c_2272])).

tff(c_2480,plain,(
    ! [C_336,B_337,A_338] :
      ( v5_relat_1(C_336,B_337)
      | ~ m1_subset_1(C_336,k1_zfmisc_1(k2_zfmisc_1(A_338,B_337))) ) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_2492,plain,(
    v5_relat_1('#skF_5','#skF_2') ),
    inference(resolution,[status(thm)],[c_96,c_2480])).

tff(c_30,plain,(
    ! [B_17,A_16] :
      ( r1_tarski(k2_relat_1(B_17),A_16)
      | ~ v5_relat_1(B_17,A_16)
      | ~ v1_relat_1(B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_2284,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_102,c_2272])).

tff(c_2746,plain,(
    ! [D_368,C_369,A_370,B_371] :
      ( D_368 = C_369
      | ~ r2_relset_1(A_370,B_371,C_369,D_368)
      | ~ m1_subset_1(D_368,k1_zfmisc_1(k2_zfmisc_1(A_370,B_371)))
      | ~ m1_subset_1(C_369,k1_zfmisc_1(k2_zfmisc_1(A_370,B_371))) ) ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_2760,plain,
    ( k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5') = k6_partfun1('#skF_2')
    | ~ m1_subset_1(k6_partfun1('#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2')))
    | ~ m1_subset_1(k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(resolution,[status(thm)],[c_94,c_2746])).

tff(c_2783,plain,
    ( k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5') = k6_partfun1('#skF_2')
    | ~ m1_subset_1(k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_2760])).

tff(c_2824,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_2783])).

tff(c_3571,plain,
    ( ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2')))
    | ~ v1_funct_1('#skF_5')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_72,c_2824])).

tff(c_3575,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_106,c_102,c_100,c_96,c_3571])).

tff(c_3576,plain,(
    k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5') = k6_partfun1('#skF_2') ),
    inference(splitRight,[status(thm)],[c_2783])).

tff(c_3806,plain,(
    ! [C_487,E_488,A_486,D_484,F_483,B_485] :
      ( k1_partfun1(A_486,B_485,C_487,D_484,E_488,F_483) = k5_relat_1(E_488,F_483)
      | ~ m1_subset_1(F_483,k1_zfmisc_1(k2_zfmisc_1(C_487,D_484)))
      | ~ v1_funct_1(F_483)
      | ~ m1_subset_1(E_488,k1_zfmisc_1(k2_zfmisc_1(A_486,B_485)))
      | ~ v1_funct_1(E_488) ) ),
    inference(cnfTransformation,[status(thm)],[f_182])).

tff(c_3814,plain,(
    ! [A_486,B_485,E_488] :
      ( k1_partfun1(A_486,B_485,'#skF_3','#skF_2',E_488,'#skF_5') = k5_relat_1(E_488,'#skF_5')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1(E_488,k1_zfmisc_1(k2_zfmisc_1(A_486,B_485)))
      | ~ v1_funct_1(E_488) ) ),
    inference(resolution,[status(thm)],[c_96,c_3806])).

tff(c_4009,plain,(
    ! [A_511,B_512,E_513] :
      ( k1_partfun1(A_511,B_512,'#skF_3','#skF_2',E_513,'#skF_5') = k5_relat_1(E_513,'#skF_5')
      | ~ m1_subset_1(E_513,k1_zfmisc_1(k2_zfmisc_1(A_511,B_512)))
      | ~ v1_funct_1(E_513) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_3814])).

tff(c_4021,plain,
    ( k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5') = k5_relat_1('#skF_4','#skF_5')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_102,c_4009])).

tff(c_4032,plain,(
    k5_relat_1('#skF_4','#skF_5') = k6_partfun1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_106,c_3576,c_4021])).

tff(c_36,plain,(
    ! [A_20,B_22] :
      ( r1_tarski(k2_relat_1(k5_relat_1(A_20,B_22)),k2_relat_1(B_22))
      | ~ v1_relat_1(B_22)
      | ~ v1_relat_1(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_4039,plain,
    ( r1_tarski(k2_relat_1(k6_partfun1('#skF_2')),k2_relat_1('#skF_5'))
    | ~ v1_relat_1('#skF_5')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_4032,c_36])).

tff(c_4052,plain,(
    r1_tarski('#skF_2',k2_relat_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2284,c_2285,c_112,c_4039])).

tff(c_14,plain,(
    ! [B_7,A_6] :
      ( B_7 = A_6
      | ~ r1_tarski(B_7,A_6)
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_4068,plain,
    ( k2_relat_1('#skF_5') = '#skF_2'
    | ~ r1_tarski(k2_relat_1('#skF_5'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_4052,c_14])).

tff(c_4123,plain,(
    ~ r1_tarski(k2_relat_1('#skF_5'),'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_4068])).

tff(c_4129,plain,
    ( ~ v5_relat_1('#skF_5','#skF_2')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_30,c_4123])).

tff(c_4134,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2285,c_2492,c_4129])).

tff(c_4135,plain,(
    k2_relat_1('#skF_5') = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_4068])).

tff(c_18,plain,(
    ! [B_7] : r1_tarski(B_7,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_2502,plain,(
    ! [B_340,A_341] :
      ( v5_relat_1(B_340,A_341)
      | ~ r1_tarski(k2_relat_1(B_340),A_341)
      | ~ v1_relat_1(B_340) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_2516,plain,(
    ! [B_340] :
      ( v5_relat_1(B_340,k2_relat_1(B_340))
      | ~ v1_relat_1(B_340) ) ),
    inference(resolution,[status(thm)],[c_18,c_2502])).

tff(c_2579,plain,(
    ! [B_349] :
      ( v2_funct_2(B_349,k2_relat_1(B_349))
      | ~ v5_relat_1(B_349,k2_relat_1(B_349))
      | ~ v1_relat_1(B_349) ) ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_2597,plain,(
    ! [B_340] :
      ( v2_funct_2(B_340,k2_relat_1(B_340))
      | ~ v1_relat_1(B_340) ) ),
    inference(resolution,[status(thm)],[c_2516,c_2579])).

tff(c_4155,plain,
    ( v2_funct_2('#skF_5','#skF_2')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_4135,c_2597])).

tff(c_4171,plain,(
    v2_funct_2('#skF_5','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2285,c_4155])).

tff(c_4173,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2071,c_4171])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 18:10:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.20/2.17  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.20/2.18  
% 6.20/2.18  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.20/2.18  %$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > v1_partfun1 > r2_xboole_0 > r2_hidden > r1_tarski > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 6.20/2.18  
% 6.20/2.18  %Foreground sorts:
% 6.20/2.18  
% 6.20/2.18  
% 6.20/2.18  %Background operators:
% 6.20/2.18  
% 6.20/2.18  
% 6.20/2.18  %Foreground operators:
% 6.20/2.18  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 6.20/2.18  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 6.20/2.18  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.20/2.18  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 6.20/2.18  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 6.20/2.18  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 6.20/2.18  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 6.20/2.18  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.20/2.18  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 6.20/2.18  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 6.20/2.18  tff('#skF_5', type, '#skF_5': $i).
% 6.20/2.18  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 6.20/2.18  tff('#skF_2', type, '#skF_2': $i).
% 6.20/2.18  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 6.20/2.18  tff('#skF_3', type, '#skF_3': $i).
% 6.20/2.18  tff(v2_funct_2, type, v2_funct_2: ($i * $i) > $o).
% 6.20/2.18  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 6.20/2.18  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 6.20/2.18  tff(r2_xboole_0, type, r2_xboole_0: ($i * $i) > $o).
% 6.20/2.18  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 6.20/2.18  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.20/2.18  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 6.20/2.18  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 6.20/2.18  tff('#skF_4', type, '#skF_4': $i).
% 6.20/2.18  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 6.20/2.18  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.20/2.18  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 6.20/2.18  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 6.20/2.18  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 6.20/2.18  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 6.20/2.18  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 6.20/2.18  
% 6.20/2.20  tff(f_226, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (r2_relset_1(A, A, k1_partfun1(A, B, B, A, C, D), k6_partfun1(A)) => (v2_funct_1(C) & v2_funct_2(D, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_funct_2)).
% 6.20/2.20  tff(f_126, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 6.20/2.20  tff(f_184, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 6.20/2.20  tff(f_122, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v2_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc4_funct_1)).
% 6.20/2.20  tff(f_182, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 6.20/2.20  tff(f_160, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (v1_funct_1(k1_partfun1(A, B, C, D, E, F)) & m1_subset_1(k1_partfun1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 6.20/2.20  tff(f_164, axiom, (![A]: (v1_partfun1(k6_partfun1(A), A) & m1_subset_1(k6_partfun1(A), k1_zfmisc_1(k2_zfmisc_1(A, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_partfun1)).
% 6.20/2.20  tff(f_140, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 6.20/2.20  tff(f_102, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 6.20/2.20  tff(f_98, axiom, (![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_relat_1)).
% 6.20/2.20  tff(f_206, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, B, C)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (v2_funct_1(k1_partfun1(A, B, B, C, D, E)) => (((C = k1_xboole_0) & ~(B = k1_xboole_0)) | v2_funct_1(D))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t26_funct_2)).
% 6.20/2.20  tff(f_33, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 6.20/2.20  tff(f_172, axiom, (![A]: (~v1_xboole_0(A) => (~v1_xboole_0(k6_relat_1(A)) & v1_relat_1(k6_relat_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc7_relset_1)).
% 6.20/2.20  tff(f_58, axiom, (![A, B]: (v1_xboole_0(A) => v1_xboole_0(k2_zfmisc_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc4_zfmisc_1)).
% 6.20/2.20  tff(f_118, axiom, (![A]: (((v1_xboole_0(A) & v1_relat_1(A)) & v1_funct_1(A)) => ((v1_relat_1(A) & v1_funct_1(A)) & v2_funct_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_funct_1)).
% 6.20/2.20  tff(f_65, axiom, (![A]: (v1_xboole_0(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_subset_1)).
% 6.20/2.20  tff(f_132, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 6.20/2.20  tff(f_75, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 6.20/2.20  tff(f_90, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => r1_tarski(k2_relat_1(k5_relat_1(A, B)), k2_relat_1(B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t45_relat_1)).
% 6.20/2.20  tff(f_49, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 6.20/2.20  tff(f_148, axiom, (![A, B]: ((v1_relat_1(B) & v5_relat_1(B, A)) => (v2_funct_2(B, A) <=> (k2_relat_1(B) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_funct_2)).
% 6.20/2.20  tff(c_102, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_226])).
% 6.20/2.20  tff(c_2055, plain, (![C_270, A_271, B_272]: (v1_relat_1(C_270) | ~m1_subset_1(C_270, k1_zfmisc_1(k2_zfmisc_1(A_271, B_272))))), inference(cnfTransformation, [status(thm)], [f_126])).
% 6.20/2.20  tff(c_2067, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_102, c_2055])).
% 6.20/2.20  tff(c_86, plain, (![A_54]: (k6_relat_1(A_54)=k6_partfun1(A_54))), inference(cnfTransformation, [status(thm)], [f_184])).
% 6.20/2.20  tff(c_56, plain, (![A_27]: (v2_funct_1(k6_relat_1(A_27)))), inference(cnfTransformation, [status(thm)], [f_122])).
% 6.20/2.20  tff(c_109, plain, (![A_27]: (v2_funct_1(k6_partfun1(A_27)))), inference(demodulation, [status(thm), theory('equality')], [c_86, c_56])).
% 6.20/2.20  tff(c_106, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_226])).
% 6.20/2.20  tff(c_100, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_226])).
% 6.20/2.20  tff(c_96, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_226])).
% 6.20/2.20  tff(c_1015, plain, (![A_195, E_197, C_196, B_194, F_192, D_193]: (k1_partfun1(A_195, B_194, C_196, D_193, E_197, F_192)=k5_relat_1(E_197, F_192) | ~m1_subset_1(F_192, k1_zfmisc_1(k2_zfmisc_1(C_196, D_193))) | ~v1_funct_1(F_192) | ~m1_subset_1(E_197, k1_zfmisc_1(k2_zfmisc_1(A_195, B_194))) | ~v1_funct_1(E_197))), inference(cnfTransformation, [status(thm)], [f_182])).
% 6.20/2.20  tff(c_1023, plain, (![A_195, B_194, E_197]: (k1_partfun1(A_195, B_194, '#skF_3', '#skF_2', E_197, '#skF_5')=k5_relat_1(E_197, '#skF_5') | ~v1_funct_1('#skF_5') | ~m1_subset_1(E_197, k1_zfmisc_1(k2_zfmisc_1(A_195, B_194))) | ~v1_funct_1(E_197))), inference(resolution, [status(thm)], [c_96, c_1015])).
% 6.20/2.20  tff(c_1434, plain, (![A_233, B_234, E_235]: (k1_partfun1(A_233, B_234, '#skF_3', '#skF_2', E_235, '#skF_5')=k5_relat_1(E_235, '#skF_5') | ~m1_subset_1(E_235, k1_zfmisc_1(k2_zfmisc_1(A_233, B_234))) | ~v1_funct_1(E_235))), inference(demodulation, [status(thm), theory('equality')], [c_100, c_1023])).
% 6.20/2.20  tff(c_1452, plain, (k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5')=k5_relat_1('#skF_4', '#skF_5') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_102, c_1434])).
% 6.20/2.20  tff(c_1469, plain, (k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5')=k5_relat_1('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_106, c_1452])).
% 6.20/2.20  tff(c_72, plain, (![E_44, C_42, F_45, A_40, D_43, B_41]: (m1_subset_1(k1_partfun1(A_40, B_41, C_42, D_43, E_44, F_45), k1_zfmisc_1(k2_zfmisc_1(A_40, D_43))) | ~m1_subset_1(F_45, k1_zfmisc_1(k2_zfmisc_1(C_42, D_43))) | ~v1_funct_1(F_45) | ~m1_subset_1(E_44, k1_zfmisc_1(k2_zfmisc_1(A_40, B_41))) | ~v1_funct_1(E_44))), inference(cnfTransformation, [status(thm)], [f_160])).
% 6.20/2.20  tff(c_1596, plain, (m1_subset_1(k5_relat_1('#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'))) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2'))) | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~v1_funct_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1469, c_72])).
% 6.20/2.20  tff(c_1603, plain, (m1_subset_1(k5_relat_1('#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_106, c_102, c_100, c_96, c_1596])).
% 6.20/2.20  tff(c_78, plain, (![A_46]: (m1_subset_1(k6_partfun1(A_46), k1_zfmisc_1(k2_zfmisc_1(A_46, A_46))))), inference(cnfTransformation, [status(thm)], [f_164])).
% 6.20/2.20  tff(c_94, plain, (r2_relset_1('#skF_2', '#skF_2', k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5'), k6_partfun1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_226])).
% 6.20/2.20  tff(c_839, plain, (![D_166, C_167, A_168, B_169]: (D_166=C_167 | ~r2_relset_1(A_168, B_169, C_167, D_166) | ~m1_subset_1(D_166, k1_zfmisc_1(k2_zfmisc_1(A_168, B_169))) | ~m1_subset_1(C_167, k1_zfmisc_1(k2_zfmisc_1(A_168, B_169))))), inference(cnfTransformation, [status(thm)], [f_140])).
% 6.20/2.20  tff(c_851, plain, (k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5')=k6_partfun1('#skF_2') | ~m1_subset_1(k6_partfun1('#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'))) | ~m1_subset_1(k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(resolution, [status(thm)], [c_94, c_839])).
% 6.20/2.20  tff(c_871, plain, (k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5')=k6_partfun1('#skF_2') | ~m1_subset_1(k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_851])).
% 6.20/2.20  tff(c_1798, plain, (k5_relat_1('#skF_4', '#skF_5')=k6_partfun1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1603, c_1469, c_1469, c_871])).
% 6.20/2.20  tff(c_92, plain, (~v2_funct_2('#skF_5', '#skF_2') | ~v2_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_226])).
% 6.20/2.20  tff(c_158, plain, (~v2_funct_1('#skF_4')), inference(splitLeft, [status(thm)], [c_92])).
% 6.20/2.20  tff(c_44, plain, (![A_24]: (k2_relat_1(k6_relat_1(A_24))=A_24)), inference(cnfTransformation, [status(thm)], [f_102])).
% 6.20/2.20  tff(c_112, plain, (![A_24]: (k2_relat_1(k6_partfun1(A_24))=A_24)), inference(demodulation, [status(thm), theory('equality')], [c_86, c_44])).
% 6.20/2.20  tff(c_54, plain, (![A_27]: (v1_relat_1(k6_relat_1(A_27)))), inference(cnfTransformation, [status(thm)], [f_122])).
% 6.20/2.20  tff(c_110, plain, (![A_27]: (v1_relat_1(k6_partfun1(A_27)))), inference(demodulation, [status(thm), theory('equality')], [c_86, c_54])).
% 6.20/2.20  tff(c_170, plain, (![A_79]: (k2_relat_1(A_79)!=k1_xboole_0 | k1_xboole_0=A_79 | ~v1_relat_1(A_79))), inference(cnfTransformation, [status(thm)], [f_98])).
% 6.20/2.20  tff(c_176, plain, (![A_27]: (k2_relat_1(k6_partfun1(A_27))!=k1_xboole_0 | k6_partfun1(A_27)=k1_xboole_0)), inference(resolution, [status(thm)], [c_110, c_170])).
% 6.20/2.20  tff(c_180, plain, (![A_27]: (k1_xboole_0!=A_27 | k6_partfun1(A_27)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_112, c_176])).
% 6.20/2.20  tff(c_285, plain, (r2_relset_1('#skF_2', '#skF_2', k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5'), k1_xboole_0) | k1_xboole_0!='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_180, c_94])).
% 6.20/2.20  tff(c_351, plain, (k1_xboole_0!='#skF_2'), inference(splitLeft, [status(thm)], [c_285])).
% 6.20/2.20  tff(c_104, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_226])).
% 6.20/2.20  tff(c_98, plain, (v1_funct_2('#skF_5', '#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_226])).
% 6.20/2.20  tff(c_90, plain, (![B_56, C_57, A_55, E_60, D_58]: (k1_xboole_0=C_57 | v2_funct_1(D_58) | ~v2_funct_1(k1_partfun1(A_55, B_56, B_56, C_57, D_58, E_60)) | ~m1_subset_1(E_60, k1_zfmisc_1(k2_zfmisc_1(B_56, C_57))) | ~v1_funct_2(E_60, B_56, C_57) | ~v1_funct_1(E_60) | ~m1_subset_1(D_58, k1_zfmisc_1(k2_zfmisc_1(A_55, B_56))) | ~v1_funct_2(D_58, A_55, B_56) | ~v1_funct_1(D_58))), inference(cnfTransformation, [status(thm)], [f_206])).
% 6.20/2.20  tff(c_1593, plain, (k1_xboole_0='#skF_2' | v2_funct_1('#skF_4') | ~v2_funct_1(k5_relat_1('#skF_4', '#skF_5')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2'))) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_2') | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3') | ~v1_funct_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1469, c_90])).
% 6.20/2.20  tff(c_1600, plain, (k1_xboole_0='#skF_2' | v2_funct_1('#skF_4') | ~v2_funct_1(k5_relat_1('#skF_4', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_106, c_104, c_102, c_100, c_98, c_96, c_1593])).
% 6.20/2.20  tff(c_1601, plain, (~v2_funct_1(k5_relat_1('#skF_4', '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_158, c_351, c_1600])).
% 6.20/2.20  tff(c_1804, plain, (~v2_funct_1(k6_partfun1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_1798, c_1601])).
% 6.20/2.20  tff(c_1814, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_109, c_1804])).
% 6.20/2.20  tff(c_1816, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_285])).
% 6.20/2.20  tff(c_8, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 6.20/2.20  tff(c_182, plain, (![A_80]: (k1_xboole_0!=A_80 | k6_partfun1(A_80)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_112, c_176])).
% 6.20/2.20  tff(c_82, plain, (![A_47]: (~v1_xboole_0(k6_relat_1(A_47)) | v1_xboole_0(A_47))), inference(cnfTransformation, [status(thm)], [f_172])).
% 6.20/2.20  tff(c_107, plain, (![A_47]: (~v1_xboole_0(k6_partfun1(A_47)) | v1_xboole_0(A_47))), inference(demodulation, [status(thm), theory('equality')], [c_86, c_82])).
% 6.20/2.20  tff(c_188, plain, (![A_80]: (~v1_xboole_0(k1_xboole_0) | v1_xboole_0(A_80) | k1_xboole_0!=A_80)), inference(superposition, [status(thm), theory('equality')], [c_182, c_107])).
% 6.20/2.20  tff(c_207, plain, (![A_80]: (v1_xboole_0(A_80) | k1_xboole_0!=A_80)), inference(demodulation, [status(thm), theory('equality')], [c_8, c_188])).
% 6.20/2.20  tff(c_1835, plain, (v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1816, c_207])).
% 6.20/2.20  tff(c_22, plain, (![A_10, B_11]: (v1_xboole_0(k2_zfmisc_1(A_10, B_11)) | ~v1_xboole_0(A_10))), inference(cnfTransformation, [status(thm)], [f_58])).
% 6.20/2.20  tff(c_1953, plain, (![A_263]: (v2_funct_1(A_263) | ~v1_funct_1(A_263) | ~v1_relat_1(A_263) | ~v1_xboole_0(A_263))), inference(cnfTransformation, [status(thm)], [f_118])).
% 6.20/2.20  tff(c_1956, plain, (~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4') | ~v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_1953, c_158])).
% 6.20/2.20  tff(c_1959, plain, (~v1_relat_1('#skF_4') | ~v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_106, c_1956])).
% 6.20/2.20  tff(c_1960, plain, (~v1_xboole_0('#skF_4')), inference(splitLeft, [status(thm)], [c_1959])).
% 6.20/2.20  tff(c_2023, plain, (![B_268, A_269]: (v1_xboole_0(B_268) | ~m1_subset_1(B_268, k1_zfmisc_1(A_269)) | ~v1_xboole_0(A_269))), inference(cnfTransformation, [status(thm)], [f_65])).
% 6.20/2.20  tff(c_2029, plain, (v1_xboole_0('#skF_4') | ~v1_xboole_0(k2_zfmisc_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_102, c_2023])).
% 6.20/2.20  tff(c_2036, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_2', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_1960, c_2029])).
% 6.20/2.20  tff(c_2046, plain, (~v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_22, c_2036])).
% 6.20/2.20  tff(c_2052, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1835, c_2046])).
% 6.20/2.20  tff(c_2053, plain, (~v1_relat_1('#skF_4')), inference(splitRight, [status(thm)], [c_1959])).
% 6.20/2.20  tff(c_2070, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2067, c_2053])).
% 6.20/2.20  tff(c_2071, plain, (~v2_funct_2('#skF_5', '#skF_2')), inference(splitRight, [status(thm)], [c_92])).
% 6.20/2.20  tff(c_2272, plain, (![C_307, A_308, B_309]: (v1_relat_1(C_307) | ~m1_subset_1(C_307, k1_zfmisc_1(k2_zfmisc_1(A_308, B_309))))), inference(cnfTransformation, [status(thm)], [f_126])).
% 6.20/2.20  tff(c_2285, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_96, c_2272])).
% 6.20/2.20  tff(c_2480, plain, (![C_336, B_337, A_338]: (v5_relat_1(C_336, B_337) | ~m1_subset_1(C_336, k1_zfmisc_1(k2_zfmisc_1(A_338, B_337))))), inference(cnfTransformation, [status(thm)], [f_132])).
% 6.20/2.20  tff(c_2492, plain, (v5_relat_1('#skF_5', '#skF_2')), inference(resolution, [status(thm)], [c_96, c_2480])).
% 6.20/2.20  tff(c_30, plain, (![B_17, A_16]: (r1_tarski(k2_relat_1(B_17), A_16) | ~v5_relat_1(B_17, A_16) | ~v1_relat_1(B_17))), inference(cnfTransformation, [status(thm)], [f_75])).
% 6.20/2.20  tff(c_2284, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_102, c_2272])).
% 6.20/2.20  tff(c_2746, plain, (![D_368, C_369, A_370, B_371]: (D_368=C_369 | ~r2_relset_1(A_370, B_371, C_369, D_368) | ~m1_subset_1(D_368, k1_zfmisc_1(k2_zfmisc_1(A_370, B_371))) | ~m1_subset_1(C_369, k1_zfmisc_1(k2_zfmisc_1(A_370, B_371))))), inference(cnfTransformation, [status(thm)], [f_140])).
% 6.20/2.20  tff(c_2760, plain, (k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5')=k6_partfun1('#skF_2') | ~m1_subset_1(k6_partfun1('#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'))) | ~m1_subset_1(k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(resolution, [status(thm)], [c_94, c_2746])).
% 6.20/2.20  tff(c_2783, plain, (k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5')=k6_partfun1('#skF_2') | ~m1_subset_1(k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_2760])).
% 6.20/2.20  tff(c_2824, plain, (~m1_subset_1(k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(splitLeft, [status(thm)], [c_2783])).
% 6.20/2.20  tff(c_3571, plain, (~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2'))) | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_72, c_2824])).
% 6.20/2.20  tff(c_3575, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_106, c_102, c_100, c_96, c_3571])).
% 6.20/2.20  tff(c_3576, plain, (k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5')=k6_partfun1('#skF_2')), inference(splitRight, [status(thm)], [c_2783])).
% 6.20/2.20  tff(c_3806, plain, (![C_487, E_488, A_486, D_484, F_483, B_485]: (k1_partfun1(A_486, B_485, C_487, D_484, E_488, F_483)=k5_relat_1(E_488, F_483) | ~m1_subset_1(F_483, k1_zfmisc_1(k2_zfmisc_1(C_487, D_484))) | ~v1_funct_1(F_483) | ~m1_subset_1(E_488, k1_zfmisc_1(k2_zfmisc_1(A_486, B_485))) | ~v1_funct_1(E_488))), inference(cnfTransformation, [status(thm)], [f_182])).
% 6.20/2.20  tff(c_3814, plain, (![A_486, B_485, E_488]: (k1_partfun1(A_486, B_485, '#skF_3', '#skF_2', E_488, '#skF_5')=k5_relat_1(E_488, '#skF_5') | ~v1_funct_1('#skF_5') | ~m1_subset_1(E_488, k1_zfmisc_1(k2_zfmisc_1(A_486, B_485))) | ~v1_funct_1(E_488))), inference(resolution, [status(thm)], [c_96, c_3806])).
% 6.20/2.20  tff(c_4009, plain, (![A_511, B_512, E_513]: (k1_partfun1(A_511, B_512, '#skF_3', '#skF_2', E_513, '#skF_5')=k5_relat_1(E_513, '#skF_5') | ~m1_subset_1(E_513, k1_zfmisc_1(k2_zfmisc_1(A_511, B_512))) | ~v1_funct_1(E_513))), inference(demodulation, [status(thm), theory('equality')], [c_100, c_3814])).
% 6.20/2.20  tff(c_4021, plain, (k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5')=k5_relat_1('#skF_4', '#skF_5') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_102, c_4009])).
% 6.20/2.20  tff(c_4032, plain, (k5_relat_1('#skF_4', '#skF_5')=k6_partfun1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_106, c_3576, c_4021])).
% 6.20/2.20  tff(c_36, plain, (![A_20, B_22]: (r1_tarski(k2_relat_1(k5_relat_1(A_20, B_22)), k2_relat_1(B_22)) | ~v1_relat_1(B_22) | ~v1_relat_1(A_20))), inference(cnfTransformation, [status(thm)], [f_90])).
% 6.20/2.20  tff(c_4039, plain, (r1_tarski(k2_relat_1(k6_partfun1('#skF_2')), k2_relat_1('#skF_5')) | ~v1_relat_1('#skF_5') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_4032, c_36])).
% 6.20/2.20  tff(c_4052, plain, (r1_tarski('#skF_2', k2_relat_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_2284, c_2285, c_112, c_4039])).
% 6.20/2.20  tff(c_14, plain, (![B_7, A_6]: (B_7=A_6 | ~r1_tarski(B_7, A_6) | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_49])).
% 6.20/2.20  tff(c_4068, plain, (k2_relat_1('#skF_5')='#skF_2' | ~r1_tarski(k2_relat_1('#skF_5'), '#skF_2')), inference(resolution, [status(thm)], [c_4052, c_14])).
% 6.20/2.20  tff(c_4123, plain, (~r1_tarski(k2_relat_1('#skF_5'), '#skF_2')), inference(splitLeft, [status(thm)], [c_4068])).
% 6.20/2.20  tff(c_4129, plain, (~v5_relat_1('#skF_5', '#skF_2') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_30, c_4123])).
% 6.20/2.20  tff(c_4134, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2285, c_2492, c_4129])).
% 6.20/2.20  tff(c_4135, plain, (k2_relat_1('#skF_5')='#skF_2'), inference(splitRight, [status(thm)], [c_4068])).
% 6.20/2.20  tff(c_18, plain, (![B_7]: (r1_tarski(B_7, B_7))), inference(cnfTransformation, [status(thm)], [f_49])).
% 6.20/2.20  tff(c_2502, plain, (![B_340, A_341]: (v5_relat_1(B_340, A_341) | ~r1_tarski(k2_relat_1(B_340), A_341) | ~v1_relat_1(B_340))), inference(cnfTransformation, [status(thm)], [f_75])).
% 6.20/2.20  tff(c_2516, plain, (![B_340]: (v5_relat_1(B_340, k2_relat_1(B_340)) | ~v1_relat_1(B_340))), inference(resolution, [status(thm)], [c_18, c_2502])).
% 6.20/2.20  tff(c_2579, plain, (![B_349]: (v2_funct_2(B_349, k2_relat_1(B_349)) | ~v5_relat_1(B_349, k2_relat_1(B_349)) | ~v1_relat_1(B_349))), inference(cnfTransformation, [status(thm)], [f_148])).
% 6.20/2.20  tff(c_2597, plain, (![B_340]: (v2_funct_2(B_340, k2_relat_1(B_340)) | ~v1_relat_1(B_340))), inference(resolution, [status(thm)], [c_2516, c_2579])).
% 6.20/2.20  tff(c_4155, plain, (v2_funct_2('#skF_5', '#skF_2') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_4135, c_2597])).
% 6.20/2.20  tff(c_4171, plain, (v2_funct_2('#skF_5', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2285, c_4155])).
% 6.20/2.20  tff(c_4173, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2071, c_4171])).
% 6.20/2.20  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.20/2.20  
% 6.20/2.20  Inference rules
% 6.20/2.20  ----------------------
% 6.20/2.20  #Ref     : 12
% 6.20/2.20  #Sup     : 836
% 6.20/2.20  #Fact    : 0
% 6.20/2.20  #Define  : 0
% 6.20/2.20  #Split   : 32
% 6.20/2.20  #Chain   : 0
% 6.20/2.20  #Close   : 0
% 6.20/2.20  
% 6.20/2.20  Ordering : KBO
% 6.20/2.20  
% 6.20/2.21  Simplification rules
% 6.20/2.21  ----------------------
% 6.20/2.21  #Subsume      : 166
% 6.20/2.21  #Demod        : 514
% 6.20/2.21  #Tautology    : 198
% 6.20/2.21  #SimpNegUnit  : 11
% 6.20/2.21  #BackRed      : 36
% 6.20/2.21  
% 6.20/2.21  #Partial instantiations: 0
% 6.20/2.21  #Strategies tried      : 1
% 6.20/2.21  
% 6.20/2.21  Timing (in seconds)
% 6.20/2.21  ----------------------
% 6.20/2.21  Preprocessing        : 0.38
% 6.20/2.21  Parsing              : 0.20
% 6.20/2.21  CNF conversion       : 0.03
% 6.20/2.21  Main loop            : 1.03
% 6.20/2.21  Inferencing          : 0.35
% 6.20/2.21  Reduction            : 0.35
% 6.20/2.21  Demodulation         : 0.24
% 6.20/2.21  BG Simplification    : 0.04
% 6.20/2.21  Subsumption          : 0.21
% 6.20/2.21  Abstraction          : 0.04
% 6.20/2.21  MUC search           : 0.00
% 6.20/2.21  Cooper               : 0.00
% 6.20/2.21  Total                : 1.45
% 6.20/2.21  Index Insertion      : 0.00
% 6.20/2.21  Index Deletion       : 0.00
% 6.20/2.21  Index Matching       : 0.00
% 6.20/2.21  BG Taut test         : 0.00
%------------------------------------------------------------------------------
