%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:11:59 EST 2020

% Result     : Theorem 5.76s
% Output     : CNFRefutation 5.76s
% Verified   : 
% Statistics : Number of formulae       :  125 ( 248 expanded)
%              Number of leaves         :   37 ( 101 expanded)
%              Depth                    :   11
%              Number of atoms          :  226 ( 780 expanded)
%              Number of equality atoms :   68 ( 216 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k4_relset_1 > k1_partfun1 > k2_relset_1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_135,negated_conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_funct_2)).

tff(f_61,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_79,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_65,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k2_relset_1(A,B,C),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_relset_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_113,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_85,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k4_relset_1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_relset_1)).

tff(f_71,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => m1_subset_1(k4_relset_1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_relset_1)).

tff(f_42,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => r1_tarski(k2_relat_1(k5_relat_1(A,B)),k2_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_relat_1)).

tff(f_75,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_103,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).

tff(f_57,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( ( v1_relat_1(B)
            & v1_funct_1(B) )
         => ( ( k2_relat_1(k5_relat_1(B,A)) = k2_relat_1(A)
              & v2_funct_1(A) )
           => r1_tarski(k1_relat_1(A),k2_relat_1(B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_funct_1)).

tff(c_56,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_77,plain,(
    ! [C_50,A_51,B_52] :
      ( v1_relat_1(C_50)
      | ~ m1_subset_1(C_50,k1_zfmisc_1(k2_zfmisc_1(A_51,B_52))) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_90,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_56,c_77])).

tff(c_60,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_50,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_89,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_50,c_77])).

tff(c_54,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_137,plain,(
    ! [A_64,B_65,C_66] :
      ( k2_relset_1(A_64,B_65,C_66) = k2_relat_1(C_66)
      | ~ m1_subset_1(C_66,k1_zfmisc_1(k2_zfmisc_1(A_64,B_65))) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_149,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_50,c_137])).

tff(c_199,plain,(
    ! [A_75,B_76,C_77] :
      ( m1_subset_1(k2_relset_1(A_75,B_76,C_77),k1_zfmisc_1(B_76))
      | ~ m1_subset_1(C_77,k1_zfmisc_1(k2_zfmisc_1(A_75,B_76))) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_223,plain,
    ( m1_subset_1(k2_relat_1('#skF_5'),k1_zfmisc_1('#skF_3'))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_149,c_199])).

tff(c_234,plain,(
    m1_subset_1(k2_relat_1('#skF_5'),k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_223])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( r1_tarski(A_3,B_4)
      | ~ m1_subset_1(A_3,k1_zfmisc_1(B_4)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_251,plain,(
    r1_tarski(k2_relat_1('#skF_5'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_234,c_8])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_254,plain,
    ( k2_relat_1('#skF_5') = '#skF_3'
    | ~ r1_tarski('#skF_3',k2_relat_1('#skF_5')) ),
    inference(resolution,[status(thm)],[c_251,c_2])).

tff(c_259,plain,(
    ~ r1_tarski('#skF_3',k2_relat_1('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_254])).

tff(c_2769,plain,(
    ! [E_299,C_301,B_298,D_302,A_297,F_300] :
      ( k1_partfun1(A_297,B_298,C_301,D_302,E_299,F_300) = k5_relat_1(E_299,F_300)
      | ~ m1_subset_1(F_300,k1_zfmisc_1(k2_zfmisc_1(C_301,D_302)))
      | ~ v1_funct_1(F_300)
      | ~ m1_subset_1(E_299,k1_zfmisc_1(k2_zfmisc_1(A_297,B_298)))
      | ~ v1_funct_1(E_299) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_2793,plain,(
    ! [A_297,B_298,E_299] :
      ( k1_partfun1(A_297,B_298,'#skF_2','#skF_3',E_299,'#skF_5') = k5_relat_1(E_299,'#skF_5')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1(E_299,k1_zfmisc_1(k2_zfmisc_1(A_297,B_298)))
      | ~ v1_funct_1(E_299) ) ),
    inference(resolution,[status(thm)],[c_50,c_2769])).

tff(c_2998,plain,(
    ! [A_305,B_306,E_307] :
      ( k1_partfun1(A_305,B_306,'#skF_2','#skF_3',E_307,'#skF_5') = k5_relat_1(E_307,'#skF_5')
      | ~ m1_subset_1(E_307,k1_zfmisc_1(k2_zfmisc_1(A_305,B_306)))
      | ~ v1_funct_1(E_307) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_2793])).

tff(c_3038,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_3','#skF_4','#skF_5') = k5_relat_1('#skF_4','#skF_5')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_56,c_2998])).

tff(c_3054,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_3','#skF_4','#skF_5') = k5_relat_1('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_3038])).

tff(c_48,plain,(
    k2_relset_1('#skF_1','#skF_3',k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_3','#skF_4','#skF_5')) = '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_793,plain,(
    ! [B_150,C_154,D_149,E_153,F_152,A_151] :
      ( k4_relset_1(A_151,B_150,C_154,D_149,E_153,F_152) = k5_relat_1(E_153,F_152)
      | ~ m1_subset_1(F_152,k1_zfmisc_1(k2_zfmisc_1(C_154,D_149)))
      | ~ m1_subset_1(E_153,k1_zfmisc_1(k2_zfmisc_1(A_151,B_150))) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_812,plain,(
    ! [A_155,B_156,E_157] :
      ( k4_relset_1(A_155,B_156,'#skF_2','#skF_3',E_157,'#skF_5') = k5_relat_1(E_157,'#skF_5')
      | ~ m1_subset_1(E_157,k1_zfmisc_1(k2_zfmisc_1(A_155,B_156))) ) ),
    inference(resolution,[status(thm)],[c_50,c_793])).

tff(c_835,plain,(
    k4_relset_1('#skF_1','#skF_2','#skF_2','#skF_3','#skF_4','#skF_5') = k5_relat_1('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_56,c_812])).

tff(c_916,plain,(
    ! [D_170,A_167,C_166,B_168,E_171,F_169] :
      ( m1_subset_1(k4_relset_1(A_167,B_168,C_166,D_170,E_171,F_169),k1_zfmisc_1(k2_zfmisc_1(A_167,D_170)))
      | ~ m1_subset_1(F_169,k1_zfmisc_1(k2_zfmisc_1(C_166,D_170)))
      | ~ m1_subset_1(E_171,k1_zfmisc_1(k2_zfmisc_1(A_167,B_168))) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_972,plain,
    ( m1_subset_1(k5_relat_1('#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3')))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_835,c_916])).

tff(c_997,plain,(
    m1_subset_1(k5_relat_1('#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_50,c_972])).

tff(c_1294,plain,(
    r1_tarski(k5_relat_1('#skF_4','#skF_5'),k2_zfmisc_1('#skF_1','#skF_3')) ),
    inference(resolution,[status(thm)],[c_997,c_8])).

tff(c_1187,plain,(
    ! [C_176,D_177,E_174,A_172,B_173,F_175] :
      ( k1_partfun1(A_172,B_173,C_176,D_177,E_174,F_175) = k5_relat_1(E_174,F_175)
      | ~ m1_subset_1(F_175,k1_zfmisc_1(k2_zfmisc_1(C_176,D_177)))
      | ~ v1_funct_1(F_175)
      | ~ m1_subset_1(E_174,k1_zfmisc_1(k2_zfmisc_1(A_172,B_173)))
      | ~ v1_funct_1(E_174) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_1206,plain,(
    ! [A_172,B_173,E_174] :
      ( k1_partfun1(A_172,B_173,'#skF_2','#skF_3',E_174,'#skF_5') = k5_relat_1(E_174,'#skF_5')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1(E_174,k1_zfmisc_1(k2_zfmisc_1(A_172,B_173)))
      | ~ v1_funct_1(E_174) ) ),
    inference(resolution,[status(thm)],[c_50,c_1187])).

tff(c_1455,plain,(
    ! [A_183,B_184,E_185] :
      ( k1_partfun1(A_183,B_184,'#skF_2','#skF_3',E_185,'#skF_5') = k5_relat_1(E_185,'#skF_5')
      | ~ m1_subset_1(E_185,k1_zfmisc_1(k2_zfmisc_1(A_183,B_184)))
      | ~ v1_funct_1(E_185) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_1206])).

tff(c_1488,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_3','#skF_4','#skF_5') = k5_relat_1('#skF_4','#skF_5')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_56,c_1455])).

tff(c_1502,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_3','#skF_4','#skF_5') = k5_relat_1('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_1488])).

tff(c_10,plain,(
    ! [A_3,B_4] :
      ( m1_subset_1(A_3,k1_zfmisc_1(B_4))
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_226,plain,
    ( m1_subset_1('#skF_3',k1_zfmisc_1('#skF_3'))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_3','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_199])).

tff(c_313,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_3','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_226])).

tff(c_376,plain,(
    ~ r1_tarski(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_3','#skF_4','#skF_5'),k2_zfmisc_1('#skF_1','#skF_3')) ),
    inference(resolution,[status(thm)],[c_10,c_313])).

tff(c_1507,plain,(
    ~ r1_tarski(k5_relat_1('#skF_4','#skF_5'),k2_zfmisc_1('#skF_1','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1502,c_376])).

tff(c_1512,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1294,c_1507])).

tff(c_1514,plain,(
    m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_3','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_226])).

tff(c_24,plain,(
    ! [A_26,B_27,C_28] :
      ( k2_relset_1(A_26,B_27,C_28) = k2_relat_1(C_28)
      | ~ m1_subset_1(C_28,k1_zfmisc_1(k2_zfmisc_1(A_26,B_27))) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_1527,plain,(
    k2_relset_1('#skF_1','#skF_3',k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_3','#skF_4','#skF_5')) = k2_relat_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_3','#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_1514,c_24])).

tff(c_1538,plain,(
    k2_relat_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_3','#skF_4','#skF_5')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_1527])).

tff(c_3072,plain,(
    k2_relat_1(k5_relat_1('#skF_4','#skF_5')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3054,c_1538])).

tff(c_12,plain,(
    ! [A_5,B_7] :
      ( r1_tarski(k2_relat_1(k5_relat_1(A_5,B_7)),k2_relat_1(B_7))
      | ~ v1_relat_1(B_7)
      | ~ v1_relat_1(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_3099,plain,
    ( r1_tarski('#skF_3',k2_relat_1('#skF_5'))
    | ~ v1_relat_1('#skF_5')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_3072,c_12])).

tff(c_3114,plain,(
    r1_tarski('#skF_3',k2_relat_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_89,c_3099])).

tff(c_3116,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_259,c_3114])).

tff(c_3117,plain,(
    k2_relat_1('#skF_5') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_254])).

tff(c_46,plain,(
    v2_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_44,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_52,plain,(
    v1_funct_2('#skF_5','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_185,plain,(
    ! [A_72,B_73,C_74] :
      ( k1_relset_1(A_72,B_73,C_74) = k1_relat_1(C_74)
      | ~ m1_subset_1(C_74,k1_zfmisc_1(k2_zfmisc_1(A_72,B_73))) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_197,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_50,c_185])).

tff(c_3401,plain,(
    ! [B_358,A_359,C_360] :
      ( k1_xboole_0 = B_358
      | k1_relset_1(A_359,B_358,C_360) = A_359
      | ~ v1_funct_2(C_360,A_359,B_358)
      | ~ m1_subset_1(C_360,k1_zfmisc_1(k2_zfmisc_1(A_359,B_358))) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_3412,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relset_1('#skF_2','#skF_3','#skF_5') = '#skF_2'
    | ~ v1_funct_2('#skF_5','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_50,c_3401])).

tff(c_3420,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relat_1('#skF_5') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_197,c_3412])).

tff(c_3421,plain,(
    k1_relat_1('#skF_5') = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_3420])).

tff(c_3444,plain,(
    ! [A_361,B_362] :
      ( r1_tarski(k1_relat_1(A_361),k2_relat_1(B_362))
      | ~ v2_funct_1(A_361)
      | k2_relat_1(k5_relat_1(B_362,A_361)) != k2_relat_1(A_361)
      | ~ v1_funct_1(B_362)
      | ~ v1_relat_1(B_362)
      | ~ v1_funct_1(A_361)
      | ~ v1_relat_1(A_361) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_3456,plain,(
    ! [B_362] :
      ( r1_tarski('#skF_2',k2_relat_1(B_362))
      | ~ v2_funct_1('#skF_5')
      | k2_relat_1(k5_relat_1(B_362,'#skF_5')) != k2_relat_1('#skF_5')
      | ~ v1_funct_1(B_362)
      | ~ v1_relat_1(B_362)
      | ~ v1_funct_1('#skF_5')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3421,c_3444])).

tff(c_3470,plain,(
    ! [B_363] :
      ( r1_tarski('#skF_2',k2_relat_1(B_363))
      | k2_relat_1(k5_relat_1(B_363,'#skF_5')) != '#skF_3'
      | ~ v1_funct_1(B_363)
      | ~ v1_relat_1(B_363) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_89,c_54,c_3117,c_46,c_3456])).

tff(c_150,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_56,c_137])).

tff(c_42,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_4') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_155,plain,(
    k2_relat_1('#skF_4') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_150,c_42])).

tff(c_220,plain,
    ( m1_subset_1(k2_relat_1('#skF_4'),k1_zfmisc_1('#skF_2'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_150,c_199])).

tff(c_232,plain,(
    m1_subset_1(k2_relat_1('#skF_4'),k1_zfmisc_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_220])).

tff(c_238,plain,(
    r1_tarski(k2_relat_1('#skF_4'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_232,c_8])).

tff(c_240,plain,
    ( k2_relat_1('#skF_4') = '#skF_2'
    | ~ r1_tarski('#skF_2',k2_relat_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_238,c_2])).

tff(c_243,plain,(
    ~ r1_tarski('#skF_2',k2_relat_1('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_155,c_240])).

tff(c_3477,plain,
    ( k2_relat_1(k5_relat_1('#skF_4','#skF_5')) != '#skF_3'
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_3470,c_243])).

tff(c_3488,plain,(
    k2_relat_1(k5_relat_1('#skF_4','#skF_5')) != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_60,c_3477])).

tff(c_4014,plain,(
    ! [C_406,F_405,B_403,D_407,E_404,A_402] :
      ( k1_partfun1(A_402,B_403,C_406,D_407,E_404,F_405) = k5_relat_1(E_404,F_405)
      | ~ m1_subset_1(F_405,k1_zfmisc_1(k2_zfmisc_1(C_406,D_407)))
      | ~ v1_funct_1(F_405)
      | ~ m1_subset_1(E_404,k1_zfmisc_1(k2_zfmisc_1(A_402,B_403)))
      | ~ v1_funct_1(E_404) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_4031,plain,(
    ! [A_402,B_403,E_404] :
      ( k1_partfun1(A_402,B_403,'#skF_2','#skF_3',E_404,'#skF_5') = k5_relat_1(E_404,'#skF_5')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1(E_404,k1_zfmisc_1(k2_zfmisc_1(A_402,B_403)))
      | ~ v1_funct_1(E_404) ) ),
    inference(resolution,[status(thm)],[c_50,c_4014])).

tff(c_4433,plain,(
    ! [A_416,B_417,E_418] :
      ( k1_partfun1(A_416,B_417,'#skF_2','#skF_3',E_418,'#skF_5') = k5_relat_1(E_418,'#skF_5')
      | ~ m1_subset_1(E_418,k1_zfmisc_1(k2_zfmisc_1(A_416,B_417)))
      | ~ v1_funct_1(E_418) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_4031])).

tff(c_4466,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_3','#skF_4','#skF_5') = k5_relat_1('#skF_4','#skF_5')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_56,c_4433])).

tff(c_4480,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_3','#skF_4','#skF_5') = k5_relat_1('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_4466])).

tff(c_4493,plain,(
    k2_relset_1('#skF_1','#skF_3',k5_relat_1('#skF_4','#skF_5')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4480,c_48])).

tff(c_3618,plain,(
    ! [D_372,A_374,E_376,C_377,B_373,F_375] :
      ( k4_relset_1(A_374,B_373,C_377,D_372,E_376,F_375) = k5_relat_1(E_376,F_375)
      | ~ m1_subset_1(F_375,k1_zfmisc_1(k2_zfmisc_1(C_377,D_372)))
      | ~ m1_subset_1(E_376,k1_zfmisc_1(k2_zfmisc_1(A_374,B_373))) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_3719,plain,(
    ! [A_386,B_387,E_388] :
      ( k4_relset_1(A_386,B_387,'#skF_2','#skF_3',E_388,'#skF_5') = k5_relat_1(E_388,'#skF_5')
      | ~ m1_subset_1(E_388,k1_zfmisc_1(k2_zfmisc_1(A_386,B_387))) ) ),
    inference(resolution,[status(thm)],[c_50,c_3618])).

tff(c_3742,plain,(
    k4_relset_1('#skF_1','#skF_2','#skF_2','#skF_3','#skF_4','#skF_5') = k5_relat_1('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_56,c_3719])).

tff(c_3800,plain,(
    ! [A_397,C_396,B_398,F_399,D_400,E_401] :
      ( m1_subset_1(k4_relset_1(A_397,B_398,C_396,D_400,E_401,F_399),k1_zfmisc_1(k2_zfmisc_1(A_397,D_400)))
      | ~ m1_subset_1(F_399,k1_zfmisc_1(k2_zfmisc_1(C_396,D_400)))
      | ~ m1_subset_1(E_401,k1_zfmisc_1(k2_zfmisc_1(A_397,B_398))) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_3847,plain,
    ( m1_subset_1(k5_relat_1('#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3')))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_3742,c_3800])).

tff(c_3867,plain,(
    m1_subset_1(k5_relat_1('#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_50,c_3847])).

tff(c_3905,plain,(
    k2_relset_1('#skF_1','#skF_3',k5_relat_1('#skF_4','#skF_5')) = k2_relat_1(k5_relat_1('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_3867,c_24])).

tff(c_4498,plain,(
    k2_relat_1(k5_relat_1('#skF_4','#skF_5')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4493,c_3905])).

tff(c_4500,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3488,c_4498])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:33:38 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.76/2.14  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.76/2.15  
% 5.76/2.15  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.76/2.15  %$ v1_funct_2 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k4_relset_1 > k1_partfun1 > k2_relset_1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 5.76/2.15  
% 5.76/2.15  %Foreground sorts:
% 5.76/2.15  
% 5.76/2.15  
% 5.76/2.15  %Background operators:
% 5.76/2.15  
% 5.76/2.15  
% 5.76/2.15  %Foreground operators:
% 5.76/2.15  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 5.76/2.15  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 5.76/2.15  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 5.76/2.15  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.76/2.15  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.76/2.15  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 5.76/2.15  tff(k4_relset_1, type, k4_relset_1: ($i * $i * $i * $i * $i * $i) > $i).
% 5.76/2.15  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.76/2.15  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 5.76/2.15  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 5.76/2.15  tff('#skF_5', type, '#skF_5': $i).
% 5.76/2.15  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 5.76/2.15  tff('#skF_2', type, '#skF_2': $i).
% 5.76/2.15  tff('#skF_3', type, '#skF_3': $i).
% 5.76/2.15  tff('#skF_1', type, '#skF_1': $i).
% 5.76/2.15  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 5.76/2.15  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.76/2.15  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.76/2.15  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.76/2.15  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 5.76/2.15  tff('#skF_4', type, '#skF_4': $i).
% 5.76/2.15  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.76/2.15  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 5.76/2.15  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.76/2.15  
% 5.76/2.18  tff(f_135, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, B, C)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (((k2_relset_1(A, C, k1_partfun1(A, B, B, C, D, E)) = C) & v2_funct_1(E)) => ((C = k1_xboole_0) | (k2_relset_1(A, B, D) = B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_funct_2)).
% 5.76/2.18  tff(f_61, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 5.76/2.18  tff(f_79, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 5.76/2.18  tff(f_65, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k2_relset_1(A, B, C), k1_zfmisc_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_relset_1)).
% 5.76/2.18  tff(f_35, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 5.76/2.18  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 5.76/2.18  tff(f_113, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 5.76/2.18  tff(f_85, axiom, (![A, B, C, D, E, F]: ((m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k4_relset_1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k4_relset_1)).
% 5.76/2.18  tff(f_71, axiom, (![A, B, C, D, E, F]: ((m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => m1_subset_1(k4_relset_1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k4_relset_1)).
% 5.76/2.18  tff(f_42, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => r1_tarski(k2_relat_1(k5_relat_1(A, B)), k2_relat_1(B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t45_relat_1)).
% 5.76/2.18  tff(f_75, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 5.76/2.18  tff(f_103, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 5.76/2.18  tff(f_57, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (((k2_relat_1(k5_relat_1(B, A)) = k2_relat_1(A)) & v2_funct_1(A)) => r1_tarski(k1_relat_1(A), k2_relat_1(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t51_funct_1)).
% 5.76/2.18  tff(c_56, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_135])).
% 5.76/2.18  tff(c_77, plain, (![C_50, A_51, B_52]: (v1_relat_1(C_50) | ~m1_subset_1(C_50, k1_zfmisc_1(k2_zfmisc_1(A_51, B_52))))), inference(cnfTransformation, [status(thm)], [f_61])).
% 5.76/2.18  tff(c_90, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_56, c_77])).
% 5.76/2.18  tff(c_60, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_135])).
% 5.76/2.18  tff(c_50, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_135])).
% 5.76/2.18  tff(c_89, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_50, c_77])).
% 5.76/2.18  tff(c_54, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_135])).
% 5.76/2.18  tff(c_137, plain, (![A_64, B_65, C_66]: (k2_relset_1(A_64, B_65, C_66)=k2_relat_1(C_66) | ~m1_subset_1(C_66, k1_zfmisc_1(k2_zfmisc_1(A_64, B_65))))), inference(cnfTransformation, [status(thm)], [f_79])).
% 5.76/2.18  tff(c_149, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_50, c_137])).
% 5.76/2.18  tff(c_199, plain, (![A_75, B_76, C_77]: (m1_subset_1(k2_relset_1(A_75, B_76, C_77), k1_zfmisc_1(B_76)) | ~m1_subset_1(C_77, k1_zfmisc_1(k2_zfmisc_1(A_75, B_76))))), inference(cnfTransformation, [status(thm)], [f_65])).
% 5.76/2.18  tff(c_223, plain, (m1_subset_1(k2_relat_1('#skF_5'), k1_zfmisc_1('#skF_3')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_149, c_199])).
% 5.76/2.18  tff(c_234, plain, (m1_subset_1(k2_relat_1('#skF_5'), k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_223])).
% 5.76/2.18  tff(c_8, plain, (![A_3, B_4]: (r1_tarski(A_3, B_4) | ~m1_subset_1(A_3, k1_zfmisc_1(B_4)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 5.76/2.18  tff(c_251, plain, (r1_tarski(k2_relat_1('#skF_5'), '#skF_3')), inference(resolution, [status(thm)], [c_234, c_8])).
% 5.76/2.18  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.76/2.18  tff(c_254, plain, (k2_relat_1('#skF_5')='#skF_3' | ~r1_tarski('#skF_3', k2_relat_1('#skF_5'))), inference(resolution, [status(thm)], [c_251, c_2])).
% 5.76/2.18  tff(c_259, plain, (~r1_tarski('#skF_3', k2_relat_1('#skF_5'))), inference(splitLeft, [status(thm)], [c_254])).
% 5.76/2.18  tff(c_2769, plain, (![E_299, C_301, B_298, D_302, A_297, F_300]: (k1_partfun1(A_297, B_298, C_301, D_302, E_299, F_300)=k5_relat_1(E_299, F_300) | ~m1_subset_1(F_300, k1_zfmisc_1(k2_zfmisc_1(C_301, D_302))) | ~v1_funct_1(F_300) | ~m1_subset_1(E_299, k1_zfmisc_1(k2_zfmisc_1(A_297, B_298))) | ~v1_funct_1(E_299))), inference(cnfTransformation, [status(thm)], [f_113])).
% 5.76/2.18  tff(c_2793, plain, (![A_297, B_298, E_299]: (k1_partfun1(A_297, B_298, '#skF_2', '#skF_3', E_299, '#skF_5')=k5_relat_1(E_299, '#skF_5') | ~v1_funct_1('#skF_5') | ~m1_subset_1(E_299, k1_zfmisc_1(k2_zfmisc_1(A_297, B_298))) | ~v1_funct_1(E_299))), inference(resolution, [status(thm)], [c_50, c_2769])).
% 5.76/2.18  tff(c_2998, plain, (![A_305, B_306, E_307]: (k1_partfun1(A_305, B_306, '#skF_2', '#skF_3', E_307, '#skF_5')=k5_relat_1(E_307, '#skF_5') | ~m1_subset_1(E_307, k1_zfmisc_1(k2_zfmisc_1(A_305, B_306))) | ~v1_funct_1(E_307))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_2793])).
% 5.76/2.18  tff(c_3038, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_3', '#skF_4', '#skF_5')=k5_relat_1('#skF_4', '#skF_5') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_56, c_2998])).
% 5.76/2.18  tff(c_3054, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_3', '#skF_4', '#skF_5')=k5_relat_1('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_3038])).
% 5.76/2.18  tff(c_48, plain, (k2_relset_1('#skF_1', '#skF_3', k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_3', '#skF_4', '#skF_5'))='#skF_3'), inference(cnfTransformation, [status(thm)], [f_135])).
% 5.76/2.18  tff(c_793, plain, (![B_150, C_154, D_149, E_153, F_152, A_151]: (k4_relset_1(A_151, B_150, C_154, D_149, E_153, F_152)=k5_relat_1(E_153, F_152) | ~m1_subset_1(F_152, k1_zfmisc_1(k2_zfmisc_1(C_154, D_149))) | ~m1_subset_1(E_153, k1_zfmisc_1(k2_zfmisc_1(A_151, B_150))))), inference(cnfTransformation, [status(thm)], [f_85])).
% 5.76/2.18  tff(c_812, plain, (![A_155, B_156, E_157]: (k4_relset_1(A_155, B_156, '#skF_2', '#skF_3', E_157, '#skF_5')=k5_relat_1(E_157, '#skF_5') | ~m1_subset_1(E_157, k1_zfmisc_1(k2_zfmisc_1(A_155, B_156))))), inference(resolution, [status(thm)], [c_50, c_793])).
% 5.76/2.18  tff(c_835, plain, (k4_relset_1('#skF_1', '#skF_2', '#skF_2', '#skF_3', '#skF_4', '#skF_5')=k5_relat_1('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_56, c_812])).
% 5.76/2.18  tff(c_916, plain, (![D_170, A_167, C_166, B_168, E_171, F_169]: (m1_subset_1(k4_relset_1(A_167, B_168, C_166, D_170, E_171, F_169), k1_zfmisc_1(k2_zfmisc_1(A_167, D_170))) | ~m1_subset_1(F_169, k1_zfmisc_1(k2_zfmisc_1(C_166, D_170))) | ~m1_subset_1(E_171, k1_zfmisc_1(k2_zfmisc_1(A_167, B_168))))), inference(cnfTransformation, [status(thm)], [f_71])).
% 5.76/2.18  tff(c_972, plain, (m1_subset_1(k5_relat_1('#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3'))) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_835, c_916])).
% 5.76/2.18  tff(c_997, plain, (m1_subset_1(k5_relat_1('#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_50, c_972])).
% 5.76/2.18  tff(c_1294, plain, (r1_tarski(k5_relat_1('#skF_4', '#skF_5'), k2_zfmisc_1('#skF_1', '#skF_3'))), inference(resolution, [status(thm)], [c_997, c_8])).
% 5.76/2.18  tff(c_1187, plain, (![C_176, D_177, E_174, A_172, B_173, F_175]: (k1_partfun1(A_172, B_173, C_176, D_177, E_174, F_175)=k5_relat_1(E_174, F_175) | ~m1_subset_1(F_175, k1_zfmisc_1(k2_zfmisc_1(C_176, D_177))) | ~v1_funct_1(F_175) | ~m1_subset_1(E_174, k1_zfmisc_1(k2_zfmisc_1(A_172, B_173))) | ~v1_funct_1(E_174))), inference(cnfTransformation, [status(thm)], [f_113])).
% 5.76/2.18  tff(c_1206, plain, (![A_172, B_173, E_174]: (k1_partfun1(A_172, B_173, '#skF_2', '#skF_3', E_174, '#skF_5')=k5_relat_1(E_174, '#skF_5') | ~v1_funct_1('#skF_5') | ~m1_subset_1(E_174, k1_zfmisc_1(k2_zfmisc_1(A_172, B_173))) | ~v1_funct_1(E_174))), inference(resolution, [status(thm)], [c_50, c_1187])).
% 5.76/2.18  tff(c_1455, plain, (![A_183, B_184, E_185]: (k1_partfun1(A_183, B_184, '#skF_2', '#skF_3', E_185, '#skF_5')=k5_relat_1(E_185, '#skF_5') | ~m1_subset_1(E_185, k1_zfmisc_1(k2_zfmisc_1(A_183, B_184))) | ~v1_funct_1(E_185))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_1206])).
% 5.76/2.18  tff(c_1488, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_3', '#skF_4', '#skF_5')=k5_relat_1('#skF_4', '#skF_5') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_56, c_1455])).
% 5.76/2.18  tff(c_1502, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_3', '#skF_4', '#skF_5')=k5_relat_1('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_1488])).
% 5.76/2.18  tff(c_10, plain, (![A_3, B_4]: (m1_subset_1(A_3, k1_zfmisc_1(B_4)) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 5.76/2.18  tff(c_226, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_3')) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_3', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_48, c_199])).
% 5.76/2.18  tff(c_313, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_3', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3')))), inference(splitLeft, [status(thm)], [c_226])).
% 5.76/2.18  tff(c_376, plain, (~r1_tarski(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_3', '#skF_4', '#skF_5'), k2_zfmisc_1('#skF_1', '#skF_3'))), inference(resolution, [status(thm)], [c_10, c_313])).
% 5.76/2.18  tff(c_1507, plain, (~r1_tarski(k5_relat_1('#skF_4', '#skF_5'), k2_zfmisc_1('#skF_1', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_1502, c_376])).
% 5.76/2.18  tff(c_1512, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1294, c_1507])).
% 5.76/2.18  tff(c_1514, plain, (m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_3', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3')))), inference(splitRight, [status(thm)], [c_226])).
% 5.76/2.18  tff(c_24, plain, (![A_26, B_27, C_28]: (k2_relset_1(A_26, B_27, C_28)=k2_relat_1(C_28) | ~m1_subset_1(C_28, k1_zfmisc_1(k2_zfmisc_1(A_26, B_27))))), inference(cnfTransformation, [status(thm)], [f_79])).
% 5.76/2.18  tff(c_1527, plain, (k2_relset_1('#skF_1', '#skF_3', k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_3', '#skF_4', '#skF_5'))=k2_relat_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_3', '#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_1514, c_24])).
% 5.76/2.18  tff(c_1538, plain, (k2_relat_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_3', '#skF_4', '#skF_5'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_48, c_1527])).
% 5.76/2.18  tff(c_3072, plain, (k2_relat_1(k5_relat_1('#skF_4', '#skF_5'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_3054, c_1538])).
% 5.76/2.18  tff(c_12, plain, (![A_5, B_7]: (r1_tarski(k2_relat_1(k5_relat_1(A_5, B_7)), k2_relat_1(B_7)) | ~v1_relat_1(B_7) | ~v1_relat_1(A_5))), inference(cnfTransformation, [status(thm)], [f_42])).
% 5.76/2.18  tff(c_3099, plain, (r1_tarski('#skF_3', k2_relat_1('#skF_5')) | ~v1_relat_1('#skF_5') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_3072, c_12])).
% 5.76/2.18  tff(c_3114, plain, (r1_tarski('#skF_3', k2_relat_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_90, c_89, c_3099])).
% 5.76/2.18  tff(c_3116, plain, $false, inference(negUnitSimplification, [status(thm)], [c_259, c_3114])).
% 5.76/2.18  tff(c_3117, plain, (k2_relat_1('#skF_5')='#skF_3'), inference(splitRight, [status(thm)], [c_254])).
% 5.76/2.18  tff(c_46, plain, (v2_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_135])).
% 5.76/2.18  tff(c_44, plain, (k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_135])).
% 5.76/2.18  tff(c_52, plain, (v1_funct_2('#skF_5', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_135])).
% 5.76/2.18  tff(c_185, plain, (![A_72, B_73, C_74]: (k1_relset_1(A_72, B_73, C_74)=k1_relat_1(C_74) | ~m1_subset_1(C_74, k1_zfmisc_1(k2_zfmisc_1(A_72, B_73))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 5.76/2.18  tff(c_197, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_50, c_185])).
% 5.76/2.18  tff(c_3401, plain, (![B_358, A_359, C_360]: (k1_xboole_0=B_358 | k1_relset_1(A_359, B_358, C_360)=A_359 | ~v1_funct_2(C_360, A_359, B_358) | ~m1_subset_1(C_360, k1_zfmisc_1(k2_zfmisc_1(A_359, B_358))))), inference(cnfTransformation, [status(thm)], [f_103])).
% 5.76/2.18  tff(c_3412, plain, (k1_xboole_0='#skF_3' | k1_relset_1('#skF_2', '#skF_3', '#skF_5')='#skF_2' | ~v1_funct_2('#skF_5', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_50, c_3401])).
% 5.76/2.18  tff(c_3420, plain, (k1_xboole_0='#skF_3' | k1_relat_1('#skF_5')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_52, c_197, c_3412])).
% 5.76/2.18  tff(c_3421, plain, (k1_relat_1('#skF_5')='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_44, c_3420])).
% 5.76/2.18  tff(c_3444, plain, (![A_361, B_362]: (r1_tarski(k1_relat_1(A_361), k2_relat_1(B_362)) | ~v2_funct_1(A_361) | k2_relat_1(k5_relat_1(B_362, A_361))!=k2_relat_1(A_361) | ~v1_funct_1(B_362) | ~v1_relat_1(B_362) | ~v1_funct_1(A_361) | ~v1_relat_1(A_361))), inference(cnfTransformation, [status(thm)], [f_57])).
% 5.76/2.18  tff(c_3456, plain, (![B_362]: (r1_tarski('#skF_2', k2_relat_1(B_362)) | ~v2_funct_1('#skF_5') | k2_relat_1(k5_relat_1(B_362, '#skF_5'))!=k2_relat_1('#skF_5') | ~v1_funct_1(B_362) | ~v1_relat_1(B_362) | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_3421, c_3444])).
% 5.76/2.18  tff(c_3470, plain, (![B_363]: (r1_tarski('#skF_2', k2_relat_1(B_363)) | k2_relat_1(k5_relat_1(B_363, '#skF_5'))!='#skF_3' | ~v1_funct_1(B_363) | ~v1_relat_1(B_363))), inference(demodulation, [status(thm), theory('equality')], [c_89, c_54, c_3117, c_46, c_3456])).
% 5.76/2.18  tff(c_150, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_56, c_137])).
% 5.76/2.18  tff(c_42, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_4')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_135])).
% 5.76/2.18  tff(c_155, plain, (k2_relat_1('#skF_4')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_150, c_42])).
% 5.76/2.18  tff(c_220, plain, (m1_subset_1(k2_relat_1('#skF_4'), k1_zfmisc_1('#skF_2')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_150, c_199])).
% 5.76/2.18  tff(c_232, plain, (m1_subset_1(k2_relat_1('#skF_4'), k1_zfmisc_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_220])).
% 5.76/2.18  tff(c_238, plain, (r1_tarski(k2_relat_1('#skF_4'), '#skF_2')), inference(resolution, [status(thm)], [c_232, c_8])).
% 5.76/2.18  tff(c_240, plain, (k2_relat_1('#skF_4')='#skF_2' | ~r1_tarski('#skF_2', k2_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_238, c_2])).
% 5.76/2.18  tff(c_243, plain, (~r1_tarski('#skF_2', k2_relat_1('#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_155, c_240])).
% 5.76/2.18  tff(c_3477, plain, (k2_relat_1(k5_relat_1('#skF_4', '#skF_5'))!='#skF_3' | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_3470, c_243])).
% 5.76/2.18  tff(c_3488, plain, (k2_relat_1(k5_relat_1('#skF_4', '#skF_5'))!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_90, c_60, c_3477])).
% 5.76/2.18  tff(c_4014, plain, (![C_406, F_405, B_403, D_407, E_404, A_402]: (k1_partfun1(A_402, B_403, C_406, D_407, E_404, F_405)=k5_relat_1(E_404, F_405) | ~m1_subset_1(F_405, k1_zfmisc_1(k2_zfmisc_1(C_406, D_407))) | ~v1_funct_1(F_405) | ~m1_subset_1(E_404, k1_zfmisc_1(k2_zfmisc_1(A_402, B_403))) | ~v1_funct_1(E_404))), inference(cnfTransformation, [status(thm)], [f_113])).
% 5.76/2.18  tff(c_4031, plain, (![A_402, B_403, E_404]: (k1_partfun1(A_402, B_403, '#skF_2', '#skF_3', E_404, '#skF_5')=k5_relat_1(E_404, '#skF_5') | ~v1_funct_1('#skF_5') | ~m1_subset_1(E_404, k1_zfmisc_1(k2_zfmisc_1(A_402, B_403))) | ~v1_funct_1(E_404))), inference(resolution, [status(thm)], [c_50, c_4014])).
% 5.76/2.18  tff(c_4433, plain, (![A_416, B_417, E_418]: (k1_partfun1(A_416, B_417, '#skF_2', '#skF_3', E_418, '#skF_5')=k5_relat_1(E_418, '#skF_5') | ~m1_subset_1(E_418, k1_zfmisc_1(k2_zfmisc_1(A_416, B_417))) | ~v1_funct_1(E_418))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_4031])).
% 5.76/2.18  tff(c_4466, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_3', '#skF_4', '#skF_5')=k5_relat_1('#skF_4', '#skF_5') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_56, c_4433])).
% 5.76/2.18  tff(c_4480, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_3', '#skF_4', '#skF_5')=k5_relat_1('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_4466])).
% 5.76/2.18  tff(c_4493, plain, (k2_relset_1('#skF_1', '#skF_3', k5_relat_1('#skF_4', '#skF_5'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_4480, c_48])).
% 5.76/2.18  tff(c_3618, plain, (![D_372, A_374, E_376, C_377, B_373, F_375]: (k4_relset_1(A_374, B_373, C_377, D_372, E_376, F_375)=k5_relat_1(E_376, F_375) | ~m1_subset_1(F_375, k1_zfmisc_1(k2_zfmisc_1(C_377, D_372))) | ~m1_subset_1(E_376, k1_zfmisc_1(k2_zfmisc_1(A_374, B_373))))), inference(cnfTransformation, [status(thm)], [f_85])).
% 5.76/2.18  tff(c_3719, plain, (![A_386, B_387, E_388]: (k4_relset_1(A_386, B_387, '#skF_2', '#skF_3', E_388, '#skF_5')=k5_relat_1(E_388, '#skF_5') | ~m1_subset_1(E_388, k1_zfmisc_1(k2_zfmisc_1(A_386, B_387))))), inference(resolution, [status(thm)], [c_50, c_3618])).
% 5.76/2.18  tff(c_3742, plain, (k4_relset_1('#skF_1', '#skF_2', '#skF_2', '#skF_3', '#skF_4', '#skF_5')=k5_relat_1('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_56, c_3719])).
% 5.76/2.18  tff(c_3800, plain, (![A_397, C_396, B_398, F_399, D_400, E_401]: (m1_subset_1(k4_relset_1(A_397, B_398, C_396, D_400, E_401, F_399), k1_zfmisc_1(k2_zfmisc_1(A_397, D_400))) | ~m1_subset_1(F_399, k1_zfmisc_1(k2_zfmisc_1(C_396, D_400))) | ~m1_subset_1(E_401, k1_zfmisc_1(k2_zfmisc_1(A_397, B_398))))), inference(cnfTransformation, [status(thm)], [f_71])).
% 5.76/2.18  tff(c_3847, plain, (m1_subset_1(k5_relat_1('#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3'))) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_3742, c_3800])).
% 5.76/2.18  tff(c_3867, plain, (m1_subset_1(k5_relat_1('#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_50, c_3847])).
% 5.76/2.18  tff(c_3905, plain, (k2_relset_1('#skF_1', '#skF_3', k5_relat_1('#skF_4', '#skF_5'))=k2_relat_1(k5_relat_1('#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_3867, c_24])).
% 5.76/2.18  tff(c_4498, plain, (k2_relat_1(k5_relat_1('#skF_4', '#skF_5'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_4493, c_3905])).
% 5.76/2.18  tff(c_4500, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3488, c_4498])).
% 5.76/2.18  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.76/2.18  
% 5.76/2.18  Inference rules
% 5.76/2.18  ----------------------
% 5.76/2.18  #Ref     : 0
% 5.76/2.18  #Sup     : 986
% 5.76/2.18  #Fact    : 0
% 5.76/2.18  #Define  : 0
% 5.76/2.18  #Split   : 18
% 5.76/2.18  #Chain   : 0
% 5.76/2.18  #Close   : 0
% 5.76/2.18  
% 5.76/2.18  Ordering : KBO
% 5.76/2.18  
% 5.76/2.18  Simplification rules
% 5.76/2.18  ----------------------
% 5.76/2.18  #Subsume      : 14
% 5.76/2.18  #Demod        : 366
% 5.76/2.18  #Tautology    : 264
% 5.76/2.18  #SimpNegUnit  : 52
% 5.76/2.18  #BackRed      : 38
% 5.76/2.18  
% 5.76/2.18  #Partial instantiations: 0
% 5.76/2.18  #Strategies tried      : 1
% 5.76/2.18  
% 5.76/2.18  Timing (in seconds)
% 5.76/2.18  ----------------------
% 6.05/2.18  Preprocessing        : 0.35
% 6.05/2.18  Parsing              : 0.19
% 6.05/2.18  CNF conversion       : 0.02
% 6.05/2.18  Main loop            : 1.01
% 6.05/2.18  Inferencing          : 0.35
% 6.05/2.18  Reduction            : 0.34
% 6.05/2.18  Demodulation         : 0.24
% 6.05/2.18  BG Simplification    : 0.04
% 6.05/2.18  Subsumption          : 0.18
% 6.05/2.18  Abstraction          : 0.06
% 6.05/2.18  MUC search           : 0.00
% 6.05/2.18  Cooper               : 0.00
% 6.05/2.18  Total                : 1.41
% 6.05/2.18  Index Insertion      : 0.00
% 6.05/2.18  Index Deletion       : 0.00
% 6.05/2.18  Index Matching       : 0.00
% 6.05/2.18  BG Taut test         : 0.00
%------------------------------------------------------------------------------
