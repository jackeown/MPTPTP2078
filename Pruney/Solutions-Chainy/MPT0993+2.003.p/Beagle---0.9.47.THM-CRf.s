%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:13:43 EST 2020

% Result     : Theorem 2.46s
% Output     : CNFRefutation 2.46s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 157 expanded)
%              Number of leaves         :   32 (  68 expanded)
%              Depth                    :   11
%              Number of atoms          :  106 ( 352 expanded)
%              Number of equality atoms :   34 (  92 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_partfun1 > k1_relset_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_relset_1,type,(
    r2_relset_1: ( $i * $i * $i * $i ) > $o )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_106,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( r1_tarski(A,C)
         => r2_relset_1(A,B,k2_partfun1(A,B,D,C),D) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_funct_2)).

tff(f_65,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_47,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_57,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_89,axiom,(
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

tff(f_71,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,C)))
     => ( r1_tarski(k1_relat_1(D),B)
       => m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,C))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_relset_1)).

tff(f_53,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_95,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => k2_partfun1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(c_48,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_150,plain,(
    ! [A_55,B_56,D_57] :
      ( r2_relset_1(A_55,B_56,D_57,D_57)
      | ~ m1_subset_1(D_57,k1_zfmisc_1(k2_zfmisc_1(A_55,B_56))) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_157,plain,(
    r2_relset_1('#skF_1','#skF_2','#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_48,c_150])).

tff(c_92,plain,(
    ! [C_36,A_37,B_38] :
      ( v1_relat_1(C_36)
      | ~ m1_subset_1(C_36,k1_zfmisc_1(k2_zfmisc_1(A_37,B_38))) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_100,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_48,c_92])).

tff(c_46,plain,(
    r1_tarski('#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_50,plain,(
    v1_funct_2('#skF_4','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_160,plain,(
    ! [A_62,B_63,C_64] :
      ( k1_relset_1(A_62,B_63,C_64) = k1_relat_1(C_64)
      | ~ m1_subset_1(C_64,k1_zfmisc_1(k2_zfmisc_1(A_62,B_63))) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_170,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_48,c_160])).

tff(c_211,plain,(
    ! [B_90,A_91,C_92] :
      ( k1_xboole_0 = B_90
      | k1_relset_1(A_91,B_90,C_92) = A_91
      | ~ v1_funct_2(C_92,A_91,B_90)
      | ~ m1_subset_1(C_92,k1_zfmisc_1(k2_zfmisc_1(A_91,B_90))) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_214,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1('#skF_1','#skF_2','#skF_4') = '#skF_1'
    | ~ v1_funct_2('#skF_4','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_48,c_211])).

tff(c_223,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_170,c_214])).

tff(c_225,plain,(
    k1_relat_1('#skF_4') = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_223])).

tff(c_202,plain,(
    ! [D_86,B_87,C_88,A_89] :
      ( m1_subset_1(D_86,k1_zfmisc_1(k2_zfmisc_1(B_87,C_88)))
      | ~ r1_tarski(k1_relat_1(D_86),B_87)
      | ~ m1_subset_1(D_86,k1_zfmisc_1(k2_zfmisc_1(A_89,C_88))) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_209,plain,(
    ! [B_87] :
      ( m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(B_87,'#skF_2')))
      | ~ r1_tarski(k1_relat_1('#skF_4'),B_87) ) ),
    inference(resolution,[status(thm)],[c_48,c_202])).

tff(c_236,plain,(
    ! [B_93] :
      ( m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(B_93,'#skF_2')))
      | ~ r1_tarski('#skF_1',B_93) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_225,c_209])).

tff(c_20,plain,(
    ! [C_12,A_10,B_11] :
      ( v4_relat_1(C_12,A_10)
      | ~ m1_subset_1(C_12,k1_zfmisc_1(k2_zfmisc_1(A_10,B_11))) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_276,plain,(
    ! [B_94] :
      ( v4_relat_1('#skF_4',B_94)
      | ~ r1_tarski('#skF_1',B_94) ) ),
    inference(resolution,[status(thm)],[c_236,c_20])).

tff(c_14,plain,(
    ! [B_6,A_5] :
      ( k7_relat_1(B_6,A_5) = B_6
      | ~ v4_relat_1(B_6,A_5)
      | ~ v1_relat_1(B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_279,plain,(
    ! [B_94] :
      ( k7_relat_1('#skF_4',B_94) = '#skF_4'
      | ~ v1_relat_1('#skF_4')
      | ~ r1_tarski('#skF_1',B_94) ) ),
    inference(resolution,[status(thm)],[c_276,c_14])).

tff(c_284,plain,(
    ! [B_95] :
      ( k7_relat_1('#skF_4',B_95) = '#skF_4'
      | ~ r1_tarski('#skF_1',B_95) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_279])).

tff(c_294,plain,(
    k7_relat_1('#skF_4','#skF_3') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_46,c_284])).

tff(c_52,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_180,plain,(
    ! [A_75,B_76,C_77,D_78] :
      ( k2_partfun1(A_75,B_76,C_77,D_78) = k7_relat_1(C_77,D_78)
      | ~ m1_subset_1(C_77,k1_zfmisc_1(k2_zfmisc_1(A_75,B_76)))
      | ~ v1_funct_1(C_77) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_182,plain,(
    ! [D_78] :
      ( k2_partfun1('#skF_1','#skF_2','#skF_4',D_78) = k7_relat_1('#skF_4',D_78)
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_48,c_180])).

tff(c_189,plain,(
    ! [D_78] : k2_partfun1('#skF_1','#skF_2','#skF_4',D_78) = k7_relat_1('#skF_4',D_78) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_182])).

tff(c_44,plain,(
    ~ r2_relset_1('#skF_1','#skF_2',k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_190,plain,(
    ~ r2_relset_1('#skF_1','#skF_2',k7_relat_1('#skF_4','#skF_3'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_189,c_44])).

tff(c_295,plain,(
    ~ r2_relset_1('#skF_1','#skF_2','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_294,c_190])).

tff(c_298,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_157,c_295])).

tff(c_299,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_223])).

tff(c_10,plain,(
    ! [A_3] : k2_zfmisc_1(A_3,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_330,plain,(
    ! [A_3] : k2_zfmisc_1(A_3,'#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_299,c_299,c_10])).

tff(c_336,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_330,c_48])).

tff(c_125,plain,(
    ! [C_47,A_48,B_49] :
      ( v4_relat_1(C_47,A_48)
      | ~ m1_subset_1(C_47,k1_zfmisc_1(k2_zfmisc_1(A_48,B_49))) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_131,plain,(
    ! [C_47,A_3] :
      ( v4_relat_1(C_47,A_3)
      | ~ m1_subset_1(C_47,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_125])).

tff(c_413,plain,(
    ! [C_109,A_110] :
      ( v4_relat_1(C_109,A_110)
      | ~ m1_subset_1(C_109,k1_zfmisc_1('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_299,c_131])).

tff(c_419,plain,(
    ! [A_111] : v4_relat_1('#skF_4',A_111) ),
    inference(resolution,[status(thm)],[c_336,c_413])).

tff(c_422,plain,(
    ! [A_111] :
      ( k7_relat_1('#skF_4',A_111) = '#skF_4'
      | ~ v1_relat_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_419,c_14])).

tff(c_425,plain,(
    ! [A_111] : k7_relat_1('#skF_4',A_111) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_422])).

tff(c_426,plain,(
    ~ r2_relset_1('#skF_1','#skF_2','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_425,c_190])).

tff(c_431,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_157,c_426])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n012.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 17:55:37 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.46/1.28  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.46/1.29  
% 2.46/1.29  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.46/1.29  %$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_partfun1 > k1_relset_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.46/1.29  
% 2.46/1.29  %Foreground sorts:
% 2.46/1.29  
% 2.46/1.29  
% 2.46/1.29  %Background operators:
% 2.46/1.29  
% 2.46/1.29  
% 2.46/1.29  %Foreground operators:
% 2.46/1.29  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.46/1.29  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.46/1.29  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 2.46/1.29  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.46/1.29  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.46/1.29  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.46/1.29  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.46/1.29  tff('#skF_2', type, '#skF_2': $i).
% 2.46/1.29  tff('#skF_3', type, '#skF_3': $i).
% 2.46/1.29  tff('#skF_1', type, '#skF_1': $i).
% 2.46/1.29  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.46/1.29  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.46/1.29  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.46/1.29  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.46/1.29  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.46/1.29  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.46/1.29  tff('#skF_4', type, '#skF_4': $i).
% 2.46/1.29  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.46/1.29  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 2.46/1.29  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.46/1.29  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.46/1.29  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.46/1.29  
% 2.46/1.31  tff(f_106, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r1_tarski(A, C) => r2_relset_1(A, B, k2_partfun1(A, B, D, C), D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t40_funct_2)).
% 2.46/1.31  tff(f_65, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 2.46/1.31  tff(f_47, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.46/1.31  tff(f_57, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.46/1.31  tff(f_89, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 2.46/1.31  tff(f_71, axiom, (![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, C))) => (r1_tarski(k1_relat_1(D), B) => m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t13_relset_1)).
% 2.46/1.31  tff(f_53, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.46/1.31  tff(f_43, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t209_relat_1)).
% 2.46/1.31  tff(f_95, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (k2_partfun1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_partfun1)).
% 2.46/1.31  tff(f_37, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 2.46/1.31  tff(c_48, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_106])).
% 2.46/1.31  tff(c_150, plain, (![A_55, B_56, D_57]: (r2_relset_1(A_55, B_56, D_57, D_57) | ~m1_subset_1(D_57, k1_zfmisc_1(k2_zfmisc_1(A_55, B_56))))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.46/1.31  tff(c_157, plain, (r2_relset_1('#skF_1', '#skF_2', '#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_48, c_150])).
% 2.46/1.31  tff(c_92, plain, (![C_36, A_37, B_38]: (v1_relat_1(C_36) | ~m1_subset_1(C_36, k1_zfmisc_1(k2_zfmisc_1(A_37, B_38))))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.46/1.31  tff(c_100, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_48, c_92])).
% 2.46/1.31  tff(c_46, plain, (r1_tarski('#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_106])).
% 2.46/1.31  tff(c_50, plain, (v1_funct_2('#skF_4', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_106])).
% 2.46/1.31  tff(c_160, plain, (![A_62, B_63, C_64]: (k1_relset_1(A_62, B_63, C_64)=k1_relat_1(C_64) | ~m1_subset_1(C_64, k1_zfmisc_1(k2_zfmisc_1(A_62, B_63))))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.46/1.31  tff(c_170, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_48, c_160])).
% 2.46/1.31  tff(c_211, plain, (![B_90, A_91, C_92]: (k1_xboole_0=B_90 | k1_relset_1(A_91, B_90, C_92)=A_91 | ~v1_funct_2(C_92, A_91, B_90) | ~m1_subset_1(C_92, k1_zfmisc_1(k2_zfmisc_1(A_91, B_90))))), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.46/1.31  tff(c_214, plain, (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', '#skF_4')='#skF_1' | ~v1_funct_2('#skF_4', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_48, c_211])).
% 2.46/1.31  tff(c_223, plain, (k1_xboole_0='#skF_2' | k1_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_50, c_170, c_214])).
% 2.46/1.31  tff(c_225, plain, (k1_relat_1('#skF_4')='#skF_1'), inference(splitLeft, [status(thm)], [c_223])).
% 2.46/1.31  tff(c_202, plain, (![D_86, B_87, C_88, A_89]: (m1_subset_1(D_86, k1_zfmisc_1(k2_zfmisc_1(B_87, C_88))) | ~r1_tarski(k1_relat_1(D_86), B_87) | ~m1_subset_1(D_86, k1_zfmisc_1(k2_zfmisc_1(A_89, C_88))))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.46/1.31  tff(c_209, plain, (![B_87]: (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(B_87, '#skF_2'))) | ~r1_tarski(k1_relat_1('#skF_4'), B_87))), inference(resolution, [status(thm)], [c_48, c_202])).
% 2.46/1.31  tff(c_236, plain, (![B_93]: (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(B_93, '#skF_2'))) | ~r1_tarski('#skF_1', B_93))), inference(demodulation, [status(thm), theory('equality')], [c_225, c_209])).
% 2.46/1.31  tff(c_20, plain, (![C_12, A_10, B_11]: (v4_relat_1(C_12, A_10) | ~m1_subset_1(C_12, k1_zfmisc_1(k2_zfmisc_1(A_10, B_11))))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.46/1.31  tff(c_276, plain, (![B_94]: (v4_relat_1('#skF_4', B_94) | ~r1_tarski('#skF_1', B_94))), inference(resolution, [status(thm)], [c_236, c_20])).
% 2.46/1.31  tff(c_14, plain, (![B_6, A_5]: (k7_relat_1(B_6, A_5)=B_6 | ~v4_relat_1(B_6, A_5) | ~v1_relat_1(B_6))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.46/1.31  tff(c_279, plain, (![B_94]: (k7_relat_1('#skF_4', B_94)='#skF_4' | ~v1_relat_1('#skF_4') | ~r1_tarski('#skF_1', B_94))), inference(resolution, [status(thm)], [c_276, c_14])).
% 2.46/1.31  tff(c_284, plain, (![B_95]: (k7_relat_1('#skF_4', B_95)='#skF_4' | ~r1_tarski('#skF_1', B_95))), inference(demodulation, [status(thm), theory('equality')], [c_100, c_279])).
% 2.46/1.31  tff(c_294, plain, (k7_relat_1('#skF_4', '#skF_3')='#skF_4'), inference(resolution, [status(thm)], [c_46, c_284])).
% 2.46/1.31  tff(c_52, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_106])).
% 2.46/1.31  tff(c_180, plain, (![A_75, B_76, C_77, D_78]: (k2_partfun1(A_75, B_76, C_77, D_78)=k7_relat_1(C_77, D_78) | ~m1_subset_1(C_77, k1_zfmisc_1(k2_zfmisc_1(A_75, B_76))) | ~v1_funct_1(C_77))), inference(cnfTransformation, [status(thm)], [f_95])).
% 2.46/1.31  tff(c_182, plain, (![D_78]: (k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_78)=k7_relat_1('#skF_4', D_78) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_48, c_180])).
% 2.46/1.31  tff(c_189, plain, (![D_78]: (k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_78)=k7_relat_1('#skF_4', D_78))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_182])).
% 2.46/1.31  tff(c_44, plain, (~r2_relset_1('#skF_1', '#skF_2', k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_106])).
% 2.46/1.31  tff(c_190, plain, (~r2_relset_1('#skF_1', '#skF_2', k7_relat_1('#skF_4', '#skF_3'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_189, c_44])).
% 2.46/1.31  tff(c_295, plain, (~r2_relset_1('#skF_1', '#skF_2', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_294, c_190])).
% 2.46/1.31  tff(c_298, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_157, c_295])).
% 2.46/1.31  tff(c_299, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_223])).
% 2.46/1.31  tff(c_10, plain, (![A_3]: (k2_zfmisc_1(A_3, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.46/1.31  tff(c_330, plain, (![A_3]: (k2_zfmisc_1(A_3, '#skF_2')='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_299, c_299, c_10])).
% 2.46/1.31  tff(c_336, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_330, c_48])).
% 2.46/1.31  tff(c_125, plain, (![C_47, A_48, B_49]: (v4_relat_1(C_47, A_48) | ~m1_subset_1(C_47, k1_zfmisc_1(k2_zfmisc_1(A_48, B_49))))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.46/1.31  tff(c_131, plain, (![C_47, A_3]: (v4_relat_1(C_47, A_3) | ~m1_subset_1(C_47, k1_zfmisc_1(k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_125])).
% 2.46/1.31  tff(c_413, plain, (![C_109, A_110]: (v4_relat_1(C_109, A_110) | ~m1_subset_1(C_109, k1_zfmisc_1('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_299, c_131])).
% 2.46/1.31  tff(c_419, plain, (![A_111]: (v4_relat_1('#skF_4', A_111))), inference(resolution, [status(thm)], [c_336, c_413])).
% 2.46/1.31  tff(c_422, plain, (![A_111]: (k7_relat_1('#skF_4', A_111)='#skF_4' | ~v1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_419, c_14])).
% 2.46/1.31  tff(c_425, plain, (![A_111]: (k7_relat_1('#skF_4', A_111)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_100, c_422])).
% 2.46/1.31  tff(c_426, plain, (~r2_relset_1('#skF_1', '#skF_2', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_425, c_190])).
% 2.46/1.31  tff(c_431, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_157, c_426])).
% 2.46/1.31  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.46/1.31  
% 2.46/1.31  Inference rules
% 2.46/1.31  ----------------------
% 2.46/1.31  #Ref     : 0
% 2.46/1.31  #Sup     : 87
% 2.46/1.31  #Fact    : 0
% 2.46/1.31  #Define  : 0
% 2.46/1.31  #Split   : 4
% 2.46/1.31  #Chain   : 0
% 2.46/1.31  #Close   : 0
% 2.46/1.31  
% 2.46/1.31  Ordering : KBO
% 2.46/1.31  
% 2.46/1.31  Simplification rules
% 2.46/1.31  ----------------------
% 2.46/1.31  #Subsume      : 8
% 2.46/1.31  #Demod        : 77
% 2.46/1.31  #Tautology    : 42
% 2.46/1.31  #SimpNegUnit  : 0
% 2.46/1.31  #BackRed      : 24
% 2.46/1.31  
% 2.46/1.31  #Partial instantiations: 0
% 2.46/1.31  #Strategies tried      : 1
% 2.46/1.31  
% 2.46/1.31  Timing (in seconds)
% 2.46/1.31  ----------------------
% 2.46/1.31  Preprocessing        : 0.31
% 2.46/1.31  Parsing              : 0.16
% 2.46/1.31  CNF conversion       : 0.02
% 2.46/1.31  Main loop            : 0.25
% 2.46/1.31  Inferencing          : 0.08
% 2.46/1.31  Reduction            : 0.08
% 2.46/1.31  Demodulation         : 0.06
% 2.46/1.31  BG Simplification    : 0.02
% 2.46/1.31  Subsumption          : 0.05
% 2.46/1.31  Abstraction          : 0.01
% 2.46/1.31  MUC search           : 0.00
% 2.46/1.31  Cooper               : 0.00
% 2.46/1.31  Total                : 0.59
% 2.46/1.31  Index Insertion      : 0.00
% 2.46/1.31  Index Deletion       : 0.00
% 2.46/1.31  Index Matching       : 0.00
% 2.46/1.31  BG Taut test         : 0.00
%------------------------------------------------------------------------------
