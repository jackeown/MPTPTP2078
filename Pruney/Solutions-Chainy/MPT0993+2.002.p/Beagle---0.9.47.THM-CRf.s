%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:13:42 EST 2020

% Result     : Theorem 2.49s
% Output     : CNFRefutation 2.79s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 164 expanded)
%              Number of leaves         :   34 (  71 expanded)
%              Depth                    :   11
%              Number of atoms          :  118 ( 369 expanded)
%              Number of equality atoms :   35 (  93 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_partfun1 > k1_relset_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_108,negated_conjecture,(
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

tff(f_91,axiom,(
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

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_73,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( ( r1_tarski(k1_relat_1(C),A)
          & r1_tarski(k2_relat_1(C),B) )
       => m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_relset_1)).

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

tff(f_97,axiom,(
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
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_150,plain,(
    ! [A_54,B_55,D_56] :
      ( r2_relset_1(A_54,B_55,D_56,D_56)
      | ~ m1_subset_1(D_56,k1_zfmisc_1(k2_zfmisc_1(A_54,B_55))) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_157,plain,(
    r2_relset_1('#skF_1','#skF_2','#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_48,c_150])).

tff(c_92,plain,(
    ! [C_35,A_36,B_37] :
      ( v1_relat_1(C_35)
      | ~ m1_subset_1(C_35,k1_zfmisc_1(k2_zfmisc_1(A_36,B_37))) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_100,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_48,c_92])).

tff(c_46,plain,(
    r1_tarski('#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_50,plain,(
    v1_funct_2('#skF_4','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_160,plain,(
    ! [A_61,B_62,C_63] :
      ( k1_relset_1(A_61,B_62,C_63) = k1_relat_1(C_63)
      | ~ m1_subset_1(C_63,k1_zfmisc_1(k2_zfmisc_1(A_61,B_62))) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_170,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_48,c_160])).

tff(c_231,plain,(
    ! [B_88,A_89,C_90] :
      ( k1_xboole_0 = B_88
      | k1_relset_1(A_89,B_88,C_90) = A_89
      | ~ v1_funct_2(C_90,A_89,B_88)
      | ~ m1_subset_1(C_90,k1_zfmisc_1(k2_zfmisc_1(A_89,B_88))) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_237,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1('#skF_1','#skF_2','#skF_4') = '#skF_1'
    | ~ v1_funct_2('#skF_4','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_48,c_231])).

tff(c_247,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_170,c_237])).

tff(c_249,plain,(
    k1_relat_1('#skF_4') = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_247])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_202,plain,(
    ! [C_85,A_86,B_87] :
      ( m1_subset_1(C_85,k1_zfmisc_1(k2_zfmisc_1(A_86,B_87)))
      | ~ r1_tarski(k2_relat_1(C_85),B_87)
      | ~ r1_tarski(k1_relat_1(C_85),A_86)
      | ~ v1_relat_1(C_85) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_20,plain,(
    ! [C_12,A_10,B_11] :
      ( v4_relat_1(C_12,A_10)
      | ~ m1_subset_1(C_12,k1_zfmisc_1(k2_zfmisc_1(A_10,B_11))) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_277,plain,(
    ! [C_94,A_95,B_96] :
      ( v4_relat_1(C_94,A_95)
      | ~ r1_tarski(k2_relat_1(C_94),B_96)
      | ~ r1_tarski(k1_relat_1(C_94),A_95)
      | ~ v1_relat_1(C_94) ) ),
    inference(resolution,[status(thm)],[c_202,c_20])).

tff(c_281,plain,(
    ! [C_97,A_98] :
      ( v4_relat_1(C_97,A_98)
      | ~ r1_tarski(k1_relat_1(C_97),A_98)
      | ~ v1_relat_1(C_97) ) ),
    inference(resolution,[status(thm)],[c_6,c_277])).

tff(c_284,plain,(
    ! [A_98] :
      ( v4_relat_1('#skF_4',A_98)
      | ~ r1_tarski('#skF_1',A_98)
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_249,c_281])).

tff(c_302,plain,(
    ! [A_100] :
      ( v4_relat_1('#skF_4',A_100)
      | ~ r1_tarski('#skF_1',A_100) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_284])).

tff(c_14,plain,(
    ! [B_6,A_5] :
      ( k7_relat_1(B_6,A_5) = B_6
      | ~ v4_relat_1(B_6,A_5)
      | ~ v1_relat_1(B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_305,plain,(
    ! [A_100] :
      ( k7_relat_1('#skF_4',A_100) = '#skF_4'
      | ~ v1_relat_1('#skF_4')
      | ~ r1_tarski('#skF_1',A_100) ) ),
    inference(resolution,[status(thm)],[c_302,c_14])).

tff(c_330,plain,(
    ! [A_106] :
      ( k7_relat_1('#skF_4',A_106) = '#skF_4'
      | ~ r1_tarski('#skF_1',A_106) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_305])).

tff(c_340,plain,(
    k7_relat_1('#skF_4','#skF_3') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_46,c_330])).

tff(c_52,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_180,plain,(
    ! [A_74,B_75,C_76,D_77] :
      ( k2_partfun1(A_74,B_75,C_76,D_77) = k7_relat_1(C_76,D_77)
      | ~ m1_subset_1(C_76,k1_zfmisc_1(k2_zfmisc_1(A_74,B_75)))
      | ~ v1_funct_1(C_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_182,plain,(
    ! [D_77] :
      ( k2_partfun1('#skF_1','#skF_2','#skF_4',D_77) = k7_relat_1('#skF_4',D_77)
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_48,c_180])).

tff(c_189,plain,(
    ! [D_77] : k2_partfun1('#skF_1','#skF_2','#skF_4',D_77) = k7_relat_1('#skF_4',D_77) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_182])).

tff(c_44,plain,(
    ~ r2_relset_1('#skF_1','#skF_2',k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_190,plain,(
    ~ r2_relset_1('#skF_1','#skF_2',k7_relat_1('#skF_4','#skF_3'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_189,c_44])).

tff(c_341,plain,(
    ~ r2_relset_1('#skF_1','#skF_2','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_340,c_190])).

tff(c_344,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_157,c_341])).

tff(c_345,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_247])).

tff(c_10,plain,(
    ! [A_3] : k2_zfmisc_1(A_3,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_362,plain,(
    ! [A_3] : k2_zfmisc_1(A_3,'#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_345,c_345,c_10])).

tff(c_393,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_362,c_48])).

tff(c_125,plain,(
    ! [C_46,A_47,B_48] :
      ( v4_relat_1(C_46,A_47)
      | ~ m1_subset_1(C_46,k1_zfmisc_1(k2_zfmisc_1(A_47,B_48))) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_131,plain,(
    ! [C_46,A_3] :
      ( v4_relat_1(C_46,A_3)
      | ~ m1_subset_1(C_46,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_125])).

tff(c_446,plain,(
    ! [C_113,A_114] :
      ( v4_relat_1(C_113,A_114)
      | ~ m1_subset_1(C_113,k1_zfmisc_1('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_345,c_131])).

tff(c_451,plain,(
    ! [A_115] : v4_relat_1('#skF_4',A_115) ),
    inference(resolution,[status(thm)],[c_393,c_446])).

tff(c_454,plain,(
    ! [A_115] :
      ( k7_relat_1('#skF_4',A_115) = '#skF_4'
      | ~ v1_relat_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_451,c_14])).

tff(c_457,plain,(
    ! [A_115] : k7_relat_1('#skF_4',A_115) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_454])).

tff(c_458,plain,(
    ~ r2_relset_1('#skF_1','#skF_2','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_457,c_190])).

tff(c_463,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_157,c_458])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n007.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 18:35:21 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.49/1.37  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.79/1.38  
% 2.79/1.38  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.79/1.38  %$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_partfun1 > k1_relset_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.79/1.38  
% 2.79/1.38  %Foreground sorts:
% 2.79/1.38  
% 2.79/1.38  
% 2.79/1.38  %Background operators:
% 2.79/1.38  
% 2.79/1.38  
% 2.79/1.38  %Foreground operators:
% 2.79/1.38  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.79/1.38  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.79/1.38  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 2.79/1.38  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.79/1.38  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.79/1.38  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.79/1.38  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.79/1.38  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.79/1.38  tff('#skF_2', type, '#skF_2': $i).
% 2.79/1.38  tff('#skF_3', type, '#skF_3': $i).
% 2.79/1.38  tff('#skF_1', type, '#skF_1': $i).
% 2.79/1.38  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.79/1.38  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.79/1.38  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.79/1.38  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.79/1.38  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.79/1.38  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.79/1.38  tff('#skF_4', type, '#skF_4': $i).
% 2.79/1.38  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.79/1.38  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 2.79/1.38  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.79/1.38  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.79/1.38  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.79/1.38  
% 2.79/1.40  tff(f_108, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r1_tarski(A, C) => r2_relset_1(A, B, k2_partfun1(A, B, D, C), D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t40_funct_2)).
% 2.79/1.40  tff(f_65, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 2.79/1.40  tff(f_47, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.79/1.40  tff(f_57, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.79/1.40  tff(f_91, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 2.79/1.40  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.79/1.40  tff(f_73, axiom, (![A, B, C]: (v1_relat_1(C) => ((r1_tarski(k1_relat_1(C), A) & r1_tarski(k2_relat_1(C), B)) => m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_relset_1)).
% 2.79/1.40  tff(f_53, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.79/1.40  tff(f_43, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t209_relat_1)).
% 2.79/1.40  tff(f_97, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (k2_partfun1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_partfun1)).
% 2.79/1.40  tff(f_37, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 2.79/1.40  tff(c_48, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_108])).
% 2.79/1.40  tff(c_150, plain, (![A_54, B_55, D_56]: (r2_relset_1(A_54, B_55, D_56, D_56) | ~m1_subset_1(D_56, k1_zfmisc_1(k2_zfmisc_1(A_54, B_55))))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.79/1.40  tff(c_157, plain, (r2_relset_1('#skF_1', '#skF_2', '#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_48, c_150])).
% 2.79/1.40  tff(c_92, plain, (![C_35, A_36, B_37]: (v1_relat_1(C_35) | ~m1_subset_1(C_35, k1_zfmisc_1(k2_zfmisc_1(A_36, B_37))))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.79/1.40  tff(c_100, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_48, c_92])).
% 2.79/1.40  tff(c_46, plain, (r1_tarski('#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_108])).
% 2.79/1.40  tff(c_50, plain, (v1_funct_2('#skF_4', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_108])).
% 2.79/1.40  tff(c_160, plain, (![A_61, B_62, C_63]: (k1_relset_1(A_61, B_62, C_63)=k1_relat_1(C_63) | ~m1_subset_1(C_63, k1_zfmisc_1(k2_zfmisc_1(A_61, B_62))))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.79/1.40  tff(c_170, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_48, c_160])).
% 2.79/1.40  tff(c_231, plain, (![B_88, A_89, C_90]: (k1_xboole_0=B_88 | k1_relset_1(A_89, B_88, C_90)=A_89 | ~v1_funct_2(C_90, A_89, B_88) | ~m1_subset_1(C_90, k1_zfmisc_1(k2_zfmisc_1(A_89, B_88))))), inference(cnfTransformation, [status(thm)], [f_91])).
% 2.79/1.40  tff(c_237, plain, (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', '#skF_4')='#skF_1' | ~v1_funct_2('#skF_4', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_48, c_231])).
% 2.79/1.40  tff(c_247, plain, (k1_xboole_0='#skF_2' | k1_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_50, c_170, c_237])).
% 2.79/1.40  tff(c_249, plain, (k1_relat_1('#skF_4')='#skF_1'), inference(splitLeft, [status(thm)], [c_247])).
% 2.79/1.40  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.79/1.40  tff(c_202, plain, (![C_85, A_86, B_87]: (m1_subset_1(C_85, k1_zfmisc_1(k2_zfmisc_1(A_86, B_87))) | ~r1_tarski(k2_relat_1(C_85), B_87) | ~r1_tarski(k1_relat_1(C_85), A_86) | ~v1_relat_1(C_85))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.79/1.40  tff(c_20, plain, (![C_12, A_10, B_11]: (v4_relat_1(C_12, A_10) | ~m1_subset_1(C_12, k1_zfmisc_1(k2_zfmisc_1(A_10, B_11))))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.79/1.40  tff(c_277, plain, (![C_94, A_95, B_96]: (v4_relat_1(C_94, A_95) | ~r1_tarski(k2_relat_1(C_94), B_96) | ~r1_tarski(k1_relat_1(C_94), A_95) | ~v1_relat_1(C_94))), inference(resolution, [status(thm)], [c_202, c_20])).
% 2.79/1.40  tff(c_281, plain, (![C_97, A_98]: (v4_relat_1(C_97, A_98) | ~r1_tarski(k1_relat_1(C_97), A_98) | ~v1_relat_1(C_97))), inference(resolution, [status(thm)], [c_6, c_277])).
% 2.79/1.40  tff(c_284, plain, (![A_98]: (v4_relat_1('#skF_4', A_98) | ~r1_tarski('#skF_1', A_98) | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_249, c_281])).
% 2.79/1.40  tff(c_302, plain, (![A_100]: (v4_relat_1('#skF_4', A_100) | ~r1_tarski('#skF_1', A_100))), inference(demodulation, [status(thm), theory('equality')], [c_100, c_284])).
% 2.79/1.40  tff(c_14, plain, (![B_6, A_5]: (k7_relat_1(B_6, A_5)=B_6 | ~v4_relat_1(B_6, A_5) | ~v1_relat_1(B_6))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.79/1.40  tff(c_305, plain, (![A_100]: (k7_relat_1('#skF_4', A_100)='#skF_4' | ~v1_relat_1('#skF_4') | ~r1_tarski('#skF_1', A_100))), inference(resolution, [status(thm)], [c_302, c_14])).
% 2.79/1.40  tff(c_330, plain, (![A_106]: (k7_relat_1('#skF_4', A_106)='#skF_4' | ~r1_tarski('#skF_1', A_106))), inference(demodulation, [status(thm), theory('equality')], [c_100, c_305])).
% 2.79/1.40  tff(c_340, plain, (k7_relat_1('#skF_4', '#skF_3')='#skF_4'), inference(resolution, [status(thm)], [c_46, c_330])).
% 2.79/1.40  tff(c_52, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_108])).
% 2.79/1.40  tff(c_180, plain, (![A_74, B_75, C_76, D_77]: (k2_partfun1(A_74, B_75, C_76, D_77)=k7_relat_1(C_76, D_77) | ~m1_subset_1(C_76, k1_zfmisc_1(k2_zfmisc_1(A_74, B_75))) | ~v1_funct_1(C_76))), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.79/1.40  tff(c_182, plain, (![D_77]: (k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_77)=k7_relat_1('#skF_4', D_77) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_48, c_180])).
% 2.79/1.40  tff(c_189, plain, (![D_77]: (k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_77)=k7_relat_1('#skF_4', D_77))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_182])).
% 2.79/1.40  tff(c_44, plain, (~r2_relset_1('#skF_1', '#skF_2', k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_108])).
% 2.79/1.40  tff(c_190, plain, (~r2_relset_1('#skF_1', '#skF_2', k7_relat_1('#skF_4', '#skF_3'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_189, c_44])).
% 2.79/1.40  tff(c_341, plain, (~r2_relset_1('#skF_1', '#skF_2', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_340, c_190])).
% 2.79/1.40  tff(c_344, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_157, c_341])).
% 2.79/1.40  tff(c_345, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_247])).
% 2.79/1.40  tff(c_10, plain, (![A_3]: (k2_zfmisc_1(A_3, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.79/1.40  tff(c_362, plain, (![A_3]: (k2_zfmisc_1(A_3, '#skF_2')='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_345, c_345, c_10])).
% 2.79/1.40  tff(c_393, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_362, c_48])).
% 2.79/1.40  tff(c_125, plain, (![C_46, A_47, B_48]: (v4_relat_1(C_46, A_47) | ~m1_subset_1(C_46, k1_zfmisc_1(k2_zfmisc_1(A_47, B_48))))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.79/1.40  tff(c_131, plain, (![C_46, A_3]: (v4_relat_1(C_46, A_3) | ~m1_subset_1(C_46, k1_zfmisc_1(k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_125])).
% 2.79/1.40  tff(c_446, plain, (![C_113, A_114]: (v4_relat_1(C_113, A_114) | ~m1_subset_1(C_113, k1_zfmisc_1('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_345, c_131])).
% 2.79/1.40  tff(c_451, plain, (![A_115]: (v4_relat_1('#skF_4', A_115))), inference(resolution, [status(thm)], [c_393, c_446])).
% 2.79/1.40  tff(c_454, plain, (![A_115]: (k7_relat_1('#skF_4', A_115)='#skF_4' | ~v1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_451, c_14])).
% 2.79/1.40  tff(c_457, plain, (![A_115]: (k7_relat_1('#skF_4', A_115)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_100, c_454])).
% 2.79/1.40  tff(c_458, plain, (~r2_relset_1('#skF_1', '#skF_2', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_457, c_190])).
% 2.79/1.40  tff(c_463, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_157, c_458])).
% 2.79/1.40  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.79/1.40  
% 2.79/1.40  Inference rules
% 2.79/1.40  ----------------------
% 2.79/1.40  #Ref     : 0
% 2.79/1.40  #Sup     : 95
% 2.79/1.40  #Fact    : 0
% 2.79/1.40  #Define  : 0
% 2.79/1.40  #Split   : 3
% 2.79/1.40  #Chain   : 0
% 2.79/1.40  #Close   : 0
% 2.79/1.40  
% 2.79/1.40  Ordering : KBO
% 2.79/1.40  
% 2.79/1.40  Simplification rules
% 2.79/1.40  ----------------------
% 2.79/1.40  #Subsume      : 8
% 2.79/1.40  #Demod        : 70
% 2.79/1.40  #Tautology    : 42
% 2.79/1.40  #SimpNegUnit  : 0
% 2.79/1.40  #BackRed      : 23
% 2.79/1.40  
% 2.79/1.40  #Partial instantiations: 0
% 2.79/1.40  #Strategies tried      : 1
% 2.79/1.40  
% 2.79/1.40  Timing (in seconds)
% 2.79/1.40  ----------------------
% 2.79/1.40  Preprocessing        : 0.33
% 2.79/1.40  Parsing              : 0.17
% 2.79/1.40  CNF conversion       : 0.02
% 2.79/1.40  Main loop            : 0.29
% 2.79/1.40  Inferencing          : 0.10
% 2.79/1.40  Reduction            : 0.09
% 2.79/1.40  Demodulation         : 0.06
% 2.79/1.40  BG Simplification    : 0.02
% 2.79/1.40  Subsumption          : 0.06
% 2.79/1.40  Abstraction          : 0.02
% 2.79/1.40  MUC search           : 0.00
% 2.79/1.40  Cooper               : 0.00
% 2.79/1.40  Total                : 0.66
% 2.79/1.40  Index Insertion      : 0.00
% 2.79/1.40  Index Deletion       : 0.00
% 2.79/1.40  Index Matching       : 0.00
% 2.79/1.40  BG Taut test         : 0.00
%------------------------------------------------------------------------------
