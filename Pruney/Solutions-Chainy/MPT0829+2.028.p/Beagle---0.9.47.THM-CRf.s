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
% DateTime   : Thu Dec  3 10:07:25 EST 2020

% Result     : Theorem 2.15s
% Output     : CNFRefutation 2.51s
% Verified   : 
% Statistics : Number of formulae       :   72 ( 131 expanded)
%              Number of leaves         :   31 (  57 expanded)
%              Depth                    :    9
%              Number of atoms          :   99 ( 233 expanded)
%              Number of equality atoms :   24 (  67 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

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

tff(f_87,negated_conjecture,(
    ~ ! [A,B,C] :
        ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
       => ( r1_tarski(k6_relat_1(B),C)
         => ( r1_tarski(B,k1_relset_1(A,B,C))
            & B = k2_relset_1(A,B,C) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_relset_1)).

tff(f_70,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_78,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( r1_tarski(k6_relat_1(C),D)
       => ( r1_tarski(C,k1_relset_1(A,B,D))
          & r1_tarski(C,k2_relset_1(A,B,D)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_relset_1)).

tff(f_44,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_40,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_32,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_66,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_60,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v1_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k1_relat_1(B),A)
       => k5_relat_1(k6_relat_1(A),B) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_relat_1)).

tff(f_56,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k2_relat_1(B),A)
       => k5_relat_1(B,k6_relat_1(A)) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_relat_1)).

tff(c_36,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_352,plain,(
    ! [A_99,B_100,C_101] :
      ( k2_relset_1(A_99,B_100,C_101) = k2_relat_1(C_101)
      | ~ m1_subset_1(C_101,k1_zfmisc_1(k2_zfmisc_1(A_99,B_100))) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_356,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_36,c_352])).

tff(c_32,plain,
    ( k2_relset_1('#skF_1','#skF_2','#skF_3') != '#skF_2'
    | ~ r1_tarski('#skF_2',k1_relset_1('#skF_1','#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_65,plain,(
    ~ r1_tarski('#skF_2',k1_relset_1('#skF_1','#skF_2','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_32])).

tff(c_34,plain,(
    r1_tarski(k6_relat_1('#skF_2'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_206,plain,(
    ! [C_69,A_70,B_71,D_72] :
      ( r1_tarski(C_69,k1_relset_1(A_70,B_71,D_72))
      | ~ r1_tarski(k6_relat_1(C_69),D_72)
      | ~ m1_subset_1(D_72,k1_zfmisc_1(k2_zfmisc_1(A_70,B_71))) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_237,plain,(
    ! [A_73,B_74] :
      ( r1_tarski('#skF_2',k1_relset_1(A_73,B_74,'#skF_3'))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(A_73,B_74))) ) ),
    inference(resolution,[status(thm)],[c_34,c_206])).

tff(c_240,plain,(
    r1_tarski('#skF_2',k1_relset_1('#skF_1','#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_36,c_237])).

tff(c_244,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_65,c_240])).

tff(c_245,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') != '#skF_2' ),
    inference(splitRight,[status(thm)],[c_32])).

tff(c_357,plain,(
    k2_relat_1('#skF_3') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_356,c_245])).

tff(c_10,plain,(
    ! [A_8] : k1_relat_1(k6_relat_1(A_8)) = A_8 ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_8,plain,(
    ! [A_6,B_7] : v1_relat_1(k2_zfmisc_1(A_6,B_7)) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_58,plain,(
    ! [B_30,A_31] :
      ( v1_relat_1(B_30)
      | ~ m1_subset_1(B_30,k1_zfmisc_1(A_31))
      | ~ v1_relat_1(A_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_61,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_36,c_58])).

tff(c_64,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_61])).

tff(c_264,plain,(
    ! [C_81,B_82,A_83] :
      ( v5_relat_1(C_81,B_82)
      | ~ m1_subset_1(C_81,k1_zfmisc_1(k2_zfmisc_1(A_83,B_82))) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_268,plain,(
    v5_relat_1('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_36,c_264])).

tff(c_6,plain,(
    ! [B_5,A_4] :
      ( r1_tarski(k2_relat_1(B_5),A_4)
      | ~ v5_relat_1(B_5,A_4)
      | ~ v1_relat_1(B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_379,plain,(
    ! [C_106,A_107,B_108,D_109] :
      ( r1_tarski(C_106,k2_relset_1(A_107,B_108,D_109))
      | ~ r1_tarski(k6_relat_1(C_106),D_109)
      | ~ m1_subset_1(D_109,k1_zfmisc_1(k2_zfmisc_1(A_107,B_108))) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_383,plain,(
    ! [A_110,B_111] :
      ( r1_tarski('#skF_2',k2_relset_1(A_110,B_111,'#skF_3'))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(A_110,B_111))) ) ),
    inference(resolution,[status(thm)],[c_34,c_379])).

tff(c_386,plain,(
    r1_tarski('#skF_2',k2_relset_1('#skF_1','#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_36,c_383])).

tff(c_388,plain,(
    r1_tarski('#skF_2',k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_356,c_386])).

tff(c_18,plain,(
    ! [A_13] : v1_relat_1(k6_relat_1(A_13)) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_320,plain,(
    ! [A_95,B_96] :
      ( k5_relat_1(k6_relat_1(A_95),B_96) = B_96
      | ~ r1_tarski(k1_relat_1(B_96),A_95)
      | ~ v1_relat_1(B_96) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_323,plain,(
    ! [A_95,A_8] :
      ( k5_relat_1(k6_relat_1(A_95),k6_relat_1(A_8)) = k6_relat_1(A_8)
      | ~ r1_tarski(A_8,A_95)
      | ~ v1_relat_1(k6_relat_1(A_8)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_320])).

tff(c_326,plain,(
    ! [A_97,A_98] :
      ( k5_relat_1(k6_relat_1(A_97),k6_relat_1(A_98)) = k6_relat_1(A_98)
      | ~ r1_tarski(A_98,A_97) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_323])).

tff(c_12,plain,(
    ! [A_8] : k2_relat_1(k6_relat_1(A_8)) = A_8 ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_279,plain,(
    ! [B_89,A_90] :
      ( k5_relat_1(B_89,k6_relat_1(A_90)) = B_89
      | ~ r1_tarski(k2_relat_1(B_89),A_90)
      | ~ v1_relat_1(B_89) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_285,plain,(
    ! [A_8,A_90] :
      ( k5_relat_1(k6_relat_1(A_8),k6_relat_1(A_90)) = k6_relat_1(A_8)
      | ~ r1_tarski(A_8,A_90)
      | ~ v1_relat_1(k6_relat_1(A_8)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_279])).

tff(c_288,plain,(
    ! [A_8,A_90] :
      ( k5_relat_1(k6_relat_1(A_8),k6_relat_1(A_90)) = k6_relat_1(A_8)
      | ~ r1_tarski(A_8,A_90) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_285])).

tff(c_332,plain,(
    ! [A_98,A_97] :
      ( k6_relat_1(A_98) = k6_relat_1(A_97)
      | ~ r1_tarski(A_97,A_98)
      | ~ r1_tarski(A_98,A_97) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_326,c_288])).

tff(c_391,plain,
    ( k6_relat_1(k2_relat_1('#skF_3')) = k6_relat_1('#skF_2')
    | ~ r1_tarski(k2_relat_1('#skF_3'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_388,c_332])).

tff(c_392,plain,(
    ~ r1_tarski(k2_relat_1('#skF_3'),'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_391])).

tff(c_395,plain,
    ( ~ v5_relat_1('#skF_3','#skF_2')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_6,c_392])).

tff(c_399,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_268,c_395])).

tff(c_400,plain,(
    k6_relat_1(k2_relat_1('#skF_3')) = k6_relat_1('#skF_2') ),
    inference(splitRight,[status(thm)],[c_391])).

tff(c_448,plain,(
    k1_relat_1(k6_relat_1('#skF_2')) = k2_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_400,c_10])).

tff(c_461,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_448])).

tff(c_463,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_357,c_461])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 12:35:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.15/1.33  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.51/1.33  
% 2.51/1.33  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.51/1.33  %$ v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 2.51/1.33  
% 2.51/1.33  %Foreground sorts:
% 2.51/1.33  
% 2.51/1.33  
% 2.51/1.33  %Background operators:
% 2.51/1.33  
% 2.51/1.33  
% 2.51/1.33  %Foreground operators:
% 2.51/1.33  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 2.51/1.33  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.51/1.33  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.51/1.33  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.51/1.33  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.51/1.33  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.51/1.33  tff('#skF_2', type, '#skF_2': $i).
% 2.51/1.33  tff('#skF_3', type, '#skF_3': $i).
% 2.51/1.33  tff('#skF_1', type, '#skF_1': $i).
% 2.51/1.33  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.51/1.33  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.51/1.33  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.51/1.33  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.51/1.33  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.51/1.33  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.51/1.33  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 2.51/1.33  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.51/1.33  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.51/1.33  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.51/1.33  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.51/1.33  
% 2.51/1.35  tff(f_87, negated_conjecture, ~(![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (r1_tarski(k6_relat_1(B), C) => (r1_tarski(B, k1_relset_1(A, B, C)) & (B = k2_relset_1(A, B, C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t32_relset_1)).
% 2.51/1.35  tff(f_70, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 2.51/1.35  tff(f_78, axiom, (![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (r1_tarski(k6_relat_1(C), D) => (r1_tarski(C, k1_relset_1(A, B, D)) & r1_tarski(C, k2_relset_1(A, B, D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t30_relset_1)).
% 2.51/1.35  tff(f_44, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 2.51/1.35  tff(f_40, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 2.51/1.35  tff(f_32, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 2.51/1.35  tff(f_66, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.51/1.35  tff(f_38, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 2.51/1.35  tff(f_60, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v1_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc3_funct_1)).
% 2.51/1.35  tff(f_50, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(B), A) => (k5_relat_1(k6_relat_1(A), B) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t77_relat_1)).
% 2.51/1.35  tff(f_56, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(B), A) => (k5_relat_1(B, k6_relat_1(A)) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_relat_1)).
% 2.51/1.35  tff(c_36, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.51/1.35  tff(c_352, plain, (![A_99, B_100, C_101]: (k2_relset_1(A_99, B_100, C_101)=k2_relat_1(C_101) | ~m1_subset_1(C_101, k1_zfmisc_1(k2_zfmisc_1(A_99, B_100))))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.51/1.35  tff(c_356, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_36, c_352])).
% 2.51/1.35  tff(c_32, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')!='#skF_2' | ~r1_tarski('#skF_2', k1_relset_1('#skF_1', '#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.51/1.35  tff(c_65, plain, (~r1_tarski('#skF_2', k1_relset_1('#skF_1', '#skF_2', '#skF_3'))), inference(splitLeft, [status(thm)], [c_32])).
% 2.51/1.35  tff(c_34, plain, (r1_tarski(k6_relat_1('#skF_2'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.51/1.35  tff(c_206, plain, (![C_69, A_70, B_71, D_72]: (r1_tarski(C_69, k1_relset_1(A_70, B_71, D_72)) | ~r1_tarski(k6_relat_1(C_69), D_72) | ~m1_subset_1(D_72, k1_zfmisc_1(k2_zfmisc_1(A_70, B_71))))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.51/1.35  tff(c_237, plain, (![A_73, B_74]: (r1_tarski('#skF_2', k1_relset_1(A_73, B_74, '#skF_3')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(A_73, B_74))))), inference(resolution, [status(thm)], [c_34, c_206])).
% 2.51/1.35  tff(c_240, plain, (r1_tarski('#skF_2', k1_relset_1('#skF_1', '#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_36, c_237])).
% 2.51/1.35  tff(c_244, plain, $false, inference(negUnitSimplification, [status(thm)], [c_65, c_240])).
% 2.51/1.35  tff(c_245, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')!='#skF_2'), inference(splitRight, [status(thm)], [c_32])).
% 2.51/1.35  tff(c_357, plain, (k2_relat_1('#skF_3')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_356, c_245])).
% 2.51/1.35  tff(c_10, plain, (![A_8]: (k1_relat_1(k6_relat_1(A_8))=A_8)), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.51/1.35  tff(c_8, plain, (![A_6, B_7]: (v1_relat_1(k2_zfmisc_1(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.51/1.35  tff(c_58, plain, (![B_30, A_31]: (v1_relat_1(B_30) | ~m1_subset_1(B_30, k1_zfmisc_1(A_31)) | ~v1_relat_1(A_31))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.51/1.35  tff(c_61, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_36, c_58])).
% 2.51/1.35  tff(c_64, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_8, c_61])).
% 2.51/1.35  tff(c_264, plain, (![C_81, B_82, A_83]: (v5_relat_1(C_81, B_82) | ~m1_subset_1(C_81, k1_zfmisc_1(k2_zfmisc_1(A_83, B_82))))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.51/1.35  tff(c_268, plain, (v5_relat_1('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_36, c_264])).
% 2.51/1.35  tff(c_6, plain, (![B_5, A_4]: (r1_tarski(k2_relat_1(B_5), A_4) | ~v5_relat_1(B_5, A_4) | ~v1_relat_1(B_5))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.51/1.35  tff(c_379, plain, (![C_106, A_107, B_108, D_109]: (r1_tarski(C_106, k2_relset_1(A_107, B_108, D_109)) | ~r1_tarski(k6_relat_1(C_106), D_109) | ~m1_subset_1(D_109, k1_zfmisc_1(k2_zfmisc_1(A_107, B_108))))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.51/1.35  tff(c_383, plain, (![A_110, B_111]: (r1_tarski('#skF_2', k2_relset_1(A_110, B_111, '#skF_3')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(A_110, B_111))))), inference(resolution, [status(thm)], [c_34, c_379])).
% 2.51/1.35  tff(c_386, plain, (r1_tarski('#skF_2', k2_relset_1('#skF_1', '#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_36, c_383])).
% 2.51/1.35  tff(c_388, plain, (r1_tarski('#skF_2', k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_356, c_386])).
% 2.51/1.35  tff(c_18, plain, (![A_13]: (v1_relat_1(k6_relat_1(A_13)))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.51/1.35  tff(c_320, plain, (![A_95, B_96]: (k5_relat_1(k6_relat_1(A_95), B_96)=B_96 | ~r1_tarski(k1_relat_1(B_96), A_95) | ~v1_relat_1(B_96))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.51/1.35  tff(c_323, plain, (![A_95, A_8]: (k5_relat_1(k6_relat_1(A_95), k6_relat_1(A_8))=k6_relat_1(A_8) | ~r1_tarski(A_8, A_95) | ~v1_relat_1(k6_relat_1(A_8)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_320])).
% 2.51/1.35  tff(c_326, plain, (![A_97, A_98]: (k5_relat_1(k6_relat_1(A_97), k6_relat_1(A_98))=k6_relat_1(A_98) | ~r1_tarski(A_98, A_97))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_323])).
% 2.51/1.35  tff(c_12, plain, (![A_8]: (k2_relat_1(k6_relat_1(A_8))=A_8)), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.51/1.35  tff(c_279, plain, (![B_89, A_90]: (k5_relat_1(B_89, k6_relat_1(A_90))=B_89 | ~r1_tarski(k2_relat_1(B_89), A_90) | ~v1_relat_1(B_89))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.51/1.35  tff(c_285, plain, (![A_8, A_90]: (k5_relat_1(k6_relat_1(A_8), k6_relat_1(A_90))=k6_relat_1(A_8) | ~r1_tarski(A_8, A_90) | ~v1_relat_1(k6_relat_1(A_8)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_279])).
% 2.51/1.35  tff(c_288, plain, (![A_8, A_90]: (k5_relat_1(k6_relat_1(A_8), k6_relat_1(A_90))=k6_relat_1(A_8) | ~r1_tarski(A_8, A_90))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_285])).
% 2.51/1.35  tff(c_332, plain, (![A_98, A_97]: (k6_relat_1(A_98)=k6_relat_1(A_97) | ~r1_tarski(A_97, A_98) | ~r1_tarski(A_98, A_97))), inference(superposition, [status(thm), theory('equality')], [c_326, c_288])).
% 2.51/1.35  tff(c_391, plain, (k6_relat_1(k2_relat_1('#skF_3'))=k6_relat_1('#skF_2') | ~r1_tarski(k2_relat_1('#skF_3'), '#skF_2')), inference(resolution, [status(thm)], [c_388, c_332])).
% 2.51/1.35  tff(c_392, plain, (~r1_tarski(k2_relat_1('#skF_3'), '#skF_2')), inference(splitLeft, [status(thm)], [c_391])).
% 2.51/1.35  tff(c_395, plain, (~v5_relat_1('#skF_3', '#skF_2') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_6, c_392])).
% 2.51/1.35  tff(c_399, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_64, c_268, c_395])).
% 2.51/1.35  tff(c_400, plain, (k6_relat_1(k2_relat_1('#skF_3'))=k6_relat_1('#skF_2')), inference(splitRight, [status(thm)], [c_391])).
% 2.51/1.35  tff(c_448, plain, (k1_relat_1(k6_relat_1('#skF_2'))=k2_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_400, c_10])).
% 2.51/1.35  tff(c_461, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_10, c_448])).
% 2.51/1.35  tff(c_463, plain, $false, inference(negUnitSimplification, [status(thm)], [c_357, c_461])).
% 2.51/1.35  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.51/1.35  
% 2.51/1.35  Inference rules
% 2.51/1.35  ----------------------
% 2.51/1.35  #Ref     : 0
% 2.51/1.35  #Sup     : 91
% 2.51/1.35  #Fact    : 0
% 2.51/1.35  #Define  : 0
% 2.51/1.35  #Split   : 6
% 2.51/1.35  #Chain   : 0
% 2.51/1.35  #Close   : 0
% 2.51/1.35  
% 2.51/1.35  Ordering : KBO
% 2.51/1.35  
% 2.51/1.35  Simplification rules
% 2.51/1.35  ----------------------
% 2.51/1.35  #Subsume      : 6
% 2.51/1.35  #Demod        : 36
% 2.51/1.35  #Tautology    : 31
% 2.51/1.35  #SimpNegUnit  : 2
% 2.51/1.35  #BackRed      : 1
% 2.51/1.35  
% 2.51/1.35  #Partial instantiations: 0
% 2.51/1.35  #Strategies tried      : 1
% 2.51/1.35  
% 2.51/1.35  Timing (in seconds)
% 2.51/1.35  ----------------------
% 2.51/1.35  Preprocessing        : 0.29
% 2.51/1.35  Parsing              : 0.15
% 2.51/1.35  CNF conversion       : 0.02
% 2.51/1.35  Main loop            : 0.26
% 2.51/1.35  Inferencing          : 0.10
% 2.51/1.35  Reduction            : 0.08
% 2.51/1.35  Demodulation         : 0.05
% 2.51/1.35  BG Simplification    : 0.01
% 2.51/1.35  Subsumption          : 0.04
% 2.51/1.35  Abstraction          : 0.02
% 2.51/1.35  MUC search           : 0.00
% 2.51/1.35  Cooper               : 0.00
% 2.51/1.35  Total                : 0.58
% 2.51/1.35  Index Insertion      : 0.00
% 2.51/1.35  Index Deletion       : 0.00
% 2.51/1.35  Index Matching       : 0.00
% 2.51/1.35  BG Taut test         : 0.00
%------------------------------------------------------------------------------
