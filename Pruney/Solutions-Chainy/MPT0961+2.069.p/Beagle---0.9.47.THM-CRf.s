%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:10:51 EST 2020

% Result     : Theorem 2.48s
% Output     : CNFRefutation 2.48s
% Verified   : 
% Statistics : Number of formulae       :   67 ( 171 expanded)
%              Number of leaves         :   24 (  65 expanded)
%              Depth                    :    8
%              Number of atoms          :  100 ( 383 expanded)
%              Number of equality atoms :   42 ( 147 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

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

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_85,negated_conjecture,(
    ~ ! [A] :
        ( ( v1_relat_1(A)
          & v1_funct_1(A) )
       => ( v1_funct_1(A)
          & v1_funct_2(A,k1_relat_1(A),k2_relat_1(A))
          & m1_subset_1(A,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A)))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_funct_2)).

tff(f_41,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => r1_tarski(A,k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_relat_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_56,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_52,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ( k1_relat_1(A) = k1_xboole_0
          | k2_relat_1(A) = k1_xboole_0 )
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).

tff(f_74,axiom,(
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

tff(f_44,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_27,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(c_38,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_517,plain,(
    ! [A_107] :
      ( r1_tarski(A_107,k2_zfmisc_1(k1_relat_1(A_107),k2_relat_1(A_107)))
      | ~ v1_relat_1(A_107) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_6,plain,(
    ! [A_2,B_3] :
      ( m1_subset_1(A_2,k1_zfmisc_1(B_3))
      | ~ r1_tarski(A_2,B_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_10,plain,(
    ! [A_7] :
      ( r1_tarski(A_7,k2_zfmisc_1(k1_relat_1(A_7),k2_relat_1(A_7)))
      | ~ v1_relat_1(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_93,plain,(
    ! [A_28,B_29,C_30] :
      ( k1_relset_1(A_28,B_29,C_30) = k1_relat_1(C_30)
      | ~ m1_subset_1(C_30,k1_zfmisc_1(k2_zfmisc_1(A_28,B_29))) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_114,plain,(
    ! [A_38,B_39,A_40] :
      ( k1_relset_1(A_38,B_39,A_40) = k1_relat_1(A_40)
      | ~ r1_tarski(A_40,k2_zfmisc_1(A_38,B_39)) ) ),
    inference(resolution,[status(thm)],[c_6,c_93])).

tff(c_122,plain,(
    ! [A_7] :
      ( k1_relset_1(k1_relat_1(A_7),k2_relat_1(A_7),A_7) = k1_relat_1(A_7)
      | ~ v1_relat_1(A_7) ) ),
    inference(resolution,[status(thm)],[c_10,c_114])).

tff(c_65,plain,(
    ! [A_22] :
      ( k2_relat_1(A_22) != k1_xboole_0
      | k1_xboole_0 = A_22
      | ~ v1_relat_1(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_69,plain,
    ( k2_relat_1('#skF_1') != k1_xboole_0
    | k1_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_38,c_65])).

tff(c_70,plain,(
    k2_relat_1('#skF_1') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_69])).

tff(c_212,plain,(
    ! [B_55,C_56,A_57] :
      ( k1_xboole_0 = B_55
      | v1_funct_2(C_56,A_57,B_55)
      | k1_relset_1(A_57,B_55,C_56) != A_57
      | ~ m1_subset_1(C_56,k1_zfmisc_1(k2_zfmisc_1(A_57,B_55))) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_226,plain,(
    ! [B_60,A_61,A_62] :
      ( k1_xboole_0 = B_60
      | v1_funct_2(A_61,A_62,B_60)
      | k1_relset_1(A_62,B_60,A_61) != A_62
      | ~ r1_tarski(A_61,k2_zfmisc_1(A_62,B_60)) ) ),
    inference(resolution,[status(thm)],[c_6,c_212])).

tff(c_275,plain,(
    ! [A_71] :
      ( k2_relat_1(A_71) = k1_xboole_0
      | v1_funct_2(A_71,k1_relat_1(A_71),k2_relat_1(A_71))
      | k1_relset_1(k1_relat_1(A_71),k2_relat_1(A_71),A_71) != k1_relat_1(A_71)
      | ~ v1_relat_1(A_71) ) ),
    inference(resolution,[status(thm)],[c_10,c_226])).

tff(c_36,plain,(
    v1_funct_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_34,plain,
    ( ~ m1_subset_1('#skF_1',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_1'),k2_relat_1('#skF_1'))))
    | ~ v1_funct_2('#skF_1',k1_relat_1('#skF_1'),k2_relat_1('#skF_1'))
    | ~ v1_funct_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_40,plain,
    ( ~ m1_subset_1('#skF_1',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_1'),k2_relat_1('#skF_1'))))
    | ~ v1_funct_2('#skF_1',k1_relat_1('#skF_1'),k2_relat_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34])).

tff(c_64,plain,(
    ~ v1_funct_2('#skF_1',k1_relat_1('#skF_1'),k2_relat_1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_40])).

tff(c_282,plain,
    ( k2_relat_1('#skF_1') = k1_xboole_0
    | k1_relset_1(k1_relat_1('#skF_1'),k2_relat_1('#skF_1'),'#skF_1') != k1_relat_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_275,c_64])).

tff(c_294,plain,
    ( k2_relat_1('#skF_1') = k1_xboole_0
    | k1_relset_1(k1_relat_1('#skF_1'),k2_relat_1('#skF_1'),'#skF_1') != k1_relat_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_282])).

tff(c_295,plain,(
    k1_relset_1(k1_relat_1('#skF_1'),k2_relat_1('#skF_1'),'#skF_1') != k1_relat_1('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_294])).

tff(c_302,plain,(
    ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_122,c_295])).

tff(c_306,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_302])).

tff(c_307,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_69])).

tff(c_14,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_314,plain,(
    k1_relat_1('#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_307,c_307,c_14])).

tff(c_2,plain,(
    ! [A_1] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_1)) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_312,plain,(
    ! [A_1] : m1_subset_1('#skF_1',k1_zfmisc_1(A_1)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_307,c_2])).

tff(c_381,plain,(
    ! [A_86,B_87,C_88] :
      ( k1_relset_1(A_86,B_87,C_88) = k1_relat_1(C_88)
      | ~ m1_subset_1(C_88,k1_zfmisc_1(k2_zfmisc_1(A_86,B_87))) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_385,plain,(
    ! [A_86,B_87] : k1_relset_1(A_86,B_87,'#skF_1') = k1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_312,c_381])).

tff(c_391,plain,(
    ! [A_86,B_87] : k1_relset_1(A_86,B_87,'#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_314,c_385])).

tff(c_26,plain,(
    ! [C_14,B_13] :
      ( v1_funct_2(C_14,k1_xboole_0,B_13)
      | k1_relset_1(k1_xboole_0,B_13,C_14) != k1_xboole_0
      | ~ m1_subset_1(C_14,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_13))) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_483,plain,(
    ! [C_103,B_104] :
      ( v1_funct_2(C_103,'#skF_1',B_104)
      | k1_relset_1('#skF_1',B_104,C_103) != '#skF_1'
      | ~ m1_subset_1(C_103,k1_zfmisc_1(k2_zfmisc_1('#skF_1',B_104))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_307,c_307,c_307,c_307,c_26])).

tff(c_487,plain,(
    ! [B_104] :
      ( v1_funct_2('#skF_1','#skF_1',B_104)
      | k1_relset_1('#skF_1',B_104,'#skF_1') != '#skF_1' ) ),
    inference(resolution,[status(thm)],[c_312,c_483])).

tff(c_494,plain,(
    ! [B_104] : v1_funct_2('#skF_1','#skF_1',B_104) ),
    inference(demodulation,[status(thm),theory(equality)],[c_391,c_487])).

tff(c_308,plain,(
    k2_relat_1('#skF_1') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_69])).

tff(c_319,plain,(
    k2_relat_1('#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_307,c_308])).

tff(c_320,plain,(
    ~ v1_funct_2('#skF_1',k1_relat_1('#skF_1'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_319,c_64])).

tff(c_346,plain,(
    ~ v1_funct_2('#skF_1','#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_314,c_320])).

tff(c_498,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_494,c_346])).

tff(c_499,plain,(
    ~ m1_subset_1('#skF_1',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_1'),k2_relat_1('#skF_1')))) ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_516,plain,(
    ~ r1_tarski('#skF_1',k2_zfmisc_1(k1_relat_1('#skF_1'),k2_relat_1('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_6,c_499])).

tff(c_520,plain,(
    ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_517,c_516])).

tff(c_530,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_520])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n018.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 19:17:12 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.48/1.44  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.48/1.44  
% 2.48/1.44  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.48/1.44  %$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1
% 2.48/1.44  
% 2.48/1.44  %Foreground sorts:
% 2.48/1.44  
% 2.48/1.44  
% 2.48/1.44  %Background operators:
% 2.48/1.44  
% 2.48/1.44  
% 2.48/1.44  %Foreground operators:
% 2.48/1.44  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.48/1.44  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.48/1.44  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.48/1.44  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.48/1.44  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.48/1.44  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.48/1.44  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.48/1.44  tff('#skF_1', type, '#skF_1': $i).
% 2.48/1.44  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.48/1.44  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.48/1.44  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.48/1.44  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.48/1.44  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.48/1.44  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.48/1.44  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.48/1.44  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.48/1.44  
% 2.48/1.46  tff(f_85, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => ((v1_funct_1(A) & v1_funct_2(A, k1_relat_1(A), k2_relat_1(A))) & m1_subset_1(A, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_funct_2)).
% 2.48/1.46  tff(f_41, axiom, (![A]: (v1_relat_1(A) => r1_tarski(A, k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t21_relat_1)).
% 2.48/1.46  tff(f_31, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 2.48/1.46  tff(f_56, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.48/1.46  tff(f_52, axiom, (![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_relat_1)).
% 2.48/1.46  tff(f_74, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 2.48/1.46  tff(f_44, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 2.48/1.46  tff(f_27, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 2.48/1.46  tff(c_38, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.48/1.46  tff(c_517, plain, (![A_107]: (r1_tarski(A_107, k2_zfmisc_1(k1_relat_1(A_107), k2_relat_1(A_107))) | ~v1_relat_1(A_107))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.48/1.46  tff(c_6, plain, (![A_2, B_3]: (m1_subset_1(A_2, k1_zfmisc_1(B_3)) | ~r1_tarski(A_2, B_3))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.48/1.46  tff(c_10, plain, (![A_7]: (r1_tarski(A_7, k2_zfmisc_1(k1_relat_1(A_7), k2_relat_1(A_7))) | ~v1_relat_1(A_7))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.48/1.46  tff(c_93, plain, (![A_28, B_29, C_30]: (k1_relset_1(A_28, B_29, C_30)=k1_relat_1(C_30) | ~m1_subset_1(C_30, k1_zfmisc_1(k2_zfmisc_1(A_28, B_29))))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.48/1.46  tff(c_114, plain, (![A_38, B_39, A_40]: (k1_relset_1(A_38, B_39, A_40)=k1_relat_1(A_40) | ~r1_tarski(A_40, k2_zfmisc_1(A_38, B_39)))), inference(resolution, [status(thm)], [c_6, c_93])).
% 2.48/1.46  tff(c_122, plain, (![A_7]: (k1_relset_1(k1_relat_1(A_7), k2_relat_1(A_7), A_7)=k1_relat_1(A_7) | ~v1_relat_1(A_7))), inference(resolution, [status(thm)], [c_10, c_114])).
% 2.48/1.46  tff(c_65, plain, (![A_22]: (k2_relat_1(A_22)!=k1_xboole_0 | k1_xboole_0=A_22 | ~v1_relat_1(A_22))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.48/1.46  tff(c_69, plain, (k2_relat_1('#skF_1')!=k1_xboole_0 | k1_xboole_0='#skF_1'), inference(resolution, [status(thm)], [c_38, c_65])).
% 2.48/1.46  tff(c_70, plain, (k2_relat_1('#skF_1')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_69])).
% 2.48/1.46  tff(c_212, plain, (![B_55, C_56, A_57]: (k1_xboole_0=B_55 | v1_funct_2(C_56, A_57, B_55) | k1_relset_1(A_57, B_55, C_56)!=A_57 | ~m1_subset_1(C_56, k1_zfmisc_1(k2_zfmisc_1(A_57, B_55))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.48/1.46  tff(c_226, plain, (![B_60, A_61, A_62]: (k1_xboole_0=B_60 | v1_funct_2(A_61, A_62, B_60) | k1_relset_1(A_62, B_60, A_61)!=A_62 | ~r1_tarski(A_61, k2_zfmisc_1(A_62, B_60)))), inference(resolution, [status(thm)], [c_6, c_212])).
% 2.48/1.46  tff(c_275, plain, (![A_71]: (k2_relat_1(A_71)=k1_xboole_0 | v1_funct_2(A_71, k1_relat_1(A_71), k2_relat_1(A_71)) | k1_relset_1(k1_relat_1(A_71), k2_relat_1(A_71), A_71)!=k1_relat_1(A_71) | ~v1_relat_1(A_71))), inference(resolution, [status(thm)], [c_10, c_226])).
% 2.48/1.46  tff(c_36, plain, (v1_funct_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.48/1.46  tff(c_34, plain, (~m1_subset_1('#skF_1', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_1'), k2_relat_1('#skF_1')))) | ~v1_funct_2('#skF_1', k1_relat_1('#skF_1'), k2_relat_1('#skF_1')) | ~v1_funct_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.48/1.46  tff(c_40, plain, (~m1_subset_1('#skF_1', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_1'), k2_relat_1('#skF_1')))) | ~v1_funct_2('#skF_1', k1_relat_1('#skF_1'), k2_relat_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34])).
% 2.48/1.46  tff(c_64, plain, (~v1_funct_2('#skF_1', k1_relat_1('#skF_1'), k2_relat_1('#skF_1'))), inference(splitLeft, [status(thm)], [c_40])).
% 2.48/1.46  tff(c_282, plain, (k2_relat_1('#skF_1')=k1_xboole_0 | k1_relset_1(k1_relat_1('#skF_1'), k2_relat_1('#skF_1'), '#skF_1')!=k1_relat_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_275, c_64])).
% 2.48/1.46  tff(c_294, plain, (k2_relat_1('#skF_1')=k1_xboole_0 | k1_relset_1(k1_relat_1('#skF_1'), k2_relat_1('#skF_1'), '#skF_1')!=k1_relat_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_282])).
% 2.48/1.46  tff(c_295, plain, (k1_relset_1(k1_relat_1('#skF_1'), k2_relat_1('#skF_1'), '#skF_1')!=k1_relat_1('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_70, c_294])).
% 2.48/1.46  tff(c_302, plain, (~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_122, c_295])).
% 2.48/1.46  tff(c_306, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_38, c_302])).
% 2.48/1.46  tff(c_307, plain, (k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_69])).
% 2.48/1.46  tff(c_14, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.48/1.46  tff(c_314, plain, (k1_relat_1('#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_307, c_307, c_14])).
% 2.48/1.46  tff(c_2, plain, (![A_1]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_1)))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.48/1.46  tff(c_312, plain, (![A_1]: (m1_subset_1('#skF_1', k1_zfmisc_1(A_1)))), inference(demodulation, [status(thm), theory('equality')], [c_307, c_2])).
% 2.48/1.46  tff(c_381, plain, (![A_86, B_87, C_88]: (k1_relset_1(A_86, B_87, C_88)=k1_relat_1(C_88) | ~m1_subset_1(C_88, k1_zfmisc_1(k2_zfmisc_1(A_86, B_87))))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.48/1.46  tff(c_385, plain, (![A_86, B_87]: (k1_relset_1(A_86, B_87, '#skF_1')=k1_relat_1('#skF_1'))), inference(resolution, [status(thm)], [c_312, c_381])).
% 2.48/1.46  tff(c_391, plain, (![A_86, B_87]: (k1_relset_1(A_86, B_87, '#skF_1')='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_314, c_385])).
% 2.48/1.46  tff(c_26, plain, (![C_14, B_13]: (v1_funct_2(C_14, k1_xboole_0, B_13) | k1_relset_1(k1_xboole_0, B_13, C_14)!=k1_xboole_0 | ~m1_subset_1(C_14, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_13))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.48/1.46  tff(c_483, plain, (![C_103, B_104]: (v1_funct_2(C_103, '#skF_1', B_104) | k1_relset_1('#skF_1', B_104, C_103)!='#skF_1' | ~m1_subset_1(C_103, k1_zfmisc_1(k2_zfmisc_1('#skF_1', B_104))))), inference(demodulation, [status(thm), theory('equality')], [c_307, c_307, c_307, c_307, c_26])).
% 2.48/1.46  tff(c_487, plain, (![B_104]: (v1_funct_2('#skF_1', '#skF_1', B_104) | k1_relset_1('#skF_1', B_104, '#skF_1')!='#skF_1')), inference(resolution, [status(thm)], [c_312, c_483])).
% 2.48/1.46  tff(c_494, plain, (![B_104]: (v1_funct_2('#skF_1', '#skF_1', B_104))), inference(demodulation, [status(thm), theory('equality')], [c_391, c_487])).
% 2.48/1.46  tff(c_308, plain, (k2_relat_1('#skF_1')=k1_xboole_0), inference(splitRight, [status(thm)], [c_69])).
% 2.48/1.46  tff(c_319, plain, (k2_relat_1('#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_307, c_308])).
% 2.48/1.46  tff(c_320, plain, (~v1_funct_2('#skF_1', k1_relat_1('#skF_1'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_319, c_64])).
% 2.48/1.46  tff(c_346, plain, (~v1_funct_2('#skF_1', '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_314, c_320])).
% 2.48/1.46  tff(c_498, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_494, c_346])).
% 2.48/1.46  tff(c_499, plain, (~m1_subset_1('#skF_1', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_1'), k2_relat_1('#skF_1'))))), inference(splitRight, [status(thm)], [c_40])).
% 2.48/1.46  tff(c_516, plain, (~r1_tarski('#skF_1', k2_zfmisc_1(k1_relat_1('#skF_1'), k2_relat_1('#skF_1')))), inference(resolution, [status(thm)], [c_6, c_499])).
% 2.48/1.46  tff(c_520, plain, (~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_517, c_516])).
% 2.48/1.46  tff(c_530, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_38, c_520])).
% 2.48/1.46  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.48/1.46  
% 2.48/1.46  Inference rules
% 2.48/1.46  ----------------------
% 2.48/1.46  #Ref     : 0
% 2.48/1.46  #Sup     : 89
% 2.48/1.46  #Fact    : 0
% 2.48/1.46  #Define  : 0
% 2.48/1.46  #Split   : 5
% 2.48/1.46  #Chain   : 0
% 2.48/1.46  #Close   : 0
% 2.48/1.46  
% 2.48/1.46  Ordering : KBO
% 2.48/1.46  
% 2.48/1.46  Simplification rules
% 2.48/1.46  ----------------------
% 2.48/1.46  #Subsume      : 3
% 2.48/1.46  #Demod        : 106
% 2.48/1.46  #Tautology    : 53
% 2.48/1.46  #SimpNegUnit  : 1
% 2.48/1.46  #BackRed      : 8
% 2.48/1.46  
% 2.48/1.46  #Partial instantiations: 0
% 2.48/1.46  #Strategies tried      : 1
% 2.48/1.46  
% 2.48/1.46  Timing (in seconds)
% 2.48/1.46  ----------------------
% 2.48/1.46  Preprocessing        : 0.37
% 2.48/1.46  Parsing              : 0.20
% 2.48/1.46  CNF conversion       : 0.02
% 2.48/1.46  Main loop            : 0.25
% 2.48/1.46  Inferencing          : 0.10
% 2.48/1.46  Reduction            : 0.08
% 2.48/1.46  Demodulation         : 0.05
% 2.48/1.46  BG Simplification    : 0.02
% 2.48/1.46  Subsumption          : 0.04
% 2.48/1.46  Abstraction          : 0.01
% 2.48/1.46  MUC search           : 0.00
% 2.48/1.46  Cooper               : 0.00
% 2.48/1.46  Total                : 0.66
% 2.48/1.46  Index Insertion      : 0.00
% 2.48/1.46  Index Deletion       : 0.00
% 2.48/1.46  Index Matching       : 0.00
% 2.48/1.46  BG Taut test         : 0.00
%------------------------------------------------------------------------------
