%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:10:51 EST 2020

% Result     : Theorem 2.09s
% Output     : CNFRefutation 2.12s
% Verified   : 
% Statistics : Number of formulae       :   66 ( 208 expanded)
%              Number of leaves         :   21 (  77 expanded)
%              Depth                    :    9
%              Number of atoms          :  102 ( 474 expanded)
%              Number of equality atoms :   37 ( 147 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

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

tff(f_72,negated_conjecture,(
    ~ ! [A] :
        ( ( v1_relat_1(A)
          & v1_funct_1(A) )
       => ( v1_funct_1(A)
          & v1_funct_2(A,k1_relat_1(A),k2_relat_1(A))
          & m1_subset_1(A,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A)))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_funct_2)).

tff(f_33,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => r1_tarski(A,k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_relat_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_39,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( k1_relat_1(A) = k1_xboole_0
      <=> k2_relat_1(A) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_relat_1)).

tff(f_61,axiom,(
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

tff(c_30,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_143,plain,(
    ! [A_52] :
      ( r1_tarski(A_52,k2_zfmisc_1(k1_relat_1(A_52),k2_relat_1(A_52)))
      | ~ v1_relat_1(A_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( m1_subset_1(A_1,k1_zfmisc_1(B_2))
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_6,plain,(
    ! [A_3] :
      ( r1_tarski(A_3,k2_zfmisc_1(k1_relat_1(A_3),k2_relat_1(A_3)))
      | ~ v1_relat_1(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_53,plain,(
    ! [A_18,B_19,C_20] :
      ( k1_relset_1(A_18,B_19,C_20) = k1_relat_1(C_20)
      | ~ m1_subset_1(C_20,k1_zfmisc_1(k2_zfmisc_1(A_18,B_19))) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_59,plain,(
    ! [A_21,B_22,A_23] :
      ( k1_relset_1(A_21,B_22,A_23) = k1_relat_1(A_23)
      | ~ r1_tarski(A_23,k2_zfmisc_1(A_21,B_22)) ) ),
    inference(resolution,[status(thm)],[c_4,c_53])).

tff(c_63,plain,(
    ! [A_3] :
      ( k1_relset_1(k1_relat_1(A_3),k2_relat_1(A_3),A_3) = k1_relat_1(A_3)
      | ~ v1_relat_1(A_3) ) ),
    inference(resolution,[status(thm)],[c_6,c_59])).

tff(c_39,plain,(
    ! [A_15] :
      ( k1_relat_1(A_15) = k1_xboole_0
      | k2_relat_1(A_15) != k1_xboole_0
      | ~ v1_relat_1(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_43,plain,
    ( k1_relat_1('#skF_1') = k1_xboole_0
    | k2_relat_1('#skF_1') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_30,c_39])).

tff(c_49,plain,(
    k2_relat_1('#skF_1') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_43])).

tff(c_111,plain,(
    ! [B_45,C_46,A_47] :
      ( k1_xboole_0 = B_45
      | v1_funct_2(C_46,A_47,B_45)
      | k1_relset_1(A_47,B_45,C_46) != A_47
      | ~ m1_subset_1(C_46,k1_zfmisc_1(k2_zfmisc_1(A_47,B_45))) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_117,plain,(
    ! [B_48,A_49,A_50] :
      ( k1_xboole_0 = B_48
      | v1_funct_2(A_49,A_50,B_48)
      | k1_relset_1(A_50,B_48,A_49) != A_50
      | ~ r1_tarski(A_49,k2_zfmisc_1(A_50,B_48)) ) ),
    inference(resolution,[status(thm)],[c_4,c_111])).

tff(c_122,plain,(
    ! [A_51] :
      ( k2_relat_1(A_51) = k1_xboole_0
      | v1_funct_2(A_51,k1_relat_1(A_51),k2_relat_1(A_51))
      | k1_relset_1(k1_relat_1(A_51),k2_relat_1(A_51),A_51) != k1_relat_1(A_51)
      | ~ v1_relat_1(A_51) ) ),
    inference(resolution,[status(thm)],[c_6,c_117])).

tff(c_28,plain,(
    v1_funct_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_26,plain,
    ( ~ m1_subset_1('#skF_1',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_1'),k2_relat_1('#skF_1'))))
    | ~ v1_funct_2('#skF_1',k1_relat_1('#skF_1'),k2_relat_1('#skF_1'))
    | ~ v1_funct_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_32,plain,
    ( ~ m1_subset_1('#skF_1',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_1'),k2_relat_1('#skF_1'))))
    | ~ v1_funct_2('#skF_1',k1_relat_1('#skF_1'),k2_relat_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26])).

tff(c_51,plain,(
    ~ v1_funct_2('#skF_1',k1_relat_1('#skF_1'),k2_relat_1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_32])).

tff(c_125,plain,
    ( k2_relat_1('#skF_1') = k1_xboole_0
    | k1_relset_1(k1_relat_1('#skF_1'),k2_relat_1('#skF_1'),'#skF_1') != k1_relat_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_122,c_51])).

tff(c_128,plain,
    ( k2_relat_1('#skF_1') = k1_xboole_0
    | k1_relset_1(k1_relat_1('#skF_1'),k2_relat_1('#skF_1'),'#skF_1') != k1_relat_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_125])).

tff(c_129,plain,(
    k1_relset_1(k1_relat_1('#skF_1'),k2_relat_1('#skF_1'),'#skF_1') != k1_relat_1('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_49,c_128])).

tff(c_132,plain,(
    ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_63,c_129])).

tff(c_136,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_132])).

tff(c_137,plain,(
    ~ m1_subset_1('#skF_1',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_1'),k2_relat_1('#skF_1')))) ),
    inference(splitRight,[status(thm)],[c_32])).

tff(c_142,plain,(
    ~ r1_tarski('#skF_1',k2_zfmisc_1(k1_relat_1('#skF_1'),k2_relat_1('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_4,c_137])).

tff(c_146,plain,(
    ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_143,c_142])).

tff(c_150,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_146])).

tff(c_151,plain,(
    k1_relat_1('#skF_1') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_43])).

tff(c_152,plain,(
    k2_relat_1('#skF_1') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_43])).

tff(c_161,plain,(
    ! [A_53] :
      ( r1_tarski(A_53,k2_zfmisc_1(k1_relat_1(A_53),k2_relat_1(A_53)))
      | ~ v1_relat_1(A_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_164,plain,
    ( r1_tarski('#skF_1',k2_zfmisc_1(k1_relat_1('#skF_1'),k1_xboole_0))
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_152,c_161])).

tff(c_169,plain,(
    r1_tarski('#skF_1',k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_151,c_164])).

tff(c_175,plain,
    ( ~ m1_subset_1('#skF_1',k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ v1_funct_2('#skF_1',k1_xboole_0,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_152,c_151,c_152,c_151,c_32])).

tff(c_176,plain,(
    ~ v1_funct_2('#skF_1',k1_xboole_0,k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_175])).

tff(c_177,plain,(
    ! [A_54,B_55,C_56] :
      ( k1_relset_1(A_54,B_55,C_56) = k1_relat_1(C_56)
      | ~ m1_subset_1(C_56,k1_zfmisc_1(k2_zfmisc_1(A_54,B_55))) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_183,plain,(
    ! [A_57,B_58,A_59] :
      ( k1_relset_1(A_57,B_58,A_59) = k1_relat_1(A_59)
      | ~ r1_tarski(A_59,k2_zfmisc_1(A_57,B_58)) ) ),
    inference(resolution,[status(thm)],[c_4,c_177])).

tff(c_186,plain,(
    k1_relset_1(k1_xboole_0,k1_xboole_0,'#skF_1') = k1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_169,c_183])).

tff(c_191,plain,(
    k1_relset_1(k1_xboole_0,k1_xboole_0,'#skF_1') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_151,c_186])).

tff(c_245,plain,(
    ! [C_71,B_72] :
      ( v1_funct_2(C_71,k1_xboole_0,B_72)
      | k1_relset_1(k1_xboole_0,B_72,C_71) != k1_xboole_0
      | ~ m1_subset_1(C_71,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_72))) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_251,plain,(
    ! [A_73,B_74] :
      ( v1_funct_2(A_73,k1_xboole_0,B_74)
      | k1_relset_1(k1_xboole_0,B_74,A_73) != k1_xboole_0
      | ~ r1_tarski(A_73,k2_zfmisc_1(k1_xboole_0,B_74)) ) ),
    inference(resolution,[status(thm)],[c_4,c_245])).

tff(c_254,plain,
    ( v1_funct_2('#skF_1',k1_xboole_0,k1_xboole_0)
    | k1_relset_1(k1_xboole_0,k1_xboole_0,'#skF_1') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_169,c_251])).

tff(c_257,plain,(
    v1_funct_2('#skF_1',k1_xboole_0,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_191,c_254])).

tff(c_259,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_176,c_257])).

tff(c_260,plain,(
    ~ m1_subset_1('#skF_1',k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ),
    inference(splitRight,[status(thm)],[c_175])).

tff(c_264,plain,(
    ~ r1_tarski('#skF_1',k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) ),
    inference(resolution,[status(thm)],[c_4,c_260])).

tff(c_268,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_169,c_264])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n025.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 11:05:20 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.09/1.24  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.12/1.24  
% 2.12/1.24  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.12/1.25  %$ v1_funct_2 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1
% 2.12/1.25  
% 2.12/1.25  %Foreground sorts:
% 2.12/1.25  
% 2.12/1.25  
% 2.12/1.25  %Background operators:
% 2.12/1.25  
% 2.12/1.25  
% 2.12/1.25  %Foreground operators:
% 2.12/1.25  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.12/1.25  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.12/1.25  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.12/1.25  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.12/1.25  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.12/1.25  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.12/1.25  tff('#skF_1', type, '#skF_1': $i).
% 2.12/1.25  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.12/1.25  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.12/1.25  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.12/1.25  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.12/1.25  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.12/1.25  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.12/1.25  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.12/1.25  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.12/1.25  
% 2.12/1.26  tff(f_72, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => ((v1_funct_1(A) & v1_funct_2(A, k1_relat_1(A), k2_relat_1(A))) & m1_subset_1(A, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_funct_2)).
% 2.12/1.26  tff(f_33, axiom, (![A]: (v1_relat_1(A) => r1_tarski(A, k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t21_relat_1)).
% 2.12/1.26  tff(f_29, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 2.12/1.26  tff(f_43, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.12/1.26  tff(f_39, axiom, (![A]: (v1_relat_1(A) => ((k1_relat_1(A) = k1_xboole_0) <=> (k2_relat_1(A) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_relat_1)).
% 2.12/1.26  tff(f_61, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 2.12/1.26  tff(c_30, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.12/1.26  tff(c_143, plain, (![A_52]: (r1_tarski(A_52, k2_zfmisc_1(k1_relat_1(A_52), k2_relat_1(A_52))) | ~v1_relat_1(A_52))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.12/1.26  tff(c_4, plain, (![A_1, B_2]: (m1_subset_1(A_1, k1_zfmisc_1(B_2)) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.12/1.26  tff(c_6, plain, (![A_3]: (r1_tarski(A_3, k2_zfmisc_1(k1_relat_1(A_3), k2_relat_1(A_3))) | ~v1_relat_1(A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.12/1.26  tff(c_53, plain, (![A_18, B_19, C_20]: (k1_relset_1(A_18, B_19, C_20)=k1_relat_1(C_20) | ~m1_subset_1(C_20, k1_zfmisc_1(k2_zfmisc_1(A_18, B_19))))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.12/1.26  tff(c_59, plain, (![A_21, B_22, A_23]: (k1_relset_1(A_21, B_22, A_23)=k1_relat_1(A_23) | ~r1_tarski(A_23, k2_zfmisc_1(A_21, B_22)))), inference(resolution, [status(thm)], [c_4, c_53])).
% 2.12/1.26  tff(c_63, plain, (![A_3]: (k1_relset_1(k1_relat_1(A_3), k2_relat_1(A_3), A_3)=k1_relat_1(A_3) | ~v1_relat_1(A_3))), inference(resolution, [status(thm)], [c_6, c_59])).
% 2.12/1.26  tff(c_39, plain, (![A_15]: (k1_relat_1(A_15)=k1_xboole_0 | k2_relat_1(A_15)!=k1_xboole_0 | ~v1_relat_1(A_15))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.12/1.26  tff(c_43, plain, (k1_relat_1('#skF_1')=k1_xboole_0 | k2_relat_1('#skF_1')!=k1_xboole_0), inference(resolution, [status(thm)], [c_30, c_39])).
% 2.12/1.26  tff(c_49, plain, (k2_relat_1('#skF_1')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_43])).
% 2.12/1.26  tff(c_111, plain, (![B_45, C_46, A_47]: (k1_xboole_0=B_45 | v1_funct_2(C_46, A_47, B_45) | k1_relset_1(A_47, B_45, C_46)!=A_47 | ~m1_subset_1(C_46, k1_zfmisc_1(k2_zfmisc_1(A_47, B_45))))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.12/1.26  tff(c_117, plain, (![B_48, A_49, A_50]: (k1_xboole_0=B_48 | v1_funct_2(A_49, A_50, B_48) | k1_relset_1(A_50, B_48, A_49)!=A_50 | ~r1_tarski(A_49, k2_zfmisc_1(A_50, B_48)))), inference(resolution, [status(thm)], [c_4, c_111])).
% 2.12/1.26  tff(c_122, plain, (![A_51]: (k2_relat_1(A_51)=k1_xboole_0 | v1_funct_2(A_51, k1_relat_1(A_51), k2_relat_1(A_51)) | k1_relset_1(k1_relat_1(A_51), k2_relat_1(A_51), A_51)!=k1_relat_1(A_51) | ~v1_relat_1(A_51))), inference(resolution, [status(thm)], [c_6, c_117])).
% 2.12/1.26  tff(c_28, plain, (v1_funct_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.12/1.26  tff(c_26, plain, (~m1_subset_1('#skF_1', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_1'), k2_relat_1('#skF_1')))) | ~v1_funct_2('#skF_1', k1_relat_1('#skF_1'), k2_relat_1('#skF_1')) | ~v1_funct_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.12/1.26  tff(c_32, plain, (~m1_subset_1('#skF_1', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_1'), k2_relat_1('#skF_1')))) | ~v1_funct_2('#skF_1', k1_relat_1('#skF_1'), k2_relat_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_26])).
% 2.12/1.26  tff(c_51, plain, (~v1_funct_2('#skF_1', k1_relat_1('#skF_1'), k2_relat_1('#skF_1'))), inference(splitLeft, [status(thm)], [c_32])).
% 2.12/1.26  tff(c_125, plain, (k2_relat_1('#skF_1')=k1_xboole_0 | k1_relset_1(k1_relat_1('#skF_1'), k2_relat_1('#skF_1'), '#skF_1')!=k1_relat_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_122, c_51])).
% 2.12/1.26  tff(c_128, plain, (k2_relat_1('#skF_1')=k1_xboole_0 | k1_relset_1(k1_relat_1('#skF_1'), k2_relat_1('#skF_1'), '#skF_1')!=k1_relat_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_125])).
% 2.12/1.26  tff(c_129, plain, (k1_relset_1(k1_relat_1('#skF_1'), k2_relat_1('#skF_1'), '#skF_1')!=k1_relat_1('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_49, c_128])).
% 2.12/1.26  tff(c_132, plain, (~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_63, c_129])).
% 2.12/1.26  tff(c_136, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_30, c_132])).
% 2.12/1.26  tff(c_137, plain, (~m1_subset_1('#skF_1', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_1'), k2_relat_1('#skF_1'))))), inference(splitRight, [status(thm)], [c_32])).
% 2.12/1.26  tff(c_142, plain, (~r1_tarski('#skF_1', k2_zfmisc_1(k1_relat_1('#skF_1'), k2_relat_1('#skF_1')))), inference(resolution, [status(thm)], [c_4, c_137])).
% 2.12/1.26  tff(c_146, plain, (~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_143, c_142])).
% 2.12/1.26  tff(c_150, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_30, c_146])).
% 2.12/1.26  tff(c_151, plain, (k1_relat_1('#skF_1')=k1_xboole_0), inference(splitRight, [status(thm)], [c_43])).
% 2.12/1.26  tff(c_152, plain, (k2_relat_1('#skF_1')=k1_xboole_0), inference(splitRight, [status(thm)], [c_43])).
% 2.12/1.26  tff(c_161, plain, (![A_53]: (r1_tarski(A_53, k2_zfmisc_1(k1_relat_1(A_53), k2_relat_1(A_53))) | ~v1_relat_1(A_53))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.12/1.26  tff(c_164, plain, (r1_tarski('#skF_1', k2_zfmisc_1(k1_relat_1('#skF_1'), k1_xboole_0)) | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_152, c_161])).
% 2.12/1.26  tff(c_169, plain, (r1_tarski('#skF_1', k2_zfmisc_1(k1_xboole_0, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_151, c_164])).
% 2.12/1.26  tff(c_175, plain, (~m1_subset_1('#skF_1', k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, k1_xboole_0))) | ~v1_funct_2('#skF_1', k1_xboole_0, k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_152, c_151, c_152, c_151, c_32])).
% 2.12/1.26  tff(c_176, plain, (~v1_funct_2('#skF_1', k1_xboole_0, k1_xboole_0)), inference(splitLeft, [status(thm)], [c_175])).
% 2.12/1.26  tff(c_177, plain, (![A_54, B_55, C_56]: (k1_relset_1(A_54, B_55, C_56)=k1_relat_1(C_56) | ~m1_subset_1(C_56, k1_zfmisc_1(k2_zfmisc_1(A_54, B_55))))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.12/1.26  tff(c_183, plain, (![A_57, B_58, A_59]: (k1_relset_1(A_57, B_58, A_59)=k1_relat_1(A_59) | ~r1_tarski(A_59, k2_zfmisc_1(A_57, B_58)))), inference(resolution, [status(thm)], [c_4, c_177])).
% 2.12/1.26  tff(c_186, plain, (k1_relset_1(k1_xboole_0, k1_xboole_0, '#skF_1')=k1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_169, c_183])).
% 2.12/1.26  tff(c_191, plain, (k1_relset_1(k1_xboole_0, k1_xboole_0, '#skF_1')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_151, c_186])).
% 2.12/1.26  tff(c_245, plain, (![C_71, B_72]: (v1_funct_2(C_71, k1_xboole_0, B_72) | k1_relset_1(k1_xboole_0, B_72, C_71)!=k1_xboole_0 | ~m1_subset_1(C_71, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_72))))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.12/1.26  tff(c_251, plain, (![A_73, B_74]: (v1_funct_2(A_73, k1_xboole_0, B_74) | k1_relset_1(k1_xboole_0, B_74, A_73)!=k1_xboole_0 | ~r1_tarski(A_73, k2_zfmisc_1(k1_xboole_0, B_74)))), inference(resolution, [status(thm)], [c_4, c_245])).
% 2.12/1.26  tff(c_254, plain, (v1_funct_2('#skF_1', k1_xboole_0, k1_xboole_0) | k1_relset_1(k1_xboole_0, k1_xboole_0, '#skF_1')!=k1_xboole_0), inference(resolution, [status(thm)], [c_169, c_251])).
% 2.12/1.26  tff(c_257, plain, (v1_funct_2('#skF_1', k1_xboole_0, k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_191, c_254])).
% 2.12/1.26  tff(c_259, plain, $false, inference(negUnitSimplification, [status(thm)], [c_176, c_257])).
% 2.12/1.26  tff(c_260, plain, (~m1_subset_1('#skF_1', k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, k1_xboole_0)))), inference(splitRight, [status(thm)], [c_175])).
% 2.12/1.26  tff(c_264, plain, (~r1_tarski('#skF_1', k2_zfmisc_1(k1_xboole_0, k1_xboole_0))), inference(resolution, [status(thm)], [c_4, c_260])).
% 2.12/1.26  tff(c_268, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_169, c_264])).
% 2.12/1.26  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.12/1.26  
% 2.12/1.26  Inference rules
% 2.12/1.26  ----------------------
% 2.12/1.26  #Ref     : 0
% 2.12/1.26  #Sup     : 42
% 2.12/1.26  #Fact    : 0
% 2.12/1.26  #Define  : 0
% 2.12/1.26  #Split   : 3
% 2.12/1.26  #Chain   : 0
% 2.12/1.26  #Close   : 0
% 2.12/1.26  
% 2.12/1.26  Ordering : KBO
% 2.12/1.26  
% 2.12/1.26  Simplification rules
% 2.12/1.26  ----------------------
% 2.12/1.26  #Subsume      : 3
% 2.12/1.26  #Demod        : 27
% 2.12/1.26  #Tautology    : 15
% 2.12/1.26  #SimpNegUnit  : 3
% 2.12/1.26  #BackRed      : 0
% 2.12/1.26  
% 2.12/1.26  #Partial instantiations: 0
% 2.12/1.26  #Strategies tried      : 1
% 2.12/1.26  
% 2.12/1.26  Timing (in seconds)
% 2.12/1.26  ----------------------
% 2.12/1.26  Preprocessing        : 0.30
% 2.12/1.26  Parsing              : 0.16
% 2.12/1.26  CNF conversion       : 0.02
% 2.12/1.26  Main loop            : 0.19
% 2.12/1.26  Inferencing          : 0.07
% 2.12/1.26  Reduction            : 0.05
% 2.12/1.26  Demodulation         : 0.04
% 2.12/1.27  BG Simplification    : 0.01
% 2.12/1.27  Subsumption          : 0.03
% 2.12/1.27  Abstraction          : 0.01
% 2.12/1.27  MUC search           : 0.00
% 2.12/1.27  Cooper               : 0.00
% 2.12/1.27  Total                : 0.52
% 2.12/1.27  Index Insertion      : 0.00
% 2.12/1.27  Index Deletion       : 0.00
% 2.12/1.27  Index Matching       : 0.00
% 2.12/1.27  BG Taut test         : 0.00
%------------------------------------------------------------------------------
