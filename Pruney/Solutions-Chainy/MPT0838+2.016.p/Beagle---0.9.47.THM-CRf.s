%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:08:11 EST 2020

% Result     : Theorem 2.37s
% Output     : CNFRefutation 2.61s
% Verified   : 
% Statistics : Number of formulae       :   69 ( 124 expanded)
%              Number of leaves         :   31 (  55 expanded)
%              Depth                    :    8
%              Number of atoms          :   91 ( 240 expanded)
%              Number of equality atoms :   31 (  71 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_94,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B] :
            ( ~ v1_xboole_0(B)
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
               => ~ ( k1_relset_1(A,B,C) != k1_xboole_0
                    & ! [D] :
                        ( m1_subset_1(D,B)
                       => ~ r2_hidden(D,k2_relset_1(A,B,C)) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_relset_1)).

tff(f_59,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_55,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( k1_relat_1(A) = k1_xboole_0
      <=> k2_relat_1(A) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_relat_1)).

tff(f_65,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_33,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_37,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

tff(f_73,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_69,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(c_30,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_4') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_32,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_55,plain,(
    ! [C_42,A_43,B_44] :
      ( v1_relat_1(C_42)
      | ~ m1_subset_1(C_42,k1_zfmisc_1(k2_zfmisc_1(A_43,B_44))) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_64,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_32,c_55])).

tff(c_16,plain,(
    ! [A_10] :
      ( k2_relat_1(A_10) = k1_xboole_0
      | k1_relat_1(A_10) != k1_xboole_0
      | ~ v1_relat_1(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_68,plain,
    ( k2_relat_1('#skF_4') = k1_xboole_0
    | k1_relat_1('#skF_4') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_64,c_16])).

tff(c_69,plain,(
    k1_relat_1('#skF_4') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_68])).

tff(c_76,plain,(
    ! [A_48] :
      ( k1_relat_1(A_48) = k1_xboole_0
      | k2_relat_1(A_48) != k1_xboole_0
      | ~ v1_relat_1(A_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_79,plain,
    ( k1_relat_1('#skF_4') = k1_xboole_0
    | k2_relat_1('#skF_4') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_64,c_76])).

tff(c_82,plain,(
    k2_relat_1('#skF_4') != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_69,c_79])).

tff(c_83,plain,(
    ! [C_49,B_50,A_51] :
      ( v5_relat_1(C_49,B_50)
      | ~ m1_subset_1(C_49,k1_zfmisc_1(k2_zfmisc_1(A_51,B_50))) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_92,plain,(
    v5_relat_1('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_32,c_83])).

tff(c_12,plain,(
    ! [B_9,A_8] :
      ( r1_tarski(k2_relat_1(B_9),A_8)
      | ~ v5_relat_1(B_9,A_8)
      | ~ v1_relat_1(B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_2,plain,(
    ! [A_1] :
      ( r2_hidden('#skF_1'(A_1),A_1)
      | k1_xboole_0 = A_1 ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_6,plain,(
    ! [A_3,B_4] :
      ( m1_subset_1(A_3,k1_zfmisc_1(B_4))
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_137,plain,(
    ! [A_65,C_66,B_67] :
      ( m1_subset_1(A_65,C_66)
      | ~ m1_subset_1(B_67,k1_zfmisc_1(C_66))
      | ~ r2_hidden(A_65,B_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_168,plain,(
    ! [A_73,B_74,A_75] :
      ( m1_subset_1(A_73,B_74)
      | ~ r2_hidden(A_73,A_75)
      | ~ r1_tarski(A_75,B_74) ) ),
    inference(resolution,[status(thm)],[c_6,c_137])).

tff(c_172,plain,(
    ! [A_76,B_77] :
      ( m1_subset_1('#skF_1'(A_76),B_77)
      | ~ r1_tarski(A_76,B_77)
      | k1_xboole_0 = A_76 ) ),
    inference(resolution,[status(thm)],[c_2,c_168])).

tff(c_145,plain,(
    ! [A_69,B_70,C_71] :
      ( k2_relset_1(A_69,B_70,C_71) = k2_relat_1(C_71)
      | ~ m1_subset_1(C_71,k1_zfmisc_1(k2_zfmisc_1(A_69,B_70))) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_154,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_32,c_145])).

tff(c_49,plain,(
    ! [D_41] :
      ( ~ r2_hidden(D_41,k2_relset_1('#skF_2','#skF_3','#skF_4'))
      | ~ m1_subset_1(D_41,'#skF_3') ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_54,plain,
    ( ~ m1_subset_1('#skF_1'(k2_relset_1('#skF_2','#skF_3','#skF_4')),'#skF_3')
    | k2_relset_1('#skF_2','#skF_3','#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2,c_49])).

tff(c_93,plain,(
    ~ m1_subset_1('#skF_1'(k2_relset_1('#skF_2','#skF_3','#skF_4')),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_54])).

tff(c_155,plain,(
    ~ m1_subset_1('#skF_1'(k2_relat_1('#skF_4')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_154,c_93])).

tff(c_175,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_4'),'#skF_3')
    | k2_relat_1('#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_172,c_155])).

tff(c_201,plain,(
    ~ r1_tarski(k2_relat_1('#skF_4'),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_175])).

tff(c_225,plain,
    ( ~ v5_relat_1('#skF_4','#skF_3')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_12,c_201])).

tff(c_229,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_92,c_225])).

tff(c_230,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_4') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_300,plain,(
    ! [A_102,B_103,C_104] :
      ( k2_relset_1(A_102,B_103,C_104) = k2_relat_1(C_104)
      | ~ m1_subset_1(C_104,k1_zfmisc_1(k2_zfmisc_1(A_102,B_103))) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_307,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_32,c_300])).

tff(c_310,plain,(
    k2_relat_1('#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_230,c_307])).

tff(c_312,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_310])).

tff(c_314,plain,(
    k1_relat_1('#skF_4') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_68])).

tff(c_490,plain,(
    ! [A_147,B_148,C_149] :
      ( k1_relset_1(A_147,B_148,C_149) = k1_relat_1(C_149)
      | ~ m1_subset_1(C_149,k1_zfmisc_1(k2_zfmisc_1(A_147,B_148))) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_501,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_32,c_490])).

tff(c_505,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_314,c_501])).

tff(c_507,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_505])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:42:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.37/1.36  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.37/1.36  
% 2.37/1.36  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.37/1.36  %$ v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4
% 2.37/1.36  
% 2.37/1.36  %Foreground sorts:
% 2.37/1.36  
% 2.37/1.36  
% 2.37/1.36  %Background operators:
% 2.37/1.36  
% 2.37/1.36  
% 2.37/1.36  %Foreground operators:
% 2.37/1.36  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 2.37/1.36  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.37/1.36  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.37/1.36  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.37/1.36  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.37/1.36  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.37/1.36  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.37/1.36  tff('#skF_2', type, '#skF_2': $i).
% 2.37/1.36  tff('#skF_3', type, '#skF_3': $i).
% 2.37/1.36  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.37/1.36  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.37/1.36  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.37/1.36  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.37/1.36  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.37/1.36  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.37/1.36  tff('#skF_4', type, '#skF_4': $i).
% 2.37/1.36  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.37/1.36  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.37/1.36  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.37/1.36  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.37/1.36  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.37/1.36  
% 2.61/1.38  tff(f_94, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ~(~(k1_relset_1(A, B, C) = k1_xboole_0) & (![D]: (m1_subset_1(D, B) => ~r2_hidden(D, k2_relset_1(A, B, C))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_relset_1)).
% 2.61/1.38  tff(f_59, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.61/1.38  tff(f_55, axiom, (![A]: (v1_relat_1(A) => ((k1_relat_1(A) = k1_xboole_0) <=> (k2_relat_1(A) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_relat_1)).
% 2.61/1.38  tff(f_65, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.61/1.38  tff(f_49, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 2.61/1.38  tff(f_33, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 2.61/1.38  tff(f_37, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 2.61/1.38  tff(f_43, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset)).
% 2.61/1.38  tff(f_73, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 2.61/1.38  tff(f_69, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.61/1.38  tff(c_30, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_4')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_94])).
% 2.61/1.38  tff(c_32, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_94])).
% 2.61/1.38  tff(c_55, plain, (![C_42, A_43, B_44]: (v1_relat_1(C_42) | ~m1_subset_1(C_42, k1_zfmisc_1(k2_zfmisc_1(A_43, B_44))))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.61/1.38  tff(c_64, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_32, c_55])).
% 2.61/1.38  tff(c_16, plain, (![A_10]: (k2_relat_1(A_10)=k1_xboole_0 | k1_relat_1(A_10)!=k1_xboole_0 | ~v1_relat_1(A_10))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.61/1.38  tff(c_68, plain, (k2_relat_1('#skF_4')=k1_xboole_0 | k1_relat_1('#skF_4')!=k1_xboole_0), inference(resolution, [status(thm)], [c_64, c_16])).
% 2.61/1.38  tff(c_69, plain, (k1_relat_1('#skF_4')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_68])).
% 2.61/1.38  tff(c_76, plain, (![A_48]: (k1_relat_1(A_48)=k1_xboole_0 | k2_relat_1(A_48)!=k1_xboole_0 | ~v1_relat_1(A_48))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.61/1.38  tff(c_79, plain, (k1_relat_1('#skF_4')=k1_xboole_0 | k2_relat_1('#skF_4')!=k1_xboole_0), inference(resolution, [status(thm)], [c_64, c_76])).
% 2.61/1.38  tff(c_82, plain, (k2_relat_1('#skF_4')!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_69, c_79])).
% 2.61/1.38  tff(c_83, plain, (![C_49, B_50, A_51]: (v5_relat_1(C_49, B_50) | ~m1_subset_1(C_49, k1_zfmisc_1(k2_zfmisc_1(A_51, B_50))))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.61/1.38  tff(c_92, plain, (v5_relat_1('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_32, c_83])).
% 2.61/1.38  tff(c_12, plain, (![B_9, A_8]: (r1_tarski(k2_relat_1(B_9), A_8) | ~v5_relat_1(B_9, A_8) | ~v1_relat_1(B_9))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.61/1.38  tff(c_2, plain, (![A_1]: (r2_hidden('#skF_1'(A_1), A_1) | k1_xboole_0=A_1)), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.61/1.38  tff(c_6, plain, (![A_3, B_4]: (m1_subset_1(A_3, k1_zfmisc_1(B_4)) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.61/1.38  tff(c_137, plain, (![A_65, C_66, B_67]: (m1_subset_1(A_65, C_66) | ~m1_subset_1(B_67, k1_zfmisc_1(C_66)) | ~r2_hidden(A_65, B_67))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.61/1.38  tff(c_168, plain, (![A_73, B_74, A_75]: (m1_subset_1(A_73, B_74) | ~r2_hidden(A_73, A_75) | ~r1_tarski(A_75, B_74))), inference(resolution, [status(thm)], [c_6, c_137])).
% 2.61/1.38  tff(c_172, plain, (![A_76, B_77]: (m1_subset_1('#skF_1'(A_76), B_77) | ~r1_tarski(A_76, B_77) | k1_xboole_0=A_76)), inference(resolution, [status(thm)], [c_2, c_168])).
% 2.61/1.38  tff(c_145, plain, (![A_69, B_70, C_71]: (k2_relset_1(A_69, B_70, C_71)=k2_relat_1(C_71) | ~m1_subset_1(C_71, k1_zfmisc_1(k2_zfmisc_1(A_69, B_70))))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.61/1.38  tff(c_154, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_32, c_145])).
% 2.61/1.38  tff(c_49, plain, (![D_41]: (~r2_hidden(D_41, k2_relset_1('#skF_2', '#skF_3', '#skF_4')) | ~m1_subset_1(D_41, '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_94])).
% 2.61/1.38  tff(c_54, plain, (~m1_subset_1('#skF_1'(k2_relset_1('#skF_2', '#skF_3', '#skF_4')), '#skF_3') | k2_relset_1('#skF_2', '#skF_3', '#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_2, c_49])).
% 2.61/1.38  tff(c_93, plain, (~m1_subset_1('#skF_1'(k2_relset_1('#skF_2', '#skF_3', '#skF_4')), '#skF_3')), inference(splitLeft, [status(thm)], [c_54])).
% 2.61/1.38  tff(c_155, plain, (~m1_subset_1('#skF_1'(k2_relat_1('#skF_4')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_154, c_93])).
% 2.61/1.38  tff(c_175, plain, (~r1_tarski(k2_relat_1('#skF_4'), '#skF_3') | k2_relat_1('#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_172, c_155])).
% 2.61/1.38  tff(c_201, plain, (~r1_tarski(k2_relat_1('#skF_4'), '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_82, c_175])).
% 2.61/1.38  tff(c_225, plain, (~v5_relat_1('#skF_4', '#skF_3') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_12, c_201])).
% 2.61/1.38  tff(c_229, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_64, c_92, c_225])).
% 2.61/1.38  tff(c_230, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_4')=k1_xboole_0), inference(splitRight, [status(thm)], [c_54])).
% 2.61/1.38  tff(c_300, plain, (![A_102, B_103, C_104]: (k2_relset_1(A_102, B_103, C_104)=k2_relat_1(C_104) | ~m1_subset_1(C_104, k1_zfmisc_1(k2_zfmisc_1(A_102, B_103))))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.61/1.38  tff(c_307, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_32, c_300])).
% 2.61/1.38  tff(c_310, plain, (k2_relat_1('#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_230, c_307])).
% 2.61/1.38  tff(c_312, plain, $false, inference(negUnitSimplification, [status(thm)], [c_82, c_310])).
% 2.61/1.38  tff(c_314, plain, (k1_relat_1('#skF_4')=k1_xboole_0), inference(splitRight, [status(thm)], [c_68])).
% 2.61/1.38  tff(c_490, plain, (![A_147, B_148, C_149]: (k1_relset_1(A_147, B_148, C_149)=k1_relat_1(C_149) | ~m1_subset_1(C_149, k1_zfmisc_1(k2_zfmisc_1(A_147, B_148))))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.61/1.38  tff(c_501, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_32, c_490])).
% 2.61/1.38  tff(c_505, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_314, c_501])).
% 2.61/1.38  tff(c_507, plain, $false, inference(negUnitSimplification, [status(thm)], [c_30, c_505])).
% 2.61/1.38  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.61/1.38  
% 2.61/1.38  Inference rules
% 2.61/1.38  ----------------------
% 2.61/1.38  #Ref     : 0
% 2.61/1.38  #Sup     : 91
% 2.61/1.38  #Fact    : 0
% 2.61/1.38  #Define  : 0
% 2.61/1.38  #Split   : 3
% 2.61/1.38  #Chain   : 0
% 2.61/1.38  #Close   : 0
% 2.61/1.38  
% 2.61/1.38  Ordering : KBO
% 2.61/1.38  
% 2.61/1.38  Simplification rules
% 2.61/1.38  ----------------------
% 2.61/1.38  #Subsume      : 4
% 2.61/1.38  #Demod        : 26
% 2.61/1.38  #Tautology    : 23
% 2.61/1.38  #SimpNegUnit  : 5
% 2.61/1.38  #BackRed      : 3
% 2.61/1.38  
% 2.61/1.38  #Partial instantiations: 0
% 2.61/1.38  #Strategies tried      : 1
% 2.61/1.38  
% 2.61/1.38  Timing (in seconds)
% 2.61/1.38  ----------------------
% 2.61/1.38  Preprocessing        : 0.30
% 2.61/1.38  Parsing              : 0.16
% 2.61/1.38  CNF conversion       : 0.02
% 2.61/1.38  Main loop            : 0.26
% 2.61/1.38  Inferencing          : 0.11
% 2.61/1.38  Reduction            : 0.07
% 2.61/1.38  Demodulation         : 0.05
% 2.61/1.38  BG Simplification    : 0.01
% 2.61/1.38  Subsumption          : 0.03
% 2.61/1.38  Abstraction          : 0.02
% 2.61/1.38  MUC search           : 0.00
% 2.61/1.38  Cooper               : 0.00
% 2.61/1.38  Total                : 0.59
% 2.61/1.39  Index Insertion      : 0.00
% 2.61/1.39  Index Deletion       : 0.00
% 2.61/1.39  Index Matching       : 0.00
% 2.61/1.39  BG Taut test         : 0.00
%------------------------------------------------------------------------------
