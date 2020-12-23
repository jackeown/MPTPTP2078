%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:08:24 EST 2020

% Result     : Theorem 2.22s
% Output     : CNFRefutation 2.22s
% Verified   : 
% Statistics : Number of formulae       :   68 ( 113 expanded)
%              Number of leaves         :   31 (  51 expanded)
%              Depth                    :   10
%              Number of atoms          :   87 ( 212 expanded)
%              Number of equality atoms :   29 (  59 expanded)
%              Maximal formula depth    :   13 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > v4_relat_1 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k2_relset_1 > k1_relset_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

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

tff(f_96,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B] :
            ( ~ v1_xboole_0(B)
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(B,A)))
               => ~ ( k2_relset_1(B,A,C) != k1_xboole_0
                    & ! [D] :
                        ( m1_subset_1(D,B)
                       => ~ r2_hidden(D,k1_relset_1(B,A,C)) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_relset_1)).

tff(f_61,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_49,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( k1_relat_1(A) = k1_xboole_0
      <=> k2_relat_1(A) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_relat_1)).

tff(f_33,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_67,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_57,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k1_relat_1(k7_relat_1(C,B)))
      <=> ( r2_hidden(A,B)
          & r2_hidden(A,k1_relat_1(C)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t86_relat_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

tff(f_71,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_75,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(c_30,plain,(
    k2_relset_1('#skF_3','#skF_2','#skF_4') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_32,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_44,plain,(
    ! [C_39,A_40,B_41] :
      ( v1_relat_1(C_39)
      | ~ m1_subset_1(C_39,k1_zfmisc_1(k2_zfmisc_1(A_40,B_41))) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_53,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_32,c_44])).

tff(c_60,plain,(
    ! [A_43] :
      ( k2_relat_1(A_43) = k1_xboole_0
      | k1_relat_1(A_43) != k1_xboole_0
      | ~ v1_relat_1(A_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_64,plain,
    ( k2_relat_1('#skF_4') = k1_xboole_0
    | k1_relat_1('#skF_4') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_53,c_60])).

tff(c_65,plain,(
    k1_relat_1('#skF_4') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_64])).

tff(c_2,plain,(
    ! [A_1] :
      ( r2_hidden('#skF_1'(A_1),A_1)
      | k1_xboole_0 = A_1 ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_74,plain,(
    ! [C_47,A_48,B_49] :
      ( v4_relat_1(C_47,A_48)
      | ~ m1_subset_1(C_47,k1_zfmisc_1(k2_zfmisc_1(A_48,B_49))) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_83,plain,(
    v4_relat_1('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_32,c_74])).

tff(c_6,plain,(
    ! [B_6,A_5] :
      ( k7_relat_1(B_6,A_5) = B_6
      | ~ v4_relat_1(B_6,A_5)
      | ~ v1_relat_1(B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_86,plain,
    ( k7_relat_1('#skF_4','#skF_3') = '#skF_4'
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_83,c_6])).

tff(c_89,plain,(
    k7_relat_1('#skF_4','#skF_3') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_53,c_86])).

tff(c_105,plain,(
    ! [A_53,B_54,C_55] :
      ( r2_hidden(A_53,B_54)
      | ~ r2_hidden(A_53,k1_relat_1(k7_relat_1(C_55,B_54)))
      | ~ v1_relat_1(C_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_108,plain,(
    ! [A_53] :
      ( r2_hidden(A_53,'#skF_3')
      | ~ r2_hidden(A_53,k1_relat_1('#skF_4'))
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_89,c_105])).

tff(c_116,plain,(
    ! [A_56] :
      ( r2_hidden(A_56,'#skF_3')
      | ~ r2_hidden(A_56,k1_relat_1('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_53,c_108])).

tff(c_120,plain,
    ( r2_hidden('#skF_1'(k1_relat_1('#skF_4')),'#skF_3')
    | k1_relat_1('#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2,c_116])).

tff(c_123,plain,(
    r2_hidden('#skF_1'(k1_relat_1('#skF_4')),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_65,c_120])).

tff(c_4,plain,(
    ! [A_3,B_4] :
      ( m1_subset_1(A_3,B_4)
      | ~ r2_hidden(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_137,plain,(
    m1_subset_1('#skF_1'(k1_relat_1('#skF_4')),'#skF_3') ),
    inference(resolution,[status(thm)],[c_123,c_4])).

tff(c_124,plain,(
    ! [A_57,B_58,C_59] :
      ( k1_relset_1(A_57,B_58,C_59) = k1_relat_1(C_59)
      | ~ m1_subset_1(C_59,k1_zfmisc_1(k2_zfmisc_1(A_57,B_58))) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_133,plain,(
    k1_relset_1('#skF_3','#skF_2','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_32,c_124])).

tff(c_54,plain,(
    ! [D_42] :
      ( ~ r2_hidden(D_42,k1_relset_1('#skF_3','#skF_2','#skF_4'))
      | ~ m1_subset_1(D_42,'#skF_3') ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_59,plain,
    ( ~ m1_subset_1('#skF_1'(k1_relset_1('#skF_3','#skF_2','#skF_4')),'#skF_3')
    | k1_relset_1('#skF_3','#skF_2','#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2,c_54])).

tff(c_94,plain,(
    ~ m1_subset_1('#skF_1'(k1_relset_1('#skF_3','#skF_2','#skF_4')),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_59])).

tff(c_138,plain,(
    ~ m1_subset_1('#skF_1'(k1_relat_1('#skF_4')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_133,c_94])).

tff(c_142,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_137,c_138])).

tff(c_143,plain,(
    k1_relset_1('#skF_3','#skF_2','#skF_4') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_59])).

tff(c_226,plain,(
    ! [A_76,B_77,C_78] :
      ( k1_relset_1(A_76,B_77,C_78) = k1_relat_1(C_78)
      | ~ m1_subset_1(C_78,k1_zfmisc_1(k2_zfmisc_1(A_76,B_77))) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_233,plain,(
    k1_relset_1('#skF_3','#skF_2','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_32,c_226])).

tff(c_236,plain,(
    k1_relat_1('#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_143,c_233])).

tff(c_238,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_65,c_236])).

tff(c_239,plain,(
    k2_relat_1('#skF_4') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_64])).

tff(c_349,plain,(
    ! [A_101,B_102,C_103] :
      ( k2_relset_1(A_101,B_102,C_103) = k2_relat_1(C_103)
      | ~ m1_subset_1(C_103,k1_zfmisc_1(k2_zfmisc_1(A_101,B_102))) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_356,plain,(
    k2_relset_1('#skF_3','#skF_2','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_32,c_349])).

tff(c_359,plain,(
    k2_relset_1('#skF_3','#skF_2','#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_239,c_356])).

tff(c_361,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_359])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n007.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 12:34:36 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.22/1.26  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.22/1.26  
% 2.22/1.26  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.22/1.26  %$ v5_relat_1 > v4_relat_1 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k2_relset_1 > k1_relset_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4
% 2.22/1.26  
% 2.22/1.26  %Foreground sorts:
% 2.22/1.26  
% 2.22/1.26  
% 2.22/1.26  %Background operators:
% 2.22/1.26  
% 2.22/1.26  
% 2.22/1.26  %Foreground operators:
% 2.22/1.26  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 2.22/1.26  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.22/1.26  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.22/1.26  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.22/1.26  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.22/1.26  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.22/1.26  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.22/1.26  tff('#skF_2', type, '#skF_2': $i).
% 2.22/1.26  tff('#skF_3', type, '#skF_3': $i).
% 2.22/1.26  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.22/1.26  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.22/1.26  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.22/1.26  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.22/1.26  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.22/1.26  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.22/1.26  tff('#skF_4', type, '#skF_4': $i).
% 2.22/1.26  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.22/1.26  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.22/1.26  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.22/1.26  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.22/1.26  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.22/1.26  
% 2.22/1.28  tff(f_96, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => ~(~(k2_relset_1(B, A, C) = k1_xboole_0) & (![D]: (m1_subset_1(D, B) => ~r2_hidden(D, k1_relset_1(B, A, C))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t50_relset_1)).
% 2.22/1.28  tff(f_61, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.22/1.28  tff(f_49, axiom, (![A]: (v1_relat_1(A) => ((k1_relat_1(A) = k1_xboole_0) <=> (k2_relat_1(A) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_relat_1)).
% 2.22/1.28  tff(f_33, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 2.22/1.28  tff(f_67, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.22/1.28  tff(f_43, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t209_relat_1)).
% 2.22/1.28  tff(f_57, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k1_relat_1(k7_relat_1(C, B))) <=> (r2_hidden(A, B) & r2_hidden(A, k1_relat_1(C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t86_relat_1)).
% 2.22/1.28  tff(f_37, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_subset)).
% 2.22/1.28  tff(f_71, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.22/1.28  tff(f_75, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 2.22/1.28  tff(c_30, plain, (k2_relset_1('#skF_3', '#skF_2', '#skF_4')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_96])).
% 2.22/1.28  tff(c_32, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_96])).
% 2.22/1.28  tff(c_44, plain, (![C_39, A_40, B_41]: (v1_relat_1(C_39) | ~m1_subset_1(C_39, k1_zfmisc_1(k2_zfmisc_1(A_40, B_41))))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.22/1.28  tff(c_53, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_32, c_44])).
% 2.22/1.28  tff(c_60, plain, (![A_43]: (k2_relat_1(A_43)=k1_xboole_0 | k1_relat_1(A_43)!=k1_xboole_0 | ~v1_relat_1(A_43))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.22/1.28  tff(c_64, plain, (k2_relat_1('#skF_4')=k1_xboole_0 | k1_relat_1('#skF_4')!=k1_xboole_0), inference(resolution, [status(thm)], [c_53, c_60])).
% 2.22/1.28  tff(c_65, plain, (k1_relat_1('#skF_4')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_64])).
% 2.22/1.28  tff(c_2, plain, (![A_1]: (r2_hidden('#skF_1'(A_1), A_1) | k1_xboole_0=A_1)), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.22/1.28  tff(c_74, plain, (![C_47, A_48, B_49]: (v4_relat_1(C_47, A_48) | ~m1_subset_1(C_47, k1_zfmisc_1(k2_zfmisc_1(A_48, B_49))))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.22/1.28  tff(c_83, plain, (v4_relat_1('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_32, c_74])).
% 2.22/1.28  tff(c_6, plain, (![B_6, A_5]: (k7_relat_1(B_6, A_5)=B_6 | ~v4_relat_1(B_6, A_5) | ~v1_relat_1(B_6))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.22/1.28  tff(c_86, plain, (k7_relat_1('#skF_4', '#skF_3')='#skF_4' | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_83, c_6])).
% 2.22/1.28  tff(c_89, plain, (k7_relat_1('#skF_4', '#skF_3')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_53, c_86])).
% 2.22/1.28  tff(c_105, plain, (![A_53, B_54, C_55]: (r2_hidden(A_53, B_54) | ~r2_hidden(A_53, k1_relat_1(k7_relat_1(C_55, B_54))) | ~v1_relat_1(C_55))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.22/1.28  tff(c_108, plain, (![A_53]: (r2_hidden(A_53, '#skF_3') | ~r2_hidden(A_53, k1_relat_1('#skF_4')) | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_89, c_105])).
% 2.22/1.28  tff(c_116, plain, (![A_56]: (r2_hidden(A_56, '#skF_3') | ~r2_hidden(A_56, k1_relat_1('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_53, c_108])).
% 2.22/1.28  tff(c_120, plain, (r2_hidden('#skF_1'(k1_relat_1('#skF_4')), '#skF_3') | k1_relat_1('#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_2, c_116])).
% 2.22/1.28  tff(c_123, plain, (r2_hidden('#skF_1'(k1_relat_1('#skF_4')), '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_65, c_120])).
% 2.22/1.28  tff(c_4, plain, (![A_3, B_4]: (m1_subset_1(A_3, B_4) | ~r2_hidden(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.22/1.28  tff(c_137, plain, (m1_subset_1('#skF_1'(k1_relat_1('#skF_4')), '#skF_3')), inference(resolution, [status(thm)], [c_123, c_4])).
% 2.22/1.28  tff(c_124, plain, (![A_57, B_58, C_59]: (k1_relset_1(A_57, B_58, C_59)=k1_relat_1(C_59) | ~m1_subset_1(C_59, k1_zfmisc_1(k2_zfmisc_1(A_57, B_58))))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.22/1.28  tff(c_133, plain, (k1_relset_1('#skF_3', '#skF_2', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_32, c_124])).
% 2.22/1.28  tff(c_54, plain, (![D_42]: (~r2_hidden(D_42, k1_relset_1('#skF_3', '#skF_2', '#skF_4')) | ~m1_subset_1(D_42, '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_96])).
% 2.22/1.28  tff(c_59, plain, (~m1_subset_1('#skF_1'(k1_relset_1('#skF_3', '#skF_2', '#skF_4')), '#skF_3') | k1_relset_1('#skF_3', '#skF_2', '#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_2, c_54])).
% 2.22/1.28  tff(c_94, plain, (~m1_subset_1('#skF_1'(k1_relset_1('#skF_3', '#skF_2', '#skF_4')), '#skF_3')), inference(splitLeft, [status(thm)], [c_59])).
% 2.22/1.28  tff(c_138, plain, (~m1_subset_1('#skF_1'(k1_relat_1('#skF_4')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_133, c_94])).
% 2.22/1.28  tff(c_142, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_137, c_138])).
% 2.22/1.28  tff(c_143, plain, (k1_relset_1('#skF_3', '#skF_2', '#skF_4')=k1_xboole_0), inference(splitRight, [status(thm)], [c_59])).
% 2.22/1.28  tff(c_226, plain, (![A_76, B_77, C_78]: (k1_relset_1(A_76, B_77, C_78)=k1_relat_1(C_78) | ~m1_subset_1(C_78, k1_zfmisc_1(k2_zfmisc_1(A_76, B_77))))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.22/1.28  tff(c_233, plain, (k1_relset_1('#skF_3', '#skF_2', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_32, c_226])).
% 2.22/1.28  tff(c_236, plain, (k1_relat_1('#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_143, c_233])).
% 2.22/1.28  tff(c_238, plain, $false, inference(negUnitSimplification, [status(thm)], [c_65, c_236])).
% 2.22/1.28  tff(c_239, plain, (k2_relat_1('#skF_4')=k1_xboole_0), inference(splitRight, [status(thm)], [c_64])).
% 2.22/1.28  tff(c_349, plain, (![A_101, B_102, C_103]: (k2_relset_1(A_101, B_102, C_103)=k2_relat_1(C_103) | ~m1_subset_1(C_103, k1_zfmisc_1(k2_zfmisc_1(A_101, B_102))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.22/1.28  tff(c_356, plain, (k2_relset_1('#skF_3', '#skF_2', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_32, c_349])).
% 2.22/1.28  tff(c_359, plain, (k2_relset_1('#skF_3', '#skF_2', '#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_239, c_356])).
% 2.22/1.28  tff(c_361, plain, $false, inference(negUnitSimplification, [status(thm)], [c_30, c_359])).
% 2.22/1.28  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.22/1.28  
% 2.22/1.28  Inference rules
% 2.22/1.28  ----------------------
% 2.22/1.28  #Ref     : 0
% 2.22/1.28  #Sup     : 64
% 2.22/1.28  #Fact    : 0
% 2.22/1.28  #Define  : 0
% 2.22/1.28  #Split   : 3
% 2.22/1.28  #Chain   : 0
% 2.22/1.28  #Close   : 0
% 2.22/1.28  
% 2.22/1.28  Ordering : KBO
% 2.22/1.28  
% 2.22/1.28  Simplification rules
% 2.22/1.28  ----------------------
% 2.22/1.28  #Subsume      : 2
% 2.22/1.28  #Demod        : 23
% 2.22/1.28  #Tautology    : 19
% 2.22/1.28  #SimpNegUnit  : 5
% 2.22/1.28  #BackRed      : 6
% 2.22/1.28  
% 2.22/1.28  #Partial instantiations: 0
% 2.22/1.28  #Strategies tried      : 1
% 2.22/1.28  
% 2.22/1.28  Timing (in seconds)
% 2.22/1.28  ----------------------
% 2.22/1.28  Preprocessing        : 0.29
% 2.22/1.28  Parsing              : 0.15
% 2.22/1.28  CNF conversion       : 0.02
% 2.22/1.28  Main loop            : 0.23
% 2.22/1.28  Inferencing          : 0.09
% 2.22/1.28  Reduction            : 0.07
% 2.22/1.28  Demodulation         : 0.04
% 2.22/1.28  BG Simplification    : 0.01
% 2.22/1.28  Subsumption          : 0.03
% 2.22/1.28  Abstraction          : 0.02
% 2.22/1.28  MUC search           : 0.00
% 2.22/1.28  Cooper               : 0.00
% 2.22/1.28  Total                : 0.56
% 2.22/1.28  Index Insertion      : 0.00
% 2.22/1.28  Index Deletion       : 0.00
% 2.22/1.28  Index Matching       : 0.00
% 2.22/1.28  BG Taut test         : 0.00
%------------------------------------------------------------------------------
