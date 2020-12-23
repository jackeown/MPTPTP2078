%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:08:23 EST 2020

% Result     : Theorem 2.15s
% Output     : CNFRefutation 2.48s
% Verified   : 
% Statistics : Number of formulae       :   63 ( 117 expanded)
%              Number of leaves         :   30 (  53 expanded)
%              Depth                    :   11
%              Number of atoms          :   84 ( 230 expanded)
%              Number of equality atoms :   28 (  68 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_92,negated_conjecture,(
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

tff(f_57,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_63,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_53,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( k1_relat_1(A) = k1_xboole_0
      <=> k2_relat_1(A) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_relat_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ~ ( B != k1_xboole_0
          & ! [C] :
              ( m1_subset_1(C,A)
             => ~ r2_hidden(C,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_subset_1)).

tff(f_67,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_71,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(c_30,plain,(
    k2_relset_1('#skF_3','#skF_2','#skF_4') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_32,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_50,plain,(
    ! [C_40,A_41,B_42] :
      ( v1_relat_1(C_40)
      | ~ m1_subset_1(C_40,k1_zfmisc_1(k2_zfmisc_1(A_41,B_42))) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_59,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_32,c_50])).

tff(c_70,plain,(
    ! [C_43,A_44,B_45] :
      ( v4_relat_1(C_43,A_44)
      | ~ m1_subset_1(C_43,k1_zfmisc_1(k2_zfmisc_1(A_44,B_45))) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_79,plain,(
    v4_relat_1('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_32,c_70])).

tff(c_12,plain,(
    ! [B_7,A_6] :
      ( r1_tarski(k1_relat_1(B_7),A_6)
      | ~ v4_relat_1(B_7,A_6)
      | ~ v1_relat_1(B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_8,plain,(
    ! [A_4,B_5] :
      ( m1_subset_1(A_4,k1_zfmisc_1(B_5))
      | ~ r1_tarski(A_4,B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_14,plain,(
    ! [A_8] :
      ( k1_relat_1(A_8) = k1_xboole_0
      | k2_relat_1(A_8) != k1_xboole_0
      | ~ v1_relat_1(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_66,plain,
    ( k1_relat_1('#skF_4') = k1_xboole_0
    | k2_relat_1('#skF_4') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_59,c_14])).

tff(c_68,plain,(
    k2_relat_1('#skF_4') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_66])).

tff(c_16,plain,(
    ! [A_8] :
      ( k2_relat_1(A_8) = k1_xboole_0
      | k1_relat_1(A_8) != k1_xboole_0
      | ~ v1_relat_1(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_67,plain,
    ( k2_relat_1('#skF_4') = k1_xboole_0
    | k1_relat_1('#skF_4') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_59,c_16])).

tff(c_69,plain,(
    k1_relat_1('#skF_4') != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_67])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( m1_subset_1('#skF_1'(A_1,B_2),A_1)
      | k1_xboole_0 = B_2
      | ~ m1_subset_1(B_2,k1_zfmisc_1(A_1)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),B_2)
      | k1_xboole_0 = B_2
      | ~ m1_subset_1(B_2,k1_zfmisc_1(A_1)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_160,plain,(
    ! [A_75,B_76,C_77] :
      ( k1_relset_1(A_75,B_76,C_77) = k1_relat_1(C_77)
      | ~ m1_subset_1(C_77,k1_zfmisc_1(k2_zfmisc_1(A_75,B_76))) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_174,plain,(
    k1_relset_1('#skF_3','#skF_2','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_32,c_160])).

tff(c_28,plain,(
    ! [D_32] :
      ( ~ r2_hidden(D_32,k1_relset_1('#skF_3','#skF_2','#skF_4'))
      | ~ m1_subset_1(D_32,'#skF_3') ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_180,plain,(
    ! [D_78] :
      ( ~ r2_hidden(D_78,k1_relat_1('#skF_4'))
      | ~ m1_subset_1(D_78,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_174,c_28])).

tff(c_184,plain,(
    ! [A_1] :
      ( ~ m1_subset_1('#skF_1'(A_1,k1_relat_1('#skF_4')),'#skF_3')
      | k1_relat_1('#skF_4') = k1_xboole_0
      | ~ m1_subset_1(k1_relat_1('#skF_4'),k1_zfmisc_1(A_1)) ) ),
    inference(resolution,[status(thm)],[c_2,c_180])).

tff(c_199,plain,(
    ! [A_82] :
      ( ~ m1_subset_1('#skF_1'(A_82,k1_relat_1('#skF_4')),'#skF_3')
      | ~ m1_subset_1(k1_relat_1('#skF_4'),k1_zfmisc_1(A_82)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_69,c_184])).

tff(c_203,plain,
    ( k1_relat_1('#skF_4') = k1_xboole_0
    | ~ m1_subset_1(k1_relat_1('#skF_4'),k1_zfmisc_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_4,c_199])).

tff(c_206,plain,(
    ~ m1_subset_1(k1_relat_1('#skF_4'),k1_zfmisc_1('#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_69,c_203])).

tff(c_225,plain,(
    ~ r1_tarski(k1_relat_1('#skF_4'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_8,c_206])).

tff(c_228,plain,
    ( ~ v4_relat_1('#skF_4','#skF_3')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_12,c_225])).

tff(c_232,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_59,c_79,c_228])).

tff(c_233,plain,(
    k1_relat_1('#skF_4') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_66])).

tff(c_240,plain,(
    k2_relat_1('#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_233,c_67])).

tff(c_374,plain,(
    ! [A_120,B_121,C_122] :
      ( k2_relset_1(A_120,B_121,C_122) = k2_relat_1(C_122)
      | ~ m1_subset_1(C_122,k1_zfmisc_1(k2_zfmisc_1(A_120,B_121))) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_385,plain,(
    k2_relset_1('#skF_3','#skF_2','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_32,c_374])).

tff(c_389,plain,(
    k2_relset_1('#skF_3','#skF_2','#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_240,c_385])).

tff(c_391,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_389])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:11:29 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.15/1.32  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.48/1.32  
% 2.48/1.32  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.48/1.33  %$ v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 2.48/1.33  
% 2.48/1.33  %Foreground sorts:
% 2.48/1.33  
% 2.48/1.33  
% 2.48/1.33  %Background operators:
% 2.48/1.33  
% 2.48/1.33  
% 2.48/1.33  %Foreground operators:
% 2.48/1.33  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 2.48/1.33  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.48/1.33  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.48/1.33  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.48/1.33  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.48/1.33  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.48/1.33  tff('#skF_2', type, '#skF_2': $i).
% 2.48/1.33  tff('#skF_3', type, '#skF_3': $i).
% 2.48/1.33  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.48/1.33  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.48/1.33  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.48/1.33  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.48/1.33  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.48/1.33  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.48/1.33  tff('#skF_4', type, '#skF_4': $i).
% 2.48/1.33  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.48/1.33  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.48/1.33  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.48/1.33  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.48/1.33  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.48/1.33  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.48/1.33  
% 2.48/1.34  tff(f_92, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => ~(~(k2_relset_1(B, A, C) = k1_xboole_0) & (![D]: (m1_subset_1(D, B) => ~r2_hidden(D, k1_relset_1(B, A, C))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t50_relset_1)).
% 2.48/1.34  tff(f_57, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.48/1.34  tff(f_63, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.48/1.34  tff(f_47, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d18_relat_1)).
% 2.48/1.34  tff(f_41, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 2.48/1.34  tff(f_53, axiom, (![A]: (v1_relat_1(A) => ((k1_relat_1(A) = k1_xboole_0) <=> (k2_relat_1(A) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_relat_1)).
% 2.48/1.34  tff(f_37, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => ~(~(B = k1_xboole_0) & (![C]: (m1_subset_1(C, A) => ~r2_hidden(C, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_subset_1)).
% 2.48/1.34  tff(f_67, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.48/1.34  tff(f_71, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 2.48/1.34  tff(c_30, plain, (k2_relset_1('#skF_3', '#skF_2', '#skF_4')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.48/1.34  tff(c_32, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.48/1.34  tff(c_50, plain, (![C_40, A_41, B_42]: (v1_relat_1(C_40) | ~m1_subset_1(C_40, k1_zfmisc_1(k2_zfmisc_1(A_41, B_42))))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.48/1.34  tff(c_59, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_32, c_50])).
% 2.48/1.34  tff(c_70, plain, (![C_43, A_44, B_45]: (v4_relat_1(C_43, A_44) | ~m1_subset_1(C_43, k1_zfmisc_1(k2_zfmisc_1(A_44, B_45))))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.48/1.34  tff(c_79, plain, (v4_relat_1('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_32, c_70])).
% 2.48/1.34  tff(c_12, plain, (![B_7, A_6]: (r1_tarski(k1_relat_1(B_7), A_6) | ~v4_relat_1(B_7, A_6) | ~v1_relat_1(B_7))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.48/1.34  tff(c_8, plain, (![A_4, B_5]: (m1_subset_1(A_4, k1_zfmisc_1(B_5)) | ~r1_tarski(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.48/1.34  tff(c_14, plain, (![A_8]: (k1_relat_1(A_8)=k1_xboole_0 | k2_relat_1(A_8)!=k1_xboole_0 | ~v1_relat_1(A_8))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.48/1.34  tff(c_66, plain, (k1_relat_1('#skF_4')=k1_xboole_0 | k2_relat_1('#skF_4')!=k1_xboole_0), inference(resolution, [status(thm)], [c_59, c_14])).
% 2.48/1.34  tff(c_68, plain, (k2_relat_1('#skF_4')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_66])).
% 2.48/1.34  tff(c_16, plain, (![A_8]: (k2_relat_1(A_8)=k1_xboole_0 | k1_relat_1(A_8)!=k1_xboole_0 | ~v1_relat_1(A_8))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.48/1.34  tff(c_67, plain, (k2_relat_1('#skF_4')=k1_xboole_0 | k1_relat_1('#skF_4')!=k1_xboole_0), inference(resolution, [status(thm)], [c_59, c_16])).
% 2.48/1.34  tff(c_69, plain, (k1_relat_1('#skF_4')!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_68, c_67])).
% 2.48/1.34  tff(c_4, plain, (![A_1, B_2]: (m1_subset_1('#skF_1'(A_1, B_2), A_1) | k1_xboole_0=B_2 | ~m1_subset_1(B_2, k1_zfmisc_1(A_1)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.48/1.34  tff(c_2, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), B_2) | k1_xboole_0=B_2 | ~m1_subset_1(B_2, k1_zfmisc_1(A_1)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.48/1.34  tff(c_160, plain, (![A_75, B_76, C_77]: (k1_relset_1(A_75, B_76, C_77)=k1_relat_1(C_77) | ~m1_subset_1(C_77, k1_zfmisc_1(k2_zfmisc_1(A_75, B_76))))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.48/1.34  tff(c_174, plain, (k1_relset_1('#skF_3', '#skF_2', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_32, c_160])).
% 2.48/1.34  tff(c_28, plain, (![D_32]: (~r2_hidden(D_32, k1_relset_1('#skF_3', '#skF_2', '#skF_4')) | ~m1_subset_1(D_32, '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.48/1.34  tff(c_180, plain, (![D_78]: (~r2_hidden(D_78, k1_relat_1('#skF_4')) | ~m1_subset_1(D_78, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_174, c_28])).
% 2.48/1.34  tff(c_184, plain, (![A_1]: (~m1_subset_1('#skF_1'(A_1, k1_relat_1('#skF_4')), '#skF_3') | k1_relat_1('#skF_4')=k1_xboole_0 | ~m1_subset_1(k1_relat_1('#skF_4'), k1_zfmisc_1(A_1)))), inference(resolution, [status(thm)], [c_2, c_180])).
% 2.48/1.34  tff(c_199, plain, (![A_82]: (~m1_subset_1('#skF_1'(A_82, k1_relat_1('#skF_4')), '#skF_3') | ~m1_subset_1(k1_relat_1('#skF_4'), k1_zfmisc_1(A_82)))), inference(negUnitSimplification, [status(thm)], [c_69, c_184])).
% 2.48/1.34  tff(c_203, plain, (k1_relat_1('#skF_4')=k1_xboole_0 | ~m1_subset_1(k1_relat_1('#skF_4'), k1_zfmisc_1('#skF_3'))), inference(resolution, [status(thm)], [c_4, c_199])).
% 2.48/1.34  tff(c_206, plain, (~m1_subset_1(k1_relat_1('#skF_4'), k1_zfmisc_1('#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_69, c_203])).
% 2.48/1.34  tff(c_225, plain, (~r1_tarski(k1_relat_1('#skF_4'), '#skF_3')), inference(resolution, [status(thm)], [c_8, c_206])).
% 2.48/1.34  tff(c_228, plain, (~v4_relat_1('#skF_4', '#skF_3') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_12, c_225])).
% 2.48/1.34  tff(c_232, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_59, c_79, c_228])).
% 2.48/1.34  tff(c_233, plain, (k1_relat_1('#skF_4')=k1_xboole_0), inference(splitRight, [status(thm)], [c_66])).
% 2.48/1.34  tff(c_240, plain, (k2_relat_1('#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_233, c_67])).
% 2.48/1.34  tff(c_374, plain, (![A_120, B_121, C_122]: (k2_relset_1(A_120, B_121, C_122)=k2_relat_1(C_122) | ~m1_subset_1(C_122, k1_zfmisc_1(k2_zfmisc_1(A_120, B_121))))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.48/1.34  tff(c_385, plain, (k2_relset_1('#skF_3', '#skF_2', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_32, c_374])).
% 2.48/1.34  tff(c_389, plain, (k2_relset_1('#skF_3', '#skF_2', '#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_240, c_385])).
% 2.48/1.34  tff(c_391, plain, $false, inference(negUnitSimplification, [status(thm)], [c_30, c_389])).
% 2.48/1.34  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.48/1.34  
% 2.48/1.34  Inference rules
% 2.48/1.34  ----------------------
% 2.48/1.34  #Ref     : 0
% 2.48/1.34  #Sup     : 66
% 2.48/1.34  #Fact    : 0
% 2.48/1.34  #Define  : 0
% 2.48/1.34  #Split   : 2
% 2.48/1.34  #Chain   : 0
% 2.48/1.34  #Close   : 0
% 2.48/1.34  
% 2.48/1.34  Ordering : KBO
% 2.48/1.34  
% 2.48/1.34  Simplification rules
% 2.48/1.34  ----------------------
% 2.48/1.34  #Subsume      : 3
% 2.48/1.34  #Demod        : 21
% 2.48/1.34  #Tautology    : 18
% 2.48/1.34  #SimpNegUnit  : 4
% 2.48/1.34  #BackRed      : 1
% 2.48/1.34  
% 2.48/1.34  #Partial instantiations: 0
% 2.48/1.34  #Strategies tried      : 1
% 2.48/1.34  
% 2.48/1.34  Timing (in seconds)
% 2.48/1.34  ----------------------
% 2.48/1.35  Preprocessing        : 0.32
% 2.48/1.35  Parsing              : 0.17
% 2.48/1.35  CNF conversion       : 0.02
% 2.48/1.35  Main loop            : 0.25
% 2.48/1.35  Inferencing          : 0.11
% 2.48/1.35  Reduction            : 0.07
% 2.48/1.35  Demodulation         : 0.04
% 2.48/1.35  BG Simplification    : 0.02
% 2.48/1.35  Subsumption          : 0.04
% 2.48/1.35  Abstraction          : 0.02
% 2.48/1.35  MUC search           : 0.00
% 2.48/1.35  Cooper               : 0.00
% 2.48/1.35  Total                : 0.61
% 2.48/1.35  Index Insertion      : 0.00
% 2.48/1.35  Index Deletion       : 0.00
% 2.48/1.35  Index Matching       : 0.00
% 2.48/1.35  BG Taut test         : 0.00
%------------------------------------------------------------------------------
