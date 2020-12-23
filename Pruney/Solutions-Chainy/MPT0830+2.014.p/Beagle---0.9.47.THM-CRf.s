%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:07:27 EST 2020

% Result     : Theorem 8.08s
% Output     : CNFRefutation 8.08s
% Verified   : 
% Statistics : Number of formulae       :   53 (  76 expanded)
%              Number of leaves         :   27 (  38 expanded)
%              Depth                    :    8
%              Number of atoms          :   76 ( 117 expanded)
%              Number of equality atoms :    3 (   3 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k5_relset_1 > k7_relat_1 > k3_xboole_0 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k5_relset_1,type,(
    k5_relset_1: ( $i * $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_86,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,C)))
       => m1_subset_1(k5_relset_1(A,C,D,B),k1_zfmisc_1(k2_zfmisc_1(B,C))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t33_relset_1)).

tff(f_59,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_65,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v4_relat_1(C,B) )
     => ( v1_relat_1(k7_relat_1(C,A))
        & v4_relat_1(k7_relat_1(C,A),A)
        & v4_relat_1(k7_relat_1(C,A),B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc23_relat_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k7_relat_1(B,A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_relat_1)).

tff(f_81,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,C)))
     => ( r1_tarski(A,D)
       => m1_subset_1(A,k1_zfmisc_1(k2_zfmisc_1(B,C))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_relset_1)).

tff(f_75,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,C)))
     => ( r1_tarski(k1_relat_1(D),B)
       => m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,C))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_relset_1)).

tff(f_69,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k5_relset_1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k5_relset_1)).

tff(c_32,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_34,plain,(
    ! [C_33,A_34,B_35] :
      ( v1_relat_1(C_33)
      | ~ m1_subset_1(C_33,k1_zfmisc_1(k2_zfmisc_1(A_34,B_35))) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_38,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_32,c_34])).

tff(c_52,plain,(
    ! [C_48,A_49,B_50] :
      ( v4_relat_1(C_48,A_49)
      | ~ m1_subset_1(C_48,k1_zfmisc_1(k2_zfmisc_1(A_49,B_50))) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_56,plain,(
    v4_relat_1('#skF_4','#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_52])).

tff(c_10,plain,(
    ! [C_5,A_3,B_4] :
      ( v1_relat_1(k7_relat_1(C_5,A_3))
      | ~ v4_relat_1(C_5,B_4)
      | ~ v1_relat_1(C_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_61,plain,(
    ! [A_3] :
      ( v1_relat_1(k7_relat_1('#skF_4',A_3))
      | ~ v1_relat_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_56,c_10])).

tff(c_67,plain,(
    ! [A_3] : v1_relat_1(k7_relat_1('#skF_4',A_3)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_61])).

tff(c_77,plain,(
    ! [C_51,A_52,B_53] :
      ( v4_relat_1(k7_relat_1(C_51,A_52),A_52)
      | ~ v4_relat_1(C_51,B_53)
      | ~ v1_relat_1(C_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_79,plain,(
    ! [A_52] :
      ( v4_relat_1(k7_relat_1('#skF_4',A_52),A_52)
      | ~ v1_relat_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_56,c_77])).

tff(c_82,plain,(
    ! [A_52] : v4_relat_1(k7_relat_1('#skF_4',A_52),A_52) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_79])).

tff(c_4,plain,(
    ! [B_2,A_1] :
      ( r1_tarski(k1_relat_1(B_2),A_1)
      | ~ v4_relat_1(B_2,A_1)
      | ~ v1_relat_1(B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_16,plain,(
    ! [B_12,A_11] :
      ( r1_tarski(k7_relat_1(B_12,A_11),B_12)
      | ~ v1_relat_1(B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_847,plain,(
    ! [A_97,B_98,C_99,D_100] :
      ( m1_subset_1(A_97,k1_zfmisc_1(k2_zfmisc_1(B_98,C_99)))
      | ~ r1_tarski(A_97,D_100)
      | ~ m1_subset_1(D_100,k1_zfmisc_1(k2_zfmisc_1(B_98,C_99))) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_3331,plain,(
    ! [B_151,A_152,B_153,C_154] :
      ( m1_subset_1(k7_relat_1(B_151,A_152),k1_zfmisc_1(k2_zfmisc_1(B_153,C_154)))
      | ~ m1_subset_1(B_151,k1_zfmisc_1(k2_zfmisc_1(B_153,C_154)))
      | ~ v1_relat_1(B_151) ) ),
    inference(resolution,[status(thm)],[c_16,c_847])).

tff(c_26,plain,(
    ! [D_26,B_24,C_25,A_23] :
      ( m1_subset_1(D_26,k1_zfmisc_1(k2_zfmisc_1(B_24,C_25)))
      | ~ r1_tarski(k1_relat_1(D_26),B_24)
      | ~ m1_subset_1(D_26,k1_zfmisc_1(k2_zfmisc_1(A_23,C_25))) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_11980,plain,(
    ! [A_293,B_296,B_297,C_295,B_294] :
      ( m1_subset_1(k7_relat_1(B_296,A_293),k1_zfmisc_1(k2_zfmisc_1(B_294,C_295)))
      | ~ r1_tarski(k1_relat_1(k7_relat_1(B_296,A_293)),B_294)
      | ~ m1_subset_1(B_296,k1_zfmisc_1(k2_zfmisc_1(B_297,C_295)))
      | ~ v1_relat_1(B_296) ) ),
    inference(resolution,[status(thm)],[c_3331,c_26])).

tff(c_11992,plain,(
    ! [A_293,B_294] :
      ( m1_subset_1(k7_relat_1('#skF_4',A_293),k1_zfmisc_1(k2_zfmisc_1(B_294,'#skF_3')))
      | ~ r1_tarski(k1_relat_1(k7_relat_1('#skF_4',A_293)),B_294)
      | ~ v1_relat_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_32,c_11980])).

tff(c_12128,plain,(
    ! [A_299,B_300] :
      ( m1_subset_1(k7_relat_1('#skF_4',A_299),k1_zfmisc_1(k2_zfmisc_1(B_300,'#skF_3')))
      | ~ r1_tarski(k1_relat_1(k7_relat_1('#skF_4',A_299)),B_300) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_11992])).

tff(c_541,plain,(
    ! [A_83,B_84,C_85,D_86] :
      ( k5_relset_1(A_83,B_84,C_85,D_86) = k7_relat_1(C_85,D_86)
      | ~ m1_subset_1(C_85,k1_zfmisc_1(k2_zfmisc_1(A_83,B_84))) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_544,plain,(
    ! [D_86] : k5_relset_1('#skF_1','#skF_3','#skF_4',D_86) = k7_relat_1('#skF_4',D_86) ),
    inference(resolution,[status(thm)],[c_32,c_541])).

tff(c_30,plain,(
    ~ m1_subset_1(k5_relset_1('#skF_1','#skF_3','#skF_4','#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_545,plain,(
    ~ m1_subset_1(k7_relat_1('#skF_4','#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_544,c_30])).

tff(c_12234,plain,(
    ~ r1_tarski(k1_relat_1(k7_relat_1('#skF_4','#skF_2')),'#skF_2') ),
    inference(resolution,[status(thm)],[c_12128,c_545])).

tff(c_12263,plain,
    ( ~ v4_relat_1(k7_relat_1('#skF_4','#skF_2'),'#skF_2')
    | ~ v1_relat_1(k7_relat_1('#skF_4','#skF_2')) ),
    inference(resolution,[status(thm)],[c_4,c_12234])).

tff(c_12267,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_67,c_82,c_12263])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:16:04 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.08/2.92  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.08/2.93  
% 8.08/2.93  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.08/2.93  %$ v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k5_relset_1 > k7_relat_1 > k3_xboole_0 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 8.08/2.93  
% 8.08/2.93  %Foreground sorts:
% 8.08/2.93  
% 8.08/2.93  
% 8.08/2.93  %Background operators:
% 8.08/2.93  
% 8.08/2.93  
% 8.08/2.93  %Foreground operators:
% 8.08/2.93  tff(k5_relset_1, type, k5_relset_1: ($i * $i * $i * $i) > $i).
% 8.08/2.93  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.08/2.93  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 8.08/2.93  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 8.08/2.93  tff('#skF_2', type, '#skF_2': $i).
% 8.08/2.93  tff('#skF_3', type, '#skF_3': $i).
% 8.08/2.93  tff('#skF_1', type, '#skF_1': $i).
% 8.08/2.93  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 8.08/2.93  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 8.08/2.93  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.08/2.93  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 8.08/2.93  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 8.08/2.93  tff('#skF_4', type, '#skF_4': $i).
% 8.08/2.93  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.08/2.93  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 8.08/2.93  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 8.08/2.93  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 8.08/2.93  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 8.08/2.93  
% 8.08/2.94  tff(f_86, negated_conjecture, ~(![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, C))) => m1_subset_1(k5_relset_1(A, C, D, B), k1_zfmisc_1(k2_zfmisc_1(B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t33_relset_1)).
% 8.08/2.94  tff(f_59, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 8.08/2.94  tff(f_65, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 8.08/2.94  tff(f_41, axiom, (![A, B, C]: ((v1_relat_1(C) & v4_relat_1(C, B)) => ((v1_relat_1(k7_relat_1(C, A)) & v4_relat_1(k7_relat_1(C, A), A)) & v4_relat_1(k7_relat_1(C, A), B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc23_relat_1)).
% 8.08/2.94  tff(f_31, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d18_relat_1)).
% 8.08/2.94  tff(f_55, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k7_relat_1(B, A), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t88_relat_1)).
% 8.08/2.94  tff(f_81, axiom, (![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C))) => (r1_tarski(A, D) => m1_subset_1(A, k1_zfmisc_1(k2_zfmisc_1(B, C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_relset_1)).
% 8.08/2.94  tff(f_75, axiom, (![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, C))) => (r1_tarski(k1_relat_1(D), B) => m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t13_relset_1)).
% 8.08/2.94  tff(f_69, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k5_relset_1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k5_relset_1)).
% 8.08/2.94  tff(c_32, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_86])).
% 8.08/2.94  tff(c_34, plain, (![C_33, A_34, B_35]: (v1_relat_1(C_33) | ~m1_subset_1(C_33, k1_zfmisc_1(k2_zfmisc_1(A_34, B_35))))), inference(cnfTransformation, [status(thm)], [f_59])).
% 8.08/2.94  tff(c_38, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_32, c_34])).
% 8.08/2.94  tff(c_52, plain, (![C_48, A_49, B_50]: (v4_relat_1(C_48, A_49) | ~m1_subset_1(C_48, k1_zfmisc_1(k2_zfmisc_1(A_49, B_50))))), inference(cnfTransformation, [status(thm)], [f_65])).
% 8.08/2.94  tff(c_56, plain, (v4_relat_1('#skF_4', '#skF_1')), inference(resolution, [status(thm)], [c_32, c_52])).
% 8.08/2.94  tff(c_10, plain, (![C_5, A_3, B_4]: (v1_relat_1(k7_relat_1(C_5, A_3)) | ~v4_relat_1(C_5, B_4) | ~v1_relat_1(C_5))), inference(cnfTransformation, [status(thm)], [f_41])).
% 8.08/2.94  tff(c_61, plain, (![A_3]: (v1_relat_1(k7_relat_1('#skF_4', A_3)) | ~v1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_56, c_10])).
% 8.08/2.94  tff(c_67, plain, (![A_3]: (v1_relat_1(k7_relat_1('#skF_4', A_3)))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_61])).
% 8.08/2.94  tff(c_77, plain, (![C_51, A_52, B_53]: (v4_relat_1(k7_relat_1(C_51, A_52), A_52) | ~v4_relat_1(C_51, B_53) | ~v1_relat_1(C_51))), inference(cnfTransformation, [status(thm)], [f_41])).
% 8.08/2.94  tff(c_79, plain, (![A_52]: (v4_relat_1(k7_relat_1('#skF_4', A_52), A_52) | ~v1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_56, c_77])).
% 8.08/2.94  tff(c_82, plain, (![A_52]: (v4_relat_1(k7_relat_1('#skF_4', A_52), A_52))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_79])).
% 8.08/2.94  tff(c_4, plain, (![B_2, A_1]: (r1_tarski(k1_relat_1(B_2), A_1) | ~v4_relat_1(B_2, A_1) | ~v1_relat_1(B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 8.08/2.94  tff(c_16, plain, (![B_12, A_11]: (r1_tarski(k7_relat_1(B_12, A_11), B_12) | ~v1_relat_1(B_12))), inference(cnfTransformation, [status(thm)], [f_55])).
% 8.08/2.94  tff(c_847, plain, (![A_97, B_98, C_99, D_100]: (m1_subset_1(A_97, k1_zfmisc_1(k2_zfmisc_1(B_98, C_99))) | ~r1_tarski(A_97, D_100) | ~m1_subset_1(D_100, k1_zfmisc_1(k2_zfmisc_1(B_98, C_99))))), inference(cnfTransformation, [status(thm)], [f_81])).
% 8.08/2.94  tff(c_3331, plain, (![B_151, A_152, B_153, C_154]: (m1_subset_1(k7_relat_1(B_151, A_152), k1_zfmisc_1(k2_zfmisc_1(B_153, C_154))) | ~m1_subset_1(B_151, k1_zfmisc_1(k2_zfmisc_1(B_153, C_154))) | ~v1_relat_1(B_151))), inference(resolution, [status(thm)], [c_16, c_847])).
% 8.08/2.94  tff(c_26, plain, (![D_26, B_24, C_25, A_23]: (m1_subset_1(D_26, k1_zfmisc_1(k2_zfmisc_1(B_24, C_25))) | ~r1_tarski(k1_relat_1(D_26), B_24) | ~m1_subset_1(D_26, k1_zfmisc_1(k2_zfmisc_1(A_23, C_25))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 8.08/2.94  tff(c_11980, plain, (![A_293, B_296, B_297, C_295, B_294]: (m1_subset_1(k7_relat_1(B_296, A_293), k1_zfmisc_1(k2_zfmisc_1(B_294, C_295))) | ~r1_tarski(k1_relat_1(k7_relat_1(B_296, A_293)), B_294) | ~m1_subset_1(B_296, k1_zfmisc_1(k2_zfmisc_1(B_297, C_295))) | ~v1_relat_1(B_296))), inference(resolution, [status(thm)], [c_3331, c_26])).
% 8.08/2.94  tff(c_11992, plain, (![A_293, B_294]: (m1_subset_1(k7_relat_1('#skF_4', A_293), k1_zfmisc_1(k2_zfmisc_1(B_294, '#skF_3'))) | ~r1_tarski(k1_relat_1(k7_relat_1('#skF_4', A_293)), B_294) | ~v1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_32, c_11980])).
% 8.08/2.94  tff(c_12128, plain, (![A_299, B_300]: (m1_subset_1(k7_relat_1('#skF_4', A_299), k1_zfmisc_1(k2_zfmisc_1(B_300, '#skF_3'))) | ~r1_tarski(k1_relat_1(k7_relat_1('#skF_4', A_299)), B_300))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_11992])).
% 8.08/2.94  tff(c_541, plain, (![A_83, B_84, C_85, D_86]: (k5_relset_1(A_83, B_84, C_85, D_86)=k7_relat_1(C_85, D_86) | ~m1_subset_1(C_85, k1_zfmisc_1(k2_zfmisc_1(A_83, B_84))))), inference(cnfTransformation, [status(thm)], [f_69])).
% 8.08/2.94  tff(c_544, plain, (![D_86]: (k5_relset_1('#skF_1', '#skF_3', '#skF_4', D_86)=k7_relat_1('#skF_4', D_86))), inference(resolution, [status(thm)], [c_32, c_541])).
% 8.08/2.94  tff(c_30, plain, (~m1_subset_1(k5_relset_1('#skF_1', '#skF_3', '#skF_4', '#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_86])).
% 8.08/2.94  tff(c_545, plain, (~m1_subset_1(k7_relat_1('#skF_4', '#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_544, c_30])).
% 8.08/2.94  tff(c_12234, plain, (~r1_tarski(k1_relat_1(k7_relat_1('#skF_4', '#skF_2')), '#skF_2')), inference(resolution, [status(thm)], [c_12128, c_545])).
% 8.08/2.94  tff(c_12263, plain, (~v4_relat_1(k7_relat_1('#skF_4', '#skF_2'), '#skF_2') | ~v1_relat_1(k7_relat_1('#skF_4', '#skF_2'))), inference(resolution, [status(thm)], [c_4, c_12234])).
% 8.08/2.94  tff(c_12267, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_67, c_82, c_12263])).
% 8.08/2.94  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.08/2.94  
% 8.08/2.94  Inference rules
% 8.08/2.94  ----------------------
% 8.08/2.94  #Ref     : 0
% 8.08/2.94  #Sup     : 3106
% 8.08/2.94  #Fact    : 0
% 8.08/2.94  #Define  : 0
% 8.08/2.94  #Split   : 0
% 8.08/2.94  #Chain   : 0
% 8.08/2.94  #Close   : 0
% 8.08/2.94  
% 8.08/2.94  Ordering : KBO
% 8.08/2.94  
% 8.08/2.94  Simplification rules
% 8.08/2.94  ----------------------
% 8.08/2.94  #Subsume      : 141
% 8.08/2.94  #Demod        : 3883
% 8.08/2.94  #Tautology    : 1537
% 8.08/2.94  #SimpNegUnit  : 0
% 8.08/2.94  #BackRed      : 13
% 8.08/2.94  
% 8.08/2.94  #Partial instantiations: 0
% 8.08/2.94  #Strategies tried      : 1
% 8.08/2.94  
% 8.08/2.94  Timing (in seconds)
% 8.08/2.94  ----------------------
% 8.08/2.94  Preprocessing        : 0.31
% 8.08/2.94  Parsing              : 0.17
% 8.08/2.94  CNF conversion       : 0.02
% 8.08/2.94  Main loop            : 1.88
% 8.08/2.94  Inferencing          : 0.45
% 8.08/2.94  Reduction            : 0.86
% 8.08/2.94  Demodulation         : 0.71
% 8.08/2.94  BG Simplification    : 0.05
% 8.08/2.94  Subsumption          : 0.39
% 8.08/2.94  Abstraction          : 0.08
% 8.08/2.94  MUC search           : 0.00
% 8.08/2.94  Cooper               : 0.00
% 8.08/2.94  Total                : 2.21
% 8.08/2.94  Index Insertion      : 0.00
% 8.08/2.94  Index Deletion       : 0.00
% 8.08/2.94  Index Matching       : 0.00
% 8.08/2.94  BG Taut test         : 0.00
%------------------------------------------------------------------------------
