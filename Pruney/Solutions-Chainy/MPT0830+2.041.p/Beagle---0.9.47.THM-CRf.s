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
% DateTime   : Thu Dec  3 10:07:31 EST 2020

% Result     : Theorem 2.28s
% Output     : CNFRefutation 2.28s
% Verified   : 
% Statistics : Number of formulae       :   66 ( 174 expanded)
%              Number of leaves         :   29 (  70 expanded)
%              Depth                    :   14
%              Number of atoms          :   93 ( 302 expanded)
%              Number of equality atoms :    3 (   6 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k5_relset_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_50,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_81,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,C)))
       => m1_subset_1(k5_relset_1(A,C,D,B),k1_zfmisc_1(k2_zfmisc_1(B,C))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t33_relset_1)).

tff(f_42,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_58,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k7_relat_1(B,A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_relat_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_64,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_48,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_54,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k1_relat_1(k7_relat_1(B,A)),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_relat_1)).

tff(f_76,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( ( r1_tarski(k1_relat_1(C),A)
          & r1_tarski(k2_relat_1(C),B) )
       => m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_relset_1)).

tff(f_68,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k5_relset_1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k5_relset_1)).

tff(c_14,plain,(
    ! [A_11,B_12] : v1_relat_1(k2_zfmisc_1(A_11,B_12)) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_30,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_44,plain,(
    ! [B_37,A_38] :
      ( v1_relat_1(B_37)
      | ~ m1_subset_1(B_37,k1_zfmisc_1(A_38))
      | ~ v1_relat_1(A_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_50,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_3')) ),
    inference(resolution,[status(thm)],[c_30,c_44])).

tff(c_54,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_50])).

tff(c_18,plain,(
    ! [B_16,A_15] :
      ( r1_tarski(k7_relat_1(B_16,A_15),B_16)
      | ~ v1_relat_1(B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_34,plain,(
    ! [A_33,B_34] :
      ( r1_tarski(A_33,B_34)
      | ~ m1_subset_1(A_33,k1_zfmisc_1(B_34)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_42,plain,(
    r1_tarski('#skF_4',k2_zfmisc_1('#skF_1','#skF_3')) ),
    inference(resolution,[status(thm)],[c_30,c_34])).

tff(c_86,plain,(
    ! [A_48,C_49,B_50] :
      ( r1_tarski(A_48,C_49)
      | ~ r1_tarski(B_50,C_49)
      | ~ r1_tarski(A_48,B_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_115,plain,(
    ! [A_57] :
      ( r1_tarski(A_57,k2_zfmisc_1('#skF_1','#skF_3'))
      | ~ r1_tarski(A_57,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_42,c_86])).

tff(c_6,plain,(
    ! [A_4,B_5] :
      ( m1_subset_1(A_4,k1_zfmisc_1(B_5))
      | ~ r1_tarski(A_4,B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_76,plain,(
    ! [C_45,B_46,A_47] :
      ( v5_relat_1(C_45,B_46)
      | ~ m1_subset_1(C_45,k1_zfmisc_1(k2_zfmisc_1(A_47,B_46))) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_84,plain,(
    ! [A_4,B_46,A_47] :
      ( v5_relat_1(A_4,B_46)
      | ~ r1_tarski(A_4,k2_zfmisc_1(A_47,B_46)) ) ),
    inference(resolution,[status(thm)],[c_6,c_76])).

tff(c_128,plain,(
    ! [A_57] :
      ( v5_relat_1(A_57,'#skF_3')
      | ~ r1_tarski(A_57,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_115,c_84])).

tff(c_51,plain,(
    ! [A_4,B_5] :
      ( v1_relat_1(A_4)
      | ~ v1_relat_1(B_5)
      | ~ r1_tarski(A_4,B_5) ) ),
    inference(resolution,[status(thm)],[c_6,c_44])).

tff(c_127,plain,(
    ! [A_57] :
      ( v1_relat_1(A_57)
      | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_3'))
      | ~ r1_tarski(A_57,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_115,c_51])).

tff(c_134,plain,(
    ! [A_58] :
      ( v1_relat_1(A_58)
      | ~ r1_tarski(A_58,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_127])).

tff(c_142,plain,(
    ! [A_15] :
      ( v1_relat_1(k7_relat_1('#skF_4',A_15))
      | ~ v1_relat_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_18,c_134])).

tff(c_146,plain,(
    ! [A_15] : v1_relat_1(k7_relat_1('#skF_4',A_15)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_142])).

tff(c_12,plain,(
    ! [B_10,A_9] :
      ( r1_tarski(k2_relat_1(B_10),A_9)
      | ~ v5_relat_1(B_10,A_9)
      | ~ v1_relat_1(B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_16,plain,(
    ! [B_14,A_13] :
      ( r1_tarski(k1_relat_1(k7_relat_1(B_14,A_13)),A_13)
      | ~ v1_relat_1(B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_293,plain,(
    ! [C_96,A_97,B_98] :
      ( m1_subset_1(C_96,k1_zfmisc_1(k2_zfmisc_1(A_97,B_98)))
      | ~ r1_tarski(k2_relat_1(C_96),B_98)
      | ~ r1_tarski(k1_relat_1(C_96),A_97)
      | ~ v1_relat_1(C_96) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_247,plain,(
    ! [A_85,B_86,C_87,D_88] :
      ( k5_relset_1(A_85,B_86,C_87,D_88) = k7_relat_1(C_87,D_88)
      | ~ m1_subset_1(C_87,k1_zfmisc_1(k2_zfmisc_1(A_85,B_86))) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_254,plain,(
    ! [D_88] : k5_relset_1('#skF_1','#skF_3','#skF_4',D_88) = k7_relat_1('#skF_4',D_88) ),
    inference(resolution,[status(thm)],[c_30,c_247])).

tff(c_28,plain,(
    ~ m1_subset_1(k5_relset_1('#skF_1','#skF_3','#skF_4','#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_256,plain,(
    ~ m1_subset_1(k7_relat_1('#skF_4','#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_254,c_28])).

tff(c_296,plain,
    ( ~ r1_tarski(k2_relat_1(k7_relat_1('#skF_4','#skF_2')),'#skF_3')
    | ~ r1_tarski(k1_relat_1(k7_relat_1('#skF_4','#skF_2')),'#skF_2')
    | ~ v1_relat_1(k7_relat_1('#skF_4','#skF_2')) ),
    inference(resolution,[status(thm)],[c_293,c_256])).

tff(c_313,plain,
    ( ~ r1_tarski(k2_relat_1(k7_relat_1('#skF_4','#skF_2')),'#skF_3')
    | ~ r1_tarski(k1_relat_1(k7_relat_1('#skF_4','#skF_2')),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_146,c_296])).

tff(c_364,plain,(
    ~ r1_tarski(k1_relat_1(k7_relat_1('#skF_4','#skF_2')),'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_313])).

tff(c_367,plain,(
    ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_16,c_364])).

tff(c_371,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_367])).

tff(c_372,plain,(
    ~ r1_tarski(k2_relat_1(k7_relat_1('#skF_4','#skF_2')),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_313])).

tff(c_376,plain,
    ( ~ v5_relat_1(k7_relat_1('#skF_4','#skF_2'),'#skF_3')
    | ~ v1_relat_1(k7_relat_1('#skF_4','#skF_2')) ),
    inference(resolution,[status(thm)],[c_12,c_372])).

tff(c_379,plain,(
    ~ v5_relat_1(k7_relat_1('#skF_4','#skF_2'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_146,c_376])).

tff(c_383,plain,(
    ~ r1_tarski(k7_relat_1('#skF_4','#skF_2'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_128,c_379])).

tff(c_386,plain,(
    ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_18,c_383])).

tff(c_390,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_386])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:32:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.28/1.40  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.28/1.41  
% 2.28/1.41  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.28/1.41  %$ v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k5_relset_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.28/1.41  
% 2.28/1.41  %Foreground sorts:
% 2.28/1.41  
% 2.28/1.41  
% 2.28/1.41  %Background operators:
% 2.28/1.41  
% 2.28/1.41  
% 2.28/1.41  %Foreground operators:
% 2.28/1.41  tff(k5_relset_1, type, k5_relset_1: ($i * $i * $i * $i) > $i).
% 2.28/1.41  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.28/1.41  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.28/1.41  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.28/1.41  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.28/1.41  tff('#skF_2', type, '#skF_2': $i).
% 2.28/1.41  tff('#skF_3', type, '#skF_3': $i).
% 2.28/1.41  tff('#skF_1', type, '#skF_1': $i).
% 2.28/1.41  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.28/1.41  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.28/1.41  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.28/1.41  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.28/1.41  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.28/1.41  tff('#skF_4', type, '#skF_4': $i).
% 2.28/1.41  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.28/1.41  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.28/1.41  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.28/1.41  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.28/1.41  
% 2.28/1.43  tff(f_50, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 2.28/1.43  tff(f_81, negated_conjecture, ~(![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, C))) => m1_subset_1(k5_relset_1(A, C, D, B), k1_zfmisc_1(k2_zfmisc_1(B, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t33_relset_1)).
% 2.28/1.43  tff(f_42, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 2.28/1.43  tff(f_58, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k7_relat_1(B, A), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t88_relat_1)).
% 2.28/1.43  tff(f_35, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 2.28/1.43  tff(f_31, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 2.28/1.43  tff(f_64, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.28/1.43  tff(f_48, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 2.28/1.43  tff(f_54, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k7_relat_1(B, A)), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t87_relat_1)).
% 2.28/1.43  tff(f_76, axiom, (![A, B, C]: (v1_relat_1(C) => ((r1_tarski(k1_relat_1(C), A) & r1_tarski(k2_relat_1(C), B)) => m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_relset_1)).
% 2.28/1.43  tff(f_68, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k5_relset_1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k5_relset_1)).
% 2.28/1.43  tff(c_14, plain, (![A_11, B_12]: (v1_relat_1(k2_zfmisc_1(A_11, B_12)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.28/1.43  tff(c_30, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.28/1.43  tff(c_44, plain, (![B_37, A_38]: (v1_relat_1(B_37) | ~m1_subset_1(B_37, k1_zfmisc_1(A_38)) | ~v1_relat_1(A_38))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.28/1.43  tff(c_50, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_3'))), inference(resolution, [status(thm)], [c_30, c_44])).
% 2.28/1.43  tff(c_54, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_14, c_50])).
% 2.28/1.43  tff(c_18, plain, (![B_16, A_15]: (r1_tarski(k7_relat_1(B_16, A_15), B_16) | ~v1_relat_1(B_16))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.28/1.43  tff(c_34, plain, (![A_33, B_34]: (r1_tarski(A_33, B_34) | ~m1_subset_1(A_33, k1_zfmisc_1(B_34)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.28/1.43  tff(c_42, plain, (r1_tarski('#skF_4', k2_zfmisc_1('#skF_1', '#skF_3'))), inference(resolution, [status(thm)], [c_30, c_34])).
% 2.28/1.43  tff(c_86, plain, (![A_48, C_49, B_50]: (r1_tarski(A_48, C_49) | ~r1_tarski(B_50, C_49) | ~r1_tarski(A_48, B_50))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.28/1.43  tff(c_115, plain, (![A_57]: (r1_tarski(A_57, k2_zfmisc_1('#skF_1', '#skF_3')) | ~r1_tarski(A_57, '#skF_4'))), inference(resolution, [status(thm)], [c_42, c_86])).
% 2.28/1.43  tff(c_6, plain, (![A_4, B_5]: (m1_subset_1(A_4, k1_zfmisc_1(B_5)) | ~r1_tarski(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.28/1.43  tff(c_76, plain, (![C_45, B_46, A_47]: (v5_relat_1(C_45, B_46) | ~m1_subset_1(C_45, k1_zfmisc_1(k2_zfmisc_1(A_47, B_46))))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.28/1.43  tff(c_84, plain, (![A_4, B_46, A_47]: (v5_relat_1(A_4, B_46) | ~r1_tarski(A_4, k2_zfmisc_1(A_47, B_46)))), inference(resolution, [status(thm)], [c_6, c_76])).
% 2.28/1.43  tff(c_128, plain, (![A_57]: (v5_relat_1(A_57, '#skF_3') | ~r1_tarski(A_57, '#skF_4'))), inference(resolution, [status(thm)], [c_115, c_84])).
% 2.28/1.43  tff(c_51, plain, (![A_4, B_5]: (v1_relat_1(A_4) | ~v1_relat_1(B_5) | ~r1_tarski(A_4, B_5))), inference(resolution, [status(thm)], [c_6, c_44])).
% 2.28/1.43  tff(c_127, plain, (![A_57]: (v1_relat_1(A_57) | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_3')) | ~r1_tarski(A_57, '#skF_4'))), inference(resolution, [status(thm)], [c_115, c_51])).
% 2.28/1.43  tff(c_134, plain, (![A_58]: (v1_relat_1(A_58) | ~r1_tarski(A_58, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_127])).
% 2.28/1.43  tff(c_142, plain, (![A_15]: (v1_relat_1(k7_relat_1('#skF_4', A_15)) | ~v1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_18, c_134])).
% 2.28/1.43  tff(c_146, plain, (![A_15]: (v1_relat_1(k7_relat_1('#skF_4', A_15)))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_142])).
% 2.28/1.43  tff(c_12, plain, (![B_10, A_9]: (r1_tarski(k2_relat_1(B_10), A_9) | ~v5_relat_1(B_10, A_9) | ~v1_relat_1(B_10))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.28/1.43  tff(c_16, plain, (![B_14, A_13]: (r1_tarski(k1_relat_1(k7_relat_1(B_14, A_13)), A_13) | ~v1_relat_1(B_14))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.28/1.43  tff(c_293, plain, (![C_96, A_97, B_98]: (m1_subset_1(C_96, k1_zfmisc_1(k2_zfmisc_1(A_97, B_98))) | ~r1_tarski(k2_relat_1(C_96), B_98) | ~r1_tarski(k1_relat_1(C_96), A_97) | ~v1_relat_1(C_96))), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.28/1.43  tff(c_247, plain, (![A_85, B_86, C_87, D_88]: (k5_relset_1(A_85, B_86, C_87, D_88)=k7_relat_1(C_87, D_88) | ~m1_subset_1(C_87, k1_zfmisc_1(k2_zfmisc_1(A_85, B_86))))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.28/1.43  tff(c_254, plain, (![D_88]: (k5_relset_1('#skF_1', '#skF_3', '#skF_4', D_88)=k7_relat_1('#skF_4', D_88))), inference(resolution, [status(thm)], [c_30, c_247])).
% 2.28/1.43  tff(c_28, plain, (~m1_subset_1(k5_relset_1('#skF_1', '#skF_3', '#skF_4', '#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.28/1.43  tff(c_256, plain, (~m1_subset_1(k7_relat_1('#skF_4', '#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_254, c_28])).
% 2.28/1.43  tff(c_296, plain, (~r1_tarski(k2_relat_1(k7_relat_1('#skF_4', '#skF_2')), '#skF_3') | ~r1_tarski(k1_relat_1(k7_relat_1('#skF_4', '#skF_2')), '#skF_2') | ~v1_relat_1(k7_relat_1('#skF_4', '#skF_2'))), inference(resolution, [status(thm)], [c_293, c_256])).
% 2.28/1.43  tff(c_313, plain, (~r1_tarski(k2_relat_1(k7_relat_1('#skF_4', '#skF_2')), '#skF_3') | ~r1_tarski(k1_relat_1(k7_relat_1('#skF_4', '#skF_2')), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_146, c_296])).
% 2.28/1.43  tff(c_364, plain, (~r1_tarski(k1_relat_1(k7_relat_1('#skF_4', '#skF_2')), '#skF_2')), inference(splitLeft, [status(thm)], [c_313])).
% 2.28/1.43  tff(c_367, plain, (~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_16, c_364])).
% 2.28/1.43  tff(c_371, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_54, c_367])).
% 2.28/1.43  tff(c_372, plain, (~r1_tarski(k2_relat_1(k7_relat_1('#skF_4', '#skF_2')), '#skF_3')), inference(splitRight, [status(thm)], [c_313])).
% 2.28/1.43  tff(c_376, plain, (~v5_relat_1(k7_relat_1('#skF_4', '#skF_2'), '#skF_3') | ~v1_relat_1(k7_relat_1('#skF_4', '#skF_2'))), inference(resolution, [status(thm)], [c_12, c_372])).
% 2.28/1.43  tff(c_379, plain, (~v5_relat_1(k7_relat_1('#skF_4', '#skF_2'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_146, c_376])).
% 2.28/1.43  tff(c_383, plain, (~r1_tarski(k7_relat_1('#skF_4', '#skF_2'), '#skF_4')), inference(resolution, [status(thm)], [c_128, c_379])).
% 2.28/1.43  tff(c_386, plain, (~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_18, c_383])).
% 2.28/1.43  tff(c_390, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_54, c_386])).
% 2.28/1.43  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.28/1.43  
% 2.28/1.43  Inference rules
% 2.28/1.43  ----------------------
% 2.28/1.43  #Ref     : 0
% 2.28/1.43  #Sup     : 71
% 2.28/1.43  #Fact    : 0
% 2.28/1.43  #Define  : 0
% 2.28/1.43  #Split   : 2
% 2.28/1.43  #Chain   : 0
% 2.28/1.43  #Close   : 0
% 2.28/1.43  
% 2.28/1.43  Ordering : KBO
% 2.28/1.43  
% 2.28/1.43  Simplification rules
% 2.28/1.43  ----------------------
% 2.28/1.43  #Subsume      : 7
% 2.28/1.43  #Demod        : 19
% 2.28/1.43  #Tautology    : 9
% 2.28/1.43  #SimpNegUnit  : 0
% 2.28/1.43  #BackRed      : 2
% 2.28/1.43  
% 2.28/1.43  #Partial instantiations: 0
% 2.28/1.43  #Strategies tried      : 1
% 2.28/1.43  
% 2.28/1.43  Timing (in seconds)
% 2.28/1.43  ----------------------
% 2.28/1.43  Preprocessing        : 0.36
% 2.28/1.43  Parsing              : 0.19
% 2.28/1.43  CNF conversion       : 0.02
% 2.28/1.43  Main loop            : 0.25
% 2.28/1.43  Inferencing          : 0.10
% 2.28/1.43  Reduction            : 0.07
% 2.28/1.43  Demodulation         : 0.05
% 2.28/1.43  BG Simplification    : 0.01
% 2.28/1.43  Subsumption          : 0.05
% 2.28/1.43  Abstraction          : 0.01
% 2.28/1.43  MUC search           : 0.00
% 2.28/1.43  Cooper               : 0.00
% 2.28/1.43  Total                : 0.64
% 2.28/1.43  Index Insertion      : 0.00
% 2.28/1.43  Index Deletion       : 0.00
% 2.28/1.43  Index Matching       : 0.00
% 2.28/1.43  BG Taut test         : 0.00
%------------------------------------------------------------------------------
