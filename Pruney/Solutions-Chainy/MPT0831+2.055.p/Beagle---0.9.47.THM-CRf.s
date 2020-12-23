%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:07:39 EST 2020

% Result     : Theorem 2.21s
% Output     : CNFRefutation 2.21s
% Verified   : 
% Statistics : Number of formulae       :   64 (  95 expanded)
%              Number of leaves         :   29 (  44 expanded)
%              Depth                    :   13
%              Number of atoms          :   89 ( 154 expanded)
%              Number of equality atoms :   10 (  10 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k5_relset_1 > k1_relset_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k5_relset_1,type,(
    k5_relset_1: ( $i * $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_relset_1,type,(
    r2_relset_1: ( $i * $i * $i * $i ) > $o )).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_81,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,A)))
       => ( r1_tarski(B,C)
         => r2_relset_1(B,A,k5_relset_1(B,A,D,C),D) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_relset_1)).

tff(f_42,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_64,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_60,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k1_relset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_relset_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_48,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_56,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_68,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k5_relset_1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k5_relset_1)).

tff(f_74,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => r2_relset_1(A,B,C,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',reflexivity_r2_relset_1)).

tff(c_14,plain,(
    ! [A_11,B_12] : v1_relat_1(k2_zfmisc_1(A_11,B_12)) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_30,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_42,plain,(
    ! [B_35,A_36] :
      ( v1_relat_1(B_35)
      | ~ m1_subset_1(B_35,k1_zfmisc_1(A_36))
      | ~ v1_relat_1(A_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_48,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_1')) ),
    inference(resolution,[status(thm)],[c_30,c_42])).

tff(c_52,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_48])).

tff(c_155,plain,(
    ! [A_59,B_60,C_61] :
      ( k1_relset_1(A_59,B_60,C_61) = k1_relat_1(C_61)
      | ~ m1_subset_1(C_61,k1_zfmisc_1(k2_zfmisc_1(A_59,B_60))) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_164,plain,(
    k1_relset_1('#skF_2','#skF_1','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_30,c_155])).

tff(c_217,plain,(
    ! [A_73,B_74,C_75] :
      ( m1_subset_1(k1_relset_1(A_73,B_74,C_75),k1_zfmisc_1(A_73))
      | ~ m1_subset_1(C_75,k1_zfmisc_1(k2_zfmisc_1(A_73,B_74))) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_230,plain,
    ( m1_subset_1(k1_relat_1('#skF_4'),k1_zfmisc_1('#skF_2'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_164,c_217])).

tff(c_235,plain,(
    m1_subset_1(k1_relat_1('#skF_4'),k1_zfmisc_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_230])).

tff(c_4,plain,(
    ! [A_4,B_5] :
      ( r1_tarski(A_4,B_5)
      | ~ m1_subset_1(A_4,k1_zfmisc_1(B_5)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_243,plain,(
    r1_tarski(k1_relat_1('#skF_4'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_235,c_4])).

tff(c_10,plain,(
    ! [B_10,A_9] :
      ( v4_relat_1(B_10,A_9)
      | ~ r1_tarski(k1_relat_1(B_10),A_9)
      | ~ v1_relat_1(B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_253,plain,
    ( v4_relat_1('#skF_4','#skF_2')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_243,c_10])).

tff(c_262,plain,(
    v4_relat_1('#skF_4','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_253])).

tff(c_12,plain,(
    ! [B_10,A_9] :
      ( r1_tarski(k1_relat_1(B_10),A_9)
      | ~ v4_relat_1(B_10,A_9)
      | ~ v1_relat_1(B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_28,plain,(
    r1_tarski('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_76,plain,(
    ! [A_45,C_46,B_47] :
      ( r1_tarski(A_45,C_46)
      | ~ r1_tarski(B_47,C_46)
      | ~ r1_tarski(A_45,B_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_86,plain,(
    ! [A_48] :
      ( r1_tarski(A_48,'#skF_3')
      | ~ r1_tarski(A_48,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_28,c_76])).

tff(c_113,plain,(
    ! [B_51] :
      ( r1_tarski(k1_relat_1(B_51),'#skF_3')
      | ~ v4_relat_1(B_51,'#skF_2')
      | ~ v1_relat_1(B_51) ) ),
    inference(resolution,[status(thm)],[c_12,c_86])).

tff(c_123,plain,(
    ! [B_51] :
      ( v4_relat_1(B_51,'#skF_3')
      | ~ v4_relat_1(B_51,'#skF_2')
      | ~ v1_relat_1(B_51) ) ),
    inference(resolution,[status(thm)],[c_113,c_10])).

tff(c_268,plain,
    ( v4_relat_1('#skF_4','#skF_3')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_262,c_123])).

tff(c_277,plain,(
    v4_relat_1('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_268])).

tff(c_16,plain,(
    ! [B_14,A_13] :
      ( k7_relat_1(B_14,A_13) = B_14
      | ~ v4_relat_1(B_14,A_13)
      | ~ v1_relat_1(B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_301,plain,
    ( k7_relat_1('#skF_4','#skF_3') = '#skF_4'
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_277,c_16])).

tff(c_307,plain,(
    k7_relat_1('#skF_4','#skF_3') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_301])).

tff(c_318,plain,(
    ! [A_76,B_77,C_78,D_79] :
      ( k5_relset_1(A_76,B_77,C_78,D_79) = k7_relat_1(C_78,D_79)
      | ~ m1_subset_1(C_78,k1_zfmisc_1(k2_zfmisc_1(A_76,B_77))) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_329,plain,(
    ! [D_79] : k5_relset_1('#skF_2','#skF_1','#skF_4',D_79) = k7_relat_1('#skF_4',D_79) ),
    inference(resolution,[status(thm)],[c_30,c_318])).

tff(c_26,plain,(
    ~ r2_relset_1('#skF_2','#skF_1',k5_relset_1('#skF_2','#skF_1','#skF_4','#skF_3'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_330,plain,(
    ~ r2_relset_1('#skF_2','#skF_1',k7_relat_1('#skF_4','#skF_3'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_329,c_26])).

tff(c_331,plain,(
    ~ r2_relset_1('#skF_2','#skF_1','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_307,c_330])).

tff(c_354,plain,(
    ! [A_83,B_84,C_85,D_86] :
      ( r2_relset_1(A_83,B_84,C_85,C_85)
      | ~ m1_subset_1(D_86,k1_zfmisc_1(k2_zfmisc_1(A_83,B_84)))
      | ~ m1_subset_1(C_85,k1_zfmisc_1(k2_zfmisc_1(A_83,B_84))) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_368,plain,(
    ! [C_89] :
      ( r2_relset_1('#skF_2','#skF_1',C_89,C_89)
      | ~ m1_subset_1(C_89,k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ) ),
    inference(resolution,[status(thm)],[c_30,c_354])).

tff(c_376,plain,(
    r2_relset_1('#skF_2','#skF_1','#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_30,c_368])).

tff(c_382,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_331,c_376])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n021.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 12:46:49 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.21/1.31  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.21/1.32  
% 2.21/1.32  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.21/1.32  %$ r2_relset_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k5_relset_1 > k1_relset_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.21/1.32  
% 2.21/1.32  %Foreground sorts:
% 2.21/1.32  
% 2.21/1.32  
% 2.21/1.32  %Background operators:
% 2.21/1.32  
% 2.21/1.32  
% 2.21/1.32  %Foreground operators:
% 2.21/1.32  tff(k5_relset_1, type, k5_relset_1: ($i * $i * $i * $i) > $i).
% 2.21/1.32  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.21/1.32  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 2.21/1.32  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.21/1.32  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.21/1.32  tff('#skF_2', type, '#skF_2': $i).
% 2.21/1.32  tff('#skF_3', type, '#skF_3': $i).
% 2.21/1.32  tff('#skF_1', type, '#skF_1': $i).
% 2.21/1.32  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.21/1.32  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.21/1.32  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.21/1.32  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.21/1.32  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.21/1.32  tff('#skF_4', type, '#skF_4': $i).
% 2.21/1.32  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.21/1.32  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.21/1.32  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.21/1.32  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.21/1.32  
% 2.21/1.34  tff(f_50, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 2.21/1.34  tff(f_81, negated_conjecture, ~(![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A))) => (r1_tarski(B, C) => r2_relset_1(B, A, k5_relset_1(B, A, D, C), D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t34_relset_1)).
% 2.21/1.34  tff(f_42, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 2.21/1.34  tff(f_64, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.21/1.34  tff(f_60, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k1_relset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_relset_1)).
% 2.21/1.34  tff(f_35, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 2.21/1.34  tff(f_48, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d18_relat_1)).
% 2.21/1.34  tff(f_31, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 2.21/1.34  tff(f_56, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t209_relat_1)).
% 2.21/1.34  tff(f_68, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k5_relset_1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k5_relset_1)).
% 2.21/1.34  tff(f_74, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => r2_relset_1(A, B, C, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', reflexivity_r2_relset_1)).
% 2.21/1.34  tff(c_14, plain, (![A_11, B_12]: (v1_relat_1(k2_zfmisc_1(A_11, B_12)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.21/1.34  tff(c_30, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.21/1.34  tff(c_42, plain, (![B_35, A_36]: (v1_relat_1(B_35) | ~m1_subset_1(B_35, k1_zfmisc_1(A_36)) | ~v1_relat_1(A_36))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.21/1.34  tff(c_48, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_1'))), inference(resolution, [status(thm)], [c_30, c_42])).
% 2.21/1.34  tff(c_52, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_14, c_48])).
% 2.21/1.34  tff(c_155, plain, (![A_59, B_60, C_61]: (k1_relset_1(A_59, B_60, C_61)=k1_relat_1(C_61) | ~m1_subset_1(C_61, k1_zfmisc_1(k2_zfmisc_1(A_59, B_60))))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.21/1.34  tff(c_164, plain, (k1_relset_1('#skF_2', '#skF_1', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_30, c_155])).
% 2.21/1.34  tff(c_217, plain, (![A_73, B_74, C_75]: (m1_subset_1(k1_relset_1(A_73, B_74, C_75), k1_zfmisc_1(A_73)) | ~m1_subset_1(C_75, k1_zfmisc_1(k2_zfmisc_1(A_73, B_74))))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.21/1.34  tff(c_230, plain, (m1_subset_1(k1_relat_1('#skF_4'), k1_zfmisc_1('#skF_2')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_164, c_217])).
% 2.21/1.34  tff(c_235, plain, (m1_subset_1(k1_relat_1('#skF_4'), k1_zfmisc_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_230])).
% 2.21/1.34  tff(c_4, plain, (![A_4, B_5]: (r1_tarski(A_4, B_5) | ~m1_subset_1(A_4, k1_zfmisc_1(B_5)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.21/1.34  tff(c_243, plain, (r1_tarski(k1_relat_1('#skF_4'), '#skF_2')), inference(resolution, [status(thm)], [c_235, c_4])).
% 2.21/1.34  tff(c_10, plain, (![B_10, A_9]: (v4_relat_1(B_10, A_9) | ~r1_tarski(k1_relat_1(B_10), A_9) | ~v1_relat_1(B_10))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.21/1.34  tff(c_253, plain, (v4_relat_1('#skF_4', '#skF_2') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_243, c_10])).
% 2.21/1.34  tff(c_262, plain, (v4_relat_1('#skF_4', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_253])).
% 2.21/1.34  tff(c_12, plain, (![B_10, A_9]: (r1_tarski(k1_relat_1(B_10), A_9) | ~v4_relat_1(B_10, A_9) | ~v1_relat_1(B_10))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.21/1.34  tff(c_28, plain, (r1_tarski('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.21/1.34  tff(c_76, plain, (![A_45, C_46, B_47]: (r1_tarski(A_45, C_46) | ~r1_tarski(B_47, C_46) | ~r1_tarski(A_45, B_47))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.21/1.34  tff(c_86, plain, (![A_48]: (r1_tarski(A_48, '#skF_3') | ~r1_tarski(A_48, '#skF_2'))), inference(resolution, [status(thm)], [c_28, c_76])).
% 2.21/1.34  tff(c_113, plain, (![B_51]: (r1_tarski(k1_relat_1(B_51), '#skF_3') | ~v4_relat_1(B_51, '#skF_2') | ~v1_relat_1(B_51))), inference(resolution, [status(thm)], [c_12, c_86])).
% 2.21/1.34  tff(c_123, plain, (![B_51]: (v4_relat_1(B_51, '#skF_3') | ~v4_relat_1(B_51, '#skF_2') | ~v1_relat_1(B_51))), inference(resolution, [status(thm)], [c_113, c_10])).
% 2.21/1.34  tff(c_268, plain, (v4_relat_1('#skF_4', '#skF_3') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_262, c_123])).
% 2.21/1.34  tff(c_277, plain, (v4_relat_1('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_268])).
% 2.21/1.34  tff(c_16, plain, (![B_14, A_13]: (k7_relat_1(B_14, A_13)=B_14 | ~v4_relat_1(B_14, A_13) | ~v1_relat_1(B_14))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.21/1.34  tff(c_301, plain, (k7_relat_1('#skF_4', '#skF_3')='#skF_4' | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_277, c_16])).
% 2.21/1.34  tff(c_307, plain, (k7_relat_1('#skF_4', '#skF_3')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_52, c_301])).
% 2.21/1.34  tff(c_318, plain, (![A_76, B_77, C_78, D_79]: (k5_relset_1(A_76, B_77, C_78, D_79)=k7_relat_1(C_78, D_79) | ~m1_subset_1(C_78, k1_zfmisc_1(k2_zfmisc_1(A_76, B_77))))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.21/1.34  tff(c_329, plain, (![D_79]: (k5_relset_1('#skF_2', '#skF_1', '#skF_4', D_79)=k7_relat_1('#skF_4', D_79))), inference(resolution, [status(thm)], [c_30, c_318])).
% 2.21/1.34  tff(c_26, plain, (~r2_relset_1('#skF_2', '#skF_1', k5_relset_1('#skF_2', '#skF_1', '#skF_4', '#skF_3'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.21/1.34  tff(c_330, plain, (~r2_relset_1('#skF_2', '#skF_1', k7_relat_1('#skF_4', '#skF_3'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_329, c_26])).
% 2.21/1.34  tff(c_331, plain, (~r2_relset_1('#skF_2', '#skF_1', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_307, c_330])).
% 2.21/1.34  tff(c_354, plain, (![A_83, B_84, C_85, D_86]: (r2_relset_1(A_83, B_84, C_85, C_85) | ~m1_subset_1(D_86, k1_zfmisc_1(k2_zfmisc_1(A_83, B_84))) | ~m1_subset_1(C_85, k1_zfmisc_1(k2_zfmisc_1(A_83, B_84))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.21/1.34  tff(c_368, plain, (![C_89]: (r2_relset_1('#skF_2', '#skF_1', C_89, C_89) | ~m1_subset_1(C_89, k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))))), inference(resolution, [status(thm)], [c_30, c_354])).
% 2.21/1.34  tff(c_376, plain, (r2_relset_1('#skF_2', '#skF_1', '#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_30, c_368])).
% 2.21/1.34  tff(c_382, plain, $false, inference(negUnitSimplification, [status(thm)], [c_331, c_376])).
% 2.21/1.34  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.21/1.34  
% 2.21/1.34  Inference rules
% 2.21/1.34  ----------------------
% 2.21/1.34  #Ref     : 0
% 2.21/1.34  #Sup     : 76
% 2.21/1.34  #Fact    : 0
% 2.21/1.34  #Define  : 0
% 2.21/1.34  #Split   : 4
% 2.21/1.34  #Chain   : 0
% 2.21/1.34  #Close   : 0
% 2.21/1.34  
% 2.21/1.34  Ordering : KBO
% 2.21/1.34  
% 2.21/1.34  Simplification rules
% 2.21/1.34  ----------------------
% 2.21/1.34  #Subsume      : 8
% 2.21/1.34  #Demod        : 18
% 2.21/1.34  #Tautology    : 16
% 2.21/1.34  #SimpNegUnit  : 1
% 2.21/1.34  #BackRed      : 1
% 2.21/1.34  
% 2.21/1.34  #Partial instantiations: 0
% 2.21/1.34  #Strategies tried      : 1
% 2.21/1.34  
% 2.21/1.34  Timing (in seconds)
% 2.21/1.34  ----------------------
% 2.21/1.34  Preprocessing        : 0.29
% 2.21/1.34  Parsing              : 0.16
% 2.21/1.34  CNF conversion       : 0.02
% 2.21/1.34  Main loop            : 0.26
% 2.21/1.34  Inferencing          : 0.10
% 2.21/1.34  Reduction            : 0.07
% 2.21/1.34  Demodulation         : 0.05
% 2.21/1.34  BG Simplification    : 0.01
% 2.21/1.34  Subsumption          : 0.05
% 2.21/1.34  Abstraction          : 0.01
% 2.21/1.34  MUC search           : 0.00
% 2.21/1.34  Cooper               : 0.00
% 2.21/1.34  Total                : 0.58
% 2.21/1.34  Index Insertion      : 0.00
% 2.21/1.34  Index Deletion       : 0.00
% 2.21/1.34  Index Matching       : 0.00
% 2.21/1.34  BG Taut test         : 0.00
%------------------------------------------------------------------------------
