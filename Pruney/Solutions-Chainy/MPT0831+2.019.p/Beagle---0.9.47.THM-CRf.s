%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:07:35 EST 2020

% Result     : Theorem 3.08s
% Output     : CNFRefutation 3.16s
% Verified   : 
% Statistics : Number of formulae       :   60 (  79 expanded)
%              Number of leaves         :   27 (  38 expanded)
%              Depth                    :   12
%              Number of atoms          :   87 ( 127 expanded)
%              Number of equality atoms :    8 (   8 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k5_relset_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_83,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,A)))
       => ( r1_tarski(B,C)
         => r2_relset_1(B,A,k5_relset_1(B,A,D,C),D) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_relset_1)).

tff(f_76,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_64,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => ( r1_tarski(k2_zfmisc_1(A,C),k2_zfmisc_1(B,C))
        & r1_tarski(k2_zfmisc_1(C,A),k2_zfmisc_1(C,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t118_zfmisc_1)).

tff(f_54,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(A,B)
           => ( r1_tarski(k1_relat_1(A),k1_relat_1(B))
              & r1_tarski(k2_relat_1(A),k2_relat_1(B)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_relat_1)).

tff(f_43,axiom,(
    ! [A,B] : r1_tarski(k1_relat_1(k2_zfmisc_1(A,B)),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t193_relat_1)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_60,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k1_relat_1(B),A)
       => k7_relat_1(B,A) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t97_relat_1)).

tff(f_68,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k5_relset_1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k5_relset_1)).

tff(c_32,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_250,plain,(
    ! [A_88,B_89,D_90] :
      ( r2_relset_1(A_88,B_89,D_90,D_90)
      | ~ m1_subset_1(D_90,k1_zfmisc_1(k2_zfmisc_1(A_88,B_89))) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_257,plain,(
    r2_relset_1('#skF_2','#skF_1','#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_32,c_250])).

tff(c_44,plain,(
    ! [C_33,A_34,B_35] :
      ( v1_relat_1(C_33)
      | ~ m1_subset_1(C_33,k1_zfmisc_1(k2_zfmisc_1(A_34,B_35))) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_53,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_32,c_44])).

tff(c_35,plain,(
    ! [A_31,B_32] :
      ( r1_tarski(A_31,B_32)
      | ~ m1_subset_1(A_31,k1_zfmisc_1(B_32)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_43,plain,(
    r1_tarski('#skF_4',k2_zfmisc_1('#skF_2','#skF_1')) ),
    inference(resolution,[status(thm)],[c_32,c_35])).

tff(c_30,plain,(
    r1_tarski('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_178,plain,(
    ! [A_67,C_68,B_69] :
      ( r1_tarski(k2_zfmisc_1(A_67,C_68),k2_zfmisc_1(B_69,C_68))
      | ~ r1_tarski(A_67,B_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_10,plain,(
    ! [A_7,B_8] :
      ( m1_subset_1(A_7,k1_zfmisc_1(B_8))
      | ~ r1_tarski(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_52,plain,(
    ! [A_7,A_34,B_35] :
      ( v1_relat_1(A_7)
      | ~ r1_tarski(A_7,k2_zfmisc_1(A_34,B_35)) ) ),
    inference(resolution,[status(thm)],[c_10,c_44])).

tff(c_217,plain,(
    ! [A_77,C_78,B_79] :
      ( v1_relat_1(k2_zfmisc_1(A_77,C_78))
      | ~ r1_tarski(A_77,B_79) ) ),
    inference(resolution,[status(thm)],[c_178,c_52])).

tff(c_244,plain,(
    ! [C_78] : v1_relat_1(k2_zfmisc_1('#skF_2',C_78)) ),
    inference(resolution,[status(thm)],[c_30,c_217])).

tff(c_347,plain,(
    ! [A_111,B_112] :
      ( r1_tarski(k1_relat_1(A_111),k1_relat_1(B_112))
      | ~ r1_tarski(A_111,B_112)
      | ~ v1_relat_1(B_112)
      | ~ v1_relat_1(A_111) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_12,plain,(
    ! [A_9,B_10] : r1_tarski(k1_relat_1(k2_zfmisc_1(A_9,B_10)),A_9) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_66,plain,(
    ! [A_42,C_43,B_44] :
      ( r1_tarski(A_42,C_43)
      | ~ r1_tarski(B_44,C_43)
      | ~ r1_tarski(A_42,B_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_76,plain,(
    ! [A_45] :
      ( r1_tarski(A_45,'#skF_3')
      | ~ r1_tarski(A_45,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_30,c_66])).

tff(c_82,plain,(
    ! [B_46] : r1_tarski(k1_relat_1(k2_zfmisc_1('#skF_2',B_46)),'#skF_3') ),
    inference(resolution,[status(thm)],[c_12,c_76])).

tff(c_2,plain,(
    ! [A_1,C_3,B_2] :
      ( r1_tarski(A_1,C_3)
      | ~ r1_tarski(B_2,C_3)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_85,plain,(
    ! [A_1,B_46] :
      ( r1_tarski(A_1,'#skF_3')
      | ~ r1_tarski(A_1,k1_relat_1(k2_zfmisc_1('#skF_2',B_46))) ) ),
    inference(resolution,[status(thm)],[c_82,c_2])).

tff(c_361,plain,(
    ! [A_111,B_46] :
      ( r1_tarski(k1_relat_1(A_111),'#skF_3')
      | ~ r1_tarski(A_111,k2_zfmisc_1('#skF_2',B_46))
      | ~ v1_relat_1(k2_zfmisc_1('#skF_2',B_46))
      | ~ v1_relat_1(A_111) ) ),
    inference(resolution,[status(thm)],[c_347,c_85])).

tff(c_663,plain,(
    ! [A_194,B_195] :
      ( r1_tarski(k1_relat_1(A_194),'#skF_3')
      | ~ r1_tarski(A_194,k2_zfmisc_1('#skF_2',B_195))
      | ~ v1_relat_1(A_194) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_244,c_361])).

tff(c_678,plain,
    ( r1_tarski(k1_relat_1('#skF_4'),'#skF_3')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_43,c_663])).

tff(c_693,plain,(
    r1_tarski(k1_relat_1('#skF_4'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_53,c_678])).

tff(c_18,plain,(
    ! [B_15,A_14] :
      ( k7_relat_1(B_15,A_14) = B_15
      | ~ r1_tarski(k1_relat_1(B_15),A_14)
      | ~ v1_relat_1(B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_717,plain,
    ( k7_relat_1('#skF_4','#skF_3') = '#skF_4'
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_693,c_18])).

tff(c_731,plain,(
    k7_relat_1('#skF_4','#skF_3') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_53,c_717])).

tff(c_475,plain,(
    ! [A_153,B_154,C_155,D_156] :
      ( k5_relset_1(A_153,B_154,C_155,D_156) = k7_relat_1(C_155,D_156)
      | ~ m1_subset_1(C_155,k1_zfmisc_1(k2_zfmisc_1(A_153,B_154))) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_482,plain,(
    ! [D_156] : k5_relset_1('#skF_2','#skF_1','#skF_4',D_156) = k7_relat_1('#skF_4',D_156) ),
    inference(resolution,[status(thm)],[c_32,c_475])).

tff(c_28,plain,(
    ~ r2_relset_1('#skF_2','#skF_1',k5_relset_1('#skF_2','#skF_1','#skF_4','#skF_3'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_483,plain,(
    ~ r2_relset_1('#skF_2','#skF_1',k7_relat_1('#skF_4','#skF_3'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_482,c_28])).

tff(c_742,plain,(
    ~ r2_relset_1('#skF_2','#skF_1','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_731,c_483])).

tff(c_745,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_257,c_742])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.35  % Computer   : n008.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 10:08:15 EST 2020
% 0.15/0.36  % CPUTime    : 
% 0.15/0.37  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.08/1.45  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.08/1.46  
% 3.08/1.46  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.16/1.46  %$ r2_relset_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k5_relset_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 3.16/1.46  
% 3.16/1.46  %Foreground sorts:
% 3.16/1.46  
% 3.16/1.46  
% 3.16/1.46  %Background operators:
% 3.16/1.46  
% 3.16/1.46  
% 3.16/1.46  %Foreground operators:
% 3.16/1.46  tff(k5_relset_1, type, k5_relset_1: ($i * $i * $i * $i) > $i).
% 3.16/1.46  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.16/1.46  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 3.16/1.46  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 3.16/1.46  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.16/1.46  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.16/1.46  tff('#skF_2', type, '#skF_2': $i).
% 3.16/1.46  tff('#skF_3', type, '#skF_3': $i).
% 3.16/1.46  tff('#skF_1', type, '#skF_1': $i).
% 3.16/1.46  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.16/1.46  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.16/1.46  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.16/1.46  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.16/1.46  tff('#skF_4', type, '#skF_4': $i).
% 3.16/1.46  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.16/1.46  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.16/1.46  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.16/1.46  
% 3.16/1.47  tff(f_83, negated_conjecture, ~(![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A))) => (r1_tarski(B, C) => r2_relset_1(B, A, k5_relset_1(B, A, D, C), D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t34_relset_1)).
% 3.16/1.47  tff(f_76, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 3.16/1.47  tff(f_64, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.16/1.47  tff(f_41, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 3.16/1.47  tff(f_37, axiom, (![A, B, C]: (r1_tarski(A, B) => (r1_tarski(k2_zfmisc_1(A, C), k2_zfmisc_1(B, C)) & r1_tarski(k2_zfmisc_1(C, A), k2_zfmisc_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t118_zfmisc_1)).
% 3.16/1.47  tff(f_54, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(A, B) => (r1_tarski(k1_relat_1(A), k1_relat_1(B)) & r1_tarski(k2_relat_1(A), k2_relat_1(B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t25_relat_1)).
% 3.16/1.47  tff(f_43, axiom, (![A, B]: r1_tarski(k1_relat_1(k2_zfmisc_1(A, B)), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t193_relat_1)).
% 3.16/1.47  tff(f_31, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 3.16/1.47  tff(f_60, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(B), A) => (k7_relat_1(B, A) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t97_relat_1)).
% 3.16/1.47  tff(f_68, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k5_relset_1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k5_relset_1)).
% 3.16/1.47  tff(c_32, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.16/1.47  tff(c_250, plain, (![A_88, B_89, D_90]: (r2_relset_1(A_88, B_89, D_90, D_90) | ~m1_subset_1(D_90, k1_zfmisc_1(k2_zfmisc_1(A_88, B_89))))), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.16/1.47  tff(c_257, plain, (r2_relset_1('#skF_2', '#skF_1', '#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_32, c_250])).
% 3.16/1.47  tff(c_44, plain, (![C_33, A_34, B_35]: (v1_relat_1(C_33) | ~m1_subset_1(C_33, k1_zfmisc_1(k2_zfmisc_1(A_34, B_35))))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.16/1.47  tff(c_53, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_32, c_44])).
% 3.16/1.47  tff(c_35, plain, (![A_31, B_32]: (r1_tarski(A_31, B_32) | ~m1_subset_1(A_31, k1_zfmisc_1(B_32)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.16/1.47  tff(c_43, plain, (r1_tarski('#skF_4', k2_zfmisc_1('#skF_2', '#skF_1'))), inference(resolution, [status(thm)], [c_32, c_35])).
% 3.16/1.47  tff(c_30, plain, (r1_tarski('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.16/1.47  tff(c_178, plain, (![A_67, C_68, B_69]: (r1_tarski(k2_zfmisc_1(A_67, C_68), k2_zfmisc_1(B_69, C_68)) | ~r1_tarski(A_67, B_69))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.16/1.47  tff(c_10, plain, (![A_7, B_8]: (m1_subset_1(A_7, k1_zfmisc_1(B_8)) | ~r1_tarski(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.16/1.47  tff(c_52, plain, (![A_7, A_34, B_35]: (v1_relat_1(A_7) | ~r1_tarski(A_7, k2_zfmisc_1(A_34, B_35)))), inference(resolution, [status(thm)], [c_10, c_44])).
% 3.16/1.47  tff(c_217, plain, (![A_77, C_78, B_79]: (v1_relat_1(k2_zfmisc_1(A_77, C_78)) | ~r1_tarski(A_77, B_79))), inference(resolution, [status(thm)], [c_178, c_52])).
% 3.16/1.47  tff(c_244, plain, (![C_78]: (v1_relat_1(k2_zfmisc_1('#skF_2', C_78)))), inference(resolution, [status(thm)], [c_30, c_217])).
% 3.16/1.47  tff(c_347, plain, (![A_111, B_112]: (r1_tarski(k1_relat_1(A_111), k1_relat_1(B_112)) | ~r1_tarski(A_111, B_112) | ~v1_relat_1(B_112) | ~v1_relat_1(A_111))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.16/1.47  tff(c_12, plain, (![A_9, B_10]: (r1_tarski(k1_relat_1(k2_zfmisc_1(A_9, B_10)), A_9))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.16/1.47  tff(c_66, plain, (![A_42, C_43, B_44]: (r1_tarski(A_42, C_43) | ~r1_tarski(B_44, C_43) | ~r1_tarski(A_42, B_44))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.16/1.47  tff(c_76, plain, (![A_45]: (r1_tarski(A_45, '#skF_3') | ~r1_tarski(A_45, '#skF_2'))), inference(resolution, [status(thm)], [c_30, c_66])).
% 3.16/1.47  tff(c_82, plain, (![B_46]: (r1_tarski(k1_relat_1(k2_zfmisc_1('#skF_2', B_46)), '#skF_3'))), inference(resolution, [status(thm)], [c_12, c_76])).
% 3.16/1.47  tff(c_2, plain, (![A_1, C_3, B_2]: (r1_tarski(A_1, C_3) | ~r1_tarski(B_2, C_3) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.16/1.47  tff(c_85, plain, (![A_1, B_46]: (r1_tarski(A_1, '#skF_3') | ~r1_tarski(A_1, k1_relat_1(k2_zfmisc_1('#skF_2', B_46))))), inference(resolution, [status(thm)], [c_82, c_2])).
% 3.16/1.47  tff(c_361, plain, (![A_111, B_46]: (r1_tarski(k1_relat_1(A_111), '#skF_3') | ~r1_tarski(A_111, k2_zfmisc_1('#skF_2', B_46)) | ~v1_relat_1(k2_zfmisc_1('#skF_2', B_46)) | ~v1_relat_1(A_111))), inference(resolution, [status(thm)], [c_347, c_85])).
% 3.16/1.47  tff(c_663, plain, (![A_194, B_195]: (r1_tarski(k1_relat_1(A_194), '#skF_3') | ~r1_tarski(A_194, k2_zfmisc_1('#skF_2', B_195)) | ~v1_relat_1(A_194))), inference(demodulation, [status(thm), theory('equality')], [c_244, c_361])).
% 3.16/1.47  tff(c_678, plain, (r1_tarski(k1_relat_1('#skF_4'), '#skF_3') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_43, c_663])).
% 3.16/1.47  tff(c_693, plain, (r1_tarski(k1_relat_1('#skF_4'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_53, c_678])).
% 3.16/1.47  tff(c_18, plain, (![B_15, A_14]: (k7_relat_1(B_15, A_14)=B_15 | ~r1_tarski(k1_relat_1(B_15), A_14) | ~v1_relat_1(B_15))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.16/1.47  tff(c_717, plain, (k7_relat_1('#skF_4', '#skF_3')='#skF_4' | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_693, c_18])).
% 3.16/1.47  tff(c_731, plain, (k7_relat_1('#skF_4', '#skF_3')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_53, c_717])).
% 3.16/1.47  tff(c_475, plain, (![A_153, B_154, C_155, D_156]: (k5_relset_1(A_153, B_154, C_155, D_156)=k7_relat_1(C_155, D_156) | ~m1_subset_1(C_155, k1_zfmisc_1(k2_zfmisc_1(A_153, B_154))))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.16/1.47  tff(c_482, plain, (![D_156]: (k5_relset_1('#skF_2', '#skF_1', '#skF_4', D_156)=k7_relat_1('#skF_4', D_156))), inference(resolution, [status(thm)], [c_32, c_475])).
% 3.16/1.47  tff(c_28, plain, (~r2_relset_1('#skF_2', '#skF_1', k5_relset_1('#skF_2', '#skF_1', '#skF_4', '#skF_3'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.16/1.47  tff(c_483, plain, (~r2_relset_1('#skF_2', '#skF_1', k7_relat_1('#skF_4', '#skF_3'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_482, c_28])).
% 3.16/1.47  tff(c_742, plain, (~r2_relset_1('#skF_2', '#skF_1', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_731, c_483])).
% 3.16/1.47  tff(c_745, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_257, c_742])).
% 3.16/1.47  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.16/1.47  
% 3.16/1.47  Inference rules
% 3.16/1.47  ----------------------
% 3.16/1.47  #Ref     : 0
% 3.16/1.47  #Sup     : 183
% 3.16/1.47  #Fact    : 0
% 3.16/1.47  #Define  : 0
% 3.16/1.47  #Split   : 1
% 3.16/1.47  #Chain   : 0
% 3.16/1.47  #Close   : 0
% 3.16/1.47  
% 3.16/1.47  Ordering : KBO
% 3.16/1.47  
% 3.16/1.47  Simplification rules
% 3.16/1.47  ----------------------
% 3.16/1.47  #Subsume      : 12
% 3.16/1.47  #Demod        : 31
% 3.16/1.47  #Tautology    : 28
% 3.16/1.48  #SimpNegUnit  : 0
% 3.16/1.48  #BackRed      : 2
% 3.16/1.48  
% 3.16/1.48  #Partial instantiations: 0
% 3.16/1.48  #Strategies tried      : 1
% 3.16/1.48  
% 3.16/1.48  Timing (in seconds)
% 3.16/1.48  ----------------------
% 3.16/1.48  Preprocessing        : 0.30
% 3.16/1.48  Parsing              : 0.16
% 3.16/1.48  CNF conversion       : 0.02
% 3.16/1.48  Main loop            : 0.40
% 3.16/1.48  Inferencing          : 0.14
% 3.16/1.48  Reduction            : 0.12
% 3.16/1.48  Demodulation         : 0.09
% 3.16/1.48  BG Simplification    : 0.02
% 3.16/1.48  Subsumption          : 0.09
% 3.16/1.48  Abstraction          : 0.02
% 3.16/1.48  MUC search           : 0.00
% 3.16/1.48  Cooper               : 0.00
% 3.16/1.48  Total                : 0.73
% 3.16/1.48  Index Insertion      : 0.00
% 3.16/1.48  Index Deletion       : 0.00
% 3.16/1.48  Index Matching       : 0.00
% 3.16/1.48  BG Taut test         : 0.00
%------------------------------------------------------------------------------
