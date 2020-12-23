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
% DateTime   : Thu Dec  3 10:08:44 EST 2020

% Result     : Theorem 2.59s
% Output     : CNFRefutation 2.93s
% Verified   : 
% Statistics : Number of formulae       :   56 (  76 expanded)
%              Number of leaves         :   27 (  37 expanded)
%              Depth                    :   11
%              Number of atoms          :   80 ( 120 expanded)
%              Number of equality atoms :   18 (  32 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_relat_1 > k5_relset_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

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

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_79,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(C,A)))
       => ( r1_xboole_0(B,C)
         => k5_relset_1(C,A,D,B) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_relset_1)).

tff(f_54,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k5_relset_1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k5_relset_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_44,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_42,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_66,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,C)))
     => m1_subset_1(k5_relset_1(A,C,D,B),k1_zfmisc_1(k2_zfmisc_1(B,C))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t33_relset_1)).

tff(f_72,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,A)))
     => ( r1_tarski(B,C)
       => r2_relset_1(B,A,k5_relset_1(B,A,D,C),D) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_relset_1)).

tff(f_62,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_50,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r1_xboole_0(A,B)
       => k7_relat_1(k7_relat_1(C,A),B) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t207_relat_1)).

tff(c_30,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_75,plain,(
    ! [A_44,B_45,C_46,D_47] :
      ( k5_relset_1(A_44,B_45,C_46,D_47) = k7_relat_1(C_46,D_47)
      | ~ m1_subset_1(C_46,k1_zfmisc_1(k2_zfmisc_1(A_44,B_45))) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_78,plain,(
    ! [D_47] : k5_relset_1('#skF_3','#skF_1','#skF_4',D_47) = k7_relat_1('#skF_4',D_47) ),
    inference(resolution,[status(thm)],[c_30,c_75])).

tff(c_26,plain,(
    k5_relset_1('#skF_3','#skF_1','#skF_4','#skF_2') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_79,plain,(
    k7_relat_1('#skF_4','#skF_2') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_26])).

tff(c_28,plain,(
    r1_xboole_0('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_34,plain,(
    ! [B_32,A_33] :
      ( r1_xboole_0(B_32,A_33)
      | ~ r1_xboole_0(A_33,B_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_37,plain,(
    r1_xboole_0('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_28,c_34])).

tff(c_12,plain,(
    ! [A_8,B_9] : v1_relat_1(k2_zfmisc_1(A_8,B_9)) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_49,plain,(
    ! [B_36,A_37] :
      ( v1_relat_1(B_36)
      | ~ m1_subset_1(B_36,k1_zfmisc_1(A_37))
      | ~ v1_relat_1(A_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_52,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_3','#skF_1')) ),
    inference(resolution,[status(thm)],[c_30,c_49])).

tff(c_55,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_52])).

tff(c_8,plain,(
    ! [B_4] : r1_tarski(B_4,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_89,plain,(
    ! [A_49,C_50,D_51,B_52] :
      ( m1_subset_1(k5_relset_1(A_49,C_50,D_51,B_52),k1_zfmisc_1(k2_zfmisc_1(B_52,C_50)))
      | ~ m1_subset_1(D_51,k1_zfmisc_1(k2_zfmisc_1(A_49,C_50))) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_99,plain,(
    ! [D_47] :
      ( m1_subset_1(k7_relat_1('#skF_4',D_47),k1_zfmisc_1(k2_zfmisc_1(D_47,'#skF_1')))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_1'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_78,c_89])).

tff(c_106,plain,(
    ! [D_47] : m1_subset_1(k7_relat_1('#skF_4',D_47),k1_zfmisc_1(k2_zfmisc_1(D_47,'#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_99])).

tff(c_240,plain,(
    ! [B_77,A_78,D_79,C_80] :
      ( r2_relset_1(B_77,A_78,k5_relset_1(B_77,A_78,D_79,C_80),D_79)
      | ~ r1_tarski(B_77,C_80)
      | ~ m1_subset_1(D_79,k1_zfmisc_1(k2_zfmisc_1(B_77,A_78))) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_252,plain,(
    ! [C_80] :
      ( r2_relset_1('#skF_3','#skF_1',k5_relset_1('#skF_3','#skF_1','#skF_4',C_80),'#skF_4')
      | ~ r1_tarski('#skF_3',C_80) ) ),
    inference(resolution,[status(thm)],[c_30,c_240])).

tff(c_260,plain,(
    ! [C_80] :
      ( r2_relset_1('#skF_3','#skF_1',k7_relat_1('#skF_4',C_80),'#skF_4')
      | ~ r1_tarski('#skF_3',C_80) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_252])).

tff(c_317,plain,(
    ! [D_90,C_91,A_92,B_93] :
      ( D_90 = C_91
      | ~ r2_relset_1(A_92,B_93,C_91,D_90)
      | ~ m1_subset_1(D_90,k1_zfmisc_1(k2_zfmisc_1(A_92,B_93)))
      | ~ m1_subset_1(C_91,k1_zfmisc_1(k2_zfmisc_1(A_92,B_93))) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_319,plain,(
    ! [C_80] :
      ( k7_relat_1('#skF_4',C_80) = '#skF_4'
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_1')))
      | ~ m1_subset_1(k7_relat_1('#skF_4',C_80),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_1')))
      | ~ r1_tarski('#skF_3',C_80) ) ),
    inference(resolution,[status(thm)],[c_260,c_317])).

tff(c_663,plain,(
    ! [C_127] :
      ( k7_relat_1('#skF_4',C_127) = '#skF_4'
      | ~ m1_subset_1(k7_relat_1('#skF_4',C_127),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_1')))
      | ~ r1_tarski('#skF_3',C_127) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_319])).

tff(c_667,plain,
    ( k7_relat_1('#skF_4','#skF_3') = '#skF_4'
    | ~ r1_tarski('#skF_3','#skF_3') ),
    inference(resolution,[status(thm)],[c_106,c_663])).

tff(c_670,plain,(
    k7_relat_1('#skF_4','#skF_3') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_667])).

tff(c_14,plain,(
    ! [C_12,A_10,B_11] :
      ( k7_relat_1(k7_relat_1(C_12,A_10),B_11) = k1_xboole_0
      | ~ r1_xboole_0(A_10,B_11)
      | ~ v1_relat_1(C_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_712,plain,(
    ! [B_11] :
      ( k7_relat_1('#skF_4',B_11) = k1_xboole_0
      | ~ r1_xboole_0('#skF_3',B_11)
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_670,c_14])).

tff(c_732,plain,(
    ! [B_128] :
      ( k7_relat_1('#skF_4',B_128) = k1_xboole_0
      | ~ r1_xboole_0('#skF_3',B_128) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_55,c_712])).

tff(c_735,plain,(
    k7_relat_1('#skF_4','#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_37,c_732])).

tff(c_739,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_79,c_735])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n006.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 14:04:22 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.59/1.43  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.59/1.43  
% 2.59/1.43  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.59/1.44  %$ r2_relset_1 > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_relat_1 > k5_relset_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.59/1.44  
% 2.59/1.44  %Foreground sorts:
% 2.59/1.44  
% 2.59/1.44  
% 2.59/1.44  %Background operators:
% 2.59/1.44  
% 2.59/1.44  
% 2.59/1.44  %Foreground operators:
% 2.59/1.44  tff(k5_relset_1, type, k5_relset_1: ($i * $i * $i * $i) > $i).
% 2.59/1.44  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.59/1.44  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 2.59/1.44  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.59/1.44  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.59/1.44  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.59/1.44  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.59/1.44  tff('#skF_2', type, '#skF_2': $i).
% 2.59/1.44  tff('#skF_3', type, '#skF_3': $i).
% 2.59/1.44  tff('#skF_1', type, '#skF_1': $i).
% 2.59/1.44  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.59/1.44  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.59/1.44  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.59/1.44  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.59/1.44  tff('#skF_4', type, '#skF_4': $i).
% 2.59/1.44  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.59/1.44  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.59/1.44  
% 2.93/1.45  tff(f_79, negated_conjecture, ~(![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(C, A))) => (r1_xboole_0(B, C) => (k5_relset_1(C, A, D, B) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_relset_1)).
% 2.93/1.45  tff(f_54, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k5_relset_1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k5_relset_1)).
% 2.93/1.45  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 2.93/1.45  tff(f_44, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 2.93/1.45  tff(f_42, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 2.93/1.45  tff(f_35, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.93/1.45  tff(f_66, axiom, (![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, C))) => m1_subset_1(k5_relset_1(A, C, D, B), k1_zfmisc_1(k2_zfmisc_1(B, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t33_relset_1)).
% 2.93/1.45  tff(f_72, axiom, (![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A))) => (r1_tarski(B, C) => r2_relset_1(B, A, k5_relset_1(B, A, D, C), D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t34_relset_1)).
% 2.93/1.45  tff(f_62, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 2.93/1.45  tff(f_50, axiom, (![A, B, C]: (v1_relat_1(C) => (r1_xboole_0(A, B) => (k7_relat_1(k7_relat_1(C, A), B) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t207_relat_1)).
% 2.93/1.45  tff(c_30, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.93/1.45  tff(c_75, plain, (![A_44, B_45, C_46, D_47]: (k5_relset_1(A_44, B_45, C_46, D_47)=k7_relat_1(C_46, D_47) | ~m1_subset_1(C_46, k1_zfmisc_1(k2_zfmisc_1(A_44, B_45))))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.93/1.45  tff(c_78, plain, (![D_47]: (k5_relset_1('#skF_3', '#skF_1', '#skF_4', D_47)=k7_relat_1('#skF_4', D_47))), inference(resolution, [status(thm)], [c_30, c_75])).
% 2.93/1.45  tff(c_26, plain, (k5_relset_1('#skF_3', '#skF_1', '#skF_4', '#skF_2')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.93/1.45  tff(c_79, plain, (k7_relat_1('#skF_4', '#skF_2')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_78, c_26])).
% 2.93/1.45  tff(c_28, plain, (r1_xboole_0('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.93/1.45  tff(c_34, plain, (![B_32, A_33]: (r1_xboole_0(B_32, A_33) | ~r1_xboole_0(A_33, B_32))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.93/1.45  tff(c_37, plain, (r1_xboole_0('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_28, c_34])).
% 2.93/1.45  tff(c_12, plain, (![A_8, B_9]: (v1_relat_1(k2_zfmisc_1(A_8, B_9)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.93/1.45  tff(c_49, plain, (![B_36, A_37]: (v1_relat_1(B_36) | ~m1_subset_1(B_36, k1_zfmisc_1(A_37)) | ~v1_relat_1(A_37))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.93/1.45  tff(c_52, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_3', '#skF_1'))), inference(resolution, [status(thm)], [c_30, c_49])).
% 2.93/1.45  tff(c_55, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_12, c_52])).
% 2.93/1.45  tff(c_8, plain, (![B_4]: (r1_tarski(B_4, B_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.93/1.45  tff(c_89, plain, (![A_49, C_50, D_51, B_52]: (m1_subset_1(k5_relset_1(A_49, C_50, D_51, B_52), k1_zfmisc_1(k2_zfmisc_1(B_52, C_50))) | ~m1_subset_1(D_51, k1_zfmisc_1(k2_zfmisc_1(A_49, C_50))))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.93/1.45  tff(c_99, plain, (![D_47]: (m1_subset_1(k7_relat_1('#skF_4', D_47), k1_zfmisc_1(k2_zfmisc_1(D_47, '#skF_1'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_1'))))), inference(superposition, [status(thm), theory('equality')], [c_78, c_89])).
% 2.93/1.45  tff(c_106, plain, (![D_47]: (m1_subset_1(k7_relat_1('#skF_4', D_47), k1_zfmisc_1(k2_zfmisc_1(D_47, '#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_99])).
% 2.93/1.45  tff(c_240, plain, (![B_77, A_78, D_79, C_80]: (r2_relset_1(B_77, A_78, k5_relset_1(B_77, A_78, D_79, C_80), D_79) | ~r1_tarski(B_77, C_80) | ~m1_subset_1(D_79, k1_zfmisc_1(k2_zfmisc_1(B_77, A_78))))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.93/1.45  tff(c_252, plain, (![C_80]: (r2_relset_1('#skF_3', '#skF_1', k5_relset_1('#skF_3', '#skF_1', '#skF_4', C_80), '#skF_4') | ~r1_tarski('#skF_3', C_80))), inference(resolution, [status(thm)], [c_30, c_240])).
% 2.93/1.45  tff(c_260, plain, (![C_80]: (r2_relset_1('#skF_3', '#skF_1', k7_relat_1('#skF_4', C_80), '#skF_4') | ~r1_tarski('#skF_3', C_80))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_252])).
% 2.93/1.45  tff(c_317, plain, (![D_90, C_91, A_92, B_93]: (D_90=C_91 | ~r2_relset_1(A_92, B_93, C_91, D_90) | ~m1_subset_1(D_90, k1_zfmisc_1(k2_zfmisc_1(A_92, B_93))) | ~m1_subset_1(C_91, k1_zfmisc_1(k2_zfmisc_1(A_92, B_93))))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.93/1.45  tff(c_319, plain, (![C_80]: (k7_relat_1('#skF_4', C_80)='#skF_4' | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_1'))) | ~m1_subset_1(k7_relat_1('#skF_4', C_80), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_1'))) | ~r1_tarski('#skF_3', C_80))), inference(resolution, [status(thm)], [c_260, c_317])).
% 2.93/1.45  tff(c_663, plain, (![C_127]: (k7_relat_1('#skF_4', C_127)='#skF_4' | ~m1_subset_1(k7_relat_1('#skF_4', C_127), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_1'))) | ~r1_tarski('#skF_3', C_127))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_319])).
% 2.93/1.45  tff(c_667, plain, (k7_relat_1('#skF_4', '#skF_3')='#skF_4' | ~r1_tarski('#skF_3', '#skF_3')), inference(resolution, [status(thm)], [c_106, c_663])).
% 2.93/1.45  tff(c_670, plain, (k7_relat_1('#skF_4', '#skF_3')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_8, c_667])).
% 2.93/1.45  tff(c_14, plain, (![C_12, A_10, B_11]: (k7_relat_1(k7_relat_1(C_12, A_10), B_11)=k1_xboole_0 | ~r1_xboole_0(A_10, B_11) | ~v1_relat_1(C_12))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.93/1.45  tff(c_712, plain, (![B_11]: (k7_relat_1('#skF_4', B_11)=k1_xboole_0 | ~r1_xboole_0('#skF_3', B_11) | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_670, c_14])).
% 2.93/1.45  tff(c_732, plain, (![B_128]: (k7_relat_1('#skF_4', B_128)=k1_xboole_0 | ~r1_xboole_0('#skF_3', B_128))), inference(demodulation, [status(thm), theory('equality')], [c_55, c_712])).
% 2.93/1.45  tff(c_735, plain, (k7_relat_1('#skF_4', '#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_37, c_732])).
% 2.93/1.45  tff(c_739, plain, $false, inference(negUnitSimplification, [status(thm)], [c_79, c_735])).
% 2.93/1.45  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.93/1.45  
% 2.93/1.45  Inference rules
% 2.93/1.45  ----------------------
% 2.93/1.45  #Ref     : 0
% 2.93/1.45  #Sup     : 153
% 2.93/1.45  #Fact    : 0
% 2.93/1.45  #Define  : 0
% 2.93/1.45  #Split   : 2
% 2.93/1.45  #Chain   : 0
% 2.93/1.45  #Close   : 0
% 2.93/1.45  
% 2.93/1.45  Ordering : KBO
% 2.93/1.45  
% 2.93/1.45  Simplification rules
% 2.93/1.45  ----------------------
% 2.93/1.45  #Subsume      : 7
% 2.93/1.45  #Demod        : 137
% 2.93/1.45  #Tautology    : 79
% 2.93/1.45  #SimpNegUnit  : 5
% 2.93/1.45  #BackRed      : 8
% 2.93/1.45  
% 2.93/1.45  #Partial instantiations: 0
% 2.93/1.45  #Strategies tried      : 1
% 2.93/1.45  
% 2.93/1.45  Timing (in seconds)
% 2.93/1.45  ----------------------
% 2.93/1.45  Preprocessing        : 0.28
% 2.93/1.45  Parsing              : 0.15
% 2.93/1.45  CNF conversion       : 0.02
% 2.93/1.45  Main loop            : 0.35
% 2.93/1.45  Inferencing          : 0.13
% 2.93/1.46  Reduction            : 0.12
% 2.93/1.46  Demodulation         : 0.09
% 2.93/1.46  BG Simplification    : 0.02
% 2.93/1.46  Subsumption          : 0.06
% 2.93/1.46  Abstraction          : 0.02
% 2.93/1.46  MUC search           : 0.00
% 2.93/1.46  Cooper               : 0.00
% 2.93/1.46  Total                : 0.66
% 2.93/1.46  Index Insertion      : 0.00
% 2.93/1.46  Index Deletion       : 0.00
% 2.93/1.46  Index Matching       : 0.00
% 2.93/1.46  BG Taut test         : 0.00
%------------------------------------------------------------------------------
