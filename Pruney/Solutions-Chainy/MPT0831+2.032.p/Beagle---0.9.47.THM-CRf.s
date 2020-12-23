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
% DateTime   : Thu Dec  3 10:07:36 EST 2020

% Result     : Theorem 1.93s
% Output     : CNFRefutation 2.11s
% Verified   : 
% Statistics : Number of formulae       :   57 (  74 expanded)
%              Number of leaves         :   29 (  38 expanded)
%              Depth                    :   10
%              Number of atoms          :   79 ( 115 expanded)
%              Number of equality atoms :   11 (  11 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k5_relset_1 > k7_relat_1 > k2_zfmisc_1 > k2_xboole_0 > #nlpp > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_79,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,A)))
       => ( r1_tarski(B,C)
         => r2_relset_1(B,A,k5_relset_1(B,A,D,C),D) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_relset_1)).

tff(f_72,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_48,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_40,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_60,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_46,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_29,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_xboole_0(A,B),C)
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).

tff(f_54,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_64,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k5_relset_1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k5_relset_1)).

tff(c_30,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_89,plain,(
    ! [A_49,B_50,D_51] :
      ( r2_relset_1(A_49,B_50,D_51,D_51)
      | ~ m1_subset_1(D_51,k1_zfmisc_1(k2_zfmisc_1(A_49,B_50))) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_92,plain,(
    r2_relset_1('#skF_2','#skF_1','#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_30,c_89])).

tff(c_12,plain,(
    ! [A_11,B_12] : v1_relat_1(k2_zfmisc_1(A_11,B_12)) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_51,plain,(
    ! [B_35,A_36] :
      ( v1_relat_1(B_35)
      | ~ m1_subset_1(B_35,k1_zfmisc_1(A_36))
      | ~ v1_relat_1(A_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_54,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_1')) ),
    inference(resolution,[status(thm)],[c_30,c_51])).

tff(c_57,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_54])).

tff(c_74,plain,(
    ! [C_46,A_47,B_48] :
      ( v4_relat_1(C_46,A_47)
      | ~ m1_subset_1(C_46,k1_zfmisc_1(k2_zfmisc_1(A_47,B_48))) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_78,plain,(
    v4_relat_1('#skF_4','#skF_2') ),
    inference(resolution,[status(thm)],[c_30,c_74])).

tff(c_28,plain,(
    r1_tarski('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_58,plain,(
    ! [B_37,A_38] :
      ( r1_tarski(k1_relat_1(B_37),A_38)
      | ~ v4_relat_1(B_37,A_38)
      | ~ v1_relat_1(B_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_4,plain,(
    ! [A_4,B_5] :
      ( k2_xboole_0(A_4,B_5) = B_5
      | ~ r1_tarski(A_4,B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_93,plain,(
    ! [B_52,A_53] :
      ( k2_xboole_0(k1_relat_1(B_52),A_53) = A_53
      | ~ v4_relat_1(B_52,A_53)
      | ~ v1_relat_1(B_52) ) ),
    inference(resolution,[status(thm)],[c_58,c_4])).

tff(c_2,plain,(
    ! [A_1,C_3,B_2] :
      ( r1_tarski(A_1,C_3)
      | ~ r1_tarski(k2_xboole_0(A_1,B_2),C_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_105,plain,(
    ! [B_54,C_55,A_56] :
      ( r1_tarski(k1_relat_1(B_54),C_55)
      | ~ r1_tarski(A_56,C_55)
      | ~ v4_relat_1(B_54,A_56)
      | ~ v1_relat_1(B_54) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_93,c_2])).

tff(c_115,plain,(
    ! [B_57] :
      ( r1_tarski(k1_relat_1(B_57),'#skF_3')
      | ~ v4_relat_1(B_57,'#skF_2')
      | ~ v1_relat_1(B_57) ) ),
    inference(resolution,[status(thm)],[c_28,c_105])).

tff(c_8,plain,(
    ! [B_10,A_9] :
      ( v4_relat_1(B_10,A_9)
      | ~ r1_tarski(k1_relat_1(B_10),A_9)
      | ~ v1_relat_1(B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_127,plain,(
    ! [B_58] :
      ( v4_relat_1(B_58,'#skF_3')
      | ~ v4_relat_1(B_58,'#skF_2')
      | ~ v1_relat_1(B_58) ) ),
    inference(resolution,[status(thm)],[c_115,c_8])).

tff(c_130,plain,
    ( v4_relat_1('#skF_4','#skF_3')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_78,c_127])).

tff(c_133,plain,(
    v4_relat_1('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_57,c_130])).

tff(c_14,plain,(
    ! [B_14,A_13] :
      ( k7_relat_1(B_14,A_13) = B_14
      | ~ v4_relat_1(B_14,A_13)
      | ~ v1_relat_1(B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_140,plain,
    ( k7_relat_1('#skF_4','#skF_3') = '#skF_4'
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_133,c_14])).

tff(c_143,plain,(
    k7_relat_1('#skF_4','#skF_3') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_57,c_140])).

tff(c_134,plain,(
    ! [A_59,B_60,C_61,D_62] :
      ( k5_relset_1(A_59,B_60,C_61,D_62) = k7_relat_1(C_61,D_62)
      | ~ m1_subset_1(C_61,k1_zfmisc_1(k2_zfmisc_1(A_59,B_60))) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_137,plain,(
    ! [D_62] : k5_relset_1('#skF_2','#skF_1','#skF_4',D_62) = k7_relat_1('#skF_4',D_62) ),
    inference(resolution,[status(thm)],[c_30,c_134])).

tff(c_26,plain,(
    ~ r2_relset_1('#skF_2','#skF_1',k5_relset_1('#skF_2','#skF_1','#skF_4','#skF_3'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_148,plain,(
    ~ r2_relset_1('#skF_2','#skF_1',k7_relat_1('#skF_4','#skF_3'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_137,c_26])).

tff(c_151,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_143,c_148])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n012.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 09:22:22 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.93/1.22  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.06/1.23  
% 2.06/1.23  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.06/1.23  %$ r2_relset_1 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k5_relset_1 > k7_relat_1 > k2_zfmisc_1 > k2_xboole_0 > #nlpp > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.06/1.23  
% 2.06/1.23  %Foreground sorts:
% 2.06/1.23  
% 2.06/1.23  
% 2.06/1.23  %Background operators:
% 2.06/1.23  
% 2.06/1.23  
% 2.06/1.23  %Foreground operators:
% 2.06/1.23  tff(k5_relset_1, type, k5_relset_1: ($i * $i * $i * $i) > $i).
% 2.06/1.23  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.06/1.23  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 2.06/1.23  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.06/1.23  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.06/1.23  tff('#skF_2', type, '#skF_2': $i).
% 2.06/1.23  tff('#skF_3', type, '#skF_3': $i).
% 2.06/1.23  tff('#skF_1', type, '#skF_1': $i).
% 2.06/1.23  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.06/1.23  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.06/1.23  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.06/1.23  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.06/1.23  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.06/1.23  tff('#skF_4', type, '#skF_4': $i).
% 2.06/1.23  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.06/1.23  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.06/1.23  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.06/1.23  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.06/1.23  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.06/1.23  
% 2.11/1.24  tff(f_79, negated_conjecture, ~(![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A))) => (r1_tarski(B, C) => r2_relset_1(B, A, k5_relset_1(B, A, D, C), D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t34_relset_1)).
% 2.11/1.24  tff(f_72, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 2.11/1.24  tff(f_48, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 2.11/1.24  tff(f_40, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 2.11/1.24  tff(f_60, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.11/1.24  tff(f_46, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d18_relat_1)).
% 2.11/1.24  tff(f_33, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 2.11/1.24  tff(f_29, axiom, (![A, B, C]: (r1_tarski(k2_xboole_0(A, B), C) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_xboole_1)).
% 2.11/1.24  tff(f_54, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t209_relat_1)).
% 2.11/1.24  tff(f_64, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k5_relset_1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k5_relset_1)).
% 2.11/1.24  tff(c_30, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.11/1.24  tff(c_89, plain, (![A_49, B_50, D_51]: (r2_relset_1(A_49, B_50, D_51, D_51) | ~m1_subset_1(D_51, k1_zfmisc_1(k2_zfmisc_1(A_49, B_50))))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.11/1.24  tff(c_92, plain, (r2_relset_1('#skF_2', '#skF_1', '#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_30, c_89])).
% 2.11/1.24  tff(c_12, plain, (![A_11, B_12]: (v1_relat_1(k2_zfmisc_1(A_11, B_12)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.11/1.24  tff(c_51, plain, (![B_35, A_36]: (v1_relat_1(B_35) | ~m1_subset_1(B_35, k1_zfmisc_1(A_36)) | ~v1_relat_1(A_36))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.11/1.24  tff(c_54, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_1'))), inference(resolution, [status(thm)], [c_30, c_51])).
% 2.11/1.24  tff(c_57, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_12, c_54])).
% 2.11/1.24  tff(c_74, plain, (![C_46, A_47, B_48]: (v4_relat_1(C_46, A_47) | ~m1_subset_1(C_46, k1_zfmisc_1(k2_zfmisc_1(A_47, B_48))))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.11/1.24  tff(c_78, plain, (v4_relat_1('#skF_4', '#skF_2')), inference(resolution, [status(thm)], [c_30, c_74])).
% 2.11/1.24  tff(c_28, plain, (r1_tarski('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.11/1.24  tff(c_58, plain, (![B_37, A_38]: (r1_tarski(k1_relat_1(B_37), A_38) | ~v4_relat_1(B_37, A_38) | ~v1_relat_1(B_37))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.11/1.24  tff(c_4, plain, (![A_4, B_5]: (k2_xboole_0(A_4, B_5)=B_5 | ~r1_tarski(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.11/1.24  tff(c_93, plain, (![B_52, A_53]: (k2_xboole_0(k1_relat_1(B_52), A_53)=A_53 | ~v4_relat_1(B_52, A_53) | ~v1_relat_1(B_52))), inference(resolution, [status(thm)], [c_58, c_4])).
% 2.11/1.24  tff(c_2, plain, (![A_1, C_3, B_2]: (r1_tarski(A_1, C_3) | ~r1_tarski(k2_xboole_0(A_1, B_2), C_3))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.11/1.24  tff(c_105, plain, (![B_54, C_55, A_56]: (r1_tarski(k1_relat_1(B_54), C_55) | ~r1_tarski(A_56, C_55) | ~v4_relat_1(B_54, A_56) | ~v1_relat_1(B_54))), inference(superposition, [status(thm), theory('equality')], [c_93, c_2])).
% 2.11/1.24  tff(c_115, plain, (![B_57]: (r1_tarski(k1_relat_1(B_57), '#skF_3') | ~v4_relat_1(B_57, '#skF_2') | ~v1_relat_1(B_57))), inference(resolution, [status(thm)], [c_28, c_105])).
% 2.11/1.24  tff(c_8, plain, (![B_10, A_9]: (v4_relat_1(B_10, A_9) | ~r1_tarski(k1_relat_1(B_10), A_9) | ~v1_relat_1(B_10))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.11/1.24  tff(c_127, plain, (![B_58]: (v4_relat_1(B_58, '#skF_3') | ~v4_relat_1(B_58, '#skF_2') | ~v1_relat_1(B_58))), inference(resolution, [status(thm)], [c_115, c_8])).
% 2.11/1.24  tff(c_130, plain, (v4_relat_1('#skF_4', '#skF_3') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_78, c_127])).
% 2.11/1.24  tff(c_133, plain, (v4_relat_1('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_57, c_130])).
% 2.11/1.24  tff(c_14, plain, (![B_14, A_13]: (k7_relat_1(B_14, A_13)=B_14 | ~v4_relat_1(B_14, A_13) | ~v1_relat_1(B_14))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.11/1.24  tff(c_140, plain, (k7_relat_1('#skF_4', '#skF_3')='#skF_4' | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_133, c_14])).
% 2.11/1.24  tff(c_143, plain, (k7_relat_1('#skF_4', '#skF_3')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_57, c_140])).
% 2.11/1.24  tff(c_134, plain, (![A_59, B_60, C_61, D_62]: (k5_relset_1(A_59, B_60, C_61, D_62)=k7_relat_1(C_61, D_62) | ~m1_subset_1(C_61, k1_zfmisc_1(k2_zfmisc_1(A_59, B_60))))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.11/1.24  tff(c_137, plain, (![D_62]: (k5_relset_1('#skF_2', '#skF_1', '#skF_4', D_62)=k7_relat_1('#skF_4', D_62))), inference(resolution, [status(thm)], [c_30, c_134])).
% 2.11/1.24  tff(c_26, plain, (~r2_relset_1('#skF_2', '#skF_1', k5_relset_1('#skF_2', '#skF_1', '#skF_4', '#skF_3'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.11/1.24  tff(c_148, plain, (~r2_relset_1('#skF_2', '#skF_1', k7_relat_1('#skF_4', '#skF_3'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_137, c_26])).
% 2.11/1.24  tff(c_151, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_92, c_143, c_148])).
% 2.11/1.24  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.11/1.24  
% 2.11/1.24  Inference rules
% 2.11/1.24  ----------------------
% 2.11/1.24  #Ref     : 0
% 2.11/1.24  #Sup     : 28
% 2.11/1.24  #Fact    : 0
% 2.11/1.24  #Define  : 0
% 2.11/1.24  #Split   : 0
% 2.11/1.24  #Chain   : 0
% 2.11/1.24  #Close   : 0
% 2.11/1.24  
% 2.11/1.24  Ordering : KBO
% 2.11/1.24  
% 2.11/1.24  Simplification rules
% 2.11/1.24  ----------------------
% 2.11/1.24  #Subsume      : 0
% 2.11/1.24  #Demod        : 7
% 2.11/1.24  #Tautology    : 9
% 2.11/1.24  #SimpNegUnit  : 0
% 2.11/1.24  #BackRed      : 1
% 2.11/1.24  
% 2.11/1.24  #Partial instantiations: 0
% 2.11/1.24  #Strategies tried      : 1
% 2.11/1.24  
% 2.11/1.24  Timing (in seconds)
% 2.11/1.24  ----------------------
% 2.11/1.25  Preprocessing        : 0.28
% 2.11/1.25  Parsing              : 0.15
% 2.11/1.25  CNF conversion       : 0.02
% 2.11/1.25  Main loop            : 0.15
% 2.11/1.25  Inferencing          : 0.06
% 2.11/1.25  Reduction            : 0.05
% 2.11/1.25  Demodulation         : 0.03
% 2.11/1.25  BG Simplification    : 0.01
% 2.11/1.25  Subsumption          : 0.02
% 2.11/1.25  Abstraction          : 0.01
% 2.11/1.25  MUC search           : 0.00
% 2.11/1.25  Cooper               : 0.00
% 2.11/1.25  Total                : 0.47
% 2.11/1.25  Index Insertion      : 0.00
% 2.11/1.25  Index Deletion       : 0.00
% 2.11/1.25  Index Matching       : 0.00
% 2.11/1.25  BG Taut test         : 0.00
%------------------------------------------------------------------------------
