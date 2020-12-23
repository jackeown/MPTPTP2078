%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:07:37 EST 2020

% Result     : Theorem 1.97s
% Output     : CNFRefutation 2.12s
% Verified   : 
% Statistics : Number of formulae       :   56 (  77 expanded)
%              Number of leaves         :   27 (  38 expanded)
%              Depth                    :   10
%              Number of atoms          :   78 ( 124 expanded)
%              Number of equality atoms :    8 (   8 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k5_relset_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_46,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_75,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,A)))
       => ( r1_tarski(B,C)
         => r2_relset_1(B,A,k5_relset_1(B,A,D,C),D) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_relset_1)).

tff(f_38,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_58,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_52,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k1_relat_1(B),A)
       => k7_relat_1(B,A) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t97_relat_1)).

tff(f_62,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k5_relset_1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k5_relset_1)).

tff(f_68,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => r2_relset_1(A,B,C,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',reflexivity_r2_relset_1)).

tff(c_10,plain,(
    ! [A_9,B_10] : v1_relat_1(k2_zfmisc_1(A_9,B_10)) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_26,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_28,plain,(
    ! [B_26,A_27] :
      ( v1_relat_1(B_26)
      | ~ m1_subset_1(B_26,k1_zfmisc_1(A_27))
      | ~ v1_relat_1(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_31,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_1')) ),
    inference(resolution,[status(thm)],[c_26,c_28])).

tff(c_34,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_31])).

tff(c_54,plain,(
    ! [C_36,A_37,B_38] :
      ( v4_relat_1(C_36,A_37)
      | ~ m1_subset_1(C_36,k1_zfmisc_1(k2_zfmisc_1(A_37,B_38))) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_58,plain,(
    v4_relat_1('#skF_4','#skF_2') ),
    inference(resolution,[status(thm)],[c_26,c_54])).

tff(c_8,plain,(
    ! [B_8,A_7] :
      ( r1_tarski(k1_relat_1(B_8),A_7)
      | ~ v4_relat_1(B_8,A_7)
      | ~ v1_relat_1(B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_24,plain,(
    r1_tarski('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_41,plain,(
    ! [A_32,C_33,B_34] :
      ( r1_tarski(A_32,C_33)
      | ~ r1_tarski(B_34,C_33)
      | ~ r1_tarski(A_32,B_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_48,plain,(
    ! [A_35] :
      ( r1_tarski(A_35,'#skF_3')
      | ~ r1_tarski(A_35,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_24,c_41])).

tff(c_64,plain,(
    ! [B_42] :
      ( r1_tarski(k1_relat_1(B_42),'#skF_3')
      | ~ v4_relat_1(B_42,'#skF_2')
      | ~ v1_relat_1(B_42) ) ),
    inference(resolution,[status(thm)],[c_8,c_48])).

tff(c_6,plain,(
    ! [B_8,A_7] :
      ( v4_relat_1(B_8,A_7)
      | ~ r1_tarski(k1_relat_1(B_8),A_7)
      | ~ v1_relat_1(B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_81,plain,(
    ! [B_45] :
      ( v4_relat_1(B_45,'#skF_3')
      | ~ v4_relat_1(B_45,'#skF_2')
      | ~ v1_relat_1(B_45) ) ),
    inference(resolution,[status(thm)],[c_64,c_6])).

tff(c_84,plain,
    ( v4_relat_1('#skF_4','#skF_3')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_58,c_81])).

tff(c_87,plain,(
    v4_relat_1('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_84])).

tff(c_72,plain,(
    ! [B_43,A_44] :
      ( k7_relat_1(B_43,A_44) = B_43
      | ~ r1_tarski(k1_relat_1(B_43),A_44)
      | ~ v1_relat_1(B_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_88,plain,(
    ! [B_46,A_47] :
      ( k7_relat_1(B_46,A_47) = B_46
      | ~ v4_relat_1(B_46,A_47)
      | ~ v1_relat_1(B_46) ) ),
    inference(resolution,[status(thm)],[c_8,c_72])).

tff(c_91,plain,
    ( k7_relat_1('#skF_4','#skF_3') = '#skF_4'
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_87,c_88])).

tff(c_97,plain,(
    k7_relat_1('#skF_4','#skF_3') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_91])).

tff(c_127,plain,(
    ! [A_54,B_55,C_56,D_57] :
      ( k5_relset_1(A_54,B_55,C_56,D_57) = k7_relat_1(C_56,D_57)
      | ~ m1_subset_1(C_56,k1_zfmisc_1(k2_zfmisc_1(A_54,B_55))) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_130,plain,(
    ! [D_57] : k5_relset_1('#skF_2','#skF_1','#skF_4',D_57) = k7_relat_1('#skF_4',D_57) ),
    inference(resolution,[status(thm)],[c_26,c_127])).

tff(c_22,plain,(
    ~ r2_relset_1('#skF_2','#skF_1',k5_relset_1('#skF_2','#skF_1','#skF_4','#skF_3'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_135,plain,(
    ~ r2_relset_1('#skF_2','#skF_1',k7_relat_1('#skF_4','#skF_3'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_130,c_22])).

tff(c_136,plain,(
    ~ r2_relset_1('#skF_2','#skF_1','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_97,c_135])).

tff(c_131,plain,(
    ! [A_58,B_59,C_60,D_61] :
      ( r2_relset_1(A_58,B_59,C_60,C_60)
      | ~ m1_subset_1(D_61,k1_zfmisc_1(k2_zfmisc_1(A_58,B_59)))
      | ~ m1_subset_1(C_60,k1_zfmisc_1(k2_zfmisc_1(A_58,B_59))) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_146,plain,(
    ! [C_63] :
      ( r2_relset_1('#skF_2','#skF_1',C_63,C_63)
      | ~ m1_subset_1(C_63,k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ) ),
    inference(resolution,[status(thm)],[c_26,c_131])).

tff(c_148,plain,(
    r2_relset_1('#skF_2','#skF_1','#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_26,c_146])).

tff(c_152,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_136,c_148])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:31:16 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.97/1.22  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.97/1.23  
% 1.97/1.23  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.97/1.23  %$ r2_relset_1 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k5_relset_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 1.97/1.23  
% 1.97/1.23  %Foreground sorts:
% 1.97/1.23  
% 1.97/1.23  
% 1.97/1.23  %Background operators:
% 1.97/1.23  
% 1.97/1.23  
% 1.97/1.23  %Foreground operators:
% 1.97/1.23  tff(k5_relset_1, type, k5_relset_1: ($i * $i * $i * $i) > $i).
% 1.97/1.23  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.97/1.23  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 1.97/1.23  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 1.97/1.23  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.97/1.23  tff('#skF_2', type, '#skF_2': $i).
% 1.97/1.23  tff('#skF_3', type, '#skF_3': $i).
% 1.97/1.23  tff('#skF_1', type, '#skF_1': $i).
% 1.97/1.23  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 1.97/1.23  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.97/1.23  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.97/1.23  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.97/1.23  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.97/1.23  tff('#skF_4', type, '#skF_4': $i).
% 1.97/1.23  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.97/1.23  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 1.97/1.23  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.97/1.23  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.97/1.23  
% 2.12/1.25  tff(f_46, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 2.12/1.25  tff(f_75, negated_conjecture, ~(![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A))) => (r1_tarski(B, C) => r2_relset_1(B, A, k5_relset_1(B, A, D, C), D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t34_relset_1)).
% 2.12/1.25  tff(f_38, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 2.12/1.25  tff(f_58, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.12/1.25  tff(f_44, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d18_relat_1)).
% 2.12/1.25  tff(f_31, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 2.12/1.25  tff(f_52, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(B), A) => (k7_relat_1(B, A) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t97_relat_1)).
% 2.12/1.25  tff(f_62, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k5_relset_1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k5_relset_1)).
% 2.12/1.25  tff(f_68, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => r2_relset_1(A, B, C, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', reflexivity_r2_relset_1)).
% 2.12/1.25  tff(c_10, plain, (![A_9, B_10]: (v1_relat_1(k2_zfmisc_1(A_9, B_10)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.12/1.25  tff(c_26, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.12/1.25  tff(c_28, plain, (![B_26, A_27]: (v1_relat_1(B_26) | ~m1_subset_1(B_26, k1_zfmisc_1(A_27)) | ~v1_relat_1(A_27))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.12/1.25  tff(c_31, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_1'))), inference(resolution, [status(thm)], [c_26, c_28])).
% 2.12/1.25  tff(c_34, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_10, c_31])).
% 2.12/1.25  tff(c_54, plain, (![C_36, A_37, B_38]: (v4_relat_1(C_36, A_37) | ~m1_subset_1(C_36, k1_zfmisc_1(k2_zfmisc_1(A_37, B_38))))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.12/1.25  tff(c_58, plain, (v4_relat_1('#skF_4', '#skF_2')), inference(resolution, [status(thm)], [c_26, c_54])).
% 2.12/1.25  tff(c_8, plain, (![B_8, A_7]: (r1_tarski(k1_relat_1(B_8), A_7) | ~v4_relat_1(B_8, A_7) | ~v1_relat_1(B_8))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.12/1.25  tff(c_24, plain, (r1_tarski('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.12/1.25  tff(c_41, plain, (![A_32, C_33, B_34]: (r1_tarski(A_32, C_33) | ~r1_tarski(B_34, C_33) | ~r1_tarski(A_32, B_34))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.12/1.25  tff(c_48, plain, (![A_35]: (r1_tarski(A_35, '#skF_3') | ~r1_tarski(A_35, '#skF_2'))), inference(resolution, [status(thm)], [c_24, c_41])).
% 2.12/1.25  tff(c_64, plain, (![B_42]: (r1_tarski(k1_relat_1(B_42), '#skF_3') | ~v4_relat_1(B_42, '#skF_2') | ~v1_relat_1(B_42))), inference(resolution, [status(thm)], [c_8, c_48])).
% 2.12/1.25  tff(c_6, plain, (![B_8, A_7]: (v4_relat_1(B_8, A_7) | ~r1_tarski(k1_relat_1(B_8), A_7) | ~v1_relat_1(B_8))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.12/1.25  tff(c_81, plain, (![B_45]: (v4_relat_1(B_45, '#skF_3') | ~v4_relat_1(B_45, '#skF_2') | ~v1_relat_1(B_45))), inference(resolution, [status(thm)], [c_64, c_6])).
% 2.12/1.25  tff(c_84, plain, (v4_relat_1('#skF_4', '#skF_3') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_58, c_81])).
% 2.12/1.25  tff(c_87, plain, (v4_relat_1('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_84])).
% 2.12/1.25  tff(c_72, plain, (![B_43, A_44]: (k7_relat_1(B_43, A_44)=B_43 | ~r1_tarski(k1_relat_1(B_43), A_44) | ~v1_relat_1(B_43))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.12/1.25  tff(c_88, plain, (![B_46, A_47]: (k7_relat_1(B_46, A_47)=B_46 | ~v4_relat_1(B_46, A_47) | ~v1_relat_1(B_46))), inference(resolution, [status(thm)], [c_8, c_72])).
% 2.12/1.25  tff(c_91, plain, (k7_relat_1('#skF_4', '#skF_3')='#skF_4' | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_87, c_88])).
% 2.12/1.25  tff(c_97, plain, (k7_relat_1('#skF_4', '#skF_3')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_34, c_91])).
% 2.12/1.25  tff(c_127, plain, (![A_54, B_55, C_56, D_57]: (k5_relset_1(A_54, B_55, C_56, D_57)=k7_relat_1(C_56, D_57) | ~m1_subset_1(C_56, k1_zfmisc_1(k2_zfmisc_1(A_54, B_55))))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.12/1.25  tff(c_130, plain, (![D_57]: (k5_relset_1('#skF_2', '#skF_1', '#skF_4', D_57)=k7_relat_1('#skF_4', D_57))), inference(resolution, [status(thm)], [c_26, c_127])).
% 2.12/1.25  tff(c_22, plain, (~r2_relset_1('#skF_2', '#skF_1', k5_relset_1('#skF_2', '#skF_1', '#skF_4', '#skF_3'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.12/1.25  tff(c_135, plain, (~r2_relset_1('#skF_2', '#skF_1', k7_relat_1('#skF_4', '#skF_3'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_130, c_22])).
% 2.12/1.25  tff(c_136, plain, (~r2_relset_1('#skF_2', '#skF_1', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_97, c_135])).
% 2.12/1.25  tff(c_131, plain, (![A_58, B_59, C_60, D_61]: (r2_relset_1(A_58, B_59, C_60, C_60) | ~m1_subset_1(D_61, k1_zfmisc_1(k2_zfmisc_1(A_58, B_59))) | ~m1_subset_1(C_60, k1_zfmisc_1(k2_zfmisc_1(A_58, B_59))))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.12/1.25  tff(c_146, plain, (![C_63]: (r2_relset_1('#skF_2', '#skF_1', C_63, C_63) | ~m1_subset_1(C_63, k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))))), inference(resolution, [status(thm)], [c_26, c_131])).
% 2.12/1.25  tff(c_148, plain, (r2_relset_1('#skF_2', '#skF_1', '#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_26, c_146])).
% 2.12/1.25  tff(c_152, plain, $false, inference(negUnitSimplification, [status(thm)], [c_136, c_148])).
% 2.12/1.25  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.12/1.25  
% 2.12/1.25  Inference rules
% 2.12/1.25  ----------------------
% 2.12/1.25  #Ref     : 0
% 2.12/1.25  #Sup     : 26
% 2.12/1.25  #Fact    : 0
% 2.12/1.25  #Define  : 0
% 2.12/1.25  #Split   : 0
% 2.12/1.25  #Chain   : 0
% 2.12/1.25  #Close   : 0
% 2.12/1.25  
% 2.12/1.25  Ordering : KBO
% 2.12/1.25  
% 2.12/1.25  Simplification rules
% 2.12/1.25  ----------------------
% 2.12/1.25  #Subsume      : 0
% 2.12/1.25  #Demod        : 8
% 2.12/1.25  #Tautology    : 8
% 2.12/1.25  #SimpNegUnit  : 1
% 2.12/1.25  #BackRed      : 1
% 2.12/1.25  
% 2.12/1.25  #Partial instantiations: 0
% 2.12/1.25  #Strategies tried      : 1
% 2.12/1.25  
% 2.12/1.25  Timing (in seconds)
% 2.12/1.25  ----------------------
% 2.12/1.25  Preprocessing        : 0.28
% 2.12/1.25  Parsing              : 0.15
% 2.12/1.25  CNF conversion       : 0.02
% 2.12/1.25  Main loop            : 0.15
% 2.12/1.25  Inferencing          : 0.06
% 2.12/1.25  Reduction            : 0.04
% 2.12/1.25  Demodulation         : 0.03
% 2.12/1.25  BG Simplification    : 0.01
% 2.12/1.25  Subsumption          : 0.02
% 2.12/1.25  Abstraction          : 0.01
% 2.12/1.25  MUC search           : 0.00
% 2.12/1.25  Cooper               : 0.00
% 2.12/1.25  Total                : 0.46
% 2.12/1.25  Index Insertion      : 0.00
% 2.12/1.25  Index Deletion       : 0.00
% 2.12/1.25  Index Matching       : 0.00
% 2.12/1.25  BG Taut test         : 0.00
%------------------------------------------------------------------------------
