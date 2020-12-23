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
% DateTime   : Thu Dec  3 10:07:15 EST 2020

% Result     : Theorem 1.93s
% Output     : CNFRefutation 1.93s
% Verified   : 
% Statistics : Number of formulae       :   52 (  71 expanded)
%              Number of leaves         :   24 (  35 expanded)
%              Depth                    :    6
%              Number of atoms          :   68 ( 116 expanded)
%              Number of equality atoms :   10 (  12 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > m1_subset_1 > v1_relat_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

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

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_63,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B)))
       => ( r1_tarski(k6_relat_1(C),D)
         => ( r1_tarski(C,k1_relset_1(A,B,D))
            & r1_tarski(C,k2_relset_1(A,B,D)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_relset_1)).

tff(f_46,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_27,axiom,(
    ! [A] : v1_relat_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).

tff(f_42,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_38,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(A,B)
           => ( r1_tarski(k1_relat_1(A),k1_relat_1(B))
              & r1_tarski(k2_relat_1(A),k2_relat_1(B)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_relat_1)).

tff(f_54,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_50,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(c_22,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_42,plain,(
    ! [C_18,A_19,B_20] :
      ( v1_relat_1(C_18)
      | ~ m1_subset_1(C_18,k1_zfmisc_1(k2_zfmisc_1(A_19,B_20))) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_46,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_22,c_42])).

tff(c_20,plain,(
    r1_tarski(k6_relat_1('#skF_3'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_2,plain,(
    ! [A_1] : v1_relat_1(k6_relat_1(A_1)) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_10,plain,(
    ! [A_5] : k2_relat_1(k6_relat_1(A_5)) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_47,plain,(
    ! [A_21,B_22] :
      ( r1_tarski(k2_relat_1(A_21),k2_relat_1(B_22))
      | ~ r1_tarski(A_21,B_22)
      | ~ v1_relat_1(B_22)
      | ~ v1_relat_1(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_50,plain,(
    ! [A_5,B_22] :
      ( r1_tarski(A_5,k2_relat_1(B_22))
      | ~ r1_tarski(k6_relat_1(A_5),B_22)
      | ~ v1_relat_1(B_22)
      | ~ v1_relat_1(k6_relat_1(A_5)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_47])).

tff(c_58,plain,(
    ! [A_23,B_24] :
      ( r1_tarski(A_23,k2_relat_1(B_24))
      | ~ r1_tarski(k6_relat_1(A_23),B_24)
      | ~ v1_relat_1(B_24) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_50])).

tff(c_61,plain,
    ( r1_tarski('#skF_3',k2_relat_1('#skF_4'))
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_20,c_58])).

tff(c_64,plain,(
    r1_tarski('#skF_3',k2_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_61])).

tff(c_120,plain,(
    ! [A_41,B_42,C_43] :
      ( k2_relset_1(A_41,B_42,C_43) = k2_relat_1(C_43)
      | ~ m1_subset_1(C_43,k1_zfmisc_1(k2_zfmisc_1(A_41,B_42))) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_124,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_22,c_120])).

tff(c_78,plain,(
    ! [A_32,B_33,C_34] :
      ( k1_relset_1(A_32,B_33,C_34) = k1_relat_1(C_34)
      | ~ m1_subset_1(C_34,k1_zfmisc_1(k2_zfmisc_1(A_32,B_33))) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_82,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_22,c_78])).

tff(c_18,plain,
    ( ~ r1_tarski('#skF_3',k2_relset_1('#skF_1','#skF_2','#skF_4'))
    | ~ r1_tarski('#skF_3',k1_relset_1('#skF_1','#skF_2','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_65,plain,(
    ~ r1_tarski('#skF_3',k1_relset_1('#skF_1','#skF_2','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_18])).

tff(c_87,plain,(
    ~ r1_tarski('#skF_3',k1_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_65])).

tff(c_8,plain,(
    ! [A_5] : k1_relat_1(k6_relat_1(A_5)) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_92,plain,(
    ! [A_35,B_36] :
      ( r1_tarski(k1_relat_1(A_35),k1_relat_1(B_36))
      | ~ r1_tarski(A_35,B_36)
      | ~ v1_relat_1(B_36)
      | ~ v1_relat_1(A_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_95,plain,(
    ! [A_5,B_36] :
      ( r1_tarski(A_5,k1_relat_1(B_36))
      | ~ r1_tarski(k6_relat_1(A_5),B_36)
      | ~ v1_relat_1(B_36)
      | ~ v1_relat_1(k6_relat_1(A_5)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_92])).

tff(c_103,plain,(
    ! [A_37,B_38] :
      ( r1_tarski(A_37,k1_relat_1(B_38))
      | ~ r1_tarski(k6_relat_1(A_37),B_38)
      | ~ v1_relat_1(B_38) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_95])).

tff(c_106,plain,
    ( r1_tarski('#skF_3',k1_relat_1('#skF_4'))
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_20,c_103])).

tff(c_109,plain,(
    r1_tarski('#skF_3',k1_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_106])).

tff(c_111,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_87,c_109])).

tff(c_112,plain,(
    ~ r1_tarski('#skF_3',k2_relset_1('#skF_1','#skF_2','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_18])).

tff(c_125,plain,(
    ~ r1_tarski('#skF_3',k2_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_124,c_112])).

tff(c_128,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_125])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n007.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 15:05:51 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.93/1.23  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.93/1.24  
% 1.93/1.24  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.93/1.24  %$ r1_tarski > m1_subset_1 > v1_relat_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 1.93/1.24  
% 1.93/1.24  %Foreground sorts:
% 1.93/1.24  
% 1.93/1.24  
% 1.93/1.24  %Background operators:
% 1.93/1.24  
% 1.93/1.24  
% 1.93/1.24  %Foreground operators:
% 1.93/1.24  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 1.93/1.24  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.93/1.24  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.93/1.24  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.93/1.24  tff('#skF_2', type, '#skF_2': $i).
% 1.93/1.24  tff('#skF_3', type, '#skF_3': $i).
% 1.93/1.24  tff('#skF_1', type, '#skF_1': $i).
% 1.93/1.24  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 1.93/1.24  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.93/1.24  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.93/1.24  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.93/1.24  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.93/1.24  tff('#skF_4', type, '#skF_4': $i).
% 1.93/1.24  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 1.93/1.24  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.93/1.24  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.93/1.24  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.93/1.24  
% 1.93/1.25  tff(f_63, negated_conjecture, ~(![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (r1_tarski(k6_relat_1(C), D) => (r1_tarski(C, k1_relset_1(A, B, D)) & r1_tarski(C, k2_relset_1(A, B, D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t30_relset_1)).
% 1.93/1.25  tff(f_46, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 1.93/1.25  tff(f_27, axiom, (![A]: v1_relat_1(k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 1.93/1.25  tff(f_42, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 1.93/1.25  tff(f_38, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(A, B) => (r1_tarski(k1_relat_1(A), k1_relat_1(B)) & r1_tarski(k2_relat_1(A), k2_relat_1(B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t25_relat_1)).
% 1.93/1.25  tff(f_54, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 1.93/1.25  tff(f_50, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 1.93/1.25  tff(c_22, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_63])).
% 1.93/1.25  tff(c_42, plain, (![C_18, A_19, B_20]: (v1_relat_1(C_18) | ~m1_subset_1(C_18, k1_zfmisc_1(k2_zfmisc_1(A_19, B_20))))), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.93/1.25  tff(c_46, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_22, c_42])).
% 1.93/1.25  tff(c_20, plain, (r1_tarski(k6_relat_1('#skF_3'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_63])).
% 1.93/1.25  tff(c_2, plain, (![A_1]: (v1_relat_1(k6_relat_1(A_1)))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.93/1.25  tff(c_10, plain, (![A_5]: (k2_relat_1(k6_relat_1(A_5))=A_5)), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.93/1.25  tff(c_47, plain, (![A_21, B_22]: (r1_tarski(k2_relat_1(A_21), k2_relat_1(B_22)) | ~r1_tarski(A_21, B_22) | ~v1_relat_1(B_22) | ~v1_relat_1(A_21))), inference(cnfTransformation, [status(thm)], [f_38])).
% 1.93/1.25  tff(c_50, plain, (![A_5, B_22]: (r1_tarski(A_5, k2_relat_1(B_22)) | ~r1_tarski(k6_relat_1(A_5), B_22) | ~v1_relat_1(B_22) | ~v1_relat_1(k6_relat_1(A_5)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_47])).
% 1.93/1.25  tff(c_58, plain, (![A_23, B_24]: (r1_tarski(A_23, k2_relat_1(B_24)) | ~r1_tarski(k6_relat_1(A_23), B_24) | ~v1_relat_1(B_24))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_50])).
% 1.93/1.25  tff(c_61, plain, (r1_tarski('#skF_3', k2_relat_1('#skF_4')) | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_20, c_58])).
% 1.93/1.25  tff(c_64, plain, (r1_tarski('#skF_3', k2_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_61])).
% 1.93/1.25  tff(c_120, plain, (![A_41, B_42, C_43]: (k2_relset_1(A_41, B_42, C_43)=k2_relat_1(C_43) | ~m1_subset_1(C_43, k1_zfmisc_1(k2_zfmisc_1(A_41, B_42))))), inference(cnfTransformation, [status(thm)], [f_54])).
% 1.93/1.25  tff(c_124, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_22, c_120])).
% 1.93/1.25  tff(c_78, plain, (![A_32, B_33, C_34]: (k1_relset_1(A_32, B_33, C_34)=k1_relat_1(C_34) | ~m1_subset_1(C_34, k1_zfmisc_1(k2_zfmisc_1(A_32, B_33))))), inference(cnfTransformation, [status(thm)], [f_50])).
% 1.93/1.25  tff(c_82, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_22, c_78])).
% 1.93/1.25  tff(c_18, plain, (~r1_tarski('#skF_3', k2_relset_1('#skF_1', '#skF_2', '#skF_4')) | ~r1_tarski('#skF_3', k1_relset_1('#skF_1', '#skF_2', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_63])).
% 1.93/1.25  tff(c_65, plain, (~r1_tarski('#skF_3', k1_relset_1('#skF_1', '#skF_2', '#skF_4'))), inference(splitLeft, [status(thm)], [c_18])).
% 1.93/1.25  tff(c_87, plain, (~r1_tarski('#skF_3', k1_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_65])).
% 1.93/1.25  tff(c_8, plain, (![A_5]: (k1_relat_1(k6_relat_1(A_5))=A_5)), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.93/1.25  tff(c_92, plain, (![A_35, B_36]: (r1_tarski(k1_relat_1(A_35), k1_relat_1(B_36)) | ~r1_tarski(A_35, B_36) | ~v1_relat_1(B_36) | ~v1_relat_1(A_35))), inference(cnfTransformation, [status(thm)], [f_38])).
% 1.93/1.25  tff(c_95, plain, (![A_5, B_36]: (r1_tarski(A_5, k1_relat_1(B_36)) | ~r1_tarski(k6_relat_1(A_5), B_36) | ~v1_relat_1(B_36) | ~v1_relat_1(k6_relat_1(A_5)))), inference(superposition, [status(thm), theory('equality')], [c_8, c_92])).
% 1.93/1.25  tff(c_103, plain, (![A_37, B_38]: (r1_tarski(A_37, k1_relat_1(B_38)) | ~r1_tarski(k6_relat_1(A_37), B_38) | ~v1_relat_1(B_38))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_95])).
% 1.93/1.25  tff(c_106, plain, (r1_tarski('#skF_3', k1_relat_1('#skF_4')) | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_20, c_103])).
% 1.93/1.25  tff(c_109, plain, (r1_tarski('#skF_3', k1_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_106])).
% 1.93/1.25  tff(c_111, plain, $false, inference(negUnitSimplification, [status(thm)], [c_87, c_109])).
% 1.93/1.25  tff(c_112, plain, (~r1_tarski('#skF_3', k2_relset_1('#skF_1', '#skF_2', '#skF_4'))), inference(splitRight, [status(thm)], [c_18])).
% 1.93/1.25  tff(c_125, plain, (~r1_tarski('#skF_3', k2_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_124, c_112])).
% 1.93/1.25  tff(c_128, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_64, c_125])).
% 1.93/1.25  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.93/1.25  
% 1.93/1.25  Inference rules
% 1.93/1.25  ----------------------
% 1.93/1.25  #Ref     : 0
% 1.93/1.25  #Sup     : 20
% 1.93/1.25  #Fact    : 0
% 1.93/1.25  #Define  : 0
% 1.93/1.25  #Split   : 1
% 1.93/1.25  #Chain   : 0
% 1.93/1.25  #Close   : 0
% 1.93/1.25  
% 1.93/1.25  Ordering : KBO
% 1.93/1.25  
% 1.93/1.25  Simplification rules
% 1.93/1.25  ----------------------
% 1.93/1.25  #Subsume      : 0
% 1.93/1.25  #Demod        : 11
% 1.93/1.25  #Tautology    : 8
% 1.93/1.25  #SimpNegUnit  : 1
% 1.93/1.25  #BackRed      : 2
% 1.93/1.25  
% 1.93/1.25  #Partial instantiations: 0
% 1.93/1.25  #Strategies tried      : 1
% 1.93/1.25  
% 1.93/1.25  Timing (in seconds)
% 1.93/1.25  ----------------------
% 1.93/1.26  Preprocessing        : 0.30
% 1.93/1.26  Parsing              : 0.16
% 1.93/1.26  CNF conversion       : 0.02
% 1.93/1.26  Main loop            : 0.14
% 1.93/1.26  Inferencing          : 0.06
% 1.93/1.26  Reduction            : 0.04
% 1.93/1.26  Demodulation         : 0.03
% 1.93/1.26  BG Simplification    : 0.01
% 1.93/1.26  Subsumption          : 0.02
% 1.93/1.26  Abstraction          : 0.01
% 1.93/1.26  MUC search           : 0.00
% 1.93/1.26  Cooper               : 0.00
% 1.93/1.26  Total                : 0.47
% 1.93/1.26  Index Insertion      : 0.00
% 1.93/1.26  Index Deletion       : 0.00
% 1.93/1.26  Index Matching       : 0.00
% 1.93/1.26  BG Taut test         : 0.00
%------------------------------------------------------------------------------
