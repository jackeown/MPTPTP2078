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
% DateTime   : Thu Dec  3 10:13:46 EST 2020

% Result     : Theorem 1.93s
% Output     : CNFRefutation 1.98s
% Verified   : 
% Statistics : Number of formulae       :   48 (  62 expanded)
%              Number of leaves         :   26 (  34 expanded)
%              Depth                    :    8
%              Number of atoms          :   63 ( 107 expanded)
%              Number of equality atoms :   10 (  10 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_partfun1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_relset_1,type,(
    r2_relset_1: ( $i * $i * $i * $i ) > $o )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

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

tff(k2_partfun1,type,(
    k2_partfun1: ( $i * $i * $i * $i ) > $i )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_75,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( r1_tarski(A,C)
         => r2_relset_1(A,B,k2_partfun1(A,B,D,C),D) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_funct_2)).

tff(f_58,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_44,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_50,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_40,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => ! [C] :
          ( ( v1_relat_1(C)
            & v4_relat_1(C,A) )
         => v4_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t217_relat_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_64,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => k2_partfun1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

tff(c_22,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_53,plain,(
    ! [A_32,B_33,D_34] :
      ( r2_relset_1(A_32,B_33,D_34,D_34)
      | ~ m1_subset_1(D_34,k1_zfmisc_1(k2_zfmisc_1(A_32,B_33))) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_56,plain,(
    r2_relset_1('#skF_1','#skF_2','#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_22,c_53])).

tff(c_20,plain,(
    r1_tarski('#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_27,plain,(
    ! [C_21,A_22,B_23] :
      ( v1_relat_1(C_21)
      | ~ m1_subset_1(C_21,k1_zfmisc_1(k2_zfmisc_1(A_22,B_23))) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_31,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_22,c_27])).

tff(c_32,plain,(
    ! [C_24,A_25,B_26] :
      ( v4_relat_1(C_24,A_25)
      | ~ m1_subset_1(C_24,k1_zfmisc_1(k2_zfmisc_1(A_25,B_26))) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_36,plain,(
    v4_relat_1('#skF_4','#skF_1') ),
    inference(resolution,[status(thm)],[c_22,c_32])).

tff(c_57,plain,(
    ! [C_35,B_36,A_37] :
      ( v4_relat_1(C_35,B_36)
      | ~ v4_relat_1(C_35,A_37)
      | ~ v1_relat_1(C_35)
      | ~ r1_tarski(A_37,B_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_59,plain,(
    ! [B_36] :
      ( v4_relat_1('#skF_4',B_36)
      | ~ v1_relat_1('#skF_4')
      | ~ r1_tarski('#skF_1',B_36) ) ),
    inference(resolution,[status(thm)],[c_36,c_57])).

tff(c_63,plain,(
    ! [B_38] :
      ( v4_relat_1('#skF_4',B_38)
      | ~ r1_tarski('#skF_1',B_38) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_31,c_59])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( k7_relat_1(B_2,A_1) = B_2
      | ~ v4_relat_1(B_2,A_1)
      | ~ v1_relat_1(B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_68,plain,(
    ! [B_38] :
      ( k7_relat_1('#skF_4',B_38) = '#skF_4'
      | ~ v1_relat_1('#skF_4')
      | ~ r1_tarski('#skF_1',B_38) ) ),
    inference(resolution,[status(thm)],[c_63,c_2])).

tff(c_75,plain,(
    ! [B_39] :
      ( k7_relat_1('#skF_4',B_39) = '#skF_4'
      | ~ r1_tarski('#skF_1',B_39) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_31,c_68])).

tff(c_79,plain,(
    k7_relat_1('#skF_4','#skF_3') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_20,c_75])).

tff(c_26,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_89,plain,(
    ! [A_42,B_43,C_44,D_45] :
      ( k2_partfun1(A_42,B_43,C_44,D_45) = k7_relat_1(C_44,D_45)
      | ~ m1_subset_1(C_44,k1_zfmisc_1(k2_zfmisc_1(A_42,B_43)))
      | ~ v1_funct_1(C_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_91,plain,(
    ! [D_45] :
      ( k2_partfun1('#skF_1','#skF_2','#skF_4',D_45) = k7_relat_1('#skF_4',D_45)
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_22,c_89])).

tff(c_94,plain,(
    ! [D_45] : k2_partfun1('#skF_1','#skF_2','#skF_4',D_45) = k7_relat_1('#skF_4',D_45) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_91])).

tff(c_18,plain,(
    ~ r2_relset_1('#skF_1','#skF_2',k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_95,plain,(
    ~ r2_relset_1('#skF_1','#skF_2',k7_relat_1('#skF_4','#skF_3'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_18])).

tff(c_98,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_79,c_95])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n006.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 16:59:07 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.93/1.21  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.93/1.22  
% 1.93/1.22  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.98/1.22  %$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_partfun1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 1.98/1.22  
% 1.98/1.22  %Foreground sorts:
% 1.98/1.22  
% 1.98/1.22  
% 1.98/1.22  %Background operators:
% 1.98/1.22  
% 1.98/1.22  
% 1.98/1.22  %Foreground operators:
% 1.98/1.22  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 1.98/1.22  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.98/1.22  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 1.98/1.22  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 1.98/1.22  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.98/1.22  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 1.98/1.22  tff('#skF_2', type, '#skF_2': $i).
% 1.98/1.22  tff('#skF_3', type, '#skF_3': $i).
% 1.98/1.22  tff('#skF_1', type, '#skF_1': $i).
% 1.98/1.22  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 1.98/1.22  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.98/1.22  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.98/1.22  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.98/1.22  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.98/1.22  tff('#skF_4', type, '#skF_4': $i).
% 1.98/1.22  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.98/1.22  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 1.98/1.22  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 1.98/1.22  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.98/1.22  
% 1.98/1.23  tff(f_75, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r1_tarski(A, C) => r2_relset_1(A, B, k2_partfun1(A, B, D, C), D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t40_funct_2)).
% 1.98/1.23  tff(f_58, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 1.98/1.23  tff(f_44, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 1.98/1.23  tff(f_50, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 1.98/1.23  tff(f_40, axiom, (![A, B]: (r1_tarski(A, B) => (![C]: ((v1_relat_1(C) & v4_relat_1(C, A)) => v4_relat_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t217_relat_1)).
% 1.98/1.23  tff(f_31, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t209_relat_1)).
% 1.98/1.23  tff(f_64, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (k2_partfun1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_partfun1)).
% 1.98/1.23  tff(c_22, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_75])).
% 1.98/1.23  tff(c_53, plain, (![A_32, B_33, D_34]: (r2_relset_1(A_32, B_33, D_34, D_34) | ~m1_subset_1(D_34, k1_zfmisc_1(k2_zfmisc_1(A_32, B_33))))), inference(cnfTransformation, [status(thm)], [f_58])).
% 1.98/1.23  tff(c_56, plain, (r2_relset_1('#skF_1', '#skF_2', '#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_22, c_53])).
% 1.98/1.23  tff(c_20, plain, (r1_tarski('#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_75])).
% 1.98/1.23  tff(c_27, plain, (![C_21, A_22, B_23]: (v1_relat_1(C_21) | ~m1_subset_1(C_21, k1_zfmisc_1(k2_zfmisc_1(A_22, B_23))))), inference(cnfTransformation, [status(thm)], [f_44])).
% 1.98/1.23  tff(c_31, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_22, c_27])).
% 1.98/1.23  tff(c_32, plain, (![C_24, A_25, B_26]: (v4_relat_1(C_24, A_25) | ~m1_subset_1(C_24, k1_zfmisc_1(k2_zfmisc_1(A_25, B_26))))), inference(cnfTransformation, [status(thm)], [f_50])).
% 1.98/1.23  tff(c_36, plain, (v4_relat_1('#skF_4', '#skF_1')), inference(resolution, [status(thm)], [c_22, c_32])).
% 1.98/1.23  tff(c_57, plain, (![C_35, B_36, A_37]: (v4_relat_1(C_35, B_36) | ~v4_relat_1(C_35, A_37) | ~v1_relat_1(C_35) | ~r1_tarski(A_37, B_36))), inference(cnfTransformation, [status(thm)], [f_40])).
% 1.98/1.23  tff(c_59, plain, (![B_36]: (v4_relat_1('#skF_4', B_36) | ~v1_relat_1('#skF_4') | ~r1_tarski('#skF_1', B_36))), inference(resolution, [status(thm)], [c_36, c_57])).
% 1.98/1.23  tff(c_63, plain, (![B_38]: (v4_relat_1('#skF_4', B_38) | ~r1_tarski('#skF_1', B_38))), inference(demodulation, [status(thm), theory('equality')], [c_31, c_59])).
% 1.98/1.23  tff(c_2, plain, (![B_2, A_1]: (k7_relat_1(B_2, A_1)=B_2 | ~v4_relat_1(B_2, A_1) | ~v1_relat_1(B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.98/1.23  tff(c_68, plain, (![B_38]: (k7_relat_1('#skF_4', B_38)='#skF_4' | ~v1_relat_1('#skF_4') | ~r1_tarski('#skF_1', B_38))), inference(resolution, [status(thm)], [c_63, c_2])).
% 1.98/1.23  tff(c_75, plain, (![B_39]: (k7_relat_1('#skF_4', B_39)='#skF_4' | ~r1_tarski('#skF_1', B_39))), inference(demodulation, [status(thm), theory('equality')], [c_31, c_68])).
% 1.98/1.23  tff(c_79, plain, (k7_relat_1('#skF_4', '#skF_3')='#skF_4'), inference(resolution, [status(thm)], [c_20, c_75])).
% 1.98/1.23  tff(c_26, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_75])).
% 1.98/1.23  tff(c_89, plain, (![A_42, B_43, C_44, D_45]: (k2_partfun1(A_42, B_43, C_44, D_45)=k7_relat_1(C_44, D_45) | ~m1_subset_1(C_44, k1_zfmisc_1(k2_zfmisc_1(A_42, B_43))) | ~v1_funct_1(C_44))), inference(cnfTransformation, [status(thm)], [f_64])).
% 1.98/1.23  tff(c_91, plain, (![D_45]: (k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_45)=k7_relat_1('#skF_4', D_45) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_22, c_89])).
% 1.98/1.23  tff(c_94, plain, (![D_45]: (k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_45)=k7_relat_1('#skF_4', D_45))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_91])).
% 1.98/1.23  tff(c_18, plain, (~r2_relset_1('#skF_1', '#skF_2', k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_75])).
% 1.98/1.23  tff(c_95, plain, (~r2_relset_1('#skF_1', '#skF_2', k7_relat_1('#skF_4', '#skF_3'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_94, c_18])).
% 1.98/1.23  tff(c_98, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_56, c_79, c_95])).
% 1.98/1.23  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.98/1.23  
% 1.98/1.23  Inference rules
% 1.98/1.23  ----------------------
% 1.98/1.23  #Ref     : 0
% 1.98/1.23  #Sup     : 15
% 1.98/1.23  #Fact    : 0
% 1.98/1.23  #Define  : 0
% 1.98/1.23  #Split   : 1
% 1.98/1.23  #Chain   : 0
% 1.98/1.23  #Close   : 0
% 1.98/1.23  
% 1.98/1.23  Ordering : KBO
% 1.98/1.23  
% 1.98/1.23  Simplification rules
% 1.98/1.23  ----------------------
% 1.98/1.23  #Subsume      : 0
% 1.98/1.23  #Demod        : 8
% 1.98/1.23  #Tautology    : 4
% 1.98/1.23  #SimpNegUnit  : 0
% 1.98/1.23  #BackRed      : 1
% 1.98/1.24  
% 1.98/1.24  #Partial instantiations: 0
% 1.98/1.24  #Strategies tried      : 1
% 1.98/1.24  
% 1.98/1.24  Timing (in seconds)
% 1.98/1.24  ----------------------
% 1.98/1.24  Preprocessing        : 0.32
% 1.98/1.24  Parsing              : 0.17
% 1.98/1.24  CNF conversion       : 0.02
% 1.98/1.24  Main loop            : 0.11
% 1.98/1.24  Inferencing          : 0.04
% 1.98/1.24  Reduction            : 0.04
% 1.98/1.24  Demodulation         : 0.03
% 1.98/1.24  BG Simplification    : 0.01
% 1.98/1.24  Subsumption          : 0.02
% 1.98/1.24  Abstraction          : 0.01
% 1.98/1.24  MUC search           : 0.00
% 1.98/1.24  Cooper               : 0.00
% 1.98/1.24  Total                : 0.46
% 1.98/1.24  Index Insertion      : 0.00
% 1.98/1.24  Index Deletion       : 0.00
% 1.98/1.24  Index Matching       : 0.00
% 1.98/1.24  BG Taut test         : 0.00
%------------------------------------------------------------------------------
