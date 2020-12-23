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
% DateTime   : Thu Dec  3 10:13:46 EST 2020

% Result     : Theorem 1.91s
% Output     : CNFRefutation 1.91s
% Verified   : 
% Statistics : Number of formulae       :   58 (  79 expanded)
%              Number of leaves         :   29 (  40 expanded)
%              Depth                    :   10
%              Number of atoms          :   77 ( 138 expanded)
%              Number of equality atoms :   13 (  13 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_partfun1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_80,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( r1_tarski(A,C)
         => r2_relset_1(A,B,k2_partfun1(A,B,D,C),D) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_funct_2)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_57,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k1_relat_1(k7_relat_1(B,A)),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_relat_1)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k1_relat_1(B),A)
       => k7_relat_1(B,A) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t97_relat_1)).

tff(f_69,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => k2_partfun1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

tff(f_63,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => r2_relset_1(A,B,C,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',reflexivity_r2_relset_1)).

tff(c_24,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_29,plain,(
    ! [C_24,A_25,B_26] :
      ( v1_relat_1(C_24)
      | ~ m1_subset_1(C_24,k1_zfmisc_1(k2_zfmisc_1(A_25,B_26))) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_33,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_24,c_29])).

tff(c_41,plain,(
    ! [C_34,A_35,B_36] :
      ( v4_relat_1(C_34,A_35)
      | ~ m1_subset_1(C_34,k1_zfmisc_1(k2_zfmisc_1(A_35,B_36))) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_45,plain,(
    v4_relat_1('#skF_4','#skF_1') ),
    inference(resolution,[status(thm)],[c_24,c_41])).

tff(c_4,plain,(
    ! [B_5,A_4] :
      ( k7_relat_1(B_5,A_4) = B_5
      | ~ v4_relat_1(B_5,A_4)
      | ~ v1_relat_1(B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_48,plain,
    ( k7_relat_1('#skF_4','#skF_1') = '#skF_4'
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_45,c_4])).

tff(c_51,plain,(
    k7_relat_1('#skF_4','#skF_1') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_33,c_48])).

tff(c_6,plain,(
    ! [B_7,A_6] :
      ( r1_tarski(k1_relat_1(k7_relat_1(B_7,A_6)),A_6)
      | ~ v1_relat_1(B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_55,plain,
    ( r1_tarski(k1_relat_1('#skF_4'),'#skF_1')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_51,c_6])).

tff(c_59,plain,(
    r1_tarski(k1_relat_1('#skF_4'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_33,c_55])).

tff(c_22,plain,(
    r1_tarski('#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_61,plain,(
    ! [A_37,C_38,B_39] :
      ( r1_tarski(A_37,C_38)
      | ~ r1_tarski(B_39,C_38)
      | ~ r1_tarski(A_37,B_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_70,plain,(
    ! [A_37] :
      ( r1_tarski(A_37,'#skF_3')
      | ~ r1_tarski(A_37,'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_22,c_61])).

tff(c_103,plain,(
    ! [B_45,A_46] :
      ( k7_relat_1(B_45,A_46) = B_45
      | ~ r1_tarski(k1_relat_1(B_45),A_46)
      | ~ v1_relat_1(B_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_123,plain,(
    ! [B_47] :
      ( k7_relat_1(B_47,'#skF_3') = B_47
      | ~ v1_relat_1(B_47)
      | ~ r1_tarski(k1_relat_1(B_47),'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_70,c_103])).

tff(c_129,plain,
    ( k7_relat_1('#skF_4','#skF_3') = '#skF_4'
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_59,c_123])).

tff(c_137,plain,(
    k7_relat_1('#skF_4','#skF_3') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_33,c_129])).

tff(c_28,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_148,plain,(
    ! [A_48,B_49,C_50,D_51] :
      ( k2_partfun1(A_48,B_49,C_50,D_51) = k7_relat_1(C_50,D_51)
      | ~ m1_subset_1(C_50,k1_zfmisc_1(k2_zfmisc_1(A_48,B_49)))
      | ~ v1_funct_1(C_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_150,plain,(
    ! [D_51] :
      ( k2_partfun1('#skF_1','#skF_2','#skF_4',D_51) = k7_relat_1('#skF_4',D_51)
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_24,c_148])).

tff(c_153,plain,(
    ! [D_51] : k2_partfun1('#skF_1','#skF_2','#skF_4',D_51) = k7_relat_1('#skF_4',D_51) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_150])).

tff(c_20,plain,(
    ~ r2_relset_1('#skF_1','#skF_2',k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_173,plain,(
    ~ r2_relset_1('#skF_1','#skF_2',k7_relat_1('#skF_4','#skF_3'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_153,c_20])).

tff(c_174,plain,(
    ~ r2_relset_1('#skF_1','#skF_2','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_137,c_173])).

tff(c_244,plain,(
    ! [A_64,B_65,C_66,D_67] :
      ( r2_relset_1(A_64,B_65,C_66,C_66)
      | ~ m1_subset_1(D_67,k1_zfmisc_1(k2_zfmisc_1(A_64,B_65)))
      | ~ m1_subset_1(C_66,k1_zfmisc_1(k2_zfmisc_1(A_64,B_65))) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_248,plain,(
    ! [C_68] :
      ( r2_relset_1('#skF_1','#skF_2',C_68,C_68)
      | ~ m1_subset_1(C_68,k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ) ),
    inference(resolution,[status(thm)],[c_24,c_244])).

tff(c_250,plain,(
    r2_relset_1('#skF_1','#skF_2','#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_24,c_248])).

tff(c_254,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_174,c_250])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.01/0.06  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.01/0.07  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.06/0.25  % Computer   : n007.cluster.edu
% 0.06/0.25  % Model      : x86_64 x86_64
% 0.06/0.25  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.06/0.25  % Memory     : 8042.1875MB
% 0.06/0.25  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.06/0.25  % CPULimit   : 60
% 0.06/0.25  % DateTime   : Tue Dec  1 21:02:51 EST 2020
% 0.06/0.25  % CPUTime    : 
% 0.06/0.25  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.91/1.01  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.91/1.02  
% 1.91/1.02  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.91/1.02  %$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_partfun1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 1.91/1.02  
% 1.91/1.02  %Foreground sorts:
% 1.91/1.02  
% 1.91/1.02  
% 1.91/1.02  %Background operators:
% 1.91/1.02  
% 1.91/1.02  
% 1.91/1.02  %Foreground operators:
% 1.91/1.02  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 1.91/1.02  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.91/1.02  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 1.91/1.02  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 1.91/1.02  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.91/1.02  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 1.91/1.02  tff('#skF_2', type, '#skF_2': $i).
% 1.91/1.02  tff('#skF_3', type, '#skF_3': $i).
% 1.91/1.02  tff('#skF_1', type, '#skF_1': $i).
% 1.91/1.02  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 1.91/1.02  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.91/1.02  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.91/1.02  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.91/1.02  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.91/1.02  tff('#skF_4', type, '#skF_4': $i).
% 1.91/1.02  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.91/1.02  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 1.91/1.02  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 1.91/1.02  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.91/1.02  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.91/1.02  
% 1.91/1.03  tff(f_80, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r1_tarski(A, C) => r2_relset_1(A, B, k2_partfun1(A, B, D, C), D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t40_funct_2)).
% 1.91/1.03  tff(f_51, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 1.91/1.03  tff(f_57, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 1.91/1.03  tff(f_37, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t209_relat_1)).
% 1.91/1.03  tff(f_41, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k7_relat_1(B, A)), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t87_relat_1)).
% 1.91/1.03  tff(f_31, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 1.91/1.03  tff(f_47, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(B), A) => (k7_relat_1(B, A) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t97_relat_1)).
% 1.91/1.03  tff(f_69, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (k2_partfun1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_partfun1)).
% 1.91/1.03  tff(f_63, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => r2_relset_1(A, B, C, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', reflexivity_r2_relset_1)).
% 1.91/1.03  tff(c_24, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_80])).
% 1.91/1.03  tff(c_29, plain, (![C_24, A_25, B_26]: (v1_relat_1(C_24) | ~m1_subset_1(C_24, k1_zfmisc_1(k2_zfmisc_1(A_25, B_26))))), inference(cnfTransformation, [status(thm)], [f_51])).
% 1.91/1.03  tff(c_33, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_24, c_29])).
% 1.91/1.03  tff(c_41, plain, (![C_34, A_35, B_36]: (v4_relat_1(C_34, A_35) | ~m1_subset_1(C_34, k1_zfmisc_1(k2_zfmisc_1(A_35, B_36))))), inference(cnfTransformation, [status(thm)], [f_57])).
% 1.91/1.03  tff(c_45, plain, (v4_relat_1('#skF_4', '#skF_1')), inference(resolution, [status(thm)], [c_24, c_41])).
% 1.91/1.03  tff(c_4, plain, (![B_5, A_4]: (k7_relat_1(B_5, A_4)=B_5 | ~v4_relat_1(B_5, A_4) | ~v1_relat_1(B_5))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.91/1.03  tff(c_48, plain, (k7_relat_1('#skF_4', '#skF_1')='#skF_4' | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_45, c_4])).
% 1.91/1.03  tff(c_51, plain, (k7_relat_1('#skF_4', '#skF_1')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_33, c_48])).
% 1.91/1.03  tff(c_6, plain, (![B_7, A_6]: (r1_tarski(k1_relat_1(k7_relat_1(B_7, A_6)), A_6) | ~v1_relat_1(B_7))), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.91/1.03  tff(c_55, plain, (r1_tarski(k1_relat_1('#skF_4'), '#skF_1') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_51, c_6])).
% 1.91/1.03  tff(c_59, plain, (r1_tarski(k1_relat_1('#skF_4'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_33, c_55])).
% 1.91/1.03  tff(c_22, plain, (r1_tarski('#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_80])).
% 1.91/1.03  tff(c_61, plain, (![A_37, C_38, B_39]: (r1_tarski(A_37, C_38) | ~r1_tarski(B_39, C_38) | ~r1_tarski(A_37, B_39))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.91/1.03  tff(c_70, plain, (![A_37]: (r1_tarski(A_37, '#skF_3') | ~r1_tarski(A_37, '#skF_1'))), inference(resolution, [status(thm)], [c_22, c_61])).
% 1.91/1.03  tff(c_103, plain, (![B_45, A_46]: (k7_relat_1(B_45, A_46)=B_45 | ~r1_tarski(k1_relat_1(B_45), A_46) | ~v1_relat_1(B_45))), inference(cnfTransformation, [status(thm)], [f_47])).
% 1.91/1.03  tff(c_123, plain, (![B_47]: (k7_relat_1(B_47, '#skF_3')=B_47 | ~v1_relat_1(B_47) | ~r1_tarski(k1_relat_1(B_47), '#skF_1'))), inference(resolution, [status(thm)], [c_70, c_103])).
% 1.91/1.03  tff(c_129, plain, (k7_relat_1('#skF_4', '#skF_3')='#skF_4' | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_59, c_123])).
% 1.91/1.03  tff(c_137, plain, (k7_relat_1('#skF_4', '#skF_3')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_33, c_129])).
% 1.91/1.03  tff(c_28, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_80])).
% 1.91/1.03  tff(c_148, plain, (![A_48, B_49, C_50, D_51]: (k2_partfun1(A_48, B_49, C_50, D_51)=k7_relat_1(C_50, D_51) | ~m1_subset_1(C_50, k1_zfmisc_1(k2_zfmisc_1(A_48, B_49))) | ~v1_funct_1(C_50))), inference(cnfTransformation, [status(thm)], [f_69])).
% 1.91/1.03  tff(c_150, plain, (![D_51]: (k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_51)=k7_relat_1('#skF_4', D_51) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_24, c_148])).
% 1.91/1.03  tff(c_153, plain, (![D_51]: (k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_51)=k7_relat_1('#skF_4', D_51))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_150])).
% 1.91/1.03  tff(c_20, plain, (~r2_relset_1('#skF_1', '#skF_2', k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_80])).
% 1.91/1.03  tff(c_173, plain, (~r2_relset_1('#skF_1', '#skF_2', k7_relat_1('#skF_4', '#skF_3'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_153, c_20])).
% 1.91/1.03  tff(c_174, plain, (~r2_relset_1('#skF_1', '#skF_2', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_137, c_173])).
% 1.91/1.03  tff(c_244, plain, (![A_64, B_65, C_66, D_67]: (r2_relset_1(A_64, B_65, C_66, C_66) | ~m1_subset_1(D_67, k1_zfmisc_1(k2_zfmisc_1(A_64, B_65))) | ~m1_subset_1(C_66, k1_zfmisc_1(k2_zfmisc_1(A_64, B_65))))), inference(cnfTransformation, [status(thm)], [f_63])).
% 1.91/1.03  tff(c_248, plain, (![C_68]: (r2_relset_1('#skF_1', '#skF_2', C_68, C_68) | ~m1_subset_1(C_68, k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))))), inference(resolution, [status(thm)], [c_24, c_244])).
% 1.91/1.03  tff(c_250, plain, (r2_relset_1('#skF_1', '#skF_2', '#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_24, c_248])).
% 1.91/1.03  tff(c_254, plain, $false, inference(negUnitSimplification, [status(thm)], [c_174, c_250])).
% 1.91/1.03  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.91/1.03  
% 1.91/1.03  Inference rules
% 1.91/1.03  ----------------------
% 1.91/1.03  #Ref     : 0
% 1.91/1.03  #Sup     : 50
% 1.91/1.03  #Fact    : 0
% 1.91/1.03  #Define  : 0
% 1.91/1.03  #Split   : 1
% 1.91/1.03  #Chain   : 0
% 1.91/1.03  #Close   : 0
% 1.91/1.03  
% 1.91/1.03  Ordering : KBO
% 1.91/1.03  
% 1.91/1.03  Simplification rules
% 1.91/1.03  ----------------------
% 1.91/1.03  #Subsume      : 7
% 1.91/1.03  #Demod        : 19
% 1.91/1.03  #Tautology    : 11
% 1.91/1.03  #SimpNegUnit  : 1
% 1.91/1.03  #BackRed      : 1
% 1.91/1.03  
% 1.91/1.03  #Partial instantiations: 0
% 1.91/1.03  #Strategies tried      : 1
% 1.91/1.03  
% 1.91/1.03  Timing (in seconds)
% 1.91/1.03  ----------------------
% 1.91/1.04  Preprocessing        : 0.28
% 1.91/1.04  Parsing              : 0.15
% 1.91/1.04  CNF conversion       : 0.02
% 1.91/1.04  Main loop            : 0.20
% 1.91/1.04  Inferencing          : 0.08
% 1.91/1.04  Reduction            : 0.06
% 1.91/1.04  Demodulation         : 0.04
% 1.91/1.04  BG Simplification    : 0.01
% 1.91/1.04  Subsumption          : 0.04
% 1.91/1.04  Abstraction          : 0.01
% 1.91/1.04  MUC search           : 0.00
% 1.91/1.04  Cooper               : 0.00
% 1.91/1.04  Total                : 0.51
% 1.91/1.04  Index Insertion      : 0.00
% 1.91/1.04  Index Deletion       : 0.00
% 1.91/1.04  Index Matching       : 0.00
% 1.91/1.04  BG Taut test         : 0.00
%------------------------------------------------------------------------------
