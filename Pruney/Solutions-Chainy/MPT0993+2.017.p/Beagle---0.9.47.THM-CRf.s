%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:13:44 EST 2020

% Result     : Theorem 2.32s
% Output     : CNFRefutation 2.53s
% Verified   : 
% Statistics : Number of formulae       :   56 (  70 expanded)
%              Number of leaves         :   28 (  37 expanded)
%              Depth                    :    9
%              Number of atoms          :   79 ( 127 expanded)
%              Number of equality atoms :   10 (  10 expanded)
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

tff(f_76,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( r1_tarski(A,C)
         => r2_relset_1(A,B,k2_partfun1(A,B,D,C),D) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_funct_2)).

tff(f_47,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_53,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_37,axiom,(
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

tff(f_43,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k1_relat_1(B),A)
       => k7_relat_1(B,A) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t97_relat_1)).

tff(f_65,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => k2_partfun1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

tff(f_59,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => r2_relset_1(A,B,C,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',reflexivity_r2_relset_1)).

tff(c_24,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_29,plain,(
    ! [C_22,A_23,B_24] :
      ( v1_relat_1(C_22)
      | ~ m1_subset_1(C_22,k1_zfmisc_1(k2_zfmisc_1(A_23,B_24))) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_33,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_24,c_29])).

tff(c_45,plain,(
    ! [C_32,A_33,B_34] :
      ( v4_relat_1(C_32,A_33)
      | ~ m1_subset_1(C_32,k1_zfmisc_1(k2_zfmisc_1(A_33,B_34))) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_49,plain,(
    v4_relat_1('#skF_4','#skF_1') ),
    inference(resolution,[status(thm)],[c_24,c_45])).

tff(c_6,plain,(
    ! [B_5,A_4] :
      ( r1_tarski(k1_relat_1(B_5),A_4)
      | ~ v4_relat_1(B_5,A_4)
      | ~ v1_relat_1(B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_22,plain,(
    r1_tarski('#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_50,plain,(
    ! [A_35,C_36,B_37] :
      ( r1_tarski(A_35,C_36)
      | ~ r1_tarski(B_37,C_36)
      | ~ r1_tarski(A_35,B_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_57,plain,(
    ! [A_38] :
      ( r1_tarski(A_38,'#skF_3')
      | ~ r1_tarski(A_38,'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_22,c_50])).

tff(c_4,plain,(
    ! [B_5,A_4] :
      ( v4_relat_1(B_5,A_4)
      | ~ r1_tarski(k1_relat_1(B_5),A_4)
      | ~ v1_relat_1(B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_98,plain,(
    ! [B_45] :
      ( v4_relat_1(B_45,'#skF_3')
      | ~ v1_relat_1(B_45)
      | ~ r1_tarski(k1_relat_1(B_45),'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_57,c_4])).

tff(c_104,plain,(
    ! [B_46] :
      ( v4_relat_1(B_46,'#skF_3')
      | ~ v4_relat_1(B_46,'#skF_1')
      | ~ v1_relat_1(B_46) ) ),
    inference(resolution,[status(thm)],[c_6,c_98])).

tff(c_66,plain,(
    ! [B_39,A_40] :
      ( k7_relat_1(B_39,A_40) = B_39
      | ~ r1_tarski(k1_relat_1(B_39),A_40)
      | ~ v1_relat_1(B_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_75,plain,(
    ! [B_5,A_4] :
      ( k7_relat_1(B_5,A_4) = B_5
      | ~ v4_relat_1(B_5,A_4)
      | ~ v1_relat_1(B_5) ) ),
    inference(resolution,[status(thm)],[c_6,c_66])).

tff(c_109,plain,(
    ! [B_47] :
      ( k7_relat_1(B_47,'#skF_3') = B_47
      | ~ v4_relat_1(B_47,'#skF_1')
      | ~ v1_relat_1(B_47) ) ),
    inference(resolution,[status(thm)],[c_104,c_75])).

tff(c_112,plain,
    ( k7_relat_1('#skF_4','#skF_3') = '#skF_4'
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_49,c_109])).

tff(c_115,plain,(
    k7_relat_1('#skF_4','#skF_3') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_33,c_112])).

tff(c_28,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_131,plain,(
    ! [A_52,B_53,C_54,D_55] :
      ( k2_partfun1(A_52,B_53,C_54,D_55) = k7_relat_1(C_54,D_55)
      | ~ m1_subset_1(C_54,k1_zfmisc_1(k2_zfmisc_1(A_52,B_53)))
      | ~ v1_funct_1(C_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_133,plain,(
    ! [D_55] :
      ( k2_partfun1('#skF_1','#skF_2','#skF_4',D_55) = k7_relat_1('#skF_4',D_55)
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_24,c_131])).

tff(c_136,plain,(
    ! [D_55] : k2_partfun1('#skF_1','#skF_2','#skF_4',D_55) = k7_relat_1('#skF_4',D_55) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_133])).

tff(c_20,plain,(
    ~ r2_relset_1('#skF_1','#skF_2',k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_137,plain,(
    ~ r2_relset_1('#skF_1','#skF_2',k7_relat_1('#skF_4','#skF_3'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_136,c_20])).

tff(c_138,plain,(
    ~ r2_relset_1('#skF_1','#skF_2','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_115,c_137])).

tff(c_169,plain,(
    ! [A_63,B_64,C_65,D_66] :
      ( r2_relset_1(A_63,B_64,C_65,C_65)
      | ~ m1_subset_1(D_66,k1_zfmisc_1(k2_zfmisc_1(A_63,B_64)))
      | ~ m1_subset_1(C_65,k1_zfmisc_1(k2_zfmisc_1(A_63,B_64))) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_173,plain,(
    ! [C_67] :
      ( r2_relset_1('#skF_1','#skF_2',C_67,C_67)
      | ~ m1_subset_1(C_67,k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ) ),
    inference(resolution,[status(thm)],[c_24,c_169])).

tff(c_175,plain,(
    r2_relset_1('#skF_1','#skF_2','#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_24,c_173])).

tff(c_179,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_138,c_175])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.33  % Computer   : n005.cluster.edu
% 0.14/0.33  % Model      : x86_64 x86_64
% 0.14/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.33  % Memory     : 8042.1875MB
% 0.14/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.33  % CPULimit   : 60
% 0.14/0.33  % DateTime   : Tue Dec  1 18:27:32 EST 2020
% 0.14/0.33  % CPUTime    : 
% 0.14/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.32/1.59  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.32/1.60  
% 2.32/1.60  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.32/1.60  %$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_partfun1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.32/1.60  
% 2.32/1.60  %Foreground sorts:
% 2.32/1.60  
% 2.32/1.60  
% 2.32/1.60  %Background operators:
% 2.32/1.60  
% 2.32/1.60  
% 2.32/1.60  %Foreground operators:
% 2.32/1.60  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.32/1.60  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.32/1.60  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 2.32/1.60  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.32/1.60  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.32/1.60  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.32/1.60  tff('#skF_2', type, '#skF_2': $i).
% 2.32/1.60  tff('#skF_3', type, '#skF_3': $i).
% 2.32/1.60  tff('#skF_1', type, '#skF_1': $i).
% 2.32/1.60  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.32/1.60  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.32/1.60  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.32/1.60  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.32/1.60  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.32/1.60  tff('#skF_4', type, '#skF_4': $i).
% 2.32/1.60  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.32/1.60  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 2.32/1.60  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.32/1.60  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.32/1.60  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.32/1.60  
% 2.53/1.61  tff(f_76, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r1_tarski(A, C) => r2_relset_1(A, B, k2_partfun1(A, B, D, C), D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t40_funct_2)).
% 2.53/1.61  tff(f_47, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.53/1.61  tff(f_53, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.53/1.61  tff(f_37, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d18_relat_1)).
% 2.53/1.61  tff(f_31, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 2.53/1.61  tff(f_43, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(B), A) => (k7_relat_1(B, A) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t97_relat_1)).
% 2.53/1.61  tff(f_65, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (k2_partfun1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_partfun1)).
% 2.53/1.61  tff(f_59, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => r2_relset_1(A, B, C, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', reflexivity_r2_relset_1)).
% 2.53/1.61  tff(c_24, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.53/1.61  tff(c_29, plain, (![C_22, A_23, B_24]: (v1_relat_1(C_22) | ~m1_subset_1(C_22, k1_zfmisc_1(k2_zfmisc_1(A_23, B_24))))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.53/1.61  tff(c_33, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_24, c_29])).
% 2.53/1.61  tff(c_45, plain, (![C_32, A_33, B_34]: (v4_relat_1(C_32, A_33) | ~m1_subset_1(C_32, k1_zfmisc_1(k2_zfmisc_1(A_33, B_34))))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.53/1.61  tff(c_49, plain, (v4_relat_1('#skF_4', '#skF_1')), inference(resolution, [status(thm)], [c_24, c_45])).
% 2.53/1.61  tff(c_6, plain, (![B_5, A_4]: (r1_tarski(k1_relat_1(B_5), A_4) | ~v4_relat_1(B_5, A_4) | ~v1_relat_1(B_5))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.53/1.61  tff(c_22, plain, (r1_tarski('#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.53/1.61  tff(c_50, plain, (![A_35, C_36, B_37]: (r1_tarski(A_35, C_36) | ~r1_tarski(B_37, C_36) | ~r1_tarski(A_35, B_37))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.53/1.61  tff(c_57, plain, (![A_38]: (r1_tarski(A_38, '#skF_3') | ~r1_tarski(A_38, '#skF_1'))), inference(resolution, [status(thm)], [c_22, c_50])).
% 2.53/1.61  tff(c_4, plain, (![B_5, A_4]: (v4_relat_1(B_5, A_4) | ~r1_tarski(k1_relat_1(B_5), A_4) | ~v1_relat_1(B_5))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.53/1.61  tff(c_98, plain, (![B_45]: (v4_relat_1(B_45, '#skF_3') | ~v1_relat_1(B_45) | ~r1_tarski(k1_relat_1(B_45), '#skF_1'))), inference(resolution, [status(thm)], [c_57, c_4])).
% 2.53/1.61  tff(c_104, plain, (![B_46]: (v4_relat_1(B_46, '#skF_3') | ~v4_relat_1(B_46, '#skF_1') | ~v1_relat_1(B_46))), inference(resolution, [status(thm)], [c_6, c_98])).
% 2.53/1.61  tff(c_66, plain, (![B_39, A_40]: (k7_relat_1(B_39, A_40)=B_39 | ~r1_tarski(k1_relat_1(B_39), A_40) | ~v1_relat_1(B_39))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.53/1.61  tff(c_75, plain, (![B_5, A_4]: (k7_relat_1(B_5, A_4)=B_5 | ~v4_relat_1(B_5, A_4) | ~v1_relat_1(B_5))), inference(resolution, [status(thm)], [c_6, c_66])).
% 2.53/1.61  tff(c_109, plain, (![B_47]: (k7_relat_1(B_47, '#skF_3')=B_47 | ~v4_relat_1(B_47, '#skF_1') | ~v1_relat_1(B_47))), inference(resolution, [status(thm)], [c_104, c_75])).
% 2.53/1.61  tff(c_112, plain, (k7_relat_1('#skF_4', '#skF_3')='#skF_4' | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_49, c_109])).
% 2.53/1.61  tff(c_115, plain, (k7_relat_1('#skF_4', '#skF_3')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_33, c_112])).
% 2.53/1.61  tff(c_28, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.53/1.61  tff(c_131, plain, (![A_52, B_53, C_54, D_55]: (k2_partfun1(A_52, B_53, C_54, D_55)=k7_relat_1(C_54, D_55) | ~m1_subset_1(C_54, k1_zfmisc_1(k2_zfmisc_1(A_52, B_53))) | ~v1_funct_1(C_54))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.53/1.61  tff(c_133, plain, (![D_55]: (k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_55)=k7_relat_1('#skF_4', D_55) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_24, c_131])).
% 2.53/1.61  tff(c_136, plain, (![D_55]: (k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_55)=k7_relat_1('#skF_4', D_55))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_133])).
% 2.53/1.61  tff(c_20, plain, (~r2_relset_1('#skF_1', '#skF_2', k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.53/1.61  tff(c_137, plain, (~r2_relset_1('#skF_1', '#skF_2', k7_relat_1('#skF_4', '#skF_3'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_136, c_20])).
% 2.53/1.61  tff(c_138, plain, (~r2_relset_1('#skF_1', '#skF_2', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_115, c_137])).
% 2.53/1.61  tff(c_169, plain, (![A_63, B_64, C_65, D_66]: (r2_relset_1(A_63, B_64, C_65, C_65) | ~m1_subset_1(D_66, k1_zfmisc_1(k2_zfmisc_1(A_63, B_64))) | ~m1_subset_1(C_65, k1_zfmisc_1(k2_zfmisc_1(A_63, B_64))))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.53/1.61  tff(c_173, plain, (![C_67]: (r2_relset_1('#skF_1', '#skF_2', C_67, C_67) | ~m1_subset_1(C_67, k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))))), inference(resolution, [status(thm)], [c_24, c_169])).
% 2.53/1.61  tff(c_175, plain, (r2_relset_1('#skF_1', '#skF_2', '#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_24, c_173])).
% 2.53/1.61  tff(c_179, plain, $false, inference(negUnitSimplification, [status(thm)], [c_138, c_175])).
% 2.53/1.61  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.53/1.61  
% 2.53/1.61  Inference rules
% 2.53/1.61  ----------------------
% 2.53/1.61  #Ref     : 0
% 2.53/1.61  #Sup     : 32
% 2.53/1.61  #Fact    : 0
% 2.53/1.61  #Define  : 0
% 2.53/1.61  #Split   : 2
% 2.53/1.61  #Chain   : 0
% 2.53/1.61  #Close   : 0
% 2.53/1.61  
% 2.53/1.61  Ordering : KBO
% 2.53/1.61  
% 2.53/1.61  Simplification rules
% 2.53/1.61  ----------------------
% 2.53/1.61  #Subsume      : 2
% 2.53/1.61  #Demod        : 8
% 2.53/1.61  #Tautology    : 8
% 2.53/1.61  #SimpNegUnit  : 1
% 2.53/1.61  #BackRed      : 1
% 2.53/1.61  
% 2.53/1.61  #Partial instantiations: 0
% 2.53/1.61  #Strategies tried      : 1
% 2.53/1.61  
% 2.53/1.61  Timing (in seconds)
% 2.53/1.61  ----------------------
% 2.53/1.62  Preprocessing        : 0.47
% 2.53/1.62  Parsing              : 0.25
% 2.53/1.62  CNF conversion       : 0.03
% 2.53/1.62  Main loop            : 0.28
% 2.53/1.62  Inferencing          : 0.11
% 2.53/1.62  Reduction            : 0.07
% 2.53/1.62  Demodulation         : 0.05
% 2.53/1.62  BG Simplification    : 0.02
% 2.53/1.62  Subsumption          : 0.06
% 2.53/1.62  Abstraction          : 0.02
% 2.53/1.62  MUC search           : 0.00
% 2.53/1.62  Cooper               : 0.00
% 2.53/1.62  Total                : 0.78
% 2.53/1.62  Index Insertion      : 0.00
% 2.53/1.62  Index Deletion       : 0.00
% 2.53/1.62  Index Matching       : 0.00
% 2.53/1.62  BG Taut test         : 0.00
%------------------------------------------------------------------------------
