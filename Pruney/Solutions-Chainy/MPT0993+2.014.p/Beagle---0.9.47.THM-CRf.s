%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:13:44 EST 2020

% Result     : Theorem 1.95s
% Output     : CNFRefutation 2.12s
% Verified   : 
% Statistics : Number of formulae       :   53 (  63 expanded)
%              Number of leaves         :   28 (  35 expanded)
%              Depth                    :    8
%              Number of atoms          :   73 ( 109 expanded)
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

tff(f_78,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( r1_tarski(A,C)
         => r2_relset_1(A,B,k2_partfun1(A,B,D,C),D) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_funct_2)).

tff(f_61,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

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
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_67,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => k2_partfun1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

tff(c_26,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_112,plain,(
    ! [A_46,B_47,D_48] :
      ( r2_relset_1(A_46,B_47,D_48,D_48)
      | ~ m1_subset_1(D_48,k1_zfmisc_1(k2_zfmisc_1(A_46,B_47))) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_115,plain,(
    r2_relset_1('#skF_1','#skF_2','#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_26,c_112])).

tff(c_31,plain,(
    ! [C_22,A_23,B_24] :
      ( v1_relat_1(C_22)
      | ~ m1_subset_1(C_22,k1_zfmisc_1(k2_zfmisc_1(A_23,B_24))) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_35,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_26,c_31])).

tff(c_43,plain,(
    ! [C_32,A_33,B_34] :
      ( v4_relat_1(C_32,A_33)
      | ~ m1_subset_1(C_32,k1_zfmisc_1(k2_zfmisc_1(A_33,B_34))) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_47,plain,(
    v4_relat_1('#skF_4','#skF_1') ),
    inference(resolution,[status(thm)],[c_26,c_43])).

tff(c_6,plain,(
    ! [B_5,A_4] :
      ( r1_tarski(k1_relat_1(B_5),A_4)
      | ~ v4_relat_1(B_5,A_4)
      | ~ v1_relat_1(B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_24,plain,(
    r1_tarski('#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_63,plain,(
    ! [A_37,C_38,B_39] :
      ( r1_tarski(A_37,C_38)
      | ~ r1_tarski(B_39,C_38)
      | ~ r1_tarski(A_37,B_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_70,plain,(
    ! [A_40] :
      ( r1_tarski(A_40,'#skF_3')
      | ~ r1_tarski(A_40,'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_24,c_63])).

tff(c_4,plain,(
    ! [B_5,A_4] :
      ( v4_relat_1(B_5,A_4)
      | ~ r1_tarski(k1_relat_1(B_5),A_4)
      | ~ v1_relat_1(B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_90,plain,(
    ! [B_43] :
      ( v4_relat_1(B_43,'#skF_3')
      | ~ v1_relat_1(B_43)
      | ~ r1_tarski(k1_relat_1(B_43),'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_70,c_4])).

tff(c_96,plain,(
    ! [B_44] :
      ( v4_relat_1(B_44,'#skF_3')
      | ~ v4_relat_1(B_44,'#skF_1')
      | ~ v1_relat_1(B_44) ) ),
    inference(resolution,[status(thm)],[c_6,c_90])).

tff(c_8,plain,(
    ! [B_7,A_6] :
      ( k7_relat_1(B_7,A_6) = B_7
      | ~ v4_relat_1(B_7,A_6)
      | ~ v1_relat_1(B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_101,plain,(
    ! [B_45] :
      ( k7_relat_1(B_45,'#skF_3') = B_45
      | ~ v4_relat_1(B_45,'#skF_1')
      | ~ v1_relat_1(B_45) ) ),
    inference(resolution,[status(thm)],[c_96,c_8])).

tff(c_104,plain,
    ( k7_relat_1('#skF_4','#skF_3') = '#skF_4'
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_47,c_101])).

tff(c_107,plain,(
    k7_relat_1('#skF_4','#skF_3') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_35,c_104])).

tff(c_30,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_121,plain,(
    ! [A_52,B_53,C_54,D_55] :
      ( k2_partfun1(A_52,B_53,C_54,D_55) = k7_relat_1(C_54,D_55)
      | ~ m1_subset_1(C_54,k1_zfmisc_1(k2_zfmisc_1(A_52,B_53)))
      | ~ v1_funct_1(C_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_123,plain,(
    ! [D_55] :
      ( k2_partfun1('#skF_1','#skF_2','#skF_4',D_55) = k7_relat_1('#skF_4',D_55)
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_26,c_121])).

tff(c_126,plain,(
    ! [D_55] : k2_partfun1('#skF_1','#skF_2','#skF_4',D_55) = k7_relat_1('#skF_4',D_55) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_123])).

tff(c_22,plain,(
    ~ r2_relset_1('#skF_1','#skF_2',k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_127,plain,(
    ~ r2_relset_1('#skF_1','#skF_2',k7_relat_1('#skF_4','#skF_3'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_126,c_22])).

tff(c_130,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_115,c_107,c_127])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n008.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 10:19:00 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.95/1.26  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.95/1.26  
% 1.95/1.26  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.95/1.27  %$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_partfun1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 1.95/1.27  
% 1.95/1.27  %Foreground sorts:
% 1.95/1.27  
% 1.95/1.27  
% 1.95/1.27  %Background operators:
% 1.95/1.27  
% 1.95/1.27  
% 1.95/1.27  %Foreground operators:
% 1.95/1.27  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 1.95/1.27  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.95/1.27  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 1.95/1.27  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 1.95/1.27  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.95/1.27  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 1.95/1.27  tff('#skF_2', type, '#skF_2': $i).
% 1.95/1.27  tff('#skF_3', type, '#skF_3': $i).
% 1.95/1.27  tff('#skF_1', type, '#skF_1': $i).
% 1.95/1.27  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 1.95/1.27  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.95/1.27  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.95/1.27  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.95/1.27  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.95/1.27  tff('#skF_4', type, '#skF_4': $i).
% 1.95/1.27  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.95/1.27  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 1.95/1.27  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 1.95/1.27  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.95/1.27  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.95/1.27  
% 2.12/1.28  tff(f_78, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r1_tarski(A, C) => r2_relset_1(A, B, k2_partfun1(A, B, D, C), D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t40_funct_2)).
% 2.12/1.28  tff(f_61, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 2.12/1.28  tff(f_47, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.12/1.28  tff(f_53, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.12/1.28  tff(f_37, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d18_relat_1)).
% 2.12/1.28  tff(f_31, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 2.12/1.28  tff(f_43, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t209_relat_1)).
% 2.12/1.28  tff(f_67, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (k2_partfun1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_partfun1)).
% 2.12/1.28  tff(c_26, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.12/1.28  tff(c_112, plain, (![A_46, B_47, D_48]: (r2_relset_1(A_46, B_47, D_48, D_48) | ~m1_subset_1(D_48, k1_zfmisc_1(k2_zfmisc_1(A_46, B_47))))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.12/1.28  tff(c_115, plain, (r2_relset_1('#skF_1', '#skF_2', '#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_26, c_112])).
% 2.12/1.28  tff(c_31, plain, (![C_22, A_23, B_24]: (v1_relat_1(C_22) | ~m1_subset_1(C_22, k1_zfmisc_1(k2_zfmisc_1(A_23, B_24))))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.12/1.28  tff(c_35, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_26, c_31])).
% 2.12/1.28  tff(c_43, plain, (![C_32, A_33, B_34]: (v4_relat_1(C_32, A_33) | ~m1_subset_1(C_32, k1_zfmisc_1(k2_zfmisc_1(A_33, B_34))))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.12/1.28  tff(c_47, plain, (v4_relat_1('#skF_4', '#skF_1')), inference(resolution, [status(thm)], [c_26, c_43])).
% 2.12/1.28  tff(c_6, plain, (![B_5, A_4]: (r1_tarski(k1_relat_1(B_5), A_4) | ~v4_relat_1(B_5, A_4) | ~v1_relat_1(B_5))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.12/1.28  tff(c_24, plain, (r1_tarski('#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.12/1.28  tff(c_63, plain, (![A_37, C_38, B_39]: (r1_tarski(A_37, C_38) | ~r1_tarski(B_39, C_38) | ~r1_tarski(A_37, B_39))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.12/1.28  tff(c_70, plain, (![A_40]: (r1_tarski(A_40, '#skF_3') | ~r1_tarski(A_40, '#skF_1'))), inference(resolution, [status(thm)], [c_24, c_63])).
% 2.12/1.28  tff(c_4, plain, (![B_5, A_4]: (v4_relat_1(B_5, A_4) | ~r1_tarski(k1_relat_1(B_5), A_4) | ~v1_relat_1(B_5))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.12/1.28  tff(c_90, plain, (![B_43]: (v4_relat_1(B_43, '#skF_3') | ~v1_relat_1(B_43) | ~r1_tarski(k1_relat_1(B_43), '#skF_1'))), inference(resolution, [status(thm)], [c_70, c_4])).
% 2.12/1.28  tff(c_96, plain, (![B_44]: (v4_relat_1(B_44, '#skF_3') | ~v4_relat_1(B_44, '#skF_1') | ~v1_relat_1(B_44))), inference(resolution, [status(thm)], [c_6, c_90])).
% 2.12/1.28  tff(c_8, plain, (![B_7, A_6]: (k7_relat_1(B_7, A_6)=B_7 | ~v4_relat_1(B_7, A_6) | ~v1_relat_1(B_7))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.12/1.28  tff(c_101, plain, (![B_45]: (k7_relat_1(B_45, '#skF_3')=B_45 | ~v4_relat_1(B_45, '#skF_1') | ~v1_relat_1(B_45))), inference(resolution, [status(thm)], [c_96, c_8])).
% 2.12/1.28  tff(c_104, plain, (k7_relat_1('#skF_4', '#skF_3')='#skF_4' | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_47, c_101])).
% 2.12/1.28  tff(c_107, plain, (k7_relat_1('#skF_4', '#skF_3')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_35, c_104])).
% 2.12/1.28  tff(c_30, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.12/1.28  tff(c_121, plain, (![A_52, B_53, C_54, D_55]: (k2_partfun1(A_52, B_53, C_54, D_55)=k7_relat_1(C_54, D_55) | ~m1_subset_1(C_54, k1_zfmisc_1(k2_zfmisc_1(A_52, B_53))) | ~v1_funct_1(C_54))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.12/1.28  tff(c_123, plain, (![D_55]: (k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_55)=k7_relat_1('#skF_4', D_55) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_26, c_121])).
% 2.12/1.28  tff(c_126, plain, (![D_55]: (k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_55)=k7_relat_1('#skF_4', D_55))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_123])).
% 2.12/1.28  tff(c_22, plain, (~r2_relset_1('#skF_1', '#skF_2', k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.12/1.28  tff(c_127, plain, (~r2_relset_1('#skF_1', '#skF_2', k7_relat_1('#skF_4', '#skF_3'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_126, c_22])).
% 2.12/1.28  tff(c_130, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_115, c_107, c_127])).
% 2.12/1.28  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.12/1.28  
% 2.12/1.28  Inference rules
% 2.12/1.28  ----------------------
% 2.12/1.28  #Ref     : 0
% 2.12/1.28  #Sup     : 22
% 2.12/1.28  #Fact    : 0
% 2.12/1.28  #Define  : 0
% 2.12/1.28  #Split   : 0
% 2.12/1.28  #Chain   : 0
% 2.12/1.28  #Close   : 0
% 2.12/1.28  
% 2.12/1.28  Ordering : KBO
% 2.12/1.28  
% 2.12/1.28  Simplification rules
% 2.12/1.28  ----------------------
% 2.12/1.28  #Subsume      : 1
% 2.12/1.28  #Demod        : 7
% 2.12/1.28  #Tautology    : 6
% 2.12/1.28  #SimpNegUnit  : 0
% 2.12/1.28  #BackRed      : 1
% 2.12/1.28  
% 2.12/1.28  #Partial instantiations: 0
% 2.12/1.28  #Strategies tried      : 1
% 2.12/1.28  
% 2.12/1.28  Timing (in seconds)
% 2.12/1.28  ----------------------
% 2.12/1.28  Preprocessing        : 0.31
% 2.12/1.28  Parsing              : 0.17
% 2.12/1.28  CNF conversion       : 0.02
% 2.12/1.28  Main loop            : 0.13
% 2.12/1.28  Inferencing          : 0.05
% 2.12/1.28  Reduction            : 0.04
% 2.12/1.28  Demodulation         : 0.03
% 2.12/1.28  BG Simplification    : 0.01
% 2.12/1.28  Subsumption          : 0.02
% 2.12/1.28  Abstraction          : 0.01
% 2.12/1.28  MUC search           : 0.00
% 2.12/1.28  Cooper               : 0.00
% 2.12/1.28  Total                : 0.47
% 2.12/1.28  Index Insertion      : 0.00
% 2.12/1.28  Index Deletion       : 0.00
% 2.12/1.28  Index Matching       : 0.00
% 2.12/1.28  BG Taut test         : 0.00
%------------------------------------------------------------------------------
