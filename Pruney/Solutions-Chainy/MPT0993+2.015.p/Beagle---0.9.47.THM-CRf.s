%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:13:44 EST 2020

% Result     : Theorem 2.00s
% Output     : CNFRefutation 2.00s
% Verified   : 
% Statistics : Number of formulae       :   54 (  66 expanded)
%              Number of leaves         :   28 (  36 expanded)
%              Depth                    :    8
%              Number of atoms          :   76 ( 118 expanded)
%              Number of equality atoms :   11 (  11 expanded)
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_funct_2)).

tff(f_61,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_47,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_53,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_37,axiom,(
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

tff(f_43,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k1_relat_1(B),A)
       => k7_relat_1(B,A) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t97_relat_1)).

tff(f_67,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => k2_partfun1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

tff(c_26,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_128,plain,(
    ! [A_49,B_50,D_51] :
      ( r2_relset_1(A_49,B_50,D_51,D_51)
      | ~ m1_subset_1(D_51,k1_zfmisc_1(k2_zfmisc_1(A_49,B_50))) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_131,plain,(
    r2_relset_1('#skF_1','#skF_2','#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_26,c_128])).

tff(c_31,plain,(
    ! [C_22,A_23,B_24] :
      ( v1_relat_1(C_22)
      | ~ m1_subset_1(C_22,k1_zfmisc_1(k2_zfmisc_1(A_23,B_24))) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_35,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_26,c_31])).

tff(c_41,plain,(
    ! [C_28,A_29,B_30] :
      ( v4_relat_1(C_28,A_29)
      | ~ m1_subset_1(C_28,k1_zfmisc_1(k2_zfmisc_1(A_29,B_30))) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_45,plain,(
    v4_relat_1('#skF_4','#skF_1') ),
    inference(resolution,[status(thm)],[c_26,c_41])).

tff(c_6,plain,(
    ! [B_5,A_4] :
      ( r1_tarski(k1_relat_1(B_5),A_4)
      | ~ v4_relat_1(B_5,A_4)
      | ~ v1_relat_1(B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_24,plain,(
    r1_tarski('#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_52,plain,(
    ! [A_35,C_36,B_37] :
      ( r1_tarski(A_35,C_36)
      | ~ r1_tarski(B_37,C_36)
      | ~ r1_tarski(A_35,B_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_59,plain,(
    ! [A_38] :
      ( r1_tarski(A_38,'#skF_3')
      | ~ r1_tarski(A_38,'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_24,c_52])).

tff(c_4,plain,(
    ! [B_5,A_4] :
      ( v4_relat_1(B_5,A_4)
      | ~ r1_tarski(k1_relat_1(B_5),A_4)
      | ~ v1_relat_1(B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_100,plain,(
    ! [B_45] :
      ( v4_relat_1(B_45,'#skF_3')
      | ~ v1_relat_1(B_45)
      | ~ r1_tarski(k1_relat_1(B_45),'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_59,c_4])).

tff(c_106,plain,(
    ! [B_46] :
      ( v4_relat_1(B_46,'#skF_3')
      | ~ v4_relat_1(B_46,'#skF_1')
      | ~ v1_relat_1(B_46) ) ),
    inference(resolution,[status(thm)],[c_6,c_100])).

tff(c_68,plain,(
    ! [B_39,A_40] :
      ( k7_relat_1(B_39,A_40) = B_39
      | ~ r1_tarski(k1_relat_1(B_39),A_40)
      | ~ v1_relat_1(B_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_77,plain,(
    ! [B_5,A_4] :
      ( k7_relat_1(B_5,A_4) = B_5
      | ~ v4_relat_1(B_5,A_4)
      | ~ v1_relat_1(B_5) ) ),
    inference(resolution,[status(thm)],[c_6,c_68])).

tff(c_111,plain,(
    ! [B_47] :
      ( k7_relat_1(B_47,'#skF_3') = B_47
      | ~ v4_relat_1(B_47,'#skF_1')
      | ~ v1_relat_1(B_47) ) ),
    inference(resolution,[status(thm)],[c_106,c_77])).

tff(c_114,plain,
    ( k7_relat_1('#skF_4','#skF_3') = '#skF_4'
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_45,c_111])).

tff(c_117,plain,(
    k7_relat_1('#skF_4','#skF_3') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_35,c_114])).

tff(c_30,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_132,plain,(
    ! [A_52,B_53,C_54,D_55] :
      ( k2_partfun1(A_52,B_53,C_54,D_55) = k7_relat_1(C_54,D_55)
      | ~ m1_subset_1(C_54,k1_zfmisc_1(k2_zfmisc_1(A_52,B_53)))
      | ~ v1_funct_1(C_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_134,plain,(
    ! [D_55] :
      ( k2_partfun1('#skF_1','#skF_2','#skF_4',D_55) = k7_relat_1('#skF_4',D_55)
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_26,c_132])).

tff(c_137,plain,(
    ! [D_55] : k2_partfun1('#skF_1','#skF_2','#skF_4',D_55) = k7_relat_1('#skF_4',D_55) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_134])).

tff(c_22,plain,(
    ~ r2_relset_1('#skF_1','#skF_2',k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_138,plain,(
    ~ r2_relset_1('#skF_1','#skF_2',k7_relat_1('#skF_4','#skF_3'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_137,c_22])).

tff(c_141,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_131,c_117,c_138])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n015.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 19:01:08 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.00/1.20  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.00/1.20  
% 2.00/1.20  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.00/1.21  %$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_partfun1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.00/1.21  
% 2.00/1.21  %Foreground sorts:
% 2.00/1.21  
% 2.00/1.21  
% 2.00/1.21  %Background operators:
% 2.00/1.21  
% 2.00/1.21  
% 2.00/1.21  %Foreground operators:
% 2.00/1.21  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.00/1.21  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.00/1.21  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 2.00/1.21  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.00/1.21  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.00/1.21  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.00/1.21  tff('#skF_2', type, '#skF_2': $i).
% 2.00/1.21  tff('#skF_3', type, '#skF_3': $i).
% 2.00/1.21  tff('#skF_1', type, '#skF_1': $i).
% 2.00/1.21  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.00/1.21  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.00/1.21  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.00/1.21  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.00/1.21  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.00/1.21  tff('#skF_4', type, '#skF_4': $i).
% 2.00/1.21  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.00/1.21  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 2.00/1.21  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.00/1.21  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.00/1.21  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.00/1.21  
% 2.00/1.22  tff(f_78, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r1_tarski(A, C) => r2_relset_1(A, B, k2_partfun1(A, B, D, C), D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t40_funct_2)).
% 2.00/1.22  tff(f_61, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 2.00/1.22  tff(f_47, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.00/1.22  tff(f_53, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.00/1.22  tff(f_37, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d18_relat_1)).
% 2.00/1.22  tff(f_31, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 2.00/1.22  tff(f_43, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(B), A) => (k7_relat_1(B, A) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t97_relat_1)).
% 2.00/1.22  tff(f_67, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (k2_partfun1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_partfun1)).
% 2.00/1.22  tff(c_26, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.00/1.22  tff(c_128, plain, (![A_49, B_50, D_51]: (r2_relset_1(A_49, B_50, D_51, D_51) | ~m1_subset_1(D_51, k1_zfmisc_1(k2_zfmisc_1(A_49, B_50))))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.00/1.22  tff(c_131, plain, (r2_relset_1('#skF_1', '#skF_2', '#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_26, c_128])).
% 2.00/1.22  tff(c_31, plain, (![C_22, A_23, B_24]: (v1_relat_1(C_22) | ~m1_subset_1(C_22, k1_zfmisc_1(k2_zfmisc_1(A_23, B_24))))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.00/1.22  tff(c_35, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_26, c_31])).
% 2.00/1.22  tff(c_41, plain, (![C_28, A_29, B_30]: (v4_relat_1(C_28, A_29) | ~m1_subset_1(C_28, k1_zfmisc_1(k2_zfmisc_1(A_29, B_30))))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.00/1.22  tff(c_45, plain, (v4_relat_1('#skF_4', '#skF_1')), inference(resolution, [status(thm)], [c_26, c_41])).
% 2.00/1.22  tff(c_6, plain, (![B_5, A_4]: (r1_tarski(k1_relat_1(B_5), A_4) | ~v4_relat_1(B_5, A_4) | ~v1_relat_1(B_5))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.00/1.22  tff(c_24, plain, (r1_tarski('#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.00/1.22  tff(c_52, plain, (![A_35, C_36, B_37]: (r1_tarski(A_35, C_36) | ~r1_tarski(B_37, C_36) | ~r1_tarski(A_35, B_37))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.00/1.22  tff(c_59, plain, (![A_38]: (r1_tarski(A_38, '#skF_3') | ~r1_tarski(A_38, '#skF_1'))), inference(resolution, [status(thm)], [c_24, c_52])).
% 2.00/1.22  tff(c_4, plain, (![B_5, A_4]: (v4_relat_1(B_5, A_4) | ~r1_tarski(k1_relat_1(B_5), A_4) | ~v1_relat_1(B_5))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.00/1.22  tff(c_100, plain, (![B_45]: (v4_relat_1(B_45, '#skF_3') | ~v1_relat_1(B_45) | ~r1_tarski(k1_relat_1(B_45), '#skF_1'))), inference(resolution, [status(thm)], [c_59, c_4])).
% 2.00/1.22  tff(c_106, plain, (![B_46]: (v4_relat_1(B_46, '#skF_3') | ~v4_relat_1(B_46, '#skF_1') | ~v1_relat_1(B_46))), inference(resolution, [status(thm)], [c_6, c_100])).
% 2.00/1.22  tff(c_68, plain, (![B_39, A_40]: (k7_relat_1(B_39, A_40)=B_39 | ~r1_tarski(k1_relat_1(B_39), A_40) | ~v1_relat_1(B_39))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.00/1.22  tff(c_77, plain, (![B_5, A_4]: (k7_relat_1(B_5, A_4)=B_5 | ~v4_relat_1(B_5, A_4) | ~v1_relat_1(B_5))), inference(resolution, [status(thm)], [c_6, c_68])).
% 2.00/1.22  tff(c_111, plain, (![B_47]: (k7_relat_1(B_47, '#skF_3')=B_47 | ~v4_relat_1(B_47, '#skF_1') | ~v1_relat_1(B_47))), inference(resolution, [status(thm)], [c_106, c_77])).
% 2.00/1.22  tff(c_114, plain, (k7_relat_1('#skF_4', '#skF_3')='#skF_4' | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_45, c_111])).
% 2.00/1.22  tff(c_117, plain, (k7_relat_1('#skF_4', '#skF_3')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_35, c_114])).
% 2.00/1.22  tff(c_30, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.00/1.22  tff(c_132, plain, (![A_52, B_53, C_54, D_55]: (k2_partfun1(A_52, B_53, C_54, D_55)=k7_relat_1(C_54, D_55) | ~m1_subset_1(C_54, k1_zfmisc_1(k2_zfmisc_1(A_52, B_53))) | ~v1_funct_1(C_54))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.00/1.22  tff(c_134, plain, (![D_55]: (k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_55)=k7_relat_1('#skF_4', D_55) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_26, c_132])).
% 2.00/1.22  tff(c_137, plain, (![D_55]: (k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_55)=k7_relat_1('#skF_4', D_55))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_134])).
% 2.00/1.22  tff(c_22, plain, (~r2_relset_1('#skF_1', '#skF_2', k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.00/1.22  tff(c_138, plain, (~r2_relset_1('#skF_1', '#skF_2', k7_relat_1('#skF_4', '#skF_3'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_137, c_22])).
% 2.00/1.22  tff(c_141, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_131, c_117, c_138])).
% 2.00/1.22  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.00/1.22  
% 2.00/1.22  Inference rules
% 2.00/1.22  ----------------------
% 2.00/1.22  #Ref     : 0
% 2.00/1.22  #Sup     : 24
% 2.00/1.22  #Fact    : 0
% 2.00/1.22  #Define  : 0
% 2.00/1.22  #Split   : 0
% 2.00/1.22  #Chain   : 0
% 2.00/1.22  #Close   : 0
% 2.00/1.22  
% 2.00/1.22  Ordering : KBO
% 2.00/1.22  
% 2.00/1.22  Simplification rules
% 2.00/1.22  ----------------------
% 2.00/1.22  #Subsume      : 2
% 2.00/1.22  #Demod        : 7
% 2.00/1.22  #Tautology    : 6
% 2.00/1.22  #SimpNegUnit  : 0
% 2.00/1.22  #BackRed      : 1
% 2.00/1.22  
% 2.00/1.22  #Partial instantiations: 0
% 2.00/1.22  #Strategies tried      : 1
% 2.00/1.22  
% 2.00/1.22  Timing (in seconds)
% 2.00/1.22  ----------------------
% 2.00/1.22  Preprocessing        : 0.30
% 2.00/1.22  Parsing              : 0.16
% 2.00/1.22  CNF conversion       : 0.02
% 2.00/1.22  Main loop            : 0.15
% 2.00/1.22  Inferencing          : 0.05
% 2.00/1.22  Reduction            : 0.04
% 2.00/1.22  Demodulation         : 0.03
% 2.00/1.22  BG Simplification    : 0.01
% 2.00/1.22  Subsumption          : 0.03
% 2.00/1.22  Abstraction          : 0.01
% 2.00/1.22  MUC search           : 0.00
% 2.00/1.22  Cooper               : 0.00
% 2.00/1.22  Total                : 0.48
% 2.00/1.22  Index Insertion      : 0.00
% 2.00/1.22  Index Deletion       : 0.00
% 2.00/1.22  Index Matching       : 0.00
% 2.00/1.22  BG Taut test         : 0.00
%------------------------------------------------------------------------------
