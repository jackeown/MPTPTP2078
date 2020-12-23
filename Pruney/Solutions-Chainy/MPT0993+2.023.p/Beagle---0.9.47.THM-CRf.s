%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:13:45 EST 2020

% Result     : Theorem 2.82s
% Output     : CNFRefutation 2.82s
% Verified   : 
% Statistics : Number of formulae       :   56 (  66 expanded)
%              Number of leaves         :   28 (  35 expanded)
%              Depth                    :    9
%              Number of atoms          :   77 ( 112 expanded)
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

tff(f_82,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( r1_tarski(A,C)
         => r2_relset_1(A,B,k2_partfun1(A,B,D,C),D) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_funct_2)).

tff(f_65,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_51,axiom,(
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

tff(f_31,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_57,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_71,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => k2_partfun1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

tff(c_30,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_302,plain,(
    ! [A_92,B_93,D_94] :
      ( r2_relset_1(A_92,B_93,D_94,D_94)
      | ~ m1_subset_1(D_94,k1_zfmisc_1(k2_zfmisc_1(A_92,B_93))) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_309,plain,(
    r2_relset_1('#skF_1','#skF_2','#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_30,c_302])).

tff(c_28,plain,(
    r1_tarski('#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_45,plain,(
    ! [C_29,A_30,B_31] :
      ( v1_relat_1(C_29)
      | ~ m1_subset_1(C_29,k1_zfmisc_1(k2_zfmisc_1(A_30,B_31))) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_54,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_30,c_45])).

tff(c_36,plain,(
    ! [A_27,B_28] :
      ( r1_tarski(A_27,B_28)
      | ~ m1_subset_1(A_27,k1_zfmisc_1(B_28)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_44,plain,(
    r1_tarski('#skF_4',k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_30,c_36])).

tff(c_221,plain,(
    ! [A_75,C_76,B_77] :
      ( r1_tarski(k2_zfmisc_1(A_75,C_76),k2_zfmisc_1(B_77,C_76))
      | ~ r1_tarski(A_75,B_77) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_2,plain,(
    ! [A_1,C_3,B_2] :
      ( r1_tarski(A_1,C_3)
      | ~ r1_tarski(B_2,C_3)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_653,plain,(
    ! [A_181,B_182,C_183,A_184] :
      ( r1_tarski(A_181,k2_zfmisc_1(B_182,C_183))
      | ~ r1_tarski(A_181,k2_zfmisc_1(A_184,C_183))
      | ~ r1_tarski(A_184,B_182) ) ),
    inference(resolution,[status(thm)],[c_221,c_2])).

tff(c_669,plain,(
    ! [B_185] :
      ( r1_tarski('#skF_4',k2_zfmisc_1(B_185,'#skF_2'))
      | ~ r1_tarski('#skF_1',B_185) ) ),
    inference(resolution,[status(thm)],[c_44,c_653])).

tff(c_10,plain,(
    ! [A_7,B_8] :
      ( m1_subset_1(A_7,k1_zfmisc_1(B_8))
      | ~ r1_tarski(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_84,plain,(
    ! [C_44,A_45,B_46] :
      ( v4_relat_1(C_44,A_45)
      | ~ m1_subset_1(C_44,k1_zfmisc_1(k2_zfmisc_1(A_45,B_46))) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_92,plain,(
    ! [A_7,A_45,B_46] :
      ( v4_relat_1(A_7,A_45)
      | ~ r1_tarski(A_7,k2_zfmisc_1(A_45,B_46)) ) ),
    inference(resolution,[status(thm)],[c_10,c_84])).

tff(c_747,plain,(
    ! [B_186] :
      ( v4_relat_1('#skF_4',B_186)
      | ~ r1_tarski('#skF_1',B_186) ) ),
    inference(resolution,[status(thm)],[c_669,c_92])).

tff(c_12,plain,(
    ! [B_10,A_9] :
      ( k7_relat_1(B_10,A_9) = B_10
      | ~ v4_relat_1(B_10,A_9)
      | ~ v1_relat_1(B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_750,plain,(
    ! [B_186] :
      ( k7_relat_1('#skF_4',B_186) = '#skF_4'
      | ~ v1_relat_1('#skF_4')
      | ~ r1_tarski('#skF_1',B_186) ) ),
    inference(resolution,[status(thm)],[c_747,c_12])).

tff(c_754,plain,(
    ! [B_187] :
      ( k7_relat_1('#skF_4',B_187) = '#skF_4'
      | ~ r1_tarski('#skF_1',B_187) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_750])).

tff(c_768,plain,(
    k7_relat_1('#skF_4','#skF_3') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_28,c_754])).

tff(c_34,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_380,plain,(
    ! [A_116,B_117,C_118,D_119] :
      ( k2_partfun1(A_116,B_117,C_118,D_119) = k7_relat_1(C_118,D_119)
      | ~ m1_subset_1(C_118,k1_zfmisc_1(k2_zfmisc_1(A_116,B_117)))
      | ~ v1_funct_1(C_118) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_385,plain,(
    ! [D_119] :
      ( k2_partfun1('#skF_1','#skF_2','#skF_4',D_119) = k7_relat_1('#skF_4',D_119)
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_30,c_380])).

tff(c_389,plain,(
    ! [D_119] : k2_partfun1('#skF_1','#skF_2','#skF_4',D_119) = k7_relat_1('#skF_4',D_119) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_385])).

tff(c_26,plain,(
    ~ r2_relset_1('#skF_1','#skF_2',k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_392,plain,(
    ~ r2_relset_1('#skF_1','#skF_2',k7_relat_1('#skF_4','#skF_3'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_389,c_26])).

tff(c_769,plain,(
    ~ r2_relset_1('#skF_1','#skF_2','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_768,c_392])).

tff(c_772,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_309,c_769])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 17:02:05 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.82/1.51  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.82/1.52  
% 2.82/1.52  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.82/1.52  %$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_partfun1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.82/1.52  
% 2.82/1.52  %Foreground sorts:
% 2.82/1.52  
% 2.82/1.52  
% 2.82/1.52  %Background operators:
% 2.82/1.52  
% 2.82/1.52  
% 2.82/1.52  %Foreground operators:
% 2.82/1.52  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.82/1.52  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.82/1.52  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 2.82/1.52  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.82/1.52  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.82/1.52  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.82/1.52  tff('#skF_2', type, '#skF_2': $i).
% 2.82/1.52  tff('#skF_3', type, '#skF_3': $i).
% 2.82/1.52  tff('#skF_1', type, '#skF_1': $i).
% 2.82/1.52  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.82/1.52  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.82/1.52  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.82/1.52  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.82/1.52  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.82/1.52  tff('#skF_4', type, '#skF_4': $i).
% 2.82/1.52  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.82/1.52  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 2.82/1.52  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.82/1.52  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.82/1.52  
% 2.82/1.53  tff(f_82, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r1_tarski(A, C) => r2_relset_1(A, B, k2_partfun1(A, B, D, C), D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t40_funct_2)).
% 2.82/1.53  tff(f_65, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 2.82/1.53  tff(f_51, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.82/1.53  tff(f_41, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 2.82/1.53  tff(f_37, axiom, (![A, B, C]: (r1_tarski(A, B) => (r1_tarski(k2_zfmisc_1(A, C), k2_zfmisc_1(B, C)) & r1_tarski(k2_zfmisc_1(C, A), k2_zfmisc_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t118_zfmisc_1)).
% 2.82/1.53  tff(f_31, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 2.82/1.53  tff(f_57, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.82/1.53  tff(f_47, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t209_relat_1)).
% 2.82/1.53  tff(f_71, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (k2_partfun1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_partfun1)).
% 2.82/1.53  tff(c_30, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.82/1.53  tff(c_302, plain, (![A_92, B_93, D_94]: (r2_relset_1(A_92, B_93, D_94, D_94) | ~m1_subset_1(D_94, k1_zfmisc_1(k2_zfmisc_1(A_92, B_93))))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.82/1.53  tff(c_309, plain, (r2_relset_1('#skF_1', '#skF_2', '#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_30, c_302])).
% 2.82/1.53  tff(c_28, plain, (r1_tarski('#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.82/1.53  tff(c_45, plain, (![C_29, A_30, B_31]: (v1_relat_1(C_29) | ~m1_subset_1(C_29, k1_zfmisc_1(k2_zfmisc_1(A_30, B_31))))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.82/1.53  tff(c_54, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_30, c_45])).
% 2.82/1.53  tff(c_36, plain, (![A_27, B_28]: (r1_tarski(A_27, B_28) | ~m1_subset_1(A_27, k1_zfmisc_1(B_28)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.82/1.53  tff(c_44, plain, (r1_tarski('#skF_4', k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_30, c_36])).
% 2.82/1.53  tff(c_221, plain, (![A_75, C_76, B_77]: (r1_tarski(k2_zfmisc_1(A_75, C_76), k2_zfmisc_1(B_77, C_76)) | ~r1_tarski(A_75, B_77))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.82/1.53  tff(c_2, plain, (![A_1, C_3, B_2]: (r1_tarski(A_1, C_3) | ~r1_tarski(B_2, C_3) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.82/1.53  tff(c_653, plain, (![A_181, B_182, C_183, A_184]: (r1_tarski(A_181, k2_zfmisc_1(B_182, C_183)) | ~r1_tarski(A_181, k2_zfmisc_1(A_184, C_183)) | ~r1_tarski(A_184, B_182))), inference(resolution, [status(thm)], [c_221, c_2])).
% 2.82/1.53  tff(c_669, plain, (![B_185]: (r1_tarski('#skF_4', k2_zfmisc_1(B_185, '#skF_2')) | ~r1_tarski('#skF_1', B_185))), inference(resolution, [status(thm)], [c_44, c_653])).
% 2.82/1.53  tff(c_10, plain, (![A_7, B_8]: (m1_subset_1(A_7, k1_zfmisc_1(B_8)) | ~r1_tarski(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.82/1.53  tff(c_84, plain, (![C_44, A_45, B_46]: (v4_relat_1(C_44, A_45) | ~m1_subset_1(C_44, k1_zfmisc_1(k2_zfmisc_1(A_45, B_46))))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.82/1.53  tff(c_92, plain, (![A_7, A_45, B_46]: (v4_relat_1(A_7, A_45) | ~r1_tarski(A_7, k2_zfmisc_1(A_45, B_46)))), inference(resolution, [status(thm)], [c_10, c_84])).
% 2.82/1.53  tff(c_747, plain, (![B_186]: (v4_relat_1('#skF_4', B_186) | ~r1_tarski('#skF_1', B_186))), inference(resolution, [status(thm)], [c_669, c_92])).
% 2.82/1.53  tff(c_12, plain, (![B_10, A_9]: (k7_relat_1(B_10, A_9)=B_10 | ~v4_relat_1(B_10, A_9) | ~v1_relat_1(B_10))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.82/1.53  tff(c_750, plain, (![B_186]: (k7_relat_1('#skF_4', B_186)='#skF_4' | ~v1_relat_1('#skF_4') | ~r1_tarski('#skF_1', B_186))), inference(resolution, [status(thm)], [c_747, c_12])).
% 2.82/1.53  tff(c_754, plain, (![B_187]: (k7_relat_1('#skF_4', B_187)='#skF_4' | ~r1_tarski('#skF_1', B_187))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_750])).
% 2.82/1.53  tff(c_768, plain, (k7_relat_1('#skF_4', '#skF_3')='#skF_4'), inference(resolution, [status(thm)], [c_28, c_754])).
% 2.82/1.53  tff(c_34, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.82/1.53  tff(c_380, plain, (![A_116, B_117, C_118, D_119]: (k2_partfun1(A_116, B_117, C_118, D_119)=k7_relat_1(C_118, D_119) | ~m1_subset_1(C_118, k1_zfmisc_1(k2_zfmisc_1(A_116, B_117))) | ~v1_funct_1(C_118))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.82/1.53  tff(c_385, plain, (![D_119]: (k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_119)=k7_relat_1('#skF_4', D_119) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_30, c_380])).
% 2.82/1.53  tff(c_389, plain, (![D_119]: (k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_119)=k7_relat_1('#skF_4', D_119))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_385])).
% 2.82/1.53  tff(c_26, plain, (~r2_relset_1('#skF_1', '#skF_2', k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.82/1.53  tff(c_392, plain, (~r2_relset_1('#skF_1', '#skF_2', k7_relat_1('#skF_4', '#skF_3'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_389, c_26])).
% 2.82/1.53  tff(c_769, plain, (~r2_relset_1('#skF_1', '#skF_2', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_768, c_392])).
% 2.82/1.53  tff(c_772, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_309, c_769])).
% 2.82/1.53  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.82/1.53  
% 2.82/1.53  Inference rules
% 2.82/1.53  ----------------------
% 2.82/1.53  #Ref     : 0
% 2.82/1.53  #Sup     : 184
% 2.82/1.53  #Fact    : 0
% 2.82/1.53  #Define  : 0
% 2.82/1.53  #Split   : 2
% 2.82/1.53  #Chain   : 0
% 2.82/1.53  #Close   : 0
% 2.82/1.53  
% 2.82/1.53  Ordering : KBO
% 2.82/1.53  
% 2.82/1.53  Simplification rules
% 2.82/1.53  ----------------------
% 2.82/1.53  #Subsume      : 25
% 2.82/1.53  #Demod        : 46
% 2.82/1.53  #Tautology    : 45
% 2.82/1.53  #SimpNegUnit  : 0
% 2.82/1.53  #BackRed      : 2
% 2.82/1.53  
% 2.82/1.53  #Partial instantiations: 0
% 2.82/1.53  #Strategies tried      : 1
% 2.82/1.53  
% 2.82/1.53  Timing (in seconds)
% 2.82/1.53  ----------------------
% 2.82/1.54  Preprocessing        : 0.29
% 2.82/1.54  Parsing              : 0.15
% 2.82/1.54  CNF conversion       : 0.02
% 2.82/1.54  Main loop            : 0.36
% 2.82/1.54  Inferencing          : 0.14
% 2.82/1.54  Reduction            : 0.10
% 2.82/1.54  Demodulation         : 0.07
% 2.82/1.54  BG Simplification    : 0.02
% 2.82/1.54  Subsumption          : 0.08
% 2.82/1.54  Abstraction          : 0.02
% 2.82/1.54  MUC search           : 0.00
% 2.82/1.54  Cooper               : 0.00
% 2.82/1.54  Total                : 0.69
% 2.82/1.54  Index Insertion      : 0.00
% 2.82/1.54  Index Deletion       : 0.00
% 2.82/1.54  Index Matching       : 0.00
% 2.82/1.54  BG Taut test         : 0.00
%------------------------------------------------------------------------------
