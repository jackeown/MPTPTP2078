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
% DateTime   : Thu Dec  3 10:13:44 EST 2020

% Result     : Theorem 2.14s
% Output     : CNFRefutation 2.14s
% Verified   : 
% Statistics : Number of formulae       :   55 (  67 expanded)
%              Number of leaves         :   28 (  36 expanded)
%              Depth                    :    9
%              Number of atoms          :   76 ( 118 expanded)
%              Number of equality atoms :    9 (   9 expanded)
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_funct_2)).

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
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_65,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => k2_partfun1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

tff(f_59,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => r2_relset_1(A,B,C,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',reflexivity_r2_relset_1)).

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

tff(c_62,plain,(
    ! [C_38,A_39,B_40] :
      ( v4_relat_1(C_38,A_39)
      | ~ m1_subset_1(C_38,k1_zfmisc_1(k2_zfmisc_1(A_39,B_40))) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_66,plain,(
    v4_relat_1('#skF_4','#skF_1') ),
    inference(resolution,[status(thm)],[c_24,c_62])).

tff(c_6,plain,(
    ! [B_5,A_4] :
      ( r1_tarski(k1_relat_1(B_5),A_4)
      | ~ v4_relat_1(B_5,A_4)
      | ~ v1_relat_1(B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_22,plain,(
    r1_tarski('#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_40,plain,(
    ! [A_30,C_31,B_32] :
      ( r1_tarski(A_30,C_31)
      | ~ r1_tarski(B_32,C_31)
      | ~ r1_tarski(A_30,B_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_44,plain,(
    ! [A_33] :
      ( r1_tarski(A_33,'#skF_3')
      | ~ r1_tarski(A_33,'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_22,c_40])).

tff(c_4,plain,(
    ! [B_5,A_4] :
      ( v4_relat_1(B_5,A_4)
      | ~ r1_tarski(k1_relat_1(B_5),A_4)
      | ~ v1_relat_1(B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_104,plain,(
    ! [B_48] :
      ( v4_relat_1(B_48,'#skF_3')
      | ~ v1_relat_1(B_48)
      | ~ r1_tarski(k1_relat_1(B_48),'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_44,c_4])).

tff(c_110,plain,(
    ! [B_49] :
      ( v4_relat_1(B_49,'#skF_3')
      | ~ v4_relat_1(B_49,'#skF_1')
      | ~ v1_relat_1(B_49) ) ),
    inference(resolution,[status(thm)],[c_6,c_104])).

tff(c_8,plain,(
    ! [B_7,A_6] :
      ( k7_relat_1(B_7,A_6) = B_7
      | ~ v4_relat_1(B_7,A_6)
      | ~ v1_relat_1(B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_115,plain,(
    ! [B_50] :
      ( k7_relat_1(B_50,'#skF_3') = B_50
      | ~ v4_relat_1(B_50,'#skF_1')
      | ~ v1_relat_1(B_50) ) ),
    inference(resolution,[status(thm)],[c_110,c_8])).

tff(c_118,plain,
    ( k7_relat_1('#skF_4','#skF_3') = '#skF_4'
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_66,c_115])).

tff(c_121,plain,(
    k7_relat_1('#skF_4','#skF_3') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_33,c_118])).

tff(c_28,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_67,plain,(
    ! [A_41,B_42,C_43,D_44] :
      ( k2_partfun1(A_41,B_42,C_43,D_44) = k7_relat_1(C_43,D_44)
      | ~ m1_subset_1(C_43,k1_zfmisc_1(k2_zfmisc_1(A_41,B_42)))
      | ~ v1_funct_1(C_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_69,plain,(
    ! [D_44] :
      ( k2_partfun1('#skF_1','#skF_2','#skF_4',D_44) = k7_relat_1('#skF_4',D_44)
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_24,c_67])).

tff(c_72,plain,(
    ! [D_44] : k2_partfun1('#skF_1','#skF_2','#skF_4',D_44) = k7_relat_1('#skF_4',D_44) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_69])).

tff(c_20,plain,(
    ~ r2_relset_1('#skF_1','#skF_2',k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_83,plain,(
    ~ r2_relset_1('#skF_1','#skF_2',k7_relat_1('#skF_4','#skF_3'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_20])).

tff(c_122,plain,(
    ~ r2_relset_1('#skF_1','#skF_2','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_121,c_83])).

tff(c_127,plain,(
    ! [A_51,B_52,C_53,D_54] :
      ( r2_relset_1(A_51,B_52,C_53,C_53)
      | ~ m1_subset_1(D_54,k1_zfmisc_1(k2_zfmisc_1(A_51,B_52)))
      | ~ m1_subset_1(C_53,k1_zfmisc_1(k2_zfmisc_1(A_51,B_52))) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_131,plain,(
    ! [C_55] :
      ( r2_relset_1('#skF_1','#skF_2',C_55,C_55)
      | ~ m1_subset_1(C_55,k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ) ),
    inference(resolution,[status(thm)],[c_24,c_127])).

tff(c_133,plain,(
    r2_relset_1('#skF_1','#skF_2','#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_24,c_131])).

tff(c_137,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_122,c_133])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n017.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 19:49:16 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.14/1.19  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.14/1.19  
% 2.14/1.19  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.14/1.19  %$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_partfun1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.14/1.19  
% 2.14/1.19  %Foreground sorts:
% 2.14/1.19  
% 2.14/1.19  
% 2.14/1.19  %Background operators:
% 2.14/1.19  
% 2.14/1.19  
% 2.14/1.19  %Foreground operators:
% 2.14/1.19  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.14/1.19  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.14/1.19  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 2.14/1.19  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.14/1.19  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.14/1.19  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.14/1.19  tff('#skF_2', type, '#skF_2': $i).
% 2.14/1.19  tff('#skF_3', type, '#skF_3': $i).
% 2.14/1.19  tff('#skF_1', type, '#skF_1': $i).
% 2.14/1.19  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.14/1.19  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.14/1.19  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.14/1.19  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.14/1.19  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.14/1.19  tff('#skF_4', type, '#skF_4': $i).
% 2.14/1.19  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.14/1.19  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 2.14/1.19  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.14/1.19  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.14/1.19  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.14/1.19  
% 2.14/1.21  tff(f_76, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r1_tarski(A, C) => r2_relset_1(A, B, k2_partfun1(A, B, D, C), D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t40_funct_2)).
% 2.14/1.21  tff(f_47, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.14/1.21  tff(f_53, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.14/1.21  tff(f_37, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d18_relat_1)).
% 2.14/1.21  tff(f_31, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 2.14/1.21  tff(f_43, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t209_relat_1)).
% 2.14/1.21  tff(f_65, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (k2_partfun1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_partfun1)).
% 2.14/1.21  tff(f_59, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => r2_relset_1(A, B, C, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', reflexivity_r2_relset_1)).
% 2.14/1.21  tff(c_24, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.14/1.21  tff(c_29, plain, (![C_22, A_23, B_24]: (v1_relat_1(C_22) | ~m1_subset_1(C_22, k1_zfmisc_1(k2_zfmisc_1(A_23, B_24))))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.14/1.21  tff(c_33, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_24, c_29])).
% 2.14/1.21  tff(c_62, plain, (![C_38, A_39, B_40]: (v4_relat_1(C_38, A_39) | ~m1_subset_1(C_38, k1_zfmisc_1(k2_zfmisc_1(A_39, B_40))))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.14/1.21  tff(c_66, plain, (v4_relat_1('#skF_4', '#skF_1')), inference(resolution, [status(thm)], [c_24, c_62])).
% 2.14/1.21  tff(c_6, plain, (![B_5, A_4]: (r1_tarski(k1_relat_1(B_5), A_4) | ~v4_relat_1(B_5, A_4) | ~v1_relat_1(B_5))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.14/1.21  tff(c_22, plain, (r1_tarski('#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.14/1.21  tff(c_40, plain, (![A_30, C_31, B_32]: (r1_tarski(A_30, C_31) | ~r1_tarski(B_32, C_31) | ~r1_tarski(A_30, B_32))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.14/1.21  tff(c_44, plain, (![A_33]: (r1_tarski(A_33, '#skF_3') | ~r1_tarski(A_33, '#skF_1'))), inference(resolution, [status(thm)], [c_22, c_40])).
% 2.14/1.21  tff(c_4, plain, (![B_5, A_4]: (v4_relat_1(B_5, A_4) | ~r1_tarski(k1_relat_1(B_5), A_4) | ~v1_relat_1(B_5))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.14/1.21  tff(c_104, plain, (![B_48]: (v4_relat_1(B_48, '#skF_3') | ~v1_relat_1(B_48) | ~r1_tarski(k1_relat_1(B_48), '#skF_1'))), inference(resolution, [status(thm)], [c_44, c_4])).
% 2.14/1.21  tff(c_110, plain, (![B_49]: (v4_relat_1(B_49, '#skF_3') | ~v4_relat_1(B_49, '#skF_1') | ~v1_relat_1(B_49))), inference(resolution, [status(thm)], [c_6, c_104])).
% 2.14/1.21  tff(c_8, plain, (![B_7, A_6]: (k7_relat_1(B_7, A_6)=B_7 | ~v4_relat_1(B_7, A_6) | ~v1_relat_1(B_7))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.14/1.21  tff(c_115, plain, (![B_50]: (k7_relat_1(B_50, '#skF_3')=B_50 | ~v4_relat_1(B_50, '#skF_1') | ~v1_relat_1(B_50))), inference(resolution, [status(thm)], [c_110, c_8])).
% 2.14/1.21  tff(c_118, plain, (k7_relat_1('#skF_4', '#skF_3')='#skF_4' | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_66, c_115])).
% 2.14/1.21  tff(c_121, plain, (k7_relat_1('#skF_4', '#skF_3')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_33, c_118])).
% 2.14/1.21  tff(c_28, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.14/1.21  tff(c_67, plain, (![A_41, B_42, C_43, D_44]: (k2_partfun1(A_41, B_42, C_43, D_44)=k7_relat_1(C_43, D_44) | ~m1_subset_1(C_43, k1_zfmisc_1(k2_zfmisc_1(A_41, B_42))) | ~v1_funct_1(C_43))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.14/1.21  tff(c_69, plain, (![D_44]: (k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_44)=k7_relat_1('#skF_4', D_44) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_24, c_67])).
% 2.14/1.21  tff(c_72, plain, (![D_44]: (k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_44)=k7_relat_1('#skF_4', D_44))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_69])).
% 2.14/1.21  tff(c_20, plain, (~r2_relset_1('#skF_1', '#skF_2', k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.14/1.21  tff(c_83, plain, (~r2_relset_1('#skF_1', '#skF_2', k7_relat_1('#skF_4', '#skF_3'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_20])).
% 2.14/1.21  tff(c_122, plain, (~r2_relset_1('#skF_1', '#skF_2', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_121, c_83])).
% 2.14/1.21  tff(c_127, plain, (![A_51, B_52, C_53, D_54]: (r2_relset_1(A_51, B_52, C_53, C_53) | ~m1_subset_1(D_54, k1_zfmisc_1(k2_zfmisc_1(A_51, B_52))) | ~m1_subset_1(C_53, k1_zfmisc_1(k2_zfmisc_1(A_51, B_52))))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.14/1.21  tff(c_131, plain, (![C_55]: (r2_relset_1('#skF_1', '#skF_2', C_55, C_55) | ~m1_subset_1(C_55, k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))))), inference(resolution, [status(thm)], [c_24, c_127])).
% 2.14/1.21  tff(c_133, plain, (r2_relset_1('#skF_1', '#skF_2', '#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_24, c_131])).
% 2.14/1.21  tff(c_137, plain, $false, inference(negUnitSimplification, [status(thm)], [c_122, c_133])).
% 2.14/1.21  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.14/1.21  
% 2.14/1.21  Inference rules
% 2.14/1.21  ----------------------
% 2.14/1.21  #Ref     : 0
% 2.14/1.21  #Sup     : 24
% 2.14/1.21  #Fact    : 0
% 2.14/1.21  #Define  : 0
% 2.14/1.21  #Split   : 0
% 2.14/1.21  #Chain   : 0
% 2.14/1.21  #Close   : 0
% 2.14/1.21  
% 2.14/1.21  Ordering : KBO
% 2.14/1.21  
% 2.14/1.21  Simplification rules
% 2.14/1.21  ----------------------
% 2.14/1.21  #Subsume      : 1
% 2.14/1.21  #Demod        : 6
% 2.14/1.21  #Tautology    : 8
% 2.14/1.21  #SimpNegUnit  : 1
% 2.14/1.21  #BackRed      : 2
% 2.14/1.21  
% 2.14/1.21  #Partial instantiations: 0
% 2.14/1.21  #Strategies tried      : 1
% 2.14/1.21  
% 2.14/1.21  Timing (in seconds)
% 2.14/1.21  ----------------------
% 2.14/1.21  Preprocessing        : 0.29
% 2.14/1.21  Parsing              : 0.16
% 2.14/1.21  CNF conversion       : 0.02
% 2.14/1.21  Main loop            : 0.15
% 2.14/1.21  Inferencing          : 0.06
% 2.14/1.21  Reduction            : 0.05
% 2.14/1.21  Demodulation         : 0.03
% 2.14/1.21  BG Simplification    : 0.01
% 2.14/1.21  Subsumption          : 0.02
% 2.14/1.21  Abstraction          : 0.01
% 2.14/1.21  MUC search           : 0.00
% 2.14/1.21  Cooper               : 0.00
% 2.14/1.21  Total                : 0.47
% 2.14/1.21  Index Insertion      : 0.00
% 2.14/1.21  Index Deletion       : 0.00
% 2.14/1.21  Index Matching       : 0.00
% 2.14/1.21  BG Taut test         : 0.00
%------------------------------------------------------------------------------
