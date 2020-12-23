%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:13:43 EST 2020

% Result     : Theorem 1.97s
% Output     : CNFRefutation 2.04s
% Verified   : 
% Statistics : Number of formulae       :   51 (  60 expanded)
%              Number of leaves         :   27 (  33 expanded)
%              Depth                    :    9
%              Number of atoms          :   67 ( 100 expanded)
%              Number of equality atoms :   10 (  10 expanded)
%              Maximal formula depth    :   10 (   4 average)
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

tff(f_80,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( r1_tarski(A,C)
         => r2_relset_1(A,B,k2_partfun1(A,B,D,C),D) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_funct_2)).

tff(f_55,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_63,axiom,(
    ! [A,B,C,D,E] :
      ( m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,C)))
     => ( ( r1_tarski(A,B)
          & r1_tarski(C,D) )
       => m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(B,D))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_relset_1)).

tff(f_47,axiom,(
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

tff(f_69,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => k2_partfun1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

tff(c_28,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_72,plain,(
    ! [A_38,B_39,D_40] :
      ( r2_relset_1(A_38,B_39,D_40,D_40)
      | ~ m1_subset_1(D_40,k1_zfmisc_1(k2_zfmisc_1(A_38,B_39))) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_75,plain,(
    r2_relset_1('#skF_1','#skF_2','#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_28,c_72])).

tff(c_46,plain,(
    ! [C_27,A_28,B_29] :
      ( v1_relat_1(C_27)
      | ~ m1_subset_1(C_27,k1_zfmisc_1(k2_zfmisc_1(A_28,B_29))) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_50,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_28,c_46])).

tff(c_26,plain,(
    r1_tarski('#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_92,plain,(
    ! [C_46,A_50,D_47,E_49,B_48] :
      ( m1_subset_1(E_49,k1_zfmisc_1(k2_zfmisc_1(B_48,D_47)))
      | ~ r1_tarski(C_46,D_47)
      | ~ r1_tarski(A_50,B_48)
      | ~ m1_subset_1(E_49,k1_zfmisc_1(k2_zfmisc_1(A_50,C_46))) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_99,plain,(
    ! [E_51,B_52,B_53,A_54] :
      ( m1_subset_1(E_51,k1_zfmisc_1(k2_zfmisc_1(B_52,B_53)))
      | ~ r1_tarski(A_54,B_52)
      | ~ m1_subset_1(E_51,k1_zfmisc_1(k2_zfmisc_1(A_54,B_53))) ) ),
    inference(resolution,[status(thm)],[c_6,c_92])).

tff(c_106,plain,(
    ! [E_55,B_56] :
      ( m1_subset_1(E_55,k1_zfmisc_1(k2_zfmisc_1('#skF_3',B_56)))
      | ~ m1_subset_1(E_55,k1_zfmisc_1(k2_zfmisc_1('#skF_1',B_56))) ) ),
    inference(resolution,[status(thm)],[c_26,c_99])).

tff(c_14,plain,(
    ! [C_10,A_8,B_9] :
      ( v4_relat_1(C_10,A_8)
      | ~ m1_subset_1(C_10,k1_zfmisc_1(k2_zfmisc_1(A_8,B_9))) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_132,plain,(
    ! [E_61,B_62] :
      ( v4_relat_1(E_61,'#skF_3')
      | ~ m1_subset_1(E_61,k1_zfmisc_1(k2_zfmisc_1('#skF_1',B_62))) ) ),
    inference(resolution,[status(thm)],[c_106,c_14])).

tff(c_136,plain,(
    v4_relat_1('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_28,c_132])).

tff(c_8,plain,(
    ! [B_4,A_3] :
      ( k7_relat_1(B_4,A_3) = B_4
      | ~ v4_relat_1(B_4,A_3)
      | ~ v1_relat_1(B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_139,plain,
    ( k7_relat_1('#skF_4','#skF_3') = '#skF_4'
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_136,c_8])).

tff(c_142,plain,(
    k7_relat_1('#skF_4','#skF_3') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_139])).

tff(c_32,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_76,plain,(
    ! [A_41,B_42,C_43,D_44] :
      ( k2_partfun1(A_41,B_42,C_43,D_44) = k7_relat_1(C_43,D_44)
      | ~ m1_subset_1(C_43,k1_zfmisc_1(k2_zfmisc_1(A_41,B_42)))
      | ~ v1_funct_1(C_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_78,plain,(
    ! [D_44] :
      ( k2_partfun1('#skF_1','#skF_2','#skF_4',D_44) = k7_relat_1('#skF_4',D_44)
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_28,c_76])).

tff(c_81,plain,(
    ! [D_44] : k2_partfun1('#skF_1','#skF_2','#skF_4',D_44) = k7_relat_1('#skF_4',D_44) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_78])).

tff(c_24,plain,(
    ~ r2_relset_1('#skF_1','#skF_2',k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_82,plain,(
    ~ r2_relset_1('#skF_1','#skF_2',k7_relat_1('#skF_4','#skF_3'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_81,c_24])).

tff(c_143,plain,(
    ~ r2_relset_1('#skF_1','#skF_2','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_142,c_82])).

tff(c_146,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_75,c_143])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n017.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 10:15:31 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.97/1.18  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.97/1.19  
% 1.97/1.19  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.97/1.19  %$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_partfun1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 1.97/1.19  
% 1.97/1.19  %Foreground sorts:
% 1.97/1.19  
% 1.97/1.19  
% 1.97/1.19  %Background operators:
% 1.97/1.19  
% 1.97/1.19  
% 1.97/1.19  %Foreground operators:
% 1.97/1.19  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 1.97/1.19  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.97/1.19  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 1.97/1.19  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 1.97/1.19  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.97/1.19  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 1.97/1.19  tff('#skF_2', type, '#skF_2': $i).
% 1.97/1.19  tff('#skF_3', type, '#skF_3': $i).
% 1.97/1.19  tff('#skF_1', type, '#skF_1': $i).
% 1.97/1.19  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 1.97/1.19  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.97/1.19  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.97/1.19  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.97/1.19  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.97/1.19  tff('#skF_4', type, '#skF_4': $i).
% 1.97/1.19  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.97/1.19  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 1.97/1.19  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 1.97/1.19  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.97/1.19  
% 2.04/1.20  tff(f_80, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r1_tarski(A, C) => r2_relset_1(A, B, k2_partfun1(A, B, D, C), D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t40_funct_2)).
% 2.04/1.20  tff(f_55, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 2.04/1.20  tff(f_41, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.04/1.20  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.04/1.20  tff(f_63, axiom, (![A, B, C, D, E]: (m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, C))) => ((r1_tarski(A, B) & r1_tarski(C, D)) => m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(B, D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_relset_1)).
% 2.04/1.20  tff(f_47, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.04/1.20  tff(f_37, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t209_relat_1)).
% 2.04/1.20  tff(f_69, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (k2_partfun1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_partfun1)).
% 2.04/1.20  tff(c_28, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.04/1.20  tff(c_72, plain, (![A_38, B_39, D_40]: (r2_relset_1(A_38, B_39, D_40, D_40) | ~m1_subset_1(D_40, k1_zfmisc_1(k2_zfmisc_1(A_38, B_39))))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.04/1.20  tff(c_75, plain, (r2_relset_1('#skF_1', '#skF_2', '#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_28, c_72])).
% 2.04/1.20  tff(c_46, plain, (![C_27, A_28, B_29]: (v1_relat_1(C_27) | ~m1_subset_1(C_27, k1_zfmisc_1(k2_zfmisc_1(A_28, B_29))))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.04/1.20  tff(c_50, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_28, c_46])).
% 2.04/1.20  tff(c_26, plain, (r1_tarski('#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.04/1.20  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.04/1.20  tff(c_92, plain, (![C_46, A_50, D_47, E_49, B_48]: (m1_subset_1(E_49, k1_zfmisc_1(k2_zfmisc_1(B_48, D_47))) | ~r1_tarski(C_46, D_47) | ~r1_tarski(A_50, B_48) | ~m1_subset_1(E_49, k1_zfmisc_1(k2_zfmisc_1(A_50, C_46))))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.04/1.20  tff(c_99, plain, (![E_51, B_52, B_53, A_54]: (m1_subset_1(E_51, k1_zfmisc_1(k2_zfmisc_1(B_52, B_53))) | ~r1_tarski(A_54, B_52) | ~m1_subset_1(E_51, k1_zfmisc_1(k2_zfmisc_1(A_54, B_53))))), inference(resolution, [status(thm)], [c_6, c_92])).
% 2.04/1.20  tff(c_106, plain, (![E_55, B_56]: (m1_subset_1(E_55, k1_zfmisc_1(k2_zfmisc_1('#skF_3', B_56))) | ~m1_subset_1(E_55, k1_zfmisc_1(k2_zfmisc_1('#skF_1', B_56))))), inference(resolution, [status(thm)], [c_26, c_99])).
% 2.04/1.20  tff(c_14, plain, (![C_10, A_8, B_9]: (v4_relat_1(C_10, A_8) | ~m1_subset_1(C_10, k1_zfmisc_1(k2_zfmisc_1(A_8, B_9))))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.04/1.20  tff(c_132, plain, (![E_61, B_62]: (v4_relat_1(E_61, '#skF_3') | ~m1_subset_1(E_61, k1_zfmisc_1(k2_zfmisc_1('#skF_1', B_62))))), inference(resolution, [status(thm)], [c_106, c_14])).
% 2.04/1.20  tff(c_136, plain, (v4_relat_1('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_28, c_132])).
% 2.04/1.20  tff(c_8, plain, (![B_4, A_3]: (k7_relat_1(B_4, A_3)=B_4 | ~v4_relat_1(B_4, A_3) | ~v1_relat_1(B_4))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.04/1.20  tff(c_139, plain, (k7_relat_1('#skF_4', '#skF_3')='#skF_4' | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_136, c_8])).
% 2.04/1.20  tff(c_142, plain, (k7_relat_1('#skF_4', '#skF_3')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_50, c_139])).
% 2.04/1.20  tff(c_32, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.04/1.20  tff(c_76, plain, (![A_41, B_42, C_43, D_44]: (k2_partfun1(A_41, B_42, C_43, D_44)=k7_relat_1(C_43, D_44) | ~m1_subset_1(C_43, k1_zfmisc_1(k2_zfmisc_1(A_41, B_42))) | ~v1_funct_1(C_43))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.04/1.20  tff(c_78, plain, (![D_44]: (k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_44)=k7_relat_1('#skF_4', D_44) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_28, c_76])).
% 2.04/1.20  tff(c_81, plain, (![D_44]: (k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_44)=k7_relat_1('#skF_4', D_44))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_78])).
% 2.04/1.20  tff(c_24, plain, (~r2_relset_1('#skF_1', '#skF_2', k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.04/1.20  tff(c_82, plain, (~r2_relset_1('#skF_1', '#skF_2', k7_relat_1('#skF_4', '#skF_3'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_81, c_24])).
% 2.04/1.20  tff(c_143, plain, (~r2_relset_1('#skF_1', '#skF_2', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_142, c_82])).
% 2.04/1.20  tff(c_146, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_75, c_143])).
% 2.04/1.20  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.04/1.20  
% 2.04/1.20  Inference rules
% 2.04/1.20  ----------------------
% 2.04/1.20  #Ref     : 0
% 2.04/1.20  #Sup     : 24
% 2.04/1.20  #Fact    : 0
% 2.04/1.20  #Define  : 0
% 2.04/1.20  #Split   : 1
% 2.04/1.20  #Chain   : 0
% 2.04/1.20  #Close   : 0
% 2.04/1.20  
% 2.04/1.20  Ordering : KBO
% 2.04/1.20  
% 2.04/1.20  Simplification rules
% 2.04/1.20  ----------------------
% 2.04/1.20  #Subsume      : 2
% 2.04/1.20  #Demod        : 9
% 2.04/1.20  #Tautology    : 8
% 2.04/1.20  #SimpNegUnit  : 0
% 2.04/1.20  #BackRed      : 2
% 2.04/1.20  
% 2.04/1.20  #Partial instantiations: 0
% 2.04/1.20  #Strategies tried      : 1
% 2.04/1.20  
% 2.04/1.20  Timing (in seconds)
% 2.04/1.20  ----------------------
% 2.04/1.21  Preprocessing        : 0.30
% 2.04/1.21  Parsing              : 0.16
% 2.04/1.21  CNF conversion       : 0.02
% 2.04/1.21  Main loop            : 0.15
% 2.04/1.21  Inferencing          : 0.05
% 2.04/1.21  Reduction            : 0.05
% 2.04/1.21  Demodulation         : 0.03
% 2.04/1.21  BG Simplification    : 0.01
% 2.04/1.21  Subsumption          : 0.03
% 2.04/1.21  Abstraction          : 0.01
% 2.04/1.21  MUC search           : 0.00
% 2.04/1.21  Cooper               : 0.00
% 2.04/1.21  Total                : 0.48
% 2.04/1.21  Index Insertion      : 0.00
% 2.04/1.21  Index Deletion       : 0.00
% 2.04/1.21  Index Matching       : 0.00
% 2.04/1.21  BG Taut test         : 0.00
%------------------------------------------------------------------------------
