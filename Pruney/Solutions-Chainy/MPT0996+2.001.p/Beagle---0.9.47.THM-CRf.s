%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:13:51 EST 2020

% Result     : Theorem 1.86s
% Output     : CNFRefutation 1.94s
% Verified   : 
% Statistics : Number of formulae       :   47 (  57 expanded)
%              Number of leaves         :   28 (  33 expanded)
%              Depth                    :    7
%              Number of atoms          :   52 (  76 expanded)
%              Number of equality atoms :    6 (   6 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k9_relat_1 > k2_zfmisc_1 > k2_xboole_0 > #nlpp > k2_relat_1 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k7_relset_1,type,(
    k7_relset_1: ( $i * $i * $i * $i ) > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_66,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => r1_tarski(k7_relset_1(A,B,D,C),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_funct_2)).

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

tff(f_39,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k9_relat_1(B,A),k2_relat_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t144_relat_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_29,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_xboole_0(A,B),C)
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_xboole_1)).

tff(f_57,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(c_22,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_33,plain,(
    ! [C_24,A_25,B_26] :
      ( v1_relat_1(C_24)
      | ~ m1_subset_1(C_24,k1_zfmisc_1(k2_zfmisc_1(A_25,B_26))) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_37,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_22,c_33])).

tff(c_44,plain,(
    ! [C_33,B_34,A_35] :
      ( v5_relat_1(C_33,B_34)
      | ~ m1_subset_1(C_33,k1_zfmisc_1(k2_zfmisc_1(A_35,B_34))) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_48,plain,(
    v5_relat_1('#skF_4','#skF_2') ),
    inference(resolution,[status(thm)],[c_22,c_44])).

tff(c_8,plain,(
    ! [B_7,A_6] :
      ( r1_tarski(k2_relat_1(B_7),A_6)
      | ~ v5_relat_1(B_7,A_6)
      | ~ v1_relat_1(B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_28,plain,(
    ! [B_22,A_23] :
      ( r1_tarski(k9_relat_1(B_22,A_23),k2_relat_1(B_22))
      | ~ v1_relat_1(B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_4,plain,(
    ! [A_4,B_5] :
      ( k2_xboole_0(A_4,B_5) = B_5
      | ~ r1_tarski(A_4,B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_85,plain,(
    ! [B_47,A_48] :
      ( k2_xboole_0(k9_relat_1(B_47,A_48),k2_relat_1(B_47)) = k2_relat_1(B_47)
      | ~ v1_relat_1(B_47) ) ),
    inference(resolution,[status(thm)],[c_28,c_4])).

tff(c_2,plain,(
    ! [A_1,C_3,B_2] :
      ( r1_tarski(A_1,C_3)
      | ~ r1_tarski(k2_xboole_0(A_1,B_2),C_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_97,plain,(
    ! [B_49,A_50,C_51] :
      ( r1_tarski(k9_relat_1(B_49,A_50),C_51)
      | ~ r1_tarski(k2_relat_1(B_49),C_51)
      | ~ v1_relat_1(B_49) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_85,c_2])).

tff(c_59,plain,(
    ! [A_40,B_41,C_42,D_43] :
      ( k7_relset_1(A_40,B_41,C_42,D_43) = k9_relat_1(C_42,D_43)
      | ~ m1_subset_1(C_42,k1_zfmisc_1(k2_zfmisc_1(A_40,B_41))) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_62,plain,(
    ! [D_43] : k7_relset_1('#skF_1','#skF_2','#skF_4',D_43) = k9_relat_1('#skF_4',D_43) ),
    inference(resolution,[status(thm)],[c_22,c_59])).

tff(c_20,plain,(
    ~ r1_tarski(k7_relset_1('#skF_1','#skF_2','#skF_4','#skF_3'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_63,plain,(
    ~ r1_tarski(k9_relat_1('#skF_4','#skF_3'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_20])).

tff(c_100,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_4'),'#skF_2')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_97,c_63])).

tff(c_106,plain,(
    ~ r1_tarski(k2_relat_1('#skF_4'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_37,c_100])).

tff(c_110,plain,
    ( ~ v5_relat_1('#skF_4','#skF_2')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_8,c_106])).

tff(c_114,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_37,c_48,c_110])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n019.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 15:08:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.86/1.21  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.86/1.22  
% 1.86/1.22  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.86/1.22  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k9_relat_1 > k2_zfmisc_1 > k2_xboole_0 > #nlpp > k2_relat_1 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 1.86/1.22  
% 1.86/1.22  %Foreground sorts:
% 1.86/1.22  
% 1.86/1.22  
% 1.86/1.22  %Background operators:
% 1.86/1.22  
% 1.86/1.22  
% 1.86/1.22  %Foreground operators:
% 1.86/1.22  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 1.86/1.22  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.86/1.22  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.86/1.22  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.86/1.22  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 1.86/1.22  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 1.86/1.22  tff('#skF_2', type, '#skF_2': $i).
% 1.86/1.22  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 1.86/1.22  tff('#skF_3', type, '#skF_3': $i).
% 1.86/1.22  tff('#skF_1', type, '#skF_1': $i).
% 1.86/1.22  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 1.86/1.22  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.86/1.22  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.86/1.22  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.86/1.22  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.86/1.22  tff('#skF_4', type, '#skF_4': $i).
% 1.86/1.22  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.86/1.22  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 1.86/1.22  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.86/1.22  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.86/1.22  
% 1.94/1.23  tff(f_66, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => r1_tarski(k7_relset_1(A, B, D, C), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_funct_2)).
% 1.94/1.23  tff(f_47, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 1.94/1.23  tff(f_53, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 1.94/1.23  tff(f_39, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 1.94/1.23  tff(f_43, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k9_relat_1(B, A), k2_relat_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t144_relat_1)).
% 1.94/1.23  tff(f_33, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 1.94/1.23  tff(f_29, axiom, (![A, B, C]: (r1_tarski(k2_xboole_0(A, B), C) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_xboole_1)).
% 1.94/1.23  tff(f_57, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 1.94/1.23  tff(c_22, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_66])).
% 1.94/1.23  tff(c_33, plain, (![C_24, A_25, B_26]: (v1_relat_1(C_24) | ~m1_subset_1(C_24, k1_zfmisc_1(k2_zfmisc_1(A_25, B_26))))), inference(cnfTransformation, [status(thm)], [f_47])).
% 1.94/1.23  tff(c_37, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_22, c_33])).
% 1.94/1.23  tff(c_44, plain, (![C_33, B_34, A_35]: (v5_relat_1(C_33, B_34) | ~m1_subset_1(C_33, k1_zfmisc_1(k2_zfmisc_1(A_35, B_34))))), inference(cnfTransformation, [status(thm)], [f_53])).
% 1.94/1.23  tff(c_48, plain, (v5_relat_1('#skF_4', '#skF_2')), inference(resolution, [status(thm)], [c_22, c_44])).
% 1.94/1.23  tff(c_8, plain, (![B_7, A_6]: (r1_tarski(k2_relat_1(B_7), A_6) | ~v5_relat_1(B_7, A_6) | ~v1_relat_1(B_7))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.94/1.23  tff(c_28, plain, (![B_22, A_23]: (r1_tarski(k9_relat_1(B_22, A_23), k2_relat_1(B_22)) | ~v1_relat_1(B_22))), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.94/1.23  tff(c_4, plain, (![A_4, B_5]: (k2_xboole_0(A_4, B_5)=B_5 | ~r1_tarski(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.94/1.23  tff(c_85, plain, (![B_47, A_48]: (k2_xboole_0(k9_relat_1(B_47, A_48), k2_relat_1(B_47))=k2_relat_1(B_47) | ~v1_relat_1(B_47))), inference(resolution, [status(thm)], [c_28, c_4])).
% 1.94/1.23  tff(c_2, plain, (![A_1, C_3, B_2]: (r1_tarski(A_1, C_3) | ~r1_tarski(k2_xboole_0(A_1, B_2), C_3))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.94/1.23  tff(c_97, plain, (![B_49, A_50, C_51]: (r1_tarski(k9_relat_1(B_49, A_50), C_51) | ~r1_tarski(k2_relat_1(B_49), C_51) | ~v1_relat_1(B_49))), inference(superposition, [status(thm), theory('equality')], [c_85, c_2])).
% 1.94/1.23  tff(c_59, plain, (![A_40, B_41, C_42, D_43]: (k7_relset_1(A_40, B_41, C_42, D_43)=k9_relat_1(C_42, D_43) | ~m1_subset_1(C_42, k1_zfmisc_1(k2_zfmisc_1(A_40, B_41))))), inference(cnfTransformation, [status(thm)], [f_57])).
% 1.94/1.23  tff(c_62, plain, (![D_43]: (k7_relset_1('#skF_1', '#skF_2', '#skF_4', D_43)=k9_relat_1('#skF_4', D_43))), inference(resolution, [status(thm)], [c_22, c_59])).
% 1.94/1.23  tff(c_20, plain, (~r1_tarski(k7_relset_1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_66])).
% 1.94/1.23  tff(c_63, plain, (~r1_tarski(k9_relat_1('#skF_4', '#skF_3'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_20])).
% 1.94/1.23  tff(c_100, plain, (~r1_tarski(k2_relat_1('#skF_4'), '#skF_2') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_97, c_63])).
% 1.94/1.23  tff(c_106, plain, (~r1_tarski(k2_relat_1('#skF_4'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_37, c_100])).
% 1.94/1.23  tff(c_110, plain, (~v5_relat_1('#skF_4', '#skF_2') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_8, c_106])).
% 1.94/1.23  tff(c_114, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_37, c_48, c_110])).
% 1.94/1.23  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.94/1.23  
% 1.94/1.23  Inference rules
% 1.94/1.23  ----------------------
% 1.94/1.23  #Ref     : 0
% 1.94/1.23  #Sup     : 18
% 1.94/1.23  #Fact    : 0
% 1.94/1.23  #Define  : 0
% 1.94/1.23  #Split   : 0
% 1.94/1.23  #Chain   : 0
% 1.94/1.23  #Close   : 0
% 1.94/1.23  
% 1.94/1.23  Ordering : KBO
% 1.94/1.23  
% 1.94/1.23  Simplification rules
% 1.94/1.23  ----------------------
% 1.94/1.23  #Subsume      : 0
% 1.94/1.23  #Demod        : 4
% 1.94/1.23  #Tautology    : 7
% 1.94/1.23  #SimpNegUnit  : 0
% 1.94/1.23  #BackRed      : 1
% 1.94/1.23  
% 1.94/1.23  #Partial instantiations: 0
% 1.94/1.23  #Strategies tried      : 1
% 1.94/1.23  
% 1.94/1.23  Timing (in seconds)
% 1.94/1.23  ----------------------
% 1.94/1.23  Preprocessing        : 0.30
% 1.94/1.23  Parsing              : 0.17
% 1.94/1.23  CNF conversion       : 0.02
% 1.94/1.23  Main loop            : 0.12
% 1.94/1.23  Inferencing          : 0.05
% 1.94/1.23  Reduction            : 0.03
% 1.94/1.23  Demodulation         : 0.02
% 1.94/1.23  BG Simplification    : 0.01
% 1.94/1.23  Subsumption          : 0.02
% 1.94/1.23  Abstraction          : 0.01
% 1.94/1.23  MUC search           : 0.00
% 1.94/1.23  Cooper               : 0.00
% 1.94/1.23  Total                : 0.45
% 1.94/1.23  Index Insertion      : 0.00
% 1.94/1.23  Index Deletion       : 0.00
% 1.94/1.23  Index Matching       : 0.00
% 1.94/1.23  BG Taut test         : 0.00
%------------------------------------------------------------------------------
