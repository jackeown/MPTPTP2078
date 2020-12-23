%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:13:51 EST 2020

% Result     : Theorem 1.68s
% Output     : CNFRefutation 1.68s
% Verified   : 
% Statistics : Number of formulae       :   45 (  50 expanded)
%              Number of leaves         :   27 (  30 expanded)
%              Depth                    :    5
%              Number of atoms          :   55 (  69 expanded)
%              Number of equality atoms :    3 (   3 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k9_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_46,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_69,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => r1_tarski(k7_relset_1(A,B,D,C),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_funct_2)).

tff(f_38,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_56,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k9_relat_1(B,A),k2_relat_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t144_relat_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_60,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(c_10,plain,(
    ! [A_9,B_10] : v1_relat_1(k2_zfmisc_1(A_9,B_10)) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_22,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_29,plain,(
    ! [B_24,A_25] :
      ( v1_relat_1(B_24)
      | ~ m1_subset_1(B_24,k1_zfmisc_1(A_25))
      | ~ v1_relat_1(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_32,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_22,c_29])).

tff(c_35,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_32])).

tff(c_37,plain,(
    ! [C_28,B_29,A_30] :
      ( v5_relat_1(C_28,B_29)
      | ~ m1_subset_1(C_28,k1_zfmisc_1(k2_zfmisc_1(A_30,B_29))) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_41,plain,(
    v5_relat_1('#skF_4','#skF_2') ),
    inference(resolution,[status(thm)],[c_22,c_37])).

tff(c_12,plain,(
    ! [B_12,A_11] :
      ( r1_tarski(k9_relat_1(B_12,A_11),k2_relat_1(B_12))
      | ~ v1_relat_1(B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_51,plain,(
    ! [B_37,A_38] :
      ( r1_tarski(k2_relat_1(B_37),A_38)
      | ~ v5_relat_1(B_37,A_38)
      | ~ v1_relat_1(B_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_2,plain,(
    ! [A_1,C_3,B_2] :
      ( r1_tarski(A_1,C_3)
      | ~ r1_tarski(B_2,C_3)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_79,plain,(
    ! [A_47,A_48,B_49] :
      ( r1_tarski(A_47,A_48)
      | ~ r1_tarski(A_47,k2_relat_1(B_49))
      | ~ v5_relat_1(B_49,A_48)
      | ~ v1_relat_1(B_49) ) ),
    inference(resolution,[status(thm)],[c_51,c_2])).

tff(c_87,plain,(
    ! [B_50,A_51,A_52] :
      ( r1_tarski(k9_relat_1(B_50,A_51),A_52)
      | ~ v5_relat_1(B_50,A_52)
      | ~ v1_relat_1(B_50) ) ),
    inference(resolution,[status(thm)],[c_12,c_79])).

tff(c_59,plain,(
    ! [A_39,B_40,C_41,D_42] :
      ( k7_relset_1(A_39,B_40,C_41,D_42) = k9_relat_1(C_41,D_42)
      | ~ m1_subset_1(C_41,k1_zfmisc_1(k2_zfmisc_1(A_39,B_40))) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_62,plain,(
    ! [D_42] : k7_relset_1('#skF_1','#skF_2','#skF_4',D_42) = k9_relat_1('#skF_4',D_42) ),
    inference(resolution,[status(thm)],[c_22,c_59])).

tff(c_20,plain,(
    ~ r1_tarski(k7_relset_1('#skF_1','#skF_2','#skF_4','#skF_3'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_63,plain,(
    ~ r1_tarski(k9_relat_1('#skF_4','#skF_3'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_20])).

tff(c_97,plain,
    ( ~ v5_relat_1('#skF_4','#skF_2')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_87,c_63])).

tff(c_105,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_35,c_41,c_97])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:54:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.68/1.14  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.68/1.14  
% 1.68/1.14  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.68/1.15  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k9_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 1.68/1.15  
% 1.68/1.15  %Foreground sorts:
% 1.68/1.15  
% 1.68/1.15  
% 1.68/1.15  %Background operators:
% 1.68/1.15  
% 1.68/1.15  
% 1.68/1.15  %Foreground operators:
% 1.68/1.15  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 1.68/1.15  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.68/1.15  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.68/1.15  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.68/1.15  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 1.68/1.15  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 1.68/1.15  tff('#skF_2', type, '#skF_2': $i).
% 1.68/1.15  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 1.68/1.15  tff('#skF_3', type, '#skF_3': $i).
% 1.68/1.15  tff('#skF_1', type, '#skF_1': $i).
% 1.68/1.15  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 1.68/1.15  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.68/1.15  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.68/1.15  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.68/1.15  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.68/1.15  tff('#skF_4', type, '#skF_4': $i).
% 1.68/1.15  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.68/1.15  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 1.68/1.15  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.68/1.15  
% 1.68/1.16  tff(f_46, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 1.68/1.16  tff(f_69, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => r1_tarski(k7_relset_1(A, B, D, C), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_funct_2)).
% 1.68/1.16  tff(f_38, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 1.68/1.16  tff(f_56, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 1.68/1.16  tff(f_50, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k9_relat_1(B, A), k2_relat_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t144_relat_1)).
% 1.68/1.16  tff(f_44, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 1.68/1.16  tff(f_31, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 1.68/1.16  tff(f_60, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 1.68/1.16  tff(c_10, plain, (![A_9, B_10]: (v1_relat_1(k2_zfmisc_1(A_9, B_10)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.68/1.16  tff(c_22, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_69])).
% 1.68/1.16  tff(c_29, plain, (![B_24, A_25]: (v1_relat_1(B_24) | ~m1_subset_1(B_24, k1_zfmisc_1(A_25)) | ~v1_relat_1(A_25))), inference(cnfTransformation, [status(thm)], [f_38])).
% 1.68/1.16  tff(c_32, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_22, c_29])).
% 1.68/1.16  tff(c_35, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_10, c_32])).
% 1.68/1.16  tff(c_37, plain, (![C_28, B_29, A_30]: (v5_relat_1(C_28, B_29) | ~m1_subset_1(C_28, k1_zfmisc_1(k2_zfmisc_1(A_30, B_29))))), inference(cnfTransformation, [status(thm)], [f_56])).
% 1.68/1.16  tff(c_41, plain, (v5_relat_1('#skF_4', '#skF_2')), inference(resolution, [status(thm)], [c_22, c_37])).
% 1.68/1.16  tff(c_12, plain, (![B_12, A_11]: (r1_tarski(k9_relat_1(B_12, A_11), k2_relat_1(B_12)) | ~v1_relat_1(B_12))), inference(cnfTransformation, [status(thm)], [f_50])).
% 1.68/1.16  tff(c_51, plain, (![B_37, A_38]: (r1_tarski(k2_relat_1(B_37), A_38) | ~v5_relat_1(B_37, A_38) | ~v1_relat_1(B_37))), inference(cnfTransformation, [status(thm)], [f_44])).
% 1.68/1.16  tff(c_2, plain, (![A_1, C_3, B_2]: (r1_tarski(A_1, C_3) | ~r1_tarski(B_2, C_3) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.68/1.16  tff(c_79, plain, (![A_47, A_48, B_49]: (r1_tarski(A_47, A_48) | ~r1_tarski(A_47, k2_relat_1(B_49)) | ~v5_relat_1(B_49, A_48) | ~v1_relat_1(B_49))), inference(resolution, [status(thm)], [c_51, c_2])).
% 1.68/1.16  tff(c_87, plain, (![B_50, A_51, A_52]: (r1_tarski(k9_relat_1(B_50, A_51), A_52) | ~v5_relat_1(B_50, A_52) | ~v1_relat_1(B_50))), inference(resolution, [status(thm)], [c_12, c_79])).
% 1.68/1.16  tff(c_59, plain, (![A_39, B_40, C_41, D_42]: (k7_relset_1(A_39, B_40, C_41, D_42)=k9_relat_1(C_41, D_42) | ~m1_subset_1(C_41, k1_zfmisc_1(k2_zfmisc_1(A_39, B_40))))), inference(cnfTransformation, [status(thm)], [f_60])).
% 1.68/1.16  tff(c_62, plain, (![D_42]: (k7_relset_1('#skF_1', '#skF_2', '#skF_4', D_42)=k9_relat_1('#skF_4', D_42))), inference(resolution, [status(thm)], [c_22, c_59])).
% 1.68/1.16  tff(c_20, plain, (~r1_tarski(k7_relset_1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_69])).
% 1.68/1.16  tff(c_63, plain, (~r1_tarski(k9_relat_1('#skF_4', '#skF_3'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_20])).
% 1.68/1.16  tff(c_97, plain, (~v5_relat_1('#skF_4', '#skF_2') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_87, c_63])).
% 1.68/1.16  tff(c_105, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_35, c_41, c_97])).
% 1.68/1.16  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.68/1.16  
% 1.68/1.16  Inference rules
% 1.68/1.16  ----------------------
% 1.68/1.16  #Ref     : 0
% 1.68/1.16  #Sup     : 16
% 1.68/1.16  #Fact    : 0
% 1.68/1.16  #Define  : 0
% 1.68/1.16  #Split   : 0
% 1.68/1.16  #Chain   : 0
% 1.68/1.16  #Close   : 0
% 1.68/1.16  
% 1.68/1.16  Ordering : KBO
% 1.68/1.16  
% 1.68/1.16  Simplification rules
% 1.68/1.16  ----------------------
% 1.68/1.16  #Subsume      : 0
% 1.68/1.16  #Demod        : 4
% 1.68/1.16  #Tautology    : 3
% 1.68/1.16  #SimpNegUnit  : 0
% 1.68/1.16  #BackRed      : 1
% 1.68/1.16  
% 1.68/1.16  #Partial instantiations: 0
% 1.68/1.16  #Strategies tried      : 1
% 1.68/1.16  
% 1.68/1.16  Timing (in seconds)
% 1.68/1.16  ----------------------
% 1.68/1.16  Preprocessing        : 0.29
% 1.68/1.16  Parsing              : 0.16
% 1.68/1.16  CNF conversion       : 0.02
% 1.68/1.16  Main loop            : 0.12
% 1.68/1.16  Inferencing          : 0.05
% 1.91/1.16  Reduction            : 0.03
% 1.91/1.16  Demodulation         : 0.03
% 1.91/1.16  BG Simplification    : 0.01
% 1.91/1.16  Subsumption          : 0.02
% 1.91/1.16  Abstraction          : 0.01
% 1.91/1.16  MUC search           : 0.00
% 1.91/1.16  Cooper               : 0.00
% 1.91/1.16  Total                : 0.43
% 1.91/1.16  Index Insertion      : 0.00
% 1.91/1.16  Index Deletion       : 0.00
% 1.91/1.16  Index Matching       : 0.00
% 1.91/1.16  BG Taut test         : 0.00
%------------------------------------------------------------------------------
