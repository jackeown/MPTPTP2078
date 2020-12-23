%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:18:03 EST 2020

% Result     : Theorem 13.39s
% Output     : CNFRefutation 13.56s
% Verified   : 
% Statistics : Number of formulae       :   54 (  63 expanded)
%              Number of leaves         :   31 (  37 expanded)
%              Depth                    :    9
%              Number of atoms          :   74 ( 111 expanded)
%              Number of equality atoms :   11 (  17 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k4_tarski > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_4 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_8 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_84,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,B,C)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,C))) )
       => ~ ( r2_hidden(A,k2_relset_1(B,C,D))
            & ! [E] :
                ( m1_subset_1(E,B)
               => A != k1_funct_1(D,E) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t190_funct_2)).

tff(f_64,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( B = k2_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(D,C),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_relat_1)).

tff(f_60,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( r2_hidden(k4_tarski(A,B),C)
      <=> ( r2_hidden(A,k1_relat_1(C))
          & B = k1_funct_1(C,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_funct_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

tff(f_31,axiom,(
    ! [A,B,C,D] :
      ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(C,D))
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,D) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l54_zfmisc_1)).

tff(f_42,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

tff(f_68,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(c_38,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_7'))) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_49,plain,(
    ! [C_44,A_45,B_46] :
      ( v1_relat_1(C_44)
      | ~ m1_subset_1(C_44,k1_zfmisc_1(k2_zfmisc_1(A_45,B_46))) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_53,plain,(
    v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_38,c_49])).

tff(c_42,plain,(
    v1_funct_1('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_85,plain,(
    ! [A_72,C_73] :
      ( r2_hidden(k4_tarski('#skF_4'(A_72,k2_relat_1(A_72),C_73),C_73),A_72)
      | ~ r2_hidden(C_73,k2_relat_1(A_72)) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_26,plain,(
    ! [C_32,A_30,B_31] :
      ( k1_funct_1(C_32,A_30) = B_31
      | ~ r2_hidden(k4_tarski(A_30,B_31),C_32)
      | ~ v1_funct_1(C_32)
      | ~ v1_relat_1(C_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_108,plain,(
    ! [A_72,C_73] :
      ( k1_funct_1(A_72,'#skF_4'(A_72,k2_relat_1(A_72),C_73)) = C_73
      | ~ v1_funct_1(A_72)
      | ~ v1_relat_1(A_72)
      | ~ r2_hidden(C_73,k2_relat_1(A_72)) ) ),
    inference(resolution,[status(thm)],[c_85,c_26])).

tff(c_8,plain,(
    ! [C_8,A_5,B_6] :
      ( r2_hidden(C_8,A_5)
      | ~ r2_hidden(C_8,B_6)
      | ~ m1_subset_1(B_6,k1_zfmisc_1(A_5)) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_3295,plain,(
    ! [A_298,C_299,A_300] :
      ( r2_hidden(k4_tarski('#skF_4'(A_298,k2_relat_1(A_298),C_299),C_299),A_300)
      | ~ m1_subset_1(A_298,k1_zfmisc_1(A_300))
      | ~ r2_hidden(C_299,k2_relat_1(A_298)) ) ),
    inference(resolution,[status(thm)],[c_85,c_8])).

tff(c_6,plain,(
    ! [A_1,C_3,B_2,D_4] :
      ( r2_hidden(A_1,C_3)
      | ~ r2_hidden(k4_tarski(A_1,B_2),k2_zfmisc_1(C_3,D_4)) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_20240,plain,(
    ! [A_762,C_763,C_764,D_765] :
      ( r2_hidden('#skF_4'(A_762,k2_relat_1(A_762),C_763),C_764)
      | ~ m1_subset_1(A_762,k1_zfmisc_1(k2_zfmisc_1(C_764,D_765)))
      | ~ r2_hidden(C_763,k2_relat_1(A_762)) ) ),
    inference(resolution,[status(thm)],[c_3295,c_6])).

tff(c_20272,plain,(
    ! [C_766] :
      ( r2_hidden('#skF_4'('#skF_8',k2_relat_1('#skF_8'),C_766),'#skF_6')
      | ~ r2_hidden(C_766,k2_relat_1('#skF_8')) ) ),
    inference(resolution,[status(thm)],[c_38,c_20240])).

tff(c_10,plain,(
    ! [A_9,B_10] :
      ( m1_subset_1(A_9,B_10)
      | ~ r2_hidden(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_20319,plain,(
    ! [C_767] :
      ( m1_subset_1('#skF_4'('#skF_8',k2_relat_1('#skF_8'),C_767),'#skF_6')
      | ~ r2_hidden(C_767,k2_relat_1('#skF_8')) ) ),
    inference(resolution,[status(thm)],[c_20272,c_10])).

tff(c_34,plain,(
    ! [E_40] :
      ( k1_funct_1('#skF_8',E_40) != '#skF_5'
      | ~ m1_subset_1(E_40,'#skF_6') ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_20324,plain,(
    ! [C_768] :
      ( k1_funct_1('#skF_8','#skF_4'('#skF_8',k2_relat_1('#skF_8'),C_768)) != '#skF_5'
      | ~ r2_hidden(C_768,k2_relat_1('#skF_8')) ) ),
    inference(resolution,[status(thm)],[c_20319,c_34])).

tff(c_20328,plain,(
    ! [C_73] :
      ( C_73 != '#skF_5'
      | ~ r2_hidden(C_73,k2_relat_1('#skF_8'))
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8')
      | ~ r2_hidden(C_73,k2_relat_1('#skF_8')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_108,c_20324])).

tff(c_20332,plain,(
    ~ r2_hidden('#skF_5',k2_relat_1('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_53,c_42,c_20328])).

tff(c_62,plain,(
    ! [A_62,B_63,C_64] :
      ( k2_relset_1(A_62,B_63,C_64) = k2_relat_1(C_64)
      | ~ m1_subset_1(C_64,k1_zfmisc_1(k2_zfmisc_1(A_62,B_63))) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_66,plain,(
    k2_relset_1('#skF_6','#skF_7','#skF_8') = k2_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_38,c_62])).

tff(c_36,plain,(
    r2_hidden('#skF_5',k2_relset_1('#skF_6','#skF_7','#skF_8')) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_70,plain,(
    r2_hidden('#skF_5',k2_relat_1('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_36])).

tff(c_20334,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_20332,c_70])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n014.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 18:33:07 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 13.39/4.65  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 13.39/4.65  
% 13.39/4.65  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 13.39/4.66  %$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k4_tarski > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_4 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_8 > #skF_2 > #skF_1
% 13.39/4.66  
% 13.39/4.66  %Foreground sorts:
% 13.39/4.66  
% 13.39/4.66  
% 13.39/4.66  %Background operators:
% 13.39/4.66  
% 13.39/4.66  
% 13.39/4.66  %Foreground operators:
% 13.39/4.66  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 13.39/4.66  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 13.39/4.66  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 13.39/4.66  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 13.39/4.66  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 13.39/4.66  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 13.39/4.66  tff('#skF_7', type, '#skF_7': $i).
% 13.39/4.66  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 13.39/4.66  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 13.39/4.66  tff('#skF_5', type, '#skF_5': $i).
% 13.39/4.66  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 13.39/4.66  tff('#skF_6', type, '#skF_6': $i).
% 13.39/4.66  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 13.39/4.66  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 13.39/4.66  tff('#skF_8', type, '#skF_8': $i).
% 13.39/4.66  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 13.39/4.66  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 13.39/4.66  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 13.39/4.66  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 13.39/4.66  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 13.39/4.66  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 13.39/4.66  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 13.39/4.66  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 13.39/4.66  
% 13.56/4.67  tff(f_84, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, B, C)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => ~(r2_hidden(A, k2_relset_1(B, C, D)) & (![E]: (m1_subset_1(E, B) => ~(A = k1_funct_1(D, E))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t190_funct_2)).
% 13.56/4.67  tff(f_64, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 13.56/4.67  tff(f_50, axiom, (![A, B]: ((B = k2_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(D, C), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_relat_1)).
% 13.56/4.67  tff(f_60, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(k4_tarski(A, B), C) <=> (r2_hidden(A, k1_relat_1(C)) & (B = k1_funct_1(C, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_funct_1)).
% 13.56/4.67  tff(f_38, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_subset_1)).
% 13.56/4.67  tff(f_31, axiom, (![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(C, D)) <=> (r2_hidden(A, C) & r2_hidden(B, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l54_zfmisc_1)).
% 13.56/4.67  tff(f_42, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_subset)).
% 13.56/4.67  tff(f_68, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 13.56/4.67  tff(c_38, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_6', '#skF_7')))), inference(cnfTransformation, [status(thm)], [f_84])).
% 13.56/4.67  tff(c_49, plain, (![C_44, A_45, B_46]: (v1_relat_1(C_44) | ~m1_subset_1(C_44, k1_zfmisc_1(k2_zfmisc_1(A_45, B_46))))), inference(cnfTransformation, [status(thm)], [f_64])).
% 13.56/4.67  tff(c_53, plain, (v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_38, c_49])).
% 13.56/4.67  tff(c_42, plain, (v1_funct_1('#skF_8')), inference(cnfTransformation, [status(thm)], [f_84])).
% 13.56/4.67  tff(c_85, plain, (![A_72, C_73]: (r2_hidden(k4_tarski('#skF_4'(A_72, k2_relat_1(A_72), C_73), C_73), A_72) | ~r2_hidden(C_73, k2_relat_1(A_72)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 13.56/4.67  tff(c_26, plain, (![C_32, A_30, B_31]: (k1_funct_1(C_32, A_30)=B_31 | ~r2_hidden(k4_tarski(A_30, B_31), C_32) | ~v1_funct_1(C_32) | ~v1_relat_1(C_32))), inference(cnfTransformation, [status(thm)], [f_60])).
% 13.56/4.67  tff(c_108, plain, (![A_72, C_73]: (k1_funct_1(A_72, '#skF_4'(A_72, k2_relat_1(A_72), C_73))=C_73 | ~v1_funct_1(A_72) | ~v1_relat_1(A_72) | ~r2_hidden(C_73, k2_relat_1(A_72)))), inference(resolution, [status(thm)], [c_85, c_26])).
% 13.56/4.67  tff(c_8, plain, (![C_8, A_5, B_6]: (r2_hidden(C_8, A_5) | ~r2_hidden(C_8, B_6) | ~m1_subset_1(B_6, k1_zfmisc_1(A_5)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 13.56/4.67  tff(c_3295, plain, (![A_298, C_299, A_300]: (r2_hidden(k4_tarski('#skF_4'(A_298, k2_relat_1(A_298), C_299), C_299), A_300) | ~m1_subset_1(A_298, k1_zfmisc_1(A_300)) | ~r2_hidden(C_299, k2_relat_1(A_298)))), inference(resolution, [status(thm)], [c_85, c_8])).
% 13.56/4.67  tff(c_6, plain, (![A_1, C_3, B_2, D_4]: (r2_hidden(A_1, C_3) | ~r2_hidden(k4_tarski(A_1, B_2), k2_zfmisc_1(C_3, D_4)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 13.56/4.67  tff(c_20240, plain, (![A_762, C_763, C_764, D_765]: (r2_hidden('#skF_4'(A_762, k2_relat_1(A_762), C_763), C_764) | ~m1_subset_1(A_762, k1_zfmisc_1(k2_zfmisc_1(C_764, D_765))) | ~r2_hidden(C_763, k2_relat_1(A_762)))), inference(resolution, [status(thm)], [c_3295, c_6])).
% 13.56/4.67  tff(c_20272, plain, (![C_766]: (r2_hidden('#skF_4'('#skF_8', k2_relat_1('#skF_8'), C_766), '#skF_6') | ~r2_hidden(C_766, k2_relat_1('#skF_8')))), inference(resolution, [status(thm)], [c_38, c_20240])).
% 13.56/4.67  tff(c_10, plain, (![A_9, B_10]: (m1_subset_1(A_9, B_10) | ~r2_hidden(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_42])).
% 13.56/4.67  tff(c_20319, plain, (![C_767]: (m1_subset_1('#skF_4'('#skF_8', k2_relat_1('#skF_8'), C_767), '#skF_6') | ~r2_hidden(C_767, k2_relat_1('#skF_8')))), inference(resolution, [status(thm)], [c_20272, c_10])).
% 13.56/4.67  tff(c_34, plain, (![E_40]: (k1_funct_1('#skF_8', E_40)!='#skF_5' | ~m1_subset_1(E_40, '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_84])).
% 13.56/4.67  tff(c_20324, plain, (![C_768]: (k1_funct_1('#skF_8', '#skF_4'('#skF_8', k2_relat_1('#skF_8'), C_768))!='#skF_5' | ~r2_hidden(C_768, k2_relat_1('#skF_8')))), inference(resolution, [status(thm)], [c_20319, c_34])).
% 13.56/4.67  tff(c_20328, plain, (![C_73]: (C_73!='#skF_5' | ~r2_hidden(C_73, k2_relat_1('#skF_8')) | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8') | ~r2_hidden(C_73, k2_relat_1('#skF_8')))), inference(superposition, [status(thm), theory('equality')], [c_108, c_20324])).
% 13.56/4.67  tff(c_20332, plain, (~r2_hidden('#skF_5', k2_relat_1('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_53, c_42, c_20328])).
% 13.56/4.67  tff(c_62, plain, (![A_62, B_63, C_64]: (k2_relset_1(A_62, B_63, C_64)=k2_relat_1(C_64) | ~m1_subset_1(C_64, k1_zfmisc_1(k2_zfmisc_1(A_62, B_63))))), inference(cnfTransformation, [status(thm)], [f_68])).
% 13.56/4.67  tff(c_66, plain, (k2_relset_1('#skF_6', '#skF_7', '#skF_8')=k2_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_38, c_62])).
% 13.56/4.67  tff(c_36, plain, (r2_hidden('#skF_5', k2_relset_1('#skF_6', '#skF_7', '#skF_8'))), inference(cnfTransformation, [status(thm)], [f_84])).
% 13.56/4.67  tff(c_70, plain, (r2_hidden('#skF_5', k2_relat_1('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_36])).
% 13.56/4.67  tff(c_20334, plain, $false, inference(negUnitSimplification, [status(thm)], [c_20332, c_70])).
% 13.56/4.67  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 13.56/4.67  
% 13.56/4.67  Inference rules
% 13.56/4.67  ----------------------
% 13.56/4.67  #Ref     : 0
% 13.56/4.67  #Sup     : 5305
% 13.56/4.67  #Fact    : 0
% 13.56/4.67  #Define  : 0
% 13.56/4.67  #Split   : 15
% 13.56/4.67  #Chain   : 0
% 13.56/4.67  #Close   : 0
% 13.56/4.67  
% 13.56/4.67  Ordering : KBO
% 13.56/4.67  
% 13.56/4.67  Simplification rules
% 13.56/4.67  ----------------------
% 13.56/4.67  #Subsume      : 365
% 13.56/4.67  #Demod        : 188
% 13.56/4.67  #Tautology    : 91
% 13.56/4.67  #SimpNegUnit  : 35
% 13.56/4.67  #BackRed      : 85
% 13.56/4.67  
% 13.56/4.67  #Partial instantiations: 0
% 13.56/4.67  #Strategies tried      : 1
% 13.56/4.67  
% 13.56/4.67  Timing (in seconds)
% 13.56/4.67  ----------------------
% 13.58/4.67  Preprocessing        : 0.30
% 13.58/4.67  Parsing              : 0.15
% 13.58/4.67  CNF conversion       : 0.02
% 13.58/4.67  Main loop            : 3.59
% 13.58/4.67  Inferencing          : 0.83
% 13.58/4.67  Reduction            : 0.72
% 13.58/4.67  Demodulation         : 0.47
% 13.58/4.67  BG Simplification    : 0.13
% 13.58/4.67  Subsumption          : 1.57
% 13.58/4.67  Abstraction          : 0.16
% 13.58/4.67  MUC search           : 0.00
% 13.58/4.67  Cooper               : 0.00
% 13.58/4.67  Total                : 3.92
% 13.58/4.67  Index Insertion      : 0.00
% 13.58/4.67  Index Deletion       : 0.00
% 13.58/4.67  Index Matching       : 0.00
% 13.58/4.67  BG Taut test         : 0.00
%------------------------------------------------------------------------------
