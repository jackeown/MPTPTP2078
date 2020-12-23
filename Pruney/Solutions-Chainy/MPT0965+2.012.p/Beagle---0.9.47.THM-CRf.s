%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:11:01 EST 2020

% Result     : Theorem 2.04s
% Output     : CNFRefutation 2.17s
% Verified   : 
% Statistics : Number of formulae       :   47 (  58 expanded)
%              Number of leaves         :   26 (  34 expanded)
%              Depth                    :    9
%              Number of atoms          :   69 ( 120 expanded)
%              Number of equality atoms :    9 (  17 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

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

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

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

tff(f_73,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( r2_hidden(C,A)
         => ( B = k1_xboole_0
            | r2_hidden(k1_funct_1(D,C),B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_funct_2)).

tff(f_44,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_38,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_48,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_60,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_hidden(C,A)
       => ( B = k1_xboole_0
          | r2_hidden(k1_funct_1(D,C),k2_relset_1(A,B,D)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_funct_2)).

tff(f_34,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A) )
     => ! [C] :
          ( r2_hidden(C,k2_relat_1(B))
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t202_relat_1)).

tff(c_18,plain,(
    r2_hidden('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_20,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_30,plain,(
    ! [C_21,B_22,A_23] :
      ( v5_relat_1(C_21,B_22)
      | ~ m1_subset_1(C_21,k1_zfmisc_1(k2_zfmisc_1(A_23,B_22))) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_34,plain,(
    v5_relat_1('#skF_4','#skF_2') ),
    inference(resolution,[status(thm)],[c_20,c_30])).

tff(c_25,plain,(
    ! [C_18,A_19,B_20] :
      ( v1_relat_1(C_18)
      | ~ m1_subset_1(C_18,k1_zfmisc_1(k2_zfmisc_1(A_19,B_20))) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_29,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_20,c_25])).

tff(c_16,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_24,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_22,plain,(
    v1_funct_2('#skF_4','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_40,plain,(
    ! [A_27,B_28,C_29] :
      ( k2_relset_1(A_27,B_28,C_29) = k2_relat_1(C_29)
      | ~ m1_subset_1(C_29,k1_zfmisc_1(k2_zfmisc_1(A_27,B_28))) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_44,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_20,c_40])).

tff(c_50,plain,(
    ! [D_33,C_34,A_35,B_36] :
      ( r2_hidden(k1_funct_1(D_33,C_34),k2_relset_1(A_35,B_36,D_33))
      | k1_xboole_0 = B_36
      | ~ r2_hidden(C_34,A_35)
      | ~ m1_subset_1(D_33,k1_zfmisc_1(k2_zfmisc_1(A_35,B_36)))
      | ~ v1_funct_2(D_33,A_35,B_36)
      | ~ v1_funct_1(D_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_53,plain,(
    ! [C_34] :
      ( r2_hidden(k1_funct_1('#skF_4',C_34),k2_relat_1('#skF_4'))
      | k1_xboole_0 = '#skF_2'
      | ~ r2_hidden(C_34,'#skF_1')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
      | ~ v1_funct_2('#skF_4','#skF_1','#skF_2')
      | ~ v1_funct_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_50])).

tff(c_55,plain,(
    ! [C_34] :
      ( r2_hidden(k1_funct_1('#skF_4',C_34),k2_relat_1('#skF_4'))
      | k1_xboole_0 = '#skF_2'
      | ~ r2_hidden(C_34,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_22,c_20,c_53])).

tff(c_57,plain,(
    ! [C_37] :
      ( r2_hidden(k1_funct_1('#skF_4',C_37),k2_relat_1('#skF_4'))
      | ~ r2_hidden(C_37,'#skF_1') ) ),
    inference(negUnitSimplification,[status(thm)],[c_16,c_55])).

tff(c_2,plain,(
    ! [C_4,A_1,B_2] :
      ( r2_hidden(C_4,A_1)
      | ~ r2_hidden(C_4,k2_relat_1(B_2))
      | ~ v5_relat_1(B_2,A_1)
      | ~ v1_relat_1(B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_59,plain,(
    ! [C_37,A_1] :
      ( r2_hidden(k1_funct_1('#skF_4',C_37),A_1)
      | ~ v5_relat_1('#skF_4',A_1)
      | ~ v1_relat_1('#skF_4')
      | ~ r2_hidden(C_37,'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_57,c_2])).

tff(c_63,plain,(
    ! [C_38,A_39] :
      ( r2_hidden(k1_funct_1('#skF_4',C_38),A_39)
      | ~ v5_relat_1('#skF_4',A_39)
      | ~ r2_hidden(C_38,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_29,c_59])).

tff(c_14,plain,(
    ~ r2_hidden(k1_funct_1('#skF_4','#skF_3'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_69,plain,
    ( ~ v5_relat_1('#skF_4','#skF_2')
    | ~ r2_hidden('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_63,c_14])).

tff(c_74,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_34,c_69])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n012.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 15:17:22 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.04/1.44  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.04/1.44  
% 2.04/1.44  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.04/1.45  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.04/1.45  
% 2.04/1.45  %Foreground sorts:
% 2.04/1.45  
% 2.04/1.45  
% 2.04/1.45  %Background operators:
% 2.04/1.45  
% 2.04/1.45  
% 2.04/1.45  %Foreground operators:
% 2.04/1.45  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 2.04/1.45  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.04/1.45  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.04/1.45  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.04/1.45  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.04/1.45  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.04/1.45  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.04/1.45  tff('#skF_2', type, '#skF_2': $i).
% 2.04/1.45  tff('#skF_3', type, '#skF_3': $i).
% 2.04/1.45  tff('#skF_1', type, '#skF_1': $i).
% 2.04/1.45  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.04/1.45  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.04/1.45  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.04/1.45  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.04/1.45  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.04/1.45  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.04/1.45  tff('#skF_4', type, '#skF_4': $i).
% 2.04/1.45  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.04/1.45  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.04/1.45  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.04/1.45  
% 2.17/1.47  tff(f_73, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_hidden(C, A) => ((B = k1_xboole_0) | r2_hidden(k1_funct_1(D, C), B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_funct_2)).
% 2.17/1.47  tff(f_44, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.17/1.47  tff(f_38, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.17/1.47  tff(f_48, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 2.17/1.47  tff(f_60, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_hidden(C, A) => ((B = k1_xboole_0) | r2_hidden(k1_funct_1(D, C), k2_relset_1(A, B, D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_funct_2)).
% 2.17/1.47  tff(f_34, axiom, (![A, B]: ((v1_relat_1(B) & v5_relat_1(B, A)) => (![C]: (r2_hidden(C, k2_relat_1(B)) => r2_hidden(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t202_relat_1)).
% 2.17/1.47  tff(c_18, plain, (r2_hidden('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.17/1.47  tff(c_20, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.17/1.47  tff(c_30, plain, (![C_21, B_22, A_23]: (v5_relat_1(C_21, B_22) | ~m1_subset_1(C_21, k1_zfmisc_1(k2_zfmisc_1(A_23, B_22))))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.17/1.47  tff(c_34, plain, (v5_relat_1('#skF_4', '#skF_2')), inference(resolution, [status(thm)], [c_20, c_30])).
% 2.17/1.47  tff(c_25, plain, (![C_18, A_19, B_20]: (v1_relat_1(C_18) | ~m1_subset_1(C_18, k1_zfmisc_1(k2_zfmisc_1(A_19, B_20))))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.17/1.47  tff(c_29, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_20, c_25])).
% 2.17/1.47  tff(c_16, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.17/1.47  tff(c_24, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.17/1.47  tff(c_22, plain, (v1_funct_2('#skF_4', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.17/1.47  tff(c_40, plain, (![A_27, B_28, C_29]: (k2_relset_1(A_27, B_28, C_29)=k2_relat_1(C_29) | ~m1_subset_1(C_29, k1_zfmisc_1(k2_zfmisc_1(A_27, B_28))))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.17/1.47  tff(c_44, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_20, c_40])).
% 2.17/1.47  tff(c_50, plain, (![D_33, C_34, A_35, B_36]: (r2_hidden(k1_funct_1(D_33, C_34), k2_relset_1(A_35, B_36, D_33)) | k1_xboole_0=B_36 | ~r2_hidden(C_34, A_35) | ~m1_subset_1(D_33, k1_zfmisc_1(k2_zfmisc_1(A_35, B_36))) | ~v1_funct_2(D_33, A_35, B_36) | ~v1_funct_1(D_33))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.17/1.47  tff(c_53, plain, (![C_34]: (r2_hidden(k1_funct_1('#skF_4', C_34), k2_relat_1('#skF_4')) | k1_xboole_0='#skF_2' | ~r2_hidden(C_34, '#skF_1') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_4', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_44, c_50])).
% 2.17/1.47  tff(c_55, plain, (![C_34]: (r2_hidden(k1_funct_1('#skF_4', C_34), k2_relat_1('#skF_4')) | k1_xboole_0='#skF_2' | ~r2_hidden(C_34, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_22, c_20, c_53])).
% 2.17/1.47  tff(c_57, plain, (![C_37]: (r2_hidden(k1_funct_1('#skF_4', C_37), k2_relat_1('#skF_4')) | ~r2_hidden(C_37, '#skF_1'))), inference(negUnitSimplification, [status(thm)], [c_16, c_55])).
% 2.17/1.47  tff(c_2, plain, (![C_4, A_1, B_2]: (r2_hidden(C_4, A_1) | ~r2_hidden(C_4, k2_relat_1(B_2)) | ~v5_relat_1(B_2, A_1) | ~v1_relat_1(B_2))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.17/1.47  tff(c_59, plain, (![C_37, A_1]: (r2_hidden(k1_funct_1('#skF_4', C_37), A_1) | ~v5_relat_1('#skF_4', A_1) | ~v1_relat_1('#skF_4') | ~r2_hidden(C_37, '#skF_1'))), inference(resolution, [status(thm)], [c_57, c_2])).
% 2.17/1.47  tff(c_63, plain, (![C_38, A_39]: (r2_hidden(k1_funct_1('#skF_4', C_38), A_39) | ~v5_relat_1('#skF_4', A_39) | ~r2_hidden(C_38, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_29, c_59])).
% 2.17/1.47  tff(c_14, plain, (~r2_hidden(k1_funct_1('#skF_4', '#skF_3'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.17/1.47  tff(c_69, plain, (~v5_relat_1('#skF_4', '#skF_2') | ~r2_hidden('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_63, c_14])).
% 2.17/1.47  tff(c_74, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_18, c_34, c_69])).
% 2.17/1.47  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.17/1.47  
% 2.17/1.47  Inference rules
% 2.17/1.47  ----------------------
% 2.17/1.47  #Ref     : 0
% 2.17/1.47  #Sup     : 10
% 2.17/1.47  #Fact    : 0
% 2.17/1.47  #Define  : 0
% 2.17/1.47  #Split   : 0
% 2.17/1.47  #Chain   : 0
% 2.17/1.47  #Close   : 0
% 2.17/1.47  
% 2.17/1.47  Ordering : KBO
% 2.17/1.47  
% 2.17/1.47  Simplification rules
% 2.17/1.47  ----------------------
% 2.17/1.47  #Subsume      : 0
% 2.17/1.47  #Demod        : 6
% 2.17/1.47  #Tautology    : 2
% 2.17/1.47  #SimpNegUnit  : 1
% 2.17/1.47  #BackRed      : 0
% 2.17/1.47  
% 2.17/1.47  #Partial instantiations: 0
% 2.17/1.47  #Strategies tried      : 1
% 2.17/1.47  
% 2.17/1.47  Timing (in seconds)
% 2.17/1.47  ----------------------
% 2.17/1.47  Preprocessing        : 0.43
% 2.17/1.47  Parsing              : 0.24
% 2.17/1.47  CNF conversion       : 0.03
% 2.17/1.47  Main loop            : 0.15
% 2.17/1.47  Inferencing          : 0.07
% 2.17/1.47  Reduction            : 0.05
% 2.17/1.47  Demodulation         : 0.03
% 2.17/1.47  BG Simplification    : 0.01
% 2.17/1.47  Subsumption          : 0.02
% 2.17/1.47  Abstraction          : 0.01
% 2.17/1.47  MUC search           : 0.00
% 2.17/1.47  Cooper               : 0.00
% 2.17/1.47  Total                : 0.62
% 2.17/1.47  Index Insertion      : 0.00
% 2.17/1.47  Index Deletion       : 0.00
% 2.17/1.47  Index Matching       : 0.00
% 2.17/1.47  BG Taut test         : 0.00
%------------------------------------------------------------------------------
