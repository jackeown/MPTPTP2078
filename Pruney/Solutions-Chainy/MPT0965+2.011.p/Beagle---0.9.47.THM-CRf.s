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
% DateTime   : Thu Dec  3 10:11:01 EST 2020

% Result     : Theorem 1.94s
% Output     : CNFRefutation 1.94s
% Verified   : 
% Statistics : Number of formulae       :   47 (  58 expanded)
%              Number of leaves         :   26 (  34 expanded)
%              Depth                    :    6
%              Number of atoms          :   64 ( 115 expanded)
%              Number of equality atoms :   18 (  26 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > m1_subset_1 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_81,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( r2_hidden(C,A)
         => ( B = k1_xboole_0
            | r2_hidden(k1_funct_1(D,C),B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_funct_2)).

tff(f_50,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_68,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( ( ( B = k1_xboole_0
           => A = k1_xboole_0 )
         => ( v1_funct_2(C,A,B)
          <=> A = k1_relset_1(A,B,C) ) )
        & ( B = k1_xboole_0
         => ( A = k1_xboole_0
            | ( v1_funct_2(C,A,B)
            <=> C = k1_xboole_0 ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).

tff(f_40,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_46,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_36,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A)
        & v1_funct_1(B) )
     => ! [C] :
          ( r2_hidden(C,k1_relat_1(B))
         => r2_hidden(k1_funct_1(B,C),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t172_funct_1)).

tff(c_28,plain,(
    r2_hidden('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_26,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_32,plain,(
    v1_funct_2('#skF_4','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_30,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_51,plain,(
    ! [A_27,B_28,C_29] :
      ( k1_relset_1(A_27,B_28,C_29) = k1_relat_1(C_29)
      | ~ m1_subset_1(C_29,k1_zfmisc_1(k2_zfmisc_1(A_27,B_28))) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_55,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_30,c_51])).

tff(c_77,plain,(
    ! [B_42,A_43,C_44] :
      ( k1_xboole_0 = B_42
      | k1_relset_1(A_43,B_42,C_44) = A_43
      | ~ v1_funct_2(C_44,A_43,B_42)
      | ~ m1_subset_1(C_44,k1_zfmisc_1(k2_zfmisc_1(A_43,B_42))) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_80,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1('#skF_1','#skF_2','#skF_4') = '#skF_1'
    | ~ v1_funct_2('#skF_4','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_30,c_77])).

tff(c_83,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_55,c_80])).

tff(c_84,plain,(
    k1_relat_1('#skF_4') = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_83])).

tff(c_35,plain,(
    ! [C_17,A_18,B_19] :
      ( v1_relat_1(C_17)
      | ~ m1_subset_1(C_17,k1_zfmisc_1(k2_zfmisc_1(A_18,B_19))) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_39,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_30,c_35])).

tff(c_45,plain,(
    ! [C_23,B_24,A_25] :
      ( v5_relat_1(C_23,B_24)
      | ~ m1_subset_1(C_23,k1_zfmisc_1(k2_zfmisc_1(A_25,B_24))) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_49,plain,(
    v5_relat_1('#skF_4','#skF_2') ),
    inference(resolution,[status(thm)],[c_30,c_45])).

tff(c_34,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_63,plain,(
    ! [B_36,C_37,A_38] :
      ( r2_hidden(k1_funct_1(B_36,C_37),A_38)
      | ~ r2_hidden(C_37,k1_relat_1(B_36))
      | ~ v1_funct_1(B_36)
      | ~ v5_relat_1(B_36,A_38)
      | ~ v1_relat_1(B_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_24,plain,(
    ~ r2_hidden(k1_funct_1('#skF_4','#skF_3'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_66,plain,
    ( ~ r2_hidden('#skF_3',k1_relat_1('#skF_4'))
    | ~ v1_funct_1('#skF_4')
    | ~ v5_relat_1('#skF_4','#skF_2')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_63,c_24])).

tff(c_69,plain,(
    ~ r2_hidden('#skF_3',k1_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_39,c_49,c_34,c_66])).

tff(c_85,plain,(
    ~ r2_hidden('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_69])).

tff(c_89,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_85])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:27:16 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.94/1.23  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.94/1.24  
% 1.94/1.24  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.94/1.24  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > m1_subset_1 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 1.94/1.24  
% 1.94/1.24  %Foreground sorts:
% 1.94/1.24  
% 1.94/1.24  
% 1.94/1.24  %Background operators:
% 1.94/1.24  
% 1.94/1.24  
% 1.94/1.24  %Foreground operators:
% 1.94/1.24  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 1.94/1.24  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.94/1.24  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.94/1.24  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.94/1.24  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 1.94/1.24  tff('#skF_2', type, '#skF_2': $i).
% 1.94/1.24  tff('#skF_3', type, '#skF_3': $i).
% 1.94/1.24  tff('#skF_1', type, '#skF_1': $i).
% 1.94/1.24  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 1.94/1.24  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 1.94/1.24  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.94/1.24  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 1.94/1.24  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.94/1.24  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.94/1.24  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.94/1.24  tff('#skF_4', type, '#skF_4': $i).
% 1.94/1.24  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.94/1.24  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 1.94/1.24  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.94/1.24  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.94/1.24  
% 1.94/1.25  tff(f_81, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_hidden(C, A) => ((B = k1_xboole_0) | r2_hidden(k1_funct_1(D, C), B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_funct_2)).
% 1.94/1.25  tff(f_50, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 1.94/1.25  tff(f_68, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 1.94/1.25  tff(f_40, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 1.94/1.25  tff(f_46, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 1.94/1.25  tff(f_36, axiom, (![A, B]: (((v1_relat_1(B) & v5_relat_1(B, A)) & v1_funct_1(B)) => (![C]: (r2_hidden(C, k1_relat_1(B)) => r2_hidden(k1_funct_1(B, C), A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t172_funct_1)).
% 1.94/1.25  tff(c_28, plain, (r2_hidden('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_81])).
% 1.94/1.25  tff(c_26, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_81])).
% 1.94/1.25  tff(c_32, plain, (v1_funct_2('#skF_4', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_81])).
% 1.94/1.25  tff(c_30, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_81])).
% 1.94/1.25  tff(c_51, plain, (![A_27, B_28, C_29]: (k1_relset_1(A_27, B_28, C_29)=k1_relat_1(C_29) | ~m1_subset_1(C_29, k1_zfmisc_1(k2_zfmisc_1(A_27, B_28))))), inference(cnfTransformation, [status(thm)], [f_50])).
% 1.94/1.25  tff(c_55, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_30, c_51])).
% 1.94/1.25  tff(c_77, plain, (![B_42, A_43, C_44]: (k1_xboole_0=B_42 | k1_relset_1(A_43, B_42, C_44)=A_43 | ~v1_funct_2(C_44, A_43, B_42) | ~m1_subset_1(C_44, k1_zfmisc_1(k2_zfmisc_1(A_43, B_42))))), inference(cnfTransformation, [status(thm)], [f_68])).
% 1.94/1.25  tff(c_80, plain, (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', '#skF_4')='#skF_1' | ~v1_funct_2('#skF_4', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_30, c_77])).
% 1.94/1.25  tff(c_83, plain, (k1_xboole_0='#skF_2' | k1_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_32, c_55, c_80])).
% 1.94/1.25  tff(c_84, plain, (k1_relat_1('#skF_4')='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_26, c_83])).
% 1.94/1.25  tff(c_35, plain, (![C_17, A_18, B_19]: (v1_relat_1(C_17) | ~m1_subset_1(C_17, k1_zfmisc_1(k2_zfmisc_1(A_18, B_19))))), inference(cnfTransformation, [status(thm)], [f_40])).
% 1.94/1.25  tff(c_39, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_30, c_35])).
% 1.94/1.25  tff(c_45, plain, (![C_23, B_24, A_25]: (v5_relat_1(C_23, B_24) | ~m1_subset_1(C_23, k1_zfmisc_1(k2_zfmisc_1(A_25, B_24))))), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.94/1.25  tff(c_49, plain, (v5_relat_1('#skF_4', '#skF_2')), inference(resolution, [status(thm)], [c_30, c_45])).
% 1.94/1.25  tff(c_34, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_81])).
% 1.94/1.25  tff(c_63, plain, (![B_36, C_37, A_38]: (r2_hidden(k1_funct_1(B_36, C_37), A_38) | ~r2_hidden(C_37, k1_relat_1(B_36)) | ~v1_funct_1(B_36) | ~v5_relat_1(B_36, A_38) | ~v1_relat_1(B_36))), inference(cnfTransformation, [status(thm)], [f_36])).
% 1.94/1.25  tff(c_24, plain, (~r2_hidden(k1_funct_1('#skF_4', '#skF_3'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_81])).
% 1.94/1.25  tff(c_66, plain, (~r2_hidden('#skF_3', k1_relat_1('#skF_4')) | ~v1_funct_1('#skF_4') | ~v5_relat_1('#skF_4', '#skF_2') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_63, c_24])).
% 1.94/1.25  tff(c_69, plain, (~r2_hidden('#skF_3', k1_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_39, c_49, c_34, c_66])).
% 1.94/1.25  tff(c_85, plain, (~r2_hidden('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_84, c_69])).
% 1.94/1.25  tff(c_89, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_28, c_85])).
% 1.94/1.25  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.94/1.25  
% 1.94/1.25  Inference rules
% 1.94/1.25  ----------------------
% 1.94/1.25  #Ref     : 0
% 1.94/1.25  #Sup     : 9
% 1.94/1.25  #Fact    : 0
% 1.94/1.25  #Define  : 0
% 1.94/1.25  #Split   : 0
% 1.94/1.25  #Chain   : 0
% 1.94/1.25  #Close   : 0
% 1.94/1.25  
% 1.94/1.25  Ordering : KBO
% 1.94/1.25  
% 1.94/1.25  Simplification rules
% 1.94/1.25  ----------------------
% 1.94/1.25  #Subsume      : 0
% 1.94/1.25  #Demod        : 10
% 1.94/1.25  #Tautology    : 3
% 1.94/1.25  #SimpNegUnit  : 2
% 1.94/1.25  #BackRed      : 2
% 1.94/1.25  
% 1.94/1.25  #Partial instantiations: 0
% 1.94/1.25  #Strategies tried      : 1
% 1.94/1.25  
% 1.94/1.25  Timing (in seconds)
% 1.94/1.25  ----------------------
% 1.94/1.25  Preprocessing        : 0.32
% 1.94/1.25  Parsing              : 0.17
% 1.94/1.25  CNF conversion       : 0.02
% 1.94/1.25  Main loop            : 0.12
% 1.94/1.25  Inferencing          : 0.04
% 1.94/1.25  Reduction            : 0.04
% 1.94/1.25  Demodulation         : 0.03
% 1.94/1.26  BG Simplification    : 0.01
% 1.94/1.26  Subsumption          : 0.02
% 1.94/1.26  Abstraction          : 0.00
% 1.94/1.26  MUC search           : 0.00
% 1.94/1.26  Cooper               : 0.00
% 1.94/1.26  Total                : 0.47
% 1.94/1.26  Index Insertion      : 0.00
% 1.94/1.26  Index Deletion       : 0.00
% 1.94/1.26  Index Matching       : 0.00
% 1.94/1.26  BG Taut test         : 0.00
%------------------------------------------------------------------------------
