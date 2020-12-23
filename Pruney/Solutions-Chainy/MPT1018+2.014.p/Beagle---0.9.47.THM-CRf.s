%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:15:47 EST 2020

% Result     : Theorem 1.80s
% Output     : CNFRefutation 2.10s
% Verified   : 
% Statistics : Number of formulae       :   57 ( 160 expanded)
%              Number of leaves         :   27 (  71 expanded)
%              Depth                    :    8
%              Number of atoms          :   89 ( 508 expanded)
%              Number of equality atoms :   35 ( 198 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff(v2_funct_1,type,(
    v2_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_89,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_funct_1(B)
          & v1_funct_2(B,A,A)
          & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
       => ( v2_funct_1(B)
         => ! [C,D] :
              ( ( r2_hidden(C,A)
                & r2_hidden(D,A)
                & k1_funct_1(B,C) = k1_funct_1(B,D) )
             => C = D ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t85_funct_2)).

tff(f_34,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_32,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_53,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_71,axiom,(
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

tff(f_49,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
      <=> ! [B,C] :
            ( ( r2_hidden(B,k1_relat_1(A))
              & r2_hidden(C,k1_relat_1(A))
              & k1_funct_1(A,B) = k1_funct_1(A,C) )
           => B = C ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_funct_1)).

tff(c_30,plain,(
    '#skF_5' != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_34,plain,(
    r2_hidden('#skF_6','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_4,plain,(
    ! [A_4,B_5] : v1_relat_1(k2_zfmisc_1(A_4,B_5)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_40,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_50,plain,(
    ! [B_23,A_24] :
      ( v1_relat_1(B_23)
      | ~ m1_subset_1(B_23,k1_zfmisc_1(A_24))
      | ~ v1_relat_1(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_53,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_3','#skF_3')) ),
    inference(resolution,[status(thm)],[c_40,c_50])).

tff(c_56,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_53])).

tff(c_44,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_38,plain,(
    v2_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_36,plain,(
    r2_hidden('#skF_5','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_42,plain,(
    v1_funct_2('#skF_4','#skF_3','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_60,plain,(
    ! [A_28,B_29,C_30] :
      ( k1_relset_1(A_28,B_29,C_30) = k1_relat_1(C_30)
      | ~ m1_subset_1(C_30,k1_zfmisc_1(k2_zfmisc_1(A_28,B_29))) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_64,plain,(
    k1_relset_1('#skF_3','#skF_3','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_40,c_60])).

tff(c_88,plain,(
    ! [B_42,A_43,C_44] :
      ( k1_xboole_0 = B_42
      | k1_relset_1(A_43,B_42,C_44) = A_43
      | ~ v1_funct_2(C_44,A_43,B_42)
      | ~ m1_subset_1(C_44,k1_zfmisc_1(k2_zfmisc_1(A_43,B_42))) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_91,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relset_1('#skF_3','#skF_3','#skF_4') = '#skF_3'
    | ~ v1_funct_2('#skF_4','#skF_3','#skF_3') ),
    inference(resolution,[status(thm)],[c_40,c_88])).

tff(c_94,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relat_1('#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_64,c_91])).

tff(c_95,plain,(
    k1_relat_1('#skF_4') = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_94])).

tff(c_32,plain,(
    k1_funct_1('#skF_4','#skF_5') = k1_funct_1('#skF_4','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_115,plain,(
    ! [C_45,B_46,A_47] :
      ( C_45 = B_46
      | k1_funct_1(A_47,C_45) != k1_funct_1(A_47,B_46)
      | ~ r2_hidden(C_45,k1_relat_1(A_47))
      | ~ r2_hidden(B_46,k1_relat_1(A_47))
      | ~ v2_funct_1(A_47)
      | ~ v1_funct_1(A_47)
      | ~ v1_relat_1(A_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_123,plain,(
    ! [C_45] :
      ( C_45 = '#skF_5'
      | k1_funct_1('#skF_4',C_45) != k1_funct_1('#skF_4','#skF_6')
      | ~ r2_hidden(C_45,k1_relat_1('#skF_4'))
      | ~ r2_hidden('#skF_5',k1_relat_1('#skF_4'))
      | ~ v2_funct_1('#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_115])).

tff(c_132,plain,(
    ! [C_48] :
      ( C_48 = '#skF_5'
      | k1_funct_1('#skF_4',C_48) != k1_funct_1('#skF_4','#skF_6')
      | ~ r2_hidden(C_48,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_44,c_38,c_36,c_95,c_95,c_123])).

tff(c_135,plain,(
    '#skF_5' = '#skF_6' ),
    inference(resolution,[status(thm)],[c_34,c_132])).

tff(c_142,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_135])).

tff(c_144,plain,(
    k1_relat_1('#skF_4') != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_94])).

tff(c_143,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_94])).

tff(c_26,plain,(
    ! [B_17,C_18] :
      ( k1_relset_1(k1_xboole_0,B_17,C_18) = k1_xboole_0
      | ~ v1_funct_2(C_18,k1_xboole_0,B_17)
      | ~ m1_subset_1(C_18,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_17))) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_164,plain,(
    ! [B_52,C_53] :
      ( k1_relset_1('#skF_3',B_52,C_53) = '#skF_3'
      | ~ v1_funct_2(C_53,'#skF_3',B_52)
      | ~ m1_subset_1(C_53,k1_zfmisc_1(k2_zfmisc_1('#skF_3',B_52))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_143,c_143,c_143,c_143,c_26])).

tff(c_167,plain,
    ( k1_relset_1('#skF_3','#skF_3','#skF_4') = '#skF_3'
    | ~ v1_funct_2('#skF_4','#skF_3','#skF_3') ),
    inference(resolution,[status(thm)],[c_40,c_164])).

tff(c_170,plain,(
    k1_relat_1('#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_64,c_167])).

tff(c_172,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_144,c_170])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:39:23 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.80/1.32  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.80/1.32  
% 1.80/1.32  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.80/1.33  %$ v1_funct_2 > r2_hidden > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_4
% 1.80/1.33  
% 1.80/1.33  %Foreground sorts:
% 1.80/1.33  
% 1.80/1.33  
% 1.80/1.33  %Background operators:
% 1.80/1.33  
% 1.80/1.33  
% 1.80/1.33  %Foreground operators:
% 1.80/1.33  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 1.80/1.33  tff('#skF_2', type, '#skF_2': $i > $i).
% 1.80/1.33  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 1.80/1.33  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.80/1.33  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.80/1.33  tff('#skF_1', type, '#skF_1': $i > $i).
% 1.80/1.33  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.80/1.33  tff('#skF_5', type, '#skF_5': $i).
% 1.80/1.33  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 1.80/1.33  tff('#skF_6', type, '#skF_6': $i).
% 1.80/1.33  tff('#skF_3', type, '#skF_3': $i).
% 1.80/1.33  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 1.80/1.33  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.80/1.33  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 1.80/1.33  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.80/1.33  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.80/1.33  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.80/1.33  tff('#skF_4', type, '#skF_4': $i).
% 1.80/1.33  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.80/1.33  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.80/1.33  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.80/1.33  
% 2.10/1.34  tff(f_89, negated_conjecture, ~(![A, B]: (((v1_funct_1(B) & v1_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (v2_funct_1(B) => (![C, D]: (((r2_hidden(C, A) & r2_hidden(D, A)) & (k1_funct_1(B, C) = k1_funct_1(B, D))) => (C = D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t85_funct_2)).
% 2.10/1.34  tff(f_34, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 2.10/1.34  tff(f_32, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 2.10/1.34  tff(f_53, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.10/1.34  tff(f_71, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 2.10/1.34  tff(f_49, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) <=> (![B, C]: (((r2_hidden(B, k1_relat_1(A)) & r2_hidden(C, k1_relat_1(A))) & (k1_funct_1(A, B) = k1_funct_1(A, C))) => (B = C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_funct_1)).
% 2.10/1.34  tff(c_30, plain, ('#skF_5'!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.10/1.34  tff(c_34, plain, (r2_hidden('#skF_6', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.10/1.34  tff(c_4, plain, (![A_4, B_5]: (v1_relat_1(k2_zfmisc_1(A_4, B_5)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.10/1.34  tff(c_40, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.10/1.34  tff(c_50, plain, (![B_23, A_24]: (v1_relat_1(B_23) | ~m1_subset_1(B_23, k1_zfmisc_1(A_24)) | ~v1_relat_1(A_24))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.10/1.34  tff(c_53, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_3', '#skF_3'))), inference(resolution, [status(thm)], [c_40, c_50])).
% 2.10/1.34  tff(c_56, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_53])).
% 2.10/1.34  tff(c_44, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.10/1.34  tff(c_38, plain, (v2_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.10/1.34  tff(c_36, plain, (r2_hidden('#skF_5', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.10/1.34  tff(c_42, plain, (v1_funct_2('#skF_4', '#skF_3', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.10/1.34  tff(c_60, plain, (![A_28, B_29, C_30]: (k1_relset_1(A_28, B_29, C_30)=k1_relat_1(C_30) | ~m1_subset_1(C_30, k1_zfmisc_1(k2_zfmisc_1(A_28, B_29))))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.10/1.34  tff(c_64, plain, (k1_relset_1('#skF_3', '#skF_3', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_40, c_60])).
% 2.10/1.34  tff(c_88, plain, (![B_42, A_43, C_44]: (k1_xboole_0=B_42 | k1_relset_1(A_43, B_42, C_44)=A_43 | ~v1_funct_2(C_44, A_43, B_42) | ~m1_subset_1(C_44, k1_zfmisc_1(k2_zfmisc_1(A_43, B_42))))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.10/1.34  tff(c_91, plain, (k1_xboole_0='#skF_3' | k1_relset_1('#skF_3', '#skF_3', '#skF_4')='#skF_3' | ~v1_funct_2('#skF_4', '#skF_3', '#skF_3')), inference(resolution, [status(thm)], [c_40, c_88])).
% 2.10/1.34  tff(c_94, plain, (k1_xboole_0='#skF_3' | k1_relat_1('#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_42, c_64, c_91])).
% 2.10/1.34  tff(c_95, plain, (k1_relat_1('#skF_4')='#skF_3'), inference(splitLeft, [status(thm)], [c_94])).
% 2.10/1.34  tff(c_32, plain, (k1_funct_1('#skF_4', '#skF_5')=k1_funct_1('#skF_4', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.10/1.34  tff(c_115, plain, (![C_45, B_46, A_47]: (C_45=B_46 | k1_funct_1(A_47, C_45)!=k1_funct_1(A_47, B_46) | ~r2_hidden(C_45, k1_relat_1(A_47)) | ~r2_hidden(B_46, k1_relat_1(A_47)) | ~v2_funct_1(A_47) | ~v1_funct_1(A_47) | ~v1_relat_1(A_47))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.10/1.34  tff(c_123, plain, (![C_45]: (C_45='#skF_5' | k1_funct_1('#skF_4', C_45)!=k1_funct_1('#skF_4', '#skF_6') | ~r2_hidden(C_45, k1_relat_1('#skF_4')) | ~r2_hidden('#skF_5', k1_relat_1('#skF_4')) | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_32, c_115])).
% 2.10/1.34  tff(c_132, plain, (![C_48]: (C_48='#skF_5' | k1_funct_1('#skF_4', C_48)!=k1_funct_1('#skF_4', '#skF_6') | ~r2_hidden(C_48, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_44, c_38, c_36, c_95, c_95, c_123])).
% 2.10/1.34  tff(c_135, plain, ('#skF_5'='#skF_6'), inference(resolution, [status(thm)], [c_34, c_132])).
% 2.10/1.34  tff(c_142, plain, $false, inference(negUnitSimplification, [status(thm)], [c_30, c_135])).
% 2.10/1.34  tff(c_144, plain, (k1_relat_1('#skF_4')!='#skF_3'), inference(splitRight, [status(thm)], [c_94])).
% 2.10/1.34  tff(c_143, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_94])).
% 2.10/1.34  tff(c_26, plain, (![B_17, C_18]: (k1_relset_1(k1_xboole_0, B_17, C_18)=k1_xboole_0 | ~v1_funct_2(C_18, k1_xboole_0, B_17) | ~m1_subset_1(C_18, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_17))))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.10/1.34  tff(c_164, plain, (![B_52, C_53]: (k1_relset_1('#skF_3', B_52, C_53)='#skF_3' | ~v1_funct_2(C_53, '#skF_3', B_52) | ~m1_subset_1(C_53, k1_zfmisc_1(k2_zfmisc_1('#skF_3', B_52))))), inference(demodulation, [status(thm), theory('equality')], [c_143, c_143, c_143, c_143, c_26])).
% 2.10/1.34  tff(c_167, plain, (k1_relset_1('#skF_3', '#skF_3', '#skF_4')='#skF_3' | ~v1_funct_2('#skF_4', '#skF_3', '#skF_3')), inference(resolution, [status(thm)], [c_40, c_164])).
% 2.10/1.34  tff(c_170, plain, (k1_relat_1('#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_42, c_64, c_167])).
% 2.10/1.34  tff(c_172, plain, $false, inference(negUnitSimplification, [status(thm)], [c_144, c_170])).
% 2.10/1.34  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.10/1.34  
% 2.10/1.34  Inference rules
% 2.10/1.34  ----------------------
% 2.10/1.34  #Ref     : 1
% 2.10/1.34  #Sup     : 26
% 2.10/1.34  #Fact    : 0
% 2.10/1.34  #Define  : 0
% 2.10/1.34  #Split   : 1
% 2.10/1.34  #Chain   : 0
% 2.10/1.34  #Close   : 0
% 2.10/1.34  
% 2.10/1.34  Ordering : KBO
% 2.10/1.34  
% 2.10/1.34  Simplification rules
% 2.10/1.34  ----------------------
% 2.10/1.34  #Subsume      : 0
% 2.10/1.34  #Demod        : 46
% 2.10/1.34  #Tautology    : 19
% 2.10/1.34  #SimpNegUnit  : 2
% 2.10/1.34  #BackRed      : 7
% 2.10/1.34  
% 2.10/1.34  #Partial instantiations: 0
% 2.10/1.34  #Strategies tried      : 1
% 2.10/1.34  
% 2.10/1.34  Timing (in seconds)
% 2.10/1.34  ----------------------
% 2.10/1.34  Preprocessing        : 0.32
% 2.10/1.34  Parsing              : 0.18
% 2.10/1.34  CNF conversion       : 0.02
% 2.10/1.34  Main loop            : 0.17
% 2.10/1.34  Inferencing          : 0.06
% 2.10/1.34  Reduction            : 0.05
% 2.10/1.34  Demodulation         : 0.04
% 2.10/1.34  BG Simplification    : 0.01
% 2.10/1.34  Subsumption          : 0.03
% 2.10/1.34  Abstraction          : 0.01
% 2.10/1.34  MUC search           : 0.00
% 2.10/1.34  Cooper               : 0.00
% 2.10/1.34  Total                : 0.52
% 2.10/1.34  Index Insertion      : 0.00
% 2.10/1.34  Index Deletion       : 0.00
% 2.10/1.34  Index Matching       : 0.00
% 2.10/1.34  BG Taut test         : 0.00
%------------------------------------------------------------------------------
