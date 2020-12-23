%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:15:46 EST 2020

% Result     : Theorem 1.98s
% Output     : CNFRefutation 1.98s
% Verified   : 
% Statistics : Number of formulae       :   45 (  73 expanded)
%              Number of leaves         :   25 (  41 expanded)
%              Depth                    :    6
%              Number of atoms          :   64 ( 200 expanded)
%              Number of equality atoms :   20 (  55 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_4

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

tff(f_74,negated_conjecture,(
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

tff(f_44,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_48,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_56,axiom,(
    ! [A,B] :
      ( ( v1_funct_1(B)
        & v1_funct_2(B,A,A)
        & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
     => k1_relset_1(A,A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_funct_2)).

tff(f_40,axiom,(
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

tff(c_18,plain,(
    '#skF_5' != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_22,plain,(
    r2_hidden('#skF_6','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_28,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_37,plain,(
    ! [C_18,A_19,B_20] :
      ( v1_relat_1(C_18)
      | ~ m1_subset_1(C_18,k1_zfmisc_1(k2_zfmisc_1(A_19,B_20))) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_41,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_28,c_37])).

tff(c_32,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_26,plain,(
    v2_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_30,plain,(
    v1_funct_2('#skF_4','#skF_3','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_45,plain,(
    ! [A_24,B_25,C_26] :
      ( k1_relset_1(A_24,B_25,C_26) = k1_relat_1(C_26)
      | ~ m1_subset_1(C_26,k1_zfmisc_1(k2_zfmisc_1(A_24,B_25))) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_49,plain,(
    k1_relset_1('#skF_3','#skF_3','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_28,c_45])).

tff(c_63,plain,(
    ! [A_28,B_29] :
      ( k1_relset_1(A_28,A_28,B_29) = A_28
      | ~ m1_subset_1(B_29,k1_zfmisc_1(k2_zfmisc_1(A_28,A_28)))
      | ~ v1_funct_2(B_29,A_28,A_28)
      | ~ v1_funct_1(B_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_66,plain,
    ( k1_relset_1('#skF_3','#skF_3','#skF_4') = '#skF_3'
    | ~ v1_funct_2('#skF_4','#skF_3','#skF_3')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_28,c_63])).

tff(c_69,plain,(
    k1_relat_1('#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_49,c_66])).

tff(c_24,plain,(
    r2_hidden('#skF_5','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_20,plain,(
    k1_funct_1('#skF_4','#skF_5') = k1_funct_1('#skF_4','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_93,plain,(
    ! [C_30,B_31,A_32] :
      ( C_30 = B_31
      | k1_funct_1(A_32,C_30) != k1_funct_1(A_32,B_31)
      | ~ r2_hidden(C_30,k1_relat_1(A_32))
      | ~ r2_hidden(B_31,k1_relat_1(A_32))
      | ~ v2_funct_1(A_32)
      | ~ v1_funct_1(A_32)
      | ~ v1_relat_1(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_99,plain,(
    ! [B_31] :
      ( B_31 = '#skF_5'
      | k1_funct_1('#skF_4',B_31) != k1_funct_1('#skF_4','#skF_6')
      | ~ r2_hidden('#skF_5',k1_relat_1('#skF_4'))
      | ~ r2_hidden(B_31,k1_relat_1('#skF_4'))
      | ~ v2_funct_1('#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_93])).

tff(c_106,plain,(
    ! [B_33] :
      ( B_33 = '#skF_5'
      | k1_funct_1('#skF_4',B_33) != k1_funct_1('#skF_4','#skF_6')
      | ~ r2_hidden(B_33,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_41,c_32,c_26,c_69,c_24,c_69,c_99])).

tff(c_109,plain,(
    '#skF_5' = '#skF_6' ),
    inference(resolution,[status(thm)],[c_22,c_106])).

tff(c_116,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_18,c_109])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n001.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 18:09:30 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.98/1.24  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.98/1.24  
% 1.98/1.24  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.98/1.24  %$ v1_funct_2 > r2_hidden > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_4
% 1.98/1.24  
% 1.98/1.24  %Foreground sorts:
% 1.98/1.24  
% 1.98/1.24  
% 1.98/1.24  %Background operators:
% 1.98/1.24  
% 1.98/1.24  
% 1.98/1.24  %Foreground operators:
% 1.98/1.24  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 1.98/1.24  tff('#skF_2', type, '#skF_2': $i > $i).
% 1.98/1.24  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 1.98/1.24  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.98/1.24  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.98/1.24  tff('#skF_1', type, '#skF_1': $i > $i).
% 1.98/1.24  tff('#skF_5', type, '#skF_5': $i).
% 1.98/1.24  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 1.98/1.24  tff('#skF_6', type, '#skF_6': $i).
% 1.98/1.24  tff('#skF_3', type, '#skF_3': $i).
% 1.98/1.24  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 1.98/1.24  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.98/1.24  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 1.98/1.24  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.98/1.24  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.98/1.24  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.98/1.24  tff('#skF_4', type, '#skF_4': $i).
% 1.98/1.24  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.98/1.24  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.98/1.24  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.98/1.24  
% 1.98/1.25  tff(f_74, negated_conjecture, ~(![A, B]: (((v1_funct_1(B) & v1_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (v2_funct_1(B) => (![C, D]: (((r2_hidden(C, A) & r2_hidden(D, A)) & (k1_funct_1(B, C) = k1_funct_1(B, D))) => (C = D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t85_funct_2)).
% 1.98/1.25  tff(f_44, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 1.98/1.25  tff(f_48, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 1.98/1.25  tff(f_56, axiom, (![A, B]: (((v1_funct_1(B) & v1_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (k1_relset_1(A, A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t67_funct_2)).
% 1.98/1.25  tff(f_40, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) <=> (![B, C]: (((r2_hidden(B, k1_relat_1(A)) & r2_hidden(C, k1_relat_1(A))) & (k1_funct_1(A, B) = k1_funct_1(A, C))) => (B = C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_funct_1)).
% 1.98/1.25  tff(c_18, plain, ('#skF_5'!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_74])).
% 1.98/1.25  tff(c_22, plain, (r2_hidden('#skF_6', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_74])).
% 1.98/1.25  tff(c_28, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_74])).
% 1.98/1.25  tff(c_37, plain, (![C_18, A_19, B_20]: (v1_relat_1(C_18) | ~m1_subset_1(C_18, k1_zfmisc_1(k2_zfmisc_1(A_19, B_20))))), inference(cnfTransformation, [status(thm)], [f_44])).
% 1.98/1.25  tff(c_41, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_28, c_37])).
% 1.98/1.25  tff(c_32, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_74])).
% 1.98/1.25  tff(c_26, plain, (v2_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_74])).
% 1.98/1.25  tff(c_30, plain, (v1_funct_2('#skF_4', '#skF_3', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_74])).
% 1.98/1.25  tff(c_45, plain, (![A_24, B_25, C_26]: (k1_relset_1(A_24, B_25, C_26)=k1_relat_1(C_26) | ~m1_subset_1(C_26, k1_zfmisc_1(k2_zfmisc_1(A_24, B_25))))), inference(cnfTransformation, [status(thm)], [f_48])).
% 1.98/1.25  tff(c_49, plain, (k1_relset_1('#skF_3', '#skF_3', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_28, c_45])).
% 1.98/1.25  tff(c_63, plain, (![A_28, B_29]: (k1_relset_1(A_28, A_28, B_29)=A_28 | ~m1_subset_1(B_29, k1_zfmisc_1(k2_zfmisc_1(A_28, A_28))) | ~v1_funct_2(B_29, A_28, A_28) | ~v1_funct_1(B_29))), inference(cnfTransformation, [status(thm)], [f_56])).
% 1.98/1.25  tff(c_66, plain, (k1_relset_1('#skF_3', '#skF_3', '#skF_4')='#skF_3' | ~v1_funct_2('#skF_4', '#skF_3', '#skF_3') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_28, c_63])).
% 1.98/1.25  tff(c_69, plain, (k1_relat_1('#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_49, c_66])).
% 1.98/1.25  tff(c_24, plain, (r2_hidden('#skF_5', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_74])).
% 1.98/1.25  tff(c_20, plain, (k1_funct_1('#skF_4', '#skF_5')=k1_funct_1('#skF_4', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_74])).
% 1.98/1.25  tff(c_93, plain, (![C_30, B_31, A_32]: (C_30=B_31 | k1_funct_1(A_32, C_30)!=k1_funct_1(A_32, B_31) | ~r2_hidden(C_30, k1_relat_1(A_32)) | ~r2_hidden(B_31, k1_relat_1(A_32)) | ~v2_funct_1(A_32) | ~v1_funct_1(A_32) | ~v1_relat_1(A_32))), inference(cnfTransformation, [status(thm)], [f_40])).
% 1.98/1.25  tff(c_99, plain, (![B_31]: (B_31='#skF_5' | k1_funct_1('#skF_4', B_31)!=k1_funct_1('#skF_4', '#skF_6') | ~r2_hidden('#skF_5', k1_relat_1('#skF_4')) | ~r2_hidden(B_31, k1_relat_1('#skF_4')) | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_20, c_93])).
% 1.98/1.25  tff(c_106, plain, (![B_33]: (B_33='#skF_5' | k1_funct_1('#skF_4', B_33)!=k1_funct_1('#skF_4', '#skF_6') | ~r2_hidden(B_33, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_41, c_32, c_26, c_69, c_24, c_69, c_99])).
% 1.98/1.25  tff(c_109, plain, ('#skF_5'='#skF_6'), inference(resolution, [status(thm)], [c_22, c_106])).
% 1.98/1.25  tff(c_116, plain, $false, inference(negUnitSimplification, [status(thm)], [c_18, c_109])).
% 1.98/1.25  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.98/1.25  
% 1.98/1.25  Inference rules
% 1.98/1.25  ----------------------
% 1.98/1.25  #Ref     : 1
% 1.98/1.25  #Sup     : 21
% 1.98/1.25  #Fact    : 0
% 1.98/1.25  #Define  : 0
% 1.98/1.25  #Split   : 0
% 1.98/1.25  #Chain   : 0
% 1.98/1.25  #Close   : 0
% 1.98/1.25  
% 1.98/1.25  Ordering : KBO
% 1.98/1.25  
% 1.98/1.25  Simplification rules
% 1.98/1.25  ----------------------
% 1.98/1.25  #Subsume      : 0
% 1.98/1.25  #Demod        : 22
% 1.98/1.25  #Tautology    : 15
% 1.98/1.25  #SimpNegUnit  : 1
% 1.98/1.25  #BackRed      : 1
% 1.98/1.25  
% 1.98/1.25  #Partial instantiations: 0
% 1.98/1.25  #Strategies tried      : 1
% 1.98/1.25  
% 1.98/1.25  Timing (in seconds)
% 1.98/1.25  ----------------------
% 1.98/1.26  Preprocessing        : 0.33
% 1.98/1.26  Parsing              : 0.17
% 1.98/1.26  CNF conversion       : 0.02
% 1.98/1.26  Main loop            : 0.14
% 1.98/1.26  Inferencing          : 0.06
% 1.98/1.26  Reduction            : 0.04
% 1.98/1.26  Demodulation         : 0.03
% 1.98/1.26  BG Simplification    : 0.01
% 1.98/1.26  Subsumption          : 0.02
% 1.98/1.26  Abstraction          : 0.01
% 1.98/1.26  MUC search           : 0.00
% 1.98/1.26  Cooper               : 0.00
% 1.98/1.26  Total                : 0.49
% 1.98/1.26  Index Insertion      : 0.00
% 1.98/1.26  Index Deletion       : 0.00
% 1.98/1.26  Index Matching       : 0.00
% 1.98/1.26  BG Taut test         : 0.00
%------------------------------------------------------------------------------
