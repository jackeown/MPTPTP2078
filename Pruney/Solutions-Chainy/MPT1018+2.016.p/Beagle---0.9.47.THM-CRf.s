%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:15:47 EST 2020

% Result     : Theorem 1.87s
% Output     : CNFRefutation 1.87s
% Verified   : 
% Statistics : Number of formulae       :   48 (  76 expanded)
%              Number of leaves         :   26 (  42 expanded)
%              Depth                    :    6
%              Number of atoms          :   70 ( 206 expanded)
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

tff(f_79,negated_conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t85_funct_2)).

tff(f_34,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_32,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_53,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_61,axiom,(
    ! [A,B] :
      ( ( v1_funct_1(B)
        & v1_funct_2(B,A,A)
        & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
     => k1_relset_1(A,A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_funct_2)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_funct_1)).

tff(c_20,plain,(
    '#skF_5' != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_24,plain,(
    r2_hidden('#skF_6','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_4,plain,(
    ! [A_4,B_5] : v1_relat_1(k2_zfmisc_1(A_4,B_5)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_30,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_40,plain,(
    ! [B_22,A_23] :
      ( v1_relat_1(B_22)
      | ~ m1_subset_1(B_22,k1_zfmisc_1(A_23))
      | ~ v1_relat_1(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_43,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_3','#skF_3')) ),
    inference(resolution,[status(thm)],[c_30,c_40])).

tff(c_46,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_43])).

tff(c_34,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_28,plain,(
    v2_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_32,plain,(
    v1_funct_2('#skF_4','#skF_3','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_50,plain,(
    ! [A_27,B_28,C_29] :
      ( k1_relset_1(A_27,B_28,C_29) = k1_relat_1(C_29)
      | ~ m1_subset_1(C_29,k1_zfmisc_1(k2_zfmisc_1(A_27,B_28))) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_54,plain,(
    k1_relset_1('#skF_3','#skF_3','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_30,c_50])).

tff(c_68,plain,(
    ! [A_31,B_32] :
      ( k1_relset_1(A_31,A_31,B_32) = A_31
      | ~ m1_subset_1(B_32,k1_zfmisc_1(k2_zfmisc_1(A_31,A_31)))
      | ~ v1_funct_2(B_32,A_31,A_31)
      | ~ v1_funct_1(B_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_71,plain,
    ( k1_relset_1('#skF_3','#skF_3','#skF_4') = '#skF_3'
    | ~ v1_funct_2('#skF_4','#skF_3','#skF_3')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_30,c_68])).

tff(c_74,plain,(
    k1_relat_1('#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_54,c_71])).

tff(c_26,plain,(
    r2_hidden('#skF_5','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_22,plain,(
    k1_funct_1('#skF_4','#skF_5') = k1_funct_1('#skF_4','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_98,plain,(
    ! [C_33,B_34,A_35] :
      ( C_33 = B_34
      | k1_funct_1(A_35,C_33) != k1_funct_1(A_35,B_34)
      | ~ r2_hidden(C_33,k1_relat_1(A_35))
      | ~ r2_hidden(B_34,k1_relat_1(A_35))
      | ~ v2_funct_1(A_35)
      | ~ v1_funct_1(A_35)
      | ~ v1_relat_1(A_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_104,plain,(
    ! [B_34] :
      ( B_34 = '#skF_5'
      | k1_funct_1('#skF_4',B_34) != k1_funct_1('#skF_4','#skF_6')
      | ~ r2_hidden('#skF_5',k1_relat_1('#skF_4'))
      | ~ r2_hidden(B_34,k1_relat_1('#skF_4'))
      | ~ v2_funct_1('#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_98])).

tff(c_111,plain,(
    ! [B_36] :
      ( B_36 = '#skF_5'
      | k1_funct_1('#skF_4',B_36) != k1_funct_1('#skF_4','#skF_6')
      | ~ r2_hidden(B_36,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_34,c_28,c_74,c_26,c_74,c_104])).

tff(c_114,plain,(
    '#skF_5' = '#skF_6' ),
    inference(resolution,[status(thm)],[c_24,c_111])).

tff(c_121,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_20,c_114])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n002.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 20:44:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.87/1.20  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.87/1.21  
% 1.87/1.21  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.87/1.21  %$ v1_funct_2 > r2_hidden > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_4
% 1.87/1.21  
% 1.87/1.21  %Foreground sorts:
% 1.87/1.21  
% 1.87/1.21  
% 1.87/1.21  %Background operators:
% 1.87/1.21  
% 1.87/1.21  
% 1.87/1.21  %Foreground operators:
% 1.87/1.21  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 1.87/1.21  tff('#skF_2', type, '#skF_2': $i > $i).
% 1.87/1.21  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 1.87/1.21  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.87/1.21  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.87/1.21  tff('#skF_1', type, '#skF_1': $i > $i).
% 1.87/1.21  tff('#skF_5', type, '#skF_5': $i).
% 1.87/1.21  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 1.87/1.21  tff('#skF_6', type, '#skF_6': $i).
% 1.87/1.21  tff('#skF_3', type, '#skF_3': $i).
% 1.87/1.21  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 1.87/1.21  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.87/1.21  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 1.87/1.21  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.87/1.21  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.87/1.21  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.87/1.21  tff('#skF_4', type, '#skF_4': $i).
% 1.87/1.21  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.87/1.21  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.87/1.21  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.87/1.21  
% 1.87/1.22  tff(f_79, negated_conjecture, ~(![A, B]: (((v1_funct_1(B) & v1_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (v2_funct_1(B) => (![C, D]: (((r2_hidden(C, A) & r2_hidden(D, A)) & (k1_funct_1(B, C) = k1_funct_1(B, D))) => (C = D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t85_funct_2)).
% 1.87/1.22  tff(f_34, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 1.87/1.22  tff(f_32, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 1.87/1.22  tff(f_53, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 1.87/1.22  tff(f_61, axiom, (![A, B]: (((v1_funct_1(B) & v1_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (k1_relset_1(A, A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t67_funct_2)).
% 1.87/1.22  tff(f_49, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) <=> (![B, C]: (((r2_hidden(B, k1_relat_1(A)) & r2_hidden(C, k1_relat_1(A))) & (k1_funct_1(A, B) = k1_funct_1(A, C))) => (B = C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_funct_1)).
% 1.87/1.22  tff(c_20, plain, ('#skF_5'!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_79])).
% 1.87/1.22  tff(c_24, plain, (r2_hidden('#skF_6', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_79])).
% 1.87/1.22  tff(c_4, plain, (![A_4, B_5]: (v1_relat_1(k2_zfmisc_1(A_4, B_5)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 1.87/1.22  tff(c_30, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_79])).
% 1.87/1.22  tff(c_40, plain, (![B_22, A_23]: (v1_relat_1(B_22) | ~m1_subset_1(B_22, k1_zfmisc_1(A_23)) | ~v1_relat_1(A_23))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.87/1.22  tff(c_43, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_3', '#skF_3'))), inference(resolution, [status(thm)], [c_30, c_40])).
% 1.87/1.22  tff(c_46, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_43])).
% 1.87/1.22  tff(c_34, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_79])).
% 1.87/1.22  tff(c_28, plain, (v2_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_79])).
% 1.87/1.22  tff(c_32, plain, (v1_funct_2('#skF_4', '#skF_3', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_79])).
% 1.87/1.22  tff(c_50, plain, (![A_27, B_28, C_29]: (k1_relset_1(A_27, B_28, C_29)=k1_relat_1(C_29) | ~m1_subset_1(C_29, k1_zfmisc_1(k2_zfmisc_1(A_27, B_28))))), inference(cnfTransformation, [status(thm)], [f_53])).
% 1.87/1.22  tff(c_54, plain, (k1_relset_1('#skF_3', '#skF_3', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_30, c_50])).
% 1.87/1.22  tff(c_68, plain, (![A_31, B_32]: (k1_relset_1(A_31, A_31, B_32)=A_31 | ~m1_subset_1(B_32, k1_zfmisc_1(k2_zfmisc_1(A_31, A_31))) | ~v1_funct_2(B_32, A_31, A_31) | ~v1_funct_1(B_32))), inference(cnfTransformation, [status(thm)], [f_61])).
% 1.87/1.22  tff(c_71, plain, (k1_relset_1('#skF_3', '#skF_3', '#skF_4')='#skF_3' | ~v1_funct_2('#skF_4', '#skF_3', '#skF_3') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_30, c_68])).
% 1.87/1.22  tff(c_74, plain, (k1_relat_1('#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_54, c_71])).
% 1.87/1.22  tff(c_26, plain, (r2_hidden('#skF_5', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_79])).
% 1.87/1.22  tff(c_22, plain, (k1_funct_1('#skF_4', '#skF_5')=k1_funct_1('#skF_4', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_79])).
% 1.87/1.22  tff(c_98, plain, (![C_33, B_34, A_35]: (C_33=B_34 | k1_funct_1(A_35, C_33)!=k1_funct_1(A_35, B_34) | ~r2_hidden(C_33, k1_relat_1(A_35)) | ~r2_hidden(B_34, k1_relat_1(A_35)) | ~v2_funct_1(A_35) | ~v1_funct_1(A_35) | ~v1_relat_1(A_35))), inference(cnfTransformation, [status(thm)], [f_49])).
% 1.87/1.22  tff(c_104, plain, (![B_34]: (B_34='#skF_5' | k1_funct_1('#skF_4', B_34)!=k1_funct_1('#skF_4', '#skF_6') | ~r2_hidden('#skF_5', k1_relat_1('#skF_4')) | ~r2_hidden(B_34, k1_relat_1('#skF_4')) | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_22, c_98])).
% 1.87/1.22  tff(c_111, plain, (![B_36]: (B_36='#skF_5' | k1_funct_1('#skF_4', B_36)!=k1_funct_1('#skF_4', '#skF_6') | ~r2_hidden(B_36, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_34, c_28, c_74, c_26, c_74, c_104])).
% 1.87/1.22  tff(c_114, plain, ('#skF_5'='#skF_6'), inference(resolution, [status(thm)], [c_24, c_111])).
% 1.87/1.22  tff(c_121, plain, $false, inference(negUnitSimplification, [status(thm)], [c_20, c_114])).
% 1.87/1.22  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.87/1.22  
% 1.87/1.22  Inference rules
% 1.87/1.22  ----------------------
% 1.87/1.22  #Ref     : 1
% 1.87/1.22  #Sup     : 21
% 1.87/1.22  #Fact    : 0
% 1.87/1.22  #Define  : 0
% 1.87/1.22  #Split   : 0
% 1.87/1.22  #Chain   : 0
% 1.87/1.22  #Close   : 0
% 1.87/1.22  
% 1.87/1.22  Ordering : KBO
% 1.87/1.22  
% 1.87/1.22  Simplification rules
% 1.87/1.22  ----------------------
% 1.87/1.22  #Subsume      : 0
% 1.87/1.22  #Demod        : 23
% 1.87/1.22  #Tautology    : 15
% 1.87/1.22  #SimpNegUnit  : 1
% 1.87/1.22  #BackRed      : 1
% 1.87/1.22  
% 1.87/1.22  #Partial instantiations: 0
% 1.87/1.22  #Strategies tried      : 1
% 1.87/1.22  
% 1.87/1.22  Timing (in seconds)
% 1.87/1.22  ----------------------
% 1.87/1.22  Preprocessing        : 0.28
% 1.87/1.22  Parsing              : 0.14
% 1.87/1.22  CNF conversion       : 0.02
% 1.87/1.22  Main loop            : 0.14
% 1.87/1.22  Inferencing          : 0.06
% 1.87/1.22  Reduction            : 0.04
% 1.87/1.22  Demodulation         : 0.03
% 1.87/1.22  BG Simplification    : 0.01
% 1.87/1.22  Subsumption          : 0.02
% 1.87/1.22  Abstraction          : 0.01
% 1.87/1.22  MUC search           : 0.00
% 1.87/1.22  Cooper               : 0.00
% 1.87/1.22  Total                : 0.44
% 1.87/1.22  Index Insertion      : 0.00
% 1.87/1.22  Index Deletion       : 0.00
% 1.87/1.22  Index Matching       : 0.00
% 1.87/1.22  BG Taut test         : 0.00
%------------------------------------------------------------------------------
