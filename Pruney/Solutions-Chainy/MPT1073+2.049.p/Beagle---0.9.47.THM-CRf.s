%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:18:04 EST 2020

% Result     : Theorem 2.13s
% Output     : CNFRefutation 2.32s
% Verified   : 
% Statistics : Number of formulae       :   54 (  72 expanded)
%              Number of leaves         :   32 (  42 expanded)
%              Depth                    :    6
%              Number of atoms          :   71 ( 135 expanded)
%              Number of equality atoms :   15 (  24 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_relat_1 > v1_funct_1 > k8_relset_1 > k7_relset_1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_8 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k8_relset_1,type,(
    k8_relset_1: ( $i * $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(k7_relset_1,type,(
    k7_relset_1: ( $i * $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_38,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_81,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,B,C)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,C))) )
       => ~ ( r2_hidden(A,k2_relset_1(B,C,D))
            & ! [E] :
                ( m1_subset_1(E,B)
               => A != k1_funct_1(D,E) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t190_funct_2)).

tff(f_36,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_55,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B,C] :
          ( C = k9_relat_1(A,B)
        <=> ! [D] :
              ( r2_hidden(D,C)
            <=> ? [E] :
                  ( r2_hidden(E,k1_relat_1(A))
                  & r2_hidden(E,B)
                  & D = k1_funct_1(A,E) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d12_funct_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

tff(f_59,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_65,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( k7_relset_1(A,B,C,A) = k2_relset_1(A,B,C)
        & k8_relset_1(A,B,C,B) = k1_relset_1(A,B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_relset_1)).

tff(c_6,plain,(
    ! [A_6,B_7] : v1_relat_1(k2_zfmisc_1(A_6,B_7)) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_42,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_7'))) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_54,plain,(
    ! [B_64,A_65] :
      ( v1_relat_1(B_64)
      | ~ m1_subset_1(B_64,k1_zfmisc_1(A_65))
      | ~ v1_relat_1(A_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_57,plain,
    ( v1_relat_1('#skF_8')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_6','#skF_7')) ),
    inference(resolution,[status(thm)],[c_42,c_54])).

tff(c_60,plain,(
    v1_relat_1('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_57])).

tff(c_46,plain,(
    v1_funct_1('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_10,plain,(
    ! [A_8,B_31,D_46] :
      ( k1_funct_1(A_8,'#skF_4'(A_8,B_31,k9_relat_1(A_8,B_31),D_46)) = D_46
      | ~ r2_hidden(D_46,k9_relat_1(A_8,B_31))
      | ~ v1_funct_1(A_8)
      | ~ v1_relat_1(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_98,plain,(
    ! [A_77,B_78,D_79] :
      ( r2_hidden('#skF_4'(A_77,B_78,k9_relat_1(A_77,B_78),D_79),B_78)
      | ~ r2_hidden(D_79,k9_relat_1(A_77,B_78))
      | ~ v1_funct_1(A_77)
      | ~ v1_relat_1(A_77) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( m1_subset_1(A_1,B_2)
      | ~ r2_hidden(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_108,plain,(
    ! [A_83,B_84,D_85] :
      ( m1_subset_1('#skF_4'(A_83,B_84,k9_relat_1(A_83,B_84),D_85),B_84)
      | ~ r2_hidden(D_85,k9_relat_1(A_83,B_84))
      | ~ v1_funct_1(A_83)
      | ~ v1_relat_1(A_83) ) ),
    inference(resolution,[status(thm)],[c_98,c_2])).

tff(c_38,plain,(
    ! [E_58] :
      ( k1_funct_1('#skF_8',E_58) != '#skF_5'
      | ~ m1_subset_1(E_58,'#skF_6') ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_162,plain,(
    ! [A_101,D_102] :
      ( k1_funct_1('#skF_8','#skF_4'(A_101,'#skF_6',k9_relat_1(A_101,'#skF_6'),D_102)) != '#skF_5'
      | ~ r2_hidden(D_102,k9_relat_1(A_101,'#skF_6'))
      | ~ v1_funct_1(A_101)
      | ~ v1_relat_1(A_101) ) ),
    inference(resolution,[status(thm)],[c_108,c_38])).

tff(c_166,plain,(
    ! [D_46] :
      ( D_46 != '#skF_5'
      | ~ r2_hidden(D_46,k9_relat_1('#skF_8','#skF_6'))
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8')
      | ~ r2_hidden(D_46,k9_relat_1('#skF_8','#skF_6'))
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_162])).

tff(c_169,plain,(
    ~ r2_hidden('#skF_5',k9_relat_1('#skF_8','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_46,c_60,c_46,c_166])).

tff(c_61,plain,(
    ! [A_66,B_67,C_68,D_69] :
      ( k7_relset_1(A_66,B_67,C_68,D_69) = k9_relat_1(C_68,D_69)
      | ~ m1_subset_1(C_68,k1_zfmisc_1(k2_zfmisc_1(A_66,B_67))) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_64,plain,(
    ! [D_69] : k7_relset_1('#skF_6','#skF_7','#skF_8',D_69) = k9_relat_1('#skF_8',D_69) ),
    inference(resolution,[status(thm)],[c_42,c_61])).

tff(c_74,plain,(
    ! [A_71,B_72,C_73] :
      ( k7_relset_1(A_71,B_72,C_73,A_71) = k2_relset_1(A_71,B_72,C_73)
      | ~ m1_subset_1(C_73,k1_zfmisc_1(k2_zfmisc_1(A_71,B_72))) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_76,plain,(
    k7_relset_1('#skF_6','#skF_7','#skF_8','#skF_6') = k2_relset_1('#skF_6','#skF_7','#skF_8') ),
    inference(resolution,[status(thm)],[c_42,c_74])).

tff(c_78,plain,(
    k2_relset_1('#skF_6','#skF_7','#skF_8') = k9_relat_1('#skF_8','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_76])).

tff(c_40,plain,(
    r2_hidden('#skF_5',k2_relset_1('#skF_6','#skF_7','#skF_8')) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_80,plain,(
    r2_hidden('#skF_5',k9_relat_1('#skF_8','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_40])).

tff(c_171,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_169,c_80])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n008.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 10:45:00 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.13/1.28  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.13/1.28  
% 2.13/1.28  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.13/1.29  %$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_relat_1 > v1_funct_1 > k8_relset_1 > k7_relset_1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_8 > #skF_3
% 2.13/1.29  
% 2.13/1.29  %Foreground sorts:
% 2.13/1.29  
% 2.13/1.29  
% 2.13/1.29  %Background operators:
% 2.13/1.29  
% 2.13/1.29  
% 2.13/1.29  %Foreground operators:
% 2.13/1.29  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 2.13/1.29  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.13/1.29  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.13/1.29  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.13/1.29  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.13/1.29  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 2.13/1.29  tff('#skF_7', type, '#skF_7': $i).
% 2.13/1.29  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 2.13/1.29  tff('#skF_5', type, '#skF_5': $i).
% 2.13/1.29  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.13/1.29  tff('#skF_6', type, '#skF_6': $i).
% 2.13/1.29  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.13/1.29  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.13/1.29  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.13/1.29  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.13/1.29  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.13/1.29  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i) > $i).
% 2.13/1.29  tff('#skF_8', type, '#skF_8': $i).
% 2.13/1.29  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.13/1.29  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.13/1.29  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.13/1.29  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 2.13/1.29  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.13/1.29  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.13/1.29  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.13/1.29  
% 2.32/1.30  tff(f_38, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 2.32/1.30  tff(f_81, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, B, C)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => ~(r2_hidden(A, k2_relset_1(B, C, D)) & (![E]: (m1_subset_1(E, B) => ~(A = k1_funct_1(D, E))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t190_funct_2)).
% 2.32/1.30  tff(f_36, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 2.32/1.30  tff(f_55, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B, C]: ((C = k9_relat_1(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (?[E]: ((r2_hidden(E, k1_relat_1(A)) & r2_hidden(E, B)) & (D = k1_funct_1(A, E)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d12_funct_1)).
% 2.32/1.30  tff(f_29, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_subset)).
% 2.32/1.30  tff(f_59, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 2.32/1.30  tff(f_65, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((k7_relset_1(A, B, C, A) = k2_relset_1(A, B, C)) & (k8_relset_1(A, B, C, B) = k1_relset_1(A, B, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_relset_1)).
% 2.32/1.30  tff(c_6, plain, (![A_6, B_7]: (v1_relat_1(k2_zfmisc_1(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.32/1.30  tff(c_42, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_6', '#skF_7')))), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.32/1.30  tff(c_54, plain, (![B_64, A_65]: (v1_relat_1(B_64) | ~m1_subset_1(B_64, k1_zfmisc_1(A_65)) | ~v1_relat_1(A_65))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.32/1.30  tff(c_57, plain, (v1_relat_1('#skF_8') | ~v1_relat_1(k2_zfmisc_1('#skF_6', '#skF_7'))), inference(resolution, [status(thm)], [c_42, c_54])).
% 2.32/1.30  tff(c_60, plain, (v1_relat_1('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_6, c_57])).
% 2.32/1.30  tff(c_46, plain, (v1_funct_1('#skF_8')), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.32/1.30  tff(c_10, plain, (![A_8, B_31, D_46]: (k1_funct_1(A_8, '#skF_4'(A_8, B_31, k9_relat_1(A_8, B_31), D_46))=D_46 | ~r2_hidden(D_46, k9_relat_1(A_8, B_31)) | ~v1_funct_1(A_8) | ~v1_relat_1(A_8))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.32/1.30  tff(c_98, plain, (![A_77, B_78, D_79]: (r2_hidden('#skF_4'(A_77, B_78, k9_relat_1(A_77, B_78), D_79), B_78) | ~r2_hidden(D_79, k9_relat_1(A_77, B_78)) | ~v1_funct_1(A_77) | ~v1_relat_1(A_77))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.32/1.30  tff(c_2, plain, (![A_1, B_2]: (m1_subset_1(A_1, B_2) | ~r2_hidden(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.32/1.30  tff(c_108, plain, (![A_83, B_84, D_85]: (m1_subset_1('#skF_4'(A_83, B_84, k9_relat_1(A_83, B_84), D_85), B_84) | ~r2_hidden(D_85, k9_relat_1(A_83, B_84)) | ~v1_funct_1(A_83) | ~v1_relat_1(A_83))), inference(resolution, [status(thm)], [c_98, c_2])).
% 2.32/1.30  tff(c_38, plain, (![E_58]: (k1_funct_1('#skF_8', E_58)!='#skF_5' | ~m1_subset_1(E_58, '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.32/1.30  tff(c_162, plain, (![A_101, D_102]: (k1_funct_1('#skF_8', '#skF_4'(A_101, '#skF_6', k9_relat_1(A_101, '#skF_6'), D_102))!='#skF_5' | ~r2_hidden(D_102, k9_relat_1(A_101, '#skF_6')) | ~v1_funct_1(A_101) | ~v1_relat_1(A_101))), inference(resolution, [status(thm)], [c_108, c_38])).
% 2.32/1.30  tff(c_166, plain, (![D_46]: (D_46!='#skF_5' | ~r2_hidden(D_46, k9_relat_1('#skF_8', '#skF_6')) | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8') | ~r2_hidden(D_46, k9_relat_1('#skF_8', '#skF_6')) | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_10, c_162])).
% 2.32/1.30  tff(c_169, plain, (~r2_hidden('#skF_5', k9_relat_1('#skF_8', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_46, c_60, c_46, c_166])).
% 2.32/1.30  tff(c_61, plain, (![A_66, B_67, C_68, D_69]: (k7_relset_1(A_66, B_67, C_68, D_69)=k9_relat_1(C_68, D_69) | ~m1_subset_1(C_68, k1_zfmisc_1(k2_zfmisc_1(A_66, B_67))))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.32/1.30  tff(c_64, plain, (![D_69]: (k7_relset_1('#skF_6', '#skF_7', '#skF_8', D_69)=k9_relat_1('#skF_8', D_69))), inference(resolution, [status(thm)], [c_42, c_61])).
% 2.32/1.30  tff(c_74, plain, (![A_71, B_72, C_73]: (k7_relset_1(A_71, B_72, C_73, A_71)=k2_relset_1(A_71, B_72, C_73) | ~m1_subset_1(C_73, k1_zfmisc_1(k2_zfmisc_1(A_71, B_72))))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.32/1.30  tff(c_76, plain, (k7_relset_1('#skF_6', '#skF_7', '#skF_8', '#skF_6')=k2_relset_1('#skF_6', '#skF_7', '#skF_8')), inference(resolution, [status(thm)], [c_42, c_74])).
% 2.32/1.30  tff(c_78, plain, (k2_relset_1('#skF_6', '#skF_7', '#skF_8')=k9_relat_1('#skF_8', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_76])).
% 2.32/1.30  tff(c_40, plain, (r2_hidden('#skF_5', k2_relset_1('#skF_6', '#skF_7', '#skF_8'))), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.32/1.30  tff(c_80, plain, (r2_hidden('#skF_5', k9_relat_1('#skF_8', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_40])).
% 2.32/1.30  tff(c_171, plain, $false, inference(negUnitSimplification, [status(thm)], [c_169, c_80])).
% 2.32/1.30  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.32/1.30  
% 2.32/1.30  Inference rules
% 2.32/1.30  ----------------------
% 2.32/1.30  #Ref     : 0
% 2.32/1.30  #Sup     : 27
% 2.32/1.30  #Fact    : 0
% 2.32/1.30  #Define  : 0
% 2.32/1.30  #Split   : 0
% 2.32/1.30  #Chain   : 0
% 2.32/1.30  #Close   : 0
% 2.32/1.30  
% 2.32/1.30  Ordering : KBO
% 2.32/1.30  
% 2.32/1.30  Simplification rules
% 2.32/1.30  ----------------------
% 2.32/1.30  #Subsume      : 0
% 2.32/1.30  #Demod        : 9
% 2.32/1.30  #Tautology    : 9
% 2.32/1.30  #SimpNegUnit  : 1
% 2.32/1.30  #BackRed      : 3
% 2.32/1.30  
% 2.32/1.30  #Partial instantiations: 0
% 2.32/1.30  #Strategies tried      : 1
% 2.32/1.30  
% 2.32/1.30  Timing (in seconds)
% 2.32/1.30  ----------------------
% 2.32/1.30  Preprocessing        : 0.34
% 2.32/1.30  Parsing              : 0.17
% 2.32/1.30  CNF conversion       : 0.03
% 2.32/1.30  Main loop            : 0.17
% 2.32/1.30  Inferencing          : 0.07
% 2.32/1.30  Reduction            : 0.05
% 2.32/1.30  Demodulation         : 0.04
% 2.32/1.30  BG Simplification    : 0.02
% 2.32/1.30  Subsumption          : 0.03
% 2.32/1.30  Abstraction          : 0.02
% 2.32/1.30  MUC search           : 0.00
% 2.32/1.30  Cooper               : 0.00
% 2.32/1.30  Total                : 0.54
% 2.32/1.30  Index Insertion      : 0.00
% 2.32/1.30  Index Deletion       : 0.00
% 2.32/1.30  Index Matching       : 0.00
% 2.32/1.30  BG Taut test         : 0.00
%------------------------------------------------------------------------------
