%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:11:30 EST 2020

% Result     : Theorem 1.90s
% Output     : CNFRefutation 1.90s
% Verified   : 
% Statistics : Number of formulae       :   48 (  63 expanded)
%              Number of leaves         :   30 (  39 expanded)
%              Depth                    :    5
%              Number of atoms          :   57 ( 115 expanded)
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

tff(f_72,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ~ ( r2_hidden(C,k2_relset_1(A,B,D))
            & ! [E] :
                ~ ( r2_hidden(E,A)
                  & k1_funct_1(D,E) = C ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_funct_2)).

tff(f_46,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_42,axiom,(
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

tff(f_50,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_56,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( k7_relset_1(A,B,C,A) = k2_relset_1(A,B,C)
        & k8_relset_1(A,B,C,B) = k1_relset_1(A,B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_relset_1)).

tff(c_38,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_6'))) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_44,plain,(
    ! [C_56,A_57,B_58] :
      ( v1_relat_1(C_56)
      | ~ m1_subset_1(C_56,k1_zfmisc_1(k2_zfmisc_1(A_57,B_58))) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_48,plain,(
    v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_38,c_44])).

tff(c_42,plain,(
    v1_funct_1('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_4,plain,(
    ! [A_1,B_24,D_39] :
      ( k1_funct_1(A_1,'#skF_4'(A_1,B_24,k9_relat_1(A_1,B_24),D_39)) = D_39
      | ~ r2_hidden(D_39,k9_relat_1(A_1,B_24))
      | ~ v1_funct_1(A_1)
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_80,plain,(
    ! [A_70,B_71,D_72] :
      ( r2_hidden('#skF_4'(A_70,B_71,k9_relat_1(A_70,B_71),D_72),B_71)
      | ~ r2_hidden(D_72,k9_relat_1(A_70,B_71))
      | ~ v1_funct_1(A_70)
      | ~ v1_relat_1(A_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_34,plain,(
    ! [E_54] :
      ( k1_funct_1('#skF_8',E_54) != '#skF_7'
      | ~ r2_hidden(E_54,'#skF_5') ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_100,plain,(
    ! [A_82,D_83] :
      ( k1_funct_1('#skF_8','#skF_4'(A_82,'#skF_5',k9_relat_1(A_82,'#skF_5'),D_83)) != '#skF_7'
      | ~ r2_hidden(D_83,k9_relat_1(A_82,'#skF_5'))
      | ~ v1_funct_1(A_82)
      | ~ v1_relat_1(A_82) ) ),
    inference(resolution,[status(thm)],[c_80,c_34])).

tff(c_104,plain,(
    ! [D_39] :
      ( D_39 != '#skF_7'
      | ~ r2_hidden(D_39,k9_relat_1('#skF_8','#skF_5'))
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8')
      | ~ r2_hidden(D_39,k9_relat_1('#skF_8','#skF_5'))
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_100])).

tff(c_107,plain,(
    ~ r2_hidden('#skF_7',k9_relat_1('#skF_8','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_42,c_48,c_42,c_104])).

tff(c_49,plain,(
    ! [A_59,B_60,C_61,D_62] :
      ( k7_relset_1(A_59,B_60,C_61,D_62) = k9_relat_1(C_61,D_62)
      | ~ m1_subset_1(C_61,k1_zfmisc_1(k2_zfmisc_1(A_59,B_60))) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_52,plain,(
    ! [D_62] : k7_relset_1('#skF_5','#skF_6','#skF_8',D_62) = k9_relat_1('#skF_8',D_62) ),
    inference(resolution,[status(thm)],[c_38,c_49])).

tff(c_70,plain,(
    ! [A_67,B_68,C_69] :
      ( k7_relset_1(A_67,B_68,C_69,A_67) = k2_relset_1(A_67,B_68,C_69)
      | ~ m1_subset_1(C_69,k1_zfmisc_1(k2_zfmisc_1(A_67,B_68))) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_72,plain,(
    k7_relset_1('#skF_5','#skF_6','#skF_8','#skF_5') = k2_relset_1('#skF_5','#skF_6','#skF_8') ),
    inference(resolution,[status(thm)],[c_38,c_70])).

tff(c_74,plain,(
    k2_relset_1('#skF_5','#skF_6','#skF_8') = k9_relat_1('#skF_8','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_72])).

tff(c_36,plain,(
    r2_hidden('#skF_7',k2_relset_1('#skF_5','#skF_6','#skF_8')) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_75,plain,(
    r2_hidden('#skF_7',k9_relat_1('#skF_8','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_36])).

tff(c_109,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_107,c_75])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:39:29 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.90/1.17  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.90/1.18  
% 1.90/1.18  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.90/1.18  %$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_relat_1 > v1_funct_1 > k8_relset_1 > k7_relset_1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_8 > #skF_3
% 1.90/1.18  
% 1.90/1.18  %Foreground sorts:
% 1.90/1.18  
% 1.90/1.18  
% 1.90/1.18  %Background operators:
% 1.90/1.18  
% 1.90/1.18  
% 1.90/1.18  %Foreground operators:
% 1.90/1.18  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 1.90/1.18  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 1.90/1.18  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 1.90/1.18  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.90/1.18  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.90/1.18  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 1.90/1.18  tff('#skF_7', type, '#skF_7': $i).
% 1.90/1.18  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 1.90/1.18  tff('#skF_5', type, '#skF_5': $i).
% 1.90/1.18  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 1.90/1.18  tff('#skF_6', type, '#skF_6': $i).
% 1.90/1.18  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 1.90/1.18  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 1.90/1.18  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 1.90/1.18  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.90/1.18  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 1.90/1.18  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i) > $i).
% 1.90/1.18  tff('#skF_8', type, '#skF_8': $i).
% 1.90/1.18  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.90/1.18  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.90/1.18  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.90/1.18  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 1.90/1.18  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.90/1.18  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.90/1.18  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.90/1.18  
% 1.90/1.19  tff(f_72, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ~(r2_hidden(C, k2_relset_1(A, B, D)) & (![E]: ~(r2_hidden(E, A) & (k1_funct_1(D, E) = C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_funct_2)).
% 1.90/1.19  tff(f_46, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 1.90/1.19  tff(f_42, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B, C]: ((C = k9_relat_1(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (?[E]: ((r2_hidden(E, k1_relat_1(A)) & r2_hidden(E, B)) & (D = k1_funct_1(A, E)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d12_funct_1)).
% 1.90/1.19  tff(f_50, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 1.90/1.19  tff(f_56, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((k7_relset_1(A, B, C, A) = k2_relset_1(A, B, C)) & (k8_relset_1(A, B, C, B) = k1_relset_1(A, B, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_relset_1)).
% 1.90/1.19  tff(c_38, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_6')))), inference(cnfTransformation, [status(thm)], [f_72])).
% 1.90/1.19  tff(c_44, plain, (![C_56, A_57, B_58]: (v1_relat_1(C_56) | ~m1_subset_1(C_56, k1_zfmisc_1(k2_zfmisc_1(A_57, B_58))))), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.90/1.19  tff(c_48, plain, (v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_38, c_44])).
% 1.90/1.19  tff(c_42, plain, (v1_funct_1('#skF_8')), inference(cnfTransformation, [status(thm)], [f_72])).
% 1.90/1.19  tff(c_4, plain, (![A_1, B_24, D_39]: (k1_funct_1(A_1, '#skF_4'(A_1, B_24, k9_relat_1(A_1, B_24), D_39))=D_39 | ~r2_hidden(D_39, k9_relat_1(A_1, B_24)) | ~v1_funct_1(A_1) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.90/1.19  tff(c_80, plain, (![A_70, B_71, D_72]: (r2_hidden('#skF_4'(A_70, B_71, k9_relat_1(A_70, B_71), D_72), B_71) | ~r2_hidden(D_72, k9_relat_1(A_70, B_71)) | ~v1_funct_1(A_70) | ~v1_relat_1(A_70))), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.90/1.19  tff(c_34, plain, (![E_54]: (k1_funct_1('#skF_8', E_54)!='#skF_7' | ~r2_hidden(E_54, '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_72])).
% 1.90/1.19  tff(c_100, plain, (![A_82, D_83]: (k1_funct_1('#skF_8', '#skF_4'(A_82, '#skF_5', k9_relat_1(A_82, '#skF_5'), D_83))!='#skF_7' | ~r2_hidden(D_83, k9_relat_1(A_82, '#skF_5')) | ~v1_funct_1(A_82) | ~v1_relat_1(A_82))), inference(resolution, [status(thm)], [c_80, c_34])).
% 1.90/1.19  tff(c_104, plain, (![D_39]: (D_39!='#skF_7' | ~r2_hidden(D_39, k9_relat_1('#skF_8', '#skF_5')) | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8') | ~r2_hidden(D_39, k9_relat_1('#skF_8', '#skF_5')) | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_4, c_100])).
% 1.90/1.19  tff(c_107, plain, (~r2_hidden('#skF_7', k9_relat_1('#skF_8', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_42, c_48, c_42, c_104])).
% 1.90/1.19  tff(c_49, plain, (![A_59, B_60, C_61, D_62]: (k7_relset_1(A_59, B_60, C_61, D_62)=k9_relat_1(C_61, D_62) | ~m1_subset_1(C_61, k1_zfmisc_1(k2_zfmisc_1(A_59, B_60))))), inference(cnfTransformation, [status(thm)], [f_50])).
% 1.90/1.19  tff(c_52, plain, (![D_62]: (k7_relset_1('#skF_5', '#skF_6', '#skF_8', D_62)=k9_relat_1('#skF_8', D_62))), inference(resolution, [status(thm)], [c_38, c_49])).
% 1.90/1.19  tff(c_70, plain, (![A_67, B_68, C_69]: (k7_relset_1(A_67, B_68, C_69, A_67)=k2_relset_1(A_67, B_68, C_69) | ~m1_subset_1(C_69, k1_zfmisc_1(k2_zfmisc_1(A_67, B_68))))), inference(cnfTransformation, [status(thm)], [f_56])).
% 1.90/1.19  tff(c_72, plain, (k7_relset_1('#skF_5', '#skF_6', '#skF_8', '#skF_5')=k2_relset_1('#skF_5', '#skF_6', '#skF_8')), inference(resolution, [status(thm)], [c_38, c_70])).
% 1.90/1.19  tff(c_74, plain, (k2_relset_1('#skF_5', '#skF_6', '#skF_8')=k9_relat_1('#skF_8', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_72])).
% 1.90/1.19  tff(c_36, plain, (r2_hidden('#skF_7', k2_relset_1('#skF_5', '#skF_6', '#skF_8'))), inference(cnfTransformation, [status(thm)], [f_72])).
% 1.90/1.19  tff(c_75, plain, (r2_hidden('#skF_7', k9_relat_1('#skF_8', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_36])).
% 1.90/1.19  tff(c_109, plain, $false, inference(negUnitSimplification, [status(thm)], [c_107, c_75])).
% 1.90/1.19  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.90/1.19  
% 1.90/1.19  Inference rules
% 1.90/1.19  ----------------------
% 1.90/1.19  #Ref     : 0
% 1.90/1.19  #Sup     : 15
% 1.90/1.19  #Fact    : 0
% 1.90/1.19  #Define  : 0
% 1.90/1.19  #Split   : 0
% 1.90/1.19  #Chain   : 0
% 1.90/1.19  #Close   : 0
% 1.90/1.19  
% 1.90/1.19  Ordering : KBO
% 1.90/1.19  
% 1.90/1.19  Simplification rules
% 1.90/1.19  ----------------------
% 1.90/1.19  #Subsume      : 0
% 1.90/1.19  #Demod        : 6
% 1.90/1.19  #Tautology    : 8
% 1.90/1.19  #SimpNegUnit  : 1
% 1.90/1.19  #BackRed      : 2
% 1.90/1.19  
% 1.90/1.19  #Partial instantiations: 0
% 1.90/1.19  #Strategies tried      : 1
% 1.90/1.19  
% 1.90/1.19  Timing (in seconds)
% 1.90/1.19  ----------------------
% 1.90/1.19  Preprocessing        : 0.31
% 1.90/1.19  Parsing              : 0.16
% 1.90/1.19  CNF conversion       : 0.03
% 1.90/1.19  Main loop            : 0.13
% 1.90/1.19  Inferencing          : 0.04
% 1.90/1.19  Reduction            : 0.04
% 1.90/1.19  Demodulation         : 0.03
% 1.90/1.19  BG Simplification    : 0.01
% 1.90/1.19  Subsumption          : 0.02
% 1.90/1.19  Abstraction          : 0.01
% 1.90/1.19  MUC search           : 0.00
% 1.90/1.19  Cooper               : 0.00
% 1.90/1.19  Total                : 0.46
% 1.90/1.19  Index Insertion      : 0.00
% 1.90/1.19  Index Deletion       : 0.00
% 1.90/1.19  Index Matching       : 0.00
% 1.90/1.19  BG Taut test         : 0.00
%------------------------------------------------------------------------------
