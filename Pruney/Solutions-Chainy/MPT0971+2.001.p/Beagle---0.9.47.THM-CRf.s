%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:11:29 EST 2020

% Result     : Theorem 1.93s
% Output     : CNFRefutation 1.93s
% Verified   : 
% Statistics : Number of formulae       :   56 ( 104 expanded)
%              Number of leaves         :   33 (  54 expanded)
%              Depth                    :    8
%              Number of atoms          :   72 ( 207 expanded)
%              Number of equality atoms :   18 (  40 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k9_relat_1 > k7_relat_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_8 > #skF_3

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

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

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

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

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

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_82,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ~ ( r2_hidden(C,k2_relset_1(A,B,D))
            & ! [E] :
                ~ ( r2_hidden(E,A)
                  & k1_funct_1(D,E) = C ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_funct_2)).

tff(f_56,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_62,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_52,axiom,(
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

tff(f_66,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(c_42,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_6'))) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_48,plain,(
    ! [C_59,A_60,B_61] :
      ( v1_relat_1(C_59)
      | ~ m1_subset_1(C_59,k1_zfmisc_1(k2_zfmisc_1(A_60,B_61))) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_52,plain,(
    v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_42,c_48])).

tff(c_46,plain,(
    v1_funct_1('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_53,plain,(
    ! [C_62,A_63,B_64] :
      ( v4_relat_1(C_62,A_63)
      | ~ m1_subset_1(C_62,k1_zfmisc_1(k2_zfmisc_1(A_63,B_64))) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_57,plain,(
    v4_relat_1('#skF_8','#skF_5') ),
    inference(resolution,[status(thm)],[c_42,c_53])).

tff(c_67,plain,(
    ! [B_67,A_68] :
      ( k7_relat_1(B_67,A_68) = B_67
      | ~ v4_relat_1(B_67,A_68)
      | ~ v1_relat_1(B_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_70,plain,
    ( k7_relat_1('#skF_8','#skF_5') = '#skF_8'
    | ~ v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_57,c_67])).

tff(c_73,plain,(
    k7_relat_1('#skF_8','#skF_5') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_70])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( k2_relat_1(k7_relat_1(B_2,A_1)) = k9_relat_1(B_2,A_1)
      | ~ v1_relat_1(B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_77,plain,
    ( k9_relat_1('#skF_8','#skF_5') = k2_relat_1('#skF_8')
    | ~ v1_relat_1('#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_73,c_2])).

tff(c_81,plain,(
    k9_relat_1('#skF_8','#skF_5') = k2_relat_1('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_77])).

tff(c_139,plain,(
    ! [A_90,B_91,D_92] :
      ( k1_funct_1(A_90,'#skF_4'(A_90,B_91,k9_relat_1(A_90,B_91),D_92)) = D_92
      | ~ r2_hidden(D_92,k9_relat_1(A_90,B_91))
      | ~ v1_funct_1(A_90)
      | ~ v1_relat_1(A_90) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_102,plain,(
    ! [A_75,B_76,D_77] :
      ( r2_hidden('#skF_4'(A_75,B_76,k9_relat_1(A_75,B_76),D_77),B_76)
      | ~ r2_hidden(D_77,k9_relat_1(A_75,B_76))
      | ~ v1_funct_1(A_75)
      | ~ v1_relat_1(A_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_38,plain,(
    ! [E_57] :
      ( k1_funct_1('#skF_8',E_57) != '#skF_7'
      | ~ r2_hidden(E_57,'#skF_5') ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_110,plain,(
    ! [A_75,D_77] :
      ( k1_funct_1('#skF_8','#skF_4'(A_75,'#skF_5',k9_relat_1(A_75,'#skF_5'),D_77)) != '#skF_7'
      | ~ r2_hidden(D_77,k9_relat_1(A_75,'#skF_5'))
      | ~ v1_funct_1(A_75)
      | ~ v1_relat_1(A_75) ) ),
    inference(resolution,[status(thm)],[c_102,c_38])).

tff(c_153,plain,(
    ! [D_92] :
      ( D_92 != '#skF_7'
      | ~ r2_hidden(D_92,k9_relat_1('#skF_8','#skF_5'))
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8')
      | ~ r2_hidden(D_92,k9_relat_1('#skF_8','#skF_5'))
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_139,c_110])).

tff(c_168,plain,(
    ~ r2_hidden('#skF_7',k2_relat_1('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_46,c_81,c_52,c_46,c_81,c_153])).

tff(c_92,plain,(
    ! [A_72,B_73,C_74] :
      ( k2_relset_1(A_72,B_73,C_74) = k2_relat_1(C_74)
      | ~ m1_subset_1(C_74,k1_zfmisc_1(k2_zfmisc_1(A_72,B_73))) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_96,plain,(
    k2_relset_1('#skF_5','#skF_6','#skF_8') = k2_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_42,c_92])).

tff(c_40,plain,(
    r2_hidden('#skF_7',k2_relset_1('#skF_5','#skF_6','#skF_8')) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_97,plain,(
    r2_hidden('#skF_7',k2_relat_1('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_40])).

tff(c_170,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_168,c_97])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n015.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 09:32:38 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.93/1.21  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.93/1.21  
% 1.93/1.21  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.93/1.22  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k9_relat_1 > k7_relat_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_8 > #skF_3
% 1.93/1.22  
% 1.93/1.22  %Foreground sorts:
% 1.93/1.22  
% 1.93/1.22  
% 1.93/1.22  %Background operators:
% 1.93/1.22  
% 1.93/1.22  
% 1.93/1.22  %Foreground operators:
% 1.93/1.22  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 1.93/1.22  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 1.93/1.22  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 1.93/1.22  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.93/1.22  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.93/1.22  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 1.93/1.22  tff('#skF_7', type, '#skF_7': $i).
% 1.93/1.22  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.93/1.22  tff('#skF_5', type, '#skF_5': $i).
% 1.93/1.22  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 1.93/1.22  tff('#skF_6', type, '#skF_6': $i).
% 1.93/1.22  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 1.93/1.22  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 1.93/1.22  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 1.93/1.22  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.93/1.22  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 1.93/1.22  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i) > $i).
% 1.93/1.22  tff('#skF_8', type, '#skF_8': $i).
% 1.93/1.22  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.93/1.22  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.93/1.22  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.93/1.22  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 1.93/1.22  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.93/1.22  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 1.93/1.22  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.93/1.22  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.93/1.22  
% 1.93/1.23  tff(f_82, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ~(r2_hidden(C, k2_relset_1(A, B, D)) & (![E]: ~(r2_hidden(E, A) & (k1_funct_1(D, E) = C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_funct_2)).
% 1.93/1.23  tff(f_56, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 1.93/1.23  tff(f_62, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 1.93/1.23  tff(f_35, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t209_relat_1)).
% 1.93/1.23  tff(f_29, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_relat_1)).
% 1.93/1.23  tff(f_52, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B, C]: ((C = k9_relat_1(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (?[E]: ((r2_hidden(E, k1_relat_1(A)) & r2_hidden(E, B)) & (D = k1_funct_1(A, E)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d12_funct_1)).
% 1.93/1.23  tff(f_66, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 1.93/1.23  tff(c_42, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_6')))), inference(cnfTransformation, [status(thm)], [f_82])).
% 1.93/1.23  tff(c_48, plain, (![C_59, A_60, B_61]: (v1_relat_1(C_59) | ~m1_subset_1(C_59, k1_zfmisc_1(k2_zfmisc_1(A_60, B_61))))), inference(cnfTransformation, [status(thm)], [f_56])).
% 1.93/1.23  tff(c_52, plain, (v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_42, c_48])).
% 1.93/1.23  tff(c_46, plain, (v1_funct_1('#skF_8')), inference(cnfTransformation, [status(thm)], [f_82])).
% 1.93/1.23  tff(c_53, plain, (![C_62, A_63, B_64]: (v4_relat_1(C_62, A_63) | ~m1_subset_1(C_62, k1_zfmisc_1(k2_zfmisc_1(A_63, B_64))))), inference(cnfTransformation, [status(thm)], [f_62])).
% 1.93/1.23  tff(c_57, plain, (v4_relat_1('#skF_8', '#skF_5')), inference(resolution, [status(thm)], [c_42, c_53])).
% 1.93/1.23  tff(c_67, plain, (![B_67, A_68]: (k7_relat_1(B_67, A_68)=B_67 | ~v4_relat_1(B_67, A_68) | ~v1_relat_1(B_67))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.93/1.23  tff(c_70, plain, (k7_relat_1('#skF_8', '#skF_5')='#skF_8' | ~v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_57, c_67])).
% 1.93/1.23  tff(c_73, plain, (k7_relat_1('#skF_8', '#skF_5')='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_52, c_70])).
% 1.93/1.23  tff(c_2, plain, (![B_2, A_1]: (k2_relat_1(k7_relat_1(B_2, A_1))=k9_relat_1(B_2, A_1) | ~v1_relat_1(B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.93/1.23  tff(c_77, plain, (k9_relat_1('#skF_8', '#skF_5')=k2_relat_1('#skF_8') | ~v1_relat_1('#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_73, c_2])).
% 1.93/1.23  tff(c_81, plain, (k9_relat_1('#skF_8', '#skF_5')=k2_relat_1('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_77])).
% 1.93/1.23  tff(c_139, plain, (![A_90, B_91, D_92]: (k1_funct_1(A_90, '#skF_4'(A_90, B_91, k9_relat_1(A_90, B_91), D_92))=D_92 | ~r2_hidden(D_92, k9_relat_1(A_90, B_91)) | ~v1_funct_1(A_90) | ~v1_relat_1(A_90))), inference(cnfTransformation, [status(thm)], [f_52])).
% 1.93/1.23  tff(c_102, plain, (![A_75, B_76, D_77]: (r2_hidden('#skF_4'(A_75, B_76, k9_relat_1(A_75, B_76), D_77), B_76) | ~r2_hidden(D_77, k9_relat_1(A_75, B_76)) | ~v1_funct_1(A_75) | ~v1_relat_1(A_75))), inference(cnfTransformation, [status(thm)], [f_52])).
% 1.93/1.23  tff(c_38, plain, (![E_57]: (k1_funct_1('#skF_8', E_57)!='#skF_7' | ~r2_hidden(E_57, '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_82])).
% 1.93/1.23  tff(c_110, plain, (![A_75, D_77]: (k1_funct_1('#skF_8', '#skF_4'(A_75, '#skF_5', k9_relat_1(A_75, '#skF_5'), D_77))!='#skF_7' | ~r2_hidden(D_77, k9_relat_1(A_75, '#skF_5')) | ~v1_funct_1(A_75) | ~v1_relat_1(A_75))), inference(resolution, [status(thm)], [c_102, c_38])).
% 1.93/1.23  tff(c_153, plain, (![D_92]: (D_92!='#skF_7' | ~r2_hidden(D_92, k9_relat_1('#skF_8', '#skF_5')) | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8') | ~r2_hidden(D_92, k9_relat_1('#skF_8', '#skF_5')) | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_139, c_110])).
% 1.93/1.23  tff(c_168, plain, (~r2_hidden('#skF_7', k2_relat_1('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_46, c_81, c_52, c_46, c_81, c_153])).
% 1.93/1.23  tff(c_92, plain, (![A_72, B_73, C_74]: (k2_relset_1(A_72, B_73, C_74)=k2_relat_1(C_74) | ~m1_subset_1(C_74, k1_zfmisc_1(k2_zfmisc_1(A_72, B_73))))), inference(cnfTransformation, [status(thm)], [f_66])).
% 1.93/1.23  tff(c_96, plain, (k2_relset_1('#skF_5', '#skF_6', '#skF_8')=k2_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_42, c_92])).
% 1.93/1.23  tff(c_40, plain, (r2_hidden('#skF_7', k2_relset_1('#skF_5', '#skF_6', '#skF_8'))), inference(cnfTransformation, [status(thm)], [f_82])).
% 1.93/1.23  tff(c_97, plain, (r2_hidden('#skF_7', k2_relat_1('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_96, c_40])).
% 1.93/1.23  tff(c_170, plain, $false, inference(negUnitSimplification, [status(thm)], [c_168, c_97])).
% 1.93/1.23  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.93/1.23  
% 1.93/1.23  Inference rules
% 1.93/1.23  ----------------------
% 1.93/1.23  #Ref     : 0
% 1.93/1.23  #Sup     : 26
% 1.93/1.23  #Fact    : 0
% 1.93/1.23  #Define  : 0
% 1.93/1.23  #Split   : 0
% 1.93/1.23  #Chain   : 0
% 1.93/1.23  #Close   : 0
% 1.93/1.23  
% 1.93/1.23  Ordering : KBO
% 1.93/1.23  
% 1.93/1.23  Simplification rules
% 1.93/1.23  ----------------------
% 1.93/1.23  #Subsume      : 1
% 1.93/1.23  #Demod        : 25
% 1.93/1.23  #Tautology    : 10
% 1.93/1.23  #SimpNegUnit  : 1
% 1.93/1.23  #BackRed      : 2
% 1.93/1.23  
% 1.93/1.23  #Partial instantiations: 0
% 1.93/1.23  #Strategies tried      : 1
% 1.93/1.23  
% 1.93/1.23  Timing (in seconds)
% 1.93/1.23  ----------------------
% 1.93/1.23  Preprocessing        : 0.32
% 1.93/1.23  Parsing              : 0.16
% 2.16/1.23  CNF conversion       : 0.03
% 2.16/1.23  Main loop            : 0.15
% 2.16/1.23  Inferencing          : 0.06
% 2.16/1.23  Reduction            : 0.05
% 2.16/1.23  Demodulation         : 0.03
% 2.16/1.23  BG Simplification    : 0.02
% 2.16/1.23  Subsumption          : 0.03
% 2.16/1.23  Abstraction          : 0.01
% 2.16/1.23  MUC search           : 0.00
% 2.16/1.23  Cooper               : 0.00
% 2.16/1.23  Total                : 0.50
% 2.16/1.23  Index Insertion      : 0.00
% 2.16/1.23  Index Deletion       : 0.00
% 2.16/1.23  Index Matching       : 0.00
% 2.16/1.23  BG Taut test         : 0.00
%------------------------------------------------------------------------------
