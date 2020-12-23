%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:15:48 EST 2020

% Result     : Theorem 2.08s
% Output     : CNFRefutation 2.17s
% Verified   : 
% Statistics : Number of formulae       :   58 ( 114 expanded)
%              Number of leaves         :   26 (  55 expanded)
%              Depth                    :   10
%              Number of atoms          :   88 ( 325 expanded)
%              Number of equality atoms :   23 (  77 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff(k2_funct_1,type,(
    k2_funct_1: $i > $i )).

tff(v2_funct_1,type,(
    v2_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

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

tff(f_76,negated_conjecture,(
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

tff(f_50,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_58,axiom,(
    ! [A,B] :
      ( ( v1_funct_1(B)
        & v1_funct_2(B,A,A)
        & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
     => k1_relset_1(A,A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_funct_2)).

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

tff(f_46,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( ( v2_funct_1(B)
          & r2_hidden(A,k1_relat_1(B)) )
       => ( A = k1_funct_1(k2_funct_1(B),k1_funct_1(B,A))
          & A = k1_funct_1(k5_relat_1(B,k2_funct_1(B)),A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_funct_1)).

tff(c_18,plain,(
    r2_hidden('#skF_4','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_28,plain,(
    v1_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_26,plain,(
    v1_funct_2('#skF_2','#skF_1','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_24,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_41,plain,(
    ! [A_19,B_20,C_21] :
      ( k1_relset_1(A_19,B_20,C_21) = k1_relat_1(C_21)
      | ~ m1_subset_1(C_21,k1_zfmisc_1(k2_zfmisc_1(A_19,B_20))) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_45,plain,(
    k1_relset_1('#skF_1','#skF_1','#skF_2') = k1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_24,c_41])).

tff(c_106,plain,(
    ! [A_26,B_27] :
      ( k1_relset_1(A_26,A_26,B_27) = A_26
      | ~ m1_subset_1(B_27,k1_zfmisc_1(k2_zfmisc_1(A_26,A_26)))
      | ~ v1_funct_2(B_27,A_26,A_26)
      | ~ v1_funct_1(B_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_109,plain,
    ( k1_relset_1('#skF_1','#skF_1','#skF_2') = '#skF_1'
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_24,c_106])).

tff(c_112,plain,(
    k1_relat_1('#skF_2') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_45,c_109])).

tff(c_14,plain,(
    '#skF_3' != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_4,plain,(
    ! [A_4,B_5] : v1_relat_1(k2_zfmisc_1(A_4,B_5)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_34,plain,(
    ! [B_17,A_18] :
      ( v1_relat_1(B_17)
      | ~ m1_subset_1(B_17,k1_zfmisc_1(A_18))
      | ~ v1_relat_1(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_37,plain,
    ( v1_relat_1('#skF_2')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_1')) ),
    inference(resolution,[status(thm)],[c_24,c_34])).

tff(c_40,plain,(
    v1_relat_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_37])).

tff(c_22,plain,(
    v2_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_20,plain,(
    r2_hidden('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_71,plain,(
    ! [A_24,B_25] :
      ( k1_relset_1(A_24,A_24,B_25) = A_24
      | ~ m1_subset_1(B_25,k1_zfmisc_1(k2_zfmisc_1(A_24,A_24)))
      | ~ v1_funct_2(B_25,A_24,A_24)
      | ~ v1_funct_1(B_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_74,plain,
    ( k1_relset_1('#skF_1','#skF_1','#skF_2') = '#skF_1'
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_24,c_71])).

tff(c_77,plain,(
    k1_relat_1('#skF_2') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_45,c_74])).

tff(c_16,plain,(
    k1_funct_1('#skF_2','#skF_3') = k1_funct_1('#skF_2','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_50,plain,(
    ! [B_22,A_23] :
      ( k1_funct_1(k2_funct_1(B_22),k1_funct_1(B_22,A_23)) = A_23
      | ~ r2_hidden(A_23,k1_relat_1(B_22))
      | ~ v2_funct_1(B_22)
      | ~ v1_funct_1(B_22)
      | ~ v1_relat_1(B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_65,plain,
    ( k1_funct_1(k2_funct_1('#skF_2'),k1_funct_1('#skF_2','#skF_4')) = '#skF_3'
    | ~ r2_hidden('#skF_3',k1_relat_1('#skF_2'))
    | ~ v2_funct_1('#skF_2')
    | ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_50])).

tff(c_69,plain,
    ( k1_funct_1(k2_funct_1('#skF_2'),k1_funct_1('#skF_2','#skF_4')) = '#skF_3'
    | ~ r2_hidden('#skF_3',k1_relat_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_28,c_22,c_65])).

tff(c_70,plain,(
    ~ r2_hidden('#skF_3',k1_relat_1('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_69])).

tff(c_84,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_77,c_70])).

tff(c_85,plain,(
    k1_funct_1(k2_funct_1('#skF_2'),k1_funct_1('#skF_2','#skF_4')) = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_69])).

tff(c_8,plain,(
    ! [B_7,A_6] :
      ( k1_funct_1(k2_funct_1(B_7),k1_funct_1(B_7,A_6)) = A_6
      | ~ r2_hidden(A_6,k1_relat_1(B_7))
      | ~ v2_funct_1(B_7)
      | ~ v1_funct_1(B_7)
      | ~ v1_relat_1(B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_93,plain,
    ( '#skF_3' = '#skF_4'
    | ~ r2_hidden('#skF_4',k1_relat_1('#skF_2'))
    | ~ v2_funct_1('#skF_2')
    | ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_85,c_8])).

tff(c_100,plain,
    ( '#skF_3' = '#skF_4'
    | ~ r2_hidden('#skF_4',k1_relat_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_28,c_22,c_93])).

tff(c_101,plain,(
    ~ r2_hidden('#skF_4',k1_relat_1('#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_14,c_100])).

tff(c_113,plain,(
    ~ r2_hidden('#skF_4','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_112,c_101])).

tff(c_118,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_113])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n007.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:54:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.08/1.19  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.17/1.20  
% 2.17/1.20  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.17/1.20  %$ v1_funct_2 > r2_hidden > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.17/1.20  
% 2.17/1.20  %Foreground sorts:
% 2.17/1.20  
% 2.17/1.20  
% 2.17/1.20  %Background operators:
% 2.17/1.20  
% 2.17/1.20  
% 2.17/1.20  %Foreground operators:
% 2.17/1.20  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.17/1.20  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 2.17/1.20  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 2.17/1.20  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.17/1.20  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.17/1.20  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.17/1.20  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.17/1.20  tff('#skF_2', type, '#skF_2': $i).
% 2.17/1.20  tff('#skF_3', type, '#skF_3': $i).
% 2.17/1.20  tff('#skF_1', type, '#skF_1': $i).
% 2.17/1.20  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.17/1.20  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.17/1.20  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.17/1.20  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.17/1.20  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.17/1.20  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.17/1.20  tff('#skF_4', type, '#skF_4': $i).
% 2.17/1.20  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.17/1.20  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.17/1.20  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.17/1.20  
% 2.17/1.22  tff(f_76, negated_conjecture, ~(![A, B]: (((v1_funct_1(B) & v1_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (v2_funct_1(B) => (![C, D]: (((r2_hidden(C, A) & r2_hidden(D, A)) & (k1_funct_1(B, C) = k1_funct_1(B, D))) => (C = D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t85_funct_2)).
% 2.17/1.22  tff(f_50, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.17/1.22  tff(f_58, axiom, (![A, B]: (((v1_funct_1(B) & v1_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (k1_relset_1(A, A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t67_funct_2)).
% 2.17/1.22  tff(f_34, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 2.17/1.22  tff(f_32, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 2.17/1.22  tff(f_46, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((v2_funct_1(B) & r2_hidden(A, k1_relat_1(B))) => ((A = k1_funct_1(k2_funct_1(B), k1_funct_1(B, A))) & (A = k1_funct_1(k5_relat_1(B, k2_funct_1(B)), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t56_funct_1)).
% 2.17/1.22  tff(c_18, plain, (r2_hidden('#skF_4', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.17/1.22  tff(c_28, plain, (v1_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.17/1.22  tff(c_26, plain, (v1_funct_2('#skF_2', '#skF_1', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.17/1.22  tff(c_24, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.17/1.22  tff(c_41, plain, (![A_19, B_20, C_21]: (k1_relset_1(A_19, B_20, C_21)=k1_relat_1(C_21) | ~m1_subset_1(C_21, k1_zfmisc_1(k2_zfmisc_1(A_19, B_20))))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.17/1.22  tff(c_45, plain, (k1_relset_1('#skF_1', '#skF_1', '#skF_2')=k1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_24, c_41])).
% 2.17/1.22  tff(c_106, plain, (![A_26, B_27]: (k1_relset_1(A_26, A_26, B_27)=A_26 | ~m1_subset_1(B_27, k1_zfmisc_1(k2_zfmisc_1(A_26, A_26))) | ~v1_funct_2(B_27, A_26, A_26) | ~v1_funct_1(B_27))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.17/1.22  tff(c_109, plain, (k1_relset_1('#skF_1', '#skF_1', '#skF_2')='#skF_1' | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_24, c_106])).
% 2.17/1.22  tff(c_112, plain, (k1_relat_1('#skF_2')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_28, c_26, c_45, c_109])).
% 2.17/1.22  tff(c_14, plain, ('#skF_3'!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.17/1.22  tff(c_4, plain, (![A_4, B_5]: (v1_relat_1(k2_zfmisc_1(A_4, B_5)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.17/1.22  tff(c_34, plain, (![B_17, A_18]: (v1_relat_1(B_17) | ~m1_subset_1(B_17, k1_zfmisc_1(A_18)) | ~v1_relat_1(A_18))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.17/1.22  tff(c_37, plain, (v1_relat_1('#skF_2') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_1'))), inference(resolution, [status(thm)], [c_24, c_34])).
% 2.17/1.22  tff(c_40, plain, (v1_relat_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_37])).
% 2.17/1.22  tff(c_22, plain, (v2_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.17/1.22  tff(c_20, plain, (r2_hidden('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.17/1.22  tff(c_71, plain, (![A_24, B_25]: (k1_relset_1(A_24, A_24, B_25)=A_24 | ~m1_subset_1(B_25, k1_zfmisc_1(k2_zfmisc_1(A_24, A_24))) | ~v1_funct_2(B_25, A_24, A_24) | ~v1_funct_1(B_25))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.17/1.22  tff(c_74, plain, (k1_relset_1('#skF_1', '#skF_1', '#skF_2')='#skF_1' | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_24, c_71])).
% 2.17/1.22  tff(c_77, plain, (k1_relat_1('#skF_2')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_28, c_26, c_45, c_74])).
% 2.17/1.22  tff(c_16, plain, (k1_funct_1('#skF_2', '#skF_3')=k1_funct_1('#skF_2', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.17/1.22  tff(c_50, plain, (![B_22, A_23]: (k1_funct_1(k2_funct_1(B_22), k1_funct_1(B_22, A_23))=A_23 | ~r2_hidden(A_23, k1_relat_1(B_22)) | ~v2_funct_1(B_22) | ~v1_funct_1(B_22) | ~v1_relat_1(B_22))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.17/1.22  tff(c_65, plain, (k1_funct_1(k2_funct_1('#skF_2'), k1_funct_1('#skF_2', '#skF_4'))='#skF_3' | ~r2_hidden('#skF_3', k1_relat_1('#skF_2')) | ~v2_funct_1('#skF_2') | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_16, c_50])).
% 2.17/1.22  tff(c_69, plain, (k1_funct_1(k2_funct_1('#skF_2'), k1_funct_1('#skF_2', '#skF_4'))='#skF_3' | ~r2_hidden('#skF_3', k1_relat_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_28, c_22, c_65])).
% 2.17/1.22  tff(c_70, plain, (~r2_hidden('#skF_3', k1_relat_1('#skF_2'))), inference(splitLeft, [status(thm)], [c_69])).
% 2.17/1.22  tff(c_84, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_20, c_77, c_70])).
% 2.17/1.22  tff(c_85, plain, (k1_funct_1(k2_funct_1('#skF_2'), k1_funct_1('#skF_2', '#skF_4'))='#skF_3'), inference(splitRight, [status(thm)], [c_69])).
% 2.17/1.22  tff(c_8, plain, (![B_7, A_6]: (k1_funct_1(k2_funct_1(B_7), k1_funct_1(B_7, A_6))=A_6 | ~r2_hidden(A_6, k1_relat_1(B_7)) | ~v2_funct_1(B_7) | ~v1_funct_1(B_7) | ~v1_relat_1(B_7))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.17/1.22  tff(c_93, plain, ('#skF_3'='#skF_4' | ~r2_hidden('#skF_4', k1_relat_1('#skF_2')) | ~v2_funct_1('#skF_2') | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_85, c_8])).
% 2.17/1.22  tff(c_100, plain, ('#skF_3'='#skF_4' | ~r2_hidden('#skF_4', k1_relat_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_28, c_22, c_93])).
% 2.17/1.22  tff(c_101, plain, (~r2_hidden('#skF_4', k1_relat_1('#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_14, c_100])).
% 2.17/1.22  tff(c_113, plain, (~r2_hidden('#skF_4', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_112, c_101])).
% 2.17/1.22  tff(c_118, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_18, c_113])).
% 2.17/1.22  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.17/1.22  
% 2.17/1.22  Inference rules
% 2.17/1.22  ----------------------
% 2.17/1.22  #Ref     : 0
% 2.17/1.22  #Sup     : 20
% 2.17/1.22  #Fact    : 0
% 2.17/1.22  #Define  : 0
% 2.17/1.22  #Split   : 1
% 2.17/1.22  #Chain   : 0
% 2.17/1.22  #Close   : 0
% 2.17/1.22  
% 2.17/1.22  Ordering : KBO
% 2.17/1.22  
% 2.17/1.22  Simplification rules
% 2.17/1.22  ----------------------
% 2.17/1.22  #Subsume      : 1
% 2.17/1.22  #Demod        : 23
% 2.17/1.22  #Tautology    : 10
% 2.17/1.22  #SimpNegUnit  : 2
% 2.17/1.22  #BackRed      : 4
% 2.17/1.22  
% 2.17/1.22  #Partial instantiations: 0
% 2.17/1.22  #Strategies tried      : 1
% 2.17/1.22  
% 2.17/1.22  Timing (in seconds)
% 2.17/1.22  ----------------------
% 2.17/1.22  Preprocessing        : 0.29
% 2.17/1.22  Parsing              : 0.16
% 2.17/1.22  CNF conversion       : 0.02
% 2.17/1.22  Main loop            : 0.13
% 2.17/1.22  Inferencing          : 0.05
% 2.17/1.22  Reduction            : 0.04
% 2.17/1.22  Demodulation         : 0.03
% 2.17/1.22  BG Simplification    : 0.01
% 2.17/1.22  Subsumption          : 0.02
% 2.17/1.22  Abstraction          : 0.01
% 2.17/1.22  MUC search           : 0.00
% 2.17/1.22  Cooper               : 0.00
% 2.17/1.22  Total                : 0.46
% 2.17/1.22  Index Insertion      : 0.00
% 2.17/1.22  Index Deletion       : 0.00
% 2.17/1.22  Index Matching       : 0.00
% 2.17/1.22  BG Taut test         : 0.00
%------------------------------------------------------------------------------
