%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:16:21 EST 2020

% Result     : Theorem 2.09s
% Output     : CNFRefutation 2.09s
% Verified   : 
% Statistics : Number of formulae       :   47 (  69 expanded)
%              Number of leaves         :   22 (  37 expanded)
%              Depth                    :   11
%              Number of atoms          :   86 ( 228 expanded)
%              Number of equality atoms :    7 (  22 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > r2_hidden > m1_subset_1 > v1_funct_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_subset_1 > k1_zfmisc_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_relset_1,type,(
    r2_relset_1: ( $i * $i * $i * $i ) > $o )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i ) > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_76,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ! [D] :
            ( ( v1_funct_1(D)
              & v1_funct_2(D,A,B)
              & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
           => ( ! [E] :
                  ( m1_subset_1(E,A)
                 => k1_funct_1(C,E) = k1_funct_1(D,E) )
             => r2_relset_1(A,B,C,D) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_funct_2)).

tff(f_55,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ! [D] :
          ( ( v1_funct_1(D)
            & v1_funct_2(D,A,B)
            & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
         => ( ! [E] :
                ( r2_hidden(E,A)
               => k1_funct_1(C,E) = k1_funct_1(D,E) )
           => r2_relset_1(A,B,C,D) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_funct_2)).

tff(f_27,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_29,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

tff(c_12,plain,(
    ~ r2_relset_1('#skF_2','#skF_3','#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_26,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_24,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_22,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_20,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_18,plain,(
    v1_funct_2('#skF_5','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_16,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_52,plain,(
    ! [A_29,B_30,C_31,D_32] :
      ( r2_hidden('#skF_1'(A_29,B_30,C_31,D_32),A_29)
      | r2_relset_1(A_29,B_30,C_31,D_32)
      | ~ m1_subset_1(D_32,k1_zfmisc_1(k2_zfmisc_1(A_29,B_30)))
      | ~ v1_funct_2(D_32,A_29,B_30)
      | ~ v1_funct_1(D_32)
      | ~ m1_subset_1(C_31,k1_zfmisc_1(k2_zfmisc_1(A_29,B_30)))
      | ~ v1_funct_2(C_31,A_29,B_30)
      | ~ v1_funct_1(C_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_56,plain,(
    ! [C_31] :
      ( r2_hidden('#skF_1'('#skF_2','#skF_3',C_31,'#skF_5'),'#skF_2')
      | r2_relset_1('#skF_2','#skF_3',C_31,'#skF_5')
      | ~ v1_funct_2('#skF_5','#skF_2','#skF_3')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1(C_31,k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
      | ~ v1_funct_2(C_31,'#skF_2','#skF_3')
      | ~ v1_funct_1(C_31) ) ),
    inference(resolution,[status(thm)],[c_16,c_52])).

tff(c_91,plain,(
    ! [C_38] :
      ( r2_hidden('#skF_1'('#skF_2','#skF_3',C_38,'#skF_5'),'#skF_2')
      | r2_relset_1('#skF_2','#skF_3',C_38,'#skF_5')
      | ~ m1_subset_1(C_38,k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
      | ~ v1_funct_2(C_38,'#skF_2','#skF_3')
      | ~ v1_funct_1(C_38) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_18,c_56])).

tff(c_94,plain,
    ( r2_hidden('#skF_1'('#skF_2','#skF_3','#skF_4','#skF_5'),'#skF_2')
    | r2_relset_1('#skF_2','#skF_3','#skF_4','#skF_5')
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_3')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_22,c_91])).

tff(c_104,plain,
    ( r2_hidden('#skF_1'('#skF_2','#skF_3','#skF_4','#skF_5'),'#skF_2')
    | r2_relset_1('#skF_2','#skF_3','#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_24,c_94])).

tff(c_105,plain,(
    r2_hidden('#skF_1'('#skF_2','#skF_3','#skF_4','#skF_5'),'#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_12,c_104])).

tff(c_2,plain,(
    ! [A_1] : k2_subset_1(A_1) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_4,plain,(
    ! [A_2] : m1_subset_1(k2_subset_1(A_2),k1_zfmisc_1(A_2)) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_27,plain,(
    ! [A_2] : m1_subset_1(A_2,k1_zfmisc_1(A_2)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_4])).

tff(c_39,plain,(
    ! [A_22,C_23,B_24] :
      ( m1_subset_1(A_22,C_23)
      | ~ m1_subset_1(B_24,k1_zfmisc_1(C_23))
      | ~ r2_hidden(A_22,B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_48,plain,(
    ! [A_22,A_2] :
      ( m1_subset_1(A_22,A_2)
      | ~ r2_hidden(A_22,A_2) ) ),
    inference(resolution,[status(thm)],[c_27,c_39])).

tff(c_113,plain,(
    m1_subset_1('#skF_1'('#skF_2','#skF_3','#skF_4','#skF_5'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_105,c_48])).

tff(c_14,plain,(
    ! [E_18] :
      ( k1_funct_1('#skF_5',E_18) = k1_funct_1('#skF_4',E_18)
      | ~ m1_subset_1(E_18,'#skF_2') ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_117,plain,(
    k1_funct_1('#skF_5','#skF_1'('#skF_2','#skF_3','#skF_4','#skF_5')) = k1_funct_1('#skF_4','#skF_1'('#skF_2','#skF_3','#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_113,c_14])).

tff(c_8,plain,(
    ! [D_12,A_6,B_7,C_8] :
      ( k1_funct_1(D_12,'#skF_1'(A_6,B_7,C_8,D_12)) != k1_funct_1(C_8,'#skF_1'(A_6,B_7,C_8,D_12))
      | r2_relset_1(A_6,B_7,C_8,D_12)
      | ~ m1_subset_1(D_12,k1_zfmisc_1(k2_zfmisc_1(A_6,B_7)))
      | ~ v1_funct_2(D_12,A_6,B_7)
      | ~ v1_funct_1(D_12)
      | ~ m1_subset_1(C_8,k1_zfmisc_1(k2_zfmisc_1(A_6,B_7)))
      | ~ v1_funct_2(C_8,A_6,B_7)
      | ~ v1_funct_1(C_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_139,plain,
    ( r2_relset_1('#skF_2','#skF_3','#skF_4','#skF_5')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
    | ~ v1_funct_2('#skF_5','#skF_2','#skF_3')
    | ~ v1_funct_1('#skF_5')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_3')
    | ~ v1_funct_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_117,c_8])).

tff(c_144,plain,(
    r2_relset_1('#skF_2','#skF_3','#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_24,c_22,c_20,c_18,c_16,c_139])).

tff(c_146,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_12,c_144])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n005.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 11:17:32 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.09/1.19  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.09/1.20  
% 2.09/1.20  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.09/1.20  %$ r2_relset_1 > v1_funct_2 > r2_hidden > m1_subset_1 > v1_funct_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_subset_1 > k1_zfmisc_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 2.09/1.20  
% 2.09/1.20  %Foreground sorts:
% 2.09/1.20  
% 2.09/1.20  
% 2.09/1.20  %Background operators:
% 2.09/1.20  
% 2.09/1.20  
% 2.09/1.20  %Foreground operators:
% 2.09/1.20  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.09/1.20  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.09/1.20  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 2.09/1.20  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.09/1.20  tff('#skF_5', type, '#skF_5': $i).
% 2.09/1.20  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.09/1.20  tff('#skF_2', type, '#skF_2': $i).
% 2.09/1.20  tff('#skF_3', type, '#skF_3': $i).
% 2.09/1.20  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.09/1.20  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.09/1.20  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.09/1.20  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.09/1.20  tff('#skF_4', type, '#skF_4': $i).
% 2.09/1.20  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.09/1.20  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 2.09/1.20  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 2.09/1.20  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.09/1.20  
% 2.09/1.21  tff(f_76, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((![E]: (m1_subset_1(E, A) => (k1_funct_1(C, E) = k1_funct_1(D, E)))) => r2_relset_1(A, B, C, D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_funct_2)).
% 2.09/1.21  tff(f_55, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((![E]: (r2_hidden(E, A) => (k1_funct_1(C, E) = k1_funct_1(D, E)))) => r2_relset_1(A, B, C, D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t18_funct_2)).
% 2.09/1.21  tff(f_27, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 2.09/1.21  tff(f_29, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 2.09/1.21  tff(f_35, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset)).
% 2.09/1.21  tff(c_12, plain, (~r2_relset_1('#skF_2', '#skF_3', '#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.09/1.21  tff(c_26, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.09/1.21  tff(c_24, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.09/1.21  tff(c_22, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.09/1.21  tff(c_20, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.09/1.21  tff(c_18, plain, (v1_funct_2('#skF_5', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.09/1.21  tff(c_16, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.09/1.21  tff(c_52, plain, (![A_29, B_30, C_31, D_32]: (r2_hidden('#skF_1'(A_29, B_30, C_31, D_32), A_29) | r2_relset_1(A_29, B_30, C_31, D_32) | ~m1_subset_1(D_32, k1_zfmisc_1(k2_zfmisc_1(A_29, B_30))) | ~v1_funct_2(D_32, A_29, B_30) | ~v1_funct_1(D_32) | ~m1_subset_1(C_31, k1_zfmisc_1(k2_zfmisc_1(A_29, B_30))) | ~v1_funct_2(C_31, A_29, B_30) | ~v1_funct_1(C_31))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.09/1.21  tff(c_56, plain, (![C_31]: (r2_hidden('#skF_1'('#skF_2', '#skF_3', C_31, '#skF_5'), '#skF_2') | r2_relset_1('#skF_2', '#skF_3', C_31, '#skF_5') | ~v1_funct_2('#skF_5', '#skF_2', '#skF_3') | ~v1_funct_1('#skF_5') | ~m1_subset_1(C_31, k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~v1_funct_2(C_31, '#skF_2', '#skF_3') | ~v1_funct_1(C_31))), inference(resolution, [status(thm)], [c_16, c_52])).
% 2.09/1.21  tff(c_91, plain, (![C_38]: (r2_hidden('#skF_1'('#skF_2', '#skF_3', C_38, '#skF_5'), '#skF_2') | r2_relset_1('#skF_2', '#skF_3', C_38, '#skF_5') | ~m1_subset_1(C_38, k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~v1_funct_2(C_38, '#skF_2', '#skF_3') | ~v1_funct_1(C_38))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_18, c_56])).
% 2.09/1.21  tff(c_94, plain, (r2_hidden('#skF_1'('#skF_2', '#skF_3', '#skF_4', '#skF_5'), '#skF_2') | r2_relset_1('#skF_2', '#skF_3', '#skF_4', '#skF_5') | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_22, c_91])).
% 2.09/1.21  tff(c_104, plain, (r2_hidden('#skF_1'('#skF_2', '#skF_3', '#skF_4', '#skF_5'), '#skF_2') | r2_relset_1('#skF_2', '#skF_3', '#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_24, c_94])).
% 2.09/1.21  tff(c_105, plain, (r2_hidden('#skF_1'('#skF_2', '#skF_3', '#skF_4', '#skF_5'), '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_12, c_104])).
% 2.09/1.21  tff(c_2, plain, (![A_1]: (k2_subset_1(A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.09/1.21  tff(c_4, plain, (![A_2]: (m1_subset_1(k2_subset_1(A_2), k1_zfmisc_1(A_2)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.09/1.21  tff(c_27, plain, (![A_2]: (m1_subset_1(A_2, k1_zfmisc_1(A_2)))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_4])).
% 2.09/1.21  tff(c_39, plain, (![A_22, C_23, B_24]: (m1_subset_1(A_22, C_23) | ~m1_subset_1(B_24, k1_zfmisc_1(C_23)) | ~r2_hidden(A_22, B_24))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.09/1.21  tff(c_48, plain, (![A_22, A_2]: (m1_subset_1(A_22, A_2) | ~r2_hidden(A_22, A_2))), inference(resolution, [status(thm)], [c_27, c_39])).
% 2.09/1.21  tff(c_113, plain, (m1_subset_1('#skF_1'('#skF_2', '#skF_3', '#skF_4', '#skF_5'), '#skF_2')), inference(resolution, [status(thm)], [c_105, c_48])).
% 2.09/1.21  tff(c_14, plain, (![E_18]: (k1_funct_1('#skF_5', E_18)=k1_funct_1('#skF_4', E_18) | ~m1_subset_1(E_18, '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.09/1.21  tff(c_117, plain, (k1_funct_1('#skF_5', '#skF_1'('#skF_2', '#skF_3', '#skF_4', '#skF_5'))=k1_funct_1('#skF_4', '#skF_1'('#skF_2', '#skF_3', '#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_113, c_14])).
% 2.09/1.21  tff(c_8, plain, (![D_12, A_6, B_7, C_8]: (k1_funct_1(D_12, '#skF_1'(A_6, B_7, C_8, D_12))!=k1_funct_1(C_8, '#skF_1'(A_6, B_7, C_8, D_12)) | r2_relset_1(A_6, B_7, C_8, D_12) | ~m1_subset_1(D_12, k1_zfmisc_1(k2_zfmisc_1(A_6, B_7))) | ~v1_funct_2(D_12, A_6, B_7) | ~v1_funct_1(D_12) | ~m1_subset_1(C_8, k1_zfmisc_1(k2_zfmisc_1(A_6, B_7))) | ~v1_funct_2(C_8, A_6, B_7) | ~v1_funct_1(C_8))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.09/1.21  tff(c_139, plain, (r2_relset_1('#skF_2', '#skF_3', '#skF_4', '#skF_5') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~v1_funct_2('#skF_5', '#skF_2', '#skF_3') | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3') | ~v1_funct_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_117, c_8])).
% 2.09/1.21  tff(c_144, plain, (r2_relset_1('#skF_2', '#skF_3', '#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_24, c_22, c_20, c_18, c_16, c_139])).
% 2.09/1.21  tff(c_146, plain, $false, inference(negUnitSimplification, [status(thm)], [c_12, c_144])).
% 2.09/1.21  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.09/1.21  
% 2.09/1.21  Inference rules
% 2.09/1.21  ----------------------
% 2.09/1.21  #Ref     : 1
% 2.09/1.21  #Sup     : 22
% 2.09/1.21  #Fact    : 0
% 2.09/1.21  #Define  : 0
% 2.09/1.21  #Split   : 3
% 2.09/1.21  #Chain   : 0
% 2.09/1.21  #Close   : 0
% 2.09/1.21  
% 2.09/1.21  Ordering : KBO
% 2.09/1.21  
% 2.09/1.21  Simplification rules
% 2.09/1.21  ----------------------
% 2.09/1.21  #Subsume      : 0
% 2.09/1.21  #Demod        : 28
% 2.09/1.21  #Tautology    : 5
% 2.09/1.21  #SimpNegUnit  : 2
% 2.09/1.21  #BackRed      : 0
% 2.09/1.21  
% 2.09/1.21  #Partial instantiations: 0
% 2.09/1.21  #Strategies tried      : 1
% 2.09/1.21  
% 2.09/1.21  Timing (in seconds)
% 2.09/1.21  ----------------------
% 2.09/1.22  Preprocessing        : 0.29
% 2.09/1.22  Parsing              : 0.15
% 2.09/1.22  CNF conversion       : 0.02
% 2.09/1.22  Main loop            : 0.18
% 2.09/1.22  Inferencing          : 0.07
% 2.09/1.22  Reduction            : 0.06
% 2.09/1.22  Demodulation         : 0.04
% 2.09/1.22  BG Simplification    : 0.01
% 2.09/1.22  Subsumption          : 0.03
% 2.09/1.22  Abstraction          : 0.01
% 2.09/1.22  MUC search           : 0.00
% 2.09/1.22  Cooper               : 0.00
% 2.09/1.22  Total                : 0.49
% 2.09/1.22  Index Insertion      : 0.00
% 2.09/1.22  Index Deletion       : 0.00
% 2.09/1.22  Index Matching       : 0.00
% 2.09/1.22  BG Taut test         : 0.00
%------------------------------------------------------------------------------
