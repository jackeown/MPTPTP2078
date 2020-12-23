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
% DateTime   : Thu Dec  3 10:15:34 EST 2020

% Result     : Theorem 1.89s
% Output     : CNFRefutation 1.89s
% Verified   : 
% Statistics : Number of formulae       :   43 ( 100 expanded)
%              Number of leaves         :   20 (  49 expanded)
%              Depth                    :   12
%              Number of atoms          :   90 ( 351 expanded)
%              Number of equality atoms :   10 (  15 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > r2_hidden > m1_subset_1 > v1_funct_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_tarski > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1

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

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

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

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_71,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,A,k1_tarski(B))
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,k1_tarski(B)))) )
       => ! [D] :
            ( ( v1_funct_1(D)
              & v1_funct_2(D,A,k1_tarski(B))
              & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,k1_tarski(B)))) )
           => r2_relset_1(A,k1_tarski(B),C,D) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_funct_2)).

tff(f_45,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_funct_2)).

tff(f_55,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,k1_tarski(B))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,k1_tarski(B)))) )
     => ( r2_hidden(C,A)
       => k1_funct_1(D,C) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_funct_2)).

tff(c_8,plain,(
    ~ r2_relset_1('#skF_2',k1_tarski('#skF_3'),'#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_20,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_18,plain,(
    v1_funct_2('#skF_4','#skF_2',k1_tarski('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_16,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2',k1_tarski('#skF_3')))) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_14,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_12,plain,(
    v1_funct_2('#skF_5','#skF_2',k1_tarski('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_10,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2',k1_tarski('#skF_3')))) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_22,plain,(
    ! [A_18,B_19,C_20,D_21] :
      ( r2_hidden('#skF_1'(A_18,B_19,C_20,D_21),A_18)
      | r2_relset_1(A_18,B_19,C_20,D_21)
      | ~ m1_subset_1(D_21,k1_zfmisc_1(k2_zfmisc_1(A_18,B_19)))
      | ~ v1_funct_2(D_21,A_18,B_19)
      | ~ v1_funct_1(D_21)
      | ~ m1_subset_1(C_20,k1_zfmisc_1(k2_zfmisc_1(A_18,B_19)))
      | ~ v1_funct_2(C_20,A_18,B_19)
      | ~ v1_funct_1(C_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_26,plain,(
    ! [C_20] :
      ( r2_hidden('#skF_1'('#skF_2',k1_tarski('#skF_3'),C_20,'#skF_5'),'#skF_2')
      | r2_relset_1('#skF_2',k1_tarski('#skF_3'),C_20,'#skF_5')
      | ~ v1_funct_2('#skF_5','#skF_2',k1_tarski('#skF_3'))
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1(C_20,k1_zfmisc_1(k2_zfmisc_1('#skF_2',k1_tarski('#skF_3'))))
      | ~ v1_funct_2(C_20,'#skF_2',k1_tarski('#skF_3'))
      | ~ v1_funct_1(C_20) ) ),
    inference(resolution,[status(thm)],[c_10,c_22])).

tff(c_48,plain,(
    ! [C_23] :
      ( r2_hidden('#skF_1'('#skF_2',k1_tarski('#skF_3'),C_23,'#skF_5'),'#skF_2')
      | r2_relset_1('#skF_2',k1_tarski('#skF_3'),C_23,'#skF_5')
      | ~ m1_subset_1(C_23,k1_zfmisc_1(k2_zfmisc_1('#skF_2',k1_tarski('#skF_3'))))
      | ~ v1_funct_2(C_23,'#skF_2',k1_tarski('#skF_3'))
      | ~ v1_funct_1(C_23) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_12,c_26])).

tff(c_51,plain,
    ( r2_hidden('#skF_1'('#skF_2',k1_tarski('#skF_3'),'#skF_4','#skF_5'),'#skF_2')
    | r2_relset_1('#skF_2',k1_tarski('#skF_3'),'#skF_4','#skF_5')
    | ~ v1_funct_2('#skF_4','#skF_2',k1_tarski('#skF_3'))
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_16,c_48])).

tff(c_57,plain,
    ( r2_hidden('#skF_1'('#skF_2',k1_tarski('#skF_3'),'#skF_4','#skF_5'),'#skF_2')
    | r2_relset_1('#skF_2',k1_tarski('#skF_3'),'#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_18,c_51])).

tff(c_58,plain,(
    r2_hidden('#skF_1'('#skF_2',k1_tarski('#skF_3'),'#skF_4','#skF_5'),'#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_8,c_57])).

tff(c_6,plain,(
    ! [D_12,C_11,B_10,A_9] :
      ( k1_funct_1(D_12,C_11) = B_10
      | ~ r2_hidden(C_11,A_9)
      | ~ m1_subset_1(D_12,k1_zfmisc_1(k2_zfmisc_1(A_9,k1_tarski(B_10))))
      | ~ v1_funct_2(D_12,A_9,k1_tarski(B_10))
      | ~ v1_funct_1(D_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_70,plain,(
    ! [D_28,B_29] :
      ( k1_funct_1(D_28,'#skF_1'('#skF_2',k1_tarski('#skF_3'),'#skF_4','#skF_5')) = B_29
      | ~ m1_subset_1(D_28,k1_zfmisc_1(k2_zfmisc_1('#skF_2',k1_tarski(B_29))))
      | ~ v1_funct_2(D_28,'#skF_2',k1_tarski(B_29))
      | ~ v1_funct_1(D_28) ) ),
    inference(resolution,[status(thm)],[c_58,c_6])).

tff(c_73,plain,
    ( k1_funct_1('#skF_4','#skF_1'('#skF_2',k1_tarski('#skF_3'),'#skF_4','#skF_5')) = '#skF_3'
    | ~ v1_funct_2('#skF_4','#skF_2',k1_tarski('#skF_3'))
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_16,c_70])).

tff(c_79,plain,(
    k1_funct_1('#skF_4','#skF_1'('#skF_2',k1_tarski('#skF_3'),'#skF_4','#skF_5')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_18,c_73])).

tff(c_76,plain,
    ( k1_funct_1('#skF_5','#skF_1'('#skF_2',k1_tarski('#skF_3'),'#skF_4','#skF_5')) = '#skF_3'
    | ~ v1_funct_2('#skF_5','#skF_2',k1_tarski('#skF_3'))
    | ~ v1_funct_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_10,c_70])).

tff(c_82,plain,(
    k1_funct_1('#skF_5','#skF_1'('#skF_2',k1_tarski('#skF_3'),'#skF_4','#skF_5')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_12,c_76])).

tff(c_2,plain,(
    ! [D_7,A_1,B_2,C_3] :
      ( k1_funct_1(D_7,'#skF_1'(A_1,B_2,C_3,D_7)) != k1_funct_1(C_3,'#skF_1'(A_1,B_2,C_3,D_7))
      | r2_relset_1(A_1,B_2,C_3,D_7)
      | ~ m1_subset_1(D_7,k1_zfmisc_1(k2_zfmisc_1(A_1,B_2)))
      | ~ v1_funct_2(D_7,A_1,B_2)
      | ~ v1_funct_1(D_7)
      | ~ m1_subset_1(C_3,k1_zfmisc_1(k2_zfmisc_1(A_1,B_2)))
      | ~ v1_funct_2(C_3,A_1,B_2)
      | ~ v1_funct_1(C_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_89,plain,
    ( k1_funct_1('#skF_4','#skF_1'('#skF_2',k1_tarski('#skF_3'),'#skF_4','#skF_5')) != '#skF_3'
    | r2_relset_1('#skF_2',k1_tarski('#skF_3'),'#skF_4','#skF_5')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2',k1_tarski('#skF_3'))))
    | ~ v1_funct_2('#skF_5','#skF_2',k1_tarski('#skF_3'))
    | ~ v1_funct_1('#skF_5')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2',k1_tarski('#skF_3'))))
    | ~ v1_funct_2('#skF_4','#skF_2',k1_tarski('#skF_3'))
    | ~ v1_funct_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_82,c_2])).

tff(c_93,plain,(
    r2_relset_1('#skF_2',k1_tarski('#skF_3'),'#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_18,c_16,c_14,c_12,c_10,c_79,c_89])).

tff(c_95,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_8,c_93])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:31:53 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.89/1.22  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.89/1.23  
% 1.89/1.23  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.89/1.23  %$ r2_relset_1 > v1_funct_2 > r2_hidden > m1_subset_1 > v1_funct_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_tarski > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 1.89/1.23  
% 1.89/1.23  %Foreground sorts:
% 1.89/1.23  
% 1.89/1.23  
% 1.89/1.23  %Background operators:
% 1.89/1.23  
% 1.89/1.23  
% 1.89/1.23  %Foreground operators:
% 1.89/1.23  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 1.89/1.23  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.89/1.23  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 1.89/1.23  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.89/1.23  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.89/1.23  tff('#skF_5', type, '#skF_5': $i).
% 1.89/1.23  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 1.89/1.23  tff('#skF_2', type, '#skF_2': $i).
% 1.89/1.23  tff('#skF_3', type, '#skF_3': $i).
% 1.89/1.23  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.89/1.23  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 1.89/1.23  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.89/1.23  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.89/1.23  tff('#skF_4', type, '#skF_4': $i).
% 1.89/1.23  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.89/1.23  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 1.89/1.23  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.89/1.23  
% 1.89/1.24  tff(f_71, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, k1_tarski(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, k1_tarski(B))))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, A, k1_tarski(B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, k1_tarski(B))))) => r2_relset_1(A, k1_tarski(B), C, D))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t66_funct_2)).
% 1.89/1.24  tff(f_45, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((![E]: (r2_hidden(E, A) => (k1_funct_1(C, E) = k1_funct_1(D, E)))) => r2_relset_1(A, B, C, D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t18_funct_2)).
% 1.89/1.24  tff(f_55, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, k1_tarski(B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, k1_tarski(B))))) => (r2_hidden(C, A) => (k1_funct_1(D, C) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_funct_2)).
% 1.89/1.24  tff(c_8, plain, (~r2_relset_1('#skF_2', k1_tarski('#skF_3'), '#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_71])).
% 1.89/1.24  tff(c_20, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_71])).
% 1.89/1.24  tff(c_18, plain, (v1_funct_2('#skF_4', '#skF_2', k1_tarski('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_71])).
% 1.89/1.24  tff(c_16, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', k1_tarski('#skF_3'))))), inference(cnfTransformation, [status(thm)], [f_71])).
% 1.89/1.24  tff(c_14, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_71])).
% 1.89/1.24  tff(c_12, plain, (v1_funct_2('#skF_5', '#skF_2', k1_tarski('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_71])).
% 1.89/1.24  tff(c_10, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', k1_tarski('#skF_3'))))), inference(cnfTransformation, [status(thm)], [f_71])).
% 1.89/1.24  tff(c_22, plain, (![A_18, B_19, C_20, D_21]: (r2_hidden('#skF_1'(A_18, B_19, C_20, D_21), A_18) | r2_relset_1(A_18, B_19, C_20, D_21) | ~m1_subset_1(D_21, k1_zfmisc_1(k2_zfmisc_1(A_18, B_19))) | ~v1_funct_2(D_21, A_18, B_19) | ~v1_funct_1(D_21) | ~m1_subset_1(C_20, k1_zfmisc_1(k2_zfmisc_1(A_18, B_19))) | ~v1_funct_2(C_20, A_18, B_19) | ~v1_funct_1(C_20))), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.89/1.24  tff(c_26, plain, (![C_20]: (r2_hidden('#skF_1'('#skF_2', k1_tarski('#skF_3'), C_20, '#skF_5'), '#skF_2') | r2_relset_1('#skF_2', k1_tarski('#skF_3'), C_20, '#skF_5') | ~v1_funct_2('#skF_5', '#skF_2', k1_tarski('#skF_3')) | ~v1_funct_1('#skF_5') | ~m1_subset_1(C_20, k1_zfmisc_1(k2_zfmisc_1('#skF_2', k1_tarski('#skF_3')))) | ~v1_funct_2(C_20, '#skF_2', k1_tarski('#skF_3')) | ~v1_funct_1(C_20))), inference(resolution, [status(thm)], [c_10, c_22])).
% 1.89/1.24  tff(c_48, plain, (![C_23]: (r2_hidden('#skF_1'('#skF_2', k1_tarski('#skF_3'), C_23, '#skF_5'), '#skF_2') | r2_relset_1('#skF_2', k1_tarski('#skF_3'), C_23, '#skF_5') | ~m1_subset_1(C_23, k1_zfmisc_1(k2_zfmisc_1('#skF_2', k1_tarski('#skF_3')))) | ~v1_funct_2(C_23, '#skF_2', k1_tarski('#skF_3')) | ~v1_funct_1(C_23))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_12, c_26])).
% 1.89/1.24  tff(c_51, plain, (r2_hidden('#skF_1'('#skF_2', k1_tarski('#skF_3'), '#skF_4', '#skF_5'), '#skF_2') | r2_relset_1('#skF_2', k1_tarski('#skF_3'), '#skF_4', '#skF_5') | ~v1_funct_2('#skF_4', '#skF_2', k1_tarski('#skF_3')) | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_16, c_48])).
% 1.89/1.24  tff(c_57, plain, (r2_hidden('#skF_1'('#skF_2', k1_tarski('#skF_3'), '#skF_4', '#skF_5'), '#skF_2') | r2_relset_1('#skF_2', k1_tarski('#skF_3'), '#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_20, c_18, c_51])).
% 1.89/1.24  tff(c_58, plain, (r2_hidden('#skF_1'('#skF_2', k1_tarski('#skF_3'), '#skF_4', '#skF_5'), '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_8, c_57])).
% 1.89/1.24  tff(c_6, plain, (![D_12, C_11, B_10, A_9]: (k1_funct_1(D_12, C_11)=B_10 | ~r2_hidden(C_11, A_9) | ~m1_subset_1(D_12, k1_zfmisc_1(k2_zfmisc_1(A_9, k1_tarski(B_10)))) | ~v1_funct_2(D_12, A_9, k1_tarski(B_10)) | ~v1_funct_1(D_12))), inference(cnfTransformation, [status(thm)], [f_55])).
% 1.89/1.24  tff(c_70, plain, (![D_28, B_29]: (k1_funct_1(D_28, '#skF_1'('#skF_2', k1_tarski('#skF_3'), '#skF_4', '#skF_5'))=B_29 | ~m1_subset_1(D_28, k1_zfmisc_1(k2_zfmisc_1('#skF_2', k1_tarski(B_29)))) | ~v1_funct_2(D_28, '#skF_2', k1_tarski(B_29)) | ~v1_funct_1(D_28))), inference(resolution, [status(thm)], [c_58, c_6])).
% 1.89/1.24  tff(c_73, plain, (k1_funct_1('#skF_4', '#skF_1'('#skF_2', k1_tarski('#skF_3'), '#skF_4', '#skF_5'))='#skF_3' | ~v1_funct_2('#skF_4', '#skF_2', k1_tarski('#skF_3')) | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_16, c_70])).
% 1.89/1.24  tff(c_79, plain, (k1_funct_1('#skF_4', '#skF_1'('#skF_2', k1_tarski('#skF_3'), '#skF_4', '#skF_5'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_20, c_18, c_73])).
% 1.89/1.24  tff(c_76, plain, (k1_funct_1('#skF_5', '#skF_1'('#skF_2', k1_tarski('#skF_3'), '#skF_4', '#skF_5'))='#skF_3' | ~v1_funct_2('#skF_5', '#skF_2', k1_tarski('#skF_3')) | ~v1_funct_1('#skF_5')), inference(resolution, [status(thm)], [c_10, c_70])).
% 1.89/1.24  tff(c_82, plain, (k1_funct_1('#skF_5', '#skF_1'('#skF_2', k1_tarski('#skF_3'), '#skF_4', '#skF_5'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_14, c_12, c_76])).
% 1.89/1.24  tff(c_2, plain, (![D_7, A_1, B_2, C_3]: (k1_funct_1(D_7, '#skF_1'(A_1, B_2, C_3, D_7))!=k1_funct_1(C_3, '#skF_1'(A_1, B_2, C_3, D_7)) | r2_relset_1(A_1, B_2, C_3, D_7) | ~m1_subset_1(D_7, k1_zfmisc_1(k2_zfmisc_1(A_1, B_2))) | ~v1_funct_2(D_7, A_1, B_2) | ~v1_funct_1(D_7) | ~m1_subset_1(C_3, k1_zfmisc_1(k2_zfmisc_1(A_1, B_2))) | ~v1_funct_2(C_3, A_1, B_2) | ~v1_funct_1(C_3))), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.89/1.24  tff(c_89, plain, (k1_funct_1('#skF_4', '#skF_1'('#skF_2', k1_tarski('#skF_3'), '#skF_4', '#skF_5'))!='#skF_3' | r2_relset_1('#skF_2', k1_tarski('#skF_3'), '#skF_4', '#skF_5') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', k1_tarski('#skF_3')))) | ~v1_funct_2('#skF_5', '#skF_2', k1_tarski('#skF_3')) | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', k1_tarski('#skF_3')))) | ~v1_funct_2('#skF_4', '#skF_2', k1_tarski('#skF_3')) | ~v1_funct_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_82, c_2])).
% 1.89/1.24  tff(c_93, plain, (r2_relset_1('#skF_2', k1_tarski('#skF_3'), '#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_20, c_18, c_16, c_14, c_12, c_10, c_79, c_89])).
% 1.89/1.24  tff(c_95, plain, $false, inference(negUnitSimplification, [status(thm)], [c_8, c_93])).
% 1.89/1.24  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.89/1.24  
% 1.89/1.24  Inference rules
% 1.89/1.24  ----------------------
% 1.89/1.24  #Ref     : 1
% 1.89/1.24  #Sup     : 14
% 1.89/1.24  #Fact    : 0
% 1.89/1.24  #Define  : 0
% 1.89/1.24  #Split   : 3
% 1.89/1.24  #Chain   : 0
% 1.89/1.24  #Close   : 0
% 1.89/1.24  
% 1.89/1.24  Ordering : KBO
% 1.89/1.24  
% 1.89/1.24  Simplification rules
% 1.89/1.24  ----------------------
% 1.89/1.24  #Subsume      : 0
% 1.89/1.24  #Demod        : 23
% 1.89/1.24  #Tautology    : 3
% 1.89/1.24  #SimpNegUnit  : 2
% 1.89/1.24  #BackRed      : 0
% 1.89/1.24  
% 1.89/1.24  #Partial instantiations: 0
% 1.89/1.24  #Strategies tried      : 1
% 1.89/1.24  
% 1.89/1.24  Timing (in seconds)
% 1.89/1.24  ----------------------
% 2.09/1.24  Preprocessing        : 0.31
% 2.09/1.24  Parsing              : 0.17
% 2.09/1.24  CNF conversion       : 0.02
% 2.09/1.24  Main loop            : 0.16
% 2.09/1.24  Inferencing          : 0.07
% 2.09/1.24  Reduction            : 0.05
% 2.09/1.24  Demodulation         : 0.04
% 2.09/1.25  BG Simplification    : 0.01
% 2.09/1.25  Subsumption          : 0.02
% 2.09/1.25  Abstraction          : 0.01
% 2.09/1.25  MUC search           : 0.00
% 2.09/1.25  Cooper               : 0.00
% 2.09/1.25  Total                : 0.49
% 2.09/1.25  Index Insertion      : 0.00
% 2.09/1.25  Index Deletion       : 0.00
% 2.09/1.25  Index Matching       : 0.00
% 2.09/1.25  BG Taut test         : 0.00
%------------------------------------------------------------------------------
