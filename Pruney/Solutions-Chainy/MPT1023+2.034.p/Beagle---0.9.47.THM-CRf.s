%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:16:21 EST 2020

% Result     : Theorem 1.75s
% Output     : CNFRefutation 1.75s
% Verified   : 
% Statistics : Number of formulae       :   40 (  62 expanded)
%              Number of leaves         :   19 (  34 expanded)
%              Depth                    :   11
%              Number of atoms          :   77 ( 219 expanded)
%              Number of equality atoms :    5 (  20 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > r2_hidden > m1_subset_1 > v1_funct_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1

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

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_70,negated_conjecture,(
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

tff(f_49,axiom,(
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

tff(f_29,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

tff(c_8,plain,(
    ~ r2_relset_1('#skF_2','#skF_3','#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_22,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_20,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_18,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_16,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_14,plain,(
    v1_funct_2('#skF_5','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_12,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_25,plain,(
    ! [A_19,B_20,C_21,D_22] :
      ( r2_hidden('#skF_1'(A_19,B_20,C_21,D_22),A_19)
      | r2_relset_1(A_19,B_20,C_21,D_22)
      | ~ m1_subset_1(D_22,k1_zfmisc_1(k2_zfmisc_1(A_19,B_20)))
      | ~ v1_funct_2(D_22,A_19,B_20)
      | ~ v1_funct_1(D_22)
      | ~ m1_subset_1(C_21,k1_zfmisc_1(k2_zfmisc_1(A_19,B_20)))
      | ~ v1_funct_2(C_21,A_19,B_20)
      | ~ v1_funct_1(C_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_27,plain,(
    ! [C_21] :
      ( r2_hidden('#skF_1'('#skF_2','#skF_3',C_21,'#skF_5'),'#skF_2')
      | r2_relset_1('#skF_2','#skF_3',C_21,'#skF_5')
      | ~ v1_funct_2('#skF_5','#skF_2','#skF_3')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1(C_21,k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
      | ~ v1_funct_2(C_21,'#skF_2','#skF_3')
      | ~ v1_funct_1(C_21) ) ),
    inference(resolution,[status(thm)],[c_12,c_25])).

tff(c_36,plain,(
    ! [C_23] :
      ( r2_hidden('#skF_1'('#skF_2','#skF_3',C_23,'#skF_5'),'#skF_2')
      | r2_relset_1('#skF_2','#skF_3',C_23,'#skF_5')
      | ~ m1_subset_1(C_23,k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
      | ~ v1_funct_2(C_23,'#skF_2','#skF_3')
      | ~ v1_funct_1(C_23) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_14,c_27])).

tff(c_42,plain,
    ( r2_hidden('#skF_1'('#skF_2','#skF_3','#skF_4','#skF_5'),'#skF_2')
    | r2_relset_1('#skF_2','#skF_3','#skF_4','#skF_5')
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_3')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_18,c_36])).

tff(c_48,plain,
    ( r2_hidden('#skF_1'('#skF_2','#skF_3','#skF_4','#skF_5'),'#skF_2')
    | r2_relset_1('#skF_2','#skF_3','#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_20,c_42])).

tff(c_49,plain,(
    r2_hidden('#skF_1'('#skF_2','#skF_3','#skF_4','#skF_5'),'#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_8,c_48])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( m1_subset_1(A_1,B_2)
      | ~ r2_hidden(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_53,plain,(
    m1_subset_1('#skF_1'('#skF_2','#skF_3','#skF_4','#skF_5'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_49,c_2])).

tff(c_10,plain,(
    ! [E_15] :
      ( k1_funct_1('#skF_5',E_15) = k1_funct_1('#skF_4',E_15)
      | ~ m1_subset_1(E_15,'#skF_2') ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_57,plain,(
    k1_funct_1('#skF_5','#skF_1'('#skF_2','#skF_3','#skF_4','#skF_5')) = k1_funct_1('#skF_4','#skF_1'('#skF_2','#skF_3','#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_53,c_10])).

tff(c_4,plain,(
    ! [D_9,A_3,B_4,C_5] :
      ( k1_funct_1(D_9,'#skF_1'(A_3,B_4,C_5,D_9)) != k1_funct_1(C_5,'#skF_1'(A_3,B_4,C_5,D_9))
      | r2_relset_1(A_3,B_4,C_5,D_9)
      | ~ m1_subset_1(D_9,k1_zfmisc_1(k2_zfmisc_1(A_3,B_4)))
      | ~ v1_funct_2(D_9,A_3,B_4)
      | ~ v1_funct_1(D_9)
      | ~ m1_subset_1(C_5,k1_zfmisc_1(k2_zfmisc_1(A_3,B_4)))
      | ~ v1_funct_2(C_5,A_3,B_4)
      | ~ v1_funct_1(C_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_65,plain,
    ( r2_relset_1('#skF_2','#skF_3','#skF_4','#skF_5')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
    | ~ v1_funct_2('#skF_5','#skF_2','#skF_3')
    | ~ v1_funct_1('#skF_5')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_3')
    | ~ v1_funct_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_57,c_4])).

tff(c_70,plain,(
    r2_relset_1('#skF_2','#skF_3','#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_20,c_18,c_16,c_14,c_12,c_65])).

tff(c_72,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_8,c_70])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n019.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 15:10:22 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.75/1.13  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.75/1.14  
% 1.75/1.14  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.75/1.14  %$ r2_relset_1 > v1_funct_2 > r2_hidden > m1_subset_1 > v1_funct_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 1.75/1.14  
% 1.75/1.14  %Foreground sorts:
% 1.75/1.14  
% 1.75/1.14  
% 1.75/1.14  %Background operators:
% 1.75/1.14  
% 1.75/1.14  
% 1.75/1.14  %Foreground operators:
% 1.75/1.14  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 1.75/1.14  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.75/1.14  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 1.75/1.14  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.75/1.14  tff('#skF_5', type, '#skF_5': $i).
% 1.75/1.14  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 1.75/1.14  tff('#skF_2', type, '#skF_2': $i).
% 1.75/1.14  tff('#skF_3', type, '#skF_3': $i).
% 1.75/1.14  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.75/1.14  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 1.75/1.14  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.75/1.14  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.75/1.14  tff('#skF_4', type, '#skF_4': $i).
% 1.75/1.14  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.75/1.14  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 1.75/1.14  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.75/1.14  
% 1.75/1.15  tff(f_70, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((![E]: (m1_subset_1(E, A) => (k1_funct_1(C, E) = k1_funct_1(D, E)))) => r2_relset_1(A, B, C, D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_funct_2)).
% 1.75/1.15  tff(f_49, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((![E]: (r2_hidden(E, A) => (k1_funct_1(C, E) = k1_funct_1(D, E)))) => r2_relset_1(A, B, C, D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t18_funct_2)).
% 1.75/1.15  tff(f_29, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_subset)).
% 1.75/1.15  tff(c_8, plain, (~r2_relset_1('#skF_2', '#skF_3', '#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_70])).
% 1.75/1.15  tff(c_22, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_70])).
% 1.75/1.15  tff(c_20, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_70])).
% 1.75/1.15  tff(c_18, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_70])).
% 1.75/1.15  tff(c_16, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_70])).
% 1.75/1.15  tff(c_14, plain, (v1_funct_2('#skF_5', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_70])).
% 1.75/1.15  tff(c_12, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_70])).
% 1.75/1.15  tff(c_25, plain, (![A_19, B_20, C_21, D_22]: (r2_hidden('#skF_1'(A_19, B_20, C_21, D_22), A_19) | r2_relset_1(A_19, B_20, C_21, D_22) | ~m1_subset_1(D_22, k1_zfmisc_1(k2_zfmisc_1(A_19, B_20))) | ~v1_funct_2(D_22, A_19, B_20) | ~v1_funct_1(D_22) | ~m1_subset_1(C_21, k1_zfmisc_1(k2_zfmisc_1(A_19, B_20))) | ~v1_funct_2(C_21, A_19, B_20) | ~v1_funct_1(C_21))), inference(cnfTransformation, [status(thm)], [f_49])).
% 1.75/1.15  tff(c_27, plain, (![C_21]: (r2_hidden('#skF_1'('#skF_2', '#skF_3', C_21, '#skF_5'), '#skF_2') | r2_relset_1('#skF_2', '#skF_3', C_21, '#skF_5') | ~v1_funct_2('#skF_5', '#skF_2', '#skF_3') | ~v1_funct_1('#skF_5') | ~m1_subset_1(C_21, k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~v1_funct_2(C_21, '#skF_2', '#skF_3') | ~v1_funct_1(C_21))), inference(resolution, [status(thm)], [c_12, c_25])).
% 1.75/1.15  tff(c_36, plain, (![C_23]: (r2_hidden('#skF_1'('#skF_2', '#skF_3', C_23, '#skF_5'), '#skF_2') | r2_relset_1('#skF_2', '#skF_3', C_23, '#skF_5') | ~m1_subset_1(C_23, k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~v1_funct_2(C_23, '#skF_2', '#skF_3') | ~v1_funct_1(C_23))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_14, c_27])).
% 1.75/1.15  tff(c_42, plain, (r2_hidden('#skF_1'('#skF_2', '#skF_3', '#skF_4', '#skF_5'), '#skF_2') | r2_relset_1('#skF_2', '#skF_3', '#skF_4', '#skF_5') | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_18, c_36])).
% 1.75/1.15  tff(c_48, plain, (r2_hidden('#skF_1'('#skF_2', '#skF_3', '#skF_4', '#skF_5'), '#skF_2') | r2_relset_1('#skF_2', '#skF_3', '#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_22, c_20, c_42])).
% 1.75/1.15  tff(c_49, plain, (r2_hidden('#skF_1'('#skF_2', '#skF_3', '#skF_4', '#skF_5'), '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_8, c_48])).
% 1.75/1.15  tff(c_2, plain, (![A_1, B_2]: (m1_subset_1(A_1, B_2) | ~r2_hidden(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.75/1.15  tff(c_53, plain, (m1_subset_1('#skF_1'('#skF_2', '#skF_3', '#skF_4', '#skF_5'), '#skF_2')), inference(resolution, [status(thm)], [c_49, c_2])).
% 1.75/1.15  tff(c_10, plain, (![E_15]: (k1_funct_1('#skF_5', E_15)=k1_funct_1('#skF_4', E_15) | ~m1_subset_1(E_15, '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_70])).
% 1.75/1.15  tff(c_57, plain, (k1_funct_1('#skF_5', '#skF_1'('#skF_2', '#skF_3', '#skF_4', '#skF_5'))=k1_funct_1('#skF_4', '#skF_1'('#skF_2', '#skF_3', '#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_53, c_10])).
% 1.75/1.15  tff(c_4, plain, (![D_9, A_3, B_4, C_5]: (k1_funct_1(D_9, '#skF_1'(A_3, B_4, C_5, D_9))!=k1_funct_1(C_5, '#skF_1'(A_3, B_4, C_5, D_9)) | r2_relset_1(A_3, B_4, C_5, D_9) | ~m1_subset_1(D_9, k1_zfmisc_1(k2_zfmisc_1(A_3, B_4))) | ~v1_funct_2(D_9, A_3, B_4) | ~v1_funct_1(D_9) | ~m1_subset_1(C_5, k1_zfmisc_1(k2_zfmisc_1(A_3, B_4))) | ~v1_funct_2(C_5, A_3, B_4) | ~v1_funct_1(C_5))), inference(cnfTransformation, [status(thm)], [f_49])).
% 1.75/1.15  tff(c_65, plain, (r2_relset_1('#skF_2', '#skF_3', '#skF_4', '#skF_5') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~v1_funct_2('#skF_5', '#skF_2', '#skF_3') | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3') | ~v1_funct_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_57, c_4])).
% 1.75/1.15  tff(c_70, plain, (r2_relset_1('#skF_2', '#skF_3', '#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_22, c_20, c_18, c_16, c_14, c_12, c_65])).
% 1.75/1.15  tff(c_72, plain, $false, inference(negUnitSimplification, [status(thm)], [c_8, c_70])).
% 1.75/1.15  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.75/1.15  
% 1.75/1.15  Inference rules
% 1.75/1.15  ----------------------
% 1.75/1.15  #Ref     : 1
% 1.75/1.15  #Sup     : 9
% 1.75/1.15  #Fact    : 0
% 1.75/1.15  #Define  : 0
% 1.75/1.15  #Split   : 1
% 1.75/1.15  #Chain   : 0
% 1.75/1.15  #Close   : 0
% 1.75/1.15  
% 1.75/1.15  Ordering : KBO
% 1.75/1.15  
% 1.75/1.15  Simplification rules
% 1.75/1.15  ----------------------
% 1.75/1.15  #Subsume      : 0
% 1.75/1.15  #Demod        : 14
% 1.75/1.15  #Tautology    : 1
% 1.75/1.15  #SimpNegUnit  : 2
% 1.75/1.15  #BackRed      : 0
% 1.75/1.15  
% 1.75/1.15  #Partial instantiations: 0
% 1.75/1.15  #Strategies tried      : 1
% 1.75/1.15  
% 1.75/1.15  Timing (in seconds)
% 1.75/1.15  ----------------------
% 1.75/1.15  Preprocessing        : 0.28
% 1.75/1.15  Parsing              : 0.15
% 1.75/1.15  CNF conversion       : 0.02
% 1.75/1.15  Main loop            : 0.11
% 1.75/1.15  Inferencing          : 0.04
% 1.75/1.15  Reduction            : 0.04
% 1.75/1.15  Demodulation         : 0.03
% 1.75/1.15  BG Simplification    : 0.01
% 1.75/1.15  Subsumption          : 0.01
% 1.75/1.15  Abstraction          : 0.01
% 1.75/1.15  MUC search           : 0.00
% 1.75/1.15  Cooper               : 0.00
% 1.75/1.15  Total                : 0.42
% 1.75/1.15  Index Insertion      : 0.00
% 1.75/1.15  Index Deletion       : 0.00
% 1.75/1.15  Index Matching       : 0.00
% 1.75/1.15  BG Taut test         : 0.00
%------------------------------------------------------------------------------
