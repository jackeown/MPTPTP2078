%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:16:38 EST 2020

% Result     : Theorem 1.96s
% Output     : CNFRefutation 1.96s
% Verified   : 
% Statistics : Number of formulae       :   43 (  81 expanded)
%              Number of leaves         :   20 (  40 expanded)
%              Depth                    :    7
%              Number of atoms          :   69 ( 240 expanded)
%              Number of equality atoms :    9 (  32 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_funct_1 > k7_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k7_relset_1,type,(
    k7_relset_1: ( $i * $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_66,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ! [E] :
            ~ ( r2_hidden(E,k7_relset_1(A,B,D,C))
              & ! [F] :
                  ( m1_subset_1(F,A)
                 => ~ ( r2_hidden(F,C)
                      & E = k1_funct_1(D,F) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t116_funct_2)).

tff(f_47,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ! [E] :
          ~ ( r2_hidden(E,k7_relset_1(A,B,D,C))
            & ! [F] :
                ~ ( r2_hidden(F,A)
                  & r2_hidden(F,C)
                  & E = k1_funct_1(D,F) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t115_funct_2)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

tff(c_12,plain,(
    r2_hidden('#skF_6',k7_relset_1('#skF_2','#skF_3','#skF_5','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_18,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_16,plain,(
    v1_funct_2('#skF_5','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_14,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_25,plain,(
    ! [A_21,C_22,D_20,B_24,E_23] :
      ( r2_hidden('#skF_1'(D_20,A_21,C_22,E_23,B_24),C_22)
      | ~ r2_hidden(E_23,k7_relset_1(A_21,B_24,D_20,C_22))
      | ~ m1_subset_1(D_20,k1_zfmisc_1(k2_zfmisc_1(A_21,B_24)))
      | ~ v1_funct_2(D_20,A_21,B_24)
      | ~ v1_funct_1(D_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_27,plain,(
    ! [C_22,E_23] :
      ( r2_hidden('#skF_1'('#skF_5','#skF_2',C_22,E_23,'#skF_3'),C_22)
      | ~ r2_hidden(E_23,k7_relset_1('#skF_2','#skF_3','#skF_5',C_22))
      | ~ v1_funct_2('#skF_5','#skF_2','#skF_3')
      | ~ v1_funct_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_14,c_25])).

tff(c_31,plain,(
    ! [C_25,E_26] :
      ( r2_hidden('#skF_1'('#skF_5','#skF_2',C_25,E_26,'#skF_3'),C_25)
      | ~ r2_hidden(E_26,k7_relset_1('#skF_2','#skF_3','#skF_5',C_25)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_16,c_27])).

tff(c_10,plain,(
    ! [F_16] :
      ( k1_funct_1('#skF_5',F_16) != '#skF_6'
      | ~ r2_hidden(F_16,'#skF_4')
      | ~ m1_subset_1(F_16,'#skF_2') ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_41,plain,(
    ! [E_27] :
      ( k1_funct_1('#skF_5','#skF_1'('#skF_5','#skF_2','#skF_4',E_27,'#skF_3')) != '#skF_6'
      | ~ m1_subset_1('#skF_1'('#skF_5','#skF_2','#skF_4',E_27,'#skF_3'),'#skF_2')
      | ~ r2_hidden(E_27,k7_relset_1('#skF_2','#skF_3','#skF_5','#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_31,c_10])).

tff(c_50,plain,
    ( k1_funct_1('#skF_5','#skF_1'('#skF_5','#skF_2','#skF_4','#skF_6','#skF_3')) != '#skF_6'
    | ~ m1_subset_1('#skF_1'('#skF_5','#skF_2','#skF_4','#skF_6','#skF_3'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_12,c_41])).

tff(c_59,plain,(
    ~ m1_subset_1('#skF_1'('#skF_5','#skF_2','#skF_4','#skF_6','#skF_3'),'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_50])).

tff(c_60,plain,(
    ! [E_33,A_31,D_30,C_32,B_34] :
      ( r2_hidden('#skF_1'(D_30,A_31,C_32,E_33,B_34),A_31)
      | ~ r2_hidden(E_33,k7_relset_1(A_31,B_34,D_30,C_32))
      | ~ m1_subset_1(D_30,k1_zfmisc_1(k2_zfmisc_1(A_31,B_34)))
      | ~ v1_funct_2(D_30,A_31,B_34)
      | ~ v1_funct_1(D_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_62,plain,(
    ! [C_32,E_33] :
      ( r2_hidden('#skF_1'('#skF_5','#skF_2',C_32,E_33,'#skF_3'),'#skF_2')
      | ~ r2_hidden(E_33,k7_relset_1('#skF_2','#skF_3','#skF_5',C_32))
      | ~ v1_funct_2('#skF_5','#skF_2','#skF_3')
      | ~ v1_funct_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_14,c_60])).

tff(c_80,plain,(
    ! [C_40,E_41] :
      ( r2_hidden('#skF_1'('#skF_5','#skF_2',C_40,E_41,'#skF_3'),'#skF_2')
      | ~ r2_hidden(E_41,k7_relset_1('#skF_2','#skF_3','#skF_5',C_40)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_16,c_62])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( m1_subset_1(A_1,B_2)
      | ~ r2_hidden(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_85,plain,(
    ! [C_42,E_43] :
      ( m1_subset_1('#skF_1'('#skF_5','#skF_2',C_42,E_43,'#skF_3'),'#skF_2')
      | ~ r2_hidden(E_43,k7_relset_1('#skF_2','#skF_3','#skF_5',C_42)) ) ),
    inference(resolution,[status(thm)],[c_80,c_2])).

tff(c_92,plain,(
    m1_subset_1('#skF_1'('#skF_5','#skF_2','#skF_4','#skF_6','#skF_3'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_12,c_85])).

tff(c_97,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_59,c_92])).

tff(c_98,plain,(
    k1_funct_1('#skF_5','#skF_1'('#skF_5','#skF_2','#skF_4','#skF_6','#skF_3')) != '#skF_6' ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_122,plain,(
    ! [B_57,D_53,C_55,E_56,A_54] :
      ( k1_funct_1(D_53,'#skF_1'(D_53,A_54,C_55,E_56,B_57)) = E_56
      | ~ r2_hidden(E_56,k7_relset_1(A_54,B_57,D_53,C_55))
      | ~ m1_subset_1(D_53,k1_zfmisc_1(k2_zfmisc_1(A_54,B_57)))
      | ~ v1_funct_2(D_53,A_54,B_57)
      | ~ v1_funct_1(D_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_127,plain,
    ( k1_funct_1('#skF_5','#skF_1'('#skF_5','#skF_2','#skF_4','#skF_6','#skF_3')) = '#skF_6'
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
    | ~ v1_funct_2('#skF_5','#skF_2','#skF_3')
    | ~ v1_funct_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_12,c_122])).

tff(c_131,plain,(
    k1_funct_1('#skF_5','#skF_1'('#skF_5','#skF_2','#skF_4','#skF_6','#skF_3')) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_16,c_14,c_127])).

tff(c_133,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_98,c_131])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.01/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n003.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 16:50:12 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.96/1.21  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.96/1.21  
% 1.96/1.21  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.96/1.21  %$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_funct_1 > k7_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 1.96/1.21  
% 1.96/1.21  %Foreground sorts:
% 1.96/1.21  
% 1.96/1.21  
% 1.96/1.21  %Background operators:
% 1.96/1.21  
% 1.96/1.21  
% 1.96/1.21  %Foreground operators:
% 1.96/1.21  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 1.96/1.21  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.96/1.21  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.96/1.21  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 1.96/1.21  tff('#skF_5', type, '#skF_5': $i).
% 1.96/1.21  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 1.96/1.21  tff('#skF_6', type, '#skF_6': $i).
% 1.96/1.21  tff('#skF_2', type, '#skF_2': $i).
% 1.96/1.21  tff('#skF_3', type, '#skF_3': $i).
% 1.96/1.21  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.96/1.21  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 1.96/1.21  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i * $i) > $i).
% 1.96/1.21  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.96/1.21  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.96/1.21  tff('#skF_4', type, '#skF_4': $i).
% 1.96/1.21  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.96/1.21  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.96/1.21  
% 1.96/1.23  tff(f_66, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: ~(r2_hidden(E, k7_relset_1(A, B, D, C)) & (![F]: (m1_subset_1(F, A) => ~(r2_hidden(F, C) & (E = k1_funct_1(D, F))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t116_funct_2)).
% 1.96/1.23  tff(f_47, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: ~(r2_hidden(E, k7_relset_1(A, B, D, C)) & (![F]: ~((r2_hidden(F, A) & r2_hidden(F, C)) & (E = k1_funct_1(D, F)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t115_funct_2)).
% 1.96/1.23  tff(f_29, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_subset)).
% 1.96/1.23  tff(c_12, plain, (r2_hidden('#skF_6', k7_relset_1('#skF_2', '#skF_3', '#skF_5', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_66])).
% 1.96/1.23  tff(c_18, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_66])).
% 1.96/1.23  tff(c_16, plain, (v1_funct_2('#skF_5', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_66])).
% 1.96/1.23  tff(c_14, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_66])).
% 1.96/1.23  tff(c_25, plain, (![A_21, C_22, D_20, B_24, E_23]: (r2_hidden('#skF_1'(D_20, A_21, C_22, E_23, B_24), C_22) | ~r2_hidden(E_23, k7_relset_1(A_21, B_24, D_20, C_22)) | ~m1_subset_1(D_20, k1_zfmisc_1(k2_zfmisc_1(A_21, B_24))) | ~v1_funct_2(D_20, A_21, B_24) | ~v1_funct_1(D_20))), inference(cnfTransformation, [status(thm)], [f_47])).
% 1.96/1.23  tff(c_27, plain, (![C_22, E_23]: (r2_hidden('#skF_1'('#skF_5', '#skF_2', C_22, E_23, '#skF_3'), C_22) | ~r2_hidden(E_23, k7_relset_1('#skF_2', '#skF_3', '#skF_5', C_22)) | ~v1_funct_2('#skF_5', '#skF_2', '#skF_3') | ~v1_funct_1('#skF_5'))), inference(resolution, [status(thm)], [c_14, c_25])).
% 1.96/1.23  tff(c_31, plain, (![C_25, E_26]: (r2_hidden('#skF_1'('#skF_5', '#skF_2', C_25, E_26, '#skF_3'), C_25) | ~r2_hidden(E_26, k7_relset_1('#skF_2', '#skF_3', '#skF_5', C_25)))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_16, c_27])).
% 1.96/1.23  tff(c_10, plain, (![F_16]: (k1_funct_1('#skF_5', F_16)!='#skF_6' | ~r2_hidden(F_16, '#skF_4') | ~m1_subset_1(F_16, '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_66])).
% 1.96/1.23  tff(c_41, plain, (![E_27]: (k1_funct_1('#skF_5', '#skF_1'('#skF_5', '#skF_2', '#skF_4', E_27, '#skF_3'))!='#skF_6' | ~m1_subset_1('#skF_1'('#skF_5', '#skF_2', '#skF_4', E_27, '#skF_3'), '#skF_2') | ~r2_hidden(E_27, k7_relset_1('#skF_2', '#skF_3', '#skF_5', '#skF_4')))), inference(resolution, [status(thm)], [c_31, c_10])).
% 1.96/1.23  tff(c_50, plain, (k1_funct_1('#skF_5', '#skF_1'('#skF_5', '#skF_2', '#skF_4', '#skF_6', '#skF_3'))!='#skF_6' | ~m1_subset_1('#skF_1'('#skF_5', '#skF_2', '#skF_4', '#skF_6', '#skF_3'), '#skF_2')), inference(resolution, [status(thm)], [c_12, c_41])).
% 1.96/1.23  tff(c_59, plain, (~m1_subset_1('#skF_1'('#skF_5', '#skF_2', '#skF_4', '#skF_6', '#skF_3'), '#skF_2')), inference(splitLeft, [status(thm)], [c_50])).
% 1.96/1.23  tff(c_60, plain, (![E_33, A_31, D_30, C_32, B_34]: (r2_hidden('#skF_1'(D_30, A_31, C_32, E_33, B_34), A_31) | ~r2_hidden(E_33, k7_relset_1(A_31, B_34, D_30, C_32)) | ~m1_subset_1(D_30, k1_zfmisc_1(k2_zfmisc_1(A_31, B_34))) | ~v1_funct_2(D_30, A_31, B_34) | ~v1_funct_1(D_30))), inference(cnfTransformation, [status(thm)], [f_47])).
% 1.96/1.23  tff(c_62, plain, (![C_32, E_33]: (r2_hidden('#skF_1'('#skF_5', '#skF_2', C_32, E_33, '#skF_3'), '#skF_2') | ~r2_hidden(E_33, k7_relset_1('#skF_2', '#skF_3', '#skF_5', C_32)) | ~v1_funct_2('#skF_5', '#skF_2', '#skF_3') | ~v1_funct_1('#skF_5'))), inference(resolution, [status(thm)], [c_14, c_60])).
% 1.96/1.23  tff(c_80, plain, (![C_40, E_41]: (r2_hidden('#skF_1'('#skF_5', '#skF_2', C_40, E_41, '#skF_3'), '#skF_2') | ~r2_hidden(E_41, k7_relset_1('#skF_2', '#skF_3', '#skF_5', C_40)))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_16, c_62])).
% 1.96/1.23  tff(c_2, plain, (![A_1, B_2]: (m1_subset_1(A_1, B_2) | ~r2_hidden(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.96/1.23  tff(c_85, plain, (![C_42, E_43]: (m1_subset_1('#skF_1'('#skF_5', '#skF_2', C_42, E_43, '#skF_3'), '#skF_2') | ~r2_hidden(E_43, k7_relset_1('#skF_2', '#skF_3', '#skF_5', C_42)))), inference(resolution, [status(thm)], [c_80, c_2])).
% 1.96/1.23  tff(c_92, plain, (m1_subset_1('#skF_1'('#skF_5', '#skF_2', '#skF_4', '#skF_6', '#skF_3'), '#skF_2')), inference(resolution, [status(thm)], [c_12, c_85])).
% 1.96/1.23  tff(c_97, plain, $false, inference(negUnitSimplification, [status(thm)], [c_59, c_92])).
% 1.96/1.23  tff(c_98, plain, (k1_funct_1('#skF_5', '#skF_1'('#skF_5', '#skF_2', '#skF_4', '#skF_6', '#skF_3'))!='#skF_6'), inference(splitRight, [status(thm)], [c_50])).
% 1.96/1.23  tff(c_122, plain, (![B_57, D_53, C_55, E_56, A_54]: (k1_funct_1(D_53, '#skF_1'(D_53, A_54, C_55, E_56, B_57))=E_56 | ~r2_hidden(E_56, k7_relset_1(A_54, B_57, D_53, C_55)) | ~m1_subset_1(D_53, k1_zfmisc_1(k2_zfmisc_1(A_54, B_57))) | ~v1_funct_2(D_53, A_54, B_57) | ~v1_funct_1(D_53))), inference(cnfTransformation, [status(thm)], [f_47])).
% 1.96/1.23  tff(c_127, plain, (k1_funct_1('#skF_5', '#skF_1'('#skF_5', '#skF_2', '#skF_4', '#skF_6', '#skF_3'))='#skF_6' | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~v1_funct_2('#skF_5', '#skF_2', '#skF_3') | ~v1_funct_1('#skF_5')), inference(resolution, [status(thm)], [c_12, c_122])).
% 1.96/1.23  tff(c_131, plain, (k1_funct_1('#skF_5', '#skF_1'('#skF_5', '#skF_2', '#skF_4', '#skF_6', '#skF_3'))='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_18, c_16, c_14, c_127])).
% 1.96/1.23  tff(c_133, plain, $false, inference(negUnitSimplification, [status(thm)], [c_98, c_131])).
% 1.96/1.23  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.96/1.23  
% 1.96/1.23  Inference rules
% 1.96/1.23  ----------------------
% 1.96/1.23  #Ref     : 0
% 1.96/1.23  #Sup     : 22
% 1.96/1.23  #Fact    : 0
% 1.96/1.23  #Define  : 0
% 1.96/1.23  #Split   : 1
% 1.96/1.23  #Chain   : 0
% 1.96/1.23  #Close   : 0
% 1.96/1.23  
% 1.96/1.23  Ordering : KBO
% 1.96/1.23  
% 1.96/1.23  Simplification rules
% 1.96/1.23  ----------------------
% 1.96/1.23  #Subsume      : 0
% 1.96/1.23  #Demod        : 13
% 1.96/1.23  #Tautology    : 3
% 1.96/1.23  #SimpNegUnit  : 2
% 1.96/1.23  #BackRed      : 0
% 1.96/1.23  
% 1.96/1.23  #Partial instantiations: 0
% 1.96/1.23  #Strategies tried      : 1
% 1.96/1.23  
% 1.96/1.23  Timing (in seconds)
% 1.96/1.23  ----------------------
% 1.96/1.23  Preprocessing        : 0.27
% 1.96/1.23  Parsing              : 0.15
% 1.96/1.23  CNF conversion       : 0.02
% 1.96/1.23  Main loop            : 0.18
% 1.96/1.23  Inferencing          : 0.08
% 1.96/1.23  Reduction            : 0.05
% 1.96/1.23  Demodulation         : 0.04
% 1.96/1.23  BG Simplification    : 0.01
% 1.96/1.23  Subsumption          : 0.03
% 1.96/1.23  Abstraction          : 0.01
% 1.96/1.23  MUC search           : 0.00
% 1.96/1.23  Cooper               : 0.00
% 1.96/1.23  Total                : 0.49
% 1.96/1.23  Index Insertion      : 0.00
% 1.96/1.23  Index Deletion       : 0.00
% 1.96/1.23  Index Matching       : 0.00
% 1.96/1.23  BG Taut test         : 0.00
%------------------------------------------------------------------------------
