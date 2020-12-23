%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:16:57 EST 2020

% Result     : Theorem 1.94s
% Output     : CNFRefutation 2.12s
% Verified   : 
% Statistics : Number of formulae       :   63 ( 182 expanded)
%              Number of leaves         :   21 (  70 expanded)
%              Depth                    :    7
%              Number of atoms          :  117 ( 561 expanded)
%              Number of equality atoms :   11 (  31 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > v1_partfun1 > r1_partfun1 > m1_subset_1 > v1_xboole_0 > v1_funct_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_relset_1,type,(
    r2_relset_1: ( $i * $i * $i * $i ) > $o )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(v1_partfun1,type,(
    v1_partfun1: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(r1_partfun1,type,(
    r1_partfun1: ( $i * $i ) > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_97,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_funct_1(B)
          & v1_funct_2(B,A,A)
          & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
       => ! [C] :
            ( ( v1_funct_1(C)
              & v1_funct_2(C,A,A)
              & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
           => ( r1_partfun1(B,C)
             => r2_relset_1(A,A,B,C) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t143_funct_2)).

tff(f_48,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_40,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(B,A)))
         => v1_xboole_0(C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc4_relset_1)).

tff(f_62,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => ( ( v1_funct_1(C)
              & v1_funct_2(C,A,B) )
           => ( v1_funct_1(C)
              & v1_partfun1(C,A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc5_funct_2)).

tff(f_79,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ! [D] :
          ( ( v1_funct_1(D)
            & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
         => ( ( v1_partfun1(C,A)
              & v1_partfun1(D,A)
              & r1_partfun1(C,D) )
           => C = D ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_partfun1)).

tff(f_33,axiom,(
    ! [A,B] :
      ~ ( v1_xboole_0(A)
        & A != B
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_boole)).

tff(c_20,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_42,plain,(
    ! [A_26,B_27,D_28] :
      ( r2_relset_1(A_26,B_27,D_28,D_28)
      | ~ m1_subset_1(D_28,k1_zfmisc_1(k2_zfmisc_1(A_26,B_27))) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_47,plain,(
    r2_relset_1('#skF_1','#skF_1','#skF_3','#skF_3') ),
    inference(resolution,[status(thm)],[c_20,c_42])).

tff(c_32,plain,(
    ! [C_23,B_24,A_25] :
      ( v1_xboole_0(C_23)
      | ~ m1_subset_1(C_23,k1_zfmisc_1(k2_zfmisc_1(B_24,A_25)))
      | ~ v1_xboole_0(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_39,plain,
    ( v1_xboole_0('#skF_3')
    | ~ v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_20,c_32])).

tff(c_41,plain,(
    ~ v1_xboole_0('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_39])).

tff(c_30,plain,(
    v1_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_28,plain,(
    v1_funct_2('#skF_2','#skF_1','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_26,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_49,plain,(
    ! [C_29,A_30,B_31] :
      ( v1_partfun1(C_29,A_30)
      | ~ v1_funct_2(C_29,A_30,B_31)
      | ~ v1_funct_1(C_29)
      | ~ m1_subset_1(C_29,k1_zfmisc_1(k2_zfmisc_1(A_30,B_31)))
      | v1_xboole_0(B_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_55,plain,
    ( v1_partfun1('#skF_2','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2')
    | v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_26,c_49])).

tff(c_62,plain,
    ( v1_partfun1('#skF_2','#skF_1')
    | v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_55])).

tff(c_63,plain,(
    v1_partfun1('#skF_2','#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_41,c_62])).

tff(c_24,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_22,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_52,plain,
    ( v1_partfun1('#skF_3','#skF_1')
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_3')
    | v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_20,c_49])).

tff(c_58,plain,
    ( v1_partfun1('#skF_3','#skF_1')
    | v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_22,c_52])).

tff(c_59,plain,(
    v1_partfun1('#skF_3','#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_41,c_58])).

tff(c_18,plain,(
    r1_partfun1('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_77,plain,(
    ! [D_36,C_37,A_38,B_39] :
      ( D_36 = C_37
      | ~ r1_partfun1(C_37,D_36)
      | ~ v1_partfun1(D_36,A_38)
      | ~ v1_partfun1(C_37,A_38)
      | ~ m1_subset_1(D_36,k1_zfmisc_1(k2_zfmisc_1(A_38,B_39)))
      | ~ v1_funct_1(D_36)
      | ~ m1_subset_1(C_37,k1_zfmisc_1(k2_zfmisc_1(A_38,B_39)))
      | ~ v1_funct_1(C_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_79,plain,(
    ! [A_38,B_39] :
      ( '#skF_2' = '#skF_3'
      | ~ v1_partfun1('#skF_3',A_38)
      | ~ v1_partfun1('#skF_2',A_38)
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(A_38,B_39)))
      | ~ v1_funct_1('#skF_3')
      | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1(A_38,B_39)))
      | ~ v1_funct_1('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_18,c_77])).

tff(c_82,plain,(
    ! [A_38,B_39] :
      ( '#skF_2' = '#skF_3'
      | ~ v1_partfun1('#skF_3',A_38)
      | ~ v1_partfun1('#skF_2',A_38)
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(A_38,B_39)))
      | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1(A_38,B_39))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_24,c_79])).

tff(c_84,plain,(
    ! [A_40,B_41] :
      ( ~ v1_partfun1('#skF_3',A_40)
      | ~ v1_partfun1('#skF_2',A_40)
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(A_40,B_41)))
      | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1(A_40,B_41))) ) ),
    inference(splitLeft,[status(thm)],[c_82])).

tff(c_87,plain,
    ( ~ v1_partfun1('#skF_3','#skF_1')
    | ~ v1_partfun1('#skF_2','#skF_1')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_26,c_84])).

tff(c_91,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_63,c_59,c_87])).

tff(c_92,plain,(
    '#skF_2' = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_82])).

tff(c_16,plain,(
    ~ r2_relset_1('#skF_1','#skF_1','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_96,plain,(
    ~ r2_relset_1('#skF_1','#skF_1','#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_16])).

tff(c_105,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_47,c_96])).

tff(c_107,plain,(
    v1_xboole_0('#skF_1') ),
    inference(splitRight,[status(thm)],[c_39])).

tff(c_106,plain,(
    v1_xboole_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_39])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( ~ v1_xboole_0(B_2)
      | B_2 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_126,plain,(
    ! [A_45] :
      ( A_45 = '#skF_3'
      | ~ v1_xboole_0(A_45) ) ),
    inference(resolution,[status(thm)],[c_106,c_2])).

tff(c_137,plain,(
    '#skF_3' = '#skF_1' ),
    inference(resolution,[status(thm)],[c_107,c_126])).

tff(c_111,plain,(
    ! [A_42,B_43,D_44] :
      ( r2_relset_1(A_42,B_43,D_44,D_44)
      | ~ m1_subset_1(D_44,k1_zfmisc_1(k2_zfmisc_1(A_42,B_43))) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_116,plain,(
    r2_relset_1('#skF_1','#skF_1','#skF_3','#skF_3') ),
    inference(resolution,[status(thm)],[c_20,c_111])).

tff(c_179,plain,(
    r2_relset_1('#skF_1','#skF_1','#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_137,c_137,c_116])).

tff(c_40,plain,
    ( v1_xboole_0('#skF_2')
    | ~ v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_26,c_32])).

tff(c_122,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_107,c_40])).

tff(c_136,plain,(
    '#skF_2' = '#skF_3' ),
    inference(resolution,[status(thm)],[c_122,c_126])).

tff(c_143,plain,(
    ~ r2_relset_1('#skF_1','#skF_1','#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_136,c_16])).

tff(c_181,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_179,c_137,c_137,c_143])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.33  % Computer   : n012.cluster.edu
% 0.14/0.33  % Model      : x86_64 x86_64
% 0.14/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.33  % Memory     : 8042.1875MB
% 0.14/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.33  % CPULimit   : 60
% 0.14/0.33  % DateTime   : Tue Dec  1 12:45:52 EST 2020
% 0.14/0.33  % CPUTime    : 
% 0.14/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.94/1.21  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.94/1.22  
% 1.94/1.22  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.94/1.22  %$ r2_relset_1 > v1_funct_2 > v1_partfun1 > r1_partfun1 > m1_subset_1 > v1_xboole_0 > v1_funct_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1
% 1.94/1.22  
% 1.94/1.22  %Foreground sorts:
% 1.94/1.22  
% 1.94/1.22  
% 1.94/1.22  %Background operators:
% 1.94/1.22  
% 1.94/1.22  
% 1.94/1.22  %Foreground operators:
% 1.94/1.22  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 1.94/1.22  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.94/1.22  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 1.94/1.22  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 1.94/1.22  tff('#skF_2', type, '#skF_2': $i).
% 1.94/1.22  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 1.94/1.22  tff('#skF_3', type, '#skF_3': $i).
% 1.94/1.22  tff('#skF_1', type, '#skF_1': $i).
% 1.94/1.22  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.94/1.22  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.94/1.22  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.94/1.22  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.94/1.22  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.94/1.22  tff(r1_partfun1, type, r1_partfun1: ($i * $i) > $o).
% 1.94/1.22  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.94/1.22  
% 2.12/1.23  tff(f_97, negated_conjecture, ~(![A, B]: (((v1_funct_1(B) & v1_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, A, A)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (r1_partfun1(B, C) => r2_relset_1(A, A, B, C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t143_funct_2)).
% 2.12/1.23  tff(f_48, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 2.12/1.23  tff(f_40, axiom, (![A, B]: (v1_xboole_0(A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => v1_xboole_0(C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc4_relset_1)).
% 2.12/1.23  tff(f_62, axiom, (![A, B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) => (v1_funct_1(C) & v1_partfun1(C, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc5_funct_2)).
% 2.12/1.23  tff(f_79, axiom, (![A, B, C]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: ((v1_funct_1(D) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((v1_partfun1(C, A) & v1_partfun1(D, A)) & r1_partfun1(C, D)) => (C = D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_partfun1)).
% 2.12/1.23  tff(f_33, axiom, (![A, B]: ~((v1_xboole_0(A) & ~(A = B)) & v1_xboole_0(B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_boole)).
% 2.12/1.23  tff(c_20, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.12/1.23  tff(c_42, plain, (![A_26, B_27, D_28]: (r2_relset_1(A_26, B_27, D_28, D_28) | ~m1_subset_1(D_28, k1_zfmisc_1(k2_zfmisc_1(A_26, B_27))))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.12/1.23  tff(c_47, plain, (r2_relset_1('#skF_1', '#skF_1', '#skF_3', '#skF_3')), inference(resolution, [status(thm)], [c_20, c_42])).
% 2.12/1.23  tff(c_32, plain, (![C_23, B_24, A_25]: (v1_xboole_0(C_23) | ~m1_subset_1(C_23, k1_zfmisc_1(k2_zfmisc_1(B_24, A_25))) | ~v1_xboole_0(A_25))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.12/1.23  tff(c_39, plain, (v1_xboole_0('#skF_3') | ~v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_20, c_32])).
% 2.12/1.23  tff(c_41, plain, (~v1_xboole_0('#skF_1')), inference(splitLeft, [status(thm)], [c_39])).
% 2.12/1.23  tff(c_30, plain, (v1_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.12/1.23  tff(c_28, plain, (v1_funct_2('#skF_2', '#skF_1', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.12/1.23  tff(c_26, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.12/1.23  tff(c_49, plain, (![C_29, A_30, B_31]: (v1_partfun1(C_29, A_30) | ~v1_funct_2(C_29, A_30, B_31) | ~v1_funct_1(C_29) | ~m1_subset_1(C_29, k1_zfmisc_1(k2_zfmisc_1(A_30, B_31))) | v1_xboole_0(B_31))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.12/1.23  tff(c_55, plain, (v1_partfun1('#skF_2', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2') | v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_26, c_49])).
% 2.12/1.23  tff(c_62, plain, (v1_partfun1('#skF_2', '#skF_1') | v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_55])).
% 2.12/1.23  tff(c_63, plain, (v1_partfun1('#skF_2', '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_41, c_62])).
% 2.12/1.23  tff(c_24, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.12/1.23  tff(c_22, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.12/1.23  tff(c_52, plain, (v1_partfun1('#skF_3', '#skF_1') | ~v1_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_3') | v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_20, c_49])).
% 2.12/1.23  tff(c_58, plain, (v1_partfun1('#skF_3', '#skF_1') | v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_24, c_22, c_52])).
% 2.12/1.23  tff(c_59, plain, (v1_partfun1('#skF_3', '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_41, c_58])).
% 2.12/1.23  tff(c_18, plain, (r1_partfun1('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.12/1.23  tff(c_77, plain, (![D_36, C_37, A_38, B_39]: (D_36=C_37 | ~r1_partfun1(C_37, D_36) | ~v1_partfun1(D_36, A_38) | ~v1_partfun1(C_37, A_38) | ~m1_subset_1(D_36, k1_zfmisc_1(k2_zfmisc_1(A_38, B_39))) | ~v1_funct_1(D_36) | ~m1_subset_1(C_37, k1_zfmisc_1(k2_zfmisc_1(A_38, B_39))) | ~v1_funct_1(C_37))), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.12/1.23  tff(c_79, plain, (![A_38, B_39]: ('#skF_2'='#skF_3' | ~v1_partfun1('#skF_3', A_38) | ~v1_partfun1('#skF_2', A_38) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(A_38, B_39))) | ~v1_funct_1('#skF_3') | ~m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1(A_38, B_39))) | ~v1_funct_1('#skF_2'))), inference(resolution, [status(thm)], [c_18, c_77])).
% 2.12/1.23  tff(c_82, plain, (![A_38, B_39]: ('#skF_2'='#skF_3' | ~v1_partfun1('#skF_3', A_38) | ~v1_partfun1('#skF_2', A_38) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(A_38, B_39))) | ~m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1(A_38, B_39))))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_24, c_79])).
% 2.12/1.23  tff(c_84, plain, (![A_40, B_41]: (~v1_partfun1('#skF_3', A_40) | ~v1_partfun1('#skF_2', A_40) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(A_40, B_41))) | ~m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1(A_40, B_41))))), inference(splitLeft, [status(thm)], [c_82])).
% 2.12/1.23  tff(c_87, plain, (~v1_partfun1('#skF_3', '#skF_1') | ~v1_partfun1('#skF_2', '#skF_1') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_26, c_84])).
% 2.12/1.23  tff(c_91, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_20, c_63, c_59, c_87])).
% 2.12/1.23  tff(c_92, plain, ('#skF_2'='#skF_3'), inference(splitRight, [status(thm)], [c_82])).
% 2.12/1.23  tff(c_16, plain, (~r2_relset_1('#skF_1', '#skF_1', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.12/1.23  tff(c_96, plain, (~r2_relset_1('#skF_1', '#skF_1', '#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_92, c_16])).
% 2.12/1.23  tff(c_105, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_47, c_96])).
% 2.12/1.23  tff(c_107, plain, (v1_xboole_0('#skF_1')), inference(splitRight, [status(thm)], [c_39])).
% 2.12/1.23  tff(c_106, plain, (v1_xboole_0('#skF_3')), inference(splitRight, [status(thm)], [c_39])).
% 2.12/1.23  tff(c_2, plain, (![B_2, A_1]: (~v1_xboole_0(B_2) | B_2=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.12/1.23  tff(c_126, plain, (![A_45]: (A_45='#skF_3' | ~v1_xboole_0(A_45))), inference(resolution, [status(thm)], [c_106, c_2])).
% 2.12/1.23  tff(c_137, plain, ('#skF_3'='#skF_1'), inference(resolution, [status(thm)], [c_107, c_126])).
% 2.12/1.23  tff(c_111, plain, (![A_42, B_43, D_44]: (r2_relset_1(A_42, B_43, D_44, D_44) | ~m1_subset_1(D_44, k1_zfmisc_1(k2_zfmisc_1(A_42, B_43))))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.12/1.23  tff(c_116, plain, (r2_relset_1('#skF_1', '#skF_1', '#skF_3', '#skF_3')), inference(resolution, [status(thm)], [c_20, c_111])).
% 2.12/1.23  tff(c_179, plain, (r2_relset_1('#skF_1', '#skF_1', '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_137, c_137, c_116])).
% 2.12/1.23  tff(c_40, plain, (v1_xboole_0('#skF_2') | ~v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_26, c_32])).
% 2.12/1.23  tff(c_122, plain, (v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_107, c_40])).
% 2.12/1.23  tff(c_136, plain, ('#skF_2'='#skF_3'), inference(resolution, [status(thm)], [c_122, c_126])).
% 2.12/1.23  tff(c_143, plain, (~r2_relset_1('#skF_1', '#skF_1', '#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_136, c_16])).
% 2.12/1.23  tff(c_181, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_179, c_137, c_137, c_143])).
% 2.12/1.23  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.12/1.23  
% 2.12/1.23  Inference rules
% 2.12/1.23  ----------------------
% 2.12/1.24  #Ref     : 0
% 2.12/1.24  #Sup     : 25
% 2.12/1.24  #Fact    : 0
% 2.12/1.24  #Define  : 0
% 2.12/1.24  #Split   : 2
% 2.12/1.24  #Chain   : 0
% 2.12/1.24  #Close   : 0
% 2.12/1.24  
% 2.12/1.24  Ordering : KBO
% 2.12/1.24  
% 2.12/1.24  Simplification rules
% 2.12/1.24  ----------------------
% 2.12/1.24  #Subsume      : 3
% 2.12/1.24  #Demod        : 51
% 2.12/1.24  #Tautology    : 19
% 2.12/1.24  #SimpNegUnit  : 2
% 2.12/1.24  #BackRed      : 20
% 2.12/1.24  
% 2.12/1.24  #Partial instantiations: 0
% 2.12/1.24  #Strategies tried      : 1
% 2.12/1.24  
% 2.12/1.24  Timing (in seconds)
% 2.12/1.24  ----------------------
% 2.12/1.24  Preprocessing        : 0.30
% 2.12/1.24  Parsing              : 0.17
% 2.12/1.24  CNF conversion       : 0.02
% 2.12/1.24  Main loop            : 0.17
% 2.12/1.24  Inferencing          : 0.07
% 2.12/1.24  Reduction            : 0.05
% 2.12/1.24  Demodulation         : 0.04
% 2.12/1.24  BG Simplification    : 0.01
% 2.12/1.24  Subsumption          : 0.03
% 2.12/1.24  Abstraction          : 0.01
% 2.12/1.24  MUC search           : 0.00
% 2.12/1.24  Cooper               : 0.00
% 2.12/1.24  Total                : 0.51
% 2.12/1.24  Index Insertion      : 0.00
% 2.12/1.24  Index Deletion       : 0.00
% 2.12/1.24  Index Matching       : 0.00
% 2.12/1.24  BG Taut test         : 0.00
%------------------------------------------------------------------------------
