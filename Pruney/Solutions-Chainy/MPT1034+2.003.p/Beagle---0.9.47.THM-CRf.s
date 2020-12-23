%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:16:57 EST 2020

% Result     : Theorem 1.98s
% Output     : CNFRefutation 2.10s
% Verified   : 
% Statistics : Number of formulae       :   67 ( 199 expanded)
%              Number of leaves         :   22 (  76 expanded)
%              Depth                    :    8
%              Number of atoms          :  119 ( 574 expanded)
%              Number of equality atoms :   14 (  47 expanded)
%              Maximal formula depth    :   13 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > v1_partfun1 > r1_partfun1 > m1_subset_1 > v1_xboole_0 > v1_funct_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_relset_1,type,(
    r2_relset_1: ( $i * $i * $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

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

tff(f_93,negated_conjecture,(
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

tff(f_44,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_36,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(B,A)))
         => v1_xboole_0(C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc4_relset_1)).

tff(f_58,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => ( ( v1_funct_1(C)
              & v1_funct_2(C,A,B) )
           => ( v1_funct_1(C)
              & v1_partfun1(C,A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc5_funct_2)).

tff(f_75,axiom,(
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

tff(f_29,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(c_20,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_42,plain,(
    ! [A_24,B_25,D_26] :
      ( r2_relset_1(A_24,B_25,D_26,D_26)
      | ~ m1_subset_1(D_26,k1_zfmisc_1(k2_zfmisc_1(A_24,B_25))) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_48,plain,(
    r2_relset_1('#skF_1','#skF_1','#skF_3','#skF_3') ),
    inference(resolution,[status(thm)],[c_20,c_42])).

tff(c_26,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_32,plain,(
    ! [C_21,B_22,A_23] :
      ( v1_xboole_0(C_21)
      | ~ m1_subset_1(C_21,k1_zfmisc_1(k2_zfmisc_1(B_22,A_23)))
      | ~ v1_xboole_0(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_39,plain,
    ( v1_xboole_0('#skF_2')
    | ~ v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_26,c_32])).

tff(c_41,plain,(
    ~ v1_xboole_0('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_39])).

tff(c_30,plain,(
    v1_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_28,plain,(
    v1_funct_2('#skF_2','#skF_1','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_49,plain,(
    ! [C_27,A_28,B_29] :
      ( v1_partfun1(C_27,A_28)
      | ~ v1_funct_2(C_27,A_28,B_29)
      | ~ v1_funct_1(C_27)
      | ~ m1_subset_1(C_27,k1_zfmisc_1(k2_zfmisc_1(A_28,B_29)))
      | v1_xboole_0(B_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_52,plain,
    ( v1_partfun1('#skF_2','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2')
    | v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_26,c_49])).

tff(c_58,plain,
    ( v1_partfun1('#skF_2','#skF_1')
    | v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_52])).

tff(c_59,plain,(
    v1_partfun1('#skF_2','#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_41,c_58])).

tff(c_24,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_22,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_55,plain,
    ( v1_partfun1('#skF_3','#skF_1')
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_3')
    | v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_20,c_49])).

tff(c_62,plain,
    ( v1_partfun1('#skF_3','#skF_1')
    | v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_22,c_55])).

tff(c_63,plain,(
    v1_partfun1('#skF_3','#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_41,c_62])).

tff(c_18,plain,(
    r1_partfun1('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_77,plain,(
    ! [D_34,C_35,A_36,B_37] :
      ( D_34 = C_35
      | ~ r1_partfun1(C_35,D_34)
      | ~ v1_partfun1(D_34,A_36)
      | ~ v1_partfun1(C_35,A_36)
      | ~ m1_subset_1(D_34,k1_zfmisc_1(k2_zfmisc_1(A_36,B_37)))
      | ~ v1_funct_1(D_34)
      | ~ m1_subset_1(C_35,k1_zfmisc_1(k2_zfmisc_1(A_36,B_37)))
      | ~ v1_funct_1(C_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_79,plain,(
    ! [A_36,B_37] :
      ( '#skF_2' = '#skF_3'
      | ~ v1_partfun1('#skF_3',A_36)
      | ~ v1_partfun1('#skF_2',A_36)
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(A_36,B_37)))
      | ~ v1_funct_1('#skF_3')
      | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1(A_36,B_37)))
      | ~ v1_funct_1('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_18,c_77])).

tff(c_82,plain,(
    ! [A_36,B_37] :
      ( '#skF_2' = '#skF_3'
      | ~ v1_partfun1('#skF_3',A_36)
      | ~ v1_partfun1('#skF_2',A_36)
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(A_36,B_37)))
      | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1(A_36,B_37))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_24,c_79])).

tff(c_84,plain,(
    ! [A_38,B_39] :
      ( ~ v1_partfun1('#skF_3',A_38)
      | ~ v1_partfun1('#skF_2',A_38)
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(A_38,B_39)))
      | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1(A_38,B_39))) ) ),
    inference(splitLeft,[status(thm)],[c_82])).

tff(c_87,plain,
    ( ~ v1_partfun1('#skF_3','#skF_1')
    | ~ v1_partfun1('#skF_2','#skF_1')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_26,c_84])).

tff(c_91,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_59,c_63,c_87])).

tff(c_92,plain,(
    '#skF_2' = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_82])).

tff(c_16,plain,(
    ~ r2_relset_1('#skF_1','#skF_1','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_96,plain,(
    ~ r2_relset_1('#skF_1','#skF_1','#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_16])).

tff(c_105,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_96])).

tff(c_107,plain,(
    v1_xboole_0('#skF_1') ),
    inference(splitRight,[status(thm)],[c_39])).

tff(c_2,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_122,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_107,c_2])).

tff(c_106,plain,(
    v1_xboole_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_39])).

tff(c_111,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_106,c_2])).

tff(c_128,plain,(
    '#skF_2' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_122,c_111])).

tff(c_112,plain,(
    ! [A_40,B_41,D_42] :
      ( r2_relset_1(A_40,B_41,D_42,D_42)
      | ~ m1_subset_1(D_42,k1_zfmisc_1(k2_zfmisc_1(A_40,B_41))) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_117,plain,(
    r2_relset_1('#skF_1','#skF_1','#skF_2','#skF_2') ),
    inference(resolution,[status(thm)],[c_26,c_112])).

tff(c_176,plain,(
    r2_relset_1('#skF_1','#skF_1','#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_128,c_128,c_117])).

tff(c_40,plain,
    ( v1_xboole_0('#skF_3')
    | ~ v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_20,c_32])).

tff(c_134,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_107,c_40])).

tff(c_123,plain,(
    ! [A_1] :
      ( A_1 = '#skF_2'
      | ~ v1_xboole_0(A_1) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_111,c_2])).

tff(c_147,plain,(
    ! [A_43] :
      ( A_43 = '#skF_1'
      | ~ v1_xboole_0(A_43) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_128,c_123])).

tff(c_154,plain,(
    '#skF_3' = '#skF_1' ),
    inference(resolution,[status(thm)],[c_134,c_147])).

tff(c_137,plain,(
    ~ r2_relset_1('#skF_1','#skF_1','#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_128,c_16])).

tff(c_179,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_176,c_154,c_137])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:46:16 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.98/1.20  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.98/1.21  
% 1.98/1.21  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.98/1.21  %$ r2_relset_1 > v1_funct_2 > v1_partfun1 > r1_partfun1 > m1_subset_1 > v1_xboole_0 > v1_funct_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 1.98/1.21  
% 1.98/1.21  %Foreground sorts:
% 1.98/1.21  
% 1.98/1.21  
% 1.98/1.21  %Background operators:
% 1.98/1.21  
% 1.98/1.21  
% 1.98/1.21  %Foreground operators:
% 1.98/1.21  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 1.98/1.21  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.98/1.21  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 1.98/1.21  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.98/1.21  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 1.98/1.21  tff('#skF_2', type, '#skF_2': $i).
% 1.98/1.21  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 1.98/1.21  tff('#skF_3', type, '#skF_3': $i).
% 1.98/1.21  tff('#skF_1', type, '#skF_1': $i).
% 1.98/1.21  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.98/1.21  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.98/1.21  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.98/1.21  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.98/1.21  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.98/1.21  tff(r1_partfun1, type, r1_partfun1: ($i * $i) > $o).
% 1.98/1.21  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.98/1.21  
% 2.10/1.23  tff(f_93, negated_conjecture, ~(![A, B]: (((v1_funct_1(B) & v1_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, A, A)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (r1_partfun1(B, C) => r2_relset_1(A, A, B, C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t143_funct_2)).
% 2.10/1.23  tff(f_44, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 2.10/1.23  tff(f_36, axiom, (![A, B]: (v1_xboole_0(A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => v1_xboole_0(C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc4_relset_1)).
% 2.10/1.23  tff(f_58, axiom, (![A, B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) => (v1_funct_1(C) & v1_partfun1(C, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc5_funct_2)).
% 2.10/1.23  tff(f_75, axiom, (![A, B, C]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: ((v1_funct_1(D) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((v1_partfun1(C, A) & v1_partfun1(D, A)) & r1_partfun1(C, D)) => (C = D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_partfun1)).
% 2.10/1.23  tff(f_29, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 2.10/1.23  tff(c_20, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.10/1.23  tff(c_42, plain, (![A_24, B_25, D_26]: (r2_relset_1(A_24, B_25, D_26, D_26) | ~m1_subset_1(D_26, k1_zfmisc_1(k2_zfmisc_1(A_24, B_25))))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.10/1.23  tff(c_48, plain, (r2_relset_1('#skF_1', '#skF_1', '#skF_3', '#skF_3')), inference(resolution, [status(thm)], [c_20, c_42])).
% 2.10/1.23  tff(c_26, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.10/1.23  tff(c_32, plain, (![C_21, B_22, A_23]: (v1_xboole_0(C_21) | ~m1_subset_1(C_21, k1_zfmisc_1(k2_zfmisc_1(B_22, A_23))) | ~v1_xboole_0(A_23))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.10/1.23  tff(c_39, plain, (v1_xboole_0('#skF_2') | ~v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_26, c_32])).
% 2.10/1.23  tff(c_41, plain, (~v1_xboole_0('#skF_1')), inference(splitLeft, [status(thm)], [c_39])).
% 2.10/1.23  tff(c_30, plain, (v1_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.10/1.23  tff(c_28, plain, (v1_funct_2('#skF_2', '#skF_1', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.10/1.23  tff(c_49, plain, (![C_27, A_28, B_29]: (v1_partfun1(C_27, A_28) | ~v1_funct_2(C_27, A_28, B_29) | ~v1_funct_1(C_27) | ~m1_subset_1(C_27, k1_zfmisc_1(k2_zfmisc_1(A_28, B_29))) | v1_xboole_0(B_29))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.10/1.23  tff(c_52, plain, (v1_partfun1('#skF_2', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2') | v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_26, c_49])).
% 2.10/1.23  tff(c_58, plain, (v1_partfun1('#skF_2', '#skF_1') | v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_52])).
% 2.10/1.23  tff(c_59, plain, (v1_partfun1('#skF_2', '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_41, c_58])).
% 2.10/1.23  tff(c_24, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.10/1.23  tff(c_22, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.10/1.23  tff(c_55, plain, (v1_partfun1('#skF_3', '#skF_1') | ~v1_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_3') | v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_20, c_49])).
% 2.10/1.23  tff(c_62, plain, (v1_partfun1('#skF_3', '#skF_1') | v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_24, c_22, c_55])).
% 2.10/1.23  tff(c_63, plain, (v1_partfun1('#skF_3', '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_41, c_62])).
% 2.10/1.23  tff(c_18, plain, (r1_partfun1('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.10/1.23  tff(c_77, plain, (![D_34, C_35, A_36, B_37]: (D_34=C_35 | ~r1_partfun1(C_35, D_34) | ~v1_partfun1(D_34, A_36) | ~v1_partfun1(C_35, A_36) | ~m1_subset_1(D_34, k1_zfmisc_1(k2_zfmisc_1(A_36, B_37))) | ~v1_funct_1(D_34) | ~m1_subset_1(C_35, k1_zfmisc_1(k2_zfmisc_1(A_36, B_37))) | ~v1_funct_1(C_35))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.10/1.23  tff(c_79, plain, (![A_36, B_37]: ('#skF_2'='#skF_3' | ~v1_partfun1('#skF_3', A_36) | ~v1_partfun1('#skF_2', A_36) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(A_36, B_37))) | ~v1_funct_1('#skF_3') | ~m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1(A_36, B_37))) | ~v1_funct_1('#skF_2'))), inference(resolution, [status(thm)], [c_18, c_77])).
% 2.10/1.23  tff(c_82, plain, (![A_36, B_37]: ('#skF_2'='#skF_3' | ~v1_partfun1('#skF_3', A_36) | ~v1_partfun1('#skF_2', A_36) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(A_36, B_37))) | ~m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1(A_36, B_37))))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_24, c_79])).
% 2.10/1.23  tff(c_84, plain, (![A_38, B_39]: (~v1_partfun1('#skF_3', A_38) | ~v1_partfun1('#skF_2', A_38) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(A_38, B_39))) | ~m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1(A_38, B_39))))), inference(splitLeft, [status(thm)], [c_82])).
% 2.10/1.23  tff(c_87, plain, (~v1_partfun1('#skF_3', '#skF_1') | ~v1_partfun1('#skF_2', '#skF_1') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_26, c_84])).
% 2.10/1.23  tff(c_91, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_20, c_59, c_63, c_87])).
% 2.10/1.23  tff(c_92, plain, ('#skF_2'='#skF_3'), inference(splitRight, [status(thm)], [c_82])).
% 2.10/1.23  tff(c_16, plain, (~r2_relset_1('#skF_1', '#skF_1', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.10/1.23  tff(c_96, plain, (~r2_relset_1('#skF_1', '#skF_1', '#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_92, c_16])).
% 2.10/1.23  tff(c_105, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_48, c_96])).
% 2.10/1.23  tff(c_107, plain, (v1_xboole_0('#skF_1')), inference(splitRight, [status(thm)], [c_39])).
% 2.10/1.23  tff(c_2, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.10/1.23  tff(c_122, plain, (k1_xboole_0='#skF_1'), inference(resolution, [status(thm)], [c_107, c_2])).
% 2.10/1.23  tff(c_106, plain, (v1_xboole_0('#skF_2')), inference(splitRight, [status(thm)], [c_39])).
% 2.10/1.23  tff(c_111, plain, (k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_106, c_2])).
% 2.10/1.23  tff(c_128, plain, ('#skF_2'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_122, c_111])).
% 2.10/1.23  tff(c_112, plain, (![A_40, B_41, D_42]: (r2_relset_1(A_40, B_41, D_42, D_42) | ~m1_subset_1(D_42, k1_zfmisc_1(k2_zfmisc_1(A_40, B_41))))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.10/1.23  tff(c_117, plain, (r2_relset_1('#skF_1', '#skF_1', '#skF_2', '#skF_2')), inference(resolution, [status(thm)], [c_26, c_112])).
% 2.10/1.23  tff(c_176, plain, (r2_relset_1('#skF_1', '#skF_1', '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_128, c_128, c_117])).
% 2.10/1.23  tff(c_40, plain, (v1_xboole_0('#skF_3') | ~v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_20, c_32])).
% 2.10/1.23  tff(c_134, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_107, c_40])).
% 2.10/1.23  tff(c_123, plain, (![A_1]: (A_1='#skF_2' | ~v1_xboole_0(A_1))), inference(demodulation, [status(thm), theory('equality')], [c_111, c_2])).
% 2.10/1.23  tff(c_147, plain, (![A_43]: (A_43='#skF_1' | ~v1_xboole_0(A_43))), inference(demodulation, [status(thm), theory('equality')], [c_128, c_123])).
% 2.10/1.23  tff(c_154, plain, ('#skF_3'='#skF_1'), inference(resolution, [status(thm)], [c_134, c_147])).
% 2.10/1.23  tff(c_137, plain, (~r2_relset_1('#skF_1', '#skF_1', '#skF_1', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_128, c_16])).
% 2.10/1.23  tff(c_179, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_176, c_154, c_137])).
% 2.10/1.23  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.10/1.23  
% 2.10/1.23  Inference rules
% 2.10/1.23  ----------------------
% 2.10/1.23  #Ref     : 0
% 2.10/1.23  #Sup     : 25
% 2.10/1.23  #Fact    : 0
% 2.10/1.23  #Define  : 0
% 2.10/1.23  #Split   : 2
% 2.10/1.23  #Chain   : 0
% 2.10/1.23  #Close   : 0
% 2.10/1.23  
% 2.10/1.23  Ordering : KBO
% 2.10/1.23  
% 2.10/1.23  Simplification rules
% 2.10/1.23  ----------------------
% 2.10/1.23  #Subsume      : 1
% 2.10/1.23  #Demod        : 52
% 2.10/1.23  #Tautology    : 21
% 2.10/1.23  #SimpNegUnit  : 2
% 2.10/1.23  #BackRed      : 20
% 2.10/1.23  
% 2.10/1.23  #Partial instantiations: 0
% 2.10/1.23  #Strategies tried      : 1
% 2.10/1.23  
% 2.10/1.23  Timing (in seconds)
% 2.10/1.23  ----------------------
% 2.10/1.23  Preprocessing        : 0.29
% 2.10/1.23  Parsing              : 0.17
% 2.10/1.23  CNF conversion       : 0.02
% 2.10/1.23  Main loop            : 0.17
% 2.10/1.23  Inferencing          : 0.06
% 2.10/1.23  Reduction            : 0.06
% 2.10/1.23  Demodulation         : 0.04
% 2.10/1.23  BG Simplification    : 0.01
% 2.10/1.23  Subsumption          : 0.02
% 2.10/1.23  Abstraction          : 0.01
% 2.10/1.23  MUC search           : 0.00
% 2.10/1.23  Cooper               : 0.00
% 2.10/1.23  Total                : 0.50
% 2.10/1.23  Index Insertion      : 0.00
% 2.10/1.23  Index Deletion       : 0.00
% 2.10/1.23  Index Matching       : 0.00
% 2.10/1.23  BG Taut test         : 0.00
%------------------------------------------------------------------------------
