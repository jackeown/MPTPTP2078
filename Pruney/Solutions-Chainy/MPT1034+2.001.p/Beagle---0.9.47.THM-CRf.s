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
% DateTime   : Thu Dec  3 10:16:57 EST 2020

% Result     : Theorem 1.98s
% Output     : CNFRefutation 2.05s
% Verified   : 
% Statistics : Number of formulae       :   62 ( 141 expanded)
%              Number of leaves         :   20 (  59 expanded)
%              Depth                    :    6
%              Number of atoms          :  132 ( 508 expanded)
%              Number of equality atoms :   10 (  20 expanded)
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

tff(f_89,negated_conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t143_funct_2)).

tff(f_33,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_40,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => v1_partfun1(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_partfun1)).

tff(f_54,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => ( ( v1_funct_1(C)
              & v1_funct_2(C,A,B) )
           => ( v1_funct_1(C)
              & v1_partfun1(C,A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc5_funct_2)).

tff(f_71,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_partfun1)).

tff(c_18,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_29,plain,(
    ! [A_19,B_20,D_21] :
      ( r2_relset_1(A_19,B_20,D_21,D_21)
      | ~ m1_subset_1(D_21,k1_zfmisc_1(k2_zfmisc_1(A_19,B_20))) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_34,plain,(
    r2_relset_1('#skF_1','#skF_1','#skF_3','#skF_3') ),
    inference(resolution,[status(thm)],[c_18,c_29])).

tff(c_36,plain,(
    ! [C_22,A_23,B_24] :
      ( v1_partfun1(C_22,A_23)
      | ~ m1_subset_1(C_22,k1_zfmisc_1(k2_zfmisc_1(A_23,B_24)))
      | ~ v1_xboole_0(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_43,plain,
    ( v1_partfun1('#skF_3','#skF_1')
    | ~ v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_18,c_36])).

tff(c_45,plain,(
    ~ v1_xboole_0('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_43])).

tff(c_28,plain,(
    v1_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_26,plain,(
    v1_funct_2('#skF_2','#skF_1','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_24,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_46,plain,(
    ! [C_25,A_26,B_27] :
      ( v1_partfun1(C_25,A_26)
      | ~ v1_funct_2(C_25,A_26,B_27)
      | ~ v1_funct_1(C_25)
      | ~ m1_subset_1(C_25,k1_zfmisc_1(k2_zfmisc_1(A_26,B_27)))
      | v1_xboole_0(B_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_52,plain,
    ( v1_partfun1('#skF_2','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2')
    | v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_24,c_46])).

tff(c_59,plain,
    ( v1_partfun1('#skF_2','#skF_1')
    | v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_52])).

tff(c_60,plain,(
    v1_partfun1('#skF_2','#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_45,c_59])).

tff(c_22,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_20,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_49,plain,
    ( v1_partfun1('#skF_3','#skF_1')
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_3')
    | v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_18,c_46])).

tff(c_55,plain,
    ( v1_partfun1('#skF_3','#skF_1')
    | v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_20,c_49])).

tff(c_56,plain,(
    v1_partfun1('#skF_3','#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_45,c_55])).

tff(c_16,plain,(
    r1_partfun1('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_74,plain,(
    ! [D_32,C_33,A_34,B_35] :
      ( D_32 = C_33
      | ~ r1_partfun1(C_33,D_32)
      | ~ v1_partfun1(D_32,A_34)
      | ~ v1_partfun1(C_33,A_34)
      | ~ m1_subset_1(D_32,k1_zfmisc_1(k2_zfmisc_1(A_34,B_35)))
      | ~ v1_funct_1(D_32)
      | ~ m1_subset_1(C_33,k1_zfmisc_1(k2_zfmisc_1(A_34,B_35)))
      | ~ v1_funct_1(C_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_76,plain,(
    ! [A_34,B_35] :
      ( '#skF_2' = '#skF_3'
      | ~ v1_partfun1('#skF_3',A_34)
      | ~ v1_partfun1('#skF_2',A_34)
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(A_34,B_35)))
      | ~ v1_funct_1('#skF_3')
      | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1(A_34,B_35)))
      | ~ v1_funct_1('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_16,c_74])).

tff(c_79,plain,(
    ! [A_34,B_35] :
      ( '#skF_2' = '#skF_3'
      | ~ v1_partfun1('#skF_3',A_34)
      | ~ v1_partfun1('#skF_2',A_34)
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(A_34,B_35)))
      | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1(A_34,B_35))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_22,c_76])).

tff(c_81,plain,(
    ! [A_36,B_37] :
      ( ~ v1_partfun1('#skF_3',A_36)
      | ~ v1_partfun1('#skF_2',A_36)
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(A_36,B_37)))
      | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1(A_36,B_37))) ) ),
    inference(splitLeft,[status(thm)],[c_79])).

tff(c_84,plain,
    ( ~ v1_partfun1('#skF_3','#skF_1')
    | ~ v1_partfun1('#skF_2','#skF_1')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_24,c_81])).

tff(c_88,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_60,c_56,c_84])).

tff(c_89,plain,(
    '#skF_2' = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_79])).

tff(c_14,plain,(
    ~ r2_relset_1('#skF_1','#skF_1','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_93,plain,(
    ~ r2_relset_1('#skF_1','#skF_1','#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_89,c_14])).

tff(c_102,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_93])).

tff(c_104,plain,(
    v1_xboole_0('#skF_1') ),
    inference(splitRight,[status(thm)],[c_43])).

tff(c_44,plain,
    ( v1_partfun1('#skF_2','#skF_1')
    | ~ v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_24,c_36])).

tff(c_119,plain,(
    v1_partfun1('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_44])).

tff(c_103,plain,(
    v1_partfun1('#skF_3','#skF_1') ),
    inference(splitRight,[status(thm)],[c_43])).

tff(c_133,plain,(
    ! [D_45,C_46,A_47,B_48] :
      ( D_45 = C_46
      | ~ r1_partfun1(C_46,D_45)
      | ~ v1_partfun1(D_45,A_47)
      | ~ v1_partfun1(C_46,A_47)
      | ~ m1_subset_1(D_45,k1_zfmisc_1(k2_zfmisc_1(A_47,B_48)))
      | ~ v1_funct_1(D_45)
      | ~ m1_subset_1(C_46,k1_zfmisc_1(k2_zfmisc_1(A_47,B_48)))
      | ~ v1_funct_1(C_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_135,plain,(
    ! [A_47,B_48] :
      ( '#skF_2' = '#skF_3'
      | ~ v1_partfun1('#skF_3',A_47)
      | ~ v1_partfun1('#skF_2',A_47)
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(A_47,B_48)))
      | ~ v1_funct_1('#skF_3')
      | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1(A_47,B_48)))
      | ~ v1_funct_1('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_16,c_133])).

tff(c_138,plain,(
    ! [A_47,B_48] :
      ( '#skF_2' = '#skF_3'
      | ~ v1_partfun1('#skF_3',A_47)
      | ~ v1_partfun1('#skF_2',A_47)
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(A_47,B_48)))
      | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1(A_47,B_48))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_22,c_135])).

tff(c_140,plain,(
    ! [A_49,B_50] :
      ( ~ v1_partfun1('#skF_3',A_49)
      | ~ v1_partfun1('#skF_2',A_49)
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(A_49,B_50)))
      | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1(A_49,B_50))) ) ),
    inference(splitLeft,[status(thm)],[c_138])).

tff(c_143,plain,
    ( ~ v1_partfun1('#skF_3','#skF_1')
    | ~ v1_partfun1('#skF_2','#skF_1')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_24,c_140])).

tff(c_147,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_119,c_103,c_143])).

tff(c_148,plain,(
    '#skF_2' = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_138])).

tff(c_152,plain,(
    ~ r2_relset_1('#skF_1','#skF_1','#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_148,c_14])).

tff(c_161,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_152])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n015.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 12:06:08 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.98/1.18  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.98/1.18  
% 1.98/1.18  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.98/1.19  %$ r2_relset_1 > v1_funct_2 > v1_partfun1 > r1_partfun1 > m1_subset_1 > v1_xboole_0 > v1_funct_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1
% 1.98/1.19  
% 1.98/1.19  %Foreground sorts:
% 1.98/1.19  
% 1.98/1.19  
% 1.98/1.19  %Background operators:
% 1.98/1.19  
% 1.98/1.19  
% 1.98/1.19  %Foreground operators:
% 1.98/1.19  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 1.98/1.19  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.98/1.19  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 1.98/1.19  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 1.98/1.19  tff('#skF_2', type, '#skF_2': $i).
% 1.98/1.19  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 1.98/1.19  tff('#skF_3', type, '#skF_3': $i).
% 1.98/1.19  tff('#skF_1', type, '#skF_1': $i).
% 1.98/1.19  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.98/1.19  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.98/1.19  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.98/1.19  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.98/1.19  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.98/1.19  tff(r1_partfun1, type, r1_partfun1: ($i * $i) > $o).
% 1.98/1.19  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.98/1.19  
% 2.05/1.20  tff(f_89, negated_conjecture, ~(![A, B]: (((v1_funct_1(B) & v1_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, A, A)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (r1_partfun1(B, C) => r2_relset_1(A, A, B, C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t143_funct_2)).
% 2.05/1.20  tff(f_33, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 2.05/1.20  tff(f_40, axiom, (![A, B]: (v1_xboole_0(A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_partfun1(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_partfun1)).
% 2.05/1.20  tff(f_54, axiom, (![A, B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) => (v1_funct_1(C) & v1_partfun1(C, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc5_funct_2)).
% 2.05/1.20  tff(f_71, axiom, (![A, B, C]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: ((v1_funct_1(D) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((v1_partfun1(C, A) & v1_partfun1(D, A)) & r1_partfun1(C, D)) => (C = D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_partfun1)).
% 2.05/1.20  tff(c_18, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.05/1.20  tff(c_29, plain, (![A_19, B_20, D_21]: (r2_relset_1(A_19, B_20, D_21, D_21) | ~m1_subset_1(D_21, k1_zfmisc_1(k2_zfmisc_1(A_19, B_20))))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.05/1.20  tff(c_34, plain, (r2_relset_1('#skF_1', '#skF_1', '#skF_3', '#skF_3')), inference(resolution, [status(thm)], [c_18, c_29])).
% 2.05/1.20  tff(c_36, plain, (![C_22, A_23, B_24]: (v1_partfun1(C_22, A_23) | ~m1_subset_1(C_22, k1_zfmisc_1(k2_zfmisc_1(A_23, B_24))) | ~v1_xboole_0(A_23))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.05/1.20  tff(c_43, plain, (v1_partfun1('#skF_3', '#skF_1') | ~v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_18, c_36])).
% 2.05/1.20  tff(c_45, plain, (~v1_xboole_0('#skF_1')), inference(splitLeft, [status(thm)], [c_43])).
% 2.05/1.20  tff(c_28, plain, (v1_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.05/1.20  tff(c_26, plain, (v1_funct_2('#skF_2', '#skF_1', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.05/1.20  tff(c_24, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.05/1.20  tff(c_46, plain, (![C_25, A_26, B_27]: (v1_partfun1(C_25, A_26) | ~v1_funct_2(C_25, A_26, B_27) | ~v1_funct_1(C_25) | ~m1_subset_1(C_25, k1_zfmisc_1(k2_zfmisc_1(A_26, B_27))) | v1_xboole_0(B_27))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.05/1.20  tff(c_52, plain, (v1_partfun1('#skF_2', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2') | v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_24, c_46])).
% 2.05/1.20  tff(c_59, plain, (v1_partfun1('#skF_2', '#skF_1') | v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_26, c_52])).
% 2.05/1.20  tff(c_60, plain, (v1_partfun1('#skF_2', '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_45, c_59])).
% 2.05/1.20  tff(c_22, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.05/1.20  tff(c_20, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.05/1.20  tff(c_49, plain, (v1_partfun1('#skF_3', '#skF_1') | ~v1_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_3') | v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_18, c_46])).
% 2.05/1.20  tff(c_55, plain, (v1_partfun1('#skF_3', '#skF_1') | v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_22, c_20, c_49])).
% 2.05/1.20  tff(c_56, plain, (v1_partfun1('#skF_3', '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_45, c_55])).
% 2.05/1.20  tff(c_16, plain, (r1_partfun1('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.05/1.20  tff(c_74, plain, (![D_32, C_33, A_34, B_35]: (D_32=C_33 | ~r1_partfun1(C_33, D_32) | ~v1_partfun1(D_32, A_34) | ~v1_partfun1(C_33, A_34) | ~m1_subset_1(D_32, k1_zfmisc_1(k2_zfmisc_1(A_34, B_35))) | ~v1_funct_1(D_32) | ~m1_subset_1(C_33, k1_zfmisc_1(k2_zfmisc_1(A_34, B_35))) | ~v1_funct_1(C_33))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.05/1.20  tff(c_76, plain, (![A_34, B_35]: ('#skF_2'='#skF_3' | ~v1_partfun1('#skF_3', A_34) | ~v1_partfun1('#skF_2', A_34) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(A_34, B_35))) | ~v1_funct_1('#skF_3') | ~m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1(A_34, B_35))) | ~v1_funct_1('#skF_2'))), inference(resolution, [status(thm)], [c_16, c_74])).
% 2.05/1.20  tff(c_79, plain, (![A_34, B_35]: ('#skF_2'='#skF_3' | ~v1_partfun1('#skF_3', A_34) | ~v1_partfun1('#skF_2', A_34) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(A_34, B_35))) | ~m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1(A_34, B_35))))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_22, c_76])).
% 2.05/1.20  tff(c_81, plain, (![A_36, B_37]: (~v1_partfun1('#skF_3', A_36) | ~v1_partfun1('#skF_2', A_36) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(A_36, B_37))) | ~m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1(A_36, B_37))))), inference(splitLeft, [status(thm)], [c_79])).
% 2.05/1.20  tff(c_84, plain, (~v1_partfun1('#skF_3', '#skF_1') | ~v1_partfun1('#skF_2', '#skF_1') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_24, c_81])).
% 2.05/1.20  tff(c_88, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_18, c_60, c_56, c_84])).
% 2.05/1.20  tff(c_89, plain, ('#skF_2'='#skF_3'), inference(splitRight, [status(thm)], [c_79])).
% 2.05/1.20  tff(c_14, plain, (~r2_relset_1('#skF_1', '#skF_1', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.05/1.20  tff(c_93, plain, (~r2_relset_1('#skF_1', '#skF_1', '#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_89, c_14])).
% 2.05/1.20  tff(c_102, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_34, c_93])).
% 2.05/1.20  tff(c_104, plain, (v1_xboole_0('#skF_1')), inference(splitRight, [status(thm)], [c_43])).
% 2.05/1.20  tff(c_44, plain, (v1_partfun1('#skF_2', '#skF_1') | ~v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_24, c_36])).
% 2.05/1.20  tff(c_119, plain, (v1_partfun1('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_104, c_44])).
% 2.05/1.20  tff(c_103, plain, (v1_partfun1('#skF_3', '#skF_1')), inference(splitRight, [status(thm)], [c_43])).
% 2.05/1.20  tff(c_133, plain, (![D_45, C_46, A_47, B_48]: (D_45=C_46 | ~r1_partfun1(C_46, D_45) | ~v1_partfun1(D_45, A_47) | ~v1_partfun1(C_46, A_47) | ~m1_subset_1(D_45, k1_zfmisc_1(k2_zfmisc_1(A_47, B_48))) | ~v1_funct_1(D_45) | ~m1_subset_1(C_46, k1_zfmisc_1(k2_zfmisc_1(A_47, B_48))) | ~v1_funct_1(C_46))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.05/1.20  tff(c_135, plain, (![A_47, B_48]: ('#skF_2'='#skF_3' | ~v1_partfun1('#skF_3', A_47) | ~v1_partfun1('#skF_2', A_47) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(A_47, B_48))) | ~v1_funct_1('#skF_3') | ~m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1(A_47, B_48))) | ~v1_funct_1('#skF_2'))), inference(resolution, [status(thm)], [c_16, c_133])).
% 2.05/1.20  tff(c_138, plain, (![A_47, B_48]: ('#skF_2'='#skF_3' | ~v1_partfun1('#skF_3', A_47) | ~v1_partfun1('#skF_2', A_47) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(A_47, B_48))) | ~m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1(A_47, B_48))))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_22, c_135])).
% 2.05/1.20  tff(c_140, plain, (![A_49, B_50]: (~v1_partfun1('#skF_3', A_49) | ~v1_partfun1('#skF_2', A_49) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(A_49, B_50))) | ~m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1(A_49, B_50))))), inference(splitLeft, [status(thm)], [c_138])).
% 2.05/1.20  tff(c_143, plain, (~v1_partfun1('#skF_3', '#skF_1') | ~v1_partfun1('#skF_2', '#skF_1') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_24, c_140])).
% 2.05/1.20  tff(c_147, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_18, c_119, c_103, c_143])).
% 2.05/1.20  tff(c_148, plain, ('#skF_2'='#skF_3'), inference(splitRight, [status(thm)], [c_138])).
% 2.05/1.20  tff(c_152, plain, (~r2_relset_1('#skF_1', '#skF_1', '#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_148, c_14])).
% 2.05/1.20  tff(c_161, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_34, c_152])).
% 2.05/1.20  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.05/1.20  
% 2.05/1.20  Inference rules
% 2.05/1.20  ----------------------
% 2.05/1.20  #Ref     : 0
% 2.05/1.20  #Sup     : 16
% 2.05/1.20  #Fact    : 0
% 2.05/1.20  #Define  : 0
% 2.05/1.20  #Split   : 3
% 2.05/1.20  #Chain   : 0
% 2.05/1.20  #Close   : 0
% 2.05/1.20  
% 2.05/1.20  Ordering : KBO
% 2.05/1.20  
% 2.05/1.20  Simplification rules
% 2.05/1.20  ----------------------
% 2.05/1.20  #Subsume      : 1
% 2.05/1.20  #Demod        : 50
% 2.05/1.20  #Tautology    : 13
% 2.05/1.20  #SimpNegUnit  : 2
% 2.05/1.20  #BackRed      : 14
% 2.05/1.20  
% 2.05/1.20  #Partial instantiations: 0
% 2.05/1.20  #Strategies tried      : 1
% 2.05/1.20  
% 2.05/1.20  Timing (in seconds)
% 2.05/1.20  ----------------------
% 2.05/1.21  Preprocessing        : 0.27
% 2.05/1.21  Parsing              : 0.15
% 2.05/1.21  CNF conversion       : 0.02
% 2.05/1.21  Main loop            : 0.16
% 2.05/1.21  Inferencing          : 0.06
% 2.05/1.21  Reduction            : 0.05
% 2.05/1.21  Demodulation         : 0.04
% 2.05/1.21  BG Simplification    : 0.01
% 2.05/1.21  Subsumption          : 0.02
% 2.05/1.21  Abstraction          : 0.01
% 2.05/1.21  MUC search           : 0.00
% 2.05/1.21  Cooper               : 0.00
% 2.05/1.21  Total                : 0.46
% 2.05/1.21  Index Insertion      : 0.00
% 2.05/1.21  Index Deletion       : 0.00
% 2.05/1.21  Index Matching       : 0.00
% 2.05/1.21  BG Taut test         : 0.00
%------------------------------------------------------------------------------
